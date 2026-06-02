# Intended changes to the FormalizationSSD library

This folder (`LLPO`) is kept self-contained: it depends on `FormalizationSSD-Library`
but does **not** modify any of its files, so copying just this folder onto another
machine (next to a pristine, git-clean library) is enough to typecheck everything.

Where a proof really belongs upstream in the library, it is instead developed in a
**local** module here, and the intended upstream edit is recorded below for you to
apply and review later.

## 1. `StoneSpaces/Examples/Ninfty.agda` — complete `neededIso`

The Stone iso `neededIso : Iso SpB∞ ℕ∞` is currently commented out at the bottom of
the file, with its `inv` written but `sec`/`ret` left as holes.

Local stand-in: **`NinftyExtras.agda`** (module `NinftyExtras`), which re-exports
`StoneSpaces.Examples.Ninfty` and adds the finished `neededIso`.

Upstream action: uncomment the `neededIso` block and replace the two holes with:

```agda
neededIso : Iso SpB∞ ℕ∞
neededIso .Iso.fun f = Sp→BinarySequence f , SpHits1AtMostOnce f
neededIso .Iso.inv (α , α1atmostOnce) = inducedHom BoolBR (BinarySequence→SpFreeℕ α)
  λ n → hits1AtMostOnce→respectsRelations α α1atmostOnce (fst $ Iso.inv ℕ×ℕ≅ℕ n) (snd $ Iso.inv ℕ×ℕ≅ℕ n)
neededIso .Iso.sec (α , α1atmostOnce) = Σ≡Prop isPropHits1AtMostOnce
  (funExt (λ n → cong (λ h → h $cr generator n) (evalInduce BoolBR)) ∙ evalBAInduce ℕ BoolBR α)
neededIso .Iso.ret f = inducedHomUnique BoolBR _ _ f
  (inducedBAHomUnique ℕ BoolBR (Sp→BinarySequence f) (f ∘cr quotientImageHom) refl)
```

- `sec`: `Σ≡Prop` reduces to equality of underlying sequences; `evalInduce` gives
  `inv (α,_) ∘cr quotientImageHom ≡ BinarySequence→SpFreeℕ α`, then `evalBAInduce`
  identifies that with `α` on each generator.
- `ret`: a hom out of the quotient is fixed by its precomposition with
  `quotientImageHom` (`inducedHomUnique`); that precomposition agrees with
  `f ∘cr quotientImageHom` on generators definitionally (`inducedBAHomUnique … refl`).

Once this is upstream, `NinftyExtras` can be deleted and imports pointed back at
`StoneSpaces.Examples.Ninfty`.

## 2. New module `AntiEquivalence/StoneSums.agda` — `Sp (A ×BR B) ≅ Sp A ⊎ Sp B`

A new, self-contained module proving that the spectrum sends binary products of
Boolean algebras to binary sums of Stone spaces (the contravariant
"products ↦ coproducts" direction of the anti-equivalence). The substantive iso

```agda
SpProd≅SpSum : (A B : BooleanRing ℓ-zero)
  → Iso (SpGeneralBooleanRing (A ×BR B))
        (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
```

needs **no** Stone-duality axiom and **no** countable-presentation hypothesis: it
is special to the codomain `2 = BoolBR` (connected/indecomposable), where a map
`A ×BR B → 2` factors through exactly one projection. It also re-exports the
anti-equivalence facts `SpFullyFaithful`/`SpEmbedding` from `Axioms.StoneDuality`.

Local stand-in: **`StoneSums.agda`** (module `StoneSums`) — identical except for
the module name.

Upstream action: drop it in as `AntiEquivalence/StoneSums.agda` (restore
`module AntiEquivalence.StoneSums where`). Then `LLPOAttemptLLMAided` can
`import AntiEquivalence.StoneSums` instead of the local `StoneSums`, and
`StoneSums.agda` here can be deleted.

## 3. Pre-existing breakage (NOT introduced here) — `ProductClosure` / `Products`

`CountablyPresentedBooleanRings/ProductClosure.agda` does not typecheck on a clean
checkout for two reasons:

1. it imports the **untracked** `BooleanRing.Products` (line 39) for `_×BR_` /
   `⟨_,_⟩BR`; and
2. it references `QB.quotientRec` (line 382), `QB.quotientRecβ`, and
   `QB.quotientElimProp`, **none** of which are in scope in git's
   `BooleanRing.BooleanRingQuotients.QuotientBool` (that module exposes only
   `quotientImageHom` / `inducedHom` / `_/Im_` etc.).

Anything importing it (notably `AntiEquivalence/Products.agda`, which holds
`StoneCat-BinProducts`) therefore also fails.

### Worked around locally — `ProductClosureLocal.agda`

The whole algebraic proof is ported to the portable module **`ProductClosureLocal.agda`**
(module `ProductClosureLocal`), proving the *same* statement

```agda
Booleω-closed-×BR : (X Y : Booleω) → is-countably-presented-alt (fst X ×BR fst Y)
```

with two fixes:

- **`_×BR_` swap:** the `BooleanRing.Products` import is replaced by the local shim
  `ProductBAProjections` (item 5), so the product is git-tracked
  `BooleanRing.ProductBA`'s `_×BR_` and `⟨_,_⟩BR = ProductBAProjections.⟨_,_⟩BR`.
  Both products have carrier `⟨A⟩ × ⟨B⟩` with componentwise operations, and at
  `ℓ-zero` the same universe level, so the proof body is otherwise verbatim. This
  also makes `Booleω-closed-×BR` produce `is-countably-presented-alt (B∞ ×BR B∞)`
  for the *same* `_×BR_` that `LLPOAttemptLLMAided` / `StoneSums` use.
- **Missing quotient recursors:** a small local module `QBExtra` reconstructs
  `quotientRec` / `quotientRecβ` / `quotientElimProp`. It `unfolding`s QB's opaque
  `_/Im_` and `quotientImageHom`, after which `⟨ B /Im f ⟩` reduces to a
  `Cubical.HITs.SetQuotients` quotient by the relation
  `λ x y → (x - y) ∈ fst (IQ.genIdeal R f)`. Then `quotientRec = SQ.rec`,
  `quotientElimProp = SQ.elimProp` (with that relation supplied explicitly), and
  `quotientRecβ` holds by `refl`. The existing well-definedness proofs `α-wd` /
  `β-wd` plug into `SQ.rec`'s coherence argument unchanged.

`LLPOAttemptLLMAided.prodPresented` now uses
`ProductClosureLocal.Booleω-closed-×BR (B∞ , presented) (B∞ , presented)`
(`fst (B∞ , presented) ×BR fst (B∞ , presented)` is definitionally `B∞ ×BR B∞`),
and the old ODisc-spaces hole `odiscClosedUnderProducts` is commented out as
superseded.

Upstream action: add `quotientRec` / `quotientRecβ` / `quotientElimProp` to
`QuotientBool` (e.g. exactly as in `QBExtra`) and either commit
`BooleanRing.Products` or use `BooleanRing.ProductBA`; then `ProductClosure.agda`
compiles and `ProductClosureLocal.agda` can be deleted (point imports back at
`CountablyPresentedBooleanRings.ProductClosure`).

## 4. New module `CategoricalSumsProducts.agda` — Stone spaces have binary sums

A categorical account of "Boolean algebras have binary products, therefore Stone
spaces have binary sums (coproducts)", and an exposure of the category of Stone
spaces as a first-class object.

Local module: **`CategoricalSumsProducts.agda`** (module `CategoricalSumsProducts`).

Content:

- Exposes `StoneCat` an sich, together with `StoneCategory = StoneCat ^op` (the
  honest, geometric category of Stone spaces, whose morphisms are the continuous
  maps `Sp X → Sp Y`), plus `StoneOb`/`StoneHom`. Recall `StoneCat [ X , Y ] =
  (Sp Y → Sp X)`, so `StoneCat` is `Stone ^op` and `StoneCat ^op` is the category
  that has the sums.
- `StoneCat-BinProducts : BinProducts StoneCat` (rebuilt locally, dualising-free)
  and its dual
  `Stone-BinCoproducts : BinCoproducts (StoneCat ^op)`, the headline categorical
  theorem, with coproduct object of `X , Y` being `Sp (X ×BR Y)` and injections
  `Sp πB`, `Sp πC`. Derived from `Booleω` having binary products via the fully
  faithful contravariant `SpFunctor` (`SpFullyFaithful sd`).

Two hypotheses are taken as parameters where needed:

- `sd : StoneDualityAxiom` (the anti-equivalence), and
- `closed : ClosedUnderProductsBR`, i.e.
  `(X Y : Booleω) → is-countably-presented-alt (fst X ×BR fst Y)`.

The second is *only* needed because the product object must land back in
`Booleω`; it is exactly the type of `CountablyPresentedBooleanRings.ProductClosure.
Booleω-closed-×BR`, which is unavailable due to the breakage in item 3. The module
intentionally does **not** import `ProductClosure`/`AntiEquivalence.Products`.

Upstream action: once item 3 is fixed, drop `CategoricalSumsProducts` in as e.g.
`AntiEquivalence/Sums.agda` next to `AntiEquivalence.Products`, and discharge the
`ClosedUnderProductsBR` hypothesis with `Booleω-closed-×BR`, so that
`Stone-BinCoproducts : BinCoproducts (StoneCat ^op)` depends only on `sd`.

## 5. `BooleanRing.Products` is not in git — local shim `ProductBAProjections`

`BooleanRing/Products.agda` (named projections `pr₁-BR`/`pr₂-BR`, pairing
`⟨_,_⟩BR`, and its universal property) exists in the working library but is
**untracked** — it is not in the library's git version, so depending on it breaks
portability of this folder. `CategoricalSumsProducts` originally imported it.

Fix: the local shim **`ProductBAProjections.agda`** rebuilds that exact interface
on top of the git-tracked `BooleanRing.ProductBA` (`pr₁-BR = BRProduct.πB`,
`⟨_,_⟩BR = BRProduct.UP.⟨f,g⟩`, etc.), and `CategoricalSumsProducts` now imports
the shim. Bonus: this makes the categorical file use the *same* `_×BR_` as
`StoneSums` and the main LLPO file (previously it used a different, nominally
distinct product).

Upstream action: commit `BooleanRing.Products` to the library (or add those names
to `BooleanRing.ProductBA`); then `ProductBAProjections` can be deleted and
`CategoricalSumsProducts` can import the library module directly.
