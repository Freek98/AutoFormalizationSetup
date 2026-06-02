# Intended changes to the FormalizationSSD library

This folder (`LLPO`) is kept self-contained: it depends on `FormalizationSSD-Library`
but does **not** modify any of its files, so copying just this folder onto another
machine (next to a pristine, git-clean library) is enough to typecheck everything.

Where a proof really belongs upstream in the library, it is instead developed in a
**local** module here, and the intended upstream edit is recorded below for you to
apply and review later.

## 1. `StoneSpaces/Examples/Ninfty.agda` — `neededIso` (DONE — committed upstream)

The Stone iso `neededIso : Iso SpB∞ ℕ∞` (where `SpB∞ = Sp presentation` and
`presentation = freeBA ℕ /Im relationsℕ`) is now finished and committed in the
library. There is nothing left to do upstream, and there is **no** `NinftyExtras`
stand-in.

Caveat — why a local adapter remains: the LLPO development is phrased over
`ℕfinCofinBA` (the concrete finite/cofinite sub-BA, required for the even/odd
`splitHom`), not over `presentation`. The two are isomorphic but **not**
definitionally equal, so `neededIso` (over `presentation`) is not the iso the proof
consumes. The local module **`SpNfcIso.agda`** therefore *transports* it:

```agda
σ = compIso (Sp ℕFinCof=Presentation) neededIso : Iso (Sp ℕfinCofinBA) ℕ∞
```

across the committed BA-iso `ℕFinCof=Presentation : BooleanRingEquiv presentation
ℕfinCofinBA` (in `CountablyPresentedBooleanRings.Examples.NFinCofin`), pushed through
the contravariant spectrum action. Concretely, `SpNfcIso.SpEq` turns the BA-iso into a
`CatIso BACat` via `BAIso≅BAEquiv` and applies the spectrum *functor* `SpGeneralFunctor`'s
preservation of isomorphisms (`preserveIsosF`) — which on morphisms is precomposition —
rather than hand-proving the section/retraction. The bridge lemma
`σfun≡toℕ∞seq` reconciles the upstream read-off `Sp→BinarySequence` (via
`generator`/`quotientImageHom`) with the local `toℕ∞seq` (via `singleton`); these
agree only propositionally (`eval-gen`).

`SpNfcIso` is thus a thin adapter of committed content, not a workaround for
anything missing; it stays as long as the proof is phrased over `ℕfinCofinBA`.

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

- **`_×BR_` swap:** the `BooleanRing.Products` import is replaced by the git-tracked
  `BooleanRing.ProductBA` (item 5), so the product is its `_×BR_` and the forward map
  `φ` is built with the pairing `induceProdMapBR`.
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

## 5. `BooleanRing.Products` is not in git — names inlined from `BooleanRing.ProductBA`

`BooleanRing/Products.agda` (named projections `pr₁-BR`/`pr₂-BR`, pairing
`⟨_,_⟩BR`, and its universal property) exists in the working library but is
**untracked** — not in the library's git version, so depending on it breaks
portability of this folder.

Fix: depend only on the git-tracked `BooleanRing.ProductBA`, which already carries
the same content under its own names — the pairing `induceProdMapBR` and the
projections `BRProduct.fstBA` / `BRProduct.sndBA` (the product `_×BR_` lives there
too). These are used directly at the call sites:

- `StoneSums.agda` — the inverse `bwd` via `BRProduct.fstBA`/`BRProduct.sndBA`;
- `EvenOddSplit.agda` — `splitHom = induceProdMapBR evenHom oddHom` (the split map as the
  universal product map of its two halves);
- `ProductClosureLocal.agda` — the forward map `φ` via `induceProdMapBR`.

An earlier local shim **`ProductBAProjections.agda`** re-exported these under the
`pr₁-BR`/`pr₂-BR`/`⟨_,_⟩BR` spelling (on top of the then-current `BRProduct.πB`/`πC`
names); it has been **deleted**, and the projections were renamed `πB`/`πC` →
`fstBA`/`sndBA` upstream.

Upstream action: none needed for portability. If the `pr₁-BR`/`⟨_,_⟩BR` spelling
should be available library-wide, commit `BooleanRing.Products` to git; the call
sites here can then use it but do not depend on it.
