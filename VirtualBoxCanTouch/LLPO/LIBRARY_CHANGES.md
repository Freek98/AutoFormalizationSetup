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

`CountablyPresentedBooleanRings/ProductClosure.agda:382` references
`QB.quotientRec`, which is not in scope in
`BooleanRing.BooleanRingQuotients.QuotientBool` — so `ProductClosure.agda` and
anything importing it (notably `AntiEquivalence/Products.agda`, which holds
`StoneCat-BinProducts`) currently fail to typecheck on a clean checkout. This is
independent of the work in this folder (none of these files are imported here).
`StoneSums` deliberately avoids importing `AntiEquivalence.Products` for this
reason. Worth fixing upstream if you want `Stone-has-BinProducts` available.
