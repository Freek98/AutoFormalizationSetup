{-# OPTIONS --cubical --guardedness #-}

module work.Part10c where

open import work.Part10a public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Data.Unit using (tt)

module BooleanAlgebraLawsModule2 where
  open StoneAsClosedSubsetOfCantorModule
  open StoneAsClosedSubsetOfCantorModule2
  open StoneEqualityClosedModule using (isPropIsClosedProp)
  open BooleanAlgebraLawsModule

  ×-Unit-right : (P : hProp ℓ-zero)
    → ((fst P × Unit) , isProp× (snd P) (λ _ _ → refl)) ≡ P
  ×-Unit-right P = hProp≡ _ _ (λ (p , _) → p) (λ p → p , tt)

  ⊎-⊥-right : (P : hProp ℓ-zero)
    → (∥ fst P ⊎ ⊥ ∥₁ , squash₁) ≡ P
  ⊎-⊥-right P = hProp≡ _ _
    (PT.rec (snd P) (λ { (inl p) → p ; (inr ()) }))
    (λ p → ∣ inl p ∣₁)

  ×-⊥-right : (P : hProp ℓ-zero)
    → ((fst P × ⊥) , isProp× (snd P) isProp⊥) ≡ ⊥-hProp
  ×-⊥-right P = hProp≡ _ _ (λ (_ , bot) → bot) (λ ())

  ⊎-Unit-right : (P : hProp ℓ-zero)
    → (∥ fst P ⊎ Unit ∥₁ , squash₁) ≡ ⊤-hProp
  ⊎-Unit-right P = hProp≡ _ _
    (λ _ → tt)
    (λ _ → ∣ inr tt ∣₁)

  closedIntersectionFull' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A FullClosedSubset ≡ A
  closedIntersectionFull' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × Unit) , isProp× (snd (A x)) (λ _ _ → refl)) ≡ A
    fst-path = funExt (λ x → ×-Unit-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊤-hProp (Aclosed x) ⊤-isClosed)
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  closedUnionEmpty' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A EmptyClosedSubset ≡ A
  closedUnionEmpty' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ ⊥ ∥₁) , squash₁) ≡ A
    fst-path = funExt (λ x → ⊎-⊥-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) ⊥-hProp (Aclosed x) ⊥-isClosed)
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  closedIntersectionEmpty' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A EmptyClosedSubset ≡ EmptyClosedSubset
  closedIntersectionEmpty' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × ⊥) , isProp× (snd (A x)) isProp⊥) ≡ (λ _ → ⊥-hProp)
    fst-path = funExt (λ x → ×-⊥-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊥-hProp (Aclosed x) ⊥-isClosed)
                     (λ _ → ⊥-isClosed)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  closedUnionFull' : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A FullClosedSubset ≡ FullClosedSubset
  closedUnionFull' (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ Unit ∥₁) , squash₁) ≡ (λ _ → ⊤-hProp)
    fst-path = funExt (λ x → ⊎-Unit-right (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) ⊤-hProp (Aclosed x) ⊤-isClosed)
                     (λ _ → ⊤-isClosed)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _
