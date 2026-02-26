{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.NFinCofin where

open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Foundations.Equiv
open import Cubical.Data.Fin
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingMaps
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat hiding (_·_ ; _+_)
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Base

open import Cubical.Data.Sum
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order
open import Cubical.Algebra.CommRing.Instances.Unit
open import QuickFixes

--this approach suggested after conversation with AI
isFinite : binarySequence → Type
isFinite α = Σ[ n ∈ ℕ ] (∀ (m : ℕ) → m > n → α m ≡ false)

isCofinite : binarySequence → Type 
isCofinite α = Σ[ n ∈ ℕ ](∀ (m : ℕ) → m > n → α m ≡ true)

BooleanStructureOnBinarySequences : BooleanRingStr binarySequence
BooleanStructureOnBinarySequences = pointWiseStructure ℕ (λ _ → Bool) (λ _ → snd BoolBR)

open BooleanRingStr ⦃...⦄
instance
 _ = BooleanStructureOnBinarySequences 
 _ = BoolBR

open BooleanAlgebraStr (binarySequence , BooleanStructureOnBinarySequences)

complementFiniteIsCofinite : (α : binarySequence) → isFinite α → 
                             isCofinite (¬ α)
complementFiniteIsCofinite α (n , α>n=0) = n , λ m m>n → cong not (α>n=0 m m>n) 

complementCofiniteIsFinite : (α : binarySequence) → isCofinite α → 
                             isFinite (¬ α)
complementCofiniteIsFinite α (n , α>n=1) = n , λ m m>n → cong not (α>n=1 m m>n) 

open <-Reasoning

--unionFiniteFinite : (α β : binarySequence) → 
--  isFinite α → isFinite β → isFinite (α ∨ β)
--unionFiniteFinite α β (n , α>n=0) (m , β>m=0) = max m n , λ r r>mn → 
--  (α ∨ β) r 
--    ≡⟨⟩ 
--  BooleanAlgebraStr._∨_ BoolBR (α r) (β r)
--    ≡⟨ cong₂ (BooleanAlgebraStr._∨_ BoolBR) 
--      (α>n=0 r $ n ≤<⟨ right-≤-max {m = m}⟩ max m n <≡⟨ r>mn ⟩ r ∎)
--      (β>m=0 r $ m ≤<⟨ left-≤-max         ⟩ max m n <≡⟨ r>mn ⟩ r ∎) 
--     ⟩ 
--  BooleanAlgebraStr._∨_ BoolBR false false
--    ≡⟨⟩ 
--  false ∎ 
--  I think it's sufficient to use deMorgan and negations to show the other combinations match up if you realize that intersection with Finite is Finite. If I've proven that, I'll delete this. 

intersectionWithFiniteIsFinite : (α β : binarySequence) → 
  isFinite α → isFinite (α ∧ β)
intersectionWithFiniteIsFinite α β (n , α>n=0) = n , λ r r>mn → 
  (α ∧ β) r 
    ≡⟨⟩ 
  BooleanAlgebraStr._∧_ BoolBR (α r) (β r)
    ≡⟨ cong (λ a' → BooleanAlgebraStr._∧_ BoolBR a' (β r)) 
      (α>n=0 r r>mn)
     ⟩ 
  BooleanAlgebraStr._∧_ BoolBR false (β r)
    ≡⟨⟩ 
  false ∎ 

UnionCofiniteIsCofinite : (α β : binarySequence) → 
  isCofinite α → isCofinite (α ∨ β)
UnionCofiniteIsCofinite α β αCofin = subst isCofinite 
  (¬ (¬ α ∧ ¬ β) 
    ≡⟨ DeMorgan¬∧ {x = ¬ α} {y = ¬ β} ⟩ 
  ¬ ¬ α ∨ ¬ ¬ β 
    ≡⟨ cong₂ _∨_ (¬Invol {x = α}) ¬Invol ⟩ 
  α ∨ β ∎)
  (complementFiniteIsCofinite (¬ α ∧ ¬ β) 
  (intersectionWithFiniteIsFinite (¬ α) (¬ β) (complementCofiniteIsFinite α αCofin))) 

--isFiniteOrCofinite : (α : binarySequence) → Type
--isFiniteOrCofinite α = isFinite α ⊎ isCofinite α
-- I feel there should be some generalization to subalgebras here. 
-- Suppose I have some algebraic structure, say rings, I can show in general that if R is a ring, and P : ⟨ R ⟩ → hProp -- Note you didn't do hProp :(, but you can truncate I guess. 
--  then Σ[ r ∈ R ] P r is also a ring, with the inherited ring structure. 
--  Then you can do the same for commRings, BooleanRings and all the structures you need for that. Let's ask that to some AI program, feel it should be a good short task. 

data FinCofinℕ : Type where
  Finite   : (α : binarySequence) → isFinite α   → FinCofinℕ
  Cofinite : (α : binarySequence) → isCofinite α → FinCofinℕ

open BooleanRingStr
BooleanRingStrOnFinCofinℕ : BooleanRingStr FinCofinℕ 
BooleanRingStrOnFinCofinℕ .𝟘 = Finite   (λ _ → false) (0 , λ _ _ → refl)
BooleanRingStrOnFinCofinℕ .𝟙 = Cofinite (λ _ → true)  (0 , λ _ _ → refl)
BooleanRingStrOnFinCofinℕ ._+_ = {! !}
BooleanRingStrOnFinCofinℕ ._·_ = {! !}
- BooleanRingStrOnFinCofinℕ = {! !}
BooleanRingStrOnFinCofinℕ .isBooleanRing = {! !} 

