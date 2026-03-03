{-# OPTIONS --cubical --guardedness #-}
module StoneSpaces.Spectrum where
open import BooleanRing.BooleanRingMaps
open import CountablyPresentedBooleanRings.Definitions 
open import Cubical.Data.Sigma
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sum
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism renaming (isIso to isRealIso ; compIso to compRealIso)
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Cubical.HITs.PropositionalTruncation as PT

open import CountablyPresentedBooleanRings.Examples.Bool
open import QuickFixes

open import BooleanRing.BoolRingUnivalence

open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence.AdjointEquivalence hiding (adjunction)
open import Cubical.Categories.Isomorphism renaming (invIso to CatInvIso)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Tactics.CategorySolver.Reflection

open import CategoryTheory.BasicFacts
open import CategoryTheory.SigmaPropCat
open import CategoryTheory.Image

open Category hiding (_∘_)
SpGeneralBooleanRing : {ℓ : Level} → BooleanRing ℓ → Type ℓ
SpGeneralBooleanRing B = BoolHom B BoolBR

Booleω : Type (ℓ-suc ℓ-zero)
Booleω = countablyPresentedBooleanRing
-- just changed this if things crash Loading is slow for some reason. 

Sp : Booleω → Type ℓ-zero
Sp = SpGeneralBooleanRing ∘ fst 

isSetBoolHom : {ℓ ℓ' : Level} → (B : BooleanRing ℓ) → (C : BooleanRing ℓ') → isSet $ BoolHom B C
isSetBoolHom B C = Embedding-into-isSet→isSet 
  (fst , hasPropFibers→isEmbedding propFiber)
  (isSet→ CSet) where
    CSet : isSet ⟨ C ⟩
    CSet = BooleanRingStr.is-set (snd C)
    proj : BoolHom B C → fst B → fst C
    proj = fst 
    propFiber : (f : ⟨ B ⟩ → ⟨ C ⟩) → isProp (Σ[ z ∈ BoolHom B C ] fst z ≡ f)
    propFiber f ((g , ghom) , g=f) ((h , hhom) , h=f) = Σ≡Prop 
      (λ f' → isSet→ CSet (fst f') f) (Σ≡Prop 
      (λ f' → isPropIsBoolRingHom (snd B) f' (snd C)) 
      (g=f ∙ sym h=f)) 

isSetSp : {ℓ : Level} → (B : BooleanRing ℓ) → isSet (SpGeneralBooleanRing B)
isSetSp B = isSetBoolHom B BoolBR 

ev : (B C : BooleanRing ℓ-zero ) → (b  : ⟨ B ⟩) → BoolHom B C → ⟨ C ⟩
ev B C b f = f $cr b 

evaluationMapGeneralBooleanRing : (B : BooleanRing ℓ-zero ) → (b  : ⟨ B ⟩) → SpGeneralBooleanRing B → Bool
evaluationMapGeneralBooleanRing B = ev B BoolBR

evaluationMap : (B : Booleω) → (b : ⟨ fst B ⟩) → Sp B → Bool
evaluationMap B = evaluationMapGeneralBooleanRing (fst B)

BAstructOnDecidableSubsets : {ℓ : Level} → (S : Type ℓ) → BooleanRingStr (S → Bool)
BAstructOnDecidableSubsets S = pointWiseStructure S (λ _ → Bool) (λ _ → snd BoolBR) 

2^ : {ℓ : Level} → (S : Type ℓ) → BooleanRing ℓ
2^ S .fst = S → Bool
2^ S .snd = BAstructOnDecidableSubsets S 

hasStoneStr : Type ℓ-zero → Type (ℓ-suc ℓ-zero) 
hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S

Stone : Type (ℓ-suc ℓ-zero)
Stone = TypeWithStr ℓ-zero hasStoneStr
