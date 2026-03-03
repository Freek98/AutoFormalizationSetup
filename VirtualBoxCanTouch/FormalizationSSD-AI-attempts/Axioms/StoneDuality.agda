{-# OPTIONS --cubical --guardedness #-}
module Axioms.StoneDuality where
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
open import StoneSpaces.Spectrum

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
open import CategoryTheory.StuffFromStoneAboutBAs
open import CategoryTheory.StuffThatWasInStoneAndShouldBeOrganized
open Functor

StoneDualityAxiom : Type (ℓ-suc ℓ-zero)
StoneDualityAxiom = (B : Booleω) → isEquiv (evaluationMap B)

module _ (SD : StoneDualityAxiom) where
  SDHomVersion : (B : Booleω) → BooleanRingEquiv (fst B) (2^ (Sp B))
  SDHomVersion B .fst .fst = evaluationMap B
  SDHomVersion B .fst .snd = SD B
  SDHomVersion B .snd      = evaluationIsHom B 
  
  ηIsoOnBooleω : (B : Booleω) → isIso BACat {x = fst B} {y = 2^ (Sp B)} (ηBA' (fst B)) 
  ηIsoOnBooleω B = subst (isIso BACat {x = fst B} {y = 2^ (Sp B)}) 
    (sym $ ηBA'Agrees (fst B)) 
    (snd $ (Iso.inv $ BAIso≅BAEquiv (fst B) (2^ (Sp B))) (SDHomVersion B)) 

  SpFullyFaithful : isFullyFaithful SpFunctor
  SpFullyFaithful = adjunctionFact.ηIsoOnImageH→FHFullyFaithful SpGeneralFunctor 2^Functor Sp⊣2^ BooleωEmbedding 
   BooleωEmbeddingIsFullyFaithful ηIsoOnBooleω 

  SpEmbeddingIntoSets : isEmbedding ((SpFunctor .F-ob) :> (Booleω → hSet ℓ-zero))
  SpEmbeddingIntoSets = isFullyFaithful→isEmbd-ob BooleωUnivalent 
    (isUnivalentOp (isUnivalentSET {ℓ-zero})) {F = SpFunctor} SpFullyFaithful 

  SpEmbedding : isEmbedding Sp 
  SpEmbedding = snd $ compEmbedding 
                    (ΣpropEmbedding isSet λ A → isPropIsSet {A = A})
                    (SpFunctor .F-ob , SpEmbeddingIntoSets) 
  
  isPropHasStoneStr : (S : Type ℓ-zero) → isProp (hasStoneStr S)
  isPropHasStoneStr = isEmbedding→hasPropFibers SpEmbedding 

StoneCat : Category (ℓ-suc ℓ-zero) ℓ-zero 
StoneCat = ImageFunctor.Image SpFunctor  

