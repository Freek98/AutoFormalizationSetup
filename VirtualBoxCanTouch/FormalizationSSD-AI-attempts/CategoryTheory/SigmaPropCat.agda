
{-# OPTIONS --cubical --guardedness #-}
module CategoryTheory.SigmaPropCat where

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
open import Cubical.Functions.Surjection
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism renaming (isIso to isRealIso ; compIso to compRealIso)
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT

open import QuickFixes
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

open Category

module _ {ℓCob ℓChom ℓprop : Level} (C : Category ℓCob ℓChom) (P : C .ob → hProp ℓprop) where
  ΣPropCat* :  Category (ℓ-max ℓCob ℓprop) ℓChom 
  ΣPropCat* .ob = Σ[ c ∈ C .ob ] ⟨ P c ⟩
  ΣPropCat* .Hom[_,_] (c , _) (d , _) = C [ c , d ]
  ΣPropCat* .id       = C .id
  ΣPropCat* ._⋆_      = C ._⋆_
  ΣPropCat* .⋆IdL     = C .⋆IdL
  ΣPropCat* .⋆IdR     = C .⋆IdR
  ΣPropCat* .⋆Assoc   = C .⋆Assoc
  ΣPropCat* .isSetHom = C .isSetHom 

  open isIso
  isIsoΣPropCat* : {x y : ob C} {xp : ⟨ P x ⟩} {yp : ⟨ P y ⟩}
                   {f : C [ x , y ]}
                   → isIso C f → isIso ΣPropCat* {x , xp} {y , yp} f
  (isIsoΣPropCat* isIsoF).inv = isIsoF .inv
  (isIsoΣPropCat* isIsoF).sec = isIsoF .sec
  (isIsoΣPropCat* isIsoF).ret = isIsoF .ret
  
  open Functor
  fstFunctor : Functor ΣPropCat* C
  fstFunctor .F-ob      = fst
  fstFunctor .F-hom f   = f
  fstFunctor .F-id      = refl
  fstFunctor .F-seq _ _ = refl 

module _ {ℓCob ℓChom ℓprop : Level} {C : Category ℓCob ℓChom} (P : C .ob → hProp ℓprop) where
  module _ {ℓBob ℓBhom : Level} {B : Category ℓBob ℓBhom} (F : Functor B C) 
    (FLandsInP : (b : B .ob) → fst $ P (F ⟅ b ⟆)) where
    open Functor 
    FrestrictedToPropCat : Functor B (ΣPropCat* C P)
    FrestrictedToPropCat .F-ob  b = F ⟅ b ⟆ , FLandsInP b
    FrestrictedToPropCat .F-hom   = F .F-hom
    FrestrictedToPropCat .F-id    = F .F-id
    FrestrictedToPropCat .F-seq   = F .F-seq 
