

{-# OPTIONS --cubical --guardedness #-}
module CategoryTheory.Image where

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
open Functor

module ImageFunctor
  {ℓ ℓ' ℓ'' ℓ''' : Level} {C : Category ℓ ℓ'} {D : Category ℓ'' ℓ'''}
  (F : Functor C D)  where
--  Image : Category (ℓ-max ℓ ℓ'') ℓ''' 
--  Image .ob           = Σ[ d ∈ D .ob ] fiber (F .F-ob) d
--  Image .Hom[_,_] d e = D [ fst d , fst e ]
  Image : Category ℓ ℓ''' 
  Image .ob           = C .ob
  Image .Hom[_,_] c d = D [ F .F-ob c , F .F-ob d ]
  Image .id           = D .id
  Image ._⋆_          = D ._⋆_
  Image .⋆IdL         = D .⋆IdL
  Image .⋆IdR         = D .⋆IdR
  Image .⋆Assoc       = D .⋆Assoc
  Image .isSetHom     = D .isSetHom 
  
  RestrictCodomain : Functor C Image
  RestrictCodomain .F-ob c = c
  RestrictCodomain .F-hom  = F .F-hom
  RestrictCodomain .F-id   = F .F-id
  RestrictCodomain .F-seq  = F .F-seq

  ExtendImage : Functor Image D
  ExtendImage .F-ob      = F .F-ob
  ExtendImage .F-hom f   = f
  ExtendImage .F-id      = refl
  ExtendImage .F-seq f g = refl
  
  Factorization : ExtendImage ∘F RestrictCodomain ≡ F
  Factorization = Functor≡ (λ _ → refl) λ _ → refl 

{-
  module _ {ℓE ℓE' : Level} {E : Category ℓE ℓE'} (G : Functor D E) where
    RestrictToImage : Functor Image E
    RestrictToImage = G ∘F ExtendImage

  module _ (G : Functor D C) where
    open NaturalBijection
    module _ (F⊣G : F ⊣ G) where
      open _⊣_
      restrictAdjunction : RestrictCodomain ⊣ RestrictToImage G  
      restrictAdjunction .adjIso    = F⊣G .adjIso
      restrictAdjunction .adjNatInD = F⊣G .adjNatInD
      restrictAdjunction .adjNatInC = F⊣G .adjNatInC 
-}

module SubObjectAlongAdjointEquivalence 
--
--      H 
--  E -----> C
--           |
--           |F
--           v
--           D
  {ℓC ℓC' ℓD ℓD' ℓE ℓE' : Level}  
  {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} {E : Category ℓE ℓE'}
  (H : Functor E C) (HfullyFaithful : isFullyFaithful H) 
  (equ : AdjointEquivalence C D) 
  where
  open AdjointEquivalence
  private 
    F = equ .fun
    G = equ .inv

  EFH : Category _ _ 
  EFH = ImageFunctor.Image (F ∘F H) 
