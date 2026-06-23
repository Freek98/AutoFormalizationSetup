{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module AdjunctionUnitIsoEquivalence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Isomorphism renaming (invIso to CatInvIso)
open import QuickFixes
open import CategoryTheory.SigmaPropCat
open import CategoryTheory.BasicFacts

open Category hiding (_∘_)
open Functor

module adjunctionFact
  {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) (G : Functor D C) (adj : F UnitCounit.⊣ G) where

  open UnitCounit._⊣_ adj

  adjIso : (c : C .ob) (d : D .ob) → Iso (C [ c , G .F-ob d ]) (D [ F .F-ob c , d ])
  adjIso c d = invIso $ adj→adj' F G adj .NaturalBijection._⊣_.adjIso {c} {d}

  compη : (x y : C .ob) → (C [ x , y ]) → C [ x , (G ∘F F) ⟅ y ⟆ ]
  compη _ y f = f ⋆⟨ C ⟩ (η ⟦ y ⟧)

  module _ (x y : C .ob) where
    opaque
      compose : Iso.fun (adjIso x (F .F-ob y)) ∘ compη x y ≡ F .F-hom {x = x} {y = y}
      compose = funExt λ f →
        F ⟪ f   ⋆⟨ C ⟩ (η ⟦ y ⟧)⟫      ⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧)
          ≡⟨ cong (λ h → h ⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧)) (F .F-seq f (η ⟦ y ⟧)) ⟩
        F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ η ⟦ y ⟧ ⟫   ⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧)
          ≡⟨ D .⋆Assoc _ _ _ ⟩
        F ⟪ f ⟫ ⋆⟨ D ⟩ ((F ⟪ η ⟦ y ⟧ ⟫)⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧) )
          ≡⟨ cong (λ h → F ⟪ f ⟫ ⋆⟨ D ⟩ h) (Δ₁ y) ⟩
        F ⟪ f ⟫ ⋆⟨ D ⟩ D .id
          ≡⟨ D .⋆IdR (F ⟪ f ⟫) ⟩
        F ⟪ f ⟫ ∎
    module _ (ηIsoy : isIso C (η ⟦ y ⟧)) where
      ηIso→FHomEqu : isEquiv $ F . F-hom {x = x} {y = y}
      ηIso→FHomEqu = 2/3.ghEqu (F .F-hom) (compη x y) (Iso.fun $ adjIso x (F .F-ob y)) compose
        (isIsoToIsEquiv (composeWithIsoRisIso C (η ⟦ y ⟧) ηIsoy))
        (snd (isoToEquiv (adjIso x (F .F-ob y))))

  ηIso→FFullyFaithful : (ηIso : (c : C .ob) → isIso C (η ⟦ c ⟧ )) → isFullyFaithful F
  ηIso→FFullyFaithful ηIso x y = ηIso→FHomEqu x y (ηIso y)

module ImageFunctor
  {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) 
  where
  inImage : D .ob → hProp _
  inImage Y = ∥ Σ[ X ∈ C .ob ] F .F-ob X ≡ Y ∥₁ , squash₁

  ImageCat : Category _ _
  ImageCat = ΣPropCat* D inImage

  -- The corestriction of F to its image
  F|Image : Functor C ImageCat
  F|Image .F-ob X = F .F-ob X , ∣ X , refl ∣₁
  F|Image .F-hom  = F .F-hom
  F|Image .F-id   = F .F-id
  F|Image .F-seq  = F .F-seq

  F|ImageIsEssentiallySurjective : isEssentiallySurj F|Image
  F|ImageIsEssentiallySurjective (y , ∃xFx=y) =
    rec squash₁
      (λ (X , p) → ∣ X , pathToIso (Σ≡Prop (λ _ → squash₁) p) ∣₁)
      ∃xFx=y

module imageEquivalence
  {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) (G : Functor D C) (adj : F UnitCounit.⊣ G) where

  open UnitCounit._⊣_ adj
  open ImageFunctor F
  open adjunctionFact F G adj
  open isWeakEquivalence

  ηIso→F|ImageIsWeakEquivalence :
    (ηIso : (c : C .ob) → isIso C (η ⟦ c ⟧)) →
    isWeakEquivalence F|Image
  ηIso→F|ImageIsWeakEquivalence ηIso .fullfaith = ηIso→FFullyFaithful ηIso
  ηIso→F|ImageIsWeakEquivalence ηIso .esssurj   = F|ImageIsEssentiallySurjective
