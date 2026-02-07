
{-# OPTIONS --cubical --guardedness #-}
module CategoryTheory.Adjunction where

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
open import Cubical.Foundations.Isomorphism renaming (Iso to RealIso ; isIso to isRealIso ; compIso to compRealIso ; invIso to invRealIso)
open import Cubical.Foundations.Equiv

open import Cubical.HITs.PropositionalTruncation as PT

open import QuickFixes
open import Cubical.Categories.Category.Base 
open import Cubical.Categories.Category 
open import Cubical.Categories.Functor 
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence.AdjointEquivalence hiding (adjunction)
open import Cubical.Categories.Isomorphism 
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Tactics.CategorySolver.Reflection

open import CategoryTheory.BasicFacts
open import CategoryTheory.Image
open import CategoryTheory.SigmaPropCat

open Category hiding (_∘_)
open Functor

module basicFacts {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'} 
  (adjointEquivalence : AdjointEquivalence C D) where
  open AdjointEquivalence adjointEquivalence
  funEquivalence : isEquivalence fun 
  funEquivalence = ∣ record { invFunc = inv ; η = η ; ε = ε } ∣₁ 
  invEquivalence : isEquivalence inv 
  invEquivalence = ∣ record { invFunc = fun ; η = symNatIso ε ; ε = symNatIso η } ∣₁ 
  

module adjunctionFact 
  {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) (G : Functor D C) (adj : F UnitCounit.⊣ G) where

  open UnitCounit._⊣_ adj

  adjIso : (c : C .ob) (d : D .ob) → RealIso (C [ c , G ⟅ d ⟆ ]) (D [ F ⟅ c ⟆ , d ])
  adjIso c d = invRealIso $ adj→adj' F G adj .NaturalBijection._⊣_.adjIso {c} {d} 
  
  compη : (x y : C .ob) → (C [ x , y ]) → C [ x , (G ∘F F) ⟅ y ⟆ ]
  compη _ y f = f ⋆⟨ C ⟩ (η ⟦ y ⟧)

  module _ (x y : C .ob) where 
-- x → y -------> F x → F y
--  _⋆η \           / adjIso
--        x → G F y
    opaque
      compose : RealIso.fun (adjIso x (F ⟅ y ⟆)) ∘ compη x y ≡ F .F-hom {x = x} {y = y}
      compose = funExt λ f →  
        F ⟪ f   ⋆⟨ C ⟩ (η ⟦ y ⟧)⟫      ⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧) 
          ≡⟨ cong (λ h → h ⋆⟨ D ⟩ _) (F .F-seq f (η ⟦ y ⟧)) ⟩ 
        F ⟪ f ⟫ ⋆⟨ D ⟩ F ⟪ η ⟦ y ⟧ ⟫   ⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧) 
          ≡⟨ D .⋆Assoc _ _ _ ⟩ 
        F ⟪ f ⟫ ⋆⟨ D ⟩ ((F ⟪ η ⟦ y ⟧ ⟫)⋆⟨ D ⟩ (ε ⟦ F ⟅ y ⟆ ⟧) )
          ≡⟨ cong (λ h → F ⟪ f ⟫ ⋆⟨ D ⟩ h) (Δ₁ y) ⟩ 
        F ⟪ f ⟫ ⋆⟨ D ⟩ D .id 
          ≡⟨ D .⋆IdR (F ⟪ f ⟫) ⟩ 
        F ⟪ f ⟫ ∎
    module _ (ηIsoy : isIso C (η ⟦ y ⟧)) where
      ηIso→FHomEqu : isEquiv $ F . F-hom {x = x} {y = y}
      ηIso→FHomEqu = 2/3.ghEqu (F .F-hom) (compη x y) (RealIso.fun $ adjIso x (F .F-ob y)) compose 
        (isIsoToIsEquiv (composeWithIsoRisIso C (η ⟦ y ⟧) ηIsoy)) 
        (snd (isoToEquiv (adjIso x (F .F-ob y)))) 

  ηIsIso : C . ob → hProp _
  ηIsIso c = isIso C (η ⟦ c ⟧) , isPropIsIso (η ⟦ c ⟧)

  εIsIso : D . ob → hProp _
  εIsIso d = isIso D (ε ⟦ d ⟧) , isPropIsIso (ε ⟦ d ⟧)

  Fpreserves : (c : C .ob) → ⟨ ηIsIso c ⟩ → ⟨ εIsIso (F ⟅ c ⟆) ⟩
  Fpreserves c ηcIso = isoUniqueness.SectionIsIsoToIsIso (Δ₁ c) (F-PresIsIso {F = F} ηcIso)
  
  Gpreserves : (d : D .ob) → ⟨ εIsIso d ⟩ → ⟨ ηIsIso (G ⟅ d ⟆) ⟩ 
  Gpreserves d εdIso = isoUniqueness.RetractionIsIsoToIsIso (Δ₂ d) (F-PresIsIso {F = G} εdIso) 

  ηIsoSubCat : Category _ _ 
  ηIsoSubCat = ΣPropCat* C ηIsIso

  εIsoSubCat  : Category _ _ 
  εIsoSubCat = ΣPropCat* D εIsIso
  
  open NatTrans
  open NatIso
  open UnitCounit.TriangleIdentities
  ηIso≃εIso : AdjointEquivalence ηIsoSubCat εIsoSubCat 
  ηIso≃εIso .AdjointEquivalence.fun = FrestrictedToPropCat εIsIso (F ∘F fstFunctor C ηIsIso) (uncurry Fpreserves)
  ηIso≃εIso .AdjointEquivalence.inv = FrestrictedToPropCat ηIsIso (G ∘F fstFunctor D εIsIso) (uncurry Gpreserves)
  ηIso≃εIso .AdjointEquivalence.η .trans .N-ob         (c , _)        = η ⟦ c ⟧
  ηIso≃εIso .AdjointEquivalence.ε .trans .N-ob         (d , _)        = ε ⟦ d ⟧
  ηIso≃εIso .AdjointEquivalence.η .trans .N-hom                       = η .N-hom
  ηIso≃εIso .AdjointEquivalence.ε .trans .N-hom                       = ε .N-hom
  ηIso≃εIso .AdjointEquivalence.η .nIso                (c , ηcIso)    = isIsoΣPropCat* C ηIsIso ηcIso 
  ηIso≃εIso .AdjointEquivalence.ε .nIso                (d , εdIso)    = isIsoΣPropCat* D εIsIso εdIso
  ηIso≃εIso .AdjointEquivalence.triangleIdentities .Δ₁ (c , _)        = Δ₁ triangleIdentities c
  ηIso≃εIso .AdjointEquivalence.triangleIdentities .Δ₂ (d , _)        = Δ₂ triangleIdentities d
 
  
  module _ {ℓS ℓS' : Level} {S : Category ℓS ℓS'} (H : Functor S ηIsoSubCat) (HfullyFaithful : isFullyFaithful H) where
    private
      F' = ηIso≃εIso .AdjointEquivalence.fun
      G' = ηIso≃εIso .AdjointEquivalence.inv

      G'isEquivalence : isEquivalence G'
      G'isEquivalence = basicFacts.invEquivalence ηIso≃εIso


    ηHIso : (x : S .ob) → CatIso ηIsoSubCat (H ⟅ x ⟆) ((G' ∘F F' ∘F H) ⟅ x ⟆) 
    ηHIso x .fst = η ⟦ fst $ H ⟅ x ⟆ ⟧ 
    ηHIso x .snd = isIsoΣPropCat* C ηIsIso (snd $ H ⟅ x ⟆)
    
    module morphAction {x y : S .ob} where 
      ηconjugationIso : RealIso 
        (ηIsoSubCat [ (G' ∘F F' ∘F H) ⟅ x ⟆ , (G' ∘F F' ∘F H) ⟅ y ⟆ ]) 
        (ηIsoSubCat [              H  ⟅ x ⟆ ,              H  ⟅ y ⟆ ])
      ηconjugationIso = compRealIso 
        (uncurry (composeWithIsoRIso ηIsoSubCat) (invIso (ηHIso y)) {z = (G' ∘F F' ∘F H) ⟅ x ⟆}) 
        (uncurry (composeWithIsoLIso ηIsoSubCat)         (ηHIso x)  {z =              H  ⟅ y ⟆}) 
      
      ηconjugation = RealIso.fun ηconjugationIso 
      
      reflectBackIntoE : ηIsoSubCat [ H ⟅ x ⟆  , H ⟅ y ⟆ ] → S [ x , y ] 
      reflectBackIntoE = fst $ invEquiv (H .F-hom , HfullyFaithful x y)

      totalAction : εIsoSubCat [ (F' ∘F H) ⟅ x ⟆ , (F' ∘F H) ⟅ y ⟆ ] → S [ x , y ]
      totalAction = (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom)
      
      totalActionEquiv : εIsoSubCat [ (F' ∘F H) ⟅ x ⟆ , (F' ∘F H) ⟅ y ⟆ ] ≃ S [ x , y ]
      totalActionEquiv = 
        G'HomEquiv  ∙ₑ ηconjugationEquiv ∙ₑ GhomEquiv  where 
          G'HomEquiv : εIsoSubCat [       (F' ∘F H) ⟅ x ⟆ ,       (F' ∘F H) ⟅ y ⟆ ] ≃ 
                       ηIsoSubCat [ (G' ∘F F' ∘F H) ⟅ x ⟆ , (G' ∘F F' ∘F H) ⟅ y ⟆ ] 
          G'HomEquiv .fst = G' .F-hom {x = (F' ∘F H) ⟅ x ⟆} {y = (F' ∘F H) ⟅ y ⟆}
          G'HomEquiv .snd = (isEquiv→FullyFaithful G'isEquivalence ((F' ∘F H) ⟅ x ⟆) ((F' ∘F H) ⟅ y ⟆)) 
          ηconjugationEquiv = isoToEquiv ηconjugationIso
          GhomEquiv = invEquiv (H .F-hom , HfullyFaithful x y)

    module morphActionId {x : S .ob} where
      open morphAction
      ηconjugationId : ηconjugation {x = x} (C .id) ≡ C .id
      ηconjugationId = ηconjugation (C .id) 
                         ≡⟨ solveCat! C ⟩
                       η ⟦ fst (H ⟅ x ⟆) ⟧ ⋆⟨ C ⟩ (snd (H ⟅ x ⟆) .isIso.inv)
                         ≡⟨ snd (H ⟅ x ⟆) .isIso.ret ⟩
                       C .id ∎

      reflectBackIntoEId : reflectBackIntoE {x = x} (C .id) ≡ S .id
      reflectBackIntoEId = invEquivFact.knownInfo (H .F-hom , HfullyFaithful x x) (S .id) (C .id) (H .F-id) 

      totalActionId : totalAction {x = x} (D .id) ≡ S .id
      totalActionId =
        (reflectBackIntoE ∘ ηconjugation ∘ (G .F-hom)) (D .id) 
          ≡⟨ cong (reflectBackIntoE ∘ ηconjugation) (G .F-id) ⟩ 
        (reflectBackIntoE ∘ ηconjugation) (C .id) 
          ≡⟨ cong reflectBackIntoE ηconjugationId ⟩ 
        reflectBackIntoE (C .id) 
          ≡⟨ reflectBackIntoEId ⟩ 
        S .id ∎
    module morphActionSeq {x y z : S .ob} 
        where
      open morphAction 
      ηconjugationSeq : 
        (f : ηIsoSubCat [ (G' ∘F F' ∘F H) ⟅ x ⟆ , (G' ∘F F' ∘F H) ⟅ y ⟆ ]) →
        (g : ηIsoSubCat [ (G' ∘F F' ∘F H) ⟅ y ⟆ , (G' ∘F F' ∘F H) ⟅ z ⟆ ]) → 
        ηconjugation (f ⋆⟨ C ⟩ g) ≡ ((ηconjugation f) ⋆⟨ C ⟩ (ηconjugation g))
      ηconjugationSeq f g = 
        ηx ⋆⟨ C ⟩ ((f ⋆⟨ C ⟩                          g) ⋆⟨ C ⟩ ηzInv)
          ≡⟨ solveCat! C ⟩ 
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩      (C .id) ⋆⟨ C ⟩      g) ⋆⟨ C ⟩ ηzInv 
          ≡⟨ cong (λ h → 
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩        h ⋆⟨ C ⟩          g) ⋆⟨ C ⟩ ηzInv) 
          (sym (sec $ snd $ H ⟅ y ⟆ )) 
           ⟩ 
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ (ηyInv ⋆⟨ C ⟩ ηy) ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ηzInv
          ≡⟨ solveCat! C ⟩
        (ηconjugation f) ⋆⟨ C ⟩ (ηconjugation g) 
          ∎ where
          open isIso 
          E = ηIsoSubCat
          ηx    = η ⟦ fst $ H ⟅ x ⟆ ⟧
          ηy    = η ⟦ fst $ H ⟅ y ⟆ ⟧
          ηyInv = inv (snd $ H ⟅ y ⟆)
          ηzInv = inv (snd $ H ⟅ z ⟆)

      reflectBackIntoESeq : 
        (f : ηIsoSubCat [ H ⟅ x ⟆  , H ⟅ y ⟆ ]) → 
        (g : ηIsoSubCat [ H ⟅ y ⟆  , H ⟅ z ⟆ ]) → 
        reflectBackIntoE (f ⋆⟨ C ⟩ g) ≡ 
        (reflectBackIntoE f ⋆⟨ S ⟩ reflectBackIntoE g)
      reflectBackIntoESeq f g = 
          invEquivFact.embedding (F-hom H , HfullyFaithful x z) _ _ $
            H ⟪ invHhom (f ⋆⟨ C ⟩ g) ⟫ 
              ≡⟨ lInvH ⟩ 
            f ⋆⟨ C ⟩ g
              ≡⟨ sym $ cong₂ (C ._⋆_) lInvH lInvH ⟩ 
            H ⟪ (invHhom f) ⟫ ⋆⟨ C ⟩ H ⟪ (invHhom g) ⟫
              ≡⟨ sym (H .F-seq (invHhom f) (invHhom g)) ⟩ 
            H ⟪ (invHhom f) ⋆⟨ S ⟩ (invHhom g) ⟫ ∎
            where
              HhomEqu : {x y : S .ob} → S [ x , y ] ≃ ηIsoSubCat [ H ⟅ x ⟆  , H ⟅ y ⟆ ] 
              HhomEqu {x = x} {y = y} = (H .F-hom , HfullyFaithful x y)
              invHhom : {x y : S .ob} → ηIsoSubCat [ H ⟅ x ⟆  , H ⟅ y ⟆ ] → S [ x , y ]
              invHhom = fst $ invEquiv HhomEqu
              lInvH   : {x y : S .ob} → {f : ηIsoSubCat [ H ⟅ x ⟆ , H ⟅ y ⟆ ]} → (H ⟪ invHhom f ⟫ ≡ f)
              lInvH {x = x} {y = y} {f = f} = cong (λ e → fst e f) (invEquiv-is-linv HhomEqu) 

      totalActionSeq : 
        (f : εIsoSubCat [ (F' ∘F H) ⟅ x ⟆ , (F' ∘F H) ⟅ y ⟆ ]) → 
        (g : εIsoSubCat [ (F' ∘F H) ⟅ y ⟆ , (F' ∘F H) ⟅ z ⟆ ]) → 
        totalAction (f ⋆⟨ D ⟩  g) ≡ totalAction f ⋆⟨ S ⟩ totalAction g
      totalActionSeq f g = 
        (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom) (f ⋆⟨ D ⟩ g) 
          ≡⟨ cong (reflectBackIntoE ∘ ηconjugation) (G .F-seq f g) ⟩ 
        (reflectBackIntoE ∘ ηconjugation) ( (G .F-hom f) ⋆⟨ C ⟩ (G .F-hom g) ) 
          ≡⟨ cong reflectBackIntoE (ηconjugationSeq _ _) ⟩ 
        (reflectBackIntoE) (((ηconjugation ∘ G .F-hom) f) ⋆⟨ C ⟩ (ηconjugation ∘ G .F-hom) g ) 
          ≡⟨ reflectBackIntoESeq _ _ ⟩ 
        (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom) f ⋆⟨ S ⟩ 
        (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom) g  ∎
    restrictRightAdjoint : Functor (ImageFunctor.Image (F' ∘F H)) S
    restrictRightAdjoint .F-ob e = e 
    restrictRightAdjoint .F-hom  = totalAction where
      open morphAction
    restrictRightAdjoint .F-id = totalActionId where
      open morphActionId 
    restrictRightAdjoint .F-seq = totalActionSeq where
      open morphActionSeq
    
    open AdjointEquivalence renaming (η to ηAdjEqu)
    open ImageFunctor
    restrictedAdjunction : AdjointEquivalence S $ Image (F' ∘F H)
    restrictedAdjunction .fun = RestrictCodomain (F' ∘F H)
    restrictedAdjunction .inv = restrictRightAdjoint
    restrictedAdjunction .ηAdjEqu .trans .N-ob x = reflectBackIntoE {! η ⟦ fst (H ⟅ x ⟆) ⟧ !} where
      open morphAction
    restrictedAdjunction .ηAdjEqu .trans .N-hom = {! !}
    restrictedAdjunction .ηAdjEqu .nIso = {! !}
    restrictedAdjunction .ε = {! !}
    restrictedAdjunction .triangleIdentities = {! !} 


