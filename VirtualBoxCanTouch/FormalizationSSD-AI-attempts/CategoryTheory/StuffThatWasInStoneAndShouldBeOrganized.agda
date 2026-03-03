{-# OPTIONS --cubical --guardedness #-}
module CategoryTheory.StuffThatWasInStoneAndShouldBeOrganized where
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

open Category hiding (_∘_)
open Functor
open isUnivalent

module _ {ℓ ℓ' ℓ'' ℓ''' : Level} 
  (C : Category ℓ ℓ') (D : Category ℓ'' ℓ''') (Duniv : isUnivalent D) 
  (F : Functor C D) (FEmbedding : isEmbedding (F .F-ob)) 
  (FFullyFaithFul : isFullyFaithful F) where

--              univ
--     B = C ---------> B ≃ C
--       |                |
-- congF |                |  PreservesIso F 
--       |                |
--       v                v
--   F C = F C -----> F B ≃ F C
--              univ

  module _ (x y : C .ob) where
    Fembed'  : (x ≡ y) ≃ ((F .F-ob x) ≡ (F .F-ob y))
    Fembed'  = cong (F .F-ob) , FEmbedding x y 

    Duniv'   : ((F .F-ob x) ≡ (F .F-ob y)) ≃ (CatIso D (F .F-ob x) (F . F-ob y))
    Duniv'   = univEquiv Duniv (F .F-ob x) (F .F-ob y) 

    Fembed'' : CatIso C x y ≃ (CatIso D (F . F-ob x) (F . F-ob y)) 
    Fembed'' = isoToEquiv $ 
     IsoΣ (equivToIso (F .F-hom , FFullyFaithFul x y)) 
     (isIso C) (isIso D) isPropIsIso isPropIsIso 
     (λ f fIso → snd $ F-Iso {F = F}                (f , fIso)) 
     (λ f fIso → snd $ liftIso       {F = F} FFullyFaithFul (f , fIso))

    decompPathToIso : (x ≡ y) ≃ CatIso C x y
    decompPathToIso = compEquiv Fembed' (compEquiv Duniv' (invEquiv Fembed'')) 
    
    leftway : (x ≡ y) ≃ CatIso D (F .F-ob x) (F .F-ob y)
    leftway = compEquiv Fembed' Duniv' 
    
    rightwayMap : x ≡ y → CatIso D (F .F-ob x) (F .F-ob y)
    rightwayMap = F-Iso {F = F} ∘ pathToIso {C = C}  

  module _ (x : C .ob) where   
    leftway=rightway : (y : C .ob) → fst (leftway x y ) ≡ rightwayMap x y
    leftway=rightway y = funExt (J (λ y p → fst (leftway x y) p ≡ rightwayMap x y p) $
      fst (leftway x x) refl         ≡⟨ pathToIso-refl ⟩
      idCatIso                       ≡⟨ CatIso≡ _ _ (sym $ F .F-id) ⟩
      F-Iso {F = F} idCatIso ≡⟨ cong (F-Iso {F = F}) (sym pathToIso-refl) ⟩
      rightwayMap x x refl ∎ )
  
  Cuniv : isUnivalent C  
  Cuniv .univ x y = 2/3.fhEqu 
    (fst $ leftway x y) pathToIso (F-Iso {F = F}) 
    (sym $ leftway=rightway x y) 
    (snd $ leftway x y) (snd $ Fembed'' x y) 

    
{-
-- PvA: 
-- Bewijs dat voor functors tussen univalent categories ze fully faithful zijn iff hun object map een embedding is. 
--            
--           univ
--    B = C ---------> B ≃ C
--      |                |
--   Sp |                |  PreservesIso Sp --- NOTE LATER PreservesIso moet F-Iso zijn. 
--      |                |
--      v                v
--   Sp = Sp C ---> Sp B ≃ Sp C
--              univ
--
-- Bewijs dat PreservesIso Sp een equivalence is als Sp fully faithful. 
-- Idee hiervoor is dat isIso een propositie is, dus weer ΣEquiv gebruiken. 
--
--
--
-- Bewijs dat PreservesIso Sp fully faithful is met volgende driehoek: 
--
--              Sp.Hom 
--    B -> C =======> Sp B -> Sp C
--      \\            __ .
--   ∙∘η \\            // |
--        \\|         //  adjunctie
--        _\|        //
--            B -> 2^Sp C
--
-- for ∙ ∘ η, gebruik: 
--isEquiv[equivFunA≃B∘f]→isEquiv[f] : {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
--                 → (f : C → A) (A≃B : A ≃ B)
--                 → isEquiv (equivFun A≃B ∘ f)
--                 → isEquiv f
--
-- Bovenstaadnde gedaan, al moest dat laatste zelf voor de category versie. 
-- Probleem : BACat and BooleωCat zijn niet hetzelfde. 
-- Je kan naar Stone gaan. 
-}
module adjunctionFact 
  {ℓC ℓC' ℓD ℓD' : Level} {C : Category ℓC ℓC'} {D : Category ℓD ℓD'}
  (F : Functor C D) (G : Functor D C) (adj : F UnitCounit.⊣ G) where

  open UnitCounit._⊣_ adj

  adjIso : (c : C .ob) (d : D .ob) → Iso (C [ c , G .F-ob d ]) (D [ F .F-ob c , d ])
  adjIso c d = invIso $ adj→adj' F G adj .NaturalBijection._⊣_.adjIso {c} {d} 
  
  compη : (x y : C .ob) → (C [ x , y ]) → C [ x , (G ∘F F) ⟅ y ⟆ ]
  compη _ y f = f ⋆⟨ C ⟩ (η ⟦ y ⟧)

  module _ (x y : C .ob) where 
-- x → y -------> F x → F y
--  _⋆η \           / adjIso
--        x → G F y
    opaque
      compose : Iso.fun (adjIso x (F .F-ob y)) ∘ compη x y ≡ F .F-hom {x = x} {y = y}
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
      ηIso→FHomEqu = 2/3.ghEqu (F .F-hom) (compη x y) (Iso.fun $ adjIso x (F .F-ob y)) compose 
        (isIsoToIsEquiv (composeWithIsoRisIso C (η ⟦ y ⟧) ηIsoy)) 
        (snd (isoToEquiv (adjIso x (F .F-ob y)))) 
  
  module _ where
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

  module _ {ℓE ℓE' : Level} {E : Category ℓE ℓE'} 
    (H : Functor E C) (HfullyFaithful : isFullyFaithful H) 
    (ηIsoOnHImage : (e : E .ob) → isIso C (η ⟦ H ⟅ e ⟆ ⟧))  where
    
    ηIsoOnImageH→FHFullyFaithful : isFullyFaithful (F ∘F H)
    ηIsoOnImageH→FHFullyFaithful e f = 2/3.ghEqu 
      ((F ∘F H) .F-hom) (H .F-hom) (F .F-hom) refl (HfullyFaithful e f) 
      (ηIso→FHomEqu (H .F-ob e) (H .F-ob f) (ηIsoOnHImage f))

    open isIso 
    open NatIso
    ηIso : NatIso (𝟙⟨ C ⟩ ∘F H) ((G ∘F F) ∘F H) 
    ηIso .trans = η ∘ˡ H
    ηIso .nIso  = ηIsoOnHImage 

    ηInvIso : NatIso ((G ∘F F) ∘F H) (𝟙⟨ C ⟩ ∘F H)  
    ηInvIso = symNatIso ηIso 

    ηInv : NatTrans  ((G ∘F F) ∘F H) (𝟙⟨ C ⟩ ∘F H)  
    ηInv = ηInvIso .trans
    
    module morphAction {x y : E .ob} where 
      ηconjugation : (C [ (G ∘F F ∘F H) ⟅ x ⟆ , (G ∘F F ∘F H) ⟅ y ⟆ ]) → C [ H ⟅ x ⟆  , H ⟅ y ⟆ ]
      ηconjugation g = η ⟦ H ⟅ x ⟆ ⟧ ⋆⟨ C ⟩ g ⋆⟨ C ⟩ inv (ηIsoOnHImage y)

      ηconjugationInv : C [ H ⟅ x ⟆  , H ⟅ y ⟆ ] → C [ (G ∘F F ∘F H) ⟅ x ⟆ , (G ∘F F ∘F H) ⟅ y ⟆ ]
      ηconjugationInv g = inv (ηIsoOnHImage x) ⋆⟨ C ⟩ g ⋆⟨ C ⟩ η ⟦ H ⟅ y ⟆ ⟧

      ηconjugationIso : Iso (C [ (G ∘F F ∘F H) ⟅ x ⟆ , (G ∘F F ∘F H) ⟅ y ⟆ ]) (C [ H ⟅ x ⟆  , H ⟅ y ⟆ ])
      ηconjugationIso .Iso.fun      = ηconjugation
      ηconjugationIso .Iso.inv      = ηconjugationInv
      ηconjugationIso .Iso.sec g = 
        ηconjugation (ηconjugationInv g) 
          ≡⟨ solveCat! C ⟩ 
        (η ⟦ H ⟅ x ⟆ ⟧ ⋆⟨ C ⟩ inv (ηIsoOnHImage x)) ⋆⟨ C ⟩ 
        g ⋆⟨ C ⟩ 
        (η ⟦ H ⟅ y ⟆ ⟧ ⋆⟨ C ⟩ inv (ηIsoOnHImage y))
          ≡⟨ cong₂ (λ r s → r ⋆⟨ C ⟩ g ⋆⟨ C ⟩ s) (ret (ηIsoOnHImage x)) (ret (ηIsoOnHImage y)) ⟩ 
        C .id ⋆⟨ C ⟩ g ⋆⟨ C ⟩ C .id
          ≡⟨ C .⋆IdR _ ∙ C .⋆IdL _ ⟩ 
        g ∎
      ηconjugationIso .Iso.ret  g = 
        ηconjugationInv (ηconjugation g) 
          ≡⟨ solveCat! C ⟩ 
        (inv (ηIsoOnHImage x) ⋆⟨ C ⟩ η ⟦ H ⟅ x ⟆ ⟧) ⋆⟨ C ⟩ 
        g ⋆⟨ C ⟩ 
        (inv (ηIsoOnHImage y) ⋆⟨ C ⟩ η ⟦ H ⟅ y ⟆ ⟧)
          ≡⟨ cong₂ (λ r s → r ⋆⟨ C ⟩ g ⋆⟨ C ⟩ s) (sec (ηIsoOnHImage x)) (sec (ηIsoOnHImage y)) ⟩ 
        C .id ⋆⟨ C ⟩ g ⋆⟨ C ⟩ C .id 
          ≡⟨ C .⋆IdR _ ∙ C .⋆IdL _ ⟩
        g ∎

        -- this should be an inverse of (G ∘F F) .F-hom 
      --
      --ηconjugationcheck : {! !} ≡ (ηInv .NatTrans.N-ob)
      --ηconjugationcheck = {! !} 
  
      reflectBackIntoE : C [ H ⟅ x ⟆  , H ⟅ y ⟆ ] → E [ x , y ] 
      reflectBackIntoE = fst $ invEquiv (H .F-hom , HfullyFaithful x y)

      totalAction : D [ (F ∘F H) ⟅ x ⟆ , (F ∘F H) ⟅ y ⟆ ] → E [ x , y ]
      totalAction = (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom)
    
    module morphActionId {x : E .ob} where
      open morphAction
      ηconjugationId : ηconjugation (C .id) ≡ C .id
      ηconjugationId = 
        η ⟦ H ⟅ x ⟆ ⟧ ⋆⟨ C ⟩ (C .id) ⋆⟨ C ⟩ inv (ηIsoOnHImage x) 
          ≡⟨ cong (λ h →  h ⋆⟨ C ⟩ inv (ηIsoOnHImage x)) (C .⋆IdR (η ⟦ H ⟅ x ⟆ ⟧)) ⟩ 
        η ⟦ H ⟅ x ⟆ ⟧ ⋆⟨ C ⟩ inv (ηIsoOnHImage x) 
          ≡⟨ ret (ηIsoOnHImage x) ⟩ 
        C .id ∎  
      reflectBackIntoEId : reflectBackIntoE {x = x} (C .id) ≡ E .id
      reflectBackIntoEId = invEquivFact.knownInfo (H .F-hom , HfullyFaithful x x) (E .id) (C .id) (H .F-id) 

      totalActionId : totalAction {x = x} (D .id) ≡ E .id
      totalActionId =
        (reflectBackIntoE ∘ ηconjugation ∘ (G .F-hom)) (D .id) 
          ≡⟨ cong (reflectBackIntoE ∘ ηconjugation) (G .F-id) ⟩ 
        (reflectBackIntoE ∘ ηconjugation) (C .id) 
          ≡⟨ cong reflectBackIntoE ηconjugationId ⟩ 
        reflectBackIntoE (C .id) 
          ≡⟨ reflectBackIntoEId ⟩ 
        E .id ∎
    module morphActionSeq {x y z : E .ob} 
        where
      open morphAction 
      ηconjugationSeq : 
        (f : C [ (G ∘F F ∘F H) ⟅ x ⟆ , (G ∘F F ∘F H) ⟅ y ⟆ ]) 
        (g : C [ (G ∘F F ∘F H) ⟅ y ⟆ , (G ∘F F ∘F H) ⟅ z ⟆ ]) → 
        ηconjugation (f ⋆⟨ C ⟩ g) ≡ ((ηconjugation f) ⋆⟨ C ⟩ (ηconjugation g))
      ηconjugationSeq f g =
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩                          g) ⋆⟨ C ⟩ ηzInv
          ≡⟨ solveCat! C ⟩ 
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩      (C .id) ⋆⟨ C ⟩      g) ⋆⟨ C ⟩ ηzInv 
          ≡⟨ cong (λ h → 
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩        h ⋆⟨ C ⟩          g) ⋆⟨ C ⟩ ηzInv) 
          (sym (sec $ ηIsoOnHImage y)) 
           ⟩ 
        ηx ⋆⟨ C ⟩ (f ⋆⟨ C ⟩ (ηyInv ⋆⟨ C ⟩ ηy) ⋆⟨ C ⟩ g) ⋆⟨ C ⟩ ηzInv
          ≡⟨ solveCat! C ⟩
        (ηconjugation f) ⋆⟨ C ⟩ (ηconjugation g) 
          ∎ where
          ηx    = η ⟦ H ⟅ x ⟆ ⟧
          ηy    = η ⟦ H ⟅ y ⟆ ⟧
          ηyInv = inv (ηIsoOnHImage y)
          ηzInv = inv (ηIsoOnHImage z)

      reflectBackIntoESeq : 
        (f : C [ H ⟅ x ⟆  , H ⟅ y ⟆ ]) → 
        (g : C [ H ⟅ y ⟆  , H ⟅ z ⟆ ]) → 
        reflectBackIntoE (f ⋆⟨ C ⟩ g) ≡ 
        (reflectBackIntoE f ⋆⟨ E ⟩ reflectBackIntoE g)
      reflectBackIntoESeq f g = 
          invEquivFact.embedding (F-hom H , HfullyFaithful x z) _ _ $
            H ⟪ invHhom (f ⋆⟨ C ⟩ g) ⟫ 
              ≡⟨ lInvH ⟩ 
            f ⋆⟨ C ⟩ g
              ≡⟨ sym $ cong₂ (C ._⋆_) lInvH lInvH ⟩ 
            H ⟪ (invHhom f) ⟫ ⋆⟨ C ⟩ H ⟪ (invHhom g) ⟫
              ≡⟨ sym (H .F-seq (invHhom f) (invHhom g)) ⟩ 
            H ⟪ (invHhom f) ⋆⟨ E ⟩ (invHhom g) ⟫ ∎
            where
              HhomEqu : {x y : E .ob} → E [ x , y ] ≃ C [ H ⟅ x ⟆  , H ⟅ y ⟆ ] 
              HhomEqu {x = x} {y = y} = (H .F-hom , HfullyFaithful x y)
              invHhom : {x y : E .ob} → C [ H ⟅ x ⟆  , H ⟅ y ⟆ ] → E [ x , y ]
              invHhom = fst $ invEquiv HhomEqu
              lInvH   : {x y : E .ob} → {f : C [ H ⟅ x ⟆ , H ⟅ y ⟆ ]} → (H ⟪ invHhom f ⟫ ≡ f)
              lInvH {x = x} {y = y} {f = f} = cong (λ e → fst e f) (invEquiv-is-linv HhomEqu) 

      totalActionSeq : 
        (f : D [ (F ∘F H) ⟅ x ⟆ , (F ∘F H) ⟅ y ⟆ ]) → 
        (g : D [ (F ∘F H) ⟅ y ⟆ , (F ∘F H) ⟅ z ⟆ ]) → 
        totalAction (f ⋆⟨ D ⟩  g) ≡ totalAction f ⋆⟨ E ⟩ totalAction g
      totalActionSeq f g = 
        (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom) (f ⋆⟨ D ⟩ g) 
          ≡⟨ cong (reflectBackIntoE ∘ ηconjugation) (G .F-seq f g) ⟩ 
        (reflectBackIntoE ∘ ηconjugation) ( (G .F-hom f) ⋆⟨ C ⟩ (G .F-hom g) ) 
          ≡⟨ cong reflectBackIntoE (ηconjugationSeq _ _) ⟩ 
        (reflectBackIntoE) (((ηconjugation ∘ G .F-hom) f) ⋆⟨ C ⟩ (ηconjugation ∘ G .F-hom) g ) 
          ≡⟨ reflectBackIntoESeq _ _ ⟩ 
        (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom) f ⋆⟨ E ⟩ 
        (reflectBackIntoE ∘ ηconjugation ∘ G .F-hom) g  ∎

    restrictRightAdjoint : Functor (ImageFunctor.Image (F ∘F H)) E
    restrictRightAdjoint .F-ob e = e 
    restrictRightAdjoint .F-hom  = totalAction where
      open morphAction
    restrictRightAdjoint .F-id = totalActionId where
      open morphActionId 
    restrictRightAdjoint .F-seq = totalActionSeq where
      open morphActionSeq
    open UnitCounit
    open NatIso
    open NatTrans
    -- I want to do this for the case where the original adjunction is an isomorphism.
--    need : ImageFunctor.RestrictCodomain (F ∘F H) ⊣ restrictRightAdjoint
--    need ._⊣_.η .N-ob  e = {! !}
--    need ._⊣_.η .N-hom   = {! !}
--    need ._⊣_.ε = {! !}
--    need ._⊣_.triangleIdentities = {! !}

  ηIso→FFullyFaithful : (ηIso : (c : C .ob) → isIso C (η ⟦ c ⟧ )) → isFullyFaithful F
  ηIso→FFullyFaithful ηIso x y = ηIso→FHomEqu x y (ηIso y)
