{-# OPTIONS --cubical --guardedness #-}
module SSD.Library.StoneDuality where
--TODO check whether Voevodsky agrees with the name univalent category as 
--opposed to use precategory for the cubical category definition
--and category for the univalent version. 

-- Done: 2^ restricted as Functor Stone → Booleω (see 2^Restricted, Sp-AdjointEquivalence)
-- Done: Sp is embedding (see SpEmbedding)
--             - Stone agrees with the image of Booleω
--             - All of this in general version.
--             - Finish ¬ WLPO, MP
--              
--              check chech cohomology of our paper and Hugo
--  Also look what it means given finite approximation (coboundary, cocycle)
--  Look up cyclic cohomology
--  Felix' lecture notes on some German course (Thierry will send mail). 

--import Cat.Functor.Adjoint.Reflective
--Naim advised me to use --no-load-primitives
open import SSD.Library.PresentedBoole 
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

open import SSD.Library.Examples.Bool
open import SSD.Library.QuickFixes

open import SSD.Library.BoolRingUnivalence

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

open import SSD.Library.CategoryTheory.BasicFacts
open import SSD.Library.CategoryTheory.SigmaPropCat
open import SSD.Library.CategoryTheory.Image

open Category hiding (_∘_)
SpGeneralBooleanRing : {ℓ : Level} → BooleanRing ℓ → Type ℓ
SpGeneralBooleanRing B = BoolHom B BoolBR

Booleω : Type (ℓ-suc ℓ-zero)
Booleω = Σ[ B ∈ BooleanRing ℓ-zero ] ∥ has-Boole-ω' B ∥₁ 

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

BACat : Category (ℓ-suc ℓ-zero) (ℓ-zero)
BACat .ob                       = BooleanRing ℓ-zero
BACat .Hom[_,_]                 = BoolHom
BACat .id {x = B}               = idBoolHom B
BACat ._⋆_ f g                  = g ∘cr f
BACat .⋆IdL _                   = CommRingHom≡ refl
BACat .⋆IdR _                   = CommRingHom≡ refl
BACat .⋆Assoc _ _ _             = CommRingHom≡ refl
BACat .isSetHom {x = B} {y = C} = isSetBoolHom B C 

BooleωCat : Category (ℓ-suc ℓ-zero) ℓ-zero 
BooleωCat = ΣPropCat* BACat λ B → ∥ has-Boole-ω' B ∥₁ , squash₁

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
--  module _ {ℓP : Level} (P : C .ob → hProp ℓP) (ηIsoOnP : ((c : C .ob) → ⟨ P c ⟩ → ⟨ ηIsIso c ⟩)) where

  module _ {ℓE ℓE' : Level} {E : Category ℓE ℓE'} 
    (Hrest : Functor E ηIsoSubCat) (HfullyFaithful : isFullyFaithful Hrest) where
      

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

module _ (B C : BooleanRing ℓ-zero)  where
  open isIso
  -- Idea : show BACAT is Univalent 
  -- we need to show that the map B ≡ C → CatIso BooleωCat B C  induced by sending refl to IdIso
  -- is itself an equivalence. We will decompose it into BoolPath followed by the following:
  -- Then we show using J that this is indeed a decomposition, and thus the map is an equivalence
  -- I instead went for the same result for BooleanRing, and think that if C is univalent, 
  -- so is any full subcategory of C. 

  BAIso≅BAEquiv : Iso (CatIso BACat B C) (BooleanRingEquiv B C)
  BAIso≅BAEquiv .Iso.fun ((f , fHom) , fIso) .fst = isoToEquiv $ 
    iso f (fst $ inv fIso) (funExt⁻ $ cong fst $ sec fIso) (funExt⁻ $ cong fst $ ret fIso)
  BAIso≅BAEquiv .Iso.fun ((f , fHom) , fIso) .snd = fHom
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .fst .fst = f 
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .fst .snd = fHom
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .inv .fst = fst $ invEquiv (f , fEqu)
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .inv .snd = invIsHom B C (f , fHom) (IsoToIsIso (equivToIso (f , fEqu)))
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .sec = CommRingHom≡ $ cong fst (invEquiv-is-linv (f , fEqu))
  BAIso≅BAEquiv .Iso.inv ((f , fEqu) , fHom) .snd .ret = CommRingHom≡ $ cong fst (invEquiv-is-rinv (f , fEqu))
  BAIso≅BAEquiv .Iso.sec e = BooleanRingEquiv≡ B C _ e refl
  BAIso≅BAEquiv .Iso.ret  e = CatIso≡ _ e refl 
  
  pathToIsoDecomp : (B ≡ C) ≃ (CatIso BACat B C)
  pathToIsoDecomp = compEquiv (invEquiv $ BoolRingPath B C) (isoToEquiv (invIso BAIso≅BAEquiv)) 

pathToIsoDecompAtRefl : (B : BooleanRing ℓ-zero) → fst (pathToIsoDecomp B B) refl ≡ idCatIso
pathToIsoDecompAtRefl B = CatIso≡ _ _ (CommRingHom≡ (BoolRingPathInvRefl≡Idfun B)) 

pathToIsoDecompIsDecomp : (B C : BooleanRing ℓ-zero) → pathToIso {x = B} {y = C} ≡ fst (pathToIsoDecomp B C)
pathToIsoDecompIsDecomp B C = funExt $ 
  J (λ C' p → pathToIso {x = B} {y = C'} p ≡ fst (pathToIsoDecomp B C') p) 
  (pathToIso-refl ∙ (sym $ pathToIsoDecompAtRefl B)) 

BACatUnivalent : isUnivalent BACat
BACatUnivalent .univ B C = subst isEquiv (sym (pathToIsoDecompIsDecomp B C)) (snd $ pathToIsoDecomp B C) 

BooleωEmbedding : Functor BooleωCat BACat
BooleωEmbedding .F-ob      = fst
BooleωEmbedding .F-hom f   = f
BooleωEmbedding .F-id      = refl
BooleωEmbedding .F-seq _ _ = refl 

BooleωEmbeddingIsFullyFaithful : isFullyFaithful BooleωEmbedding
BooleωEmbeddingIsFullyFaithful B C .equiv-proof f .fst .fst           = f
BooleωEmbeddingIsFullyFaithful B C .equiv-proof f .fst .snd           = refl
BooleωEmbeddingIsFullyFaithful B C .equiv-proof f .snd (g , Embedg=f) = Σ≡Prop 
 (λ _ → isSetBoolHom (fst B) (fst C) _ f) $ sym Embedg=f

BooleωEmbeddingIsEmbedding : isEmbedding (BooleωEmbedding .F-ob)
BooleωEmbeddingIsEmbedding = snd (EmbeddingΣProp λ _ → squash₁)

BooleωUnivalent : isUnivalent BooleωCat 
BooleωUnivalent = Cuniv BooleωCat BACat BACatUnivalent BooleωEmbedding BooleωEmbeddingIsEmbedding
 BooleωEmbeddingIsFullyFaithful 

SpGeneralFunctor : Functor BACat ((SET ℓ-zero) ^op) 
SpGeneralFunctor .F-ob  B   = SpGeneralBooleanRing B , isSetBoolHom B BoolBR
SpGeneralFunctor .F-hom f g = g ∘cr f
SpGeneralFunctor .F-id      = funExt λ _ → CommRingHom≡ refl
SpGeneralFunctor .F-seq _ _ = funExt λ _ → CommRingHom≡ refl

ev : (B C : BooleanRing ℓ-zero ) → (b  : ⟨ B ⟩) → BoolHom B C → ⟨ C ⟩
ev B C b f = f $cr b 

evaluationMapGeneralBooleanRing : (B : BooleanRing ℓ-zero ) → (b  : ⟨ B ⟩) → SpGeneralBooleanRing B → Bool
evaluationMapGeneralBooleanRing B = ev B BoolBR

evaluationMap : (B : Booleω) → (b : ⟨ fst B ⟩) → Sp B → Bool
evaluationMap B = evaluationMapGeneralBooleanRing (fst B)

StoneDualityAxiom : Type (ℓ-suc ℓ-zero)
StoneDualityAxiom = (B : Booleω) → isEquiv (evaluationMap B)
  
BAstructOnDecidableSubsets : {ℓ : Level} → (S : Type ℓ) → BooleanRingStr (S → Bool)
BAstructOnDecidableSubsets S = pointWiseStructure S (λ _ → Bool) (λ _ → snd BoolBR) 

2^ : {ℓ : Level} → (S : Type ℓ) → BooleanRing ℓ
2^ S .fst = S → Bool
2^ S .snd = BAstructOnDecidableSubsets S 

module _ where
  open IsCommRingHom
  -- this, just as pointwisestructure, looks generizalable
  evaluationIsHom' : (B : BooleanRing ℓ-zero) → IsBoolRingHom (snd B) (evaluationMapGeneralBooleanRing B) 
    (snd $ 2^ (SpGeneralBooleanRing B))
  evaluationIsHom' B .pres0     = funExt λ f → pres0 (snd f)
  evaluationIsHom' B .pres1     = funExt λ f → pres1 (snd f)
  evaluationIsHom' B .pres+ x y = funExt λ f → pres+ (snd f) x y
  evaluationIsHom' B .pres· x y = funExt λ f → pres· (snd f) x y
  evaluationIsHom' B .pres- x   = funExt λ f → pres- (snd f) x 

  evaluationIsHom : (B : Booleω) → IsBoolRingHom (snd (fst B)) (evaluationMap B) (snd $ 2^ (Sp B))
  evaluationIsHom B = evaluationIsHom' (fst B)

  evaluationHomGeneralBooleanRing : (B : BooleanRing ℓ-zero) → BoolHom B (2^ (SpGeneralBooleanRing B))
  evaluationHomGeneralBooleanRing B .fst = evaluationMapGeneralBooleanRing B
  evaluationHomGeneralBooleanRing B .snd = evaluationIsHom' B 

  evaluationHom : (B : Booleω) → BoolHom (fst B) (2^ (Sp B))
  evaluationHom B = evaluationHomGeneralBooleanRing (fst B)

module SpDecAdjunction (B : BooleanRing ℓ-zero) (X : Set) where
  flipArgs : BoolHom B (2^ X) → X → ⟨ B ⟩ → Bool
  flipArgs f x b = (f $cr b) x 

  open IsCommRingHom
  flipArgsGivesHom : (f : BoolHom B (2^ X)) → (x : X) → IsBoolRingHom (snd B) (flipArgs f x) (snd BoolBR)
  flipArgsGivesHom f x .pres0     = cong (λ f → f x) (pres0 (snd f))
  flipArgsGivesHom f x .pres1     = cong (λ f → f x) (pres1 (snd f))
  flipArgsGivesHom f x .pres+ a b = cong (λ f → f x) (pres+ (snd f) a b)
  flipArgsGivesHom f x .pres· a b = cong (λ f → f x) (pres· (snd f) a b)
  flipArgsGivesHom f x .pres- a   = cong (λ f → f x) (pres- (snd f) a) 

  BoolHom→SetHom : (f : BoolHom B (2^ X)) → (x : X) → SpGeneralBooleanRing B
  BoolHom→SetHom f x = flipArgs f x , flipArgsGivesHom f x 

  flipArgsOtherDirection : (X → SpGeneralBooleanRing B) → ⟨ B ⟩ → X → Bool
  flipArgsOtherDirection f b x = f x $cr b 

  flipArgsOtherDirectionGivesHom : (f : (X → SpGeneralBooleanRing B)) → 
    IsBoolRingHom (snd B) (flipArgsOtherDirection f) (snd $ 2^ X)
  flipArgsOtherDirectionGivesHom f .pres0     = funExt λ x → pres0 (snd $ f x)
  flipArgsOtherDirectionGivesHom f .pres1     = funExt λ x → pres1 (snd $ f x)
  flipArgsOtherDirectionGivesHom f .pres+ a b = funExt λ x → pres+ (snd $ f x) a b
  flipArgsOtherDirectionGivesHom f .pres· a b = funExt λ x → pres· (snd $ f x) a b
  flipArgsOtherDirectionGivesHom f .pres- a   = funExt λ x → pres- (snd $ f x) a 

  SetHom→BoolHom : (X → SpGeneralBooleanRing B) → BoolHom B (2^ X)
  SetHom→BoolHom f = flipArgsOtherDirection f , flipArgsOtherDirectionGivesHom f

  adjunction : BoolHom B (2^ X) ≃ (X → SpGeneralBooleanRing B)
  adjunction .fst                          = BoolHom→SetHom 
  adjunction .snd .equiv-proof f .fst .fst = SetHom→BoolHom f
  adjunction .snd .equiv-proof f .fst .snd = funExt λ _ → CommRingHom≡ refl
  adjunction .snd .equiv-proof f .snd (g , flipArgsG≡f) = Σ≡Prop 
    (λ x → isSet→ (isSetSp B) (BoolHom→SetHom x) f) 
    (cong SetHom→BoolHom (sym flipArgsG≡f) ∙ CommRingHom≡ (funExt λ x → refl) ) 

2^Functor : Functor (SET ℓ-zero ^op) (BACat)
2^Functor .F-ob X = 2^ ⟨ X ⟩
2^Functor .F-hom f .fst g x = g (f x)
2^Functor .F-hom f .snd .IsCommRingHom.pres0     = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres1     = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres+ a b = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres· a b = refl
2^Functor .F-hom f .snd .IsCommRingHom.pres- a   = refl
2^Functor .F-id                     = CommRingHom≡ refl
2^Functor .F-seq f g                = CommRingHom≡ refl 

Sp⊣2^' : SpGeneralFunctor NaturalBijection.⊣ 2^Functor
Sp⊣2^' .NaturalBijection._⊣_.adjIso    {c = B} {d = X}  = invIso $ equivToIso $ SpDecAdjunction.adjunction B ⟨ X ⟩
Sp⊣2^' .NaturalBijection._⊣_.adjNatInD _ _              = CommRingHom≡ refl
Sp⊣2^' .NaturalBijection._⊣_.adjNatInC _ _ = funExt λ _ → CommRingHom≡ refl

Sp⊣2^ : SpGeneralFunctor UnitCounit.⊣ 2^Functor
Sp⊣2^ = adj'→adj _ _ Sp⊣2^' 

ηBA : 𝟙⟨ BACat ⟩ ⇒  2^Functor ∘F SpGeneralFunctor
ηBA = UnitCounit._⊣_.η Sp⊣2^ 

ηBA' : (B : BooleanRing ℓ-zero) → BoolHom B (2^ (SpGeneralBooleanRing B))
ηBA' B = NatTrans.N-ob ηBA B 

ηBA'Agrees : (B : BooleanRing ℓ-zero) → ηBA' B ≡ evaluationHomGeneralBooleanRing B
ηBA'Agrees B = CommRingHom≡ refl

ηBooleω' : 𝟙⟨ BACat ⟩ ∘F BooleωEmbedding ⇒  (2^Functor ∘F SpGeneralFunctor) ∘F BooleωEmbedding
ηBooleω' = ηBA ∘ˡ BooleωEmbedding 

ηBooleω : BooleωEmbedding ⇒ (2^Functor ∘F SpGeneralFunctor) ∘F BooleωEmbedding
ηBooleω = subst  (λ F → F ⇒ (2^Functor ∘F SpGeneralFunctor) ∘F BooleωEmbedding) F-rUnit ηBooleω' 

SpFunctor : Functor BooleωCat ((SET ℓ-zero) ^op)
SpFunctor = SpGeneralFunctor ∘F BooleωEmbedding

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

hasStoneStr : Type ℓ-zero → Type (ℓ-suc ℓ-zero) 
hasStoneStr S = Σ[ B ∈ Booleω ] Sp B ≡ S

module _ (SD : StoneDualityAxiom) where
  isPropHasStoneStr : (S : Set) → isProp (hasStoneStr S)
  isPropHasStoneStr S = isEmbedding→hasPropFibers (SpEmbedding SD) S 

Stone : Type (ℓ-suc ℓ-zero)
Stone = TypeWithStr ℓ-zero hasStoneStr

-- tex lines 371-392: Anti-equivalence of Booleω and Stone
-- StoneCat: objects are Booleω, morphisms are maps between spectra (Sp C → Sp B)
-- This is the category of Stone spaces with continuous maps.
module _ (SD : StoneDualityAxiom) where
  StoneCat : Category (ℓ-suc ℓ-zero) ℓ-zero
  StoneCat = ImageFunctor.Image SpFunctor

  SpRestricted : Functor BooleωCat StoneCat
  SpRestricted = ImageFunctor.RestrictCodomain SpFunctor

  -- tex lines 371-392: Anti-equivalence of Booleω and Stone
  open import Cubical.Categories.Equivalence.Base using (isEquivalence ; _≃ᶜ_)
  open import Cubical.Categories.Equivalence.Properties
    using (isFullyFaithful+isEquivF-ob→isEquiv)

  Sp-isEquivalence : isEquivalence SpRestricted
  Sp-isEquivalence =
    isFullyFaithful+isEquivF-ob→isEquiv {F = SpRestricted}
      (SpFullyFaithful SD) (idIsEquiv Booleω)

  Sp-AntiEquivalence : BooleωCat ≃ᶜ StoneCat
  Sp-AntiEquivalence ._≃ᶜ_.func = SpRestricted
  Sp-AntiEquivalence ._≃ᶜ_.isEquiv = Sp-isEquivalence

  -- tex lines 371-392: The inverse of the anti-equivalence is the 2^ functor
  -- 2^Restricted : StoneCat → BooleωCat
  -- On objects: identity (both categories have Booleω as objects)
  -- On morphisms (f : Sp C → Sp B): the unique BoolHom B C obtained by
  --   inverting SpFunctor.F-hom (which is an equivalence since Sp is fully faithful)
  -- This is the 2^ functor restricted to Stone spaces:
  --   given f : Sp C → Sp B, the corresponding BoolHom is obtained by
  --   conjugating 2^(f) : 2^(Sp B) → 2^(Sp C) with the evaluation isomorphism η

  private module AF = adjunctionFact SpGeneralFunctor 2^Functor Sp⊣2^

  -- The inverse functor via adjunctionFact.restrictRightAdjoint
  2^Restricted : Functor StoneCat BooleωCat
  2^Restricted = AF.restrictRightAdjoint BooleωEmbedding
    BooleωEmbeddingIsFullyFaithful (ηIsoOnBooleω SD)

  -- The adjoint equivalence between BooleωCat and StoneCat
  -- SpRestricted is identity on objects and fully faithful, so the
  -- unit and counit are both natural isomorphisms

  private
    SpFF = SpFullyFaithful SD

    -- Hom equivalences
    SpHomEquiv : (x y : Booleω) → BooleωCat [ x , y ] ≃ StoneCat [ x , y ]
    SpHomEquiv x y = SpFunctor .F-hom {x = x} {y = y} , SpFF x y

    -- The inverse of SpFunctor on morphisms
    SpHomInv : (x y : Booleω) → StoneCat [ x , y ] → BooleωCat [ x , y ]
    SpHomInv x y = invEq (SpHomEquiv x y)

  -- The inverse functor: 2^ restricted to Stone spaces
  -- On objects: identity. On morphisms: inverse of SpFunctor.F-hom.
  2^Restricted' : Functor StoneCat BooleωCat
  2^Restricted' .F-ob B = B
  2^Restricted' .F-hom {x = x} {y = y} = SpHomInv x y
  2^Restricted' .F-id {x = x} =
    cong (SpHomInv x x) (sym (SpFunctor .F-id {x = x}))
    ∙ retEq (SpHomEquiv x x) (BooleωCat .id {x = x})
  2^Restricted' .F-seq {x = x} {y = y} {z = z} f g =
    cong (SpHomInv x z) step ∙ retEq (SpHomEquiv x z) _
    where
      f' = SpHomInv x y f
      g' = SpHomInv y z g
      step : StoneCat ._⋆_ {x = x} {y = y} {z = z} f g ≡
             equivFun (SpHomEquiv x z) (BooleωCat ._⋆_ {x = x} {y = y} {z = z} f' g')
      step = sym (cong₂ (StoneCat ._⋆_ {x = x} {y = y} {z = z})
                    (secEq (SpHomEquiv x y) f)
                    (secEq (SpHomEquiv y z) g))
             ∙ sym (SpFunctor .F-seq {x = x} {y = y} {z = z} f' g')

  -- The unit and counit are both identity natural transformations
  -- since both SpRestricted and 2^Restricted' are identity on objects
  -- and their composition on morphisms is retEq/secEq

  private
    -- Naturality of η: f ⋆ η(y) ≡ η(x) ⋆ (2^R' ∘ Sp)(f)
    -- i.e., f ⋆ id ≡ id ⋆ Sp⁻¹(Sp(f))
    unitNat' : {x y : Booleω} (f : BooleωCat [ x , y ])
      → (BooleωCat ._⋆_ {x = x} {y = y} {z = y})
          (𝟙⟨ BooleωCat ⟩ .F-hom {x = x} {y = y} f) (BooleωCat .id {x = y}) ≡
        (BooleωCat ._⋆_ {x = x} {y = x} {z = y})
          (BooleωCat .id {x = x}) ((2^Restricted' ∘F SpRestricted) .F-hom {x = x} {y = y} f)
    unitNat' {x} {y} f =
      BooleωCat .⋆IdR {x = x} {y = y} _ ∙
      sym (retEq (SpHomEquiv x y) f) ∙
      sym (BooleωCat .⋆IdL {x = x} {y = y} _)

    -- Naturality of ε: (Sp ∘ 2^R') f ⋆ ε(y) ≡ ε(x) ⋆ f
    -- i.e., Sp(Sp⁻¹(f)) ⋆ id ≡ id ⋆ f
    counitNat' : {x y : Booleω} (f : StoneCat [ x , y ])
      → (StoneCat ._⋆_ {x = x} {y = y} {z = y})
          ((SpRestricted ∘F 2^Restricted') .F-hom {x = x} {y = y} f)
          (StoneCat .id {x = y}) ≡
        (StoneCat ._⋆_ {x = x} {y = x} {z = y})
          (StoneCat .id {x = x})
          (𝟙⟨ StoneCat ⟩ .F-hom {x = x} {y = y} f)
    counitNat' {x} {y} f =
      StoneCat .⋆IdR {x = x} {y = y}
        (SpFunctor .F-hom {x = x} {y = y} (SpHomInv x y f)) ∙
      secEq (SpHomEquiv x y) f ∙
      sym (StoneCat .⋆IdL {x = x} {y = y} f)

  open NatIso
  open NatTrans
  open isIso
  open UnitCounit.TriangleIdentities

  Sp-AdjointEquivalence : AdjointEquivalence BooleωCat StoneCat
  Sp-AdjointEquivalence .AdjointEquivalence.fun = SpRestricted
  Sp-AdjointEquivalence .AdjointEquivalence.inv = 2^Restricted'
  Sp-AdjointEquivalence .AdjointEquivalence.η .trans .N-ob  x =
    BooleωCat .id {x = x}
  Sp-AdjointEquivalence .AdjointEquivalence.η .trans .N-hom {x = x} {y = y} f =
    unitNat' {x = x} {y = y} f
  Sp-AdjointEquivalence .AdjointEquivalence.η .nIso x .inv =
    BooleωCat .id {x = x}
  Sp-AdjointEquivalence .AdjointEquivalence.η .nIso x .sec =
    BooleωCat .⋆IdL {x = x} {y = x} _
  Sp-AdjointEquivalence .AdjointEquivalence.η .nIso x .ret =
    BooleωCat .⋆IdL {x = x} {y = x} _
  Sp-AdjointEquivalence .AdjointEquivalence.ε .trans .N-ob x =
    StoneCat .id {x = x}
  Sp-AdjointEquivalence .AdjointEquivalence.ε .trans .N-hom {x = x} {y = y} f =
    counitNat' {x = x} {y = y} f
  Sp-AdjointEquivalence .AdjointEquivalence.ε .nIso x .inv =
    StoneCat .id {x = x}
  Sp-AdjointEquivalence .AdjointEquivalence.ε .nIso x .sec =
    StoneCat .⋆IdL {x = x} {y = x} _
  Sp-AdjointEquivalence .AdjointEquivalence.ε .nIso x .ret =
    StoneCat .⋆IdL {x = x} {y = x} _
  Sp-AdjointEquivalence .AdjointEquivalence.triangleIdentities .Δ₁ x =
    (StoneCat ._⋆_ {x = x} {y = x} {z = x})
      (SpRestricted .F-hom {x = x} {y = x} (BooleωCat .id {x = x}))
      (StoneCat .id {x = x})
      ≡⟨ StoneCat .⋆IdR {x = x} {y = x} _ ⟩
    SpRestricted .F-hom {x = x} {y = x} (BooleωCat .id {x = x})
      ≡⟨ SpRestricted .F-id {x = x} ⟩
    StoneCat .id {x = x} ∎
  Sp-AdjointEquivalence .AdjointEquivalence.triangleIdentities .Δ₂ x =
    (BooleωCat ._⋆_ {x = x} {y = x} {z = x})
      (BooleωCat .id {x = x})
      (2^Restricted' .F-hom {x = x} {y = x} (StoneCat .id {x = x}))
      ≡⟨ BooleωCat .⋆IdL {x = x} {y = x} _ ⟩
    2^Restricted' .F-hom {x = x} {y = x} (StoneCat .id {x = x})
      ≡⟨ 2^Restricted' .F-id {x = x} ⟩
    BooleωCat .id {x = x} ∎

  -- The inverse functor 2^Restricted' acts as the 2^ functor:
  -- Given f : Sp C → Sp B (morphism in StoneCat),
  -- 2^Restricted'.F-hom f is the unique BoolHom B C such that
  -- Sp(2^Restricted'.F-hom f) = f
  -- i.e., Sp ∘ 2^Restricted' = 𝟙 on StoneCat morphisms (secEq)
  -- and   2^Restricted' ∘ Sp = 𝟙 on BooleωCat morphisms (retEq)
