{-# OPTIONS --cubical --guardedness #-}
module BooleanRing.BooleanRingMaps where 

open import Cubical.Data.Sigma
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import BooleanRing.BoolRingUnivalence

module _ {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') where
  BooleanRingEquiv : Type (ℓ-max ℓ ℓ')
  BooleanRingEquiv = BoolRingEquiv A B 

isPropIsBoolRingHom : {ℓ ℓ' : Level} → {A : Type ℓ} {B : Type ℓ'} (R : BooleanRingStr A) (f : A → B) (S : BooleanRingStr B)
  → isProp (IsBoolRingHom R f S)
isPropIsBoolRingHom R f S = isPropIsCommRingHom (BooleanRingStr→CommRingStr R) f (BooleanRingStr→CommRingStr S) 
  
module _ { ℓ ℓ' : Level} (B : BooleanRing ℓ) (C : BooleanRing ℓ') (f g : BooleanRingEquiv B C) where
  BooleanRingEquiv≡ : (fst (fst f) ≡ fst (fst g)) → f ≡ g
  BooleanRingEquiv≡ p = Σ≡Prop (λ h → isPropIsBoolRingHom (snd B) (fst h) (snd C)) 
                        (Σ≡Prop isPropIsEquiv p) 

module _ {ℓ : Level} (B : BooleanRing ℓ) where
  open IsCommRingHom 
  idBoolHom : BoolHom B B
  idBoolHom .fst = idfun ⟨ B ⟩
  idBoolHom .snd .pres0     = refl
  idBoolHom .snd .pres1     = refl
  idBoolHom .snd .pres+ a b = refl
  idBoolHom .snd .pres· a b = refl
  idBoolHom .snd .pres- a   = refl 

  idFunGivesIdBoolHom : (f : BoolHom B B) → (fst f ≡ idfun ⟨ B ⟩) → f ≡ idBoolHom
  idFunGivesIdBoolHom f p = CommRingHom≡ p

  idBoolEquiv : BooleanRingEquiv B B
  idBoolEquiv .fst .fst = idfun ⟨ B ⟩
  idBoolEquiv .fst .snd = idIsEquiv ⟨ B ⟩ 
  idBoolEquiv .snd = snd idBoolHom 

  idFunGivesIdBoolEquiv : (f : BooleanRingEquiv B B ) → (fst (fst f) ≡ idfun ⟨ B ⟩) → f ≡ idBoolEquiv
  idFunGivesIdBoolEquiv f = BooleanRingEquiv≡ B B f idBoolEquiv 

module _ {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') (f : BooleanRingEquiv A B) where
  invBooleanRingEquiv : BooleanRingEquiv B A
  invBooleanRingEquiv = invCommRingEquiv (BooleanRing→CommRing A) (BooleanRing→CommRing B) f

  BooleanEquivToHom : BoolHom A B
  BooleanEquivToHom = fst (fst f) , snd f 

  BooleanEquivToHomInv : BoolHom B A
  BooleanEquivToHomInv = fst (fst invBooleanRingEquiv) , snd invBooleanRingEquiv 
  BooleanEquivLeftInv : BooleanEquivToHomInv ∘cr BooleanEquivToHom ≡ idBoolHom A
  BooleanEquivLeftInv = idFunGivesIdBoolHom A (BooleanEquivToHomInv ∘cr BooleanEquivToHom) 
     (funExt $ equivToIso (fst f) .Iso.ret) 
  
  BooleanEquivRightInv : BooleanEquivToHom ∘cr BooleanEquivToHomInv ≡ idBoolHom B
  BooleanEquivRightInv = idFunGivesIdBoolHom B (BooleanEquivToHom ∘cr BooleanEquivToHomInv) 
     (funExt $ equivToIso (fst f) .Iso.sec) 
