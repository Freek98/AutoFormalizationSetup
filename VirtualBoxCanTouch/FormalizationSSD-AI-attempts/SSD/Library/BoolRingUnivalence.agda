{-# OPTIONS --cubical --guardedness #-}

module SSD.Library.BoolRingUnivalence where
{- 
-- Introduces the proper notions of morphisms and equivalences of Boolean rings. 
-- Uses Evan's cool technology to deduce univalence for this notion of equivalences. 
-- -}


open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.SIP

open import Cubical.Data.Sigma

open import Cubical.Displayed.Base
open import Cubical.Displayed.Auto
open import Cubical.Displayed.Record
open import Cubical.Displayed.Universe

open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing

open import Cubical.Reflection.RecordEquiv

open import Cubical.Foundations.Function
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Reflection.RecordEquiv
private
  variable
    ℓ  : Level
    ℓ' : Level

IsBoolRingHom : {A : Type ℓ} → {B : Type ℓ'} → (Astr : BooleanRingStr A) → 
                (f : A → B)   → (Bstr : BooleanRingStr B) → 
                Type _
IsBoolRingHom Astr f Bstr = IsCommRingHom (BooleanRingStr→CommRingStr Astr) 
                                        f (BooleanRingStr→CommRingStr Bstr)

IsBoolRingEquiv : {A : Type ℓ} → {B : Type ℓ'} → (Astr : BooleanRingStr A) → 
                  (e : A ≃ B)  → (Bstr : BooleanRingStr B) → 
                  Type _
IsBoolRingEquiv Astr e Bstr = 
  IsBoolRingHom Astr (fst e) Bstr

BoolRingEquiv : {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') → Type _
BoolRingEquiv A B = Σ[ e ∈ ⟨ A ⟩ ≃ ⟨ B ⟩ ] IsBoolRingEquiv (snd A) e (snd B)

unquoteDecl IsBooleanRingIsoΣ = declareRecordIsoΣ IsBooleanRingIsoΣ (quote IsBooleanRing)

isPropIsBooleanRing : {B : Type ℓ} → 
   {𝟘 𝟙 : B} {_+_ _·_ : B → B → B} { -_ : B → B} → 
   isProp (IsBooleanRing 𝟘 𝟙 _+_ _·_ -_)

isPropIsBooleanRing {B = B} {_·_ = _·h_} = isOfHLevelRetractFromIso 1 IsBooleanRingIsoΣ 
  (isPropΣ (isPropIsCommRing _ _ _ _ _) f) where 
    open CommRingStr 
    f : IsCommRing _ _ _ _·h_ _ → isProp ((x : B) → (x ·h x) ≡ x) 
    f isCR p q = funExt λ x → is-set CRstr (x ·h x) x (p x) (q x) where
      CRstr : CommRingStr B
      CRstr .0r  = _
      CRstr .1r  = _
      CRstr ._+_ = _
      CRstr ._·_ = _
      CRstr .-_  = _
      CRstr .isCommRing = isCR 

𝒮ᴰ-BooleanRing : DUARel (𝒮-Univ ℓ) BooleanRingStr ℓ
𝒮ᴰ-BooleanRing =
  𝒮ᴰ-Record (𝒮-Univ _) IsBoolRingEquiv
    (fields:
      data[  𝟘  ∣ null ∣ pres0 ]
      data[  𝟙  ∣ null ∣ pres1 ]
      data[ _+_ ∣ bin  ∣ pres+ ]
      data[ _·_ ∣ bin  ∣ pres· ]
      data[ -_  ∣ autoDUARel _ _ ∣ pres- ]
      prop[ isBooleanRing ∣ (λ _ _ → isPropIsBooleanRing) ])
 where
  open BooleanRingStr
  open IsCommRingHom
  
  null = autoDUARel (𝒮-Univ _) (λ a → a)
  bin  = autoDUARel (𝒮-Univ _) (λ a → a → a → a)

opaque 
  BoolRingPath : (R S : BooleanRing ℓ) → BoolRingEquiv R S ≃ (R ≡ S)
  BoolRingPath = ∫ 𝒮ᴰ-BooleanRing .UARel.ua
  
  BoolRingPathInvRefl≡Idfun : (B : BooleanRing ℓ) → fst (fst ((fst $ invEquiv $ BoolRingPath B B) refl)) ≡ idfun ⟨ B ⟩ 
  BoolRingPathInvRefl≡Idfun B = funExt transportRefl
  
  uaBoolRing : {A B : BooleanRing ℓ} → BoolRingEquiv A B → A ≡ B
  uaBoolRing {A = A} {B = B} = equivFun (BoolRingPath A B)


