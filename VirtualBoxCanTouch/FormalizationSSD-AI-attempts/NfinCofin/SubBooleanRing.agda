{-# OPTIONS --cubical --guardedness #-}
module NfinCofin.SubBooleanRing where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.BooleanRing

private
  variable
    ℓ ℓ' : Level

-- Given any BooleanRing B and a propositional predicate P on its carrier,
-- if P is closed under 0, 1, +, ·, and -, then Σ ⟨ B ⟩ P is a BooleanRing.

module SubBoolRing
  (B : BooleanRing ℓ)
  (P : ⟨ B ⟩ → Type ℓ')
  (isPropP : (x : ⟨ B ⟩) → isProp (P x))
  where

  private
    module S = BooleanRingStr (str B)
    A = ⟨ B ⟩
    SubType = Σ A P

  -- Closure conditions
  record IsSubBooleanRing : Type (ℓ-max ℓ ℓ') where
    field
      0-closed : P S.𝟘
      1-closed : P S.𝟙
      +-closed : {x y : A} → P x → P y → P (x S.+ y)
      ·-closed : {x y : A} → P x → P y → P (x S.· y)
      neg-closed : {x : A} → P x → P (S.- x)

  module MkSub (cls : IsSubBooleanRing) where
    open IsSubBooleanRing cls

    private
      isSetSub : isSet SubType
      isSetSub = isSetΣ S.is-set (λ x → isProp→isSet (isPropP x))

      eq : {x y : SubType} → fst x ≡ fst y → x ≡ y
      eq = Σ≡Prop isPropP

      0s : SubType
      0s = S.𝟘 , 0-closed

      1s : SubType
      1s = S.𝟙 , 1-closed

      _+s_ : SubType → SubType → SubType
      (x , px) +s (y , py) = (x S.+ y) , +-closed px py

      _·s_ : SubType → SubType → SubType
      (x , px) ·s (y , py) = (x S.· y) , ·-closed px py

      -s_ : SubType → SubType
      -s (x , px) = (S.- x) , neg-closed px

    -- Build up the algebraic hierarchy on Sub

    private
      +s-assoc : (x y z : SubType) → x +s (y +s z) ≡ (x +s y) +s z
      +s-assoc (x , _) (y , _) (z , _) = eq (S.+Assoc x y z)

      +s-idr : (x : SubType) → x +s 0s ≡ x
      +s-idr (x , _) = eq (S.+IdR x)

      +s-idl : (x : SubType) → 0s +s x ≡ x
      +s-idl (x , _) = eq (S.+IdL x)

      +s-invr : (x : SubType) → x +s (-s x) ≡ 0s
      +s-invr (x , _) = eq (S.+InvR x)

      +s-invl : (x : SubType) → (-s x) +s x ≡ 0s
      +s-invl (x , _) = eq (S.+InvL x)

      +s-comm : (x y : SubType) → x +s y ≡ y +s x
      +s-comm (x , _) (y , _) = eq (S.+Comm x y)

      ·s-assoc : (x y z : SubType) → x ·s (y ·s z) ≡ (x ·s y) ·s z
      ·s-assoc (x , _) (y , _) (z , _) = eq (S.·Assoc x y z)

      ·s-idr : (x : SubType) → x ·s 1s ≡ x
      ·s-idr (x , _) = eq (S.·IdR x)

      ·s-idl : (x : SubType) → 1s ·s x ≡ x
      ·s-idl (x , _) = eq (S.·IdL x)

      ·s-distrR+ : (x y z : SubType) → x ·s (y +s z) ≡ (x ·s y) +s (x ·s z)
      ·s-distrR+ (x , _) (y , _) (z , _) = eq (S.·DistR+ x y z)

      ·s-distrL+ : (x y z : SubType) → (x +s y) ·s z ≡ (x ·s z) +s (y ·s z)
      ·s-distrL+ (x , _) (y , _) (z , _) = eq (S.·DistL+ x y z)

      ·s-comm : (x y : SubType) → x ·s y ≡ y ·s x
      ·s-comm (x , _) (y , _) = eq (S.·Comm x y)

      ·s-idem : (x : SubType) → x ·s x ≡ x
      ·s-idem (x , _) = eq (IsBooleanRing.·Idem S.isBooleanRing x)

    -- The sub-BooleanRing
    subBooleanRing : BooleanRing (ℓ-max ℓ ℓ')
    subBooleanRing .fst = SubType
    subBooleanRing .snd .BooleanRingStr.𝟘 = 0s
    subBooleanRing .snd .BooleanRingStr.𝟙 = 1s
    subBooleanRing .snd .BooleanRingStr._+_ = _+s_
    subBooleanRing .snd .BooleanRingStr._·_ = _·s_
    subBooleanRing .snd .BooleanRingStr.-_ = -s_
    subBooleanRing .snd .BooleanRingStr.isBooleanRing .IsBooleanRing.isCommRing =
      makeIsCommRing isSetSub +s-assoc +s-idr +s-invr +s-comm ·s-assoc ·s-idr ·s-distrR+ ·s-comm
    subBooleanRing .snd .BooleanRingStr.isBooleanRing .IsBooleanRing.·Idem = ·s-idem
