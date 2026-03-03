{-# OPTIONS --cubical --guardedness #-}
module BooleanRing.SubBooleanRing where

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)

open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.BooleanRing
open import BooleanRing.AlgebraicFacts

private
  variable
    ℓ ℓ' : Level

-- Given any BooleanRing B and a propositional predicate P on its carrier,
-- if P is closed under 0, 1, +, ·, and -, then Σ ⟨ B ⟩ P is a BooleanRing.
-- Similar for the closure properties of Boolean algebras.

module SubBoolRing
  (B : BooleanRing ℓ)
  (P : ⟨ B ⟩ → Type ℓ')
  (isPropP : (x : ⟨ B ⟩) → isProp (P x))
  where

  open BooleanRingStr (snd B)
  A = ⟨ B ⟩
  SubType = Σ A P

  -- Closure conditions
  record IsSubBooleanRing : Type (ℓ-max ℓ ℓ') where
    field
      0-closed : P 𝟘
      1-closed : P 𝟙
      +-closed : {x y : A} → P x → P y → P (x + y)
      ·-closed : {x y : A} → P x → P y → P (x · y)
      neg-closed : {x : A} → P x → P (- x)

  module deriveBooleanRing (cls : IsSubBooleanRing) where
    open IsSubBooleanRing cls

    isSetSub : isSet SubType
    isSetSub = isSetΣ is-set (λ x → isProp→isSet (isPropP x))

    eq : {x y : SubType} → fst x ≡ fst y → x ≡ y
    eq = Σ≡Prop isPropP

    0s : SubType
    0s = 𝟘 , 0-closed

    1s : SubType
    1s = 𝟙 , 1-closed

    _+s_ : SubType → SubType → SubType
    (x , px) +s (y , py) = (x + y) , +-closed px py

    _·s_ : SubType → SubType → SubType
    (x , px) ·s (y , py) = (x · y) , ·-closed px py

    -s_ : SubType → SubType
    -s (x , px) = (- x) , neg-closed px

    +s-assoc : (x y z : SubType) → x +s (y +s z) ≡ (x +s y) +s z
    +s-assoc (x , _) (y , _) (z , _) = eq (+Assoc x y z)

    +s-idr : (x : SubType) → x +s 0s ≡ x
    +s-idr (x , _) = eq (+IdR x)

    +s-idl : (x : SubType) → 0s +s x ≡ x
    +s-idl (x , _) = eq (+IdL x)

    +s-invr : (x : SubType) → x +s (-s x) ≡ 0s
    +s-invr (x , _) = eq (+InvR x)

    +s-invl : (x : SubType) → (-s x) +s x ≡ 0s
    +s-invl (x , _) = eq (+InvL x)

    +s-comm : (x y : SubType) → x +s y ≡ y +s x
    +s-comm (x , _) (y , _) = eq (+Comm x y)

    ·s-assoc : (x y z : SubType) → x ·s (y ·s z) ≡ (x ·s y) ·s z
    ·s-assoc (x , _) (y , _) (z , _) = eq (·Assoc x y z)

    ·s-idr : (x : SubType) → x ·s 1s ≡ x
    ·s-idr (x , _) = eq (·IdR x)

    ·s-idl : (x : SubType) → 1s ·s x ≡ x
    ·s-idl (x , _) = eq (·IdL x)

    ·s-distrR+ : (x y z : SubType) → x ·s (y +s z) ≡ (x ·s y) +s (x ·s z)
    ·s-distrR+ (x , _) (y , _) (z , _) = eq (·DistR+ x y z)

    ·s-distrL+ : (x y z : SubType) → (x +s y) ·s z ≡ (x ·s z) +s (y ·s z)
    ·s-distrL+ (x , _) (y , _) (z , _) = eq (·DistL+ x y z)

    ·s-comm : (x y : SubType) → x ·s y ≡ y ·s x
    ·s-comm (x , _) (y , _) = eq (·Comm x y)

    ·s-idem : (x : SubType) → x ·s x ≡ x
    ·s-idem (x , _) = eq (IsBooleanRing.·Idem isBooleanRing x)

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

  subRing≡ : {x y : SubType} → fst x ≡ fst y → x ≡ y 
  subRing≡ = Σ≡Prop isPropP 


module SubBooleanAlgebra (B : BooleanRing ℓ) (P : ⟨ B ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x)) where 
  open BooleanRingStr (snd B)
  open BooleanAlgebraStr (snd B)
  record IsSubBooleanAlgebra : Type (ℓ-max ℓ ℓ') where
    field
      𝟘-cl : P 𝟘
      𝟙-cl : P 𝟙
      ∧-cl : ∀ {x y} → P x → P y → P (x ∧ y)
      ∨-cl : ∀ {x y} → P x → P y → P (x ∨ y)
      ¬-cl : ∀ {x} → P x → P (¬ x)
  module DeriveRingClosure (subAlgebraClosure : IsSubBooleanAlgebra) where
    open IsSubBooleanAlgebra subAlgebraClosure 
    +-cl : ∀ {x y} → P x → P y → P (x + y)
    +-cl px py = subst P (sym (+FromBooleanAlgebraStr B)) 
      (∨-cl (∧-cl px (¬-cl py)) (∧-cl (¬-cl px) py))
  
    ·-cl : ∀ {x y} → P x → P y → P (x · y)
    ·-cl = ∧-cl
  
    neg-cl : ∀ {x} → P x → P (- x)
    neg-cl px = subst P -IsId px

    open SubBoolRing
    open IsSubBooleanRing
  
    deriveRing-cl : IsSubBooleanRing B P isPropP
    deriveRing-cl .0-closed = 𝟘-cl
    deriveRing-cl .1-closed = 𝟙-cl
    deriveRing-cl .+-closed = +-cl
    deriveRing-cl .·-closed = ·-cl
    deriveRing-cl .neg-closed = neg-cl 
  
    subBooleanAlgebra : BooleanRing (ℓ-max ℓ ℓ')
    subBooleanAlgebra = deriveBooleanRing.subBooleanRing B P isPropP deriveRing-cl 
  

mkSubBooleanAlgebra : {B : BooleanRing ℓ} {P : ⟨ B ⟩ → Type ℓ'} {isPropP : ∀ x → isProp (P x)} → (SubBooleanAlgebra.IsSubBooleanAlgebra B P isPropP) → BooleanRing (ℓ-max ℓ ℓ') 
mkSubBooleanAlgebra {B = B} {P = P} {isPropP = isPropP} = SubBooleanAlgebra.DeriveRingClosure.subBooleanAlgebra B P isPropP 
