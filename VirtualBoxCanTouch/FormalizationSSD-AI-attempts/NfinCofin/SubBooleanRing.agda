{-# OPTIONS --cubical --guardedness #-}
module NfinCofin.SubBooleanRing where

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
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
open import Cubical.Tactics.CommRingSolver

private
  variable
    ℓ ℓ' : Level

------------------------------------------------------------------------
-- Sub-Monoid
------------------------------------------------------------------------

module SubMonoidConstr
  (M : Monoid ℓ) (P : ⟨ M ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (ε-cl : P (MonoidStr.ε (str M)))
  (·-cl : ∀ {x y} → P x → P y → P (MonoidStr._·_ (str M) x y))
  where

  private
    module S = MonoidStr (str M)
    eq : ∀ {a b : Σ ⟨ M ⟩ P} → fst a ≡ fst b → a ≡ b
    eq = Σ≡Prop isPropP

  subIsMonoid : IsMonoid (S.ε , ε-cl) (λ (x , px) (y , py) → x S.· y , ·-cl px py)
  subIsMonoid .IsMonoid.isSemigroup .IsSemigroup.is-set =
    isSetΣ S.is-set (λ x → isProp→isSet (isPropP x))
  subIsMonoid .IsMonoid.isSemigroup .IsSemigroup.·Assoc (x , _) (y , _) (z , _) =
    eq (S.·Assoc x y z)
  subIsMonoid .IsMonoid.·IdR (x , _) = eq (S.·IdR x)
  subIsMonoid .IsMonoid.·IdL (x , _) = eq (S.·IdL x)

  subMonoid : Monoid (ℓ-max ℓ ℓ')
  subMonoid .fst = Σ ⟨ M ⟩ P
  subMonoid .snd .MonoidStr.ε = S.ε , ε-cl
  subMonoid .snd .MonoidStr._·_ (x , px) (y , py) = x S.· y , ·-cl px py
  subMonoid .snd .MonoidStr.isMonoid = subIsMonoid


------------------------------------------------------------------------
-- Sub-Group  (factors through SubMonoid via Group→Monoid)
------------------------------------------------------------------------

module SubGroupConstr
  (G : Group ℓ) (P : ⟨ G ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (1g-cl  : P (GroupStr.1g (str G)))
  (·-cl   : ∀ {x y} → P x → P y → P (GroupStr._·_ (str G) x y))
  (inv-cl : ∀ {x} → P x → P (GroupStr.inv (str G) x))
  where

  private
    module S = GroupStr (str G)
    module SM = SubMonoidConstr (Group→Monoid G) P isPropP 1g-cl ·-cl
    eq : ∀ {a b : Σ ⟨ G ⟩ P} → fst a ≡ fst b → a ≡ b
    eq = Σ≡Prop isPropP

  subIsMonoid : IsMonoid _ _
  subIsMonoid = SM.subIsMonoid

  subIsGroup : IsGroup (S.1g , 1g-cl)
    (λ (x , px) (y , py) → x S.· y , ·-cl px py)
    (λ (x , px) → S.inv x , inv-cl px)
  subIsGroup .IsGroup.isMonoid = subIsMonoid
  subIsGroup .IsGroup.·InvR (x , _) = eq (S.·InvR x)
  subIsGroup .IsGroup.·InvL (x , _) = eq (S.·InvL x)

  subGroup : Group (ℓ-max ℓ ℓ')
  subGroup .fst = Σ ⟨ G ⟩ P
  subGroup .snd .GroupStr.1g = S.1g , 1g-cl
  subGroup .snd .GroupStr._·_ (x , px) (y , py) = x S.· y , ·-cl px py
  subGroup .snd .GroupStr.inv (x , px) = S.inv x , inv-cl px
  subGroup .snd .GroupStr.isGroup = subIsGroup


------------------------------------------------------------------------
-- Sub-AbGroup  (factors through SubGroup via AbGroup→Group)
------------------------------------------------------------------------

module SubAbGroupConstr
  (G : AbGroup ℓ) (P : ⟨ G ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (0g-cl  : P (AbGroupStr.0g (str G)))
  (+-cl   : ∀ {x y} → P x → P y → P (AbGroupStr._+_ (str G) x y))
  (neg-cl : ∀ {x} → P x → P (AbGroupStr.-_ (str G) x))
  where

  private
    module S = AbGroupStr (str G)
    module SG = SubGroupConstr (AbGroup→Group G) P isPropP 0g-cl +-cl neg-cl
    eq : ∀ {a b : Σ ⟨ G ⟩ P} → fst a ≡ fst b → a ≡ b
    eq = Σ≡Prop isPropP

  subIsGroup : IsGroup _ _ _
  subIsGroup = SG.subIsGroup

  subIsAbGroup : IsAbGroup (S.0g , 0g-cl)
    (λ (x , px) (y , py) → x S.+ y , +-cl px py)
    (λ (x , px) → S.- x , neg-cl px)
  subIsAbGroup .IsAbGroup.isGroup = subIsGroup
  subIsAbGroup .IsAbGroup.+Comm (x , _) (y , _) = eq (S.+Comm x y)

  subAbGroup : AbGroup (ℓ-max ℓ ℓ')
  subAbGroup .fst = Σ ⟨ G ⟩ P
  subAbGroup .snd .AbGroupStr.0g = S.0g , 0g-cl
  subAbGroup .snd .AbGroupStr._+_ (x , px) (y , py) = x S.+ y , +-cl px py
  subAbGroup .snd .AbGroupStr.-_ (x , px) = S.- x , neg-cl px
  subAbGroup .snd .AbGroupStr.isAbGroup = subIsAbGroup


------------------------------------------------------------------------
-- Sub-Ring  (factors through SubAbGroup for + and SubMonoid for ·)
------------------------------------------------------------------------

module SubRingConstr
  (R : Ring ℓ) (P : ⟨ R ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (0-cl   : P (RingStr.0r (str R)))
  (1-cl   : P (RingStr.1r (str R)))
  (+-cl   : ∀ {x y} → P x → P y → P (RingStr._+_ (str R) x y))
  (·-cl   : ∀ {x y} → P x → P y → P (RingStr._·_ (str R) x y))
  (neg-cl : ∀ {x} → P x → P (RingStr.-_ (str R) x))
  where

  private
    module S = RingStr (str R)
    module SAG = SubAbGroupConstr (Ring→AbGroup R) P isPropP 0-cl +-cl neg-cl
    module SM  = SubMonoidConstr (Ring→MultMonoid R) P isPropP 1-cl ·-cl
    eq : ∀ {a b : Σ ⟨ R ⟩ P} → fst a ≡ fst b → a ≡ b
    eq = Σ≡Prop isPropP

  subIsAbGroup : IsAbGroup _ _ _
  subIsAbGroup = SAG.subIsAbGroup

  subMultIsMonoid : IsMonoid _ _
  subMultIsMonoid = SM.subIsMonoid

  subIsRing : IsRing (S.0r , 0-cl) (S.1r , 1-cl)
    (λ (x , px) (y , py) → x S.+ y , +-cl px py)
    (λ (x , px) (y , py) → x S.· y , ·-cl px py)
    (λ (x , px) → S.- x , neg-cl px)
  subIsRing .IsRing.+IsAbGroup = subIsAbGroup
  subIsRing .IsRing.·IsMonoid  = subMultIsMonoid
  subIsRing .IsRing.·DistR+ (x , _) (y , _) (z , _) = eq (S.·DistR+ x y z)
  subIsRing .IsRing.·DistL+ (x , _) (y , _) (z , _) = eq (S.·DistL+ x y z)

  subRing : Ring (ℓ-max ℓ ℓ')
  subRing .fst = Σ ⟨ R ⟩ P
  subRing .snd .RingStr.0r = S.0r , 0-cl
  subRing .snd .RingStr.1r = S.1r , 1-cl
  subRing .snd .RingStr._+_ (x , px) (y , py) = x S.+ y , +-cl px py
  subRing .snd .RingStr._·_ (x , px) (y , py) = x S.· y , ·-cl px py
  subRing .snd .RingStr.-_ (x , px) = S.- x , neg-cl px
  subRing .snd .RingStr.isRing = subIsRing


------------------------------------------------------------------------
-- Sub-CommRing  (factors through SubRing via CommRing→Ring)
------------------------------------------------------------------------

module SubCommRingConstr
  (R : CommRing ℓ) (P : ⟨ R ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (0-cl   : P (CommRingStr.0r (str R)))
  (1-cl   : P (CommRingStr.1r (str R)))
  (+-cl   : ∀ {x y} → P x → P y → P (CommRingStr._+_ (str R) x y))
  (·-cl   : ∀ {x y} → P x → P y → P (CommRingStr._·_ (str R) x y))
  (neg-cl : ∀ {x} → P x → P (CommRingStr.-_ (str R) x))
  where

  private
    module S = CommRingStr (str R)
    module SR = SubRingConstr (CommRing→Ring R) P isPropP 0-cl 1-cl +-cl ·-cl neg-cl
    eq : ∀ {a b : Σ ⟨ R ⟩ P} → fst a ≡ fst b → a ≡ b
    eq = Σ≡Prop isPropP

  subIsRing : IsRing _ _ _ _ _
  subIsRing = SR.subIsRing

  subIsCommRing : IsCommRing (S.0r , 0-cl) (S.1r , 1-cl)
    (λ (x , px) (y , py) → x S.+ y , +-cl px py)
    (λ (x , px) (y , py) → x S.· y , ·-cl px py)
    (λ (x , px) → S.- x , neg-cl px)
  subIsCommRing .IsCommRing.isRing = subIsRing
  subIsCommRing .IsCommRing.·Comm (x , _) (y , _) = eq (S.·Comm x y)

  subCommRing : CommRing (ℓ-max ℓ ℓ')
  subCommRing .fst = Σ ⟨ R ⟩ P
  subCommRing .snd .CommRingStr.0r = S.0r , 0-cl
  subCommRing .snd .CommRingStr.1r = S.1r , 1-cl
  subCommRing .snd .CommRingStr._+_ (x , px) (y , py) = x S.+ y , +-cl px py
  subCommRing .snd .CommRingStr._·_ (x , px) (y , py) = x S.· y , ·-cl px py
  subCommRing .snd .CommRingStr.-_ (x , px) = S.- x , neg-cl px
  subCommRing .snd .CommRingStr.isCommRing = subIsCommRing


------------------------------------------------------------------------
-- Sub-BooleanRing  (factors through SubCommRing via BooleanRing→CommRing)
------------------------------------------------------------------------

module SubBoolRingConstr
  (B : BooleanRing ℓ) (P : ⟨ B ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (0-cl   : P (BooleanRingStr.𝟘 (str B)))
  (1-cl   : P (BooleanRingStr.𝟙 (str B)))
  (+-cl   : ∀ {x y} → P x → P y → P (BooleanRingStr._+_ (str B) x y))
  (·-cl   : ∀ {x y} → P x → P y → P (BooleanRingStr._·_ (str B) x y))
  (neg-cl : ∀ {x} → P x → P (BooleanRingStr.-_ (str B) x))
  where

  private
    module S = BooleanRingStr (str B)
    module SCR = SubCommRingConstr (BooleanRing→CommRing B) P isPropP 0-cl 1-cl +-cl ·-cl neg-cl
    eq : ∀ {a b : Σ ⟨ B ⟩ P} → fst a ≡ fst b → a ≡ b
    eq = Σ≡Prop isPropP

  subIsCommRing : IsCommRing _ _ _ _ _
  subIsCommRing = SCR.subIsCommRing

  subIsBooleanRing : IsBooleanRing (S.𝟘 , 0-cl) (S.𝟙 , 1-cl)
    (λ (x , px) (y , py) → x S.+ y , +-cl px py)
    (λ (x , px) (y , py) → x S.· y , ·-cl px py)
    (λ (x , px) → S.- x , neg-cl px)
  subIsBooleanRing .IsBooleanRing.isCommRing = subIsCommRing
  subIsBooleanRing .IsBooleanRing.·Idem (x , _) =
    eq (IsBooleanRing.·Idem S.isBooleanRing x)

  subBooleanRing : BooleanRing (ℓ-max ℓ ℓ')
  subBooleanRing .fst = Σ ⟨ B ⟩ P
  subBooleanRing .snd .BooleanRingStr.𝟘 = S.𝟘 , 0-cl
  subBooleanRing .snd .BooleanRingStr.𝟙 = S.𝟙 , 1-cl
  subBooleanRing .snd .BooleanRingStr._+_ (x , px) (y , py) = x S.+ y , +-cl px py
  subBooleanRing .snd .BooleanRingStr._·_ (x , px) (y , py) = x S.· y , ·-cl px py
  subBooleanRing .snd .BooleanRingStr.-_ (x , px) = S.- x , neg-cl px
  subBooleanRing .snd .BooleanRingStr.isBooleanRing = subIsBooleanRing


------------------------------------------------------------------------
-- Sub-BooleanRing via Boolean algebra operations (∧, ∨, ¬)
--
-- Often it is easier to prove closure under the Boolean algebra
-- operations than under the ring operations.  This module derives
-- ring closure from Boolean algebra closure.
------------------------------------------------------------------------

module SubBoolAlgConstr
  (B : BooleanRing ℓ) (P : ⟨ B ⟩ → Type ℓ') (isPropP : ∀ x → isProp (P x))
  (𝟘-cl : P (BooleanRingStr.𝟘 (str B)))
  (𝟙-cl : P (BooleanRingStr.𝟙 (str B)))
  (∧-cl : ∀ {x y} → P x → P y → P (BooleanAlgebraStr._∧_ B x y))
  (∨-cl : ∀ {x y} → P x → P y → P (BooleanAlgebraStr._∨_ B x y))
  (¬-cl : ∀ {x} → P x → P (BooleanAlgebraStr.¬_ B x))
  where

  private
    module S = BooleanRingStr (str B)
    module BA = BooleanAlgebraStr B
    open BA using (¬_ ; ¬Cancels∧R ; -IsId ; characteristic2)
    _∧ˡ_ = BA._∧_
    _∨ˡ_ = BA._∨_

    -- Key identity: x + y ≡ (x ∧ ¬ y) ∨ (¬ x ∧ y)
    +≡∧∨ : ∀ {x y : ⟨ B ⟩} → (x S.+ y) ≡ ((x ∧ˡ (¬ y)) ∨ˡ ((¬ x) ∧ˡ y))
    +≡∧∨ {x} {y} = sym (
      ((x ∧ˡ (¬ y)) ∨ˡ ((¬ x) ∧ˡ y))
        ≡⟨⟩
      ((x ∧ˡ (¬ y)) S.+ ((¬ x) ∧ˡ y)) S.+ ((x ∧ˡ (¬ y)) ∧ˡ ((¬ x) ∧ˡ y))
        ≡⟨ solve! (BooleanRing→CommRing B) ⟩
      ((x ∧ˡ (¬ y)) S.+ ((¬ x) ∧ˡ y)) S.+ ((x ∧ˡ (¬ x)) ∧ˡ ((¬ y) ∧ˡ y))
        ≡⟨ cong (λ b → ((x ∧ˡ (¬ y)) S.+ ((¬ x) ∧ˡ y)) S.+ (b ∧ˡ ((¬ y) ∧ˡ y))) ¬Cancels∧R ⟩
      ((x ∧ˡ (¬ y)) S.+ ((¬ x) ∧ˡ y)) S.+ (S.𝟘 ∧ˡ ((¬ y) ∧ˡ y))
        ≡⟨ solve! (BooleanRing→CommRing B) ⟩
      (x ∧ˡ (¬ y)) S.+ ((¬ x) ∧ˡ y)
        ≡⟨⟩
      (x ∧ˡ (S.𝟙 S.+ y)) S.+ ((S.𝟙 S.+ x) ∧ˡ y)
        ≡⟨ solve! (BooleanRing→CommRing B) ⟩
      (x S.+ (x S.· y)) S.+ (y S.+ x S.· y)
        ≡⟨ solve! (BooleanRing→CommRing B) ⟩
      (x S.+ y) S.+ (x S.· y S.+ x S.· y)
        ≡⟨ cong (λ b → (x S.+ y) S.+ b) characteristic2 ⟩
      (x S.+ y) S.+ S.𝟘
        ≡⟨ S.+IdR (x S.+ y) ⟩
      x S.+ y ∎)

    -- Derive ring closure from boolean algebra closure
    +-cl : ∀ {x y} → P x → P y → P (x S.+ y)
    +-cl {x} {y} px py = subst P (sym +≡∧∨)
      (∨-cl (∧-cl px (¬-cl py)) (∧-cl (¬-cl px) py))

    -- a · b = a ∧ b (definitionally)
    ·-cl : ∀ {x y} → P x → P y → P (x S.· y)
    ·-cl {x} {y} = ∧-cl {x} {y}

    -- In a Boolean ring, - x ≡ x
    neg-cl : ∀ {x} → P x → P (S.- x)
    neg-cl {x} px = subst P -IsId px

  open module R = SubBoolRingConstr B P isPropP 𝟘-cl 𝟙-cl +-cl ·-cl neg-cl public
