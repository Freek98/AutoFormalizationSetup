{-# OPTIONS --cubical --guardedness #-}

module work.Part15 where

open import work.Part14 public

module ShapeTheoryFromCubical where
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Algebra.Group.Base
  open import Cubical.Algebra.Group.Morphisms
  open import Cubical.Algebra.Group.MorphismProperties
  open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
  open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup; UnitGroup₀)
  open import Cubical.HITs.S1 using (S¹; base; loop)
  open IntervalIsCHausModule using (UnitInterval)

  Unit-initial-STF : (G : Group ℓ-zero) → (φ : GroupHom UnitGroup₀ G) → (x : Unit) → fst φ x ≡ GroupStr.1g (snd G)
  Unit-initial-STF G (φ , is-hom) tt = IsGroupHom.pres1 is-hom

  Unit-terminal-STF : (G : Group ℓ-zero) → (φ : GroupHom G UnitGroup₀) → (x : fst G) → fst φ x ≡ tt
  Unit-terminal-STF G (φ , is-hom) x = refl

  no-group-retract-of-Unit-STF : (G : Group ℓ-zero)
    → (s : GroupHom UnitGroup₀ G)
    → (r : GroupHom G UnitGroup₀)
    → ((x : fst G) → fst s (fst r x) ≡ x)
    → (x : fst G) → x ≡ GroupStr.1g (snd G)
  no-group-retract-of-Unit-STF G s r sec x =
    x                        ≡⟨ sym (sec x) ⟩
    fst s (fst r x)          ≡⟨ cong (fst s) (Unit-terminal-STF G r x) ⟩
    fst s tt                 ≡⟨ Unit-initial-STF G s tt ⟩
    GroupStr.1g (snd G)      ∎

  private
    one-neq-zero-ℤ : pos 1 ≡ pos 0 → ⊥
    one-neq-zero-ℤ p = subst isPos p tt
      where
      isPos : ℤ → Type
      isPos (pos zero) = ⊥
      isPos (pos (suc n)) = Unit
      isPos (negsuc n) = ⊥

  ℤ-not-retract-of-Unit-STF : (s : GroupHom UnitGroup₀ ℤGroup)
    → (r : GroupHom ℤGroup UnitGroup₀)
    → ((n : ℤ) → fst s (fst r n) ≡ n)
    → ⊥
  ℤ-not-retract-of-Unit-STF s r sec =
    let all-zero = no-group-retract-of-Unit-STF ℤGroup s r sec
        one-is-zero : pos 1 ≡ pos 0
        one-is-zero = all-zero (pos 1)
    in one-neq-zero-ℤ one-is-zero

module ConnectednessForBoolILocal where
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Homotopy.Connected using (isConnected)
  open import Cubical.HITs.Truncation using (hLevelTrunc; ∣_∣ₕ; rec; elim)
  open IntervalIsCHausModule using (UnitInterval)

  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; rec)

  is-1-connected : Type ℓ-zero → Type ℓ-zero
  is-1-connected A = isContr ∥ A ∥₁

  postulate
    connected-1-to-set-constant-postulate : {A : Type ℓ-zero} {B : Type ℓ-zero}
      → is-1-connected A
      → isSet B
      → (f : A → B)
      → (x y : A) → f x ≡ f y

  connected-1-to-set-constant : {A : Type ℓ-zero} {B : Type ℓ-zero}
    → is-1-connected A
    → isSet B
    → (f : A → B)
    → (x y : A) → f x ≡ f y
  connected-1-to-set-constant = connected-1-to-set-constant-postulate

  open import Cubical.Data.Bool using (Bool; true; false; isSetBool)

module FundamentalGroupS1 where

  open import Cubical.HITs.S1.Base using (S¹; base; loop; ΩS¹; winding; intLoop;
                                          ΩS¹Isoℤ; windingℤLoop; decodeEncode;
                                          isSetΩS¹)
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; isoToPath)

  loop-winding-is-1 : winding loop ≡ pos 1
  loop-winding-is-1 = refl

  refl-winding-is-0 : winding refl ≡ pos 0
  refl-winding-is-0 = refl

  loop-neq-refl : loop ≡ refl → ⊥
  loop-neq-refl p = one-neq-zero (cong winding p)
    where
      one-neq-zero : pos 1 ≡ pos 0 → ⊥
      one-neq-zero q = subst isPos q tt
        where
          isPos : ℤ → Type
          isPos (pos zero) = ⊥
          isPos (pos (suc _)) = Unit
          isPos (negsuc _) = ⊥

  S¹-not-contractible : isContr S¹ → ⊥
  S¹-not-contractible (c , contr) = loop-neq-refl loop≡refl
    where
      base-to-c : base ≡ c
      base-to-c = sym (contr base)

      S¹-is-prop : isProp S¹
      S¹-is-prop = isContr→isProp (c , contr)

      loop≡refl : loop ≡ refl
      loop≡refl = isProp→isSet S¹-is-prop base base loop refl

  ΩS¹≃ℤ : ΩS¹ ≃ ℤ
  ΩS¹≃ℤ = isoToEquiv ΩS¹Isoℤ

module SimplyConnectedTypes where

  open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; rec)

  is-simply-connected : Type ℓ-zero → Type ℓ-zero
  is-simply-connected X = (x y : X) → ∥ x ≡ y ∥₁
                        × ((x : X) → isProp (x ≡ x))

  isContr→is-simply-connected : {X : Type ℓ-zero} → isContr X → is-simply-connected X
  isContr→is-simply-connected {X} (c , paths) x y = ∣ sym (paths x) ∙ paths y ∣₁ , loops-trivial
    where
    isPropX : isProp X
    isPropX = isContr→isProp (c , paths)
    isSetX : isSet X
    isSetX = isProp→isSet isPropX
    loops-trivial : (x₁ : X) → isProp (x₁ ≡ x₁)
    loops-trivial x₁ = isSetX x₁ x₁

module CohomologyFunctorialityTypeChecked where

  open import Cubical.ZCohomology.GroupStructure using (coHomGr; coHomFun; coHomMorph)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom)
  open import Cubical.Algebra.Group.MorphismProperties using (compGroupHomId)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂; isSetPathImplicit)

  coHom-functorial-comp : {A : Type ℓ-zero} {B : Type ℓ-zero} (n : ℕ)
    → (f : A → B) → (g : B → A)
    → ((a : A) → g (f a) ≡ a)
    → (x : fst (coHomGr n A))
    → fst (coHomMorph n f) (fst (coHomMorph n g) x) ≡ x
  coHom-functorial-comp n f g gf≡id =
    ST.elim (λ _ → isSetPathImplicit)
      (λ β → cong ∣_∣₂ (funExt λ a → cong β (gf≡id a)))

module CohomologyContractibleTypeChecked where

  open import Cubical.ZCohomology.Groups.Unit using (Hⁿ-contrType≅0)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupIso)
  open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup; UnitGroup₀)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.ZCohomology.Groups.Unit using (Hⁿ-Unit≅0)

  H¹-Unit≅0 : GroupIso {ℓ-zero} {ℓ-zero} (coHomGr 1 Unit) UnitGroup₀
  H¹-Unit≅0 = Hⁿ-Unit≅0 0

  H²-Unit≅0 : GroupIso {ℓ-zero} {ℓ-zero} (coHomGr 2 Unit) UnitGroup₀
  H²-Unit≅0 = Hⁿ-Unit≅0 1

module EMSpaceTypeChecked where
  open import Cubical.Algebra.AbGroup.Base using (AbGroup)
  open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; EM∙)
  open import Cubical.Homotopy.EilenbergMacLane.Properties using (EM≃ΩEM+1)
  open import Cubical.Foundations.Equiv using (_≃_)
  open import Cubical.Homotopy.Loopspace using (Ω)

  EM-loop-equiv-witness : (G : AbGroup ℓ-zero) (n : ℕ)
    → EM G n ≃ fst (Ω (EM∙ G (suc n)))
  EM-loop-equiv-witness G n = EM≃ΩEM+1 {G = G} n
