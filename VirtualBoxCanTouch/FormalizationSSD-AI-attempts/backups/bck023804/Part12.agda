{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)

module work.Part12 (fa : FoundationalAxioms) where

open import work.Part11 fa public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Bool using (Bool; true; false; false≢true; true≢false)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁; ∣_∣₁)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Data.Sum as ⊎
open ⊎ using (_⊎_)
open import Cubical.Data.Int using (ℤ)

record IntervalAxioms : Type (ℓ-suc ℓ-zero) where
  open CompactHausdorffModule
  open CantorIsStoneModule
  field
    UnitInterval : Type ℓ-zero
    isSetUnitInterval : isSet UnitInterval
    cs : CantorSpace → UnitInterval
    cs-surjective : (x : UnitInterval) → ∥ Σ[ α ∈ CantorSpace ] cs α ≡ x ∥₁
    IntervalIsCHaus : hasCHausStr UnitInterval
    isContrUnitInterval : isContr UnitInterval
    _≤I_ : UnitInterval → UnitInterval → Type ℓ-zero
    _<I_ : UnitInterval → UnitInterval → Type ℓ-zero
    ≤I-isProp : (x y : UnitInterval) → isProp (x ≤I y)
    <I-isProp : (x y : UnitInterval) → isProp (x <I y)
    0I : UnitInterval
    1I : UnitInterval
    <I-isOpen : (x y : UnitInterval) → isOpenProp ((x <I y) , <I-isProp x y)
    ≠I-apartness : (x y : UnitInterval)
      → (x ≡ y → ⊥) ↔ ((x <I y) ⊎ (y <I x))
    ≤I-antisym : (x y : UnitInterval) → x ≤I y → y ≤I x → x ≡ y
    ≤I-trans : (x y z : UnitInterval) → x ≤I y → y ≤I z → x ≤I z
    ≤I-refl : (x : UnitInterval) → x ≤I x
    <I-from-≤-≢ : (x y : UnitInterval) → x ≤I y → (x ≡ y → ⊥) → x <I y
    ≤-from-<I : (x y : UnitInterval) → x <I y → x ≤I y
    <I-asymmetric : (x y : UnitInterval) → x <I y → y <I x → ⊥

  DecSubsetCantor : Type ℓ-zero
  DecSubsetCantor = CantorSpace → Bool

  FiniteClosedIntervals : ℕ → Type ℓ-zero
  FiniteClosedIntervals n = (i : Fin n) → UnitInterval × UnitInterval

  inFiniteClosedIntervals : (n : ℕ) → FiniteClosedIntervals n → UnitInterval → Type ℓ-zero
  inFiniteClosedIntervals n Is x = Σ[ i ∈ Fin n ] (fst (Is i) ≤I x) × (x ≤I snd (Is i))

  FiniteOpenIntervals : ℕ → Type ℓ-zero
  FiniteOpenIntervals n = (i : Fin n) → UnitInterval × UnitInterval

  inFiniteOpenIntervals : (n : ℕ) → FiniteOpenIntervals n → UnitInterval → Type ℓ-zero
  inFiniteOpenIntervals n Is x = Σ[ i ∈ Fin n ] (fst (Is i) <I x) × (x <I snd (Is i))

  field
    ImageDecidableClosedInterval : (D : DecSubsetCantor)
      → ∥ Σ[ n ∈ ℕ ] Σ[ Is ∈ FiniteClosedIntervals n ]
          ((x : UnitInterval) → (Σ[ α ∈ CantorSpace ] (D α ≡ true) × (cs α ≡ x))
                              ↔ inFiniteClosedIntervals n Is x) ∥₁
    complementClosedIntervalOpenIntervals : (n : ℕ) → (Is : FiniteClosedIntervals n)
      → ∥ Σ[ m ∈ ℕ ] Σ[ Os ∈ FiniteOpenIntervals m ]
          ((x : UnitInterval) → (¬ inFiniteClosedIntervals n Is x)
                              ↔ inFiniteOpenIntervals m Os x) ∥₁
    IntervalTopologyStandard : (U : UnitInterval → hProp ℓ-zero)
      → ((x : UnitInterval) → isOpenProp (U x))
      → ∥ Σ[ S ∈ (ℕ → UnitInterval × UnitInterval) ]
          ((x : UnitInterval) → fst (U x) ≡ ∥ Σ[ n ∈ ℕ ] x <I fst (S n) × snd (S n) <I x ∥₁) ∥₁

module IntervalTheory (ia : IntervalAxioms) where
  open IntervalAxioms ia public
  open CompactHausdorffModule
  open CantorIsStoneModule
  open InhabitedClosedSubSpaceClosedCHausModule

  IntervalCHaus : CHaus
  IntervalCHaus = UnitInterval , IntervalIsCHaus

  contr-map-const-local : {X : Type ℓ-zero} {Y : Type ℓ-zero} → isContr X → (f : X → Y)
                        → (x y : X) → f x ≡ f y
  contr-map-const-local contr f x y = cong f (sym (snd contr x) ∙ snd contr y)

  open import Cubical.Data.Int using (ℤ)

  Z-I-local : (f : UnitInterval → ℤ) → (x y : UnitInterval) → f x ≡ f y
  Z-I-local = contr-map-const-local isContrUnitInterval

  Bool-I-local : (f : UnitInterval → Bool) → (x y : UnitInterval) → f x ≡ f y
  Bool-I-local = contr-map-const-local isContrUnitInterval

  U₀ : (f : UnitInterval → UnitInterval) → UnitInterval → UnitInterval → Type ℓ-zero
  U₀ f y x = f x <I y

  U₁ : (f : UnitInterval → UnitInterval) → UnitInterval → UnitInterval → Type ℓ-zero
  U₁ f y x = y <I f x

  cover-when-no-solution : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → ((x : UnitInterval) → (f x ≡ y → ⊥))
    → (x : UnitInterval) → U₀ f y x ⊎ U₁ f y x
  cover-when-no-solution f y no-sol x = fst (≠I-apartness (f x) y) (no-sol x)

  IVT-char-fun : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → ((x : UnitInterval) → (f x ≡ y → ⊥))
    → UnitInterval → Bool
  IVT-char-fun f y no-sol x with cover-when-no-solution f y no-sol x
  ... | ⊎.inl _ = false
  ... | ⊎.inr _ = true

  IVT-char-fun-at-0 : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → (no-sol : (x : UnitInterval) → (f x ≡ y → ⊥))
    → (f0≤y : f 0I ≤I y)
    → IVT-char-fun f y no-sol 0I ≡ false
  IVT-char-fun-at-0 f y no-sol f0≤y with cover-when-no-solution f y no-sol 0I
  ... | ⊎.inl _ = refl
  ... | ⊎.inr y<f0 =
    let f0<y = <I-from-≤-≢ (f 0I) y f0≤y (no-sol 0I)
    in ex-falso (<I-asymmetric (f 0I) y f0<y y<f0)

  IVT-char-fun-at-1 : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → (no-sol : (x : UnitInterval) → (f x ≡ y → ⊥))
    → (y≤f1 : y ≤I f 1I)
    → IVT-char-fun f y no-sol 1I ≡ true
  IVT-char-fun-at-1 f y no-sol y≤f1 with cover-when-no-solution f y no-sol 1I
  ... | ⊎.inr _ = refl
  ... | ⊎.inl f1<y =
    let y<f1 = <I-from-≤-≢ y (f 1I) y≤f1 (λ eq → no-sol 1I (sym eq))
    in ex-falso (<I-asymmetric y (f 1I) y<f1 f1<y)

  IVT-contradiction : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → (no-sol : (x : UnitInterval) → (f x ≡ y → ⊥))
    → (f0≤y : f 0I ≤I y) → (y≤f1 : y ≤I f 1I)
    → ⊥
  IVT-contradiction f y no-sol f0≤y y≤f1 = false≢true chain
    where
    char = IVT-char-fun f y no-sol
    chain : false ≡ true
    chain =
      false
        ≡⟨ sym (IVT-char-fun-at-0 f y no-sol f0≤y) ⟩
      char 0I
        ≡⟨ Bool-I-local char 0I 1I ⟩
      char 1I
        ≡⟨ IVT-char-fun-at-1 f y no-sol y≤f1 ⟩
      true ∎

  -- tex Theorem 3082
  IntermediateValueTheorem : (f : UnitInterval → UnitInterval)
    → (y : UnitInterval)
    → f 0I ≤I y → y ≤I f 1I
    → ∥ Σ[ x ∈ UnitInterval ] f x ≡ y ∥₁
  IntermediateValueTheorem f y f0≤y y≤f1 =
    let existence-prop : hProp ℓ-zero
        existence-prop = (∥ Σ[ x ∈ UnitInterval ] f x ≡ y ∥₁) , squash₁

        A : UnitInterval → hProp ℓ-zero
        A x = (f x ≡ y) , isSetUnitInterval (f x) y

        A-closed : (x : UnitInterval) → isClosedProp (A x)
        A-closed x = CompactHausdorffModule.hasCHausStr.equalityClosed IntervalIsCHaus (f x) y

        existence-closed : isClosedProp existence-prop
        existence-closed = InhabitedClosedSubSpaceClosedCHaus IntervalCHaus A A-closed

        ¬¬existence : ¬ ¬ ∥ Σ[ x ∈ UnitInterval ] f x ≡ y ∥₁
        ¬¬existence ¬∃ =
          let no-sol : (x : UnitInterval) → (f x ≡ y → ⊥)
              no-sol x fx=y = ¬∃ ∣ x , fx=y ∣₁
          in IVT-contradiction f y no-sol f0≤y y≤f1

    in closedIsStable existence-prop existence-closed ¬¬existence
