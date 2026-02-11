{-# OPTIONS --cubical --guardedness #-}

module work.Part12 where

open import work.Part11 public

import Cubical.Data.Sum as ⊎

module IntervalIsCHausModule where
  open CompactHausdorffModule
  open CantorIsStoneModule

  postulate
    UnitInterval : Type ℓ-zero
    isSetUnitInterval : isSet UnitInterval
    cs : CantorSpace → UnitInterval
    cs-surjective : (x : UnitInterval) → ∥ Σ[ α ∈ CantorSpace ] cs α ≡ x ∥₁
    IntervalIsCHaus : hasCHausStr UnitInterval

  IntervalCHaus : CHaus
  IntervalCHaus = UnitInterval , IntervalIsCHaus

  -- The unit interval [0,1] is contractible (tex Corollary 3047)
  postulate
    isContrUnitInterval : isContr UnitInterval

-- IntervalTopologyModule (tex 2614-2762)

module IntervalTopologyModule where
  open IntervalIsCHausModule

  postulate
    _≤I_ : UnitInterval → UnitInterval → Type ℓ-zero
    _<I_ : UnitInterval → UnitInterval → Type ℓ-zero
    ≤I-isProp : (x y : UnitInterval) → isProp (x ≤I y)
    <I-isProp : (x y : UnitInterval) → isProp (x <I y)
    0I : UnitInterval
    1I : UnitInterval

  <I-hProp : UnitInterval → UnitInterval → hProp ℓ-zero
  <I-hProp x y = (x <I y) , <I-isProp x y

  -- tex Remark 2610: x<y is an open proposition
  postulate
    <I-isOpen : (x y : UnitInterval) → isOpenProp (<I-hProp x y)

  -- tex Remark 2610: x≠y is equivalent to (x<y) ∨ (y<x)
  postulate
    ≠I-apartness : (x y : UnitInterval)
      → (x ≡ y → ⊥) ↔ ((x <I y) ⊎ (y <I x))

  postulate
    ≤I-antisym : (x y : UnitInterval) → x ≤I y → y ≤I x → x ≡ y
    ≤I-trans : (x y z : UnitInterval) → x ≤I y → y ≤I z → x ≤I z
    ≤I-refl : (x : UnitInterval) → x ≤I x
    <I-from-≤-≢ : (x y : UnitInterval) → x ≤I y → (x ≡ y → ⊥) → x <I y
    ≤-from-<I : (x y : UnitInterval) → x <I y → x ≤I y
    <I-asymmetric : (x y : UnitInterval) → x <I y → y <I x → ⊥

  -- tex Lemma 2614: Image of a decidable subset under cs is a finite union of closed intervals
  DecSubsetCantor : Type ℓ-zero
  DecSubsetCantor = CantorSpace → Bool

  FiniteClosedIntervals : ℕ → Type ℓ-zero
  FiniteClosedIntervals n = (i : Fin n) → UnitInterval × UnitInterval

  inFiniteClosedIntervals : (n : ℕ) → FiniteClosedIntervals n → UnitInterval → Type ℓ-zero
  inFiniteClosedIntervals n Is x = Σ[ i ∈ Fin n ] (fst (Is i) ≤I x) × (x ≤I snd (Is i))

  postulate
    -- tex Lemma 2614
    ImageDecidableClosedInterval : (D : DecSubsetCantor)
      → ∥ Σ[ n ∈ ℕ ] Σ[ Is ∈ FiniteClosedIntervals n ]
          ((x : UnitInterval) → (Σ[ α ∈ CantorSpace ] (D α ≡ true) × (cs α ≡ x))
                              ↔ inFiniteClosedIntervals n Is x) ∥₁

  -- tex Lemma 2673: Complement of finite union of closed intervals is finite union of open intervals
  FiniteOpenIntervals : ℕ → Type ℓ-zero
  FiniteOpenIntervals n = (i : Fin n) → UnitInterval × UnitInterval

  inFiniteOpenIntervals : (n : ℕ) → FiniteOpenIntervals n → UnitInterval → Type ℓ-zero
  inFiniteOpenIntervals n Is x = Σ[ i ∈ Fin n ] (fst (Is i) <I x) × (x <I snd (Is i))

  postulate
    -- tex Lemma 2673
    complementClosedIntervalOpenIntervals : (n : ℕ) → (Is : FiniteClosedIntervals n)
      → ∥ Σ[ m ∈ ℕ ] Σ[ Os ∈ FiniteOpenIntervals m ]
          ((x : UnitInterval) → (¬ inFiniteClosedIntervals n Is x)
                              ↔ inFiniteOpenIntervals m Os x) ∥₁

  -- tex Lemma 2729: Open sets in I have standard form
  postulate
    IntervalTopologyStandard : (U : UnitInterval → hProp ℓ-zero)
      → ((x : UnitInterval) → isOpenProp (U x))
      → ∥ Σ[ S ∈ (ℕ → UnitInterval × UnitInterval) ]
          ((x : UnitInterval) → fst (U x) ≡ ∥ Σ[ n ∈ ℕ ] x <I fst (S n) × snd (S n) <I x ∥₁) ∥₁

-- ZILocalModule (tex Lemma 3015)

module ZILocalModule where
  open IntervalIsCHausModule
  open IntervalTopologyModule
  open import Cubical.Data.Int using (ℤ)

  contr-map-const-local : {X : Type ℓ-zero} {Y : Type ℓ-zero} → isContr X → (f : X → Y)
                        → (x y : X) → f x ≡ f y
  contr-map-const-local contr f x y = cong f (sym (snd contr x) ∙ snd contr y)

  Z-I-local : (f : UnitInterval → ℤ) → (x y : UnitInterval) → f x ≡ f y
  Z-I-local = contr-map-const-local isContrUnitInterval

  -- tex Lemma 3015 corollary
  Bool-I-local : (f : UnitInterval → Bool) → (x y : UnitInterval) → f x ≡ f y
  Bool-I-local = contr-map-const-local isContrUnitInterval

-- IntermediateValueTheoremModule (tex Theorem ivt, lines 3082-3097)

module IntermediateValueTheoremModule where
  open IntervalIsCHausModule
  open IntervalTopologyModule
  open ZILocalModule
  open InhabitedClosedSubSpaceClosedCHausModule

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
    let f0≠y = no-sol 0I
        f0<y = <I-from-≤-≢ (f 0I) y f0≤y f0≠y
    in ex-falso (<I-asymmetric (f 0I) y f0<y y<f0)

  IVT-char-fun-at-1 : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → (no-sol : (x : UnitInterval) → (f x ≡ y → ⊥))
    → (y≤f1 : y ≤I f 1I)
    → IVT-char-fun f y no-sol 1I ≡ true
  IVT-char-fun-at-1 f y no-sol y≤f1 with cover-when-no-solution f y no-sol 1I
  ... | ⊎.inr _ = refl
  ... | ⊎.inl f1<y =
    let f1≠y = no-sol 1I
        y<f1 = <I-from-≤-≢ y (f 1I) y≤f1 (λ eq → f1≠y (sym eq))
    in ex-falso (<I-asymmetric y (f 1I) y<f1 f1<y)

  IVT-contradiction : (f : UnitInterval → UnitInterval) → (y : UnitInterval)
    → (no-sol : (x : UnitInterval) → (f x ≡ y → ⊥))
    → (f0≤y : f 0I ≤I y) → (y≤f1 : y ≤I f 1I)
    → ⊥
  IVT-contradiction f y no-sol f0≤y y≤f1 =
    let char = IVT-char-fun f y no-sol
    in false≢true (sym (IVT-char-fun-at-0 f y no-sol f0≤y)
                   ∙ Bool-I-local char 0I 1I
                   ∙ IVT-char-fun-at-1 f y no-sol y≤f1)

  -- The main theorem (tex Theorem 3082)
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

-- BrouwerFixedPointTheoremModule (tex Theorem, lines 3099-3111)
