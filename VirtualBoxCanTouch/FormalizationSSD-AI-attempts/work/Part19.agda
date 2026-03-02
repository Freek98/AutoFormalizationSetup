{-# OPTIONS --cubical --guardedness #-}

module work.Part19 where

open import work.Part14 public

-- tex Remark after Lemma 3015: Stone spaces are I-local
module StoneILocalTC where
  open ZILocalModule using (Bool-I-local)
  open IntervalIsCHausModule using (UnitInterval)
  open import Cubical.Data.Bool using (Bool)
  open import Cubical.Algebra.CommRing.Base using (CommRingHom≡)

  funspace-I-local : {A : Type ℓ-zero} {B : Type ℓ-zero}
    → isSet A
    → ((f : UnitInterval → B) → (x y : UnitInterval) → f x ≡ f y)
    → (g : UnitInterval → (A → B))
    → (x y : UnitInterval) → g x ≡ g y
  funspace-I-local {A} {B} setA B-local g x y = funExt (λ a → B-local (λ i → g i a) x y)

  Stone-Sp-I-local : (B : Booleω) → (f : UnitInterval → Sp B)
    → (x y : UnitInterval) → f x ≡ f y
  Stone-Sp-I-local B f x y =
    CommRingHom≡ (funspace-I-local (BooleanRingStr.is-set (snd (fst B))) Bool-I-local
                   (λ i → fst (f i)) x y)

-- tex Lemma 3027: BZ is I-local
module BZILocalTC where
  open CohomologyModule using (BZ)
  open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)

  BZ-I-local : (f : UnitInterval → BZ) → (x y : UnitInterval) → f x ≡ f y
  BZ-I-local = ZILocalModule.contr-map-const-local isContrUnitInterval

-- tex Lemma 3035: continuously-path-connected-contractible
module PathConnectedContractibleTC where
  open IntervalIsCHausModule using (UnitInterval)
  open IntervalTopologyModule using (0I; 1I)

  ContinuousPath : {X : Type ℓ-zero} → X → X → Type ℓ-zero
  ContinuousPath {X} x y = Σ[ f ∈ (UnitInterval → X) ] (f 0I ≡ x) × (f 1I ≡ y)

  isContPathConnectedFrom : (X : Type ℓ-zero) → X → Type ℓ-zero
  isContPathConnectedFrom X x = (y : X) → ContinuousPath x y

  open import Cubical.Foundations.Function using (_∘_)

  -- tex Lemma 3035: If X is continuously path-connected from x₀ and Y is I-local,
  -- then any f : X → Y is constant (f(x) = f(x₀) for all x).
  path-connected→const : {X Y : Type ℓ-zero}
    → (x₀ : X)
    → isContPathConnectedFrom X x₀
    → ((g : UnitInterval → Y) → (a b : UnitInterval) → g a ≡ g b)
    → (f : X → Y) → (x : X) → f x ≡ f x₀
  path-connected→const {X} {Y} x₀ paths Y-I-local f x =
    let (h , h0≡x₀ , h1≡x) = paths x
        fh-const : f (h 1I) ≡ f (h 0I)
        fh-const = Y-I-local (f ∘ h) 1I 0I
    in f x
         ≡⟨ cong f (sym h1≡x) ⟩
       f (h 1I)
         ≡⟨ fh-const ⟩
       f (h 0I)
         ≡⟨ cong f h0≡x₀ ⟩
       f x₀ ∎

  -- Corollary: path-connected types have trivial functions to I-local targets
  -- (i.e., any f : X → Y with X path-connected and Y I-local is homotopic to const f(x₀))
  path-connected→I-contractible : {X Y : Type ℓ-zero}
    → (x₀ : X)
    → isContPathConnectedFrom X x₀
    → ((g : UnitInterval → Y) → (a b : UnitInterval) → g a ≡ g b)
    → (f : X → Y) → f ≡ (λ _ → f x₀)
  path-connected→I-contractible x₀ paths Y-loc f =
    funExt (λ x → path-connected→const x₀ paths Y-loc f x)

-- tex Theorem 475: ¬WLPO from Stone Duality
module NotWLPOTC where
  import WLPO as WLPOmod
  open CantorIsStoneModule
  open import Axioms.StoneDuality using (evaluationMap)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
  open import Cubical.Foundations.Equiv using (invEq; secEq)
  open import Cubical.Relation.Nullary using (yes; no)
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Algebra.CommRing using (_$cr_)

  SD-freeBA-ℕ : isEquiv (evaluationMap freeBA-ℕ-Booleω)
  SD-freeBA-ℕ = sd-axiom freeBA-ℕ-Booleω

  decPred→elem' : (Sp freeBA-ℕ-Booleω → Bool) → ⟨ freeBA ℕ ⟩
  decPred→elem' = invEq (_ , SD-freeBA-ℕ)

  decPred→elem-property' : (g : Sp freeBA-ℕ-Booleω → Bool) (h : Sp freeBA-ℕ-Booleω)
    → evaluationMap freeBA-ℕ-Booleω (decPred→elem' g) h ≡ g h
  decPred→elem-property' g h = funExt⁻ (secEq (_ , SD-freeBA-ℕ) g) h

  ¬WLPO : ¬ WLPO
  ¬WLPO wlpo = contradiction'
    where
    decide-fn : binarySequence → Bool
    decide-fn α with wlpo α
    ... | yes _ = false
    ... | no _ = true

    WLPOf : (α : binarySequence) → (decide-fn α ≡ false) ↔ ((n : ℕ) → α n ≡ false)
    WLPOf α = forward , backward
      where
      forward : decide-fn α ≡ false → (n : ℕ) → α n ≡ false
      forward fα=false with wlpo α
      ... | yes all-zero = all-zero
      ... | no _ = ex-falso (true≢false fα=false)

      backward : ((n : ℕ) → α n ≡ false) → decide-fn α ≡ false
      backward all-zero with wlpo α
      ... | yes _ = refl
      ... | no ¬all-zero = ex-falso (¬all-zero all-zero)

    elem-c : ⟨ freeBA ℕ ⟩
    elem-c = decPred→elem' (decide-fn ∘ Iso.fun Sp-freeBA-ℕ-Iso)

    SD-property : (α : binarySequence) → decide-fn α ≡ WLPOmod.evaluate α $cr elem-c
    SD-property α = sym (
      evaluationMap freeBA-ℕ-Booleω elem-c (Iso.inv Sp-freeBA-ℕ-Iso α)
        ≡⟨ decPred→elem-property' (decide-fn ∘ Iso.fun Sp-freeBA-ℕ-Iso) (Iso.inv Sp-freeBA-ℕ-Iso α) ⟩
      decide-fn (Iso.fun Sp-freeBA-ℕ-Iso (Iso.inv Sp-freeBA-ℕ-Iso α))
        ≡⟨ cong decide-fn (Iso.sec Sp-freeBA-ℕ-Iso α) ⟩
      decide-fn α ∎)

    open WLPOmod.PlayingWithWLPO' decide-fn WLPOf elem-c SD-property