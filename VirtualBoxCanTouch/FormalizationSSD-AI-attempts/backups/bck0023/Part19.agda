{-# OPTIONS --cubical --guardedness #-}

module work.Part19 where

open import work.Part15 public

module PostulateStatusTC where
  -- These are foundational axioms from the tex file that define
  --     (tex Corollary 415: ¬¬Sp(B) ≃ ∥Sp(B)∥₁ for Booleω B)
  --     (actual statement would be isContr (L_I R), tex Corollary 3047)
  -- INTENTIONALLY PERMANENT: 4 postulates (fundamental axioms from tex)

module IntervalConnectednessDerivedTC where
  open ConnectednessForBoolILocal
  open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)
  open import Cubical.Data.Bool using (Bool; isSetBool)
  open import Cubical.Data.Int using (ℤ; isSetℤ)

  private
    contr-map-const : {X : Type₀} {Y : Type₀} → isContr X → (f : X → Y)
                    → (x y : X) → f x ≡ f y
    contr-map-const contr f x y = cong f (sym (snd contr x) ∙ snd contr y)

  -- Justification from tex (Lemma 3035 and surrounding):

  is-1-connected-I : is-1-connected UnitInterval
  is-1-connected-I = CohomologyModule.IntervalConnectedFromContr.is-1-connected-I-derived

  Bool-I-local-derived : (f : UnitInterval → Bool) → (x y : UnitInterval) → f x ≡ f y
  Bool-I-local-derived = contr-map-const isContrUnitInterval

  -- DERIVED: Z-I-local from contractibility (tex Lemma 3015, CHANGES0409)

  Z-I-local-derived : (f : UnitInterval → ℤ) → (x y : UnitInterval) → f x ≡ f y
  Z-I-local-derived = contr-map-const isContrUnitInterval

-- StoneILocalTC: Stone spaces are I-local (tex Remark after Lemma 3015)

module StoneILocalTC where
  open IntervalConnectednessDerivedTC using (Bool-I-local-derived; is-1-connected-I)
  open IntervalIsCHausModule using (UnitInterval)
  open import Axioms.StoneDuality using (Stone; hasStoneStr; SpGeneralBooleanRing)
  open import Cubical.Data.Bool using (Bool; isSetBool)
  open import Cubical.Algebra.CommRing.Base using (CommRingHom≡)

  funspace-I-local : {A : Type ℓ-zero} {B : Type ℓ-zero}
    → isSet A
    → ((f : UnitInterval → B) → (x y : UnitInterval) → f x ≡ f y)
    → (g : UnitInterval → (A → B))
    → (x y : UnitInterval) → g x ≡ g y
  funspace-I-local {A} {B} setA B-local g x y = funExt pointwise
    where
    pointwise : (a : A) → g x a ≡ g y a
    pointwise a = B-local (λ i → g i a) x y

  fun-to-Bool-I-local : {X : Type ℓ-zero}
    → isSet X
    → (g : UnitInterval → (X → Bool))
    → (x y : UnitInterval) → g x ≡ g y
  fun-to-Bool-I-local setX = funspace-I-local setX Bool-I-local-derived

  Sp-to-fun : (B : Booleω) → Sp B → (⟨ fst B ⟩ → Bool)
  Sp-to-fun B h = fst h

  Stone-Sp-I-local : (B : Booleω) → (f : UnitInterval → Sp B)
    → (x y : UnitInterval) → f x ≡ f y
  Stone-Sp-I-local B f x y = goal
    where
    B-is-set : isSet ⟨ fst B ⟩
    B-is-set = BooleanRingStr.is-set (snd (fst B))

    g : UnitInterval → (⟨ fst B ⟩ → Bool)
    g i = Sp-to-fun B (f i)

    g-const : g x ≡ g y
    g-const = fun-to-Bool-I-local B-is-set g x y

    goal : f x ≡ f y
    goal = CommRingHom≡ g-const

  -- SUMMARY (tex Remark after Lemma 3015)

-- tex Lemma 3027: BZ is I-local

module BZILocalTC where
  -- TEX LEMMA 3027: "Bℤ is I-local."
  -- PROOF STRUCTURE (from tex):

  open IntervalConnectednessDerivedTC using (Z-I-local-derived)
  open CohomologyModule using (BZ; BZ∙; bz₀; isOfHLevel-BZ; H¹; interval-cohomology-vanishes)
  open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)

  open import Cubical.Data.Int using (ℤ)
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Foundations.Equiv using (invEq; retEq; secEq)

  ℤ-I-local-from-derived : (f : UnitInterval → ℤ) → (x y : UnitInterval) → f x ≡ f y
  ℤ-I-local-from-derived = Z-I-local-derived

  open import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp
    using (EM≃ΩEM+1; ΩEM+1→EM; EM→ΩEM+1)
  open import Cubical.Data.Int.Properties using (isSetℤ)
  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)

  ΩBZ≃ℤ : (bz₀ ≡ bz₀) ≃ ℤ
  ΩBZ≃ℤ = invEquiv (EM≃ΩEM+1 {G = ℤAbGroup} 0)

  path-to-int : bz₀ ≡ bz₀ → ℤ
  path-to-int = fst ΩBZ≃ℤ

  int-to-path : ℤ → bz₀ ≡ bz₀
  int-to-path = invEq ΩBZ≃ℤ

  paths-at-bz₀-I-local : (g : UnitInterval → (bz₀ ≡ bz₀)) → (x y : UnitInterval) → g x ≡ g y
  paths-at-bz₀-I-local g x y = path-eq
    where
    g' : UnitInterval → ℤ
    g' i = path-to-int (g i)

    g'-const : g' x ≡ g' y
    g'-const = ℤ-I-local-from-derived g' x y

    path-eq : g x ≡ g y
    path-eq = sym (retEq ΩBZ≃ℤ (g x)) ∙ cong int-to-path g'-const ∙ retEq ΩBZ≃ℤ (g y)

  contr-map-const : {X : Type₀} {Y : Type₀} → isContr X → (f : X → Y)
                  → (x y : X) → f x ≡ f y
  contr-map-const contr f x y = cong f (sym (snd contr x) ∙ snd contr y)

  BZ-I-local : (f : UnitInterval → BZ) → (x y : UnitInterval) → f x ≡ f y
  BZ-I-local = contr-map-const isContrUnitInterval

  -- SUMMARY (tex Lemma 3027)
  -- OUR DERIVATION is much simpler than the tex proof:
  -- The tex proof uses H¹(I,ℤ) = 0 to show maps I → BZ are null-homotopic.
  -- - tex Lemma 3035 (continuously-path-connected-contractible)
  -- - tex Proposition 3051 (shape of S¹ is BZ)

-- tex Lemma 3035: continuously-path-connected-contractible

module PathConnectedContractibleTC where
  -- This module documents tex Lemma 3035:

  open IntervalIsCHausModule using (UnitInterval)
  open IntervalTopologyModule using (0I; 1I)

  -- TEX PROOF STRUCTURE (Lemma 3035)

  ContinuousPath : {X : Type ℓ-zero} → X → X → Type ℓ-zero
  ContinuousPath {X} x y = Σ[ f ∈ (UnitInterval → X) ] (f 0I ≡ x) × (f 1I ≡ y)

  isContPathConnectedFrom : (X : Type ℓ-zero) → X → Type ℓ-zero
  isContPathConnectedFrom X x = (y : X) → ContinuousPath x y

  -- SUMMARY (tex Lemma 3035)
  -- 3. The shape computation for S¹ = R/Z (tex Proposition 3051)
  -- Combined with BZ-I-local (tex Lemma 3027), this gives the tools

-- NotWLPOTC: ¬WLPO from Stone Duality (tex Theorem NotWLPO, line 475)

module NotWLPOTC where
  import WLPO as WLPOmod
  open CantorIsStoneModule
  open import Axioms.StoneDuality using (evaluationMap; SDHomVersion)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
  open import Cubical.Foundations.Equiv using (invEq; secEq)
  open import Cubical.Relation.Nullary using (Dec; yes; no)
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
    ... | yes _ = false  -- all zeros → false
    ... | no _ = true    -- not all zeros → true

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
      WLPOmod.evaluate α $cr elem-c
        ≡⟨ refl ⟩  -- by def of evaluationMap
      evaluationMap freeBA-ℕ-Booleω elem-c (WLPOmod.evaluate α)
        ≡⟨ cong (evaluationMap freeBA-ℕ-Booleω elem-c) evaluate-is-Iso-inv ⟩
      evaluationMap freeBA-ℕ-Booleω elem-c (Iso.inv Sp-freeBA-ℕ-Iso α)
        ≡⟨ decPred→elem-property' (decide-fn ∘ Iso.fun Sp-freeBA-ℕ-Iso) (Iso.inv Sp-freeBA-ℕ-Iso α) ⟩
      decide-fn (Iso.fun Sp-freeBA-ℕ-Iso (Iso.inv Sp-freeBA-ℕ-Iso α))
        ≡⟨ cong decide-fn (Iso.sec Sp-freeBA-ℕ-Iso α) ⟩
      decide-fn α ∎)
      where
      open import BooleanRing.FreeBooleanRing.FreeBool using (inducedBAHom; freeBA-universal-property)

      evaluate-is-Iso-inv : WLPOmod.evaluate α ≡ Iso.inv Sp-freeBA-ℕ-Iso α
      evaluate-is-Iso-inv = refl  -- Both are definitionally inducedBAHom ℕ BoolBR α

    open WLPOmod.PlayingWithWLPO' decide-fn WLPOf elem-c SD-property

-- tex Proposition 3051: L_I(R/Z) = BZ (Shape of Circle is BZ)
-- PROPOSITION (tex line 3051):
-- TEX PROOF STRUCTURE:
-- 3. BZ is I-local (tex Lemma 3027, proved in BZILocalTC)
-- 5. Fibers are I-contractible since R is I-contractible (tex Cor 3047)
