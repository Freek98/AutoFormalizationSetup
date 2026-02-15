{-# OPTIONS --cubical --guardedness #-}

module work where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ; _<ᵇ_; snotz; znots; injSuc; predℕ)
open import Cubical.Data.Nat.Properties using (+-comm; +-suc; suc-predℕ)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Order.Inductive
  using (_<ᵗ_; _≤ᵗ_; <ᵗ-trans; <ᵗ-trans-suc; isProp<ᵗ; <ᵗsucm;
         ¬m<ᵗm; Trichotomyᵗ; _≟ᵗ_; Trichotomyᵗ-suc)
  renaming (lt to ltᵗ; eq to eqᵗ; gt to gtᵗ)

open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties using (discreteFin; isSetFin)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_; inl; inr)
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Relation.Nullary

open import Cubical.Algebra.AbGroup.Base
open import Cubical.Algebra.AbGroup.Properties
  using (addGroupHom; subtrGroupHom; negGroupHom)
open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠAbGroup)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.MorphismProperties
  using (compGroupHom; trivGroupHom; idGroupHom; makeIsGroupHom;
         isPropIsGroupHom; isSetGroupHom)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom; GroupHom)
import Cubical.Algebra.Group.Properties as GroupProps

open import Cubical.Algebra.ChainComplex.Base
  using (CoChainComplex)

private
  variable
    ℓ ℓ' : Level

-- ================================================================
-- Section 1: Fin Infrastructure
-- ================================================================

-- Boolean comparison helpers
private
  ¬<ᵗ0 : {n : ℕ} → n <ᵗ zero → ⊥
  ¬<ᵗ0 {zero} h = h
  ¬<ᵗ0 {suc _} h = h

  <ᵗ-≤ᵗ-trans : {a b c : ℕ} → a <ᵗ b → b ≤ᵗ c → a <ᵗ c
  <ᵗ-≤ᵗ-trans {zero} {zero} h _ = ⊥.rec h
  <ᵗ-≤ᵗ-trans {zero} {suc b} {zero} _ h = ⊥.rec (¬<ᵗ0 {b} h)
  <ᵗ-≤ᵗ-trans {zero} {suc _} {suc _} _ _ = tt
  <ᵗ-≤ᵗ-trans {suc _} {zero} h _ = ⊥.rec h
  <ᵗ-≤ᵗ-trans {suc _} {suc b} {zero} _ h = ⊥.rec (¬<ᵗ0 {b} h)
  <ᵗ-≤ᵗ-trans {suc a} {suc b} {suc c} = <ᵗ-≤ᵗ-trans {a} {b} {c}

-- punchIn: insert a gap at position i
-- Maps Fin n → Fin (suc n), skipping position i
-- Recursive definition: punchIn (suc a) (suc c) = fsuc (punchIn a c)
-- This gives definitional reduction for the simplicial identity proof
punchIn : {n : ℕ} → Fin (suc n) → Fin n → Fin (suc n)
punchIn (zero , _) j = fsuc j
punchIn {suc _} (suc a , p) (zero , _) = fzero
punchIn {suc _} (suc a , p) (suc c , q) = fsuc (punchIn (a , p) (c , q))

-- ℕ-level punchIn (mirrors Fin version, for proving simplicial identity)
punchIn-ℕ : ℕ → ℕ → ℕ
punchIn-ℕ zero c = suc c
punchIn-ℕ (suc a) zero = zero
punchIn-ℕ (suc a) (suc c) = suc (punchIn-ℕ a c)

-- Simplicial identity at ℕ level: for a ≤ b,
--   punchIn a (punchIn b c) = punchIn (suc b) (punchIn a c)
simplicial-ℕ : (a b c : ℕ) → a ≤ᵗ b
  → punchIn-ℕ a (punchIn-ℕ b c) ≡ punchIn-ℕ (suc b) (punchIn-ℕ a c)
simplicial-ℕ zero b c _ = refl
simplicial-ℕ (suc a) zero c h = ⊥.rec (¬<ᵗ0 {a} h)
simplicial-ℕ (suc a) (suc b) zero h = refl
simplicial-ℕ (suc a) (suc b) (suc c) h = cong suc (simplicial-ℕ a b c h)

-- fst of punchIn agrees with punchIn-ℕ (definitional)
punchIn-fst : {n : ℕ} (i : Fin (suc n)) (j : Fin n)
  → fst (punchIn i j) ≡ punchIn-ℕ (fst i) (fst j)
punchIn-fst (zero , _) j = refl
punchIn-fst {suc _} (suc a , p) (zero , _) = refl
punchIn-fst {suc _} (suc a , p) (suc c , q) = cong suc (punchIn-fst (a , p) (c , q))

-- Adjacent punchIn: for positions a and suc a, punchIn-ℕ either gives
-- the same value (when c ≠ a) or swaps a ↔ suc a (when c = a at ℕ level)
adj-punchIn-ℕ : (a c : ℕ)
  → (punchIn-ℕ a c ≡ punchIn-ℕ (suc a) c)
    ⊎ ((punchIn-ℕ a c ≡ suc a) × (punchIn-ℕ (suc a) c ≡ a))
adj-punchIn-ℕ zero zero = inr (refl , refl)
adj-punchIn-ℕ zero (suc c) = inl refl
adj-punchIn-ℕ (suc a) zero = inl refl
adj-punchIn-ℕ (suc a) (suc c) =
  ⊎.rec (λ e → inl (cong suc e))
        (λ pq → inr (cong suc (fst pq) , cong suc (snd pq)))
        (adj-punchIn-ℕ a c)

-- punchIn-ℕ is injective
punchIn-ℕ-inj : (a c₁ c₂ : ℕ) → punchIn-ℕ a c₁ ≡ punchIn-ℕ a c₂ → c₁ ≡ c₂
punchIn-ℕ-inj zero c₁ c₂ e = injSuc e
punchIn-ℕ-inj (suc a) zero zero _ = refl
punchIn-ℕ-inj (suc a) zero (suc c₂) e = ⊥.rec (znots e)
punchIn-ℕ-inj (suc a) (suc c₁) zero e = ⊥.rec (snotz e)
punchIn-ℕ-inj (suc a) (suc c₁) (suc c₂) e = cong suc (punchIn-ℕ-inj a c₁ c₂ (injSuc e))

-- Simplicial identity at Fin level (direct pattern matching)
simplicial : {n : ℕ} (i : Fin (suc (suc n))) (j : Fin (suc n)) (k : Fin n)
  (i' : Fin (suc n)) → fst i ≡ fst i' → fst i ≤ᵗ fst j
  → punchIn i (punchIn j k) ≡ punchIn (fsuc j) (punchIn i' k)
simplicial (zero , pi) j k (zero , pi') e h = refl
simplicial (zero , pi) j k (suc a' , pi') e h =
  ⊥.rec (znots e)
simplicial {suc n} (suc a , pi) (zero , pj) k i' e h =
  ⊥.rec (¬<ᵗ0 {a} h)
simplicial {suc n} (suc a , pi) (suc b , pj) (zero , pk) (zero , pi') e h =
  ⊥.rec (snotz e)
simplicial {suc n} (suc a , pi) (suc b , pj) (zero , pk) (suc a' , pi') e h =
  refl
simplicial {suc n} (suc a , pi) (suc b , pj) (suc c , pk) (zero , pi') e h =
  ⊥.rec (snotz e)
simplicial {suc n} (suc a , pi) (suc b , pj) (suc c , pk) (suc a' , pi') e h =
  cong fsuc (simplicial (a , pi) (b , pj) (c , pk) (a' , pi') (injSuc e) h)

-- Face map: delete position i from a (suc n)-tuple to get an n-tuple
faceMap : {n : ℕ} {A : Type ℓ} → Fin (suc n) → (Fin (suc n) → A) → (Fin n → A)
faceMap i σ = σ ∘ punchIn i

-- punchOut: inverse of punchIn (given k ≠ i, find j with punchIn k j = i)
punchOut : {n : ℕ} → (k : Fin (suc n)) → (i : Fin (suc n))
  → ¬ (fst k ≡ fst i) → Fin n
punchOut (zero , _) (zero , _) neq = ⊥.rec (neq refl)
punchOut (zero , _) (suc c , q) _ = (c , q)
punchOut {suc _} (suc a , p) (zero , _) _ = fzero
punchOut {suc _} (suc a , p) (suc c , q) neq =
  fsuc (punchOut (a , p) (c , q) (λ eq → neq (cong suc eq)))

-- punchIn ∘ punchOut = id
punchIn-punchOut : {n : ℕ} (k : Fin (suc n)) (i : Fin (suc n))
  (neq : ¬ (fst k ≡ fst i)) → punchIn k (punchOut k i neq) ≡ i
punchIn-punchOut (zero , _) (zero , _) neq = ⊥.rec (neq refl)
punchIn-punchOut (zero , _) (suc c , q) _ = refl
punchIn-punchOut {suc _} (suc a , p) (zero , _) _ = refl
punchIn-punchOut {suc _} (suc a , p) (suc c , q) neq =
  cong fsuc (punchIn-punchOut (a , p) (c , q) (λ eq → neq (cong suc eq)))

-- Swap two positions (using ≟ᵗ for with-matching in proofs)
swapFin : {n : ℕ} → Fin n → Fin n → Fin n → Fin n
swapFin i j k with fst k ≟ᵗ fst i
... | eqᵗ _ = j
... | ltᵗ _ with fst k ≟ᵗ fst j
...   | eqᵗ _ = i
...   | _ = k
swapFin i j k | gtᵗ _ with fst k ≟ᵗ fst j
...   | eqᵗ _ = i
...   | _ = k

-- swapFin properties
swapFin-ij : {n : ℕ} (i j : Fin n) → _≡_ {A = Fin n} (swapFin {n} i j i) j
swapFin-ij i j with fst i ≟ᵗ fst i
... | eqᵗ _ = refl
... | ltᵗ h = ⊥.rec (¬m<ᵗm {fst i} h)
... | gtᵗ h = ⊥.rec (¬m<ᵗm {fst i} h)

swapFin-ji : {n : ℕ} (i j : Fin n) → _≡_ {A = Fin n} (swapFin {n} i j j) i
swapFin-ji {n} i j with fst j ≟ᵗ fst i
... | eqᵗ e = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = n}) e
... | ltᵗ _ with fst j ≟ᵗ fst j
...   | eqᵗ _ = refl
...   | ltᵗ h = ⊥.rec (¬m<ᵗm {fst j} h)
...   | gtᵗ h = ⊥.rec (¬m<ᵗm {fst j} h)
swapFin-ji {n} i j | gtᵗ _ with fst j ≟ᵗ fst j
...   | eqᵗ _ = refl
...   | ltᵗ h = ⊥.rec (¬m<ᵗm {fst j} h)
...   | gtᵗ h = ⊥.rec (¬m<ᵗm {fst j} h)

swapFin-fix : {n : ℕ} (i j k : Fin n)
  → ¬ (fst k ≡ fst i) → ¬ (fst k ≡ fst j) → _≡_ {A = Fin n} (swapFin {n} i j k) k
swapFin-fix i j k k≠i k≠j with fst k ≟ᵗ fst i
... | eqᵗ e = ⊥.rec (k≠i e)
... | ltᵗ _ with fst k ≟ᵗ fst j
...   | eqᵗ e = ⊥.rec (k≠j e)
...   | ltᵗ _ = refl
...   | gtᵗ _ = refl
swapFin-fix i j k k≠i k≠j | gtᵗ _ with fst k ≟ᵗ fst j
...   | eqᵗ e = ⊥.rec (k≠j e)
...   | ltᵗ _ = refl
...   | gtᵗ _ = refl

-- m <ᵗ m + suc d (by induction on m)
m<m+sd : (m : ℕ) (dd : ℕ) → m <ᵗ (m + suc dd)
m<m+sd zero _ = tt
m<m+sd (suc m') dd = m<m+sd m' dd

-- ================================================================
-- Section 2: Strict Total Order with Trichotomy
-- ================================================================

-- Trichotomy type avoiding path types (cubical Agda can't pattern-match
-- on ⊎ when one branch contains a path type)
data Tri< {ℓ : Level} {A : Type ℓ} (_<_ : A → A → Type ℓ) (a b : A) : Type ℓ where
  is-lt : a < b → Tri< _<_ a b
  is-eq : ¬ (a < b) → ¬ (b < a) → Tri< _<_ a b
  is-gt : b < a → Tri< _<_ a b

Tri<-elim : ∀ {ℓ ℓ'} {A : Type ℓ} {_<_ : A → A → Type ℓ} {a b : A}
  {P : Tri< _<_ a b → Type ℓ'}
  → ((x : a < b) → P (is-lt x))
  → ((x : ¬ (a < b)) (y : ¬ (b < a)) → P (is-eq x y))
  → ((x : b < a) → P (is-gt x))
  → (r : Tri< _<_ a b) → P r
Tri<-elim f g h (is-lt x) = f x
Tri<-elim f g h (is-eq x y) = g x y
Tri<-elim f g h (is-gt x) = h x

record DecStrictTotalOrder {ℓ : Level} (A : Type ℓ) : Type (ℓ-suc ℓ) where
  field
    _<sto_ : A → A → Type ℓ
    <sto-prop : (a b : A) → isProp (a <sto b)
    <sto-irrefl : (a : A) → ¬ (a <sto a)
    <sto-trans : {a b c : A} → a <sto b → b <sto c → a <sto c
    <sto-tricho : (a b : A) → Tri< _<sto_ a b
    isSetA : isSet A

-- ================================================================
-- Section 3: General Čech Complex
-- ================================================================

module GeneralCech {ℓ : Level}
  (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where

  |A|_ : S → Type ℓ
  |A| x = fst (A x)

  module Ax (x : S) = AbGroupStr (snd (A x))
  module Gx (x : S) = GroupProps.GroupTheory (AbGroup→Group (A x))

  Cⁿ : ℕ → Type ℓ
  Cⁿ p = (x : S) → (Fin (suc p) → T x) → |A| x

  0C : {p : ℕ} → Cⁿ p
  0C x _ = Ax.0g x

  negC : {p : ℕ} → Cⁿ p → Cⁿ p
  negC s x σ = Ax.-_ x (s x σ)

  addC : {p : ℕ} → Cⁿ p → Cⁿ p → Cⁿ p
  addC s t x σ = Ax._+_ x (s x σ) (t x σ)

  negPow : {x : S} → ℕ → |A| x → |A| x
  negPow {x} zero a = a
  negPow {x} (suc n) a = Ax.-_ x (negPow n a)

  altFinSum : {x : S} → {n : ℕ} → (Fin n → |A| x) → |A| x
  altFinSum {x} {n} f = sumFinGen {n = n} (Ax._+_ x) (Ax.0g x)
    (λ j → negPow (fst j) (f j))

  d : {p : ℕ} → Cⁿ p → Cⁿ (suc p)
  d {p} s x σ = altFinSum {x} {suc (suc p)}
    (λ j → s x (faceMap j σ))

  CⁿAbGroup : (p : ℕ) → AbGroup ℓ
  CⁿAbGroup p = ΠAbGroup {X = S} (λ x →
    ΠAbGroup {X = Fin (suc p) → T x} (λ _ → A x))

  -- ================================================================
  -- Properties of negPow
  -- ================================================================

  negPow-two : {x : S} (a : |A| x) → negPow {x} 2 a ≡ a
  negPow-two {x} a = Gx.invInv x a

  negPow-add : {x : S} (n : ℕ) (a b : |A| x)
    → negPow n (Ax._+_ x a b) ≡ Ax._+_ x (negPow n a) (negPow n b)
  negPow-add zero a b = refl
  negPow-add {x} (suc n) a b =
    Ax.-_ x (negPow n (Ax._+_ x a b))
      ≡⟨ cong (Ax.-_ x) (negPow-add n a b) ⟩
    Ax.-_ x (Ax._+_ x (negPow n a) (negPow n b))
      ≡⟨ Gx.invDistr x (negPow n a) (negPow n b) ⟩
    Ax._+_ x (Ax.-_ x (negPow n b)) (Ax.-_ x (negPow n a))
      ≡⟨ Ax.+Comm x _ _ ⟩
    Ax._+_ x (Ax.-_ x (negPow n a)) (Ax.-_ x (negPow n b)) ∎

  negPow-0g : {x : S} (n : ℕ) → negPow {x} n (Ax.0g x) ≡ Ax.0g x
  negPow-0g zero = refl
  negPow-0g {x} (suc n) =
    Ax.-_ x (negPow n (Ax.0g x))
      ≡⟨ cong (Ax.-_ x) (negPow-0g n) ⟩
    Ax.-_ x (Ax.0g x)
      ≡⟨ GroupProps.GroupTheory.inv1g (AbGroup→Group (A x)) ⟩
    Ax.0g x ∎

  -- negPow composes: negPow i (negPow j a) ≡ negPow (i + j) a
  negPow-comp : {x : S} (i j : ℕ) (a : |A| x)
    → negPow i (negPow j a) ≡ negPow (i + j) a
  negPow-comp zero j a = refl
  negPow-comp {x} (suc i) j a = cong (Ax.-_ x) (negPow-comp i j a)

  -- negPow distributes over sumFinGen
  negPow-sum : {x : S} {m : ℕ} (n : ℕ) (f : Fin m → |A| x)
    → negPow n (sumFinGen {n = m} (Ax._+_ x) (Ax.0g x) f)
    ≡ sumFinGen {n = m} (Ax._+_ x) (Ax.0g x) (λ j → negPow n (f j))
  negPow-sum {m = zero} n f = negPow-0g n
  negPow-sum {x} {m = suc m} n f =
    negPow-add n (f flast) (sumFinGen {n = m} (Ax._+_ x) (Ax.0g x) (f ∘ injectSuc))
    ∙ cong (Ax._+_ x (negPow n (f flast)))
           (negPow-sum {x = x} {m = m} n (f ∘ injectSuc))

  -- ================================================================
  -- Linearity of d and d² = 0
  -- ================================================================

  private
    -- Abelian group interchange: (a+b)+(c+d) = (a+c)+(b+d)
    interchange : {x : S} (a b c d' : |A| x)
      → Ax._+_ x (Ax._+_ x a b) (Ax._+_ x c d')
      ≡ Ax._+_ x (Ax._+_ x a c) (Ax._+_ x b d')
    interchange {x} a b c d' =
      sym (Ax.+Assoc x a b _)
      ∙ cong (Ax._+_ x a) (Ax.+Assoc x b c d')
      ∙ cong (λ z → Ax._+_ x a (Ax._+_ x z d')) (Ax.+Comm x b c)
      ∙ cong (Ax._+_ x a) (sym (Ax.+Assoc x c b d'))
      ∙ Ax.+Assoc x a c _

  -- sumFinGen distributes over +
  sumFinGen-+ : {x : S} {n : ℕ} (f g : Fin n → |A| x)
    → sumFinGen {n = n} (Ax._+_ x) (Ax.0g x) (λ j → Ax._+_ x (f j) (g j))
    ≡ Ax._+_ x (sumFinGen {n = n} (Ax._+_ x) (Ax.0g x) f)
                (sumFinGen {n = n} (Ax._+_ x) (Ax.0g x) g)
  sumFinGen-+ {x} {zero} f g = sym (Ax.+IdR x _)
  sumFinGen-+ {x} {suc n} f g =
    cong (Ax._+_ x (Ax._+_ x (f flast) (g flast)))
         (sumFinGen-+ {x} {n} (f ∘ injectSuc) (g ∘ injectSuc))
    ∙ interchange (f flast) (g flast) _ _

  d-pres+ : {p : ℕ} (s t : Cⁿ p) (x : S) (σ : Fin (suc (suc p)) → T x)
    → d (addC s t) x σ ≡ Ax._+_ x (d s x σ) (d t x σ)
  d-pres+ {p} s t x σ =
    cong (sumFinGen {n = suc (suc p)} (Ax._+_ x) (Ax.0g x))
         (funExt (λ j → negPow-add (fst j) (s x (faceMap j σ)) (t x (faceMap j σ))))
    ∙ sumFinGen-+ {n = suc (suc p)}
                  (λ j → negPow (fst j) (s x (faceMap j σ)))
                  (λ j → negPow (fst j) (t x (faceMap j σ)))

  -- For p=0: face map compositions agree on Fin 1 (direct computation)
  -- Cancelling pairs: (0,0)↔(1,0), (0,1)↔(2,0), (1,1)↔(2,1)
  private
    face-comp-00≡10 : {B : Type ℓ} (σ : Fin 3 → B)
      → σ ∘ punchIn {2} fzero ∘ punchIn {1} fzero
      ≡ σ ∘ punchIn {2} fone ∘ punchIn {1} fzero
    face-comp-00≡10 σ = funExt λ { (zero , _) → refl ; (suc _ , q) → ⊥.rec q }

    face-comp-01≡20 : {B : Type ℓ} (σ : Fin 3 → B)
      → σ ∘ punchIn {2} fzero ∘ punchIn {1} fone
      ≡ σ ∘ punchIn {2} (2 , tt) ∘ punchIn {1} fzero
    face-comp-01≡20 σ = funExt λ { (zero , _) → refl ; (suc _ , q) → ⊥.rec q }

    face-comp-11≡21 : {B : Type ℓ} (σ : Fin 3 → B)
      → σ ∘ punchIn {2} fone ∘ punchIn {1} fone
      ≡ σ ∘ punchIn {2} (2 , tt) ∘ punchIn {1} fone
    face-comp-11≡21 σ = funExt λ { (zero , _) → refl ; (suc _ , q) → ⊥.rec q }

  -- Algebraic helpers for d²
  private
    -- Telescoping: (-p + q) + (-q + r) ≡ -p + r
    telescope : {x : S} (p q r : |A| x)
      → Ax._+_ x (Ax._+_ x (Ax.-_ x p) q)
                  (Ax._+_ x (Ax.-_ x q) r)
      ≡ Ax._+_ x (Ax.-_ x p) r
    telescope {x} p q r =
      sym (Ax.+Assoc x (Ax.-_ x p) q _)
      ∙ cong (Ax._+_ x (Ax.-_ x p)) (Ax.+Assoc x q (Ax.-_ x q) r)
      ∙ cong (λ z → Ax._+_ x (Ax.-_ x p) (Ax._+_ x z r)) (Ax.+InvR x q)
      ∙ cong (Ax._+_ x (Ax.-_ x p)) (Ax.+IdL x r)

    -- Cancellation: (-c + b) + ((-a + c) + (-b + a)) ≡ 0g
    cancel3 : {x : S} (a b c : |A| x)
      → Ax._+_ x (Ax._+_ x (Ax.-_ x c) b)
                  (Ax._+_ x (Ax._+_ x (Ax.-_ x a) c)
                            (Ax._+_ x (Ax.-_ x b) a))
      ≡ Ax.0g x
    cancel3 {x} a b c =
      cong (Ax._+_ x (Ax._+_ x (Ax.-_ x c) b))
           (Ax.+Comm x _ _)
      ∙ Ax.+Assoc x _ _ _
      ∙ cong (λ z → Ax._+_ x z (Ax._+_ x (Ax.-_ x a) c))
             (telescope c b a)
      ∙ telescope c a c
      ∙ Ax.+InvL x c

  -- d² = 0 for degree 0 (direct computation)
  d²-0 : (s : Cⁿ 0) (x : S) (σ : Fin 3 → T x)
    → d (d s) x σ ≡ Ax.0g x
  d²-0 s x σ = step1 ∙ step2 ∙ cancel3 T₀₀ T₀₁ T₁₁
    where
      T₀₀ = s x (σ ∘ punchIn {2} fzero ∘ punchIn {1} fzero)
      T₀₁ = s x (σ ∘ punchIn {2} fzero ∘ punchIn {1} fone)
      T₁₁ = s x (σ ∘ punchIn {2} fone ∘ punchIn {1} fone)
      eq₁ = cong (s x) (face-comp-00≡10 σ)
      eq₂ = cong (s x) (face-comp-01≡20 σ)
      eq₃ = cong (s x) (face-comp-11≡21 σ)
      -- Step 1: substitute face-comp equalities (6 vars → 3 vars)
      step1 = cong₂ (Ax._+_ x)
        (cong (λ w → Ax.-_ x (Ax.-_ x w))
          (cong₂ (Ax._+_ x) (cong (Ax.-_ x) (sym eq₃))
                             (cong (λ z → Ax._+_ x z (Ax.0g x)) (sym eq₂))))
        (cong (λ z → Ax._+_ x
          (Ax.-_ x (Ax._+_ x (Ax.-_ x T₁₁) (Ax._+_ x z (Ax.0g x))))
          (Ax._+_ x (Ax._+_ x (Ax.-_ x T₀₁) (Ax._+_ x T₀₀ (Ax.0g x)))
                    (Ax.0g x)))
          (sym eq₁))
      -- Step 2: simplify using invInv, +IdR, invDistr → cancel3 form
      step2 = cong₂ (Ax._+_ x)
        (Gx.invInv x _ ∙ cong (Ax._+_ x (Ax.-_ x T₁₁)) (Ax.+IdR x T₀₁))
        (cong₂ (Ax._+_ x)
          (cong (Ax.-_ x) (cong (Ax._+_ x (Ax.-_ x T₁₁)) (Ax.+IdR x T₀₀))
           ∙ Gx.invDistr x (Ax.-_ x T₁₁) T₀₀
           ∙ cong (Ax._+_ x (Ax.-_ x T₀₀)) (Gx.invInv x T₁₁))
          (Ax.+IdR x _ ∙ cong (Ax._+_ x (Ax.-_ x T₀₁)) (Ax.+IdR x T₀₀)))

  -- negPow n a + negPow (suc n) a ≡ 0g  (cancel adjacent signs)
  negPow-suc-cancel : {x : S} (n : ℕ) (a : |A| x)
    → Ax._+_ x (negPow n a) (negPow (suc n) a) ≡ Ax.0g x
  negPow-suc-cancel {x} n a = Ax.+InvR x (negPow n a)

  -- Face map composition via simplicial identity
  face-comp : {n : ℕ} {B : Type ℓ} (i : Fin (suc (suc n))) (j : Fin (suc n))
    (i' : Fin (suc n)) (σ : Fin (suc (suc n)) → B)
    → fst i ≡ fst i' → fst i ≤ᵗ fst j
    → faceMap j (faceMap i σ) ≡ faceMap i' (faceMap (fsuc j) σ)
  face-comp i j i' σ e h = funExt (λ k → cong σ (simplicial i j k i' e h))

  -- Sum of zeros is zero
  sfg-0 : {x : S} (n : ℕ) (f : Fin n → |A| x)
    → (∀ k → f k ≡ Ax.0g x)
    → sumFinGen {n = n} (Ax._+_ x) (Ax.0g x) f ≡ Ax.0g x
  sfg-0 zero f h = refl
  sfg-0 {x} (suc n) f h =
    cong₂ (Ax._+_ x) (h flast)
      (sfg-0 n (λ k → f (injectSuc k)) (λ k → h (injectSuc k)))
    ∙ Ax.+IdR x (Ax.0g x)

  -- Sum with a single nonzero term
  sfg-single : {x : S} (n : ℕ) (f : Fin (suc n) → |A| x) (i : Fin (suc n))
    → ((k : Fin (suc n)) → ¬ (fst k ≡ fst i) → f k ≡ Ax.0g x)
    → sumFinGen {n = suc n} (Ax._+_ x) (Ax.0g x) f ≡ f i
  sfg-single {x} zero f (zero , _) h =
    Ax.+IdR x (f fzero)
  sfg-single {x} zero f (suc _ , q) h = ⊥.rec q
  sfg-single {x} (suc n') f i h with suc n' ≟ᵗ fst i
  ... | eqᵗ p =
    let flast≡i : flast ≡ i
        flast≡i = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) p
        -- every injectSuc k has fst k < suc n' = fst i, so k ≠ i
        rest-zero : (k : Fin (suc n')) → f (injectSuc k) ≡ Ax.0g x
        rest-zero k = h (injectSuc k) λ e →
          ¬m<ᵗm {fst i} (subst (_<ᵗ fst i) e (subst (fst k <ᵗ_) p (snd k)))
    in cong₂ (Ax._+_ x) (cong f flast≡i)
         (sfg-0 (suc n') (f ∘ injectSuc) rest-zero)
       ∙ Ax.+IdR x (f i)
  ... | ltᵗ q = ⊥.rec (¬m<ᵗm {suc n'} (<ᵗ-≤ᵗ-trans {suc n'} {fst i} {suc n'} q (snd i)))
  ... | gtᵗ q =
    let n≠i : ¬ (suc n' ≡ fst i)
        n≠i e = ¬m<ᵗm {fst i} (subst (fst i <ᵗ_) e q)
        i' : Fin (suc n')
        i' = fst i , q
        iS≡i : injectSuc i' ≡ i
        iS≡i = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) refl
    in cong₂ (Ax._+_ x) (h flast n≠i)
         (sfg-single {x} n' (f ∘ injectSuc) i'
           (λ k k≠i' → h (injectSuc k) k≠i'))
       ∙ Ax.+IdL x (f (injectSuc i'))
       ∙ cong f iS≡i

  -- Sum with two nonzero terms that cancel
  sfg-two-cancel : {x : S} (n : ℕ) (f : Fin (suc n) → |A| x)
    (i j : Fin (suc n)) → ¬ (fst i ≡ fst j)
    → Ax._+_ x (f i) (f j) ≡ Ax.0g x
    → ((k : Fin (suc n)) → ¬ (fst k ≡ fst i) → ¬ (fst k ≡ fst j) → f k ≡ Ax.0g x)
    → sumFinGen {n = suc n} (Ax._+_ x) (Ax.0g x) f ≡ Ax.0g x
  -- Base: n=0 means Fin 1, can't have two distinct elements
  sfg-two-cancel {x} zero f i j i≠j _ _ = ⊥.rec (i≠j (cong fst (go i) ∙ sym (cong fst (go j))))
    where go : (k : Fin 1) → k ≡ fzero
          go (zero , _) = Σ≡Prop (λ z → isProp<ᵗ {n = z} {m = 1}) refl
          go (suc _ , q) = ⊥.rec q
  -- Step: n = suc n'
  sfg-two-cancel {x} (suc n') f i j i≠j cancel h with suc n' ≟ᵗ fst i
  ... | ltᵗ q = ⊥.rec (¬m<ᵗm {suc n'} (<ᵗ-≤ᵗ-trans {suc n'} {fst i} {suc n'} q (snd i)))
  ... | eqᵗ p = goal
    where
      flast≡i : flast ≡ i
      flast≡i = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) p
      j<sn : fst j <ᵗ suc n'
      j<sn with suc n' ≟ᵗ fst j
      ... | eqᵗ e = ⊥.rec (i≠j (sym p ∙ e))
      ... | ltᵗ r = ⊥.rec (¬m<ᵗm {suc n'} (<ᵗ-≤ᵗ-trans {suc n'} {fst j} {suc n'} r (snd j)))
      ... | gtᵗ r = r
      j' : Fin (suc n')
      j' = fst j , j<sn
      jS≡j : injectSuc j' ≡ j
      jS≡j = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) refl
      k<i : (k : Fin (suc n')) → fst k <ᵗ fst i
      k<i k = subst (fst k <ᵗ_) p (snd k)
      goal : _
      goal = cong₂ (Ax._+_ x) (cong f flast≡i)
         (sfg-single n' (f ∘ injectSuc) j'
           (λ k k≠j' → h (injectSuc k)
             (λ e → ¬m<ᵗm {fst i} (subst (_<ᵗ fst i) e (k<i k)))
             k≠j')
         ∙ cong f jS≡j)
       ∙ cancel
  ... | gtᵗ q with suc n' ≟ᵗ fst j
  ...   | ltᵗ r = ⊥.rec (¬m<ᵗm {suc n'} (<ᵗ-≤ᵗ-trans {suc n'} {fst j} {suc n'} r (snd j)))
  ...   | eqᵗ p =
    let flast≡j : flast ≡ j
        flast≡j = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) p
        i' : Fin (suc n')
        i' = fst i , q
        iS≡i : injectSuc i' ≡ i
        iS≡i = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) refl
        k<j : (k : Fin (suc n')) → fst k <ᵗ fst j
        k<j k = subst (fst k <ᵗ_) p (snd k)
    in cong₂ (Ax._+_ x) (cong f flast≡j)
         (sfg-single n' (f ∘ injectSuc) i'
           (λ k k≠i' → h (injectSuc k) k≠i'
             (λ e → ¬m<ᵗm {fst j} (subst (_<ᵗ fst j) e (k<j k))))
         ∙ cong f iS≡i)
       ∙ Ax.+Comm x (f j) (f i) ∙ cancel
  ...   | gtᵗ r =
    let n≠i : ¬ (suc n' ≡ fst i)
        n≠i e = ¬m<ᵗm {fst i} (subst (fst i <ᵗ_) e q)
        n≠j : ¬ (suc n' ≡ fst j)
        n≠j e = ¬m<ᵗm {fst j} (subst (fst j <ᵗ_) e r)
        i' : Fin (suc n')
        i' = fst i , q
        j' : Fin (suc n')
        j' = fst j , r
        iS≡i : injectSuc i' ≡ i
        iS≡i = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) refl
        jS≡j : injectSuc j' ≡ j
        jS≡j = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc n')}) refl
        i'≠j' : ¬ (fst i' ≡ fst j')
        i'≠j' = i≠j
    in cong₂ (Ax._+_ x)
         (h flast n≠i n≠j)
         (sfg-two-cancel n' (f ∘ injectSuc) i' j' i'≠j'
           (cong₂ (Ax._+_ x) (cong f iS≡i) (cong f jS≡j) ∙ cancel)
           (λ k k≠i' k≠j' → h (injectSuc k) k≠i' k≠j'))
       ∙ Ax.+IdR x (Ax.0g x)

  -- Fubini: interchange of summation order
  -- Σᵢ Σⱼ g(i,j) ≡ Σⱼ Σᵢ g(i,j)
  sumFinGen-swap : {x : S} (n m : ℕ) (g : Fin n → Fin m → |A| x)
    → sumFinGen {n = n} (Ax._+_ x) (Ax.0g x)
        (λ i → sumFinGen {n = m} (Ax._+_ x) (Ax.0g x) (g i))
    ≡ sumFinGen {n = m} (Ax._+_ x) (Ax.0g x)
        (λ j → sumFinGen {n = n} (Ax._+_ x) (Ax.0g x) (λ i → g i j))
  sumFinGen-swap {x} zero m g =
    sym (sfg-0 m (λ _ → Ax.0g x) (λ _ → refl))
  sumFinGen-swap {x} (suc n) m g =
    let _+_ = Ax._+_ x ; 0g = Ax.0g x
        ih = sumFinGen-swap {x} n m (λ i → g (injectSuc i))
        f₁ = g flast
        f₂ = λ j → sumFinGen {n = n} _+_ 0g (λ i → g (injectSuc i) j)
    in cong (_+_ (sumFinGen {n = m} _+_ 0g f₁)) ih
       ∙ sym (sumFinGen-+ {n = m} f₁ f₂)

  -- General d² = 0 (uses d²-0 pattern; general case requires simplicial identity)
  postulate
    d² : {p : ℕ} (s : Cⁿ p) (x : S)
      (σ : Fin (suc (suc (suc p))) → T x)
      → d (d s) x σ ≡ Ax.0g x

-- ================================================================
-- Section 4: Alternating Čech Complex
-- ================================================================

module AlternatingCech {ℓ : Level}
  (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ)
  (ordT : (x : S) → DecStrictTotalOrder (T x)) where

  open GeneralCech S T A public
  open module Ox (x : S) = DecStrictTotalOrder (ordT x)

  -- ================================================================
  -- 4.1: Tuple properties
  -- ================================================================

  isInjTuple : {p : ℕ} {x : S} → (Fin (suc p) → T x) → Type ℓ
  isInjTuple σ = ∀ i j → σ i ≡ σ j → i ≡ j

  hasRepeat : {p : ℕ} {x : S} → (Fin (suc p) → T x) → Type ℓ
  hasRepeat σ = Σ[ i ∈ _ ] Σ[ j ∈ _ ] (¬ (i ≡ j)) × (σ i ≡ σ j)

  isOrdered : {p : ℕ} {x : S} → (Fin (suc p) → T x) → Type ℓ
  isOrdered {p} {x} σ = ∀ (i j : Fin (suc p)) → fst i <ᵗ fst j
    → _<sto_ x (σ i) (σ j)

  -- ================================================================
  -- 4.2: Alternating cochains (Definition 20.23.1)
  -- ================================================================

  isAlternating : {p : ℕ} → Cⁿ p → Type ℓ
  isAlternating {p} s =
    ((x : S) (σ : Fin (suc p) → T x) (i j : Fin (suc p))
      → ¬ (i ≡ j) → σ i ≡ σ j → s x σ ≡ Ax.0g x)
    ×
    ((x : S) (σ : Fin (suc p) → T x) (i j : Fin (suc p))
      → ¬ (i ≡ j) → s x (σ ∘ swapFin {suc p} i j) ≡ Ax.-_ x (s x σ))

  Cⁿ-alt : ℕ → Type ℓ
  Cⁿ-alt p = Σ (Cⁿ p) (isAlternating {p})

  -- ================================================================
  -- 4.3: Ordered Čech complex (Definition 20.23.2)
  -- ================================================================

  OrdTuple : ℕ → S → Type ℓ
  OrdTuple p x = Σ (Fin (suc p) → T x) (isOrdered {p} {x})

  Cⁿ-ord : ℕ → Type ℓ
  Cⁿ-ord p = (x : S) → OrdTuple p x → |A| x

  -- ================================================================
  -- 4.4: Comparison maps
  -- ================================================================

  πmap : {p : ℕ} → Cⁿ p → Cⁿ-ord p
  πmap s x (σ , _) = s x σ

  ιmap : {p : ℕ} → Cⁿ-alt p → Cⁿ p
  ιmap = fst

  -- ================================================================
  -- 4.5: Sorting infrastructure for degree 1
  -- ================================================================

  sortPair : {x : S} → T x → T x → (T x × T x × ℕ)
  sortPair {x} a b with <sto-tricho x a b
  ... | is-lt _ = (a , b , 0)
  ... | is-eq _ _ = (a , b , 0)
  ... | is-gt _ = (b , a , 1)

  -- Ordered pair witness: direct pattern matching on Fin 2
  -- Key: n <ᵗ 0 = ⊥ and suc n <ᵗ suc m = n <ᵗ m definitionally
  mkOrd2 : {x : S} (σ : Fin 2 → T x) → _<sto_ x (σ fzero) (σ fone)
    → isOrdered {1} {x} σ
  mkOrd2 σ a<b (zero , _) (zero , _) p = ⊥.rec p
  mkOrd2 σ a<b (zero , _) (suc zero , _) _ = a<b
  mkOrd2 σ a<b (zero , _) (suc (suc _) , q) _ = ⊥.rec q
  mkOrd2 σ a<b (suc zero , _) (zero , _) p = ⊥.rec p
  mkOrd2 σ a<b (suc zero , _) (suc zero , _) p = ⊥.rec p
  mkOrd2 σ a<b (suc zero , _) (suc (suc _) , q) _ = ⊥.rec q
  mkOrd2 σ a<b (suc (suc _) , q) _ _ = ⊥.rec q

  -- ================================================================
  -- 4.6: Comparison map c for degree 1 (Lemma 20.23.3)
  -- ================================================================

  -- Core of comparison map: takes trichotomy result as explicit argument
  c₁-core : Cⁿ-ord 1 → (x : S) → (σ : Fin 2 → T x)
    → Tri< (_<sto_ x) (σ fzero) (σ fone) → |A| x
  c₁-core s x σ (is-lt a<b) = s x (σ , mkOrd2 σ a<b)
  c₁-core s x σ (is-eq _ _) = Ax.0g x
  c₁-core s x σ (is-gt b<a) = Ax.-_ x
    (s x (σ ∘ swapFin {2} fzero fone , mkOrd2 (σ ∘ swapFin {2} fzero fone) b<a))

  c₁-fun : Cⁿ-ord 1 → Cⁿ 1
  c₁-fun s x σ = c₁-core s x σ (<sto-tricho x (σ fzero) (σ fone))

  -- c₁-fun vanishes when σ fzero ≡ σ fone (repeated entry)
  -- Uses Tri<-elim + lambda to avoid binding path types in pattern LHS
  private
    c₁-vanish : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x)
      → σ fzero ≡ σ fone → c₁-fun s x σ ≡ Ax.0g x
    c₁-vanish s x σ = λ eq → Tri<-elim {P = λ r → c₁-core s x σ r ≡ Ax.0g x}
      (λ a<b → ⊥.rec (<sto-irrefl x (σ fzero)
        (subst (_<sto_ x (σ fzero)) (sym eq) a<b)))
      (λ _ _ → refl)
      (λ b<a → ⊥.rec (<sto-irrefl x (σ fzero)
        (subst (λ y → _<sto_ x y (σ fzero)) (sym eq) b<a)))
      (<sto-tricho x (σ fzero) (σ fone))

  -- Vanishing part of c₁-alternating: case split on Fin 2 indices,
  -- but keep eq : σ i ≡ σ j as a lambda argument (not on LHS)
  private
    c₁-alt-vanish : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x)
      (i j : Fin 2) → ¬ (i ≡ j) → σ i ≡ σ j → c₁-fun s x σ ≡ Ax.0g x
    c₁-alt-vanish s x σ (zero , _) (zero , _) ¬eq =
      λ _ → ⊥.rec (¬eq (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = 2}) refl))
    c₁-alt-vanish s x σ (zero , _) (suc zero , _) _ =
      c₁-vanish s x σ
    c₁-alt-vanish s x σ (zero , _) (suc (suc _) , q) _ = λ _ → ⊥.rec q
    c₁-alt-vanish s x σ (suc zero , _) (zero , _) _ =
      c₁-vanish s x σ ∘ sym
    c₁-alt-vanish s x σ (suc zero , _) (suc zero , _) ¬eq =
      λ _ → ⊥.rec (¬eq (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = 2}) refl))
    c₁-alt-vanish s x σ (suc zero , _) (suc (suc _) , q) _ = λ _ → ⊥.rec q
    c₁-alt-vanish s x σ (suc (suc _) , q) _ _ = λ _ → ⊥.rec q

  -- isOrdered is a proposition (since _<sto_ is prop-valued)
  isPropIsOrdered : {p : ℕ} {x : S} {σ : Fin (suc p) → T x}
    → isProp (isOrdered {p} {x} σ)
  isPropIsOrdered {x = x} {σ} =
    isPropΠ λ i → isPropΠ λ j → isPropΠ λ _ → <sto-prop x (σ i) (σ j)

  -- Swap involution: swapFin {2} fzero fone applied twice = id
  private
    sw01 : Fin 2 → Fin 2
    sw01 = swapFin {2} fzero fone

    sw01² : (k : Fin 2) → sw01 (sw01 k) ≡ k
    sw01² (zero , _) = refl
    sw01² (suc zero , _) = refl
    sw01² (suc (suc _) , q) = ⊥.rec q

    sw01-comp : {x : S} (σ : Fin 2 → T x) → σ ∘ sw01 ∘ sw01 ≡ σ
    sw01-comp σ = funExt (λ k → cong σ (sw01² k))

  -- Antisymmetry of c₁-core: case analysis on two trichotomy results
  -- (no path types in scope, so direct pattern matching is safe)
  private
    c₁-antisym-core : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x)
      → (r₁ : Tri< (_<sto_ x) (σ fzero) (σ fone))
      → (r₂ : Tri< (_<sto_ x) (σ fone) (σ fzero))
      → c₁-core s x (σ ∘ sw01) r₂ ≡ Ax.-_ x (c₁-core s x σ r₁)
    -- (lt, lt): contradiction via transitivity
    c₁-antisym-core s x σ (is-lt p<q) (is-lt q<p) =
      ⊥.rec (<sto-irrefl x _ (<sto-trans x p<q q<p))
    -- (lt, eq): ¬p<q contradicts p<q
    c₁-antisym-core s x σ (is-lt p<q) (is-eq _ ¬p<q) = ⊥.rec (¬p<q p<q)
    -- (lt, gt): VALID — need swap involution
    c₁-antisym-core s x σ (is-lt p<q) (is-gt p<q') =
      cong (Ax.-_ x) (cong (s x) (Σ≡Prop (λ _ → isPropIsOrdered) (sw01-comp σ)))
    -- (eq, lt): contradiction
    c₁-antisym-core s x σ (is-eq _ ¬q<p) (is-lt q<p) = ⊥.rec (¬q<p q<p)
    -- (eq, eq): VALID — 0g ≡ -(0g)
    c₁-antisym-core s x σ (is-eq _ _) (is-eq _ _) =
      sym (GroupProps.GroupTheory.inv1g (AbGroup→Group (A x)))
    -- (eq, gt): contradiction
    c₁-antisym-core s x σ (is-eq ¬p<q _) (is-gt p<q) = ⊥.rec (¬p<q p<q)
    -- (gt, lt): VALID — invInv
    c₁-antisym-core s x σ (is-gt q<p) (is-lt q<p') =
      cong (s x) (Σ≡Prop (λ _ → isPropIsOrdered) refl)
      ∙ sym (Gx.invInv x _)
    -- (gt, eq): contradiction
    c₁-antisym-core s x σ (is-gt q<p) (is-eq ¬q<p _) = ⊥.rec (¬q<p q<p)
    -- (gt, gt): contradiction
    c₁-antisym-core s x σ (is-gt q<p) (is-gt p<q) =
      ⊥.rec (<sto-irrefl x _ (<sto-trans x q<p p<q))

    c₁-antisym01 : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x)
      → c₁-fun s x (σ ∘ sw01) ≡ Ax.-_ x (c₁-fun s x σ)
    c₁-antisym01 s x σ = c₁-antisym-core s x σ
      (<sto-tricho x (σ fzero) (σ fone))
      (<sto-tricho x (σ fone) (σ fzero))

  -- For swap(fone, fzero): sw10 k ≡ sw01 k for all k : Fin 2
  private
    sw10≡sw01 : (k : Fin 2) → swapFin {2} fone fzero k ≡ sw01 k
    sw10≡sw01 (zero , _) = refl
    sw10≡sw01 (suc zero , _) = refl
    sw10≡sw01 (suc (suc _) , q) = ⊥.rec q

    c₁-antisym10 : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x)
      → c₁-fun s x (σ ∘ swapFin {2} fone fzero) ≡ Ax.-_ x (c₁-fun s x σ)
    c₁-antisym10 s x σ =
      cong (c₁-fun s x) (funExt (λ k → cong σ (sw10≡sw01 k)))
      ∙ c₁-antisym01 s x σ

  -- Full antisymmetry: case split on i,j : Fin 2
  private
    c₁-alt-antisym : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x)
      (i j : Fin 2) → ¬ (i ≡ j)
      → c₁-fun s x (σ ∘ swapFin {2} i j) ≡ Ax.-_ x (c₁-fun s x σ)
    c₁-alt-antisym s x σ (zero , _) (zero , _) ¬eq =
      ⊥.rec (¬eq (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = 2}) refl))
    c₁-alt-antisym s x σ (zero , _) (suc zero , _) _ =
      c₁-antisym01 s x σ
    c₁-alt-antisym s x σ (zero , _) (suc (suc _) , q) _ = ⊥.rec q
    c₁-alt-antisym s x σ (suc zero , _) (zero , _) _ =
      c₁-antisym10 s x σ
    c₁-alt-antisym s x σ (suc zero , _) (suc zero , _) ¬eq =
      ⊥.rec (¬eq (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = 2}) refl))
    c₁-alt-antisym s x σ (suc zero , _) (suc (suc _) , q) _ = ⊥.rec q
    c₁-alt-antisym s x σ (suc (suc _) , q) _ _ = ⊥.rec q

  c₁-alternating : (s : Cⁿ-ord 1) → isAlternating (c₁-fun s)
  fst (c₁-alternating s) = c₁-alt-vanish s
  snd (c₁-alternating s) = c₁-alt-antisym s

  c₁ : Cⁿ-ord 1 → Cⁿ-alt 1
  c₁ s = c₁-fun s , c₁-alternating s

  -- ================================================================
  -- 4.7: π ∘ c = id (Lemma 20.23.4)
  -- ================================================================

  private
    π∘c₁-core : (s : Cⁿ-ord 1) (x : S) (σ : Fin 2 → T x) (ord : isOrdered {1} {x} σ)
      → (r : Tri< (_<sto_ x) (σ fzero) (σ fone))
      → c₁-core s x σ r ≡ s x (σ , ord)
    π∘c₁-core s x σ ord (is-lt a<b) =
      cong (s x) (Σ≡Prop (λ _ → isPropIsOrdered) refl)
    π∘c₁-core s x σ ord (is-eq ¬a<b _) = ⊥.rec (¬a<b (ord fzero fone tt))
    π∘c₁-core s x σ ord (is-gt b<a) =
      ⊥.rec (<sto-irrefl x (σ fzero)
        (<sto-trans x (ord fzero fone tt) b<a))

  π∘c₁ : (s : Cⁿ-ord 1) → (x : S) → (ot : OrdTuple 1 x)
    → πmap (c₁-fun s) x ot ≡ s x ot
  π∘c₁ s x (σ , ord) = π∘c₁-core s x σ ord (<sto-tricho x (σ fzero) (σ fone))

  -- ================================================================
  -- 4.8: d preserves alternating cochains
  -- ================================================================

  -- Helper: if σ has a repeat at (i,j) and k ≠ i,j, then σ ∘ punchIn k has a repeat
  private
    face-has-repeat : {p : ℕ} {x : S} (σ : Fin (suc (suc p)) → T x)
      (i j : Fin (suc (suc p))) (k : Fin (suc (suc p)))
      → ¬ (fst k ≡ fst i) → ¬ (fst k ≡ fst j)
      → ¬ (i ≡ j) → σ i ≡ σ j
      → hasRepeat (σ ∘ punchIn k)
    face-has-repeat σ i j k k≠i k≠j i≠j σi≡σj =
      let i' = punchOut k i k≠i
          j' = punchOut k j k≠j
          eq-i = punchIn-punchOut k i k≠i
          eq-j = punchIn-punchOut k j k≠j
          i'≠j' : ¬ (i' ≡ j')
          i'≠j' p = i≠j (sym eq-i ∙ cong (punchIn k) p ∙ eq-j)
      in i' , j' , i'≠j' , (cong σ eq-i ∙ σi≡σj ∙ sym (cong σ eq-j))

    -- Each term in the alternating sum: for faces that still have repeats, s vanishes
    face-term-zero : {p : ℕ} {x : S} (s : Cⁿ p)
      → (van : (x : S) (σ : Fin (suc p) → T x) (i j : Fin (suc p))
              → ¬ (i ≡ j) → σ i ≡ σ j → s x σ ≡ Ax.0g x)
      → (σ : Fin (suc (suc p)) → T x)
      → (i j : Fin (suc (suc p))) → ¬ (i ≡ j) → σ i ≡ σ j
      → (k : Fin (suc (suc p))) → ¬ (fst k ≡ fst i) → ¬ (fst k ≡ fst j)
      → negPow (fst k) (s x (σ ∘ punchIn k)) ≡ Ax.0g x
    face-term-zero {x = x} s van σ i j i≠j σeq k k≠i k≠j =
      let hr = face-has-repeat σ i j k k≠i k≠j i≠j σeq
          i' = fst hr ; j' = fst (snd hr)
          i'≠j' = fst (snd (snd hr)) ; σeq' = snd (snd (snd hr))
      in cong (negPow (fst k)) (van x (σ ∘ punchIn k) i' j' i'≠j' σeq')
         ∙ negPow-0g (fst k)

  -- ℕ arithmetic: a + (b ∸ suc a) ≡ predℕ b when a <ᵗ b
  private
    +∸≡predℕ : (a b : ℕ) → a <ᵗ b → a + (b ∸ suc a) ≡ predℕ b
    +∸≡predℕ zero (suc b') _ = refl
    +∸≡predℕ (suc a') (suc (suc b'')) h = cong suc (+∸≡predℕ a' (suc b'') h)

  -- ℕ arithmetic helpers
  private
    suc+∸≡ : (a b : ℕ) → a <ᵗ b → suc a + (b ∸ suc a) ≡ b
    suc+∸≡ zero (suc b') _ = refl
    suc+∸≡ (suc a') (suc (suc b'')) h = cong suc (suc+∸≡ a' (suc b'') h)

    +1≡suc : (d : ℕ) → d + 1 ≡ suc d
    +1≡suc zero = refl
    +1≡suc (suc d') = cong suc (+1≡suc d')

  -- Adjacent face equality: when fst j = suc(fst i) and σ i = σ j,
  -- σ ∘ punchIn i and σ ∘ punchIn j agree pointwise.
  -- Uses adj-punchIn-ℕ: either both punchIns give same value (cong σ),
  -- or they hit i and j (bridged by σeq).
  adj-face-eq : {p : ℕ} {x : S} (σ : Fin (suc (suc p)) → T x)
    (i j : Fin (suc (suc p)))
    → suc (fst i) ≡ fst j → σ i ≡ σ j
    → (c : Fin (suc p)) → σ (punchIn i c) ≡ σ (punchIn j c)
  adj-face-eq {p} σ i j si≡fj σeq c =
    ⊎.rec
      (λ e →
        -- same ℕ value: punchIn-ℕ (fst i) (fst c) = punchIn-ℕ (fst j) (fst c)
        -- so punchIn i c = punchIn j c as Fin elements
        let fst-eq : fst (punchIn i c) ≡ fst (punchIn j c)
            fst-eq = punchIn-fst i c ∙ e ∙ cong (λ z → punchIn-ℕ z (fst c)) si≡fj
                   ∙ sym (punchIn-fst j c)
        in cong σ (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc p)}) fst-eq))
      (λ pq →
        -- punchIn-ℕ (fst i) (fst c) = suc(fst i) = fst j, and
        -- punchIn-ℕ (suc(fst i)) (fst c) = fst i
        let pi-eq : fst (punchIn i c) ≡ fst j
            pi-eq = punchIn-fst i c ∙ fst pq ∙ si≡fj
            pj-eq : fst (punchIn j c) ≡ fst i
            pj-eq = punchIn-fst j c
                  ∙ cong (λ z → punchIn-ℕ z (fst c)) (sym si≡fj)
                  ∙ snd pq
            Σeq = λ {a} {b} (e : fst a ≡ fst b) →
              Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc p)}) {u = a} {v = b} e
        in cong σ (Σeq pi-eq)
           ∙ sym σeq
           ∙ sym (cong σ (Σeq pj-eq)))
      (adj-punchIn-ℕ (fst i) (fst c))

  -- Face shift: by induction on gap d where suc(fst i) + d = fst j.
  -- Base: d=0, adjacent faces agree pointwise (σ(i) = σ(j) bridges the gap).
  -- Step: define σ' = σ ∘ swap(i, i+1). Then:
  --   face i of σ = face (i+1) of σ'  [punchIn-swap identity]
  --   face j of σ' = (face j of σ) ∘ swap  [swap-punchIn commutation]
  --   By IH on (σ', i+1, j, gap-1) + antisymmetry: compose signs.
  face-shift-aux : {p : ℕ} (s : Cⁿ p) (alt : isAlternating s)
    → (x : S) (d : ℕ) (σ : Fin (suc (suc p)) → T x)
    → (i j : Fin (suc (suc p)))
    → suc (fst i) + d ≡ fst j → σ i ≡ σ j
    → s x (σ ∘ punchIn i) ≡ negPow d (s x (σ ∘ punchIn j))
  face-shift-aux s alt x zero σ i j si+0≡fj σeq =
    -- d=0: suc(fst i) = fst j, faces agree pointwise
    let si≡fj : suc (fst i) ≡ fst j
        si≡fj = sym (+-comm (suc (fst i)) 0) ∙ si+0≡fj
    in cong (s x) (funExt (adj-face-eq σ i j si≡fj σeq))
  face-shift-aux {p} s alt x (suc d') σ i j si+sd≡fj σeq = goal
    where
      -- i₊₁ : next position after i, with bound proof
      si<fj : suc (fst i) <ᵗ fst j
      si<fj = subst (suc (fst i) <ᵗ_) si+sd≡fj (m<m+sd (suc (fst i)) d')

      i₊₁-bnd : suc (fst i) <ᵗ suc (suc p)
      i₊₁-bnd = <ᵗ-trans {suc (fst i)} {fst j} {suc (suc p)} si<fj (snd j)

      i₊₁ : Fin (suc (suc p))
      i₊₁ = suc (fst i) , i₊₁-bnd

      -- σ' = σ ∘ swap(i, i₊₁)
      σ' : Fin (suc (suc p)) → T x
      σ' = σ ∘ swapFin {suc (suc p)} i i₊₁

      -- Gap arithmetic: suc(fst i₊₁) + d' = fst j
      -- suc(suc(fst i)) + d' ≡[cong suc (+-comm ...)]≡ suc(fst i) + suc d' ≡ fst j
      gap' : suc (suc (fst i)) + d' ≡ fst j
      gap' = cong suc (sym (+-suc (fst i) d')) ∙ si+sd≡fj

      -- σ' has repeat at (i₊₁, j)
      -- σ'(i₊₁) = σ(swap(i,i₊₁)(i₊₁)) = σ(i) [by swapFin-ji]
      -- σ'(j) = σ(swap(i,i₊₁)(j)) = σ(j) [by swapFin-fix, since j ≠ i and j ≠ i₊₁]
      i≠i₊₁ : ¬ (fst i ≡ fst i₊₁)
      i≠i₊₁ e = ¬m<ᵗm {fst i} (subst (fst i <ᵗ_) (sym e) (<ᵗsucm {m = fst i}))

      j≠i : ¬ (fst j ≡ fst i)
      j≠i e = ¬m<ᵗm {fst i} (subst (fst i <ᵗ_) e (<ᵗ-trans {fst i} {suc (fst i)} {fst j} (<ᵗsucm {m = fst i}) si<fj))

      j≠i₊₁ : ¬ (fst j ≡ suc (fst i))
      j≠i₊₁ e = ¬m<ᵗm {suc (fst i)} (subst (suc (fst i) <ᵗ_) e si<fj)

      σ'repeat : σ' i₊₁ ≡ σ' j
      σ'repeat = cong σ (swapFin-ji {suc (suc p)} i i₊₁)
               ∙ σeq
               ∙ sym (cong σ (swapFin-fix {suc (suc p)} i i₊₁ j j≠i j≠i₊₁))

      -- IH: s x (σ' ∘ punchIn i₊₁) = negPow d' (s x (σ' ∘ punchIn j))
      ih : s x (σ' ∘ punchIn i₊₁) ≡ negPow d' (s x (σ' ∘ punchIn j))
      ih = face-shift-aux s alt x d' σ' i₊₁ j gap' σ'repeat

      -- Key identity: swap(i,i₊₁) ∘ punchIn(i₊₁) = punchIn(i) (pointwise)
      -- Case analysis via adj-punchIn-ℕ:
      --   inl: punchIn-ℕ values agree, punchIn i₊₁ c avoids both i and i₊₁,
      --        so swap fixes it, and result = punchIn i c
      --   inr: punchIn i₊₁ c has fst = fst i, swap takes i↦i₊₁,
      --        and punchIn i c has fst = fst i₊₁ = suc(fst i)
      swap-punchIn-adj : (c : Fin (suc p))
        → _≡_ {A = Fin (suc (suc p))} (swapFin {suc (suc p)} i i₊₁ (punchIn i₊₁ c)) (punchIn i c)
      swap-punchIn-adj c = ⊎.rec case-same case-swap (adj-punchIn-ℕ (fst i) (fst c))
        where
          Σeq : {a b : Fin (suc (suc p))} → fst a ≡ fst b → a ≡ b
          Σeq = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc p)})
          -- punchIn-ℕ (fst i) avoids fst i, so result ≠ fst i
          punchIn-ℕ-avoids : (a c : ℕ) → ¬ (punchIn-ℕ a c ≡ a)
          punchIn-ℕ-avoids zero c e = snotz e
          punchIn-ℕ-avoids (suc a) zero e = znots e
          punchIn-ℕ-avoids (suc a) (suc c) e = punchIn-ℕ-avoids a c (injSuc e)
          case-same : punchIn-ℕ (fst i) (fst c) ≡ punchIn-ℕ (suc (fst i)) (fst c)
            → swapFin {suc (suc p)} i i₊₁ (punchIn i₊₁ c) ≡ punchIn i c
          case-same e =
            let pi₊₁-fst = punchIn-fst i₊₁ c
                pi-fst = punchIn-fst i c
                -- fst(punchIn i₊₁ c) ≠ fst i (since punchIn-ℕ(fst i) avoids fst i, and they agree)
                ne-i : ¬ (fst (punchIn i₊₁ c) ≡ fst i)
                ne-i h = punchIn-ℕ-avoids (fst i) (fst c)
                  (e ∙ sym pi₊₁-fst ∙ h)
                -- fst(punchIn i₊₁ c) ≠ suc(fst i) (punchIn avoids its argument)
                ne-i₊₁ : ¬ (fst (punchIn i₊₁ c) ≡ fst i₊₁)
                ne-i₊₁ h = punchIn-ℕ-avoids (suc (fst i)) (fst c) (sym (pi₊₁-fst) ∙ h)
                -- swap fixes punchIn i₊₁ c
                swap-fix = swapFin-fix {suc (suc p)} i i₊₁ (punchIn i₊₁ c) ne-i ne-i₊₁
                -- fst equality: punchIn-ℕ (suc(fst i)) (fst c) = punchIn-ℕ (fst i) (fst c)
                fst-eq : fst (punchIn i₊₁ c) ≡ fst (punchIn i c)
                fst-eq = pi₊₁-fst ∙ sym e ∙ sym pi-fst
            in swap-fix ∙ Σeq fst-eq
          case-swap : (punchIn-ℕ (fst i) (fst c) ≡ suc (fst i))
                    × (punchIn-ℕ (suc (fst i)) (fst c) ≡ fst i)
            → swapFin {suc (suc p)} i i₊₁ (punchIn i₊₁ c) ≡ punchIn i c
          case-swap (pi-eq , pi₊₁-eq) =
            let pi₊₁-fst = punchIn-fst i₊₁ c
                pi-fst = punchIn-fst i c
                -- fst(punchIn i₊₁ c) = fst i, so swap takes i ↦ i₊₁
                fst-is-i : fst (punchIn i₊₁ c) ≡ fst i
                fst-is-i = pi₊₁-fst ∙ pi₊₁-eq
                pi₊₁-is-i : punchIn i₊₁ c ≡ i
                pi₊₁-is-i = Σeq fst-is-i
                -- swap(i,i₊₁)(i) = i₊₁
                swap-gives-i₊₁ : swapFin {suc (suc p)} i i₊₁ (punchIn i₊₁ c) ≡ i₊₁
                swap-gives-i₊₁ = cong (swapFin {suc (suc p)} i i₊₁) pi₊₁-is-i
                                ∙ swapFin-ij {suc (suc p)} i i₊₁
                -- punchIn i c has fst = suc(fst i) = fst i₊₁
                pi-is-i₊₁ : punchIn i c ≡ i₊₁
                pi-is-i₊₁ = Σeq (pi-fst ∙ pi-eq)
            in swap-gives-i₊₁ ∙ sym pi-is-i₊₁

      -- Fact 1: σ ∘ punchIn i = σ' ∘ punchIn i₊₁
      fact1 : s x (σ ∘ punchIn i) ≡ s x (σ' ∘ punchIn i₊₁)
      fact1 = cong (s x) (funExt (λ c → sym (cong σ (swap-punchIn-adj c))))

      -- Fact 5: s x (σ' ∘ punchIn j) = -(s x (σ ∘ punchIn j))
      -- Preimages of i, i₊₁ under punchIn j (both below j)
      i' : Fin (suc p)
      i' = punchOut j i j≠i
      i₊₁' : Fin (suc p)
      i₊₁' = punchOut j i₊₁ j≠i₊₁

      i'≠i₊₁' : ¬ (i' ≡ i₊₁')
      i'≠i₊₁' e =
        let i≡i₊₁ = sym (punchIn-punchOut j i j≠i)
                   ∙ cong (punchIn j) e
                   ∙ punchIn-punchOut j i₊₁ j≠i₊₁
        in i≠i₊₁ (cong fst i≡i₊₁)

      -- Key commutation: swap(i,i₊₁) ∘ punchIn j = punchIn j ∘ swap(i', i₊₁') (pointwise)
      -- Three cases: c has fst equal to fst i', fst i₊₁', or neither.
      swap-punchIn-comm : (c : Fin (suc p))
        → _≡_ {A = Fin (suc (suc p))}
               (swapFin {suc (suc p)} i i₊₁ (punchIn j c))
               (punchIn j (swapFin {suc p} i' i₊₁' c))
      swap-punchIn-comm c = go (fst c ≟ᵗ fst i') (fst c ≟ᵗ fst i₊₁')
        where
          Σeqp = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc p})
          Σeqp2 = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc p)})
          -- punchIn j is injective on fst
          pj-inj : {a b : Fin (suc p)} → fst (punchIn j a) ≡ fst (punchIn j b) → fst a ≡ fst b
          pj-inj {a} {b} e = punchIn-ℕ-inj (fst j) (fst a) (fst b)
            (sym (punchIn-fst j a) ∙ e ∙ punchIn-fst j b)
          -- Roundtrip identities
          pj-i' = punchIn-punchOut j i j≠i        -- punchIn j i' ≡ i
          pj-i₊₁' = punchIn-punchOut j i₊₁ j≠i₊₁  -- punchIn j i₊₁' ≡ i₊₁
          -- Helper for "neither" case: both swaps fix
          go-fix : ¬ (fst c ≡ fst i') → ¬ (fst c ≡ fst i₊₁')
                 → swapFin {suc (suc p)} i i₊₁ (punchIn j c) ≡ punchIn j (swapFin {suc p} i' i₊₁' c)
          go-fix c≠i' c≠i₊₁' =
            let rhs-fix = swapFin-fix {suc p} i' i₊₁' c c≠i' c≠i₊₁'
                pjc≠i : ¬ (fst (punchIn j c) ≡ fst i)
                pjc≠i h = c≠i' (pj-inj (h ∙ sym (cong fst pj-i')))
                pjc≠i₊₁ : ¬ (fst (punchIn j c) ≡ fst i₊₁)
                pjc≠i₊₁ h = c≠i₊₁' (pj-inj (h ∙ sym (cong fst pj-i₊₁')))
                lhs-fix = swapFin-fix {suc (suc p)} i i₊₁ (punchIn j c) pjc≠i pjc≠i₊₁
            in lhs-fix ∙ cong (punchIn j) (sym rhs-fix)
          -- Derive ¬-proofs from trichotomy evidence
          lt-ne : {a b : ℕ} → a <ᵗ b → ¬ (a ≡ b)
          lt-ne {a} h e = ¬m<ᵗm {a} (subst (a <ᵗ_) (sym e) h)
          gt-ne : {a b : ℕ} → b <ᵗ a → ¬ (a ≡ b)
          gt-ne {a} {b} h e = ¬m<ᵗm {b} (subst (b <ᵗ_) e h)
          go : Trichotomyᵗ (fst c) (fst i') → Trichotomyᵗ (fst c) (fst i₊₁')
             → swapFin {suc (suc p)} i i₊₁ (punchIn j c) ≡ punchIn j (swapFin {suc p} i' i₊₁' c)
          go (eqᵗ e) _ =
            let c≡i' = Σeqp e
                lhs = cong (swapFin {suc (suc p)} i i₊₁) (cong (punchIn j) c≡i' ∙ pj-i')
                    ∙ swapFin-ij {suc (suc p)} i i₊₁
                rhs = cong (punchIn j) (cong (swapFin {suc p} i' i₊₁') c≡i'
                    ∙ swapFin-ij {suc p} i' i₊₁') ∙ pj-i₊₁'
            in lhs ∙ sym rhs
          go _ (eqᵗ e) =
            let c≡i₊₁' = Σeqp e
                lhs = cong (swapFin {suc (suc p)} i i₊₁) (cong (punchIn j) c≡i₊₁' ∙ pj-i₊₁')
                    ∙ swapFin-ji {suc (suc p)} i i₊₁
                rhs = cong (punchIn j) (cong (swapFin {suc p} i' i₊₁') c≡i₊₁'
                    ∙ swapFin-ji {suc p} i' i₊₁') ∙ pj-i'
            in lhs ∙ sym rhs
          go (ltᵗ h1) (ltᵗ h2) = go-fix (lt-ne h1) (lt-ne h2)
          go (ltᵗ h1) (gtᵗ h2) = go-fix (lt-ne h1) (gt-ne h2)
          go (gtᵗ h1) (ltᵗ h2) = go-fix (gt-ne h1) (lt-ne h2)
          go (gtᵗ h1) (gtᵗ h2) = go-fix (gt-ne h1) (gt-ne h2)

      -- σ' ∘ punchIn j = (σ ∘ punchIn j) ∘ swap(i', i₊₁')
      fact5-eq : σ' ∘ punchIn j ≡ (σ ∘ punchIn j) ∘ swapFin {suc p} i' i₊₁'
      fact5-eq = funExt (λ c → cong σ (swap-punchIn-comm c))

      -- By antisymmetry of s: s(τ ∘ swap) = -(s τ)
      fact5 : s x (σ' ∘ punchIn j) ≡ Ax.-_ x (s x (σ ∘ punchIn j))
      fact5 = cong (s x) fact5-eq ∙ snd alt x (σ ∘ punchIn j) i' i₊₁' i'≠i₊₁'

      -- Chain: s(σ ∘ pI i) =[fact1]= s(σ' ∘ pI i₊₁)
      --   =[ih]= negPow d' (s(σ' ∘ pI j))
      --   =[cong fact5]= negPow d' (-(s(σ ∘ pI j)))
      --   = negPow d' (negPow 1 (s(σ ∘ pI j)))
      --   =[negPow-comp]= negPow (d'+1) (s(σ ∘ pI j))
      --   =[+-comm]= negPow (suc d') (s(σ ∘ pI j))
      goal : s x (σ ∘ punchIn i) ≡ negPow (suc d') (s x (σ ∘ punchIn j))
      goal = let v = s x (σ ∘ punchIn j) in
             fact1
           ∙ ih
           ∙ cong (negPow d') fact5
           ∙ negPow-comp d' 1 v
           ∙ cong (λ n → negPow n v) (+-comm d' 1)

  face-shift : {p : ℕ} (s : Cⁿ p) (alt : isAlternating s)
    → (x : S) (σ : Fin (suc (suc p)) → T x)
    → (i j : Fin (suc (suc p))) → fst i <ᵗ fst j → σ i ≡ σ j
    → s x (σ ∘ punchIn i) ≡ negPow (fst j ∸ suc (fst i)) (s x (σ ∘ punchIn j))
  face-shift {p} s alt x σ i j i<j σeq =
    face-shift-aux s alt x (fst j ∸ suc (fst i)) σ i j (suc+∸≡ (fst i) (fst j) i<j) σeq

  -- Key sub-lemmas for d-preserves-alt (to be discharged)
  postulate
    -- Antisymmetry: d s x (σ ∘ swap i j) = -(d s x σ) (for alternating s)
    d-antisym-swap : {p : ℕ} (s : Cⁿ p) (alt : isAlternating s)
      → (x : S) (σ : Fin (suc (suc p)) → T x)
      → (i j : Fin (suc (suc p))) → ¬ (i ≡ j)
      → d s x (σ ∘ swapFin {suc (suc p)} i j) ≡ Ax.-_ x (d s x σ)

  -- The two face terms at repeat positions cancel
  -- Proof: WLOG fst i < fst j. By face-shift, s(face i) = negPow d (s(face j)).
  -- Then negPow(fst i)(negPow d v) + negPow(fst j)(v)
  --    = negPow(predℕ(fst j))(v) + negPow(fst j)(v) = 0.
  face-terms-cancel : {p : ℕ} (s : Cⁿ p) (alt : isAlternating s)
    → (x : S) (σ : Fin (suc (suc p)) → T x)
    → (i j : Fin (suc (suc p))) → ¬ (i ≡ j) → σ i ≡ σ j
    → Ax._+_ x (negPow (fst i) (s x (σ ∘ punchIn i)))
               (negPow (fst j) (s x (σ ∘ punchIn j))) ≡ Ax.0g x
  face-terms-cancel {p} s alt x σ i j i≠j σeq = go (fst i ≟ᵗ fst j)
    where
      _+A_ = Ax._+_ x ; v = s x (σ ∘ punchIn j) ; w = s x (σ ∘ punchIn i)
      fst-i≠j : ¬ (fst i ≡ fst j)
      fst-i≠j e = i≠j (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc p)}) e)
      -- Case fst i < fst j
      go-lt : fst i <ᵗ fst j
        → negPow (fst i) w +A negPow (fst j) v ≡ Ax.0g x
      go-lt i<j =
        let d = fst j ∸ suc (fst i)
            shift = face-shift s alt x σ i j i<j σeq
            arith : fst i + d ≡ predℕ (fst j)
            arith = +∸≡predℕ (fst i) (fst j) i<j
            step1 : negPow (fst i) w ≡ negPow (predℕ (fst j)) v
            step1 = cong (negPow (fst i)) shift
                   ∙ negPow-comp (fst i) d v
                   ∙ cong (λ n → negPow n v) arith
            j>0 : ¬ (fst j ≡ 0)
            j>0 e = ¬<ᵗ0 {fst i} (subst (fst i <ᵗ_) e i<j)
            pred-suc : suc (predℕ (fst j)) ≡ fst j
            pred-suc = sym (suc-predℕ (fst j) j>0)
        in cong (_+A negPow (fst j) v) step1
           ∙ cong (λ n → negPow (predℕ (fst j)) v +A negPow n v) (sym pred-suc)
           ∙ negPow-suc-cancel (predℕ (fst j)) v
      -- Case fst j < fst i: swap and use commutativity
      go-gt : fst j <ᵗ fst i
        → negPow (fst i) w +A negPow (fst j) v ≡ Ax.0g x
      go-gt j<i =
        let d = fst i ∸ suc (fst j)
            shift = face-shift s alt x σ j i j<i (sym σeq)
            arith : fst j + d ≡ predℕ (fst i)
            arith = +∸≡predℕ (fst j) (fst i) j<i
            step1 : negPow (fst j) v ≡ negPow (predℕ (fst i)) w
            step1 = cong (negPow (fst j)) shift
                   ∙ negPow-comp (fst j) d w
                   ∙ cong (λ n → negPow n w) arith
            i>0 : ¬ (fst i ≡ 0)
            i>0 e = ¬<ᵗ0 {fst j} (subst (fst j <ᵗ_) e j<i)
            pred-suc : suc (predℕ (fst i)) ≡ fst i
            pred-suc = sym (suc-predℕ (fst i) i>0)
        in Ax.+Comm x _ _
           ∙ cong (_+A negPow (fst i) w) step1
           ∙ cong (λ n → negPow (predℕ (fst i)) w +A negPow n w) (sym pred-suc)
           ∙ negPow-suc-cancel (predℕ (fst i)) w
      go : Trichotomyᵗ (fst i) (fst j) → _
      go (eqᵗ e) = ⊥.rec (fst-i≠j e)
      go (ltᵗ q) = go-lt q
      go (gtᵗ q) = go-gt q

  -- Vanishing: if σ has a repeat, then d s x σ = 0 (for alternating s)
  -- Uses sfg-two-cancel: terms at k ≠ i,j vanish (face-term-zero),
  -- terms at i,j cancel (face-terms-cancel).
  d-vanish-repeat : {p : ℕ} (s : Cⁿ p) (alt : isAlternating s)
    → (x : S) (σ : Fin (suc (suc p)) → T x)
    → (i j : Fin (suc (suc p))) → ¬ (i ≡ j) → σ i ≡ σ j
    → d s x σ ≡ Ax.0g x
  d-vanish-repeat {p} s alt x σ i j i≠j σeq =
    sfg-two-cancel (suc p) f i j fst-i≠j cancel zeros
    where
      f : Fin (suc (suc p)) → |A| x
      f k = negPow (fst k) (s x (σ ∘ punchIn k))
      fst-i≠j : ¬ (fst i ≡ fst j)
      fst-i≠j e = i≠j (Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc (suc p)}) e)
      cancel : Ax._+_ x (f i) (f j) ≡ Ax.0g x
      cancel = face-terms-cancel s alt x σ i j i≠j σeq
      zeros : (k : Fin (suc (suc p))) → ¬ (fst k ≡ fst i) → ¬ (fst k ≡ fst j)
        → f k ≡ Ax.0g x
      zeros k k≠i k≠j = face-term-zero s (fst alt) σ i j i≠j σeq k k≠i k≠j

  d-preserves-alt : {p : ℕ} (s : Cⁿ p)
    → isAlternating s → isAlternating (d s)
  d-preserves-alt s alt =
    (λ x σ i j i≠j σeq → d-vanish-repeat s alt x σ i j i≠j σeq) ,
    (λ x σ i j i≠j → d-antisym-swap s alt x σ i j i≠j)

  -- ================================================================
  -- Section 5: Main Theorems (Stacks Project Tag 01FG)
  -- ================================================================

  -- Lemma 20.23.6: The chain homotopy
  -- h_n : Cⁿ (suc n) → Cⁿ n such that d∘h + h∘d = id - κ
  -- where κ = c ∘ π
  -- Formula at degree (suc p): for s : Cⁿ (suc p),
  --   d (h p s) + h (suc p) (d s) = s - κ s
  postulate
    cπ-homotopic-to-id :
      (κ : {n : ℕ} → Cⁿ n → Cⁿ n)
      (h : (n : ℕ) → Cⁿ (suc n) → Cⁿ n)
      → {p : ℕ} (s : Cⁿ (suc p)) (x : S) (σ : Fin (suc (suc p)) → T x)
      → Ax._+_ x (d (h p s) x σ) (h (suc p) (d s) x σ)
        ≡ Ax._+_ x (s x σ) (Ax.-_ x (κ s x σ))

  -- Lemma 20.23.7: Contractibility when U_i = X
  postulate
    contractible-with-section : {p : ℕ}
      → (x₀ : S) → T x₀
      → (s : Cⁿ-alt (suc p))
      → Σ (Cⁿ-alt p) (λ t → d (ιmap t) ≡ ιmap s)

-- ================================================================
-- Section 6: Connection to Part14
-- ================================================================

module ConnectionToPart14 {ℓ : Level}
  (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where

  open GeneralCech S T A

  to-simple-C⁰ : Cⁿ 0 → ((x : S) → T x → |A| x)
  to-simple-C⁰ s x t = s x (λ _ → t)

  from-simple-C⁰ : ((x : S) → T x → |A| x) → Cⁿ 0
  from-simple-C⁰ s x σ = s x (σ fzero)

  to-simple-C¹ : Cⁿ 1 → ((x : S) → T x → T x → |A| x)
  to-simple-C¹ s x u v = s x tup
    where
      tup : Fin 2 → T x
      tup (zero , _) = u
      tup (suc zero , _) = v

  from-simple-C¹ : ((x : S) → T x → T x → |A| x) → Cⁿ 1
  from-simple-C¹ s x σ = s x (σ fzero) (σ fone)

  mk2Tuple : {B : Type ℓ} → B → B → Fin 2 → B
  mk2Tuple a b (zero , _) = a
  mk2Tuple a b (suc zero , _) = b

  mk3Tuple : {B : Type ℓ} → B → B → B → Fin 3 → B
  mk3Tuple u v w (zero , _) = u
  mk3Tuple u v w (suc zero , _) = v
  mk3Tuple u v w (suc (suc zero) , _) = w

  -- Face map equalities relating face maps of mk3Tuple to mk2Tuple/σ
  private
    face0≡ : {x : S} (u v w : T x)
      → faceMap fzero (mk3Tuple u v w) ≡ mk2Tuple v w
    face0≡ u v w = funExt go where
      go : ∀ k → _
      go (zero , _) = refl
      go (suc zero , _) = refl
      go (suc (suc _) , q) = ⊥.rec q

    face1≡ : {x : S} (u v w : T x)
      → faceMap fone (mk3Tuple u v w) ≡ mk2Tuple u w
    face1≡ u v w = funExt go where
      go : ∀ k → _
      go (zero , _) = refl
      go (suc zero , _) = refl
      go (suc (suc _) , q) = ⊥.rec q

    face2≡ : {x : S} (u v w : T x)
      → faceMap (2 , tt) (mk3Tuple u v w) ≡ mk2Tuple u v
    face2≡ u v w = funExt go where
      go : ∀ k → _
      go (zero , _) = refl
      go (suc zero , _) = refl
      go (suc (suc _) , q) = ⊥.rec q

    mk2≡σ : {x : S} (σ : Fin 2 → T x) → mk2Tuple (σ fzero) (σ fone) ≡ σ
    mk2≡σ σ = funExt go where
      go : ∀ k → _
      go (zero , _) = refl
      go (suc zero , _) = refl
      go (suc (suc _) , q) = ⊥.rec q

  section-exact : ((x : S) → T x)
    → (β : Cⁿ 1) → ((x : S) (u v w : T x) →
        d β x (mk3Tuple u v w) ≡ Ax.0g x)
    → Σ (Cⁿ 0) (λ α → ∀ x σ → d α x σ ≡ β x σ)
  section-exact t β cocycle = α , proof
    where
      α : Cⁿ 0
      α x σ = β x (mk2Tuple (t x) (σ fzero))

      proof : ∀ x σ → d α x σ ≡ β x σ
      proof x σ =
        let p = σ fzero ; q = σ fone
            _+_ = Ax._+_ x ; -_ = Ax.-_ x ; 0g = Ax.0g x
            c = β x (mk2Tuple (t x) p)  -- = α x (faceMap fone σ)
            b = β x (mk2Tuple (t x) q)  -- = α x (faceMap fzero σ)
            -- Raw cocycle: d β x (mk3Tuple (t x) p q) ≡ 0g
            -- Definitionally: -(-(β face2)) + (-(β face1) + (β face0 + 0g)) ≡ 0g
            -- Convert using face≡ + invInv to: c + (-b + (β σ + 0g)) ≡ 0g
            cocyc-conv : (- (- (β x (faceMap (2 , tt) (mk3Tuple (t x) p q)))))
                         + ((- (β x (faceMap fone (mk3Tuple (t x) p q))))
                         + (β x (faceMap fzero (mk3Tuple (t x) p q)) + 0g))
                       ≡ c + ((- b) + (β x σ + 0g))
            cocyc-conv =
              cong₂ _+_
                (Gx.invInv x _ ∙ cong (β x) (face2≡ (t x) p q))
                (cong₂ _+_
                  (cong -_ (cong (β x) (face1≡ (t x) p q)))
                  (cong (_+ 0g) (cong (β x) (face0≡ (t x) p q ∙ mk2≡σ σ))))
            cocyc' : c + ((- b) + (β x σ + 0g)) ≡ 0g
            cocyc' = sym cocyc-conv ∙ cocycle x (t x) p q
            -- From cocyc': c + (-b + a) = 0 (after +IdR)
            -- invUniqueR: -b + a = -c
            -- Then: -c + b = a (algebraic rearrangement)
            step1 : c + ((- b) + β x σ) ≡ 0g
            step1 = subst (λ z → c + ((- b) + z) ≡ 0g) (Ax.+IdR x (β x σ)) cocyc'
            step2 : (- b) + β x σ ≡ - c
            step2 = Gx.invUniqueR x step1
        in
        (- c) + (b + 0g)
          ≡⟨ cong ((- c) +_) (Ax.+IdR x b) ⟩
        (- c) + b
          ≡⟨ Ax.+Comm x (- c) b ⟩
        b + (- c)
          ≡⟨ cong (b +_) (sym step2) ⟩
        b + ((- b) + β x σ)
          ≡⟨ Ax.+Assoc x b (- b) (β x σ) ⟩
        (b + (- b)) + β x σ
          ≡⟨ cong (_+ β x σ) (Ax.+InvR x b) ⟩
        0g + β x σ
          ≡⟨ Ax.+IdL x (β x σ) ⟩
        β x σ ∎

-- ================================================================
-- Section 7: Cochain Complex Structure
-- ================================================================

module CechCoChainComplex {ℓ : Level}
  (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ)
  (isSetS : isSet S)
  (isSetT : (x : S) → isSet (T x)) where

  open GeneralCech S T A

  CⁿAb : ℕ → AbGroup ℓ
  CⁿAb = CⁿAbGroup

  dHom : (p : ℕ) → AbGroupHom (CⁿAb p) (CⁿAb (suc p))
  fst (dHom p) = d {p}
  snd (dHom p) = makeIsGroupHom
    (λ s t → funExt λ x → funExt λ σ → d-pres+ s t x σ)

  d²=0 : (p : ℕ) → compGroupHom (dHom p) (dHom (suc p)) ≡ trivGroupHom
  d²=0 p = Σ≡Prop (λ _ → isPropIsGroupHom _ _)
    (funExt λ s → funExt λ x → funExt λ σ → d² s x σ)

  CechCoChain : CoChainComplex ℓ
  CoChainComplex.cochain CechCoChain = CⁿAb
  CoChainComplex.cobdry CechCoChain = dHom
  CoChainComplex.cobdry²=0 CechCoChain = d²=0
