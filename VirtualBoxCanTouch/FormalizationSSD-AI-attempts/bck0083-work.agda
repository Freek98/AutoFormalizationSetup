{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module work where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit

-- ════════════════════════════════════════════════════════════════
-- § Inductive ≤ (≤E) — better for recursion/induction on proofs
-- ════════════════════════════════════════════════════════════════

data _≤E_ : ℕ → ℕ → Type where
  ≤E-refl : {n : ℕ} → n ≤E n
  ≤E-step : {n m : ℕ} → n ≤E m → n ≤E suc m

suc-≤E-suc : {n m : ℕ} → n ≤E m → suc n ≤E suc m
suc-≤E-suc ≤E-refl = ≤E-refl
suc-≤E-suc (≤E-step c) = ≤E-step (suc-≤E-suc c)

≤E-sucʳ : {n : ℕ} → n ≤E suc n
≤E-sucʳ = ≤E-step ≤E-refl

≤E-trans : {n m k : ℕ} → n ≤E m → m ≤E k → n ≤E k
≤E-trans p ≤E-refl = p
≤E-trans p (≤E-step q) = ≤E-step (≤E-trans p q)

-- Conversion to/from library ≤
≤E→≤ : {n m : ℕ} → n ≤E m → n ≤ m
≤E→≤ ≤E-refl = ≤-refl
≤E→≤ (≤E-step p) = ≤-suc (≤E→≤ p)

≤→≤E : {n m : ℕ} → n ≤ m → n ≤E m
≤→≤E {n} {m} (k , p) = go n m k p where
  go : (n m k : ℕ) → k + n ≡ m → n ≤E m
  go n m zero p = subst (n ≤E_) p ≤E-refl
  go n zero (suc k) p = ex-falso (¬-<-zero (n , +-comm n (suc k) ∙ p))
  go n (suc m) (suc k) p = ≤E-step (go n m k (cong predℕ p))

-- ≤→≤E commutes with the successor step (definitional on concrete pairs)
≤→≤E-suc : {n m : ℕ} (p : n ≤ m) → ≤→≤E (≤-suc p) ≡ ≤E-step (≤→≤E p)
≤→≤E-suc (k , e) = refl

-- ≤E is a proposition (via retract of isProp≤)
≤E-retract : {n m : ℕ} (p : n ≤E m) → ≤→≤E (≤E→≤ p) ≡ p
≤E-retract ≤E-refl = transportRefl ≤E-refl
≤E-retract (≤E-step q) = ≤→≤E-suc (≤E→≤ q) ∙ cong ≤E-step (≤E-retract q)

isProp≤E : {n m : ℕ} → isProp (n ≤E m)
isProp≤E p q =
  sym (≤E-retract p) ∙ cong ≤→≤E (isProp≤ (≤E→≤ p) (≤E→≤ q)) ∙ ≤E-retract q

-- ════════════════════════════════════════════════════════════════
-- § Sequential colimit: iterated maps and incl compatibility
-- ════════════════════════════════════════════════════════════════

module SeqColimMaps {ℓ : Level} (S : Sequence ℓ) where

  private
    X = Sequence.obj S
    f = Sequence.map S

  -- Iterated map: for n ≤E m, transport X n → X m
  -- Base: identity.  Step: apply f.
  ι : {n m : ℕ} → n ≤E m → X n → X m
  ι ≤E-refl x = x
  ι (≤E-step p) x = f (ι p x)

  -- Version taking library ≤
  ι≤ : {n m : ℕ} → n ≤ m → X n → X m
  ι≤ p = ι (≤→≤E p)

  -- ι is proof-irrelevant (since ≤E is a prop)
  ι-propIrrel : {n m : ℕ} (p q : n ≤E m) (x : X n) → ι p x ≡ ι q x
  ι-propIrrel p q x = cong (λ r → ι r x) (isProp≤E p q)

  -- ι respects composition
  ι-comp : {n m k : ℕ} (p : n ≤E m) (q : m ≤E k) (x : X n)
    → ι q (ι p x) ≡ ι (≤E-trans p q) x
  ι-comp p ≤E-refl x = refl
  ι-comp p (≤E-step q) x = cong f (ι-comp p q x)

  -- THE KEY LEMMA: incl x ≡ incl (ι p x)
  -- By induction on ≤E: refl for base, push ∙ IH for step.
  ι-incl : {n m : ℕ} (p : n ≤E m) (x : X n)
    → incl {X = S} x ≡ incl (ι p x)
  ι-incl ≤E-refl x = refl
  ι-incl (≤E-step p) x =
    ι-incl p x ∙ push (ι p x)

  -- Version for library ≤
  ι≤-incl : {n m : ℕ} (p : n ≤ m) (x : X n)
    → incl {X = S} x ≡ incl (ι≤ p x)
  ι≤-incl p = ι-incl (≤→≤E p)

  -- Preservation: equal at level k implies equal at any level l ≥ k
  ι-pres : {n m k l : ℕ}
    (p : n ≤E k) (q : m ≤E k) (r : k ≤E l)
    (s : n ≤E l) (t : m ≤E l)
    (x : X n) (y : X m)
    → ι p x ≡ ι q y → ι s x ≡ ι t y
  ι-pres {n} {m} {k} {l} p q r s t x y e =
    ι s x               ≡⟨ ι-propIrrel s (≤E-trans p r) x ⟩
    ι (≤E-trans p r) x   ≡⟨ sym (ι-comp p r x) ⟩
    ι r (ι p x)          ≡⟨ cong (ι r) e ⟩
    ι r (ι q y)          ≡⟨ ι-comp q r y ⟩
    ι (≤E-trans q r) y   ≡⟨ ι-propIrrel (≤E-trans q r) t y ⟩
    ι t y               ∎
