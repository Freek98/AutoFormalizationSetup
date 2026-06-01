{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module work where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence using (hPropExt)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit
open import Cubical.Relation.Nullary
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)

-- ════════════════════════════════════════════════════════════════
-- § Inductive ≤ (≤E) — better for recursion/induction on proofs
-- ════════════════════════════════════════════════════════════════

data _≤E_ : ℕ → ℕ → Type where
  ≤E-refl : {n : ℕ} → n ≤E n
  ≤E-step : {n m : ℕ} → n ≤E m → n ≤E suc m

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
isProp≤E = isPropRetract ≤E→≤ ≤→≤E ≤E-retract isProp≤

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
    ι s x                ≡⟨ ι-propIrrel s (≤E-trans p r) x ⟩
    ι (≤E-trans p r) x   ≡⟨ sym (ι-comp p r x) ⟩
    ι r (ι p x)          ≡⟨ cong (ι r) e ⟩
    ι r (ι q y)          ≡⟨ ι-comp q r y ⟩
    ι (≤E-trans q r) y   ≡⟨ ι-propIrrel (≤E-trans q r) t y ⟩
    ι t y               ∎

-- ════════════════════════════════════════════════════════════════
-- § Finite-type sequential colimits (decidable equality witnesses)
-- ════════════════════════════════════════════════════════════════

-- Decidable Σ over propositions
decΣProp : {A : Type} {B : A → Type}
  → isProp A → ((a : A) → isProp (B a))
  → Dec A → ((a : A) → Dec (B a)) → Dec (Σ A B)
decΣProp Ap Bp (yes a) Bd with Bd a
... | yes b = yes (a , b)
... | no ¬b = no λ (a' , b) → ¬b (subst _ (Ap a' a) b)
decΣProp Ap Bp (no ¬a) Bd = no (¬a ∘ fst)

≤E-Dec : (n m : ℕ) → Dec (n ≤E m)
≤E-Dec n m with ≤Dec n m
... | yes p = yes (≤→≤E p)
... | no ¬p = no (¬p ∘ ≤E→≤)

module FiniteSeqColim
  (X : ℕ → Type) (Xmap : {n : ℕ} → X n → X (suc n))
  (isFin : (n : ℕ) → isFinSet (X n)) where

  Xseq : Sequence _
  Xseq .Sequence.obj = X
  Xseq .Sequence.map = Xmap

  open SeqColimMaps Xseq public

  X∞ : Type
  X∞ = SeqColim Xseq

  -- Two elements agree at level k if they both map into X k and become equal
  EqualAt : {n m : ℕ} → X n → X m → ℕ → Type
  EqualAt {n} {m} x y k =
    Σ[ p ∈ n ≤E k ] Σ[ q ∈ m ≤E k ] ι p x ≡ ι q y

  isPropEqualAt : {n m : ℕ} {x : X n} {y : X m} (k : ℕ) → isProp (EqualAt x y k)
  isPropEqualAt k =
    isPropΣ isProp≤E λ _ →
    isPropΣ isProp≤E λ _ →
    isFinSet→isSet (isFin k) _ _

  isDecEqualAt : {n m : ℕ} {x : X n} {y : X m} (k : ℕ) → Dec (EqualAt x y k)
  isDecEqualAt {n} {m} k =
    decΣProp isProp≤E (λ _ → isPropΣ isProp≤E λ _ → isFinSet→isSet (isFin k) _ _)
      (≤E-Dec n k) λ _ →
    decΣProp isProp≤E (λ _ → isFinSet→isSet (isFin k) _ _)
      (≤E-Dec m k) λ _ →
    isFinSet→Discrete (isFin k) _ _

  EqWitness : {n m : ℕ} → X n → X m → Type
  EqWitness x y = Σ[ k ∈ ℕ ] EqualAt x y k

  EqWitness-splitSupport : {n m : ℕ} (x : X n) (y : X m) → SplitSupport (EqWitness x y)
  EqWitness-splitSupport x y =
    Collapsible→SplitSupport (Decidable→Collapsible isPropEqualAt isDecEqualAt)

  EqWitness-refl : {n : ℕ} (x : X n) → EqWitness x x
  EqWitness-refl x = _ , ≤E-refl , ≤E-refl , refl

  EqWitness-sym : {n m : ℕ} (x : X n) (y : X m) → EqWitness x y → EqWitness y x
  EqWitness-sym _ _ (k , p , q , e) = k , q , p , sym e

  EqWitness-suc : {n : ℕ} (x : X n) → EqWitness x (Xmap x)
  EqWitness-suc x = _ , ≤E-step ≤E-refl , ≤E-refl , refl

  EqWitness-trans : {n m l : ℕ} (x : X n) (y : X m) (z : X l)
    → EqWitness x y → EqWitness y z → EqWitness x z
  EqWitness-trans x y z (j , p₁ , q₁ , e₁) (k , p₂ , q₂ , e₂) =
    _ ,
    ≤E-trans p₁ jk ,
    ≤E-trans q₂ kk ,
    ι-pres p₁ q₁ jk (≤E-trans p₁ jk) mjk x y e₁
    ∙ ι-pres p₂ q₂ kk mjk (≤E-trans q₂ kk) y z e₂
    where
    jk = ≤→≤E (left-≤-max {m = j})
    kk = ≤→≤E (right-≤-max {m = j})
    mjk = ≤E-trans q₁ jk

  -- Push compatibility (needed for Code over push)
  EqWitness-push→ : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → EqWitness x (Xmap y)
  EqWitness-push→ x y w = EqWitness-trans x y _ w (EqWitness-suc y)

  EqWitness-push← : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x (Xmap y) → EqWitness x y
  EqWitness-push← x y w = EqWitness-trans x (Xmap y) y w (EqWitness-sym y _ (EqWitness-suc y))

  -- From witness to path in the colimit
  EqWitness→Path : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → incl {X = Xseq} x ≡ incl y
  EqWitness→Path x y (k , p , q , e) =
    ι-incl p x ∙ cong incl e ∙ sym (ι-incl q y)

  -- Encode-decode
  Code : (n : ℕ) → X n → X∞ → Type
  Code n x (incl y) = ∥ EqWitness x y ∥₁
  Code n x (push y i) =
    hPropExt squash₁ squash₁
      (PT.map (EqWitness-push→ x y))
      (PT.map (EqWitness-push← x y)) i

  encode : (n : ℕ) (x : X n) (y : X∞) → incl x ≡ y → Code n x y
  encode n x y p = J (λ y _ → Code n x y) ∣ EqWitness-refl x ∣₁ p
