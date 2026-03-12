{-# OPTIONS --cubical --guardedness #-}

module LLPOwork.EvenOdd where

-- ═══════════════════════════════════════════════════════════════
-- Even/Odd library for natural numbers
-- Multiple interfaces: Bool-valued, Type-valued, Σ-witness, data
-- ═══════════════════════════════════════════════════════════════

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Bool
  hiding (_≤_ ; _≥_)
open import Cubical.Data.Nat
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary

-- ───────────────────────────────────────────────────────────────
-- Section 1: Core functions (double, half)
-- ───────────────────────────────────────────────────────────────

double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- ───────────────────────────────────────────────────────────────
-- Section 2: double n ≡ n +ℕ n
-- ───────────────────────────────────────────────────────────────

double≡+self : (n : ℕ) → double n ≡ n +ℕ n
double≡+self zero = refl
double≡+self (suc n) =
  cong suc (cong suc (double≡+self n) ∙ sym (+-suc n n))

-- ───────────────────────────────────────────────────────────────
-- Section 3: Bool-valued parity identities
-- ───────────────────────────────────────────────────────────────

-- isEven, isOdd : ℕ → Bool  are from Cubical.Data.Nat

isEven-suc-suc : (n : ℕ) → isEven (suc (suc n)) ≡ isEven n
isEven-suc-suc n = refl

isOdd≡not-isEven : (n : ℕ) → isOdd n ≡ not (isEven n)
isOdd≡not-isEven zero = refl
isOdd≡not-isEven (suc zero) = refl
isOdd≡not-isEven (suc (suc n)) = isOdd≡not-isEven n

isEven≡not-isOdd : (n : ℕ) → isEven n ≡ not (isOdd n)
isEven≡not-isOdd zero = refl
isEven≡not-isOdd (suc zero) = refl
isEven≡not-isOdd (suc (suc n)) = isEven≡not-isOdd n

-- Complement lemmas
isEven-false→isOdd-true : {n : ℕ} → isEven n ≡ false → isOdd n ≡ true
isEven-false→isOdd-true {n} p = isOdd≡not-isEven n ∙ cong not p

isOdd-false→isEven-true : {n : ℕ} → isOdd n ≡ false → isEven n ≡ true
isOdd-false→isEven-true {n} p = isEven≡not-isOdd n ∙ cong not p

-- ───────────────────────────────────────────────────────────────
-- Section 4: isEven/isOdd of double and suc∘double
-- ───────────────────────────────────────────────────────────────

isEven-double : (k : ℕ) → isEven (double k) ≡ true
isEven-double zero = refl
isEven-double (suc k) = isEven-double k

isEven-suc-double : (k : ℕ) → isEven (suc (double k)) ≡ false
isEven-suc-double zero = refl
isEven-suc-double (suc k) = isEven-suc-double k

isOdd-double : (k : ℕ) → isOdd (double k) ≡ false
isOdd-double zero = refl
isOdd-double (suc k) = isOdd-double k

isOdd-suc-double : (k : ℕ) → isOdd (suc (double k)) ≡ true
isOdd-suc-double k = isEven-double k

-- ───────────────────────────────────────────────────────────────
-- Section 5: half ∘ double and double ∘ half round-trips
-- ───────────────────────────────────────────────────────────────

half-double : (k : ℕ) → half (double k) ≡ k
half-double zero = refl
half-double (suc k) = cong suc (half-double k)

half-suc-double : (k : ℕ) → half (suc (double k)) ≡ k
half-suc-double zero = refl
half-suc-double (suc k) = cong suc (half-suc-double k)

double-half-even : (n : ℕ) → isEven n ≡ true → double (half n) ≡ n
double-half-even zero _ = refl
double-half-even (suc zero) p = ⊥.rec (false≢true p)
double-half-even (suc (suc n)) p = cong (suc ∘ suc) (double-half-even n p)

suc-double-half-odd : (n : ℕ) → isEven n ≡ false → suc (double (half n)) ≡ n
suc-double-half-odd zero p = ⊥.rec (true≢false p)
suc-double-half-odd (suc zero) _ = refl
suc-double-half-odd (suc (suc n)) p = cong (suc ∘ suc) (suc-double-half-odd n p)

-- ───────────────────────────────────────────────────────────────
-- Section 6: Inductive data type for parity
-- ───────────────────────────────────────────────────────────────

data Parity : ℕ → Type where
  even : (k : ℕ) → Parity (double k)
  odd  : (k : ℕ) → Parity (suc (double k))

parity : (n : ℕ) → Parity n
parity zero = even zero
parity (suc n) with parity n
... | even k = odd k
... | odd k  = even (suc k)

-- ───────────────────────────────────────────────────────────────
-- Section 7: Σ-type witnesses
-- ───────────────────────────────────────────────────────────────

-- n is even ↔ ∃ k, n ≡ double k
Even : ℕ → Type
Even n = Σ[ k ∈ ℕ ] n ≡ double k

-- n is odd ↔ ∃ k, n ≡ suc (double k)
Odd : ℕ → Type
Odd n = Σ[ k ∈ ℕ ] n ≡ suc (double k)

-- n is even ↔ ∃ k, n ≡ k + k
Even+ : ℕ → Type
Even+ n = Σ[ k ∈ ℕ ] n ≡ k +ℕ k

-- n is odd ↔ ∃ k, n ≡ k + k + 1
Odd+ : ℕ → Type
Odd+ n = Σ[ k ∈ ℕ ] n ≡ k +ℕ k +ℕ 1

-- n is odd ↔ ∃ k, n ≡ 1 + (k + k)
Odd+' : ℕ → Type
Odd+' n = Σ[ k ∈ ℕ ] n ≡ 1 +ℕ (k +ℕ k)

-- ───────────────────────────────────────────────────────────────
-- Section 8: Conversions between Even/Odd interfaces
-- ───────────────────────────────────────────────────────────────

Even→Even+ : {n : ℕ} → Even n → Even+ n
Even→Even+ (k , p) = k , p ∙ double≡+self k

Even+→Even : {n : ℕ} → Even+ n → Even n
Even+→Even (k , p) = k , p ∙ sym (double≡+self k)

Odd→Odd+ : {n : ℕ} → Odd n → Odd+ n
Odd→Odd+ (k , p) = k , p ∙ cong suc (double≡+self k) ∙ +-comm 1 (k +ℕ k)

Odd+→Odd : {n : ℕ} → Odd+ n → Odd n
Odd+→Odd (k , p) = k , p ∙ +-comm (k +ℕ k) 1 ∙ cong suc (sym (double≡+self k))

Odd→Odd+' : {n : ℕ} → Odd n → Odd+' n
Odd→Odd+' (k , p) = k , p ∙ cong suc (double≡+self k)

Odd+'→Odd : {n : ℕ} → Odd+' n → Odd n
Odd+'→Odd (k , p) = k , p ∙ cong suc (sym (double≡+self k))

-- ───────────────────────────────────────────────────────────────
-- Section 9: Bool-valued ↔ Σ-witness conversions
-- ───────────────────────────────────────────────────────────────

-- isEven true → Even (using half)
isEven→Even : {n : ℕ} → isEven n ≡ true → Even n
isEven→Even {n} p = half n , sym (double-half-even n p)

-- Even → isEven true
Even→isEven : {n : ℕ} → Even n → isEven n ≡ true
Even→isEven (k , p) = subst (λ m → isEven m ≡ true) (sym p) (isEven-double k)

-- isEven false → Odd (using half)
isEvenFalse→Odd : {n : ℕ} → isEven n ≡ false → Odd n
isEvenFalse→Odd {n} p = half n , sym (suc-double-half-odd n p)

-- Odd → isEven false
Odd→isEvenFalse : {n : ℕ} → Odd n → isEven n ≡ false
Odd→isEvenFalse (k , p) = subst (λ m → isEven m ≡ false) (sym p) (isEven-suc-double k)

-- isOdd true → Odd
isOdd→Odd : {n : ℕ} → isOdd n ≡ true → Odd n
isOdd→Odd {n} p = isEvenFalse→Odd (isEven≡not-isOdd n ∙ cong not p)

-- Odd → isOdd true
Odd→isOdd : {n : ℕ} → Odd n → isOdd n ≡ true
Odd→isOdd {n} o = isEven-false→isOdd-true {n} (Odd→isEvenFalse o)

-- isOdd false → Even
isOddFalse→Even : {n : ℕ} → isOdd n ≡ false → Even n
isOddFalse→Even {n} p = isEven→Even (isOdd-false→isEven-true {n} p)

-- Even → isOdd false
Even→isOdd : {n : ℕ} → Even n → isOdd n ≡ false
Even→isOdd {n} e = isOdd≡not-isEven n ∙ cong not (Even→isEven e)

-- ───────────────────────────────────────────────────────────────
-- Section 10: Parity data ↔ other interfaces
-- ───────────────────────────────────────────────────────────────

Parity→Even⊎Odd : {n : ℕ} → Parity n → Even n ⊎ Odd n
Parity→Even⊎Odd (even k) = inl (k , refl)
Parity→Even⊎Odd (odd k)  = inr (k , refl)

Even→Parity : {n : ℕ} → Even n → Parity n
Even→Parity (k , p) = subst Parity (sym p) (even k)

Odd→Parity : {n : ℕ} → Odd n → Parity n
Odd→Parity (k , p) = subst Parity (sym p) (odd k)

-- ───────────────────────────────────────────────────────────────
-- Section 11: Decidability and mutual exclusion
-- ───────────────────────────────────────────────────────────────

even-or-odd : (n : ℕ) → Even n ⊎ Odd n
even-or-odd n = Parity→Even⊎Odd (parity n)

¬Even∧Odd : {n : ℕ} → Even n → Odd n → ⊥
¬Even∧Odd e o = true≢false (sym (Even→isEven e) ∙ Odd→isEvenFalse o)

even-xor-odd : (n : ℕ) → (Even n × (Odd n → ⊥)) ⊎ (Odd n × (Even n → ⊥))
even-xor-odd n with even-or-odd n
... | inl e = inl (e , λ o → ¬Even∧Odd e o)
... | inr o = inr (o , λ e → ¬Even∧Odd e o)

-- ───────────────────────────────────────────────────────────────
-- Section 12: Even/Odd of zero, suc, double
-- ───────────────────────────────────────────────────────────────

Even-zero : Even zero
Even-zero = 0 , refl

Odd-one : Odd 1
Odd-one = 0 , refl

Even-double : (k : ℕ) → Even (double k)
Even-double k = k , refl

Odd-suc-double : (k : ℕ) → Odd (suc (double k))
Odd-suc-double k = k , refl

-- suc swaps parity
Even-suc→Odd : {n : ℕ} → Even (suc n) → Odd n
Even-suc→Odd (zero , p) = ⊥.rec (snotz p)
Even-suc→Odd (suc k , p) = k , injSuc p

Odd-suc→Even : {n : ℕ} → Odd (suc n) → Even n
Odd-suc→Even (k , p) = k , injSuc p

Even→Odd-suc : {n : ℕ} → Even n → Odd (suc n)
Even→Odd-suc (k , p) = k , cong suc p

Odd→Even-suc : {n : ℕ} → Odd n → Even (suc n)
Odd→Even-suc (k , p) = suc k , cong suc p

-- ───────────────────────────────────────────────────────────────
-- Section 13: Injectivity of double
-- ───────────────────────────────────────────────────────────────

double-inj : (m n : ℕ) → double m ≡ double n → m ≡ n
double-inj zero zero _ = refl
double-inj zero (suc n) p = ⊥.rec (znots p)
double-inj (suc m) zero p = ⊥.rec (snotz p)
double-inj (suc m) (suc n) p = cong suc (double-inj m n (injSuc (injSuc p)))

suc-double-inj : (m n : ℕ) → suc (double m) ≡ suc (double n) → m ≡ n
suc-double-inj m n p = double-inj m n (injSuc p)

-- double k ≠ suc (double j) : even ≠ odd
double≢suc-double : (j k : ℕ) → double k ≡ suc (double j) → ⊥
double≢suc-double j k p = true≢false (sym (isEven-double k) ∙ subst (λ m → isEven m ≡ false) (sym p) (isEven-suc-double j))

-- Even and Odd witnesses are unique
Even-unique : {n : ℕ} → (e₁ e₂ : Even n) → fst e₁ ≡ fst e₂
Even-unique (j , p) (k , q) = double-inj j k (sym p ∙ q)

Odd-unique : {n : ℕ} → (o₁ o₂ : Odd n) → fst o₁ ≡ fst o₂
Odd-unique (j , p) (k , q) = suc-double-inj j k (sym p ∙ q)

-- ───────────────────────────────────────────────────────────────
-- Section 14: Reconstruction from parity and half
-- ───────────────────────────────────────────────────────────────

-- If two numbers have the same parity and same half, they are equal
even→eq : (n m : ℕ) → isEven n ≡ true → isEven m ≡ true → half n ≡ half m → n ≡ m
even→eq n m en em hq =
  sym (double-half-even n en) ∙ cong double hq ∙ double-half-even m em

odd→eq : (n m : ℕ) → isEven n ≡ false → isEven m ≡ false → half n ≡ half m → n ≡ m
odd→eq n m on om hq =
  sym (suc-double-half-odd n on) ∙ cong (suc ∘ double) hq ∙ suc-double-half-odd m om

-- ───────────────────────────────────────────────────────────────
-- Section 15: half is bounded
-- ───────────────────────────────────────────────────────────────

half≤ : (n : ℕ) → half n ≤ n
half≤ zero = zero , refl
half≤ (suc zero) = 1 , refl
half≤ (suc (suc n)) =
  let (d , p) = half≤ n
  in suc d , cong suc (+-suc d (half n)) ∙ cong (suc ∘ suc) p

-- ───────────────────────────────────────────────────────────────
-- Section 16: double is monotone
-- ───────────────────────────────────────────────────────────────

double-suc : (n : ℕ) → double (suc n) ≡ suc (suc (double n))
double-suc n = refl

private
  double-+ : (a b : ℕ) → double (a +ℕ b) ≡ double a +ℕ double b
  double-+ zero b = refl
  double-+ (suc a) b = cong (suc ∘ suc) (double-+ a b)

double-mono : (m n : ℕ) → m ≤ n → double m ≤ double n
double-mono m n (d , p) = double d , sym (double-+ d m) ∙ cong double p

-- ───────────────────────────────────────────────────────────────
-- Section 17: Parity of addition
-- ───────────────────────────────────────────────────────────────

Even+Even→Even : {m n : ℕ} → Even m → Even n → Even (m +ℕ n)
Even+Even→Even {m} {n} (j , p) (k , q) =
  j +ℕ k , cong (_+ℕ n) p ∙ cong (double j +ℕ_) q ∙ sym (double-+ j k)

Odd+Odd→Even : {m n : ℕ} → Odd m → Odd n → Even (m +ℕ n)
Odd+Odd→Even {m} {n} (j , p) (k , q) =
  suc (j +ℕ k) , cong (_+ℕ n) p ∙ cong (suc (double j) +ℕ_) q ∙ lem j k
  where
  lem : (a b : ℕ) → suc (double a) +ℕ suc (double b) ≡ double (suc (a +ℕ b))
  lem zero b = refl
  lem (suc a) b = cong (suc ∘ suc) (lem a b)

Even+Odd→Odd : {m n : ℕ} → Even m → Odd n → Odd (m +ℕ n)
Even+Odd→Odd {m} {n} (j , p) (k , q) =
  j +ℕ k , cong (_+ℕ n) p ∙ cong (double j +ℕ_) q ∙ lem j k
  where
  lem : (a b : ℕ) → double a +ℕ suc (double b) ≡ suc (double (a +ℕ b))
  lem zero b = refl
  lem (suc a) b = cong (suc ∘ suc) (lem a b)

Odd+Even→Odd : {m n : ℕ} → Odd m → Even n → Odd (m +ℕ n)
Odd+Even→Odd {m} {n} (j , p) (k , q) =
  j +ℕ k , cong (_+ℕ n) p ∙ cong (suc (double j) +ℕ_) q ∙ lem j k
  where
  lem : (a b : ℕ) → suc (double a) +ℕ double b ≡ suc (double (a +ℕ b))
  lem zero b = refl
  lem (suc a) b = cong (suc ∘ suc) (lem a b)

-- ───────────────────────────────────────────────────────────────
-- Section 18: Convenience eliminators
-- ───────────────────────────────────────────────────────────────

-- Eliminate by parity into any type family
parityElim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → ((k : ℕ) → A (double k))
  → ((k : ℕ) → A (suc (double k)))
  → (n : ℕ) → A n
parityElim fe fo n with parity n
... | even k = fe k
... | odd k  = fo k

-- Non-dependent parity case split
parityRec : ∀ {ℓ} {A : Type ℓ}
  → ((k : ℕ) → A)
  → ((k : ℕ) → A)
  → (n : ℕ) → A
parityRec {A = A} fe fo = parityElim {A = λ _ → A} fe fo

-- Case split using Even/Odd witnesses
evenOddElim : ∀ {ℓ} {A : ℕ → Type ℓ}
  → ((n : ℕ) → Even n → A n)
  → ((n : ℕ) → Odd n → A n)
  → (n : ℕ) → A n
evenOddElim fe fo n with even-or-odd n
... | inl e = fe n e
... | inr o = fo n o
