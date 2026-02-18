{-# OPTIONS --cubical --guardedness #-}

-- tex Section 1.1: Preliminaries (lines 126-280)

module SSD.StoneDuality.Preliminaries where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.Foundations.Isomorphism using (Iso)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
import SSD.Library.QuotientBool as QB
import Cubical.Data.Sum as ⊎

-- tex Definition 148-155: Countable, Countably presented Boolean algebra
-- (These are defined in the library: SSD.Library.PresentedBoole)

-- Basic definitions

binarySequence : Type₀
binarySequence = ℕ → Bool

CantorSpace : Type₀
CantorSpace = binarySequence

_↔_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

infixr 3 _↔_

-- tex Definition 672: Open and Closed propositions

isOpenWitness : hProp ℓ-zero → Type₀
isOpenWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ (Σ[ n ∈ ℕ ] α n ≡ true)

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = ∥ isOpenWitness P ∥₁

isPropIsOpenProp : {P : hProp ℓ-zero} → isProp (isOpenProp P)
isPropIsOpenProp = squash₁

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = ∃[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false)

isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)
isPropIsClosedProp = squash₁

Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P

¬hProp : hProp ℓ-zero → hProp ℓ-zero
¬hProp P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

-- tex Remark 676: Negation of open is closed

negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬hProp P)
negOpenIsClosed P Popen = PT.rec squash₁ go Popen
  where
  go : isOpenWitness P → isClosedProp (¬hProp P)
  go (α , P→∃ , ∃→P) = ∣ α , forward , backward ∣₁
    where
    forward : ¬ ⟨ P ⟩ → (n : ℕ) → α n ≡ false
    forward ¬p n with α n =B true
    ... | yes αn=t = ex-falso (¬p (∃→P (n , αn=t)))
    ... | no αn≠t = ¬true→false (α n) αn≠t

    backward : ((n : ℕ) → α n ≡ false) → ¬ ⟨ P ⟩
    backward all-false p with P→∃ p
    ... | (n , αn=t) = false≢true (sym (all-false n) ∙ αn=t)

decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = ∣ (λ _ → true) , (λ _ → 0 , refl) , (λ _ → p) ∣₁
decIsOpen P (no ¬p) = ∣ (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , (λ x → ex-falso (false≢true (snd x))) ∣₁

decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = ∣ (λ _ → false) , (λ _ _ → refl) , (λ _ → p) ∣₁
decIsClosed P (no ¬p) = ∣ (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , (λ f → ex-falso (true≢false (f 0))) ∣₁

⊥-hProp : hProp ℓ-zero
⊥-hProp = ⊥ , isProp⊥

⊥-isOpen : isOpenProp ⊥-hProp
⊥-isOpen = decIsOpen ⊥-hProp (no (λ x → x))

Bool-equality-closed : (a b : Bool) → isClosedProp ((a ≡ b) , isSetBool a b)
Bool-equality-closed a b = decIsClosed ((a ≡ b) , isSetBool a b) (a =B b)

-- tex Definition at line 475: WLPO, Markov, LLPO

MarkovPrinciple : Type₀
MarkovPrinciple = (α : binarySequence) → ¬ ((n : ℕ) → α n ≡ false) → Σ[ n ∈ ℕ ] α n ≡ true

-- tex Theorem NotWLPO, line 475
WLPO : Type₀
WLPO = (α : binarySequence) → Dec ((n : ℕ) → α n ≡ false)

hitsAtMostOnce : binarySequence → Type₀
hitsAtMostOnce α = (m n : ℕ) → α m ≡ true → α n ≡ true → m ≡ n

isPropHitsAtMostOnce : (α : binarySequence) → isProp (hitsAtMostOnce α)
isPropHitsAtMostOnce α = isPropΠ λ m → isPropΠ λ n → isPropΠ λ _ → isPropΠ λ _ → isSetℕ m n

ℕ∞ : Type₀
ℕ∞ = Σ[ α ∈ binarySequence ] hitsAtMostOnce α

-- tex Theorem 541: LLPO
LLPO : Type₀
LLPO = (α : ℕ∞) → ∥ ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false) ∥₁

-- Negation of closed is open (with Markov)

negClosedIsOpen : MarkovPrinciple → (P : hProp ℓ-zero)
  → (α : binarySequence) → ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false)
  → isOpenProp (¬hProp P)
negClosedIsOpen mp P α (P→∀ , ∀→P) = ∣ α , forward , backward ∣₁
  where
  forward : ¬ ⟨ P ⟩ → Σ[ n ∈ ℕ ] α n ≡ true
  forward ¬p = mp α (λ all-false → ¬p (∀→P all-false))

  backward : Σ[ n ∈ ℕ ] α n ≡ true → ¬ ⟨ P ⟩
  backward (n , αn=t) p = true≢false (sym αn=t ∙ P→∀ p n)

closedIsStable : (P : hProp ℓ-zero) → isClosedProp P → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
closedIsStable P Pclosed ¬¬p = PT.rec (snd P) go Pclosed
  where
  go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false) → ⟨ P ⟩
  go (α , P→∀ , ∀→P) = ∀→P all-false
    where
    all-false : (n : ℕ) → α n ≡ false
    all-false n with α n =B true
    ... | yes αn=t = ex-falso (¬¬p (λ p → true≢false (sym αn=t ∙ P→∀ p n)))
    ... | no αn≠t = ¬true→false (α n) αn≠t

openIsStable : MarkovPrinciple → (P : hProp ℓ-zero) → isOpenProp P → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
openIsStable mp P Popen ¬¬p = PT.rec (snd P) go Popen
  where
  go : isOpenWitness P → ⟨ P ⟩
  go (α , P→∃ , ∃→P) = ∃→P (mp α ¬all-false)
    where
    ¬all-false : ¬ ((n : ℕ) → α n ≡ false)
    ¬all-false all-false = ¬¬p (λ p → false≢true (sym (all-false (fst (P→∃ p))) ∙ snd (P→∃ p)))

-- Interleaving of binary sequences (used in many proofs)

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

isEvenB : ℕ → Bool
isEvenB zero = true
isEvenB (suc zero) = false
isEvenB (suc (suc n)) = isEvenB n

2·suc : (k : ℕ) → 2 ·ℕ (suc k) ≡ suc (suc (2 ·ℕ k))
2·suc k = cong suc (+-suc k (k +ℕ zero))

isEvenB-2k : (k : ℕ) → isEvenB (2 ·ℕ k) ≡ true
isEvenB-2k zero = refl
isEvenB-2k (suc k) = subst (λ n → isEvenB n ≡ true) (sym (2·suc k)) (isEvenB-2k k)

isEvenB-2k+1 : (k : ℕ) → isEvenB (suc (2 ·ℕ k)) ≡ false
isEvenB-2k+1 zero = refl
isEvenB-2k+1 (suc k) = subst (λ n → isEvenB (suc n) ≡ false) (sym (2·suc k)) (isEvenB-2k+1 k)

half-2k : (k : ℕ) → half (2 ·ℕ k) ≡ k
half-2k zero = refl
half-2k (suc k) = subst (λ n → half n ≡ suc k) (sym (2·suc k)) (cong suc (half-2k k))

half-2k+1 : (k : ℕ) → half (suc (2 ·ℕ k)) ≡ k
half-2k+1 zero = refl
half-2k+1 (suc k) = subst (λ n → half (suc n) ≡ suc k) (sym (2·suc k)) (cong suc (half-2k+1 k))

2·half-even : (n : ℕ) → isEvenB n ≡ true → 2 ·ℕ (half n) ≡ n
2·half-even zero _ = refl
2·half-even (suc zero) even-f = ex-falso (false≢true even-f)
2·half-even (suc (suc n)) even-ssn =
  2 ·ℕ (suc (half n))      ≡⟨ 2·suc (half n) ⟩
  suc (suc (2 ·ℕ (half n))) ≡⟨ cong (suc ∘ suc) (2·half-even n even-ssn) ⟩
  suc (suc n)              ∎

suc-2·half-odd : (n : ℕ) → isEvenB n ≡ false → suc (2 ·ℕ (half n)) ≡ n
suc-2·half-odd zero odd-f = ex-falso (true≢false odd-f)
suc-2·half-odd (suc zero) _ = refl
suc-2·half-odd (suc (suc n)) odd-ssn =
  suc (2 ·ℕ (suc (half n)))      ≡⟨ cong suc (2·suc (half n)) ⟩
  suc (suc (suc (2 ·ℕ (half n)))) ≡⟨ cong (suc ∘ suc) (suc-2·half-odd n odd-ssn) ⟩
    suc (suc n)                    ∎

interleave : binarySequence → binarySequence → binarySequence
interleave α β n = if isEvenB n then α (half n) else β (half n)

interleave-2k : (α β : binarySequence) (k : ℕ) → interleave α β (2 ·ℕ k) ≡ α k
interleave-2k α β k =
  (if isEvenB (2 ·ℕ k) then α (half (2 ·ℕ k)) else β (half (2 ·ℕ k)))
    ≡⟨ cong (λ x → if x then α (half (2 ·ℕ k)) else β (half (2 ·ℕ k))) (isEvenB-2k k) ⟩
  α (half (2 ·ℕ k))                ≡⟨ cong α (half-2k k) ⟩
  α k                              ∎

interleave-2k+1 : (α β : binarySequence) (k : ℕ) → interleave α β (suc (2 ·ℕ k)) ≡ β k
interleave-2k+1 α β k =
  (if isEvenB (suc (2 ·ℕ k)) then α (half (suc (2 ·ℕ k))) else β (half (suc (2 ·ℕ k))))
    ≡⟨ cong (λ x → if x then α (half (suc (2 ·ℕ k))) else β (half (suc (2 ·ℕ k)))) (isEvenB-2k+1 k) ⟩
  β (half (suc (2 ·ℕ k)))          ≡⟨ cong β (half-2k+1 k) ⟩
  β k                              ∎

interleave-even : (α β : binarySequence) (n : ℕ) → isEvenB n ≡ true
                 → interleave α β n ≡ α (half n)
interleave-even α β n n-even =
  cong (λ x → if x then α (half n) else β (half n)) n-even

interleave-odd : (α β : binarySequence) (n : ℕ) → isEvenB n ≡ false
                → interleave α β n ≡ β (half n)
interleave-odd α β n n-odd =
  cong (λ x → if x then α (half n) else β (half n)) n-odd

-- Cantor pairing

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

cantorPair : ℕ → ℕ → ℕ
cantorPair m n = Iso.fun ℕ×ℕ≅ℕ (m , n)

cantorUnpair : ℕ → ℕ × ℕ
cantorUnpair = Iso.inv ℕ×ℕ≅ℕ

cantorUnpair-pair : (m n : ℕ) → cantorUnpair (cantorPair m n) ≡ (m , n)
cantorUnpair-pair m n = Iso.ret ℕ×ℕ≅ℕ (m , n)

-- firstTrue helper (for LLPO proofs)

firstTrue : binarySequence → binarySequence
firstTrue α zero = α zero
firstTrue α (suc n) with α zero
... | true = false
... | false = firstTrue (α ∘ suc) n

firstTrue-preserves-allFalse : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
                             → (n : ℕ) → firstTrue α n ≡ false
firstTrue-preserves-allFalse α allF zero = allF zero
firstTrue-preserves-allFalse α allF (suc n) with α zero | allF zero
... | true  | α0=f = ex-falso (false≢true (sym α0=f))
... | false | _    = firstTrue-preserves-allFalse (α ∘ suc) (allF ∘ suc) n

firstTrue-hitsAtMostOnce : (α : binarySequence) → hitsAtMostOnce (firstTrue α)
firstTrue-hitsAtMostOnce α m n ftm=t ftn=t = aux α m n ftm=t ftn=t
  where
  aux : (α : binarySequence) → (m n : ℕ) → firstTrue α m ≡ true → firstTrue α n ≡ true → m ≡ n
  aux α zero zero _ _ = refl
  aux α zero (suc n) ft0=t ft-sn=t with α zero
  aux α zero (suc n) ft0=t ft-sn=t | true = ex-falso (false≢true ft-sn=t)
  aux α zero (suc n) ft0=t ft-sn=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) zero ft-sm=t ft0=t with α zero
  aux α (suc m) zero ft-sm=t ft0=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) zero ft-sm=t ft0=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t with α zero
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | false = cong suc (aux (α ∘ suc) m n ft-sm=t ft-sn=t)

firstTrue-true-implies-original-true : (α : binarySequence) (n : ℕ)
                                      → firstTrue α n ≡ true → α n ≡ true
firstTrue-true-implies-original-true α zero ft0=t = ft0=t
firstTrue-true-implies-original-true α (suc n) ft-sn=t with α zero
... | true  = ex-falso (false≢true ft-sn=t)
... | false = firstTrue-true-implies-original-true (α ∘ suc) n ft-sn=t

-- Inspect pattern (needed for with-abstractions)

data Reveal_·_is_ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) (y : B x) : Type₀ where
  [_] : f x ≡ y → Reveal f · x is y

inspect : ∀ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]

firstTrue-false-but-original-true : (α : binarySequence) (n : ℕ)
                                   → firstTrue α n ≡ false → α n ≡ true
                                   → Σ[ m ∈ ℕ ] (suc m ≤ n) × (α m ≡ true)
firstTrue-false-but-original-true α zero ft0=f α0=t = ex-falso (true≢false (sym α0=t ∙ ft0=f))
firstTrue-false-but-original-true α (suc n) ft-sn=f α-sn=t with α zero | inspect α zero
... | true  | [ α0=t ] = zero , suc-≤-suc zero-≤ , α0=t
... | false | _ =
  let (m , m<n , αsm=t) = firstTrue-false-but-original-true (α ∘ suc) n ft-sn=f α-sn=t
  in suc m , suc-≤-suc m<n , αsm=t

-- openEquiv and closedEquiv

openEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
          → isOpenProp P → isOpenProp Q
openEquiv P Q P→Q Q→P Popen =
  PT.map (λ (α , P→∃ , ∃→P) → α , (λ q → P→∃ (Q→P q)) , (λ w → P→Q (∃→P w))) Popen

closedEquiv : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
            → isClosedProp P → isClosedProp Q
closedEquiv P Q P→Q Q→P Pclosed =
  PT.map (λ (α , P→∀ , ∀→P) → α , (λ q → P→∀ (Q→P q)) , (λ w → P→Q (∀→P w))) Pclosed

-- tex Definition (line 884-886): Open/Closed subsets

isOpenSubset : {T : Type₀} → (A : T → hProp ℓ-zero) → Type₀
isOpenSubset {T} A = (t : T) → isOpenProp (A t)

-- tex Remark 889: Continuity
preimageOpenIsOpen : {S T : Type₀} (f : S → T) (A : T → hProp ℓ-zero)
                   → isOpenSubset A → isOpenSubset (λ s → A (f s))
preimageOpenIsOpen f A Aopen s = Aopen (f s)
