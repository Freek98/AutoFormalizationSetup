{-# OPTIONS --cubical --guardedness #-}

module work.Part01 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
import QuotientBool as QB
import Cubical.Data.Sum as ⊎

open import BooleanRing.BooleanRingQuotients.QuotientConclusions using (BoolQuotientEquiv) public

binarySequence : Type₀
binarySequence = ℕ → Bool

CantorSpace : Type₀
CantorSpace = binarySequence

_↔_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

infixr 3 _↔_

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

LLPO : Type₀
LLPO = (α : ℕ∞) → ∥ ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false) ∥₁

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

closedAnd : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
          → isClosedProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
closedAnd P Q Pclosed Qclosed = PT.rec2 squash₁ go Pclosed Qclosed
  where
  go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false)
     → Σ[ β ∈ binarySequence ] ⟨ Q ⟩ ↔ ((n : ℕ) → β n ≡ false)
     → isClosedProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
  go (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) = ∣ γ , forward , backward ∣₁
    where
    γ : binarySequence
    γ = interleave α β

    forward : ⟨ P ⟩ × ⟨ Q ⟩ → (n : ℕ) → γ n ≡ false
    forward (p , q) n with isEvenB n =B true
    ... | yes even = subst (λ x → (if x then α (half n) else β (half n)) ≡ false) (sym even) (P→∀α p (half n))
    ... | no notEven = subst (λ x → (if x then α (half n) else β (half n)) ≡ false) (sym (¬true→false (isEvenB n) notEven)) (Q→∀β q (half n))

    backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ × ⟨ Q ⟩
    backward all-zero = (∀α→P α-zero) , (∀β→Q β-zero)
      where
      α-zero : (k : ℕ) → α k ≡ false
      α-zero k = sym (interleave-2k α β k) ∙ all-zero (2 ·ℕ k)

      β-zero : (k : ℕ) → β k ≡ false
      β-zero k = sym (interleave-2k+1 α β k) ∙ all-zero (suc (2 ·ℕ k))

openOrMP : MarkovPrinciple → (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
openOrMP mp P Q Popen Qopen = PT.rec2 squash₁ go Popen Qopen
  where
  go : isOpenWitness P → isOpenWitness Q → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
  go (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = ∣ γ , forward , backward ∣₁
    where
    γ : binarySequence
    γ = interleave α β

    backward : Σ[ n ∈ ℕ ] γ n ≡ true → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
    backward (n , γn=t) with isEvenB n =B true
    ... | yes even = ∣ inl (∃α→P (half n , claim)) ∣₁
      where
      claim : α (half n) ≡ true
      claim = subst (λ x → (if x then α (half n) else β (half n)) ≡ true) even γn=t
    ... | no notEven = ∣ inr (∃β→Q (half n , claim)) ∣₁
      where
      claim : β (half n) ≡ true
      claim = subst (λ x → (if x then α (half n) else β (half n)) ≡ true) (¬true→false (isEvenB n) notEven) γn=t

    forward : ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ → Σ[ n ∈ ℕ ] γ n ≡ true
    forward truncPQ = mp γ ¬all-false
      where
      ¬all-false : ¬ ((n : ℕ) → γ n ≡ false)
      ¬all-false all-false = PT.rec isProp⊥ helper truncPQ
        where
        helper : ⟨ P ⟩ ⊎ ⟨ Q ⟩ → ⊥
        helper (inl p) =
          let (k , αk=t) = P→∃α p
          in false≢true (sym (sym (interleave-2k α β k) ∙ all-false (2 ·ℕ k)) ∙ αk=t)
        helper (inr q) =
          let (k , βk=t) = Q→∃β q
          in false≢true (sym (sym (interleave-2k+1 α β k) ∙ all-false (suc (2 ·ℕ k))) ∙ βk=t)
