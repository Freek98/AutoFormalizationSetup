{-# OPTIONS --cubical --guardedness #-}
-- Note from Freek, this file contains some useless imports, so it didn't clean those out properly. It did clean out most comments, and some results about decidable props being closed under negation and disjunction (I think this fell within the mandate)
module work.Part01 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; rCancel; lCancel) renaming (assoc to ∙assoc)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Transport using (transport⁻; transportTransport⁻)

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Fin using (Fin)
import Cubical.Induction.WellFounded as WF
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (isEmbedding-inl; isEmbedding-inr)

open import Cubical.Functions.Embedding using (isEmbedding→Inj)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.DirectProd
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→; BoolBR→IsUnique)

open import Axioms.StoneDuality using (StoneDualityAxiom; Sp; Booleω; SpEmbedding)

import OmnisciencePrinciples.Markov as MarkovLib

open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; _is-presented-by_/_; BooleanRingEquiv; invBooleanRingEquiv; idBoolEquiv; has-Countability-structure)
open import CountablyPresentedBooleanRings.Examples.Bool using (is-cp-2)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
import QuotientBool as QB
open import BooleanRing.BoolRingUnivalence using (uaBoolRing; BoolRingPath)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
import Cubical.Data.Sum as ⊎

open import Cubical.Homotopy.EilenbergMacLane.Base as EM using (EM; EM∙; 0ₖ; hLevelEM; EM-raw→EM)
open import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp using (EM≃ΩEM+1; EM→ΩEM+1; ΩEM+1→EM; ΩEM+1→EM-refl)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure as EMGS using (_+ₖ_; -ₖ_; rCancelₖ)
open import Cubical.Homotopy.Connected using (isConnected; isConnectedFun)
open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; _+ₕ_; -ₕ_; 0ₕ)
open import Cubical.ZCohomology.Groups.Unit using (isContrHⁿ-Unit; Hⁿ-contrType≅0)
open import Cubical.ZCohomology.Groups.Sn using (H¹-S¹≅ℤ; Hⁿ-Sⁿ≅ℤ)
open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr; IsAbGroup; AbGroup→Group; makeIsAbGroup)
open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Homotopy.Loopspace using (Ω; Ω→)
open import Cubical.Foundations.Pointed using (Pointed; Pointed₀; _→∙_; pt)
open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
open import Cubical.HITs.EilenbergMacLane1 as EM₁ using (EM₁; emloop; embase)

postulate
  BoolQuotientEquiv : (A : BooleanRing ℓ-zero) (f g : ℕ → ⟨ A ⟩) →
    BooleanRing→CommRing (A QB./Im (⊎.rec f g)) ≡
    BooleanRing→CommRing ((A QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))

binarySequence : Type₀
binarySequence = ℕ → Bool

CantorSpace : Type₀
CantorSpace = binarySequence

_↔_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ-max ℓ ℓ')
A ↔ B = (A → B) × (B → A)

infixr 3 _↔_

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = Σ[ α ∈ binarySequence ] (⟨ P ⟩ → Σ[ n ∈ ℕ ] α n ≡ true) × (Σ[ n ∈ ℕ ] α n ≡ true → ⟨ P ⟩)

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = Σ[ α ∈ binarySequence ] (⟨ P ⟩ → ((n : ℕ) → α n ≡ false)) × (((n : ℕ) → α n ≡ false) → ⟨ P ⟩)

Open : Type₁
Open = Σ[ P ∈ hProp ℓ-zero ] isOpenProp P

Closed : Type₁
Closed = Σ[ P ∈ hProp ℓ-zero ] isClosedProp P

isSetBinarySequence : isSet binarySequence
isSetBinarySequence = isSetΠ (λ _ → isSetBool)

isSetIsOpenProp : (P : hProp ℓ-zero) → isSet (isOpenProp P)
isSetIsOpenProp P = isSetΣ isSetBinarySequence
  (λ α → isSet× (isSetΠ (λ _ → isSetΣ isSetℕ (λ n → isProp→isSet (isSetBool _ _))))
                 (isSetΠ (λ _ → isProp→isSet (snd P))))

isSetIsClosedProp : (P : hProp ℓ-zero) → isSet (isClosedProp P)
isSetIsClosedProp P = isSetΣ isSetBinarySequence
  (λ α → isSet× (isProp→isSet (isPropΠ (λ _ → isPropΠ (λ _ → isSetBool _ _))))
                 (isProp→isSet (isPropΠ (λ _ → snd P))))

isOpen : hProp ℓ-zero → hProp ℓ-zero
isOpen P = ∥ isOpenProp P ∥₁ , squash₁

isClosed : hProp ℓ-zero → hProp ℓ-zero
isClosed P = ∥ isClosedProp P ∥₁ , squash₁

openProp : Open → hProp ℓ-zero
openProp = fst

closedProp : Closed → hProp ℓ-zero
closedProp = fst

openType : Open → Type₀
openType O = ⟨ fst O ⟩

closedType : Closed → Type₀
closedType C = ⟨ fst C ⟩

open→hProp : Open → hProp ℓ-zero
open→hProp = fst

closed→hProp : Closed → hProp ℓ-zero
closed→hProp = fst

¬hProp : hProp ℓ-zero → hProp ℓ-zero
¬hProp P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬hProp P)
negOpenIsClosed P (α , P→∃ , ∃→P) = α , forward , backward
  where
  forward : ¬ ⟨ P ⟩ → (n : ℕ) → α n ≡ false
  forward ¬p n with α n =B true
  ... | yes αn=t = ex-falso (¬p (∃→P (n , αn=t)))
  ... | no αn≠t = ¬true→false (α n) αn≠t

  backward : ((n : ℕ) → α n ≡ false) → ¬ ⟨ P ⟩
  backward all-false p with P→∃ p
  ... | (n , αn=t) = false≢true (sym (all-false n) ∙ αn=t)

decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = (λ _ → true) , (λ _ → 0 , refl) , (λ _ → p)
decIsOpen P (no ¬p) = (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , (λ x → ex-falso (false≢true (snd x)))

decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = (λ _ → false) , (λ _ _ → refl) , (λ _ → p)
decIsClosed P (no ¬p) = (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , (λ f → ex-falso (true≢false (f 0)))

⊥-hProp : hProp ℓ-zero
⊥-hProp = ⊥ , isProp⊥

⊥-isOpen : isOpenProp ⊥-hProp
⊥-isOpen = decIsOpen ⊥-hProp (no (λ x → x))

⊥-isClosed : isClosedProp ⊥-hProp
⊥-isClosed = decIsClosed ⊥-hProp (no (λ x → x))

⊤-hProp : hProp ℓ-zero
⊤-hProp = Unit , (λ _ _ → refl)

⊤-isOpen : isOpenProp ⊤-hProp
⊤-isOpen = decIsOpen ⊤-hProp (yes tt)

⊤-isClosed : isClosedProp ⊤-hProp
⊤-isClosed = decIsClosed ⊤-hProp (yes tt)

⊥-Open : Open
⊥-Open = ⊥-hProp , ⊥-isOpen

⊥-Closed : Closed
⊥-Closed = ⊥-hProp , ⊥-isClosed

⊤-Open : Open
⊤-Open = ⊤-hProp , ⊤-isOpen

⊤-Closed : Closed
⊤-Closed = ⊤-hProp , ⊤-isClosed

allFalseIsClosed : (α : binarySequence) → isClosedProp (((n : ℕ) → α n ≡ false) , isPropΠ (λ n → isSetBool (α n) false))
allFalseIsClosed α = α , (λ p → p) , (λ p → p)

Bool-equality-decidable : (a b : Bool) → Dec (a ≡ b)
Bool-equality-decidable = _=B_

Bool-equality-open : (a b : Bool) → isOpenProp ((a ≡ b) , isSetBool a b)
Bool-equality-open a b = decIsOpen ((a ≡ b) , isSetBool a b) (Bool-equality-decidable a b)

Bool-equality-closed : (a b : Bool) → isClosedProp ((a ≡ b) , isSetBool a b)
Bool-equality-closed a b = decIsClosed ((a ≡ b) , isSetBool a b) (Bool-equality-decidable a b)

ℕ-equality-decidable : (m n : ℕ) → Dec (m ≡ n)
ℕ-equality-decidable = discreteℕ

ℕ-equality-open : (m n : ℕ) → isOpenProp ((m ≡ n) , isSetℕ m n)
ℕ-equality-open m n = decIsOpen ((m ≡ n) , isSetℕ m n) (ℕ-equality-decidable m n)

ℕ-equality-closed : (m n : ℕ) → isClosedProp ((m ≡ n) , isSetℕ m n)
ℕ-equality-closed m n = decIsClosed ((m ≡ n) , isSetℕ m n) (ℕ-equality-decidable m n)

CantorSpace-equality-closed : (α β : CantorSpace)
                             → isClosedProp ((α ≡ β) , isSetBinarySequence α β)
CantorSpace-equality-closed α β = γ , forward , backward
  where
  γ : binarySequence
  γ n with α n =B β n
  ... | yes _ = false
  ... | no _ = true

  forward : α ≡ β → (n : ℕ) → γ n ≡ false
  forward α=β n with α n =B β n
  ... | yes _ = refl
  ... | no αn≠βn = ex-falso (αn≠βn (cong (λ f → f n) α=β))

  backward : ((n : ℕ) → γ n ≡ false) → α ≡ β
  backward all-false = funExt pointwise
    where
    pointwise : (n : ℕ) → α n ≡ β n
    pointwise n with α n =B β n | all-false n
    ... | yes αn=βn | _ = αn=βn
    ... | no _ | γn=f = ex-falso (true≢false γn=f)

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
LLPO = (α : ℕ∞) → ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false)

negClosedIsOpen : MarkovPrinciple → (P : hProp ℓ-zero) → isClosedProp P → isOpenProp (¬hProp P)
negClosedIsOpen mp P (α , P→∀ , ∀→P) = α , forward , backward
  where
  forward : ¬ ⟨ P ⟩ → Σ[ n ∈ ℕ ] α n ≡ true
  forward ¬p = mp α (λ all-false → ¬p (∀→P all-false))

  backward : Σ[ n ∈ ℕ ] α n ≡ true → ¬ ⟨ P ⟩
  backward (n , αn=t) p = true≢false (sym αn=t ∙ P→∀ p n)

¬-Open : Open → Closed
¬-Open O = ¬hProp (fst O) , negOpenIsClosed (fst O) (snd O)

closedIsStable : (P : hProp ℓ-zero) → isClosedProp P → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
closedIsStable P (α , P→∀ , ∀→P) ¬¬p = ∀→P all-false
  where
  all-false : (n : ℕ) → α n ≡ false
  all-false n with α n =B true
  ... | yes αn=t = ex-falso (¬¬p (λ p → true≢false (sym αn=t ∙ P→∀ p n)))
  ... | no αn≠t = ¬true→false (α n) αn≠t

openIsStable : MarkovPrinciple → (P : hProp ℓ-zero) → isOpenProp P → ¬ ¬ ⟨ P ⟩ → ⟨ P ⟩
openIsStable mp P (α , P→∃ , ∃→P) ¬¬p = ∃→P (mp α ¬all-false)
  where
  ¬all-false : ¬ ((n : ℕ) → α n ≡ false)
  ¬all-false all-false = ¬¬p (λ p → false≢true (sym (all-false (fst (P→∃ p))) ∙ snd (P→∃ p)))

¬¬hProp : hProp ℓ-zero → hProp ℓ-zero
¬¬hProp P = (¬ ¬ ⟨ P ⟩) , isProp¬ (¬ ⟨ P ⟩)

doubleNegOpenIsOpen : MarkovPrinciple → (P : hProp ℓ-zero) → isOpenProp P → isOpenProp (¬¬hProp P)
doubleNegOpenIsOpen mp P Popen = negClosedIsOpen mp (¬hProp P) (negOpenIsClosed P Popen)

doubleNegClosedIsClosed : MarkovPrinciple → (P : hProp ℓ-zero) → isClosedProp P → isClosedProp (¬¬hProp P)
doubleNegClosedIsClosed mp P Pclosed = negOpenIsClosed (¬hProp P) (negClosedIsOpen mp P Pclosed)

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
  interleave α β (2 ·ℕ k)          ≡⟨ refl ⟩
  (if isEvenB (2 ·ℕ k) then α (half (2 ·ℕ k)) else β (half (2 ·ℕ k)))
    ≡⟨ cong (λ x → if x then α (half (2 ·ℕ k)) else β (half (2 ·ℕ k))) (isEvenB-2k k) ⟩
  α (half (2 ·ℕ k))                ≡⟨ cong α (half-2k k) ⟩
  α k                              ∎

interleave-2k+1 : (α β : binarySequence) (k : ℕ) → interleave α β (suc (2 ·ℕ k)) ≡ β k
interleave-2k+1 α β k =
  interleave α β (suc (2 ·ℕ k))    ≡⟨ refl ⟩
  (if isEvenB (suc (2 ·ℕ k)) then α (half (suc (2 ·ℕ k))) else β (half (suc (2 ·ℕ k))))
    ≡⟨ cong (λ x → if x then α (half (suc (2 ·ℕ k))) else β (half (suc (2 ·ℕ k)))) (isEvenB-2k+1 k) ⟩
  β (half (suc (2 ·ℕ k)))          ≡⟨ cong β (half-2k+1 k) ⟩
  β k                              ∎

interleave-even : (α β : binarySequence) (n : ℕ) → isEvenB n ≡ true
                 → interleave α β n ≡ α (half n)
interleave-even α β n n-even =
  interleave α β n
    ≡⟨ refl ⟩
  (if isEvenB n then α (half n) else β (half n))
    ≡⟨ cong (λ x → if x then α (half n) else β (half n)) n-even ⟩
  α (half n) ∎

interleave-odd : (α β : binarySequence) (n : ℕ) → isEvenB n ≡ false
                → interleave α β n ≡ β (half n)
interleave-odd α β n n-odd =
  interleave α β n
    ≡⟨ refl ⟩
  (if isEvenB n then α (half n) else β (half n))
    ≡⟨ cong (λ x → if x then α (half n) else β (half n)) n-odd ⟩
  β (half n) ∎

closedAnd : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
          → isClosedProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
closedAnd P Q (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) = γ , forward , backward
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
openOrMP mp P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = γ , forward , backward
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

openOrNonTrunc : (P Q : hProp ℓ-zero) (αP : isOpenProp P) (αQ : isOpenProp Q)
               → ⟨ P ⟩ ⊎ ⟨ Q ⟩ → Σ[ n ∈ ℕ ] interleave (fst αP) (fst αQ) n ≡ true
openOrNonTrunc P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) (inl p) =
  let (k , αk=t) = P→∃α p
  in (2 ·ℕ k) , (interleave-2k α β k ∙ αk=t)
openOrNonTrunc P Q (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) (inr q) =
  let (k , βk=t) = Q→∃β q
  in suc (2 ·ℕ k) , (interleave-2k+1 α β k ∙ βk=t)
