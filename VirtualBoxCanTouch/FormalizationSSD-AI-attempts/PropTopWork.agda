{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module PropTopWork where

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Bool.Properties using (¬true→false ; false≢true ; true≢false ; or-zeroʳ)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎

open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Functions.Logic hiding (⊥)

open import BasicDefinitions
open import BinarySequences

private
  ¬' : Type₀ → Type₀
  ¬' A = A → Cubical.Data.Empty.⊥

open Iso

-- ════════════════════════════════════════════════════════════════
-- Open and closed propositions (definitions from OpenClosedProps)
-- ════════════════════════════════════════════════════════════════

isOpenWitness : hProp ℓ-zero → Type₀
isOpenWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ (Σ[ n ∈ ℕ ] α n ≡ true)

isOpenProp : hProp ℓ-zero → Type₀
isOpenProp P = ∥ isOpenWitness P ∥₁

isClosedWitness : hProp ℓ-zero → Type₀
isClosedWitness P = Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false)

isClosedProp : hProp ℓ-zero → Type₀
isClosedProp P = ∥ isClosedWitness P ∥₁

-- ════════════════════════════════════════════════════════════════
-- Helper: construct isOpenProp from forward/backward with truncation
-- ════════════════════════════════════════════════════════════════

isOpenPropHelperConstructor : (P : hProp ℓ-zero) →
  (α : binarySequence) → (Σℕ α → ⟨ P ⟩) → (⟨ P ⟩ → ∥ Σℕ α ∥₁) → isOpenProp P
isOpenPropHelperConstructor P α Σα→P P→∃α = ∣ α , P→Σα , Σα→P ∣₁ where
  P→Σα : ⟨ P ⟩ → Σℕ α
  P→Σα p = extractFirstHitInBinarySequence.extract α (P→∃α p)

private
  and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
  and-true-left true  _ _ = refl
  and-true-left false _ p = ex-falso (false≢true p)

  and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
  and-true-right true  b p = p
  and-true-right false _ p = ex-falso (false≢true p)

-- ════════════════════════════════════════════════════════════════
-- 1. Conjunction of open propositions is open (Open⊓)
-- ════════════════════════════════════════════════════════════════

Open⊓ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenWitness (P ⊓ Q)
Open⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = γ , P×Q→γ , γ→P×Q where
  γ : binarySequence
  γ n = α (fst (inv ℕ×ℕ≅ℕ n)) and β (snd (inv ℕ×ℕ≅ℕ n))

  γ→P×Q : Σℕ γ → ⟨ P ⊓ Q ⟩
  γ→P×Q (k , r) = α→P (m , αm) , β→Q (n , βn) where
    m = fst (inv ℕ×ℕ≅ℕ k)
    n = snd (inv ℕ×ℕ≅ℕ k)
    αm : α m ≡ true
    αm = and-true-left (α m) (β n) r
    βn : β n ≡ true
    βn = and-true-right (α m) (β n) r

  P×Q→γ : ⟨ P ⊓ Q ⟩ → Σℕ γ
  P×Q→γ (p , q) = fun ℕ×ℕ≅ℕ (m , n) , proof where
    m = fst (P→α p)
    n = fst (Q→β q)
    αm = snd (P→α p)
    βn = snd (Q→β q)
    k = fun ℕ×ℕ≅ℕ (m , n)
    eq : inv ℕ×ℕ≅ℕ k ≡ (m , n)
    eq = ret ℕ×ℕ≅ℕ (m , n)
    proof : γ k ≡ true
    proof =
      α (fst (inv ℕ×ℕ≅ℕ k)) and β (snd (inv ℕ×ℕ≅ℕ k))
        ≡⟨ cong₂ (λ x y → α x and β y) (cong fst eq) (cong snd eq) ⟩
      α m and β n
        ≡⟨ cong (_and β n) αm ⟩
      true and β n
        ≡⟨ βn ⟩
      true ∎
      -- Note from freek: this is a different proof than the one I had in mind. What this does is say γ (n,m) = α n and β m, and if there's some n , m with α n = 1, β m = 1, then γ (n , m) =1 also. 

-- Truncated version
Open⊓-prop : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q → isOpenProp (P ⊓ Q)
Open⊓-prop P Q = PT.rec2 squash₁ λ wP wQ → ∣ Open⊓ P Q wP wQ ∣₁

-- ════════════════════════════════════════════════════════════════
-- 2. Disjunction of open propositions is open (Open⊔)
-- ════════════════════════════════════════════════════════════════

Open⊔ : (P Q : hProp ℓ-zero) → isOpenWitness P → isOpenWitness Q → isOpenProp (P ⊔ Q)
Open⊔ P Q (α , P→α , α→P) (β , Q→β , β→Q) = isOpenPropHelperConstructor
  (P ⊔ Q) γ γ→P∨Q (PT.map P⊎Q→γ) where
  γ : binarySequence
  γ k = α k or β k
  P⊎Q→γ : ⟨ P ⟩ ⊎ ⟨ Q ⟩ → Σℕ γ
  P⊎Q→γ (⊎.inl p) = case P→α p return (λ _ → Σℕ γ) of λ
    (n , αn=1) → n , cong (λ a → a or (β n)) αn=1
  P⊎Q→γ (⊎.inr q) = case Q→β q return (λ _ → Σℕ γ) of λ
    (n , βn=1) → n , cong (λ b → (α n) or b) βn=1 ∙ or-zeroʳ (α n)
  γ→P⊎Q : Σℕ γ → ⟨ P ⟩ ⊎ ⟨ Q ⟩
  γ→P⊎Q (n , γn=1) = case or-true→⊎ (α n) (β n) γn=1 of λ
    { (⊎.inl αn=1) → ⊎.inl (α→P (n , αn=1))
    ; (⊎.inr βn=1) → ⊎.inr (β→Q (n , βn=1)) }
  γ→P∨Q : Σℕ γ → ⟨ P ⊔ Q ⟩
  γ→P∨Q = ∣_∣₁ ∘ γ→P⊎Q

-- ════════════════════════════════════════════════════════════════
-- 3. Negation of open is closed
-- ════════════════════════════════════════════════════════════════

negOpenWitnessIsClosedWitness : (P : hProp ℓ-zero) → isOpenWitness P → isClosedWitness (¬ P)
negOpenWitnessIsClosedWitness P (α , P→Σα , Σα→P) =
  α , ¬P→∀α , ∀α→¬P where
  ¬P→∀α : ⟨ ¬ P ⟩ → (n : ℕ) → α n ≡ false
  ¬P→∀α ¬p n = ¬true→false (α n) λ αn=t →
    ¬p (Σα→P (n , αn=t))
  ∀α→¬P : ((n : ℕ) → α n ≡ false) → ⟨ ¬ P ⟩
  ∀α→¬P ∀n¬αn p = case (P→Σα p) of
    λ ((n , αn=t)) → true≢false $
    true ≡⟨ sym αn=t ⟩ α n ≡⟨ ∀n¬αn n ⟩ false ∎

negOpenIsClosed : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp (¬ P)
negOpenIsClosed P = PT.map (negOpenWitnessIsClosedWitness P)

-- ════════════════════════════════════════════════════════════════
-- 4. Negation of closed is open (needs Markov's principle)
-- ════════════════════════════════════════════════════════════════

-- Markov's principle (weak version suffices)
weakMarkovPrinciple : Type₀
weakMarkovPrinciple = (α : binarySequence) → ¬' (∀ n → α n ≡ false) → ∃[ n ∈ ℕ ] α n ≡ true

negClosedWitnessIsOpenWitness : weakMarkovPrinciple →
  (P : hProp ℓ-zero) → isClosedWitness P → isOpenWitness (¬ P)
negClosedWitnessIsOpenWitness wMP P (α , P→∀α , ∀α→P) =
  α , ¬P→Σα , Σα→¬P where
  Σα→¬P : Σℕ α → ⟨ ¬ P ⟩
  Σα→¬P (n , αn=t) p = true≢false $
    true ≡⟨ sym αn=t ⟩ α n ≡⟨ P→∀α p n ⟩ false ∎
  ¬P→Σα : ⟨ ¬ P ⟩ → Σℕ α
  ¬P→Σα ¬p = extractFirstHitInBinarySequence.extract α
    (wMP α λ all-false → ¬p (∀α→P all-false))

negClosedIsOpen : weakMarkovPrinciple →
  (P : hProp ℓ-zero) → isClosedProp P → isOpenProp (¬ P)
negClosedIsOpen wMP P = PT.rec squash₁ (idfun _) ∘
  PT.map (λ w → ∣ negClosedWitnessIsOpenWitness wMP P w ∣₁)

-- ════════════════════════════════════════════════════════════════
-- 5. ¬¬-stability of open and closed propositions
-- ════════════════════════════════════════════════════════════════

-- Open propositions are ¬¬-stable (needs weak Markov's principle)
open-¬¬-stable : weakMarkovPrinciple → (P : hProp ℓ-zero) → isOpenWitness P → ¬' (¬' ⟨ P ⟩) → ⟨ P ⟩
open-¬¬-stable wMP P (α , P→Σα , Σα→P) ¬¬p = Σα→P (n , αn) where
  ¬all-false : ¬' ((n : ℕ) → α n ≡ false)
  ¬all-false af = ¬¬p (λ p → true≢false (sym (snd (P→Σα p)) ∙ af (fst (P→Σα p))))
  found : Σℕ α
  found = extractFirstHitInBinarySequence.extract α (wMP α ¬all-false)
  n = fst found
  αn = snd found

-- Closed propositions are also ¬¬-stable (via closed = ∀n.α(n)=false,
-- and each α(n)=false is decidable hence ¬¬-stable)
closed-¬¬-stable-witness : (P : hProp ℓ-zero) → isClosedWitness P → ¬' (¬' ⟨ P ⟩) → ⟨ P ⟩
closed-¬¬-stable-witness P (α , P→∀α , ∀α→P) ¬¬p = ∀α→P all-false where
  all-false : (n : ℕ) → α n ≡ false
  all-false n = ¬true→false (α n) λ αn=t →
    ¬¬p λ p → true≢false (sym αn=t ∙ P→∀α p n)

-- ════════════════════════════════════════════════════════════════
-- 6. Decidable propositions are open and closed
-- ════════════════════════════════════════════════════════════════

decIsOpen : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isOpenProp P
decIsOpen P (yes p) = ∣ (λ _ → true) , (λ _ → 0 , refl) , (λ _ → p) ∣₁
decIsOpen P (no ¬p) = ∣ (λ _ → false) , (λ p₁ → ex-falso (¬p p₁)) , (λ x → ex-falso (false≢true (snd x))) ∣₁

decIsClosed : (P : hProp ℓ-zero) → Dec ⟨ P ⟩ → isClosedProp P
decIsClosed P (yes p) = ∣ (λ _ → false) , (λ _ _ → refl) , (λ _ → p) ∣₁
decIsClosed P (no ¬p) = ∣ (λ _ → true) , (λ p₁ → ex-falso (¬p p₁)) , (λ f → ex-falso (true≢false (f 0))) ∣₁

-- ════════════════════════════════════════════════════════════════
-- 7. Conjunction of closed propositions is closed (Closed⊓)
-- ════════════════════════════════════════════════════════════════

Closed⊓ : (P Q : hProp ℓ-zero) → isClosedWitness P → isClosedWitness Q → isClosedWitness (P ⊓ Q)
Closed⊓ P Q (α , P→α , α→P) (β , Q→β , β→Q) = γ , P∧Q→γ , γ→P∧Q where
  γSplit : ℕ ⊎ ℕ → Bool
  γSplit = ⊎.rec α β
  γ : binarySequence
  γ = γSplit ∘ ℕ⊎ℕ≅ℕ .inv
  γ→P∧Q : ((n : ℕ) → γ n ≡ false) → ⟨ P ⊓ Q ⟩
  γ→P∧Q γ=0 = α→P (λ n → help (⊎.inl n)) , β→Q (λ n → help (⊎.inr n)) where
    help : (p : ℕ ⊎ ℕ) → γSplit p ≡ false
    help p =
      γSplit p
        ≡⟨ cong γSplit (sym $ ℕ⊎ℕ≅ℕ .ret p) ⟩
      γ (ℕ⊎ℕ≅ℕ .fun p)
        ≡⟨ γ=0 (ℕ⊎ℕ≅ℕ .fun p) ⟩
      false ∎
  P∧Q→γ : ⟨ P ⊓ Q ⟩ → (n : ℕ) → γ n ≡ false
  P∧Q→γ P∧Q n with (ℕ⊎ℕ≅ℕ .inv n)
  ... | ⊎.inl m = P→α (fst P∧Q) m
  ... | ⊎.inr m = Q→β (snd P∧Q) m

-- ════════════════════════════════════════════════════════════════
-- 8. Countable conjunction of closed propositions is closed
-- ════════════════════════════════════════════════════════════════

-- With explicit witness family (no choice needed)
Closed⊓ω-witness : (P : ℕ → hProp ℓ-zero)
  → (w : (n : ℕ) → isClosedWitness (P n))
  → isClosedWitness ((∀ n → ⟨ P n ⟩) , isPropΠ λ n → snd (P n))
Closed⊓ω-witness P w = β , fwd , bwd where
  α : ℕ → binarySequence
  α n = fst (w n)

  β : binarySequence
  β k = α (fst (inv ℕ×ℕ≅ℕ k)) (snd (inv ℕ×ℕ≅ℕ k))

  fwd : ((n : ℕ) → ⟨ P n ⟩) → (k : ℕ) → β k ≡ false
  fwd allP k = fst (snd (w n)) (allP n) m where
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)

  bwd : ((k : ℕ) → β k ≡ false) → (n : ℕ) → ⟨ P n ⟩
  bwd allβ n = snd (snd (w n)) helper where
    helper : (m : ℕ) → α n m ≡ false
    helper m =
      α n m
        ≡⟨ sym (cong (λ p → α (fst p) (snd p)) (ret ℕ×ℕ≅ℕ (n , m))) ⟩
      β (fun ℕ×ℕ≅ℕ (n , m))
        ≡⟨ allβ (fun ℕ×ℕ≅ℕ (n , m)) ⟩
      false ∎

-- ════════════════════════════════════════════════════════════════
-- 9. Countable disjunction of open propositions is open
-- ════════════════════════════════════════════════════════════════

-- With explicit witness family
Open⊔ω-witness : (P : ℕ → hProp ℓ-zero)
  → (w : (n : ℕ) → isOpenWitness (P n))
  → isOpenProp (∥ Σ ℕ (⟨_⟩ ∘ P) ∥₁ , squash₁)
Open⊔ω-witness P w = isOpenPropHelperConstructor
  (∥ Σ ℕ (⟨_⟩ ∘ P) ∥₁ , squash₁) β Σβ→∃P ∃P→∥Σβ∥ where
  α : ℕ → binarySequence
  α n = fst (w n)

  β : binarySequence
  β k = α (fst (inv ℕ×ℕ≅ℕ k)) (snd (inv ℕ×ℕ≅ℕ k))

  Σβ→∃P : Σℕ β → ∥ Σ ℕ (⟨_⟩ ∘ P) ∥₁
  Σβ→∃P (k , βk=t) = ∣ n , snd (snd (w n)) (m , αnm=t) ∣₁ where
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)
    αnm=t : α n m ≡ true
    αnm=t = βk=t

  ∃P→∥Σβ∥ : ∥ Σ ℕ (⟨_⟩ ∘ P) ∥₁ → ∥ Σℕ β ∥₁
  ∃P→∥Σβ∥ = PT.rec squash₁ λ (n , pn) →
    let (m , αnm=t) = fst (snd (w n)) pn
        k = fun ℕ×ℕ≅ℕ (n , m)
        eq : inv ℕ×ℕ≅ℕ k ≡ (n , m)
        eq = ret ℕ×ℕ≅ℕ (n , m)
        βk=t : β k ≡ true
        βk=t = cong (λ p → α (fst p) (snd p)) eq ∙ αnm=t
    in ∣ k , βk=t ∣₁

-- ════════════════════════════════════════════════════════════════
-- 10. Implication: open → closed is closed
-- ════════════════════════════════════════════════════════════════

-- Key insight: (P → Q) ↔ (¬P ∨ Q) when both sides are ¬¬-stable.
-- ¬P is closed (neg of open), Q is closed, so ¬P ∨ Q is a disjunction of closed.
-- Actually, for the witness-level proof, we go through the binary sequences directly.
-- P open witnessed by α: P ↔ ∃n. α(n)=true
-- Q closed witnessed by β: Q ↔ ∀m. β(m)=false
-- P → Q means: (∃n. α(n)=true) → (∀m. β(m)=false)
-- equivalently: ∀n.∀m. (α(n)=true → β(m)=false)
-- equivalently: ∀n.∀m. ¬(α(n)=true ∧ β(m)=true)
-- equivalently: ∀k. ¬(α(fst(unpair k))=true ∧ β(snd(unpair k))=true)
-- equivalently: ∀k. γ(k)=false where γ(k) = α(fst(unpair k)) and β(snd(unpair k))... wait that's wrong.
-- Actually: ∀n.∀m. α(n)=true → β(m)=false
-- Note α(n) and β(m) are booleans. If α(n)=false, trivially. If α(n)=true, need β(m)=false.
-- So the condition is: ∀(n,m). (α(n) and not(β(m))) = false ... hmm.
-- Actually the simplest approach: use ¬¬-stability.
-- (P → Q) ↔ (¬P ∨ Q) when P → Q is ¬¬-stable.
-- ¬P is closed, Q is closed. We need closed ∨ closed which needs LLPO.
-- But we can do it differently:
-- (P → Q) is the same as (¬P ∨ Q) since both sides are ¬¬-stable (if we assume wMP).
-- ¬P is closed. Q is closed. ¬P ∨ Q... we need LLPO for disjunction of closed.
-- Alternative direct approach: ∀k. γ(k) = false where γ uses the conjunction structure.

-- Direct witness construction:
-- P → Q means: if ∃n. α(n)=true then ∀m. β(m)=false.
-- Consider γ(k) = α(fst(unpair k)) and β(snd(unpair k)).
-- Then ∀k.γ(k)=false means: for all n,m: if α(n)=true then β(m)=false.
-- Forward: if P → Q, then for any pair (n,m), either α(n)=false (so and=false) or
--   α(n)=true, then P holds, so Q holds, so β(m)=false (so and=false).
-- Backward: if ∀k.γ(k)=false and P holds (so ∃n.α(n)=true with witness n₀),
--   then for any m, γ(pair(n₀,m))=false, so α(n₀) and β(m) = false,
--   since α(n₀)=true, we get β(m)=false. So Q holds.

-- But wait, (P → Q) is an implication, not necessarily a prop without knowing both are props.
-- We need P → Q to be a prop. Since Q is a prop (it's an hProp), P → Q is a prop.

impl-open-closed-witness : (P Q : hProp ℓ-zero) →
  isOpenWitness P → isClosedWitness Q →
  isClosedWitness ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
impl-open-closed-witness P Q (α , P→Σα , Σα→P) (β , Q→∀β , ∀β→Q) =
  γ , fwd , bwd where
  γ : binarySequence
  γ k = α (fst (inv ℕ×ℕ≅ℕ k)) and β (snd (inv ℕ×ℕ≅ℕ k))

  fwd : (⟨ P ⟩ → ⟨ Q ⟩) → (k : ℕ) → γ k ≡ false
  fwd f k = go (α n) refl where
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)
    go : (b : Bool) → α n ≡ b → b and β m ≡ false
    go false _ = refl
    go true  αn=t = Q→∀β (f (Σα→P (n , αn=t))) m

  bwd : ((k : ℕ) → γ k ≡ false) → ⟨ P ⟩ → ⟨ Q ⟩
  bwd allγ p = ∀β→Q helper where
    n₀ = fst (P→Σα p)
    αn₀ = snd (P→Σα p)
    helper : (m : ℕ) → β m ≡ false
    helper m = and-false-right where
      k = fun ℕ×ℕ≅ℕ (n₀ , m)
      eq : inv ℕ×ℕ≅ℕ k ≡ (n₀ , m)
      eq = ret ℕ×ℕ≅ℕ (n₀ , m)
      γk=false : γ k ≡ false
      γk=false = allγ k
      step : α n₀ and β m ≡ false
      step = sym (cong (λ p → α (fst p) and β (snd p)) eq) ∙ γk=false
      and-false-right : β m ≡ false
      and-false-right = subst (λ x → x and β m ≡ false) αn₀ step

impl-open-closed : (P Q : hProp ℓ-zero) →
  isOpenProp P → isClosedProp Q →
  isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
impl-open-closed P Q = PT.rec2 squash₁
  λ wP wQ → ∣ impl-open-closed-witness P Q wP wQ ∣₁

-- ════════════════════════════════════════════════════════════════
-- 11. Implication: closed → open is open
-- ════════════════════════════════════════════════════════════════

-- P closed witnessed by α: P ↔ ∀n. α(n)=false
-- Q open witnessed by β: Q ↔ ∃m. β(m)=true
-- P → Q means: (∀n. α(n)=false) → (∃m. β(m)=true)
-- This is: ∃m. β(m)=true ∨ ∃n. α(n)=true
-- i.e., ∃k. γ(k)=true where γ(k) = α(fst(unpair k)) or β(snd(unpair k))
-- Forward: if P → Q, we need ∃k.γ(k)=true.
--   Case: ∃n.α(n)=true → take k=pair(n,0), γ(k)=α(n) or β(0) = true or β(0) = true.
--   Case: ∀n.α(n)=false → then P holds, so Q holds, so ∃m.β(m)=true,
--     take k=pair(0,m), γ(k)=α(0) or β(m) = false or true = true... wait need β(m)=true.
--     Actually γ(k) = α(fst..) or β(snd..), and β(m)=true gives or-zeroʳ.
-- Backward: if ∃k.γ(k)=true, either α(n)=true for some n, or β(m)=true for some m.
--   If β(m)=true then Q holds so P→Q.
--   If α(n)=true then ¬(∀n.α(n)=false), so ¬P, so P→Q vacuously.

-- This needs the ⟨ P ⟩ → ⟨ Q ⟩ to be a proposition (it is, since Q is a prop).
-- The tricky part is the forward direction needs ¬¬-stability or Markov,
-- because from P → Q we get ¬¬(∃n.α(n)=true ∨ ∃m.β(m)=true).

-- Actually, let's think again with witness level.
-- We have (P→Q) = (∀n.α(n)=false → ∃m.β(m)=true).
-- Consider γ(k) = α(fst(unpair k)) or β(snd(unpair k)).
-- Backward: Suppose ∃k.γ(k)=true. Get (n,m) with α(n) or β(m) = true.
--   Either α(n)=true or β(m)=true.
--   If β(m)=true: for any allα, Q holds via β→Q (m, β(m)=true). ✓
--   If α(n)=true: for allα : ∀n.α(n)=false, contradiction: α(n)=true vs α(n)=false. ✓
-- Forward: Suppose P→Q. Need ∃k.γ(k)=true.
--   For each n: α(n)=true? then γ(pair(n,0))=true. ✓
--   If ∀n.α(n)=false, then P holds, so Q holds, get (m,β(m)=true).
--     γ(pair(0,m)) = α(0) or β(m) = false or true = true. ✓
--   But we can't decide "∃n.α(n)=true or ∀n.α(n)=false" without Markov/WLPO.
-- So we need ¬¬-stability of the open conclusion. With wMP:

impl-closed-open-witness : weakMarkovPrinciple → (P Q : hProp ℓ-zero) →
  isClosedWitness P → isOpenWitness Q →
  isOpenWitness ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
impl-closed-open-witness wMP P Q (α , P→∀α , ∀α→P) (β , Q→Σβ , Σβ→Q) =
  γ , fwd , bwd where
  γ : binarySequence
  γ k = α (fst (inv ℕ×ℕ≅ℕ k)) or β (snd (inv ℕ×ℕ≅ℕ k))

  bwd : Σℕ γ → ⟨ P ⟩ → ⟨ Q ⟩
  bwd (k , γk=t) allα-P = case or-true→⊎ (α n) (β m) γk=t of λ
    { (⊎.inl αn=t) → ex-falso (true≢false (sym αn=t ∙ P→∀α allα-P n))
    ; (⊎.inr βm=t) → Σβ→Q (m , βm=t) }
    where
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)

  -- Helper: a or b = false implies a = false and b = false
  or-false→× : (a b : Bool) → a or b ≡ false → (a ≡ false) × (b ≡ false)
  or-false→× false false _ = refl , refl
  or-false→× false true  p = refl , p
  or-false→× true  _     p = ex-falso (true≢false p)

  -- Extract (n,m) from k via the pairing, get α(n) or β(m) = false
  γk-decompose : (n m : ℕ) → γ (fun ℕ×ℕ≅ℕ (n , m)) ≡ false →
    (α n ≡ false) × (β m ≡ false)
  γk-decompose n m p = or-false→×  (α n) (β m)
    (sym (cong (λ q → α (fst q) or β (snd q)) (ret ℕ×ℕ≅ℕ (n , m))) ∙ p)

  fwd : (⟨ P ⟩ → ⟨ Q ⟩) → Σℕ γ
  fwd f = extractFirstHitInBinarySequence.extract γ (wMP γ ¬all-false) where
    ¬all-false : ¬' ((k : ℕ) → γ k ≡ false)
    ¬all-false allγ=0 = true≢false (sym βm₀=t ∙ snd (γk-decompose 0 m₀ (allγ=0 (fun ℕ×ℕ≅ℕ (0 , m₀))))) where
      all-α-false : (n : ℕ) → α n ≡ false
      all-α-false n = fst (γk-decompose n 0 (allγ=0 (fun ℕ×ℕ≅ℕ (n , 0))))
      q : ⟨ Q ⟩
      q = f (∀α→P all-α-false)
      m₀ = fst (Q→Σβ q)
      βm₀=t = snd (Q→Σβ q)

impl-closed-open : weakMarkovPrinciple → (P Q : hProp ℓ-zero) →
  isClosedProp P → isOpenProp Q →
  isOpenProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
impl-closed-open wMP P Q = PT.rec2 squash₁
  λ wP wQ → ∣ impl-closed-open-witness wMP P Q wP wQ ∣₁

-- ════════════════════════════════════════════════════════════════
-- 12. Closed Markov: ¬∀n.Pn ↔ ∃n.¬Pn for closed families
-- ════════════════════════════════════════════════════════════════

-- Both sides are open (assuming wMP), hence ¬¬-stable.
-- The forward direction ∃n.¬Pn → ¬∀n.Pn is trivial.
-- The backward: ¬∀n.Pn → ¬¬∃n.¬Pn (trivially), then by ¬¬-stability of open, ∃n.¬Pn.
-- But we need to show ∃n.¬Pn is open first.

-- ¬Pn is open when Pn is closed. And countable disjunction of open is open.
-- So ∃n.¬Pn = ∥ Σn. ¬Pn ∥₁ is open.

ClosedMarkov-witness : weakMarkovPrinciple → (P : ℕ → hProp ℓ-zero)
  → (w : (n : ℕ) → isClosedWitness (P n))
  → ¬' ((n : ℕ) → ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] (¬' ⟨ P n ⟩) ∥₁
ClosedMarkov-witness wMP P w ¬∀P = goal where
  -- Each ¬Pn is open
  ¬Pn-open : (n : ℕ) → isOpenWitness (¬ (P n))
  ¬Pn-open n = negClosedWitnessIsOpenWitness wMP (P n) (w n)

  -- The countable disjunction ∃n.¬Pn is open
  α : ℕ → binarySequence
  α n = fst (¬Pn-open n)

  β : binarySequence
  β k = α (fst (inv ℕ×ℕ≅ℕ k)) (snd (inv ℕ×ℕ≅ℕ k))

  -- ¬¬(∃n.¬Pn)
  ¬¬∃¬P : ¬' (¬' (Σ[ n ∈ ℕ ] (¬' ⟨ P n ⟩)))
  ¬¬∃¬P no∃ = ¬∀P (λ n → closed-¬¬-stable-witness (P n) (w n) λ ¬Pn → no∃ (n , ¬Pn))

  -- ¬(∀k.β(k)=false) because that would mean ¬(∃n.¬Pn) which contradicts ¬¬(∃n.¬Pn)
  ¬all-β-false : ¬' ((k : ℕ) → β k ≡ false)
  ¬all-β-false allβ = ¬¬∃¬P no∃ where
    no∃ : ¬' (Σ[ n ∈ ℕ ] (¬' ⟨ P n ⟩))
    no∃ (n , ¬Pn) = true≢false (sym αn-hit ∙ help m) where
      witness = fst (snd (¬Pn-open n)) ¬Pn
      m₀ = fst witness
      αn-hit = snd witness
      m = m₀
      help : (m : ℕ) → α n m ≡ false
      help m = sym eq' ∙ allβ k where
        k = fun ℕ×ℕ≅ℕ (n , m)
        eq' : β k ≡ α n m
        eq' = cong (λ p → α (fst p) (snd p)) (ret ℕ×ℕ≅ℕ (n , m))

  -- By Markov on β, get a witness
  ∃β : Σℕ β
  ∃β = extractFirstHitInBinarySequence.extract β (wMP β ¬all-β-false)

  -- Extract the n and show ¬Pn
  goal : ∥ Σ[ n ∈ ℕ ] (¬' ⟨ P n ⟩) ∥₁
  goal = ∣ n , snd (snd (¬Pn-open n)) (m , αnm=t) ∣₁ where
    k = fst ∃β
    βk=t = snd ∃β
    n = fst (inv ℕ×ℕ≅ℕ k)
    m = snd (inv ℕ×ℕ≅ℕ k)
    αnm=t : α n m ≡ true
    αnm=t = βk=t
