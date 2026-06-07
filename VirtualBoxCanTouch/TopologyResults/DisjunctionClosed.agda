module DisjunctionClosed where

open import BasicDefinitions
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (hProp)
open import Cubical.Data.Nat using (ℕ)
import Cubical.HITs.PropositionalTruncation as PT
open import BinarySequences
open import PropositionalTopology.Definitions
open import PropositionalTopology.Properties
open import OmnisciencePrinciples.LLPO

-- extra imports used by closedWitness→negOpen
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Functions.Logic using (¬_ ; _⊔_ ; _⊓_ ; ⊥)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁)

-- imports for the at-most-once witness + the LLPO de Morgan proof
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool using (Bool ; true ; false ; not ; _and_ ; true≢false ; false≢true)
import Cubical.Data.Empty as Empty
open import LLMGeneratedFixes.Parity using (double ; even-or-odd)
open import StoneSpaces.Examples.Ninfty using (ℕ∞ ; hits1AtMostOnce)
-- In this file, we show the equivalence of LLPO with the statement that for P,Q open, we have (¬ P) ∨ (¬ Q) ↔ ¬ (P ∧ Q)



-- A closed proposition is logically the negation of an open proposition:
-- with the *same* witness sequence α, P ↔ ¬ ∥ Σℕ α ∥₁, the latter being open.
-- Reuses negOpenWitnessIsClosedWitness, so no boolean reasoning is repeated.
closedWitness→negOpen : (P : hProp ℓ-zero) → isClosedWitness P
  → Σ[ Q ∈ hProp ℓ-zero ] isOpenWitness Q × (⟨ P ⟩ ↔ ⟨ ¬ Q ⟩)
closedWitness→negOpen P (α , P→∀false , ∀false→P) =
  Q , openQ , (P→¬Q , ¬Q→P)
  where
    Q : hProp ℓ-zero
    Q = ∥ Σℕ α ∥₁ , squash₁

    openQ : isOpenWitness Q
    openQ = α , (extract , ∣_∣₁)
      where open extractFirstHitInBinarySequence α

    -- ¬ Q is closed with the same witness α; grab that closed witness's ↔.
    ¬Qclosed : isClosedWitness (¬ Q)
    ¬Qclosed = negOpenWitnessIsClosedWitness Q openQ

    P→¬Q : ⟨ P ⟩ → ⟨ ¬ Q ⟩
    P→¬Q p = ¬Qclosed .snd .snd (P→∀false p)

    ¬Q→P : ⟨ ¬ Q ⟩ → ⟨ P ⟩
    ¬Q→P nq = ∀false→P (¬Qclosed .snd .fst nq)

deMorgan-easy : (P Q : hProp ℓ-zero) → ⟨ ¬ P ⊔ ¬ Q ⟩ → ⟨ ¬ (P ⊓ Q) ⟩
deMorgan-easy P Q disj (p , q) =
  PT.rec (snd ⊥) (⊎.rec (λ ¬p → ¬p p) (λ ¬q → ¬q q)) disj

-- An open proposition can equivalently be witnessed by an *increasing* sequence:
-- "P is open" iff "P ↔ there is a 1 in some increasing sequence".
open MakeIncreasing

isIncreasingOpenWitness : hProp ℓ-zero → Type
isIncreasingOpenWitness P =
  Σ[ α ∈ binarySequence ] isIncreasingSeq α × (⟨ P ⟩ ↔ Σℕ α)

isIncreasingOpenProp : hProp ℓ-zero → Type
isIncreasingOpenProp P = ∥ isIncreasingOpenWitness P ∥₁

-- an increasing open witness is in particular an open witness
incOpenWitness→openWitness : (P : hProp ℓ-zero) → isIncreasingOpenWitness P → isOpenWitness P
incOpenWitness→openWitness P (α , _ , iso) = α , iso

-- prefix-OR (makeIncreasing) turns any open witness into an increasing one,
-- preserving the ∃-hit (hit→makeIncreasingHit / extractFromMakeIncreasing).
openWitness→incOpenWitness : (P : hProp ℓ-zero) → isOpenWitness P → isIncreasingOpenWitness P
openWitness→incOpenWitness P (α , P→Σα , Σα→P) =
  makeIncreasing α , makeIncreasingIsIncreasing α ,
  ( (λ p → fwd (P→Σα p)) , (λ q → Σα→P (bwd q)) )
  where
    fwd : Σℕ α → Σℕ (makeIncreasing α)
    fwd (n , αn=1) = n , hit→makeIncreasingHit α n αn=1
    bwd : Σℕ (makeIncreasing α) → Σℕ α
    bwd (n , mαn=1) = extractFromMakeIncreasing α n mαn=1

-- a proposition is open iff it is "there is a 1 in some increasing sequence"
isOpen↔isIncreasingOpen : (P : hProp ℓ-zero) → isOpenProp P ↔ isIncreasingOpenProp P
isOpen↔isIncreasingOpen P =
  PT.map (openWitness→incOpenWitness P) , PT.map (incOpenWitness→openWitness P)

--------------------------------------------------------------------------------
-- At-most-once open witnesses: the witnessing sequence hits 1 at most once, so
-- it is a point of ℕ∞.  These are what LLPO consumes.
--------------------------------------------------------------------------------

isAtMostOnceOpenWitness : hProp ℓ-zero → Type
isAtMostOnceOpenWitness P =
  Σ[ α ∈ binarySequence ] hits1AtMostOnce α × (⟨ P ⟩ ↔ Σℕ α)

isAtMostOnceOpenProp : hProp ℓ-zero → Type
isAtMostOnceOpenProp P = ∥ isAtMostOnceOpenWitness P ∥₁

-- Make a sequence at-most-once: keep only its first hit.
-- noHitBefore α n  ≡ true  iff  α is 0 on every k < n.
noHitBefore : binarySequence → ℕ → Bool
noHitBefore α zero    = true
noHitBefore α (suc n) = noHitBefore α n and not (α n)

firstHitOnly : binarySequence → binarySequence
firstHitOnly α n = α n and noHitBefore α n

not≡true→≡false : (b : Bool) → not b ≡ true → b ≡ false
not≡true→≡false false _ = refl
not≡true→≡false true  p = Empty.rec (false≢true p)

noHitBefore-spec : (α : binarySequence) (n : ℕ)
  → noHitBefore α n ≡ true → (k : ℕ) → k < n → α k ≡ false
noHitBefore-spec α zero    p k k<0  = Empty.rec (¬-<-zero k<0)
noHitBefore-spec α (suc n) p k k<sn with and-true→× (noHitBefore α n) (not (α n)) p | <-split k<sn
... | (nhb , _)   | ⊎.inl k<n = noHitBefore-spec α n nhb k k<n
... | (_ , notαn) | ⊎.inr k≡n = subst (λ j → α j ≡ false) (sym k≡n) (not≡true→≡false (α n) notαn)

allFalseBefore→noHitBefore : (α : binarySequence) (n : ℕ)
  → ((k : ℕ) → k < n → α k ≡ false) → noHitBefore α n ≡ true
allFalseBefore→noHitBefore α zero    _        = refl
allFalseBefore→noHitBefore α (suc n) allFalse =
  cong₂ _and_
    (allFalseBefore→noHitBefore α n (λ k k<n → allFalse k (≤-suc k<n)))
    (cong not (allFalse n ≤-refl))

firstHitOnly→hit : (α : binarySequence) (n : ℕ) → firstHitOnly α n ≡ true → α n ≡ true
firstHitOnly→hit α n p = fst (and-true→× (α n) (noHitBefore α n) p)

-- uniqueness of the first hit (firstProp) gives at-most-once for free
firstHitOnlyAtMostOnce : (α : binarySequence) → hits1AtMostOnce (firstHitOnly α)
firstHitOnlyAtMostOnce α n m fn fm =
  cong fst (firstProp (n , toFirst n fn) (m , toFirst m fm))
  where
    open extractFirstHitInBinarySequence α
    toFirst : (k : ℕ) → firstHitOnly α k ≡ true → is-first-hit k
    toFirst k fk = firstHitOnly→hit α k fk
                 , noHitBefore-spec α k (snd (and-true→× (α k) (noHitBefore α k) fk))

-- same ∃-hit as α (forward uses extractFirst to land on the first hit)
Σα↔ΣfirstHitOnly : (α : binarySequence) → Σℕ α ↔ Σℕ (firstHitOnly α)
Σα↔ΣfirstHitOnly α = fwd , bwd
  where
    open extractFirstHitInBinarySequence α
    fwd : Σℕ α → Σℕ (firstHitOnly α)
    fwd (n , αn) =
      fst fh , cong₂ _and_ (fst (snd fh))
                           (allFalseBefore→noHitBefore α (fst fh) (snd (snd fh)))
      where fh = extractFirst ∣ (n , αn) ∣₁
    bwd : Σℕ (firstHitOnly α) → Σℕ α
    bwd (n , p) = n , firstHitOnly→hit α n p

openWitness→atMostOnceWitness : (P : hProp ℓ-zero) → isOpenWitness P → isAtMostOnceOpenWitness P
openWitness→atMostOnceWitness P (α , P→Σα , Σα→P) =
  firstHitOnly α , firstHitOnlyAtMostOnce α ,
  ( (λ p → fst (Σα↔ΣfirstHitOnly α) (P→Σα p))
  , (λ s → Σα→P (snd (Σα↔ΣfirstHitOnly α) s)) )

atMostOnceWitness→openWitness : (P : hProp ℓ-zero) → isAtMostOnceOpenWitness P → isOpenWitness P
atMostOnceWitness→openWitness P (α , _ , iso) = α , iso

openProp→atMostOnceProp : (P : hProp ℓ-zero) → isOpenProp P → isAtMostOnceOpenProp P
openProp→atMostOnceProp P = PT.map (openWitness→atMostOnceWitness P)

isOpen↔isAtMostOnceOpen : (P : hProp ℓ-zero) → isOpenProp P ↔ isAtMostOnceOpenProp P
isOpen↔isAtMostOnceOpen P =
  PT.map (openWitness→atMostOnceWitness P) , PT.map (atMostOnceWitness→openWitness P)

-- interleave two sequences: α on even positions, β on odd positions
interleave : binarySequence → binarySequence → binarySequence
interleave α β zero          = α zero
interleave α β (suc zero)    = β zero
interleave α β (suc (suc n)) = interleave (λ k → α (suc k)) (λ k → β (suc k)) n

interleave-even : (α β : binarySequence) (k : ℕ) → interleave α β (double k) ≡ α k
interleave-even α β zero    = refl
interleave-even α β (suc k) = interleave-even (λ j → α (suc j)) (λ j → β (suc j)) k

interleave-odd : (α β : binarySequence) (k : ℕ) → interleave α β (suc (double k)) ≡ β k
interleave-odd α β zero    = refl
interleave-odd α β (suc k) = interleave-odd (λ j → α (suc j)) (λ j → β (suc j)) k

module assumingLLPO (llpo : LLPO) where
  module ExplicitDisjunction (α β : binarySequence) where
  -- The "hard" half of de Morgan, using LLPO: for P, Q open, ¬(P ⊓ Q) → ¬P ⊔ ¬Q.
  -- Take at-most-once witnesses α (for P) and β (for Q) and interleave them into
  -- γ (α on evens, β on odds).  γ hits at most once: two even hits collide via
  -- α's at-most-once-ness, two odd hits via β's, and an even+odd hit would give
  -- ⟨P⟩ ∧ ⟨Q⟩, contradicting ¬(P ⊓ Q).  So γ ∈ ℕ∞, and LLPO says "evens all 0"
  -- (⟹ ¬P, as γ(2n) = α n) or "odds all 0" (⟹ ¬Q).
  deMorgan-hard : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
                → ⟨ ¬ (P ⊓ Q) ⟩ → ⟨ ¬ P ⊔ ¬ Q ⟩
  deMorgan-hard P Q openP openQ ¬pq =
    PT.rec2 (snd (¬ P ⊔ ¬ Q)) deMorgan-hard-witnessed
      (openProp→atMostOnceProp P openP)
      (openProp→atMostOnceProp Q openQ)
    where
      deMorgan-hard-witnessed : isAtMostOnceOpenWitness P → isAtMostOnceOpenWitness Q → ⟨ ¬ P ⊔ ¬ Q ⟩
      deMorgan-hard-witnessed (α , αOnce , P↔Σα) (β , βOnce , Q↔Σβ) =
        PT.map concl (llpo (γ , γAtMostOnce))
        where
          γ : binarySequence
          γ = interleave α β

          evenHit : (n a : ℕ) → n ≡ double a → γ n ≡ true → α a ≡ true
          evenHit n a n≡2a γn = sym (interleave-even α β a) ∙ cong γ (sym n≡2a) ∙ γn

          oddHit : (n a : ℕ) → n ≡ suc (double a) → γ n ≡ true → β a ≡ true
          oddHit n a n≡2a+1 γn = sym (interleave-odd α β a) ∙ cong γ (sym n≡2a+1) ∙ γn

          γAtMostOnce : hits1AtMostOnce γ
          γAtMostOnce n m γn γm with even-or-odd n | even-or-odd m
          ... | ⊎.inl (a , n≡2a)   | ⊎.inl (b , m≡2b)   =
                  n≡2a ∙ cong double (αOnce a b (evenHit n a n≡2a γn) (evenHit m b m≡2b γm)) ∙ sym m≡2b
          ... | ⊎.inl (a , n≡2a)   | ⊎.inr (b , m≡2b+1) =
                  Empty.rec (¬pq ( snd P↔Σα (a , evenHit n a n≡2a γn)
                                 , snd Q↔Σβ (b , oddHit m b m≡2b+1 γm) ))
          ... | ⊎.inr (a , n≡2a+1) | ⊎.inl (b , m≡2b)   =
                  Empty.rec (¬pq ( snd P↔Σα (b , evenHit m b m≡2b γm)
                                 , snd Q↔Σβ (a , oddHit n a n≡2a+1 γn) ))
          ... | ⊎.inr (a , n≡2a+1) | ⊎.inr (b , m≡2b+1) =
                  n≡2a+1 ∙ cong (λ k → suc (double k)) (βOnce a b (oddHit n a n≡2a+1 γn) (oddHit m b m≡2b+1 γm)) ∙ sym m≡2b+1

          concl : LLPOExplicitAt (γ , γAtMostOnce) → ⟨ ¬ P ⟩ ⊎ ⟨ ¬ Q ⟩
          concl (⊎.inl evensFalse) = ⊎.inl λ p →
            let (n , αn) = fst P↔Σα p
            in true≢false (sym αn ∙ sym (interleave-even α β n) ∙ evensFalse n)
          concl (⊎.inr oddsFalse) = ⊎.inr λ q →
            let (n , βn) = fst Q↔Σβ q
            in true≢false (sym βn ∙ sym (interleave-odd α β n) ∙ oddsFalse n)
    
