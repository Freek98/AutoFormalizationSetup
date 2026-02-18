{-# OPTIONS --cubical --guardedness #-}

-- tex Section 1.5: Open and closed propositions (lines 668-900)
-- Closure properties, de Morgan laws, countable operations, decidability

module SSD.StoneDuality.OpenClosed where

open import SSD.StoneDuality.Axioms public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
import Cubical.Induction.WellFounded as WF
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum.Properties using (isProp⊎)

open import Cubical.Relation.Nullary
open import Cubical.Relation.Nullary.Properties using (isPropDec)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

-- All closure properties of open/closed, parameterized over axioms

module OpenClosedProperties (axioms : Axioms) where
  open WithAxioms axioms

  -- tex Lemma 691: Closed propositions are closed under conjunction
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

  -- tex Lemma 691: Open propositions are closed under disjunction (with MP)
  openOrMP : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
          → isOpenProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
  openOrMP P Q Popen Qopen = PT.rec2 squash₁ go Popen Qopen
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

  -- tex Lemma 691: Open propositions are closed under conjunction
  openAnd : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
          → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
  openAnd P Q Popen Qopen = PT.rec2 squash₁ go Popen Qopen
    where
    go : isOpenWitness P → isOpenWitness Q
       → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
    go (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = ∣ γ , forward , backward ∣₁
      where
      γ : binarySequence
      γ k = let (n , m) = cantorUnpair k in α n and β m

      forward : ⟨ P ⟩ × ⟨ Q ⟩ → Σ[ k ∈ ℕ ] γ k ≡ true
      forward (p , q) =
        let (n , αn=t) = P→∃α p
            (m , βm=t) = Q→∃β q
            k = cantorPair n m
            γk=t : γ k ≡ true
            γk=t =
              γ k
                ≡⟨ cong (λ p → α (fst p) and β (snd p)) (cantorUnpair-pair n m) ⟩
              α n and β m
                ≡⟨ cong (λ x → x and β m) αn=t ⟩
              true and β m
                ≡⟨ cong (true and_) βm=t ⟩
              true ∎
        in (k , γk=t)

      backward : Σ[ k ∈ ℕ ] γ k ≡ true → ⟨ P ⟩ × ⟨ Q ⟩
      backward (k , γk=t) =
        let (n , m) = cantorUnpair k
            αn=t : α n ≡ true
            αn=t = and-true-left (α n) (β m) γk=t
            βm=t : β m ≡ true
            βm=t = and-true-right (α n) (β m) γk=t
        in (∃α→P (n , αn=t)) , (∃β→Q (m , βm=t))
        where
        and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
        and-true-left true  _ _ = refl
        and-true-left false _ p = ex-falso (false≢true p)

        and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
        and-true-right true  _ p = p
        and-true-right false _ p = ex-falso (false≢true p)

  -- De Morgan for closed propositions (uses LLPO)
  closedDeMorgan : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
                 → ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
  closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q = PT.rec2 squash₁ go Pclosed Qclosed
    where
    go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false)
       → Σ[ β ∈ binarySequence ] ⟨ Q ⟩ ↔ ((n : ℕ) → β n ≡ false)
       → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
    go (α , P→∀α , ∀α→P) (β , Q→∀β , ∀β→Q) =
      let
          δ₀ : binarySequence
          δ₀ = interleave α β

          δ : binarySequence
          δ = firstTrue δ₀

          δ-hamo : hitsAtMostOnce δ
          δ-hamo = firstTrue-hitsAtMostOnce δ₀

          δ∞ : ℕ∞
          δ∞ = δ , δ-hamo

          llpo-result : ∥ ((k : ℕ) → δ (2 ·ℕ k) ≡ false) ⊎ ((k : ℕ) → δ (suc (2 ·ℕ k)) ≡ false) ∥₁
          llpo-result = llpo-ax δ∞

      in PT.rec squash₁ helper llpo-result
      where
      module _ where
        open WF.WFI (<-wellfounded)

        ResultOdd : ℕ → Type₀
        ResultOdd n = interleave α β n ≡ true
                    → ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
                    → Σ[ m ∈ ℕ ] (isEvenB m ≡ false) × (β (half m) ≡ true)

        find-first-true-odd-step : (n : ℕ) → ((m : ℕ) → m < n → ResultOdd m) → ResultOdd n
        find-first-true-odd-step n rec δ₀-n=t allEvensF with firstTrue (interleave α β) n =B true
        ... | yes ft-n=t with isEvenB n =B true
        ...   | yes n-even =
                ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true)
                                            (sym (2·half-even n n-even)) ft-n=t)
                                      ∙ allEvensF (half n)))
        ...   | no n-odd =
                let odd-eq = ¬true→false (isEvenB n) n-odd
                in n , odd-eq , sym (interleave-odd α β n odd-eq) ∙ δ₀-n=t
        find-first-true-odd-step n rec δ₀-n=t allEvensF | no ft-n≠t =
          let (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n
                                      (¬true→false (firstTrue (interleave α β) n) ft-n≠t) δ₀-n=t
          in rec m m<n δ₀-m=t allEvensF

        find-first-true-odd : (n : ℕ) → ResultOdd n
        find-first-true-odd = induction find-first-true-odd-step

      allEvensF-implies-P : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false) → ⟨ P ⟩
      allEvensF-implies-P allEvensF = closedIsStable P Pclosed ¬¬P
        where
        ¬¬P : ¬ ¬ ⟨ P ⟩
        ¬¬P ¬p =
          let (k , αk=t) = mp α (λ all-false → ¬p (∀α→P all-false))
              (m , m-odd , βj=t) = find-first-true-odd (2 ·ℕ k) (interleave-2k α β k ∙ αk=t) allEvensF
          in ¬¬P∧¬Q (¬p , λ q → false≢true (sym (Q→∀β q (half m)) ∙ βj=t))

      module _ where
        open WF.WFI (<-wellfounded)

        ResultEven : ℕ → Type₀
        ResultEven n = interleave α β n ≡ true
                     → ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
                     → Σ[ m ∈ ℕ ] (isEvenB m ≡ true) × (α (half m) ≡ true)

        find-first-true-even-step : (n : ℕ) → ((m : ℕ) → m < n → ResultEven m) → ResultEven n
        find-first-true-even-step n rec δ₀-n=t allOddsF with firstTrue (interleave α β) n =B true
        ... | yes ft-n=t with isEvenB n =B true
        ...   | yes n-even =
                n , n-even , sym (interleave-even α β n n-even) ∙ δ₀-n=t
        ...   | no n-odd =
                let odd-eq = ¬true→false (isEvenB n) n-odd
                in ex-falso (true≢false (sym (subst (λ x → firstTrue (interleave α β) x ≡ true)
                                               (sym (suc-2·half-odd n odd-eq)) ft-n=t)
                                         ∙ allOddsF (half n)))
        find-first-true-even-step n rec δ₀-n=t allOddsF | no ft-n≠t =
          let (m , m<n , δ₀-m=t) = firstTrue-false-but-original-true (interleave α β) n
                                      (¬true→false (firstTrue (interleave α β) n) ft-n≠t) δ₀-n=t
          in rec m m<n δ₀-m=t allOddsF

        find-first-true-even : (n : ℕ) → ResultEven n
        find-first-true-even = induction find-first-true-even-step

      allOddsF-implies-Q : ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false) → ⟨ Q ⟩
      allOddsF-implies-Q allOddsF = closedIsStable Q Qclosed ¬¬Q
        where
        ¬¬Q : ¬ ¬ ⟨ Q ⟩
        ¬¬Q ¬q =
          let (k , βk=t) = mp β (λ all-false → ¬q (∀β→Q all-false))
              (m , m-even , αj=t) = find-first-true-even (suc (2 ·ℕ k)) (interleave-2k+1 α β k ∙ βk=t) allOddsF
          in ¬¬P∧¬Q ((λ p → false≢true (sym (P→∀α p (half m)) ∙ αj=t)) , ¬q)

      helper : ((k : ℕ) → firstTrue (interleave α β) (2 ·ℕ k) ≡ false)
             ⊎ ((k : ℕ) → firstTrue (interleave α β) (suc (2 ·ℕ k)) ≡ false)
             → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
      helper (inl allEvensF) = ∣ inl (allEvensF-implies-P allEvensF) ∣₁
      helper (inr allOddsF) = ∣ inr (allOddsF-implies-Q allOddsF) ∣₁

  -- Closed propositions are closed under disjunction
  closedOr : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
           → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
  closedOr P Q Pclosed Qclosed = PT.rec2 squash₁ go Pclosed Qclosed
    where
    go : Σ[ αP ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → αP n ≡ false)
       → Σ[ αQ ∈ binarySequence ] ⟨ Q ⟩ ↔ ((n : ℕ) → αQ n ≡ false)
       → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
    go (αP , P→∀ , ∀→P) (αQ , Q→∀ , ∀→Q) =
      PT.rec squash₁ go2 ¬P∧¬Qopen
      where
      ¬P : hProp ℓ-zero
      ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩

      ¬Q : hProp ℓ-zero
      ¬Q = (¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩

      ¬P∧¬Qopen : isOpenProp (((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) , isProp× (isProp¬ ⟨ P ⟩) (isProp¬ ⟨ Q ⟩))
      ¬P∧¬Qopen = openAnd ¬P ¬Q (negClosedIsOpen mp P αP (P→∀ , ∀→P)) (negClosedIsOpen mp Q αQ (Q→∀ , ∀→Q))

      go2 : isOpenWitness (((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) , isProp× (isProp¬ ⟨ P ⟩) (isProp¬ ⟨ Q ⟩))
          → isClosedProp (∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ , squash₁)
      go2 (γ , fwd-open , bwd-open) = ∣ γ , forward , backward ∣₁
        where
        forward : ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁ → (n : ℕ) → γ n ≡ false
        forward P∨Q n with γ n =B true
        ... | yes γn=t = ex-falso (PT.rec isProp⊥ (helper γn=t) P∨Q)
          where
          helper : γ n ≡ true → ⟨ P ⟩ ⊎ ⟨ Q ⟩ → ⊥
          helper γn=t (inl p) = fst (bwd-open (n , γn=t)) p
          helper γn=t (inr q) = snd (bwd-open (n , γn=t)) q
        ... | no γn≠t = ¬true→false (γ n) γn≠t

        backward : ((n : ℕ) → γ n ≡ false) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
        backward all-false =
          closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q
          where
          ¬¬P∧¬Q : ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩))
          ¬¬P∧¬Q (¬p , ¬q) =
            let (n , γn=t) = fwd-open (¬p , ¬q)
            in false≢true (sym (all-false n) ∙ γn=t)

  -- tex line 716: Open de Morgan
  openDeMorgan : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
               → (¬ (⟨ P ⟩ × ⟨ Q ⟩)) ↔ ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
  openDeMorgan P Q Popen Qopen = forward , backward
    where
    forward : ¬ (⟨ P ⟩ × ⟨ Q ⟩) → ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁
    forward ¬P×Q = closedDeMorgan (¬hProp P) (¬hProp Q) (negOpenIsClosed P Popen) (negOpenIsClosed Q Qopen)
      (λ (¬¬p , ¬¬q) → ¬P×Q (openIsStable mp P Popen ¬¬p , openIsStable mp Q Qopen ¬¬q))

    backward : ∥ (¬ ⟨ P ⟩) ⊎ (¬ ⟨ Q ⟩) ∥₁ → ¬ (⟨ P ⟩ × ⟨ Q ⟩)
    backward = PT.rec (isProp¬ _) λ
      { (inl ¬p) (p , _) → ¬p p
      ; (inr ¬q) (_ , q) → ¬q q
      }

  -- Countable intersection of closed is closed
  closedCountableIntersection : (P : ℕ → hProp ℓ-zero)
                              → ((n : ℕ) → isClosedProp (P n))
                              → isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
  closedCountableIntersection P αs =
    PT.rec squash₁ go (countableChoice _ αs)
    where
    go : ((n : ℕ) → Σ[ α ∈ binarySequence ] ⟨ P n ⟩ ↔ ((k : ℕ) → α k ≡ false))
       → isClosedProp (((n : ℕ) → ⟨ P n ⟩) , isPropΠ (λ n → snd (P n)))
    go αs-bare = ∣ β , forward , backward ∣₁
      where
      αP : ℕ → binarySequence
      αP n = fst (αs-bare n)

      β : binarySequence
      β k = let (m , n) = cantorUnpair k in αP m n

      forward : ((n : ℕ) → ⟨ P n ⟩) → (k : ℕ) → β k ≡ false
      forward allP k =
        let (m , n) = cantorUnpair k
            Pm→allFalse = fst (snd (αs-bare m))
        in Pm→allFalse (allP m) n

      backward : ((k : ℕ) → β k ≡ false) → (n : ℕ) → ⟨ P n ⟩
      backward allβFalse n = snd (snd (αs-bare n)) allαnFalse
        where
        allαnFalse : (k : ℕ) → αP n k ≡ false
        allαnFalse k =
          αP n k
            ≡⟨ cong (λ p → αP (fst p) (snd p)) (sym (cantorUnpair-pair n k)) ⟩
          αP (fst (cantorUnpair (cantorPair n k))) (snd (cantorUnpair (cantorPair n k)))
            ≡⟨ allβFalse (cantorPair n k) ⟩
          false ∎

  -- Countable union of open is open
  openCountableUnion : (P : ℕ → hProp ℓ-zero)
                     → ((n : ℕ) → isOpenProp (P n))
                     → isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ , squash₁)
  openCountableUnion P αs = PT.rec squash₁ go (countableChoice _ αs)
    where
    go : ((n : ℕ) → isOpenWitness (P n))
       → isOpenProp (∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ , squash₁)
    go αs-bare = ∣ β , forward , backward ∣₁
      where
      αP : ℕ → binarySequence
      αP n = fst (αs-bare n)

      β : binarySequence
      β k = let (m , n) = cantorUnpair k in αP m n

      backward : Σ[ k ∈ ℕ ] β k ≡ true → ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁
      backward (k , βk=t) = let (n , m) = cantorUnpair k in ∣ n , snd (snd (αs-bare n)) (m , βk=t) ∣₁

      forward : ∥ Σ[ n ∈ ℕ ] ⟨ P n ⟩ ∥₁ → Σ[ k ∈ ℕ ] β k ≡ true
      forward truncExists = mp β ¬allFalse
        where
        ¬allFalse : ¬ ((k : ℕ) → β k ≡ false)
        ¬allFalse allFalse = PT.rec isProp⊥ helper truncExists
          where
          helper : Σ[ n ∈ ℕ ] ⟨ P n ⟩ → ⊥
          helper (n , pn) =
            let Pn→exists = fst (snd (αs-bare n))
                (m , αnm=t) = Pn→exists pn
                k = cantorPair n m
                βk=t : β k ≡ true
                βk=t =
                  αP (fst (cantorUnpair k)) (snd (cantorUnpair k))
                    ≡⟨ cong (λ p → αP (fst p) (snd p)) (cantorUnpair-pair n m) ⟩
                  αP n m
                    ≡⟨ αnm=t ⟩
                  true ∎
            in false≢true (sym (allFalse k) ∙ βk=t)

  -- tex Corollary 774: ClopenDecidable
  clopenIsDecidable : (P : hProp ℓ-zero) → isOpenProp P → isClosedProp P → Dec ⟨ P ⟩
  clopenIsDecidable P Popen Pclosed = PT.rec (isPropDec (snd P)) go Pclosed
    where
    go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false) → Dec ⟨ P ⟩
    go (α , P→∀ , ∀→P) =
      let ¬P = (¬ ⟨ P ⟩) , isProp¬ ⟨ P ⟩
          ¬Popen = negClosedIsOpen mp P α (P→∀ , ∀→P)
          P∨¬P-trunc = (∥ ⟨ P ⟩ ⊎ (¬ ⟨ P ⟩) ∥₁) , squash₁
          P∨¬P-trunc-open = openOrMP P ¬P Popen ¬Popen
      in ⊎.rec yes no (PT.rec (isProp⊎ (snd P) (isProp¬ ⟨ P ⟩) (λ p ¬p → ¬p p)) (λ x → x)
           (openIsStable mp P∨¬P-trunc P∨¬P-trunc-open
             (λ k → k ∣ inr (λ p → k ∣ inl p ∣₁) ∣₁)))

  -- tex Lemma 857: ImplicationOpenClosed
  implicationOpenClosed : (P Q : hProp ℓ-zero) → isOpenProp P → isClosedProp Q
                        → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
  implicationOpenClosed P Q Popen Qclosed = PT.rec squash₁ go Qclosed
    where
    go : Σ[ αQ ∈ binarySequence ] ⟨ Q ⟩ ↔ ((n : ℕ) → αQ n ≡ false)
       → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
    go (αQ , Q→∀ , ∀→Q) = PT.rec squash₁ go2 ¬P∧¬Qclosed
      where
      P∧¬Qopen : isOpenProp ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩))
      P∧¬Qopen = openAnd P ((¬ ⟨ Q ⟩) , isProp¬ ⟨ Q ⟩) Popen (negClosedIsOpen mp Q αQ (Q→∀ , ∀→Q))

      ¬P∧¬Qclosed : isClosedProp (¬hProp ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)))
      ¬P∧¬Qclosed = negOpenIsClosed ((⟨ P ⟩ × (¬ ⟨ Q ⟩)) , isProp× (snd P) (isProp¬ ⟨ Q ⟩)) P∧¬Qopen

      go2 : Σ[ γ ∈ binarySequence ] (¬ (⟨ P ⟩ × (¬ ⟨ Q ⟩))) ↔ ((n : ℕ) → γ n ≡ false)
          → isClosedProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
      go2 (γ , ¬P∧¬Q→∀ , ∀→¬P∧¬Q) = ∣ γ , forward , backward ∣₁
        where
        forward : (⟨ P ⟩ → ⟨ Q ⟩) → (n : ℕ) → γ n ≡ false
        forward p→q = ¬P∧¬Q→∀ (λ (p , ¬q) → ¬q (p→q p))

        backward : ((n : ℕ) → γ n ≡ false) → ⟨ P ⟩ → ⟨ Q ⟩
        backward all-false p =
          closedIsStable (⟨ Q ⟩ , snd Q) Qclosed (λ ¬q → ∀→¬P∧¬Q all-false (p , ¬q))

  -- tex Lemma 807: ClosedMarkov
  closedMarkovTex : (P : ℕ → hProp ℓ-zero) → ((n : ℕ) → isClosedProp (P n))
                  → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
  closedMarkovTex P Pclosed = PT.rec isPropResult go (countableChoice _ Pclosed)
    where
    isPropResult : isProp ((¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁)
    isPropResult = isProp× (isPropΠ (λ _ → squash₁)) (isPropΠ (λ _ → isProp¬ _))

    go : ((n : ℕ) → Σ[ α ∈ binarySequence ] ⟨ P n ⟩ ↔ ((k : ℕ) → α k ≡ false))
       → (¬ ((n : ℕ) → ⟨ P n ⟩)) ↔ ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
    go bareWitnesses = forward , backward
      where
      ∃¬P-open : isOpenProp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁)
      ∃¬P-open = openCountableUnion (λ n → (¬ ⟨ P n ⟩) , isProp¬ _)
        (λ n → let (αn , iff) = bareWitnesses n in negClosedIsOpen mp (P n) αn iff)

      forward : ¬ ((n : ℕ) → ⟨ P n ⟩) → ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁
      forward ¬∀P = openIsStable mp (∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ , squash₁) ∃¬P-open
        (λ k → ¬∀P (λ n → closedIsStable (P n) (Pclosed n) (λ ¬Pn → k ∣ n , ¬Pn ∣₁)))

      backward : ∥ Σ[ n ∈ ℕ ] (¬ ⟨ P n ⟩) ∥₁ → ¬ ((n : ℕ) → ⟨ P n ⟩)
      backward = PT.rec (isProp¬ _) (λ { (n , ¬Pn) ∀P → ¬Pn (∀P n) })

  -- Open Sigma with decidable base
  openSigmaDecidable : (D : hProp ℓ-zero) → Dec ⟨ D ⟩
                     → (Q : ⟨ D ⟩ → hProp ℓ-zero) → ((d : ⟨ D ⟩) → isOpenProp (Q d))
                     → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
  openSigmaDecidable D (yes d) Q Qopen = PT.rec squash₁ go (Qopen d)
    where
    go : isOpenWitness (Q d) → isOpenProp (∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ , squash₁)
    go (α , Qd→∃ , ∃→Qd) = ∣ α , forward , backward ∣₁
      where
      forward : ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
      forward truncExists = mp α (λ allFalse → PT.rec isProp⊥
        (λ (d' , q) → let (n , αn=t) = Qd→∃ (subst (λ x → ⟨ Q x ⟩) (snd D d' d) q)
          in false≢true (sym (allFalse n) ∙ αn=t)) truncExists)

      backward : Σ[ n ∈ ℕ ] α n ≡ true → ∥ Σ[ d' ∈ ⟨ D ⟩ ] ⟨ Q d' ⟩ ∥₁
      backward w = ∣ d , ∃→Qd w ∣₁

  openSigmaDecidable D (no ¬d) Q Qopen = ∣ (λ _ → false) , forward , backward ∣₁
    where
    forward : ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁ → Σ[ n ∈ ℕ ] false ≡ true
    forward x = ex-falso (PT.rec isProp⊥ (λ { (d , _) → ¬d d }) x)

    backward : Σ[ n ∈ ℕ ] false ≡ true → ∥ Σ[ d ∈ ⟨ D ⟩ ] ⟨ Q d ⟩ ∥₁
    backward (_ , p) = ex-falso (false≢true p)

  -- tex Corollary OpenDependentSums 1313
  openSigmaOpen : (P : hProp ℓ-zero) → isOpenProp P
                → (Q : ⟨ P ⟩ → hProp ℓ-zero) → ((p : ⟨ P ⟩) → isOpenProp (Q p))
                → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
  openSigmaOpen P Popen Q Qopen = PT.rec squash₁ go Popen
    where
    go : isOpenWitness P → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
    go (α , P→∃ , ∃→P) = PT.rec squash₁ go-union (openCountableUnion Rn Rn-open)
      where
      witness : (n : ℕ) → (α n ≡ true) → ⟨ P ⟩
      witness n = λ eq → ∃→P (n , eq)

      Rn : ℕ → hProp ℓ-zero
      Rn n = (∥ Σ[ eq ∈ (α n ≡ true) ] ⟨ Q (witness n eq) ⟩ ∥₁) , squash₁

      Rn-open : (n : ℕ) → isOpenProp (Rn n)
      Rn-open n = openSigmaDecidable ((α n ≡ true) , isSetBool _ _) (α n =B true)
                    (λ eq → Q (witness n eq))
                    (λ eq → Qopen (witness n eq))

      go-union : isOpenWitness (∥ Σ[ n ∈ ℕ ] ⟨ Rn n ⟩ ∥₁ , squash₁)
               → isOpenProp (∥ Σ[ p ∈ ⟨ P ⟩ ] ⟨ Q p ⟩ ∥₁ , squash₁)
      go-union (β , union→∃ , ∃→union) = ∣ β ,
         (λ sigPQ → union→∃ (PT.rec squash₁
           (λ (p , qp) → let n = fst (P→∃ p) ; αn=t = snd (P→∃ p)
             in ∣ n , ∣ αn=t , subst (λ x → ⟨ Q x ⟩) (snd P p (witness n αn=t)) qp ∣₁ ∣₁)
           sigPQ)) ,
         (λ w → PT.rec squash₁ (λ (n , rn) →
           PT.rec squash₁ (λ (αn=t , qw) → ∣ witness n αn=t , qw ∣₁) rn) (∃→union w)) ∣₁

  -- tex Corollary OpenTransitive 1319
  openSubsetTransitive : {T : Type₀}
                       → (V : T → hProp ℓ-zero) → isOpenSubset V
                       → (W : (t : T) → ⟨ V t ⟩ → hProp ℓ-zero)
                       → ((t : T) (v : ⟨ V t ⟩) → isOpenProp (W t v))
                       → isOpenSubset (λ t → (∥ Σ[ v ∈ ⟨ V t ⟩ ] ⟨ W t v ⟩ ∥₁) , squash₁)
  openSubsetTransitive V Vopen W Wopen t =
    openSigmaOpen (V t) (Vopen t) (W t) (Wopen t)
