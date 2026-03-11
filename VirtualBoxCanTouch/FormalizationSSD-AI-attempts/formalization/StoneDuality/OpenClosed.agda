{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneDuality.OpenClosed (fa : FoundationalAxioms) where

open import formalization.StoneDuality.Omniscience fa public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Relation.Nullary
open import Cubical.HITs.PropositionalTruncation as PT
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
open import Axioms.StoneDuality using (Booleω; Sp; hasStoneStr)

open import BooleanRing.FreeBooleanRing.freeBATerms using (equalityFromEqualityOnGenerators)

SpB∞-to-ℕ∞-injective : (h₁ h₂ : Sp B∞-Booleω) →
  SpB∞-to-ℕ∞ h₁ ≡ SpB∞-to-ℕ∞ h₂ → h₁ ≡ h₂
SpB∞-to-ℕ∞-injective h₁ h₂ seq-eq = B∞-hom-eq
  where
  h₁-free h₂-free : BoolHom (freeBA ℕ) BoolBR
  h₁-free = h₁ ∘cr π∞
  h₂-free = h₂ ∘cr π∞

  free-hom-eq : h₁-free ≡ h₂-free
  free-hom-eq = equalityFromEqualityOnGenerators BoolBR h₁-free h₂-free (funExt⁻ (cong fst seq-eq))

  B∞-hom-eq : h₁ ≡ h₂
  B∞-hom-eq = CommRingHom≡ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = relB∞}
    (⟨ BoolBR ⟩ , BooleanRingStr.is-set (snd BoolBR))
    (cong fst free-hom-eq))

SpB∞-retraction : (h : Sp B∞-Booleω) → ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h) ≡ h
SpB∞-retraction h = SpB∞-to-ℕ∞-injective (ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h)) h
  (SpB∞-roundtrip (SpB∞-to-ℕ∞ h))

SpB∞≅ℕ∞ : Iso (Sp B∞-Booleω) ℕ∞
SpB∞≅ℕ∞ = iso SpB∞-to-ℕ∞ ℕ∞-to-SpB∞ SpB∞-roundtrip SpB∞-retraction

SpB∞≃ℕ∞ : Sp B∞-Booleω ≃ ℕ∞
SpB∞≃ℕ∞ = isoToEquiv SpB∞≅ℕ∞

ℕ∞-has-StoneStr : hasStoneStr ℕ∞
ℕ∞-has-StoneStr = B∞-Booleω , ua SpB∞≃ℕ∞

-- Bool is Stone (tex line 1527)
Bool-has-StoneStr : hasStoneStr Bool
Bool-has-StoneStr = Bool²-Booleω , ua Sp-Bool²≃Bool

-- LLPO proved from Stone Duality (tex Theorem LLPO, line 541)
llpo : LLPO
llpo = llpo-from-SD

-- (tex Lemma ClosedDeMorgan, line 760)
closedDeMorgan : (P Q : hProp ℓ-zero) → isClosedProp P → isClosedProp Q
               → ¬ ((¬ ⟨ P ⟩) × (¬ ⟨ Q ⟩)) → ∥ ⟨ P ⟩ ⊎ ⟨ Q ⟩ ∥₁
closedDeMorgan P Q Pclosed Qclosed ¬¬P∧¬Q = PT.rec2 squash₁ go Pclosed Qclosed
  where
  open import Cubical.Data.Nat.Order
  import Cubical.Induction.WellFounded as WF

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
        llpo-result = llpo δ∞

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

-- tex Lemma 691 (closed stable under finite disjunctions)
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

-- (tex line 716)
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
