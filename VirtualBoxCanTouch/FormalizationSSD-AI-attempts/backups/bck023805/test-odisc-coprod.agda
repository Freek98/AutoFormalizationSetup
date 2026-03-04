{-# OPTIONS --cubical --guardedness #-}
module work.test-odisc-coprod where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_; invEq; secEq; compEquiv; equivFun)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv; isoToPath)
open import Cubical.Foundations.HLevels using (isPropΠ; isSetΣ)
open import Cubical.Foundations.Transport using (substCommSlice; substComposite)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; _∸_; isSetℕ)
open import Cubical.Data.Nat.Properties using (+-suc; +-comm; +-zero; +∸)
open import Cubical.Data.Nat.Order using (_≤_; isProp≤; ≤-refl; ≤-suc; ≤SumRight; ≤-∸-suc; ≤-∸-+-cancel)
open import Cubical.Data.Sigma using (ΣPathP; _×_)
open import Cubical.Data.Sequence using (Sequence)
open import Cubical.Data.FinSet using (isFinSet)
open import Cubical.Data.FinSet.Properties using (isFinSetFin)
open import Cubical.Data.FinSet.Constructors using (isFinSetΣ)
open import Cubical.Data.SumFin.Base using (Fin; fzero; fsuc; toℕ; finj; flast)
open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open Sequence

-- suc (k ∸ n) ≡ suc k ∸ n for n ≤ k (from library, but with swapped sides)
suc∸≤ : (n k : ℕ) → n ≤ k → suc k ∸ n ≡ suc (k ∸ n)
suc∸≤ n k p = sym (≤-∸-suc p)

-- The Fin (suc k) ↔ (n ≤ k) bridge
toℕ-finj : {k : ℕ} (i : Fin k) → toℕ (finj i) ≡ toℕ i
toℕ-finj {suc k} fzero = refl
toℕ-finj {suc k} (fsuc x) = cong suc (toℕ-finj x)

toℕ-flast : {k : ℕ} → toℕ (flast {k}) ≡ k
toℕ-flast {zero} = refl
toℕ-flast {suc k} = cong suc toℕ-flast

-- Given a family of ODisc witnesses (sequences with finite levels), build the diagonal sequence
-- Using ℕ-indexed version: DiagObj k = Σ[ n ∈ ℕ ] (n ≤ k) × obj (Sn n) (k ∸ n)
-- This avoids PathP issues in the equivalence proof because the ℕ component is literally preserved.
module DiagSeq (Sn : ℕ → Sequence ℓ-zero)
               (finSn : (n m : ℕ) → isFinSet (obj (Sn n) m)) where

  DiagObj : ℕ → Type
  DiagObj k = Σ[ n ∈ ℕ ] (n ≤ k) × obj (Sn n) (k ∸ n)

  diagMap : {k : ℕ} → DiagObj k → DiagObj (suc k)
  diagMap {k} (n , p , x) = n , ≤-suc p , x' where
    mx : obj (Sn n) (suc (k ∸ n))
    mx = map (Sn n) x
    x' : obj (Sn n) (suc k ∸ n)
    x' = subst (obj (Sn n)) (sym (suc∸≤ n k p)) mx

  T : Sequence ℓ-zero
  obj T = DiagObj
  map T = diagMap

  -- Finiteness: DiagObj k is finite because Σ[ n ∈ ℕ ] (n ≤ k) ≃ Fin (suc k)
  -- and each fiber obj (Sn n) (k ∸ n) is finite.
  -- We prove this via an equivalence with the Fin-indexed version.
  DiagObjFin : ℕ → Type
  DiagObjFin k = Σ[ i ∈ Fin (suc k) ] obj (Sn (toℕ i)) (k ∸ toℕ i)

  isFinSetDiagObjFin : (k : ℕ) → isFinSet (DiagObjFin k)
  isFinSetDiagObjFin k = isFinSetΣ (_ , isFinSetFin)
    (λ i → _ , finSn (toℕ i) (k ∸ toℕ i))

  -- TODO: prove DiagObj k ≃ DiagObjFin k and derive isFinSet (DiagObj k)
  postulate isFinSetDiagObj : (k : ℕ) → isFinSet (DiagObj k)

  -- incl-tr: path incl x ≡ incl (subst (obj S) p x) via J
  incl-tr : {S : Sequence ℓ-zero} {m₁ m₂ : ℕ} (p : m₁ ≡ m₂) (x : obj S m₁)
    → Path (SeqColim S) (incl x) (incl (subst (obj S) p x))
  incl-tr {S = S} = J (λ m₂ p → (x : obj S _) → incl x ≡ incl (subst (obj S) p x))
    λ x → cong incl (sym (transportRefl x))

  -- Forward map: SeqColim T → Σ ℕ (SeqColim ∘ Sn)
  fwd-incl : (k : ℕ) → DiagObj k → Σ ℕ (λ n → SeqColim (Sn n))
  fwd-incl k (n , _ , x) = n , incl x

  fwd-push : (k : ℕ) (d : DiagObj k) → fwd-incl k d ≡ fwd-incl (suc k) (diagMap d)
  fwd-push k (n , p , x) = ΣPathP (refl , push-path) where
    push-path : incl x ≡ incl (subst (obj (Sn n)) (sym (suc∸≤ n k p)) (map (Sn n) x))
    push-path = push {X = Sn n} x ∙ incl-tr {S = Sn n} (sym (suc∸≤ n k p)) (map (Sn n) x)

  fwd : SeqColim T → Σ ℕ (λ n → SeqColim (Sn n))
  fwd (incl {n = k} d) = fwd-incl k d
  fwd (push {n = k} d j) = fwd-push k d j

  -- Backward map: Σ ℕ (SeqColim ∘ Sn) → SeqColim T
  -- Given (n, incl {m} y), embed at level m + n:
  --   m + n ∸ n ≡ m (by +∸)
  --   n ≤ m + n (by ≤SumRight)
  bwd-incl : (n m : ℕ) → obj (Sn n) m → SeqColim T
  bwd-incl n m y = incl {n = m + n} (n , ≤SumRight , subst (obj (Sn n)) (sym (+∸ m n)) y)

  -- Push coherence: bwd-incl n m y ≡ bwd-incl n (suc m) (map (Sn n) y)
  -- LHS: incl {m + n} (n , ≤SumRight , subst ... y)
  -- RHS: incl {suc m + n} (n , ≤SumRight , subst ... (map (Sn n) y))
  --   = incl {suc (m + n)} (n , ≤SumRight , subst ... (map (Sn n) y))
  -- Connect via push in SeqColim T:
  --   push d : incl d ≡ incl (diagMap d)
  --   Then show diagMap (...) ≡ (...) in DiagObj (suc (m + n))
  bwd-push : (n m : ℕ) (y : obj (Sn n) m) → bwd-incl n m y ≡ bwd-incl n (suc m) (map (Sn n) y)
  bwd-push n m y = push d ∙ cong incl diagMap-eq where
    d : DiagObj (m + n)
    d = n , ≤SumRight , subst (obj (Sn n)) (sym (+∸ m n)) y
    z = subst (obj (Sn n)) (sym (+∸ m n)) y
    B = obj (Sn n)
    p₁ = cong suc (sym (+∸ m n))
    p₂ = sym (suc∸≤ n (m + n) ≤SumRight)
    -- diagMap d = (n , ≤-suc ≤SumRight , subst B p₂ (map (Sn n) z))
    -- target    = (n , ≤SumRight ,        subst B (sym (+∸ (suc m) n)) (map (Sn n) y))
    elem-eq : subst B p₂ (map (Sn n) z)
            ≡ subst B (sym (+∸ (suc m) n)) (map (Sn n) y)
    elem-eq =
      subst B p₂ (map (Sn n) z)
        ≡⟨ cong (subst B p₂)
             (sym (substCommSlice B (λ k → B (suc k)) (λ k → map (Sn n)) (sym (+∸ m n)) y)) ⟩
      subst B p₂ (subst B p₁ (map (Sn n) y))
        ≡⟨ sym (substComposite B p₁ p₂ (map (Sn n) y)) ⟩
      subst B (p₁ ∙ p₂) (map (Sn n) y)
        ≡⟨ cong (λ q → subst B q (map (Sn n) y)) (isSetℕ _ _ (p₁ ∙ p₂) (sym (+∸ (suc m) n))) ⟩
      subst B (sym (+∸ (suc m) n)) (map (Sn n) y) ∎
    diagMap-eq : diagMap d ≡ (n , ≤SumRight , subst B (sym (+∸ (suc m) n)) (map (Sn n) y))
    diagMap-eq = ΣPathP (refl , ΣPathP (isProp≤ _ _ , elem-eq))

  bwd : Σ ℕ (λ n → SeqColim (Sn n)) → SeqColim T
  bwd (n , incl {n = m} y) = bwd-incl n m y
  bwd (n , push {n = m} y j) = bwd-push n m y j

  -- Roundtrip fwd ∘ bwd ≡ id
  -- On incl: fwd (bwd (n , incl y)) = fwd (incl (n , _ , subst ... y)) = (n , incl (subst ... y))
  -- Need: (n , incl (subst ... y)) ≡ (n , incl y)
  -- The incl-tr gives: incl y ≡ incl (subst ... y), so sym gives what we need.
  fwd-bwd-incl : (n m : ℕ) (y : obj (Sn n) m)
    → fwd (bwd-incl n m y) ≡ (n , incl y)
  fwd-bwd-incl n m y = ΣPathP (refl , sym (incl-tr {S = Sn n} (sym (+∸ m n)) y))

  -- bwd-fwd on incl: connect incl {(k∸n)+n} d₁ to incl {k} d₂
  -- Strategy: construct a PathP over ≤-∸-+-cancel from d₁ to d₂, then use cong incl
  bwd-fwd-incl : (k : ℕ) (d : DiagObj k) → bwd (fwd (incl {n = k} d)) ≡ incl {n = k} d
  bwd-fwd-incl k (n , p , x) = λ i → incl {n = q i} (diag-pathp i) where
    q = ≤-∸-+-cancel p
    x₁ = subst (obj (Sn n)) (sym (+∸ (k ∸ n) n)) x
    -- PathP for the obj component
    obj-pathp : PathP (λ i → obj (Sn n) (q i ∸ n)) x₁ x
    obj-pathp = toPathP (
      subst (obj (Sn n)) (cong (_∸ n) q)
        (subst (obj (Sn n)) (sym (+∸ (k ∸ n) n)) x)
        ≡⟨ sym (substComposite (obj (Sn n)) (sym (+∸ (k ∸ n) n)) (cong (_∸ n) q) x) ⟩
      subst (obj (Sn n)) (sym (+∸ (k ∸ n) n) ∙ cong (_∸ n) q) x
        ≡⟨ cong (λ r → subst (obj (Sn n)) r x) (isSetℕ _ _ _ refl) ⟩
      subst (obj (Sn n)) refl x
        ≡⟨ transportRefl x ⟩
      x ∎)
    -- PathP for the ≤ component
    leq-pathp : PathP (λ i → n ≤ q i) ≤SumRight p
    leq-pathp = isProp→PathP (λ _ → isProp≤) ≤SumRight p
    -- Combined PathP for DiagObj
    diag-pathp : PathP (λ i → DiagObj (q i))
      (n , ≤SumRight , x₁) (n , p , x)
    diag-pathp i = n , leq-pathp i , obj-pathp i

  -- For roundtrips on push cases, we need the target types to be sets
  postulate
    isSetSCn : (n : ℕ) → isSet (SeqColim (Sn n))
    isSetSCT : isSet (SeqColim T)
  isSetTarget : isSet (Σ ℕ (λ n → SeqColim (Sn n)))
  isSetTarget = isSetΣ isSetℕ (λ n → isSetSCn n)

  -- fwd ∘ bwd roundtrip
  fwd-bwd : (x : Σ ℕ (λ n → SeqColim (Sn n))) → fwd (bwd x) ≡ x
  fwd-bwd (n , incl y) = fwd-bwd-incl n _ y
  fwd-bwd (n , push {n = m} y j) =
    isProp→PathP (λ j → isSetTarget (fwd (bwd (n , push y j))) (n , push y j))
      (fwd-bwd-incl n m y) (fwd-bwd-incl n (suc m) (map (Sn n) y)) j

  -- bwd ∘ fwd roundtrip
  bwd-fwd : (c : SeqColim T) → bwd (fwd c) ≡ c
  bwd-fwd (incl {n = k} d) = bwd-fwd-incl k d
  bwd-fwd (push {n = k} d j) =
    isProp→PathP (λ j → isSetSCT (bwd (fwd (push d j))) (push d j))
      (bwd-fwd-incl k d) (bwd-fwd-incl (suc k) (diagMap d)) j

  equiv : SeqColim T ≃ Σ ℕ (λ n → SeqColim (Sn n))
  equiv = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)
