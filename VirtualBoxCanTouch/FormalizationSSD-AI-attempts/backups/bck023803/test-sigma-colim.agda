{-# OPTIONS --cubical --guardedness #-}
module work.test-sigma-colim where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
open import Cubical.Foundations.HLevels using (isSetΣ; isOfHLevelΠ)
open import Cubical.Foundations.Transport using (transportTransport⁻)
open import Cubical.Data.Nat using (ℕ; zero; suc; isSetℕ)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Sequence using (Sequence)
open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
open Sequence

module SeqColimΣ {ℓ : Level} (S : Sequence ℓ) (B : SeqColim S → Type ℓ)
  (isSetColim : isSet (SeqColim S))
  (isSetB : (a : SeqColim S) → isSet (B a)) where

  ΣObj : ℕ → Type ℓ
  ΣObj n = Σ (obj S n) (λ x → B (incl x))

  ΣMap : {n : ℕ} → ΣObj n → ΣObj (suc n)
  ΣMap (x , b) = map S x , subst B (push x) b

  ΣSeq : Sequence ℓ
  obj ΣSeq = ΣObj
  map ΣSeq = ΣMap

  -- Forward: SeqColim ΣSeq → Σ (SeqColim S) B
  fwd : SeqColim ΣSeq → Σ (SeqColim S) B
  fwd (incl (x , b)) = incl x , b
  fwd (push (x , b) i) = push x i , subst-filler B (push x) b i

  -- Backward: Σ (SeqColim S) B → SeqColim ΣSeq
  bwd : Σ (SeqColim S) B → SeqColim ΣSeq
  bwd (incl x , b) = incl (x , b)
  bwd (push {n = n} x i , b) =
    hcomp (λ j → λ { (i = i0) → incl {n = n} (x , b)
                    ; (i = i1) → incl {n = suc n} (map S x , transportTransport⁻ (cong B (push x)) b j) })
          (push {n = n} (x , b₀) i)
    where
      b₀ : B (incl x)
      b₀ = transp (λ j → B (push x (i ∧ ~ j))) (~ i) b

  -- Set-ness
  postulate isSetΣColim : isSet (SeqColim ΣSeq)
  isSetTarget : isSet (Σ (SeqColim S) B)
  isSetTarget = isSetΣ isSetColim isSetB

  -- Helper: isProp for Π into set-paths
  isPropΠ' : {A : Type ℓ} {B : A → Type ℓ} → ((a : A) → isProp (B a)) → isProp ((a : A) → B a)
  isPropΠ' h f g i a = h a (f a) (g a) i

  -- fwd ∘ bwd roundtrip
  sec : (p : Σ (SeqColim S) B) → fwd (bwd p) ≡ p
  sec (incl x , b) = refl
  sec (push {n = n} x i , b) = lemma i b where
    -- Handle push by working with the function (b : B(push x i)) → ...
    -- At each j, the type B(push x j) → (fwd(bwd(push x j, b)) ≡ (push x j, b)) is a prop
    lemma : PathP (λ i → (b : B (push x i)) → fwd (bwd (push x i , b)) ≡ (push x i , b))
                  (λ b → refl) (λ b → refl)
    lemma = isProp→PathP
      (λ j → isPropΠ' (λ b → isSetTarget (fwd (bwd (push x j , b))) (push x j , b)))
      (λ b → refl) (λ b → refl)

  -- bwd ∘ fwd roundtrip
  ret : (c : SeqColim ΣSeq) → bwd (fwd c) ≡ c
  ret (incl xb) = refl
  ret (push {n = n} (x , b) i) =
    isProp→PathP (λ j → isSetΣColim (bwd (fwd (push (x , b) j))) (push (x , b) j))
      refl refl i

  theIso : Iso (SeqColim ΣSeq) (Σ (SeqColim S) B)
  theIso = iso fwd bwd sec ret

  theEquiv : SeqColim ΣSeq ≃ Σ (SeqColim S) B
  theEquiv = isoToEquiv theIso
