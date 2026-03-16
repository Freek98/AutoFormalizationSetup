{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OvertlyDiscrete.SeqColimDef where

-- Alternative definition of overtly discrete types as sequential colimits
-- of finite sets, and product closure via Σ-type closure.
-- Translated from Part07.agda (which contains the full development
-- but doesn't compile standalone due to import issues).

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (transportTransport⁻)

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; isSetBool)

open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
open import Cubical.HITs.SequentialColimit.Properties
  using (converges→ColimIso; SeqColim→Prop)
open import Cubical.Data.Sequence using (Sequence; converges)

open import Cubical.Data.FinSet using (isFinSet)
open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
open import Cubical.Data.FinSet.Properties using (isFinSetBool; EquivPresIsFinSet)
open import Cubical.Data.FinSet.Constructors using (isFinSetΣ)

open Sequence

-- ════════════════════════════════════════════════════════════════
-- Definition: overtly discrete = sequential colimit of finite sets
-- ════════════════════════════════════════════════════════════════

isODisc : Type ℓ-zero → Type (ℓ-suc ℓ-zero)
isODisc A = ∥ Σ[ S ∈ Sequence ℓ-zero ]
              ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A) ∥₁

isProp-isODisc : (X : Type ℓ-zero) → isProp (isODisc X)
isProp-isODisc _ = squash₁

-- ════════════════════════════════════════════════════════════════
-- Basic results (from Part07)
-- ════════════════════════════════════════════════════════════════

-- Finite sets are ODisc (constant sequence)
ODiscFinSet : {A : Type ℓ-zero} → isFinSet A → isODisc A
ODiscFinSet {A} finA = ∣ S , (λ _ → finA) ,
  isoToEquiv (invIso (converges→ColimIso {seq = S} 0 (λ _ → idIsEquiv A))) ∣₁ where
  S : Sequence ℓ-zero
  obj S _ = A
  map S x = x

-- Transfer along equivalence
isODisc-equiv : {A B : Type ℓ-zero} → A ≃ B → isODisc A → isODisc B
isODisc-equiv e = PT.map λ (S , finS , eA) → S , finS , compEquiv eA e

-- Sequential colimits of sets are sets (encode-decode, from Part07 SCSet module)
-- This is a significant result (~120 lines in Part07). We postulate it here.
postulate
  isSetSeqColimOfSets : (S' : Sequence ℓ-zero)
    → ((n : ℕ) → isSet (obj S' n)) → isSet (SeqColim S')

-- ODisc types are sets
isODiscIsSet : {A : Type ℓ-zero} → isODisc A → isSet A
isODiscIsSet = PT.rec isPropIsSet λ (S' , finS , equiv) →
  isOfHLevelRespectEquiv 2 equiv
    (isSetSeqColimOfSets S' (λ n → isFinSet→isSet (finS n)))

-- ════════════════════════════════════════════════════════════════
-- Finite Σ with ODisc fibers → ODisc (uses finite choice)
-- ════════════════════════════════════════════════════════════════

-- Finite choice: from a finite set A and a family of truncated types,
-- extract a family of witnesses (because finite sets have choice).
open import Cubical.Data.FinSet.FiniteChoice using (choice)

finΣ-ODisc : {A : Type ℓ-zero} {B : A → Type ℓ-zero}
  → isFinSet A → ((a : A) → isODisc (B a)) → isODisc (Σ A B)
finΣ-ODisc {A} {B} finA odiscB = PT.rec squash₁ go (choice (_ , finA) _ odiscB) where
  go : ((a : A) → Σ[ S ∈ Sequence ℓ-zero ]
    ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ B a)) → isODisc (Σ A B)
  go wit = ∣ ΣSeq , finΣ , compEquiv colimEquiv (Σ-cong-equiv-snd eT) ∣₁ where
    T : A → Sequence ℓ-zero
    T a = fst (wit a)
    finT : (a : A) (n : ℕ) → isFinSet (obj (T a) n)
    finT a = fst (snd (wit a))
    eT : (a : A) → SeqColim (T a) ≃ B a
    eT a = snd (snd (wit a))
    ΣSeq : Sequence ℓ-zero
    obj ΣSeq n = Σ A (λ a → obj (T a) n)
    map ΣSeq (a , x) = a , map (T a) x
    finΣ : (n : ℕ) → isFinSet (obj ΣSeq n)
    finΣ n = isFinSetΣ (_ , finA) (λ a → _ , finT a n)
    -- SeqColim ΣSeq ≃ Σ A (λ a → SeqColim (T a))
    -- This is the "non-dependent" sigma-colimit equivalence
    -- (base A is discrete/finite, not a colimit)
    fwd : SeqColim ΣSeq → Σ A (λ a → SeqColim (T a))
    fwd (incl (a , x)) = a , incl x
    fwd (push (a , x) i) = a , push x i
    bwd : Σ A (λ a → SeqColim (T a)) → SeqColim ΣSeq
    bwd (a , incl x) = incl (a , x)
    bwd (a , push x i) = push (a , x) i
    colimEquiv : SeqColim ΣSeq ≃ Σ A (λ a → SeqColim (T a))
    colimEquiv = isoToEquiv (iso fwd bwd
      (λ { (a , incl x) → refl ; (a , push x i) → refl })
      (λ { (incl _) → refl ; (push _ _) → refl }))

-- ════════════════════════════════════════════════════════════════
-- ODiscColimOfODisc: SeqColim of ODisc types is ODisc
-- This is the deepest result (~150 lines in Part07, using diagonal
-- construction and dependent choice). We postulate it here.
-- ════════════════════════════════════════════════════════════════

postulate
  ODiscColimOfODisc : (S₀ : Sequence ℓ-zero)
    → ((n : ℕ) → isODisc (obj S₀ n)) → isODisc (SeqColim S₀)

-- ════════════════════════════════════════════════════════════════
-- Σ-type closure: ODisc base + ODisc fibers → ODisc total space
-- (Translated from Part07 OdiscSigma)
-- ════════════════════════════════════════════════════════════════

OdiscSigma : {A : Type ℓ-zero} {B : A → Type ℓ-zero}
  → isODisc A → ((a : A) → isODisc (B a)) → isODisc (Σ A B)
OdiscSigma {A} {B} odiscA odiscB = PT.rec squash₁ go odiscA where
  go : Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A)
     → isODisc (Σ A B)
  go (SA , finSA , eA) = isODisc-equiv Σ-total-equiv sigmaODisc where
    B' : SeqColim SA → Type ℓ-zero
    B' c = B (equivFun eA c)

    ΣSA : Sequence ℓ-zero
    obj ΣSA n = Σ (obj SA n) (λ x → B' (incl x))
    map ΣSA (x , b) = map SA x , subst B' (push x) b

    -- Each level of ΣSA is ODisc: finite base × ODisc fiber
    levelODisc : (n : ℕ) → isODisc (obj ΣSA n)
    levelODisc n = finΣ-ODisc (finSA n) (λ x → odiscB (equivFun eA (incl x)))

    -- SeqColim of ODisc levels is ODisc
    sigmaODisc : isODisc (SeqColim ΣSA)
    sigmaODisc = ODiscColimOfODisc ΣSA levelODisc

    -- SeqColim ΣSA ≃ Σ (SeqColim SA) B' ≃ Σ A B
    isSetSA : isSet (SeqColim SA)
    isSetSA = isSetSeqColimOfSets SA (λ n → isFinSet→isSet (finSA n))

    isSetB' : (c : SeqColim SA) → isSet (B' c)
    isSetB' c = isODiscIsSet (odiscB (equivFun eA c))

    -- Forward: SeqColim ΣSA → Σ (SeqColim SA) B'
    fwd : SeqColim ΣSA → Σ (SeqColim SA) B'
    fwd (incl (x , b)) = incl x , b
    fwd (push (x , b) i) = push x i , subst-filler B' (push x) b i

    -- Backward: Σ (SeqColim SA) B' → SeqColim ΣSA
    bwd : Σ (SeqColim SA) B' → SeqColim ΣSA
    bwd (incl x , b) = incl (x , b)
    bwd (push {n = n} x i , b) =
      hcomp (λ j → λ { (i = i0) → incl {n = n} (x , b)
                      ; (i = i1) → incl {n = suc n} (map SA x ,
                          transportTransport⁻ (cong B' (push x)) b j) })
            (push {n = n} (x , b₀) i)
      where
        b₀ : B' (incl x)
        b₀ = transp (λ j → B' (push x (i ∧ ~ j))) (~ i) b

    isSetTarget : isSet (Σ (SeqColim SA) B')
    isSetTarget = isSetΣ isSetSA isSetB'

    isSetΣSAColim : isSet (SeqColim ΣSA)
    isSetΣSAColim = isSetSeqColimOfSets ΣSA (λ n →
      isSetΣ (isFinSet→isSet (finSA n))
             (λ x → isODiscIsSet (odiscB (equivFun eA (incl x)))))

    sec : (p : Σ (SeqColim SA) B') → fwd (bwd p) ≡ p
    sec (incl x , b) = refl
    sec (push {n = n} x i , b) = lemma i b where
      lemma : PathP (λ i → (b : B' (push x i)) → fwd (bwd (push x i , b)) ≡ (push x i , b))
                    (λ b → refl) (λ b → refl)
      lemma = isProp→PathP
        (λ j → isPropΠ (λ b → isSetTarget (fwd (bwd (push x j , b))) (push x j , b)))
        (λ b → refl) (λ b → refl)

    ret : (c : SeqColim ΣSA) → bwd (fwd c) ≡ c
    ret (incl _) = refl
    ret (push {n = n} (x , b) i) =
      isProp→PathP (λ j → isSetΣSAColim (bwd (fwd (push (x , b) j))) (push (x , b) j))
        refl refl i

    Σ-colim-equiv : SeqColim ΣSA ≃ Σ (SeqColim SA) B'
    Σ-colim-equiv = isoToEquiv (iso fwd bwd sec ret)

    Σ-total-equiv : SeqColim ΣSA ≃ Σ A B
    Σ-total-equiv = compEquiv Σ-colim-equiv (Σ-cong-equiv-fst eA)

-- ════════════════════════════════════════════════════════════════
-- Product closure: immediate from OdiscSigma
-- ════════════════════════════════════════════════════════════════

isODisc-× : {X Y : Type ℓ-zero} → isODisc X → isODisc Y → isODisc (X × Y)
isODisc-× odX odY = OdiscSigma odX (λ _ → odY)
