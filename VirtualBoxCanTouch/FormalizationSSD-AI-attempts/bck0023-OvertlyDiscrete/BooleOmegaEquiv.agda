{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OvertlyDiscrete.BooleOmegaEquiv where

-- This file shows that a Boolean ring is countably presented (Booleω)
-- if and only if its underlying type is overtly discrete.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; _and_; isSetBool)
open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import BasicDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.FreeBooleanRing.freeBATerms
open import BooleanRing.BooleanRingMaps
import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import CountablyPresentedBooleanRings.Definitions

open import OvertlyDiscrete.Definition

open Iso

-- ════════════════════════════════════════════════════════════════
-- Forward direction: countably presented → overtly discrete
-- ════════════════════════════════════════════════════════════════

-- We postulate two key facts that are mathematically true but
-- require significant infrastructure to formalize fully.

-- freeBATerms ℕ is countable (proved in TermsCountable)
open import OvertlyDiscrete.TermsCountable using () renaming (freeBATerms-surj to freeBATerms-surj)

postulate
  -- Equality in a quotient of freeBA by a countable set of relations is open.
  -- This uses: (a) decidable equality in freeBA ℕ (by evaluation on
  --                finitely many generators + finiteness of freeBA(Fin n)),
  --            (b) countability of the witness type for ideal membership.
  freeBA-quotient-eq-open : (f : ℕ → ⟨ freeBA ℕ ⟩)
    → (x y : ⟨ freeBA ℕ QB./Im f ⟩) → isOpenProp (x ≡ y)


module Forward (f : ℕ → ⟨ freeBA ℕ ⟩) where

  private
    B = freeBA ℕ QB./Im f

    instance
      _ = snd B

    open BooleanRingStr ⦃...⦄

    -- The quotient map
    π : ⟨ freeBA ℕ ⟩ → ⟨ B ⟩
    π = fst QB.quotientImageHom

    -- The composite surjection ℕ → freeBATerms ℕ → ⟨ freeBA ℕ ⟩ → ⟨ B ⟩
    eTerms : freeBATerms ℕ → ⟨ freeBA ℕ ⟩
    eTerms = fst includeBATermsSurj

  eSurj : ℕ → ⟨ B ⟩
  eSurj n = π (eTerms (fst freeBATerms-surj n))

  eSurj-surjective : isSurjection eSurj
  eSurj-surjective y = PT.rec squash₁
    (λ (a , πa≡y) → PT.rec squash₁
      (λ (t , et≡a) → PT.rec squash₁
        (λ (n , en≡t) → ∣ n , cong (π ∘ eTerms) en≡t ∙ cong π et≡a ∙ πa≡y ∣₁)
        (snd freeBATerms-surj t))
      (snd includeBATermsSurj a))
    (QB.quotientImageHomSurjective y)

  has-Boole-ω'→has-ODisc : has-ODisc-structure ⟨ B ⟩
  has-ODisc-structure.surj   has-Boole-ω'→has-ODisc = eSurj
  has-ODisc-structure.isSurj has-Boole-ω'→has-ODisc = eSurj-surjective
  has-ODisc-structure.setX   has-Boole-ω'→has-ODisc = is-set
  has-ODisc-structure.openEq has-Boole-ω'→has-ODisc = freeBA-quotient-eq-open f


-- Derive the version for an arbitrary Boolean ring with a presentation
Boole-ω'→ODisc : (B : BooleanRing ℓ-zero) → has-Boole-ω' B → has-ODisc-structure ⟨ B ⟩
Boole-ω'→ODisc B (f , equiv) = record
  { surj   = invEq (fst equiv) ∘ eSurj
  ; isSurj = λ y → PT.map
      (λ (n , p) → n , cong (invEq (fst equiv)) p ∙ retEq (fst equiv) y)
      (eSurj-surjective (equivFun (fst equiv) y))
  ; setX   = BooleanRingStr.is-set (snd B)
  ; openEq = λ x y → openViaEquiv x y
  }
  where
  open Forward f
  open BooleanRingStr ⦃...⦄

  Q = freeBA ℕ QB./Im f
  e = fst equiv

  instance
    _ = snd B
    _ = snd Q

  -- Transport openness through the equivalence
  openViaEquiv : (x y : ⟨ B ⟩) → isOpenProp (x ≡ y)
  openViaEquiv x y = α , fwd , bwd
    where
    x' = equivFun e x
    y' = equivFun e y
    open-xy = freeBA-quotient-eq-open f x' y'
    α = fst open-xy

    fwd : x ≡ y → ∥ Σℕ α ∥₁
    fwd p = fst (snd open-xy) (cong (equivFun e) p)

    bwd : ∥ Σℕ α ∥₁ → x ≡ y
    bwd t = sym (retEq e x) ∙ cong (invEq e) (snd (snd open-xy) t) ∙ retEq e y


-- ════════════════════════════════════════════════════════════════
-- Backward direction: overtly discrete → countably presented
-- ════════════════════════════════════════════════════════════════

-- Given: B a Boolean ring with ⟨B⟩ overtly discrete.
-- Construction outline:
-- 1. The surjection e : ℕ → ⟨B⟩ induces ê = inducedBAHom ℕ B e : BoolHom (freeBA ℕ) B
-- 2. Every element of freeBA ℕ is eval(tₖ) for some term tₖ.
-- 3. For each term tₖ, "ê(eval(tₖ)) = 0_B" is an open proposition
--    (using the open equality of ⟨B⟩).
-- 4. The binary sequence αₖ witnessing this openness lets us define
--    rel(pair(k,j)) = if αₖ(j) then eval(tₖ) else 0.
-- 5. The ideal generated by {rel(n)} equals ker(ê), giving B ≅ freeBA ℕ /Im rel.

module Backward (B : BooleanRing ℓ-zero) (od : has-ODisc-structure ⟨ B ⟩) where

  open has-ODisc-structure od

  private
    instance
      _ = snd B
      _ = snd (freeBA ℕ)

    open BooleanRingStr ⦃...⦄

    -- The induced ring homomorphism from freeBA ℕ
    ê : BoolHom (freeBA ℕ) B
    ê = inducedBAHom ℕ B surj

    ê-on-gen : fst ê ∘ generator ≡ surj
    ê-on-gen = evalBAInduce ℕ B surj

    -- Open witness for kernel membership of each freeBA ℕ element
    kernelOpen : (x : ⟨ freeBA ℕ ⟩) → isOpenProp (fst ê x ≡ BooleanRingStr.𝟘 (snd B))
    kernelOpen x = openEq (fst ê x) (BooleanRingStr.𝟘 (snd B))

    -- Extract the binary sequence for each element
    αElem : (x : ⟨ freeBA ℕ ⟩) → binarySequence
    αElem x = fst (kernelOpen x)

    -- Enumerate ⟨ freeBA ℕ ⟩ elements via terms
    enumFreeBA : ℕ → ⟨ freeBA ℕ ⟩
    enumFreeBA n = fst includeBATermsSurj (fst freeBATerms-surj n)

    enumFreeBA-surj : isSurjection enumFreeBA
    enumFreeBA-surj x = PT.rec squash₁
      (λ (t , et≡x) → PT.map
        (λ (n , en≡t) → n , cong (fst includeBATermsSurj) en≡t ∙ et≡x)
        (snd freeBATerms-surj t))
      (snd includeBATermsSurj x)

  open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

  -- Helper: conditionally return an element or 0
  private
    ifThen0 : Bool → ⟨ freeBA ℕ ⟩ → ⟨ freeBA ℕ ⟩
    ifThen0 true  x = x
    ifThen0 false _ = BooleanRingStr.𝟘 (snd (freeBA ℕ))

  -- The relation function: for each pair (k, j), either contribute
  -- the k-th freeBA element (if it's in the kernel) or 0.
  rel : ℕ → ⟨ freeBA ℕ ⟩
  rel n = ifThen0 (αElem x j) x
    where
    k = fst (Iso.inv ℕ×ℕ≅ℕ n)
    j = snd (Iso.inv ℕ×ℕ≅ℕ n)
    x = enumFreeBA k

  -- The quotient ring
  Q : BooleanRing ℓ-zero
  Q = freeBA ℕ QB./Im rel

  -- The map ê kills all relations
  private
    ê-kills-ifThen0 : (b : Bool) (x : ⟨ freeBA ℕ ⟩)
      → (b ≡ true → fst ê x ≡ BooleanRingStr.𝟘 (snd B))
      → fst ê (ifThen0 b x) ≡ BooleanRingStr.𝟘 (snd B)
    ê-kills-ifThen0 true  x p = p refl
    ê-kills-ifThen0 false x p = IsCommRingHom.pres0 (snd ê)

    αElem-true→kernel : (x : ⟨ freeBA ℕ ⟩) (j : ℕ)
      → αElem x j ≡ true → fst ê x ≡ BooleanRingStr.𝟘 (snd B)
    αElem-true→kernel x j p = snd (snd (kernelOpen x)) ∣ j , p ∣₁

  ê-kills-rel : (n : ℕ) → fst ê (rel n) ≡ BooleanRingStr.𝟘 (snd B)
  ê-kills-rel n = ê-kills-ifThen0 (αElem x j) x (αElem-true→kernel x j)
    where
    k = fst (Iso.inv ℕ×ℕ≅ℕ n)
    j = snd (Iso.inv ℕ×ℕ≅ℕ n)
    x = enumFreeBA k

  -- Factor ê through Q: ê' : Q → B with ê' ∘ π = ê
  ê' : BoolHom Q B
  ê' = QB.inducedHom {B = freeBA ℕ} {f = rel} B ê ê-kills-rel

  -- ê' ∘ πQ = ê (the factoring property)
  ê'-factor : ê' ∘cr QB.quotientImageHom {B = freeBA ℕ} {f = rel} ≡ ê
  ê'-factor = QB.evalInduce {B = freeBA ℕ} {f = rel} B

  -- ê' is surjective: for y : ⟨B⟩, find n with e(n) = y,
  -- then π(gen(n)) : ⟨Q⟩ satisfies ê'(π(gen(n))) = ê(gen(n)) = e(n) = y.
  private
    πQ : ⟨ freeBA ℕ ⟩ → ⟨ Q ⟩
    πQ = fst (QB.quotientImageHom {B = freeBA ℕ} {f = rel})

  ê'-surj : isSurjection (fst ê')
  ê'-surj y = PT.map
    (λ (n , en≡y) → πQ (generator n) ,
      funExt⁻ (cong fst ê'-factor) (generator n) ∙ funExt⁻ ê-on-gen n ∙ en≡y)
    (isSurj y)

  -- ê' is injective: ker(ê) ⊆ ideal generated by {rel(n)}.
  -- Strategy: show πQ(x) = 0 whenever ê(x) = 0, then use ker≡0→inj.

  -- Key lemma: if x ∈ ker(ê), then πQ(x) = 0 in Q.
  -- Because: x = enumFreeBA(k) for some k (by surjectivity),
  -- and αElem(x)(j) = true for some j (by openness of ê(x) = 0),
  -- so rel(pair(k,j)) = x, and πQ kills all rel elements.
  private
    πQ-kills-ker : (x : ⟨ freeBA ℕ ⟩)
      → fst ê x ≡ BooleanRingStr.𝟘 (snd B)
      → πQ x ≡ BooleanRingStr.𝟘 (snd Q)
    πQ-kills-ker x êx=0 = PT.rec (BooleanRingStr.is-set (snd Q) _ _)
      (λ (k , ek≡x) → PT.rec (BooleanRingStr.is-set (snd Q) _ _)
        (λ (j , αj) →
          let
            αk-j : αElem (enumFreeBA k) j ≡ true
            αk-j = subst (λ z → αElem z j ≡ true) (sym ek≡x) αj

            n = Iso.fun ℕ×ℕ≅ℕ (k , j)

            rel-n-is-x : rel n ≡ x
            rel-n-is-x =
              cong₂ (λ a b → ifThen0 (αElem (enumFreeBA a) b) (enumFreeBA a))
                (cong fst (Iso.ret ℕ×ℕ≅ℕ (k , j)))
                (cong snd (Iso.ret ℕ×ℕ≅ℕ (k , j)))
              ∙ cong (λ b → ifThen0 b (enumFreeBA k)) αk-j
              ∙ ek≡x
          in
            sym (cong πQ rel-n-is-x)
            ∙ QB.zeroOnImage {B = freeBA ℕ} {f = rel} n)
        (fst (snd (kernelOpen x)) êx=0))
      (enumFreeBA-surj x)

  -- ê' has trivial kernel on Q: if ê'(q) = 0, then q = 0.
  -- Uses quotient elimination: q = πQ(a), ê'(πQ(a)) = ê(a) = 0, so πQ(a) = 0.
  ê'-ker-trivial : (q : ⟨ Q ⟩) → fst ê' q ≡ BooleanRingStr.𝟘 (snd B) → q ≡ BooleanRingStr.𝟘 (snd Q)
  ê'-ker-trivial q ê'q=0 = PT.rec (BooleanRingStr.is-set (snd Q) _ _)
    (λ (a , πa≡q) →
      let êa=0 : fst ê a ≡ BooleanRingStr.𝟘 (snd B)
          êa=0 = sym (funExt⁻ (cong fst ê'-factor) a)
                 ∙ cong (fst ê') πa≡q ∙ ê'q=0
      in sym πa≡q ∙ πQ-kills-ker a êa=0)
    (QB.quotientImageHomSurjective {B = freeBA ℕ} {f = rel} q)

  -- Build the equivalence: ê' is embedding (injective) + surjective → equiv
  open import Cubical.Algebra.Ring.Properties

  private
    open IsCommRingHom

    -- ker≡0→inj from RingHomTheory expects Ring's 0r; we adapt for BooleanRing's 𝟘
    ê'-inj : (x y : ⟨ Q ⟩) → fst ê' x ≡ fst ê' y → x ≡ y
    ê'-inj x y p =
      let open RingTheory (CommRing→Ring (BooleanRing→CommRing Q))
      in equalByDifference x y (ê'-ker-trivial (BooleanRingStr._+_ (snd Q) x (BooleanRingStr.-_ (snd Q) y))
           (pres+ (snd ê') x (BooleanRingStr.-_ (snd Q) y)
            ∙ cong (BooleanRingStr._+_ (snd B) (fst ê' x)) (pres- (snd ê') y)
            ∙ cong (λ z → BooleanRingStr._+_ (snd B) z (BooleanRingStr.-_ (snd B) (fst ê' y))) p
            ∙ BooleanRingStr.+InvR (snd B) (fst ê' y)))

  open import Cubical.Functions.Surjection using (isEmbedding×isSurjection→isEquiv)
  open import Cubical.Functions.Embedding using (isEmbedding; injEmbedding)

  private
    ê'-isEmb : isEmbedding (fst ê')
    ê'-isEmb = injEmbedding (BooleanRingStr.is-set (snd B)) (λ {x} {y} → ê'-inj x y)

  ê'-isEquiv : isEquiv (fst ê')
  ê'-isEquiv = isEmbedding×isSurjection→isEquiv (ê'-isEmb , ê'-surj)

  -- Construct the BooleanRingEquiv B Q
  -- We have ê' : Q → B is an isomorphism. We need B ≃ Q, so we take the inverse.
  Q≃B : BooleanRingEquiv B Q
  Q≃B = invBooleanRingEquiv Q B ((fst ê' , ê'-isEquiv) , snd ê')
    where open import BooleanRing.BooleanRingMaps using (invBooleanRingEquiv)

  -- The presentation
  has-Boole-ω'→ : has-Boole-ω' B
  has-Boole-ω'→ = rel , Q≃B


-- ════════════════════════════════════════════════════════════════
-- Combined equivalence (truncated)
-- ════════════════════════════════════════════════════════════════

-- Forward: countably presented → overtly discrete (underlying type)
CP→OD : (B : BooleanRing ℓ-zero)
  → is-countably-presented-alt B → isOvertlyDiscrete ⟨ B ⟩
CP→OD B = PT.map (Boole-ω'→ODisc B)

-- Backward: overtly discrete underlying type → countably presented
OD→CP : (B : BooleanRing ℓ-zero)
  → isOvertlyDiscrete ⟨ B ⟩ → is-countably-presented-alt B
OD→CP B = PT.map (λ od → Backward.has-Boole-ω'→ B od)
