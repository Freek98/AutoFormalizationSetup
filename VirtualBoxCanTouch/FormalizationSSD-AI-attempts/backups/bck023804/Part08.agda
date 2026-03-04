{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)

module work.Part08 (fa : FoundationalAxioms) where

open import work.Part07 fa public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Transport using (transport⁻; transportTransport⁻)
open import Cubical.Foundations.Isomorphism using (isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq; equivToIso)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing using (CommRingHom; IsCommRingHom; _$cr_; CommRingHom≡; _∘cr_)
open import Axioms.StoneDuality using (Booleω; Sp)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; has-Boole-ω'; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom; invBooleanRingEquiv)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property)
import QuotientBool as QB

module StoneEqualityClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)

  hasStoneStr→isSet : (S : Stone) → isSet (fst S)
  hasStoneStr→isSet (X , B , SpB≡X) = subst isSet SpB≡X (isSetBoolHom (fst B) BoolBR)

  SpEqualityClosed-from-presentation : (B : BooleanRing ℓ-zero)
    → (pres : has-Boole-ω' B)
    → (s t : Sp (B , ∣ pres ∣₁))
    → isClosedProp ((s ≡ t) , isSetBoolHom B BoolBR s t)
  SpEqualityClosed-from-presentation B (f , equiv) s t = PT.rec squash₁ go ∀P-closed
    where
    Q : BooleanRing ℓ-zero
    Q = freeBA ℕ QB./Im f

    presEquiv : ⟨ B ⟩ ≃ ⟨ Q ⟩
    presEquiv = fst equiv

    presEquiv-hom : BoolHom B Q
    presEquiv-hom = (fst presEquiv) , snd equiv

    presEquiv⁻¹ : ⟨ Q ⟩ → ⟨ B ⟩
    presEquiv⁻¹ = invEq presEquiv

    π : BoolHom (freeBA ℕ) Q
    π = QB.quotientImageHom

    gen-in-B : ℕ → ⟨ B ⟩
    gen-in-B n = presEquiv⁻¹ (fst π (generator n))

    P : ℕ → hProp ℓ-zero
    P n = (s $cr (gen-in-B n) ≡ t $cr (gen-in-B n)) , isSetBool _ _

    P-closed : (n : ℕ) → isClosedProp (P n)
    P-closed n = Bool-equality-closed (s $cr (gen-in-B n)) (t $cr (gen-in-B n))

    ∀P-closed : isClosedProp (((n : ℕ) → fst (P n)) , isPropΠ (λ n → snd (P n)))
    ∀P-closed = closedCountableIntersection P P-closed

    agree-forward : s ≡ t → (n : ℕ) → fst (P n)
    agree-forward s=t n = cong (λ h → h $cr (gen-in-B n)) s=t

    presEquiv⁻¹-hom : BoolHom Q B
    presEquiv⁻¹-hom = BooleanEquivToHomInv B Q equiv

    s-on-free : BoolHom (freeBA ℕ) BoolBR
    s-on-free = s ∘cr presEquiv⁻¹-hom ∘cr π

    t-on-free : BoolHom (freeBA ℕ) BoolBR
    t-on-free = t ∘cr presEquiv⁻¹-hom ∘cr π

    s-on-free=t-on-free : ((n : ℕ) → fst (P n)) → s-on-free ≡ t-on-free
    s-on-free=t-on-free allP = let FUP = freeBA-universal-property ℕ BoolBR in
      s-on-free
        ≡⟨ sym (Iso.sec FUP s-on-free) ⟩
      Iso.fun FUP (Iso.inv FUP s-on-free)
        ≡⟨ cong (Iso.fun FUP) (funExt allP) ⟩
      Iso.fun FUP (Iso.inv FUP t-on-free)
        ≡⟨ Iso.sec FUP t-on-free ⟩
      t-on-free ∎

    s-on-Q : BoolHom Q BoolBR
    s-on-Q = s ∘cr presEquiv⁻¹-hom

    t-on-Q : BoolHom Q BoolBR
    t-on-Q = t ∘cr presEquiv⁻¹-hom

    s-on-Q=t-on-Q : ((n : ℕ) → fst (P n)) → s-on-Q ≡ t-on-Q
    s-on-Q=t-on-Q allP = CommRingHom≡
      (QB.quotientImageHomEpi (Bool , isSetBool) (cong fst (s-on-free=t-on-free allP)))

    leftInv : presEquiv⁻¹-hom ∘cr presEquiv-hom ≡ idBoolHom B
    leftInv = BooleanEquivLeftInv B Q equiv

    ∀P→s=t : ((n : ℕ) → fst (P n)) → s ≡ t
    ∀P→s=t allP =
      s
        ≡⟨ CommRingHom≡ (funExt (λ _ → refl)) ⟩
      s ∘cr idBoolHom B
        ≡⟨ cong (s ∘cr_) (sym leftInv) ⟩
      s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)
        ≡⟨ CommRingHom≡ (funExt (λ _ → refl)) ⟩
      s-on-Q ∘cr presEquiv-hom
        ≡⟨ cong (_∘cr presEquiv-hom) (s-on-Q=t-on-Q allP) ⟩
      t-on-Q ∘cr presEquiv-hom
        ≡⟨ CommRingHom≡ (funExt (λ _ → refl)) ⟩
      t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)
        ≡⟨ cong (t ∘cr_) leftInv ⟩
      t ∘cr idBoolHom B
        ≡⟨ sym (CommRingHom≡ (funExt (λ _ → refl))) ⟩
      t ∎

    go : Σ[ β ∈ binarySequence ] ((n : ℕ) → fst (P n)) ↔ ((k : ℕ) → β k ≡ false)
       → isClosedProp ((s ≡ t) , isSetBoolHom B BoolBR s t)
    go (β , allP→βFalse , βFalse→allP) = ∣ β , s=t→βFalse , βFalse→s=t ∣₁
      where
      s=t→βFalse : s ≡ t → (k : ℕ) → β k ≡ false
      s=t→βFalse s=t = allP→βFalse (agree-forward s=t)

      βFalse→s=t : ((k : ℕ) → β k ≡ false) → s ≡ t
      βFalse→s=t h = ∀P→s=t (βFalse→allP h)

  SpEqualityClosed : (B : Booleω) → (s t : Sp B)
    → isClosedProp ((s ≡ t) , isSetBoolHom (fst B) BoolBR s t)
  SpEqualityClosed (B , presB) s t = PT.rec (isPropIsClosedProp {(s ≡ t) , isSetBoolHom B BoolBR s t})
    (λ pres → SpEqualityClosed-from-presentation B pres s t)
    presB

  -- tex Lemma 1636 (StoneEqualityClosed)
  StoneEqualityClosed : (S : Stone) → (s t : fst S)
    → isClosedProp ((s ≡ t) , hasStoneStr→isSet S s t)
  StoneEqualityClosed (X , B , path) s t = closedEquiv
    ((s' ≡ t') , isSetBoolHom (fst B) BoolBR s' t')
    ((s ≡ t) , hasStoneStr→isSet (X , B , path) s t)
    forward backward (SpEqualityClosed B s' t')
    where
    s' : Sp B
    s' = transport⁻ path s

    t' : Sp B
    t' = transport⁻ path t

    forward : (s' ≡ t') → (s ≡ t)
    forward s'=t' =
      s                                 ≡⟨ sym (transportTransport⁻ path s) ⟩
      transport path (transport⁻ path s)  ≡⟨ cong (transport path) s'=t' ⟩
      transport path (transport⁻ path t)  ≡⟨ transportTransport⁻ path t ⟩
      t ∎

    backward : (s ≡ t) → (s' ≡ t')
    backward s=t = cong (transport⁻ path) s=t

-- StoneClosedSubsets (tex Theorem 1648)

module StoneClosedSubsetsModule where

  module SpOfQuotientBySeq (B : BooleanRing ℓ-zero) (d : ℕ → ⟨ B ⟩) where
    B/d : BooleanRing ℓ-zero
    B/d = B QB./Im d

    π : BoolHom B B/d
    π = QB.quotientImageHom

    ClosedSubset : Type ℓ-zero
    ClosedSubset = Σ[ x ∈ BoolHom B BoolBR ] ((n : ℕ) → fst x (d n) ≡ false)

    Sp-quotient→ClosedSubset : BoolHom B/d BoolBR → ClosedSubset
    Sp-quotient→ClosedSubset h = h ∘cr π , λ n →
        fst h (fst π (d n))     ≡⟨ cong (fst h) (QB.zeroOnImage {B = B} {f = d} n) ⟩
        fst h (BooleanRingStr.𝟘 (snd B/d))  ≡⟨ IsCommRingHom.pres0 (snd h) ⟩
        false ∎

    ClosedSubset→Sp-quotient : ClosedSubset → BoolHom B/d BoolBR
    ClosedSubset→Sp-quotient (x , allZero) = QB.inducedHom {B = B} {f = d} BoolBR x allZero

    forward∘backward : (cs : ClosedSubset) → Sp-quotient→ClosedSubset (ClosedSubset→Sp-quotient cs) ≡ cs
    forward∘backward (x , allZero) = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetBool _ _))
      (QB.evalInduce {B = B} {f = d} BoolBR)

    backward∘forward : (h : BoolHom B/d BoolBR) → ClosedSubset→Sp-quotient (Sp-quotient→ClosedSubset h) ≡ h
    backward∘forward h = QB.inducedHomUnique BoolBR (h ∘cr π) (snd (Sp-quotient→ClosedSubset h)) h refl

    Sp-quotient-Iso : Iso (BoolHom B/d BoolBR) ClosedSubset
    Iso.fun Sp-quotient-Iso = Sp-quotient→ClosedSubset
    Iso.inv Sp-quotient-Iso = ClosedSubset→Sp-quotient
    Iso.sec Sp-quotient-Iso = forward∘backward
    Iso.ret Sp-quotient-Iso = backward∘forward

    Sp-quotient-≃ : BoolHom B/d BoolBR ≃ ClosedSubset
    Sp-quotient-≃ = isoToEquiv Sp-quotient-Iso

  quotientBySeqPreservesBooleω : (B : Booleω) (d : ℕ → ⟨ fst B ⟩)
    → ∥ Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))) ∥₁
  quotientBySeqPreservesBooleω B d = PT.map wrap (quotientBySeqHasBooleω B d)
    where
    wrap : has-Boole-ω' (fst B QB./Im d)
         → Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
    wrap pres = (fst B QB./Im d , ∣ pres ∣₁) , SpOfQuotientBySeq.Sp-quotient-≃ (fst B) d

-- StoneSeparated (tex Lemma 1824)
