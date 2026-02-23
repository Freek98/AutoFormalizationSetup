{-# OPTIONS --cubical --guardedness #-}

module SSD.StoneDuality.StoneEqualityClosed where

open import SSD.StoneDuality.ClosedPropSpectrum public

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
open import SSD.Library.StoneDuality using (Booleω; Sp)
open import SSD.Library.PresentedBoole using (BooleanRingEquiv; has-Boole-ω'; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom; invBooleanRingEquiv)
open import SSD.Library.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property)
import SSD.Library.QuotientBool as QB

module WithAxiomsSEC (axioms : Axioms) where
  open WithAxioms axioms
  open OpenClosedProperties axioms
  open WithAxiomsCPS axioms

  module StoneEqualityClosedModule where
    open import SSD.Library.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)

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

    quotientBySeqHasBooleω : (B : Booleω) (d : ℕ → ⟨ fst B ⟩)
      → ∥ has-Boole-ω' (fst B QB./Im d) ∥₁
    quotientBySeqHasBooleω B d = PT.rec squash₁ construct (snd B)
      where
      construct : has-Boole-ω' (fst B) → ∥ has-Boole-ω' (fst B QB./Im d) ∥₁
      construct (f , equiv) = PT.rec squash₁ (λ lifts → ∣ constructFromLifts lifts ∣₁)
          (countableChoice LiftType (λ n → QB.quotientImageHomSurjective (d' n)))
        where
        open SpOfQuotientBySeq (fst B) d

        d' : ℕ → ⟨ freeBA ℕ QB./Im f ⟩
        d' n = fst (fst equiv) (d n)

        LiftType : ℕ → Type ℓ-zero
        LiftType n = Σ[ x ∈ ⟨ freeBA ℕ ⟩ ] fst QB.quotientImageHom x ≡ d' n

        constructFromLifts : ((n : ℕ) → LiftType n) → has-Boole-ω' B/d
        constructFromLifts lifts = h , B/d-equiv
          where
          g : ℕ → ⟨ freeBA ℕ ⟩
          g n = fst (lifts n)

          g-is-section : (n : ℕ) → fst QB.quotientImageHom (g n) ≡ d' n
          g-is-section n = snd (lifts n)

          encode : ℕ ⊎ ℕ → ℕ
          encode = Iso.fun ℕ⊎ℕ≅ℕ

          decode : ℕ → ℕ ⊎ ℕ
          decode = Iso.inv ℕ⊎ℕ≅ℕ

          h : ℕ → ⟨ freeBA ℕ ⟩
          h n with decode n
          ... | inl m = f m
          ... | inr m = g m

          step2-equiv : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g))
                                         ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
          step2-equiv = commRingPath→boolRingEquiv
                          (freeBA ℕ QB./Im (⊎.rec f g))
                          ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
                          (BoolQuotientEquiv (freeBA ℕ) f g)

          h≡rec∘decode-pointwise : (n : ℕ) → h n ≡ ⊎.rec f g (decode n)
          h≡rec∘decode-pointwise n with decode n
          ... | inl m = refl
          ... | inr m = refl

          rec-quotient : BooleanRing ℓ-zero
          rec-quotient = freeBA ℕ QB./Im (⊎.rec f g)

          h-quotient : BooleanRing ℓ-zero
          h-quotient = freeBA ℕ QB./Im h

          π-rec : BoolHom (freeBA ℕ) rec-quotient
          π-rec = QB.quotientImageHom

          π-h : BoolHom (freeBA ℕ) h-quotient
          π-h = QB.quotientImageHom

          π-rec-sends-h-to-0 : (n : ℕ) → π-rec $cr (h n) ≡ BooleanRingStr.𝟘 (snd rec-quotient)
          π-rec-sends-h-to-0 n =
            π-rec $cr (h n)
              ≡⟨ cong (π-rec $cr_) (h≡rec∘decode-pointwise n) ⟩
            π-rec $cr ((⊎.rec f g) (decode n))
              ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = ⊎.rec f g} (decode n) ⟩
            BooleanRingStr.𝟘 (snd rec-quotient) ∎

          step3-forward-hom : BoolHom h-quotient rec-quotient
          step3-forward-hom = QB.inducedHom {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

          rec-eq-h-encode : (x : ℕ ⊎ ℕ) → (⊎.rec f g) x ≡ h (encode x)
          rec-eq-h-encode x =
            (⊎.rec f g) x
              ≡⟨ cong (⊎.rec f g) (sym (Iso.ret ℕ⊎ℕ≅ℕ x)) ⟩
            (⊎.rec f g) (decode (encode x))
              ≡⟨ sym (h≡rec∘decode-pointwise (encode x)) ⟩
            h (encode x) ∎

          π-h-sends-rec-to-0 : (x : ℕ ⊎ ℕ) → π-h $cr ((⊎.rec f g) x) ≡ BooleanRingStr.𝟘 (snd h-quotient)
          π-h-sends-rec-to-0 x =
            π-h $cr ((⊎.rec f g) x)
              ≡⟨ cong (π-h $cr_) (rec-eq-h-encode x) ⟩
            π-h $cr (h (encode x))
              ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = h} (encode x) ⟩
            BooleanRingStr.𝟘 (snd h-quotient) ∎

          step3-backward-hom : BoolHom rec-quotient h-quotient
          step3-backward-hom = QB.inducedHom {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient π-h π-h-sends-rec-to-0

          step3-forward : ⟨ h-quotient ⟩ → ⟨ rec-quotient ⟩
          step3-forward = fst step3-forward-hom

          step3-backward : ⟨ rec-quotient ⟩ → ⟨ h-quotient ⟩
          step3-backward = fst step3-backward-hom

          step3-forward-eval : step3-forward-hom ∘cr π-h ≡ π-rec
          step3-forward-eval = QB.evalInduce {B = freeBA ℕ} {f = h} rec-quotient

          step3-backward-eval : step3-backward-hom ∘cr π-rec ≡ π-h
          step3-backward-eval = QB.evalInduce {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient

          step3-backward∘forward-on-π : (x : ⟨ freeBA ℕ ⟩) → step3-backward (step3-forward (fst π-h x)) ≡ fst π-h x
          step3-backward∘forward-on-π x =
            step3-backward (step3-forward (fst π-h x))
              ≡⟨ cong step3-backward (cong (λ hom → fst hom x) step3-forward-eval) ⟩
            step3-backward (fst π-rec x)
              ≡⟨ cong (λ hom → fst hom x) step3-backward-eval ⟩
            fst π-h x ∎

          step3-forward∘backward-on-π : (y : ⟨ freeBA ℕ ⟩) → step3-forward (step3-backward (fst π-rec y)) ≡ fst π-rec y
          step3-forward∘backward-on-π y =
            step3-forward (step3-backward (fst π-rec y))
              ≡⟨ cong step3-forward (cong (λ hom → fst hom y) step3-backward-eval) ⟩
            step3-forward (fst π-h y)
              ≡⟨ cong (λ hom → fst hom y) step3-forward-eval ⟩
            fst π-rec y ∎

          step3-iso : Iso ⟨ h-quotient ⟩ ⟨ rec-quotient ⟩
          Iso.fun step3-iso = step3-forward
          Iso.inv step3-iso = step3-backward
          Iso.sec step3-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = ⊎.rec f g}
            (⟨ rec-quotient ⟩ , BooleanRingStr.is-set (snd rec-quotient)) (funExt step3-forward∘backward-on-π))
          Iso.ret step3-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = h}
            (⟨ h-quotient ⟩ , BooleanRingStr.is-set (snd h-quotient)) (funExt step3-backward∘forward-on-π))

          step3-equiv' : BooleanRingEquiv h-quotient rec-quotient
          step3-equiv' = isoToEquiv step3-iso , snd step3-forward-hom

          target-ring : BooleanRing ℓ-zero
          target-ring = (freeBA ℕ QB./Im f) QB./Im d'

          equiv-hom : BoolHom (fst B) (freeBA ℕ QB./Im f)
          equiv-hom = fst (fst equiv) , snd equiv

          π-d' : BoolHom (freeBA ℕ QB./Im f) target-ring
          π-d' = QB.quotientImageHom

          composite-hom-1 : BoolHom (fst B) target-ring
          composite-hom-1 = π-d' ∘cr equiv-hom

          composite-sends-d-to-0 : (n : ℕ) → composite-hom-1 $cr (d n) ≡ BooleanRingStr.𝟘 (snd target-ring)
          composite-sends-d-to-0 n = QB.zeroOnImage {f = d'} n

          step1-forward-hom : BoolHom B/d target-ring
          step1-forward-hom = QB.inducedHom target-ring composite-hom-1 composite-sends-d-to-0

          π-d : BoolHom (fst B) B/d
          π-d = QB.quotientImageHom

          equiv⁻¹-hom : BoolHom (freeBA ℕ QB./Im f) (fst B)
          equiv⁻¹-hom = fst (fst (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)) ,
                        snd (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)

          backward-composite-1 : BoolHom (freeBA ℕ QB./Im f) B/d
          backward-composite-1 = π-d ∘cr equiv⁻¹-hom

          backward-composite-sends-d'-to-0 : (n : ℕ) → backward-composite-1 $cr (d' n) ≡ BooleanRingStr.𝟘 (snd B/d)
          backward-composite-sends-d'-to-0 n =
            π-d $cr (equiv⁻¹-hom $cr (fst (fst equiv) (d n)))
              ≡⟨ cong (π-d $cr_) (Iso.ret (equivToIso (fst equiv)) (d n)) ⟩
            π-d $cr (d n)
              ≡⟨ QB.zeroOnImage {f = d} n ⟩
            BooleanRingStr.𝟘 (snd B/d) ∎

          step1-backward-hom : BoolHom target-ring B/d
          step1-backward-hom = QB.inducedHom B/d backward-composite-1 backward-composite-sends-d'-to-0

          step1-forward-fun : ⟨ B/d ⟩ → ⟨ target-ring ⟩
          step1-forward-fun = fst step1-forward-hom

          step1-backward-fun : ⟨ target-ring ⟩ → ⟨ B/d ⟩
          step1-backward-fun = fst step1-backward-hom

          step1-forward-eval : step1-forward-hom ∘cr π-d ≡ composite-hom-1
          step1-forward-eval = QB.evalInduce {B = fst B} {f = d} target-ring

          step1-backward-eval : step1-backward-hom ∘cr π-d' ≡ backward-composite-1
          step1-backward-eval = QB.evalInduce {B = freeBA ℕ QB./Im f} {f = d'} B/d

          equiv⁻¹∘equiv≡id : (x : ⟨ fst B ⟩) → fst equiv⁻¹-hom (fst (fst equiv) x) ≡ x
          equiv⁻¹∘equiv≡id = Iso.ret (equivToIso (fst equiv))

          equiv∘equiv⁻¹≡id : (y : ⟨ freeBA ℕ QB./Im f ⟩) → fst (fst equiv) (fst equiv⁻¹-hom y) ≡ y
          equiv∘equiv⁻¹≡id = Iso.sec (equivToIso (fst equiv))

          step1-backward∘forward-on-π : (x : ⟨ fst B ⟩) → step1-backward-fun (step1-forward-fun (fst π-d x)) ≡ fst π-d x
          step1-backward∘forward-on-π x =
            step1-backward-fun (step1-forward-fun (fst π-d x))
              ≡⟨ cong step1-backward-fun (cong (λ hom → fst hom x) step1-forward-eval) ⟩
            step1-backward-fun (fst composite-hom-1 x)
              ≡⟨ cong (λ hom → fst hom (fst (fst equiv) x)) step1-backward-eval ⟩
            fst π-d (fst equiv⁻¹-hom (fst (fst equiv) x))
              ≡⟨ cong (fst π-d) (equiv⁻¹∘equiv≡id x) ⟩
            fst π-d x ∎

          step1-forward∘backward-on-π : (y : ⟨ freeBA ℕ QB./Im f ⟩) →
                                         step1-forward-fun (step1-backward-fun (fst π-d' y)) ≡ fst π-d' y
          step1-forward∘backward-on-π y =
            step1-forward-fun (step1-backward-fun (fst π-d' y))
              ≡⟨ cong step1-forward-fun (cong (λ hom → fst hom y) step1-backward-eval) ⟩
            step1-forward-fun (fst backward-composite-1 y)
              ≡⟨ cong (λ hom → fst hom (fst equiv⁻¹-hom y)) step1-forward-eval ⟩
            fst π-d' (fst (fst equiv) (fst equiv⁻¹-hom y))
              ≡⟨ cong (fst π-d') (equiv∘equiv⁻¹≡id y) ⟩
            fst π-d' y ∎

          step1-iso : Iso ⟨ B/d ⟩ ⟨ target-ring ⟩
          Iso.fun step1-iso = step1-forward-fun
          Iso.inv step1-iso = step1-backward-fun
          Iso.sec step1-iso = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ QB./Im f} {f = d'}
            (⟨ target-ring ⟩ , BooleanRingStr.is-set (snd target-ring)) (funExt step1-forward∘backward-on-π))
          Iso.ret step1-iso = funExt⁻ (QB.quotientImageHomEpi {B = fst B} {f = d}
            (⟨ B/d ⟩ , BooleanRingStr.is-set (snd B/d)) (funExt step1-backward∘forward-on-π))

          step1-equiv : BooleanRingEquiv B/d target-ring
          step1-equiv = isoToEquiv step1-iso , snd step1-forward-hom

          step1-equiv' : BooleanRingEquiv B/d ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
          step1-equiv' = subst (λ seq → BooleanRingEquiv B/d ((freeBA ℕ QB./Im f) QB./Im seq))
                           (funExt (λ n → sym (g-is-section n))) step1-equiv

          B'-seq : BooleanRing ℓ-zero
          B'-seq = (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)

          invStep2-seq : BooleanRingEquiv B'-seq rec-quotient
          invStep2-seq = invBooleanRingEquiv rec-quotient B'-seq step2-equiv

          invStep3-seq : BooleanRingEquiv rec-quotient h-quotient
          invStep3-seq = invBooleanRingEquiv h-quotient rec-quotient step3-equiv'

          step12-seq : BooleanRingEquiv B/d rec-quotient
          step12-seq = compBoolRingEquiv B/d B'-seq rec-quotient step1-equiv' invStep2-seq

          B/d-equiv : BooleanRingEquiv B/d (freeBA ℕ QB./Im h)
          B/d-equiv = compBoolRingEquiv B/d rec-quotient h-quotient step12-seq invStep3-seq

    quotientBySeqPreservesBooleω : (B : Booleω) (d : ℕ → ⟨ fst B ⟩)
      → ∥ Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))) ∥₁
    quotientBySeqPreservesBooleω B d = PT.map wrap (quotientBySeqHasBooleω B d)
      where
      wrap : has-Boole-ω' (fst B QB./Im d)
           → Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
      wrap pres = (fst B QB./Im d , ∣ pres ∣₁) , SpOfQuotientBySeq.Sp-quotient-≃ (fst B) d

  -- StoneSeparated (tex Lemma 1824)
