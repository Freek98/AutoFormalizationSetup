{-# OPTIONS --cubical --guardedness #-}

module work.Part08 where

open import work.Part07 public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; hProp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Transport using (transport⁻; transportTransport⁻; transport⁻Transport)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq; invEquiv; equivToIso)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; isSetBool; true≢false; false≢true; if_then_else_; not)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Empty as Empty using (⊥)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import BooleanRing.BoolRingUnivalence using (uaBoolRing; BoolRingPath)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom; BooleanRing→CommRing)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing using (CommRing; CommRingHom; IsCommRingHom; _$cr_; CommRingHom≡; _∘cr_)
open import Axioms.StoneDuality using (Booleω; Sp)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω'; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom; invBooleanRingEquiv)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; freeBA-universal-property; inducedBAHomUnique)
import QuotientBool as QB

module StoneEqualityClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)

  hasStoneStr→isSet : (S : Stone) → isSet (fst S)
  hasStoneStr→isSet (X , B , SpB≡X) = subst isSet SpB≡X (isSetBoolHom (fst B) BoolBR)

  open import BooleanRing.FreeBooleanRing.FreeBool using (generator; freeBA-universal-property; inducedBAHomUnique)
  open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; BooleanEquivToHomInv; BooleanEquivLeftInv; idBoolHom)
  import QuotientBool as QB

  Bool-eq-closed : (x y : Bool) → isClosedProp ((x ≡ y) , isSetBool x y)
  Bool-eq-closed x y = Bool-equality-closed x y

  SpEqualityClosed-from-presentation : (B : BooleanRing ℓ-zero)
    → (pres : has-Boole-ω' B)
    → (s t : Sp (B , ∣ pres ∣₁))
    → isClosedProp ((s ≡ t) , isSetBoolHom B BoolBR s t)
  SpEqualityClosed-from-presentation B (f , equiv) s t = proof
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
    P-closed n = Bool-eq-closed (s $cr (gen-in-B n)) (t $cr (gen-in-B n))

    ∀P-closed : isClosedProp (((n : ℕ) → fst (P n)) , isPropΠ (λ n → snd (P n)))
    ∀P-closed = closedCountableIntersection P P-closed

    agree-forward : s ≡ t → (n : ℕ) → fst (P n)
    agree-forward s=t n = cong (λ h → h $cr (gen-in-B n)) s=t

    β : binarySequence
    β = fst ∀P-closed

    s=t→βFalse : s ≡ t → (k : ℕ) → β k ≡ false
    s=t→βFalse s=t = fst (snd ∀P-closed) (agree-forward s=t)

    BoolHom-ext : {A B : BooleanRing ℓ-zero} → (h k : BoolHom A B)
      → ((x : ⟨ A ⟩) → fst h x ≡ fst k x) → h ≡ k
    BoolHom-ext h k pw = CommRingHom≡ (funExt pw)

    presEquiv⁻¹-hom : BoolHom Q B
    presEquiv⁻¹-hom = BooleanEquivToHomInv B Q equiv

    s-on-free : BoolHom (freeBA ℕ) BoolBR
    s-on-free = s ∘cr presEquiv⁻¹-hom ∘cr π

    t-on-free : BoolHom (freeBA ℕ) BoolBR
    t-on-free = t ∘cr presEquiv⁻¹-hom ∘cr π

    s-on-free-on-gen : (n : ℕ) → fst s-on-free (generator n) ≡ s $cr (gen-in-B n)
    s-on-free-on-gen n = refl

    t-on-free-on-gen : (n : ℕ) → fst t-on-free (generator n) ≡ t $cr (gen-in-B n)
    t-on-free-on-gen n = refl

    agree-on-free-gen : ((n : ℕ) → fst (P n))
      → (fst s-on-free ∘ generator ≡ fst t-on-free ∘ generator)
    agree-on-free-gen allP = funExt (λ n → allP n)

    s-on-free=t-on-free : ((n : ℕ) → fst (P n)) → s-on-free ≡ t-on-free
    s-on-free=t-on-free allP =
      let s-restr : ℕ → Bool
          s-restr = fst s-on-free ∘ generator
          t-restr : ℕ → Bool
          t-restr = fst t-on-free ∘ generator
          induced-s : BoolHom (freeBA ℕ) BoolBR
          induced-s = Iso.fun (freeBA-universal-property ℕ BoolBR) s-restr
          induced-t : BoolHom (freeBA ℕ) BoolBR
          induced-t = Iso.fun (freeBA-universal-property ℕ BoolBR) t-restr
          s-on-free=induced : induced-s ≡ s-on-free
          s-on-free=induced = Iso.sec (freeBA-universal-property ℕ BoolBR) s-on-free
          t-on-free=induced : induced-t ≡ t-on-free
          t-on-free=induced = Iso.sec (freeBA-universal-property ℕ BoolBR) t-on-free
          s-restr=t-restr : s-restr ≡ t-restr
          s-restr=t-restr = agree-on-free-gen allP
          induced-s=induced-t : induced-s ≡ induced-t
          induced-s=induced-t = cong (Iso.fun (freeBA-universal-property ℕ BoolBR)) s-restr=t-restr
      in sym s-on-free=induced ∙ induced-s=induced-t ∙ t-on-free=induced

    s-on-Q : BoolHom Q BoolBR
    s-on-Q = s ∘cr presEquiv⁻¹-hom

    t-on-Q : BoolHom Q BoolBR
    t-on-Q = t ∘cr presEquiv⁻¹-hom

    s-on-Q∘π=s-on-free : fst s-on-Q ∘ fst π ≡ fst s-on-free
    s-on-Q∘π=s-on-free = refl

    t-on-Q∘π=t-on-free : fst t-on-Q ∘ fst π ≡ fst t-on-free
    t-on-Q∘π=t-on-free = refl

    s-on-Q=t-on-Q-fst : ((n : ℕ) → fst (P n)) → fst s-on-Q ≡ fst t-on-Q
    s-on-Q=t-on-Q-fst allP =
      let s-free=t-free : s-on-free ≡ t-on-free
          s-free=t-free = s-on-free=t-on-free allP
          eq-on-π : fst s-on-Q ∘ fst π ≡ fst t-on-Q ∘ fst π
          eq-on-π = s-on-Q∘π=s-on-free ∙ cong fst s-free=t-free ∙ sym t-on-Q∘π=t-on-free
      in QB.quotientImageHomEpi (Bool , isSetBool) eq-on-π

    s-on-Q=t-on-Q : ((n : ℕ) → fst (P n)) → s-on-Q ≡ t-on-Q
    s-on-Q=t-on-Q allP = BoolHom-ext {Q} {BoolBR} s-on-Q t-on-Q (λ q → funExt⁻ (s-on-Q=t-on-Q-fst allP) q)

    leftInv : presEquiv⁻¹-hom ∘cr presEquiv-hom ≡ idBoolHom B
    leftInv = BooleanEquivLeftInv B Q equiv

    ∀P→s=t : ((n : ℕ) → fst (P n)) → s ≡ t
    ∀P→s=t allP =
      let s-on-Q=t-on-Q' : s-on-Q ≡ t-on-Q
          s-on-Q=t-on-Q' = s-on-Q=t-on-Q allP
          s=s∘id : s ≡ s ∘cr idBoolHom B
          s=s∘id = BoolHom-ext {B} {BoolBR} s (s ∘cr idBoolHom B) (λ _ → refl)
          t=t∘id : t ≡ t ∘cr idBoolHom B
          t=t∘id = BoolHom-ext {B} {BoolBR} t (t ∘cr idBoolHom B) (λ _ → refl)
          step1 : s ∘cr idBoolHom B ≡ s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)
          step1 = cong (s ∘cr_) (sym leftInv)
          step2 : s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom) ≡ s-on-Q ∘cr presEquiv-hom
          step2 = BoolHom-ext {B} {BoolBR} (s ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)) (s-on-Q ∘cr presEquiv-hom) (λ _ → refl)
          step3 : s-on-Q ∘cr presEquiv-hom ≡ t-on-Q ∘cr presEquiv-hom
          step3 = cong (_∘cr presEquiv-hom) s-on-Q=t-on-Q'
          step4 : t-on-Q ∘cr presEquiv-hom ≡ t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)
          step4 = BoolHom-ext {B} {BoolBR} (t-on-Q ∘cr presEquiv-hom) (t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom)) (λ _ → refl)
          step5 : t ∘cr (presEquiv⁻¹-hom ∘cr presEquiv-hom) ≡ t ∘cr idBoolHom B
          step5 = cong (t ∘cr_) leftInv
      in s=s∘id ∙ step1 ∙ step2 ∙ step3 ∙ step4 ∙ step5 ∙ sym t=t∘id

    βFalse→s=t : ((k : ℕ) → β k ≡ false) → s ≡ t
    βFalse→s=t = λ h → ∀P→s=t (snd (snd ∀P-closed) h)

    proof : isClosedProp ((s ≡ t) , isSetBoolHom B BoolBR s t)
    proof = β , s=t→βFalse , βFalse→s=t

  postulate
    isPropIsClosedProp : {P : hProp ℓ-zero} → isProp (isClosedProp P)

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
    forward backward spClosed
    where
    s' : Sp B
    s' = transport⁻ path s

    t' : Sp B
    t' = transport⁻ path t

    spClosed : isClosedProp ((s' ≡ t') , isSetBoolHom (fst B) BoolBR s' t')
    spClosed = SpEqualityClosed B s' t'

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
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isSetBoolHom)
  open SDDecToElemModule
  open StoneEqualityClosedModule

  record ClosedBySequence (S : Stone) : Type₁ where
    field
      α : fst S → (ℕ → Bool)

  record ClosedByCountableIntersection (S : Stone) : Type₁ where
    field
      D : ℕ → fst S → Bool  -- Dₙ(x) is decidable

  seq→decIntersection : (S : Stone) → ClosedBySequence S → ClosedByCountableIntersection S
  seq→decIntersection S seqForm = record
    { D = λ n x → not (ClosedBySequence.α seqForm x n) }

  decIntersection→seq : (S : Stone) → ClosedByCountableIntersection S → ClosedBySequence S
  decIntersection→seq S decForm = record
    { α = λ x n → not (ClosedByCountableIntersection.D decForm n x) }

  subsetFromSeq : (S : Stone) → ClosedBySequence S → (fst S → hProp ℓ-zero)
  subsetFromSeq S seqForm x = ((n : ℕ) → ClosedBySequence.α seqForm x n ≡ false) ,
                              isPropΠ (λ n → isSetBool _ _)

  subsetFromSeq-isClosed : (S : Stone) (seqForm : ClosedBySequence S)
    → (x : fst S) → isClosedProp (subsetFromSeq S seqForm x)
  subsetFromSeq-isClosed S seqForm x =
    closedCountableIntersection
      (λ n → (ClosedBySequence.α seqForm x n ≡ false) , isSetBool _ _)
      (λ n → Bool-eq-false-isClosed (ClosedBySequence.α seqForm x n))
    where
    Bool-eq-false-isClosed : (b : Bool) → isClosedProp ((b ≡ false) , isSetBool _ _)
    Bool-eq-false-isClosed b = decIsClosed ((b ≡ false) , isSetBool b false) (Bool-equality-decidable b false)

  seqForm→closed : (S : Stone) (seqForm : ClosedBySequence S)
    → isClosedSubset (subsetFromSeq S seqForm)
  seqForm→closed S seqForm x = subsetFromSeq-isClosed S seqForm x

  module SpOfQuotientBySeq (B : BooleanRing ℓ-zero) (d : ℕ → ⟨ B ⟩) where
    B/d : BooleanRing ℓ-zero
    B/d = B QB./Im d

    π : BoolHom B B/d
    π = QB.quotientImageHom

    ClosedSubset : Type ℓ-zero
    ClosedSubset = Σ[ x ∈ BoolHom B BoolBR ] ((n : ℕ) → fst x (d n) ≡ false)

    Sp-quotient→ClosedSubset : BoolHom B/d BoolBR → ClosedSubset
    Sp-quotient→ClosedSubset h = h ∘cr π , λ n → zeroOnImage-applied n
      where
      zeroOnImage-applied : (n : ℕ) → fst (h ∘cr π) (d n) ≡ false
      zeroOnImage-applied n =
        fst (h ∘cr π) (d n)     ≡⟨ refl ⟩
        fst h (fst π (d n))     ≡⟨ cong (fst h) (QB.zeroOnImage {B = B} {f = d} n) ⟩
        fst h (BooleanRingStr.𝟘 (snd B/d))  ≡⟨ IsCommRingHom.pres0 (snd h) ⟩
        false ∎

    ClosedSubset→Sp-quotient : ClosedSubset → BoolHom B/d BoolBR
    ClosedSubset→Sp-quotient (x , allZero) = QB.inducedHom {B = B} {f = d} BoolBR x allZero

    forward∘backward : (cs : ClosedSubset) → Sp-quotient→ClosedSubset (ClosedSubset→Sp-quotient cs) ≡ cs
    forward∘backward (x , allZero) = Σ≡Prop (λ _ → isPropΠ (λ _ → isSetBool _ _)) path
      where
      induced = ClosedSubset→Sp-quotient (x , allZero)
      path : fst (Sp-quotient→ClosedSubset induced) ≡ x
      path = QB.evalInduce {B = B} {f = d} BoolBR x allZero

    backward∘forward : (h : BoolHom B/d BoolBR) → ClosedSubset→Sp-quotient (Sp-quotient→ClosedSubset h) ≡ h
    backward∘forward h = QB.inducedHomUnique BoolBR (h ∘cr π) allZero h refl
      where
      allZero : (n : ℕ) → fst (h ∘cr π) (d n) ≡ false
      allZero = snd (Sp-quotient→ClosedSubset h)

    Sp-quotient-Iso : Iso (BoolHom B/d BoolBR) ClosedSubset
    Iso.fun Sp-quotient-Iso = Sp-quotient→ClosedSubset
    Iso.inv Sp-quotient-Iso = ClosedSubset→Sp-quotient
    Iso.sec Sp-quotient-Iso = forward∘backward
    Iso.ret Sp-quotient-Iso = backward∘forward

    Sp-quotient-≃ : BoolHom B/d BoolBR ≃ ClosedSubset
    Sp-quotient-≃ = isoToEquiv Sp-quotient-Iso

  quotientBySeqPreservesBooleω : (B : Booleω) (d : ℕ → ⟨ fst B ⟩)
    → ∥ Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))) ∥₁
  quotientBySeqPreservesBooleω B d = PT.rec squash₁ construct (snd B)
    where
    B/d : BooleanRing ℓ-zero
    B/d = fst B QB./Im d

    construct : has-Boole-ω' (fst B) →
                ∥ Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))) ∥₁
    construct (f , equiv) = PT.rec squash₁ (λ lifts → ∣ constructFromLifts lifts ∣₁) lifts-exist
      where
      open SpOfQuotientBySeq (fst B) d

      B/d-ring : BooleanRing ℓ-zero
      B/d-ring = fst B QB./Im d

      d' : ℕ → ⟨ freeBA ℕ QB./Im f ⟩
      d' n = fst (fst equiv) (d n)

      π-f : ⟨ freeBA ℕ ⟩ → ⟨ freeBA ℕ QB./Im f ⟩
      π-f = fst QB.quotientImageHom

      d'-has-preimage : (n : ℕ) → ∥ Σ[ x ∈ ⟨ freeBA ℕ ⟩ ] π-f x ≡ d' n ∥₁
      d'-has-preimage n = QB.quotientImageHomSurjective (d' n)

      LiftType : ℕ → Type ℓ-zero
      LiftType n = Σ[ x ∈ ⟨ freeBA ℕ ⟩ ] π-f x ≡ d' n

      lifts-exist : ∥ ((n : ℕ) → LiftType n) ∥₁
      lifts-exist = countableChoice LiftType d'-has-preimage

      constructFromLifts : ((n : ℕ) → LiftType n) →
                           Σ[ C ∈ Booleω ] (Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false)))
      constructFromLifts lifts = C , Sp-equiv
        where
        g : ℕ → ⟨ freeBA ℕ ⟩
        g n = fst (lifts n)

        g-is-section : (n : ℕ) → π-f (g n) ≡ d' n
        g-is-section n = snd (lifts n)

        encode : ℕ ⊎ ℕ → ℕ
        encode = Iso.fun ℕ⊎ℕ≅ℕ

        decode : ℕ → ℕ ⊎ ℕ
        decode = Iso.inv ℕ⊎ℕ≅ℕ

        h : ℕ → ⟨ freeBA ℕ ⟩
        h n with decode n
        ... | inl m = f m    -- relations from the original presentation
        ... | inr m = g m    -- relations from d' (via lifts)

        step2-path : BooleanRing→CommRing (freeBA ℕ QB./Im (⊎.rec f g)) ≡
                     BooleanRing→CommRing ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
        step2-path = BoolQuotientEquiv (freeBA ℕ) f g

        step2-equiv : BooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g))
                                       ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
        step2-equiv = commRingPath→boolRingEquiv
                        (freeBA ℕ QB./Im (⊎.rec f g))
                        ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
                        step2-path

        h≡rec∘decode-pointwise : (n : ℕ) → h n ≡ ⊎.rec f g (decode n)
        h≡rec∘decode-pointwise n with decode n
        ... | inl m = refl
        ... | inr m = refl

        h≡rec∘decode : h ≡ (⊎.rec f g) ∘ decode
        h≡rec∘decode = funExt h≡rec∘decode-pointwise

        rec-of-decode : (n : ℕ) → ⊎.rec f g (decode n) ≡ h n
        rec-of-decode n = sym (h≡rec∘decode-pointwise n)

        encode∘decode : (n : ℕ) → encode (decode n) ≡ n
        encode∘decode = Iso.sec ℕ⊎ℕ≅ℕ

        decode∘encode : (x : ℕ ⊎ ℕ) → decode (encode x) ≡ x
        decode∘encode = Iso.ret ℕ⊎ℕ≅ℕ

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
            ≡⟨ cong (π-rec $cr_) (sym (rec-of-decode n)) ⟩
          π-rec $cr ((⊎.rec f g) (decode n))
            ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = ⊎.rec f g} (decode n) ⟩
          BooleanRingStr.𝟘 (snd rec-quotient) ∎

        step3-forward-hom : BoolHom h-quotient rec-quotient
        step3-forward-hom = QB.inducedHom {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

        rec-eq-h-encode : (x : ℕ ⊎ ℕ) → (⊎.rec f g) x ≡ h (encode x)
        rec-eq-h-encode x =
          (⊎.rec f g) x
            ≡⟨ cong (⊎.rec f g) (sym (decode∘encode x)) ⟩
          (⊎.rec f g) (decode (encode x))
            ≡⟨ rec-of-decode (encode x) ⟩
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
        step3-forward-eval = QB.evalInduce {B = freeBA ℕ} {f = h} rec-quotient π-rec π-rec-sends-h-to-0

        step3-backward-eval : step3-backward-hom ∘cr π-rec ≡ π-h
        step3-backward-eval = QB.evalInduce {B = freeBA ℕ} {f = ⊎.rec f g} h-quotient π-h π-h-sends-rec-to-0

        h-quotient-isSet : isSet ⟨ h-quotient ⟩
        h-quotient-isSet = BooleanRingStr.is-set (snd h-quotient)

        rec-quotient-isSet : isSet ⟨ rec-quotient ⟩
        rec-quotient-isSet = BooleanRingStr.is-set (snd rec-quotient)

        step3-backward∘forward-on-π : (x : ⟨ freeBA ℕ ⟩) → step3-backward (step3-forward (fst π-h x)) ≡ fst π-h x
        step3-backward∘forward-on-π x =
          step3-backward (step3-forward (fst π-h x))
            ≡⟨ cong step3-backward (cong (λ hom → fst hom x) step3-forward-eval) ⟩
          step3-backward (fst π-rec x)
            ≡⟨ cong (λ hom → fst hom x) step3-backward-eval ⟩
          fst π-h x ∎

        step3-backward∘forward-ext : (step3-backward ∘ step3-forward) ∘ fst π-h ≡ (λ x → x) ∘ fst π-h
        step3-backward∘forward-ext = funExt step3-backward∘forward-on-π

        step3-backward∘forward : (x : ⟨ h-quotient ⟩) → step3-backward (step3-forward x) ≡ x
        step3-backward∘forward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = h}
                                           (⟨ h-quotient ⟩ , h-quotient-isSet) step3-backward∘forward-ext)

        step3-forward∘backward-on-π : (y : ⟨ freeBA ℕ ⟩) → step3-forward (step3-backward (fst π-rec y)) ≡ fst π-rec y
        step3-forward∘backward-on-π y =
          step3-forward (step3-backward (fst π-rec y))
            ≡⟨ cong step3-forward (cong (λ hom → fst hom y) step3-backward-eval) ⟩
          step3-forward (fst π-h y)
            ≡⟨ cong (λ hom → fst hom y) step3-forward-eval ⟩
          fst π-rec y ∎

        step3-forward∘backward-ext : (step3-forward ∘ step3-backward) ∘ fst π-rec ≡ (λ y → y) ∘ fst π-rec
        step3-forward∘backward-ext = funExt step3-forward∘backward-on-π

        step3-forward∘backward : (y : ⟨ rec-quotient ⟩) → step3-forward (step3-backward y) ≡ y
        step3-forward∘backward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ} {f = ⊎.rec f g}
                                           (⟨ rec-quotient ⟩ , rec-quotient-isSet) step3-forward∘backward-ext)

        step3-iso : Iso ⟨ h-quotient ⟩ ⟨ rec-quotient ⟩
        Iso.fun step3-iso = step3-forward
        Iso.inv step3-iso = step3-backward
        Iso.sec step3-iso = step3-forward∘backward
        Iso.ret step3-iso = step3-backward∘forward

        step3-equiv-fun : ⟨ h-quotient ⟩ ≃ ⟨ rec-quotient ⟩
        step3-equiv-fun = isoToEquiv step3-iso

        step3-equiv' : BooleanRingEquiv h-quotient rec-quotient
        step3-equiv' = step3-equiv-fun , snd step3-forward-hom

        step3-h-eq : freeBA ℕ QB./Im h ≡ freeBA ℕ QB./Im (⊎.rec f g)
        step3-h-eq = equivFun (BoolRingPath h-quotient rec-quotient) step3-equiv'

        step3-equiv : BooleanRingEquiv (freeBA ℕ QB./Im h) (freeBA ℕ QB./Im (⊎.rec f g))
        step3-equiv = invEq (BoolRingPath _ _) step3-h-eq

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

        step1-forward-hom : BoolHom B/d-ring target-ring
        step1-forward-hom = QB.inducedHom target-ring composite-hom-1 composite-sends-d-to-0

        π-d : BoolHom (fst B) B/d-ring
        π-d = QB.quotientImageHom

        equiv⁻¹-hom : BoolHom (freeBA ℕ QB./Im f) (fst B)
        equiv⁻¹-hom = fst (fst (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)) ,
                      snd (invBooleanRingEquiv (fst B) (freeBA ℕ QB./Im f) equiv)

        backward-composite-1 : BoolHom (freeBA ℕ QB./Im f) B/d-ring
        backward-composite-1 = π-d ∘cr equiv⁻¹-hom

        backward-composite-sends-d'-to-0 : (n : ℕ) → backward-composite-1 $cr (d' n) ≡ BooleanRingStr.𝟘 (snd B/d-ring)
        backward-composite-sends-d'-to-0 n =
          backward-composite-1 $cr (d' n)
            ≡⟨ refl ⟩
          π-d $cr (equiv⁻¹-hom $cr (fst (fst equiv) (d n)))
            ≡⟨ cong (π-d $cr_) (Iso.ret (equivToIso (fst equiv)) (d n)) ⟩
          π-d $cr (d n)
            ≡⟨ QB.zeroOnImage {f = d} n ⟩
          BooleanRingStr.𝟘 (snd B/d-ring) ∎

        step1-backward-hom : BoolHom target-ring B/d-ring
        step1-backward-hom = QB.inducedHom B/d-ring backward-composite-1 backward-composite-sends-d'-to-0

        step1-forward-fun : ⟨ B/d-ring ⟩ → ⟨ target-ring ⟩
        step1-forward-fun = fst step1-forward-hom

        step1-backward-fun : ⟨ target-ring ⟩ → ⟨ B/d-ring ⟩
        step1-backward-fun = fst step1-backward-hom

        step1-forward-eval : step1-forward-hom ∘cr π-d ≡ composite-hom-1
        step1-forward-eval = QB.evalInduce {B = fst B} {f = d} target-ring composite-hom-1 composite-sends-d-to-0

        step1-backward-eval : step1-backward-hom ∘cr π-d' ≡ backward-composite-1
        step1-backward-eval = QB.evalInduce {B = freeBA ℕ QB./Im f} {f = d'} B/d-ring
                                backward-composite-1 backward-composite-sends-d'-to-0

        equiv⁻¹∘equiv≡id : (x : ⟨ fst B ⟩) → fst equiv⁻¹-hom (fst (fst equiv) x) ≡ x
        equiv⁻¹∘equiv≡id = Iso.ret (equivToIso (fst equiv))

        equiv∘equiv⁻¹≡id : (y : ⟨ freeBA ℕ QB./Im f ⟩) → fst (fst equiv) (fst equiv⁻¹-hom y) ≡ y
        equiv∘equiv⁻¹≡id = Iso.sec (equivToIso (fst equiv))

        B/d-ring-isSet : isSet ⟨ B/d-ring ⟩
        B/d-ring-isSet = BooleanRingStr.is-set (snd B/d-ring)

        target-ring-isSet : isSet ⟨ target-ring ⟩
        target-ring-isSet = BooleanRingStr.is-set (snd target-ring)

        step1-backward∘forward-on-π : (x : ⟨ fst B ⟩) → step1-backward-fun (step1-forward-fun (fst π-d x)) ≡ fst π-d x
        step1-backward∘forward-on-π x =
          step1-backward-fun (step1-forward-fun (fst π-d x))
            ≡⟨ cong step1-backward-fun (cong (λ hom → fst hom x) step1-forward-eval) ⟩
          step1-backward-fun (fst composite-hom-1 x)
            ≡⟨ refl ⟩
          step1-backward-fun (fst π-d' (fst (fst equiv) x))
            ≡⟨ cong (λ hom → fst hom (fst (fst equiv) x)) step1-backward-eval ⟩
          fst backward-composite-1 (fst (fst equiv) x)
            ≡⟨ refl ⟩
          fst π-d (fst equiv⁻¹-hom (fst (fst equiv) x))
            ≡⟨ cong (fst π-d) (equiv⁻¹∘equiv≡id x) ⟩
          fst π-d x ∎

        step1-backward∘forward-ext : (step1-backward-fun ∘ step1-forward-fun) ∘ fst π-d ≡ (λ x → x) ∘ fst π-d
        step1-backward∘forward-ext = funExt step1-backward∘forward-on-π

        step1-backward∘forward : (x : ⟨ B/d-ring ⟩) → step1-backward-fun (step1-forward-fun x) ≡ x
        step1-backward∘forward = funExt⁻ (QB.quotientImageHomEpi {B = fst B} {f = d}
                                           (⟨ B/d-ring ⟩ , B/d-ring-isSet) step1-backward∘forward-ext)

        step1-forward∘backward-on-π : (y : ⟨ freeBA ℕ QB./Im f ⟩) →
                                       step1-forward-fun (step1-backward-fun (fst π-d' y)) ≡ fst π-d' y
        step1-forward∘backward-on-π y =
          step1-forward-fun (step1-backward-fun (fst π-d' y))
            ≡⟨ cong step1-forward-fun (cong (λ hom → fst hom y) step1-backward-eval) ⟩
          step1-forward-fun (fst backward-composite-1 y)
            ≡⟨ refl ⟩
          step1-forward-fun (fst π-d (fst equiv⁻¹-hom y))
            ≡⟨ cong (λ hom → fst hom (fst equiv⁻¹-hom y)) step1-forward-eval ⟩
          fst composite-hom-1 (fst equiv⁻¹-hom y)
            ≡⟨ refl ⟩
          fst π-d' (fst (fst equiv) (fst equiv⁻¹-hom y))
            ≡⟨ cong (fst π-d') (equiv∘equiv⁻¹≡id y) ⟩
          fst π-d' y ∎

        step1-forward∘backward-ext : (step1-forward-fun ∘ step1-backward-fun) ∘ fst π-d' ≡ (λ y → y) ∘ fst π-d'
        step1-forward∘backward-ext = funExt step1-forward∘backward-on-π

        step1-forward∘backward : (y : ⟨ target-ring ⟩) → step1-forward-fun (step1-backward-fun y) ≡ y
        step1-forward∘backward = funExt⁻ (QB.quotientImageHomEpi {B = freeBA ℕ QB./Im f} {f = d'}
                                           (⟨ target-ring ⟩ , target-ring-isSet) step1-forward∘backward-ext)

        step1-iso : Iso ⟨ B/d-ring ⟩ ⟨ target-ring ⟩
        Iso.fun step1-iso = step1-forward-fun
        Iso.inv step1-iso = step1-backward-fun
        Iso.sec step1-iso = step1-forward∘backward
        Iso.ret step1-iso = step1-backward∘forward

        step1-equiv-fun : ⟨ B/d-ring ⟩ ≃ ⟨ target-ring ⟩
        step1-equiv-fun = isoToEquiv step1-iso

        step1-equiv : BooleanRingEquiv B/d-ring target-ring
        step1-equiv = step1-equiv-fun , snd step1-forward-hom

        open IsCommRingHom

        d'≡π-f∘g-pointwise : (n : ℕ) → d' n ≡ fst QB.quotientImageHom (g n)
        d'≡π-f∘g-pointwise n = sym (g-is-section n)

        d'≡π-f∘g : d' ≡ fst QB.quotientImageHom ∘ g
        d'≡π-f∘g = funExt d'≡π-f∘g-pointwise

        step1-equiv' : BooleanRingEquiv B/d-ring ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
        step1-equiv' = subst (λ seq → BooleanRingEquiv B/d-ring ((freeBA ℕ QB./Im f) QB./Im seq))
                         d'≡π-f∘g step1-equiv

        A'-seq : BooleanRing ℓ-zero
        A'-seq = B/d-ring

        B'-seq : BooleanRing ℓ-zero
        B'-seq = (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)

        C'-seq : BooleanRing ℓ-zero
        C'-seq = freeBA ℕ QB./Im (⊎.rec f g)

        D'-seq : BooleanRing ℓ-zero
        D'-seq = freeBA ℕ QB./Im h

        invStep2-seq : BooleanRingEquiv B'-seq C'-seq
        invStep2-seq = invBooleanRingEquiv (freeBA ℕ QB./Im (⊎.rec f g))
                                            ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
                                            step2-equiv

        invStep3-seq : BooleanRingEquiv C'-seq D'-seq
        invStep3-seq = invBooleanRingEquiv (freeBA ℕ QB./Im h)
                                            (freeBA ℕ QB./Im (⊎.rec f g))
                                            step3-equiv

        step12-seq : BooleanRingEquiv A'-seq C'-seq
        step12-seq = compBoolRingEquiv A'-seq B'-seq C'-seq step1-equiv' invStep2-seq

        B/d-equiv : BooleanRingEquiv B/d-ring (freeBA ℕ QB./Im h)
        B/d-equiv = compBoolRingEquiv A'-seq C'-seq D'-seq step12-seq invStep3-seq

        B/d-presentation : has-Boole-ω' B/d-ring
        B/d-presentation = h , B/d-equiv

        C : Booleω
        C = B/d-ring , ∣ B/d-presentation ∣₁

        Sp-equiv : Sp C ≃ (Σ[ x ∈ Sp B ] ((n : ℕ) → fst x (d n) ≡ false))
        Sp-equiv = Sp-quotient-≃

-- StoneSeparated (tex Lemma 1824)
