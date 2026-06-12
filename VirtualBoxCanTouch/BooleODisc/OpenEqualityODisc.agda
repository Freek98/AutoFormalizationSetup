{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module OpenEqualityODisc where

{- Countably presented Boolean algebras have open equality, and are
   overtly discrete assuming the endgoal of OvertlyDiscrete/endgoal.agda.

   The idea: two elements become equal in the quotient freeBA ℕ /Im f
   iff their sum lies in the generated ideal.  Membership in the ideal
   is a countable disjunction of decidable propositions: z is in the
   ideal iff some finite list l of relation indices satisfies
       z · ⋁_{i ∈ l} f i ≡ z
   which is decidable in freeBA ℕ (DecidableEquality), with the index
   set List ℕ countable (CountableCover).  Hence the relation is open.

   On truncations: equality openness is stated as isOpen (mere).  The
   structure-level statement (x y : B) → hasOpenStr (x ≡ y), as
   currently in endgoal.agda (hasOpenEqualityStr), appears to be too
   strong for quotients: for the family B(α) = 2/(α n)_n over
   α : 2^ℕ, a uniform choice of witnessing sequences for
   [1] ≡ [0] would give a continuous α ↦ β(α) with
   (Σn β(α)n) ↔ (Σn αn) and β(α) = β₀(α) whenever Σn αn, where
   Σn β₀(α)n always holds.  Compactness of 2^ℕ bounds the witness of
   β₀ by some N; evaluating at α = δ_k and letting k → ∞ contradicts
   β(0̄) = 0̄.  So we assume the SeqColim endgoal in the corresponding
   property form (isOpen hypothesis, merely truncated conclusion).
   On representatives, the open structure does exist untruncated
   (openEqualityOnReps below). -}

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Sigma
open import Cubical.Data.List.Base
import Cubical.Data.Empty as ⊥

open import Cubical.Relation.Nullary
open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Functions.Surjection

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit
open import Cubical.Data.FinSet

open import BasicDefinitions
open import PropositionalTopology.Definitions
open import CountablyPresentedBooleanRings.Definitions
import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import CommRingQuotients.ZeroInQuotient
open import CommRingQuotients.IdealTerms
open import BooleanRing.FreeBooleanRing.FreeBool

open import DecidableEquality using (discreteFreeBAℕ)
open import CountableCover using (hasCountableCover ; listCount ; ℕcount ; freeBAℕCountableCover)

private
  variable
    ℓ : Level

-- ═══════════════════════════════════════════════════════════════
-- Generic helpers
-- ═══════════════════════════════════════════════════════════════

private
  boolGuard : (b : Bool) → (b ≡ true → Bool) → Bool
  boolGuard true  g = g refl
  boolGuard false _ = false

  boolGuard-intro : (b : Bool) (g : b ≡ true → Bool) (q : b ≡ true)
    → g q ≡ true → boolGuard b g ≡ true
  boolGuard-intro true g q gq =
    subst (λ r → g r ≡ true) (isSetBool _ _ q refl) gq
  boolGuard-intro false g q _ = ⊥.rec (false≢true q)

  boolGuard-elim : (b : Bool) (g : b ≡ true → Bool)
    → boolGuard b g ≡ true → Σ[ q ∈ b ≡ true ] g q ≡ true
  boolGuard-elim true  g p = refl , p
  boolGuard-elim false _ p = ⊥.rec (false≢true p)

  decTrue : {P : Type} (d : Dec P) → P → Dec→Bool d ≡ true
  decTrue (yes _) _ = refl
  decTrue (no ¬p) p = ⊥.rec (¬p p)

  trueDec : {P : Type} (d : Dec P) → Dec→Bool d ≡ true → P
  trueDec (yes p) _ = p
  trueDec (no  _) e = ⊥.rec (false≢true e)

  -- mere existence of a hit of a binary sequence gives an actual hit,
  -- by searching for the least one
  splitΣα : (α : binarySequence) →
    ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁ → Σ[ n ∈ ℕ ] α n ≡ true
  splitΣα α = Collapsible→SplitSupport
    (Decidable→Collapsible (λ n → isSetBool _ _) (λ n → α n ≟ true))

  -- openness transports along biimplications of propositions
  openStr↔ : {P Q : Type} → isProp P → (P → Q) × (Q → P) →
    hasOpenStr Q → hasOpenStr P
  openStr↔ pP (to , from) (_ , α , (L , R)) =
    pP , α , ((λ p → L (to p)) , (λ s → from (R s)))

-- ═══════════════════════════════════════════════════════════════
-- Open equality for the presented algebra freeBA ℕ /Im f
-- ═══════════════════════════════════════════════════════════════

module PresentedAlgebra (f : ℕ → ⟨ freeBA ℕ ⟩) where

  open BooleanRingStr (snd (freeBA ℕ))
  open BooleanAlgebraStr (snd (freeBA ℕ)) renaming (¬_ to ¬b_ ; _∨_ to _∨f_ ; _∧_ to _∧f_)

  private
    R : CommRing ℓ-zero
    R = BooleanRing→CommRing (freeBA ℕ)

    Idl = IQ.genIdeal R f

    Q : CommRing ℓ-zero
    Q = R IQ./Im f

    π : ⟨ R ⟩ → ⟨ Q ⟩
    π = fst (quotientHom R Idl)

    πHom = snd (quotientHom R Idl)

    module QS = CommRingStr (snd Q)
    open IsCommRingHom

  -- ── the join of a finite list of relations ──────────────────────

  joinList : List ℕ → ⟨ freeBA ℕ ⟩
  joinList [] = 𝟘
  joinList (n ∷ l) = f n ∨f joinList l

  joinList-++ : (l₁ l₂ : List ℕ) →
    joinList (l₁ ++ l₂) ≡ joinList l₁ ∨f joinList l₂
  joinList-++ [] l₂ = sym ∨IdL
  joinList-++ (n ∷ l₁) l₂ = cong (f n ∨f_) (joinList-++ l₁ l₂) ∙ ∨Assoc

  -- x ≤ w (i.e. x · w ≡ x) is preserved by enlarging the join
  absorbL : (x w₁ w₂ : ⟨ freeBA ℕ ⟩) → x · w₁ ≡ x → x · (w₁ ∨f w₂) ≡ x
  absorbL x w₁ w₂ e =
    ∧DistR∨ ∙ cong (_∨f (x · w₂)) e ∙ ∨AbsorbL∧

  absorbR : (x w₁ w₂ : ⟨ freeBA ℕ ⟩) → x · w₂ ≡ x → x · (w₁ ∨f w₂) ≡ x
  absorbR x w₁ w₂ e =
    cong (x ·_) ∨Comm ∙ absorbL x w₂ w₁ e

  -- ── ideal membership is bounded by a finite join ────────────────

  boundFromTerms : (r : ⟨ R ⟩) → isInIdeal R f r →
    Σ[ l ∈ List ℕ ] r · joinList l ≡ r
  boundFromTerms r (isImage .r x fx≡r) = (x ∷ []) ,
    (cong (r ·_) ∨IdR
     ∙ cong (_· f x) (sym fx≡r)
     ∙ ·Idem (f x)
     ∙ fx≡r)
  boundFromTerms r (iszero .r 0≡r) = [] ,
    (∧AnnihilR ∙ 0≡r)
  boundFromTerms r (isSum .r s t r≡s+t s∈I t∈I) =
    (ls ++ lt) ,
    (cong (_· joinList (ls ++ lt)) r≡s+t
     ∙ ·Comm _ _
     ∙ ·DistR+ (joinList (ls ++ lt)) s t
     ∙ cong₂ _+_
         (·Comm _ _ ∙ cong (s ·_) (joinList-++ ls lt) ∙ absorbL s _ _ es)
         (·Comm _ _ ∙ cong (t ·_) (joinList-++ ls lt) ∙ absorbR t _ _ et)
     ∙ sym r≡s+t)
    where
    ls = fst (boundFromTerms s s∈I)
    es = snd (boundFromTerms s s∈I)
    lt = fst (boundFromTerms t t∈I)
    et = snd (boundFromTerms t t∈I)
  boundFromTerms r (isMul .r s t r≡s·t t∈I) =
    lt ,
    (cong (_· joinList lt) r≡s·t
     ∙ sym (·Assoc s t (joinList lt))
     ∙ cong (s ·_) et
     ∙ sym r≡s·t)
    where
    lt = fst (boundFromTerms t t∈I)
    et = snd (boundFromTerms t t∈I)

  joinInIdeal : (l : List ℕ) → IQ.generatedIdeal R f (joinList l)
  joinInIdeal [] = IQ.zero
  joinInIdeal (n ∷ l) =
    IQ.add (IQ.add (IQ.single n) (joinInIdeal l)) (IQ.mul (joinInIdeal l))

  boundToIdeal : (r : ⟨ R ⟩) (l : List ℕ) →
    r · joinList l ≡ r → IQ.generatedIdeal R f r
  boundToIdeal r l e =
    subst (IQ.generatedIdeal R f) e (IQ.mul (joinInIdeal l))

  -- ── equality in the quotient is ideal membership of the sum ─────

  eqToIdeal : (a b : ⟨ R ⟩) → π a ≡ π b → IQ.generatedIdeal R f (a + b)
  eqToIdeal a b p = zeroInQuotient→inIdeal Idl (a + b) πz≡0
    where
    πz≡0 : π (a + b) ≡ QS.0r
    πz≡0 =
      π (a + b)
        ≡⟨ pres+ πHom a b ⟩
      π a QS.+ π b
        ≡⟨ cong (QS._+ π b) p ⟩
      π b QS.+ π b
        ≡⟨ sym (pres+ πHom b b) ⟩
      π (b + b)
        ≡⟨ cong π characteristic2 ⟩
      π 𝟘
        ≡⟨ pres0 πHom ⟩
      QS.0r ∎

  idealToEq : (a b : ⟨ R ⟩) → IQ.generatedIdeal R f (a + b) → π a ≡ π b
  idealToEq a b m =
    π a
      ≡⟨ sym (QS.+IdR (π a)) ⟩
    π a QS.+ QS.0r
      ≡⟨ cong (π a QS.+_) (sym πz≡0) ⟩
    π a QS.+ π (a + b)
      ≡⟨ cong (π a QS.+_) (pres+ πHom a b) ⟩
    π a QS.+ (π a QS.+ π b)
      ≡⟨ QS.+Assoc (π a) (π a) (π b) ⟩
    (π a QS.+ π a) QS.+ π b
      ≡⟨ cong (QS._+ π b) (sym (pres+ πHom a a)) ⟩
    π (a + a) QS.+ π b
      ≡⟨ cong (QS._+ π b) (cong π characteristic2 ∙ pres0 πHom) ⟩
    QS.0r QS.+ π b
      ≡⟨ QS.+IdL (π b) ⟩
    π b ∎
    where
    πz≡0 : π (a + b) ≡ QS.0r
    πz≡0 = zeroOnIdeal Idl (a + b) m

  -- ── the open structure on representatives ───────────────────────

  private
    γL : binarySequence
    γL = fst (listCount ℕcount)

    isoL : Iso (List ℕ) (Σℕ γL)
    isoL = snd (listCount ℕcount)

  module _ (a b : ⟨ freeBA ℕ ⟩) where
    private
      zab = a + b

      testZ : List ℕ → Bool
      testZ l = Dec→Bool (discreteFreeBAℕ (zab · joinList l) zab)

      α : binarySequence
      α n = boolGuard (γL n) (λ q → testZ (Iso.inv isoL (n , q)))

      encode : Σ[ l ∈ List ℕ ] zab · joinList l ≡ zab → Σ[ n ∈ ℕ ] α n ≡ true
      encode (l , e) =
        fst (Iso.fun isoL l) ,
        boolGuard-intro (γL (fst (Iso.fun isoL l))) _ (snd (Iso.fun isoL l))
          (cong testZ (Iso.ret isoL l) ∙ decTrue (discreteFreeBAℕ _ _) e)

      decode : Σ[ n ∈ ℕ ] α n ≡ true → Σ[ l ∈ List ℕ ] zab · joinList l ≡ zab
      decode (n , h) =
        Iso.inv isoL (n , fst step) ,
        trueDec (discreteFreeBAℕ _ _) (snd step)
        where
        step = boolGuard-elim (γL n) _ h

    openEqualityOnReps : hasOpenStr (π a ≡ π b)
    openEqualityOnReps = QS.is-set (π a) (π b) , α , (fwd , bwd)
      where
      fwd : π a ≡ π b → Σ[ n ∈ ℕ ] α n ≡ true
      fwd p = splitΣα α
        (PT.map (encode ∘ boundFromTerms zab)
                (idealDecomp R f zab (eqToIdeal a b p)))

      bwd : Σ[ n ∈ ℕ ] α n ≡ true → π a ≡ π b
      bwd s = idealToEq a b (boundToIdeal zab (fst (decode s)) (snd (decode s)))

  -- ── openness and cover for the quotient, CommRing level ─────────

  openEqualityQuot : (x y : ⟨ Q ⟩) → isOpen (x ≡ y)
  openEqualityQuot x y = PT.rec2 squash₁
    (λ (a , pa) (b , pb) →
      ∣ subst2 (λ u v → hasOpenStr (u ≡ v)) pa pb (openEqualityOnReps a b) ∣₁)
    (quotientHomSurjective R Idl x)
    (quotientHomSurjective R Idl y)

  coverQuot : hasCountableCover ⟨ Q ⟩
  coverQuot =
    T , cT ,
    compSurjection cov (π , quotientHomSurjective R Idl)
    where
    T  = fst freeBAℕCountableCover
    cT = fst (snd freeBAℕCountableCover)
    cov = snd (snd freeBAℕCountableCover)

  -- ── transport to the Boolean-ring-level quotient ────────────────

  private
    BB : BooleanRing ℓ-zero
    BB = QB._/Im_ (freeBA ℕ) f

    carrierPath : ⟨ Q ⟩ ≡ ⟨ BB ⟩
    carrierPath = cong fst (QB.QuotientBooleanRingAgreesWithCommRing
                             {A = freeBA ℕ} {f = f})

  openEqualityBB : (x y : ⟨ BB ⟩) → isOpen (x ≡ y)
  openEqualityBB =
    subst (λ T' → (x y : T') → isOpen (x ≡ y)) carrierPath openEqualityQuot

  coverBB : hasCountableCover ⟨ BB ⟩
  coverBB = subst hasCountableCover carrierPath coverQuot

-- ═══════════════════════════════════════════════════════════════
-- Open equality and cover for countably presented Boolean algebras
-- ═══════════════════════════════════════════════════════════════

module _ (B : BooleanRing ℓ-zero) (pres : has-quotient-of-freeℕ-presentation B) where
  private
    f = fst pres
    open PresentedAlgebra f

    e : ⟨ B ⟩ ≃ ⟨ QB._/Im_ (freeBA ℕ) f ⟩
    e = fst (snd pres)

    isSetB : isSet ⟨ B ⟩
    isSetB = BooleanRingStr.is-set (snd B)

  presentedOpenEquality : (x y : ⟨ B ⟩) → isOpen (x ≡ y)
  presentedOpenEquality x y =
    PT.map
      (openStr↔ (isSetB x y)
        (cong (equivFun e) , isoFunInjective (equivToIso e) x y))
      (openEqualityBB (equivFun e x) (equivFun e y))

  presentedCountableCover : hasCountableCover ⟨ B ⟩
  presentedCountableCover =
    fst coverBB , fst (snd coverBB) ,
    compSurjection (snd (snd coverBB))
      (invEq e , λ b → ∣ equivFun e b , retEq e b ∣₁)

-- the truncated presentation suffices for the (propositional) openness
countablyPresentedOpenEquality : (B : BooleanRing ℓ-zero) →
  is-countably-presented-alt B → (x y : ⟨ B ⟩) → isOpen (x ≡ y)
countablyPresentedOpenEquality B =
  PT.rec (isPropΠ2 (λ _ _ → squash₁)) (presentedOpenEquality B)

-- ═══════════════════════════════════════════════════════════════
-- Overt discreteness, assuming the SeqColim endgoal
-- ═══════════════════════════════════════════════════════════════

-- definitions as in OvertlyDiscrete/endgoal.agda
isSequenceOfFiniteSets : Sequence ℓ → Type _
isSequenceOfFiniteSets An = (n : ℕ) → isFinSet (Sequence.obj An n)

sequenceOfFiniteSets : Type (ℓ-suc ℓ)
sequenceOfFiniteSets {ℓ} = Σ[ An ∈ Sequence ℓ ] isSequenceOfFiniteSets An

hasODiscStr : Type ℓ → Type (ℓ-suc ℓ)
hasODiscStr A = Σ[ An ∈ sequenceOfFiniteSets ] A ≡ SeqColim (fst An)

-- the endgoal of OvertlyDiscrete/endgoal.agda
-- (CountableCoverAndOpenEqualityImpliesODisc), in property form:
-- open equality is supplied merely, and the conclusion is truncated
module ODiscConsequence
  (seqColimEndGoal : (A : Type) →
    hasCountableCover A →
    ((x y : A) → isOpen (x ≡ y)) →
    ∥ hasODiscStr A ∥₁)
  where

  presentedODisc : (B : BooleanRing ℓ-zero) →
    has-quotient-of-freeℕ-presentation B → ∥ hasODiscStr ⟨ B ⟩ ∥₁
  presentedODisc B pres =
    seqColimEndGoal ⟨ B ⟩
      (presentedCountableCover B pres)
      (presentedOpenEquality B pres)

  countablyPresentedODisc : (B : BooleanRing ℓ-zero) →
    is-countably-presented-alt B → ∥ hasODiscStr ⟨ B ⟩ ∥₁
  countablyPresentedODisc B =
    PT.rec squash₁ (presentedODisc B)
