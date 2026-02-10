{-# OPTIONS --cubical --guardedness #-}

module work.Part05a where

open import work.Part04 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; isSetBool; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no; Discrete; Discrete→isSet)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Functions.Surjection using (isSurjection ; compSurjection)
open import BooleanRing.FreeBooleanRing.freeBATerms using
  (includeBATermsSurj ; freeBATerms ; includeBATerms-Tvar ;
   includeBATerms-+ ; includeBATerms-· ; includeBATerms-- ; includeBATerms-0 ; includeBATerms-1)
open import BooleanRing.FreeBooleanRing.SurjectiveTerms using (TermsOf_[_]; Tvar; Tconst; _+T_; -T_; _·T_; includeTerm)

π∞-surj : isSurjection (fst π∞)
π∞-surj = QB.quotientImageHomSurjective

π∞-includeTerms-surj : isSurjection (fst π∞ ∘ fst includeBATermsSurj)
π∞-includeTerms-surj = compSurjection (fst includeBATermsSurj , snd includeBATermsSurj) (fst π∞ , π∞-surj) .snd

π∞-from-terms : freeBATerms ℕ → ⟨ B∞ ⟩
π∞-from-terms t = fst π∞ (fst includeBATermsSurj t)

interpretB∞ : freeBATerms ℕ → ⟨ B∞ ⟩
interpretB∞ (Tvar n) = g∞ n
interpretB∞ (Tconst false) = 𝟘∞
interpretB∞ (Tconst true) = 𝟙∞
interpretB∞ (t +T s) = interpretB∞ t +∞ interpretB∞ s
interpretB∞ (-T t) = interpretB∞ t
interpretB∞ (t ·T s) = interpretB∞ t ·∞ interpretB∞ s

π∞-0 : fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ))) ≡ 𝟘∞
π∞-0 = IsCommRingHom.pres0 (snd π∞)

π∞-1 : fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ))) ≡ 𝟙∞
π∞-1 = IsCommRingHom.pres1 (snd π∞)

π∞-gen : (n : ℕ) → fst π∞ (generator n) ≡ g∞ n
π∞-gen n = refl

private
  _+Free_ = BooleanRingStr._+_ (snd (freeBA ℕ))
  _·Free_ = BooleanRingStr._·_ (snd (freeBA ℕ))
  -Free_ = BooleanRingStr.-_ (snd (freeBA ℕ))

π∞-+ : (a b : ⟨ freeBA ℕ ⟩) → fst π∞ (a +Free b) ≡ fst π∞ a +∞ fst π∞ b
π∞-+ a b = IsCommRingHom.pres+ (snd π∞) a b

π∞-· : (a b : ⟨ freeBA ℕ ⟩) → fst π∞ (a ·Free b) ≡ fst π∞ a ·∞ fst π∞ b
π∞-· a b = IsCommRingHom.pres· (snd π∞) a b

π∞-neg : (a : ⟨ freeBA ℕ ⟩) → fst π∞ (-Free a) ≡ BooleanRingStr.-_ (snd B∞) (fst π∞ a)
π∞-neg a = IsCommRingHom.pres- (snd π∞) a

interpretB∞-eq-composition : (t : freeBATerms ℕ) → interpretB∞ t ≡ π∞-from-terms t
interpretB∞-eq-composition (Tvar n) =
  g∞ n
    ≡⟨ sym (π∞-gen n) ⟩
  fst π∞ (generator n)
    ≡⟨ cong (fst π∞) (sym (includeBATerms-Tvar n)) ⟩
  π∞-from-terms (Tvar n) ∎
interpretB∞-eq-composition (Tconst false) =
  𝟘∞
    ≡⟨ sym π∞-0 ⟩
  fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-0) ⟩
  π∞-from-terms (Tconst false) ∎
interpretB∞-eq-composition (Tconst true) =
  𝟙∞
    ≡⟨ sym π∞-1 ⟩
  fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-1) ⟩
  π∞-from-terms (Tconst true) ∎
interpretB∞-eq-composition (t +T s) =
  interpretB∞ t +∞ interpretB∞ s
    ≡⟨ cong₂ _+∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t +∞ π∞-from-terms s
    ≡⟨ sym (π∞-+ (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._+_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-+ t s)) ⟩
  π∞-from-terms (t +T s) ∎
interpretB∞-eq-composition (-T t) =
  interpretB∞ t
    ≡⟨ interpretB∞-eq-composition t ⟩
  π∞-from-terms t
    ≡⟨ cong (fst π∞) (BooleanRing-neg-id t) ⟩
  fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj t))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-- t)) ⟩
  π∞-from-terms (-T t) ∎
  where
  BooleanRing-neg-id : (s : freeBATerms ℕ) →
    fst includeBATermsSurj s ≡ BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj s)
  BooleanRing-neg-id s = BooleanAlgebraStr.-IsId (freeBA ℕ) {x = fst includeBATermsSurj s}
interpretB∞-eq-composition (t ·T s) =
  interpretB∞ t ·∞ interpretB∞ s
    ≡⟨ cong₂ _·∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t ·∞ π∞-from-terms s
    ≡⟨ sym (π∞-· (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._·_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-· t s)) ⟩
  π∞-from-terms (t ·T s) ∎

interpretB∞-surjective : isSurjection interpretB∞
interpretB∞-surjective x = PT.map helper (π∞-includeTerms-surj x)
  where
  helper : Σ[ t ∈ freeBATerms ℕ ] π∞-from-terms t ≡ x → Σ[ t ∈ freeBATerms ℕ ] interpretB∞ t ≡ x
  helper pair = fst pair , interpretB∞-eq-composition (fst pair) ∙ snd pair

open import Cubical.Data.List using (isOfHLevelList)
open import Cubical.Data.Nat using (isSetℕ; discreteℕ)
open import Cubical.Data.List using (discreteList)

isSetListℕ : isSet (List ℕ)
isSetListℕ = isOfHLevelList 0 isSetℕ

discreteListℕ : Discrete (List ℕ)
discreteListℕ = discreteList discreteℕ

discreteNF : Discrete B∞-NormalForm
discreteNF (joinForm ns) (joinForm ms) with discreteListℕ ns ms
... | yes p = yes (cong joinForm p)
... | no ¬p = no (λ eq → ¬p (joinForm-inj eq))
  where
  joinForm-inj : joinForm ns ≡ joinForm ms → ns ≡ ms
  joinForm-inj p = cong (λ { (joinForm x) → x ; (meetNegForm _) → [] }) p
discreteNF (joinForm _) (meetNegForm _) = no (λ p → joinForm≢meetNegForm p)
  where
  joinForm≢meetNegForm : ∀ {ns ms} → joinForm ns ≡ meetNegForm ms → ⊥
  joinForm≢meetNegForm p = transport (cong (λ { (joinForm _) → Unit ; (meetNegForm _) → ⊥ }) p) tt
discreteNF (meetNegForm _) (joinForm _) = no (λ p → meetNegForm≢joinForm p)
  where
  meetNegForm≢joinForm : ∀ {ns ms} → meetNegForm ns ≡ joinForm ms → ⊥
  meetNegForm≢joinForm p = transport (cong (λ { (joinForm _) → ⊥ ; (meetNegForm _) → Unit }) p) tt
discreteNF (meetNegForm ns) (meetNegForm ms) with discreteListℕ ns ms
... | yes p = yes (cong meetNegForm p)
... | no ¬p = no (λ eq → ¬p (meetNegForm-inj eq))
  where
  meetNegForm-inj : meetNegForm ns ≡ meetNegForm ms → ns ≡ ms
  meetNegForm-inj p = cong (λ { (joinForm _) → [] ; (meetNegForm x) → x }) p

isSetB∞-NormalForm : isSet B∞-NormalForm
isSetB∞-NormalForm = Discrete→isSet discreteNF

_∈?_ : ℕ → List ℕ → Bool
n ∈? [] = false
n ∈? (m ∷ ms) with discreteℕ n m
... | yes _ = true
... | no _ = n ∈? ms

_∩L_ : List ℕ → List ℕ → List ℕ
[] ∩L ms = []
(n ∷ ns) ∩L ms with n ∈? ms
... | true = n ∷ (ns ∩L ms)
... | false = ns ∩L ms

_∖L_ : List ℕ → List ℕ → List ℕ
[] ∖L ms = []
(n ∷ ns) ∖L ms with n ∈? ms
... | true = ns ∖L ms
... | false = n ∷ (ns ∖L ms)

_△L_ : List ℕ → List ℕ → List ℕ
ns △L ms = (ns ++ ms) ∖L (ns ∩L ms)

xor-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
xor-nf (joinForm ns) (joinForm ms) = joinForm (ns △L ms)
xor-nf (joinForm ns) (meetNegForm ms) = meetNegForm (ns △L ms)
xor-nf (meetNegForm ns) (joinForm ms) = meetNegForm (ms △L ns)
xor-nf (meetNegForm ns) (meetNegForm ms) = joinForm (ns △L ms)

meet-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
meet-nf (joinForm ns) (joinForm ms) = joinForm (ns ∩L ms)
meet-nf (joinForm ns) (meetNegForm ms) = joinForm (ns ∖L ms)
meet-nf (meetNegForm ns) (joinForm ms) = joinForm (ms ∖L ns)
meet-nf (meetNegForm ns) (meetNegForm ms) = meetNegForm (ns ++ ms)

normalizeTerm : freeBATerms ℕ → B∞-NormalForm
normalizeTerm (Tvar n) = joinForm (n ∷ [])
normalizeTerm (Tconst false) = joinForm []
normalizeTerm (Tconst true) = meetNegForm []
normalizeTerm (t +T s) = xor-nf (normalizeTerm t) (normalizeTerm s)
normalizeTerm (-T t) = normalizeTerm t
normalizeTerm (t ·T s) = meet-nf (normalizeTerm t) (normalizeTerm s)

postulate
  normalizeTerm-correct : (t : freeBATerms ℕ) → ⟦ normalizeTerm t ⟧nf ≡ interpretB∞ t

normalFormExists-trunc : (x : ⟨ B∞ ⟩) → ∥ Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ x ∥₁
normalFormExists-trunc x = PT.map
  (λ pair → normalizeTerm (fst pair) , normalizeTerm-correct (fst pair) ∙ snd pair)
  (interpretB∞-surjective x)

char2-B∞ : (x : ⟨ B∞ ⟩) → x +∞ x ≡ 𝟘∞
char2-B∞ x = BooleanAlgebraStr.characteristic2 B∞ {x}

char2-B∞×B∞ : (z : ⟨ B∞×B∞ ⟩) → z +× z ≡ (𝟘∞ , 𝟘∞)
char2-B∞×B∞ (a , b) = cong₂ _,_ (char2-B∞ a) (char2-B∞ b)

postulate
  f-kernel-normalForm-05a : (nf : B∞-NormalForm) → fst f ⟦ nf ⟧nf ≡ (𝟘∞ , 𝟘∞) → ⟦ nf ⟧nf ≡ 𝟘∞

f-kernel-from-trunc-05a : (x : ⟨ B∞ ⟩) → fst f x ≡ (𝟘∞ , 𝟘∞) → x ≡ 𝟘∞
f-kernel-from-trunc-05a x fx=0 = PT.rec (BooleanRingStr.is-set (snd B∞) x 𝟘∞)
  (λ pair → let nf = fst pair
                eq = snd pair
            in sym eq ∙ f-kernel-normalForm-05a nf (cong (fst f) eq ∙ fx=0))
  (normalFormExists-trunc x)

f-injective-05a : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective-05a x y fx=fy =
  let xy-diff : ⟨ B∞ ⟩
      xy-diff = x +∞ y

      f-xy-diff : fst f xy-diff ≡ (𝟘∞ , 𝟘∞)
      f-xy-diff =
        fst f (x +∞ y)
          ≡⟨ f-pres+ x y ⟩
        (fst f x) +× (fst f y)
          ≡⟨ cong (_+× (fst f y)) fx=fy ⟩
        (fst f y) +× (fst f y)
          ≡⟨ char2-B∞×B∞ (fst f y) ⟩
        (𝟘∞ , 𝟘∞) ∎

      xy=0 : xy-diff ≡ 𝟘∞
      xy=0 = f-kernel-from-trunc-05a xy-diff f-xy-diff

      x=y : x ≡ y
      x=y = BooleanRing-xor-eq-to-eq' x y xy=0

  in x=y
  where
  BooleanRing-xor-eq-to-eq' : (a b : ⟨ B∞ ⟩) → a +∞ b ≡ 𝟘∞ → a ≡ b
  BooleanRing-xor-eq-to-eq' a b ab=0 =
    a
      ≡⟨ sym (BooleanRingStr.+IdR (snd B∞) a) ⟩
    a +∞ 𝟘∞
      ≡⟨ cong (a +∞_) (sym (char2-B∞ b)) ⟩
    a +∞ (b +∞ b)
      ≡⟨ BooleanRingStr.+Assoc (snd B∞) a b b ⟩
    (a +∞ b) +∞ b
      ≡⟨ cong (_+∞ b) ab=0 ⟩
    𝟘∞ +∞ b
      ≡⟨ BooleanRingStr.+IdL (snd B∞) b ⟩
    b ∎
