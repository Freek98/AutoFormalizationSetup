{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneDuality.NormalForms (fa : FoundationalAxioms) where

open import formalization.StoneDuality.FinCofinAlgebra fa public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec)
open import Cubical.Data.List using (List; []; _∷_; _++_)
import formalization.Library.QuotientBool as QB
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Functions.Surjection using (isSurjection ; compSurjection)
open import formalization.Library.BooleanRing.FreeBooleanRing.freeBATerms using (includeBATermsSurj ; freeBATerms)
open import formalization.Library.BooleanRing.FreeBooleanRing.SurjectiveTerms using (Tvar; Tconst; _+T_; -T_; _·T_)

private
  opaque
    unfolding freeBA
    unfolding includeBATermsSurj
    unfolding generator
    includeBATerms-Tvar : (n : ℕ) → fst includeBATermsSurj (Tvar n) ≡ generator n
    includeBATerms-Tvar n = refl
    includeBATerms-0 : fst (includeBATermsSurj {A = ℕ}) (Tconst false) ≡ BooleanRingStr.𝟘 (snd (freeBA ℕ))
    includeBATerms-0 = refl
    includeBATerms-1 : fst (includeBATermsSurj {A = ℕ}) (Tconst true) ≡ BooleanRingStr.𝟙 (snd (freeBA ℕ))
    includeBATerms-1 = refl
    includeBATerms-+ : (t s : freeBATerms ℕ) → fst includeBATermsSurj (t +T s) ≡ BooleanRingStr._+_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s)
    includeBATerms-+ t s = refl
    includeBATerms-· : (t s : freeBATerms ℕ) → fst includeBATermsSurj (t ·T s) ≡ BooleanRingStr._·_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s)
    includeBATerms-· t s = refl
    includeBATerms-- : (t : freeBATerms ℕ) → fst includeBATermsSurj (-T t) ≡ BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj t)
    includeBATerms-- t = refl

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
    ≡⟨ cong (fst π∞) (BooleanAlgebraStr.-IsId (freeBA ℕ) {x = fst includeBATermsSurj t}) ⟩
  fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj t))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-- t)) ⟩
  π∞-from-terms (-T t) ∎
interpretB∞-eq-composition (t ·T s) =
  interpretB∞ t ·∞ interpretB∞ s
    ≡⟨ cong₂ _·∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t ·∞ π∞-from-terms s
    ≡⟨ sym (π∞-· (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._·_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-· t s)) ⟩
  π∞-from-terms (t ·T s) ∎

interpretB∞-surjective : isSurjection interpretB∞
interpretB∞-surjective x =
  PT.map (λ { (t , eq) → t , interpretB∞-eq-composition t ∙ eq }) (π∞-includeTerms-surj x)

open import Cubical.Data.Nat using (discreteℕ)

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

private
  module BA∞ = BooleanAlgebraStr B∞
  +B∞-IdR = BooleanRingStr.+IdR (snd B∞)
  +B∞-IdL = BooleanRingStr.+IdL (snd B∞)
  ·B∞-IdR = BooleanRingStr.·IdR (snd B∞)
  ·B∞-Assoc = BooleanRingStr.·Assoc (snd B∞)
  +B∞-Assoc = BooleanRingStr.+Assoc (snd B∞)
  +B∞-Comm = BooleanRingStr.+Comm (snd B∞)
  ·B∞-Comm = BooleanRingStr.·Comm (snd B∞)
  ·B∞-DistR+ = BooleanRingStr.·DistR+ (snd B∞)
gen-in-finJoin : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ true → g∞ n ·∞ finJoin∞ ms ≡ g∞ n
gen-in-finJoin n [] prf = ex-falso (false≢true prf)
gen-in-finJoin n (m ∷ ms) prf with discreteℕ n m
... | yes n≡m =
  g∞ n ·∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ cong (λ x → g∞ n ·∞ (g∞ x ∨∞ finJoin∞ ms)) (sym n≡m) ⟩
  g∞ n ·∞ (g∞ n ∨∞ finJoin∞ ms)
    ≡⟨ BA∞.∧AbsorbL∨ ⟩
  g∞ n ∎
... | no n≢m =
  g∞ n ·∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ BA∞.∧DistR∨ ⟩
  (g∞ n ·∞ g∞ m) ∨∞ (g∞ n ·∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-distinct-mult-zero n m n≢m) (gen-in-finJoin n ms prf) ⟩
  𝟘∞ ∨∞ g∞ n
    ≡⟨ zero-join-left (g∞ n) ⟩
  g∞ n ∎

gen-notin-finJoin : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ false → g∞ n ·∞ finJoin∞ ms ≡ 𝟘∞
gen-notin-finJoin n [] _ = 0∞-absorbs-right (g∞ n)
gen-notin-finJoin n (m ∷ ms) prf with discreteℕ n m
... | yes _ = ex-falso (true≢false prf)
... | no n≢m =
  g∞ n ·∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ BA∞.∧DistR∨ ⟩
  (g∞ n ·∞ g∞ m) ∨∞ (g∞ n ·∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-distinct-mult-zero n m n≢m) (gen-notin-finJoin n ms prf) ⟩
  𝟘∞ ∨∞ 𝟘∞
    ≡⟨ zero-join-left 𝟘∞ ⟩
  𝟘∞ ∎

finJoin∞-∩L : (ns ms : List ℕ) → finJoin∞ (ns ∩L ms) ≡ finJoin∞ ns ·∞ finJoin∞ ms
finJoin∞-∩L [] ms = sym (0∞-absorbs-left (finJoin∞ ms))
finJoin∞-∩L (n ∷ ns) ms with n ∈? ms in eq
... | true =
  g∞ n ∨∞ finJoin∞ (ns ∩L ms)
    ≡⟨ cong (g∞ n ∨∞_) (finJoin∞-∩L ns ms) ⟩
  g∞ n ∨∞ (finJoin∞ ns ·∞ finJoin∞ ms)
    ≡⟨ cong (_∨∞ (finJoin∞ ns ·∞ finJoin∞ ms)) (sym (gen-in-finJoin n ms (builtin→Path-Bool eq))) ⟩
  (g∞ n ·∞ finJoin∞ ms) ∨∞ (finJoin∞ ns ·∞ finJoin∞ ms)
    ≡⟨ sym BA∞.∧DistL∨ ⟩
  (g∞ n ∨∞ finJoin∞ ns) ·∞ finJoin∞ ms ∎
... | false =
  finJoin∞ (ns ∩L ms)
    ≡⟨ finJoin∞-∩L ns ms ⟩
  finJoin∞ ns ·∞ finJoin∞ ms
    ≡⟨ sym (zero-join-left (finJoin∞ ns ·∞ finJoin∞ ms)) ⟩
  𝟘∞ ∨∞ (finJoin∞ ns ·∞ finJoin∞ ms)
    ≡⟨ cong (_∨∞ (finJoin∞ ns ·∞ finJoin∞ ms)) (sym (gen-notin-finJoin n ms (builtin→Path-Bool eq))) ⟩
  (g∞ n ·∞ finJoin∞ ms) ∨∞ (finJoin∞ ns ·∞ finJoin∞ ms)
    ≡⟨ sym BA∞.∧DistL∨ ⟩
  (g∞ n ∨∞ finJoin∞ ns) ·∞ finJoin∞ ms ∎

absorb→neg-zero : {a b : ⟨ B∞ ⟩} → a ·∞ b ≡ a → a ·∞ (¬∞ b) ≡ 𝟘∞
absorb→neg-zero {a} {b} ab≡a =
  a ·∞ (𝟙∞ +∞ b)         ≡⟨ ·B∞-DistR+ a 𝟙∞ b ⟩
  a ·∞ 𝟙∞ +∞ a ·∞ b     ≡⟨ cong₂ _+∞_ (·B∞-IdR a) ab≡a ⟩
  a +∞ a                  ≡⟨ BA∞.characteristic2 ⟩
  𝟘∞ ∎

orthog→neg-absorb : {a b : ⟨ B∞ ⟩} → a ·∞ b ≡ 𝟘∞ → a ·∞ (¬∞ b) ≡ a
orthog→neg-absorb {a} {b} ab≡0 =
  a ·∞ (𝟙∞ +∞ b)         ≡⟨ ·B∞-DistR+ a 𝟙∞ b ⟩
  a ·∞ 𝟙∞ +∞ a ·∞ b     ≡⟨ cong₂ _+∞_ (·B∞-IdR a) ab≡0 ⟩
  a +∞ 𝟘∞                ≡⟨ +B∞-IdR a ⟩
  a ∎

finJoin∞-∖L : (ns ms : List ℕ) → finJoin∞ (ns ∖L ms) ≡ finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms)
finJoin∞-∖L [] ms = sym (0∞-absorbs-left (¬∞ (finJoin∞ ms)))
finJoin∞-∖L (n ∷ ns) ms with n ∈? ms in eq
... | true =
  finJoin∞ (ns ∖L ms)
    ≡⟨ finJoin∞-∖L ns ms ⟩
  finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms)
    ≡⟨ sym (zero-join-left (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms))) ⟩
  𝟘∞ ∨∞ (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms))
    ≡⟨ cong (_∨∞ (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms)))
         (sym (absorb→neg-zero (gen-in-finJoin n ms (builtin→Path-Bool eq)))) ⟩
  (g∞ n ·∞ ¬∞ (finJoin∞ ms)) ∨∞ (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms))
    ≡⟨ sym BA∞.∧DistL∨ ⟩
  (g∞ n ∨∞ finJoin∞ ns) ·∞ ¬∞ (finJoin∞ ms) ∎
... | false =
  g∞ n ∨∞ finJoin∞ (ns ∖L ms)
    ≡⟨ cong (g∞ n ∨∞_) (finJoin∞-∖L ns ms) ⟩
  g∞ n ∨∞ (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms))
    ≡⟨ cong (_∨∞ (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms)))
         (sym (orthog→neg-absorb (gen-notin-finJoin n ms (builtin→Path-Bool eq)))) ⟩
  (g∞ n ·∞ ¬∞ (finJoin∞ ms)) ∨∞ (finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms))
    ≡⟨ sym BA∞.∧DistL∨ ⟩
  (g∞ n ∨∞ finJoin∞ ns) ·∞ ¬∞ (finJoin∞ ms) ∎

deMorgan-finMeetNeg : (ns : List ℕ) → finMeetNeg∞ ns ≡ ¬∞ (finJoin∞ ns)
deMorgan-finMeetNeg [] = sym (+B∞-IdR 𝟙∞)
deMorgan-finMeetNeg (n ∷ ns) =
  (¬∞ g∞ n) ·∞ finMeetNeg∞ ns
    ≡⟨ cong ((¬∞ g∞ n) ·∞_) (deMorgan-finMeetNeg ns) ⟩
  (¬∞ g∞ n) ·∞ (¬∞ (finJoin∞ ns))
    ≡⟨ sym BA∞.DeMorgan¬∨ ⟩
  ¬∞ (g∞ n ∨∞ finJoin∞ ns) ∎

finJoin∞-++ : (ns ms : List ℕ) → finJoin∞ (ns ++ ms) ≡ finJoin∞ ns ∨∞ finJoin∞ ms
finJoin∞-++ [] ms = sym (zero-join-left (finJoin∞ ms))
finJoin∞-++ (n ∷ ns) ms =
  g∞ n ∨∞ finJoin∞ (ns ++ ms)
    ≡⟨ cong (g∞ n ∨∞_) (finJoin∞-++ ns ms) ⟩
  g∞ n ∨∞ (finJoin∞ ns ∨∞ finJoin∞ ms)
    ≡⟨ BA∞.∨Assoc ⟩
  (g∞ n ∨∞ finJoin∞ ns) ∨∞ finJoin∞ ms ∎

∨·¬∧≡+ : (a b : ⟨ B∞ ⟩) → (a ∨∞ b) ·∞ ¬∞ (a ·∞ b) ≡ a +∞ b
∨·¬∧≡+ a b =
  (a ∨∞ b) ·∞ ¬∞ (a ·∞ b)
    ≡⟨ ·B∞-DistR+ (a ∨∞ b) 𝟙∞ (a ·∞ b) ⟩
  (a ∨∞ b) ·∞ 𝟙∞ +∞ (a ∨∞ b) ·∞ (a ·∞ b)
    ≡⟨ cong (_+∞ (a ∨∞ b) ·∞ (a ·∞ b)) (·B∞-IdR (a ∨∞ b)) ⟩
  (a ∨∞ b) +∞ (a ∨∞ b) ·∞ (a ·∞ b)
    ≡⟨ cong ((a ∨∞ b) +∞_) (·B∞-Assoc (a ∨∞ b) a b ∙ cong (_·∞ b) (·B∞-Comm (a ∨∞ b) a ∙ BA∞.∧AbsorbL∨)) ⟩
  (a ∨∞ b) +∞ (a ·∞ b)
    ≡⟨ sym (+B∞-Assoc (a +∞ b) (a ·∞ b) (a ·∞ b)) ⟩
  (a +∞ b) +∞ ((a ·∞ b) +∞ (a ·∞ b))
    ≡⟨ cong ((a +∞ b) +∞_) BA∞.characteristic2 ⟩
  (a +∞ b) +∞ 𝟘∞
    ≡⟨ +B∞-IdR (a +∞ b) ⟩
  a +∞ b ∎

finJoin∞-△L : (ns ms : List ℕ) → finJoin∞ (ns △L ms) ≡ finJoin∞ ns +∞ finJoin∞ ms
finJoin∞-△L ns ms =
  finJoin∞ ((ns ++ ms) ∖L (ns ∩L ms))
    ≡⟨ finJoin∞-∖L (ns ++ ms) (ns ∩L ms) ⟩
  finJoin∞ (ns ++ ms) ·∞ ¬∞ (finJoin∞ (ns ∩L ms))
    ≡⟨ cong₂ (λ x y → x ·∞ ¬∞ y) (finJoin∞-++ ns ms) (finJoin∞-∩L ns ms) ⟩
  (finJoin∞ ns ∨∞ finJoin∞ ms) ·∞ ¬∞ (finJoin∞ ns ·∞ finJoin∞ ms)
    ≡⟨ ∨·¬∧≡+ (finJoin∞ ns) (finJoin∞ ms) ⟩
  finJoin∞ ns +∞ finJoin∞ ms ∎

meet-nf-correct : (nf₁ nf₂ : B∞-NormalForm) → ⟦ meet-nf nf₁ nf₂ ⟧nf ≡ ⟦ nf₁ ⟧nf ·∞ ⟦ nf₂ ⟧nf
meet-nf-correct (joinForm ns) (joinForm ms) = finJoin∞-∩L ns ms
meet-nf-correct (joinForm ns) (meetNegForm ms) =
  finJoin∞ (ns ∖L ms)
    ≡⟨ finJoin∞-∖L ns ms ⟩
  finJoin∞ ns ·∞ ¬∞ (finJoin∞ ms)
    ≡⟨ cong (finJoin∞ ns ·∞_) (sym (deMorgan-finMeetNeg ms)) ⟩
  finJoin∞ ns ·∞ finMeetNeg∞ ms ∎
meet-nf-correct (meetNegForm ns) (joinForm ms) =
  finJoin∞ (ms ∖L ns)
    ≡⟨ finJoin∞-∖L ms ns ⟩
  finJoin∞ ms ·∞ ¬∞ (finJoin∞ ns)
    ≡⟨ cong (finJoin∞ ms ·∞_) (sym (deMorgan-finMeetNeg ns)) ⟩
  finJoin∞ ms ·∞ finMeetNeg∞ ns
    ≡⟨ ·B∞-Comm (finJoin∞ ms) (finMeetNeg∞ ns) ⟩
  finMeetNeg∞ ns ·∞ finJoin∞ ms ∎
meet-nf-correct (meetNegForm ns) (meetNegForm ms) =
  finMeetNeg∞ (ns ++ ms)
    ≡⟨ deMorgan-finMeetNeg (ns ++ ms) ⟩
  ¬∞ (finJoin∞ (ns ++ ms))
    ≡⟨ cong ¬∞_ (finJoin∞-++ ns ms) ⟩
  ¬∞ (finJoin∞ ns ∨∞ finJoin∞ ms)
    ≡⟨ BA∞.DeMorgan¬∨ ⟩
  (¬∞ finJoin∞ ns) ·∞ (¬∞ finJoin∞ ms)
    ≡⟨ cong₂ _·∞_ (sym (deMorgan-finMeetNeg ns)) (sym (deMorgan-finMeetNeg ms)) ⟩
  finMeetNeg∞ ns ·∞ finMeetNeg∞ ms ∎

private
  ¬∞-+∞-left : (a b : ⟨ B∞ ⟩) → ¬∞ (a +∞ b) ≡ a +∞ ¬∞ b
  ¬∞-+∞-left a b =
    ¬∞ (a +∞ b)
      ≡⟨ +B∞-Assoc 𝟙∞ a b ⟩
    (𝟙∞ +∞ a) +∞ b
      ≡⟨ cong (_+∞ b) (+B∞-Comm 𝟙∞ a) ⟩
    (a +∞ 𝟙∞) +∞ b
      ≡⟨ sym (+B∞-Assoc a 𝟙∞ b) ⟩
    a +∞ ¬∞ b ∎

  ¬∞-+∞-cancel : (a b : ⟨ B∞ ⟩) → ¬∞ a +∞ ¬∞ b ≡ a +∞ b
  ¬∞-+∞-cancel a b =
    (𝟙∞ +∞ a) +∞ (𝟙∞ +∞ b)
      ≡⟨ +B∞-Assoc (𝟙∞ +∞ a) 𝟙∞ b ⟩
    ((𝟙∞ +∞ a) +∞ 𝟙∞) +∞ b
      ≡⟨ cong (_+∞ b) (sym (+B∞-Assoc 𝟙∞ a 𝟙∞)
                        ∙ cong (𝟙∞ +∞_) (+B∞-Comm a 𝟙∞)
                        ∙ +B∞-Assoc 𝟙∞ 𝟙∞ a
                        ∙ cong (_+∞ a) BA∞.characteristic2
                        ∙ +B∞-IdL a) ⟩
    a +∞ b ∎

xor-nf-correct : (nf₁ nf₂ : B∞-NormalForm) → ⟦ xor-nf nf₁ nf₂ ⟧nf ≡ ⟦ nf₁ ⟧nf +∞ ⟦ nf₂ ⟧nf
xor-nf-correct (joinForm ns) (joinForm ms) = finJoin∞-△L ns ms
xor-nf-correct (joinForm ns) (meetNegForm ms) =
  finMeetNeg∞ (ns △L ms)
    ≡⟨ deMorgan-finMeetNeg (ns △L ms) ⟩
  ¬∞ (finJoin∞ (ns △L ms))
    ≡⟨ cong ¬∞_ (finJoin∞-△L ns ms) ⟩
  ¬∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ ¬∞-+∞-left (finJoin∞ ns) (finJoin∞ ms) ⟩
  finJoin∞ ns +∞ ¬∞ (finJoin∞ ms)
    ≡⟨ cong (finJoin∞ ns +∞_) (sym (deMorgan-finMeetNeg ms)) ⟩
  finJoin∞ ns +∞ finMeetNeg∞ ms ∎
xor-nf-correct (meetNegForm ns) (joinForm ms) =
  finMeetNeg∞ (ms △L ns)
    ≡⟨ deMorgan-finMeetNeg (ms △L ns) ⟩
  ¬∞ (finJoin∞ (ms △L ns))
    ≡⟨ cong ¬∞_ (finJoin∞-△L ms ns) ⟩
  ¬∞ (finJoin∞ ms +∞ finJoin∞ ns)
    ≡⟨ cong (𝟙∞ +∞_) (+B∞-Comm (finJoin∞ ms) (finJoin∞ ns)) ⟩
  𝟙∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ +B∞-Assoc 𝟙∞ (finJoin∞ ns) (finJoin∞ ms) ⟩
  (𝟙∞ +∞ finJoin∞ ns) +∞ finJoin∞ ms
    ≡⟨ cong (_+∞ finJoin∞ ms) (sym (deMorgan-finMeetNeg ns)) ⟩
  finMeetNeg∞ ns +∞ finJoin∞ ms ∎
xor-nf-correct (meetNegForm ns) (meetNegForm ms) =
  finJoin∞ (ns △L ms)
    ≡⟨ finJoin∞-△L ns ms ⟩
  finJoin∞ ns +∞ finJoin∞ ms
    ≡⟨ sym (¬∞-+∞-cancel (finJoin∞ ns) (finJoin∞ ms)) ⟩
  ¬∞ (finJoin∞ ns) +∞ ¬∞ (finJoin∞ ms)
    ≡⟨ cong₂ _+∞_ (sym (deMorgan-finMeetNeg ns)) (sym (deMorgan-finMeetNeg ms)) ⟩
  finMeetNeg∞ ns +∞ finMeetNeg∞ ms ∎

normalizeTerm-correct : (t : freeBATerms ℕ) → ⟦ normalizeTerm t ⟧nf ≡ interpretB∞ t
normalizeTerm-correct (Tvar n) = zero-join-right (g∞ n)
normalizeTerm-correct (Tconst false) = refl
normalizeTerm-correct (Tconst true) = refl
normalizeTerm-correct (-T t) = normalizeTerm-correct t
normalizeTerm-correct (t +T s) =
  ⟦ xor-nf (normalizeTerm t) (normalizeTerm s) ⟧nf
    ≡⟨ xor-nf-correct (normalizeTerm t) (normalizeTerm s) ⟩
  ⟦ normalizeTerm t ⟧nf +∞ ⟦ normalizeTerm s ⟧nf
    ≡⟨ cong₂ _+∞_ (normalizeTerm-correct t) (normalizeTerm-correct s) ⟩
  interpretB∞ t +∞ interpretB∞ s ∎
normalizeTerm-correct (t ·T s) =
  ⟦ meet-nf (normalizeTerm t) (normalizeTerm s) ⟧nf
    ≡⟨ meet-nf-correct (normalizeTerm t) (normalizeTerm s) ⟩
  ⟦ normalizeTerm t ⟧nf ·∞ ⟦ normalizeTerm s ⟧nf
    ≡⟨ cong₂ _·∞_ (normalizeTerm-correct t) (normalizeTerm-correct s) ⟩
  interpretB∞ t ·∞ interpretB∞ s ∎

normalFormExists-trunc : (x : ⟨ B∞ ⟩) → ∥ Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ x ∥₁
normalFormExists-trunc x = PT.map
  (λ pair → normalizeTerm (fst pair) , normalizeTerm-correct (fst pair) ∙ snd pair)
  (interpretB∞-surjective x)

char2-B∞ : (x : ⟨ B∞ ⟩) → x +∞ x ≡ 𝟘∞
char2-B∞ x = BooleanAlgebraStr.characteristic2 B∞ {x}

char2-B∞×B∞ : (z : ⟨ B∞×B∞ ⟩) → z +× z ≡ (𝟘∞ , 𝟘∞)
char2-B∞×B∞ (a , b) = cong₂ _,_ (char2-B∞ a) (char2-B∞ b)

module φ-injectivity where
  open B∞→FinCof using (φ)
  open import Cubical.Data.Nat.Properties using (max)
  open import Cubical.Data.Nat.Order using (left-≤-max; right-≤-max; ≤-suc; ¬m<m; ≤-antisym; <-asym'; _≤_)
  open import Cubical.Data.Bool using (_and_; _or_; not)

  private
    isSetB∞ : isSet ⟨ B∞ ⟩
    isSetB∞ = BooleanRingStr.is-set (snd B∞)

  listMax : List ℕ → ℕ
  listMax [] = 0
  listMax (n ∷ ns) = max (suc n) (listMax ns)

  m≠n→decToBool-not : (m n : ℕ) → ¬ (m ≡ n) → not (decToBool (discreteℕ m n)) ≡ true
  m≠n→decToBool-not m n m≠n with discreteℕ m n
  ... | yes p = ex-falso (m≠n p)
  ... | no _ = refl

  notMemberOf-fresh : (ns : List ℕ) (m : ℕ) → listMax ns ≤ m → notMemberOf ns m ≡ true
  notMemberOf-fresh [] m _ = refl
  notMemberOf-fresh (k ∷ ns) m lm≤m =
    let sk≤m : suc k ≤ m
        sk≤m = ≤-trans (left-≤-max {m = suc k} {n = listMax ns}) lm≤m
        m≠k : ¬ (m ≡ k)
        m≠k p = ¬m<m (subst (suc k ≤_) p sk≤m)
        rest≤m : listMax ns ≤ m
        rest≤m = ≤-trans (right-≤-max {n = listMax ns} {m = suc k}) lm≤m
    in cong₂ _and_ (m≠n→decToBool-not m k m≠k) (notMemberOf-fresh ns m rest≤m)
    where open import Cubical.Data.Nat.Order using (≤-trans; ≤-refl)

  opaque
    unfolding φ-pres-finJoin
    φ-finJoin-kernel : (ns : List ℕ) → fst φ (finJoin∞ ns) ≡ fcEmpty → finJoin∞ ns ≡ 𝟘∞
    φ-finJoin-kernel [] _ = refl
    φ-finJoin-kernel (n ∷ ns) p = ex-falso (true≢false (sym at-n≡true ∙ at-n≡false))
      where
      at-n≡false : fst (fst φ (finJoin∞ (n ∷ ns))) n ≡ false
      at-n≡false = cong (λ z → fst z n) p
      at-n≡true : fst (fst φ (finJoin∞ (n ∷ ns))) n ≡ true
      at-n≡true =
        fst (fst φ (finJoin∞ (n ∷ ns))) n
          ≡⟨ cong (λ z → fst z n) (φ-pres-finJoin (n ∷ ns)) ⟩
        fst (fcFinJoin (n ∷ ns)) n
          ≡⟨ fcFinJoin-eval (n ∷ ns) n ⟩
        decToBool (discreteℕ n n) or memberOf ns n
          ≡⟨ cong (_or memberOf ns n) (fcSingleton-self n) ⟩
        true or memberOf ns n ∎

  opaque
    unfolding φ-pres-finMeetNeg
    φ-finMeetNeg-kernel : (ns : List ℕ) → ¬ (fst φ (finMeetNeg∞ ns) ≡ fcEmpty)
    φ-finMeetNeg-kernel ns p = true≢false (sym at-m≡true ∙ at-m≡false)
      where
      m : ℕ
      m = listMax ns
      at-m≡false : fst (fst φ (finMeetNeg∞ ns)) m ≡ false
      at-m≡false = cong (λ z → fst z m) p
      at-m≡true : fst (fst φ (finMeetNeg∞ ns)) m ≡ true
      at-m≡true =
        fst (fst φ (finMeetNeg∞ ns)) m
          ≡⟨ cong (λ z → fst z m) (φ-pres-finMeetNeg ns) ⟩
        fst (fcFinMeetNeg ns) m
          ≡⟨ fcFinMeetNeg-eval ns m ⟩
        notMemberOf ns m
          ≡⟨ notMemberOf-fresh ns m ≤-refl ⟩
        true ∎
        where open import Cubical.Data.Nat.Order using (≤-refl)

  φ-nf-kernel : (nf : B∞-NormalForm) → fst φ ⟦ nf ⟧nf ≡ fcEmpty → ⟦ nf ⟧nf ≡ 𝟘∞
  φ-nf-kernel (joinForm ns) = φ-finJoin-kernel ns
  φ-nf-kernel (meetNegForm ns) p = ex-falso (φ-finMeetNeg-kernel ns p)

  φ-kernel-trivial : (x : ⟨ B∞ ⟩) → fst φ x ≡ fcEmpty → x ≡ 𝟘∞
  φ-kernel-trivial x φx≡0 = PT.rec (isSetB∞ x 𝟘∞)
    (λ (nf , nf≡x) → sym nf≡x ∙ φ-nf-kernel nf (cong (fst φ) nf≡x ∙ φx≡0))
    (normalFormExists-trunc x)

  char2-eq : (a b : ⟨ B∞ ⟩) → a +∞ b ≡ 𝟘∞ → a ≡ b
  char2-eq a b p =
    a               ≡⟨ sym (+B∞-IdR a) ⟩
    a +∞ 𝟘∞         ≡⟨ cong (a +∞_) (sym (char2-B∞ b)) ⟩
    a +∞ (b +∞ b)   ≡⟨ +B∞-Assoc a b b ⟩
    (a +∞ b) +∞ b   ≡⟨ cong (_+∞ b) p ⟩
    𝟘∞ +∞ b         ≡⟨ +B∞-IdL b ⟩
    b ∎

  φ-inj : (x y : ⟨ B∞ ⟩) → fst φ x ≡ fst φ y → x ≡ y
  φ-inj x y p = char2-eq x y (φ-kernel-trivial (x +∞ y) φ-sum-eq-0)
    where
    φ-sum-eq-0 : fst φ (x +∞ y) ≡ fcEmpty
    φ-sum-eq-0 =
      fst φ (x +∞ y)
        ≡⟨ IsCommRingHom.pres+ (snd φ) x y ⟩
      fcXor (fst φ x) (fst φ y)
        ≡⟨ cong (λ z → fcXor (fst φ x) z) (sym p) ⟩
      fcXor (fst φ x) (fst φ x)
        ≡⟨ BooleanAlgebraStr.characteristic2 FinCofBR {fst φ x} ⟩
      fcEmpty ∎

  ψ∘φ-proved : (x : ⟨ B∞ ⟩) → FinCof→B∞.ψ-fun (fst φ x) ≡ x
  ψ∘φ-proved x = φ-inj (FinCof→B∞.ψ-fun (fst φ x)) x (φ∘ψ (fst φ x))

open φ-injectivity public using (ψ∘φ-proved; φ-inj)

open import formalization.Library.CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv)
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv)
private
  φ' = B∞→FinCof.φ

B∞≅FinCofBR : BooleanRingEquiv B∞ FinCofBR
B∞≅FinCofBR = (fst φ' , isoToIsEquiv (iso (fst φ') FinCof→B∞.ψ-fun φ∘ψ ψ∘φ-proved)) , snd φ'
