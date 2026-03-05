{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module formalization.StoneDuality.NFinCofin.Presentation where

open import formalization.StoneDuality.NFinCofin.Definitions

open import formalization.Library.BooleanRing.BooleanRingMaps
open import formalization.Library.QuickFixes using (mkBooleanRingEquiv)
open import formalization.Library.BooleanRing.SubBooleanRing
open import formalization.Library.BooleanRing.AlgebraicFacts
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool
  using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import formalization.Library.BasicDefinitions

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing

open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Data.Bool renaming (_≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true; or-identityʳ; notnot; and-zeroʳ; and-comm)
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)

import Cubical.HITs.SetQuotients as SQ

-- ===== Abbreviations =====
private
  module FC = BooleanRingStr (snd ℕfinCofinBA)
  module FCAlg = BooleanAlgebraStr (snd ℕfinCofinBA)
  module Free = BooleanRingStr (snd (freeBA ℕ))
  module FreeAlg = BooleanAlgebraStr (snd (freeBA ℕ))

open FC using () renaming (_+_ to _+fc_ ; _·_ to _·fc_ ; 𝟘 to 𝟘fc ; 𝟙 to 𝟙fc ; is-set to isSetFC)
open FCAlg using () renaming (_∧_ to _∧fc_ ; _∨_ to _∨fc_ ; ¬_ to ¬fc_)
open Free using () renaming (_+_ to _+free_ ; _·_ to _·free_ ; 𝟘 to 𝟘free ; 𝟙 to 𝟙free)
open FreeAlg using () renaming (_∧_ to _∧free_ ; _∨_ to _∨free_ ; ¬_ to ¬free_)

FC≡ : {a b : ⟨ ℕfinCofinBA ⟩} → fst a ≡ fst b → a ≡ b
FC≡ = Σ≡Prop isPropisFiniteOrCofinite

-- ===== Delta sequence facts =====

δnn=1 : (n : ℕ) → δSequence n n ≡ true
δnn=1 zero = refl
δnn=1 (suc n) = δnn=1 n

pred≢ℕ : (n m : ℕ) → (suc n ≡ suc m → ⊥) → (n ≡ m → ⊥)
pred≢ℕ n m sn≢sm n=m = sn≢sm (cong suc n=m)

δnm=0 : (n m : ℕ) → (n ≡ m → ⊥) → δSequence n m ≡ false
δnm=0 zero zero x = ex-falso (x refl)
δnm=0 zero (suc m) x = refl
δnm=0 (suc n) zero x = refl
δnm=0 (suc n) (suc m) x = δnm=0 n m (pred≢ℕ n m x)

δn∧δm=0 : (n m : ℕ) → (n ≡ m → ⊥) → (k : ℕ) → (δSequence n k) and (δSequence m k) ≡ false
δn∧δm=0 zero zero n≠m _ = ex-falso (n≠m refl)
δn∧δm=0 zero _ n≠m (suc k) = refl
δn∧δm=0 (suc n) _ n≠m zero = refl
δn∧δm=0 _ (suc m) n≠m zero = and-zeroʳ _
δn∧δm=0 _ zero n≠m (suc k) = and-zeroʳ _
δn∧δm=0 (suc n) (suc m) n≠m (suc k) = δn∧δm=0 n m (pred≢ℕ n m n≠m) k

δSequenceFinite : (n : ℕ) → isFinite (δSequence n)
δSequenceFinite n = last1 n (δnn=1 n) λ k k>n → δnm=0 n k (<→≢ k>n)

singleton : (n : ℕ) → ⟨ ℕfinCofinBA ⟩
singleton n = δSequence n , Fin (δSequenceFinite n)

-- ===== Homomorphism from free algebra to ℕfinCofinBA =====

freeℕ→ℕFinCof : BoolHom (freeBA ℕ) ℕfinCofinBA
freeℕ→ℕFinCof = inducedBAHom ℕ ℕfinCofinBA singleton

private
  module FH = IsCommRingHom (snd freeℕ→ℕFinCof)

  eval-gen : (n : ℕ) → fst freeℕ→ℕFinCof (generator n) ≡ singleton n
  eval-gen n = funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n

-- ===== Relations =====

relations : ℕ × ℕ → ⟨ freeBA ℕ ⟩
relations (n , m) with discreteℕ n m
... | yes _ = 𝟘free
... | no ¬p = generator n ∧free generator m

relationsRespected : ∀ (p : ℕ × ℕ) → freeℕ→ℕFinCof $cr (relations p) ≡ 𝟘fc
relationsRespected (n , m) with discreteℕ n m
... | yes _ = FH.pres0
... | no ¬p =
  FH.pres· (generator n) (generator m)
  ∙ cong₂ _·fc_ (eval-gen n) (eval-gen m)
  ∙ FC≡ (funExt (δn∧δm=0 n m ¬p))

-- ===== The presentation =====

presentation : BooleanRing ℓ-zero
presentation = (freeBA ℕ) QB./Im relations

π : BoolHom (freeBA ℕ) presentation
π = QB.quotientImageHom

private
  module P = BooleanRingStr (snd presentation)
open P using () renaming (_+_ to _+Q_ ; _·_ to _·Q_ ; 𝟘 to 𝟘Q ; 𝟙 to 𝟙Q ; is-set to isSetQ)

-- ===== Forward map: presentation → ℕfinCofinBA =====

presentation→ℕFinCof : BoolHom presentation ℕfinCofinBA
presentation→ℕFinCof = QB.inducedHom ℕfinCofinBA freeℕ→ℕFinCof relationsRespected

opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  p→fc∘π≡fH : presentation→ℕFinCof ∘cr π ≡ freeℕ→ℕFinCof
  p→fc∘π≡fH = QB.evalInduce ℕfinCofinBA

-- ===== Inverse map: ℕfinCofinBA → presentation =====

singleEntry : (α : binarySequence) → (m : ℕ) → ⟨ freeBA ℕ ⟩
singleEntry α m = if α m then generator m else 𝟘free

embedUpTo : (α : binarySequence) → (m : ℕ) → ⟨ freeBA ℕ ⟩
embedUpTo α zero = singleEntry α 0
embedUpTo α (suc m) = embedUpTo α m ∨free singleEntry α (suc m)

Finite→FreeℕMap : (α : binarySequence) → isFinite α → ⟨ freeBA ℕ ⟩
Finite→FreeℕMap α (constant0 _) = 𝟘free
Finite→FreeℕMap α (last1 n _ _) = embedUpTo α n

ℕFinCof→FreeℕMap : ⟨ ℕfinCofinBA ⟩ → ⟨ freeBA ℕ ⟩
ℕFinCof→FreeℕMap (α , Fin αf) = Finite→FreeℕMap α αf
ℕFinCof→FreeℕMap (α , Cof αc) = ¬free (Finite→FreeℕMap (¬ α) αc)

ℕFinCof→Presentation : ⟨ ℕfinCofinBA ⟩ → ⟨ presentation ⟩
ℕFinCof→Presentation = fst π ∘ ℕFinCof→FreeℕMap

-- ===== Section property: freeℕ→ℕFinCof ∘ ℕFinCof→FreeℕMap = id =====

-- freeℕ→ℕFinCof preserves ∨ and ¬ (as a ring hom)
private
  fH-pres-∨ : (a b : ⟨ freeBA ℕ ⟩) →
    fst freeℕ→ℕFinCof (a ∨free b) ≡ fst freeℕ→ℕFinCof a ∨fc fst freeℕ→ℕFinCof b
  fH-pres-∨ a b =
    FH.pres+ (a +free b) (a ·free b)
    ∙ cong₂ _+fc_ (FH.pres+ a b) (FH.pres· a b)

  fH-pres-¬ : (a : ⟨ freeBA ℕ ⟩) → fst freeℕ→ℕFinCof (¬free a) ≡ ¬fc (fst freeℕ→ℕFinCof a)
  fH-pres-¬ a = FH.pres+ 𝟙free a ∙ cong (_+fc fst freeℕ→ℕFinCof a) FH.pres1

-- Helper: the ∨ on ℕfinCofinBA agrees with `or` pointwise
∨fc-pointwise : (a b : ⟨ ℕfinCofinBA ⟩) (k : ℕ) →
  fst (a ∨fc b) k ≡ fst a k or fst b k
∨fc-pointwise a b k = QuickBooleanFix.claim (fst a k) (fst b k)

¬fc-pointwise : (a : ⟨ ℕfinCofinBA ⟩) (k : ℕ) →
  fst (¬fc a) k ≡ not (fst a k)
¬fc-pointwise a k = refl

∨fc-zero-l : (a : ⟨ ℕfinCofinBA ⟩) → 𝟘fc ∨fc a ≡ a
∨fc-zero-l a = FCAlg.∨IdL

∨fc-zero-r : (a : ⟨ ℕfinCofinBA ⟩) → a ∨fc 𝟘fc ≡ a
∨fc-zero-r a = FCAlg.∨IdR

-- Key: evaluating singleEntry on freeℕ→ℕFinCof
eval-singleEntry-true : (m : ℕ) → (α : binarySequence) → α m ≡ true →
  fst freeℕ→ℕFinCof (singleEntry α m) ≡ singleton m
eval-singleEntry-true m α αm=t with α m
... | true = eval-gen m
... | false = ex-falso (false≢true αm=t)

eval-singleEntry-false : (m : ℕ) → (α : binarySequence) → α m ≡ false →
  fst freeℕ→ℕFinCof (singleEntry α m) ≡ 𝟘fc
eval-singleEntry-false m α αm=f with α m
... | false = FH.pres0
... | true = ex-falso (true≢false αm=f)

-- Key evaluation lemma: embedUpTo, at the pointwise level
-- We prove two pointwise lemmas, then derive the main result.

open import Cubical.Data.Nat.Properties using (snotz; injSuc)

-- Helper: fH(singleEntry α m) is false at k when m ≠ k
eval-singleEntry-neq : (m k : ℕ) (α : binarySequence) → (m ≡ k → ⊥) →
  fst (fst freeℕ→ℕFinCof (singleEntry α m)) k ≡ false
eval-singleEntry-neq m k α m≠k with α m
... | true  = funExt⁻ (cong fst (eval-gen m)) k ∙ δnm=0 m k m≠k
... | false = funExt⁻ (cong fst FH.pres0) k

-- Helper: fH(singleEntry α m) is (α m) at position m
eval-singleEntry-diag : (m : ℕ) (α : binarySequence) →
  fst (fst freeℕ→ℕFinCof (singleEntry α m)) m ≡ α m
eval-singleEntry-diag m α with α m
... | true  = funExt⁻ (cong fst (eval-gen m)) m ∙ δnn=1 m
... | false = funExt⁻ (cong fst FH.pres0) m

-- Going from fH(a ∨free b) to pointwise or
private
  fH-∨-pointwise : (a b : ⟨ freeBA ℕ ⟩) (k : ℕ) →
    fst (fst freeℕ→ℕFinCof (a ∨free b)) k ≡
    fst (fst freeℕ→ℕFinCof a) k or fst (fst freeℕ→ℕFinCof b) k
  fH-∨-pointwise a b k =
    funExt⁻ (cong fst (fH-pres-∨ a b)) k
    ∙ ∨fc-pointwise (fst freeℕ→ℕFinCof a) (fst freeℕ→ℕFinCof b) k

-- fH(embedUpTo α n) is false for k > n
opaque
  eval-embedUpTo-above : (α : binarySequence) (n k : ℕ) → k > n →
    fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k ≡ false
  eval-embedUpTo-above α zero k k>0 =
    eval-singleEntry-neq 0 k α (<→≢ k>0)
  eval-embedUpTo-above α (suc n) k k>sn =
    fH-∨-pointwise (embedUpTo α n) (singleEntry α (suc n)) k
    ∙ cong₂ _or_ (eval-embedUpTo-above α n k (≤-trans ≤-sucℕ k>sn))
                  (eval-singleEntry-neq (suc n) k α (<→≢ k>sn))

-- fH(embedUpTo α n) equals α k for k ≤ n
opaque
  eval-embedUpTo-below : (α : binarySequence) (n k : ℕ) → k ≤ n →
    fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k ≡ α k
  eval-embedUpTo-below α zero k k≤0 =
    subst (λ k' → fst (fst freeℕ→ℕFinCof (singleEntry α 0)) k' ≡ α k')
          (sym (≤0→≡0 k≤0)) (eval-singleEntry-diag 0 α)
  eval-embedUpTo-below α (suc n) k k≤sn =
    fH-∨-pointwise (embedUpTo α n) (singleEntry α (suc n)) k
    ∙ (case (≤-split k≤sn) return (λ _ →
        fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k or
        fst (fst freeℕ→ℕFinCof (singleEntry α (suc n))) k ≡ α k) of λ
      { (inl k<sn) →
          cong₂ _or_ (eval-embedUpTo-below α n k (pred-≤-pred k<sn))
                      (eval-singleEntry-neq (suc n) k α λ eq → <→≢ k<sn (sym eq))
          ∙ or-identityʳ (α k)
      ; (inr k=sn) →
          cong₂ _or_ (eval-embedUpTo-above α n k (subst (_> n) (sym k=sn) ≤-refl))
                      (subst (λ k' → fst (fst freeℕ→ℕFinCof (singleEntry α (suc n))) k' ≡ α k')
                             (sym k=sn)
                             (eval-singleEntry-diag (suc n) α))
      })

-- Main lemma: if α is zero from (suc n), then fH(embedUpTo α n) = α
opaque
  unfolding eval-embedUpTo-above
  unfolding eval-embedUpTo-below
  eval-embedUpTo-fst : (α : binarySequence) (n : ℕ) (bound : isZeroFrom (suc n) α) →
    fst (fst freeℕ→ℕFinCof (embedUpTo α n)) ≡ α
  eval-embedUpTo-fst α n bound = funExt λ k →
    case (k =ℕ n) return (λ _ → fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k ≡ α k) of λ
      { (lt k<n) → eval-embedUpTo-below α n k (≤-trans ≤-sucℕ k<n)
      ; (eq k=n) → eval-embedUpTo-below α n k (subst (k ≤_) k=n ≤-refl)
      ; (gt k>n) → eval-embedUpTo-above α n k k>n ∙ sym (bound k k>n)
      }

-- Putting together the section
section-finite : (α : binarySequence) (αf : isFinite α) →
  fst freeℕ→ℕFinCof (Finite→FreeℕMap α αf) ≡ (α , Fin αf)
section-finite α (constant0 α=0) = FH.pres0 ∙ FC≡ (funExt (λ k → sym (α=0 k zero-≤)))
section-finite α (last1 n αn=1 α>n=0) = FC≡ (eval-embedUpTo-fst α n α>n=0)

section-cofinite : (α : binarySequence) (αc : isCofinite α) →
  fst freeℕ→ℕFinCof (¬free (Finite→FreeℕMap (¬ α) αc)) ≡ (α , Cof αc)
section-cofinite α αc =
  fH-pres-¬ (Finite→FreeℕMap (¬ α) αc)
  ∙ cong ¬fc_ (section-finite (¬ α) αc)
  ∙ FC≡ (funExt (λ k → notnot (α k)))

fH-section : (x : ⟨ ℕfinCofinBA ⟩) → fst freeℕ→ℕFinCof (ℕFinCof→FreeℕMap x) ≡ x
fH-section (α , Fin αf) = section-finite α αf
fH-section (α , Cof αc) = section-cofinite α αc

-- ===== Roundtrip 1: presentation→ℕFinCof ∘ ℕFinCof→Presentation = id =====

roundtrip-ℕFinCof : (x : ⟨ ℕfinCofinBA ⟩) →
  fst presentation→ℕFinCof (ℕFinCof→Presentation x) ≡ x
roundtrip-ℕFinCof x =
  funExt⁻ (cong fst p→fc∘π≡fH) (ℕFinCof→FreeℕMap x) ∙ fH-section x

-- ===== Helper: embedUpTo of δSequence n gives generator n =====
private
  module ΠH = IsCommRingHom (snd π)

  singleEntry-δ-diag : (n : ℕ) → singleEntry (δSequence n) n ≡ generator n
  singleEntry-δ-diag n with δSequence n n | δnn=1 n
  ... | true  | _ = refl
  ... | false | p = ex-falso (false≢true p)

  singleEntry-δ-neq : (n m : ℕ) → (n ≡ m → ⊥) → singleEntry (δSequence n) m ≡ 𝟘free
  singleEntry-δ-neq n m n≠m with δSequence n m | δnm=0 n m n≠m
  ... | false | _ = refl
  ... | true  | p = ex-falso (true≢false p)

  embedUpTo-δ-below : (n m : ℕ) → m < n → embedUpTo (δSequence n) m ≡ 𝟘free
  embedUpTo-δ-below n zero m<n =
    singleEntry-δ-neq n 0 (<→≢ m<n ∘ sym)
  embedUpTo-δ-below n (suc m) sm<n =
    cong₂ _∨free_ (embedUpTo-δ-below n m (≤-trans ≤-sucℕ sm<n))
                   (singleEntry-δ-neq n (suc m) (<→≢ sm<n ∘ sym))
    ∙ FreeAlg.∨IdL

  embedUpTo-δ-n : (n : ℕ) → embedUpTo (δSequence n) n ≡ generator n
  embedUpTo-δ-n zero = singleEntry-δ-diag 0
  embedUpTo-δ-n (suc n) =
    cong₂ _∨free_ (embedUpTo-δ-below (suc n) n ≤-refl)
                   (singleEntry-δ-diag (suc n))
    ∙ FreeAlg.∨IdL

-- ===== Roundtrip 2: ℕFinCof→Presentation ∘ presentation→ℕFinCof = id =====
-- Uses the universal property of the quotient.

composite-on-gen : (n : ℕ) →
  ℕFinCof→Presentation (fst presentation→ℕFinCof (fst π (generator n))) ≡ fst π (generator n)
composite-on-gen n =
  cong ℕFinCof→Presentation (funExt⁻ (cong fst p→fc∘π≡fH) (generator n) ∙ eval-gen n)
  ∙ cong (fst π) (embedUpTo-δ-n n)

-- For roundtrip-presentation, we use quotientImageHomEpi.
-- We need: (ℕFinCof→Presentation ∘ fst presentation→ℕFinCof) ∘ fst π ≡ fst π
-- i.e., ℕFinCof→Presentation ∘ fst freeℕ→ℕFinCof ≡ fst π
-- This follows from ℕFinCof→PresentationIsHom + agreement on generators + universal property.
-- We prove ℕFinCof→PresentationIsHom using FromPres¬∧.

open import formalization.Library.BooleanRing.BoolAlgMorphism

-- Helpers for ¬¬α ≡ α at the free algebra level
private
  singleEntry-nn : (α : binarySequence) (k : ℕ) →
    singleEntry (λ n → not (not (α n))) k ≡ singleEntry α k
  singleEntry-nn α k with α k
  ... | true = refl
  ... | false = refl

  embedUpTo-nn : (α : binarySequence) (n : ℕ) →
    embedUpTo (λ k → not (not (α k))) n ≡ embedUpTo α n
  embedUpTo-nn α zero = singleEntry-nn α 0
  embedUpTo-nn α (suc n) = cong₂ _∨free_ (embedUpTo-nn α n) (singleEntry-nn α (suc n))

  F2F-nn : (α : binarySequence)
    (f : isFinite (λ n → not (not (α n)))) (g : isFinite α) →
    Finite→FreeℕMap (λ n → not (not (α n))) f ≡ Finite→FreeℕMap α g
  F2F-nn α (constant0 f0) (constant0 g0) = refl
  F2F-nn α (constant0 f0) (last1 n gn g>n) =
    ex-falso (false≢true (sym (f0 n zero-≤) ∙ notnot (α n) ∙ gn))
  F2F-nn α (last1 n fn f>n) (constant0 g0) =
    ex-falso (false≢true (sym (g0 n zero-≤) ∙ sym (notnot (α n)) ∙ fn))
  F2F-nn α (last1 n fn f>n) (last1 m gm g>m) with n =ℕ m
  ... | lt n<m = ex-falso (false≢true (sym (f>n m n<m) ∙ notnot (α m) ∙ gm))
  ... | gt n>m = ex-falso (false≢true (sym (g>m n n>m) ∙ sym (notnot (α n)) ∙ fn))
  ... | eq n=m = cong (embedUpTo (λ k → not (not (α k)))) n=m ∙ embedUpTo-nn α m

private
  module PAlg = BooleanAlgebraStr (snd presentation)

  ΠH-pres¬ : (a : ⟨ freeBA ℕ ⟩) → fst π (¬free a) ≡ PAlg.¬ (fst π a)
  ΠH-pres¬ a = ΠH.pres+ 𝟙free a ∙ cong₂ _+Q_ ΠH.pres1 refl

  pres¬-map : (x : ⟨ ℕfinCofinBA ⟩) →
    ℕFinCof→Presentation (¬fc x) ≡ PAlg.¬ (ℕFinCof→Presentation x)
  pres¬-map (α , Fin αf) =
    cong ℕFinCof→Presentation (FC≡ {b = ¬ α , Cof (¬FinIsCofin α αf)} refl)
    ∙ cong (fst π) (cong ¬free_ (F2F-nn α (¬FinIsCofin α αf) αf))
    ∙ ΠH-pres¬ _
  pres¬-map (α , Cof αc) =
    cong ℕFinCof→Presentation (FC≡ {b = ¬ α , Fin αc} refl)
    ∙ sym (cong PAlg.¬_ (ΠH-pres¬ t) ∙ PAlg.¬Invol)
    where t = Finite→FreeℕMap (¬ α) αc

  -- ===== Product formula helpers for pres∧-map =====

  -- In the quotient, gen i · gen j = 0 for i ≠ j
  relations-neq : (i j : ℕ) → (i ≡ j → ⊥) → relations (i , j) ≡ generator i ·free generator j
  relations-neq i j i≠j with discreteℕ i j
  ... | yes p = ex-falso (i≠j p)
  ... | no _ = refl

  gen-orth : (i j : ℕ) → (i ≡ j → ⊥) → fst π (generator i ·free generator j) ≡ 𝟘Q
  gen-orth i j i≠j = sym (cong (fst π) (relations-neq i j i≠j)) ∙ QB.zeroOnImage (i , j)

  -- singleEntry product at the same index (in freeBA, no quotient needed)
  SE-prod-diag : (α β : binarySequence) (m : ℕ) →
    singleEntry α m ·free singleEntry β m ≡ singleEntry (λ k → α k and β k) m
  SE-prod-diag α β m with α m | β m
  ... | true  | true  = FreeAlg.∧Idem
  ... | true  | false = FreeAlg.∧AnnihilR
  ... | false | true  = FreeAlg.∧AnnihilL
  ... | false | false = FreeAlg.∧AnnihilL

  -- singleEntry product at different indices (in quotient, = 0)
  π-SE-prod-neq : (α β : binarySequence) (i j : ℕ) → (i ≡ j → ⊥) →
    fst π (singleEntry α i ·free singleEntry β j) ≡ 𝟘Q
  π-SE-prod-neq α β i j i≠j with α i | β j
  ... | true  | true  = gen-orth i j i≠j
  ... | true  | false = cong (fst π) FreeAlg.∧AnnihilR ∙ ΠH.pres0
  ... | false | true  = cong (fst π) FreeAlg.∧AnnihilL ∙ ΠH.pres0
  ... | false | false = cong (fst π) FreeAlg.∧AnnihilL ∙ ΠH.pres0

  -- singleEntry at false index is 0
  SE-false : (α : binarySequence) (m : ℕ) → α m ≡ false → singleEntry α m ≡ 𝟘free
  SE-false α m p with α m
  ... | false = refl
  ... | true = ex-falso (true≢false p)

  -- embedUpTo can be extended with zero entries
  embedUpTo-ext-zero : (γ : binarySequence) (k : ℕ) → γ (suc k) ≡ false →
    embedUpTo γ (suc k) ≡ embedUpTo γ k
  embedUpTo-ext-zero γ k p = cong (embedUpTo γ k ∨free_) (SE-false γ (suc k) p) ∙ FreeAlg.∨IdR

  -- embedUpTo can be shrunk when entries above are zero
  embedUpTo-shrink : (γ : binarySequence) (n m : ℕ) →
    isZeroFrom (suc m) γ → m ≤ n → embedUpTo γ n ≡ embedUpTo γ m
  embedUpTo-shrink γ zero m γ>m m≤0 = cong (embedUpTo γ) (sym (≤0→≡0 m≤0))
  embedUpTo-shrink γ (suc n) m γ>m m≤sn = case ≤-split m≤sn of λ
    { (inl m<sn) → embedUpTo-ext-zero γ n (γ>m (suc n) m<sn)
                    ∙ embedUpTo-shrink γ n m γ>m (pred-≤-pred m<sn)
    ; (inr m=sn) → cong (embedUpTo γ) (sym m=sn)
    }

  -- embedUpTo all zero sequence is 𝟘
  embedUpTo-zero : (γ : binarySequence) (n : ℕ) → isZeroFrom 0 γ → embedUpTo γ n ≡ 𝟘free
  embedUpTo-zero γ zero γ=0 = SE-false γ 0 (γ=0 0 zero-≤)
  embedUpTo-zero γ (suc n) γ=0 =
    embedUpTo-ext-zero γ n (γ=0 (suc n) zero-≤) ∙ embedUpTo-zero γ n γ=0

  -- Finite→FreeℕMap equals embedUpTo at any sufficient bound
  F2FM-to-embedUpTo : (γ : binarySequence) (n : ℕ) (γ>n : isZeroFrom (suc n) γ)
    (gf : isFinite γ) → embedUpTo γ n ≡ Finite→FreeℕMap γ gf
  F2FM-to-embedUpTo γ n γ>n (constant0 γ=0) = embedUpTo-zero γ n γ=0
  F2FM-to-embedUpTo γ n γ>n (last1 p γp γ>p) =
    embedUpTo-shrink γ n p γ>p p≤n
    where
      p≤n : p ≤ n
      p≤n with p =ℕ n
      ... | lt p<n = ≤-trans ≤-sucℕ p<n
      ... | eq p=n = subst (_≤ n) (sym p=n) ≤-refl
      ... | gt p>n = ex-falso (true≢false (sym γp ∙ γ>n p p>n))

  -- π preserves ∨ (since ∨ = (x+y) + xy and π preserves + and ·)
  ΠH-pres-∨ : (a b : ⟨ freeBA ℕ ⟩) → fst π (a ∨free b) ≡ fst π a PAlg.∨ fst π b
  ΠH-pres-∨ a b = ΠH.pres+ (a +free b) (a ·free b) ∙ cong₂ _+Q_ (ΠH.pres+ a b) (ΠH.pres· a b)

  -- SE · embedUpTo = 0 in quotient when index exceeds bound
  opaque
    π-SE-times-eU-above : (α β : binarySequence) (i m : ℕ) → m < i →
      fst π (singleEntry α i ·free embedUpTo β m) ≡ 𝟘Q
    π-SE-times-eU-above α β i zero m<i =
      π-SE-prod-neq α β i 0 (<→≢ m<i ∘ sym)
    π-SE-times-eU-above α β i (suc m') m<i =
      cong (fst π) (FreeAlg.∧DistR∨ {x = singleEntry α i})
      ∙ ΠH-pres-∨ _ _
      ∙ cong₂ PAlg._∨_ (π-SE-times-eU-above α β i m' (≤-trans ≤-sucℕ m<i))
                         (π-SE-prod-neq α β i (suc m') (<→≢ m<i ∘ sym))
      ∙ PAlg.∨IdL

  -- SE · embedUpTo = SE(α∧β) in quotient when index within bound
  opaque
    unfolding π-SE-times-eU-above
    π-SE-times-eU-below : (α β : binarySequence) (i m : ℕ) → i ≤ m →
      fst π (singleEntry α i ·free embedUpTo β m) ≡ fst π (singleEntry (λ k → α k and β k) i)
    π-SE-times-eU-below α β i zero i≤0 =
      cong (λ i' → fst π (singleEntry α i' ·free singleEntry β 0)) (≤0→≡0 i≤0)
      ∙ cong (fst π) (SE-prod-diag α β 0)
      ∙ cong (λ i' → fst π (singleEntry (λ k → α k and β k) i')) (sym (≤0→≡0 i≤0))
    π-SE-times-eU-below α β i (suc m') i≤sm' =
      cong (fst π) (FreeAlg.∧DistR∨ {x = singleEntry α i})
      ∙ ΠH-pres-∨ _ _
      ∙ (case (≤-split i≤sm') return (λ _ →
          fst π (singleEntry α i ·free embedUpTo β m') PAlg.∨
          fst π (singleEntry α i ·free singleEntry β (suc m'))
          ≡ fst π (singleEntry (λ k → α k and β k) i)) of λ
        { (inl i<sm') →
            cong₂ PAlg._∨_ (π-SE-times-eU-below α β i m' (pred-≤-pred i<sm'))
                             (π-SE-prod-neq α β i (suc m') (<→≢ i<sm'))
            ∙ PAlg.∨IdR
        ; (inr i=sm') →
            cong₂ PAlg._∨_
              (π-SE-times-eU-above α β i m' (subst (_> m') (sym i=sm') ≤-refl))
              (cong (λ j → fst π (singleEntry α j ·free singleEntry β (suc m'))) i=sm'
               ∙ cong (fst π) (SE-prod-diag α β (suc m'))
               ∙ cong (λ j → fst π (singleEntry (λ k → α k and β k) j)) (sym i=sm'))
            ∙ PAlg.∨IdL
        })

  -- Main product formula: embedUpTo α n · embedUpTo β m in quotient (n ≤ m)
  opaque
    unfolding π-SE-times-eU-below
    unfolding π-SE-times-eU-above
    π-embedUpTo-prod : (α β : binarySequence) (n m : ℕ) → n ≤ m →
      fst π (embedUpTo α n ·free embedUpTo β m)
      ≡ fst π (embedUpTo (λ k → α k and β k) n)
    π-embedUpTo-prod α β zero m 0≤m =
      π-SE-times-eU-below α β 0 m 0≤m
    π-embedUpTo-prod α β (suc n') m sn≤m =
      cong (fst π) (FreeAlg.∧DistL∨ {z = embedUpTo β m})
      ∙ ΠH-pres-∨ _ _
      ∙ cong₂ PAlg._∨_
          (π-embedUpTo-prod α β n' m (≤-trans ≤-sucℕ sn≤m))
          (π-SE-times-eU-below α β (suc n') m sn≤m)
      ∙ sym (ΠH-pres-∨ _ _)

  -- Intersection bound: α∧β is zero from suc n when α is zero from suc n
  ∧-zeroFrom : (α β : binarySequence) (n : ℕ) →
    isZeroFrom (suc n) α → isZeroFrom (suc n) (λ k → α k and β k)
  ∧-zeroFrom α β n α>n k k>n = cong (_and β k) (α>n k k>n)

  -- α∧β is zero from suc m when β is zero from suc m
  ∧-zeroFromR : (α β : binarySequence) (m : ℕ) →
    isZeroFrom (suc m) β → isZeroFrom (suc m) (λ k → α k and β k)
  ∧-zeroFromR α β m β>m k k>m = cong (α k and_) (β>m k k>m) ∙ and-zeroʳ (α k)

  -- and-comm lifted to sequences
  ∧-seq-comm : (α β : binarySequence) →
    (λ k → β k and α k) ≡ (λ k → α k and β k)
  ∧-seq-comm α β = funExt (λ k → and-comm (β k) (α k))

  -- The core Fin×Fin case, split by bound comparison
  opaque
    unfolding π-embedUpTo-prod
    pres∧-FF-core : (α β : binarySequence) (n m : ℕ)
      (αn : α n ≡ true) (α>n : isZeroFrom (suc n) α)
      (βm : β m ≡ true) (β>m : isZeroFrom (suc m) β) →
      fst π (Finite→FreeℕMap (λ k → α k and β k)
             (intersectionWithFiniteIsFinite α β (last1 n αn α>n)))
      ≡ fst π (embedUpTo α n) ·Q fst π (embedUpTo β m)
    pres∧-FF-core α β n m αn α>n βm β>m with n =ℕ m
    ... | lt n<m =
      cong (fst π) (sym (F2FM-to-embedUpTo _ n (∧-zeroFrom α β n α>n) abf))
      ∙ sym (π-embedUpTo-prod α β n m (≤-trans ≤-sucℕ n<m))
      ∙ ΠH.pres· _ _
      where abf : isFinite (λ k → α k and β k)
            abf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)
    ... | eq n=m =
      cong (fst π) (sym (F2FM-to-embedUpTo _ n (∧-zeroFrom α β n α>n) abf))
      ∙ sym (π-embedUpTo-prod α β n m (subst (n ≤_) n=m ≤-refl))
      ∙ ΠH.pres· _ _
      where abf : isFinite (λ k → α k and β k)
            abf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)
    ... | gt n>m =
      cong (fst π) (sym (F2FM-to-embedUpTo _ m (∧-zeroFromR α β m β>m) abf))
      ∙ cong (fst π) (cong (λ f → embedUpTo f m) (sym (∧-seq-comm α β)))
      ∙ sym (π-embedUpTo-prod β α m n (≤-trans ≤-sucℕ n>m))
      ∙ cong (fst π) (Free.·Comm _ _)
      ∙ ΠH.pres· _ _
      where abf : isFinite (λ k → α k and β k)
            abf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)

  -- Connecting Finite→FreeℕMap product for all Fin cases
  opaque
    unfolding pres∧-FF-core
    pres∧-FF : (α β : binarySequence) (αf : isFinite α) (βf : isFinite β) →
      ℕFinCof→Presentation (α ∧ β , Fin (intersectionWithFiniteIsFinite α β αf))
      ≡ fst π (Finite→FreeℕMap α αf) ·Q fst π (Finite→FreeℕMap β βf)
    pres∧-FF α β (constant0 α=0) βf =
      let αβ=0 : isFinite (λ k → α k and β k)
          αβ=0 = constant0 (λ k _ → cong (_and β k) (α=0 k zero-≤))
          eq1 = cong (Finite→FreeℕMap _) (isPropIsFinite _ (intersectionWithFiniteIsFinite α β (constant0 α=0)) αβ=0)
      in cong (fst π) eq1
       ∙ sym (cong (fst π) (FreeAlg.∧AnnihilL {x = Finite→FreeℕMap β βf}))
       ∙ ΠH.pres· 𝟘free (Finite→FreeℕMap β βf)
    pres∧-FF α β (last1 n αn α>n) (constant0 β=0) =
      let αβ=0 : isFinite (λ k → α k and β k)
          αβ=0 = constant0 (λ k _ → cong (α k and_) (β=0 k zero-≤) ∙ and-zeroʳ (α k))
          eq1 = cong (Finite→FreeℕMap _) (isPropIsFinite _ (intersectionWithFiniteIsFinite α β (last1 n αn α>n)) αβ=0)
      in cong (fst π) eq1
       ∙ sym (cong (fst π) (FreeAlg.∧AnnihilR {x = Finite→FreeℕMap α (last1 n αn α>n)}))
       ∙ ΠH.pres· (Finite→FreeℕMap α (last1 n αn α>n)) 𝟘free
    pres∧-FF α β (last1 n αn α>n) (last1 m βm β>m) =
      pres∧-FF-core α β n m αn α>n βm β>m

-- ===== Infrastructure for Cof cases of pres∧-map =====
private
  -- Additive version of embedUpTo (uses +free instead of ∨free)
  embedUpToFlat : (α : binarySequence) → (m : ℕ) → ⟨ freeBA ℕ ⟩
  embedUpToFlat α zero = singleEntry α 0
  embedUpToFlat α (suc m) = embedUpToFlat α m +free singleEntry α (suc m)

  -- SE addition lemma: SE α k + SE (α∧¬β) k = SE (α∧β) k in freeBA
  SE-and-split : (α β : binarySequence) (k : ℕ) →
    singleEntry α k +free singleEntry (λ j → α j and not (β j)) k
    ≡ singleEntry (λ j → α j and β j) k
  SE-and-split α β k with α k | β k
  ... | false | false = Free.+IdL _
  ... | false | true  = Free.+IdL _
  ... | true  | true  = Free.+IdR _
  ... | true  | false = FreeAlg.characteristic2

  -- Rearranging sums: (a+b)+(c+d) = (a+c)+(b+d)
  rearrange-sum : (a b c d : ⟨ freeBA ℕ ⟩) →
    (a +free b) +free (c +free d) ≡ (a +free c) +free (b +free d)
  rearrange-sum a b c d =
    sym (Free.+Assoc a b (c +free d))
    ∙ cong (a +free_) (Free.+Assoc b c d
                       ∙ cong (_+free d) (Free.+Comm b c)
                       ∙ sym (Free.+Assoc c b d))
    ∙ Free.+Assoc a c (b +free d)

  -- Flat sum: eF α n + eF (α∧¬β) n = eF (α∧β) n in freeBA
  flat-and-split : (α β : binarySequence) (n : ℕ) →
    embedUpToFlat α n +free embedUpToFlat (λ k → α k and not (β k)) n
    ≡ embedUpToFlat (λ k → α k and β k) n
  flat-and-split α β zero = SE-and-split α β 0
  flat-and-split α β (suc n) =
    rearrange-sum (embedUpToFlat α n) (singleEntry α (suc n))
                  (embedUpToFlat (λ k → α k and not (β k)) n)
                  (singleEntry (λ k → α k and not (β k)) (suc n))
    ∙ cong₂ _+free_ (flat-and-split α β n) (SE-and-split α β (suc n))

  -- ∨ = + in quotient when cross-product is 0
  ∨-as-+ : (a b : ⟨ freeBA ℕ ⟩) → fst π (a ·free b) ≡ 𝟘Q →
    fst π (a ∨free b) ≡ fst π a +Q fst π b
  ∨-as-+ a b orth =
    ΠH-pres-∨ a b
    ∙ cong ((fst π a +Q fst π b) +Q_) (sym (ΠH.pres· a b) ∙ orth)
    ∙ P.+IdR _

  -- Orthogonality: eU γ n and SE γ (n+1) have zero product in quotient
  opaque
    unfolding π-SE-times-eU-above
    eU-SE-orth : (γ : binarySequence) (n : ℕ) →
      fst π (embedUpTo γ n ·free singleEntry γ (suc n)) ≡ 𝟘Q
    eU-SE-orth γ n =
      cong (fst π) (Free.·Comm (embedUpTo γ n) (singleEntry γ (suc n)))
      ∙ π-SE-times-eU-above γ γ (suc n) n ≤-refl

  -- Convert embedUpTo to embedUpToFlat in quotient
  opaque
    unfolding eU-SE-orth
    π-eU-to-flat : (γ : binarySequence) (n : ℕ) →
      fst π (embedUpTo γ n) ≡ fst π (embedUpToFlat γ n)
    π-eU-to-flat γ zero = refl
    π-eU-to-flat γ (suc n) =
      ∨-as-+ (embedUpTo γ n) (singleEntry γ (suc n)) (eU-SE-orth γ n)
      ∙ cong (_+Q fst π (singleEntry γ (suc n))) (π-eU-to-flat γ n)
      ∙ sym (ΠH.pres+ (embedUpToFlat γ n) (singleEntry γ (suc n)))

  -- The key: eU(α∧β) n ≡ eU α n + eU(α∧¬β) n in the quotient
  opaque
    unfolding π-eU-to-flat
    π-eU-and-split : (α β : binarySequence) (n : ℕ) →
      fst π (embedUpTo (λ k → α k and β k) n)
      ≡ fst π (embedUpTo α n +free embedUpTo (λ k → α k and not (β k)) n)
    π-eU-and-split α β n =
      π-eU-to-flat (λ k → α k and β k) n
      ∙ cong (fst π) (sym (flat-and-split α β n))
      ∙ ΠH.pres+ (embedUpToFlat α n) (embedUpToFlat (λ k → α k and not (β k)) n)
      ∙ cong₂ _+Q_ (sym (π-eU-to-flat α n)) (sym (π-eU-to-flat (λ k → α k and not (β k)) n))
      ∙ sym (ΠH.pres+ (embedUpTo α n) (embedUpTo (λ k → α k and not (β k)) n))

  -- Ring identity: a · (1 + b) = a + a·b
  ·-distrib-¬ : (a b : ⟨ presentation ⟩) → a ·Q (𝟙Q +Q b) ≡ a +Q a ·Q b
  ·-distrib-¬ a b = P.·DistR+ a 𝟙Q b ∙ cong (_+Q (a ·Q b)) (P.·IdR a)

  -- The Fin×Cof core: when αf = last1 n αn α>n
  opaque
    unfolding pres∧-FF
    unfolding pres∧-FF-core
    unfolding π-eU-and-split
    pres∧-FC : (α β : binarySequence) (αf : isFinite α) (βc : isCofinite β) →
      ℕFinCof→Presentation (α ∧ β , Fin (intersectionWithFiniteIsFinite α β αf))
      ≡ fst π (Finite→FreeℕMap α αf) ·Q fst π (¬free (Finite→FreeℕMap (¬ β) βc))
    pres∧-FC α β (constant0 α=0) βc =
      let αβf : isFinite (λ k → α k and β k)
          αβf = intersectionWithFiniteIsFinite α β (constant0 α=0)
          αβ0 : isFinite (λ k → α k and β k)
          αβ0 = constant0 (λ k _ → cong (_and β k) (α=0 k zero-≤))
      in cong (fst π) (cong (Finite→FreeℕMap _) (isPropIsFinite _ αβf αβ0))
       ∙ sym (cong (fst π) (FreeAlg.∧AnnihilL {x = ¬free (Finite→FreeℕMap (¬ β) βc)}))
       ∙ ΠH.pres· 𝟘free (¬free (Finite→FreeℕMap (¬ β) βc))
    pres∧-FC α β (last1 n αn α>n) βc =
      let αβf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)
          α¬βf = intersectionWithFiniteIsFinite α (¬ β) (last1 n αn α>n)
          a = embedUpTo α n
          b = Finite→FreeℕMap (¬ β) βc
      in -- Step 1: normalize F2FM(α∧β) to embedUpTo at bound n
         cong (fst π) (sym (F2FM-to-embedUpTo _ n (∧-zeroFrom α β n α>n) αβf))
         -- Step 2: split using the key lemma
       ∙ π-eU-and-split α β n
         -- Step 3: use ΠH.pres+ to split
       ∙ ΠH.pres+ a (embedUpTo (λ k → α k and not (β k)) n)
         -- Step 4: convert embedUpTo(α∧¬β) to product via pres∧-FF
       ∙ cong (fst π a +Q_)
              (cong (fst π) (F2FM-to-embedUpTo _ n (∧-zeroFrom α (¬ β) n α>n) α¬βf)
               ∙ pres∧-FF α (¬ β) (last1 n αn α>n) βc)
         -- Step 5: ring identity a·(1+b) = a + a·b (backwards)
       ∙ sym (cong (fst π a ·Q_) (ΠH-pres¬ b) ∙ ·-distrib-¬ (fst π a) (fst π b))

  -- ===== ∨-preservation for Fin×Fin (needed for Cof×Cof via De Morgan) =====

  -- Bool-level De Morgan: not (a and b) = not a or not b
  not-and-is-or-not : (a b : Bool) → not (a and b) ≡ not a or not b
  not-and-is-or-not false false = refl
  not-and-is-or-not false true  = refl
  not-and-is-or-not true  false = refl
  not-and-is-or-not true  true  = refl

  -- singleEntry distributes over or (in freeBA, no quotient needed)
  singleEntry-or-split : (α β : binarySequence) (m : ℕ) →
    singleEntry (λ k → α k or β k) m ≡ singleEntry α m ∨free singleEntry β m
  singleEntry-or-split α β m with α m | β m
  ... | false | false = sym FreeAlg.∨IdL
  ... | false | true  = sym FreeAlg.∨IdL
  ... | true  | false = sym FreeAlg.∨IdR
  ... | true  | true  = sym FreeAlg.∨Idem

  -- Rearranging ∨: (a∨b) ∨ (c∨d) = (a∨c) ∨ (b∨d)
  rearrange-∨ : (a b c d : ⟨ freeBA ℕ ⟩) →
    (a ∨free b) ∨free (c ∨free d) ≡ (a ∨free c) ∨free (b ∨free d)
  rearrange-∨ a b c d =
    FreeAlg.∨Assoc
    ∙ cong (_∨free d) (sym FreeAlg.∨Assoc ∙ cong (a ∨free_) FreeAlg.∨Comm ∙ FreeAlg.∨Assoc)
    ∙ sym FreeAlg.∨Assoc

  -- embedUpTo distributes over or (in freeBA)
  embedUpTo-or-split : (α β : binarySequence) (n : ℕ) →
    embedUpTo (λ k → α k or β k) n ≡ embedUpTo α n ∨free embedUpTo β n
  embedUpTo-or-split α β zero = singleEntry-or-split α β 0
  embedUpTo-or-split α β (suc n) =
    cong₂ _∨free_ (embedUpTo-or-split α β n) (singleEntry-or-split α β (suc n))
    ∙ rearrange-∨ (embedUpTo α n) (embedUpTo β n)
                   (singleEntry α (suc n)) (singleEntry β (suc n))

  -- isZeroFrom for or-sequences
  ∨-zeroFrom : (α β : binarySequence) (n : ℕ) →
    isZeroFrom n α → isZeroFrom n β → isZeroFrom n (λ k → α k or β k)
  ∨-zeroFrom α β n α>n β>n k k≥n = cong₂ _or_ (α>n k k≥n) (β>n k k≥n)

  -- Preservation of ∨ for Fin×Fin
  opaque
    unfolding π-embedUpTo-prod
    pres∨-FinFin : (α β : binarySequence) (αf : isFinite α) (βf : isFinite β)
      (unionf : isFinite (λ k → α k or β k)) →
      fst π (Finite→FreeℕMap (λ k → α k or β k) unionf)
      ≡ fst π (Finite→FreeℕMap α αf ∨free Finite→FreeℕMap β βf)
    pres∨-FinFin α β (constant0 α=0) βf unionf =
      let or-eq : (k : ℕ) → false or β k ≡ β k
          or-eq k = refl
          seq-eq : (λ k → α k or β k) ≡ β
          seq-eq = funExt (λ k → cong (_or β k) (α=0 k zero-≤))
          rhs-eq : Finite→FreeℕMap α (constant0 α=0) ∨free Finite→FreeℕMap β βf
                   ≡ Finite→FreeℕMap β βf
          rhs-eq = FreeAlg.∨IdL
      in cong (fst π) (cong₂ Finite→FreeℕMap seq-eq
                              (isProp→PathP (λ i → isPropIsFinite (seq-eq i)) unionf βf))
       ∙ sym (cong (fst π) rhs-eq)
    pres∨-FinFin α β (last1 n αn α>n) (constant0 β=0) unionf =
      let seq-eq : (λ k → α k or β k) ≡ α
          seq-eq = funExt (λ k → cong (α k or_) (β=0 k zero-≤) ∙ or-identityʳ (α k))
          rhs-eq : Finite→FreeℕMap α (last1 n αn α>n) ∨free Finite→FreeℕMap β (constant0 β=0)
                   ≡ Finite→FreeℕMap α (last1 n αn α>n)
          rhs-eq = FreeAlg.∨IdR
      in cong (fst π) (cong₂ Finite→FreeℕMap seq-eq
                              (isProp→PathP (λ i → isPropIsFinite (seq-eq i)) unionf (last1 n αn α>n)))
       ∙ sym (cong (fst π) rhs-eq)
    pres∨-FinFin α β (last1 n αn α>n) (last1 m βm β>m) unionf with n =ℕ m
    ... | lt n<m =
      let α>m : isZeroFrom (suc m) α
          α>m k k>m = α>n k (≤-trans n<m (≤-trans ≤-sucℕ k>m))
          or>m : isZeroFrom (suc m) (λ k → α k or β k)
          or>m = ∨-zeroFrom α β (suc m) α>m β>m
      in cong (fst π) (sym (F2FM-to-embedUpTo _ m or>m unionf))
       ∙ cong (fst π) (embedUpTo-or-split α β m)
       ∙ cong (fst π) (cong₂ _∨free_ (F2FM-to-embedUpTo α m α>m (last1 n αn α>n))
                                       refl)
    ... | eq n=m =
      let β>n : isZeroFrom (suc n) β
          β>n k k>n = β>m k (subst (_≤ k) (cong suc n=m) k>n)
          or>n : isZeroFrom (suc n) (λ k → α k or β k)
          or>n = ∨-zeroFrom α β (suc n) α>n β>n
      in cong (fst π) (sym (F2FM-to-embedUpTo _ n or>n unionf))
       ∙ cong (fst π) (embedUpTo-or-split α β n)
       ∙ cong (fst π) (cong (embedUpTo α n ∨free_) (cong (embedUpTo β) n=m))
    ... | gt n>m =
      let β>n : isZeroFrom (suc n) β
          β>n k k>n = β>m k (≤-trans n>m (≤-trans ≤-sucℕ k>n))
          or>n : isZeroFrom (suc n) (λ k → α k or β k)
          or>n = ∨-zeroFrom α β (suc n) α>n β>n
      in cong (fst π) (sym (F2FM-to-embedUpTo _ n or>n unionf))
       ∙ cong (fst π) (embedUpTo-or-split α β n)
       ∙ cong (fst π) (cong₂ _∨free_ refl
                                       (F2FM-to-embedUpTo β n β>n (last1 m βm β>m)))

  -- pres∧-map: all four cases
  pres∧-map : (x y : ⟨ ℕfinCofinBA ⟩) →
    ℕFinCof→Presentation (x ∧fc y) ≡ (ℕFinCof→Presentation x) PAlg.∧ (ℕFinCof→Presentation y)
  pres∧-map (α , Fin αf) (β , Fin βf) =
    cong ℕFinCof→Presentation (FC≡ {b = α ∧ β , Fin (intersectionWithFiniteIsFinite α β αf)} refl)
    ∙ pres∧-FF α β αf βf
  pres∧-map (α , Fin αf) (β , Cof βc) =
    cong ℕFinCof→Presentation (FC≡ {b = α ∧ β , Fin (intersectionWithFiniteIsFinite α β αf)} refl)
    ∙ pres∧-FC α β αf βc
  pres∧-map (α , Cof αc) (β , Fin βf) =
    cong ℕFinCof→Presentation
      (FC≡ {b = β ∧ α , Fin (intersectionWithFiniteIsFinite β α βf)}
           (funExt λ k → and-comm (α k) (β k)))
    ∙ pres∧-FC β α βf αc
    ∙ PAlg.∧Comm
  pres∧-map (α , Cof αc) (β , Cof βc) =
    let cofp : isCofinite (α ∧ β)
        cofp = subst isFinite (sym DeMorgan¬∧) (finiteClosedByUnion (¬ α) (¬ β) αc βc)
        not-and-seq : (λ k → not (α k and β k)) ≡ (λ k → not (α k) or not (β k))
        not-and-seq = funExt (λ k → not-and-is-or-not (α k) (β k))
        orf : isFinite (λ k → not (α k) or not (β k))
        orf = subst isFinite not-and-seq cofp
        a = Finite→FreeℕMap (¬ α) αc
        b = Finite→FreeℕMap (¬ β) βc
    in cong ℕFinCof→Presentation (FC≡ {b = α ∧ β , Cof cofp} refl)
       -- unfold: ℕFinCof→Presentation (α∧β, Cof cofp) = fst π (¬free (F2FM (¬(α∧β)) cofp))
       -- convert ¬(α∧β) to ¬α ∨ ¬β using Bool De Morgan
     ∙ cong (fst π ∘ ¬free_) (cong₂ Finite→FreeℕMap not-and-seq
                                      (isProp→PathP (λ i → isPropIsFinite (not-and-seq i)) cofp orf))
       -- go through quotient via ΠH-pres¬
     ∙ ΠH-pres¬ (Finite→FreeℕMap (λ k → not (α k) or not (β k)) orf)
       -- use pres∨-FinFin in the quotient
     ∙ cong PAlg.¬_ (pres∨-FinFin (¬ α) (¬ β) αc βc orf)
       -- go back: PAlg.¬ (fst π (a ∨free b)) = fst π (¬free (a ∨free b))
     ∙ sym (ΠH-pres¬ (a ∨free b))
       -- De Morgan in freeBA: ¬(a∨b) = ¬a · ¬b
     ∙ cong (fst π) FreeAlg.DeMorgan¬∨
       -- split product through π
     ∙ ΠH.pres· (¬free a) (¬free b)

ℕFinCof→PresentationIsHom : IsCommRingHom
  (BooleanRingStr→CommRingStr (snd ℕfinCofinBA))
  ℕFinCof→Presentation
  (BooleanRingStr→CommRingStr (snd presentation))
ℕFinCof→PresentationIsHom =
  FromPres¬∧.isBoolRingHom ℕfinCofinBA presentation ℕFinCof→Presentation
    pres¬-map pres∧-map

ℕFinCof→PresentationHom : BoolHom ℕfinCofinBA presentation
ℕFinCof→PresentationHom = ℕFinCof→Presentation , ℕFinCof→PresentationIsHom

private
  module P2H = IsCommRingHom ℕFinCof→PresentationIsHom

  compBH : BoolHom (freeBA ℕ) presentation
  fst compBH = ℕFinCof→Presentation ∘ fst freeℕ→ℕFinCof
  IsCommRingHom.pres0 (snd compBH) = cong ℕFinCof→Presentation FH.pres0 ∙ P2H.pres0
  IsCommRingHom.pres1 (snd compBH) = cong ℕFinCof→Presentation FH.pres1 ∙ P2H.pres1
  IsCommRingHom.pres+ (snd compBH) x y = cong ℕFinCof→Presentation (FH.pres+ x y) ∙ P2H.pres+ _ _
  IsCommRingHom.pres· (snd compBH) x y = cong ℕFinCof→Presentation (FH.pres· x y) ∙ P2H.pres· _ _
  IsCommRingHom.pres- (snd compBH) x = cong ℕFinCof→Presentation (FH.pres- x) ∙ P2H.pres- _

roundtrip-pre-on-free : (t : ⟨ freeBA ℕ ⟩) →
  ℕFinCof→Presentation (fst freeℕ→ℕFinCof t) ≡ fst π t
roundtrip-pre-on-free = funExt⁻ (cong fst
  (sym (inducedBAHomUnique ℕ presentation (λ n → fst π (generator n))
    compBH
    (funExt λ n → cong ℕFinCof→Presentation (sym (funExt⁻ (cong fst p→fc∘π≡fH) (generator n))) ∙ composite-on-gen n))
  ∙ inducedBAHomUnique ℕ presentation (λ n → fst π (generator n)) π refl))

roundtrip-presentation : (x : ⟨ presentation ⟩) →
  ℕFinCof→Presentation (fst presentation→ℕFinCof x) ≡ x
roundtrip-presentation = funExt⁻ (QB.quotientImageHomEpi
  (⟨ presentation ⟩ , isSetQ)
  (funExt λ t →
    cong ℕFinCof→Presentation (funExt⁻ (cong fst p→fc∘π≡fH) t)
    ∙ roundtrip-pre-on-free t))

-- ===== Final equivalence =====

ℕFinCof≅Presentation : Iso ⟨ ℕfinCofinBA ⟩ ⟨ presentation ⟩
ℕFinCof≅Presentation = iso ℕFinCof→Presentation (fst presentation→ℕFinCof) roundtrip-presentation roundtrip-ℕFinCof

private
  fwdIsEquiv : isEquiv (fst presentation→ℕFinCof)
  fwdIsEquiv = isoToIsEquiv (iso (fst presentation→ℕFinCof) ℕFinCof→Presentation
    roundtrip-ℕFinCof roundtrip-presentation)

  fwdBoolEquiv : BooleanRingEquiv presentation ℕfinCofinBA
  fwdBoolEquiv = mkBooleanRingEquiv presentation ℕfinCofinBA presentation→ℕFinCof fwdIsEquiv

ℕFinCof=Presentation : BooleanRingEquiv ℕfinCofinBA presentation
ℕFinCof=Presentation = invBooleanRingEquiv presentation ℕfinCofinBA fwdBoolEquiv
