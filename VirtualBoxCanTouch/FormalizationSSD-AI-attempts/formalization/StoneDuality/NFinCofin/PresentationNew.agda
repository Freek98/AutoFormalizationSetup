{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module formalization.StoneDuality.NFinCofin.PresentationNew where

open import formalization.StoneDuality.NFinCofin.Definitions

open import BooleanRing.BooleanRingMaps
open import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import BasicDefinitions
open import BooleanRing.BoolAlgMorphism

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism using (Iso)

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true; or-identityʳ; notnot; and-zeroʳ; and-comm)
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import CountablyPresentedBooleanRings.Definitions

open BooleanRingStr ⦃...⦄
open BooleanAlgebraStr ⦃...⦄
instance
  _ = snd ℕfinCofinBA
  _ = snd ℙℕ
  _ = snd (freeBA ℕ)

FC≡ : {a b : ⟨ ℕfinCofinBA ⟩} → fst a ≡ fst b → a ≡ b
FC≡ = Σ≡Prop isPropisFiniteOrCofinite

relations : ℕ × ℕ → ⟨ freeBA ℕ ⟩
relations (n , m) with discreteℕ n m
... | yes _ = 𝟘
... | no ¬p = generator n ∧ generator m

relationsℕ : ℕ → ⟨ freeBA ℕ ⟩
relationsℕ = relations ∘ Iso.inv ℕ×ℕ≅ℕ

presentation : BooleanRing ℓ-zero
presentation = (freeBA ℕ) QB./Im relationsℕ

instance
  _ = snd presentation

module NFinCofinPresentation where
  δnn=1 : (n : ℕ) → δSequence n n ≡ true
  δnn=1 zero = refl
  δnn=1 (suc n) = δnn=1 n

  δnm=0 : (n m : ℕ) → (n ≡ m → ⊥) → δSequence n m ≡ false
  δnm=0 zero zero x = ex-falso (x refl)
  δnm=0 zero (suc m) x = refl
  δnm=0 (suc n) zero x = refl
  δnm=0 (suc n) (suc m) x = δnm=0 n m (x ∘ cong suc)

  δn∧δm=0 : (n m : ℕ) → (n ≡ m → ⊥) → (k : ℕ) → (δSequence n k) and (δSequence m k) ≡ false
  δn∧δm=0 zero zero n≠m _ = ex-falso (n≠m refl)
  δn∧δm=0 zero _ n≠m (suc k) = refl
  δn∧δm=0 (suc n) _ n≠m zero = refl
  δn∧δm=0 _ (suc m) n≠m zero = and-zeroʳ _
  δn∧δm=0 _ zero n≠m (suc k) = and-zeroʳ _
  δn∧δm=0 (suc n) (suc m) n≠m (suc k) = δn∧δm=0 n m (n≠m ∘ cong suc) k

  δSequenceFinite : (n : ℕ) → isFinite (δSequence n)
  δSequenceFinite n = last1 n (δnn=1 n) λ k k>n → δnm=0 n k (<→≢ k>n)

  singleton : (n : ℕ) → ⟨ ℕfinCofinBA ⟩
  singleton n = δSequence n , Fin (δSequenceFinite n)

  freeℕ→ℕFinCof : BoolHom (freeBA ℕ) ℕfinCofinBA
  freeℕ→ℕFinCof = inducedBAHom ℕ ℕfinCofinBA singleton

  module FH = IsCommRingHom (snd freeℕ→ℕFinCof)
  eval-gen : (n : ℕ) → fst freeℕ→ℕFinCof (generator n) ≡ singleton n
  eval-gen n = funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n

  relationsRespected : ∀ (p : ℕ × ℕ) → freeℕ→ℕFinCof $cr (relations p) ≡ 𝟘
  relationsRespected (n , m) with discreteℕ n m
  ... | yes _ = FH.pres0
  ... | no ¬p =
    fst freeℕ→ℕFinCof (generator n · generator m)
      ≡⟨ FH.pres· (generator n) (generator m) ⟩
    fst freeℕ→ℕFinCof (generator n) · fst freeℕ→ℕFinCof (generator m)
      ≡⟨ cong₂ _·_ (eval-gen n) (eval-gen m) ⟩
    singleton n · singleton m
      ≡⟨ FC≡ (funExt (δn∧δm=0 n m ¬p)) ⟩
    𝟘 ∎

  relationsℕRespected : ∀ n → freeℕ→ℕFinCof $cr (relationsℕ n) ≡ 𝟘
  relationsℕRespected n = relationsRespected (Iso.inv ℕ×ℕ≅ℕ n)

  π : BoolHom (freeBA ℕ) presentation
  π = QB.quotientImageHom

  module ΠH = IsCommRingHom (snd π)

  singleEntry : (α : binarySequence) → (m : ℕ) → ⟨ freeBA ℕ ⟩
  singleEntry α m = if α m then generator m else 𝟘

  embedUpTo : (α : binarySequence) → (m : ℕ) → ⟨ freeBA ℕ ⟩
  embedUpTo α zero = singleEntry α 0
  embedUpTo α (suc m) = embedUpTo α m ∨ singleEntry α (suc m)

  Finite→FreeℕMap : (α : binarySequence) → isFinite α → ⟨ freeBA ℕ ⟩
  Finite→FreeℕMap α (constant0 _) = 𝟘
  Finite→FreeℕMap α (last1 n _ _) = embedUpTo α n

  ℕFinCof→FreeℕMap : ⟨ ℕfinCofinBA ⟩ → ⟨ freeBA ℕ ⟩
  ℕFinCof→FreeℕMap (α , Fin αf) = Finite→FreeℕMap α αf
  ℕFinCof→FreeℕMap (α , Cof αc) = ¬ (Finite→FreeℕMap (¬ α) αc)

  ℕFinCof→Presentation : ⟨ ℕfinCofinBA ⟩ → ⟨ presentation ⟩
  ℕFinCof→Presentation = fst π ∘ ℕFinCof→FreeℕMap

  module FHAlg = isBoolAlgHom (freeBA ℕ) ℕfinCofinBA (fst freeℕ→ℕFinCof) (snd freeℕ→ℕFinCof)
  fH-pres-∨ = FHAlg.pres∨
  fH-pres-¬ = FHAlg.pres¬

  fH-∨-pointwise : (a b : ⟨ freeBA ℕ ⟩) (k : ℕ) →
    fst (fst freeℕ→ℕFinCof (a ∨ b)) k ≡
    fst (fst freeℕ→ℕFinCof a) k or fst (fst freeℕ→ℕFinCof b) k
  fH-∨-pointwise a b k =
    cong (λ x → fst x k) (fH-pres-∨ a b)
    ∙ QuickBooleanFix.claim (fst (fst freeℕ→ℕFinCof a) k) (fst (fst freeℕ→ℕFinCof b) k)

  eval-singleEntry-neq : (m k : ℕ) (α : binarySequence) → (m ≡ k → ⊥) →
    fst (fst freeℕ→ℕFinCof (singleEntry α m)) k ≡ false
  eval-singleEntry-neq m k α m≠k with α m
  ... | true  = cong (λ x → fst x k) (eval-gen m) ∙ δnm=0 m k m≠k
  ... | false = cong (λ x → fst x k) FH.pres0

  eval-singleEntry-diag : (m : ℕ) (α : binarySequence) →
    fst (fst freeℕ→ℕFinCof (singleEntry α m)) m ≡ α m
  eval-singleEntry-diag m α with α m
  ... | true  = cong (λ x → fst x m) (eval-gen m) ∙ δnn=1 m
  ... | false = cong (λ x → fst x m) FH.pres0

  opaque
    eval-embedUpTo-above : (α : binarySequence) (n k : ℕ) → k > n →
      fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k ≡ false
    eval-embedUpTo-above α zero k k>0 =
      eval-singleEntry-neq 0 k α (<→≢ k>0)
    eval-embedUpTo-above α (suc n) k k>sn =
      fst (fst freeℕ→ℕFinCof (embedUpTo α n ∨ singleEntry α (suc n))) k
        ≡⟨ fH-∨-pointwise (embedUpTo α n) (singleEntry α (suc n)) k ⟩
      fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k or
        fst (fst freeℕ→ℕFinCof (singleEntry α (suc n))) k
        ≡⟨ cong₂ _or_ (eval-embedUpTo-above α n k (≤-trans ≤-sucℕ k>sn))
                       (eval-singleEntry-neq (suc n) k α (<→≢ k>sn)) ⟩
      false ∎

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

    eval-embedUpTo-fst : (α : binarySequence) (n : ℕ) (bound : isZeroFrom (suc n) α) →
      fst (fst freeℕ→ℕFinCof (embedUpTo α n)) ≡ α
    eval-embedUpTo-fst α n bound = funExt λ k →
      case (splitℕ-≤ k n) return (λ _ → fst (fst freeℕ→ℕFinCof (embedUpTo α n)) k ≡ α k) of λ
        { (inl k≤n) → eval-embedUpTo-below α n k k≤n
        ; (inr n<k) → eval-embedUpTo-above α n k n<k ∙ sym (bound k n<k)
        }

  section-finite : (α : binarySequence) (αf : isFinite α) →
    fst freeℕ→ℕFinCof (Finite→FreeℕMap α αf) ≡ (α , Fin αf)
  section-finite α (constant0 α=0) = FH.pres0 ∙ FC≡ (funExt (λ k → sym (α=0 k zero-≤)))
  section-finite α (last1 n αn=1 α>n=0) = FC≡ (eval-embedUpTo-fst α n α>n=0)

  section-cofinite : (α : binarySequence) (αc : isCofinite α) →
    fst freeℕ→ℕFinCof (¬ (Finite→FreeℕMap (¬ α) αc)) ≡ (α , Cof αc)
  section-cofinite α αc =
    fst freeℕ→ℕFinCof (¬ (Finite→FreeℕMap (¬ α) αc))
      ≡⟨ fH-pres-¬ (Finite→FreeℕMap (¬ α) αc) ⟩
    ¬ fst freeℕ→ℕFinCof (Finite→FreeℕMap (¬ α) αc)
      ≡⟨ cong ¬_ (section-finite (¬ α) αc) ⟩
    ¬ (¬ α , Fin αc)
      ≡⟨ FC≡ (funExt (λ k → notnot (α k))) ⟩
    (α , Cof αc) ∎

  fH-section : (x : ⟨ ℕfinCofinBA ⟩) → fst freeℕ→ℕFinCof (ℕFinCof→FreeℕMap x) ≡ x
  fH-section (α , Fin αf) = section-finite α αf
  fH-section (α , Cof αc) = section-cofinite α αc

  singleEntry-δ-diag : (n : ℕ) → singleEntry (δSequence n) n ≡ generator n
  singleEntry-δ-diag n with δSequence n n | δnn=1 n
  ... | true  | _ = refl
  ... | false | p = ex-falso (false≢true p)

  singleEntry-δ-neq : (n m : ℕ) → (n ≡ m → ⊥) → singleEntry (δSequence n) m ≡ 𝟘
  singleEntry-δ-neq n m n≠m with δSequence n m | δnm=0 n m n≠m
  ... | false | _ = refl
  ... | true  | p = ex-falso (true≢false p)

  embedUpTo-δ-below : (n m : ℕ) → m < n → embedUpTo (δSequence n) m ≡ 𝟘
  embedUpTo-δ-below n zero m<n =
    singleEntry-δ-neq n 0 (<→≢ m<n ∘ sym)
  embedUpTo-δ-below n (suc m) sm<n =
    cong₂ _∨_ (embedUpTo-δ-below n m (≤-trans ≤-sucℕ sm<n))
               (singleEntry-δ-neq n (suc m) (<→≢ sm<n ∘ sym))
    ∙ ∨IdL

  embedUpTo-δ-n : (n : ℕ) → embedUpTo (δSequence n) n ≡ generator n
  embedUpTo-δ-n zero = singleEntry-δ-diag 0
  embedUpTo-δ-n (suc n) =
    cong₂ _∨_ (embedUpTo-δ-below (suc n) n ≤-refl)
               (singleEntry-δ-diag (suc n))
    ∙ ∨IdL

  singleton→gen : (n : ℕ) → ℕFinCof→Presentation (singleton n) ≡ fst π (generator n)
  singleton→gen n = cong (fst π) (embedUpTo-δ-n n)

  module ΠHAlg = isBoolAlgHom (freeBA ℕ) presentation (fst π) (snd π)
  ΠH-pres¬ = ΠHAlg.pres¬
  ΠH-pres-∨ = ΠHAlg.pres∨

  pres¬-map : (x : ⟨ ℕfinCofinBA ⟩) →
    ℕFinCof→Presentation (¬ x) ≡ ¬ (ℕFinCof→Presentation x)
  pres¬-map (α , Fin αf) =
    let nn-eq : (λ n → not (not (α n))) ≡ α
        nn-eq = funExt (λ k → notnot (α k))
    in cong ℕFinCof→Presentation (FC≡ {b = ¬ α , Cof (¬FinIsCofin α αf)} refl)
     ∙ cong (fst π) (cong ¬_ (cong₂ Finite→FreeℕMap nn-eq
         (isProp→PathP (λ i → isPropIsFinite (nn-eq i)) (¬FinIsCofin α αf) αf)))
     ∙ ΠH-pres¬ _
  pres¬-map (α , Cof αc) =
    cong ℕFinCof→Presentation (FC≡ {b = ¬ α , Fin αc} refl)
    ∙ sym (cong ¬_ (ΠH-pres¬ t) ∙ ¬Invol)
    where t = Finite→FreeℕMap (¬ α) αc

  relations-neq : (i j : ℕ) → (i ≡ j → ⊥) → relations (i , j) ≡ generator i · generator j
  relations-neq i j i≠j with discreteℕ i j
  ... | yes p = ex-falso (i≠j p)
  ... | no _ = refl

  gen-orth : (i j : ℕ) → (i ≡ j → ⊥) → fst π (generator i · generator j) ≡ 𝟘
  gen-orth i j i≠j =
    cong (fst π) (sym (relations-neq i j i≠j)
                  ∙ sym (cong relations (Iso.ret ℕ×ℕ≅ℕ (i , j))))
    ∙ QB.zeroOnImage (Iso.fun ℕ×ℕ≅ℕ (i , j))

  SE-prod-diag : (α β : binarySequence) (m : ℕ) →
    singleEntry α m · singleEntry β m ≡ singleEntry (λ k → α k and β k) m
  SE-prod-diag α β m with α m | β m
  ... | true  | true  = ∧Idem
  ... | true  | false = ∧AnnihilR
  ... | false | true  = ∧AnnihilL
  ... | false | false = ∧AnnihilL

  π-SE-prod-neq : (α β : binarySequence) (i j : ℕ) → (i ≡ j → ⊥) →
    fst π (singleEntry α i · singleEntry β j) ≡ 𝟘
  π-SE-prod-neq α β i j i≠j with α i | β j
  ... | true  | true  = gen-orth i j i≠j
  ... | true  | false = cong (fst π) ∧AnnihilR ∙ ΠH.pres0
  ... | false | true  = cong (fst π) ∧AnnihilL ∙ ΠH.pres0
  ... | false | false = cong (fst π) ∧AnnihilL ∙ ΠH.pres0

  SE-false : (α : binarySequence) (m : ℕ) → α m ≡ false → singleEntry α m ≡ 𝟘
  SE-false α m p with α m
  ... | false = refl
  ... | true = ex-falso (true≢false p)

  embedUpTo-ext-zero : (γ : binarySequence) (k : ℕ) → γ (suc k) ≡ false →
    embedUpTo γ (suc k) ≡ embedUpTo γ k
  embedUpTo-ext-zero γ k p = cong (embedUpTo γ k ∨_) (SE-false γ (suc k) p) ∙ ∨IdR

  embedUpTo-shrink : (γ : binarySequence) (n m : ℕ) →
    isZeroFrom (suc m) γ → m ≤ n → embedUpTo γ n ≡ embedUpTo γ m
  embedUpTo-shrink γ zero m γ>m m≤0 = cong (embedUpTo γ) (sym (≤0→≡0 m≤0))
  embedUpTo-shrink γ (suc n) m γ>m m≤sn = case ≤-split m≤sn of λ
    { (inl m<sn) → embedUpTo-ext-zero γ n (γ>m (suc n) m<sn)
                    ∙ embedUpTo-shrink γ n m γ>m (pred-≤-pred m<sn)
    ; (inr m=sn) → cong (embedUpTo γ) (sym m=sn)
    }

  embedUpTo-zero : (γ : binarySequence) (n : ℕ) → isZeroFrom 0 γ → embedUpTo γ n ≡ 𝟘
  embedUpTo-zero γ zero γ=0 = SE-false γ 0 (γ=0 0 zero-≤)
  embedUpTo-zero γ (suc n) γ=0 =
    embedUpTo-ext-zero γ n (γ=0 (suc n) zero-≤) ∙ embedUpTo-zero γ n γ=0

  F2FM-to-embedUpTo : (γ : binarySequence) (n : ℕ) (γ>n : isZeroFrom (suc n) γ)
    (gf : isFinite γ) → embedUpTo γ n ≡ Finite→FreeℕMap γ gf
  F2FM-to-embedUpTo γ n γ>n (constant0 γ=0) = embedUpTo-zero γ n γ=0
  F2FM-to-embedUpTo γ n γ>n (last1 p γp γ>p) =
    embedUpTo-shrink γ n p γ>p p≤n
    where
      p≤n : p ≤ n
      p≤n with splitℕ-≤ p n
      ... | inl p≤n = p≤n
      ... | inr n<p = ex-falso (true≢false (sym γp ∙ γ>n p n<p))

  opaque
    π-SE-times-eU-above : (α β : binarySequence) (i m : ℕ) → m < i →
      fst π (singleEntry α i · embedUpTo β m) ≡ 𝟘
    π-SE-times-eU-above α β i zero m<i =
      π-SE-prod-neq α β i 0 (<→≢ m<i ∘ sym)
    π-SE-times-eU-above α β i (suc m') m<i =
      let a = singleEntry α i ; b = embedUpTo β m' ; c = singleEntry β (suc m')
      in
      fst π (a · (b ∨ c))
        ≡⟨ cong (fst π) (∧DistR∨ {x = a}) ⟩
      fst π (a · b ∨ a · c)
        ≡⟨ ΠH-pres-∨ _ _ ⟩
      fst π (a · b) ∨ fst π (a · c)
        ≡⟨ cong₂ _∨_ (π-SE-times-eU-above α β i m' (≤-trans ≤-sucℕ m<i))
                      (π-SE-prod-neq α β i (suc m') (<→≢ m<i ∘ sym)) ⟩
      𝟘 ∨ 𝟘
        ≡⟨ ∨IdL ⟩
      𝟘 ∎

    π-SE-times-eU-below : (α β : binarySequence) (i m : ℕ) → i ≤ m →
      fst π (singleEntry α i · embedUpTo β m) ≡ fst π (singleEntry (λ k → α k and β k) i)
    π-SE-times-eU-below α β i zero i≤0 =
      cong (λ i' → fst π (singleEntry α i' · singleEntry β 0)) (≤0→≡0 i≤0)
      ∙ cong (fst π) (SE-prod-diag α β 0)
      ∙ cong (λ i' → fst π (singleEntry (λ k → α k and β k) i')) (sym (≤0→≡0 i≤0))
    π-SE-times-eU-below α β i (suc m') i≤sm' =
      cong (fst π) (∧DistR∨ {x = singleEntry α i})
      ∙ ΠH-pres-∨ _ _
      ∙ (case (≤-split i≤sm') return (λ _ →
          fst π (singleEntry α i · embedUpTo β m') ∨
          fst π (singleEntry α i · singleEntry β (suc m'))
          ≡ fst π (singleEntry (λ k → α k and β k) i)) of λ
        { (inl i<sm') →
            cong₂ _∨_ (π-SE-times-eU-below α β i m' (pred-≤-pred i<sm'))
                        (π-SE-prod-neq α β i (suc m') (<→≢ i<sm'))
            ∙ ∨IdR
        ; (inr i=sm') →
            cong₂ _∨_
              (π-SE-times-eU-above α β i m' (subst (_> m') (sym i=sm') ≤-refl))
              (cong (λ j → fst π (singleEntry α j · singleEntry β (suc m'))) i=sm'
               ∙ cong (fst π) (SE-prod-diag α β (suc m'))
               ∙ cong (λ j → fst π (singleEntry (λ k → α k and β k) j)) (sym i=sm'))
            ∙ ∨IdL
        })

    π-embedUpTo-prod : (α β : binarySequence) (n m : ℕ) → n ≤ m →
      fst π (embedUpTo α n · embedUpTo β m)
      ≡ fst π (embedUpTo (λ k → α k and β k) n)
    π-embedUpTo-prod α β zero m 0≤m =
      π-SE-times-eU-below α β 0 m 0≤m
    π-embedUpTo-prod α β (suc n') m sn≤m =
      cong (fst π) (∧DistL∨ {z = embedUpTo β m})
      ∙ ΠH-pres-∨ _ _
      ∙ cong₂ _∨_
          (π-embedUpTo-prod α β n' m (≤-trans ≤-sucℕ sn≤m))
          (π-SE-times-eU-below α β (suc n') m sn≤m)
      ∙ sym (ΠH-pres-∨ _ _)

  ∧-zeroFrom : (α β : binarySequence) (n : ℕ) →
    isZeroFrom (suc n) α → isZeroFrom (suc n) (λ k → α k and β k)
  ∧-zeroFrom α β n α>n k k>n = cong (_and β k) (α>n k k>n)

  ∧-zeroFromR : (α β : binarySequence) (m : ℕ) →
    isZeroFrom (suc m) β → isZeroFrom (suc m) (λ k → α k and β k)
  ∧-zeroFromR α β m β>m k k>m = cong (α k and_) (β>m k k>m) ∙ and-zeroʳ (α k)

  ∧-seq-comm : (α β : binarySequence) →
    (λ k → β k and α k) ≡ (λ k → α k and β k)
  ∧-seq-comm α β = funExt (λ k → and-comm (β k) (α k))

  opaque
    unfolding π-embedUpTo-prod
    pres∧-FF : (α β : binarySequence) (αf : isFinite α) (βf : isFinite β) →
      ℕFinCof→Presentation (α ∧ β , Fin (intersectionWithFiniteIsFinite α β αf))
      ≡ fst π (Finite→FreeℕMap α αf) · fst π (Finite→FreeℕMap β βf)
    pres∧-FF α β (constant0 α=0) βf =
      let αβ=0 : isFinite (λ k → α k and β k)
          αβ=0 = constant0 (λ k _ → cong (_and β k) (α=0 k zero-≤))
      in cong (fst π) (cong (Finite→FreeℕMap _) (isPropIsFinite _ (intersectionWithFiniteIsFinite α β (constant0 α=0)) αβ=0))
       ∙ sym (cong (fst π) (∧AnnihilL {x = Finite→FreeℕMap β βf}))
       ∙ ΠH.pres· 𝟘 (Finite→FreeℕMap β βf)
    pres∧-FF α β (last1 n αn α>n) (constant0 β=0) =
      let αβ=0 : isFinite (λ k → α k and β k)
          αβ=0 = constant0 (λ k _ → cong (α k and_) (β=0 k zero-≤) ∙ and-zeroʳ (α k))
      in cong (fst π) (cong (Finite→FreeℕMap _) (isPropIsFinite _ (intersectionWithFiniteIsFinite α β (last1 n αn α>n)) αβ=0))
       ∙ sym (cong (fst π) (∧AnnihilR {x = Finite→FreeℕMap α (last1 n αn α>n)}))
       ∙ ΠH.pres· (Finite→FreeℕMap α (last1 n αn α>n)) 𝟘
    pres∧-FF α β (last1 n αn α>n) (last1 m βm β>m) with splitℕ-≤ n m
    ... | inl n≤m =
      cong (fst π) (sym (F2FM-to-embedUpTo _ n (∧-zeroFrom α β n α>n) abf))
      ∙ sym (π-embedUpTo-prod α β n m n≤m)
      ∙ ΠH.pres· _ _
      where abf : isFinite (λ k → α k and β k)
            abf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)
    ... | inr m<n =
      cong (fst π) (sym (F2FM-to-embedUpTo _ m (∧-zeroFromR α β m β>m) abf)
                    ∙ cong (λ f → embedUpTo f m) (sym (∧-seq-comm α β)))
      ∙ sym (π-embedUpTo-prod β α m n (≤-trans ≤-sucℕ m<n))
      ∙ cong (fst π) (·Comm _ _)
      ∙ ΠH.pres· _ _
      where abf : isFinite (λ k → α k and β k)
            abf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)

  embedUpToFlat : (α : binarySequence) → (m : ℕ) → ⟨ freeBA ℕ ⟩
  embedUpToFlat α zero = singleEntry α 0
  embedUpToFlat α (suc m) = embedUpToFlat α m + singleEntry α (suc m)

  SE-and-split : (α β : binarySequence) (k : ℕ) →
    singleEntry α k + singleEntry (λ j → α j and not (β j)) k
    ≡ singleEntry (λ j → α j and β j) k
  SE-and-split α β k with α k | β k
  ... | false | false = +IdL _
  ... | false | true  = +IdL _
  ... | true  | true  = +IdR _
  ... | true  | false = characteristic2

  rearrange-sum : (a b c d : ⟨ freeBA ℕ ⟩) →
    (a + b) + (c + d) ≡ (a + c) + (b + d)
  rearrange-sum a b c d = solve! (BooleanRing→CommRing (freeBA ℕ))

  flat-and-split : (α β : binarySequence) (n : ℕ) →
    embedUpToFlat α n + embedUpToFlat (λ k → α k and not (β k)) n
    ≡ embedUpToFlat (λ k → α k and β k) n
  flat-and-split α β zero = SE-and-split α β 0
  flat-and-split α β (suc n) =
    rearrange-sum (embedUpToFlat α n) (singleEntry α (suc n))
                  (embedUpToFlat (λ k → α k and not (β k)) n)
                  (singleEntry (λ k → α k and not (β k)) (suc n))
    ∙ cong₂ _+_ (flat-and-split α β n) (SE-and-split α β (suc n))

  ∨-as-+ : (a b : ⟨ freeBA ℕ ⟩) → fst π (a · b) ≡ 𝟘 →
    fst π (a ∨ b) ≡ fst π a + fst π b
  ∨-as-+ a b orth =
    ΠH-pres-∨ a b
    ∙ cong ((fst π a + fst π b) +_) (sym (ΠH.pres· a b) ∙ orth)
    ∙ +IdR _

  opaque
    unfolding π-SE-times-eU-above
    π-eU-to-flat : (γ : binarySequence) (n : ℕ) →
      fst π (embedUpTo γ n) ≡ fst π (embedUpToFlat γ n)
    π-eU-to-flat γ zero = refl
    π-eU-to-flat γ (suc n) =
      ∨-as-+ (embedUpTo γ n) (singleEntry γ (suc n))
        (cong (fst π) (·Comm (embedUpTo γ n) (singleEntry γ (suc n)))
         ∙ π-SE-times-eU-above γ γ (suc n) n ≤-refl)
      ∙ cong (_+ fst π (singleEntry γ (suc n))) (π-eU-to-flat γ n)
      ∙ sym (ΠH.pres+ (embedUpToFlat γ n) (singleEntry γ (suc n)))

    π-eU-and-split : (α β : binarySequence) (n : ℕ) →
      fst π (embedUpTo (λ k → α k and β k) n)
      ≡ fst π (embedUpTo α n + embedUpTo (λ k → α k and not (β k)) n)
    π-eU-and-split α β n =
      π-eU-to-flat (λ k → α k and β k) n
      ∙ cong (fst π) (sym (flat-and-split α β n))
      ∙ ΠH.pres+ (embedUpToFlat α n) (embedUpToFlat (λ k → α k and not (β k)) n)
      ∙ cong₂ _+_ (sym (π-eU-to-flat α n)) (sym (π-eU-to-flat (λ k → α k and not (β k)) n))
      ∙ sym (ΠH.pres+ (embedUpTo α n) (embedUpTo (λ k → α k and not (β k)) n))

  ·-distrib-¬ : (a b : ⟨ presentation ⟩) → a · (𝟙 + b) ≡ a + a · b
  ·-distrib-¬ a b = solve! (BooleanRing→CommRing presentation)

  opaque
    unfolding pres∧-FF
    unfolding π-eU-and-split
    pres∧-FC : (α β : binarySequence) (αf : isFinite α) (βc : isCofinite β) →
      ℕFinCof→Presentation (α ∧ β , Fin (intersectionWithFiniteIsFinite α β αf))
      ≡ fst π (Finite→FreeℕMap α αf) · fst π (¬ (Finite→FreeℕMap (¬ β) βc))
    pres∧-FC α β (constant0 α=0) βc =
      let αβf : isFinite (λ k → α k and β k)
          αβf = intersectionWithFiniteIsFinite α β (constant0 α=0)
          αβ0 : isFinite (λ k → α k and β k)
          αβ0 = constant0 (λ k _ → cong (_and β k) (α=0 k zero-≤))
      in cong (fst π) (cong (Finite→FreeℕMap _) (isPropIsFinite _ αβf αβ0))
       ∙ sym (cong (fst π) (∧AnnihilL {x = ¬ (Finite→FreeℕMap (¬ β) βc)}))
       ∙ ΠH.pres· 𝟘 (¬ (Finite→FreeℕMap (¬ β) βc))
    pres∧-FC α β (last1 n αn α>n) βc =
      let αβf = intersectionWithFiniteIsFinite α β (last1 n αn α>n)
          α¬βf = intersectionWithFiniteIsFinite α (¬ β) (last1 n αn α>n)
          a = embedUpTo α n
          b = Finite→FreeℕMap (¬ β) βc
      in cong (fst π) (sym (F2FM-to-embedUpTo _ n (∧-zeroFrom α β n α>n) αβf))
       ∙ π-eU-and-split α β n
       ∙ ΠH.pres+ a (embedUpTo (λ k → α k and not (β k)) n)
       ∙ cong (fst π a +_)
              (cong (fst π) (F2FM-to-embedUpTo _ n (∧-zeroFrom α (¬ β) n α>n) α¬βf)
               ∙ pres∧-FF α (¬ β) (last1 n αn α>n) βc)
       ∙ sym (cong (fst π a ·_) (ΠH-pres¬ b) ∙ ·-distrib-¬ (fst π a) (fst π b))

  not-and-is-or-not : (a b : Bool) → not (a and b) ≡ not a or not b
  not-and-is-or-not false false = refl
  not-and-is-or-not false true  = refl
  not-and-is-or-not true  false = refl
  not-and-is-or-not true  true  = refl

  singleEntry-or-split : (α β : binarySequence) (m : ℕ) →
    singleEntry (λ k → α k or β k) m ≡ singleEntry α m ∨ singleEntry β m
  singleEntry-or-split α β m with α m | β m
  ... | false | false = sym ∨IdL
  ... | false | true  = sym ∨IdL
  ... | true  | false = sym ∨IdR
  ... | true  | true  = sym ∨Idem

  rearrange-∨ : (a b c d : ⟨ freeBA ℕ ⟩) →
    (a ∨ b) ∨ (c ∨ d) ≡ (a ∨ c) ∨ (b ∨ d)
  rearrange-∨ a b c d = solve! (BooleanRing→CommRing (freeBA ℕ))

  embedUpTo-or-split : (α β : binarySequence) (n : ℕ) →
    embedUpTo (λ k → α k or β k) n ≡ embedUpTo α n ∨ embedUpTo β n
  embedUpTo-or-split α β zero = singleEntry-or-split α β 0
  embedUpTo-or-split α β (suc n) =
    cong₂ _∨_ (embedUpTo-or-split α β n) (singleEntry-or-split α β (suc n))
    ∙ rearrange-∨ (embedUpTo α n) (embedUpTo β n)
                   (singleEntry α (suc n)) (singleEntry β (suc n))

  ∨-zeroFrom : (α β : binarySequence) (n : ℕ) →
    isZeroFrom n α → isZeroFrom n β → isZeroFrom n (λ k → α k or β k)
  ∨-zeroFrom α β n α>n β>n k k≥n = cong₂ _or_ (α>n k k≥n) (β>n k k≥n)

  opaque
    unfolding π-embedUpTo-prod
    pres∨-FinFin : (α β : binarySequence) (αf : isFinite α) (βf : isFinite β)
      (unionf : isFinite (λ k → α k or β k)) →
      fst π (Finite→FreeℕMap (λ k → α k or β k) unionf)
      ≡ fst π (Finite→FreeℕMap α αf ∨ Finite→FreeℕMap β βf)
    pres∨-FinFin α β (constant0 α=0) βf unionf =
      let seq-eq : (λ k → α k or β k) ≡ β
          seq-eq = funExt (λ k → cong (_or β k) (α=0 k zero-≤))
      in cong (fst π) (cong₂ Finite→FreeℕMap seq-eq
                              (isProp→PathP (λ i → isPropIsFinite (seq-eq i)) unionf βf))
       ∙ sym (cong (fst π) ∨IdL)
    pres∨-FinFin α β (last1 n αn α>n) (constant0 β=0) unionf =
      let seq-eq : (λ k → α k or β k) ≡ α
          seq-eq = funExt (λ k → cong (α k or_) (β=0 k zero-≤) ∙ or-identityʳ (α k))
      in cong (fst π) (cong₂ Finite→FreeℕMap seq-eq
                              (isProp→PathP (λ i → isPropIsFinite (seq-eq i)) unionf (last1 n αn α>n)))
       ∙ sym (cong (fst π) ∨IdR)
    pres∨-FinFin α β (last1 n αn α>n) (last1 m βm β>m) unionf with n =ℕ m
    ... | lt n<m =
      let α>m : isZeroFrom (suc m) α
          α>m k k>m = α>n k (≤-trans n<m (≤-trans ≤-sucℕ k>m))
          or>m = ∨-zeroFrom α β (suc m) α>m β>m
      in cong (fst π) (sym (F2FM-to-embedUpTo _ m or>m unionf)
                        ∙ embedUpTo-or-split α β m
                        ∙ cong₂ _∨_ (F2FM-to-embedUpTo α m α>m (last1 n αn α>n)) refl)
    ... | eq n=m =
      let β>n : isZeroFrom (suc n) β
          β>n k k>n = β>m k (subst (_≤ k) (cong suc n=m) k>n)
          or>n = ∨-zeroFrom α β (suc n) α>n β>n
      in cong (fst π) (sym (F2FM-to-embedUpTo _ n or>n unionf)
                        ∙ embedUpTo-or-split α β n
                        ∙ cong (embedUpTo α n ∨_) (cong (embedUpTo β) n=m))
    ... | gt n>m =
      let β>n : isZeroFrom (suc n) β
          β>n k k>n = β>m k (≤-trans n>m (≤-trans ≤-sucℕ k>n))
          or>n = ∨-zeroFrom α β (suc n) α>n β>n
      in cong (fst π) (sym (F2FM-to-embedUpTo _ n or>n unionf)
                        ∙ embedUpTo-or-split α β n
                        ∙ cong₂ _∨_ refl (F2FM-to-embedUpTo β n β>n (last1 m βm β>m)))

  pres∧-map : (x y : ⟨ ℕfinCofinBA ⟩) →
    ℕFinCof→Presentation (x ∧ y) ≡ (ℕFinCof→Presentation x) ∧ (ℕFinCof→Presentation y)
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
    ∙ ∧Comm
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
     ∙ cong (fst π ∘ ¬_) (cong₂ Finite→FreeℕMap not-and-seq
                                   (isProp→PathP (λ i → isPropIsFinite (not-and-seq i)) cofp orf))
     ∙ ΠH-pres¬ (Finite→FreeℕMap (λ k → not (α k) or not (β k)) orf)
     ∙ cong ¬_ (pres∨-FinFin (¬ α) (¬ β) αc βc orf)
     ∙ sym (ΠH-pres¬ (a ∨ b))
     ∙ cong (fst π) DeMorgan¬∨
     ∙ ΠH.pres· (¬ a) (¬ b)

  ℕFinCof→PresentationIsHom : IsCommRingHom
    (BooleanRingStr→CommRingStr (snd ℕfinCofinBA))
    ℕFinCof→Presentation
    (BooleanRingStr→CommRingStr (snd presentation))
  ℕFinCof→PresentationIsHom =
    FromPres¬∧.isBoolRingHom ℕfinCofinBA presentation ℕFinCof→Presentation
      pres¬-map pres∧-map

  ℕFinCof→PresentationHom : BoolHom ℕfinCofinBA presentation
  ℕFinCof→PresentationHom = ℕFinCof→Presentation , ℕFinCof→PresentationIsHom

  compBH : BoolHom (freeBA ℕ) presentation
  compBH = ℕFinCof→PresentationHom ∘cr freeℕ→ℕFinCof

  roundtrip-pre-on-free : (t : ⟨ freeBA ℕ ⟩) →
    ℕFinCof→Presentation (fst freeℕ→ℕFinCof t) ≡ fst π t
  roundtrip-pre-on-free t = cong (λ h → fst h t)
    (compBH
      ≡⟨ sym (inducedBAHomUnique ℕ presentation (λ n → fst π (generator n))
              compBH
              (funExt λ n → cong ℕFinCof→Presentation (eval-gen n) ∙ singleton→gen n)) ⟩
    inducedBAHom ℕ presentation (λ n → fst π (generator n))
      ≡⟨ inducedBAHomUnique ℕ presentation (λ n → fst π (generator n)) π refl ⟩
    π ∎)

  extensionMap : (S : BooleanRing ℓ-zero) (g : BoolHom (freeBA ℕ) S)
    (g-zero : ∀ n → g $cr (relationsℕ n) ≡ BooleanRingStr.𝟘 (snd S))
    → BoolHom ℕfinCofinBA S
  extensionMap S g g-zero = QB.inducedHom S g g-zero ∘cr ℕFinCof→PresentationHom

  opaque
    unfolding QB.inducedHom
    unfolding QB.quotientImageHom
    extensionCommutes : (S : BooleanRing ℓ-zero) (g : BoolHom (freeBA ℕ) S)
      (g-zero : ∀ n → g $cr (relationsℕ n) ≡ BooleanRingStr.𝟘 (snd S))
      → extensionMap S g g-zero ∘cr freeℕ→ℕFinCof ≡ g
    extensionCommutes S g g-zero = CommRingHom≡ (funExt λ t →
      let ind = fst (QB.inducedHom S g g-zero)
      in
      ind (ℕFinCof→Presentation (fst freeℕ→ℕFinCof t))
        ≡⟨ cong ind (roundtrip-pre-on-free t) ⟩
      ind (fst π t)
        ≡⟨ cong (λ h → fst h t) (QB.evalInduce S {g} {g-zero}) ⟩
      fst g t ∎)

    extensionUnique : (S : BooleanRing ℓ-zero) (g : BoolHom (freeBA ℕ) S)
      (g-zero : ∀ n → g $cr (relationsℕ n) ≡ BooleanRingStr.𝟘 (snd S))
      (h : BoolHom ℕfinCofinBA S) → g ≡ h ∘cr freeℕ→ℕFinCof
      → extensionMap S g g-zero ≡ h
    extensionUnique S g g-zero h g≡h∘φ = CommRingHom≡ $ funExt λ x →
      let ext = fst (extensionMap S g g-zero)
          y = ℕFinCof→FreeℕMap x
      in
      ext x
        ≡⟨ cong ext (sym (fH-section x)) ⟩
      ext (fst freeℕ→ℕFinCof y)
        ≡⟨ cong (λ h → fst h y) (extensionCommutes S g g-zero) ⟩
      fst g y
        ≡⟨ cong (λ h → fst h y) g≡h∘φ ⟩
      fst h (fst freeℕ→ℕFinCof y)
        ≡⟨ cong (fst h) (fH-section x) ⟩
      fst h x ∎

open NFinCofinPresentation
open UniversalProperty
  (freeBA ℕ) relationsℕ ℕfinCofinBA freeℕ→ℕFinCof relationsℕRespected
  extensionMap extensionCommutes extensionUnique

ℕFinCof=Presentation : BooleanRingEquiv presentation ℕfinCofinBA
ℕFinCof=Presentation = quotientUniversalPropertyEquiv

ℕFinCof-has-quotient-freeℕ-presentation : has-quotient-of-freeℕ-presentation ℕfinCofinBA
ℕFinCof-has-quotient-freeℕ-presentation .fst = relationsℕ
ℕFinCof-has-quotient-freeℕ-presentation .snd = invBooleanRingEquiv presentation ℕfinCofinBA ℕFinCof=Presentation 

ℕfinCofinIsCountablyPresented : is-countably-presented-alt ℕfinCofinBA
ℕfinCofinIsCountablyPresented =  ∣ ℕFinCof-has-quotient-freeℕ-presentation ∣₁ 
