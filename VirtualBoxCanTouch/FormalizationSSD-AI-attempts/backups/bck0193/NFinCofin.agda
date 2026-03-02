{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.NFinCofin where
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open  import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.AlgebraicFacts
open import Cubical.Foundations.Equiv
open import Cubical.Tactics.NatSolver
open import Cubical.Tactics.CommRingSolver
open import BooleanRing.BooleanRingMaps
open import BooleanRing.SubBooleanRing
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_) 
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Base
open import Cubical.Algebra.CommRing.Instances.Bool

open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Bool renaming ( _≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Algebra.CommRing.Instances.Unit
open import QuickFixes

module QuickBooleanFix where
  open BooleanAlgebraStr BoolBR 
  claim : (a b : Bool) → (a ∨ b) ≡ a or b
  claim false false = refl
  claim false true  = refl
  claim true  false = refl
  claim true  true  = refl 

booleanStructureOnBinarySequences : BooleanRingStr binarySequence
booleanStructureOnBinarySequences = pointWiseStructure ℕ (λ _ → Bool) (λ _ → snd BoolBR)

ℙℕ : BooleanRing ℓ-zero
ℙℕ = binarySequence , booleanStructureOnBinarySequences


module ℕFinCofin where
  open BooleanAlgebraStr ℙℕ

  isZeroFrom : ℕ → binarySequence → Type
  isZeroFrom n α = ∀ (k : ℕ) → (k ≥ n) → α k ≡ false

  data isFinite (α : binarySequence) : Type where
    constant0 : isZeroFrom 0 α → isFinite α
    last1 : (n : ℕ) → (α n ≡ true) → isZeroFrom (suc n) α → isFinite α

  bounded→Finite : (α : binarySequence) → (n : ℕ) → isZeroFrom n α → isFinite α
  bounded→Finite α zero α≥n=0 = constant0 α≥n=0 
  bounded→Finite α (suc n) α>n=0 = case (α n =B false) return (λ _ → isFinite α) of λ 
    { (yes αn=0) → bounded→Finite α n λ k k≥n → case ≤-split k≥n of λ
              { (inl k>n) → α>n=0 k k>n
              ; (inr k=n) → sym (cong α k=n) ∙ αn=0 }
    ; (no αn≠0) → last1 n (¬false→true (α n) αn≠0) α>n=0 } 
   
  finite→Bounded : (α : binarySequence) → isFinite α → Σ[ n ∈ ℕ ] isZeroFrom n α
  finite→Bounded α (constant0 x) = 0 , x
  finite→Bounded α (last1 n _ x) = suc n , x 

  isPropIsFinite : (α : binarySequence) → isProp (isFinite α)
  isPropIsFinite α (constant0 α=0) (constant0 α=0') = 
    cong constant0 (isPropΠ2 (λ _ _ → isSetBool _ _) α=0 α=0') 
  isPropIsFinite α (constant0 α=0) (last1 n αn=1 _) = 
    ex-falso (false≢true (sym (α=0 n zero-≤) ∙ αn=1))
  isPropIsFinite α (last1 n αn=1 _) (constant0 α=0) = 
    ex-falso (false≢true (sym (α=0 n zero-≤) ∙ αn=1))
  isPropIsFinite α (last1 n αn=1 α>n=0) (last1 m αm=1 α>m=0) = 
    case (n =ℕ m) return (λ _ → last1 n αn=1 α>n=0 ≡ last1 m αm=1 α>m=0) of λ 
    { (lt n<m) → ex-falso $ true≢false $ sym αm=1 ∙ α>n=0 m n<m
    ; (gt n>m) → ex-falso $ true≢false $ sym αn=1 ∙ α>m=0 n n>m 
    ; (eq n=m) → cong₃ last1 n=m 
                 (isProp→PathP (λ _ → isSetBool _ _) αn=1 αm=1) 
                 (isProp→PathP (λ _ → isPropΠ2 λ _ _ → isSetBool _ _) α>n=0 α>m=0)
    }

  intersectWithBoundedIsBounded : (α β : binarySequence) → (n : ℕ) → isZeroFrom n α → isZeroFrom n (α ∧ β)
  intersectWithBoundedIsBounded α β n α≥n=0 k k≥n = cong (λ a → a and β k) (α≥n=0 k k≥n) 

  intersectionWithFiniteIsFinite : (α β : binarySequence) → isFinite α → isFinite (α ∧ β) 
  intersectionWithFiniteIsFinite α β αFin = case finite→Bounded α αFin of 
    λ (n , α≥n=0) → bounded→Finite (α ∧ β) n (intersectWithBoundedIsBounded α β n α≥n=0)

  disjunction-max : (α β : binarySequence) → (n m : ℕ) → isZeroFrom n α → isZeroFrom m β → isZeroFrom (max n m) (α ∨ β)
  disjunction-max α β n m α≥n=0 β≥m=0 k k≥mn = 
    (α ∨ β) k 
      ≡⟨ QuickBooleanFix.claim (α k) (β k) ⟩
    α k or β k 
      ≡⟨ cong₂ _or_ (α≥n=0 k (≤-trans (left-≤-max  {n = m}) k≥mn)) 
                    (β≥m=0 k (≤-trans (right-≤-max {m = n}) k≥mn)) ⟩ 
    false ∎  

  finiteClosedByUnion : (α β : binarySequence) → isFinite α → isFinite β → isFinite (α ∨ β)
  finiteClosedByUnion α β αFin βFin = case (finite→Bounded α  αFin , finite→Bounded β βFin) of λ 
    ((n , α≥n=0) , (m , β≥m=0)) → bounded→Finite (α ∨ β) (max n m) 
    (disjunction-max α β n m α≥n=0 β≥m=0)  

  isCofinite : binarySequence → Type 
  isCofinite α = isFinite (¬ α)

  Finite≢Cofinite : (α : binarySequence) → isFinite α → isCofinite α → ⊥ 
  Finite≢Cofinite α (constant0 α=0) (constant0 ¬α=0) = true≢false $
    true ≡⟨ cong not (sym $ α=0 0 zero-≤) ⟩
    not (α 0) ≡⟨ ¬α=0 0 ≤-refl ⟩ 
    false ∎ 
  Finite≢Cofinite α (constant0 α=0) (last1 n _ ¬α>n=0) = true≢false $ 
    true ≡⟨ cong not (sym $ α=0 (suc n) zero-≤) ⟩
    not (α (suc n)) ≡⟨ ¬α>n=0 (suc n) ≤-refl ⟩ 
    false ∎ 
  Finite≢Cofinite α (last1 n _ α>n=0) (constant0 ¬α=0) = false≢true $ 
    false ≡⟨ (sym $ ¬α=0 (suc n) zero-≤) ⟩
    (not (α (suc n))) ≡⟨ cong not (α>n=0 (suc n) ≤-refl) ⟩ 
    true ∎ 
  Finite≢Cofinite α (last1 n αn=1 α>n=0) (last1 m ¬αm=1 ¬α>m=0) = false≢true $ 
    false ≡⟨ sym (¬α>m=0 Smaxnm $ right-≤-max {m = suc n}) ⟩ 
    not (α Smaxnm) ≡⟨ cong not (α>n=0 Smaxnm $ left-≤-max {n = suc m} ) ⟩ 
    true ∎ where Smaxnm = max (suc n) (suc m)

  ¬FinIsCofin : (α : binarySequence) → isFinite α → isCofinite (¬ α)
  ¬FinIsCofin α = subst isFinite (sym $ ¬Invol) 

  ¬CofinIsFin : (α : binarySequence) → isCofinite α → isFinite (¬ α)
  ¬CofinIsFin α c = c

  data isFiniteOrCofinite (α : binarySequence) : Type where
    Fin : isFinite α → isFiniteOrCofinite α
    Cof : isCofinite α → isFiniteOrCofinite α

  isPropisFiniteOrCofinite : (α : binarySequence) → isProp (isFiniteOrCofinite α)
  isPropisFiniteOrCofinite α (Fin f) (Fin f') = cong Fin $ isPropIsFinite α f f'
  isPropisFiniteOrCofinite α (Fin f) (Cof c)  = ex-falso (Finite≢Cofinite α f c)
  isPropisFiniteOrCofinite α (Cof c) (Fin f)  = ex-falso (Finite≢Cofinite α f c)
  isPropisFiniteOrCofinite α (Cof c) (Cof c') = cong Cof $ isPropIsFinite (¬ α) c c'

  0Finite : isFinite (λ n → false)
  0Finite = constant0 λ _ _ → refl

  1Cofinite : isCofinite (λ n → true)
  1Cofinite = 0Finite

  FinCofin-∧-cl : (α β : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite β → isFiniteOrCofinite (α ∧ β) 
  FinCofin-∧-cl α β (Fin αf) (βcf) = Fin (intersectionWithFiniteIsFinite α β αf)
  FinCofin-∧-cl α β (Cof αc) (Fin βf) = subst isFiniteOrCofinite (∧Comm {x = β} {y = α}) 
    (Fin (intersectionWithFiniteIsFinite β α βf))
  FinCofin-∧-cl α β (Cof αc) (Cof βc) = Cof $ 
    subst isFinite (sym $ DeMorgan¬∧ {x = α} {y = β}) 
    (finiteClosedByUnion (¬ α) (¬ β) αc βc)

  FinCofin-¬-cl : (α : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite (¬ α)
  FinCofin-¬-cl α (Fin f) = Cof (¬FinIsCofin α f)
  FinCofin-¬-cl α (Cof c) = Fin (¬CofinIsFin α c)

  FinCofin-∨-cl : (α β : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite β → isFiniteOrCofinite (α ∨ β) 
  FinCofin-∨-cl α β αcf βcf  = subst isFiniteOrCofinite 
    (¬  ((¬ α) ∧ (¬ β)) ≡⟨ DeMorgan¬∧ {x = ¬ α} ⟩ (¬ ¬ α) ∨ (¬ ¬ β) ≡⟨ cong₂ _∨_ (¬Invol {x = α}) ¬Invol ⟩  α ∨ β ∎)  
    (FinCofin-¬-cl (¬ α ∧ ¬ β) (FinCofin-∧-cl (¬ α) (¬ β) (FinCofin-¬-cl α αcf) (FinCofin-¬-cl β βcf))) 
  -- Note it is in general true there is a smaller set of things one has to derive to generate a SubBooleanAlgebra. Maybe something to set the AI on. (one can go ¬ and then any of 0,1 and then any of ∧,∨

  open SubBooleanAlgebra
  ℕfinCofinSubBA : IsSubBooleanAlgebra ℙℕ isFiniteOrCofinite isPropisFiniteOrCofinite 
  ℕfinCofinSubBA .IsSubBooleanAlgebra.𝟘-cl = Fin 0Finite
  ℕfinCofinSubBA .IsSubBooleanAlgebra.𝟙-cl = Cof 1Cofinite
  ℕfinCofinSubBA .IsSubBooleanAlgebra.∧-cl = FinCofin-∧-cl _ _
  ℕfinCofinSubBA .IsSubBooleanAlgebra.∨-cl = FinCofin-∨-cl _ _
  ℕfinCofinSubBA .IsSubBooleanAlgebra.¬-cl = FinCofin-¬-cl _ 

  ℕfinCofinBA : BooleanRing ℓ-zero
  ℕfinCofinBA = mkSubBooleanAlgebra ℕfinCofinSubBA 

module PresentationℕfinCofin where
  open ℕFinCofin

  δnn=1 : (n : ℕ) → δSequence n n ≡ true
  δnn=1 zero = refl
  δnn=1 (suc n) = δnn=1 n 

  pred≢ℕ : (n m : ℕ) → (suc n ≡ suc m → ⊥)  → (n ≡ m → ⊥)
  pred≢ℕ n m sn≢sm n=m = sn≢sm (cong suc n=m) 

  δnm=0 : (n : ℕ) → (m : ℕ) → ((n ≡ m) → ⊥) → δSequence n m ≡ false
  δnm=0 zero zero x = ex-falso (x refl)
  δnm=0 zero (suc m) x = refl
  δnm=0 (suc n) zero x = refl
  δnm=0 (suc n) (suc m) x = δnm=0 n m (pred≢ℕ n m x) 
  
  module _ where
    open BooleanRingStr (snd ℙℕ) 
    open BooleanAlgebraStr (ℙℕ)
    δn∧δm=0 : (n : ℕ) → (m : ℕ) → ((n ≡ m) → ⊥) → (k : ℕ) → (δSequence n k) and (δSequence m k) ≡ false 
    δn∧δm=0 zero zero n≠m _ = ex-falso (n≠m refl)
    δn∧δm=0 zero _ n≠m (suc k) = refl
    δn∧δm=0 (suc n) _ n≠m zero = refl
    δn∧δm=0 _ (suc m) n≠m zero = and-zeroʳ _
    δn∧δm=0 _ zero n≠m (suc k) = and-zeroʳ _
    δn∧δm=0 (suc n) (suc m) n≠m (suc k) = δn∧δm=0 n m (pred≢ℕ n m n≠m) k

  δSequenceFinite : (n : ℕ) → isFinite (δSequence n) 
  δSequenceFinite n = last1 n (δnn=1 n) λ k k>n → δnm=0 n k (<→≢ k>n) 

  singleton : (n : ℕ) → ⟨ ℕfinCofinBA ⟩
  singleton n = δSequence n , (Fin $ δSequenceFinite n) 

  freeℕ→ℕFinCof : BoolHom (freeBA ℕ) ℕfinCofinBA
  freeℕ→ℕFinCof = inducedBAHom ℕ ℕfinCofinBA singleton



  open BooleanAlgebraStr ⦃...⦄
  instance 
    _ = freeBA ℕ
    _ = ℕfinCofinBA
  open BooleanRingStr ⦃...⦄
  instance
    _ = snd $ freeBA ℕ
    _ = snd ℕfinCofinBA
  relationHelper : (n m : ℕ) → Dec (n ≡ m) → ⟨ freeBA ℕ ⟩
  relationHelper _ _ (yes _) = 𝟘
  relationHelper n m (no ¬p) = generator n · generator m 

  relations : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  relations (n , m) = relationHelper n m (discreteℕ n m)
  
  open IsCommRingHom (snd freeℕ→ℕFinCof)
  relationHelperRespected : (n m : ℕ) → (d : Dec (n ≡ m)) → freeℕ→ℕFinCof $cr (relationHelper n m d) ≡ 𝟘
  relationHelperRespected n m (yes p) = pres0
  relationHelperRespected n m (no ¬p) = 
    freeℕ→ℕFinCof $cr (generator n · generator m)
      ≡⟨ pres· (generator n) (generator m) ⟩ 
    (freeℕ→ℕFinCof $cr generator n) · (freeℕ→ℕFinCof $cr generator m)   
      ≡⟨ cong₂ _·_ (funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n)  (funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) m) ⟩ 
    (singleton n) · (singleton m)
      ≡⟨ Σ≡Prop isPropisFiniteOrCofinite (funExt (δn∧δm=0 n m ¬p)) ⟩ 
    𝟘 ∎ 

  relationsRespected : ∀(p : ℕ × ℕ) → freeℕ→ℕFinCof $cr (relations p) ≡ 𝟘
  relationsRespected (n , m) = relationHelperRespected n m (discreteℕ n m)

open import BooleanRing.FreeBooleanRing.freeBATerms using (equalityFromEqualityOnGenerators)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Algebra.CommRing using (compCommRingEquiv ; _∘cr_ ; _∘cre_)

module CountablyPresentedProof where
  open ℕFinCofin
  open PresentationℕfinCofin
  open IsCommRingHom

  Q : BooleanRing ℓ-zero
  Q = freeBA ℕ QB./Im relations

  private
    module QS = BooleanRingStr (snd Q)
    module QA = BooleanAlgebraStr Q
    module FS = BooleanRingStr (snd (freeBA ℕ))
    module FCS = BooleanRingStr (snd ℕfinCofinBA)

  h : BoolHom Q ℕfinCofinBA
  h = QB.inducedHom ℕfinCofinBA freeℕ→ℕFinCof relationsRespected

  h∘π≡f : h ∘cr QB.quotientImageHom ≡ freeℕ→ℕFinCof
  h∘π≡f = QB.evalInduce ℕfinCofinBA

  qGen : ℕ → ⟨ Q ⟩
  qGen n = QB.quotientImageHom $cr generator n

  h-qGen : (n : ℕ) → fst h (qGen n) ≡ singleton n
  h-qGen n = cong (λ f → f $cr generator n) h∘π≡f
           ∙ funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n

  prodIsRelation : (n m : ℕ) → (n ≡ m → ⊥) →
    FS._·_ (generator n) (generator m) ≡ relations (n , m)
  prodIsRelation n m n≢m with discreteℕ n m
  ... | yes p = ex-falso (n≢m p)
  ... | no _  = refl

  qGen-disjoint : (n m : ℕ) → (n ≡ m → ⊥) → QS._·_ (qGen n) (qGen m) ≡ QS.𝟘
  qGen-disjoint n m n≢m =
    sym (pres· (snd QB.quotientImageHom) (generator n) (generator m))
    ∙ cong (fst QB.quotientImageHom) (prodIsRelation n m n≢m)
    ∙ QB.zeroOnImage (n , m)

  -- Build finite join of generators in Q
  sB : binarySequence → ℕ → ⟨ Q ⟩
  sB α zero = QS.𝟘
  sB α (suc n) with α n =B true
  ... | yes _ = QA._∨_ (sB α n) (qGen n)
  ... | no _  = sB α n

  -- Disjointness: sB α n is disjoint from qGen m when m ≥ n
  sB-disjoint : (α : binarySequence) (n m : ℕ) → m ≥ n →
    QS._·_ (sB α n) (qGen m) ≡ QS.𝟘
  sB-disjoint α zero m _ =
    solve! (BooleanRing→CommRing Q)
  sB-disjoint α (suc n) m m≥sn with α n =B true
  ... | no _ = sB-disjoint α n m (≤-trans (1 , refl) m≥sn)
  ... | yes _ =
    QS._·_ (QA._∨_ (sB α n) (qGen n)) (qGen m)
      ≡⟨ solve! (BooleanRing→CommRing Q) ⟩
    QS._+_ (QS._+_ (QS._·_ (sB α n) (qGen m))
                     (QS._·_ (qGen n) (qGen m)))
            (QS._·_ (QS._·_ (sB α n) (qGen n)) (qGen m))
      ≡⟨ cong₂ QS._+_
           (cong₂ QS._+_
             (sB-disjoint α n m (≤-trans (1 , refl) m≥sn))
             (qGen-disjoint n m λ p → ¬m<m (subst (suc n ≤_) (sym p) m≥sn)))
           (cong (λ z → QS._·_ z (qGen m))
             (sB-disjoint α n n ≤-refl)) ⟩
    QS._+_ (QS._+_ QS.𝟘 QS.𝟘) (QS._·_ QS.𝟘 (qGen m))
      ≡⟨ solve! (BooleanRing→CommRing Q) ⟩
    QS.𝟘 ∎
    where ¬m≤n : m ≤ n → ⊥
          ¬m≤n m≤n = ¬m<m (≤-trans m≥sn m≤n)

  -- ∨ simplifies when disjoint
  ∨-disjoint : (x y : ⟨ Q ⟩) → QS._·_ x y ≡ QS.𝟘 →
    QA._∨_ x y ≡ QS._+_ x y
  ∨-disjoint x y xy=0 =
    QA._∨_ x y
      ≡⟨⟩
    QS._+_ (QS._+_ x y) (QS._·_ x y)
      ≡⟨ cong (QS._+_ (QS._+_ x y)) xy=0 ⟩
    QS._+_ (QS._+_ x y) QS.𝟘
      ≡⟨ QS.+IdR _ ⟩
    QS._+_ x y ∎

  -- sB step: when α n = false, sB doesn't change at suc n
  sB-step : (α : binarySequence) (n : ℕ) → α n ≡ false → sB α (suc n) ≡ sB α n
  sB-step α n αn=false with α n =B true
  ... | yes αn=true = ex-falso (true≢false (sym αn=true ∙ αn=false))
  ... | no _ = refl

  -- Bound independence: if α is zero from m ≤ n, then sB α n = sB α m
  sB-bound-ind : (α : binarySequence) (m n : ℕ) → n ≥ m →
    isZeroFrom m α → sB α n ≡ sB α m
  sB-bound-ind α zero zero _ _ = refl
  sB-bound-ind α (suc m') zero n≥m _ = ex-falso (¬-<-zero n≥m)
  sB-bound-ind α m (suc n) n≥m α≥m=0 = case ≤-split n≥m of λ
    { (inl m<sn) →
        sB-step α n (α≥m=0 n (pred-≤-pred m<sn))
        ∙ sB-bound-ind α m n (pred-≤-pred m<sn) α≥m=0
    ; (inr m≡sn) → cong (sB α) (sym m≡sn)
    }

  -- If α is false below n, then sB α n = 0
  sB-zero : (α : binarySequence) (n : ℕ) →
    ((k : ℕ) → k < n → α k ≡ false) → sB α n ≡ QS.𝟘
  sB-zero α zero _ = refl
  sB-zero α (suc n) allFalse with α n =B true
  ... | yes αn = ex-falso (true≢false (sym αn ∙ allFalse n ≤-refl))
  ... | no _ = sB-zero α n λ k k<n → allFalse k (≤-trans k<n (1 , refl))

  -- 0 ∨ x = x in Q
  ∨-lid : (x : ⟨ Q ⟩) → QA._∨_ QS.𝟘 x ≡ x
  ∨-lid x = solve! (BooleanRing→CommRing Q)

  -- Section for finite elements
  sFin : (α : binarySequence) → isFinite α → ⟨ Q ⟩
  sFin α (constant0 _)     = QS.𝟘
  sFin α (last1 n _ α>n=0) = sB α (suc n)

  -- Full section
  sec : ⟨ ℕfinCofinBA ⟩ → ⟨ Q ⟩
  sec (α , Fin f) = sFin α f
  sec (α , Cof c) = QA.¬_ (sFin (BooleanAlgebraStr.¬_ ℙℕ α) c)

  -- h ∘ sec = id (retraction)
  -- Key: h sends sB α n to α truncated to [0,n)
  open BooleanAlgebraStr ℙℕ using () renaming (_∨_ to _∨ℕ_ ; ¬_ to ¬ℕ_)

  truncate : binarySequence → ℕ → binarySequence
  truncate α n k with <Dec k n
  ... | yes _ = α k
  ... | no _  = false

  truncate-zeroFrom : (α : binarySequence) (n : ℕ) → isZeroFrom n (truncate α n)
  truncate-zeroFrom α n k k≥n with <Dec k n
  ... | yes k<n = ex-falso (¬m<m (≤-trans k<n k≥n))
  ... | no _    = refl

  truncate-agrees : (α : binarySequence) (n : ℕ) → isZeroFrom n α →
    (k : ℕ) → truncate α n k ≡ α k
  truncate-agrees α n α≥n=0 k with <Dec k n
  ... | yes _ = refl
  ... | no k≮n = sym (α≥n=0 k (<-asym' k≮n))

  -- h sends sB to truncated sequence
  h-sB : (α : binarySequence) (n : ℕ) →
    fst (fst h (sB α n)) ≡ truncate α n
  h-sB α zero = funExt λ k →
    cong (λ x → fst x k) (pres0 (snd h))
  h-sB α (suc n) with α n =B true
  ... | no ¬αn = funExt λ k → funExt⁻ (h-sB α n) k ∙ go k where
    go : (k : ℕ) → truncate α n k ≡ truncate α (suc n) k
    go k with <Dec k n | <Dec k (suc n)
    ... | yes _   | yes _    = refl
    ... | yes k<n | no k≥sn  = ex-falso (k≥sn (≤-trans k<n (1 , refl)))
    ... | no k≥n  | yes k<sn = sym (¬true→false (α k) λ αk →
          ¬αn (subst (λ m → α m ≡ true) (≤-antisym (pred-≤-pred k<sn) (<-asym' k≥n)) αk))
    ... | no _    | no _     = refl
  ... | yes αn = {! !} -- TODO: h sends join to join, use IH

  -- Main retraction proof (h ∘ sec = id)
  postulate
    h∘sec≡id : (x : ⟨ ℕfinCofinBA ⟩) → fst h (sec x) ≡ x

  -- Section is a ring hom (needed for sec ∘ h = id)
  private module FCA = BooleanAlgebraStr ℕfinCofinBA

  sec-pres0 : sec FCS.𝟘 ≡ QS.𝟘
  sec-pres0 = refl

  sec-pres- : (x : ⟨ ℕfinCofinBA ⟩) → sec (FCS.-_ x) ≡ QS.-_ (sec x)
  sec-pres- x = cong sec FCA.-IsId ∙ sym QA.-IsId

  postulate
    sec-pres1 : sec FCS.𝟙 ≡ QS.𝟙
    sec-pres+ : (x y : ⟨ ℕfinCofinBA ⟩) → sec (FCS._+_ x y) ≡ QS._+_ (sec x) (sec y)
    sec-pres· : (x y : ⟨ ℕfinCofinBA ⟩) → sec (FCS._·_ x y) ≡ QS._·_ (sec x) (sec y)

  secHom : BoolHom ℕfinCofinBA Q
  fst secHom = sec
  snd secHom .pres0 = sec-pres0
  snd secHom .pres1 = sec-pres1
  snd secHom .pres+ = sec-pres+
  snd secHom .pres· = sec-pres·
  snd secHom .pres- = sec-pres-

  -- sec ∘ h = id via generators
  δ-below : (n k : ℕ) → k < n → δSequence n k ≡ false
  δ-below n k k<n = δnm=0 n k (<→≢ k<n ∘ sym)

  sec-on-singleton : (n : ℕ) → sec (singleton n) ≡ qGen n
  sec-on-singleton n = cong (sFin (δSequence n)) (isPropIsFinite (δSequence n) _ _)
    ∙ go n
    where
    go : (n : ℕ) → sB (δSequence n) (suc n) ≡ qGen n
    go n with δSequence n n =B true
    ... | yes _ = cong (λ z → QA._∨_ z (qGen n))
                    (sB-zero (δSequence n) n (δ-below n))
                  ∙ ∨-lid (qGen n)
    ... | no ¬p = ex-falso (¬p (δnn=1 n))

  -- sec ∘ freeℕ→ℕFinCof = quotientImageHom (by universal property)
  sec∘f≡π-on-gens : (n : ℕ) →
    (secHom ∘cr freeℕ→ℕFinCof) $cr generator n ≡ QB.quotientImageHom $cr generator n
  sec∘f≡π-on-gens n =
    sec (fst freeℕ→ℕFinCof (generator n))
      ≡⟨ cong sec (funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n) ⟩
    sec (singleton n)
      ≡⟨ sec-on-singleton n ⟩
    qGen n ∎

  sec∘f≡π : secHom ∘cr freeℕ→ℕFinCof ≡ QB.quotientImageHom
  sec∘f≡π = equalityFromEqualityOnGenerators Q _ _ sec∘f≡π-on-gens

  sec∘h≡id-fun : fst secHom ∘ fst h ≡ idfun ⟨ Q ⟩
  sec∘h≡id-fun = QB.quotientImageHomEpi (⟨ Q ⟩ , QS.is-set)
    (cong fst (cong (secHom ∘cr_) h∘π≡f ∙ sec∘f≡π))

  -- Package as BooleanRingEquiv
  compBoolRingEquiv : {A B C : BooleanRing ℓ-zero} →
    BooleanRingEquiv A B → BooleanRingEquiv B C → BooleanRingEquiv A C
  compBoolRingEquiv f g = compCommRingEquiv f g

  h-iso : Iso ⟨ Q ⟩ ⟨ ℕfinCofinBA ⟩
  h-iso .Iso.fun = fst h
  h-iso .Iso.inv = sec
  h-iso .Iso.sec = funExt h∘sec≡id
  h-iso .Iso.ret = funExt⁻ sec∘h≡id-fun

  Q≃FC : BooleanRingEquiv Q ℕfinCofinBA
  Q≃FC .fst .fst = fst h
  Q≃FC .fst .snd = isoToIsEquiv h-iso
  Q≃FC .snd = snd h

  FC≃Q : BooleanRingEquiv ℕfinCofinBA Q
  FC≃Q = invBooleanRingEquiv Q ℕfinCofinBA Q≃FC

  relationsFlat : ℕ → ⟨ freeBA ℕ ⟩
  relationsFlat n = relations (Iso.inv ℕ×ℕ≅ℕ n)

  Q' : BooleanRing ℓ-zero
  Q' = freeBA ℕ QB./Im relationsFlat

  Q≃Q' : BooleanRingEquiv Q Q'
  Q≃Q' = reindexwithEquiv ℕ×ℕ≅ℕ relations

  FC≃Q' : BooleanRingEquiv ℕfinCofinBA Q'
  FC≃Q' = compBoolRingEquiv FC≃Q Q≃Q'

  ℕfinCofinBA-presented : has-quotient-of-freeℕ-presentation ℕfinCofinBA
  ℕfinCofinBA-presented = relationsFlat , FC≃Q'

  ℕfinCofinBA-countably-presented-alt : is-countably-presented-alt ℕfinCofinBA
  ℕfinCofinBA-countably-presented-alt = ∣ ℕfinCofinBA-presented ∣₁

