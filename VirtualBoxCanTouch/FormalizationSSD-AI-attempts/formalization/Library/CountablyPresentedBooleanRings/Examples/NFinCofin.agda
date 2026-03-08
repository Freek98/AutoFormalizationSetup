{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module formalization.Library.CountablyPresentedBooleanRings.Examples.NFinCofin where
open import formalization.Library.CountablyPresentedBooleanRings.Definitions
open import formalization.Library.CountablyPresentedBooleanRings.Examples.Bool
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool
open import formalization.Library.BooleanRing.AlgebraicFacts
open import formalization.Library.BooleanRing.BoolAlgMorphism
open import Cubical.Foundations.Equiv
open import Cubical.Tactics.NatSolver
open import Cubical.Tactics.CommRingSolver
open import formalization.Library.BooleanRing.BooleanRingMaps
open import formalization.Library.BooleanRing.SubBooleanRing
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_) 
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Bool

open import Cubical.Data.Sum
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import formalization.Library.BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import formalization.Library.CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import formalization.Library.BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Bool renaming ( _≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Algebra.CommRing.Instances.Unit
open import formalization.Library.QuickFixes

open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄

module QuickBooleanFix where
  instance 
    _ = snd BoolBR
  claim : (a b : Bool) → (a ∨ b) ≡ a or b
  claim false false = refl
  claim false true  = refl
  claim true  false = refl
  claim true  true  = refl 

booleanStructureOnBinarySequences : BooleanRingStr binarySequence
booleanStructureOnBinarySequences = pointWiseStructure ℕ (λ _ → Bool) (λ _ → snd BoolBR)
instance 
  _ = booleanStructureOnBinarySequences

ℙℕ : BooleanRing ℓ-zero
ℙℕ = binarySequence , booleanStructureOnBinarySequences

module DefinitionFinCofin where 
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
  
  disjunctionBoundedBoundedIsBounded : (α β : binarySequence) → (n m : ℕ) → 
   isZeroFrom n α → isZeroFrom m β → isZeroFrom (max n m) (α ∨ β)
  disjunctionBoundedBoundedIsBounded α β n m α≥n=0 β≥m=0 k k≥mn = 
   (α ∨ β) k 
     ≡⟨ QuickBooleanFix.claim (α k) (β k) ⟩
   α k or β k 
     ≡⟨ cong₂ _or_ (α≥n=0 k (≤-trans (left-≤-max  {n = m}) k≥mn)) 
                   (β≥m=0 k (≤-trans (right-≤-max {m = n}) k≥mn)) ⟩ 
   false ∎  
  
  finiteClosedByUnion : (α β : binarySequence) → isFinite α → isFinite β → isFinite (α ∨ β)
  finiteClosedByUnion α β αFin βFin = case (finite→Bounded α  αFin , finite→Bounded β βFin) of λ 
   ((n , α≥n=0) , (m , β≥m=0)) → bounded→Finite (α ∨ β) (max n m) 
   (disjunctionBoundedBoundedIsBounded α β n m α≥n=0 β≥m=0)  
  
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

open DefinitionFinCofin

ℕfinCofinBA : BooleanRing ℓ-zero
ℕfinCofinBA = mkSubBooleanAlgebra ℕfinCofinSubBA 

instance
  _ = snd ℕfinCofinBA

module Presentation where
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

  instance _ = snd $ freeBA ℕ

  relationHelper : (n m : ℕ) → Dec (n ≡ m) → ⟨ freeBA ℕ ⟩
  relationHelper _ _ (yes _) = 𝟘
  relationHelper n m (no ¬p) = generator n ∧ generator m 

  relations : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  relations (n , m) = relationHelper n m (discreteℕ n m)

  open IsCommRingHom (snd freeℕ→ℕFinCof)
  relationHelperRespected : (n m : ℕ) → (d : Dec (n ≡ m)) → freeℕ→ℕFinCof $cr (relationHelper n m d) ≡ 𝟘
  relationHelperRespected n m (yes p) = pres0
  relationHelperRespected n m (no ¬p) = 
    freeℕ→ℕFinCof $cr (generator n ∧ generator m)
      ≡⟨ pres· (generator n) (generator m) ⟩ 
    (freeℕ→ℕFinCof $cr generator n) ∧ (freeℕ→ℕFinCof $cr generator m)   
      ≡⟨ cong₂ _∧_ (funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n)  (funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) m) ⟩ 
    (singleton n) ∧ (singleton m)
      ≡⟨ Σ≡Prop isPropisFiniteOrCofinite (funExt (δn∧δm=0 n m ¬p)) ⟩ 
    𝟘 ∎ 

  relationsRespected : ∀(p : ℕ × ℕ) → freeℕ→ℕFinCof $cr (relations p) ≡ 𝟘 
  relationsRespected (n , m) = relationHelperRespected n m (discreteℕ n m)

  presentation : BooleanRing ℓ-zero
  presentation = (freeBA ℕ) QB./Im relations

  presentation→ℕFinCof : BoolHom presentation ℕfinCofinBA 
  presentation→ℕFinCof = inducedHom ℕfinCofinBA freeℕ→ℕFinCof relationsRespected 

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
  ℕFinCof→FreeℕMap (α , Cof αc) = ¬ Finite→FreeℕMap (¬ α) αc 
  
  pres¬ToFree : (x : ⟨ ℕfinCofinBA ⟩) → (ℕFinCof→FreeℕMap (¬ x))  ≡ ¬ (ℕFinCof→FreeℕMap x)
  pres¬ToFree (α , Fin αf) = 
    ℕFinCof→FreeℕMap (¬ (α , Fin αf)) 
      ≡⟨ cong ℕFinCof→FreeℕMap (Σ≡Prop isPropisFiniteOrCofinite refl) ⟩ 
    ℕFinCof→FreeℕMap (¬ α , Cof (¬FinIsCofin α αf) )
      ≡⟨⟩ 
    ¬ (ℕFinCof→FreeℕMap (¬ ¬ α , Fin (¬CofinIsFin (¬ α) (¬FinIsCofin α αf))))
      ≡⟨ cong (¬_ ∘ ℕFinCof→FreeℕMap) (Σ≡Prop isPropisFiniteOrCofinite ¬Invol) ⟩ 
    ¬ (ℕFinCof→FreeℕMap (α , Fin αf)) ∎
  pres¬ToFree (α , Cof αc) = 
    ℕFinCof→FreeℕMap (¬ (α , Cof αc) )
      ≡⟨ cong ℕFinCof→FreeℕMap (Σ≡Prop isPropisFiniteOrCofinite refl) ⟩ 
    ℕFinCof→FreeℕMap ( ¬ α , Fin αc)
      ≡⟨⟩ 
    Finite→FreeℕMap (¬ α) αc
      ≡⟨ sym ¬Invol ⟩ 
    ¬ ¬ (Finite→FreeℕMap (¬ α) αc)
      ≡⟨⟩
    ¬ (ℕFinCof→FreeℕMap (α , Cof αc)) ∎

  ℕFinCof→Presentation : ⟨ ℕfinCofinBA ⟩ → ⟨ presentation ⟩
  ℕFinCof→Presentation = fst (QB.quotientImageHom) ∘ ℕFinCof→FreeℕMap

  ℕFinCof→PresentationIsHom : IsCommRingHom 
    (BooleanRingStr→CommRingStr (snd ℕfinCofinBA)) 
    ℕFinCof→Presentation 
    (BooleanRingStr→CommRingStr (snd presentation))
  ℕFinCof→PresentationIsHom = {! !} 

  ℕFinCof→PresentationHom : BoolHom ℕfinCofinBA presentation
  ℕFinCof→PresentationHom = ℕFinCof→Presentation , ℕFinCof→PresentationIsHom

  agreeOnGens : (n : ℕ) → 
    (QB.quotientImageHom $cr generator n) ≡ 
    ((ℕFinCof→PresentationHom ∘cr presentation→ℕFinCof ∘cr QB.quotientImageHom) $cr generator n)
  agreeOnGens = {! !} 

  roundTripPresentation : ℕFinCof→PresentationHom ∘cr presentation→ℕFinCof ≡ idBoolHom presentation
  roundTripPresentation = {! !} 

  boundedEqualIffLongEnoughEqual : (α β : binarySequence) → (n : ℕ) → (αbound : isZeroFrom n α) → (βbound : isZeroFrom n β) → 
    ((k : ℕ) → (k < n) → α k ≡ β k) → α ≡ β
  boundedEqualIffLongEnoughEqual α β n α≥n=0 β≥n=0 α=β<n = funExt λ m → case splitℕ-< m n of λ 
    { (inl m<n) → α=β<n m m<n
    ; (inr m≥n) → α≥n=0 m m≥n ∙ sym (β≥n=0 m m≥n) } 

  roundTripℕFinCofHelper : (α : binarySequence) → (αf : isFinite α) → 
    (fst (freeℕ→ℕFinCof) ∘ ℕFinCof→FreeℕMap) (α , Fin αf) ≡ (α , Fin αf)
  roundTripℕFinCofHelper α (constant0 x) = {! !}
  roundTripℕFinCofHelper α (last1 n x x₁) = {! !} 

  roundTripℕFinCof : presentation→ℕFinCof ∘cr ℕFinCof→PresentationHom ≡ idBoolHom ℕfinCofinBA
  roundTripℕFinCof = {! !} 

  ℕFinCof=Presentation : BooleanRingEquiv ℕfinCofinBA presentation
  ℕFinCof=Presentation = {! !} 



