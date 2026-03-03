{-# OPTIONS --cubical --guardedness #-}

module OmnisciencePrinciples.Markov where 

open import Axioms.StoneDuality
open import StoneSpaces.Spectrum
open import AntiEquivalence

open import Cubical.Functions.Fixpoint
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Powerset

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
open import Cubical.Tactics.CommRingSolver
open import CommRingQuotients.IdealTerms
open import BasicDefinitions 

MarkovPrinciple : Type₀ 
MarkovPrinciple = (α : binarySequence) → ¬ (∀ n → α n ≡ false) → Σ[ n ∈ ℕ ] α n ≡ true

weakMarkovPrinciple : Type₀ 
weakMarkovPrinciple = (α : binarySequence) → ¬ (∀ n → α n ≡ false) → ∃[ n ∈ ℕ ] α n ≡ true


module _ (α : binarySequence) (α≠0 : ¬ (∀ n → α n ≡ false)) where
  2/α : BooleanRing _
  2/α = BoolBR /Im α 
 
  module _ (f : BoolHom 2/α BoolBR) where
    open BooleanRingStr (snd 2/α)
    open IsCommRingHom
    
    f' : BoolHom BoolBR BoolBR
    f' = f ∘cr quotientImageHom

    f'αn=0 : (n : ℕ) → f' $cr (α n) ≡ false
    f'αn=0 n =  f' $cr (α n) ≡⟨⟩ 
                fst f (quotientImageHom $cr (α n)) ≡⟨ cong (fst f) (zeroOnImage n) ⟩ 
                fst f 𝟘 ≡⟨ pres0 (snd f)⟩ 
                false ∎ 

    f'=id : (x : Bool) → f' $cr x ≡ x
    f'=id false = pres0 (snd f')
    f'=id true  = pres1 (snd f') 
  
    αn=0 : (n : ℕ) → α n ≡ false
    αn=0 n = sym (f'=id (α n)) ∙ f'αn=0 n

    emptySp : ⊥
    emptySp = α≠0 αn=0 

module _ (α : binarySequence)  where
  t∈I→αn : isInIdeal BoolCR α true → Σ[ n ∈ ℕ ] α n ≡ true
  t∈I→αn (isImage .true n αn=true)          = n , αn=true
  t∈I→αn (iszero  .true f=t)                = ex-falso (false≢true f=t)
  t∈I→αn (isSum .true false false t=f _ _ ) = ex-falso (true≢false t=f)
  t∈I→αn (isSum .true false true  _ _ t∈I ) = t∈I→αn t∈I
  t∈I→αn (isSum .true true  _     _ t∈I _ ) = t∈I→αn t∈I
  t∈I→αn (isMul .true false _     t=f _   ) = ex-falso (true≢false t=f)
  t∈I→αn (isMul .true true  false t=f _   ) = ex-falso (true≢false t=f)
  t∈I→αn (isMul .true true  true  _ t∈I   ) = t∈I→αn t∈I 

  αI = IQ.generatedIdeal BoolCR α
  
  ∃αn : αI true → ∃[ n ∈ ℕ ] α n ≡ true 
  ∃αn x = PT.map t∈I→αn (idealDecomp BoolCR α true x) 

module extractFirstHitInBinarySequence (α : binarySequence) where
  is-first-hit : (n : ℕ) → Type
  is-first-hit m = (α m ≡ true) × ((k : ℕ) → k < m → α k ≡ false)
    
  first-hit : Type
  first-hit = Σ[ m ∈ ℕ ] is-first-hit m

  firstSeenBefore : ℕ → Type
  firstSeenBefore n = (Σ[ m ∈ ℕ ] (m < n) × is-first-hit m)
  
  pred¬firstSeenBefore : (n : ℕ) → (¬ firstSeenBefore (suc n) ) → ¬ firstSeenBefore n
  pred¬firstSeenBefore n nothingBeforeSn (m , m<n , αm , notbeforem) = nothingBeforeSn (m , ≤-suc m<n , αm , notbeforem) 

  propHelp : (n : ℕ) → isProp (is-first-hit n)
  propHelp n (p , nF) (p' , nF') = Σ≡Prop 
    (λ αn → propFun₂ λ n _ → isSetBool (α n) false) 
    (prophelp n p p') where

    propFun : { A : Type} { B : A → Type} → ((a : A)  → isProp (B a)) → isProp ((a : A) → B a)
    propFun Bprop f g = funExt {f = f} {g = g} λ { x → Bprop x (f x) (g x) } 
  
    propFun₂ : {A : Type} {B : A → Type} {C : (a : A) → (b : B a) → Type} → 
       ((a : A) → (b : B a) → isProp (C a b)) → 
       isProp ( (a : A) → (b : B a) → C a b) 
    propFun₂ Cprop f g = propFun (λ a → propFun λ b → Cprop a b) f g 
  
    prophelp : (n : ℕ) → isProp ( α n ≡ true) 
    prophelp n x y = isSetBool (α n) true x y

  firstProp : isProp first-hit
  firstProp (m , αm , mFirst) (n , αn , nFirst ) with (m ≟ n ) 
  ... | lt m<n = ex-falso (true≢false (sym αm ∙ nFirst m m<n))
  ... | eq m=n = Σ≡Prop (λ n → propHelp n) m=n
  ... | gt n<m = ex-falso (true≢false (sym αn ∙ mFirst n n<m )) 

  need : (n : ℕ) → ¬ firstSeenBefore n → (k : ℕ) → k < n → α k ≡ false 
  need zero _ _ k<0            = ex-falso $ ¬-<-zero k<0
  need (suc n) noBefore k k<Sn = ¬true→false (α k) λ { αk → noBefore 
    (k , k<Sn , αk , λ { l l<k → need n (pred¬firstSeenBefore n noBefore) l (<help l<k k<Sn) }) }  where
      <help : {m n k : ℕ} → (m < n) → n < suc k → m < k 
      <help {m} {n} {k} m<n n<Sk = pred-≤-pred (suc (suc m) ≤⟨ suc-≤-suc m<n ⟩ suc n ≤≡⟨ n<Sk ⟩ suc k ∎) 

  decidableFirst : (n : ℕ ) → Dec (firstSeenBefore n)
  decidableFirst zero    = no λ { ( _ , m<0 , _) → ¬-<-zero m<0 }
  decidableFirst (suc n) with (decidableFirst n)
  ... | yes (m , m<n , first) = yes (m , (m <⟨ m<n ⟩ n <≡⟨ 0 , refl ⟩ suc n ∎) , first)
  ... | no noEarlierFirst with (α n =B true) 
  ...     | yes αn = yes 
               (n , (0 , refl) , αn , need n noEarlierFirst )
  ...     | no ¬αn = no caseSplit where
             caseSplit : firstSeenBefore (suc n)  → ⊥ 
             caseSplit (m , m<Sn , αm , x) with <-split m<Sn 
             ... | inl m<n = noEarlierFirst (m , m<n , αm , x)
             ... | inr m=n = ¬αn (cong α (sym m=n) ∙ αm)  

  FindFirst : (n : ℕ) → α n ≡ true → firstSeenBefore (suc n)
  FindFirst n αn with decidableFirst (suc n) 
  ... | yes p = p
  ... | no ¬p = ex-falso (¬p (n , (0 , refl) , αn , (need n $ pred¬firstSeenBefore n ¬p)))
  
  extractFirst : ∃[ n ∈ ℕ ] α n ≡ true → first-hit
  extractFirst = PT.rec firstProp (uncurry goback) where
   
    spot : (n : ℕ) → firstSeenBefore n → first-hit
    spot n (m , _ , αm , mfirst) = m , αm , mfirst 

    goback : (n : ℕ) → α n ≡ true → first-hit
    goback n αn = spot (suc n) (FindFirst n αn) 
  
  first→Hit : first-hit → Σ[ n ∈ ℕ ] α n ≡ true
  first→Hit (n , αn , _ ) = n , αn 

  extract : ∃[ n ∈ ℕ ] (α n ≡ true)  → Σ[ n ∈ ℕ ] (α n ≡ true) 
  extract = first→Hit ∘ extractFirst

weakMP→MP : weakMarkovPrinciple → MarkovPrinciple
weakMP→MP wMP α = extractFirstHitInBinarySequence.extract α ∘ wMP α


--mp-from-SD : StoneDualityAxiom → MarkovPrinciple
--mp-from-SD SD α α≠0 = extractFirst α (∃αn α (trivialQuotient→1∈I BoolCR (IQ.genIdeal BoolCR α) (sym 0≡1-CR)))
--  where
--  open import Axioms.StoneDuality using (evaluationMap)
--  open import CommRingQuotients.TrivialIdeal using (trivialQuotient→1∈I)
--  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
--
--  0≡1-BR : BooleanRingStr.𝟘 (snd (BoolBR QB./Im α)) ≡ BooleanRingStr.𝟙 (snd (BoolBR QB./Im α))
--  0≡1-BR = SpectrumEmptyImpliesTrivial.0≡1-in-B SD (2/α-Booleω α) (MarkovLib.emptySp α α≠0)
--  open import BooleanRing.BooleanRingQuotients.QuotientBool using (_/Im_)
--  opaque
--    unfolding _/Im_
--    0≡1-CR : CommRingStr.0r (snd (BoolCR IQ./Im α)) ≡ CommRingStr.1r (snd (BoolCR IQ./Im α))
--    0≡1-CR = 0≡1-BR
