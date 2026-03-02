{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions where 

open import BooleanRing.BooleanRingMaps
open import BooleanRing.BoolRingUnivalence
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing.Instances.Bool
open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.FreeBooleanRing.FreeBool as FB

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import BasicDefinitions
open import CommRingQuotients.EmptyQuotient
open import CountablyPresentedBooleanRings.Definitions
open import CommRingQuotients.EquivHelper 

module quotient-of-sum-presentation (f g : ℕ → ⟨ freeBA ℕ ⟩ )where
  f+g : ℕ → ⟨ freeBA ℕ ⟩
  f+g = ⊎.rec f g ∘ Iso.inv ℕ⊎ℕ≅ℕ

  ℕ/f+g-presentation : has-quotient-of-freeℕ-presentation (freeBA ℕ QB./Im (⊎.rec f g))
  ℕ/f+g-presentation = f+g , reindexwithEquiv ℕ⊎ℕ≅ℕ (⊎.rec f g)
  
  ℕ/f+g-as-double-quotient : 
    freeBA ℕ QB./Im (⊎.rec f g) ≡
    (freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g)
  ℕ/f+g-as-double-quotient = quotientEquivBool (freeBA ℕ) f g

  doubleQuotientPresented :
    has-quotient-of-freeℕ-presentation ((freeBA ℕ QB./Im f) QB./Im (fst QB.quotientImageHom ∘ g))
  doubleQuotientPresented = subst has-quotient-of-freeℕ-presentation ℕ/f+g-as-double-quotient ℕ/f+g-presentation

module quotientByCountable (γ : binarySequence) (A : BooleanRing ℓ-zero) where
  X = Σ[ n ∈ ℕ ] γ n ≡ true 
  module _ (f : X → ⟨ A ⟩) where 
    open BooleanRingStr ⦃...⦄ 
    instance
      _ = snd A 
    g' : (n : ℕ) → (γn : Dec (γ n ≡ true)) → ⟨ A ⟩
    g' n (yes p) = f (n , p)
    g' n (no ¬p) = 𝟘
    g : ℕ → ⟨ A ⟩
    g n  = g' n (γ n =B true) 
    gYesCase' : (n : ℕ) → (γn : Dec (γ n ≡ true)) → (p : γ n ≡ true) → g' n γn ≡ f ( n , p)
    gYesCase' n (yes _) _ = cong f (Σ≡Prop (λ x → isSetBool _ _) refl)
    gYesCase' n (no ¬p) p = ex-falso $ ¬p p 
    gYesCase : (n : ℕ) → ( p : γ n ≡ true) → g n ≡ f (n , p)
    gYesCase n = gYesCase' n (γ n =B true)
    A/f = A QB./Im f 
    A/g = A QB./Im g
    instance 
      _ = snd A/f
      _ = snd A/g
    open IsCommRingHom (snd $ QB.quotientImageHom {B = A} {f = f} )
    fZeroOnG' : (n : ℕ) → (γn : Dec (γ n ≡ true) ) → QB.quotientImageHom {f = f} $cr g' n γn ≡ 𝟘 
    fZeroOnG' n (yes p) = QB.zeroOnImage (n , p)
    fZeroOnG' n (no ¬p) = pres0 
    fZeroOnG : (n : ℕ) → QB.quotientImageHom {f = f} $cr g n ≡ 𝟘 
    fZeroOnG n = fZeroOnG' n (γ n =B true) 
    A/g→A/f : BoolHom A/g A/f
    A/g→A/f = QB.inducedHom A/f QB.quotientImageHom fZeroOnG
    
    gZeroOnF : (x : X) → QB.quotientImageHom {f = g} $cr f x ≡ 𝟘 
    gZeroOnF x@(n , p) = cong (fst QB.quotientImageHom) (sym $ gYesCase n p) ∙ QB.zeroOnImage n 
    A/f→A/g : BoolHom A/f A/g
    A/f→A/g = QB.inducedHom A/g QB.quotientImageHom gZeroOnF 
    
    A/f→A/g∘qf=qg : A/f→A/g ∘cr (QB.quotientImageHom {f = f}) ≡ QB.quotientImageHom {f = g} 
    A/f→A/g∘qf=qg = QB.evalInduce A/g 

    A/g→A/f∘qg=qf : A/g→A/f ∘cr (QB.quotientImageHom {f = g}) ≡ QB.quotientImageHom {f = f} 
    A/g→A/f∘qg=qf = QB.evalInduce A/f  

    A/g∘q=q : A/f→A/g ∘cr A/g→A/f ∘cr QB.quotientImageHom {f = g} ≡ QB.quotientImageHom {f = g} 
    A/g∘q=q = cong (λ h → A/f→A/g ∘cr h) A/g→A/f∘qg=qf ∙ A/f→A/g∘qf=qg
    A/g=id : A/f→A/g ∘cr A/g→A/f ≡ idCommRingHom (BooleanRing→CommRing A/g)
    A/g=id = CommRingHom≡ $ 
       QB.quotientImageHomEpi (_ , is-set) (cong fst A/g∘q=q) 

    A/f∘q=q : A/g→A/f ∘cr A/f→A/g ∘cr QB.quotientImageHom {f = f} ≡ QB.quotientImageHom {f = f} 
    A/f∘q=q = cong (λ h → A/g→A/f ∘cr h) A/f→A/g∘qf=qg ∙ A/g→A/f∘qg=qf
    A/f=id : A/g→A/f ∘cr A/f→A/g ≡ idCommRingHom (BooleanRing→CommRing A/f)
    A/f=id =  CommRingHom≡ $ 
       QB.quotientImageHomEpi (⟨ A/f ⟩ , is-set) (cong fst A/f∘q=q)

    quotient-by-expansion-equiv : BooleanRingEquiv A/g A/f
    quotient-by-expansion-equiv = isoToCommRingEquiv A/g→A/f (fst A/f→A/g) 
      (funExt⁻ $ cong fst A/f=id) (funExt⁻ $ cong fst A/g=id) 

module freeOnCountable (α : binarySequence) where
  A = Σ[ n ∈ ℕ ] α n ≡ true
  open BooleanRingStr ⦃...⦄
  instance 
    _ = snd $ freeBA A 
    _ = snd $ freeBA ℕ 

  gensNotInAHelper : (n : ℕ) → Dec (α n ≡ true) → ⟨ freeBA ℕ ⟩
  gensNotInAHelper n (yes p) = 𝟘
  gensNotInAHelper n (no ¬p) = generator n 
  
  gensThatAreNotInA : (n : ℕ) → ⟨ freeBA ℕ ⟩
  gensThatAreNotInA n = gensNotInAHelper n (α n =B true) 

  gensNotInANoCaseHelper : (n : ℕ) → (¬αn : ¬ α n ≡ true) → 
                           (αn : Dec (α n ≡ true)) → 
                           gensNotInAHelper n αn ≡ generator n 
  gensNotInANoCaseHelper n ¬αn (yes p) = ex-falso $ ¬αn p
  gensNotInANoCaseHelper n ¬αn (no ¬p) = refl 

  gensNotInANoCase : (n : ℕ) → (¬αn : ¬ α n ≡ true) → gensThatAreNotInA n ≡ generator n
  gensNotInANoCase n ¬p = gensNotInANoCaseHelper n ¬p (α n =B true) 

  freeAcp : BooleanRing ℓ-zero
  freeAcp = freeBA ℕ /Im gensThatAreNotInA
  
  instance
    _ = snd freeAcp
 
  gensℕinFreeAHelper : (n : ℕ) → Dec (α n ≡ true) → ⟨ freeBA A ⟩
  gensℕinFreeAHelper n (yes p) = generator (n , p)
  gensℕinFreeAHelper n (no ¬p) = 𝟘 
  
  gensℕinFreeA : (n : ℕ) → ⟨ freeBA A ⟩
  gensℕinFreeA n = gensℕinFreeAHelper n (α n =B true) 

  gensℕinFreeAYesCaseHelper : (a : A) → (αn : Dec (α (fst a) ≡ true)) → 
                            gensℕinFreeAHelper (fst a) (αn) ≡ generator a
  gensℕinFreeAYesCaseHelper a (yes p) = cong generator (Σ≡Prop (λ _ → isSetBool _ _) refl)
  gensℕinFreeAYesCaseHelper a (no ¬p) = ex-falso (¬p (snd a)) 
  
  gensℕinFreeAYesCase : (a : A) → gensℕinFreeA (fst a) ≡ generator a
  gensℕinFreeAYesCase a = gensℕinFreeAYesCaseHelper a (α (fst a) =B true) 

  gensℕinFreeANoCaseHelper : (n : ℕ) → (¬αn : ¬ (α n ≡ true)) → (αn : Dec (α n ≡ true)) → 
                             gensℕinFreeAHelper n αn ≡ 𝟘 
  gensℕinFreeANoCaseHelper n ¬αn (yes p) = ex-falso $ ¬αn p 
  gensℕinFreeANoCaseHelper n ¬αn (no ¬p) = refl

  gensℕinFreeANoCase : (n : ℕ) → (¬αn : ¬ (α n ≡ true)) → gensℕinFreeA n ≡ 𝟘 
  gensℕinFreeANoCase n ¬p = gensℕinFreeANoCaseHelper n ¬p (α n =B true) 
 
  freeℕ→freeA : BoolHom (freeBA ℕ) (freeBA A)
  freeℕ→freeA = inducedBAHom ℕ (freeBA A) gensℕinFreeA
  
  open IsCommRingHom ⦃...⦄
  instance
    _ = (snd freeℕ→freeA) 

  AignoresOutsideAHelper : (n : ℕ) → (αn : Dec (α n ≡ true)) → 
    freeℕ→freeA $cr gensNotInAHelper n αn ≡ 𝟘 
  AignoresOutsideAHelper n (yes p) = pres0
  AignoresOutsideAHelper n (no ¬p) = 
    freeℕ→freeA $cr generator n 
      ≡⟨ funExt⁻ (evalBAInduce ℕ (freeBA A) gensℕinFreeA) n ⟩ 
    gensℕinFreeA n  
      ≡⟨ useDecidabilityIsUnqiue n (no ¬p) ⟩ 
    gensℕinFreeAHelper n (no ¬p)  
      ≡⟨⟩ 
    𝟘 ∎ where
    useDecidabilityIsUnqiue : (n : ℕ) → (αn : Dec (α n ≡ true)) → 
                              gensℕinFreeA n ≡ gensℕinFreeAHelper n αn
    useDecidabilityIsUnqiue n αn = cong (gensℕinFreeAHelper n) $ 
      (α n =B true) ≡⟨ isPropDec (isSetBool (α n) true) (α n =B true) αn ⟩ αn ∎ 

  AignoresOutsideA : (n : ℕ) → freeℕ→freeA $cr gensThatAreNotInA n ≡ 𝟘 
  AignoresOutsideA n = AignoresOutsideAHelper n (α n =B true) 

  freeAcp→freeA : BoolHom freeAcp (freeBA A)
  freeAcp→freeA = QB.inducedHom (freeBA A) freeℕ→freeA AignoresOutsideA 
  
  freeA→freeℕ : BoolHom (freeBA A) (freeBA ℕ)
  freeA→freeℕ = inducedBAHom A (freeBA ℕ) (generator ∘ fst) 

  freeA→freeAcp : BoolHom (freeBA A) (freeAcp)
  freeA→freeAcp = quotientImageHom ∘cr freeA→freeℕ 

  freeA→freeA≡idOnGens : (a : A) → (freeAcp→freeA ∘cr freeA→freeAcp) $cr generator a ≡ generator a
  freeA→freeA≡idOnGens a = 
    (freeAcp→freeA ∘cr quotientImageHom ∘cr freeA→freeℕ) $cr generator a 
      ≡⟨ 
        cong (λ y → (freeAcp→freeA ∘cr quotientImageHom) $cr y) 
        (funExt⁻ (evalBAInduce A (freeBA ℕ) (generator ∘ fst)) a) 
       ⟩ 
    (freeAcp→freeA ∘cr quotientImageHom) $cr generator (fst a) 
      ≡⟨⟩
    ((QB.inducedHom _ freeℕ→freeA _) ∘cr quotientImageHom)  $cr generator (fst a) 
      ≡⟨ 
        cong (λ h → h $cr generator (fst a)) 
        (QB.evalInduce _) 
       ⟩
    freeℕ→freeA $cr generator (fst a) 
      ≡⟨ 
        cong (λ h → h (fst a)) 
        (evalBAInduce ℕ (freeBA A) gensℕinFreeA)
       ⟩
    gensℕinFreeA (fst a) 
      ≡⟨ gensℕinFreeAYesCase a ⟩
    generator a ∎

  freeA→freeA≡id : (freeAcp→freeA ∘cr freeA→freeAcp) ≡ 
                   idCommRingHom (BooleanRing→CommRing (freeBA A))
  freeA→freeA≡id = equalityFromEqualityOnGenerators (freeBA A) _ _ freeA→freeA≡idOnGens

  instance 
    _ = snd (quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA} ∘cr freeA→freeℕ) 

  quotientOutNotAAgreesWithAOnGensHelper : (n : ℕ) → (Dec (α n ≡ true)) → 
    quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA} $cr 
    (freeA→freeℕ $cr gensℕinFreeA n)
    ≡ 
    quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA} $cr 
    generator n

  quotientOutNotAAgreesWithAOnGensHelper n (yes p) = 
    quotientImageHom $cr ( (freeA→freeℕ) $cr  (gensℕinFreeA n)) 
      ≡⟨ 
        cong (λ x → quotientImageHom $cr (freeA→freeℕ $cr x)) 
        (gensℕinFreeAYesCase (n , p))
       ⟩ 
    quotientImageHom $cr (((fst (freeA→freeℕ)) ∘ generator) (n , p)) 
      ≡⟨ cong (λ h → quotientImageHom $cr (h (n , p) )) (evalBAInduce _ _ _) ⟩
    quotientImageHom $cr (generator ∘ fst {B = (λ n → α n ≡ true)}) (n , p) 
      ≡⟨⟩
    quotientImageHom $cr generator n  ∎ 
  quotientOutNotAAgreesWithAOnGensHelper n (no ¬p) =  lhs=0 ∙ (sym rhs=0)  where
    
    genn=0Helper : (αn : Dec (α n ≡ true)) →  gensℕinFreeAHelper n αn ≡ 𝟘 
    genn=0Helper (yes p) = ex-falso $ ¬p p
    genn=0Helper (no ¬p) = refl 

    genn=0 : gensℕinFreeA n ≡ 𝟘 
    genn=0 = genn=0Helper (α n =B true)

    lhs=0 : quotientImageHom {B = freeBA ℕ } {f = gensThatAreNotInA } $cr 
             ((freeA→freeℕ) $cr  (gensℕinFreeA n)) ≡ 𝟘 
    lhs=0 = cong (λ x → quotientImageHom $cr (freeA→freeℕ $cr x)) genn=0 ∙ pres0
  
    rhs=0 : quotientImageHom {B = freeBA ℕ} {f = gensThatAreNotInA } $cr generator n ≡ 𝟘 
    rhs=0 = cong (fst quotientImageHom) (sym $ gensNotInANoCase n ¬p) ∙ zeroOnImage n 

  quotientOutNotAAgreesWithAOnGens : (n : ℕ) → 
    quotientImageHom $cr ( (freeA→freeℕ) $cr (gensℕinFreeA n)) 
    ≡ 
    quotientImageHom $cr generator n
  quotientOutNotAAgreesWithAOnGens n = quotientOutNotAAgreesWithAOnGensHelper n (α n =B true) 

  freeAcp→freeAcp∘q≡qOnGens : (n : ℕ) → 
    (freeA→freeAcp ∘cr freeAcp→freeA) $cr (quotientImageHom $cr generator n) 
    ≡ 
    quotientImageHom $cr (generator n)

  freeAcp→freeAcp∘q≡qOnGens n = 
    (freeA→freeAcp ∘cr freeAcp→freeA ∘cr quotientImageHom) $cr generator n 
       ≡⟨⟩ 
    (freeA→freeAcp ∘cr ((QB.inducedHom (freeBA A) freeℕ→freeA _) ∘cr quotientImageHom)) $cr generator n
       ≡⟨ cong (λ h → (freeA→freeAcp ∘cr h) $cr generator n) (QB.evalInduce _ ) ⟩ 
    (freeA→freeAcp ∘cr freeℕ→freeA) $cr generator n
       ≡⟨ cong (λ x → freeA→freeAcp $cr x ) (funExt⁻ (evalBAInduce _ _ _) n ) ⟩ 
    freeA→freeAcp $cr gensℕinFreeA n
       ≡⟨⟩
    quotientImageHom $cr (freeA→freeℕ $cr gensℕinFreeA n)
       ≡⟨ quotientOutNotAAgreesWithAOnGens n ⟩ 
     quotientImageHom $cr generator n
       ∎  

  freeAcp→freeAcp∘q≡q : (freeA→freeAcp ∘cr freeAcp→freeA ∘cr quotientImageHom) ≡ quotientImageHom 
  freeAcp→freeAcp∘q≡q = equalityFromEqualityOnGenerators freeAcp _ _ freeAcp→freeAcp∘q≡qOnGens 
  
  freeAcp→freeAcp≡id : fst (freeA→freeAcp ∘cr freeAcp→freeA) ≡ idfun ⟨ freeAcp ⟩ 
  freeAcp→freeAcp≡id = quotientImageHomEpi (_ ,  λ _ _ → is-set _ _ ) (cong fst freeAcp→freeAcp∘q≡q) 

  freeA≃freeAcp : BooleanRingEquiv (freeBA A) freeAcp
  freeA≃freeAcp .fst .fst = fst freeA→freeAcp
  freeA≃freeAcp .fst .snd = isoToIsEquiv explicitIso where
    explicitIso : Iso ⟨ freeBA A ⟩ ⟨ freeBA ℕ QB./Im gensThatAreNotInA ⟩
    explicitIso .Iso.fun = fst freeA→freeAcp
    explicitIso .Iso.inv = fst freeAcp→freeA
    explicitIso .Iso.sec = funExt⁻ freeAcp→freeAcp≡id
    explicitIso .Iso.ret = λ x → cong (λ h → h $cr x) freeA→freeA≡id 
  freeA≃freeAcp .snd = snd freeA→freeAcp 

  module quotientFreeByCountable  (γ : binarySequence) (f : (Σ[ n ∈ ℕ ] γ n ≡ true)  → ⟨ freeBA A ⟩) where
    freeA/f : BooleanRing ℓ-zero
    freeA/f = freeBA A QB./Im f 

    fExpand : ℕ → ⟨ freeBA A ⟩
    fExpand = quotientByCountable.g γ (freeBA A) f 

    freeA/fExpand : BooleanRing ℓ-zero
    freeA/fExpand = freeBA A QB./Im fExpand

    freeA/fExpand≃freeA/f : BooleanRingEquiv freeA/fExpand freeA/f
    freeA/fExpand≃freeA/f = quotientByCountable.quotient-by-expansion-equiv γ (freeBA A) f 

    e : ⟨ freeBA A ⟩ ≃ ⟨ freeAcp ⟩
    e = fst freeA≃freeAcp

    freeAcp/efExpand : BooleanRing ℓ-zero
    freeAcp/efExpand = freeAcp QB./Im (fst e ∘ fExpand) 

    freeA/fExpand≃freeAcp/efExpand : BooleanRingEquiv freeA/fExpand freeAcp/efExpand
    freeA/fExpand≃freeAcp/efExpand = EquivQuotBR freeA≃freeAcp fExpand

    liftExpandf : ℕ → ⟨ freeBA ℕ ⟩
    liftExpandf = fst freeA→freeℕ ∘ fExpand

    freeAcp/qliftExpandf : BooleanRing ℓ-zero
    freeAcp/qliftExpandf = freeAcp QB./Im (fst QB.quotientImageHom ∘ liftExpandf)
    freeA/f≃freeAcp/qliftExpandf : BooleanRingEquiv freeA/f freeAcp/qliftExpandf 
    freeA/f≃freeAcp/qliftExpandf = 
      freeA/fExpand≃freeAcp/efExpand ∘cre 
      invBooleanRingEquiv (freeBA A /Im fExpand) (freeBA A /Im f) 
      freeA/fExpand≃freeA/f

    presentation-freeℕ-freeAcp/ef : has-quotient-of-freeℕ-presentation freeAcp/qliftExpandf
    presentation-freeℕ-freeAcp/ef = quotient-of-sum-presentation.doubleQuotientPresented gensThatAreNotInA liftExpandf

    presentation-freeℕ-freeA/f : has-quotient-of-freeℕ-presentation freeA/f
    presentation-freeℕ-freeA/f = subst has-quotient-of-freeℕ-presentation 
      (sym $ uaBoolRing {A = freeA/f} {B = freeAcp/qliftExpandf } freeA/f≃freeAcp/qliftExpandf)
      presentation-freeℕ-freeAcp/ef 

free-on-countable-has-freeℕ-presentation : 
  (A : Type) → has-Countability-structure A → 
  has-quotient-of-freeℕ-presentation (freeBA A)
free-on-countable-has-freeℕ-presentation A (α , A=Σα) = 
  subst (has-quotient-of-freeℕ-presentation ∘ freeBA) 
  (sym $ isoToPath A=Σα) 
  (gensThatAreNotInA , freeA≃freeAcp)  where 
  open freeOnCountable α

quotient-of-free-on-countable-by-countable-has-freeℕ-presentation : 
  (A : Type) → has-Countability-structure A → 
  (X : Type) → has-Countability-structure X → 
  (f : X → ⟨ freeBA A ⟩) → 
  has-quotient-of-freeℕ-presentation (freeBA A QB./Im f)
quotient-of-free-on-countable-by-countable-has-freeℕ-presentation 
  A (α , A=Σα) X (γ , X=Σγ) = J2 
    {d = λ _ _ → (Σ-syntax ℕ λ n → γ n ≡ true)} 
    (λ A' _ X' _ → ( f' : X' → ⟨ freeBA A' ⟩) → has-quotient-of-freeℕ-presentation (freeBA A' QB./Im f')) 
    (freeOnCountable.quotientFreeByCountable.presentation-freeℕ-freeA/f α γ)
    (sym $ isoToPath A=Σα) (sym $ isoToPath X=Σγ)

has-countable-presentation→has-freeℕ-presentation : (B : BooleanRing ℓ-zero) → 
  has-countable-presentation B → has-quotient-of-freeℕ-presentation B
has-countable-presentation→has-freeℕ-presentation B 
  (A , Acount , X , Xcount , f , B=freeA/f) = 
  subst has-quotient-of-freeℕ-presentation 
  (sym (uaBoolRing {A = B} {B = freeBA A /Im f }B=freeA/f)) 
  (quotient-of-free-on-countable-by-countable-has-freeℕ-presentation 
  A Acount X Xcount f) 

-- Remark 1.4
countably-presented-equivalence : (B : BooleanRing ℓ-zero) → 
  is-countably-presented B ↔ is-countably-presented-alt B
countably-presented-equivalence B .fst = PT.map (has-countable-presentation→has-freeℕ-presentation B)
countably-presented-equivalence B .snd = PT.map (has-Boole'→ B) 
  
