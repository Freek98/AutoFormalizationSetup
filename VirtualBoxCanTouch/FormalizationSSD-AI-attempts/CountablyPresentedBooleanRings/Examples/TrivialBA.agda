{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Examples.TrivialBA where 

open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import BooleanRing.BooleanRingMaps
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat hiding (_·_)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing.Base

open import Cubical.Data.Sigma
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.QuotientConclusions
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import BasicDefinitions
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Foundations.Structure

open import Cubical.Algebra.CommRing.Instances.Unit

trivialBooleanRing : BooleanRing ℓ-zero 
trivialBooleanRing = idemCommRing→BR UnitCommRing λ tt → refl 

module _ {ℓ' : Level} (B : BooleanRing ℓ') where
      -- TODO note that you can do this for commutative rings, not just Boolean rings
  open BooleanRingStr (snd B) 
  mapToTrivialBooleanRing : BoolHom B trivialBooleanRing
  mapToTrivialBooleanRing = mapToUnitCommRing $ BooleanRing→CommRing B
  open IsCommRingHom (snd mapToTrivialBooleanRing)

  isTrivial : Type ℓ'
  isTrivial = 𝟘 ≡ 𝟙
  
  module TrivialCharacterization (isTriv : isTrivial) where
    isTrivial→isContr : isContr ⟨ B ⟩
    isTrivial→isContr .fst = 𝟘
    isTrivial→isContr .snd b = 𝟘  ≡⟨ sym ∧AnnihilR ⟩ (b · 𝟘) ≡⟨ cong (λ c → b · c) isTriv ⟩ b · 𝟙 ≡⟨ ∧IdR ⟩  b ∎  where 
      open BooleanAlgebraStr (snd B)

    isTrivial→isEquivmapToTrivial : isEquiv (fst mapToTrivialBooleanRing)
    isTrivial→isEquivmapToTrivial .equiv-proof tt* = (𝟘 , pres0) , λ (b , fb=tt) → Σ≡Prop 
      (λ _ → BooleanRingStr.is-set (snd trivialBooleanRing) _ _) 
      (isTrivial→isContr .snd b ) 
  
    trivialCharacterizes : BooleanRingEquiv B trivialBooleanRing
    trivialCharacterizes .fst .fst = fst mapToTrivialBooleanRing
    trivialCharacterizes .fst .snd = isTrivial→isEquivmapToTrivial
    trivialCharacterizes .snd = snd mapToTrivialBooleanRing

countUnit : has-Countability-structure Unit
countUnit = δSequence 0 , Unit=Σδ0 where
  Unit=Σδ0 : Iso Unit $ Σℕ (δSequence 0)
  Unit=Σδ0 .Iso.fun tt = 0 , refl
  Unit=Σδ0 .Iso.inv _  = tt
  Unit=Σδ0 .Iso.sec (zero , _) = Σ≡Prop (λ _ → isSetBool _ _) refl
  Unit=Σδ0 .Iso.sec (suc n , δ0Sn=true) = ex-falso (false≢true δ0Sn=true)
  Unit=Σδ0 .Iso.ret = snd isContrUnit

module trivialPresentation where 
  point1 : Unit → Bool
  point1 tt = true
  
  e = fst (fst 2≃free⊥) 
  free⊥/1 = (free⊥ /Im (e ∘ point1))

  open BooleanRingStr ⦃...⦄
  instance
    _ = snd free⊥/1
    _ = snd free⊥
  open IsCommRingHom (snd $ quotientImageHom {B = free⊥} {f = (e ∘ point1)})
  0=1 : 𝟘 ≡ 𝟙 
  0=1 = 𝟘 ≡⟨ sym $ zeroOnImage tt  ⟩ 
        quotientImageHom $cr 𝟙
          ≡⟨ pres1 ⟩ 
        𝟙 ∎

  triv≃free⊥/1 : BooleanRingEquiv trivialBooleanRing free⊥/1
  triv≃free⊥/1 = invBooleanRingEquiv free⊥/1 trivialBooleanRing 
    (TrivialCharacterization.trivialCharacterizes free⊥/1 0=1) 

  presentation : has-countable-presentation trivialBooleanRing
  presentation = ⊥ , count⊥ , Unit , countUnit , e ∘ point1 , triv≃free⊥/1
 
