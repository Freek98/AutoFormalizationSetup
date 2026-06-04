{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- This file shows algebraically that the spectrum of the product of two Boolean algebras is the sum of the spectra. The proof was written by an LLM.
--
-- Note that this file does not depend on Stone duality. Also, the result is not a corollary of the adjunction between Sp and 2^. This I personally found surprising and confusing for some time.
-- Rather, it's an application of an exercise in ring theory. See for example exercise 22 in chapter 1 of Atiyah-MacDonald, or https://stacks.math.columbia.edu/tag/00ED
--
-- The main idea is that for a Boolean map f : A × B → Bool, we have f(1,0) = 1 or f(1,0) = 0.
-- Assuming the first case, f (a,b) = f(a,0) for all b and f comes from a map A → Bool already. 
module StoneSums where

open import Cubical.Foundations.Prelude hiding (_∧_)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma hiding (_∧_)
open import Cubical.Data.Sum as ⊎ using (_⊎_ ; inl ; inr)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ex-falso)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingTheory)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BooleanRing.BooleanRingMaps
open import BooleanRing.BoolAlgMorphism
open import BooleanRing.ProductBA
open import StoneSpaces.Spectrum

private
  variable
    ℓ ℓ' : Level

module SpectrumProduct (A : BooleanRing ℓ) (B : BooleanRing ℓ') where
  open BRProduct A B
  open BooleanRingStr ⦃...⦄
  open BooleanAlgebraStr ⦃...⦄
  instance
    _ = snd A
    _ = snd B
    _ = snd product
    _ = snd BoolBR

  onlyLookAtA : SpGeneralBooleanRing A → SpGeneralBooleanRing (A ×BR B)
  onlyLookAtA = _∘cr fstBA

  onlyLookAtB : SpGeneralBooleanRing B → SpGeneralBooleanRing (A ×BR B)
  onlyLookAtB = _∘cr sndBA

  onlyLookAtOneSide : SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B → SpGeneralBooleanRing product
  onlyLookAtOneSide = ⊎.rec onlyLookAtA onlyLookAtB

  --following holds for general ring products:
  splitTupleAsSum : (a : ⟨ A ⟩) (b : ⟨ B ⟩) → (a , b) ≡ (a , 𝟘) + (𝟘 , b)
  splitTupleAsSum a b = sym $ ΣPathP (+IdR a , +IdL b)

  private
    convenientProductFactorA : (a : ⟨ A ⟩) (b : ⟨ B ⟩) → (a , b) ≡ (a , b) · (𝟙 , b)
    convenientProductFactorA a b = sym $ ΣPathP (∧IdR , ·Idem b)

    convenientProductFactorB : (a : ⟨ A ⟩) (b : ⟨ B ⟩) → (a , b) ≡ (a , b) · (a , 𝟙)
    convenientProductFactorB a b = sym $ ΣPathP (·Idem a , ∧IdR)

  module splitProductAction (f : SpGeneralBooleanRing (A ×BR B)) where
    open IsCommRingHom (snd f)
    open IsBoolAlgHom f
    actsOnlyOnA : Type _
    actsOnlyOnA = (a : ⟨ A ⟩) → (b : ⟨ B ⟩) → f $cr (a , b) ≡ f $cr (a , 𝟘)

    actsOnlyOnB : Type _
    actsOnlyOnB = (a : ⟨ A ⟩) → (b : ⟨ B ⟩) → f $cr (a , b) ≡ f $cr (𝟘 , b)

    private
      onlyOneUnitCanLive : f $cr (𝟙 , 𝟘) ≡ true → f $cr (𝟘 , 𝟙) ≡ false
      onlyOneUnitCanLive f10=t =
        f $cr (𝟘 , 𝟙)
          ≡⟨ sym $ cong (f $cr_) (ΣPathP (¬1≡0 , ¬0≡1)) ⟩
        f $cr (¬ (𝟙 , 𝟘))
          ≡⟨ pres¬ (𝟙 , 𝟘) ⟩
        ¬ f $cr (𝟙 , 𝟘)
          ≡⟨ cong ¬_ f10=t ⟩
        false ∎

    actsOnAorB : actsOnlyOnA ⊎ actsOnlyOnB
    actsOnAorB = case (dichotomyBool $ f $cr (𝟙 , 𝟘)) return (λ _ → actsOnlyOnA ⊎ actsOnlyOnB)   of λ
      { (inl f10=true) → inl λ a b →
        f $cr (a , b)
          ≡⟨ cong (f $cr_) (splitTupleAsSum a b) ⟩
        f $cr ((a , 𝟘) + (𝟘 , b))
          ≡⟨ pres+ _ _ ⟩
        f $cr (a , 𝟘) + f $cr ( 𝟘 , b)
          ≡⟨ cong ((f $cr (a , 𝟘)) +_)
                (f $cr (𝟘 , b)
                  ≡⟨ cong (f $cr_) (convenientProductFactorB 𝟘 b) ⟩
                f $cr ((𝟘 , b) · (𝟘 , 𝟙))
                  ≡⟨ pres· _ _ ⟩
                f $cr (𝟘 , b) · f $cr (𝟘 , 𝟙)
                  ≡⟨ cong ((f $cr (𝟘 , b)) ·_) (onlyOneUnitCanLive f10=true) ⟩
                f $cr (𝟘 , b) · 𝟘
                  ≡⟨ ∧AnnihilR ⟩
                𝟘 ∎)  ⟩
        f $cr (a , 𝟘) + 𝟘
          ≡⟨ +IdR (f $cr (a , 𝟘)) ⟩
        f $cr (a , 𝟘) ∎
      ; (inr f10=false) → inr λ a b →
        f $cr (a , b)
          ≡⟨ cong (f $cr_) (splitTupleAsSum a b) ⟩
        f $cr ((a , 𝟘) + (𝟘 , b))
          ≡⟨ pres+ _ _ ⟩
        f $cr (a , 𝟘)  + f $cr (𝟘 , b)
          ≡⟨ cong (_+ (f $cr (𝟘 , b))) $
               f $cr (a , 𝟘)
                 ≡⟨ cong (f $cr_) (convenientProductFactorA a 𝟘) ⟩
               f $cr ((a , 𝟘) · (𝟙 , 𝟘))
                 ≡⟨ pres· _ _ ⟩
               f $cr (a , 𝟘) · f $cr (𝟙 , 𝟘)
                 ≡⟨ cong ((f $cr (a , 𝟘)) ·_) f10=false ⟩
               f $cr (a , 𝟘) · 𝟘
                 ≡⟨ ∧AnnihilR ⟩
               𝟘 ∎ ⟩
        𝟘 + f $cr (𝟘 , b)
          ≡⟨ +IdL _ ⟩
        f $cr (𝟘 , b) ∎ }

    module ACase (aEyesOnly : actsOnlyOnA) where
      doesntCareAboutB : (a : ⟨ A ⟩) → (b b' : ⟨ B ⟩) → f $cr (a , b) ≡ f $cr (a , b')
      doesntCareAboutB a b b' = aEyesOnly a b ∙ (sym $ aEyesOnly a b')

      restrictToA : SpGeneralBooleanRing A
      restrictToA .fst a = f $cr (a , 𝟘)
      restrictToA .snd = FromPres¬∧.isBoolRingHom A BoolBR (\a → f $cr (a , 𝟘))
        (λ a → f $cr (¬ a , 𝟘)     ≡⟨ doesntCareAboutB (¬ a) 𝟘 (¬ 𝟘) ⟩
               f $cr (¬ a , (¬ 𝟘)) ≡⟨ pres¬ _ ⟩
              ¬ (f $cr (a , 𝟘))    ∎)
        λ a a' → f $cr (a ∧ a' , 𝟘 )        ≡⟨ cong (f $cr_) $ ΣPathP (refl , sym (·Idem 𝟘))⟩
                 f $cr ((a , 𝟘) ∧ (a' , 𝟘)) ≡⟨ pres∧ _ _ ⟩
                 f $cr (a , 𝟘) ∧ f $cr (a' , 𝟘) ∎

      restrictionIsRetract : onlyLookAtA restrictToA ≡ f
      restrictionIsRetract = CommRingHom≡ (funExt λ ((a , b)) → sym $ aEyesOnly a b)

    module BCase (bEyesOnly : actsOnlyOnB) where
      doesntCareAboutA : (b : ⟨ B ⟩) → (a a' : ⟨ A ⟩) → f $cr (a , b) ≡ f $cr (a' , b)
      doesntCareAboutA b a a' = bEyesOnly a b ∙ (sym $ bEyesOnly a' b)

      restrictToB : SpGeneralBooleanRing B
      restrictToB .fst b = f $cr (𝟘 , b)
      restrictToB .snd = FromPres¬∧.isBoolRingHom B BoolBR (\b → f $cr (𝟘 , b))
        (λ b → f $cr (𝟘 , ¬ b)     ≡⟨ doesntCareAboutA (¬ b) 𝟘 (¬ 𝟘) ⟩
               f $cr ((¬ 𝟘) , ¬ b) ≡⟨ pres¬ _ ⟩
              ¬ (f $cr (𝟘 , b))    ∎)
        λ b b' → f $cr (𝟘 , b ∧ b' )        ≡⟨ cong (f $cr_) $ ΣPathP (sym (·Idem 𝟘) , refl) ⟩
                 f $cr ((𝟘 , b) ∧ (𝟘 , b')) ≡⟨ pres∧ _ _ ⟩
                 f $cr (𝟘 , b) ∧ f $cr (𝟘 , b') ∎

      restrictionIsRetract : onlyLookAtB restrictToB ≡ f
      restrictionIsRetract = CommRingHom≡ (funExt λ ((a , b)) → sym $ bEyesOnly a b)
  
    splitToImportantArg : actsOnlyOnA ⊎ actsOnlyOnB → SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
    splitToImportantArg = ⊎.rec (inl ∘ ACase.restrictToA) (inr ∘ BCase.restrictToB) 

    retractCase : onlyLookAtOneSide (splitToImportantArg actsOnAorB) ≡ f 
    retractCase = case actsOnAorB return (\d → onlyLookAtOneSide (splitToImportantArg d) ≡ f) of λ 
      { (inl x) → ACase.restrictionIsRetract x
      ; (inr x) → BCase.restrictionIsRetract x } 
  
  module Asection (f : SpGeneralBooleanRing A) where
    open splitProductAction (onlyLookAtA f)
    open IsCommRingHom
    secA : (splitToImportantArg actsOnAorB) ≡ inl f 
    secA = case actsOnAorB return (λ d → splitToImportantArg d ≡ inl f) of λ 
      { (inl x) → cong inl (CommRingHom≡ refl)
      ; (inr ab=0b) → ex-falso (true≢false $ 
        𝟙                          ≡⟨ sym (pres1 $ snd f) ⟩ 
        f $cr 𝟙                    ≡⟨⟩
        onlyLookAtA f $cr (𝟙 , 𝟘)  ≡⟨ ab=0b 𝟙 𝟘 ⟩
        onlyLookAtA f $cr (𝟘 , 𝟘)  ≡⟨ pres0 $ snd (onlyLookAtA f) ⟩
        𝟘 ∎ ) } 

  module Bsection (f : SpGeneralBooleanRing B) where
    open splitProductAction (onlyLookAtB f)
    open IsCommRingHom
    secB : (splitToImportantArg actsOnAorB) ≡ inr f 
    secB = case actsOnAorB return (λ d → splitToImportantArg d ≡ inr f) of λ 
      { (inr x) → cong inr (CommRingHom≡ refl)
      ; (inl ab=a0) → ex-falso (true≢false $ 
        𝟙                          ≡⟨ sym (pres1 $ snd f) ⟩ 
        f $cr 𝟙                    ≡⟨⟩
        onlyLookAtB f $cr (𝟘 , 𝟙)  ≡⟨ ab=a0 𝟘 𝟙 ⟩
        onlyLookAtB f $cr (𝟘 , 𝟘)  ≡⟨ pres0 $ snd (onlyLookAtB f) ⟩
        𝟘 ∎ ) } 

  conclusion : Iso (SpGeneralBooleanRing (A ×BR B))
                   (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
  conclusion .Iso.fun f = splitToImportantArg actsOnAorB where
    open splitProductAction f
  conclusion .Iso.inv = onlyLookAtOneSide
  conclusion .Iso.sec (inl Amap) = Asection.secA Amap
  conclusion .Iso.sec (inr Bmap) = Bsection.secB Bmap 
  conclusion .Iso.ret = splitProductAction.retractCase

SpProd≅SpSum : (A : BooleanRing ℓ) (B : BooleanRing ℓ') → 
  Iso (SpGeneralBooleanRing (A ×BR B))
      (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
SpProd≅SpSum = SpectrumProduct.conclusion
