module StoneCatDef where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism hiding (isIso)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.WeakEquivalence
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Categories.Constructions.FullSubcategory
open import Cubical.Algebra.CommRing
open import StoneSpaces.Spectrum
open import CategoryTheory.SigmaPropCat
open import CategoryTheory.StuffFromStoneAboutBAs
open import Axioms.StoneDuality
open import CountablyPresentedBooleanRings.Definitions
open import BooleanRing.BoolRingUnivalence
open import Cubical.Foundations.Function
open import AdjunctionUnitIsoEquivalence
open import NewSpDuality

open Category hiding (_∘_)
open Functor
open isWeakEquivalence

-- The carrier of a Stone space is a set: it is (a transport of) the spectrum
-- of a Boolean algebra, which is a set.
isSetStoneCarrier : (S : Stone) → isSet ⟨ S ⟩
isSetStoneCarrier S = subst isSet (str S .snd) (isSetSp (fst (str S .fst)))

StoneCat' : Category _ _
StoneCat' .ob = Stone
StoneCat' .Hom[_,_] S T = ⟨ S ⟩ → ⟨ T ⟩
StoneCat' .id = λ x → x
StoneCat' ._⋆_ f g = g ∘ f
StoneCat' .⋆IdL f = refl
StoneCat' .⋆IdR f = refl
StoneCat' .⋆Assoc f g h = refl
StoneCat' .isSetHom {y = T} = isSetΠ λ _ → isSetStoneCarrier T

------------------------------------------------------------------------
-- StoneCat' ^op is equivalent to StoneCat (the image of Sp : Booleω → Set^op).
--
-- Both have the same carriers and the same (contravariant) function morphisms;
-- they differ only in the witness that an object is Stone: StoneCat' carries an
-- honest hasStoneStr, StoneCat a mere ∥ in the image of Sp ∥.  Going from
-- StoneCat' to StoneCat just truncates (axiom-free); going back needs split
-- support, i.e. that hasStoneStr is a proposition — which is the Stone duality
-- axiom (isPropHasStoneStr).
------------------------------------------------------------------------

-- Forget the Stone structure to mere membership in the image of Sp (axiom-free).
Stone→Image : Functor (StoneCat' ^op) StoneCat
Stone→Image .F-ob S =
  (⟨ S ⟩ , isSetStoneCarrier S) , ∣ str S .fst , TypeOfHLevel≡ 2 (str S .snd) ∣₁
Stone→Image .F-hom f   = f
Stone→Image .F-id      = refl
Stone→Image .F-seq f g = refl

module _ (sd : StoneDualityAxiom) where

  -- Recover the Stone structure from a mere image-membership witness, using that
  -- hasStoneStr is a proposition (split support).
  Image→Stone : Functor StoneCat (StoneCat' ^op)
  Image→Stone .F-ob (Y , t) =
    ⟨ Y ⟩ , rec (isPropHasStoneStr sd ⟨ Y ⟩) (λ (B , q) → B , cong fst q) t
  Image→Stone .F-hom f   = f
  Image→Stone .F-id      = refl
  Image→Stone .F-seq f g = refl

  -- Both round-trips fix carriers and morphisms, changing only the propositional
  -- structure, so unit and counit are the identity natural isos.
  unitIso : 𝟙⟨ StoneCat' ^op ⟩ ≅ᶜ (Image→Stone ∘F Stone→Image)
  unitIso .NatIso.trans .NatTrans.N-ob S  = λ x → x
  unitIso .NatIso.trans .NatTrans.N-hom f = refl
  unitIso .NatIso.nIso S                   = isiso (λ x → x) refl refl

  counitIso : (Stone→Image ∘F Image→Stone) ≅ᶜ 𝟙⟨ StoneCat ⟩
  counitIso .NatIso.trans .NatTrans.N-ob S  = λ x → x
  counitIso .NatIso.trans .NatTrans.N-hom f = refl
  counitIso .NatIso.nIso S                   = isiso (λ x → x) refl refl

  StoneCat'^op≃StoneCat : (StoneCat' ^op) ≃ᶜ StoneCat
  StoneCat'^op≃StoneCat = equivᶜ Stone→Image ∣ weakInverse ∣₁
    where
      weakInverse : WeakInverse Stone→Image
      weakInverse .WeakInverse.invFunc = Image→Stone
      weakInverse .WeakInverse.η       = unitIso
      weakInverse .WeakInverse.ε       = counitIso
