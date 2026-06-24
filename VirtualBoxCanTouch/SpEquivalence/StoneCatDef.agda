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
open WeakInverse

------------------------------------------------------------------------
-- Composition of weak inverses (Cubical only provides symWeakInverse).  The
-- unit of the composite is split out as compWInvη so the counit can reuse it
-- by symmetry.
------------------------------------------------------------------------

compWInvη :
  {ℓ𝓒 ℓ𝓒' ℓ𝓓 ℓ𝓓' ℓ𝓔 ℓ𝓔' : Level}
  {𝓒 : Category ℓ𝓒 ℓ𝓒'} {𝓓 : Category ℓ𝓓 ℓ𝓓'} {𝓔 : Category ℓ𝓔 ℓ𝓔'}
  {F : Functor 𝓒 𝓓} {H : Functor 𝓓 𝓔}
  (wF : WeakInverse F) (wH : WeakInverse H)
  → NatIso 𝟙⟨ 𝓒 ⟩ ((invFunc wF ∘F invFunc wH) ∘F (H ∘F F))
compWInvη {F = F} {H = H} wF wH =
  seqNatIso (η wF)
   (seqNatIso (invFunc wF ∘ʳi midF)
    (seqNatIso (CAT⋆Assoc F (invFunc wH ∘F H) (invFunc wF))
     (seqNatIso (F ∘ˡi CAT⋆Assoc H (invFunc wH) (invFunc wF))
      (symNatIso (CAT⋆Assoc F H (invFunc wF ∘F invFunc wH))))))
  where
    midF : NatIso F ((invFunc wH ∘F H) ∘F F)
    midF = seqNatIso (symNatIso (CAT⋆IdR {F = F})) (F ∘ˡi η wH)

compWeakInverse :
  {ℓ𝓒 ℓ𝓒' ℓ𝓓 ℓ𝓓' ℓ𝓔 ℓ𝓔' : Level}
  {𝓒 : Category ℓ𝓒 ℓ𝓒'} {𝓓 : Category ℓ𝓓 ℓ𝓓'} {𝓔 : Category ℓ𝓔 ℓ𝓔'}
  {F : Functor 𝓒 𝓓} {H : Functor 𝓓 𝓔}
  → WeakInverse F → WeakInverse H → WeakInverse (H ∘F F)
compWeakInverse wF wH .invFunc = invFunc wF ∘F invFunc wH
compWeakInverse wF wH .η = compWInvη wF wH
compWeakInverse wF wH .ε = symNatIso (compWInvη (symWeakInverse wH) (symWeakInverse wF))

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

  Stone→ImageWeakInverse : WeakInverse Stone→Image
  Stone→ImageWeakInverse .invFunc = Image→Stone
  Stone→ImageWeakInverse .η       = unitIso
  Stone→ImageWeakInverse .ε       = counitIso

  StoneCat'^op≃StoneCat : (StoneCat' ^op) ≃ᶜ StoneCat
  StoneCat'^op≃StoneCat = equivᶜ Stone→Image ∣ Stone→ImageWeakInverse ∣₁

  ------------------------------------------------------------------------
  -- Sp as a functor into StoneCat' ^op, and the proof it is an equivalence,
  -- obtained by composing  BooleωCat ≃ StoneCat  (Sp-duality) with
  -- StoneCat ≃ StoneCat' ^op  (the symmetric of StoneCat'^op≃StoneCat).
  ------------------------------------------------------------------------

  SpFunctor' : Functor BooleωCat (StoneCat' ^op)
  SpFunctor' = Image→Stone ∘F SpStoneFunctor

  SpFunctor'-isEquivalence : isEquivalence SpFunctor'
  SpFunctor'-isEquivalence =
    map2 compWeakInverse (Sp-isEquivalence sd) ∣ symWeakInverse Stone→ImageWeakInverse ∣₁

  BooleωCat≃StoneCat'^op : BooleωCat ≃ᶜ (StoneCat' ^op)
  BooleωCat≃StoneCat'^op = equivᶜ SpFunctor' SpFunctor'-isEquivalence
