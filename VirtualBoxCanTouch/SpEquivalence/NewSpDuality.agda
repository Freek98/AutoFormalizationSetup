{-# OPTIONS --cubical --guardedness --lossy-unification #-}

{-
  NewSpDuality — the category of Stone spaces as the image of the spectrum
  functor Sp : Booleω → Set^op, and the "decidable subsets" functor back.

    · StoneCat        — the image of SpFunctor (ImageFunctor.ImageCat).
    · SpStoneFunctor  — Sp corestricted to its image (ImageFunctor.F|Image).
    · 2^Stone         — decidable subsets, StoneCat → Booleω (needs the Stone
                        duality axiom so that 2^ of a Stone space is countably
                        presented).
-}

module NewSpDuality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
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
open import AdjunctionUnitIsoEquivalence

open Category using (ob)
open Functor
open isWeakEquivalence

-- The category of Stone spaces: the image of Sp : Booleω → Set^op.
StoneCat : Category _ _
StoneCat = ImageFunctor.ImageCat SpFunctor

-- Sp corestricted to its image.
SpStoneFunctor : Functor BooleωCat StoneCat
SpStoneFunctor = ImageFunctor.F|Image SpFunctor

------------------------------------------------------------------------
-- Univalence.  SET is univalent (isUnivalentSET) and Booleω is univalent
-- (BooleωUnivalent, from CategoryTheory.StuffFromStoneAboutBAs).  StoneCat is
-- a full subcategory of the univalent category SET^op on a propositional
-- predicate, hence univalent too.
------------------------------------------------------------------------

StoneCatUnivalent : isUnivalent StoneCat
StoneCatUnivalent =
  isUnivalentFullSub ((SET ℓ-zero) ^op) (λ _ → squash₁) (isUnivalentOp isUnivalentSET)

module _ (sd : StoneDualityAxiom) where
  2^isCP : (S : ob StoneCat) → is-countably-presented-alt (2^ ⟨ fst S ⟩)
  2^isCP (Y , t) =
    rec squash₁
      (λ (B , p) → subst is-countably-presented-alt
        (equivFun (BoolRingPath (fst B) (2^ (Sp B))) (SDHomVersion sd B)
          ∙ cong (λ T → 2^ ⟨ T ⟩) p)
        (snd B))
      t

  -- The right adjoint "take decidable subsets", StoneCat → Booleω.
  2^Stone : Functor StoneCat BooleωCat
  2^Stone .F-ob S    = 2^ ⟨ fst S ⟩ , 2^isCP S
  2^Stone .F-hom g   = 2^Functor .F-hom g
  2^Stone .F-id      = 2^Functor .F-id
  2^Stone .F-seq f g = 2^Functor .F-seq f g

  -- The adjunction SpStoneFunctor ⊣ 2^Stone.  The hom-set bijection is the one
  -- underlying Sp ⊣ 2^ (homs in StoneCat / BooleωCat are inherited from
  -- SET^op / BACat), so it mirrors Sp⊣2^' at the restricted objects.
  SpStoneFunctor⊣2^Stone' : SpStoneFunctor NaturalBijection.⊣ 2^Stone
  SpStoneFunctor⊣2^Stone' .NaturalBijection._⊣_.adjIso {c = B} {d = S} =
    invIso (equivToIso (SpDecAdjunction.adjunction (fst B) ⟨ fst S ⟩))
  SpStoneFunctor⊣2^Stone' .NaturalBijection._⊣_.adjNatInD _ _ = CommRingHom≡ refl
  SpStoneFunctor⊣2^Stone' .NaturalBijection._⊣_.adjNatInC _ _ = funExt λ _ → CommRingHom≡ refl

  -- … in unit–counit form.
  SpStoneFunctor⊣2^Stone : SpStoneFunctor UnitCounit.⊣ 2^Stone
  SpStoneFunctor⊣2^Stone = adj'→adj _ _ SpStoneFunctor⊣2^Stone'

  -- The unit's components are the evaluation maps.
  unitIsEvaluation : (B : ob BooleωCat)
    → NatTrans.N-ob (UnitCounit._⊣_.η SpStoneFunctor⊣2^Stone) B ≡ evaluationHom B
  unitIsEvaluation B = CommRingHom≡ refl

  -- Stone duality says exactly that the unit η is a natural iso: at each B it is
  -- the evaluation map, which the axiom makes an iso (ηIsoOnBooleω), lifted from
  -- BACat to BooleωCat.
  η-natIso : (B : ob BooleωCat)
    → isIso BooleωCat (NatTrans.N-ob (UnitCounit._⊣_.η SpStoneFunctor⊣2^Stone) B)
  η-natIso B =
    subst (isIso BooleωCat) (sym (unitIsEvaluation B))
      (isIsoΣPropCat* BACat (λ R → is-countably-presented-alt R , squash₁)
        {x = fst B} {y = 2^ (Sp B)} {xp = snd B} {yp = 2^isCP (SpStoneFunctor ⟅ B ⟆)}
        (subst (isIso BACat {x = fst B} {y = 2^ (Sp B)}) (ηBA'Agrees (fst B)) (ηIsoOnBooleω sd B)))

  -- THE HEADLINE: Sp is an anti-equivalence between Booleω and Stone.  Since
  -- SpStoneFunctor is already the corestriction of Sp to its image, it is
  -- essentially surjective by construction; the unit being iso everywhere makes
  -- it fully faithful (ηIso→FFullyFaithful).
  Sp-anti-equivalence : isWeakEquivalence SpStoneFunctor
  Sp-anti-equivalence .fullfaith =
    adjunctionFact.ηIso→FFullyFaithful SpStoneFunctor 2^Stone SpStoneFunctor⊣2^Stone η-natIso
  Sp-anti-equivalence .esssurj =
    ImageFunctor.F|ImageIsEssentiallySurjective SpFunctor

  -- Both BooleωCat and StoneCat are univalent, so the weak equivalence upgrades
  -- to a genuine equivalence of categories (an explicit inverse functor with
  -- unit and counit natural isos).
  Sp-isEquivalence : isEquivalence SpStoneFunctor
  Sp-isEquivalence = isWeakEquiv→isEquiv BooleωUnivalent StoneCatUnivalent Sp-anti-equivalence

  Sp-duality : BooleωCat ≃ᶜ StoneCat
  Sp-duality = equivᶜ SpStoneFunctor Sp-isEquivalence
