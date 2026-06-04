{-# OPTIONS --cubical --guardedness --lossy-unification #-}

{-
  SpDuality — the genuine category of Stone spaces, and the anti-equivalence
  that the Stone duality axiom produces.

  Everything about the adjunction itself already lives in FormalizationSSD
  and is used here by its existing names (not restated):

    LAYER 1 (axiom-free).  The contravariant adjunction between Boolean
      algebras and sets.  See CategoryTheory.StuffFromStoneAboutBAs:
        · SpGeneralFunctor / 2^Functor   — Sp and "decidable subsets"
        · Sp⊣2^                          — the adjunction (unit–counit form)
        · ηBA / ηBA'                      — its unit
        · ηBA'Agrees                     — unit component = evaluation map

    LAYER 2 (axiom-free, general).  CategoryTheory.StuffThatWasInStoneAnd…
      turns "the unit is an iso" into full faithfulness
      (adjunctionFact.ηIso≃εIso, …ηIsoOnImageH→FHFullyFaithful).

    LAYER 3 (Stone duality axiom).  Axioms.StoneDuality:
        · StoneDualityAxiom              — evaluation is an iso on Booleω
        · ηIsoOnBooleω                   — hence the unit is iso there
        · SpFullyFaithful                — hence SpFunctor is fully faithful

  The NEW content below is what is missing: the genuine category of Stone
  spaces as a full subcategory of SET, and the headline statement that Sp is
  an ANTI-equivalence onto it.

  STATUS (decisions: "genuine full subcategory of SET", "state only").  The
  category of Stone spaces and the corestricted spectrum functor are fully
  defined and axiom-free; the three axiom-dependent results are stated with
  their precise types and left as goals to fill interactively.
-}

module SpDuality where

open import Cubical.Foundations.Prelude
open import Cubical.Relation.Nullary
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.HLevels   using (hSet ; hProp ; TypeOfHLevel≡)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁ ; ∣_∣₁ ; squash₁ ; rec)

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.NaturalTransformation
open import Cubical.Categories.Adjoint
open import Cubical.Categories.Equivalence
open import Cubical.Categories.Equivalence.AdjointEquivalence hiding (adjunction)
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Foundations.Isomorphism using (invIso)
open import Cubical.Algebra.CommRing using (CommRingHom≡)

open import StoneSpaces.Spectrum
open import CategoryTheory.SigmaPropCat
open import CategoryTheory.StuffFromStoneAboutBAs
open import CategoryTheory.StuffThatWasInStoneAndShouldBeOrganized using (Cuniv ; module adjunctionFact)
open import Axioms.StoneDuality
open import CountablyPresentedBooleanRings.Definitions using (is-countably-presented-alt)
open import BooleanRing.BoolRingUnivalence using (BoolRingPath)
open import Cubical.Foundations.Equiv using (equivFun ; equivToIso ; idIsEquiv ; invIsEq)
open import Cubical.Functions.Embedding using (isEmbedding ; EmbeddingΣProp)
open import Cubical.Categories.Equivalence.WeakEquivalence using (isWeakEquivalence ; isWeakEquiv→isEquiv)

open Category using (ob)
open Functor

------------------------------------------------------------------------
-- The genuine category of Stone spaces.
--
-- A type is Stone if it is merely the spectrum of some countably presented
-- Boolean algebra.  Truncating keeps the predicate a proposition without
-- assuming Stone duality (under the axiom hasStoneStr is already a
-- proposition: isPropHasStoneStr).
------------------------------------------------------------------------

isStone : Type ℓ-zero → hProp (ℓ-suc ℓ-zero)
isStone S = ∥ hasStoneStr S ∥₁ , squash₁

isStoneSet : hSet ℓ-zero → hProp (ℓ-suc ℓ-zero)
isStoneSet S = isStone ⟨ S ⟩

StoneCat : Category (ℓ-suc ℓ-zero) ℓ-zero
StoneCat = ΣPropCat* (SET ℓ-zero) isStoneSet

Stone↪Set : Functor StoneCat (SET ℓ-zero)
Stone↪Set = fstFunctor (SET ℓ-zero) isStoneSet

SpStoneFunctor : Functor BooleωCat (StoneCat ^op)
SpStoneFunctor .F-ob B       = SpGeneralFunctor ⟅ fst B ⟆ , ∣ B , refl ∣₁
SpStoneFunctor .F-hom f      = SpGeneralFunctor .F-hom f
SpStoneFunctor .F-id {x = B} = SpGeneralFunctor .F-id {x = fst B}
SpStoneFunctor .F-seq f g    = SpGeneralFunctor .F-seq f g

-- StoneCat is univalent: it is the full subcategory of the univalent category
-- SET on a propositional predicate, included by Stone↪Set (axiom-free).
Stone↪Set-fullyFaithful : isFullyFaithful Stone↪Set
Stone↪Set-fullyFaithful X Y = idIsEquiv _

Stone↪Set-isEmbedding : isEmbedding (Stone↪Set .F-ob)
Stone↪Set-isEmbedding = snd (EmbeddingΣProp λ _ → squash₁)

StoneCatUnivalent : isUnivalent StoneCat
StoneCatUnivalent =
  Cuniv StoneCat (SET ℓ-zero) (isUnivalentSET {ℓ-zero}) Stone↪Set
        Stone↪Set-isEmbedding Stone↪Set-fullyFaithful

module _ (sd : StoneDualityAxiom) where
  isStoneSplitSupport : (S : Type ℓ-zero) → SplitSupport (hasStoneStr S)
  isStoneSplitSupport S = rec (isPropHasStoneStr sd S) (λ p → p)

  -- The decidable subsets of a Stone space form a countably presented algebra.
  -- This is a consequence of duality: untruncating the Stone witness gives a
  -- presenting B with Sp B ≡ ⟨S⟩, and  fst B ≅ 2^(Sp B) ≅ 2^ ⟨S⟩  (SDHomVersion),
  -- so 2^ ⟨S⟩ inherits B's countable presentation.  (The goal is a prop, so we
  -- may rec over the truncation directly.)
  2^isCP : (S : ob (StoneCat ^op)) → is-countably-presented-alt (2^ ⟨ fst S ⟩)
  2^isCP (X , t) =
    rec squash₁
      (λ (B , p) → subst is-countably-presented-alt
        (equivFun (BoolRingPath (fst B) (2^ (Sp B))) (SDHomVersion sd B) ∙ cong 2^ p)
        (snd B))
      t

  -- The "take decidable subsets" functor, corestricted to countably presented
  -- algebras (right adjoint to SpStoneFunctor).  Same data as 2^Functor.
  2^Stone : Functor (StoneCat ^op) BooleωCat
  2^Stone .F-ob S    = 2^ ⟨ fst S ⟩ , 2^isCP S
  2^Stone .F-hom g   = 2^Functor .F-hom g
  2^Stone .F-id      = 2^Functor .F-id
  2^Stone .F-seq f g = 2^Functor .F-seq f g

  -- The adjunction  SpStoneFunctor ⊣ 2^Stone.  The hom-set bijection is the same one
  -- underlying the unrestricted Sp ⊣ 2^ (homs are inherited from BACat / SET),
  -- so this mirrors Sp⊣2^' at the restricted objects.
  SpStoneFunctor⊣2^Stone' : SpStoneFunctor NaturalBijection.⊣ 2^Stone
  SpStoneFunctor⊣2^Stone' .NaturalBijection._⊣_.adjIso {c = B} {d = S} =
    invIso (equivToIso (SpDecAdjunction.adjunction (fst B) ⟨ fst S ⟩))
  SpStoneFunctor⊣2^Stone' .NaturalBijection._⊣_.adjNatInD _ _ = CommRingHom≡ refl
  SpStoneFunctor⊣2^Stone' .NaturalBijection._⊣_.adjNatInC _ _ = funExt λ _ → CommRingHom≡ refl

  -- … in unit–counit form.
  SpStoneFunctor⊣2^Stone : SpStoneFunctor UnitCounit.⊣ 2^Stone
  SpStoneFunctor⊣2^Stone = adj'→adj _ _ SpStoneFunctor⊣2^Stone'

  -- The unit of the adjunction; its components are the evaluation maps.
  unitSpStoneFunctor : 𝟙⟨ BooleωCat ⟩ ⇒ (2^Stone ∘F SpStoneFunctor)
  unitSpStoneFunctor = UnitCounit._⊣_.η SpStoneFunctor⊣2^Stone

  unitIsEvaluation : (B : ob BooleωCat) → NatTrans.N-ob unitSpStoneFunctor B ≡ evaluationHom B
  unitIsEvaluation B = CommRingHom≡ refl

  SpStoneFunctor-fully-faithful : isFullyFaithful SpStoneFunctor
  SpStoneFunctor-fully-faithful = SpFullyFaithful sd

  -- Split essential surjectivity: every Stone space is the spectrum of a
  -- countably presented algebra, uniquely (uniqueness = isPropHasStoneStr).
  SpStoneFunctor-ess-surj :
    (S : ob (StoneCat ^op)) → Σ[ B ∈ Booleω ] CatIso (StoneCat ^op) (SpStoneFunctor ⟅ B ⟆) S
  SpStoneFunctor-ess-surj (X , t) =
    fst bp , pathToIso (Σ≡Prop (λ _ → squash₁) (TypeOfHLevel≡ 2 (snd bp)))
    where
      bp : hasStoneStr ⟨ X ⟩
      bp = isStoneSplitSupport ⟨ X ⟩ t

  -- THE HEADLINE: Sp is an anti-equivalence between countably presented Boolean
  -- algebras and Stone spaces — fully faithful and essentially surjective.
  Sp-is-weak-equivalence : isWeakEquivalence SpStoneFunctor
  Sp-is-weak-equivalence = record
    { fullfaith = SpStoneFunctor-fully-faithful
    ; esssurj   = λ S → ∣ SpStoneFunctor-ess-surj S ∣₁ }

  -- … packaged as an equivalence of categories (both sides are univalent).
  Sp-duality : BooleωCat ≃ᶜ (StoneCat ^op)
  Sp-duality = equivᶜ SpStoneFunctor
    (isWeakEquiv→isEquiv BooleωUnivalent (isUnivalentOp StoneCatUnivalent) Sp-is-weak-equivalence)

  ------------------------------------------------------------------------
  -- The structured adjoint equivalence: the adjunction SpStoneFunctor ⊣ 2^Stone
  -- with unit and counit upgraded to natural isos.
  ------------------------------------------------------------------------
  private
    module AF = adjunctionFact SpStoneFunctor 2^Stone SpStoneFunctor⊣2^Stone

  -- Unit is a natural iso: its components are the evaluation map, which the
  -- axiom makes an iso (ηIsoOnBooleω), lifted from BACat to BooleωCat.
  η-natIso : (B : ob BooleωCat)
           → isIso BooleωCat (NatTrans.N-ob (UnitCounit._⊣_.η SpStoneFunctor⊣2^Stone) B)
  η-natIso B =
    subst (isIso BooleωCat) (sym (unitIsEvaluation B))
      (isIsoΣPropCat* BACat (λ R → is-countably-presented-alt R , squash₁)
        {x = fst B} {y = 2^ (Sp B)} {xp = snd B} {yp = 2^isCP (SpStoneFunctor ⟅ B ⟆)}
        (subst (isIso BACat {x = fst B} {y = 2^ (Sp B)}) (ηBA'Agrees (fst B)) (ηIsoOnBooleω sd B)))

  -- Counit is a natural iso: iso at every SpStoneFunctor B by the triangle
  -- identity (AF.Fpreserves), extended to every Stone space by the split
  -- essential surjectivity.
  ε-natIso : (S : ob (StoneCat ^op))
           → isIso (StoneCat ^op) (NatTrans.N-ob (UnitCounit._⊣_.ε SpStoneFunctor⊣2^Stone) S)
  ε-natIso S =
    subst (λ T → isIso (StoneCat ^op) (NatTrans.N-ob (UnitCounit._⊣_.ε SpStoneFunctor⊣2^Stone) T))
          (invIsEq (isUnivalent.univ (isUnivalentOp StoneCatUnivalent)
                      (SpStoneFunctor ⟅ fst esS ⟆) S) (snd esS))
          (AF.Fpreserves (fst esS) (η-natIso (fst esS)))
    where esS = SpStoneFunctor-ess-surj S

  Sp-anti-equivalence : AdjointEquivalence BooleωCat (StoneCat ^op)
  Sp-anti-equivalence .AdjointEquivalence.fun                 = SpStoneFunctor
  Sp-anti-equivalence .AdjointEquivalence.inv                 = 2^Stone
  Sp-anti-equivalence .AdjointEquivalence.η .NatIso.trans     = UnitCounit._⊣_.η SpStoneFunctor⊣2^Stone
  Sp-anti-equivalence .AdjointEquivalence.η .NatIso.nIso      = η-natIso
  Sp-anti-equivalence .AdjointEquivalence.ε .NatIso.trans     = UnitCounit._⊣_.ε SpStoneFunctor⊣2^Stone
  Sp-anti-equivalence .AdjointEquivalence.ε .NatIso.nIso      = ε-natIso
  Sp-anti-equivalence .AdjointEquivalence.triangleIdentities  = UnitCounit._⊣_.triangleIdentities SpStoneFunctor⊣2^Stone

