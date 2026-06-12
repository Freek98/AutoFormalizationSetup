{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
--
-- PREP / scaffolding for the characterisation of overtly discrete types.
--
-- Target equivalences (all for `X : Type` at ℓ-zero, where "open" lives):
--
--   isOvertlyDiscrete X   ⟺   isOpenQuotientOfCountable X   ⟺   isColimitOfFiniteSets X
--        (ODisc)                  ("countable / open")            (StoneSpacesAsLimitsOfFiniteSets)
--
-- Plan (Coquand's):
--   • a type is a sequential colimit of finite sets  ⟺  it is a quotient of a countable set by an
--     open (equivalence) relation;                                            [E1, the hard one]
--   • ODisc  ⟺  quotient of countable by open relation;                       [E2, asked for here]
--   • countably presented Boolean algebras are of this form (free terms are countable; the ring /
--     idempotent / boolean equalities are countably many ⇒ the relation is open), hence free BAs
--     are overtly discrete; countably presented BAs are open quotients of the free ones.
--
-- This file fixes the DEFINITIONS (no holes) and STATES the equivalences (holes), with the proof
-- strategy at each.  Some ingredients already exist: `OvertlyDiscrete.SeqColim`'s encode–decode
-- shows equality in a finite-sequence colimit is open (`isOpenEqInX∞`, in the finished variant),
-- which is the colimit ⇒ open-equality half.
module OvertlyDiscreteCharacterization where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩ ; str)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.HLevels using (hProp ; isSetHProp ; isPropΠ ; isPropΣ ; isPropIsSet ; isProp×)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)
open import Cubical.HITs.SetQuotients as SQ using (_/_ ; [_] ; eq/ ; squash/ ; effective ; elimProp2)
open import Cubical.Relation.Binary using (module BinaryRelation)
open BinaryRelation using (isEquivRel ; isPropValued)

open import BasicDefinitions using (is-countable)
open import PropositionalTopology.Definitions using (isOpenProp ; isOpenWitness ; Open)
open import PropositionalTopology.Properties using (isPropIsOpenProp)

open import StoneSpacesAsLimitsOfFiniteSets using (isColimitOfFiniteSets)

private variable X : Type

------------------------------------------------------------------------
-- Open relations and the quotient of a countable set by one.
------------------------------------------------------------------------

-- A (prop-valued) relation is open when each `R c c'` is an open proposition.
isOpenRel : {C : Type} → (C → C → hProp ℓ-zero) → Type
isOpenRel {C} R = (c c' : C) → isOpenProp (R c c')

-- An open equivalence relation: prop-valued (built in via `hProp`), open, and an equivalence.
record OpenEquivRel (C : Type) : Type₁ where
  field
    rel    : C → C → hProp ℓ-zero
    relOpen : isOpenRel rel
    relEqv  : isEquivRel (λ c c' → ⟨ rel c c' ⟩)

  Rel : C → C → Type
  Rel c c' = ⟨ rel c c' ⟩

  relProp : isPropValued Rel
  relProp c c' = str (rel c c')

  quotient : Type
  quotient = C / Rel

-- "countable / open": X is (merely) a quotient of a countable set by an open equivalence relation.
OpenQuotientPresentation : Type → Type₁
OpenQuotientPresentation X =
  Σ[ C ∈ Type ] is-countable C × (Σ[ R ∈ OpenEquivRel C ] (X ≃ OpenEquivRel.quotient R))

isOpenQuotientOfCountable : Type → Type₁
isOpenQuotientOfCountable X = ∥ OpenQuotientPresentation X ∥₁

------------------------------------------------------------------------
-- Overtly discrete (intrinsic): an overt set with open equality.
--   NB design choice to confirm: "overt" = (merely) covered by ℕ.  This is what is needed for the
--   open-quotient form (the cover gives the countable C); a subcountable hypothesis would be too
--   weak (a quotient of ℕ need not embed back into ℕ).
------------------------------------------------------------------------

-- equality of a set is, pointwise, an open proposition.
hasOpenEquality : (X : Type) → isSet X → Type
hasOpenEquality X setX = (x y : X) → isOpenProp ((x ≡ y) , setX x y)

-- overt: merely covered by a map out of ℕ.
isOvert : Type → Type
isOvert X = ∥ Σ[ s ∈ (ℕ → X) ] isSurjection s ∥₁

isOvertlyDiscrete : Type → Type
isOvertlyDiscrete X = Σ[ setX ∈ isSet X ] (isOvert X × hasOpenEquality X setX)

-- ODisc is a proposition — so the characterisation proofs may `PT.rec` a presentation into it.
isPropIsOvertlyDiscrete : (X : Type) → isProp (isOvertlyDiscrete X)
isPropIsOvertlyDiscrete X =
  isPropΣ isPropIsSet
    (λ setX → isProp× PT.isPropPropTrunc (isPropΠ (λ _ → isPropΠ (λ _ → isPropIsOpenProp))))

------------------------------------------------------------------------
-- Bridging lemma: a quotient by an open equivalence relation has open equality.
--   `[a] ≡ [b]  ≃  Rel a b` by effectiveness (`isEquivRel→effectiveIso`), and `Rel` is open; lift
--   from classes to arbitrary quotient elements with `SQ.elimProp` (isOpenProp is a prop).
------------------------------------------------------------------------

-- open-ness only depends on a proposition up to logical equivalence.
isOpenProp-↔ : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩)
             → isOpenProp P → isOpenProp Q
isOpenProp-↔ P Q P→Q Q→P =
  PT.map (λ { (α , P→α , α→P) → α , (λ q → P→α (Q→P q)) , (λ s → P→Q (α→P s)) })

openQuotientHasOpenEquality : {C : Type} (R : OpenEquivRel C)
  → hasOpenEquality (OpenEquivRel.quotient R) squash/
openQuotientHasOpenEquality {C} R = elimProp2 (λ _ _ → isPropIsOpenProp) goal
  where
    open OpenEquivRel R
    goal : (a b : C) → isOpenProp (([ a ] ≡ [ b ]) , squash/ _ _)
    goal a b = isOpenProp-↔ (rel a b) (([ a ] ≡ [ b ]) , squash/ _ _)
                 (eq/ a b) (effective relProp relEqv a b) (relOpen a b)

------------------------------------------------------------------------
-- E2 — THE EQUIVALENCE ASKED FOR: ODisc ⟺ countable/open.
------------------------------------------------------------------------

-- ⇐ : a quotient of a countable set by an open equiv. relation is overtly discrete.
--     overt: `[_] : C ↠ quotient` composed with a cover `ℕ ↠ C` (C countable); open equality is
--     `openQuotientHasOpenEquality`.
openQuotientOfCountable→ODisc : (X : Type) → isOpenQuotientOfCountable X → isOvertlyDiscrete X
openQuotientOfCountable→ODisc X = {!!}

-- ⇒ : an overtly discrete X is a quotient of ℕ by the open relation `kernel s` of any cover.
--     take C = ℕ, R a b = (s a ≡ s b) [open since X has open equality]; X ≃ ℕ / R because s is a
--     surjection (image factorisation / `s` effective).
ODisc→openQuotientOfCountable : (X : Type) → isOvertlyDiscrete X → isOpenQuotientOfCountable X
ODisc→openQuotientOfCountable X = {!!}

------------------------------------------------------------------------
-- E1 — the hard equivalence: colimit of finite sets ⟺ countable/open.
------------------------------------------------------------------------

colimitOfFiniteSets→openQuotient : (X : Type)
  → isColimitOfFiniteSets X → isOpenQuotientOfCountable X
colimitOfFiniteSets→openQuotient X = {!!}

openQuotient→colimitOfFiniteSets : (X : Type)
  → isOpenQuotientOfCountable X → isColimitOfFiniteSets X
openQuotient→colimitOfFiniteSets X = {!!}
