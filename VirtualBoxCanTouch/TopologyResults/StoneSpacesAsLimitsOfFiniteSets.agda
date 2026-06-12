{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
--
-- Stone spaces are limits of finite sets; countably presented Boolean algebras are colimits
-- of finite sets.  (Dual statements, via Stone duality.)
--
-- Status (2 holes total, both the genuinely-hard analytic/finiteness steps; everything else is
-- fully proven and axiom-free):
--
--   §1  definitions: "limit of finite sets" (a `Tower` with each `obj n` an `isFinSet`, via
--       `SequentialLimit`) and the dual "colimit of finite sets" (a `Sequence` of finite sets,
--       via `SeqColim`).                                                      [DONE]
--
--   §2  THE KEY ALGEBRAIC FACT: the spectrum of a *presented* Boolean algebra `freeBA A /Im r`
--       is the closed subset of Cantor space `A → Bool` cut out by the relations:
--          Sp (freeBA A /Im r)  ≅  Σ[ α ∈ (A → Bool) ] (∀ x, eval α (r x) ≡ false).      [DONE]
--       (Quotient universal property — a point kills the relations — composed with the free
--       universal property — a hom out of freeBA A is a point of Cantor.)
--
--   §3  • `CantorIsLimitOfFiniteSets` : Cantor space `ℕ → Bool` is a limit of finite sets,
--         via the restriction tower `Fin n → Bool`.                          [DONE, fully proven]
--       • `SpFreeIsLimitOfFiniteSets` : Sp(freeBA ℕ) is a limit of finite sets (the free case,
--         unconditional — Sp(freeBA ℕ) ≅ Cantor).                            [DONE, fully proven]
--       • `SpIsLimitOfFiniteSets` / `…-givenWitness` : for any countably presented B, Sp B is a
--         limit of finite sets — fully REDUCED to the one lemma `ClosedSubsetIsLimitOfFiniteSets`
--         (§2 + transport); filling that single hole closes these with no further work.
--
-- The two remaining holes:
--   • `ClosedSubsetIsLimitOfFiniteSets` (carve the closed subset into finite stages).  The one
--     missing ingredient is a per-relation finite *support*; `r x : ⟨ freeBA ℕ ⟩` lives in an
--     opaque quotient, but COUNTABLE CHOICE lifts `r` to syntactic terms (`includeBATermsSurj`,
--     the `lift-f` pattern of QuotientClosureFromCountableChoice) whose support is computable.
--   • `underlyingIsColimitOfFiniteSets` (the dual: ⟨B⟩ as a colimit of finite sets).  Needs
--     `isFinSet ⟨ freeBA (Fin n) ⟩` (free BA on n generators is finite) — not yet in the library.
module StoneSpacesAsLimitsOfFiniteSets where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (_≃_ ; compEquiv)
open import Cubical.Foundations.HLevels 
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma

open import Cubical.Data.Bool using (Bool ; false ; isSetBool)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.SumFin using (Fin ; finj ; flast ; toℕ ; elim ; fzero ; fsuc)
open import Cubical.Data.FinSet using (isFinSet ; isFinSetFin)
open import Cubical.Data.FinSet.Properties using (isFinSetBool)
open import Cubical.Data.FinSet.Constructors using (isFinSet→)
open import Cubical.Data.Sequence using (Sequence)
open import Cubical.HITs.SequentialColimit using (SeqColim)

open import Cubical.Algebra.CommRing using (_$cr_)
open import Cubical.Algebra.BooleanRing using (BooleanRing ; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)

open import Axioms.DependentChoice using (Tower ; SequentialLimit ; limitPoint)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA ; inducedBAHom ; freeBA-universal-property)
open import BooleanRing.BoolRingUnivalence using (uaBoolRing)
open import BooleanRing.BooleanRingQuotients.QuotientBool using (_/Im_)
open import BooleanRing.BooleanRingQuotients.UniversalProperty using (module MapsOutOfQuotientUniversalProperty)
open import CountablyPresentedBooleanRings.Definitions using (has-quotient-of-freeℕ-presentation ; _is-presented-by_/_)
open import StoneSpaces.Spectrum using (SpGeneralBooleanRing ; Booleω ; Sp)

------------------------------------------------------------------------
-- §1.  Limits / colimits of finite sets.
------------------------------------------------------------------------

-- A `Tower` (obj n, map : obj (suc n) → obj n) all of whose stages are finite sets.
isFiniteTower : Tower ℓ-zero → Type
isFiniteTower T = (n : ℕ) → isFinSet (Tower.obj T n)

-- S is a (sequential) limit of finite sets.
isLimitOfFiniteSets : Type ℓ-zero → Type (ℓ-suc ℓ-zero)
isLimitOfFiniteSets S =
  Σ[ T ∈ Tower ℓ-zero ] (isFiniteTower T) × (S ≃ SequentialLimit T)

-- Dually: a `Sequence` (obj n, map : obj n → obj (suc n)) of finite sets, and its colimit.
isFiniteSequence : Sequence ℓ-zero → Type
isFiniteSequence S = (n : ℕ) → isFinSet (Sequence.obj S n)

isColimitOfFiniteSets : Type ℓ-zero → Type (ℓ-suc ℓ-zero)
isColimitOfFiniteSets S =
  Σ[ Sq ∈ Sequence ℓ-zero ] (isFiniteSequence Sq) × (S ≃ SeqColim Sq)

------------------------------------------------------------------------
-- §2.  The spectrum of a presented Boolean algebra is a closed subset of Cantor space.
--
--   A point of Sp(freeBA A /Im r) is, by the quotient universal property, a hom
--   freeBA A → Bool that kills every relation r x; by the free universal property such a hom
--   is just a function α : A → Bool (a point of Cantor) — and "kills r x" reads off as
--   eval α (r x) ≡ false.
------------------------------------------------------------------------

module SpectrumOfPresentation (A : Type) {X : Type} (r : X → ⟨ freeBA A ⟩) where

  -- evaluation of a Cantor point α : A → Bool on a free element, i.e. the induced hom.
  eval : (A → Bool) → ⟨ freeBA A ⟩ → Bool
  eval α = fst (inducedBAHom A BoolBR α)

  RespectsRelations : (A → Bool) → Type
  RespectsRelations α = (x : X) → eval α (r x) ≡ false

  -- the closed subset of Cantor space A → Bool cut out by the relations.
  ClosedSubsetOfCantor : Type
  ClosedSubsetOfCantor = Σ[ α ∈ (A → Bool) ] RespectsRelations α

  private
    -- reindex the base of the Σ along the free universal property A → Bool ≅ Sp(freeBA A).
    reindex : Iso ClosedSubsetOfCantor
                  (Σ[ g ∈ SpGeneralBooleanRing (freeBA A) ] ((x : X) → g $cr (r x) ≡ false))
    reindex = Σ-cong-iso-fst (freeBA-universal-property A BoolBR)

    -- the quotient universal property: a relation-killing point of freeBA A IS a point of the quotient.
    quotUP : Iso (Σ[ g ∈ SpGeneralBooleanRing (freeBA A) ] ((x : X) → g $cr (r x) ≡ false))
                 (SpGeneralBooleanRing (freeBA A /Im r))
    quotUP = MapsOutOfQuotientUniversalProperty.mapsOutQuotientUniversalProperty (freeBA A) r BoolBR

  -- THE FACT.
  SpAsClosedSubset : Iso (SpGeneralBooleanRing (freeBA A /Im r)) ClosedSubsetOfCantor
  SpAsClosedSubset = invIso (compIso reindex quotUP)

------------------------------------------------------------------------
-- §3.  Transport along equivalences; the Cantor backbone; the main theorems.
------------------------------------------------------------------------

-- "limit/colimit of finite sets" only depends on the type up to equivalence.
isLimitOfFiniteSets-≃ : {S S' : Type ℓ-zero} → S ≃ S'
                      → isLimitOfFiniteSets S' → isLimitOfFiniteSets S
isLimitOfFiniteSets-≃ e (T , fin , e') = T , fin , compEquiv e e'

isColimitOfFiniteSets-≃ : {S S' : Type ℓ-zero} → S ≃ S'
                        → isColimitOfFiniteSets S' → isColimitOfFiniteSets S
isColimitOfFiniteSets-≃ e (Sq , fin , e') = Sq , fin , compEquiv e e'

-- The Cantor tower: stage n is the finite set `Fin n → Bool`, with restriction maps.
FinBoolTower : Tower ℓ-zero
Tower.obj FinBoolTower n = Fin n → Bool
Tower.map FinBoolTower s = s ∘ finj

FinBoolTower-finite : isFiniteTower FinBoolTower
FinBoolTower-finite n = isFinSet→ (Fin n , isFinSetFin) (Bool , isFinSetBool)

-- Cantor space `ℕ → Bool` is a limit of finite sets.
-- The tower, its finiteness, both maps, the retraction, and the *assembly* of the section are
-- all proven; the section is reduced to the single coordinate lemma `coord` — "a point of the
-- inverse limit is determined by its values coordinate-by-coordinate" — which is the one
-- remaining hole (a straightforward but fiddly induction on the tower using `commutes`).
module CantorBackbone where
  open SequentialLimit

  -- `finj` and `flast` preserve / compute the numeric coordinate.
  toℕ-finj : {k : ℕ} (i : Fin k) → toℕ (finj i) ≡ toℕ i
  toℕ-finj = elim (λ i → toℕ (finj i) ≡ toℕ i) refl (λ ih → cong (λ m → ℕ.suc m) ih)

  toℕ-flast : (k : ℕ) → toℕ (flast {k}) ≡ k
  toℕ-flast ℕ.zero    = refl
  toℕ-flast (ℕ.suc k) = cong (λ m → ℕ.suc m) (toℕ-flast k)

  -- every element of Fin (suc n) is either the top `flast` or `finj` of one below.
  decompose : (n : ℕ) (i : Fin (ℕ.suc n))
            → (i ≡ flast {n}) ⊎ (Σ[ j ∈ Fin n ] (i ≡ finj j))
  decompose ℕ.zero    fzero     = inl refl
  decompose (ℕ.suc n) fzero     = inr (fzero , refl)
  decompose (ℕ.suc n) (fsuc x) with decompose n x
  ... | inl x≡flast      = inl (cong fsuc x≡flast)
  ... | inr (j , x≡finj) = inr (fsuc j , cong fsuc x≡finj)

  module Stab (L : SequentialLimit FinBoolTower) where
    -- one-step restriction compatibility, read off `commutes`.
    step : (n : ℕ) (i : Fin n) → branch L (ℕ.suc n) (finj i) ≡ branch L n i
    step n i = funExt⁻ (commutes L n) i

    lastCoord : ℕ → Bool
    lastCoord k = branch L (ℕ.suc k) flast

    -- the value of a limit point at i depends only on `toℕ i`: collapse `finj`s via `step`,
    -- and on the top element read off `flast` directly.
    coord : (n : ℕ) (i : Fin n) → branch L n i ≡ lastCoord (toℕ i)
    coord (ℕ.suc n) i with decompose n i
    ... | inl i≡flast =
          cong (branch L (ℕ.suc n)) i≡flast
        ∙ cong lastCoord (sym (cong toℕ i≡flast ∙ toℕ-flast n))
    ... | inr (j , i≡finj) =
          cong (branch L (ℕ.suc n)) i≡finj
        ∙ step n j
        ∙ coord n j
        ∙ cong lastCoord (sym (cong toℕ i≡finj ∙ toℕ-finj j))

  fwd : (ℕ → Bool) → SequentialLimit FinBoolTower
  fwd α = limitPoint (λ n i → α (toℕ i)) (λ n → funExt (λ i → cong α (toℕ-finj i)))

  bwd : SequentialLimit FinBoolTower → (ℕ → Bool)
  bwd = Stab.lastCoord

  retr : (α : ℕ → Bool) → bwd (fwd α) ≡ α
  retr α = funExt (λ k → cong α (toℕ-flast k))

  sect : (L : SequentialLimit FinBoolTower) → fwd (bwd L) ≡ L
  sect L i = limitPoint (bp i) (cp i)
    where
      bp : branch (fwd (bwd L)) ≡ branch L
      bp = funExt (λ n → funExt (λ i → sym (Stab.coord L n i)))
      cp : PathP (λ i → (n : ℕ) → Tower.map FinBoolTower (bp i (ℕ.suc n)) ≡ bp i n)
                 (commutes (fwd (bwd L))) (commutes L)
      cp = isProp→PathP (λ _ → isPropΠ (λ _ → isSetΠ (λ _ → isSetBool) _ _))
                        (commutes (fwd (bwd L))) (commutes L)

  CantorIso : Iso (ℕ → Bool) (SequentialLimit FinBoolTower)
  CantorIso = iso fwd bwd sect retr

CantorIsLimitOfFiniteSets : isLimitOfFiniteSets (ℕ → Bool)
CantorIsLimitOfFiniteSets = FinBoolTower , FinBoolTower-finite , isoToEquiv CantorBackbone.CantorIso

-- L1 (the carving step).  The closed subset of Cantor cut out by countably many relations is
-- itself a limit of finite sets.
--   PLAN / one genuinely-missing ingredient: a finite *support* (modulus of continuity) for each
--   relation `r x`.  `r x : ⟨ freeBA ℕ ⟩` is an element of an opaque quotient, so its support is
--   not directly readable; but `includeBATermsSurj : freeBATerms ℕ ↠ ⟨ freeBA ℕ ⟩` is (merely)
--   surjective, so by COUNTABLE CHOICE one lifts `r` to terms `t : ℕ → freeBATerms ℕ` with
--   `include (t i) ≡ r i` — exactly the `lift-f` pattern of QuotientClosureFromCountableChoice.
--   A syntactic term has a computable finite support `supp (t i) ⊆ Fin (bound i)`; refine the
--   Cantor tower to
--        obj' n = { s : Fin n → Bool | ∀ i, bound i ≤ n → evalTerm s (t i) ≡ false },
--   a decidable subset of the finite `Fin n → Bool` (hence finite by `isDecProp→isFinSet`), with
--   restriction maps; its SequentialLimit is `ClosedSubsetOfCantor`.
ClosedSubsetIsLimitOfFiniteSets :
  (r : ℕ → ⟨ freeBA ℕ ⟩)
  → isLimitOfFiniteSets (SpectrumOfPresentation.ClosedSubsetOfCantor ℕ r)
ClosedSubsetIsLimitOfFiniteSets r = {!!}

-- THE SPECTRUM THEOREM, given an explicit freeℕ-presentation witness `r`.
-- Fully reduced to L1: §2 identifies Sp with the closed subset, and `isLimitOfFiniteSets-≃`
-- transports.  So filling `ClosedSubsetIsLimitOfFiniteSets` closes this with no further work.
SpIsLimitOfFiniteSets :
  (r : ℕ → ⟨ freeBA ℕ ⟩)
  → isLimitOfFiniteSets (SpGeneralBooleanRing (freeBA ℕ /Im r))
SpIsLimitOfFiniteSets r =
  isLimitOfFiniteSets-≃
    (isoToEquiv (SpectrumOfPresentation.SpAsClosedSubset ℕ r))
    (ClosedSubsetIsLimitOfFiniteSets r)

-- THE FREE CASE is unconditional (no L1 needed): Sp(freeBA ℕ) ≅ Cantor space, which §3 shows is
-- a limit of finite sets.  A complete, end-to-end instance of the theorem.
SpFreeIsLimitOfFiniteSets : isLimitOfFiniteSets (SpGeneralBooleanRing (freeBA ℕ))
SpFreeIsLimitOfFiniteSets =
  isLimitOfFiniteSets-≃
    (isoToEquiv (invIso (freeBA-universal-property ℕ BoolBR)))
    CantorIsLimitOfFiniteSets

-- THE SPECTRUM THEOREM as the user phrased it: "given a witness of B being countably presented,
-- Sp B is a limit of finite sets."  The witness `(r , eC)` gives `B ≡ freeBA ℕ /Im r` by
-- univalence, along which Sp transports; so this too is fully reduced to L1.
SpIsLimitOfFiniteSets-givenWitness :
  (B : BooleanRing ℓ-zero) → has-quotient-of-freeℕ-presentation B
  → isLimitOfFiniteSets (SpGeneralBooleanRing B)
SpIsLimitOfFiniteSets-givenWitness B (r , eC) =
  isLimitOfFiniteSets-≃
    (pathToEquiv (cong SpGeneralBooleanRing (uaBoolRing eC)))
    (SpIsLimitOfFiniteSets r)

-- THE UNDERLYING-SET THEOREM (dual).  The carrier of a countably presented BA is a colimit of
-- finite sets.
--   PLAN: `freeBA ℕ = colim freeBA (Fin n)` (freeBA is a left adjoint, ℕ = colim Fin n), and each
--   `freeBA (Fin n)` is finite (free BA on n generators has 2^(2^n) elements) — NOTE: finiteness
--   of `freeBA (Fin n)` is not yet in the library and is the main missing lemma here.  Then
--   `freeBA ℕ /Im r = colim_n (freeBA (Fin n) / relations available by stage n)`, a colimit of
--   finite BAs; take underlying sets.
underlyingIsColimitOfFiniteSets :
  (r : ℕ → ⟨ freeBA ℕ ⟩)
  → isColimitOfFiniteSets ⟨ freeBA ℕ /Im r ⟩
underlyingIsColimitOfFiniteSets r = {!!}
