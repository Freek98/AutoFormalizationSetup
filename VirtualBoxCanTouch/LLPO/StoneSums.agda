{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- Local copy (kept here for portability; intended upstream home is
-- AntiEquivalence/StoneSums.agda — see LIBRARY_CHANGES.md).  Produced with help
-- from a subagent.  Only the module name differs from the upstream version.
module StoneSums where

-- Sp is a contravariant equivalence (anti-equivalence) Boolean algebras ↔ Stone
-- spaces, and it sends (binary) products of Boolean algebras to (binary) sums
-- (coproducts) of Stone spaces.
--
-- The substantive content is purely algebraic and special to the codomain
-- 2 = BoolBR: a Boolean-algebra map out of a product A ×BR B into the connected
-- algebra 2 (which has no nontrivial idempotents) factors through exactly one
-- projection.  Concretely this is the iso
--
--     Sp (A ×BR B) ≅ Sp A ⊎ Sp B,   Sp X = BoolHom X BoolBR.
--
-- No Stone-duality axiom and no countable-presentation hypothesis are needed
-- for this iso; it holds for *all* Boolean rings A B : BooleanRing ℓ-zero.
-- (The anti-equivalence itself, recorded below, is what `sd` provides; the
-- products↦sums statement at the level of spectra is the `D = BoolBR` instance
-- and is proved directly.)

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_ ; inl ; inr ; ⊎Iso)
open import Cubical.Data.Empty as ⊥ using (⊥)
open import Cubical.Data.Bool
  renaming (_≟_ to _≟B_) hiding (_≤_ ; _≥_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingTheory)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BooleanRing.BooleanRingMaps
open import BooleanRing.ProductBA
open import StoneSpaces.Spectrum

-- The anti-equivalence (contravariant equivalence) Boole ↔ Stone is reused,
-- not reproved, from here.  (The transferred binary products on `StoneCat` live
-- in `AntiEquivalence.Products` as `StoneCat-BinProducts`; we do NOT import that
-- module here only because it currently transitively depends on a module
-- — `CountablyPresentedBooleanRings.ProductClosure` — that fails to typecheck
-- independently of this work.  See the comments in Part 1 below.)
open import Axioms.StoneDuality
  using (StoneDualityAxiom ; SpFullyFaithful ; StoneCat ; SpEmbedding)
open import CategoryTheory.StuffFromStoneAboutBAs using (SpFunctor)

private
  variable
    ℓ ℓ' : Level

-- ════════════════════════════════════════════════════════════════════════════
-- A few Bool facts we need: 2 is "connected" / indecomposable.
-- ════════════════════════════════════════════════════════════════════════════

private
  -- If x ≡ true and x and y ≡ false then y ≡ false.
  killʳ : (x y : Bool) → x ≡ true → x and y ≡ false → y ≡ false
  killʳ x y xp andp = sym (cong (_and y) xp) ∙ andp

  -- If x ≡ false and x ⊕ y ≡ true then y ≡ true.
  recoverʳ : (x y : Bool) → x ≡ false → x ⊕ y ≡ true → y ≡ true
  recoverʳ x y xp xorp = sym (cong (_⊕ y) xp) ∙ xorp

-- ════════════════════════════════════════════════════════════════════════════
-- The product-to-sum iso on spectra, for arbitrary Boolean rings.
-- ════════════════════════════════════════════════════════════════════════════

module _ (A B : BooleanRing ℓ-zero) where
  private
    module A = BooleanRingStr (snd A)
    module B = BooleanRingStr (snd B)
    module P = BooleanRingStr (snd (A ×BR B))

    AB : BooleanRing ℓ-zero
    AB = A ×BR B

    -- Annihilator lemmas in each factor.
    0RA : (x : ⟨ A ⟩) → x A.· A.𝟘 ≡ A.𝟘
    0RA = RingTheory.0RightAnnihilates (CommRing→Ring (BooleanRing→CommRing A))
    0LA : (x : ⟨ A ⟩) → A.𝟘 A.· x ≡ A.𝟘
    0LA = RingTheory.0LeftAnnihilates (CommRing→Ring (BooleanRing→CommRing A))
    0RB : (x : ⟨ B ⟩) → x B.· B.𝟘 ≡ B.𝟘
    0RB = RingTheory.0RightAnnihilates (CommRing→Ring (BooleanRing→CommRing B))
    0LB : (x : ⟨ B ⟩) → B.𝟘 B.· x ≡ B.𝟘
    0LB = RingTheory.0LeftAnnihilates (CommRing→Ring (BooleanRing→CommRing B))

    -- The complementary idempotents (𝟙_A,𝟘_B) and (𝟘_A,𝟙_B).
    e  : ⟨ AB ⟩
    e  = A.𝟙 , B.𝟘
    e' : ⟨ AB ⟩
    e' = A.𝟘 , B.𝟙

    -- Restriction of a map on the product to the first / second factor.
    rA : BoolHom AB BoolBR → ⟨ A ⟩ → Bool
    rA φ a = φ $cr (a , B.𝟘)
    rB : BoolHom AB BoolBR → ⟨ B ⟩ → Bool
    rB φ b = φ $cr (A.𝟘 , b)

    -- Componentwise sums/products in the product ring are definitional; the only
    -- non-definitional facts are 𝟘+𝟘≡𝟘 etc. in each factor, supplied here.
    open IsCommRingHom

    -- ── rA φ is a hom when φ e ≡ true ───────────────────────────────────────
    homA : (φ : BoolHom AB BoolBR) → φ $cr e ≡ true → BoolHom A BoolBR
    homA φ etrue .fst = rA φ
    homA φ etrue .snd = makeIsCommRingHom
      etrue
      (λ a a' →
        cong (φ .fst) (ΣPathP (refl , sym (B.+IdR B.𝟘)))
        ∙ φ .snd .pres+ (a , B.𝟘) (a' , B.𝟘))
      (λ a a' →
        cong (φ .fst) (ΣPathP (refl , sym (0LB B.𝟘)))
        ∙ φ .snd .pres· (a , B.𝟘) (a' , B.𝟘))

    -- ── rB φ is a hom when φ e ≡ false (so φ e' ≡ true) ──────────────────────
    homB : (φ : BoolHom AB BoolBR) → rB φ B.𝟙 ≡ true → BoolHom B BoolBR
    homB φ e'true .fst = rB φ
    homB φ e'true .snd = makeIsCommRingHom
      e'true
      (λ b b' →
        cong (φ .fst) (ΣPathP (sym (A.+IdR A.𝟘) , refl))
        ∙ φ .snd .pres+ (A.𝟘 , b) (A.𝟘 , b'))
      (λ b b' →
        cong (φ .fst) (ΣPathP (sym (0LA A.𝟘) , refl))
        ∙ φ .snd .pres· (A.𝟘 , b) (A.𝟘 , b'))

    -- ── Basic algebraic facts about φ relative to the idempotents e, e' ─────
    -- φ e and φ e' ≡ false   (because e · e' = 𝟘)
    e·e'≡0 : e P.· e' ≡ P.𝟘
    e·e'≡0 = ΣPathP (0RA A.𝟙 , 0LB B.𝟙)

    -- e + e' ≡ 𝟙
    e+e'≡1 : e P.+ e' ≡ P.𝟙
    e+e'≡1 = ΣPathP (A.+IdR A.𝟙 , B.+IdL B.𝟙)

    φe-and-φe' : (φ : BoolHom AB BoolBR) → (φ $cr e) and (φ $cr e') ≡ false
    φe-and-φe' φ = sym (φ .snd .pres· e e') ∙ cong (φ .fst) e·e'≡0 ∙ φ .snd .pres0

    φe-xor-φe' : (φ : BoolHom AB BoolBR) → (φ $cr e) ⊕ (φ $cr e') ≡ true
    φe-xor-φe' φ = sym (φ .snd .pres+ e e') ∙ cong (φ .fst) e+e'≡1 ∙ φ .snd .pres1

    -- rB φ B.𝟙 is exactly φ e'
    rBe' : (φ : BoolHom AB BoolBR) → rB φ B.𝟙 ≡ φ $cr e'
    rBe' φ = refl

    -- ── The forward map, via the contractible singleton of (φ e) ────────────
    -- We branch on the value of φ e; in the `false` branch we use that then
    -- φ e' ≡ true.
    funAux : (φ : BoolHom AB BoolBR) → Σ[ b ∈ Bool ] (φ $cr e ≡ b)
      → SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
    funAux φ (true  , etrue)  = inl (homA φ etrue)
    funAux φ (false , efalse) = inr (homB φ (recoverʳ (φ $cr e) (φ $cr e') efalse (φe-xor-φe' φ)))

    fwd : BoolHom AB BoolBR → SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
    fwd φ = funAux φ (φ $cr e , refl)

    -- ── The inverse map ─────────────────────────────────────────────────────
    bwd : SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B → BoolHom AB BoolBR
    bwd (inl ψ) = ψ ∘cr BRProduct.πB A B
    bwd (inr χ) = χ ∘cr BRProduct.πC A B

    -- ── Decomposition of φ along the two factors ────────────────────────────
    -- (a , b) ≡ (a , 𝟘) + (𝟘 , b) in the product
    pair-split : (a : ⟨ A ⟩) (b : ⟨ B ⟩) → (a , b) ≡ ((a , B.𝟘) P.+ (A.𝟘 , b))
    pair-split a b = ΣPathP (sym (A.+IdR a) , sym (B.+IdL b))

    φ-split : (φ : BoolHom AB BoolBR) (a : ⟨ A ⟩) (b : ⟨ B ⟩)
      → φ $cr (a , b) ≡ (φ $cr (a , B.𝟘)) ⊕ (φ $cr (A.𝟘 , b))
    φ-split φ a b = cong (φ .fst) (pair-split a b)
      ∙ φ .snd .pres+ (a , B.𝟘) (A.𝟘 , b)

    -- e · (𝟘 , b) = 𝟘, hence φe and φ(𝟘,b) = false
    e·rB≡0 : (b : ⟨ B ⟩) → e P.· (A.𝟘 , b) ≡ P.𝟘
    e·rB≡0 b = ΣPathP (0RA A.𝟙 , 0LB b)

    -- e' · (a , 𝟘) = 𝟘, hence φe' and φ(a,𝟘) = false
    e'·rA≡0 : (a : ⟨ A ⟩) → e' P.· (a , B.𝟘) ≡ P.𝟘
    e'·rA≡0 a = ΣPathP (0LA a , 0RB B.𝟙)

    -- φ(𝟘,b) ≡ false when φ e ≡ true
    rB≡false : (φ : BoolHom AB BoolBR) → φ $cr e ≡ true → (b : ⟨ B ⟩)
      → φ $cr (A.𝟘 , b) ≡ false
    rB≡false φ etrue b = killʳ (φ $cr e) (φ $cr (A.𝟘 , b)) etrue
      (sym (φ .snd .pres· e (A.𝟘 , b)) ∙ cong (φ .fst) (e·rB≡0 b) ∙ φ .snd .pres0)

    -- φ(a,𝟘) ≡ false when φ e' ≡ true (equivalently φ e ≡ false)
    rA≡false : (φ : BoolHom AB BoolBR) → φ $cr e' ≡ true → (a : ⟨ A ⟩)
      → φ $cr (a , B.𝟘) ≡ false
    rA≡false φ e'true a = killʳ (φ $cr e') (φ $cr (a , B.𝟘)) e'true
      (sym (φ .snd .pres· e' (a , B.𝟘)) ∙ cong (φ .fst) (e'·rA≡0 a) ∙ φ .snd .pres0)

    -- ── Retraction: bwd ∘ fwd ≡ id ──────────────────────────────────────────
    retAux : (φ : BoolHom AB BoolBR) (s : Σ[ b ∈ Bool ] (φ $cr e ≡ b))
      → bwd (funAux φ s) ≡ φ
    retAux φ (true , etrue) = CommRingHom≡ (funExt λ (a , b) →
      -- underlying of bwd (inl (homA φ etrue)) at (a,b) is φ(a,𝟘)
      sym (φ-split φ a b
        ∙ cong ((φ $cr (a , B.𝟘)) ⊕_) (rB≡false φ etrue b)
        ∙ ⊕-identityʳ (φ $cr (a , B.𝟘))))
    retAux φ (false , efalse) = CommRingHom≡ (funExt λ (a , b) →
      -- underlying of bwd (inr (homB φ _)) at (a,b) is φ(𝟘,b)
      sym (φ-split φ a b
        ∙ cong (_⊕ (φ $cr (A.𝟘 , b))) (rA≡false φ e'true a)))
      where
        e'true : φ $cr e' ≡ true
        e'true = recoverʳ (φ $cr e) (φ $cr e') efalse (φe-xor-φe' φ)

    ret : (φ : BoolHom AB BoolBR) → bwd (fwd φ) ≡ φ
    ret φ = retAux φ (φ $cr e , refl)

    -- ── Section: fwd ∘ bwd ≡ id ─────────────────────────────────────────────
    -- For inl ψ: bwd (inl ψ) = ψ ∘cr πB, whose value at e is ψ 𝟙_A = true.
    secInl : (ψ : SpGeneralBooleanRing A) → fwd (bwd (inl ψ)) ≡ inl ψ
    secInl ψ =
      cong (funAux (bwd (inl ψ)))
        (isContr→isProp (isContrSingl (bwd (inl ψ) $cr e))
          (bwd (inl ψ) $cr e , refl) (true , ψe≡true))
      ∙ cong inl (CommRingHom≡ refl)
      where
        ψe≡true : bwd (inl ψ) $cr e ≡ true
        ψe≡true = ψ .snd .pres1

    secInr : (χ : SpGeneralBooleanRing B) → fwd (bwd (inr χ)) ≡ inr χ
    secInr χ =
      cong (funAux (bwd (inr χ)))
        (isContr→isProp (isContrSingl (bwd (inr χ) $cr e))
          (bwd (inr χ) $cr e , refl) (false , χe≡false))
      ∙ cong inr (CommRingHom≡ refl)
      where
        χe≡false : bwd (inr χ) $cr e ≡ false
        χe≡false = χ .snd .pres0

    sec : (s : SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B) → fwd (bwd s) ≡ s
    sec (inl ψ) = secInl ψ
    sec (inr χ) = secInr χ

  -- ── The iso ───────────────────────────────────────────────────────────────
  SpProd≅SpSumGeneral :
    Iso (SpGeneralBooleanRing (A ×BR B))
        (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
  SpProd≅SpSumGeneral .Iso.fun = fwd
  SpProd≅SpSumGeneral .Iso.inv = bwd
  SpProd≅SpSumGeneral .Iso.sec = sec
  SpProd≅SpSumGeneral .Iso.ret = ret

-- ════════════════════════════════════════════════════════════════════════════
-- Packaged statements.
-- ════════════════════════════════════════════════════════════════════════════

-- The iso exactly in the shape needed downstream (for arbitrary Boolean rings;
-- no Stone-duality axiom or countable-presentation hypothesis is required).
SpProd≅SpSum : (A B : BooleanRing ℓ-zero)
  → Iso (SpGeneralBooleanRing (A ×BR B))
        (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
SpProd≅SpSum = SpProd≅SpSumGeneral

-- The Booleω-indexed version, for callers working with countably presented
-- Boolean algebras.  (`fst A ×BR fst B` is the carrier-level product.)
SpProd≅SpSumω : (A B : Booleω)
  → Iso (SpGeneralBooleanRing (fst A ×BR fst B))
        (SpGeneralBooleanRing (fst A) ⊎ SpGeneralBooleanRing (fst B))
SpProd≅SpSumω A B = SpProd≅SpSumGeneral (fst A) (fst B)

-- ════════════════════════════════════════════════════════════════════════════
-- Part 1: Sp as an anti-equivalence Boole ↔ Stone, and the products↦sums slogan.
-- ════════════════════════════════════════════════════════════════════════════
--
-- Given the Stone-duality axiom `sd`, `Sp` is a contravariant equivalence:
--
--   * `SpFunctor : Functor Booleω StoneCat` is fully faithful (`SpFullyFaithful
--     sd`) and `StoneCat` is by definition its image (so it is essentially
--     surjective); `SpEmbedding sd` records that `Sp` is an embedding on
--     underlying types.  This is exactly the anti-equivalence of categories
--     between (countably presented) Boolean algebras and Stone spaces.
--
--   * `Booleω` has binary products: their object part is `×BR-Booleω` (the
--     `_×BR_` of Boolean algebras, closed under countable presentation).  Via
--     the fully faithful `SpFunctor`, this product structure transfers to
--     `StoneCat-BinProducts sd : BinProducts StoneCat`, which is *already
--     proved* in `AntiEquivalence.Products`.  Because `Sp` is *contravariant*,
--     a product in `Booleω` is a *coproduct* (sum) in the Stone world.
--     (We deliberately do not re-export `StoneCat-BinProducts` from this module,
--     to keep `AntiEquivalence.StoneSums` free of the currently-broken
--     `CountablyPresentedBooleanRings.ProductClosure` dependency.)
--
-- The concrete computation of those Stone sums at the level of underlying types
-- is `SpProd≅SpSum`: the underlying type of `Sp (A ×BR B)` is the disjoint
-- union `Sp A ⊎ Sp B`.  This is the special-to-`BoolBR` instance of "maps out
-- of a product = sum of maps", and (unlike the general-`D` version, which is
-- false for rings) it holds because `2 = BoolBR` is connected.
--
-- Sp is fully faithful (the anti-equivalence on morphisms), for the record.
Sp-anti-equivalence-ff : (sd : StoneDualityAxiom) → _
Sp-anti-equivalence-ff sd = SpFullyFaithful sd

-- Sp is an embedding on underlying types (anti-equivalence on objects), for the
-- record.
Sp-anti-equivalence-embedding : (sd : StoneDualityAxiom) → _
Sp-anti-equivalence-embedding sd = SpEmbedding sd
