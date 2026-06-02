{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- as far as I (Freek) can see, this file is not this categorical approach I suggested, it should somewhere state a fact that an antiequivalence sends products to sums, and that sums of Stone are exactly the ⊎ sums. 
-- A categorical account of:
--
--   "Boolean algebras have binary products, therefore Stone spaces have binary
--    sums (coproducts)."
--
-- The conceptual statement.
--
--   `Sp` is a *contravariant* equivalence (an anti-equivalence) between
--   countably-presented Boolean algebras and Stone spaces.  In this library this
--   is witnessed by
--
--       SpFunctor : Functor BooleωCat (SET ^op)
--
--   which is fully faithful (`SpFullyFaithful sd`, given the Stone-duality
--   axiom `sd`) and essentially surjective onto its image; and `StoneCat` is by
--   definition that image:
--
--       StoneCat = ImageFunctor.Image SpFunctor.
--
--   Because the codomain is `SET ^op`, the homs of `StoneCat` run *backwards*
--   relative to the underlying spaces:
--
--       StoneCat [ X , Y ]  =  (SET ^op) [ Sp X , Sp Y ]  =  (Sp Y → Sp X).
--
--   So `StoneCat` is really `Stone ^op`: the honest, geometric category of Stone
--   spaces (with continuous maps `Sp X → Sp Y` as morphisms) is `StoneCat ^op`.
--   The anti-equivalence the task speaks of is `Booleω ≃ Stone ^op`, i.e. exactly
--   `SpFunctor : Booleω → StoneCat`.
--
-- The mechanism.
--
--   Sums are products in the opposite category.  `Booleω` has binary products
--   (object part `_×BR_`, the product of Boolean algebras), and via the fully
--   faithful contravariant `SpFunctor` these become binary products of
--   `StoneCat` (this is `AntiEquivalence.Products.StoneCat-BinProducts`).  A
--   binary product of `StoneCat` is, definitionally up to the record swap, a
--   binary *coproduct* of `StoneCat ^op` — i.e. a binary sum of honest Stone
--   spaces.  Concretely the coproduct of `Sp A` and `Sp B` is `Sp (A ×BR B)`,
--   with injections `Sp πB` and `Sp πC` coming from the two product projections.
--
-- What is proved here.
--
--   We expose `StoneCat` as a first-class object, and we produce
--
--       Stone-BinCoproducts : (sd : StoneDualityAxiom)
--         → (closed : ClosedUnderProductsBR)
--         → BinCoproducts (StoneCat ^op)
--
--   the coproduct object of `X` and `Y` being `Sp (X ×BR Y)`, derived from the
--   product structure of `Booleω` transported through `SpFullyFaithful sd`, and
--   dualised.  We rebuild the product-transfer plumbing locally rather than
--   importing `AntiEquivalence.Products`, because that module currently fails to
--   typecheck on a clean checkout: it transitively imports
--   `CountablyPresentedBooleanRings.ProductClosure`, which is broken at line 382
--   (`Not in scope: QB.quotientRec`).  See the note at the end of this file.

module CategoricalSumsProducts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_ ; inl ; inr)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import Cubical.Categories.Category.Base
open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Constructions.Opposite
open import Cubical.Categories.Limits.BinProduct
open import Cubical.Categories.Limits.BinCoproduct

open import CategoryTheory.StuffFromStoneAboutBAs using (SpFunctor ; BooleωCat)
open import BooleanRing.BooleanRingMaps
-- NB: was `BooleanRing.Products`, which is not in the library's git version.
-- Using the local `ProductBAProjections` shim over git's `BooleanRing.ProductBA`
-- keeps this folder portable (and matches the `_×BR_` used by StoneSums / the
-- main LLPO file).  See LIBRARY_CHANGES.md.
open import ProductBAProjections
  using (_×BR_ ; pr₁-BR ; pr₂-BR ; ⟨_,_⟩BR ; ⟨,⟩BR-pr₁ ; ⟨,⟩BR-pr₂ ; ⟨,⟩BR-unique)
open import StoneSpaces.Spectrum using (Sp ; SpGeneralBooleanRing ; Booleω)
open import CountablyPresentedBooleanRings.Definitions using (is-countably-presented-alt)
open import Axioms.StoneDuality using (StoneDualityAxiom ; SpFullyFaithful ; StoneCat)

-- Also re-exported for contrast: the type-level computation of the Stone sum.
open import StoneSums using (SpProd≅SpSum)

open Functor

-- ════════════════════════════════════════════════════════════════════════════
-- Part 0.  StoneCat, an sich.
-- ════════════════════════════════════════════════════════════════════════════
--
-- `StoneCat` (= the image of the contravariant `SpFunctor`) is the category we
-- call `Stone ^op`.  We expose it, and the geometric category of Stone spaces
-- `Stone = StoneCat ^op`, as first-class objects, together with names for their
-- objects and homs so that downstream code can talk about "the category Stone an
-- sich".

-- The category appearing as the codomain image of `Sp`.  Its objects are the
-- countably-presented Boolean algebras `Booleω`, and
--   StoneCat [ X , Y ] = (Sp Y → Sp X).
Stone^op : Category (ℓ-suc ℓ-zero) ℓ-zero
Stone^op = StoneCat

-- The honest, geometric category of Stone spaces: morphisms are the continuous
-- maps `Sp X → Sp Y`.  This is the category that has the binary *sums*.
StoneCategory : Category (ℓ-suc ℓ-zero) ℓ-zero
StoneCategory = StoneCat ^op

-- Objects of the Stone category are (representations of) Stone spaces, i.e. the
-- countably-presented Boolean algebras `X` standing for the space `Sp X`.
StoneOb : Type (ℓ-suc ℓ-zero)
StoneOb = StoneCategory .Category.ob

-- A morphism `X → Y` of Stone spaces is exactly a function `Sp X → Sp Y`.
StoneHom : StoneOb → StoneOb → Type ℓ-zero
StoneHom X Y = StoneCategory .Category.Hom[_,_] X Y

-- ════════════════════════════════════════════════════════════════════════════
-- Part 1.  Closure of `Booleω` under binary products.
-- ════════════════════════════════════════════════════════════════════════════
--
-- To even form the product/coproduct *object* inside `StoneCat` (whose objects
-- are `Booleω`) we must know that `A ×BR B` is again countably presented.  This
-- is precisely the content of `CountablyPresentedBooleanRings.ProductClosure`'s
-- `Booleω-closed-×BR`, which is currently unavailable (that module does not
-- typecheck on a clean checkout, see the header).  Rather than depend on it, we
-- take the closure as an explicit hypothesis with exactly its type.  Once the
-- library module is fixed, `Booleω-closed-×BR` discharges this hypothesis.

ClosedUnderProductsBR : Type (ℓ-suc ℓ-zero)
ClosedUnderProductsBR = (X Y : Booleω) → is-countably-presented-alt (fst X ×BR fst Y)

module _ (closed : ClosedUnderProductsBR) where
  -- The product Boolean algebra, packaged back into `Booleω`.
  ×BR-Booleω : Booleω → Booleω → Booleω
  ×BR-Booleω X Y = (fst X ×BR fst Y) , closed X Y

-- ════════════════════════════════════════════════════════════════════════════
-- Part 2.  Transporting products of Booleω to products of StoneCat
--          ( = coproducts of Stone), via the fully faithful Sp.
-- ════════════════════════════════════════════════════════════════════════════
--
-- This rebuilds, locally, the existence+uniqueness plumbing of
-- `AntiEquivalence.Products` (which we cannot import), and then reads it off as
-- a binary product of `StoneCat`.  Recall `StoneCat .ob = Booleω` and
-- `StoneCat [ X , Y ] = SpFunctor.F-hom`-image.

module _ (sd : StoneDualityAxiom) (closed : ClosedUnderProductsBR) where
  private
    module S = Category StoneCat
    ff : isFullyFaithful SpFunctor
    ff = SpFullyFaithful sd

    -- Sp is injective on homs (faithfulness extracted from full-faithfulness).
    Sp-inj : {A B : Booleω} {f g : BoolHom (fst A) (fst B)} →
      SpFunctor .F-hom f ≡ SpFunctor .F-hom g → f ≡ g
    Sp-inj {A} {B} {f} {g} p =
      sym (retIsEq (ff A B) f) ∙ cong (invIsEq (ff A B)) p ∙ retIsEq (ff A B) g

    -- ── Existence of the mediating morphism for a cone (f₁ : Z→X, f₂ : Z→Y).
    exists : (X Y Z : Booleω)
      (f₁ : S.Hom[_,_] Z X)
      (f₂ : S.Hom[_,_] Z Y) →
      Σ _ (λ h → (S._⋆_ h (SpFunctor .F-hom (pr₁-BR (fst X) (fst Y))) ≡ f₁)
               × (S._⋆_ h (SpFunctor .F-hom (pr₂-BR (fst X) (fst Y))) ≡ f₂))
    exists X Y Z f₁ f₂ = SpFunctor .F-hom h , pr₁-ok , pr₂-ok
      where
        f₁' : BoolHom (fst Z) (fst X)
        f₁' = invIsEq (ff Z X) f₁
        f₂' : BoolHom (fst Z) (fst Y)
        f₂' = invIsEq (ff Z Y) f₂
        h : BoolHom (fst Z) (fst X ×BR fst Y)
        h = ⟨ fst X , fst Y ⟩BR f₁' f₂'
        pr₁-ok : S._⋆_ (SpFunctor .F-hom h) (SpFunctor .F-hom (pr₁-BR (fst X) (fst Y))) ≡ f₁
        pr₁-ok = sym (SpFunctor .F-seq h (pr₁-BR (fst X) (fst Y)))
                 ∙ cong (SpFunctor .F-hom) (⟨,⟩BR-pr₁ (fst X) (fst Y) (fst Z) f₁' f₂')
                 ∙ secIsEq (ff Z X) f₁
        pr₂-ok : S._⋆_ (SpFunctor .F-hom h) (SpFunctor .F-hom (pr₂-BR (fst X) (fst Y))) ≡ f₂
        pr₂-ok = sym (SpFunctor .F-seq h (pr₂-BR (fst X) (fst Y)))
                 ∙ cong (SpFunctor .F-hom) (⟨,⟩BR-pr₂ (fst X) (fst Y) (fst Z) f₁' f₂')
                 ∙ secIsEq (ff Z Y) f₂

    -- ── Uniqueness of the mediating morphism.
    unique : (X Y Z : Booleω)
      (f₁ : S.Hom[_,_] Z X)
      (f₂ : S.Hom[_,_] Z Y)
      (other : Σ _ (λ k → (S._⋆_ k (SpFunctor .F-hom (pr₁-BR (fst X) (fst Y))) ≡ f₁)
                         × (S._⋆_ k (SpFunctor .F-hom (pr₂-BR (fst X) (fst Y))) ≡ f₂))) →
      exists X Y Z f₁ f₂ ≡ other
    unique X Y Z f₁ f₂ (k , kpr₁ , kpr₂) =
      Σ≡Prop (λ m → isProp× (S.isSetHom _ _) (S.isSetHom _ _))
        (cong (SpFunctor .F-hom) (sym k-lift≡h) ∙ k-eq)
      where
        f₁' : BoolHom (fst Z) (fst X)
        f₁' = invIsEq (ff Z X) f₁
        f₂' : BoolHom (fst Z) (fst Y)
        f₂' = invIsEq (ff Z Y) f₂
        h : BoolHom (fst Z) (fst X ×BR fst Y)
        h = ⟨ fst X , fst Y ⟩BR f₁' f₂'
        XY : Booleω
        XY = ×BR-Booleω closed X Y
        k-lift : BoolHom (fst Z) (fst XY)
        k-lift = invIsEq (ff Z XY) k
        k-eq : SpFunctor .F-hom k-lift ≡ k
        k-eq = secIsEq (ff Z XY) k

        k-pr₁-lift : pr₁-BR (fst X) (fst Y) ∘cr k-lift ≡ f₁'
        k-pr₁-lift = Sp-inj
          (SpFunctor .F-seq k-lift (pr₁-BR (fst X) (fst Y))
           ∙ cong (λ m → S._⋆_ m _) k-eq
           ∙ kpr₁ ∙ sym (secIsEq (ff Z X) f₁))

        k-pr₂-lift : pr₂-BR (fst X) (fst Y) ∘cr k-lift ≡ f₂'
        k-pr₂-lift = Sp-inj
          (SpFunctor .F-seq k-lift (pr₂-BR (fst X) (fst Y))
           ∙ cong (λ m → S._⋆_ m _) k-eq
           ∙ kpr₂ ∙ sym (secIsEq (ff Z Y) f₂))

        k-lift≡h : k-lift ≡ h
        k-lift≡h = ⟨,⟩BR-unique (fst X) (fst Y) (fst Z) f₁' f₂'
                     k-lift k-pr₁-lift k-pr₂-lift

  -- ── StoneCat has binary products (the dual of which is the coproduct below).
  StoneCat-BinProduct : (X Y : Booleω) → BinProduct StoneCat X Y
  StoneCat-BinProduct X Y .BinProduct.binProdOb = ×BR-Booleω closed X Y
  StoneCat-BinProduct X Y .BinProduct.binProdPr₁ =
    SpFunctor .F-hom (pr₁-BR (fst X) (fst Y))
  StoneCat-BinProduct X Y .BinProduct.binProdPr₂ =
    SpFunctor .F-hom (pr₂-BR (fst X) (fst Y))
  StoneCat-BinProduct X Y .BinProduct.univProp {z = Z} f₁ f₂ =
    exists X Y Z f₁ f₂ , unique X Y Z f₁ f₂

  StoneCat-BinProducts : BinProducts StoneCat
  StoneCat-BinProducts = StoneCat-BinProduct

  -- ════════════════════════════════════════════════════════════════════════════
  -- Part 3.  Stone spaces have binary sums (coproducts).
  -- ════════════════════════════════════════════════════════════════════════════
  --
  -- A binary product of `StoneCat` is, up to the record swap, exactly a binary
  -- coproduct of `StoneCat ^op = StoneCategory` (the honest Stone category): the
  -- projections become injections, and the product universal property becomes the
  -- coproduct universal property (the composite `h ⋆ prᵢ` in `StoneCat` is
  -- literally `injᵢ ⋆ h` in `StoneCat ^op`).  We read this off below.  The
  -- coproduct object of `X` and `Y` is `Sp (X ×BR Y)`, with injections `Sp πB`
  -- and `Sp πC`.

  Stone-BinCoproduct : (X Y : StoneOb) → BinCoproduct StoneCategory X Y
  Stone-BinCoproduct X Y .BinCoproduct.binCoprodOb =
    StoneCat-BinProduct X Y .BinProduct.binProdOb
  Stone-BinCoproduct X Y .BinCoproduct.binCoprodInj₁ =
    StoneCat-BinProduct X Y .BinProduct.binProdPr₁
  Stone-BinCoproduct X Y .BinCoproduct.binCoprodInj₂ =
    StoneCat-BinProduct X Y .BinProduct.binProdPr₂
  Stone-BinCoproduct X Y .BinCoproduct.univProp {z = Z} f₁ f₂ =
    StoneCat-BinProduct X Y .BinProduct.univProp {z = Z} f₁ f₂

  -- The headline categorical theorem: the category of Stone spaces has binary
  -- sums, the sum of `X` and `Y` being `Sp (X ×BR Y)`.
  Stone-BinCoproducts : BinCoproducts StoneCategory
  Stone-BinCoproducts = Stone-BinCoproduct

-- ════════════════════════════════════════════════════════════════════════════
-- Part 4.  Comparison with the type-level statement (for the record).
-- ════════════════════════════════════════════════════════════════════════════
--
-- The categorical coproduct object above is `Sp (X ×BR Y)`.  At the level of
-- underlying types this is the disjoint union `Sp X ⊎ Sp Y` of the two spectra:
-- `StoneSums.SpProd≅SpSum` proves, for *all* Boolean rings `A B`, directly via
-- the connectedness of `2 = BoolBR` (no Stone-duality axiom, no
-- countable-presentation hypothesis),
--
--     Sp (A ×BR B) ≅ Sp A ⊎ Sp B.
--
-- We restate it here as the underlying-type incarnation of the coproduct.  Note
-- `StoneSums` uses `BooleanRing.ProductBA._×BR_` while the categorical part above
-- uses `BooleanRing.Products._×BR_`; both have carrier `⟨A⟩ × ⟨B⟩` with the same
-- componentwise operations, so the two `Sp(A ×BR B)` agree on the nose for the
-- comparison's purpose.
Stone-sum-on-points : (A B : BooleanRing ℓ-zero)
  → Iso (SpGeneralBooleanRing _) (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
Stone-sum-on-points = SpProd≅SpSum

-- ════════════════════════════════════════════════════════════════════════════
-- LIBRARY note (also recorded in LIBRARY_CHANGES.md):
--   * `CountablyPresentedBooleanRings.ProductClosure` fails to typecheck on a
--     clean checkout (`Not in scope: QB.quotientRec` at line 382), so
--     `Booleω-closed-×BR` and therefore `AntiEquivalence.Products` are
--     unavailable.  Until fixed, the closure of `Booleω` under `_×BR_` is taken
--     here as the hypothesis `ClosedUnderProductsBR`; fixing the library
--     discharges it with `Booleω-closed-×BR`.
--   * Upstream, `Stone-BinCoproducts` (Stone spaces have binary sums) belongs
--     next to `AntiEquivalence.Products.StoneCat-BinProducts`, as its formal
--     dual in `StoneCat ^op`.
