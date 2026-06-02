{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- Local shim.  The library file `BooleanRing.Products` (which packages the
-- binary product of Boolean algebras with named projections `pr₁-BR`/`pr₂-BR`,
-- pairing `⟨_,_⟩BR`, and its universal property) is NOT in the library's git
-- version.  To keep this folder portable, we rebuild exactly that interface on
-- top of the git-tracked `BooleanRing.ProductBA` (whose product is the same
-- object, with projections `BRProduct.πB`/`πC` and pairing `BRProduct.UP.⟨f,g⟩`).
--
-- LIBRARY TASK: either commit `BooleanRing.Products` upstream, or add these
-- names to `BooleanRing.ProductBA`; then this shim can be deleted.
module ProductBAProjections where

open import Cubical.Foundations.Prelude
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import BooleanRing.BooleanRingMaps
open import BooleanRing.ProductBA public using (_×BR_)
open import BooleanRing.ProductBA

pr₁-BR : (A B : BooleanRing ℓ-zero) → BoolHom (A ×BR B) A
pr₁-BR A B = BRProduct.πB A B

pr₂-BR : (A B : BooleanRing ℓ-zero) → BoolHom (A ×BR B) B
pr₂-BR A B = BRProduct.πC A B

⟨_,_⟩BR : {C : BooleanRing ℓ-zero} (A B : BooleanRing ℓ-zero)
  → BoolHom C A → BoolHom C B → BoolHom C (A ×BR B)
⟨ A , B ⟩BR f g = BRProduct.UP.⟨f,g⟩ A B f g

⟨,⟩BR-pr₁ : (A B C : BooleanRing ℓ-zero) (f : BoolHom C A) (g : BoolHom C B)
  → pr₁-BR A B ∘cr ⟨ A , B ⟩BR f g ≡ f
⟨,⟩BR-pr₁ A B C f g = BRProduct.UP.extensionπB A B f g

⟨,⟩BR-pr₂ : (A B C : BooleanRing ℓ-zero) (f : BoolHom C A) (g : BoolHom C B)
  → pr₂-BR A B ∘cr ⟨ A , B ⟩BR f g ≡ g
⟨,⟩BR-pr₂ A B C f g = BRProduct.UP.extensionπC A B f g

⟨,⟩BR-unique : (A B C : BooleanRing ℓ-zero) (f : BoolHom C A) (g : BoolHom C B)
  → (h : BoolHom C (A ×BR B)) → pr₁-BR A B ∘cr h ≡ f → pr₂-BR A B ∘cr h ≡ g
  → h ≡ ⟨ A , B ⟩BR f g
⟨,⟩BR-unique A B C f g h p q = sym (BRProduct.UP.uniqueness A B f g h p q)
