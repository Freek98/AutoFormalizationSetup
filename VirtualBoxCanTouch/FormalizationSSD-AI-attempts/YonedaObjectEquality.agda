{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module YonedaObjectEquality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism

open import Cubical.Categories.Category
open import Cubical.Categories.Category.Path
open import Cubical.Categories.Functor
open import Cubical.Categories.Functor.Properties
open import Cubical.Categories.Yoneda
open import Cubical.Categories.Presheaf.Base
open import Cubical.Categories.Instances.Functors
open import Cubical.Categories.Instances.Sets

private
  variable
    ℓ ℓ' : Level

module _ {C : Category ℓ ℓ'} where
  open Category C
  open isUnivalent
  open Functor

  contravariantHomIso→CatIso : {c d : ob}
    → CatIso (PresheafCategory C ℓ') (C [-, c ]) (C [-, d ])
    → CatIso C c d
  contravariantHomIso→CatIso = liftIso {F = YO} isFullyFaithfulYO

  contravariantHomPath→CatIso : {c d : ob}
    → C [-, c ] ≡ C [-, d ]
    → CatIso C c d
  contravariantHomPath→CatIso p =
    contravariantHomIso→CatIso (pathToIso {C = PresheafCategory C _} p)

  contravariantHomPath→Path : isUnivalent C → {c d : ob}
    → C [-, c ] ≡ C [-, d ]
    → c ≡ d
  contravariantHomPath→Path univC p =
    CatIsoToPath univC (contravariantHomPath→CatIso p)


-- Covariant hom functor: C[c, -]
-- Reduced to the contravariant case by applying YO to C^op.
-- The only bridge needed: a path C[c,-] ≡ C[d,-] (Functor C (SET ℓ'))
-- induces a path (C^op)[-, c] ≡ (C^op)[-, d] (Functor (C^op^op) (SET ℓ'))
-- since C and (C^op)^op have the same Hom types definitionally.
module _ {C : Category ℓ ℓ'} where
  open Category
  open isUnivalent
  open Functor

  -- C ^op ^op ≡ C: all data (ob, Hom, id, ⋆) is definitionally the same.
  op-op≡ : C ^op ^op ≡ C
  op-op≡ = CategoryPath.mk≡ cp where
    open CategoryPath
    cp : CategoryPath (C ^op ^op) C
    ob≡ cp = refl
    Hom≡ cp = refl
    id≡ cp = refl
    ⋆≡ cp = refl

  -- Bridge: extract F-ob/F-hom paths from a C-functor path
  -- to build a (C^op)^op-functor path.
  private
    covPath→opOpPath : {c d : C .ob}
      → C [ c ,-] ≡ C [ d ,-]
      → (C ^op) [-, c ] ≡ (C ^op) [-, d ]
    covPath→opOpPath p = Functor≡
      (λ x → cong (λ F → F-ob F x) p)
      (λ f → cong (λ F → F-hom F f) p)

  covariantHomIso→CatIso^op : {c d : C .ob}
    → CatIso (PresheafCategory (C ^op) ℓ') ((C ^op) [-, c ]) ((C ^op) [-, d ])
    → CatIso (C ^op) c d
  covariantHomIso→CatIso^op = contravariantHomIso→CatIso {C = C ^op}

  covariantHomPath→CatIso^op : {c d : C .ob}
    → C [ c ,-] ≡ C [ d ,-]
    → CatIso (C ^op) c d
  covariantHomPath→CatIso^op p =
    contravariantHomPath→CatIso {C = C ^op} (covPath→opOpPath p)

  covariantHomPath→Path : isUnivalent (C ^op) → {c d : C .ob}
    → C [ c ,-] ≡ C [ d ,-]
    → c ≡ d
  covariantHomPath→Path univC^op p =
    CatIsoToPath univC^op (covariantHomPath→CatIso^op p)
