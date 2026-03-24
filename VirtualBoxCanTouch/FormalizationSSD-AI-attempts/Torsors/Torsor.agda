{-# OPTIONS --cubical --no-import-sorts --lossy-unification --guardedness #-}

module Torsors.Torsor where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.PropositionalTruncation as PT

private
  variable
    ℓ ℓ' : Level

module _ (G : Group ℓ) where
  open GroupStr (snd G) renaming (_·_ to _⊙_ ; 1g to e ; inv to g⁻¹ ;
    ·Assoc to ⊙Assoc ; ·IdR to ⊙IdR ; ·IdL to ⊙IdL ;
    ·InvR to ⊙InvR ; ·InvL to ⊙InvL ; is-set to G-isSet)

  -- A right action of G on a type X
  record IsRightAction {X : Type ℓ'} (_·ᵣ_ : X → ⟨ G ⟩ → X) : Type (ℓ-max ℓ ℓ') where
    field
      ·ᵣ-assoc : (x : X) (g h : ⟨ G ⟩) → x ·ᵣ (g ⊙ h) ≡ (x ·ᵣ g) ·ᵣ h
      ·ᵣ-identity : (x : X) → x ·ᵣ e ≡ x

  isFreeAction : {X : Type ℓ'} → (X → ⟨ G ⟩ → X) → Type (ℓ-max ℓ ℓ')
  isFreeAction {X = X} _·ᵣ_ = (a : X) (g : ⟨ G ⟩) → a ·ᵣ g ≡ a → g ≡ e

  isTransitiveAction : {X : Type ℓ'} → (X → ⟨ G ⟩ → X) → Type (ℓ-max ℓ ℓ')
  isTransitiveAction {X = X} _·ᵣ_ = (a b : X) → ∃[ g ∈ ⟨ G ⟩ ] a ·ᵣ g ≡ b

  record IsTorsor {X : Type ℓ'} (_·ᵣ_ : X → ⟨ G ⟩ → X) : Type (ℓ-max ℓ ℓ') where
    field
      isRightAction : IsRightAction _·ᵣ_
      free : isFreeAction _·ᵣ_
      transitive : isTransitiveAction _·ᵣ_
      inhabited : ∥ X ∥₁
      X-isSet : isSet X

    open IsRightAction isRightAction public

  record TorsorStr (X : Type ℓ') : Type (ℓ-max ℓ ℓ') where
    field
      _·ᵣ_ : X → ⟨ G ⟩ → X
      isTorsor : IsTorsor _·ᵣ_

    open IsTorsor isTorsor public

  Torsor : (ℓ' : Level) → Type (ℓ-max ℓ (ℓ-suc ℓ'))
  Torsor ℓ' = TypeWithStr ℓ' TorsorStr

  ---------------------------------------------------------
  -- The shear map characterization
  ---------------------------------------------------------

  shearMap : {X : Type ℓ'} → (X → ⟨ G ⟩ → X) → X × ⟨ G ⟩ → X × X
  shearMap _·ᵣ_ (a , g) = (a , a ·ᵣ g)

  module ShearEquiv {X : Type ℓ'} (_·ᵣ_ : X → ⟨ G ⟩ → X) (tor : IsTorsor _·ᵣ_) where
    open IsTorsor tor

    shearFiberProp : (a b : X) → isProp (Σ[ g ∈ ⟨ G ⟩ ] a ·ᵣ g ≡ b)
    shearFiberProp a b (g₁ , p₁) (g₂ , p₂) = ΣPathP (g-eq , toPathP (X-isSet _ _ _ _))
      where
      g-eq : g₁ ≡ g₂
      g-eq =
        g₁                ≡⟨ sym (⊙IdR g₁) ⟩
        g₁ ⊙ e            ≡⟨ cong (g₁ ⊙_) (sym (⊙InvL g₂)) ⟩
        g₁ ⊙ (g⁻¹ g₂ ⊙ g₂) ≡⟨ ⊙Assoc g₁ (g⁻¹ g₂) g₂ ⟩
        (g₁ ⊙ g⁻¹ g₂) ⊙ g₂ ≡⟨ cong (_⊙ g₂) (free a (g₁ ⊙ g⁻¹ g₂) lem) ⟩
        e ⊙ g₂            ≡⟨ ⊙IdL g₂ ⟩
        g₂ ∎
        where
        lem : a ·ᵣ (g₁ ⊙ g⁻¹ g₂) ≡ a
        lem =
          a ·ᵣ (g₁ ⊙ g⁻¹ g₂)   ≡⟨ ·ᵣ-assoc a g₁ (g⁻¹ g₂) ⟩
          (a ·ᵣ g₁) ·ᵣ g⁻¹ g₂  ≡⟨ cong (_·ᵣ g⁻¹ g₂) (p₁ ∙ sym p₂) ⟩
          (a ·ᵣ g₂) ·ᵣ g⁻¹ g₂  ≡⟨ sym (·ᵣ-assoc a g₂ (g⁻¹ g₂)) ⟩
          a ·ᵣ (g₂ ⊙ g⁻¹ g₂)   ≡⟨ cong (a ·ᵣ_) (⊙InvR g₂) ⟩
          a ·ᵣ e                 ≡⟨ ·ᵣ-identity a ⟩
          a ∎

    shearIsEquiv : isEquiv (shearMap _·ᵣ_)
    shearIsEquiv = isoToIsEquiv shearIso
      where
      extractG : (a b : X) → Σ[ g ∈ ⟨ G ⟩ ] a ·ᵣ g ≡ b
      extractG a b = PT.rec (shearFiberProp a b) (idfun _) (transitive a b)

      shearInv : X × X → X × ⟨ G ⟩
      shearInv (a , b) = a , fst (extractG a b)

      shearIso : Iso (X × ⟨ G ⟩) (X × X)
      Iso.fun shearIso = shearMap _·ᵣ_
      Iso.inv shearIso = shearInv
      Iso.sec shearIso (a , b) = ΣPathP (refl , snd (extractG a b))
      Iso.ret shearIso (a , g) = ΣPathP (refl , cong (λ p → fst p) (shearFiberProp a (a ·ᵣ g)
          (extractG a (a ·ᵣ g)) (g , refl)))

  ---------------------------------------------------------
  -- Example: G is a G-torsor via right multiplication
  ---------------------------------------------------------
  module CanonicalTorsor where
    _·ᵣ_ : ⟨ G ⟩ → ⟨ G ⟩ → ⟨ G ⟩
    a ·ᵣ g = a ⊙ g

    canonicalIsRightAction : IsRightAction _·ᵣ_
    IsRightAction.·ᵣ-assoc canonicalIsRightAction x g h = ⊙Assoc x g h
    IsRightAction.·ᵣ-identity canonicalIsRightAction x = ⊙IdR x

    canonicalFree : isFreeAction _·ᵣ_
    canonicalFree a g p =
      g               ≡⟨ sym (⊙IdL g) ⟩
      e ⊙ g           ≡⟨ cong (_⊙ g) (sym (⊙InvL a)) ⟩
      (g⁻¹ a ⊙ a) ⊙ g ≡⟨ sym (⊙Assoc (g⁻¹ a) a g) ⟩
      g⁻¹ a ⊙ (a ⊙ g) ≡⟨ cong (g⁻¹ a ⊙_) p ⟩
      g⁻¹ a ⊙ a       ≡⟨ ⊙InvL a ⟩
      e ∎

    canonicalTransitive : isTransitiveAction _·ᵣ_
    canonicalTransitive a b = ∣ g⁻¹ a ⊙ b , lem ∣₁
      where
      lem : a ⊙ (g⁻¹ a ⊙ b) ≡ b
      lem = ⊙Assoc a (g⁻¹ a) b ∙ cong (_⊙ b) (⊙InvR a) ∙ ⊙IdL b

    canonicalIsTorsor : IsTorsor _·ᵣ_
    IsTorsor.isRightAction canonicalIsTorsor = canonicalIsRightAction
    IsTorsor.free canonicalIsTorsor = canonicalFree
    IsTorsor.transitive canonicalIsTorsor = canonicalTransitive
    IsTorsor.inhabited canonicalIsTorsor = ∣ e ∣₁
    IsTorsor.X-isSet canonicalIsTorsor = G-isSet

    canonicalTorsor : Torsor ℓ
    canonicalTorsor = ⟨ G ⟩ , record { _·ᵣ_ = _·ᵣ_ ; isTorsor = canonicalIsTorsor }

  ---------------------------------------------------------
  -- Main Lemma: X ≃ (equivariant isos from X to G)
  ---------------------------------------------------------

  module MainLemma {X : Type ℓ} (_·ᵣ_ : X → ⟨ G ⟩ → X) (tor : IsTorsor _·ᵣ_) where
    open IsTorsor tor
    open ShearEquiv _·ᵣ_ tor

    fiberProp : (x y : X) → isProp (Σ[ g ∈ ⟨ G ⟩ ] x ·ᵣ g ≡ y)
    fiberProp = shearFiberProp

    extractG : (x y : X) → Σ[ g ∈ ⟨ G ⟩ ] x ·ᵣ g ≡ y
    extractG x y = PT.rec (fiberProp x y) (idfun _) (transitive x y)

    σ : X → X → ⟨ G ⟩
    σ x y = fst (extractG x y)

    σ-spec : (x y : X) → x ·ᵣ σ x y ≡ y
    σ-spec x y = snd (extractG x y)

    σ-Iso : (x : X) → Iso X ⟨ G ⟩
    Iso.fun (σ-Iso x) = σ x
    Iso.inv (σ-Iso x) g = x ·ᵣ g
    Iso.sec (σ-Iso x) g = cong (λ p → fst p) (fiberProp x (x ·ᵣ g) (extractG x (x ·ᵣ g)) (g , refl))
    Iso.ret (σ-Iso x) y = σ-spec x y

    fromIso : Iso X ⟨ G ⟩ → X
    fromIso τ = Iso.inv τ e

    IsEquivariant : Iso X ⟨ G ⟩ → Type _
    IsEquivariant τ = (y : X) (g : ⟨ G ⟩) → Iso.fun τ (y ·ᵣ g) ≡ (Iso.fun τ y) ⊙ g

    σ-equivariant : (x : X) → IsEquivariant (σ-Iso x)
    σ-equivariant x y g =
      cong (λ p → fst p) (fiberProp x (y ·ᵣ g) (extractG x (y ·ᵣ g)) (σ x y ⊙ g , lem))
      where
      lem : x ·ᵣ (σ x y ⊙ g) ≡ y ·ᵣ g
      lem = ·ᵣ-assoc x (σ x y) g ∙ cong (_·ᵣ g) (σ-spec x y)

    roundtrip₁ : (x : X) → fromIso (σ-Iso x) ≡ x
    roundtrip₁ x = ·ᵣ-identity x

    roundtrip₂-fun : (τ : Iso X ⟨ G ⟩) → IsEquivariant τ
                    → (y : X) → σ (fromIso τ) y ≡ Iso.fun τ y
    roundtrip₂-fun τ eqv y =
      cong (λ p → fst p) (fiberProp x₀ y (extractG x₀ y) (Iso.fun τ y , lem))
      where
      x₀ = Iso.inv τ e

      lem : x₀ ·ᵣ Iso.fun τ y ≡ y
      lem = isoFunInjective τ _ _
        (eqv x₀ (Iso.fun τ y)
         ∙ cong (_⊙ Iso.fun τ y) (Iso.sec τ e)
         ∙ ⊙IdL (Iso.fun τ y))

    roundtrip₂-inv : (τ : Iso X ⟨ G ⟩) → IsEquivariant τ
                    → (g : ⟨ G ⟩) → (fromIso τ) ·ᵣ g ≡ Iso.inv τ g
    roundtrip₂-inv τ eqv g = isoFunInjective τ _ _
      (eqv x₀ g
       ∙ cong (_⊙ g) (Iso.sec τ e)
       ∙ ⊙IdL g
       ∙ sym (Iso.sec τ g))
      where x₀ = Iso.inv τ e

    EquivIso : Type _
    EquivIso = Σ[ τ ∈ Iso X ⟨ G ⟩ ] IsEquivariant τ

    X≃EquivIso : Iso X EquivIso
    Iso.fun X≃EquivIso x = σ-Iso x , σ-equivariant x
    Iso.inv X≃EquivIso (τ , _) = fromIso τ
    Iso.sec X≃EquivIso (τ , eqv) =
      ΣPathP (isoPath , toPathP (isPropΠ2 (λ _ _ → G-isSet _ _) _ _))
      where
      x₀ = fromIso τ
      isoPath : σ-Iso x₀ ≡ τ
      isoPath = Iso≡Set X-isSet G-isSet (σ-Iso x₀) τ
        (roundtrip₂-fun τ eqv) (roundtrip₂-inv τ eqv)
    Iso.ret X≃EquivIso x = roundtrip₁ x
