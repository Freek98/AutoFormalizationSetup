{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)
import work.Part12

module work.Part14a (fa : FoundationalAxioms) (ia : work.Part12.IntervalAxioms fa) where

open import work.Part13 fa ia public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_; isEquiv; invEquiv; equivFun; invEq; secEq)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Transport using (transport⁻; transportTransport⁻)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁; ∣_∣₁)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Int using (ℤ)
open import Cubical.Algebra.BooleanRing using (BoolHom; BooleanRingStr; BooleanRing; BooleanRing→CommRing)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing using (_∘cr_; CommRingStr; CommRing→Ring; IsCommRingHom)
open import StoneSpaces.Spectrum using (Booleω; Sp; Stone; hasStoneStr)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv)

module CohomologyModule where
  open import StoneSpaces.Spectrum using (Stone; hasStoneStr)
  open CompactHausdorffModule using (CHaus)

  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
  open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr; AbGroup→Group)
  import Cubical.Algebra.Group.Properties as GrpProps
  open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠAbGroup)
  open import Cubical.Data.Int using (ℤ)
  open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; 0ₖ; hLevelEM)
  import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp
  open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; 0ₕ)

  BZ : Type ℓ-zero
  BZ = EM ℤAbGroup 1

  H¹ : Type ℓ-zero → Type ℓ-zero
  H¹ X = coHom 1 ℤAbGroup X

  H¹-vanishes : Type ℓ-zero → Type ℓ-zero
  H¹-vanishes X = (x : H¹ X) → x ≡ (0ₕ 1 {G = ℤAbGroup} {A = X})

  module CechComplex {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where

    |A|_ : S → Type ℓ
    |A| x = fst (A x)

    module AGx (x : S) = AbGroupStr (snd (A x))

    C⁰ : Type ℓ
    C⁰ = (x : S) → T x → |A| x

    C¹ : Type ℓ
    C¹ = (x : S) → T x → T x → |A| x

    C² : Type ℓ
    C² = (x : S) → T x → T x → T x → |A| x

    d₀ : C⁰ → C¹
    d₀ α x u v = AGx._-_ x (α x v) (α x u)

    d₁ : C¹ → C²
    d₁ β x u v w = AGx._+_ x (AGx._-_ x (β x v w) (β x u w)) (β x u v)

    is1Cocycle : C¹ → Type ℓ
    is1Cocycle β = (x : S) (u v w : T x) → d₁ β x u v w ≡ AGx.0g x

    is1Coboundary : C¹ → Type ℓ
    is1Coboundary β = Σ[ α ∈ C⁰ ] d₀ α ≡ β

    Ȟ¹-vanishes : Type ℓ
    Ȟ¹-vanishes = (β : C¹) → is1Cocycle β → ∥ is1Coboundary β ∥₁

    d₁∘d₀≡0 : (α : C⁰) (x : S) (u v w : T x) → d₁ (d₀ α) x u v w ≡ AGx.0g x
    d₁∘d₀≡0 α x u v w = goal where
      module G = AbGroupStr (snd (A x))
      module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))
      a = α x u ; b = α x v ; c = α x w
      step1 : G._+_ (G._-_ c b) (G._-_ b a) ≡ G._-_ c a
      step1 =
        G._+_ (G._+_ c (G.-_ b)) (G._+_ b (G.-_ a))
          ≡⟨ G.+Assoc (G._+_ c (G.-_ b)) b (G.-_ a) ⟩
        G._+_ (G._+_ (G._+_ c (G.-_ b)) b) (G.-_ a)
          ≡⟨ cong (λ z → G._+_ z (G.-_ a))
               (sym (G.+Assoc c (G.-_ b) b)
                ∙ cong (G._+_ c) (G.+InvL b)
                ∙ G.+IdR c) ⟩
        G._+_ c (G.-_ a) ∎
      goal : G._+_ (G._-_ (G._-_ c b) (G._-_ c a)) (G._-_ b a) ≡ G.0g
      goal =
        G._+_ (G._+_ (G._-_ c b) (G.-_ (G._-_ c a))) (G._-_ b a)
          ≡⟨ sym (G.+Assoc (G._-_ c b) (G.-_ (G._-_ c a)) (G._-_ b a)) ⟩
        G._+_ (G._-_ c b) (G._+_ (G.-_ (G._-_ c a)) (G._-_ b a))
          ≡⟨ cong (G._+_ (G._-_ c b)) (G.+Comm (G.-_ (G._-_ c a)) (G._-_ b a)) ⟩
        G._+_ (G._-_ c b) (G._+_ (G._-_ b a) (G.-_ (G._-_ c a)))
          ≡⟨ G.+Assoc (G._-_ c b) (G._-_ b a) (G.-_ (G._-_ c a)) ⟩
        G._+_ (G._+_ (G._-_ c b) (G._-_ b a)) (G.-_ (G._-_ c a))
          ≡⟨ cong (λ z → G._+_ z (G.-_ (G._-_ c a))) step1 ⟩
        G._+_ (G._-_ c a) (G.-_ (G._-_ c a))
          ≡⟨ G.+InvR (G._-_ c a) ⟩
        G.0g ∎

    module CocycleProps (β : C¹) (cocyc : is1Cocycle β) where
      private module Gx (x : S) = GrpProps.GroupTheory (AbGroup→Group (A x))

      cocycle-diag : (x : S) (u : T x) → β x u u ≡ AGx.0g x
      cocycle-diag x u =
        β x u u
          ≡⟨ sym (AGx.+IdL x (β x u u)) ⟩
        AGx._+_ x (AGx.0g x) (β x u u)
          ≡⟨ cong (λ z → AGx._+_ x z (β x u u)) (sym (AGx.+InvR x (β x u u))) ⟩
        AGx._+_ x (AGx._-_ x (β x u u) (β x u u)) (β x u u)
          ≡⟨ cocyc x u u u ⟩
        AGx.0g x ∎

      cocycle-antisym : (x : S) (u v : T x) → β x u v ≡ AGx.-_ x (β x v u)
      cocycle-antisym x u v = Gx.invUniqueR x (sym d₁-expand ∙ cocyc x v u v)
        where
        d₁-expand : d₁ β x v u v ≡ AGx._+_ x (β x v u) (β x u v)
        d₁-expand =
          AGx._+_ x (AGx._-_ x (β x u v) (β x v v)) (β x v u)
            ≡⟨ cong (λ z → AGx._+_ x (AGx._-_ x (β x u v) z) (β x v u))
                 (cocycle-diag x v) ⟩
          AGx._+_ x (AGx._-_ x (β x u v) (AGx.0g x)) (β x v u)
            ≡⟨ cong (λ z → AGx._+_ x (AGx._+_ x (β x u v) z) (β x v u))
                 (Gx.inv1g x) ⟩
          AGx._+_ x (AGx._+_ x (β x u v) (AGx.0g x)) (β x v u)
            ≡⟨ cong (λ z → AGx._+_ x z (β x v u)) (AGx.+IdR x (β x u v)) ⟩
          AGx._+_ x (β x u v) (β x v u)
            ≡⟨ AGx.+Comm x (β x u v) (β x v u) ⟩
          AGx._+_ x (β x v u) (β x u v) ∎

      cocycle-add : (x : S) (u v w : T x) → AGx._+_ x (β x u v) (β x v w) ≡ β x u w
      cocycle-add x u v w = Gx.·CancelR x (AGx.-_ x (β x u w)) add-step
        where
        add-step : AGx._+_ x (AGx._+_ x (β x u v) (β x v w)) (AGx.-_ x (β x u w))
                 ≡ AGx._+_ x (β x u w) (AGx.-_ x (β x u w))
        add-step =
          AGx._+_ x (AGx._+_ x (β x u v) (β x v w)) (AGx.-_ x (β x u w))
            ≡⟨ sym (AGx.+Assoc x (β x u v) (β x v w) (AGx.-_ x (β x u w))) ⟩
          AGx._+_ x (β x u v) (AGx._+_ x (β x v w) (AGx.-_ x (β x u w)))
            ≡⟨ AGx.+Comm x (β x u v) (AGx._-_ x (β x v w) (β x u w)) ⟩
          AGx._+_ x (AGx._-_ x (β x v w) (β x u w)) (β x u v)
            ≡⟨ cocyc x u v w ⟩
          AGx.0g x
            ≡⟨ sym (AGx.+InvR x (β x u w)) ⟩
          AGx._+_ x (β x u w) (AGx.-_ x (β x u w)) ∎

  private
    grp-sub-rearrange : {ℓ : Level} (G : AbGroup ℓ) (a b c : fst G)
      → let module Ax = AbGroupStr (snd G)
        in Ax._-_ a b ≡ Ax.-_ c → a ≡ Ax._-_ b c
    grp-sub-rearrange G a b c step1 =
      a
        ≡⟨ sym (Ax.+IdR a) ⟩
      Ax._+_ a Ax.0g
        ≡⟨ cong (Ax._+_ a) (sym (Ax.+InvL b)) ⟩
      Ax._+_ a (Ax._+_ (Ax.-_ b) b)
        ≡⟨ Ax.+Assoc a (Ax.-_ b) b ⟩
      Ax._+_ (Ax._-_ a b) b
        ≡⟨ cong (λ z → Ax._+_ z b) step1 ⟩
      Ax._+_ (Ax.-_ c) b
        ≡⟨ Ax.+Comm (Ax.-_ c) b ⟩
      Ax._-_ b c ∎
      where module Ax = AbGroupStr (snd G)

  module SectionExactCechComplex {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where
    open CechComplex S T A

    section-exact : ((x : S) → T x) → Ȟ¹-vanishes
    section-exact t β cocycle-cond = ∣ α , funExt (λ x → funExt λ u → funExt λ v → prove-at x u v) ∣₁
      where
        α : C⁰
        α x u = β x (t x) u

        prove-at : (x : S) (u v : T x) → d₀ α x u v ≡ β x u v
        prove-at x u v = sym step2
          where
            module Ax = AbGroupStr (snd (A x))
            module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))

            a = β x u v
            b = β x (t x) v
            c = β x (t x) u

            step1 : Ax._-_ a b ≡ Ax.-_ c
            step1 = Gx.invUniqueL (cocycle-cond x (t x) u v)

            step2 : a ≡ Ax._-_ b c
            step2 = grp-sub-rearrange (A x) a b c step1

  module CanonicalExactCechComplex {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where

    A^T : S → AbGroup ℓ
    A^T x = ΠAbGroup {X = T x} (λ _ → A x)

    open CechComplex S T A^T public

    canonical-exact : Ȟ¹-vanishes
    canonical-exact β cocycle-cond = ∣ α , funExt (λ x → funExt λ u → funExt λ v → funExt λ t → prove-at x u v t) ∣₁
      where
        α : C⁰
        α x u t = β x t u t

        prove-at : (x : S) (u v : T x) (t : T x) → d₀ α x u v t ≡ β x u v t
        prove-at x u v t = sym step2
          where
            module Ax = AbGroupStr (snd (A x))
            module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))

            a = β x u v t
            b = β x t v t
            c = β x t u t

            step1 : Ax._-_ a b ≡ Ax.-_ c
            step1 = Gx.invUniqueL (cong (λ f → f t) (cocycle-cond x t u v))

            step2 : a ≡ Ax._-_ b c
            step2 = grp-sub-rearrange (A x) a b c step1

  -- tex Lemma 2823
  module ExactCechComplexVanishingProof {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ)
      (A : S → AbGroup ℓ)
      (inhabited : (x : S) → ∥ T x ∥₁)
      (exact : CechComplex.Ȟ¹-vanishes S T A) where

    open CechComplex S T A

    open import Cubical.HITs.PropositionalTruncation.Properties as PT-Props
    open import Cubical.Foundations.Isomorphism using (Iso)
    open import Cubical.Foundations.GroupoidLaws using (symDistr; rCancel; lCancel; lUnit) renaming (assoc to assoc-path)

    EM-iso : (x : S) → Iso (EM (A x) 0) (0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1)
    EM-iso x = EMProp.Iso-EM-ΩEM+1 {G = A x} 0

    path-to-EM0 : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → (x : S) → T x → T x → EM (A x) 0
    path-to-EM0 α β x u v = Iso.inv (EM-iso x) (sym (β x u) ∙ β x v)

    path-to-EM0-is-cocycle : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → CechComplex.is1Cocycle S T A (path-to-EM0 α β)
    path-to-EM0-is-cocycle α β x u v w = goal
      where

        module Ax = AbGroupStr (snd (A x))
        module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))

        g : (s t : T x) → EM (A x) 0
        g s t = path-to-EM0 α β x s t

        ϕ : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1 → EM (A x) 0
        ϕ = Iso.inv (EM-iso x)

        pu = β x u
        pv = β x v
        pw = β x w

        guv = g u v
        guw = g u w
        gvw = g v w

        p-uv : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1
        p-uv = sym pu ∙ pv

        p-uw : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1
        p-uw = sym pu ∙ pw

        p-vw : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1
        p-vw = sym pv ∙ pw

        combined-path : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1
        combined-path = p-vw ∙ sym p-uw ∙ p-uv

        sym-p-uw : sym p-uw ≡ sym pw ∙ pu
        sym-p-uw =
          sym p-uw
            ≡⟨ symDistr (sym pu) pw ⟩
          sym pw ∙ pu ∎

        combined-is-refl : combined-path ≡ refl
        combined-is-refl =
          p-vw ∙ sym p-uw ∙ p-uv
            ≡⟨ cong (λ z → p-vw ∙ z ∙ p-uv) sym-p-uw ⟩
          p-vw ∙ (sym pw ∙ pu) ∙ p-uv
            ≡⟨ cong (p-vw ∙_) (sym (assoc-path (sym pw) pu p-uv)) ⟩
          p-vw ∙ (sym pw ∙ (pu ∙ (sym pu ∙ pv)))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ z)) (assoc-path pu (sym pu) pv) ⟩
          p-vw ∙ (sym pw ∙ ((pu ∙ sym pu) ∙ pv))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ z)) (cong (_∙ pv) (rCancel pu) ∙ sym (lUnit pv)) ⟩
          (sym pv ∙ pw) ∙ (sym pw ∙ pv)
            ≡⟨ sym (assoc-path (sym pv) pw (sym pw ∙ pv)) ⟩
          sym pv ∙ (pw ∙ (sym pw ∙ pv))
            ≡⟨ cong (sym pv ∙_) (assoc-path pw (sym pw) pv) ⟩
          sym pv ∙ ((pw ∙ sym pw) ∙ pv)
            ≡⟨ cong (sym pv ∙_) (cong (_∙ pv) (rCancel pw) ∙ sym (lUnit pv)) ⟩
          sym pv ∙ pv
            ≡⟨ lCancel pv ⟩
          refl ∎

        ϕ-hom : (p q : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1) → ϕ (p ∙ q) ≡ Ax._+_ (ϕ p) (ϕ q)
        ϕ-hom p q = EMProp.ΩEM+1→EM-hom {G = A x} 0 p q

        ϕ-sym : (p : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1) → ϕ (sym p) ≡ Ax.-_ (ϕ p)
        ϕ-sym p = EMProp.ΩEM+1→EM-sym {G = A x} 0 p

        ϕ-refl : ϕ refl ≡ Ax.0g
        ϕ-refl = EMProp.ΩEM+1→EM-refl {G = A x} 0

        combined-gives-0g : ϕ combined-path ≡ Ax.0g
        combined-gives-0g =
          ϕ combined-path
            ≡⟨ cong ϕ combined-is-refl ⟩
          ϕ refl
            ≡⟨ ϕ-refl ⟩
          Ax.0g ∎

        expand-combined : ϕ combined-path ≡ Ax._+_ (Ax._+_ gvw (Ax.-_ guw)) guv
        expand-combined =
          ϕ (p-vw ∙ sym p-uw ∙ p-uv)
            ≡⟨ ϕ-hom p-vw (sym p-uw ∙ p-uv) ⟩
          Ax._+_ (ϕ p-vw) (ϕ (sym p-uw ∙ p-uv))
            ≡⟨ cong (Ax._+_ (ϕ p-vw)) (ϕ-hom (sym p-uw) p-uv) ⟩
          Ax._+_ (ϕ p-vw) (Ax._+_ (ϕ (sym p-uw)) (ϕ p-uv))
            ≡⟨ cong (λ z → Ax._+_ (ϕ p-vw) (Ax._+_ z (ϕ p-uv))) (ϕ-sym p-uw) ⟩
          Ax._+_ gvw (Ax._+_ (Ax.-_ guw) guv)
            ≡⟨ Ax.+Assoc gvw (Ax.-_ guw) guv ⟩
          Ax._+_ (Ax._+_ gvw (Ax.-_ guw)) guv ∎

        goal : d₁ (path-to-EM0 α β) x u v w ≡ AGx.0g x
        goal =
          d₁ (path-to-EM0 α β) x u v w
            ≡⟨ sym expand-combined ⟩
          ϕ combined-path
            ≡⟨ combined-gives-0g ⟩
          AGx.0g x ∎

    get-coboundary : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → ∥ CechComplex.is1Coboundary S T A (path-to-EM0 α β) ∥₁
    get-coboundary α β = exact (path-to-EM0 α β) (path-to-EM0-is-cocycle α β)

    vanishing-result : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → ∥ ((x : S) → α x ≡ 0ₖ {G = A x} 1) ∥₁
    vanishing-result α β = PT-Props.map go (get-coboundary α β)
      where
        go : CechComplex.is1Coboundary S T A (path-to-EM0 α β) → (x : S) → α x ≡ 0ₖ {G = A x} 1
        go (cb-f , cb-eq) x = SE.rec→Set β-adjusted β-adjusted-constant (inhabited x)
          where
          module SE = PT-Props.SetElim (isOfHLevelPath' 2 (hLevelEM (A x) 1) (α x) (0ₖ {G = A x} 1))

          β-adjusted : T x → α x ≡ 0ₖ {G = A x} 1
          β-adjusted t = β x t ∙ Iso.fun (EM-iso x) (AGx.-_ x (cb-f x t))

          β-adjusted-constant : (u v : T x) → β-adjusted u ≡ β-adjusted v
          β-adjusted-constant u v = final-goal
            where
              module Ax = AbGroupStr (snd (A x))
              module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))

              fu = cb-f x u
              fv = cb-f x v
              βu = β x u
              βv = β x v

              ψ : EM (A x) 0 → 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1
              ψ = Iso.fun (EM-iso x)

              ϕ : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1 → EM (A x) 0
              ϕ = Iso.inv (EM-iso x)

              ψ∘ϕ : (p : 0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1) → ψ (ϕ p) ≡ p
              ψ∘ϕ = Iso.sec (EM-iso x)

              ψ-hom : (a b : EM (A x) 0) → ψ (Ax._+_ a b) ≡ ψ a ∙ ψ b
              ψ-hom = EMProp.EM→ΩEM+1-hom {G = A x} 0

              ψ-neg : (a : EM (A x) 0) → ψ (Ax.-_ a) ≡ sym (ψ a)
              ψ-neg = EMProp.EM→ΩEM+1-sym {G = A x} 0

              d₀-rel : d₀ cb-f x u v ≡ path-to-EM0 α β x u v
              d₀-rel = funExt⁻ (funExt⁻ (funExt⁻ cb-eq x) u) v

              key-rel : sym βu ∙ βv ≡ ψ (AGx._-_ x fv fu)
              key-rel =
                sym βu ∙ βv
                  ≡⟨ sym (ψ∘ϕ (sym βu ∙ βv)) ⟩
                ψ (ϕ (sym βu ∙ βv))
                  ≡⟨ cong ψ (sym d₀-rel) ⟩
                ψ (AGx._-_ x fv fu) ∎

              ψ-expand : ψ (AGx._-_ x fv fu) ≡ ψ fv ∙ sym (ψ fu)
              ψ-expand =
                ψ (AGx._-_ x fv fu)
                  ≡⟨ ψ-hom fv (Ax.-_ fu) ⟩
                ψ fv ∙ ψ (Ax.-_ fu)
                  ≡⟨ cong (ψ fv ∙_) (ψ-neg fu) ⟩
                ψ fv ∙ sym (ψ fu) ∎

              key-eq : sym βu ∙ βv ≡ ψ fv ∙ sym (ψ fu)
              key-eq =
                sym βu ∙ βv
                  ≡⟨ key-rel ⟩
                ψ (AGx._-_ x fv fu)
                  ≡⟨ ψ-expand ⟩
                ψ fv ∙ sym (ψ fu) ∎

              open import Cubical.Foundations.GroupoidLaws using (assoc)

              sym-comm : (a b : EM (A x) 0) → sym (ψ a) ∙ sym (ψ b) ≡ sym (ψ b) ∙ sym (ψ a)
              sym-comm a b =
                sym (ψ a) ∙ sym (ψ b)
                  ≡⟨ cong₂ _∙_ (sym (ψ-neg a)) (sym (ψ-neg b)) ⟩
                ψ (Ax.-_ a) ∙ ψ (Ax.-_ b)
                  ≡⟨ sym (ψ-hom (Ax.-_ a) (Ax.-_ b)) ⟩
                ψ (Ax._+_ (Ax.-_ a) (Ax.-_ b))
                  ≡⟨ cong ψ (Ax.+Comm (Ax.-_ a) (Ax.-_ b)) ⟩
                ψ (Ax._+_ (Ax.-_ b) (Ax.-_ a))
                  ≡⟨ ψ-hom (Ax.-_ b) (Ax.-_ a) ⟩
                ψ (Ax.-_ b) ∙ ψ (Ax.-_ a)
                  ≡⟨ cong₂ _∙_ (ψ-neg b) (ψ-neg a) ⟩
                sym (ψ b) ∙ sym (ψ a) ∎

              step1 : βu ∙ (sym βu ∙ βv) ≡ βu ∙ (ψ fv ∙ sym (ψ fu))
              step1 = cong (βu ∙_) key-eq

              lhs-simplify : βu ∙ (sym βu ∙ βv) ≡ βv
              lhs-simplify =
                βu ∙ (sym βu ∙ βv)
                  ≡⟨ assoc βu (sym βu) βv ⟩
                (βu ∙ sym βu) ∙ βv
                  ≡⟨ cong (_∙ βv) (rCancel βu) ∙ sym (lUnit βv) ⟩
                βv ∎

              βv-eq : βv ≡ βu ∙ (ψ fv ∙ sym (ψ fu))
              βv-eq =
                βv
                  ≡⟨ sym lhs-simplify ⟩
                βu ∙ (sym βu ∙ βv)
                  ≡⟨ step1 ⟩
                βu ∙ (ψ fv ∙ sym (ψ fu)) ∎

              step4 : βv ∙ sym (ψ fv) ≡ (βu ∙ (ψ fv ∙ sym (ψ fu))) ∙ sym (ψ fv)
              step4 = cong (_∙ sym (ψ fv)) βv-eq

              rhs-simplify : (βu ∙ (ψ fv ∙ sym (ψ fu))) ∙ sym (ψ fv) ≡ βu ∙ sym (ψ fu)
              rhs-simplify =
                (βu ∙ (ψ fv ∙ sym (ψ fu))) ∙ sym (ψ fv)
                  ≡⟨ sym (assoc βu (ψ fv ∙ sym (ψ fu)) (sym (ψ fv))) ⟩
                βu ∙ ((ψ fv ∙ sym (ψ fu)) ∙ sym (ψ fv))
                  ≡⟨ cong (βu ∙_) (
                      sym (assoc (ψ fv) (sym (ψ fu)) (sym (ψ fv)))
                      ∙ cong (ψ fv ∙_) (sym-comm fu fv)
                      ∙ assoc (ψ fv) (sym (ψ fv)) (sym (ψ fu))
                      ∙ cong (_∙ sym (ψ fu)) (rCancel (ψ fv))
                      ∙ sym (lUnit (sym (ψ fu)))) ⟩
                βu ∙ sym (ψ fu) ∎

              path-algebra-lemma : βu ∙ sym (ψ fu) ≡ βv ∙ sym (ψ fv)
              path-algebra-lemma =
                βu ∙ sym (ψ fu)
                  ≡⟨ sym rhs-simplify ⟩
                (βu ∙ (ψ fv ∙ sym (ψ fu))) ∙ sym (ψ fv)
                  ≡⟨ sym step4 ⟩
                βv ∙ sym (ψ fv) ∎

              final-goal : β-adjusted u ≡ β-adjusted v
              final-goal =
                β-adjusted u
                  ≡⟨ cong₂ _∙_ refl (ψ-neg fu) ⟩
                βu ∙ sym (ψ fu)
                  ≡⟨ path-algebra-lemma ⟩
                βv ∙ sym (ψ fv)
                  ≡⟨ sym (cong₂ _∙_ refl (ψ-neg fv)) ⟩
                β-adjusted v ∎

  exact-cech-complex-vanishing-cohomology : {ℓ : Level} (S : Type ℓ)
    (T : S → Type ℓ) (A : S → AbGroup ℓ)
    (inhabited : (x : S) → ∥ T x ∥₁)
    (exact : CechComplex.Ȟ¹-vanishes S T A)
    (α : (x : S) → EM (A x) 1)
    (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
    → ∥ ((x : S) → α x ≡ 0ₖ {G = A x} 1) ∥₁
  exact-cech-complex-vanishing-cohomology S T A inhabited exact α β =
    ExactCechComplexVanishingProof.vanishing-result S T A inhabited exact α β

  -- tex Lemma 2878: finite case
  open import Cubical.Data.FinSet.Base using (isFinSet) public

  cech-vanishing-finite : (S : Type ℓ-zero) (T : S → Type ℓ-zero)
    → isFinSet S → ((x : S) → isFinSet (T x))
    → ((x : S) → ∥ T x ∥₁)
    → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)
  cech-vanishing-finite S T finS finT inh β cocyc =
    PT.rec squash₁
      (λ sect → SectionExactCechComplex.section-exact S T (λ _ → ℤAbGroup) sect β cocyc)
      (FC.choice (_ , finS) T inh)
    where
    open import Cubical.HITs.PropositionalTruncation as PT
    open import Cubical.Data.FinSet.FiniteChoice as FC using (choice)

  -- tex Lemma 2878: Stone case

  -- tex Lemma 2843: Finite approximation of Stone families
  record FiniteApprox (S : Type ℓ-zero) (T : S → Type ℓ-zero) (β : CechComplex.C¹ S T (λ _ → ℤAbGroup)) : Type (ℓ-suc ℓ-zero) where
    field
      S' : Type ℓ-zero
      T' : S' → Type ℓ-zero
      finS' : isFinSet S'
      finT' : (s : S') → isFinSet (T' s)
      inh' : (s : S') → ∥ T' s ∥₁
      π : S → S'
      τ : (x : S) → T x → T' (π x)
      β' : CechComplex.C¹ S' T' (λ _ → ℤAbGroup)
      β-factors : (x : S) (u v : T x) → β x u v ≡ β' (π x) (τ x u) (τ x v)
      β'-cocycle : CechComplex.is1Cocycle S' T' (λ _ → ℤAbGroup) β'

  module ScottIntCodomainModule where
    open import StoneSpaces.Spectrum using (Sp; Booleω; SpGeneralBooleanRing; Stone; hasStoneStr)
    open import Cubical.Data.Int using (ℤ; pos; negsuc; abs; isSetℤ)
    open import Cubical.Data.Nat.Order using (_<_; suc-<)
    open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ)
    open import Cubical.Foundations.Equiv using (invEq; equivFun)
    open import Cubical.Data.FinSet.Constructors using (isFinSet⊎)
    open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
    open import Cubical.Data.FinSet.Properties using (isFinSetFin; EquivPresIsFinSet)
    open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
    import Cubical.Data.Fin.Base as FinBase
    import Cubical.Data.Sum as ⊎
    open import Cubical.HITs.PropositionalTruncation as PT
    open ODiscAxioms
    open MapsStoneToNareBoundedModule

    ScottIntCodomain : (B : Booleω) (rd : ODiscRingDecomp (fst B))
      → (f : Sp B → ℤ)
      → ∥ Σ[ N ∈ ℕ ] Σ[ f' ∈ (SpGeneralBooleanRing (ODiscRingDecomp.BN rd N) → ℤ) ]
          ((x : Sp B) → f x ≡ f' (SpProjection rd N x)) ∥₁
    ScottIntCodomain B rd f =
      PT.rec squash₁ go (MapsStoneToNareBounded spB (λ s → abs (f s))) where
      spB : Stone
      spB = Sp B , B , refl
      go : Σ[ M ∈ ℕ ] ((s : Sp B) → abs (f s) < M) → _
      go (M , bound) = PT.map recover
        (ScottFiniteCodomain B rd F finF isSetF f') where
        open import Cubical.Data.FinSet using (FinSet)
        BFin : ℕ → Type ℓ-zero
        BFin = FinBase.Fin
        F = BFin M ⊎.⊎ BFin M
        finBFin : (n : ℕ) → isFinSet (BFin n)
        finBFin n = EquivPresIsFinSet (SumFin≃Fin n) isFinSetFin
        FM : FinSet ℓ-zero
        FM = BFin M , finBFin M
        finF : isFinSet F
        finF = isFinSet⊎ FM FM
        isSetF : isSet F
        isSetF = isFinSet→isSet finF
        embed : (z : ℤ) → abs z < M → F
        embed (pos n) h = ⊎.inl (n , <→<ᵗ h)
        embed (negsuc n) h = ⊎.inr (n , <→<ᵗ (suc-< h))
        unembed : F → ℤ
        unembed (⊎.inl (n , _)) = pos n
        unembed (⊎.inr (n , _)) = negsuc n
        round-trip : (z : ℤ) (h : abs z < M) → unembed (embed z h) ≡ z
        round-trip (pos _) _ = refl
        round-trip (negsuc _) _ = refl
        f' : Sp B → F
        f' s = embed (f s) (bound s)
        recover : Σ[ N ∈ ℕ ] Σ[ g ∈ (SpGeneralBooleanRing (ODiscRingDecomp.BN rd N) → F) ]
                    ((x : Sp B) → f' x ≡ g (SpProjection rd N x))
               → Σ[ N ∈ ℕ ] Σ[ g' ∈ (SpGeneralBooleanRing (ODiscRingDecomp.BN rd N) → ℤ) ]
                    ((x : Sp B) → f x ≡ g' (SpProjection rd N x))
        recover (N , g , g-ok) = N , (λ ψ → unembed (g ψ)) , λ x →
          f x
            ≡⟨ sym (round-trip (f x) (bound x)) ⟩
          unembed (f' x)
            ≡⟨ cong unembed (g-ok x) ⟩
          unembed (g (SpProjection rd N x)) ∎

  -- tex Lemma 2843 + ScottFiniteCodomain (tex 1558):
  module FiniteApproximationProof where
    open ODiscAxioms
    open StoneSigmaClosedModule
    open import StoneSpaces.Spectrum using (Sp; Booleω; SpGeneralBooleanRing)

    finite-approximation : (S : Type ℓ-zero) (T : S → Type ℓ-zero)
      → hasStoneStr S → ((x : S) → hasStoneStr (T x)) → ((x : S) → ∥ T x ∥₁)
      → (β : CechComplex.C¹ S T (λ _ → ℤAbGroup))
      → CechComplex.is1Cocycle S T (λ _ → ℤAbGroup) β
      → ∥ FiniteApprox S T β ∥₁
    finite-approximation S T stoneS stoneT inh β cocyc =
      PT.rec squash₁ step2 (BooleωRingDecomp B-S) where
      open import Cubical.HITs.PropositionalTruncation as PT
      SStone : Stone
      SStone = S , stoneS
      B-S : Booleω
      B-S = fst stoneS
      eqS : Sp B-S ≡ S
      eqS = snd stoneS
      step2 : ODiscRingDecomp (fst B-S) → ∥ FiniteApprox S T β ∥₁
      step2 rdS = PT.rec squash₁ (step3 rdS) (BooleωRingDecomp B-E) where
        TStone : (x : S) → Stone
        TStone x = T x , stoneT x
        E : Type ℓ-zero
        E = Σ S T
        stoneE : hasStoneStr E
        stoneE = StoneSigmaClosed SStone TStone
        B-E : Booleω
        B-E = fst stoneE
        eqE : Sp B-E ≡ E
        eqE = snd stoneE
        step3 : ODiscRingDecomp (fst B-S) → ODiscRingDecomp (fst B-E)
          → ∥ FiniteApprox S T β ∥₁
        step3 rdS rdE =
          PT.rec squash₁ (step4 rdS rdE) (BooleωRingDecomp B-FP)
          where
            open import Cubical.Foundations.Transport using (transportTransport⁻)
            open import Cubical.Foundations.Equiv using (invEq; secEq; equivFun)
            open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
            open import Cubical.HITs.SequentialColimit.Properties using (SeqColim→Prop)
            open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
            open import Cubical.Data.FinSet.Constructors
              using (isFinSetFiber; isFinSetΣ; isFinSet∥∥; isFinSet×)
            import Cubical.Data.Int as ℤInt
            open ℤInt using (ℤ)
            open import Cubical.Data.FinSet.FiniteChoice as FC using (choice)
            open import Cubical.Algebra.CommRing using (CommRingHom≡)
            FP : Type ℓ-zero
            FP = Σ S (λ x → T x × T x)
            stoneTT : (x : S) → hasStoneStr (T x × T x)
            stoneTT x = StoneProductModule.StoneProduct (T x , stoneT x) (T x , stoneT x)
            stoneFP : hasStoneStr FP
            stoneFP = StoneSigmaClosed SStone (λ x → T x × T x , stoneTT x)
            B-FP : Booleω
            B-FP = fst stoneFP
            eqFP : Sp B-FP ≡ FP
            eqFP = snd stoneFP
            step4 : ODiscRingDecomp (fst B-S) → ODiscRingDecomp (fst B-E)
              → ODiscRingDecomp (fst B-FP) → ∥ FiniteApprox S T β ∥₁
            step4 rdS rdE rdFP =
              PT.rec2 squash₁ stepAB
                (ScottFiniteCodomain B-E rdE S'₀ finS'₀ isSetS'₀ q₀)
                (ScottIntCodomainModule.ScottIntCodomain B-FP rdFP β̃∘tr)
              where
              open ODiscRingDecomp rdS
                renaming (BN to BN-S; isFinSetBN to finS)
              open ODiscRingDecomp rdE
                renaming (BN to BN-E; isFinSetBN to finE;
                          colimEquiv to colimEquivE; colimEquiv-incl to colimEquiv-inclE;
                          fwdHom to fwdHomE)
              N₀ : ℕ
              N₀ = 0
              S'₀ : Type ℓ-zero
              S'₀ = SpGeneralBooleanRing (BN-S N₀)
              finS'₀ : isFinSet S'₀
              finS'₀ = isFinSetSpFinRing (BN-S N₀) (finS N₀)
              isSetS'₀ : isSet S'₀
              isSetS'₀ = isFinSet→isSet finS'₀
              π₀ : S → S'₀
              π₀ x = SpProjection rdS N₀ (transport⁻ eqS x)
              q₀ : SpGeneralBooleanRing (fst B-E) → S'₀
              q₀ φ = π₀ (fst (transport eqE φ))
              β̃∘tr : SpGeneralBooleanRing (fst B-FP) → ℤ
              β̃∘tr ψ = let fp = transport eqFP ψ in β (fst fp) (fst (snd fp)) (snd (snd fp))
              SpProj-sep : (φ₁ φ₂ : SpGeneralBooleanRing (fst B-E))
                → ((n : ℕ) → SpProjection rdE n φ₁ ≡ SpProjection rdE n φ₂) → φ₁ ≡ φ₂
              SpProj-sep φ₁ φ₂ allEq = CommRingHom≡ (funExt pointwise) where
                pointwise : (q : ⟨ fst B-E ⟩) → fst φ₁ q ≡ fst φ₂ q
                pointwise q = subst (λ z → fst φ₁ z ≡ fst φ₂ z) (secEq colimEquivE q)
                  (SeqColim→Prop {B = λ c → fst φ₁ (equivFun colimEquivE c)
                                            ≡ fst φ₂ (equivFun colimEquivE c)}
                    (λ _ → isSetBool _ _)
                    (λ n x →
                      fst φ₁ (equivFun colimEquivE (incl x))
                        ≡⟨ cong (fst φ₁) (colimEquiv-inclE n x) ⟩
                      fst φ₁ (fst (fwdHomE n) x)
                        ≡⟨ funExt⁻ (cong fst (allEq n)) x ⟩
                      fst φ₂ (fst (fwdHomE n) x)
                        ≡⟨ cong (fst φ₂) (sym (colimEquiv-inclE n x)) ⟩
                      fst φ₂ (equivFun colimEquivE (incl x)) ∎)
                    (invEq colimEquivE q))
              stepAB : Σ[ N₁ ∈ ℕ ] Σ[ q' ∈ (SpGeneralBooleanRing (BN-E N₁) → S'₀) ]
                         ((φ : SpGeneralBooleanRing (fst B-E)) → q₀ φ ≡ q' (SpProjection rdE N₁ φ))
                → Σ[ N₂ ∈ ℕ ] Σ[ β̃' ∈ (SpGeneralBooleanRing (ODiscRingDecomp.BN rdFP N₂) → ℤ) ]
                         ((ψ : SpGeneralBooleanRing (fst B-FP)) → β̃∘tr ψ ≡ β̃' (SpProjection rdFP N₂ ψ))
                → ∥ FiniteApprox S T β ∥₁
              stepAB (N₁ , q' , q'-ok) (N₂ , β̃' , β̃'-ok) =
                PT.rec squash₁ useRef
                  (FC.choice (_ , finS') T' inh')
                where
                E'N : Type ℓ-zero
                E'N = SpGeneralBooleanRing (BN-E N₁)
                finE'N : isFinSet E'N
                finE'N = isFinSetSpFinRing (BN-E N₁) (finE N₁)
                S' : Type ℓ-zero
                S' = Σ[ s' ∈ S'₀ ] ∥ Σ[ e' ∈ E'N ] q' e' ≡ s' ∥₁
                finS' : isFinSet S'
                finS' = isFinSetΣ (_ , finS'₀)
                  (λ s' → _ , isFinSet∥∥ (_ , isFinSetFiber (_ , finE'N) (_ , finS'₀) q' s'))
                T' : S' → Type ℓ-zero
                T' (s' , _) = Σ[ e' ∈ E'N ] q' e' ≡ s'
                finT' : (s' : S') → isFinSet (T' s')
                finT' (s' , _) = isFinSetFiber (_ , finE'N) (_ , finS'₀) q' s'
                inh' : (s' : S') → ∥ T' s' ∥₁
                inh' (_ , h) = h
                τ-lem : (x : S) (u : T x)
                  → q' (SpProjection rdE N₁ (transport⁻ eqE (x , u))) ≡ π₀ x
                τ-lem x u =
                  q' (SpProjection rdE N₁ (transport⁻ eqE (x , u)))
                    ≡⟨ sym (q'-ok (transport⁻ eqE (x , u))) ⟩
                  q₀ (transport⁻ eqE (x , u))
                    ≡⟨ cong (λ z → π₀ (fst z)) (transportTransport⁻ eqE (x , u)) ⟩
                  π₀ x ∎
                π : S → S'
                π x = π₀ x , PT.rec squash₁
                  (λ u → ∣ SpProjection rdE N₁ (transport⁻ eqE (x , u)) , τ-lem x u ∣₁)
                  (inh x)
                τ : (x : S) → T x → T' (π x)
                τ x u = SpProjection rdE N₁ (transport⁻ eqE (x , u)) , τ-lem x u
                -- tex Corollary 1590 (scott-continuity): cocycle factors through E-level.
                cocycleFactorsE : ∥ Σ[ fE ∈ (E'N → ℤ) ]
                  ((x : S) (u v : T x) → β x u v
                    ≡ ℤInt._-_ (fE (τ x v .fst)) (fE (τ x u .fst))) ∥₁
                cocycleFactorsE = ∣ fE , fE-ok ∣₁ where
                  postulate
                    fE : E'N → ℤ
                    fE-ok : (x : S) (u v : T x) → β x u v
                      ≡ ℤInt._-_ (fE (τ x v .fst)) (fE (τ x u .fst))
                useRef : ((s' : S') → T' s') → ∥ FiniteApprox S T β ∥₁
                useRef w = PT.rec squash₁ construct cocycleFactorsE
                  where
                  construct : Σ[ fE ∈ (E'N → ℤ) ]
                      ((x : S) (u v : T x) → β x u v
                        ≡ ℤInt._-_ (fE (τ x v .fst)) (fE (τ x u .fst)))
                    → ∥ FiniteApprox S T β ∥₁
                  construct (fE , fE-ok) = ∣ record
                    { S' = S'
                    ; T' = T'
                    ; finS' = finS'
                    ; finT' = finT'
                    ; inh' = inh'
                    ; π = π
                    ; τ = τ
                    ; β' = β'def
                    ; β-factors = β-fac
                    ; β'-cocycle = β'-coc
                    } ∣₁ where
                    open CechComplex S' T' (λ _ → ℤAbGroup)
                      renaming (C⁰ to C⁰'; C¹ to C¹'; d₀ to d₀'; is1Cocycle to is1Cocycle')
                    α' : C⁰'
                    α' (_ , _) (e' , _) = fE e'
                    β'def : C¹'
                    β'def = d₀' α'
                    β-fac : (x : S) (u v : T x) → β x u v ≡ β'def (π x) (τ x u) (τ x v)
                    β-fac x u v = fE-ok x u v
                    β'-coc : is1Cocycle' β'def
                    β'-coc s' u' v' w' = CechComplex.d₁∘d₀≡0 S' T' (λ _ → ℤAbGroup) α' s' u' v' w'

  open FiniteApproximationProof

  colimit-arg : (S : Type ℓ-zero) (T : S → Type ℓ-zero)
    → hasStoneStr S → ((x : S) → hasStoneStr (T x)) → ((x : S) → ∥ T x ∥₁)
    → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)
  colimit-arg S T stoneS stoneT inh β cocyc =
    PT.rec squash₁ use-approx
      (finite-approximation S T stoneS stoneT inh β cocyc)
    where
    open import Cubical.HITs.PropositionalTruncation as PT
    use-approx : FiniteApprox S T β → ∥ CechComplex.is1Coboundary S T (λ _ → ℤAbGroup) β ∥₁
    use-approx fa = PT.map lift-coboundary finite-coboundary
      where
      open FiniteApprox fa
      finite-coboundary : ∥ CechComplex.is1Coboundary S' T' (λ _ → ℤAbGroup) β' ∥₁
      finite-coboundary = cech-vanishing-finite S' T' finS' finT' inh' β' β'-cocycle
      lift-coboundary : CechComplex.is1Coboundary S' T' (λ _ → ℤAbGroup) β'
        → CechComplex.is1Coboundary S T (λ _ → ℤAbGroup) β
      lift-coboundary (α' , d₀α'≡β') = α , funExt (λ x → funExt λ u → funExt λ v → prove x u v)
        where
        α : CechComplex.C⁰ S T (λ _ → ℤAbGroup)
        α x u = α' (π x) (τ x u)
        prove : (x : S) (u v : T x)
          → CechComplex.d₀ S T (λ _ → ℤAbGroup) α x u v ≡ β x u v
        prove x u v =
          CechComplex.d₀ S T (λ _ → ℤAbGroup) α x u v
            ≡⟨ funExt⁻ (funExt⁻ (funExt⁻ d₀α'≡β' (π x)) (τ x u)) (τ x v) ⟩
          β' (π x) (τ x u) (τ x v)
            ≡⟨ sym (β-factors x u v) ⟩
          β x u v ∎

  cech-complex-vanishing-stone : (S : Type ℓ-zero) (T : S → Type ℓ-zero)
    → hasStoneStr S
    → ((x : S) → hasStoneStr (T x))
    → ((x : S) → ∥ T x ∥₁)
    → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)
  cech-complex-vanishing-stone = colimit-arg

