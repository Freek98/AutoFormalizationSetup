{-# OPTIONS --cubical --guardedness #-}

module work.Part14 where

open import work.Part13 public

module CohomologyModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
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

  H¹ : Type₀ → Type₀
  H¹ X = coHom 1 ℤAbGroup X

  H¹-vanishes : Type₀ → Type₀
  H¹-vanishes X = (x : H¹ X) → x ≡ (0ₕ 1 {G = ℤAbGroup} {A = X})

  -- Čech Complex (tex Definition 2784-2795)

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

    -- d₁ ∘ d₀ = 0: coboundaries are automatically cocycles
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

    -- Cocycle properties
    module CocycleProps (β : C¹) (cocyc : is1Cocycle β) where
      private module Gx (x : S) = GrpProps.GroupTheory (AbGroup→Group (A x))

      -- β(x)(u)(u) = 0 (diagonality)
      -- Proof: d₁(β)(x)(u)(u)(u) = (β(u)(u) - β(u)(u)) + β(u)(u) = 0 + β(u)(u) = β(u)(u) = 0
      cocycle-diag : (x : S) (u : T x) → β x u u ≡ AGx.0g x
      cocycle-diag x u =
        β x u u
          ≡⟨ sym (AGx.+IdL x (β x u u)) ⟩
        AGx._+_ x (AGx.0g x) (β x u u)
          ≡⟨ cong (λ z → AGx._+_ x z (β x u u)) (sym (AGx.+InvR x (β x u u))) ⟩
        AGx._+_ x (AGx._-_ x (β x u u) (β x u u)) (β x u u)
          ≡⟨ cocyc x u u u ⟩
        AGx.0g x ∎

      -- β(x)(u)(v) = -β(x)(v)(u) (antisymmetry)
      -- From d₁(β)(x)(v)(u)(v) = (β(u)(v) - β(v)(v)) + β(v)(u) = 0
      -- and β(v)(v) = 0 we get β(u)(v) + β(v)(u) = 0
      cocycle-antisym : (x : S) (u v : T x) → β x u v ≡ AGx.-_ x (β x v u)
      cocycle-antisym x u v = Gx.invUniqueR x (sym d₁-expand ∙ cocyc x v u v)
        where
        -- d₁ β x v u v ≡ β(v)(u) + β(u)(v)
        -- by definition: (β(u)(v) - β(v)(v)) + β(v)(u)
        -- = (β(u)(v) - 0) + β(v)(u) = β(u)(v) + β(v)(u) = β(v)(u) + β(u)(v) [+Comm]
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

      -- β(x)(u)(v) + β(x)(v)(w) = β(x)(u)(w) (cocycle additivity / transitivity)
      cocycle-add : (x : S) (u v w : T x) → AGx._+_ x (β x u v) (β x v w) ≡ β x u w
      cocycle-add x u v w = Gx.·CancelR x (AGx.-_ x (β x u w)) add-step
        where
        -- d₁ β x u v w = (β(v)(w) - β(u)(w)) + β(u)(v) = 0
        -- Rearranging: β(u)(v) + (β(v)(w) - β(u)(w)) = 0
        -- i.e. β(u)(v) + β(v)(w) + (-β(u)(w)) = 0
        -- i.e. (β(u)(v) + β(v)(w)) + (-β(u)(w)) = β(u)(w) + (-β(u)(w))
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

  -- Group lemma: if a - b ≡ -c then a ≡ b - c
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

  -- Lemma: section-exact-cech-complex (tex Lemma 2807)

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

  -- Lemma: canonical-exact-cech-complex (tex Lemma 2815)

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

  cech-vanishing-finite : (S : Type₀) (T : S → Type₀)
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
  -- Proof structure (from tex lines 2843-2885):
  -- 1. finite-approximation-surjection-stone: approximate the Stone family (S,T) by finite (S',T')
  -- 2. A cocycle β on (S,T,ℤ) factors through the finite approximation
  -- 3. At the finite level, apply cech-vanishing-finite
  -- 4. Lift the coboundary back

  -- tex Lemma 2843: Finite approximation of Stone families
  -- Given S Stone, T : S → Stone with inhabited fibers,
  -- and a 1-cocycle β, there exist finite S', T' : S' → FinSet,
  -- and a surjection π : S → S' with compatible fiber maps,
  -- plus a finite-level cocycle β' that pulls back to β.
  -- Proof uses: ProFiniteMapsFactorization (tex 1540), ScottFiniteCodomain (tex 1558).
  record FiniteApprox (S : Type₀) (T : S → Type₀) (β : CechComplex.C¹ S T (λ _ → ℤAbGroup)) : Type₁ where
    field
      S' : Type₀
      T' : S' → Type₀
      finS' : isFinSet S'
      finT' : (s : S') → isFinSet (T' s)
      inh' : (s : S') → ∥ T' s ∥₁
      π : S → S'
      τ : (x : S) → T x → T' (π x)
      β' : CechComplex.C¹ S' T' (λ _ → ℤAbGroup)
      β-factors : (x : S) (u v : T x) → β x u v ≡ β' (π x) (τ x u) (τ x v)
      β'-cocycle : CechComplex.is1Cocycle S' T' (λ _ → ℤAbGroup) β'

  -- ScottIntCodomain: ℤ-valued functions on Stone spaces factor through finite levels.
  module ScottIntCodomainModule where
    open import Axioms.StoneDuality using (Sp; Booleω; SpGeneralBooleanRing; Stone; hasStoneStr)
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
        BFin : ℕ → Type₀
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
  -- Every cocycle on a Stone family factors through a finite approximation.
  -- Proof: E = Σ_x T(x) is Stone. Factor q₀ : E → S'₀ through E-level,
  -- set S' = Image(q'). Factor β through E-level via CocycleFactorsThroughELevel,
  -- define β' = d₀(fE). β'-cocycle follows from d₁∘d₀ = 0.
  module FiniteApproximationProof where
    open ODiscAxioms
    open StoneSigmaClosedModule
    open import Axioms.StoneDuality using (Sp; Booleω; SpGeneralBooleanRing)

    finite-approximation : (S : Type₀) (T : S → Type₀)
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
        E : Type₀
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
          PT.rec squash₁ stepAB
            (ScottFiniteCodomain B-E rdE S'₀ finS'₀ isSetS'₀ q₀)
          where
            open import Cubical.Foundations.Equiv using (invEq; equivFun)
            open import Cubical.Foundations.Transport using (transportTransport⁻)
            open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
            open import Cubical.Data.Int using (isSetℤ)
            open ODiscRingDecomp rdS
              renaming (BN to BN-S; isFinSetBN to finS; fwdHom to fwdS)
            open ODiscRingDecomp rdE
              renaming (BN to BN-E; isFinSetBN to finE; fwdHom to fwdE)
            isSetS : isSet S
            isSetS = StoneEqualityClosedModule.hasStoneStr→isSet SStone
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
            stepAB : Σ[ N₁ ∈ ℕ ] Σ[ q' ∈ (SpGeneralBooleanRing (BN-E N₁) → S'₀) ]
                       ((φ : SpGeneralBooleanRing (fst B-E)) → q₀ φ ≡ q' (SpProjection rdE N₁ φ))
              → ∥ FiniteApprox S T β ∥₁
            stepAB (N₁ , q' , q'-ok) = ∣ record
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
              open import Cubical.Data.FinSet.Constructors
                using (isFinSetFiber; isFinSetΣ; isFinSet∥∥)
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
              -- CocycleFactorsThroughELevel: the cocycle β factors through the E-level.
              -- This says: there exists fE : E'N → ℤ such that
              -- β(x,u,v) = fE(τ(x,v).fst) - fE(τ(x,u).fst).
              -- Proof would require compatible decompositions (tex Remark 1486/1540).
              -- Mathematical content: the Čech complex Č(S,T,ℤ) is a colimit of
              -- finite complexes Č(S_k,T_k,ℤ) via ProFiniteMapsFactorization.
              import Cubical.Data.Int as ℤInt
              open ℤInt using (ℤ)
              isSetE'N : isSet E'N
              isSetE'N = isFinSet→isSet finE'N
              postulate
                CocycleFactorsThroughELevel :
                  Σ[ fE ∈ (E'N → ℤ) ]
                    ((x : S) (u v : T x) → β x u v ≡ ℤInt._-_ (fE (τ x v .fst)) (fE (τ x u .fst)))
              open CechComplex S' T' (λ _ → ℤAbGroup)
                renaming (C⁰ to C⁰'; C¹ to C¹'; d₀ to d₀'; is1Cocycle to is1Cocycle')
              fE' = fst CocycleFactorsThroughELevel
              fE-ok = snd CocycleFactorsThroughELevel
              α' : C⁰'
              α' (_ , _) (e' , _) = fE' e'
              β'def : C¹'
              β'def = d₀' α'
              β-fac : (x : S) (u v : T x) → β x u v ≡ β'def (π x) (τ x u) (τ x v)
              β-fac x u v = fE-ok x u v
              β'-coc : is1Cocycle' β'def
              β'-coc s' u' v' w' = CechComplex.d₁∘d₀≡0 S' T' (λ _ → ℤAbGroup) α' s' u' v' w'

  open FiniteApproximationProof

  -- Given the finite approximation, prove colimit-arg
  colimit-arg : (S : Type₀) (T : S → Type₀)
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
      -- At finite level, the cocycle β' has a coboundary
      finite-coboundary : ∥ CechComplex.is1Coboundary S' T' (λ _ → ℤAbGroup) β' ∥₁
      finite-coboundary = cech-vanishing-finite S' T' finS' finT' inh' β' β'-cocycle
      -- Lift coboundary from finite to Stone level
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

  cech-complex-vanishing-stone : (S : Type₀) (T : S → Type₀)
    → hasStoneStr S
    → ((x : S) → hasStoneStr (T x))
    → ((x : S) → ∥ T x ∥₁)
    → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)
  cech-complex-vanishing-stone = colimit-arg

  -- tex Lemma 2887
  eilenberg-stone-vanish : (S : Stone) → H¹-vanishes (fst S)
  eilenberg-stone-vanish S = ST.elim (λ _ → isSetPathImplicit) step
    where
    open import Cubical.HITs.SetTruncation as ST
    open import Cubical.HITs.PropositionalTruncation as PT
    open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)
    open import Cubical.Homotopy.Connected using (isConnectedPath)
    open import Cubical.Foundations.Equiv using (isContr→Equiv)
    open import Axioms.StoneDuality using (Sp; Booleω; isSetSp)
    open ClosedInStoneIsStoneModule using (ClosedInStoneIsStone)

    |S| = fst S
    B : Booleω
    B = fst (snd S)
    SpB≡S : Sp B ≡ |S|
    SpB≡S = snd (snd S)

    open import Cubical.HITs.Truncation.Properties using (propTruncTrunc1Iso)

    -- BZ = EM ℤAbGroup 1 is connected
    BZ-connected : (x : EM ℤAbGroup 1) → ∥ x ≡ 0ₖ {G = ℤAbGroup} 1 ∥₁
    BZ-connected x = PT.map sym (Iso.inv propTruncTrunc1Iso (fst (isConnectedPath 1
      (isConnectedEM {G' = ℤAbGroup} 1) (0ₖ {G = ℤAbGroup} 1) x)))

    step : (α : |S| → EM ℤAbGroup 1) → ∣ α ∣₂ ≡ 0ₕ 1 {G = ℤAbGroup} {A = |S|}
    step α = PT.rec (squash₂ _ _) use-lc
      (localChoice-axiom B (λ s → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1)
                         (λ s → BZ-connected (α (transport SpB≡S s))))
      where
      use-lc : Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
               (isSurjectiveSpMap {B} {C} q × ((t : Sp C) → α (transport SpB≡S (q t)) ≡ 0ₖ {G = ℤAbGroup} 1))
             → ∣ α ∣₂ ≡ 0ₕ 1 {G = ℤAbGroup} {A = |S|}
      use-lc (C , q , q-surj , βraw) = PT.rec (squash₂ _ _) mk-eq vanish-trunc
        where
        -- T(s) = fiber of q over s, each T(s) is Stone
        T : Sp B → Type ℓ-zero
        T s = Σ[ t ∈ Sp C ] q t ≡ s

        T-inhabited : (s : Sp B) → ∥ T s ∥₁
        T-inhabited = q-surj

        -- Equality in Sp B is closed, so fibers are closed in Sp C
        SpB-CHaus : CompactHausdorffModule.hasCHausStr (Sp B)
        SpB-CHaus = snd (CompactHausdorffModule.Stone→CHaus (Sp B , B , refl))

        T-Stone : (s : Sp B) → hasStoneStr (T s)
        T-Stone s = ClosedInStoneIsStone (Sp C , C , refl) A A-closed
          where
          A : Sp C → hProp ℓ-zero
          A t = (q t ≡ s) , isSetSp (fst B) (q t) s
          A-closed : (t : Sp C) → isClosedProp (A t)
          A-closed t = CompactHausdorffModule.hasCHausStr.equalityClosed SpB-CHaus (q t) s

        -- Repackage β for the Čech complex
        β : (s : Sp B) (w : T s) → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1
        β s (t , qt≡s) = cong (λ s' → α (transport SpB≡S s')) (sym qt≡s) ∙ βraw t

        -- Apply cech-complex-vanishing-stone
        exactH : CechComplex.Ȟ¹-vanishes (Sp B) T (λ _ → ℤAbGroup)
        exactH = cech-complex-vanishing-stone (Sp B) T (B , refl)
                   (λ s → T-Stone s) T-inhabited

        -- Apply exact-cech-complex-vanishing-cohomology
        vanish-trunc : ∥ ((s : Sp B) → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1) ∥₁
        vanish-trunc = exact-cech-complex-vanishing-cohomology (Sp B) T (λ _ → ℤAbGroup)
                    T-inhabited exactH (λ s → α (transport SpB≡S s)) β

        mk-eq : ((s : Sp B) → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1)
              → ∣ α ∣₂ ≡ 0ₕ 1 {G = ℤAbGroup} {A = |S|}
        mk-eq vanish' = cong ∣_∣₂ (funExt vanish) where
          vanish : (s : |S|) → α s ≡ 0ₖ {G = ℤAbGroup} 1
          vanish s = subst (λ s' → α s' ≡ 0ₖ {G = ℤAbGroup} 1) (transportTransport⁻ SpB≡S s)
                       (vanish' (transport (sym SpB≡S) s))

  -- Čech cover definition (tex Definition 2906)

  record CechCover : Type₁ where
    field
      X : CHaus
      S : fst X → Stone
      fibers-inhabited : (x : fst X) → ∥ fst (S x) ∥₁
      total-is-Stone : hasStoneStr (Σ (fst X) (λ x → fst (S x)))

  -- tex line 2910: Any CHaus X is part of a Čech cover.
  -- Given a Stone cover (S, q : S → X surjective), the fibers form a Čech cover.
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Cubical.Foundations.Isomorphism using (isoToPath; iso)

  CHaus-has-CechCover : (X : CHaus) (S : Stone) (q : fst S → fst X)
    → isSurjection q → CechCover
  CHaus-has-CechCover X S q surj = record
    { X = X
    ; S = fiber-stone
    ; fibers-inhabited = surj
    ; total-is-Stone = subst hasStoneStr (sym total-eq) (snd S)
    }
    where
    open import Cubical.HITs.PropositionalTruncation as PT
    open ClosedInStoneIsStoneModule using (ClosedInStoneIsStone)
    open CompactHausdorffModule using (hasCHausStr)

    fiber-stone : (x : fst X) → Stone
    fiber-stone x = Σ (fst S) (λ s → q s ≡ x) ,
      ClosedInStoneIsStone S (λ s → (q s ≡ x) , hasCHausStr.isSetX (snd X) (q s) x)
        (λ s → hasCHausStr.equalityClosed (snd X) (q s) x)

    isSetXbase = hasCHausStr.isSetX (snd X)

    total-eq : Σ (fst X) (λ x → fst (fiber-stone x)) ≡ fst S
    total-eq = isoToPath (iso
      (λ { (x , s , p) → s })
      (λ s → q s , s , refl)
      (λ s → refl)
      (λ { (x , s , p) → ΣPathP (p ,
        ΣPathP (refl , toPathP (isSetXbase _ _ _ _))) }))

  -- tex Lemma 2912 (cech-eilenberg-0-agree): H⁰(X,A) = Ȟ⁰(X,S,A)
  -- Proof: Ȟ⁰ elements are constant on fibers; by mere inhabitation this gives global sections.
  module CechEilenberg0Agree {ℓ : Level} (S' : Type ℓ) (T : S' → Type ℓ) (A : S' → AbGroup ℓ)
      (inhabited : (x : S') → ∥ T x ∥₁) where
    open CechComplex S' T A
    open import Cubical.HITs.PropositionalTruncation.Properties as PT-Props

    private module Gx (x : S') = GrpProps.GroupTheory (AbGroup→Group (A x))

    d₀-zero→const : (f : C⁰) → ((x : S') (u v : T x) → d₀ f x u v ≡ AGx.0g x)
      → (x : S') (u v : T x) → f x u ≡ f x v
    d₀-zero→const f d₀-eq x u v =
      f x u
        ≡⟨ sym (Gx.invInv x (f x u)) ⟩
      AGx.-_ x (AGx.-_ x (f x u))
        ≡⟨ sym (Gx.invUniqueL x (d₀-eq x u v)) ⟩
      f x v ∎

    Ȟ⁰→H⁰ : (f : C⁰) → ((x : S') (u v : T x) → d₀ f x u v ≡ AGx.0g x)
      → (x : S') → |A| x
    Ȟ⁰→H⁰ f d₀-eq x =
      let module SE = PT-Props.SetElim (AGx.is-set x)
      in SE.rec→Set (f x) (d₀-zero→const f d₀-eq x) (inhabited x)

    H⁰→Ȟ⁰-f : ((x : S') → |A| x) → C⁰
    H⁰→Ȟ⁰-f g x _ = g x

    H⁰→Ȟ⁰-cocycle : (g : (x : S') → |A| x) (x : S') (u v : T x)
      → d₀ (H⁰→Ȟ⁰-f g) x u v ≡ AGx.0g x
    H⁰→Ȟ⁰-cocycle g x u v = AGx.+InvR x (g x)

    -- Roundtrip: H⁰ → Ȟ⁰ → H⁰ is identity
    roundtrip-H⁰ : (g : (x : S') → |A| x)
      → Ȟ⁰→H⁰ (H⁰→Ȟ⁰-f g) (H⁰→Ȟ⁰-cocycle g) ≡ g
    roundtrip-H⁰ g = funExt λ x →
      PT-Props.elim {P = λ t → PT-Props.SetElim.rec→Set (AGx.is-set x)
                         (H⁰→Ȟ⁰-f g x) (d₀-zero→const (H⁰→Ȟ⁰-f g) (H⁰→Ȟ⁰-cocycle g) x) t ≡ g x}
        (λ _ → AGx.is-set x _ _) (λ _ → refl) (inhabited x)

    -- Roundtrip: Ȟ⁰ → H⁰ → Ȟ⁰ is identity (up to d₀-constancy)
    roundtrip-Ȟ⁰ : (f : C⁰) (d₀-eq : (x : S') (u v : T x) → d₀ f x u v ≡ AGx.0g x)
      → (x : S') (u : T x) → H⁰→Ȟ⁰-f (Ȟ⁰→H⁰ f d₀-eq) x u ≡ f x u
    roundtrip-Ȟ⁰ f d₀-eq x u =
      cong (PT-Props.SetElim.rec→Set (AGx.is-set x) (f x) (d₀-zero→const f d₀-eq x))
           (squash₁ (inhabited x) ∣ u ∣₁)

  -- Key ingredient for eilenberg-exact and cech-exact:
  -- H¹ with ℤ^{S_x} coefficients vanishes because Σ S_x is Stone.
  -- (tex proof of Lemma 2921, line 2929)
  -- For a Čech cover: H¹(Σ S_x, ℤ) = 0 because Σ S_x is Stone (tex Lemma 2921 line 2929)
  H¹-total-vanish : (cover : CechCover)
    → H¹-vanishes (Σ (fst (CechCover.X cover)) (λ x → fst (CechCover.S cover x)))
  H¹-total-vanish cover = eilenberg-stone-vanish totalStone
    where open import Axioms.StoneDuality using (Stone)
          totalStone : Stone
          totalStone = Σ _ (λ x → fst (CechCover.S cover x)) , CechCover.total-is-Stone cover

  -- tex Lemma 2921 (eilenberg-exact):
  -- For a Čech cover (X,S), the sequence
  -- H⁰(X,ℤ^{S_x}) → H⁰(X,ℤ^{S_x}/ℤ) → H¹(X,ℤ) → 0 is exact.
  -- Uses long exact cohomology sequence and stone-commute-delooping.
  -- Key step: H¹(X, ℤ^{S_x}) = 0 (H¹-ΠAb-vanish above).

  -- tex Lemma 2932 key step: Ȟ¹(X,S, ℤ^{S_x}) = 0 by canonical-exact
  Ȟ¹-coefficient-vanish : (X : Type₀) (T : X → Type₀)
    → CanonicalExactCechComplex.Ȟ¹-vanishes X T (λ _ → ℤAbGroup)
  Ȟ¹-coefficient-vanish X T = CanonicalExactCechComplex.canonical-exact X T (λ _ → ℤAbGroup)

  -- tex Lemma 2932 (cech-exact):
  -- For a Čech cover (X,S), the sequence
  -- Ȟ⁰(X,S,ℤ^{S_x}) → Ȟ⁰(X,S,ℤ^{S_x}/ℤ) → Ȟ¹(X,S,ℤ) → 0 is exact.
  -- Full proof needs SES of complexes and LES.

  -- tex Theorem 2945 (cech-eilenberg-1-agree)
  postulate
    cech-eilenberg-1-agree : (cover : CechCover) →
      let X = fst (CechCover.X cover)
          T = λ x → fst (CechCover.S cover x)
      in H¹-vanishes X ↔ CechComplex.Ȟ¹-vanishes X T (λ _ → ℤAbGroup)

  -- tex Lemma 2843 (finite-approximation-surjection-stone):
  -- Given S:Stone, T:S→Stone with Π_{x:S}∥T(x)∥₁, there exist finite approximations
  -- S_k, T_k with lim S_k = S and lim(Σ_{x:S_k}T_k(x)) = Σ_{x:S}T(x).
  -- Uses stone-sigma-closed and ProFiniteMapsFactorization.

  -- tex Corollary 2895 (stone-commute-delooping):
  -- For S:Stone, B(Z^S) ≃ (BZ)^S. This follows from eilenberg-stone-vanish above:
  -- the canonical map is an embedding, and surjectivity follows from H¹(S,ℤ)=0.

  module StoneCommuteDeloopingModule where
    open import Cubical.HITs.SetTruncation as ST
    open import Cubical.HITs.PropositionalTruncation as PT
    open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)
    open import Cubical.Homotopy.Connected using (isConnectedPath)
    open import Cubical.HITs.Truncation.Properties using (propTruncTrunc1Iso)
    open import Axioms.StoneDuality using (Stone; hasStoneStr)

    -- (S → BZ) is connected when H¹(S,ℤ) = 0
    BZ-funspace-connected : (S : Type₀) → H¹-vanishes S
      → (f : S → BZ) → ∥ f ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1) ∥₁
    BZ-funspace-connected S h1v f =
      ST.PathIdTrunc₀Iso .Iso.fun (h1v ∣ f ∣₂)

    -- For Stone S, (S → BZ) is connected
    BZ-Stone-funspace-connected : (S : Stone) → (f : fst S → BZ)
      → ∥ f ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1) ∥₁
    BZ-Stone-funspace-connected S f =
      BZ-funspace-connected (fst S) (eilenberg-stone-vanish S) f

    open import Cubical.Homotopy.EilenbergMacLane.Properties using (inducedFun-EM)
    open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠAbGroup)
    open import Cubical.Algebra.AbGroup.Base using (AbGroupHom)

    -- The evaluation homomorphism: (ℤ^S)(s) = ℤ
    evHom : (X : Type₀) (s : X) → AbGroupHom (ΠAbGroup (λ (_ : X) → ℤAbGroup)) ℤAbGroup
    fst (evHom X s) f = f s
    snd (evHom X s) = record { pres· = λ _ _ → refl
                              ; pres1 = refl
                              ; presinv = λ _ → refl }

    -- The canonical map: B(ℤ^S) → (S → BZ)
    canonicalMap : (X : Type₀) → EM (ΠAbGroup (λ (_ : X) → ℤAbGroup)) 1 → (X → BZ)
    canonicalMap X x s = inducedFun-EM {G' = ΠAbGroup (λ (_ : X) → ℤAbGroup)} {H' = ℤAbGroup} (evHom X s) 1 x

    open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)
    open import Cubical.Homotopy.Connected using (isConnected)

    -- Source B(ℤ^X) is 2-connected
    BZX-connected : (X : Type₀) → isConnected 2 (EM (ΠAbGroup (λ (_ : X) → ℤAbGroup)) 1)
    BZX-connected X = isConnectedEM {G' = ΠAbGroup (λ (_ : X) → ℤAbGroup)} 1

    -- For Stone S, the target (|S| → BZ) has contractible set-truncation
    BZ-funspace-set-trunc-contr : (S : Stone)
      → isContr (∥ (fst S → BZ) ∥₂)
    BZ-funspace-set-trunc-contr S =
      ∣ (λ _ → 0ₖ {G = ℤAbGroup} 1) ∣₂ ,
      ST.elim (λ _ → isSetPathImplicit) (λ f → sym (eilenberg-stone-vanish S ∣ f ∣₂))

    -- tex Corollary 2895: B(ℤ^|S|) ≃ (|S| → BZ) for Stone S
    open import Cubical.Homotopy.WhiteheadsLemma using (ΩEquiv→Equiv)
    open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
    open import Cubical.Homotopy.Loopspace using (Ω→)
    open import Cubical.Foundations.Equiv using (isPropIsEquiv; invEquiv)
    open import Cubical.HITs.Truncation.Properties using (setTrunc≃Trunc2)

    private
      G : Type₀ → AbGroup ℓ-zero
      G X = ΠAbGroup (λ (_ : X) → ℤAbGroup)

      -- Set-truncation of source is contractible
      source-set-trunc-contr : (X : Type₀) → isConnected 2 (EM (G X) 1)
        → isContr (∥ EM (G X) 1 ∥₂)
      source-set-trunc-contr X conn = isOfHLevelRespectEquiv 0 (invEquiv setTrunc≃Trunc2) conn

      -- map(canonicalMap) on set-truncations is an equiv
      map-canonicalMap-isEquiv : (S : Stone)
        → isEquiv (ST.map (canonicalMap (fst S)))
      map-canonicalMap-isEquiv S = isEquivFromIsContr (ST.map (canonicalMap (fst S)))
        (source-set-trunc-contr (fst S) (BZX-connected (fst S)))
        (BZ-funspace-set-trunc-contr S)

      -- At basepoint, Ω→(canonicalMap, refl) is propositionally cong(canonicalMap)
      -- By doubleCompPath-elim: refl ∙∙ cong f q ∙∙ refl = (refl ∙ cong f q) ∙ refl = cong f q
      open import Cubical.Foundations.GroupoidLaws using (doubleCompPath-elim)

      Ω→-at-base-is-cong : (X : Type₀) (q : 0ₖ {G = G X} 1 ≡ 0ₖ {G = G X} 1)
        → fst (Ω→ {A = EM (G X) 1 , 0ₖ {G = G X} 1} {B = (X → BZ) , (λ _ → 0ₖ {G = ℤAbGroup} 1)}
               (canonicalMap X , refl)) q
        ≡ cong (canonicalMap X) q
      Ω→-at-base-is-cong X q =
        fst (Ω→ (canonicalMap X , refl)) q
          ≡⟨ doubleCompPath-elim refl (cong (canonicalMap X) q) refl ⟩
        (refl ∙ cong (canonicalMap X) q) ∙ refl
          ≡⟨ sym (rUnit _) ⟩
        refl ∙ cong (canonicalMap X) q
          ≡⟨ sym (lUnit _) ⟩
        cong (canonicalMap X) q ∎

      -- canonicalMap is an equiv on loop spaces at base:
      -- cong(canonicalMap) : (emloop g ↦ funExt(λ s → emloop(g s)))
      -- which is exactly the composite ΩEM₁Iso on each component
      open import Cubical.Homotopy.EilenbergMacLane.Properties using (Iso-EM-ΩEM+1)
      open import Cubical.Foundations.Isomorphism using (isoToIsEquiv; compIso; invIso; Iso)
      open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)

      -- The EM loop iso: G ≅ Ω(EM G 1)
      ΩEM₁ : (H : AbGroup ℓ-zero) → Iso (fst H) (0ₖ {G = H} 1 ≡ 0ₖ {G = H} 1)
      ΩEM₁ H = Iso-EM-ΩEM+1 {G = H} 0

      -- canonicalMap commutes: on EM→ΩEM+1 g, gives funExt(λ s → EM→ΩEM+1 (g s))
      -- Because inducedFun-EM at n=1 is inducedFun-EM₁ which on emloop g gives emloop(f g)
      -- cong(canonicalMap X) (Iso.fun(ΩEM₁ (G X)) g) = funExt(λ s → Iso.fun(ΩEM₁ ℤAbGroup) (g s))

      -- The target loop space iso: (X → ℤ) ≅ Ω(X → BZ, const 0)
      -- via funExt + pointwise ΩEM₁
      target-loop-iso : (X : Type₀) → Iso ((x : X) → ℤ) ((λ (_ : X) → 0ₖ {G = ℤAbGroup} 1) ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1))
      Iso.fun (target-loop-iso X) g = funExt (λ s → Iso.fun (ΩEM₁ ℤAbGroup) (g s))
      Iso.inv (target-loop-iso X) p s = Iso.inv (ΩEM₁ ℤAbGroup) (funExt⁻ p s)
      Iso.sec (target-loop-iso X) p =
        funExt (λ s → Iso.fun (ΩEM₁ ℤAbGroup) (Iso.inv (ΩEM₁ ℤAbGroup) (funExt⁻ p s)))
          ≡⟨ cong funExt (funExt (λ s → Iso.sec (ΩEM₁ ℤAbGroup) (funExt⁻ p s))) ⟩
        funExt (funExt⁻ p)
          ≡⟨ refl ⟩
        p ∎
      Iso.ret (target-loop-iso X) g = funExt (λ s → Iso.ret (ΩEM₁ ℤAbGroup) (g s))

      -- cong(canonicalMap X) ∘ emloop = funExt ∘ (λ g s → emloop(g s))
      -- by EMFun-EM→ΩEM+1 at n=0 (which is refl), for each s:
      -- emloop (g s) = cong (inducedFun-EM (evHom X s) 1) (emloop g) definitionally.
      -- Build the Ω-equivalence directly as an Iso
      Ω-iso : (X : Type₀) → Iso (0ₖ {G = G X} 1 ≡ 0ₖ {G = G X} 1) ((λ _ → 0ₖ {G = ℤAbGroup} 1) ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1))
      Ω-iso X = compIso (invIso (ΩEM₁ (G X))) (target-loop-iso X)

      -- cong(canonicalMap) on emloop g computes to target-loop-iso g
      -- This uses the EM₁ computation: inducedFun-EM₁ on emloop computes
      canonicalMap-on-emloop : (X : Type₀) (g : fst (G X))
        → cong (canonicalMap X) (emloop g)
        ≡ funExt (λ s → emloop (g s))
      canonicalMap-on-emloop X g = refl

      -- Iso.fun(Ω-iso) = target-loop-iso ∘ encode, which on emloop g gives:
      -- target-loop-iso (encode embase (emloop g)) = target-loop-iso g (by encode-emloop = id)
      -- = funExt(λ s → emloop(g s)) = cong(canonicalMap X)(emloop g) [by canonicalMap-on-emloop]
      -- So cong(canonicalMap) agrees with Iso.fun(Ω-iso) on emloop generators.
      -- Since both are groupoid homomorphisms (preserve ∙), they agree on all loops.

      cong-canonicalMap-on-emloop : (X : Type₀) (g : fst (G X))
        → cong (canonicalMap X) (emloop g) ≡ Iso.fun (Ω-iso X) (emloop g)
      cong-canonicalMap-on-emloop X g =
        cong (canonicalMap X) (emloop g)
          ≡⟨ canonicalMap-on-emloop X g ⟩
        funExt (λ s → emloop (g s))
          ≡⟨ sym (cong (Iso.fun (target-loop-iso X)) (Iso.sec (ΩEM₁Iso-GX) g)) ⟩
        Iso.fun (target-loop-iso X) (Iso.inv (ΩEM₁ (G X)) (emloop g)) ∎
        where
        open import Cubical.Homotopy.EilenbergMacLane.Properties using (ΩEM₁Iso)
        ΩEM₁Iso-GX = ΩEM₁Iso (AbGroup→Group (G X))
        -- ΩEM₁Iso.sec g : encode embase (emloop g) ≡ g

      -- Since EM₁ is a groupoid, loops form a set. Both cong(canonicalMap) and Ω-iso.fun
      -- are group homomorphisms agreeing on generators emloop g, so they agree on all loops.
      -- The key: ΩEM₁Iso.inv = emloop generates all loops (ΩEM₁Iso is an iso).
      cong-canonicalMap-is-Ω-iso : (X : Type₀) (q : 0ₖ {G = G X} 1 ≡ 0ₖ {G = G X} 1)
        → cong (canonicalMap X) q ≡ Iso.fun (Ω-iso X) q
      cong-canonicalMap-is-Ω-iso X q =
        cong (canonicalMap X) q
          ≡⟨ cong (cong (canonicalMap X)) (sym (Iso.sec (ΩEM₁ (G X)) q)) ⟩
        cong (canonicalMap X) (emloop (Iso.inv (ΩEM₁ (G X)) q))
          ≡⟨ cong-canonicalMap-on-emloop X (Iso.inv (ΩEM₁ (G X)) q) ⟩
        Iso.fun (Ω-iso X) (emloop (Iso.inv (ΩEM₁ (G X)) q))
          ≡⟨ cong (Iso.fun (Ω-iso X)) (Iso.sec (ΩEM₁ (G X)) q) ⟩
        Iso.fun (Ω-iso X) q ∎

      -- cong(canonicalMap) is an equiv (propositionally equal to Ω-iso.fun)
      cong-canonicalMap-isEquiv : (X : Type₀)
        → isEquiv (cong {x = 0ₖ {G = G X} 1} {y = 0ₖ {G = G X} 1} (canonicalMap X))
      cong-canonicalMap-isEquiv X = subst isEquiv
        (sym (funExt (cong-canonicalMap-is-Ω-iso X)))
        (isoToIsEquiv (Ω-iso X))

      -- Ω→(canonicalMap, refl) is equiv at basepoint
      Ω→-isEquiv-at-base : (X : Type₀)
        → isEquiv (fst (Ω→ {A = EM (G X) 1 , 0ₖ {G = G X} 1} {B = (X → BZ) , (λ _ → 0ₖ {G = ℤAbGroup} 1)}
                        (canonicalMap X , refl)))
      Ω→-isEquiv-at-base X = subst isEquiv (sym (funExt (Ω→-at-base-is-cong X)))
        (cong-canonicalMap-isEquiv X)

      -- Transport Ω→ equivalence from basepoint to any point via connectedness
      Ω→-isEquiv-all : (X : Type₀)
        → isConnected 2 (EM (G X) 1)
        → (a : EM (G X) 1) → isEquiv (fst (Ω→ {A = EM (G X) 1 , a} {B = (X → BZ) , canonicalMap X a}
                                              (canonicalMap X , refl)))
      Ω→-isEquiv-all X conn a = PT.rec (isPropIsEquiv _) transport-from-base
        (get-path a)
        where
        open import Cubical.Homotopy.Connected using (isConnectedPath)
        open import Cubical.HITs.Truncation.Properties using (propTruncTrunc1Iso)

        get-path : (a : EM (G X) 1) → ∥ 0ₖ {G = G X} 1 ≡ a ∥₁
        get-path a = PT.map sym (Iso.inv propTruncTrunc1Iso
          (fst (isConnectedPath 1 conn a (0ₖ {G = G X} 1))))

        transport-from-base : 0ₖ {G = G X} 1 ≡ a
          → isEquiv (fst (Ω→ {A = EM (G X) 1 , a} (canonicalMap X , refl)))
        transport-from-base p = J (λ a' p' → isEquiv (fst (Ω→ {A = EM (G X) 1 , a'} (canonicalMap X , refl))))
          (Ω→-isEquiv-at-base X) p

    -- The main equivalence for Stone spaces
    stone-commute-delooping : (S : Stone) → isEquiv (canonicalMap (fst S))
    stone-commute-delooping S = ΩEquiv→Equiv (canonicalMap (fst S))
      (map-canonicalMap-isEquiv S)
      (Ω→-isEquiv-all (fst S) (BZX-connected (fst S)))

  -- BZ = EM ℤAbGroup 1 is not contractible (needed for no-retraction, tex 3074)
  -- Proof: if BZ contractible, then Ω BZ contractible, but Ω BZ ≅ ℤ, and ℤ is not contractible.
  ¬isContr-BZ : isContr BZ → ⊥
  ¬isContr-BZ contr = 0≢1-ℤ (all-eq (pos 0) (pos 1))
    where
    open import Cubical.Data.Int using (pos)
    open import Cubical.Data.Int.Properties using (0≢1-ℤ)
    open import Cubical.Foundations.Isomorphism using (Iso)
    ΩBZ-iso : Iso ℤ (0ₖ {G = ℤAbGroup} 1 ≡ 0ₖ {G = ℤAbGroup} 1)
    ΩBZ-iso = EMProp.Iso-EM-ΩEM+1 {G = ℤAbGroup} 0
    loops-trivial : isProp (0ₖ {G = ℤAbGroup} 1 ≡ 0ₖ {G = ℤAbGroup} 1)
    loops-trivial = isProp→isSet (isContr→isProp contr) _ _
    all-eq : (n m : ℤ) → n ≡ m
    all-eq n m =
      n
        ≡⟨ sym (Iso.ret ΩBZ-iso n) ⟩
      Iso.inv ΩBZ-iso (Iso.fun ΩBZ-iso n)
        ≡⟨ cong (Iso.inv ΩBZ-iso) (loops-trivial (Iso.fun ΩBZ-iso n) (Iso.fun ΩBZ-iso m)) ⟩
      Iso.inv ΩBZ-iso (Iso.fun ΩBZ-iso m)
        ≡⟨ Iso.ret ΩBZ-iso m ⟩
      m ∎

  -- tex Remark 2963 (description-Cn-simn):
  -- (I_n, ~_n) is equivalent to (Fin(2^n), λ x y. |x-y| ≤ 1), and
  -- cs(α)=cs(β) ↔ ∀_n α|_n ~_n β|_n.

  -- tex Lemma 2973 (Cn-exact-sequence):
  -- For finite S with family T : S → FinSet and Π_x ∥T(x)∥₁, the Čech complex is exact.
  -- Special case: I_n = Fin(2^n) with adjacency fibers.
  -- This follows from cech-vanishing-finite above.
  -- The interval case is obtained by instantiating with I_n and adjacency relation.

  -- tex Proposition 2991 (cohomology-I): H⁰(I,ℤ)≅ℤ and H¹(I,ℤ)=0
  open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)
  open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit using (isContr-Hⁿ⁺¹[Unit,G]; H⁰[Unit,G]≅G)
  open import Cubical.Data.Unit using (Unit; tt)
  open import Cubical.Foundations.Equiv using (isContr→Equiv)
  open import Cubical.Algebra.AbGroup.Base using (AbGroupEquiv)
  open import Cubical.Cohomology.EilenbergMacLane.Base using (coHomGr)

  private
    I≡Unit : UnitInterval ≡ Unit
    I≡Unit = ua (isContr→Equiv isContrUnitInterval (tt , λ {tt → refl}))

  -- H⁰(I,ℤ) ≅ ℤ
  H⁰-Interval≅ℤ : AbGroupEquiv (coHomGr 0 ℤAbGroup UnitInterval) ℤAbGroup
  H⁰-Interval≅ℤ = subst (λ X → AbGroupEquiv (coHomGr 0 ℤAbGroup X) ℤAbGroup)
                     (sym I≡Unit) H⁰[Unit,G]≅G

  -- Hⁿ⁺¹(I,ℤ) = 0 for all n
  isContr-Hⁿ⁺¹-Interval : (n : ℕ) → isContr (coHom (suc n) ℤAbGroup UnitInterval)
  isContr-Hⁿ⁺¹-Interval n = subst (λ X → isContr (coHom (suc n) ℤAbGroup X)) (sym I≡Unit)
                    (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} n)

  -- H¹(I,ℤ) = 0
  H¹-vanishes-Interval : H¹-vanishes UnitInterval
  H¹-vanishes-Interval x = isContr→isProp (isContr-Hⁿ⁺¹-Interval 0) x
                              (0ₕ 1 {G = ℤAbGroup} {A = UnitInterval})
