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

  -- tex Lemma 2878
  postulate
    cech-complex-vanishing-stone : (S : Type₀) (T : S → Type₀)
      → hasStoneStr S
      → ((x : S) → hasStoneStr (T x))
      → ((x : S) → ∥ T x ∥₁)
      → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)

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

  -- tex Lemma 2921 (eilenberg-exact):
  -- For a Čech cover (X,S), the sequence
  -- H⁰(X,ℤ^{S_x}) → H⁰(X,ℤ^{S_x}/ℤ) → H¹(X,ℤ) → 0 is exact.
  -- Uses long exact cohomology sequence and stone-commute-delooping.

  -- tex Lemma 2932 (cech-exact):
  -- For a Čech cover (X,S), the sequence
  -- Ȟ⁰(X,S,ℤ^{S_x}) → Ȟ⁰(X,S,ℤ^{S_x}/ℤ) → Ȟ¹(X,S,ℤ) → 0 is exact.
  -- Uses canonical-exact and eilenberg-stone-vanish.

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

  -- tex Remark 2963 (description-Cn-simn):
  -- (I_n, ~_n) is equivalent to (Fin(2^n), λ x y. |x-y| ≤ 1), and
  -- cs(α)=cs(β) ↔ ∀_n α|_n ~_n β|_n.

  -- tex Lemma 2973 (Cn-exact-sequence):
  -- For each n:ℕ, the Cech complex 0→ℤ→ℤ^{I_n}→ℤ^{I_n^{~2}}→ℤ^{I_n^{~3}} is exact.
  -- (I_n = 2^n with the ~_n relation from cs)
  -- This is used to prove cohomology-I via sequential colimit of exact sequences.

  -- tex Proposition 2991 (cohomology-I): H⁰(I,ℤ)=ℤ and H¹(I,ℤ)=0
  -- H⁰(I,ℤ)=ℤ is Z-I-local (Part12): any f:I→ℤ is constant.
  -- H¹(I,ℤ)=0: follows from contractibility of I (Corollary 3047)
  open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)
  open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit using (isContr-Hⁿ⁺¹[Unit,G])
  open import Cubical.Data.Unit using (Unit; tt)
  open import Cubical.Foundations.Equiv using (isContr→Equiv)

  H¹-vanishes-Interval : H¹-vanishes UnitInterval
  H¹-vanishes-Interval x = isContr→isProp contr-I x (0ₕ 1 {G = ℤAbGroup} {A = UnitInterval})
    where
    I≡Unit : UnitInterval ≡ Unit
    I≡Unit = ua (isContr→Equiv isContrUnitInterval (tt , λ {tt → refl}))
    contr-I : isContr (coHom 1 ℤAbGroup UnitInterval)
    contr-I = subst (λ X → isContr (coHom 1 ℤAbGroup X)) (sym I≡Unit)
                    (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} 0)
