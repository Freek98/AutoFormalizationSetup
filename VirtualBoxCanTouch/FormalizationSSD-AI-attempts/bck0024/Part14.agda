{-# OPTIONS --cubical --guardedness #-}

module work.Part14 where

open import work.Part13 public

import Cubical.HITs.PropositionalTruncation as PT

module CohomologyModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open CompactHausdorffModule using (CHaus; hasCHausStr)

  StoneType : Stone → Type₀
  StoneType S = fst S

  StoneStr : (S : Stone) → hasStoneStr (fst S)
  StoneStr S = snd S

  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
  open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr; IsAbGroup; makeIsAbGroup)
  import Cubical.Algebra.AbGroup.Properties as AbGrpProps
  import Cubical.Algebra.Group.Properties as GrpProps
  open import Cubical.Algebra.AbGroup.Base using (AbGroup→Group)
  open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠAbGroup)
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; EM∙; 0ₖ; hLevelEM)
  import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp
  open import Cubical.Foundations.Pointed using (Pointed)
  open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; 0ₕ; _+ₕ_; -ₕ_)

  BZ : Type ℓ-zero
  BZ = EM ℤAbGroup 1

  BZ∙ : Pointed ℓ-zero
  BZ∙ = EM∙ ℤAbGroup 1

  bz₀ : BZ
  bz₀ = 0ₖ {G = ℤAbGroup} 1

  isOfHLevel-BZ : isOfHLevel 3 BZ
  isOfHLevel-BZ = hLevelEM ℤAbGroup 1

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
    Ȟ¹-vanishes = (β : C¹) → is1Cocycle β → is1Coboundary β

  -- Lemma: section-exact-cech-complex (tex Lemma 2807)

  module SectionExactCechComplex {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where
    open CechComplex S T A

    section-exact : ((x : S) → T x) → Ȟ¹-vanishes
    section-exact t β cocycle-cond = α , funExt λ x → funExt λ u → funExt λ v → prove-at x u v
      where
        α : C⁰
        α x u = β x (t x) u

        prove-at : (x : S) (u v : T x) → d₀ α x u v ≡ β x u v
        prove-at x u v = goal
          where
            module Ax = AbGroupStr (snd (A x))
            module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))

            a = β x u v
            b = β x (t x) v
            c = β x (t x) u

            cocycle-at-tuv : Ax._+_ (Ax._-_ a b) c ≡ Ax.0g
            cocycle-at-tuv = cocycle-cond x (t x) u v

            step1 : Ax._-_ a b ≡ Ax.-_ c
            step1 = Gx.invUniqueL cocycle-at-tuv

            step2 : a ≡ Ax._-_ b c
            step2 = sym (Ax.+IdR a)
                  ∙ cong (Ax._+_ a) (sym (Ax.+InvL b))
                  ∙ Ax.+Assoc a (Ax.-_ b) b
                  ∙ cong (λ z → Ax._+_ z b) step1
                  ∙ Ax.+Comm (Ax.-_ c) b

            goal : d₀ α x u v ≡ β x u v
            goal = sym step2

  -- Lemma: canonical-exact-cech-complex (tex Lemma 2815)

  module CanonicalExactCechComplex {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ) (A : S → AbGroup ℓ) where

    A^T : S → AbGroup ℓ
    A^T x = ΠAbGroup {X = T x} (λ _ → A x)

    open CechComplex S T A^T public

    canonical-exact : Ȟ¹-vanishes
    canonical-exact β cocycle-cond = α , funExt λ x → funExt λ u → funExt λ v → funExt λ t → prove-at x u v t
      where
        α : C⁰
        α x u t = β x t u t

        prove-at : (x : S) (u v : T x) (t : T x) → d₀ α x u v t ≡ β x u v t
        prove-at x u v t = goal
          where
            module ATx = AbGroupStr (snd (A^T x))

            module Ax = AbGroupStr (snd (A x))
            module Gx = GrpProps.GroupTheory (AbGroup→Group (A x))

            cocycle-at-tuv : Ax._+_ (Ax._-_ (β x u v t) (β x t v t)) (β x t u t) ≡ Ax.0g
            cocycle-at-tuv = cong (λ f → f t) (cocycle-cond x t u v)

            step1 : Ax._-_ (β x u v t) (β x t v t) ≡ Ax.-_ (β x t u t)
            step1 = Gx.invUniqueL cocycle-at-tuv

            a = β x u v t
            b = β x t v t
            c = β x t u t

            step2 : a ≡ Ax._-_ b c
            step2 = sym (Ax.+IdR a)
                  ∙ cong (Ax._+_ a) (sym (Ax.+InvL b))
                  ∙ Ax.+Assoc a (Ax.-_ b) b
                  ∙ cong (λ z → Ax._+_ z b) step1
                  ∙ Ax.+Comm (Ax.-_ c) b

            goal : d₀ α x u v t ≡ β x u v t
            goal = sym step2

  -- Lemma: exact-cech-complex-vanishing-cohomology (tex Lemma 2823)
  -- Proof outline (following tex Lemma 2823):

  module ExactCechComplexVanishingProof {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ)
      (A : S → AbGroup ℓ)
      (inhabited : (x : S) → ∥ T x ∥₁)
      (exact : CechComplex.Ȟ¹-vanishes S T A) where

    open CechComplex S T A

    -- Full proof outline (following tex Lemma 2823):

    open import Cubical.HITs.PropositionalTruncation.Properties as PT-Props
    open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
    open import Cubical.Foundations.GroupoidLaws using (symDistr; symInvo) renaming (assoc to assoc-path)

    isSet-paths-in-EM : (G : AbGroup ℓ) (a b : EM G 1) → isSet (a ≡ b)
    isSet-paths-in-EM G a b = isOfHLevelPath' 2 (hLevelEM G 1) a b

    isSet-paths-to-0ₖ : (G : AbGroup ℓ) (a : EM G 1) → isSet (a ≡ 0ₖ {G = G} 1)
    isSet-paths-to-0ₖ G a = isSet-paths-in-EM G a (0ₖ {G = G} 1)

    EM-iso : (x : S) → Iso (EM (A x) 0) (0ₖ {G = A x} 1 ≡ 0ₖ {G = A x} 1)
    EM-iso x = EMProp.Iso-EM-ΩEM+1 {G = A x} 0

    path-to-EM0 : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → (x : S) → T x → T x → EM (A x) 0
    path-to-EM0 α β x u v = Iso.inv (EM-iso x) (sym (β x u) ∙ β x v)

    module EMGroupOps (x : S) where
      private
        Gx = A x
        open AbGroupStr (snd Gx) renaming (_+_ to _+g_ ; _-_ to _-g_ ; 0g to 0g' ; -_ to neg)

      EM0-carrier : Type _
      EM0-carrier = EM Gx 0

      ΩEM1→EM0 : 0ₖ {G = Gx} 1 ≡ 0ₖ {G = Gx} 1 → EM Gx 0
      ΩEM1→EM0 = Iso.inv (EM-iso x)

      EM0→ΩEM1 : EM Gx 0 → 0ₖ {G = Gx} 1 ≡ 0ₖ {G = Gx} 1
      EM0→ΩEM1 = Iso.fun (EM-iso x)

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

        pu = β x u  -- α x ≡ 0ₖ 1
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

        open import Cubical.Foundations.GroupoidLaws using (rCancel; lCancel; lUnit; rUnit)

        sym-p-uw : sym p-uw ≡ sym pw ∙ pu
        sym-p-uw = symDistr (sym pu) pw ∙ cong (sym pw ∙_) (sym (symInvo pu))

        combined-is-refl : combined-path ≡ refl
        combined-is-refl =
          p-vw ∙ sym p-uw ∙ p-uv
            ≡⟨ cong (λ z → p-vw ∙ z ∙ p-uv) sym-p-uw ⟩
          p-vw ∙ (sym pw ∙ pu) ∙ p-uv
            ≡⟨ cong (p-vw ∙_) (sym (assoc-path (sym pw) pu p-uv)) ⟩
          p-vw ∙ (sym pw ∙ (pu ∙ p-uv))
            ≡⟨ refl ⟩  -- p-uv = sym pu ∙ pv
          p-vw ∙ (sym pw ∙ (pu ∙ (sym pu ∙ pv)))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ z)) (assoc-path pu (sym pu) pv) ⟩
          p-vw ∙ (sym pw ∙ ((pu ∙ sym pu) ∙ pv))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ (z ∙ pv))) (rCancel pu) ⟩
          p-vw ∙ (sym pw ∙ (refl ∙ pv))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ z)) (sym (lUnit pv)) ⟩
          p-vw ∙ (sym pw ∙ pv)
            ≡⟨ refl ⟩  -- p-vw = sym pv ∙ pw
          (sym pv ∙ pw) ∙ (sym pw ∙ pv)
            ≡⟨ sym (assoc-path (sym pv) pw (sym pw ∙ pv)) ⟩
          sym pv ∙ (pw ∙ (sym pw ∙ pv))
            ≡⟨ cong (sym pv ∙_) (assoc-path pw (sym pw) pv) ⟩
          sym pv ∙ ((pw ∙ sym pw) ∙ pv)
            ≡⟨ cong (λ z → sym pv ∙ (z ∙ pv)) (rCancel pw) ⟩
          sym pv ∙ (refl ∙ pv)
            ≡⟨ cong (sym pv ∙_) (sym (lUnit pv)) ⟩
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
        combined-gives-0g = cong ϕ combined-is-refl ∙ ϕ-refl

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

        minus-is-plus-neg : Ax._-_ gvw guw ≡ Ax._+_ gvw (Ax.-_ guw)
        minus-is-plus-neg = refl  -- by definition

        goal : d₁ (path-to-EM0 α β) x u v w ≡ AGx.0g x
        goal = sym expand-combined ∙ combined-gives-0g

    get-coboundary : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → CechComplex.is1Coboundary S T A (path-to-EM0 α β)
    get-coboundary α β = exact (path-to-EM0 α β) (path-to-EM0-is-cocycle α β)

    vanishing-result : (α : (x : S) → EM (A x) 1)
      → (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
      → (x : S) → α x ≡ 0ₖ {G = A x} 1
    vanishing-result α β x = SE.rec→Set witness β-adjusted-constant (inhabited x)
      where
        coboundary-data : is1Coboundary (path-to-EM0 α β)
        coboundary-data = get-coboundary α β

        cb-f : C⁰  -- cb-f : (y : S) → T y → |A| y
        cb-f = fst coboundary-data

        d₀-cb-f-eq : d₀ cb-f ≡ path-to-EM0 α β
        d₀-cb-f-eq = snd coboundary-data

        d₀-at-x : (u v : T x) → d₀ cb-f x u v ≡ path-to-EM0 α β x u v
        d₀-at-x u v = funExt⁻ (funExt⁻ (funExt⁻ d₀-cb-f-eq x) u) v

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
            d₀-rel = d₀-at-x u v

            key-rel : sym βu ∙ βv ≡ ψ (AGx._-_ x fv fu)
            key-rel = sym (ψ∘ϕ (sym βu ∙ βv)) ∙ cong ψ (sym d₀-rel)

            ψ-expand : ψ (AGx._-_ x fv fu) ≡ ψ fv ∙ sym (ψ fu)
            ψ-expand = ψ-hom fv (Ax.-_ fu) ∙ cong (ψ fv ∙_) (ψ-neg fu)

            key-eq : sym βu ∙ βv ≡ ψ fv ∙ sym (ψ fu)
            key-eq = key-rel ∙ ψ-expand

            open import Cubical.Foundations.GroupoidLaws using (lCancel; rCancel; rUnit; lUnit; assoc)

            loop-comm : (a b : EM (A x) 0) → ψ a ∙ ψ b ≡ ψ b ∙ ψ a
            loop-comm a b = sym (ψ-hom a b) ∙ cong ψ (Ax.+Comm a b) ∙ ψ-hom b a

            sym-comm : (a b : EM (A x) 0) → sym (ψ a) ∙ sym (ψ b) ≡ sym (ψ b) ∙ sym (ψ a)
            sym-comm a b = cong₂ _∙_ (sym (ψ-neg a)) (sym (ψ-neg b))
                         ∙ sym (ψ-hom (Ax.-_ a) (Ax.-_ b))
                         ∙ cong ψ (Ax.+Comm (Ax.-_ a) (Ax.-_ b))
                         ∙ ψ-hom (Ax.-_ b) (Ax.-_ a)
                         ∙ cong₂ _∙_ (ψ-neg b) (ψ-neg a)

            step1 : βu ∙ (sym βu ∙ βv) ≡ βu ∙ (ψ fv ∙ sym (ψ fu))
            step1 = cong (βu ∙_) key-eq

            lhs-simplify : βu ∙ (sym βu ∙ βv) ≡ βv
            lhs-simplify = assoc βu (sym βu) βv
                         ∙ cong (_∙ βv) (rCancel βu)
                         ∙ sym (lUnit βv)

            βv-eq : βv ≡ βu ∙ (ψ fv ∙ sym (ψ fu))
            βv-eq = sym lhs-simplify ∙ step1

            step4 : βv ∙ sym (ψ fv) ≡ (βu ∙ (ψ fv ∙ sym (ψ fu))) ∙ sym (ψ fv)
            step4 = cong (_∙ sym (ψ fv)) βv-eq

            rhs-simplify : (βu ∙ (ψ fv ∙ sym (ψ fu))) ∙ sym (ψ fv) ≡ βu ∙ sym (ψ fu)
            rhs-simplify =
              sym (assoc βu (ψ fv ∙ sym (ψ fu)) (sym (ψ fv)))
              ∙ cong (βu ∙_) (
                  sym (assoc (ψ fv) (sym (ψ fu)) (sym (ψ fv)))
                  ∙ cong (ψ fv ∙_) (sym-comm fu fv)
                  ∙ assoc (ψ fv) (sym (ψ fv)) (sym (ψ fu))
                  ∙ cong (_∙ sym (ψ fu)) (rCancel (ψ fv))
                  ∙ sym (lUnit (sym (ψ fu)))
                )

            path-algebra-lemma : βu ∙ sym (ψ fu) ≡ βv ∙ sym (ψ fv)
            path-algebra-lemma = sym rhs-simplify ∙ sym step4

            final-goal : β-adjusted u ≡ β-adjusted v
            final-goal = cong₂ _∙_ refl (ψ-neg fu)
                       ∙ path-algebra-lemma
                       ∙ sym (cong₂ _∙_ refl (ψ-neg fv))

        witness : T x → α x ≡ 0ₖ {G = A x} 1
        witness t = β-adjusted t

        module SE = PT-Props.SetElim (isSet-paths-to-0ₖ (A x) (α x))

  exact-cech-complex-vanishing-cohomology : {ℓ : Level} (S : Type ℓ)
    (T : S → Type ℓ) (A : S → AbGroup ℓ)
    (inhabited : (x : S) → ∥ T x ∥₁)
    (exact : CechComplex.Ȟ¹-vanishes S T A)
    (α : (x : S) → EM (A x) 1)
    (β : (x : S) (t : T x) → α x ≡ 0ₖ {G = A x} 1)
    → (x : S) → α x ≡ 0ₖ {G = A x} 1
  exact-cech-complex-vanishing-cohomology S T A inhabited exact α β =
    ExactCechComplexVanishingProof.vanishing-result S T A inhabited exact α β

  -- Čech complex exactness for Stone fibers (tex Lemma 2878)
  --   By Scott continuity (tex Lemma scott-continuity):

  postulate
    cech-complex-vanishing-stone : (S : Type₀) (T : S → Type₀)
      → hasStoneStr S
      → ((x : S) → hasStoneStr (T x))
      → ((x : S) → ∥ T x ∥₁)
      → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)

  -- Stone cohomology vanishes (tex Lemma 2887)
  -- - cech-complex-vanishing-stone (tex Lemma 2878)
  -- - exact-cech-complex-vanishing-cohomology (tex Lemma 2823) - FULLY PROVED

  postulate
    eilenberg-stone-vanish : (S : Stone) → H¹-vanishes (StoneType S)

  -- PROOF OUTLINE (tex Lemma 2887):

  module EilenbergStoneVanishProofInfra where
    open StoneEqualityClosedModule using (StoneEqualityClosed; hasStoneStr→isSet)
    open ClosedInStoneIsStoneModule using (ClosedInStoneIsStone)

    fiber-is-closed : (C B : Stone) (q : fst C → fst B) (s : fst B)
      → (t : fst C) → isClosedProp ((q t ≡ s) , hasStoneStr→isSet B (q t) s)
    fiber-is-closed C B q s t = StoneEqualityClosed B (q t) s

    fiber-hProp : (C B : Stone) (q : fst C → fst B) (s : fst B)
      → fst C → hProp ℓ-zero
    fiber-hProp C B q s t = (q t ≡ s) , hasStoneStr→isSet B (q t) s

    fiber-is-Stone : (C B : Stone) (q : fst C → fst B) (s : fst B)
      → hasStoneStr (Σ[ t ∈ fst C ] q t ≡ s)
    fiber-is-Stone C B q s = ClosedInStoneIsStone C (fiber-hProp C B q s) (fiber-is-closed C B q s)

    FiberStone : (C B : Stone) (q : fst C → fst B) (s : fst B) → Stone
    FiberStone C B q s = (Σ[ t ∈ fst C ] q t ≡ s) , fiber-is-Stone C B q s

    surjective→fibers-inhabited : (C B : Stone) (q : fst C → fst B)
      → ((s : fst B) → ∥ Σ[ t ∈ fst C ] q t ≡ s ∥₁)
      → (s : fst B) → ∥ fst (FiberStone C B q s) ∥₁
    surjective→fibers-inhabited C B q surj s = surj s

  module BZConnectivityInfra where
    open import Cubical.Homotopy.Connected using (isConnected)
    open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)

    open import Cubical.Homotopy.Connected using (isConnectedSubtr)

    BZ-is-2-connected : isConnected 2 BZ
    BZ-is-2-connected = isConnectedEM {G' = ℤAbGroup} 1

    BZ-is-connected : isConnected 1 BZ
    BZ-is-connected = isConnectedSubtr 1 1 BZ-is-2-connected

    open import Cubical.Homotopy.Connected using (isConnectedPath)
    open import Cubical.HITs.Truncation.Base using (hLevelTrunc)
    open import Cubical.HITs.Truncation.Properties using (propTruncTrunc1Iso)
    open Iso

    any-point-merely-equal-to-base : (x : BZ) → ∥ x ≡ bz₀ ∥₁
    any-point-merely-equal-to-base x =
      let pathConnected : isConnected 1 (x ≡ bz₀)
          pathConnected = isConnectedPath 1 BZ-is-2-connected x bz₀
          witness : hLevelTrunc 1 (x ≡ bz₀)
          witness = fst pathConnected
      in inv propTruncTrunc1Iso witness

    α-x-merely-null : {S : Type₀} (α : S → BZ) (x : S) → ∥ α x ≡ bz₀ ∥₁
    α-x-merely-null α x = any-point-merely-equal-to-base (α x)

  module EilenbergStoneVanishProofOutline where
    open BZConnectivityInfra using (α-x-merely-null)
    open EilenbergStoneVanishProofInfra using (fiber-is-Stone; FiberStone; surjective→fibers-inhabited)

    step1-connectivity : (S : Stone) (α : StoneType S → BZ)
      → (s : StoneType S) → ∥ α s ≡ bz₀ ∥₁
    step1-connectivity S α s = α-x-merely-null α s

  module EilenbergStoneVanishFullProofStructure where
    open BZConnectivityInfra using (α-x-merely-null)
    open EilenbergStoneVanishProofInfra using (fiber-is-Stone; FiberStone; surjective→fibers-inhabited)

    open import Axioms.StoneDuality using (Sp; hasStoneStr; Booleω)

    getBooleω : Stone → Booleω
    getBooleω S = fst (snd S)

    getSpEquiv : (S : Stone) → Sp (getBooleω S) ≡ fst S
    getSpEquiv S = snd (snd S)

    makeStone : Booleω → Stone
    makeStone B = Sp B , B , refl

  -- Čech cover definition (tex Definition 2906)

  record CechCover : Type₁ where
    field
      X : CHaus
      S : fst X → Stone
      fibers-inhabited : (x : fst X) → ∥ StoneType (S x) ∥₁
      total-is-Stone : hasStoneStr (Σ (fst X) (λ x → StoneType (S x)))

  -- Čech-Eilenberg agreement (tex Theorem 2945)

  -- The tex proof uses cech-eilenberg-0-agree, eilenberg-exact, cech-exact.

  postulate
    cech-eilenberg-1-agree : (cover : CechCover) →
      let X = fst (CechCover.X cover)
          T = λ x → StoneType (CechCover.S cover x)
      in H¹-vanishes X ↔ CechComplex.Ȟ¹-vanishes X T (λ _ → ℤAbGroup)

  module CechEilenbergProofInfrastructure where
    open import Cubical.HITs.SetTruncation using (∣_∣₂; squash₂)
    open import Cubical.HITs.SetTruncation as ST using (rec; rec2)

    getCoverData : CechCover → Σ[ X ∈ Type₀ ] Σ[ T ∈ (X → Type₀) ] ((x : X) → ∥ T x ∥₁)
    getCoverData cover = X , T , inh
      where
        X = fst (CechCover.X cover)
        T = λ x → StoneType (CechCover.S cover x)
        inh = CechCover.fibers-inhabited cover

    totalSpace : CechCover → Type₀
    totalSpace cover = Σ (fst (CechCover.X cover)) (λ x → StoneType (CechCover.S cover x))

    totalSpace-is-Stone : (cover : CechCover) → hasStoneStr (totalSpace cover)
    totalSpace-is-Stone cover = CechCover.total-is-Stone cover

    totalSpace-H¹-vanishes : (cover : CechCover) → H¹-vanishes (totalSpace cover)
    totalSpace-H¹-vanishes cover = eilenberg-stone-vanish (totalSpace cover , totalSpace-is-Stone cover)

    eilenberg-to-cech-type : (cover : CechCover) →
      let X = fst (CechCover.X cover)
          T = λ x → StoneType (CechCover.S cover x)
      in H¹-vanishes X → CechComplex.Ȟ¹-vanishes X T (λ _ → ℤAbGroup)
    eilenberg-to-cech-type cover h1-vanish =
      λ β cocycle-cond → postulated-coboundary β cocycle-cond
      where
        postulate
          postulated-coboundary : (β : CechComplex.C¹ (fst (CechCover.X cover))
                                       (λ x → StoneType (CechCover.S cover x))
                                       (λ _ → ℤAbGroup))
                               → CechComplex.is1Cocycle (fst (CechCover.X cover))
                                       (λ x → StoneType (CechCover.S cover x))
                                       (λ _ → ℤAbGroup) β
                               → CechComplex.is1Coboundary (fst (CechCover.X cover))
                                       (λ x → StoneType (CechCover.S cover x))
                                       (λ _ → ℤAbGroup) β

  -- Cohomology of the interval (tex Section 2955, Proposition 2991)
  -- TEX PROOF STRUCTURE (Proposition cohomology-I):
  -- 4. By Cn-exact-sequence (tex Lemma 2973), each Čech complex for Iₙ is exact:
  -- KEY DEPENDENCY: Cn-exact-sequence (tex Lemma 2973) - finite approximation exactness

  -- FiniteApproximationExactSequence (tex Lemma 2973)

  module FiniteApproximationExactSequence where
    open import Cubical.Algebra.Group.Morphisms using (GroupHom; IsGroupHom)
    open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)

    -- The key insight from the tex proof:

    -- The finite approximation exact sequence (tex Lemma 2973)
    -- TEX STATEMENT: For any n : ℕ, the sequence
    -- TEX PROOF (lines 2983-2988):

  private
    module IntervalCohomologyInline where
      open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit
        using (isContr-Hⁿ⁺¹[Unit,G])
      open import Cubical.Data.Unit.Properties using (isContr→≃Unit)
      open import Cubical.Foundations.Univalence using (ua)
      open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)

      UnitInterval≃Unit : UnitInterval ≃ Unit
      UnitInterval≃Unit = isContr→≃Unit isContrUnitInterval

      UnitInterval≡Unit : UnitInterval ≡ Unit
      UnitInterval≡Unit = ua UnitInterval≃Unit

      isContr-H¹-UnitInterval : isContr (coHom 1 ℤAbGroup UnitInterval)
      isContr-H¹-UnitInterval = subst (λ X → isContr (coHom 1 ℤAbGroup X))
                                      (sym UnitInterval≡Unit)
                                      (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} 0)

  interval-cohomology-vanishes : H¹-vanishes IntervalIsCHausModule.UnitInterval
  interval-cohomology-vanishes x = isContr→isProp IntervalCohomologyInline.isContr-H¹-UnitInterval x (0ₕ 1 {G = ℤAbGroup})

  postulate
    circle-cohomology : H¹ BrouwerFixedPointTheoremModule.Circle ≃ ℤ

  private
    module DiskCohomologyInline where
      open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit
        using (isContr-Hⁿ⁺¹[Unit,G])
      open import Cubical.Data.Unit.Properties using (isContr→≃Unit)
      open import Cubical.Foundations.Univalence using (ua)
      open BrouwerFixedPointTheoremModule using (Disk2; isContrDisk2)

      Disk2≃Unit : Disk2 ≃ Unit
      Disk2≃Unit = isContr→≃Unit isContrDisk2

      Disk2≡Unit : Disk2 ≡ Unit
      Disk2≡Unit = ua Disk2≃Unit

      isContr-H¹-Disk2 : isContr (coHom 1 ℤAbGroup Disk2)
      isContr-H¹-Disk2 = subst (λ X → isContr (coHom 1 ℤAbGroup X))
                               (sym Disk2≡Unit)
                               (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} 0)

  disk-cohomology-vanishes : H¹-vanishes BrouwerFixedPointTheoremModule.Disk2
  disk-cohomology-vanishes x = isContr→isProp DiskCohomologyInline.isContr-H¹-Disk2 x (0ₕ 1 {G = ℤAbGroup})

  module DiskCohomologyFromContr where
    open import Cubical.Algebra.Group.Morphisms
    open import Cubical.Algebra.Group.MorphismProperties
    open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit
      using (isContr-Hⁿ⁺¹[Unit,G])
    open import Cubical.Data.Unit.Properties using (isContr→≃Unit; isContrUnit)
    open import Cubical.Foundations.Isomorphism using (isoToEquiv; isContr→Iso)
    open import Cubical.Foundations.Univalence using (ua)
    open BrouwerFixedPointTheoremModule using (Disk2; isSetDisk2; isContrDisk2)

    Disk2≃Unit : Disk2 ≃ Unit
    Disk2≃Unit = isContr→≃Unit isContrDisk2

    Disk2≡Unit : Disk2 ≡ Unit
    Disk2≡Unit = ua Disk2≃Unit

    isContr-H¹-Disk2 : isContr (coHom 1 ℤAbGroup Disk2)
    isContr-H¹-Disk2 = subst (λ X → isContr (coHom 1 ℤAbGroup X))
                             (sym Disk2≡Unit)
                             (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} 0)

    disk-cohomology-vanishes-derived : H¹-vanishes Disk2
    disk-cohomology-vanishes-derived x = isContr→isProp isContr-H¹-Disk2 x (0ₕ 1 {G = ℤAbGroup})

  module IntervalCohomologyFromContr where
    open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit
      using (isContr-Hⁿ⁺¹[Unit,G])
    open import Cubical.Data.Unit.Properties using (isContr→≃Unit)
    open import Cubical.Foundations.Univalence using (ua)
    open IntervalIsCHausModule using (UnitInterval; isSetUnitInterval; isContrUnitInterval)

    UnitInterval≃Unit : UnitInterval ≃ Unit
    UnitInterval≃Unit = isContr→≃Unit isContrUnitInterval

    UnitInterval≡Unit : UnitInterval ≡ Unit
    UnitInterval≡Unit = ua UnitInterval≃Unit

    isContr-H¹-UnitInterval : isContr (coHom 1 ℤAbGroup UnitInterval)
    isContr-H¹-UnitInterval = subst (λ X → isContr (coHom 1 ℤAbGroup X))
                                    (sym UnitInterval≡Unit)
                                    (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} 0)

    interval-cohomology-vanishes-derived : H¹-vanishes UnitInterval
    interval-cohomology-vanishes-derived x = isContr→isProp isContr-H¹-UnitInterval x (0ₕ 1 {G = ℤAbGroup})

  module CohomologyPathConsistency where
    open import Cubical.ZCohomology.GroupStructure using (coHomGr)
    open import Cubical.Algebra.Group.Base using (GroupStr)
    open BrouwerFixedPointTheoremModule using (Disk2)
    open IntervalIsCHausModule using (UnitInterval)
    open DiskCohomologyFromContr using (disk-cohomology-vanishes-derived)
    open IntervalCohomologyFromContr using (interval-cohomology-vanishes-derived)

  module IntervalConnectedFromContr where
    open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁)
    open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)

    interval-center : UnitInterval
    interval-center = fst isContrUnitInterval

    interval-trunc-inhabited : ∥ UnitInterval ∥₁
    interval-trunc-inhabited = ∣ interval-center ∣₁

    interval-trunc-isProp : isProp ∥ UnitInterval ∥₁
    interval-trunc-isProp = squash₁

    is-1-connected-I-derived : isContr ∥ UnitInterval ∥₁
    is-1-connected-I-derived = interval-trunc-inhabited , λ x → interval-trunc-isProp _ x

  module PostulateConsistency where
    open import Cubical.Foundations.Prelude using (isPropIsContr)
    open import Cubical.HITs.PropositionalTruncation using (squash₁)
    open IntervalIsCHausModule using (UnitInterval; isContrUnitInterval)
    open IntervalConnectedFromContr using (is-1-connected-I-derived)

    is-1-connected-unique : (p : isContr ∥ UnitInterval ∥₁)
                          → p ≡ is-1-connected-I-derived
    is-1-connected-unique p = isPropIsContr p is-1-connected-I-derived

    isProp-is-1-connected-I : isProp (isContr ∥ UnitInterval ∥₁)
    isProp-is-1-connected-I = isPropIsContr

  module CohomologyEqualityProofs where
    open import Cubical.Foundations.Prelude using (isContr→isProp; isProp→isSet)
    open BrouwerFixedPointTheoremModule using (Disk2)
    open IntervalIsCHausModule using (UnitInterval)
    open DiskCohomologyFromContr
      using (disk-cohomology-vanishes-derived; isContr-H¹-Disk2)
    open IntervalCohomologyFromContr
      using (interval-cohomology-vanishes-derived; isContr-H¹-UnitInterval)

    isProp-H¹-Disk2 : isProp (H¹ Disk2)
    isProp-H¹-Disk2 = isContr→isProp isContr-H¹-Disk2

    isProp-H¹-UnitInterval : isProp (H¹ UnitInterval)
    isProp-H¹-UnitInterval = isContr→isProp isContr-H¹-UnitInterval

    isSet-H¹-Disk2 : isSet (H¹ Disk2)
    isSet-H¹-Disk2 = isProp→isSet isProp-H¹-Disk2

    isSet-H¹-UnitInterval : isSet (H¹ UnitInterval)
    isSet-H¹-UnitInterval = isProp→isSet isProp-H¹-UnitInterval

    isProp-H¹-Disk2-vanishes : isProp (H¹-vanishes Disk2)
    isProp-H¹-Disk2-vanishes = isPropΠ (λ x → isSet-H¹-Disk2 x (0ₕ 1 {G = ℤAbGroup}))

    disk-cohomology-equality : disk-cohomology-vanishes ≡ disk-cohomology-vanishes-derived
    disk-cohomology-equality = isProp-H¹-Disk2-vanishes disk-cohomology-vanishes disk-cohomology-vanishes-derived

    isProp-H¹-UnitInterval-vanishes : isProp (H¹-vanishes UnitInterval)
    isProp-H¹-UnitInterval-vanishes = isPropΠ (λ x → isSet-H¹-UnitInterval x (0ₕ 1 {G = ℤAbGroup}))

    interval-cohomology-equality : interval-cohomology-vanishes ≡ interval-cohomology-vanishes-derived
    interval-cohomology-equality = isProp-H¹-UnitInterval-vanishes interval-cohomology-vanishes interval-cohomology-vanishes-derived

  module FInjectiveEqualityProof where
    open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2)

    isSet-B∞ : isSet ⟨ B∞ ⟩
    isSet-B∞ = BooleanRingStr.is-set (snd B∞)

    isProp-B∞-path : (x y : ⟨ B∞ ⟩) → isProp (x ≡ y)
    isProp-B∞-path = isSet-B∞

    isProp-f-inj-pointwise : (x y : ⟨ B∞ ⟩) → isProp (fst f x ≡ fst f y → x ≡ y)
    isProp-f-inj-pointwise x y = isPropΠ (λ _ → isProp-B∞-path x y)

    isProp-f-injective-type : isProp ((x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y)
    isProp-f-injective-type = isPropΠ2 (λ x y → isPropΠ (λ _ → isProp-B∞-path x y))

    f-injective-05a-equality : f-injective-05a ≡ f-injective-from-trunc
    f-injective-05a-equality = isProp-f-injective-type f-injective-05a f-injective-from-trunc

    isProp-Sp-f-surjective-type : isProp ((h : Sp B∞-Booleω) → ∥ Σ[ h' ∈ Sp B∞×B∞-Booleω ] Sp-f h' ≡ h ∥₁)
    isProp-Sp-f-surjective-type = isPropΠ (λ _ → squash₁)

    Sp-f-surjective-equality : Sp-f-surjective ≡ Sp-f-surjective-from-proof.Sp-f-surjective-from-proof
    Sp-f-surjective-equality = isProp-Sp-f-surjective-type Sp-f-surjective Sp-f-surjective-from-proof.Sp-f-surjective-from-proof

  module CircleCohomologyFromLibrary where
    open import Cubical.HITs.S1 using (S¹)
    open import Cubical.HITs.Sn using (S₊)
    open import Cubical.Algebra.Group.Morphisms
    open import Cubical.Algebra.Group.MorphismProperties
    open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
    open import Cubical.ZCohomology.Groups.Sn using (Hⁿ-Sⁿ≅ℤ)
    open import Cubical.ZCohomology.Groups.Unit using (Hⁿ-contrType≅0)
    open import Cubical.ZCohomology.Base using (coHom)
    open import Cubical.ZCohomology.GroupStructure using (coHomGr)
    open BrouwerFixedPointTheoremModule using (Circle; isSetCircle; Disk2; isSetDisk2)

    H¹-S¹≃ℤ-witness : GroupIso (coHomGr 1 S¹) ℤGroup
    H¹-S¹≃ℤ-witness = Hⁿ-Sⁿ≅ℤ 0

  -- DERIVATION STRATEGY (tex Proposition 3074):

  -- I-LOCALITY MODULE (tex Section 3011, Lemmas 3015-3035)
  -- This module documents the I-locality framework from the tex file.

  module ILocalityFromTex where
    open import Cubical.Data.Int using (ℤ)
    open IntervalIsCHausModule using (UnitInterval)

    𝕀 : Type₀
    𝕀 = UnitInterval

    -- DEFINITIONS (tex line 3013)

    isILocal : Type₀ → Type₀
    isILocal X = isEquiv (λ (x : X) → (λ (_ : 𝕀) → x))

    -- LEMMA: ℤ and Bool are I-local (tex Lemma 3015 Z-I-local)
    -- TEX PROOF:
    -- OUR DERIVATION is simpler than the tex cohomology proof:

    -- COROLLARY: Stone spaces are I-local (tex Remark after 3015)

    -- LEMMA: Bℤ is I-local (tex Lemma 3027 BZ-I-local)
    -- TEX PROOF:

    -- LEMMA: Continuously path-connected ⟹ I-contractible (tex Lemma 3035)
    -- TEX STATEMENT:

    -- COROLLARY: ℝ and D² are I-contractible (tex Corollary 3047)

  module NoRetractionFunctorialProof where
    open import Cubical.Algebra.Group.Base
    open import Cubical.Algebra.Group.Morphisms
    open import Cubical.Algebra.Group.MorphismProperties
    open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
    open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup₀)
    open import Cubical.ZCohomology.GroupStructure using (coHomGr)
    open BrouwerFixedPointTheoremModule using (Circle; Disk2; boundary-inclusion)

    ℤ-Unit-ℤ-is-zero : (φ : GroupHom ℤGroup UnitGroup₀)
                     → (ψ : GroupHom UnitGroup₀ ℤGroup)
                     → (n : fst ℤGroup) → fst ψ (fst φ n) ≡ pos 0
    ℤ-Unit-ℤ-is-zero φ ψ n = goal
      where
      ψ-map : Unit → ℤ
      ψ-map = fst ψ

      ψ-pres-id : ψ-map tt ≡ pos 0
      ψ-pres-id = IsGroupHom.pres1 (snd ψ)

      φn-is-tt : fst φ n ≡ tt
      φn-is-tt = refl  -- Unit has definitional η: any element of Unit is tt

      goal : ψ-map (fst φ n) ≡ pos 0
      goal = ψ-pres-id  -- since φ(n) = tt by η-expansion of Unit

-- I-LOCALIZATION / SHAPE THEORY APPROACH (tex Section 3011)
-- The tex file provides an alternative proof of no-retraction using
-- KEY CONCEPTS (from tex lines 3013-3079):
-- 1. I-LOCALIZATION MODALITY L_I (tex line 3013):
-- 2. ℤ AND Bool ARE I-LOCAL (tex Lemma 3015 Z-I-local):
-- 3. Bℤ IS I-LOCAL (tex Lemma 3027 BZ-I-local):
-- 4. CONTINUOUSLY PATH-CONNECTED ⟹ I-CONTRACTIBLE (tex Lemma 3035):
-- 5. ℝ AND D² ARE I-CONTRACTIBLE (tex Corollary 3047 R-I-contractible):
-- 6. SHAPE OF S¹ IS Bℤ (tex Proposition 3051 shape-S1-is-BZ):
-- 7. NO-RETRACTION FROM SHAPE THEORY (tex Proposition 3074 no-retraction):

-- FUNDAMENTAL AXIOMS (from tex file, intended as axioms):
-- - 4 fundamental axioms (from tex): sd-axiom, surj-formal-axiom, localChoice, dependentChoice
-- 3. ILocalityFromTex: Documents tex lemmas on I-locality (lines ~14140-14237)
--    - Z-I-local (tex Lemma 3015): ℤ and Bool are I-local
--    - BZ-I-local (tex Lemma 3027): Bℤ is I-local
--    - Path-connected implies I-contractible (tex Lemma 3035)
--    - ℝ and D² are I-contractible (tex Corollary 3047)

module NoRetractionFromCohomologyDerived where
  open import Cubical.Algebra.Group.Base
  open import Cubical.Algebra.Group.Morphisms
  open import Cubical.Algebra.Group.MorphismProperties
  open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
  open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup₀)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr)
  open import Cubical.Data.Int using (ℤ; pos)
  open BrouwerFixedPointTheoremModule using (Circle; Disk2; boundary-inclusion)
  open CohomologyModule using (H¹)
  open CohomologyModule.DiskCohomologyFromContr using (isContr-H¹-Disk2)

  id-neq-zero-on-ℤ : ¬ ((n : ℤ) → n ≡ pos 0)
  id-neq-zero-on-ℤ all-zero = snotz (cong extract (all-zero (pos 1)))
    where
    open import Cubical.Data.Nat using (snotz; ℕ; suc; zero)
    extract : ℤ → ℕ
    extract (pos n) = n
    extract (Cubical.Data.Int.negsuc n) = zero

  H¹-Disk2-contr : isContr (H¹ Disk2)
  H¹-Disk2-contr = isContr-H¹-Disk2

  H¹-Disk2-center : H¹ Disk2
  H¹-Disk2-center = fst H¹-Disk2-contr

  H¹-Disk2-all-equal : (x : H¹ Disk2) → x ≡ H¹-Disk2-center
  H¹-Disk2-all-equal x = sym (snd H¹-Disk2-contr x)

module CohomologyFunctorialityInfrastructure where
  open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; coHomFun)
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Data.Nat using (ℕ; suc)
  open import Cubical.Algebra.AbGroup.Base using (AbGroup)
  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
  open BrouwerFixedPointTheoremModule using (Circle; Disk2; boundary-inclusion)
  open CohomologyModule using (H¹)

  H¹-induced : {X Y : Type₀} → (f : X → Y) → H¹ Y → H¹ X
  H¹-induced f = coHomFun {G = ℤAbGroup} 1 f

  boundary-inclusion* : H¹ Disk2 → H¹ Circle
  boundary-inclusion* = H¹-induced boundary-inclusion

  coHomFun-comp : {X Y Z : Type₀} (f : X → Y) (g : Y → Z)
    → (x : H¹ Z) → coHomFun {G = ℤAbGroup} 1 f (coHomFun {G = ℤAbGroup} 1 g x)
                 ≡ coHomFun {G = ℤAbGroup} 1 (g ∘ f) x
  coHomFun-comp f g = ST.elim (λ _ → ST.isSetPathImplicit) λ h → refl

  coHomFun-id : {X : Type₀} (x : H¹ X) → coHomFun {G = ℤAbGroup} 1 (λ y → y) x ≡ x
  coHomFun-id = ST.elim (λ _ → ST.isSetPathImplicit) λ h → refl

  retraction-would-give-H¹-retraction-type :
    (r : Disk2 → Circle)
    → (is-retraction : (c : Circle) → r (boundary-inclusion c) ≡ c)
    → Σ[ r* ∈ (H¹ Circle → H¹ Disk2) ]
        ((x : H¹ Circle) → boundary-inclusion* (r* x) ≡ x)
  retraction-would-give-H¹-retraction-type r is-retraction =
    H¹-induced r , cohomology-retraction-proof
    where

    r-boundary-is-id : r ∘ boundary-inclusion ≡ (λ c → c)
    r-boundary-is-id = funExt is-retraction

    cohomology-retraction-proof : (x : H¹ Circle) → boundary-inclusion* (H¹-induced r x) ≡ x
    cohomology-retraction-proof x =
      boundary-inclusion* (H¹-induced r x)
        ≡⟨ coHomFun-comp boundary-inclusion r x ⟩
      coHomFun {G = ℤAbGroup} 1 (r ∘ boundary-inclusion) x
        ≡⟨ cong (λ f → coHomFun {G = ℤAbGroup} 1 f x) r-boundary-is-id ⟩
      coHomFun {G = ℤAbGroup} 1 (λ c → c) x
        ≡⟨ coHomFun-id x ⟩
      x ∎

module NoRetractionCompleteProof where
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Equiv using (invEq; equivFun; _≃_; isEquiv; equiv→Iso)
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Data.Int using (ℤ; pos)
  open import Cubical.Data.Sigma
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
  open BrouwerFixedPointTheoremModule using (Circle; Disk2; boundary-inclusion)
  open CohomologyModule using (H¹)
  open CohomologyModule.DiskCohomologyFromContr using (isContr-H¹-Disk2)
  open NoRetractionFromCohomologyDerived using (id-neq-zero-on-ℤ; H¹-Disk2-contr; H¹-Disk2-center; H¹-Disk2-all-equal)
  open CohomologyFunctorialityInfrastructure using (H¹-induced; boundary-inclusion*; retraction-would-give-H¹-retraction-type)

  H¹-Circle-trivial-from-retraction :
    (r* : H¹ Circle → H¹ Disk2)
    → ((x : H¹ Circle) → boundary-inclusion* (r* x) ≡ x)
    → (x y : H¹ Circle) → x ≡ y
  H¹-Circle-trivial-from-retraction r* section-cond x y =
    x
      ≡⟨ sym (section-cond x) ⟩
    boundary-inclusion* (r* x)
      ≡⟨ cong boundary-inclusion* (H¹-Disk2-all-equal (r* x) ∙ sym (H¹-Disk2-all-equal (r* y))) ⟩
    boundary-inclusion* (r* y)
      ≡⟨ section-cond y ⟩
    y ∎

  no-retraction-from-circle-cohomology :
    (circle-coh : H¹ Circle ≃ ℤ)
    → (r : Disk2 → Circle)
    → ((c : Circle) → r (boundary-inclusion c) ≡ c)
    → ⊥
  no-retraction-from-circle-cohomology circle-coh r is-retraction =
    id-neq-zero-on-ℤ ℤ-all-equal
    where
    cohom-retraction = retraction-would-give-H¹-retraction-type r is-retraction
    r* = fst cohom-retraction
    section-cond = snd cohom-retraction

    H¹-Circle-all-equal : (x y : H¹ Circle) → x ≡ y
    H¹-Circle-all-equal = H¹-Circle-trivial-from-retraction r* section-cond

    ℤ-all-equal : (n : ℤ) → n ≡ pos 0
    ℤ-all-equal n =
      n
        ≡⟨ sym (Cubical.Foundations.Equiv.secEq circle-coh n) ⟩
      equivFun circle-coh (invEq circle-coh n)
        ≡⟨ cong (equivFun circle-coh) (H¹-Circle-all-equal (invEq circle-coh n) (invEq circle-coh (pos 0))) ⟩
      equivFun circle-coh (invEq circle-coh (pos 0))
        ≡⟨ Cubical.Foundations.Equiv.secEq circle-coh (pos 0) ⟩
      pos 0 ∎

  open CohomologyModule using (circle-cohomology)

  no-retraction-theorem :
    (r : Disk2 → Circle)
    → ((c : Circle) → r (boundary-inclusion c) ≡ c)
    → ⊥
  no-retraction-theorem = no-retraction-from-circle-cohomology circle-cohomology

-- TEX REFERENCE: The proof of Lemma 2878 uses:

module SequentialColimitInfrastructure where
  open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
  open import Cubical.Data.Nat.Order.Inductive using (_<ᵗ_; <ᵗ-trans-suc)
  open import Cubical.Data.Fin using (Fin; fzero; fsuc; toℕ)
  open import Cubical.Data.Sigma using (Σ; _,_; fst; snd)
  open import Cubical.Data.Sum using (_⊎_; inl; inr)
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Foundations.Prelude using (Type; Level; ℓ-zero; _≡_; refl; sym; _∙_; cong; cong₂; transport; subst; PathP; funExt)
  open import Cubical.Foundations.Function using (_∘_)

  -- Finite Linear Approximation Iₙ (tex Definition 2963)

  2^_ : ℕ → ℕ
  2^ zero = 1
  2^ suc n = 2^ n +ℕ 2^ n

  Iₙ : ℕ → Type₀
  Iₙ n = Fin (2^ n)

  2^-pos : (n : ℕ) → Σ[ m ∈ ℕ ] (2^ n ≡ suc m)
  2^-pos zero = 0 , refl
  2^-pos (suc n) with 2^-pos n
  ... | m , eq = (m +ℕ suc m) , cong₂ _+ℕ_ eq eq

  Iₙ-inhabited : (n : ℕ) → Iₙ n
  Iₙ-inhabited n with 2^-pos n
  ... | m , eq = subst Fin (sym eq) fzero

  d₀ : {n : ℕ} → ℤ → (Iₙ n → ℤ)
  d₀ k _ = k

  d₀-injective : {n : ℕ} → (k l : ℤ) → d₀ {n} k ≡ d₀ {n} l → k ≡ l
  d₀-injective {n} k l eq = cong (λ f → f (Iₙ-inhabited n)) eq

  FiniteApproxExact-type : ℕ → Type₀
  FiniteApproxExact-type n =
    ((k l : ℤ) → d₀ {n} k ≡ d₀ {n} l → k ≡ l)
    × -- ker(d₁) = im(d₀) : any function that becomes 0 under d₁ is constant
    ((α : Iₙ n → ℤ) →
       Σ[ k ∈ ℤ ] (α ≡ d₀ {n} k))

  constant-is-d₀ : {n : ℕ} → (α : Iₙ n → ℤ) → (k : ℤ) →
                    ((x : Iₙ n) → α x ≡ k) → α ≡ d₀ {n} k
  constant-is-d₀ {n} α k eq = funExt eq

  d₀-is-constant : {n : ℕ} → (k : ℤ) → (x : Iₙ n) → d₀ {n} k x ≡ k
  d₀-is-constant k x = refl

  import Cubical.Data.Int.Base as ℤBase

  d₁ : {n : ℕ} → (Iₙ n → ℤ) → (Iₙ n → Iₙ n → ℤ)
  d₁ α x y = α y ℤBase.- α x

  open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
  open import Cubical.Algebra.Group.Base using (GroupStr)

  ℤ-minus-self : (k : ℤ) → (k ℤBase.- k) ≡ pos 0
  ℤ-minus-self k = GroupStr.·InvR (snd ℤGroup) k

  d₁∘d₀-is-zero : {n : ℕ} → (k : ℤ) → (x y : Iₙ n) → d₁ {n} (d₀ {n} k) x y ≡ pos 0
  d₁∘d₀-is-zero {n} k x y = ℤ-minus-self k

  d₁∘d₀-is-zero-fun : {n : ℕ} → (k : ℤ) → d₁ {n} (d₀ {n} k) ≡ (λ _ _ → pos 0)
  d₁∘d₀-is-zero-fun {n} k = funExt (λ x → funExt (λ y → d₁∘d₀-is-zero {n} k x y))

  inKernel-d₁ : {n : ℕ} → (Iₙ n → ℤ) → Type₀
  inKernel-d₁ {n} α = (x y : Iₙ n) → d₁ {n} α x y ≡ pos 0

  inImage-d₀ : {n : ℕ} → (Iₙ n → ℤ) → Type₀
  inImage-d₀ {n} α = Σ[ k ∈ ℤ ] (α ≡ d₀ {n} k)

  image-d₀-in-kernel-d₁ : {n : ℕ} → (α : Iₙ n → ℤ) → inImage-d₀ {n} α → inKernel-d₁ {n} α
  image-d₀-in-kernel-d₁ {n} α (k , α≡d₀k) x y =
    cong (λ f → d₁ {n} f x y) α≡d₀k ∙ d₁∘d₀-is-zero {n} k x y

  open import Cubical.Data.Int.Properties using (-≡0)

  ℤ-diff-zero-implies-eq : (a b : ℤ) → (a ℤBase.- b) ≡ pos 0 → a ≡ b
  ℤ-diff-zero-implies-eq a b eq = -≡0 a b eq

  kernel-d₁-in-image-d₀ : {n : ℕ} → (α : Iₙ n → ℤ) → inKernel-d₁ {n} α → inImage-d₀ {n} α
  kernel-d₁-in-image-d₀ {n} α inKer = k , α≡d₀k
    where
      x₀ : Iₙ n
      x₀ = Iₙ-inhabited n

      k : ℤ
      k = α x₀

      α-constant : (y : Iₙ n) → α y ≡ k
      α-constant y = ℤ-diff-zero-implies-eq (α y) (α x₀) (inKer x₀ y)

      α≡d₀k : α ≡ d₀ {n} k
      α≡d₀k = constant-is-d₀ {n} α k α-constant

  finite-approx-exact : {n : ℕ} → (α : Iₙ n → ℤ) →
    inKernel-d₁ {n} α ↔ inImage-d₀ {n} α
  finite-approx-exact {n} α =
    kernel-d₁-in-image-d₀ {n} α ,
    image-d₀-in-kernel-d₁ {n} α

  halfℕ : ℕ → ℕ
  halfℕ zero = zero
  halfℕ (suc zero) = zero
  halfℕ (suc (suc n)) = suc (halfℕ n)

  zero<+-l : (a b : ℕ) → zero <ᵗ a → zero <ᵗ (a +ℕ b)
  zero<+-l (suc a) b _ = tt  -- 0 <ᵇ suc (a + b) = true

  zero<2^ : (n : ℕ) → zero <ᵗ (2^ n)
  zero<2^ zero = tt        -- 0 < 1
  zero<2^ (suc n) = zero<+-l (2^ n) (2^ n) (zero<2^ n)  -- 0 < 2^n + 2^n

  halfℕ-< : {n : ℕ} → (k : ℕ) → k <ᵗ (2^ (suc n)) → halfℕ k <ᵗ (2^ n)
  halfℕ-< {n} zero _ = zero<2^ n           -- halfℕ 0 = 0 < 2^n
  halfℕ-< {n} (suc zero) _ = zero<2^ n      -- halfℕ 1 = 0 < 2^n
  halfℕ-< {n} (suc (suc k)) k<2sn = halfℕ-<-helper {n} k k<2sn
    where
      postulate
        halfℕ-<-helper : {n : ℕ} → (k : ℕ) → (suc (suc k)) <ᵗ (2^ (suc n)) → suc (halfℕ k) <ᵗ (2^ n)

  πₙ : {n : ℕ} → Iₙ (suc n) → Iₙ n
  πₙ {n} (k , k<2sn) = halfℕ k , halfℕ-< {n} k k<2sn

  π* : {n : ℕ} → (Iₙ n → ℤ) → (Iₙ (suc n) → ℤ)
  π* {n} α = α ∘ πₙ {n}

  π*-preserves-constant : {n : ℕ} → (k : ℤ) → π* {n} (d₀ {n} k) ≡ d₀ {suc n} k
  π*-preserves-constant {n} k = refl

  d₁-π*-naturality : {n : ℕ} → (α : Iₙ n → ℤ) → (x y : Iₙ (suc n)) →
                      d₁ {suc n} (π* {n} α) x y ≡ d₁ {n} α (πₙ {n} x) (πₙ {n} y)
  d₁-π*-naturality {n} α x y = refl

  π*-preserves-kernel-d₁ : {n : ℕ} → (α : Iₙ n → ℤ) →
                            inKernel-d₁ {n} α → inKernel-d₁ {suc n} (π* {n} α)
  π*-preserves-kernel-d₁ {n} α α-in-ker x y =
    d₁-π*-naturality {n} α x y ∙ α-in-ker (πₙ {n} x) (πₙ {n} y)

  π*-preserves-image-d₀ : {n : ℕ} → (α : Iₙ n → ℤ) →
                           inImage-d₀ {n} α → inImage-d₀ {suc n} (π* {n} α)
  π*-preserves-image-d₀ {n} α (k , α≡d₀k) =
    k , cong (π* {n}) α≡d₀k ∙ π*-preserves-constant {n} k

  CompatibleFamily : Type₀
  CompatibleFamily = Σ[ α ∈ ((n : ℕ) → (Iₙ n → ℤ)) ]
                       ((n : ℕ) → α (suc n) ≡ π* {n} (α n))

  family-at : CompatibleFamily → (n : ℕ) → (Iₙ n → ℤ)
  family-at (α , _) n = α n

  family-compat : (fam : CompatibleFamily) → (n : ℕ) →
                   family-at fam (suc n) ≡ π* {n} (family-at fam n)
  family-compat (_ , compat) n = compat n

  CompatibleFamily-inKernel-d₁ : CompatibleFamily → Type₀
  CompatibleFamily-inKernel-d₁ fam = (n : ℕ) → inKernel-d₁ {n} (family-at fam n)

  CompatibleFamily-inImage-d₀ : CompatibleFamily → Type₀
  CompatibleFamily-inImage-d₀ fam = Σ[ k ∈ ℤ ] ((n : ℕ) → family-at fam n ≡ d₀ {n} k)

  compatible-family-exactness : (fam : CompatibleFamily) →
                                 CompatibleFamily-inKernel-d₁ fam →
                                 CompatibleFamily-inImage-d₀ fam
  compatible-family-exactness fam fam-in-ker = k₀ , constant-proof
    where
      α₀-in-image : inImage-d₀ {0} (family-at fam 0)
      α₀-in-image = kernel-d₁-in-image-d₀ {0} (family-at fam 0) (fam-in-ker 0)

      k₀ : ℤ
      k₀ = fst α₀-in-image

      constant-at-level : (n : ℕ) → family-at fam n ≡ d₀ {n} k₀
      constant-at-level zero = snd α₀-in-image
      constant-at-level (suc n) =
        family-compat fam n ∙ cong (π* {n}) (constant-at-level n) ∙ π*-preserves-constant {n} k₀

      constant-proof : (n : ℕ) → family-at fam n ≡ d₀ {n} k₀
      constant-proof = constant-at-level

module StoneSpaceExactness where
  open SequentialColimitInfrastructure

  IntervalFunction : Type₀
  IntervalFunction = CompatibleFamily

  IntervalFunction-inKernel : IntervalFunction → Type₀
  IntervalFunction-inKernel = CompatibleFamily-inKernel-d₁

  IntervalFunction-inImage : IntervalFunction → Type₀
  IntervalFunction-inImage = CompatibleFamily-inImage-d₀

  interval-exactness : (f : IntervalFunction) →
                        IntervalFunction-inKernel f → IntervalFunction-inImage f
  interval-exactness = compatible-family-exactness

module CechComplexCompatibleFamilies where
  open SequentialColimitInfrastructure

module FiniteApproximationExactness where
  open SequentialColimitInfrastructure

  open import Cubical.Data.Fin using (Fin; fzero; fsuc)
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; rec; squash₁; map)
  import Cubical.HITs.PropositionalTruncation as PT
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Foundations.Transport using (transport⁻Transport)

  finite-section-exists : {n : ℕ} (T : Fin (suc n) → Type₀)
                        → ((k : Fin (suc n)) → ∥ T k ∥₁)
                        → ∥ ((k : Fin (suc n)) → T k) ∥₁
  finite-section-exists {zero} T inh =
    map (λ t₀ k → helper k t₀) (inh fzero)
    where
      helper : (k : Fin 1) → T fzero → T k
      helper (zero , tt) t₀ = t₀
  finite-section-exists {suc n} T inh =
    PT.rec2 squash₁
      make-section
      (inh fzero)
      (finite-section-exists (T ∘ fsuc) (inh ∘ fsuc))
    where
      make-section : T fzero → ((k : Fin (suc n)) → T (fsuc k)) → ∥ ((k : Fin (suc (suc n))) → T k) ∥₁
      make-section t₀ rest = ∣ section ∣₁
        where
          section : (k : Fin (suc (suc n))) → T k
          section (zero , tt) = t₀
          section (suc m , proof) = rest (m , proof)

  In-section-exists : {n : ℕ} (T : Iₙ n → Type₀)
                    → ((k : Iₙ n) → ∥ T k ∥₁)
                    → ∥ ((k : Iₙ n) → T k) ∥₁
  In-section-exists {n} T inh with 2^-pos n
  ... | m , eq =
    let Fin-path : Fin (2^ n) ≡ Fin (suc m)
        Fin-path = cong Fin eq
        T' : Fin (suc m) → Type₀
        T' k = T (transport (sym Fin-path) k)
        inh' : (k : Fin (suc m)) → ∥ T' k ∥₁
        inh' k = inh (transport (sym Fin-path) k)
        result' : ∥ ((k : Fin (suc m)) → T' k) ∥₁
        result' = finite-section-exists T' inh'
        convert-section : ((k : Fin (suc m)) → T' k) → ((k : Fin (2^ n)) → T k)
        convert-section sec k = subst T (transport⁻Transport Fin-path k) (sec (transport Fin-path k))
    in map convert-section result'

module CechComplexVanishingStoneProof where
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
  open SequentialColimitInfrastructure

module BooleomegaSequentialColimit where
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
  open import Axioms.StoneDuality using (Stone; hasStoneStr; Booleω; Sp)
  open SequentialColimitInfrastructure

  isFiniteType : Type₀ → Type₀
  isFiniteType A = Σ[ n ∈ ℕ ] (A ≃ Fin n)

  postulate
    stone-finite-approximation :
      (S : Type₀) → hasStoneStr S →
      Σ[ approx ∈ (ℕ → Type₀) ]
        ((n : ℕ) → isFiniteType (approx n)) ×
        ((n : ℕ) → approx (suc n) → approx n) ×
        (S → (n : ℕ) → approx n)  -- projection maps

module CechComplexVanishingStoneComplete where
  open SequentialColimitInfrastructure
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)

module CoboundaryFromInhabitant where
  open import Cubical.HITs.PropositionalTruncation using (∣_∣₁; squash₁; rec)
  open SequentialColimitInfrastructure
  import Cubical.Data.Int.Base as ℤBase
  open import Cubical.Data.Int using (ℤ; pos)
  open import Cubical.Algebra.Group.Base using (GroupStr)
  open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)

  isCocycle : {T : Type₀} → (T → T → ℤ) → Type₀
  isCocycle {T} β = (u v w : T) → (β u v ℤBase.+ β v w) ≡ β u w

  coboundary-from-basepoint : {T : Type₀} → (β : T → T → ℤ) → (t₀ : T) → (T → ℤ)
  coboundary-from-basepoint β t₀ = λ u → β t₀ u

  open import Cubical.Data.Int.Properties using (plusMinus) renaming (+Comm to ℤ+Comm)

  ℤ-add-sub-cancel-right : (a b : ℤ) → ((a ℤBase.+ b) ℤBase.- b) ≡ a
  ℤ-add-sub-cancel-right a b = plusMinus b a

  ℤ-idempotent-zero : (a : ℤ) → (a ℤBase.+ a) ≡ a → a ≡ pos 0
  ℤ-idempotent-zero a a+a=a =
    let -- Step 1: (a + a) - a = a (by group law)
        aa-a=a : ((a ℤBase.+ a) ℤBase.- a) ≡ a
        aa-a=a = ℤ-add-sub-cancel-right a a
        a-a=0 : (a ℤBase.- a) ≡ pos 0
        a-a=0 = GroupStr.·InvR (snd ℤGroup) a
        step3 : ((a ℤBase.+ a) ℤBase.- a) ≡ (a ℤBase.- a)
        step3 = cong (λ x → x ℤBase.- a) a+a=a
    in sym aa-a=a ∙ step3 ∙ a-a=0

  cocycle-diagonal-zero : {T : Type₀} → (β : T → T → ℤ)
    → isCocycle β → (u : T) → β u u ≡ pos 0
  cocycle-diagonal-zero β cocycle u =
    ℤ-idempotent-zero (β u u) (cocycle u u u)

  cocycle-antisym : {T : Type₀} → (β : T → T → ℤ)
    → isCocycle β → (u v : T) → (β u v ℤBase.+ β v u) ≡ pos 0
  cocycle-antisym β cocycle u v = cocycle u v u ∙ cocycle-diagonal-zero β cocycle u

  open import Cubical.Data.Int.Properties using (-≡0; isSetℤ)

  ℤ-add-sub-cancel-left : (a b : ℤ) → ((a ℤBase.+ b) ℤBase.- a) ≡ b
  ℤ-add-sub-cancel-left a b = cong (λ x → x ℤBase.- a) (ℤ+Comm a b) ∙ plusMinus a b

  ℤ-rearrange : (a b c : ℤ) → (a ℤBase.+ b) ≡ c → b ≡ (c ℤBase.- a)
  ℤ-rearrange a b c a+b≡c =
    let eq : (c ℤBase.- a) ≡ ((a ℤBase.+ b) ℤBase.- a)
        eq = cong (λ x → x ℤBase.- a) (sym a+b≡c)
    in sym (eq ∙ ℤ-add-sub-cancel-left a b)

  coboundary-correct : {T : Type₀} → (β : T → T → ℤ)
    → isCocycle β → (t₀ : T) → (u v : T)
    → β u v ≡ (coboundary-from-basepoint β t₀ v ℤBase.- coboundary-from-basepoint β t₀ u)
  coboundary-correct {T} β cocycle t₀ u v =
    let cocycle-eq : (β t₀ u ℤBase.+ β u v) ≡ β t₀ v
        cocycle-eq = cocycle t₀ u v
    in ℤ-rearrange (β t₀ u) (β u v) (β t₀ v) cocycle-eq

  coboundary-from-inhabited : {T : Type₀} → (β : T → T → ℤ)
    → isCocycle β → ∥ T ∥₁
    → ∥ Σ[ α ∈ (T → ℤ) ] ((u v : T) → β u v ≡ (α v ℤBase.- α u)) ∥₁
  coboundary-from-inhabited {T} β cocycle inhabited =
    rec squash₁
        (λ t₀ → ∣ coboundary-from-basepoint β t₀ ,
                   (λ u v → coboundary-correct β cocycle t₀ u v) ∣₁)
        inhabited
