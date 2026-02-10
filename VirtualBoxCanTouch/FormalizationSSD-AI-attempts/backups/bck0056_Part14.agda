{-# OPTIONS --cubical --guardedness #-}

module work.Part14 where

open import work.Part13 public

module CohomologyModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open CompactHausdorffModule using (CHaus; hasCHausStr)

  StoneType : Stone → Type₀
  StoneType S = fst S

  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
  open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr; AbGroup→Group)
  import Cubical.Algebra.Group.Properties as GrpProps
  open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠAbGroup)
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; EM∙; 0ₖ; hLevelEM)
  import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp
  open import Cubical.Foundations.Pointed using (Pointed)
  open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; 0ₕ)

  BZ : Type ℓ-zero
  BZ = EM ℤAbGroup 1

  BZ∙ : Pointed ℓ-zero
  BZ∙ = EM∙ ℤAbGroup 1

  bz₀ : BZ
  bz₀ = 0ₖ {G = ℤAbGroup} 1

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

  -- tex Lemma 2823
  module ExactCechComplexVanishingProof {ℓ : Level} (S : Type ℓ) (T : S → Type ℓ)
      (A : S → AbGroup ℓ)
      (inhabited : (x : S) → ∥ T x ∥₁)
      (exact : CechComplex.Ȟ¹-vanishes S T A) where

    open CechComplex S T A

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
            ≡⟨ refl ⟩
          p-vw ∙ (sym pw ∙ (pu ∙ (sym pu ∙ pv)))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ z)) (assoc-path pu (sym pu) pv) ⟩
          p-vw ∙ (sym pw ∙ ((pu ∙ sym pu) ∙ pv))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ (z ∙ pv))) (rCancel pu) ⟩
          p-vw ∙ (sym pw ∙ (refl ∙ pv))
            ≡⟨ cong (λ z → p-vw ∙ (sym pw ∙ z)) (sym (lUnit pv)) ⟩
          p-vw ∙ (sym pw ∙ pv)
            ≡⟨ refl ⟩
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
        minus-is-plus-neg = refl

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

        cb-f : C⁰
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

  -- tex Lemma 2878
  postulate
    cech-complex-vanishing-stone : (S : Type₀) (T : S → Type₀)
      → hasStoneStr S
      → ((x : S) → hasStoneStr (T x))
      → ((x : S) → ∥ T x ∥₁)
      → CechComplex.Ȟ¹-vanishes S T (λ _ → ℤAbGroup)

  -- tex Lemma 2887
  postulate
    eilenberg-stone-vanish : (S : Stone) → H¹-vanishes (StoneType S)

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
    open import Cubical.Homotopy.Connected using (isConnected; isConnectedSubtr; isConnectedPath)
    open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)

    BZ-is-2-connected : isConnected 2 BZ
    BZ-is-2-connected = isConnectedEM {G' = ℤAbGroup} 1

    BZ-is-connected : isConnected 1 BZ
    BZ-is-connected = isConnectedSubtr 1 1 BZ-is-2-connected

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

  -- Čech cover definition (tex Definition 2906)

  record CechCover : Type₁ where
    field
      X : CHaus
      S : fst X → Stone
      fibers-inhabited : (x : fst X) → ∥ StoneType (S x) ∥₁
      total-is-Stone : hasStoneStr (Σ (fst X) (λ x → StoneType (S x)))

  -- tex Theorem 2945
  postulate
    cech-eilenberg-1-agree : (cover : CechCover) →
      let X = fst (CechCover.X cover)
          T = λ x → StoneType (CechCover.S cover x)
      in H¹-vanishes X ↔ CechComplex.Ȟ¹-vanishes X T (λ _ → ℤAbGroup)

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

  module IntervalConnectedFromContr where
    is-1-connected-I-derived : isContr ∥ IntervalIsCHausModule.UnitInterval ∥₁
    is-1-connected-I-derived = ∣ fst IntervalIsCHausModule.isContrUnitInterval ∣₁ , λ _ → squash₁ _ _
