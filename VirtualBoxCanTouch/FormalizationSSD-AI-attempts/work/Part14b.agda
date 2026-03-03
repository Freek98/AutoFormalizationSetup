{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)
import work.Part12

module work.Part14b (fa : FoundationalAxioms) (ia : work.Part12.IntervalAxioms fa) where

open import work.Part14a fa ia public

open CohomologyModule public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_; isEquiv; invEquiv; equivFun; invEq; secEq)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.Transport using (transport⁻; transportTransport⁻)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; squash₁; ∣_∣₁)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Int using (ℤ)
open import Axioms.StoneDuality using (Booleω; Sp; Stone; hasStoneStr)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr; AbGroup→Group)
open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; 0ₖ; hLevelEM)
open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; 0ₕ; coHomGr)
import Cubical.Algebra.Group.Properties as GrpProps
import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp
open import Cubical.HITs.SetTruncation using (∥_∥₂; squash₂; ∣_∣₂)
open CompactHausdorffModule using (CHaus)

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
      T : Sp B → Type ℓ-zero
      T s = Σ[ t ∈ Sp C ] q t ≡ s

      T-inhabited : (s : Sp B) → ∥ T s ∥₁
      T-inhabited = q-surj

      SpB-CHaus : CompactHausdorffModule.hasCHausStr (Sp B)
      SpB-CHaus = snd (CompactHausdorffModule.Stone→CHaus (Sp B , B , refl))

      T-Stone : (s : Sp B) → hasStoneStr (T s)
      T-Stone s = ClosedInStoneIsStone (Sp C , C , refl) A A-closed
        where
        A : Sp C → hProp ℓ-zero
        A t = (q t ≡ s) , isSetSp (fst B) (q t) s
        A-closed : (t : Sp C) → isClosedProp (A t)
        A-closed t = CompactHausdorffModule.hasCHausStr.equalityClosed SpB-CHaus (q t) s

      β : (s : Sp B) (w : T s) → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1
      β s (t , qt≡s) = cong (λ s' → α (transport SpB≡S s')) (sym qt≡s) ∙ βraw t

      exactH : CechComplex.Ȟ¹-vanishes (Sp B) T (λ _ → ℤAbGroup)
      exactH = cech-complex-vanishing-stone (Sp B) T (B , refl)
                 (λ s → T-Stone s) T-inhabited

      vanish-trunc : ∥ ((s : Sp B) → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1) ∥₁
      vanish-trunc = exact-cech-complex-vanishing-cohomology (Sp B) T (λ _ → ℤAbGroup)
                  T-inhabited exactH (λ s → α (transport SpB≡S s)) β

      mk-eq : ((s : Sp B) → α (transport SpB≡S s) ≡ 0ₖ {G = ℤAbGroup} 1)
            → ∣ α ∣₂ ≡ 0ₕ 1 {G = ℤAbGroup} {A = |S|}
      mk-eq vanish' = cong ∣_∣₂ (funExt vanish) where
        vanish : (s : |S|) → α s ≡ 0ₖ {G = ℤAbGroup} 1
        vanish s = subst (λ s' → α s' ≡ 0ₖ {G = ℤAbGroup} 1) (transportTransport⁻ SpB≡S s)
                     (vanish' (transport (sym SpB≡S) s))

record CechCover : Type (ℓ-suc ℓ-zero) where
  field
    X : CHaus
    S : fst X → Stone
    fibers-inhabited : (x : fst X) → ∥ fst (S x) ∥₁
    total-is-Stone : hasStoneStr (Σ (fst X) (λ x → fst (S x)))

-- tex line 2910: Any CHaus X is part of a Čech cover.
open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.Foundations.Isomorphism using (isoToPath)

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

  roundtrip-H⁰ : (g : (x : S') → |A| x)
    → Ȟ⁰→H⁰ (H⁰→Ȟ⁰-f g) (H⁰→Ȟ⁰-cocycle g) ≡ g
  roundtrip-H⁰ g = funExt λ x →
    PT-Props.elim {P = λ t → PT-Props.SetElim.rec→Set (AGx.is-set x)
                       (H⁰→Ȟ⁰-f g x) (d₀-zero→const (H⁰→Ȟ⁰-f g) (H⁰→Ȟ⁰-cocycle g) x) t ≡ g x}
      (λ _ → AGx.is-set x _ _) (λ _ → refl) (inhabited x)

  roundtrip-Ȟ⁰ : (f : C⁰) (d₀-eq : (x : S') (u v : T x) → d₀ f x u v ≡ AGx.0g x)
    → (x : S') (u : T x) → H⁰→Ȟ⁰-f (Ȟ⁰→H⁰ f d₀-eq) x u ≡ f x u
  roundtrip-Ȟ⁰ f d₀-eq x u =
    cong (PT-Props.SetElim.rec→Set (AGx.is-set x) (f x) (d₀-zero→const f d₀-eq x))
         (squash₁ (inhabited x) ∣ u ∣₁)

-- tex Theorem 2945 (cech-eilenberg-1-agree): H¹(X,ℤ) = Ȟ¹(X,S,ℤ)

H¹-total-vanish : (cover : CechCover)
  → H¹-vanishes (Σ (fst (CechCover.X cover)) (λ x → fst (CechCover.S cover x)))
H¹-total-vanish cover = eilenberg-stone-vanish totalStone
  where open import Axioms.StoneDuality using (Stone)
        totalStone : Stone
        totalStone = Σ _ (λ x → fst (CechCover.S cover x)) , CechCover.total-is-Stone cover

-- tex Lemma 2921 (eilenberg-exact):

-- tex Lemma 2932 key step: Ȟ¹(X,S, ℤ^{S_x}) = 0 by canonical-exact
Ȟ¹-coefficient-vanish : (X : Type ℓ-zero) (T : X → Type ℓ-zero)
  → CanonicalExactCechComplex.Ȟ¹-vanishes X T (λ _ → ℤAbGroup)
Ȟ¹-coefficient-vanish X T = CanonicalExactCechComplex.canonical-exact X T (λ _ → ℤAbGroup)

-- tex Lemma 2843 (finite-approximation-surjection-stone):
