{-# OPTIONS --cubical --guardedness #-}

open import work.Part02Defs using (FoundationalAxioms)
import work.Part12

module work.Part14 (fa : FoundationalAxioms) (ia : work.Part12.IntervalAxioms fa) where

open import work.Part14b fa ia public

-- tex Corollary 2895 (stone-commute-delooping):

module StoneCommuteDeloopingModule where
  open import Cubical.HITs.SetTruncation as ST
  open import Cubical.HITs.PropositionalTruncation as PT
  open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)
  open import Cubical.Homotopy.Connected using (isConnectedPath)
  open import Cubical.HITs.Truncation.Properties using (propTruncTrunc1Iso)
  open import StoneSpaces.Spectrum using (Stone; hasStoneStr)
  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.HLevels
  open import Cubical.Foundations.Equiv using (isEquiv; invEquiv; isPropIsEquiv)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToIsEquiv; compIso; invIso)
  open import Cubical.Data.Int using (ℤ)
  open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
  open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroup→Group)
  open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; 0ₖ)
  open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; 0ₕ)
  open import Cubical.HITs.SetTruncation using (∥_∥₂; squash₂; ∣_∣₂)

  BZ-funspace-connected : (S : Type ℓ-zero) → H¹-vanishes S
    → (f : S → BZ) → ∥ f ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1) ∥₁
  BZ-funspace-connected S h1v f =
    ST.PathIdTrunc₀Iso .Iso.fun (h1v ∣ f ∣₂)

  BZ-Stone-funspace-connected : (S : Stone) → (f : fst S → BZ)
    → ∥ f ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1) ∥₁
  BZ-Stone-funspace-connected S f =
    BZ-funspace-connected (fst S) (eilenberg-stone-vanish S) f

  open import Cubical.Homotopy.EilenbergMacLane.Properties using (inducedFun-EM)
  open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠAbGroup)
  open import Cubical.Algebra.AbGroup.Base using (AbGroupHom)

  evHom : (X : Type ℓ-zero) (s : X) → AbGroupHom (ΠAbGroup (λ (_ : X) → ℤAbGroup)) ℤAbGroup
  fst (evHom X s) f = f s
  snd (evHom X s) = record { pres· = λ _ _ → refl
                            ; pres1 = refl
                            ; presinv = λ _ → refl }

  canonicalMap : (X : Type ℓ-zero) → EM (ΠAbGroup (λ (_ : X) → ℤAbGroup)) 1 → (X → BZ)
  canonicalMap X x s = inducedFun-EM {G' = ΠAbGroup (λ (_ : X) → ℤAbGroup)} {H' = ℤAbGroup} (evHom X s) 1 x

  open import Cubical.Homotopy.Connected using (isConnected)

  BZX-connected : (X : Type ℓ-zero) → isConnected 2 (EM (ΠAbGroup (λ (_ : X) → ℤAbGroup)) 1)
  BZX-connected X = isConnectedEM {G' = ΠAbGroup (λ (_ : X) → ℤAbGroup)} 1

  BZ-funspace-set-trunc-contr : (S : Stone)
    → isContr (∥ (fst S → BZ) ∥₂)
  BZ-funspace-set-trunc-contr S =
    ∣ (λ _ → 0ₖ {G = ℤAbGroup} 1) ∣₂ ,
    ST.elim (λ _ → isSetPathImplicit) (λ f → sym (eilenberg-stone-vanish S ∣ f ∣₂))

  open import Cubical.Homotopy.WhiteheadsLemma using (ΩEquiv→Equiv)
  open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
  open import Cubical.Homotopy.Loopspace using (Ω→)
  open import Cubical.HITs.Truncation.Properties using (setTrunc≃Trunc2)

  private
    G : Type ℓ-zero → AbGroup ℓ-zero
    G X = ΠAbGroup (λ (_ : X) → ℤAbGroup)

    source-set-trunc-contr : (X : Type ℓ-zero) → isConnected 2 (EM (G X) 1)
      → isContr (∥ EM (G X) 1 ∥₂)
    source-set-trunc-contr X conn = isOfHLevelRespectEquiv 0 (invEquiv setTrunc≃Trunc2) conn

    map-canonicalMap-isEquiv : (S : Stone)
      → isEquiv (ST.map (canonicalMap (fst S)))
    map-canonicalMap-isEquiv S = isEquivFromIsContr (ST.map (canonicalMap (fst S)))
      (source-set-trunc-contr (fst S) (BZX-connected (fst S)))
      (BZ-funspace-set-trunc-contr S)

    open import Cubical.Foundations.GroupoidLaws using (doubleCompPath-elim; rUnit; lUnit)

    Ω→-at-base-is-cong : (X : Type ℓ-zero) (q : 0ₖ {G = G X} 1 ≡ 0ₖ {G = G X} 1)
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

    open import Cubical.Homotopy.EilenbergMacLane.Properties using (Iso-EM-ΩEM+1)
    open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)

    ΩEM₁ : (H : AbGroup ℓ-zero) → Iso (fst H) (0ₖ {G = H} 1 ≡ 0ₖ {G = H} 1)
    ΩEM₁ H = Iso-EM-ΩEM+1 {G = H} 0

    target-loop-iso : (X : Type ℓ-zero) → Iso ((x : X) → ℤ) ((λ (_ : X) → 0ₖ {G = ℤAbGroup} 1) ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1))
    Iso.fun (target-loop-iso X) g = funExt (λ s → Iso.fun (ΩEM₁ ℤAbGroup) (g s))
    Iso.inv (target-loop-iso X) p s = Iso.inv (ΩEM₁ ℤAbGroup) (funExt⁻ p s)
    Iso.sec (target-loop-iso X) p =
      funExt (λ s → Iso.fun (ΩEM₁ ℤAbGroup) (Iso.inv (ΩEM₁ ℤAbGroup) (funExt⁻ p s)))
        ≡⟨ cong funExt (funExt (λ s → Iso.sec (ΩEM₁ ℤAbGroup) (funExt⁻ p s))) ⟩
      funExt (funExt⁻ p)
        ≡⟨ refl ⟩
      p ∎
    Iso.ret (target-loop-iso X) g = funExt (λ s → Iso.ret (ΩEM₁ ℤAbGroup) (g s))

    Ω-iso : (X : Type ℓ-zero) → Iso (0ₖ {G = G X} 1 ≡ 0ₖ {G = G X} 1) ((λ _ → 0ₖ {G = ℤAbGroup} 1) ≡ (λ _ → 0ₖ {G = ℤAbGroup} 1))
    Ω-iso X = compIso (invIso (ΩEM₁ (G X))) (target-loop-iso X)

    canonicalMap-on-emloop : (X : Type ℓ-zero) (g : fst (G X))
      → cong (canonicalMap X) (emloop g)
      ≡ funExt (λ s → emloop (g s))
    canonicalMap-on-emloop X g = refl

    cong-canonicalMap-on-emloop : (X : Type ℓ-zero) (g : fst (G X))
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

    cong-canonicalMap-is-Ω-iso : (X : Type ℓ-zero) (q : 0ₖ {G = G X} 1 ≡ 0ₖ {G = G X} 1)
      → cong (canonicalMap X) q ≡ Iso.fun (Ω-iso X) q
    cong-canonicalMap-is-Ω-iso X q =
      cong (canonicalMap X) q
        ≡⟨ cong (cong (canonicalMap X)) (sym (Iso.sec (ΩEM₁ (G X)) q)) ⟩
      cong (canonicalMap X) (emloop (Iso.inv (ΩEM₁ (G X)) q))
        ≡⟨ cong-canonicalMap-on-emloop X (Iso.inv (ΩEM₁ (G X)) q) ⟩
      Iso.fun (Ω-iso X) (emloop (Iso.inv (ΩEM₁ (G X)) q))
        ≡⟨ cong (Iso.fun (Ω-iso X)) (Iso.sec (ΩEM₁ (G X)) q) ⟩
      Iso.fun (Ω-iso X) q ∎

    cong-canonicalMap-isEquiv : (X : Type ℓ-zero)
      → isEquiv (cong {x = 0ₖ {G = G X} 1} {y = 0ₖ {G = G X} 1} (canonicalMap X))
    cong-canonicalMap-isEquiv X = subst isEquiv
      (sym (funExt (cong-canonicalMap-is-Ω-iso X)))
      (isoToIsEquiv (Ω-iso X))

    Ω→-isEquiv-at-base : (X : Type ℓ-zero)
      → isEquiv (fst (Ω→ {A = EM (G X) 1 , 0ₖ {G = G X} 1} {B = (X → BZ) , (λ _ → 0ₖ {G = ℤAbGroup} 1)}
                      (canonicalMap X , refl)))
    Ω→-isEquiv-at-base X = subst isEquiv (sym (funExt (Ω→-at-base-is-cong X)))
      (cong-canonicalMap-isEquiv X)

    Ω→-isEquiv-all : (X : Type ℓ-zero)
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

  stone-commute-delooping : (S : Stone) → isEquiv (canonicalMap (fst S))
  stone-commute-delooping S = ΩEquiv→Equiv (canonicalMap (fst S))
    (map-canonicalMap-isEquiv S)
    (Ω→-isEquiv-all (fst S) (BZX-connected (fst S)))

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; 0ₖ)
open import Cubical.Cohomology.EilenbergMacLane.Base using (coHom; 0ₕ; coHomGr)
import Cubical.Homotopy.EilenbergMacLane.Properties as EMProp
open import Cubical.Foundations.Isomorphism using (Iso)

¬isContr-BZ : isContr BZ → ⊥
¬isContr-BZ contr = 0≢1-ℤ (all-eq (pos 0) (pos 1))
  where
  open import Cubical.Data.Int using (pos)
  open import Cubical.Data.Int.Properties using (0≢1-ℤ)
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

-- tex Lemma 2973 (Cn-exact-sequence):

-- tex Proposition 2991 (cohomology-I): H⁰(I,ℤ)≅ℤ and H¹(I,ℤ)=0
open import Cubical.Cohomology.EilenbergMacLane.Groups.Unit using (isContr-Hⁿ⁺¹[Unit,G]; H⁰[Unit,G]≅G)
open import Cubical.Foundations.Equiv using (isContr→Equiv)
open import Cubical.Algebra.AbGroup.Base using (AbGroupEquiv)

private
  I≡Unit : UnitInterval ≡ Unit
  I≡Unit = ua (isContr→Equiv isContrUnitInterval (tt , λ {tt → refl}))

H⁰-Interval≅ℤ : AbGroupEquiv (coHomGr 0 ℤAbGroup UnitInterval) ℤAbGroup
H⁰-Interval≅ℤ = subst (λ X → AbGroupEquiv (coHomGr 0 ℤAbGroup X) ℤAbGroup)
                   (sym I≡Unit) H⁰[Unit,G]≅G

isContr-Hⁿ⁺¹-Interval : (n : ℕ) → isContr (coHom (suc n) ℤAbGroup UnitInterval)
isContr-Hⁿ⁺¹-Interval n = subst (λ X → isContr (coHom (suc n) ℤAbGroup X)) (sym I≡Unit)
                  (isContr-Hⁿ⁺¹[Unit,G] {G = ℤAbGroup} n)

H¹-vanishes-Interval : H¹-vanishes UnitInterval
H¹-vanishes-Interval x = isContr→isProp (isContr-Hⁿ⁺¹-Interval 0) x
                            (0ₕ 1 {G = ℤAbGroup} {A = UnitInterval})
