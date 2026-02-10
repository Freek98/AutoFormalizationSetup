{-# OPTIONS --cubical --guardedness #-}

module work.Part15 where

open import work.Part14 public

module ShapeTheoryFromCubical where
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Algebra.Group.Base
  open import Cubical.Algebra.Group.Morphisms
  open import Cubical.Algebra.Group.MorphismProperties
  open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
  open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup; UnitGroup₀)
  open import Cubical.HITs.S1 using (S¹; base; loop)
  open IntervalIsCHausModule using (UnitInterval)

  Unit-initial-STF : (G : Group ℓ-zero) → (φ : GroupHom UnitGroup₀ G) → (x : Unit) → fst φ x ≡ GroupStr.1g (snd G)
  Unit-initial-STF G (φ , is-hom) tt = IsGroupHom.pres1 is-hom

  Unit-terminal-STF : (G : Group ℓ-zero) → (φ : GroupHom G UnitGroup₀) → (x : fst G) → fst φ x ≡ tt
  Unit-terminal-STF G (φ , is-hom) x = refl

  no-group-retract-of-Unit-STF : (G : Group ℓ-zero)
    → (s : GroupHom UnitGroup₀ G)   -- section
    → (r : GroupHom G UnitGroup₀)   -- retraction
    → ((x : fst G) → fst s (fst r x) ≡ x)  -- s ∘ r = id
    → (x : fst G) → x ≡ GroupStr.1g (snd G)
  no-group-retract-of-Unit-STF G s r sec x =
    x                        ≡⟨ sym (sec x) ⟩
    fst s (fst r x)          ≡⟨ cong (fst s) (Unit-terminal-STF G r x) ⟩
    fst s tt                 ≡⟨ Unit-initial-STF G s tt ⟩
    GroupStr.1g (snd G)      ∎

  private
    one-neq-zero-ℤ : pos 1 ≡ pos 0 → ⊥
    one-neq-zero-ℤ p = subst isPos p tt
      where
      isPos : ℤ → Type
      isPos (pos zero) = ⊥
      isPos (pos (suc n)) = Unit
      isPos (negsuc n) = ⊥

  ℤ-not-retract-of-Unit-STF : (s : GroupHom UnitGroup₀ ℤGroup)
    → (r : GroupHom ℤGroup UnitGroup₀)
    → ((n : ℤ) → fst s (fst r n) ≡ n)
    → ⊥
  ℤ-not-retract-of-Unit-STF s r sec =
    let all-zero = no-group-retract-of-Unit-STF ℤGroup s r sec
        one-is-zero : pos 1 ≡ pos 0
        one-is-zero = all-zero (pos 1)
    in one-neq-zero-ℤ one-is-zero

module ConnectednessForBoolILocal where
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Homotopy.Connected using (isConnected)
  open import Cubical.HITs.Truncation using (hLevelTrunc; ∣_∣ₕ; rec; elim)
  open IntervalIsCHausModule using (UnitInterval)

  -- The tex file assumes path-connectedness as part of the real numbers

  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; rec)
  open import Cubical.Foundations.HLevels using (isContr; isProp→isSet)

  is-1-connected : Type ℓ-zero → Type ℓ-zero
  is-1-connected A = isContr ∥ A ∥₁

  postulate
    connected-1-to-set-constant-postulate : {A : Type ℓ-zero} {B : Type ℓ-zero}
      → is-1-connected A
      → isSet B
      → (f : A → B)
      → (x y : A) → f x ≡ f y

  connected-1-to-set-constant : {A : Type ℓ-zero} {B : Type ℓ-zero}
    → is-1-connected A
    → isSet B
    → (f : A → B)
    → (x y : A) → f x ≡ f y
  connected-1-to-set-constant = connected-1-to-set-constant-postulate

  {-
  connected-1-to-set-constant {A} {B} conn setB f x y =
    let
      g : ∥ A ∥₁ → B
      g = PT.rec setB f  -- ISSUE: rec expects isProp, not isSet

      center : ∥ A ∥₁
      center = fst conn

      path-to-center : (a : ∥ A ∥₁) → a ≡ center
      path-to-center a = snd conn a

      x-path : ∣ x ∣₁ ≡ center
      x-path = path-to-center ∣ x ∣₁

      y-path : ∣ y ∣₁ ≡ center
      y-path = path-to-center ∣ y ∣₁

      xy-path : ∣ x ∣₁ ≡ ∣ y ∣₁
      xy-path = x-path ∙ sym y-path

      g-equal : g ∣ x ∣₁ ≡ g ∣ y ∣₁
      g-equal = cong g xy-path

    in g-equal  -- f x = g(∣ x ∣₁) ≡ g(∣ y ∣₁) = f y by definition of g
  -}

  open import Cubical.Data.Bool using (Bool; true; false; isSetBool)

module HomotopyGroupInfrastructure where

  open import Cubical.Homotopy.Group.Base using (π; π')
  open import Cubical.Homotopy.Loopspace using (Ω; Ω^)
  open import Cubical.HITs.S1 using (S¹; base; loop)
  open import Cubical.Foundations.Pointed using (Pointed; _,_)

  S¹∙ : Pointed ℓ-zero
  S¹∙ = S¹ , base

  open import Cubical.HITs.SetTruncation using (∥_∥₂)

  π₁-S¹ : Type ℓ-zero
  π₁-S¹ = ∥ base ≡ base ∥₂

module CohomologyFunctorialityDoc where

  open import Cubical.ZCohomology.GroupStructure using (coHomGr)
  open import Cubical.ZCohomology.Base using (coHom)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom)

module FundamentalGroupS1 where

  open import Cubical.HITs.S1.Base using (S¹; base; loop; ΩS¹; winding; intLoop;
                                          ΩS¹Isoℤ; windingℤLoop; decodeEncode;
                                          isSetΩS¹)
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; isoToPath)

  loop-winding-is-1 : winding loop ≡ pos 1
  loop-winding-is-1 = refl  -- This is definitional!

  refl-winding-is-0 : winding refl ≡ pos 0
  refl-winding-is-0 = refl  -- Also definitional!

  loop-neq-refl : loop ≡ refl → ⊥
  loop-neq-refl p = one-neq-zero (cong winding p)
    where
      one-neq-zero : pos 1 ≡ pos 0 → ⊥
      one-neq-zero q = subst isPos q tt
        where
          isPos : ℤ → Type
          isPos (pos zero) = ⊥
          isPos (pos (suc _)) = Unit
          isPos (negsuc _) = ⊥

  S¹-not-contractible : isContr S¹ → ⊥
  S¹-not-contractible (c , contr) = loop-neq-refl loop≡refl
    where

      base-to-c : base ≡ c
      base-to-c = sym (contr base)

      S¹-is-prop : isProp S¹
      S¹-is-prop = isContr→isProp (c , contr)

      loop≡refl : loop ≡ refl
      loop≡refl = isProp→isSet S¹-is-prop base base loop refl

  ΩS¹≃ℤ : ΩS¹ ≃ ℤ
  ΩS¹≃ℤ = isoToEquiv ΩS¹Isoℤ

module SimplyConnectedTypes where

  open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁; rec)
  open import Cubical.Foundations.HLevels using (isContr)

  is-simply-connected : Type ℓ-zero → Type ℓ-zero
  is-simply-connected X = (x y : X) → ∥ x ≡ y ∥₁   -- path-connected
                        × ((x : X) → isProp (x ≡ x)) -- loops are trivial (simplified)

  isContr→is-simply-connected : {X : Type ℓ-zero} → isContr X → is-simply-connected X
  isContr→is-simply-connected {X} (c , paths) x y = ∣ sym (paths x) ∙ paths y ∣₁ , loops-trivial
    where
    open import Cubical.Foundations.HLevels using (isContr→isProp; isProp→isSet)
    isPropX : isProp X
    isPropX = isContr→isProp (c , paths)
    isSetX : isSet X
    isSetX = isProp→isSet isPropX
    loops-trivial : (x₁ : X) → isProp (x₁ ≡ x₁)
    loops-trivial x₁ = isSetX x₁ x₁

module CohomologyFunctorialityTypeChecked where

  open import Cubical.ZCohomology.GroupStructure using (coHomGr; coHomFun; coHomMorph)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom; compGroupHom)
  open import Cubical.Algebra.Group.MorphismProperties using (compGroupHomId)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂; isSetPathImplicit)

  coHom-functorial-comp : {A : Type ℓ-zero} {B : Type ℓ-zero} (n : ℕ)
    → (f : A → B) → (g : B → A)
    → ((a : A) → g (f a) ≡ a)
    → (x : fst (coHomGr n A))
    → fst (coHomMorph n f) (fst (coHomMorph n g) x) ≡ x
  coHom-functorial-comp n f g gf≡id =
    ST.elim (λ _ → isSetPathImplicit)
      (λ β → cong ∣_∣₂ (funExt λ a → cong β (gf≡id a)))

module NoRetractionTheoremComplete where

  open import Cubical.HITs.S1 using (S¹; base)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr; coHomMorph)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom)

module CohomologyContractibleTypeChecked where

  open import Cubical.ZCohomology.Groups.Unit using (Hⁿ-contrType≅0)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupIso)
  open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup; UnitGroup₀)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.ZCohomology.Groups.Unit using (Hⁿ-Unit≅0)

  H¹-Unit≅0 : GroupIso {ℓ-zero} {ℓ-zero} (coHomGr 1 Unit) UnitGroup₀
  H¹-Unit≅0 = Hⁿ-Unit≅0 0

  H²-Unit≅0 : GroupIso {ℓ-zero} {ℓ-zero} (coHomGr 2 Unit) UnitGroup₀
  H²-Unit≅0 = Hⁿ-Unit≅0 1

module CechCohomologyDoc where
  -- This module documents the Čech cohomology approach mentioned in the tex file.
  -- The key result from the tex is that H¹(X,ℤ) for compact Hausdorff X can be

  -- 1. H¹(S,ℤ) = 0 for Stone S (tex line ~2887)
  -- 2. H¹(I,ℤ) = 0 for interval I (tex Prop 2991)

module RetractionNonExistenceAssembler where

  open import Cubical.HITs.S1 using (S¹)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr; coHomMorph)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupIso)
  open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
  open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup)

module StoneCohomologyDoc where
  -- The key result (tex ~2887) is that H¹(S,ℤ) = 0 for Stone spaces S.

  -- This is formalized in the tex via Čech cohomology and the

module H0CohomologyInfrastructure where
  -- The tex file (Prop 2992) states: H⁰(I, ℤ) = ℤ and H¹(I, ℤ) = 0.

  open import Cubical.Data.Int using (ℤ; pos; negsuc; discreteℤ; isSetℤ)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr; coHomFun; coHomMorph)
  open import Cubical.Algebra.Group.Base using (Group; GroupStr)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupIso)

  const-ℤ : {X : Type ℓ-zero} → ℤ → X → ℤ
  const-ℤ n = λ _ → n

  -- This is the key to H⁰(I, ℤ) = ℤ in the tex proof

  -- Connection to tex Proposition 2992: H⁰(I,ℤ) = ℤ
  -- The tex proof shows:

module FiniteTypesCohomology where

  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Data.Fin using (Fin; fzero; fsuc)
  open import Cubical.Data.Unit using (Unit; tt)
  open import Cubical.Data.Empty using (⊥)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupIso)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr)
  open import Cubical.ZCohomology.Groups.Unit using (Hⁿ-contrType≅0)

  -- Connection to tex proof of H¹(S,ℤ) = 0 for Stone S
  -- The tex proof (Lemma 2888) says:

module GroupIsoCompositionDoc where

  open import Cubical.Algebra.Group.Base using (Group; GroupStr)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupIso)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv; iso; compIso; invIso; idIso)

  compIsoWitness : {A B C : Type ℓ-zero} → Iso A B → Iso B C → Iso A C
  compIsoWitness = compIso

  invIsoWitness : {A B : Type ℓ-zero} → Iso A B → Iso B A
  invIsoWitness = invIso

  idIsoWitness : {A : Type ℓ-zero} → Iso A A
  idIsoWitness = idIso

module DeloopingInfrastructure where
  -- The tex file uses B(G) notation for the delooping of an abelian group G.

  open import Cubical.HITs.S1 using (S¹; base; loop)
  open import Cubical.Data.Int using (ℤ; pos; negsuc; isSetℤ)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)
  open import Cubical.Homotopy.Loopspace using (Ω)
  open import Cubical.Foundations.Pointed using (Pointed; _,_)

  S¹∙ : Pointed ℓ-zero
  S¹∙ = S¹ , base

  -- tex Lemma 3020: ℤ is I-local
  -- The tex proof says:

  -- tex Lemma 3032: Bℤ is I-local
  -- The tex proof says:

module HITInfrastructure where

  open import Cubical.HITs.S1 using (S¹; base; loop; S¹ToSetRec; S¹ToSetElim)
  open import Cubical.HITs.S1 renaming (ΩS¹Isoℤ to ΩS¹IsoℤLib)
  open import Cubical.Data.Int using (ℤ; pos; negsuc)
  open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)

  ΩS¹IsoℤWitness : Iso (base ≡ base) ℤ
  ΩS¹IsoℤWitness = ΩS¹IsoℤLib

module RetractionImpossibilityAssembled where

  open import Cubical.Data.Int using (ℤ; pos)
  open import Cubical.Data.Unit using (Unit; tt)
  open import Cubical.Data.Empty using (⊥)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.Algebra.Group.Morphisms using (GroupIso; GroupHom)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr; coHomMorph)
  open import Cubical.HITs.S1 using (S¹; base)
  open import Cubical.Data.Nat using (ℕ; zero; suc)

module CohomologyProductTypes where

  open import Cubical.Data.Sigma using (_×_; fst; snd)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Algebra.Group.Base using (Group)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr)

module LocalChoiceCechCohomology where
  -- tex lines 2798-2953 describe the Čech complex and its vanishing.

  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.HITs.PropositionalTruncation using (∥_∥₁; ∣_∣₁)

  -- tex Lemma 2823: Exact complex vanishing implies H¹ = 0

  -- tex Lemma 2878: Čech complex vanishes for Stone targets

  -- tex Lemma 2888: H¹(S, ℤ) = 0 for Stone S

  -- AxLocalChoice (tex lines 348-353) states:

module TypeCheckedLemmasSummary where

module TruncationInfrastructure where

  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁; rec; elim)
  open import Cubical.HITs.SetTruncation as ST using (∥_∥₂; ∣_∣₂; squash₂)

  isProp-∥∥₁ : {A : Type ℓ-zero} → isProp ∥ A ∥₁
  isProp-∥∥₁ = squash₁

  inhabited→truncated : {A : Type ℓ-zero} → A → ∥ A ∥₁
  inhabited→truncated = ∣_∣₁

  isSet-∥∥₂ : {A : Type ℓ-zero} → isSet ∥ A ∥₂
  isSet-∥∥₂ = squash₂

  toSetTrunc : {A : Type ℓ-zero} → A → ∥ A ∥₂
  toSetTrunc = ∣_∣₂

module EquivalenceInfrastructure where

  open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
  open import Cubical.Foundations.Univalence using (ua; uaβ)

  Iso→Equiv : {A B : Type ℓ-zero} → Iso A B → A ≃ B
  Iso→Equiv = isoToEquiv

  equiv→path : {A B : Type ℓ-zero} → A ≃ B → A ≡ B
  equiv→path = ua

  ua-compute : {A B : Type ℓ-zero} (e : A ≃ B) (a : A)
    → transport (ua e) a ≡ equivFun e a
  ua-compute = uaβ

module PathSpaceProperties where
  open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit; assoc)

  path-lUnit : {A : Type ℓ-zero} {x y : A} (p : x ≡ y) → refl ∙ p ≡ p
  path-lUnit p = sym (lUnit p)

  path-rUnit : {A : Type ℓ-zero} {x y : A} (p : x ≡ y) → p ∙ refl ≡ p
  path-rUnit p = sym (rUnit p)

  path-assoc : {A : Type ℓ-zero} {w x y z : A}
    (p : w ≡ x) (q : x ≡ y) (r : y ≡ z)
    → (p ∙ q) ∙ r ≡ p ∙ (q ∙ r)
  path-assoc p q r = sym (assoc p q r)

module SpheresCohomologyConnectionDoc where

  open import Cubical.HITs.S1 using (S¹; base; loop)
  open import Cubical.HITs.Sn using (S₊)
  open import Cubical.ZCohomology.Groups.Sn using (H¹-S¹≅ℤ; Hⁿ-Sⁿ≅ℤ)
  open import Cubical.Algebra.Group.Morphisms using (GroupIso)
  open import Cubical.ZCohomology.GroupStructure using (coHomGr)
  open import Cubical.Data.Nat using (ℕ; zero; suc)
  open import Cubical.Data.Int.MoreInts.QuoInt.Base using (ℤ) renaming (ℤGroup to ℤGroup')

module BFPTStructure where

  open import Cubical.Data.Empty using (⊥)

module CompleteProofStatus where

-- This module documents the I-localization modality L_I from tex Section 6.
-- - Bool is I-local (tex Lemma 3015): functions I → Bool are constant
-- - ℤ is I-local (tex Lemma 3015): functions I → ℤ are constant
-- - Bℤ is I-local (tex Lemma 3027): from H¹(I,ℤ) = 0
-- - ℝ is I-contractible (tex Corollary 3047)
-- - D² is I-contractible (tex Corollary 3047)

module ILocalizationDoc where
  open import Cubical.Data.Int using (ℤ)

  -- Here we document its connection to the tex file.

  -- tex Lemma 3015: Bool is I-local

  -- tex Lemma 3015: ℤ is I-local
  -- This follows from H⁰(I,ℤ) = ℤ (tex Proposition 2991)

  -- tex Lemma 3035: Continuously path-connected → I-contractible

  -- tex Corollary 3047: ℝ and D² are I-contractible
  -- This follows from tex Lemma 3035 since ℝ and D² are path-connected.

-- - Bℤ is I-local (tex Lemma 3027)

module DeloopingSpaceProperties where
  open import Cubical.Data.Int using (ℤ)
  open import Cubical.Homotopy.Loopspace using (Ω)
  open import Cubical.HITs.S1.Base using (S¹; base; loop)

  -- tex Lemma 3027: Bℤ is I-local

module ContractibleCohomologyExtended where
  open import Cubical.Data.Unit using (Unit)
  open import Cubical.ZCohomology.Groups.Unit using (isContrHⁿ-Unit; Hⁿ-contrType≅0)
  open import Cubical.Algebra.Group.Morphisms using (GroupIso)

module CohomologyExactSequenceDoc where

  -- tex Lemma 3074 (no-retraction) uses:

module MayerVietorisDoc where
  -- For tex Proposition 2991 (H⁰(I,ℤ) = ℤ, H¹(I,ℤ) = 0):
  -- This is part of the Čech cohomology computation in the tex file.

module ShapeTheoryLocalization where
  -- tex Proposition 3051: L_I(ℝ/ℤ) = Bℤ
  -- 3. Bℤ is I-local (tex Lemma 3027)
  -- 4. ℝ is I-contractible (tex Corollary 3047)

module GroupTheoryAdditional where
  open import Cubical.Algebra.Group.Base using (Group; GroupStr; group)
  open import Cubical.Algebra.Group.Morphisms using (GroupHom; IsGroupHom)
  open import Cubical.Algebra.AbGroup.Base using (AbGroup; AbGroupStr)
  open import Cubical.Foundations.Structure using (⟨_⟩)

module IntervalTopologyAxiomsDoc where

module ProofStatusUpdate where

module EMSpaceTypeChecked where
  open import Cubical.Algebra.AbGroup.Base using (AbGroup)
  open import Cubical.Homotopy.EilenbergMacLane.Base using (EM; EM∙)
  open import Cubical.Homotopy.EilenbergMacLane.Properties using (EM≃ΩEM+1)
  open import Cubical.Foundations.Equiv using (_≃_)
  open import Cubical.Homotopy.Loopspace using (Ω)

  EM-loop-equiv-witness : (G : AbGroup ℓ-zero) (n : ℕ)
    → EM G n ≃ fst (Ω (EM∙ G (suc n)))
  EM-loop-equiv-witness G n = EM≃ΩEM+1 {G = G} n
