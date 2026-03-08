{-# OPTIONS --cubical --guardedness #-}

-- Bridge between B∞ and ℕfinCofinBA via their presentations.
-- B∞ = freeBA ℕ /Im relB∞ (orthogonality via Cantor pairing)
-- presentation = freeBA ℕ /Im relationsℕ (orthogonality via ℕ×ℕ pairing)
-- ℕfinCofinBA ≅ presentation (from NFinCofin.Presentation)
-- Therefore B∞ ≅ ℕfinCofinBA.

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneDuality.NFinCofin.Bridge (fa : FoundationalAxioms) where

open import formalization.StoneDuality.BooleanAlgebra fa
open import formalization.StoneDuality.NFinCofin.Definitions
open import formalization.StoneDuality.NFinCofin.Presentation

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; isoToIsEquiv; Iso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; _and_)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true)
open import Cubical.Relation.Nullary using (Dec; yes; no)
  renaming (¬_ to ¬Type_)
import formalization.Library.QuotientBool as QB
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool
  using (freeBA; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import formalization.Library.CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; invBooleanRingEquiv)
open import Cubical.Data.Empty renaming (rec to ex-falso)
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)

-- Step 1: The freeℕ→ℕFinCof homomorphism kills the B∞ relations.
-- B∞ relations: gen(a) · gen(a + suc(d)) for each k (via Cantor unpair)
-- These are just gen(i) · gen(j) with i ≠ j, which the NFinCofin presentation handles.

private
  module FC = BooleanRingStr (snd ℕfinCofinBA)
  _·f_ = BooleanRingStr._·_ (snd (freeBA ℕ))
  eval-gen : (m : ℕ) → fst freeℕ→ℕFinCof (gen m) ≡ singleton m
  eval-gen m = funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) m

freeℕ→ℕFinCof-kills-relB∞ : (k : ℕ) →
  fst freeℕ→ℕFinCof (relB∞ k) ≡ FC.𝟘
freeℕ→ℕFinCof-kills-relB∞ k =
  let (a , d) = cantorUnpair k
      n = a +ℕ suc d
      a≠n : ¬Type (a ≡ n)
      a≠n p = znots (inj-m+ (+-zero a ∙ p))
  in
  fst freeℕ→ℕFinCof (gen a ·f gen n)
    ≡⟨ IsCommRingHom.pres· (snd freeℕ→ℕFinCof) (gen a) (gen n) ⟩
  FC._·_ (fst freeℕ→ℕFinCof (gen a)) (fst freeℕ→ℕFinCof (gen n))
    ≡⟨ cong₂ FC._·_ (eval-gen a) (eval-gen n) ⟩
  FC._·_ (singleton a) (singleton n)
    ≡⟨ FC≡ (funExt (δn∧δm=0 a n a≠n)) ⟩
  FC.𝟘 ∎

-- Step 2: Factor freeℕ→ℕFinCof through B∞ to get φ_FC : B∞ → ℕfinCofinBA
φ_FC : BoolHom B∞ ℕfinCofinBA
φ_FC = QB.inducedHom ℕfinCofinBA freeℕ→ℕFinCof freeℕ→ℕFinCof-kills-relB∞

-- Step 3: The NFinCofin presentation map gen(n) ↦ g∞(n) kills the presentation relations.
-- The presentation relations are gen(i) · gen(j) = 0 for i ≠ j (via ℕ×ℕ pairing).
-- In B∞, distinct generators multiply to zero.

g∞-kills-relationsℕ : (k : ℕ) →
  fst (inducedBAHom ℕ B∞ g∞) (relationsℕ k) ≡ 𝟘∞
g∞-kills-relationsℕ k =
  let (i , j) = Iso.inv ℕ×ℕ≅ℕ k
  in go i j
  where
  g∞-free : BoolHom (freeBA ℕ) B∞
  g∞-free = inducedBAHom ℕ B∞ g∞

  g∞-free-eval : fst g∞-free ∘ gen ≡ g∞
  g∞-free-eval = evalBAInduce ℕ B∞ g∞

  go : (i j : ℕ) → fst g∞-free (relations (i , j)) ≡ 𝟘∞
  go i j with discreteℕ i j
  ... | yes _ = IsCommRingHom.pres0 (snd g∞-free)
  ... | no i≠j =
    fst g∞-free (gen i ·f gen j)
      ≡⟨ IsCommRingHom.pres· (snd g∞-free) (gen i) (gen j) ⟩
    (fst g∞-free (gen i)) ·∞ (fst g∞-free (gen j))
      ≡⟨ cong₂ _·∞_ (funExt⁻ g∞-free-eval i) (funExt⁻ g∞-free-eval j) ⟩
    g∞ i ·∞ g∞ j
      ≡⟨ g∞-distinct-mult-zero i j i≠j ⟩
    𝟘∞ ∎

-- Step 4: Factor through the presentation to get ψ_FC : presentation → B∞
private
  g∞-free : BoolHom (freeBA ℕ) B∞
  g∞-free = inducedBAHom ℕ B∞ g∞

  g∞-free-eval : fst g∞-free ∘ gen ≡ g∞
  g∞-free-eval = evalBAInduce ℕ B∞ g∞

ψ_pres : BoolHom presentation B∞
ψ_pres = QB.inducedHom B∞ g∞-free g∞-kills-relationsℕ

-- Step 5: The composite φ_FC ∘ ψ_FC_from_pres and ψ_FC_from_pres ∘ φ_FC_to_pres
-- are identities, which we show via universality on generators.

-- φ_FC sends g∞(n) to singleton(n)
opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  φ_FC-on-gen : (n : ℕ) → fst φ_FC (g∞ n) ≡ singleton n
  φ_FC-on-gen n =
    fst φ_FC (fst π∞ (gen n))
      ≡⟨ funExt⁻ (cong fst (QB.evalInduce {B = freeBA ℕ} {f = relB∞} ℕfinCofinBA)) (gen n) ⟩
    fst freeℕ→ℕFinCof (gen n)
      ≡⟨ funExt⁻ (evalBAInduce ℕ ℕfinCofinBA singleton) n ⟩
    singleton n ∎

-- ψ_pres sends π(gen(n)) to g∞(n)
opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  ψ_pres-on-gen : (n : ℕ) → fst ψ_pres (fst π (gen n)) ≡ g∞ n
  ψ_pres-on-gen n =
    fst ψ_pres (fst π (gen n))
      ≡⟨ funExt⁻ (cong fst (QB.evalInduce {B = freeBA ℕ} {f = relationsℕ} B∞)) (gen n) ⟩
    fst g∞-free (gen n)
      ≡⟨ funExt⁻ g∞-free-eval n ⟩
    g∞ n ∎

-- Step 6: Build ψ_FC : ℕfinCofinBA → B∞ using the presentation equivalence
-- ℕFinCof=Presentation : BooleanRingEquiv presentation ℕfinCofinBA
-- So we compose: ℕfinCofinBA →[inv]→ presentation →[ψ_pres]→ B∞

private
  presEquiv : BooleanRingEquiv presentation ℕfinCofinBA
  presEquiv = ℕFinCof=Presentation

  pres→FC : BoolHom presentation ℕfinCofinBA
  pres→FC = (fst (fst presEquiv)) , snd presEquiv

  FC→pres-fun : ⟨ ℕfinCofinBA ⟩ → ⟨ presentation ⟩
  FC→pres-fun = ℕFinCof→Presentation

  FC→pres : BoolHom ℕfinCofinBA presentation
  FC→pres = ℕFinCof→PresentationHom

ψ_FC : BoolHom ℕfinCofinBA B∞
ψ_FC = ψ_pres ∘cr FC→pres

-- Step 7: Roundtrip φ_FC ∘ ψ_FC = id on ℕfinCofinBA
-- We show: φ_FC (ψ_FC x) = x for all x

private
  -- First, φ_FC ∘ ψ_pres ∘ π agrees with freeℕ→ℕFinCof on generators
  opaque
    unfolding QB.inducedHom
    unfolding QB.quotientImageHom
    φ∘ψ∘π-on-gen : (n : ℕ) → fst (φ_FC ∘cr ψ_pres ∘cr π) (gen n) ≡ singleton n
    φ∘ψ∘π-on-gen n =
      fst φ_FC (fst ψ_pres (fst π (gen n)))
        ≡⟨ cong (fst φ_FC) (ψ_pres-on-gen n) ⟩
      fst φ_FC (g∞ n)
        ≡⟨ φ_FC-on-gen n ⟩
      singleton n ∎

  φ∘ψ∘π≡freeHom : φ_FC ∘cr ψ_pres ∘cr π ≡ freeℕ→ℕFinCof
  φ∘ψ∘π≡freeHom =
    sym (inducedBAHomUnique ℕ ℕfinCofinBA singleton (φ_FC ∘cr ψ_pres ∘cr π) (funExt φ∘ψ∘π-on-gen))
    ∙ inducedBAHomUnique ℕ ℕfinCofinBA singleton freeℕ→ℕFinCof (evalBAInduce ℕ ℕfinCofinBA singleton)

-- The roundtrip on ℕfinCofinBA: φ_FC (ψ_FC x) = x
-- ψ_FC = ψ_pres ∘ FC→pres
-- So φ_FC (ψ_FC x) = φ_FC (ψ_pres (FC→pres x))
-- We use: fH-section from Presentation.agda and the roundtrip above.

roundtrip-FC : (x : ⟨ ℕfinCofinBA ⟩) → fst φ_FC (fst ψ_FC x) ≡ x
roundtrip-FC x =
  fst φ_FC (fst ψ_FC x)
    ≡⟨ cong (fst φ_FC ∘ fst ψ_pres) (roundtrip-pre-on-free-lemma x) ⟩
  fst φ_FC (fst ψ_pres (fst π (ℕFinCof→FreeℕMap x)))
    ≡⟨ funExt⁻ (cong fst φ∘ψ∘π≡freeHom) (ℕFinCof→FreeℕMap x) ⟩
  fst freeℕ→ℕFinCof (ℕFinCof→FreeℕMap x)
    ≡⟨ fH-section x ⟩
  x ∎
  where
  -- ℕFinCof→Presentation x = fst π (ℕFinCof→FreeℕMap x) by definition
  roundtrip-pre-on-free-lemma : (x : ⟨ ℕfinCofinBA ⟩) →
    FC→pres-fun x ≡ fst π (ℕFinCof→FreeℕMap x)
  roundtrip-pre-on-free-lemma x = refl

-- Step 8: Roundtrip ψ_FC ∘ φ_FC = id on B∞
-- We show ψ_FC (φ_FC x) = x for all x ∈ B∞

private
  opaque
    unfolding QB.inducedHom
    unfolding QB.quotientImageHom
    ψ∘φ∘π-on-gen : (n : ℕ) → fst (ψ_FC ∘cr φ_FC ∘cr π∞) (gen n) ≡ fst π∞ (gen n)
    ψ∘φ∘π-on-gen n =
      fst ψ_FC (fst φ_FC (g∞ n))
        ≡⟨ cong (fst ψ_FC) (φ_FC-on-gen n) ⟩
      fst ψ_FC (singleton n)
        ≡⟨ cong (fst ψ_pres) (singleton→gen n) ⟩
      fst ψ_pres (fst π (gen n))
        ≡⟨ ψ_pres-on-gen n ⟩
      g∞ n ∎

  ψ∘φ∘π≡π : ψ_FC ∘cr φ_FC ∘cr π∞ ≡ π∞
  ψ∘φ∘π≡π =
    sym (inducedBAHomUnique ℕ B∞ g∞ (ψ_FC ∘cr φ_FC ∘cr π∞) (funExt ψ∘φ∘π-on-gen))
    ∙ inducedBAHomUnique ℕ B∞ g∞ π∞ refl

roundtrip-B∞ : (x : ⟨ B∞ ⟩) → fst ψ_FC (fst φ_FC x) ≡ x
roundtrip-B∞ = go
  where
  opaque
    unfolding QB._/Im_
    unfolding QB.quotientImageHom
    go : (x : ⟨ B∞ ⟩) → fst ψ_FC (fst φ_FC x) ≡ x
    go = SQ.elimProp (λ _ → BooleanRingStr.is-set (snd B∞) _ _)
           (λ a → funExt⁻ (cong fst ψ∘φ∘π≡π) a)

-- The main result: B∞ ≅ ℕfinCofinBA
B∞≅ℕfinCofinBA : BooleanRingEquiv B∞ ℕfinCofinBA
B∞≅ℕfinCofinBA =
  (fst φ_FC , isoToIsEquiv (iso (fst φ_FC) (fst ψ_FC) roundtrip-FC roundtrip-B∞))
  , snd φ_FC
