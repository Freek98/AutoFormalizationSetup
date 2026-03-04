{-# OPTIONS --cubical --guardedness #-}
module work.test-boole-odisc where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; invEq; compEquiv; equivFun; secEq)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
open import Cubical.Foundations.HLevels using (isPropΠ; isSetΣ)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat using (ℕ; zero; suc) renaming (_+_ to _+ℕ_)
open import Cubical.Data.Nat.Order using (_<_; <Dec; ≤-refl; _≤_)
open import Cubical.Data.Fin using (Fin; toℕ)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Relation.Nullary using (Dec; yes; no)

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)

open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; inducedBAHomUnique; evalBAInduce; freeBA-universal-property)
open import BooleanRing.FreeBooleanRing.freeBATerms using (freeBATerms; includeBATermsSurj)
open import BooleanRing.FreeBooleanRing.SurjectiveTerms using (TermsOf_[_]; Tvar; Tconst; _+T_; -T_; _·T_)
open import Cubical.Algebra.CommRing.Instances.Bool using (BoolCR)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; idBoolHom; BooleanRingEquiv)
open import Axioms.StoneDuality using (Booleω; Sp; StoneDualityAxiom; evaluationMap; SDHomVersion; 2^)
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
import QuotientBool as QB

-- Test: Sp(freeBA (Fin n)) ≅ (Fin n → Bool)
-- By universal property: BoolHom (freeBA (Fin n)) BoolBR ≅ (Fin n → Bool)
module SpFreeBAFin (n : ℕ) where
  open BooleanRingStr

  SpFreeBA : Type ℓ-zero
  SpFreeBA = BoolHom (freeBA (Fin n)) BoolBR

  -- Forward: SpFreeBA → (Fin n → Bool)
  fwd : SpFreeBA → (Fin n → Bool)
  fwd h = fst h ∘ generator

  -- Backward: (Fin n → Bool) → SpFreeBA
  bwd : (Fin n → Bool) → SpFreeBA
  bwd f = inducedBAHom (Fin n) BoolBR f

  -- Section: fwd (bwd f) = f
  sec : (f : Fin n → Bool) → fwd (bwd f) ≡ f
  sec f = evalBAInduce (Fin n) BoolBR f

  -- Retraction: bwd (fwd h) = h
  ret : (h : SpFreeBA) → bwd (fwd h) ≡ h
  ret h = inducedBAHomUnique (Fin n) BoolBR (fst h ∘ generator) h refl

  theIso : Iso SpFreeBA (Fin n → Bool)
  theIso = iso fwd bwd sec ret

  theEquiv : SpFreeBA ≃ (Fin n → Bool)
  theEquiv = isoToEquiv theIso

-- Step 2: freeBA (Fin n) has Booleω structure
-- Strategy: freeBA (Fin n) ≅ freeBA ℕ /Im kill where kill(k) = generator(n+k)
module FreeBAFinBooleω (n : ℕ) where
  open BooleanRingStr

  private
    freeBA-ℕ = freeBA ℕ
    freeBA-n = freeBA (Fin n)

  -- The relations: kill generators ≥ n
  killRel : ℕ → ⟨ freeBA-ℕ ⟩
  killRel k = generator (n +ℕ k)

  -- The quotient ring
  Qn : BooleanRing ℓ-zero
  Qn = freeBA-ℕ QB./Im killRel

  -- Quotient map
  πQ : ⟨ freeBA-ℕ ⟩ → ⟨ Qn ⟩
  πQ = QB.quotientImageHom {B = freeBA-ℕ} {f = killRel} .fst

  -- Forward: freeBA (Fin n) → Qn
  -- Send generator i to πQ(generator(toℕ i))
  fwd-on-gen : Fin n → ⟨ Qn ⟩
  fwd-on-gen i = πQ (generator (fst i))

  fwd-hom : BoolHom freeBA-n Qn
  fwd-hom = inducedBAHom (Fin n) Qn fwd-on-gen

  -- Backward: Qn → freeBA (Fin n)
  -- First define the map ℕ → ⟨ freeBA (Fin n) ⟩
  -- k ↦ generator(k, proof) if k < n, else 0
  open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ)

  bwd-gen : ℕ → ⟨ freeBA-n ⟩
  bwd-gen k with <Dec k n
  ... | yes p = generator (k , <→<ᵗ p)
  ... | no _  = 𝟘 (snd freeBA-n)

  -- This induces BoolHom freeBA ℕ → freeBA (Fin n)
  bwd-free : BoolHom freeBA-ℕ freeBA-n
  bwd-free = inducedBAHom ℕ freeBA-n bwd-gen

  -- bwd-free kills killRel: bwd-gen(n+k) = 0
  bwd-kills : (k : ℕ) → fst bwd-free (killRel k) ≡ 𝟘 (snd freeBA-n)
  bwd-kills k = step₁ ∙ step₂ where
    step₁ : fst bwd-free (killRel k) ≡ bwd-gen (n +ℕ k)
    step₁ = cong (λ f → f (n +ℕ k)) (evalBAInduce ℕ freeBA-n bwd-gen)
    step₂ : bwd-gen (n +ℕ k) ≡ 𝟘 (snd freeBA-n)
    step₂ with <Dec (n +ℕ k) n
    ... | yes p = ⊥.rec (¬m+n<m p) where
          open import Cubical.Data.Nat.Order using (¬m+n<m)
          open import Cubical.Data.Empty as ⊥
    ... | no _  = refl

  -- Factor through quotient: BoolHom Qn → freeBA (Fin n)
  bwd-hom : BoolHom Qn freeBA-n
  bwd-hom = QB.inducedHom {B = freeBA-ℕ} {f = killRel} freeBA-n bwd-free bwd-kills

  -- Roundtrip 1: bwd-hom ∘ fwd-hom = id on freeBA (Fin n)
  -- On generators: bwd(fwd(gen(i))) = bwd(πQ(gen(toℕ i))) = bwd-gen(toℕ i) = gen(i)
  -- (since toℕ i < n)
  postulate
    roundtrip₁ : (x : ⟨ freeBA-n ⟩) → fst bwd-hom (fst fwd-hom x) ≡ x

  -- Roundtrip 2: fwd-hom ∘ bwd-hom = id on Qn
  postulate
    roundtrip₂ : (x : ⟨ Qn ⟩) → fst fwd-hom (fst bwd-hom x) ≡ x

  equiv : BooleanRingEquiv freeBA-n Qn
  equiv = isoToEquiv (iso (fst fwd-hom) (fst bwd-hom) roundtrip₂ roundtrip₁) , snd fwd-hom

  hasBooleω : has-Boole-ω' freeBA-n
  hasBooleω = killRel , equiv

  freeBA-Fin-Booleω : Booleω
  freeBA-Fin-Booleω = freeBA-n , ∣ hasBooleω ∣₁

-- Step 3: Using SD, show freeBA (Fin n) is finite
module FreeBAFinFinite (SD : StoneDualityAxiom) (n : ℕ) where
  open FreeBAFinBooleω n
  open SpFreeBAFin n

  -- Sp(freeBA (Fin n)) as Booleω
  SpFinBA : Type ℓ-zero
  SpFinBA = Sp freeBA-Fin-Booleω

  -- SD gives: ⟨ freeBA (Fin n) ⟩ ≃ (SpFinBA → Bool)
  sd-equiv : ⟨ freeBA (Fin n) ⟩ ≃ (SpFinBA → Bool)
  sd-equiv = SDHomVersion SD freeBA-Fin-Booleω .fst

  -- SpFinBA = BoolHom (freeBA (Fin n)) BoolBR = SpFreeBA ≅ (Fin n → Bool)
  sp-equiv : SpFinBA ≃ (Fin n → Bool)
  sp-equiv = theEquiv

  -- Compose: ⟨ freeBA (Fin n) ⟩ ≃ ((Fin n → Bool) → Bool)
  -- (SpFinBA → Bool) ≃ ((Fin n → Bool) → Bool) via precomposition with sp-equiv⁻¹
  total-equiv : ⟨ freeBA (Fin n) ⟩ ≃ ((Fin n → Bool) → Bool)
  total-equiv = compEquiv sd-equiv (preCompEquiv (invEquiv sp-equiv))
    where
    open import Cubical.Foundations.Equiv using (invEquiv)
    open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)

  open import Cubical.Data.FinSet.Base using (isFinSet)
  open import Cubical.Data.FinSet.Properties using (isFinSetFin; isFinSetBool; EquivPresIsFinSet)
  open import Cubical.Foundations.Equiv using (invEquiv)
  open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
  open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)

  isFinSetOurFin : isFinSet (Fin n)
  isFinSetOurFin = EquivPresIsFinSet (SumFin≃Fin n) isFinSetFin

  -- (Fin n → Bool) → Bool is finite: transfer from (SumFin n → Bool) → Bool
  postulate isFinSetTarget : isFinSet ((Fin n → Bool) → Bool)

  isFinSet-freeBA-Fin : isFinSet ⟨ freeBA (Fin n) ⟩
  isFinSet-freeBA-Fin = EquivPresIsFinSet (invEquiv total-equiv) isFinSetTarget

-- Step 4: maxGen — extracts max generator index from a freeBA term
open import Cubical.Data.Nat using (max)

maxGen : freeBATerms ℕ → ℕ
maxGen (Tvar n) = suc n
maxGen (Tconst _) = zero
maxGen (t +T s) = max (maxGen t) (maxGen s)
maxGen (-T t) = maxGen t
maxGen (t ·T s) = max (maxGen t) (maxGen s)

-- Step 5: genBound — every element of freeBA ℕ has a truncated generator bound
-- For any x : ⟨ freeBA ℕ ⟩, there exists m such that x is in the image of
-- the inclusion ι_m : freeBA(Fin m) → freeBA ℕ.
-- This follows from includeBATermsSurj (surjection from terms to freeBA elements)
-- and maxGen (which bounds the generators used in a term).

-- The inclusion ι_m : freeBA(Fin m) → freeBA ℕ
ι : (m : ℕ) → BoolHom (freeBA (Fin m)) (freeBA ℕ)
ι m = inducedBAHom (Fin m) (freeBA ℕ) (generator ∘ fst)

-- The projection π_m : freeBA ℕ → freeBA(Fin m)
open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ)
open BooleanRingStr

π-on-gen : (m : ℕ) → ℕ → ⟨ freeBA (Fin m) ⟩
π-on-gen m k with <Dec k m
... | yes p = generator (k , <→<ᵗ p)
... | no _  = 𝟘 (snd (freeBA (Fin m)))

π : (m : ℕ) → BoolHom (freeBA ℕ) (freeBA (Fin m))
π m = inducedBAHom ℕ (freeBA (Fin m)) (π-on-gen m)

-- Key property: ι m ∘ π m agrees with id on generators < m
-- This gives: for any x with all generators < m, (ι m)(π m x) = x
-- We prove this via terms: for any term t with maxGen t ≤ m,
-- the freeBA element represented by t is in the image of ι m.

-- Re-interpret a term with generators in ℕ as a term with generators in Fin m
-- (provided maxGen t ≤ m)
open import Cubical.Foundations.Equiv using (fiber) renaming (invEquiv to invEquiv')

-- genBound: every element of freeBA ℕ is in the image of ι m for some m
genBound : (x : ⟨ freeBA ℕ ⟩) → ∥ Σ[ m ∈ ℕ ] fiber (fst (ι m)) x ∥₁
genBound x = PT.map go (snd includeBATermsSurj x) where
  go : fiber (fst includeBATermsSurj) x → Σ[ m ∈ ℕ ] fiber (fst (ι m)) x
  go (t , πt≡x) = maxGen t , fst (π (maxGen t)) x' , lem where
    m = maxGen t
    x' = fst includeBATermsSurj t
    postulate lem : fst (ι m) (fst (π m) x') ≡ x
