{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module LLPOAttemptLLMAided where
-- made in collaboration with LLM. 
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open import StoneSpaces.Examples.Ninfty
open import Parity
open import Cubical.Data.Bool renaming (_≟_ to _=B_) hiding (_≤_ ; _≥_)

open import BooleanRing.BoolAlgMorphism

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv using (fiber)

open import Cubical.Algebra.CommRing

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import CountablyPresentedBooleanRings.Definitions
open import BooleanRing.ProductBA
open import Axioms.SurjectionsAreFormalSurjections
open import StoneSpaces.Spectrum

-- LLM gave a temporary library workaround documented in LIBRARY_CHANGES.md.
import StoneSums            -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B  (see σ⊎)
import ProductClosureLocal  -- algebraic product-closure (fixes ProductClosure)

open import EvenOddSplit using (splitHom ; splitHom-kernel ; evenHom ; oddHom ; SpEvenHom-odd0 ; SpOddHom-even0)
open import SpNfcIso using (σ ; σfun≡toℕ∞seq ; toℕ∞seq)

LLPOExplicitAt : ℕ∞ → Type
LLPOExplicitAt (α , _) =
  (∀ (n : ℕ) → α (double n) ≡ false) ⊎ (∀ (n : ℕ) → α (suc $ double n) ≡ false)

LLPO : Type
LLPO = (x : ℕ∞) → ∥ LLPOExplicitAt x ∥₁

B∞ : Booleω
B∞ = ℕfinCofinBA , ℕfinCofinIsCountablyPresented

module LLPOProof (formalSurjections : formalSurjectionsAreSurjectionsAxiom) where
  
  -- We make use of the product of B∞ with itself, and we need that countably presented boolean algebras are closed under products. Right now, we use an algebraic proof for this. 
  -- Another proof that we don't use is to show that a boolean algebra is countably presented iff it is overtly discrete and show that overtly discrete is closed under products. 
  B∞xB∞ : Booleω
  B∞xB∞ = B∞ ×Booleω B∞ where 
    open ProductClosureLocal

  -- We also use that Sp is an antiequivalence and thus 
  -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B 
  -- Right now, we also use an algebraic proof for this. 
  -- It should be proven using categorical facts. 
  σ⊎ : Iso (Sp B∞xB∞) (ℕ∞ ⊎ ℕ∞)
  σ⊎ = compIso (StoneSums.SpProd≅SpSum ℕfinCofinBA ℕfinCofinBA) (⊎Iso σ σ)
 
  splitInj : isInjectiveBoolHom B∞ B∞xB∞ splitHom
  splitInj = ker≡0→injBoolHom B∞ B∞xB∞ splitHom splitHom-kernel 
  
  SpSplit : SpGeneralBooleanRing (ℕfinCofinBA ×BR ℕfinCofinBA) → SpGeneralBooleanRing ℕfinCofinBA
  SpSplit γ = γ ∘cr splitHom

  SpSplitSurj : isSurjection SpSplit
  SpSplitSurj = formalSurjections B∞ B∞xB∞ splitHom splitInj

  -- ── Spf, by definition the coproduct (copairing) of the two Stone halves ────
  -- The two halves `Sp evenHom`, `Sp oddHom` transported along σ to maps ℕ∞ → ℕ∞:
  evenStone oddStone : ℕ∞ → ℕ∞
  evenStone β = Iso.fun σ (Iso.inv σ β ∘cr evenHom)   
  oddStone  β = Iso.fun σ (Iso.inv σ β ∘cr oddHom)   

  Spf : ℕ∞ ⊎ ℕ∞ → ℕ∞
  Spf = ⊎.rec evenStone oddStone

  -- Surjectivity is inherited from the composite presentation
  -- `Iso.fun σ ∘ SpSplit ∘ Iso.inv σ⊎`, to which Spf is equal: under σ⊎ the inl/inr
  -- inclusion is precomposition with fstBA/sndBA, and `fstBA ∘cr splitHom = evenHom`
  -- (resp. sndBA) holds *definitionally* (since `splitHom = induceProdMapBR evenHom oddHom`).
  Spf-comp : ℕ∞ ⊎ ℕ∞ → ℕ∞
  Spf-comp = Iso.fun σ ∘ SpSplit ∘ Iso.inv σ⊎

  Spf≡comp : Spf ≡ Spf-comp
  Spf≡comp = funExt λ { (inl β) → cong (Iso.fun σ) (CommRingHom≡ refl)
                      ; (inr β) → cong (Iso.fun σ) (CommRingHom≡ refl) }

  SpfSurj : isSurjection Spf
  SpfSurj = subst isSurjection (sym Spf≡comp) Spf-comp-surj
    where
    Iso→↠ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → Iso X Y → X ↠ Y
    Iso→↠ i = Iso.fun i , isEquiv→isSurjection (snd (isoToEquiv i))
    Spf-comp-surj : isSurjection Spf-comp
    Spf-comp-surj = snd
      (compSurjection
        (Iso→↠ (invIso σ⊎))
        (compSurjection
          (SpSplit , SpSplitSurj)
          (Iso→↠ σ)))

  -- ── each half vanishes on the opposite parity ──────────────────────────────
  -- `evenHom` kills the odd singletons, so its Stone image is 0 on every odd
  -- coordinate; dually `oddHom` gives 0 on every even coordinate.

  evenStone-odd0 : (β : ℕ∞) (k : ℕ) → fst (evenStone β) (suc (double k)) ≡ false
  evenStone-odd0 β k =
      fst (evenStone β) (suc (double k))
    ≡⟨ funExt⁻ (σfun≡toℕ∞seq (Iso.inv σ β ∘cr evenHom)) (suc (double k)) ⟩   -- σ reads off on singletons
      toℕ∞seq (Iso.inv σ β ∘cr evenHom) (suc (double k))
    ≡⟨ SpEvenHom-odd0 (Iso.inv σ β) k ⟩                                       -- evenHom kills the odd singleton
      false ∎

  oddStone-even0 : (β : ℕ∞) (k : ℕ) → fst (oddStone β) (double k) ≡ false
  oddStone-even0 β k =
      fst (oddStone β) (double k)
    ≡⟨ funExt⁻ (σfun≡toℕ∞seq (Iso.inv σ β ∘cr oddHom)) (double k) ⟩          -- σ reads off on singletons
      toℕ∞seq (Iso.inv σ β ∘cr oddHom) (double k)
    ≡⟨ SpOddHom-even0 (Iso.inv σ β) k ⟩                                       -- oddHom kills the even singleton
      false ∎

  Spf-fibre→LLPO : (α : ℕ∞) → fiber Spf α → LLPOExplicitAt α
  Spf-fibre→LLPO α (inl β , p) = inr λ k →
      fst α (suc (double k))
    ≡⟨ cong (λ y → fst y (suc (double k))) (sym p) ⟩
      fst (evenStone β) (suc (double k))
    ≡⟨ evenStone-odd0 β k ⟩
      false ∎
  Spf-fibre→LLPO α (inr β , p) = inl λ k →
      fst α (double k)
    ≡⟨ cong (λ y → fst y (double k)) (sym p) ⟩
      fst (oddStone β) (double k)
    ≡⟨ oddStone-even0 β k ⟩
      false ∎

  llpo : LLPO
  llpo x = PT.map (Spf-fibre→LLPO x) (SpfSurj x)

llpoFromStoneDualityAndFormalSurjections : formalSurjectionsAreSurjectionsAxiom → LLPO
llpoFromStoneDualityAndFormalSurjections = LLPOProof.llpo
