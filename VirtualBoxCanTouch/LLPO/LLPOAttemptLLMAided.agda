{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module LLPOAttemptLLMAided where
-- made in collaboration with LLM. 
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open NFinCofinPresentation 
open DefinitionFinCofin
open import StoneSpaces.Examples.Ninfty
open import Cubical.Algebra.CommRing
open import Cubical.Data.Nat.Order
open import Cubical.Algebra.BooleanRing

open import Parity
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BooleanRingQuotients.QuotientBool using (quotientImageHom ; evalInduce)
open import BasicDefinitions
open import Cubical.Data.Bool hiding (_≤_)

open import BooleanRing.BoolAlgMorphism

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (fiber)

open import Cubical.Algebra.CommRing

open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import CountablyPresentedBooleanRings.Definitions
open import BooleanRing.ProductBA
open import Axioms.SurjectionsAreFormalSurjections
open import StoneSpaces.Spectrum

open import Cubical.Categories.Category.Base using (CatIso)
open import Cubical.Categories.Functor.Properties using (preserveIsosF)
open import Cubical.Categories.Isomorphism using (op-Iso⁻)
open import Cubical.Categories.Instances.Sets using (SET ; CatIso→Iso)
open import CategoryTheory.StuffFromStoneAboutBAs using (BACat ; SpGeneralFunctor ; BAIso≅BAEquiv)

-- LLM gave a temporary library workaround documented in LIBRARY_CHANGES.md.
import StoneSums            -- Sp(A ×BR B) ≅ Sp A ⊎ Sp B  (see SpB∞≃ℕ∞⊎)
import ProductClosureLocal  -- algebraic product-closure (fixes ProductClosure)

LLPOExplicitAt : ℕ∞ → Type
LLPOExplicitAt (α , _) =
  (∀ (n : ℕ) → α (double n) ≡ false) ⊎ (∀ (n : ℕ) → α (suc $ double n) ≡ false)

LLPO : Type
LLPO = (x : ℕ∞) → ∥ LLPOExplicitAt x ∥₁

B∞ : Booleω
B∞ = ℕfinCofinBA , ℕfinCofinIsCountablyPresented

SpEq : Iso (Sp B∞) (SpGeneralBooleanRing presentation)
SpEq = invIso (CatIso→Iso (op-Iso⁻ {C = SET ℓ-zero}
              (preserveIsosF {F = SpGeneralFunctor} pres≅ℕfc)))
  where
    pres≅ℕfc : CatIso BACat presentation ℕfinCofinBA
    pres≅ℕfc = BAIso≅BAEquiv presentation ℕfinCofinBA .Iso.inv ℕFinCof=Presentation

SpB∞≃ℕ∞ : Iso (Sp B∞) ℕ∞
SpB∞≃ℕ∞ = compIso SpEq neededIso

B∞eval : Sp B∞ → binarySequence
B∞eval γ n = γ $cr singleton n

ℕ∞IsoIsEval : (γ : Sp B∞) → fst (Iso.fun SpB∞≃ℕ∞ γ) ≡ B∞eval γ
ℕ∞IsoIsEval γ = funExt λ n → cong (fst γ) $
   (fst (fst ℕFinCof=Presentation) (quotientImageHom $cr generator n)) 
     ≡⟨ funExt⁻ (cong fst (evalInduce ℕfinCofinBA)) (generator n) ⟩
   (freeℕ→ℕFinCof $cr generator n) 
     ≡⟨ eval-gen n ⟩
   singleton n ∎

-- We make use of the product of B∞ with itself, and we need that countably presented boolean algebras are closed under products. Right now, we use an algebraic proof for this. 
-- Another proof that we don't use is to show that a boolean algebra is countably presented iff it is overtly discrete and show that overtly discrete is closed under products. 
B∞xB∞ : Booleω
B∞xB∞ = B∞ ×Booleω B∞ where 
  open ProductClosureLocal

-- We also use that Sp is an antiequivalence and thus 
-- Sp(A ×BR B) ≅ Sp A ⊎ Sp B 
-- Right now, we also use an algebraic proof for this. 
-- It should be proven using categorical facts. 
SpB∞≃ℕ∞⊎ : Iso (Sp B∞xB∞) (ℕ∞ ⊎ ℕ∞)
SpB∞≃ℕ∞⊎ = compIso (StoneSums.SpProd≅SpSum ℕfinCofinBA ℕfinCofinBA) (⊎Iso SpB∞≃ℕ∞ SpB∞≃ℕ∞)

module LLPOProof (formalSurjections : formalSurjectionsAreSurjectionsAxiom) where
  open BooleanAlgebraStr ⦃...⦄
  open BooleanRingStr ⦃...⦄
  instance
    _ = booleanStructureOnBinarySequences
    _ = snd $ ℕfinCofinBA
    _ = snd $ ℕfinCofinBA ×BR ℕfinCofinBA

  evenPart : binarySequence → binarySequence
  evenPart α k = α (double k)

  oddPart : binarySequence → binarySequence
  oddPart α k = α (suc (double k))

  -- ───────────────────────────────────────────────────────────────
  -- Both halves preserve finiteness, cofiniteness, hence isFiniteOrCofinite
  -- ───────────────────────────────────────────────────────────────
  k≤double : (k : ℕ) → k ≤ double k
  k≤double k = k , sym (double≡+self k)

  evenPart-zeroFrom : (α : binarySequence) (n : ℕ) → isZeroFrom n α → isZeroFrom n (evenPart α)
  evenPart-zeroFrom α n z k k≥n = z (double k) (≤-trans k≥n (k≤double k))

  oddPart-zeroFrom : (α : binarySequence) (n : ℕ) → isZeroFrom n α → isZeroFrom n (oddPart α)
  oddPart-zeroFrom α n z k k≥n = z (suc (double k)) (≤-trans k≥n (≤-trans (k≤double k) (≤-suc ≤-refl)))

  evenPart-fin : (α : binarySequence) → isFinite α → isFinite (evenPart α)
  evenPart-fin α fin = let (n , z) = finite→Bounded α fin
                       in bounded→Finite (evenPart α) n (evenPart-zeroFrom α n z)

  oddPart-fin : (α : binarySequence) → isFinite α → isFinite (oddPart α)
  oddPart-fin α fin = let (n , z) = finite→Bounded α fin
                      in bounded→Finite (oddPart α) n (oddPart-zeroFrom α n z)

  evenPart-¬ : (α : binarySequence) → evenPart (¬ α) ≡ ¬ (evenPart α)
  evenPart-¬ α = refl
  oddPart-¬ : (α : binarySequence) → oddPart (¬ α) ≡ ¬ (oddPart α)
  oddPart-¬ α = refl

  evenPart-cofin : (α : binarySequence) → isCofinite α → isCofinite (evenPart α)
  evenPart-cofin α cof = subst isFinite (sym (evenPart-¬ α)) (evenPart-fin (¬ α) cof)
  oddPart-cofin : (α : binarySequence) → isCofinite α → isCofinite (oddPart α)
  oddPart-cofin α cof = subst isFinite (sym (oddPart-¬ α)) (oddPart-fin (¬ α) cof)

  evenPart-FC : (α : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite (evenPart α)
  evenPart-FC α (Fin f) = Fin (evenPart-fin α f)
  evenPart-FC α (Cof c) = Cof (evenPart-cofin α c)

  oddPart-FC : (α : binarySequence) → isFiniteOrCofinite α → isFiniteOrCofinite (oddPart α)
  oddPart-FC α (Fin f) = Fin (oddPart-fin α f)
  oddPart-FC α (Cof c) = Cof (oddPart-cofin α c)

  -- ───────────────────────────────────────────────────────────────
  -- The split map and its trivial kernel
  -- ───────────────────────────────────────────────────────────────

  -- the two halves as Boolean-algebra homs ℕfinCofinBA → ℕfinCofinBA
  --   evenHom : I ↦ I₀ = {k | 2k   ∈ I}     oddHom : I ↦ I₁ = {k | 2k+1 ∈ I}
  evenHom : BoolHom ℕfinCofinBA ℕfinCofinBA
  fst evenHom (α , w) = evenPart α , evenPart-FC α w
  snd evenHom = makeIsCommRingHom (FC≡ refl) (λ _ _ → FC≡ refl) (λ _ _ → FC≡ refl)

  oddHom : BoolHom ℕfinCofinBA ℕfinCofinBA
  fst oddHom (α , w) = oddPart α , oddPart-FC α w
  snd oddHom = makeIsCommRingHom (FC≡ refl) (λ _ _ → FC≡ refl) (λ _ _ → FC≡ refl)

  -- the split map is now literally the universal product map of its two halves
  -- (I ↦ (I₀ , I₁)).  Realizes the old `splitFun`, now for free from the product.
  splitHom : BoolHom ℕfinCofinBA (ℕfinCofinBA ×BR ℕfinCofinBA)
  splitHom = induceProdMapBR evenHom oddHom

  -- sends a finite set to a pair of finite sets
  splitHom-finite : (α : binarySequence) → isFinite α
    → isFinite (evenPart α) × isFinite (oddPart α)
  splitHom-finite α fin = evenPart-fin α fin , oddPart-fin α fin

  -- sends a cofinite set to a pair of cofinite sets
  splitHom-cofinite : (α : binarySequence) → isCofinite α
    → isCofinite (evenPart α) × isCofinite (oddPart α)
  splitHom-cofinite α cof = evenPart-cofin α cof , oddPart-cofin α cof

  kernelSplitCase : (α : binarySequence)
    → evenPart α ≡ 𝟘 → oddPart α ≡ 𝟘 → α ≡ 𝟘
  kernelSplitCase α e o = funExt λ n → help n (even-or-odd n)
    where
      help : (n : ℕ) → Even n ⊎ Odd n → α n ≡ false
      help n (inl (k , n≡2k  )) = cong α n≡2k ∙ funExt⁻ e k
      help n (inr (k , n≡2k+1)) = cong α n≡2k+1 ∙ funExt⁻ o k

  splitHom-kernel : (b : ⟨ ℕfinCofinBA ⟩) → splitHom $cr b ≡ 𝟘 → b ≡ 𝟘
  splitHom-kernel (a , _) fa=0 = Σ≡Prop isPropisFiniteOrCofinite
    (kernelSplitCase a (cong (λ z → fst (fst z)) fa=0) (cong (λ z → fst (snd z)) fa=0))

  even≠odd : (k j : ℕ) → (double k ≡ᵇ suc (double j)) ≡ false
  even≠odd zero j = refl
  even≠odd (suc k) zero = refl
  even≠odd (suc k) (suc j) = even≠odd k j

  odd≠even : (k j : ℕ) → (suc (double k) ≡ᵇ double j) ≡ false
  odd≠even k zero = refl
  odd≠even zero (suc j) = refl
  odd≠even (suc k) (suc j) = odd≠even k j

  evenPart-δ-odd : (k : ℕ) → evenPart (δSequence (suc (double k))) ≡ (λ _ → false)
  evenPart-δ-odd k = funExt λ j → odd≠even k j
  oddPart-δ-even : (k : ℕ) → oddPart (δSequence (double k)) ≡ (λ _ → false)
  oddPart-δ-even k = funExt λ j → even≠odd k j

  evenHom-sing-odd : (k : ℕ) → evenHom $cr singleton (suc (double k)) ≡ 𝟘
  evenHom-sing-odd k = FC≡ (evenPart-δ-odd k)
  oddHom-sing-even : (k : ℕ) → oddHom $cr singleton (double k) ≡ 𝟘
  oddHom-sing-even k = FC≡ (oddPart-δ-even k)

  SpEvenHom-odd0 : (γ : SpGeneralBooleanRing ℕfinCofinBA) (k : ℕ)
    → (γ ∘cr evenHom) $cr singleton (suc (double k)) ≡ false
  SpEvenHom-odd0 γ k =
      (γ ∘cr evenHom) $cr singleton (suc (double k))
    ≡⟨ cong (λ x → γ $cr x) (evenHom-sing-odd k) ⟩
      γ $cr 𝟘
    ≡⟨ IsCommRingHom.pres0 (snd γ) ⟩
      false ∎

  SpOddHom-even0 : (γ : SpGeneralBooleanRing ℕfinCofinBA) (k : ℕ)
    → (γ ∘cr oddHom) $cr singleton (double k) ≡ false
  SpOddHom-even0 γ k =
      (γ ∘cr oddHom) $cr singleton (double k)
    ≡⟨ cong (λ x → γ $cr x) (oddHom-sing-even k) ⟩
      γ $cr 𝟘
    ≡⟨ IsCommRingHom.pres0 (snd γ) ⟩
      false ∎

  splitInj : isInjectiveBoolHom B∞ B∞xB∞ splitHom
  splitInj = ker≡0→injBoolHom B∞ B∞xB∞ splitHom splitHom-kernel 
  
  SpSplit : Sp B∞xB∞ → Sp B∞
  SpSplit γ = γ ∘cr splitHom

  SpSplitSurj : isSurjection SpSplit
  SpSplitSurj = formalSurjections B∞ B∞xB∞ splitHom splitInj

  -- ── Spf, by definition the coproduct (copairing) of the two Stone halves ────
  -- The two halves `Sp evenHom`, `Sp oddHom` transported along SpB∞≃ℕ∞ to maps ℕ∞ → ℕ∞:
  evenStone oddStone : ℕ∞ → ℕ∞
  evenStone β = Iso.fun SpB∞≃ℕ∞ (Iso.inv SpB∞≃ℕ∞ β ∘cr evenHom)   
  oddStone  β = Iso.fun SpB∞≃ℕ∞ (Iso.inv SpB∞≃ℕ∞ β ∘cr oddHom)   

  Spf : ℕ∞ ⊎ ℕ∞ → ℕ∞
  Spf = ⊎.rec evenStone oddStone

  -- Surjectivity is inherited from the composite presentation
  -- `Iso.fun SpB∞≃ℕ∞ ∘ SpSplit ∘ Iso.inv SpB∞≃ℕ∞⊎`, to which Spf is equal: under SpB∞≃ℕ∞⊎ the inl/inr
  -- inclusion is precomposition with fstBA/sndBA, and `fstBA ∘cr splitHom = evenHom`
  -- (resp. sndBA) holds *definitionally* (since `splitHom = induceProdMapBR evenHom oddHom`).
  Spf-comp : ℕ∞ ⊎ ℕ∞ → ℕ∞
  Spf-comp = Iso.fun SpB∞≃ℕ∞ ∘ SpSplit ∘ Iso.inv SpB∞≃ℕ∞⊎

  Spf≡comp : Spf ≡ Spf-comp
  Spf≡comp = funExt λ { (inl β) → cong (Iso.fun SpB∞≃ℕ∞) (CommRingHom≡ refl)
                      ; (inr β) → cong (Iso.fun SpB∞≃ℕ∞) (CommRingHom≡ refl) }

  SpfSurj : isSurjection Spf
  SpfSurj = subst isSurjection (sym Spf≡comp) Spf-comp-surj
    where
    Iso→↠ : ∀ {ℓ ℓ'} {X : Type ℓ} {Y : Type ℓ'} → Iso X Y → X ↠ Y
    Iso→↠ i = Iso.fun i , isEquiv→isSurjection (snd (isoToEquiv i))
    Spf-comp-surj : isSurjection Spf-comp
    Spf-comp-surj = snd
      (compSurjection
        (Iso→↠ (invIso SpB∞≃ℕ∞⊎))
        (compSurjection
          (SpSplit , SpSplitSurj)
          (Iso→↠ SpB∞≃ℕ∞)))

  -- ── each half vanishes on the opposite parity ──────────────────────────────
  -- `evenHom` kills the odd singletons, so its Stone image is 0 on every odd
  -- coordinate; dually `oddHom` gives 0 on every even coordinate.

  evenStone-odd0 : (β : ℕ∞) (k : ℕ) → fst (evenStone β) (suc (double k)) ≡ false
  evenStone-odd0 β k =
      fst (evenStone β) (suc (double k))
    ≡⟨ funExt⁻ (ℕ∞IsoIsEval (Iso.inv SpB∞≃ℕ∞ β ∘cr evenHom)) (suc (double k)) ⟩   -- SpB∞≃ℕ∞ reads off on singletons
      B∞eval (Iso.inv SpB∞≃ℕ∞ β ∘cr evenHom) (suc (double k))
    ≡⟨ SpEvenHom-odd0 (Iso.inv SpB∞≃ℕ∞ β) k ⟩                                       -- evenHom kills the odd singleton
      false ∎

  oddStone-even0 : (β : ℕ∞) (k : ℕ) → fst (oddStone β) (double k) ≡ false
  oddStone-even0 β k =
      fst (oddStone β) (double k)
    ≡⟨ funExt⁻ (ℕ∞IsoIsEval (Iso.inv SpB∞≃ℕ∞ β ∘cr oddHom)) (double k) ⟩          -- SpB∞≃ℕ∞ reads off on singletons
      B∞eval (Iso.inv SpB∞≃ℕ∞ β ∘cr oddHom) (double k)
    ≡⟨ SpOddHom-even0 (Iso.inv SpB∞≃ℕ∞ β) k ⟩                                       -- oddHom kills the even singleton
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
