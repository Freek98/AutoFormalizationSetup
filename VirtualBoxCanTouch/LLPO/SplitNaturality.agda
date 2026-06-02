{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- Naturality of the even/odd split at the level of spectra.
--
-- The spectrum action of `splitHom` sends a point of ℕfinCofinBA × ℕfinCofinBA to
-- a point of ℕfinCofinBA by precomposition.  Read off through the coordinate map
--     toℕ∞seq γ = (n ↦ γ(singleton n))      (a point as its sequence of bits),
-- and using the two component maps  evenHom = πB ∘ splitHom ,  oddHom = πC ∘ splitHom,
-- we prove the crux "Sp(splitHom) = e" computation at the point/sequence level:
--     toℕ∞seq (γ ∘cr evenHom) ≡ splitIntoEvens (toℕ∞seq γ)
--     toℕ∞seq (γ ∘cr oddHom)  ≡ splitIntoOdds  (toℕ∞seq γ).
-- So precomposing a point with splitHom's even (resp. odd) half is exactly the
-- even (resp. odd) split of the sequence the point represents — i.e. the map e
-- of the main file, here free of the product-iso/ℕ∞-wrapper plumbing.
module SplitNaturality where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import BasicDefinitions using (binarySequence ; δSequence)
open import Parity
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open NFinCofinPresentation using (singleton)
open import StoneSpaces.Spectrum using (SpGeneralBooleanRing)

open import BooleanRing.Products using (pr₁-BR ; pr₂-BR)
open import EvenOddSplit using (splitHom ; evenPart ; oddPart)

private
  𝟘fc : ⟨ ℕfinCofinBA ⟩
  𝟘fc = BooleanRingStr.𝟘 (snd ℕfinCofinBA)

-- the two halves of splitHom as Boolean-algebra maps ℕfinCofinBA → ℕfinCofinBA
evenHom : BoolHom ℕfinCofinBA ℕfinCofinBA
evenHom = pr₁-BR ℕfinCofinBA ℕfinCofinBA ∘cr splitHom
oddHom : BoolHom ℕfinCofinBA ℕfinCofinBA
oddHom = pr₂-BR ℕfinCofinBA ℕfinCofinBA ∘cr splitHom

-- a point read off as the sequence of its values on the singleton generators
toℕ∞seq : SpGeneralBooleanRing ℕfinCofinBA → binarySequence
toℕ∞seq γ n = γ $cr singleton n

-- the concrete even/odd split on sequences (as in the main file's `e`)
splitIntoEvens splitIntoOdds : binarySequence → binarySequence
splitIntoEvens α = evenOddElim (λ _ (k , _) → α k) (λ _ _ → false)
splitIntoOdds  α = evenOddElim (λ _ _ → false) (λ _ (k , _) → α k)

-- ── Bool-equality lemmas about double / ≡ᵇ ──
double-inj-≡ᵇ : (k j : ℕ) → (double k ≡ᵇ double j) ≡ (k ≡ᵇ j)
double-inj-≡ᵇ zero zero = refl
double-inj-≡ᵇ zero (suc j) = refl
double-inj-≡ᵇ (suc k) zero = refl
double-inj-≡ᵇ (suc k) (suc j) = double-inj-≡ᵇ k j

even-≡ᵇ-odd : (k j : ℕ) → (double k ≡ᵇ suc (double j)) ≡ false
even-≡ᵇ-odd zero j = refl
even-≡ᵇ-odd (suc k) zero = refl
even-≡ᵇ-odd (suc k) (suc j) = even-≡ᵇ-odd k j

odd-≡ᵇ-even : (k j : ℕ) → (suc (double k) ≡ᵇ double j) ≡ false
odd-≡ᵇ-even k zero = refl
odd-≡ᵇ-even zero (suc j) = refl
odd-≡ᵇ-even (suc k) (suc j) = odd-≡ᵇ-even k j

-- ── action of evenPart/oddPart on the δ-sequences (= singleton bits) ──
evenPart-δ-even : (k : ℕ) → evenPart (δSequence (double k)) ≡ δSequence k
evenPart-δ-even k = funExt λ j → double-inj-≡ᵇ k j
evenPart-δ-odd : (k : ℕ) → evenPart (δSequence (suc (double k))) ≡ (λ _ → false)
evenPart-δ-odd k = funExt λ j → odd-≡ᵇ-even k j
oddPart-δ-odd : (k : ℕ) → oddPart (δSequence (suc (double k))) ≡ δSequence k
oddPart-δ-odd k = funExt λ j → double-inj-≡ᵇ k j
oddPart-δ-even : (k : ℕ) → oddPart (δSequence (double k)) ≡ (λ _ → false)
oddPart-δ-even k = funExt λ j → even-≡ᵇ-odd k j

-- ── action of the component maps on singletons ──
evenHom-sing-even : (k : ℕ) → evenHom $cr singleton (double k) ≡ singleton k
evenHom-sing-even k = FC≡ (evenPart-δ-even k)
evenHom-sing-odd : (k : ℕ) → evenHom $cr singleton (suc (double k)) ≡ 𝟘fc
evenHom-sing-odd k = FC≡ (evenPart-δ-odd k)
oddHom-sing-odd : (k : ℕ) → oddHom $cr singleton (suc (double k)) ≡ singleton k
oddHom-sing-odd k = FC≡ (oddPart-δ-odd k)
oddHom-sing-even : (k : ℕ) → oddHom $cr singleton (double k) ≡ 𝟘fc
oddHom-sing-even k = FC≡ (oddPart-δ-even k)

-- ── the naturality squares ──
evenNaturality : (γ : SpGeneralBooleanRing ℕfinCofinBA)
  → toℕ∞seq (γ ∘cr evenHom) ≡ splitIntoEvens (toℕ∞seq γ)
evenNaturality γ = funExt ptwise
  where
    ptwise : (n : ℕ) → toℕ∞seq (γ ∘cr evenHom) n ≡ splitIntoEvens (toℕ∞seq γ) n
    ptwise n with even-or-odd n
    ... | inl (k , n2k)  = cong (λ m → γ $cr (evenHom $cr singleton m)) n2k
                           ∙ cong (λ x → γ $cr x) (evenHom-sing-even k)
    ... | inr (k , n2k1) = cong (λ m → γ $cr (evenHom $cr singleton m)) n2k1
                           ∙ cong (λ x → γ $cr x) (evenHom-sing-odd k)
                           ∙ IsCommRingHom.pres0 (snd γ)

oddNaturality : (γ : SpGeneralBooleanRing ℕfinCofinBA)
  → toℕ∞seq (γ ∘cr oddHom) ≡ splitIntoOdds (toℕ∞seq γ)
oddNaturality γ = funExt ptwise
  where
    ptwise : (n : ℕ) → toℕ∞seq (γ ∘cr oddHom) n ≡ splitIntoOdds (toℕ∞seq γ) n
    ptwise n with even-or-odd n
    ... | inl (k , n2k)  = cong (λ m → γ $cr (oddHom $cr singleton m)) n2k
                           ∙ cong (λ x → γ $cr x) (oddHom-sing-even k)
                           ∙ IsCommRingHom.pres0 (snd γ)
    ... | inr (k , n2k1) = cong (λ m → γ $cr (oddHom $cr singleton m)) n2k1
                           ∙ cong (λ x → γ $cr x) (oddHom-sing-odd k)
