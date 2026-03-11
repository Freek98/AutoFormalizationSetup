{-# OPTIONS --cubical --guardedness --lossy-unification #-}

module LLPOwork.LLPO where

-- ═══════════════════════════════════════════════════════════════
-- LLPO from Stone Duality + Surjections are Formal Surjections
-- ═══════════════════════════════════════════════════════════════
--
-- Proof outline (from LLPO.tex):
-- 1. B∞ = presentation of NFinCofin, Sp(B∞) ≅ ℕ∞
-- 2. B∞ × B∞ is countably presented, Sp(B∞ × B∞) ≅ Sp(B∞) + Sp(B∞)
-- 3. Define injective BoolHom B∞ → B∞ × B∞ via interleaving
-- 4. Apply "surjections are formal surjections" to get Sp(B∞) + Sp(B∞) ↠ Sp(B∞)
-- 5. Derive LLPO

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.Data.Bool
  hiding (_≤_ ; _≥_)
  renaming (_≟_ to _=B_)
open import Cubical.Data.Nat
  renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
  renaming (_≟_ to _=ℕ_)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁ ; ∥_∥₁ ; squash₁)
open import Cubical.Functions.Surjection using (isSurjection)

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.DirectProd

open import BasicDefinitions
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BoolAlgMorphism
open import BooleanRing.BooleanRingMaps
open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.Examples.NFinCofin
open import StoneSpaces.Spectrum
open import Axioms.SurjectionsAreFormalSurjections

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open BooleanAlgebraStr ⦃...⦄
open BooleanRingStr ⦃...⦄

-- ═══════════════════════════════════════════════════════════════
-- Part 0: ℕ∞ and Sp(B∞) (avoiding broken Ninfty import)
-- ═══════════════════════════════════════════════════════════════

hits1AtMostOnce : binarySequence → Type
hits1AtMostOnce α = ∀ (n m : ℕ) → α n ≡ true → α m ≡ true → n ≡ m

ℕ∞ : Type ℓ-zero
ℕ∞ = Σ[ α ∈ binarySequence ] hits1AtMostOnce α

-- ═══════════════════════════════════════════════════════════════
-- Part 1: B∞ as countably presented Boolean ring
-- ═══════════════════════════════════════════════════════════════

B∞ : BooleanRing ℓ-zero
B∞ = presentation

instance
  _ = snd B∞
  _ = snd (freeBA ℕ)

B∞-cp : is-countably-presented-alt B∞
B∞-cp = ∣ relationsℕ , idBoolEquiv B∞ ∣₁

B∞ω : Booleω
B∞ω = B∞ , B∞-cp

-- ═══════════════════════════════════════════════════════════════
-- Part 2: Direct product of Boolean rings
-- ═══════════════════════════════════════════════════════════════

_×BR_ : BooleanRing ℓ-zero → BooleanRing ℓ-zero → BooleanRing ℓ-zero
fst (A ×BR B) = ⟨ A ⟩ × ⟨ B ⟩
BooleanRingStr.𝟘 (snd (A ×BR B)) = 𝟘 , 𝟘
  where instance _ = snd A ; _ = snd B
BooleanRingStr.𝟙 (snd (A ×BR B)) = 𝟙 , 𝟙
  where instance _ = snd A ; _ = snd B
BooleanRingStr._+_ (snd (A ×BR B)) (a₁ , b₁) (a₂ , b₂) =
  BooleanRingStr._+_ (snd A) a₁ a₂ , BooleanRingStr._+_ (snd B) b₁ b₂
BooleanRingStr._·_ (snd (A ×BR B)) (a₁ , b₁) (a₂ , b₂) =
  BooleanRingStr._·_ (snd A) a₁ a₂ , BooleanRingStr._·_ (snd B) b₁ b₂
BooleanRingStr.-_ (snd (A ×BR B)) (a , b) =
  BooleanRingStr.-_ (snd A) a , BooleanRingStr.-_ (snd B) b
IsBooleanRing.isCommRing (BooleanRingStr.isBooleanRing (snd (A ×BR B))) =
  CommRingStr.isCommRing (snd (DirectProd-CommRing
    (BooleanRing→CommRing A) (BooleanRing→CommRing B)))
IsBooleanRing.·Idem (BooleanRingStr.isBooleanRing (snd (A ×BR B))) (a , b) i =
  BooleanRingStr.·Idem (snd A) a i , BooleanRingStr.·Idem (snd B) b i

-- Projection homomorphisms
pr₁-BR : (A B : BooleanRing ℓ-zero) → BoolHom (A ×BR B) A
fst (pr₁-BR A B) (a , _) = a
snd (pr₁-BR A B) = makeIsCommRingHom refl (λ _ _ → refl) (λ _ _ → refl)

pr₂-BR : (A B : BooleanRing ℓ-zero) → BoolHom (A ×BR B) B
fst (pr₂-BR A B) (_ , b) = b
snd (pr₂-BR A B) = makeIsCommRingHom refl (λ _ _ → refl) (λ _ _ → refl)

-- Pairing of homomorphisms
⟨_,_⟩BR : {A B C : BooleanRing ℓ-zero} → BoolHom C A → BoolHom C B → BoolHom C (A ×BR B)
fst ⟨ f , g ⟩BR x = fst f x , fst g x
snd ⟨ f , g ⟩BR = makeIsCommRingHom
  (λ i → IsCommRingHom.pres1 (snd f) i , IsCommRingHom.pres1 (snd g) i)
  (λ x y i → IsCommRingHom.pres+ (snd f) x y i , IsCommRingHom.pres+ (snd g) x y i)
  (λ x y i → IsCommRingHom.pres· (snd f) x y i , IsCommRingHom.pres· (snd g) x y i)

-- Sp(A × B) ≅ Sp(A) + Sp(B) : a point of Sp(A × B) is a BoolHom (A × B) → Bool,
-- which corresponds to either a BoolHom A → Bool or a BoolHom B → Bool
-- (since Bool has no nontrivial idempotent decomposition).

-- ═══════════════════════════════════════════════════════════════
-- Part 3: The interleaving map B∞ → B∞ × B∞
-- ═══════════════════════════════════════════════════════════════

open NFinCofinPresentation

private
  module BR-B∞ = BooleanRingStr (snd B∞)
  module BA-B∞ = BooleanAlgebraStr (snd B∞)

B∞×B∞ : BooleanRing ℓ-zero
B∞×B∞ = B∞ ×BR B∞

private
  module BR-prod = BooleanRingStr (snd B∞×B∞)
  module BA-prod = BooleanAlgebraStr (snd B∞×B∞)

-- The generators of B∞
gB∞ : ℕ → ⟨ B∞ ⟩
gB∞ n = fst π (generator n)

-- Even/odd splitting
double : ℕ → ℕ
double zero = zero
double (suc n) = suc (suc (double n))

half : ℕ → ℕ
half zero = zero
half (suc zero) = zero
half (suc (suc n)) = suc (half n)

-- isEven/isOdd from Cubical.Data.Nat: isEven 0 = true, isEven (suc n) = isOdd n
-- isOdd 0 = false, isOdd (suc n) = isEven n
-- So: isEven (suc (suc n)) = isEven n

isEven-double : (k : ℕ) → isEven (double k) ≡ true
isEven-double zero = refl
isEven-double (suc k) = isEven-double k

isOdd-double+1 : (k : ℕ) → isEven (suc (double k)) ≡ false
isOdd-double+1 zero = refl
isOdd-double+1 (suc k) = isOdd-double+1 k

half-double : (k : ℕ) → half (double k) ≡ k
half-double zero = refl
half-double (suc k) = cong suc (half-double k)

half-double+1 : (k : ℕ) → half (suc (double k)) ≡ k
half-double+1 zero = refl
half-double+1 (suc k) = cong suc (half-double+1 k)

-- Define interleave-gen using explicit even/odd index construction.
-- For even n = double(k): (𝟘, gB∞(k))
-- For odd n = suc(double(k)): (gB∞(k), 𝟘)
-- We define it on all ℕ by first splitting into even/odd.

evenGen : ℕ → ⟨ B∞×B∞ ⟩
evenGen k = BR-B∞.𝟘 , gB∞ k

oddGen : ℕ → ⟨ B∞×B∞ ⟩
oddGen k = gB∞ k , BR-B∞.𝟘

-- Use the freeBA universal property with explicit doubling:
-- We define the map on generators by going through ℕ → ⟨ B∞×B∞ ⟩
-- using interleave-gen(double k) = evenGen k, interleave-gen(suc(double k)) = oddGen k

-- Component orthogonality lemmas (postulated, will prove later)
postulate
  evenGen-orth : (k l : ℕ) → (k ≡ l → ⊥) →
    BR-prod._·_ (evenGen k) (evenGen l) ≡ BR-prod.𝟘
  oddGen-orth : (k l : ℕ) → (k ≡ l → ⊥) →
    BR-prod._·_ (oddGen k) (oddGen l) ≡ BR-prod.𝟘
  even-odd-orth : (k l : ℕ) →
    BR-prod._·_ (evenGen k) (oddGen l) ≡ BR-prod.𝟘
  odd-even-orth : (k l : ℕ) →
    BR-prod._·_ (oddGen k) (evenGen l) ≡ BR-prod.𝟘

-- We define interleave-gen using the ℕ ≅ ℕ + ℕ bijection (even/odd decomposition)
-- But to keep it simple and computable, we use direct recursion:
interleave-gen : ℕ → ⟨ B∞×B∞ ⟩
interleave-gen n with isEven n
... | true  = evenGen (half n)
... | false = oddGen (half n)

-- Orthogonality - postulated for now, will be proven using the component lemmas above
-- The key difficulty is working with `with` abstraction; we'll prove it
-- by reducing to the component orthogonality lemmas.
postulate
  interleave-gen-orth : (n m : ℕ) → (n ≡ m → ⊥) →
    BR-prod._·_ (interleave-gen n) (interleave-gen m) ≡ BR-prod.𝟘

-- The map freeBA ℕ → B∞ × B∞ induced by interleave-gen
f-free : BoolHom (freeBA ℕ) B∞×B∞
f-free = inducedBAHom ℕ B∞×B∞ interleave-gen

-- f-free respects the relations (gen n · gen m = 0 for n ≠ m)
-- This means it descends to B∞ → B∞ × B∞
private
  module FH-f = IsCommRingHom (snd f-free)

  f-free-eval : (n : ℕ) → fst f-free (generator n) ≡ interleave-gen n
  f-free-eval n = funExt⁻ (evalBAInduce ℕ B∞×B∞ interleave-gen) n

f-free-respects-rels : (k : ℕ) → fst f-free (relationsℕ k) ≡ BR-prod.𝟘
f-free-respects-rels k = f-free-respects-relations' (Iso.inv ℕ×ℕ≅ℕ k)
  where
    f-free-respects-relations' : (p : ℕ × ℕ) → fst f-free (relations p) ≡ BR-prod.𝟘
    f-free-respects-relations' (n , m) with discreteℕ n m
    ... | yes _ = FH-f.pres0
    ... | no n≠m =
      fst f-free (generator n · generator m)
        ≡⟨ FH-f.pres· (generator n) (generator m) ⟩
      BR-prod._·_ (fst f-free (generator n)) (fst f-free (generator m))
        ≡⟨ cong₂ BR-prod._·_ (f-free-eval n) (f-free-eval m) ⟩
      BR-prod._·_ (interleave-gen n) (interleave-gen m)
        ≡⟨ interleave-gen-orth n m n≠m ⟩
      BR-prod.𝟘 ∎

-- The descended map B∞ → B∞ × B∞
f : BoolHom B∞ B∞×B∞
f = QB.inducedHom B∞×B∞ f-free f-free-respects-rels

-- ═══════════════════════════════════════════════════════════════
-- Part 4: Injectivity of f
-- ═══════════════════════════════════════════════════════════════

-- To show f is injective, it suffices to show: f(x) = 0 → x = 0.
-- By the equivalence B∞ ≅ ℕfinCofinBA (NFinCofin), every x is
-- either a finite or cofinite set.
-- If x is nonempty (contains some n), then f(x) ≥ f({n}) ≠ 0.

postulate
  f-injective : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y

-- ═══════════════════════════════════════════════════════════════
-- Part 5: B∞ × B∞ is countably presented
-- ═══════════════════════════════════════════════════════════════

-- The product of countably presented Boolean rings is countably presented.
-- Generators: ℕ + ℕ ≅ ℕ (left generators and right generators)
-- Relations: from left, from right, plus cross-relations

postulate
  B∞×B∞-cp : is-countably-presented-alt B∞×B∞

B∞×B∞ω : Booleω
B∞×B∞ω = B∞×B∞ , B∞×B∞-cp

-- ═══════════════════════════════════════════════════════════════
-- Part 6: Sp(A × B) ≅ Sp(A) ⊎ Sp(B) for Boolean rings
-- ═══════════════════════════════════════════════════════════════

-- A Boolean ring hom A × B → Bool must kill one component
-- (since (1,0) and (0,1) are orthogonal idempotents mapping to Bool,
-- one must map to 0 and the other to 1)

-- Sp(A × B) ≅ Sp(A) ⊎ Sp(B)
-- A BoolHom (A × B) → Bool sends (1,0) and (0,1) to Bool.
-- Since (1,0) + (0,1) = (1,1) = 1, and (1,0) · (0,1) = (0,0) = 0,
-- we get that one maps to true and the other to false.
-- This splits into left and right components.

-- Sp(A × B) ≅ Sp(A) ⊎ Sp(B) : postulated for now
-- The key idea: φ : BoolHom (A×B) Bool sends (1,0) to either true or false.
-- If φ(1,0) = true, then a ↦ φ(a,0) is a BoolHom A → Bool (checking: pres1 = φ(1,0) = true).
-- If φ(1,0) = false, then φ(0,1) = true, and b ↦ φ(0,b) is a BoolHom B → Bool.
postulate
  SpProd→Sum : (A B : BooleanRing ℓ-zero) →
    SpGeneralBooleanRing (A ×BR B) → SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
  SpSum→Prod : (A B : BooleanRing ℓ-zero) →
    SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B → SpGeneralBooleanRing (A ×BR B)
  SpProd≅Sum : (A B : BooleanRing ℓ-zero) →
    Iso (SpGeneralBooleanRing (A ×BR B)) (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)

-- ═══════════════════════════════════════════════════════════════
-- Part 7: Apply the axiom and derive LLPO
-- ═══════════════════════════════════════════════════════════════

-- The injective BoolHom f : B∞ → B∞ × B∞ gives, by the axiom,
-- a surjection Sp(B∞ × B∞) ↠ Sp(B∞), i.e., Sp(B∞) ⊎ Sp(B∞) ↠ Sp(B∞).
--
-- The dual of f on the spectrum sends a point of Sp(B∞ × B∞) to Sp(B∞)
-- by precomposition: γ ↦ γ ∘ f.
--
-- Combined with Sp(B∞) ≅ ℕ∞, this gives ℕ∞ ⊎ ℕ∞ ↠ ℕ∞.
--
-- For α ∈ ℕ∞, being in the image of the left copy means
-- α is 0 on all evens; being in the right copy means α is 0 on all odds.

-- LLPO statement:
LLPO-statement : Type
LLPO-statement =
  (α : binarySequence) → hits1AtMostOnce α →
  ∥ ((n : ℕ) → α (double n) ≡ false) ⊎ ((n : ℕ) → α (suc (double n)) ≡ false) ∥₁

-- The main theorem
postulate
  LLPO : formalSurjectionsAreSurjectionsAxiom → LLPO-statement
