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
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import BooleanRing.BoolRingUnivalence
open import Cubical.Tactics.CommRingSolver

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

-- Helper: 𝟘 · 𝟘 = 𝟘 in B∞
private
  𝟘·𝟘≡𝟘 : BR-B∞._·_ BR-B∞.𝟘 BR-B∞.𝟘 ≡ BR-B∞.𝟘
  𝟘·𝟘≡𝟘 = BR-B∞.·Idem BR-B∞.𝟘

  𝟘·x≡𝟘 : (x : ⟨ B∞ ⟩) → BR-B∞._·_ BR-B∞.𝟘 x ≡ BR-B∞.𝟘
  𝟘·x≡𝟘 x = BA-B∞.∧AnnihilL {x = x}

  x·𝟘≡𝟘 : (x : ⟨ B∞ ⟩) → BR-B∞._·_ x BR-B∞.𝟘 ≡ BR-B∞.𝟘
  x·𝟘≡𝟘 x = BA-B∞.∧AnnihilR {x = x}

  -- gen-orth gives fst π (gen k · gen l) ≡ 𝟘
  -- but gB∞ k · gB∞ l = (fst π (gen k)) · (fst π (gen l))
  -- which differs from fst π (gen k · gen l) by π preserving ·
  module ΠH-loc = IsCommRingHom (snd π)

  gB∞-orth : (k l : ℕ) → (k ≡ l → ⊥) → BR-B∞._·_ (gB∞ k) (gB∞ l) ≡ BR-B∞.𝟘
  gB∞-orth k l k≠l =
    BR-B∞._·_ (gB∞ k) (gB∞ l)
      ≡⟨ sym (ΠH-loc.pres· (generator k) (generator l)) ⟩
    fst π (BooleanRingStr._·_ (snd (freeBA ℕ)) (generator k) (generator l))
      ≡⟨ gen-orth k l k≠l ⟩
    BR-B∞.𝟘 ∎

-- Component orthogonality lemmas
evenGen-orth : (k l : ℕ) → (k ≡ l → ⊥) →
  BR-prod._·_ (evenGen k) (evenGen l) ≡ BR-prod.𝟘
evenGen-orth k l k≠l = ΣPathP (𝟘·𝟘≡𝟘 , gB∞-orth k l k≠l)

oddGen-orth : (k l : ℕ) → (k ≡ l → ⊥) →
  BR-prod._·_ (oddGen k) (oddGen l) ≡ BR-prod.𝟘
oddGen-orth k l k≠l = ΣPathP (gB∞-orth k l k≠l , 𝟘·𝟘≡𝟘)

even-odd-orth : (k l : ℕ) →
  BR-prod._·_ (evenGen k) (oddGen l) ≡ BR-prod.𝟘
even-odd-orth k l = ΣPathP (𝟘·x≡𝟘 (gB∞ l) , x·𝟘≡𝟘 (gB∞ k))

odd-even-orth : (k l : ℕ) →
  BR-prod._·_ (oddGen k) (evenGen l) ≡ BR-prod.𝟘
odd-even-orth k l = ΣPathP (x·𝟘≡𝟘 (gB∞ k) , 𝟘·x≡𝟘 (gB∞ l))

-- We define interleave-gen using the ℕ ≅ ℕ + ℕ bijection (even/odd decomposition)
-- But to keep it simple and computable, we use direct recursion:
interleave-gen : ℕ → ⟨ B∞×B∞ ⟩
interleave-gen n with isEven n
... | true  = evenGen (half n)
... | false = oddGen (half n)

-- Reconstruct n from parity and half
-- We need: if isEven n = isEven m and half n = half m, then n = m
-- This is used to derive contradiction from half-equality.
-- If isEven n = true and isEven m = true and half n = half m, then n = m
-- Proof by induction on n and m simultaneously
even→eq : (n m : ℕ) → isEven n ≡ true → isEven m ≡ true → half n ≡ half m → n ≡ m
even→eq zero zero _ _ _ = refl
even→eq zero (suc zero) _ em _ = ex-falso (false≢true em)
even→eq zero (suc (suc m)) en em hq = ex-falso (znots hq)
even→eq (suc zero) zero en _ _ = ex-falso (false≢true en)
even→eq (suc zero) (suc _) en _ _ = ex-falso (false≢true en)
even→eq (suc (suc n)) zero en em hq = ex-falso (snotz hq)
even→eq (suc (suc n)) (suc zero) _ em _ = ex-falso (false≢true em)
even→eq (suc (suc n)) (suc (suc m)) en em hq = cong (suc ∘ suc) (even→eq n m en em (suc-inj hq))
  where
    suc-inj : {a b : ℕ} → suc a ≡ suc b → a ≡ b
    suc-inj p = cong predℕ p

odd→eq : (n m : ℕ) → isEven n ≡ false → isEven m ≡ false → half n ≡ half m → n ≡ m
odd→eq zero _ en _ _ = ex-falso (true≢false en)
odd→eq _ zero _ em _ = ex-falso (true≢false em)
odd→eq (suc zero) (suc zero) _ _ _ = refl
odd→eq (suc zero) (suc (suc m)) en em hq = ex-falso (znots hq)
odd→eq (suc (suc n)) (suc zero) en em hq = ex-falso (snotz hq)
odd→eq (suc (suc n)) (suc (suc m)) en em hq = cong (suc ∘ suc) (odd→eq n m en em (suc-inj hq))
  where
    suc-inj : {a b : ℕ} → suc a ≡ suc b → a ≡ b
    suc-inj p = cong predℕ p

-- Orthogonality of interleave-gen
import Agda.Builtin.Equality as BEq
builtin→Path : {a b : Bool} → a BEq.≡ b → a ≡ b
builtin→Path BEq.refl = refl

interleave-gen-orth : (n m : ℕ) → (n ≡ m → ⊥) →
  BR-prod._·_ (interleave-gen n) (interleave-gen m) ≡ BR-prod.𝟘
interleave-gen-orth n m n≠m with isEven n in eqN | isEven m in eqM
... | true  | true  = evenGen-orth (half n) (half m)
                        (λ p → n≠m (even→eq n m (builtin→Path eqN) (builtin→Path eqM) p))
... | false | false = oddGen-orth (half n) (half m)
                        (λ p → n≠m (odd→eq n m (builtin→Path eqN) (builtin→Path eqM) p))
... | true  | false = even-odd-orth (half n) (half m)
... | false | true  = odd-even-orth (half n) (half m)

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

-- Strategy: f(x) = 0 → x = 0.
-- Using the equivalence B∞ ≅ ℕfinCofinBA:
-- gB∞(n) is an atom, so gB∞(n)·x = 0 or gB∞(n)·x = gB∞(n).
-- If f(x) = 0, then f(gB∞(n))·f(x) = 0 = f(gB∞(n)·x).
-- Since f(gB∞(n)) ≠ 0, we get gB∞(n)·x = 0 for all n.
-- Via the equivalence, this means x = 0.

private
  -- The forward map of B∞ ≅ ℕfinCofinBA (constructed via QB.inducedHom)
  e : BoolHom B∞ ℕfinCofinBA
  e = QB.inducedHom ℕfinCofinBA freeℕ→ℕFinCof relationsℕRespected

  module E = IsCommRingHom (snd e)

  -- Computation rule: e ∘ π = freeℕ→ℕFinCof
  e-comp : e ∘cr π ≡ freeℕ→ℕFinCof
  e-comp = QB.evalInduce ℕfinCofinBA

  -- e sends gB∞(n) to singleton(n) = (δ_n, Fin ...)
  e-on-gen : (n : ℕ) → fst e (gB∞ n) ≡ singleton n
  e-on-gen n =
    funExt⁻ (cong fst e-comp) (generator n)
    ∙ eval-gen n

  -- e is an equivalence (same as the forward map of ℕFinCof=Presentation)
  e-is-equiv : isEquiv (fst e)
  e-is-equiv = snd (fst ℕFinCof=Presentation)

  -- Singleton computation: fst (singleton n) m = δSequence n m = (n ≡ᵇ m)
  -- singleton(n) at position n is true:
  singleton-n-true : (n : ℕ) → fst (singleton n) n ≡ true
  singleton-n-true n = δnn=1 n

  -- The underlying sequence of (a · b) in ℕfinCofinBA is pointwise AND
  -- (since ℕfinCofinBA is a subalgebra of ℙℕ with pointwise ops)
  FC-mul-seq : (a b : ⟨ ℕfinCofinBA ⟩) (k : ℕ) →
    fst (BooleanRingStr._·_ (snd ℕfinCofinBA) a b) k ≡ fst a k and fst b k
  FC-mul-seq a b k = refl

  -- The zero in ℕfinCofinBA has sequence everywhere false
  FC-zero-seq : (k : ℕ) → fst (BooleanRingStr.𝟘 (snd ℕfinCofinBA)) k ≡ false
  FC-zero-seq k = refl

  -- Atom property in ℕfinCofinBA:
  -- singleton(n) · y = singleton(n) if fst y n = true
  -- singleton(n) · y = 0           if fst y n = false
  singleton-mul : (n : ℕ) (y : ⟨ ℕfinCofinBA ⟩) →
    fst y n ≡ true →
    BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) y ≡ singleton n
  singleton-mul n y yn-true = FC≡ (funExt helper)
    where
      helper : (k : ℕ) →
        fst (BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) y) k ≡ fst (singleton n) k
      -- The goal is: (n ≡ᵇ k) and fst y k ≡ (n ≡ᵇ k)
      -- Key issue: n ≡ᵇ n doesn't reduce for variable n, need δnn=1
      helper k with discreteℕ n k
      ... | yes n≡k = J (λ k _ → (n ≡ᵇ k) and fst y k ≡ (n ≡ᵇ k))
                        (cong₂ _and_ (δnn=1 n) yn-true ∙ sym (δnn=1 n)) n≡k
      ... | no n≠k = cong₂ _and_ (δnm=0 n k n≠k) refl ∙ sym (δnm=0 n k n≠k)

  -- If fst y n = false, then singleton(n) · y = 0
  singleton-mul-zero : (n : ℕ) (y : ⟨ ℕfinCofinBA ⟩) →
    fst y n ≡ false →
    BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) y
      ≡ BooleanRingStr.𝟘 (snd ℕfinCofinBA)
  singleton-mul-zero n y yn-false = FC≡ (funExt helper)
    where
      helper : (k : ℕ) →
        fst (BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) y) k ≡ false
      helper k with discreteℕ n k
      ... | yes n≡k = J (λ k _ → (n ≡ᵇ k) and fst y k ≡ false)
                        (cong₂ _and_ (δnn=1 n) yn-false) n≡k
      ... | no n≠k = cong₂ _and_ (δnm=0 n k n≠k) refl

  -- If e(x) has underlying sequence everywhere false, then e(x) = 0
  seq-zero-is-zero : (y : ⟨ ℕfinCofinBA ⟩) →
    ((k : ℕ) → fst y k ≡ false) → y ≡ BooleanRingStr.𝟘 (snd ℕfinCofinBA)
  seq-zero-is-zero y all-false = FC≡ (funExt all-false)

  -- f evaluates on generators via QB.evalInduce
  f-eval-quotient : f ∘cr π ≡ f-free
  f-eval-quotient = QB.evalInduce B∞×B∞

  f-eval : (n : ℕ) → fst f (gB∞ n) ≡ interleave-gen n
  f-eval n =
    funExt⁻ (cong fst f-eval-quotient) (generator n)
    ∙ f-free-eval n

  -- gB∞(n) is nonzero in B∞
  gB∞-nonzero : (n : ℕ) → gB∞ n ≡ BR-B∞.𝟘 → ⊥
  gB∞-nonzero n p = true≢false (
    sym (singleton-n-true n) ∙ cong (λ z → fst z n) (sym (e-on-gen n) ∙ cong (fst e) p ∙ E.pres0))

  -- f(gB∞(n)) ≠ 0 in B∞×B∞
  -- interleave-gen-even/odd with explicit proof argument
  ig-even : (m : ℕ) → isEven m ≡ true → interleave-gen m ≡ evenGen (half m)
  ig-even m em with isEven m
  ... | true = refl
  ... | false = ex-falso (false≢true em)

  ig-odd : (m : ℕ) → isEven m ≡ false → interleave-gen m ≡ oddGen (half m)
  ig-odd m em with isEven m
  ... | true = ex-falso (true≢false em)
  ... | false = refl

  f-gen-nonzero : (n : ℕ) → fst f (gB∞ n) ≡ BR-prod.𝟘 → ⊥
  f-gen-nonzero n p = elim-even-odd n
    (λ eq → gB∞-nonzero (half n) (cong snd (sym (f-eval n ∙ ig-even n eq) ∙ p)))
    (λ eq → gB∞-nonzero (half n) (cong fst (sym (f-eval n ∙ ig-odd n eq) ∙ p)))
    where
      elim-even-odd : (m : ℕ) → (isEven m ≡ true → ⊥) → (isEven m ≡ false → ⊥) → ⊥
      elim-even-odd m f g with isEven m
      ... | true = f refl
      ... | false = g refl

-- For the injectivity proof: f(x) = 0 → x = 0
-- Using: gB∞(n) · x = 0 or gB∞(n) for all n (atom property via equivalence)
-- If gB∞(n) · x = gB∞(n), then f(gB∞(n)) = f(gB∞(n) · x) = f(gB∞(n)) · f(x) = f(gB∞(n)) · 0 = 0
-- contradicting f(gB∞(n)) ≠ 0

private
  module FHom = IsCommRingHom (snd f)

  e⁻¹ : ⟨ ℕfinCofinBA ⟩ → ⟨ B∞ ⟩
  e⁻¹ = invEq (fst e , e-is-equiv)

  e⁻¹-zero : e⁻¹ (BooleanRingStr.𝟘 (snd ℕfinCofinBA)) ≡ BR-B∞.𝟘
  e⁻¹-zero =
    cong e⁻¹ (sym E.pres0)
    ∙ retEq (fst e , e-is-equiv) BR-B∞.𝟘

  f-kernel-trivial : (x : ⟨ B∞ ⟩) → fst f x ≡ BR-prod.𝟘 → x ≡ BR-B∞.𝟘
  f-kernel-trivial x fx≡0 =
    sym (retEq (fst e , e-is-equiv) x)
    ∙ cong e⁻¹ (seq-zero-is-zero (fst e x) all-coords-false)
    ∙ e⁻¹-zero
    where
      -- For each n, gB∞(n) · x maps to 0 under f
      f-gen-x-zero : (n : ℕ) → fst f (BR-B∞._·_ (gB∞ n) x) ≡ BR-prod.𝟘
      f-gen-x-zero n =
        FHom.pres· (gB∞ n) x
        ∙ cong (BR-prod._·_ (fst f (gB∞ n))) fx≡0
        ∙ BA-prod.∧AnnihilR

      -- In ℕfinCofinBA: the n-th coordinate of e(x) is false
      -- Proof: singleton(n) · e(x) = e(gB∞(n) · x) = e(gB∞(n)) · e(x)
      -- This equals singleton(n) · e(x).
      -- Case 1: fst (e x) n = true → singleton(n) · e(x) = singleton(n) ≠ 0
      --   But then e(gB∞(n) · x) = singleton(n), so gB∞(n) · x ≠ 0
      --   And f(gB∞(n) · x) = 0, so f maps gB∞(n)·x to 0
      --   But gB∞(n) · x = gB∞(n) (atom property), so f(gB∞(n)) = 0, contradiction
      -- Case 2: fst (e x) n = false → the n-th coordinate is false ✓

      all-coords-false : (n : ℕ) → fst (fst e x) n ≡ false
      all-coords-false n = case-split (fst (fst e x) n) refl
        where
          -- e(gB∞(n) · x) = singleton(n) · e(x)
          e-gen-x : fst e (BR-B∞._·_ (gB∞ n) x)
            ≡ BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) (fst e x)
          e-gen-x =
            E.pres· (gB∞ n) x
            ∙ cong (λ z → BooleanRingStr._·_ (snd ℕfinCofinBA) z (fst e x))
                   (e-on-gen n)

          case-split : (b : Bool) → fst (fst e x) n ≡ b → fst (fst e x) n ≡ false
          case-split false p = p
          case-split true p = ex-falso (f-gen-nonzero n
            (sym (cong (fst f) gen-x-eq)
            ∙ f-gen-x-zero n))
            where
              -- In ℕfinCofinBA: singleton(n) · e(x) = singleton(n) (since coordinate n is true)
              sing-eq : BooleanRingStr._·_ (snd ℕfinCofinBA) (singleton n) (fst e x) ≡ singleton n
              sing-eq = singleton-mul n (fst e x) p

              -- e(gB∞(n) · x) = singleton(n) = e(gB∞(n))
              e-gen-x-eq : fst e (BR-B∞._·_ (gB∞ n) x) ≡ fst e (gB∞ n)
              e-gen-x-eq = e-gen-x ∙ sing-eq ∙ sym (e-on-gen n)

              -- Since e is an equivalence (hence injective): gB∞(n) · x = gB∞(n)
              gen-x-eq : BR-B∞._·_ (gB∞ n) x ≡ gB∞ n
              gen-x-eq =
                sym (retEq (_ , e-is-equiv) _)
                ∙ cong (invEq (_ , e-is-equiv)) e-gen-x-eq
                ∙ retEq (_ , e-is-equiv) _

f-injective : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective x y fx≡fy =
  sym (BR-B∞.+IdR x)
  ∙ cong (BR-B∞._+_ x) (sym xy≡0)
  ∙ assoc-step
  ∙ cong (λ z → BR-B∞._+_ z y) BA-B∞.characteristic2
  ∙ BR-B∞.+IdL y
  where
    -- f(x + y) = f(x) + f(y) = f(y) + f(y) = 0
    fxy≡0 : fst f (BR-B∞._+_ x y) ≡ BR-prod.𝟘
    fxy≡0 =
      FHom.pres+ x y
      ∙ cong (λ z → BR-prod._+_ z (fst f y)) fx≡fy
      ∙ BA-prod.characteristic2

    xy≡0 : BR-B∞._+_ x y ≡ BR-B∞.𝟘
    xy≡0 = f-kernel-trivial (BR-B∞._+_ x y) fxy≡0

    -- x + (x + y) ≡ (x + x) + y (associativity)
    assoc-step : BR-B∞._+_ x (BR-B∞._+_ x y) ≡ BR-B∞._+_ (BR-B∞._+_ x x) y
    assoc-step = BR-B∞.+Assoc x x y

-- ═══════════════════════════════════════════════════════════════
-- Part 5: B∞ × B∞ is countably presented
-- ═══════════════════════════════════════════════════════════════

-- The product of countably presented Boolean rings is countably presented.
-- Presentation: freeBA ℕ with generators encoded as:
--   gen 0         = e (the idempotent, maps to (1,0))
--   gen (2n+1)    = l_n (left generator, maps to (gB∞ n, 0))
--   gen (2n+2)    = r_n (right generator, maps to (0, gB∞ n))
-- Relations encode: left/right/cross orthogonality + idempotent absorption

module B∞×B∞-presentation where

  -- Generator encoding:
  --   gen 0         → (1, 0) = e (idempotent separator)
  --   gen (suc(2k)) = gen(2k+1) → (gB∞ k, 0) = left gen k
  --   gen (suc(suc(2k))) = gen(2k+2) → (0, gB∞ k) = right gen k
  gen-target : ℕ → ⟨ B∞×B∞ ⟩
  gen-target zero = BR-B∞.𝟙 , BR-B∞.𝟘
  gen-target (suc n) with isEven n
  ... | true  = gB∞ (half n) , BR-B∞.𝟘    -- suc(2k) = 2k+1 → left gen k
  ... | false = BR-B∞.𝟘 , gB∞ (half n)    -- suc(2k+1) = 2k+2 → right gen k

  -- Computation lemmas for gen-target
  gt-idem : gen-target 0 ≡ (BR-B∞.𝟙 , BR-B∞.𝟘)
  gt-idem = refl

  gt-left : (k : ℕ) → gen-target (suc (double k)) ≡ (gB∞ k , BR-B∞.𝟘)
  gt-left k with isEven (double k) in eq
  ... | true = cong (_, BR-B∞.𝟘) (cong gB∞ (half-double k))
  ... | false = ex-falso (false≢true (sym (builtin→Path eq) ∙ isEven-double k))

  gt-right : (k : ℕ) → gen-target (suc (suc (double k))) ≡ (BR-B∞.𝟘 , gB∞ k)
  gt-right k with isEven (suc (double k)) in eq
  ... | true = ex-falso (true≢false (sym (builtin→Path eq) ∙ isOdd-double+1 k))
  ... | false = cong (BR-B∞.𝟘 ,_) (cong gB∞ (half-double+1 k))

  -- The map freeBA ℕ → B∞×B∞ induced by gen-target
  φ-free : BoolHom (freeBA ℕ) B∞×B∞
  φ-free = inducedBAHom ℕ B∞×B∞ gen-target

  private
    gen = generator {A = ℕ}
    _·f_ = BooleanRingStr._·_ (snd (freeBA ℕ))
    _+f_ = BooleanRingStr._+_ (snd (freeBA ℕ))
    𝟘f = BooleanRingStr.𝟘 (snd (freeBA ℕ))

    -- φ-free evaluates on generators
    φ-eval : (n : ℕ) → fst φ-free (gen n) ≡ gen-target n
    φ-eval n = funExt⁻ (evalBAInduce ℕ B∞×B∞ gen-target) n

    module ΦH = IsCommRingHom (snd φ-free)

  -- Relation families (defined at module level for easier proofs)
  case-family : ℕ → ℕ → ℕ → ⟨ freeBA ℕ ⟩
  -- Family 0: left orth — gen(2n+1) · gen(2m+1), trivial when n=m
  case-family zero n m with discreteℕ n m
  ... | yes _ = 𝟘f
  ... | no  _ = gen (suc (double n)) ·f gen (suc (double m))
  -- Family 1: right orth — gen(2n+2) · gen(2m+2), trivial when n=m
  case-family (suc zero) n m with discreteℕ n m
  ... | yes _ = 𝟘f
  ... | no  _ = gen (suc (suc (double n))) ·f gen (suc (suc (double m)))
  -- Family 2: cross orth — gen(2n+1) · gen(2m+2) for all n,m
  case-family (suc (suc zero)) n m =
    gen (suc (double n)) ·f gen (suc (suc (double m)))
  -- Family 3: left absorb — gen(0) · gen(2n+1) + gen(2n+1)
  case-family (suc (suc (suc zero))) n _ =
    (gen 0 ·f gen (suc (double n))) +f gen (suc (double n))
  -- Family 4: right annihil — gen(0) · gen(2n+2)
  case-family (suc (suc (suc (suc zero)))) n _ =
    gen 0 ·f gen (suc (suc (double n)))
  -- Other families: trivial
  case-family _ _ _ = 𝟘f

  -- Relations encoded via ℕ×ℕ≅ℕ
  prod-relations : ℕ → ⟨ freeBA ℕ ⟩
  prod-relations k =
    let (fam , idx) = Iso.inv ℕ×ℕ≅ℕ k
        (n , m) = Iso.inv ℕ×ℕ≅ℕ idx
    in case-family fam n m

  -- The quotient ring
  Q-prod : BooleanRing ℓ-zero
  Q-prod = freeBA ℕ /Im prod-relations

  -- Show each relation family maps to 0 under φ-free
  private
    -- gB∞ orthogonality in B∞ (lifted from gen-orth via π pres·)
    gB∞-mul-zero : (n m : ℕ) → (n ≡ m → ⊥) → BR-B∞._·_ (gB∞ n) (gB∞ m) ≡ BR-B∞.𝟘
    gB∞-mul-zero n m n≠m = sym (ΠH.pres· (generator n) (generator m)) ∙ gen-orth n m n≠m

    cf-respected : (fam n m : ℕ) → fst φ-free (case-family fam n m) ≡ BR-prod.𝟘
    -- Family 0: left orth — (gB∞ n, 0) · (gB∞ m, 0) = (gB∞ n · gB∞ m, 0) = (0, 0)
    cf-respected zero n m with discreteℕ n m
    ... | yes _ = ΦH.pres0
    ... | no n≠m =
      ΦH.pres· (gen (suc (double n))) (gen (suc (double m)))
      ∙ cong₂ BR-prod._·_ (φ-eval (suc (double n)) ∙ gt-left n)
                            (φ-eval (suc (double m)) ∙ gt-left m)
      ∙ ΣPathP (gB∞-mul-zero n m n≠m , BA-B∞.∧AnnihilL)
    -- Family 1: right orth — (0, gB∞ n) · (0, gB∞ m) = (0, gB∞ n · gB∞ m) = (0, 0)
    cf-respected (suc zero) n m with discreteℕ n m
    ... | yes _ = ΦH.pres0
    ... | no n≠m =
      ΦH.pres· (gen (suc (suc (double n)))) (gen (suc (suc (double m))))
      ∙ cong₂ BR-prod._·_ (φ-eval (suc (suc (double n))) ∙ gt-right n)
                            (φ-eval (suc (suc (double m))) ∙ gt-right m)
      ∙ ΣPathP (BA-B∞.∧AnnihilL , gB∞-mul-zero n m n≠m)
    -- Family 2: cross orth — (gB∞ n, 0) · (0, gB∞ m) = (gB∞ n · 0, 0 · gB∞ m) = (0, 0)
    cf-respected (suc (suc zero)) n m =
      ΦH.pres· (gen (suc (double n))) (gen (suc (suc (double m))))
      ∙ cong₂ BR-prod._·_ (φ-eval (suc (double n)) ∙ gt-left n)
                            (φ-eval (suc (suc (double m))) ∙ gt-right m)
      ∙ ΣPathP (BA-B∞.∧AnnihilR , BA-B∞.∧AnnihilL)
    -- Family 3: left absorb — (1,0)·(gB∞ n,0) + (gB∞ n,0) = (gB∞ n,0)+(gB∞ n,0) = (0,0)
    cf-respected (suc (suc (suc zero))) n _ =
      ΦH.pres+ _ _
      ∙ cong₂ BR-prod._+_
          (ΦH.pres· (gen 0) (gen (suc (double n)))
           ∙ cong₂ BR-prod._·_ (φ-eval 0) (φ-eval (suc (double n)) ∙ gt-left n)
           ∙ ΣPathP (BR-B∞.·IdL (gB∞ n) , BA-B∞.∧AnnihilL))
          (φ-eval (suc (double n)) ∙ gt-left n)
      ∙ ΣPathP (BA-B∞.characteristic2 , BR-B∞.+IdL BR-B∞.𝟘)
    -- Family 4: right annihil — (1,0)·(0,gB∞ n) = (1·0, 0·gB∞ n) = (0, 0)
    cf-respected (suc (suc (suc (suc zero)))) n _ =
      ΦH.pres· (gen 0) (gen (suc (suc (double n))))
      ∙ cong₂ BR-prod._·_ (φ-eval 0) (φ-eval (suc (suc (double n))) ∙ gt-right n)
      ∙ ΣPathP (BA-B∞.∧AnnihilR , BA-B∞.∧AnnihilL)
    -- Other families
    cf-respected (suc (suc (suc (suc (suc _))))) _ _ = ΦH.pres0

  φ-free-respects-rels : (k : ℕ) → fst φ-free (prod-relations k) ≡ BR-prod.𝟘
  φ-free-respects-rels k = cf-respected
    (fst (Iso.inv ℕ×ℕ≅ℕ k))
    (fst (Iso.inv ℕ×ℕ≅ℕ (snd (Iso.inv ℕ×ℕ≅ℕ k))))
    (snd (Iso.inv ℕ×ℕ≅ℕ (snd (Iso.inv ℕ×ℕ≅ℕ k))))

  -- The induced map Q-prod → B∞×B∞
  φ-bar : BoolHom Q-prod B∞×B∞
  φ-bar = QB.inducedHom B∞×B∞ φ-free φ-free-respects-rels

  -- === Construction of ψ : B∞×B∞ → Q-prod ===

  private
    π-prod : BoolHom (freeBA ℕ) Q-prod
    π-prod = QB.quotientImageHom {f = prod-relations}

    module QP = BooleanRingStr (snd Q-prod)
    module QPA = BooleanAlgebraStr (snd Q-prod)
    module ΠP = IsCommRingHom (snd π-prod)

    -- The idempotent [e] and its complement [1+e]
    [e] : ⟨ Q-prod ⟩
    [e] = fst π-prod (gen 0)

    [1+e] : ⟨ Q-prod ⟩
    [1+e] = QP._+_ QP.𝟙 [e]

    -- Key lemma: prod-relations unfolds through the isomorphisms
    -- prod-relations (fun(fam, fun(n,m))) = case-family fam n m
    -- because inv(fun(x)) = x by Iso.ret
    pr-unfold : (fam n m : ℕ) →
      prod-relations (Iso.fun ℕ×ℕ≅ℕ (fam , Iso.fun ℕ×ℕ≅ℕ (n , m)))
        ≡ case-family fam n m
    pr-unfold fam n m =
      cong (λ p → let (n' , m') = Iso.inv ℕ×ℕ≅ℕ (snd p) in case-family (fst p) n' m')
           (Iso.ret ℕ×ℕ≅ℕ (fam , Iso.fun ℕ×ℕ≅ℕ (n , m)))
      ∙ cong (λ p → case-family fam (fst p) (snd p))
             (Iso.ret ℕ×ℕ≅ℕ (n , m))

    -- Family 0 relation: gen(2n+1) · gen(2m+1) for n ≠ m is a relation
    prod-fam0 : (n m : ℕ) → (n ≡ m → ⊥) →
      fst π-prod (gen (suc (double n)) ·f gen (suc (double m))) ≡ QP.𝟘
    prod-fam0 n m n≠m =
      cong (fst π-prod) (lem ∙ sym (pr-unfold 0 n m))
      ∙ QB.zeroOnImage {f = prod-relations} _
      where
        lem : gen (suc (double n)) ·f gen (suc (double m)) ≡ case-family 0 n m
        lem with discreteℕ n m
        ... | yes n≡m = ex-falso (n≠m n≡m)
        ... | no  _   = refl

    -- Family 1 relation: gen(2n+2) · gen(2m+2) for n ≠ m
    prod-fam1 : (n m : ℕ) → (n ≡ m → ⊥) →
      fst π-prod (gen (suc (suc (double n))) ·f gen (suc (suc (double m)))) ≡ QP.𝟘
    prod-fam1 n m n≠m =
      cong (fst π-prod) (lem ∙ sym (pr-unfold 1 n m))
      ∙ QB.zeroOnImage {f = prod-relations} _
      where
        lem : gen (suc (suc (double n))) ·f gen (suc (suc (double m))) ≡ case-family 1 n m
        lem with discreteℕ n m
        ... | yes n≡m = ex-falso (n≠m n≡m)
        ... | no  _   = refl

    -- Left embedding free map
    left-on-gen : ℕ → ⟨ Q-prod ⟩
    left-on-gen n = fst π-prod (gen (suc (double n)))

    left-free : BoolHom (freeBA ℕ) Q-prod
    left-free = inducedBAHom ℕ Q-prod left-on-gen

    module LFH = IsCommRingHom (snd left-free)

    left-free-eval : (n : ℕ) → fst left-free (generator n) ≡ left-on-gen n
    left-free-eval n = funExt⁻ (evalBAInduce ℕ Q-prod left-on-gen) n

    -- left-free respects B∞'s relations
    left-free-respects : (k : ℕ) → fst left-free (relationsℕ k) ≡ QP.𝟘
    left-free-respects k = go (Iso.inv ℕ×ℕ≅ℕ k)
      where
        go : (p : ℕ × ℕ) → fst left-free (relations p) ≡ QP.𝟘
        go (n , m) with discreteℕ n m
        ... | yes _ = LFH.pres0
        ... | no n≠m =
          LFH.pres· (generator n) (generator m)
          ∙ cong₂ QP._·_ (left-free-eval n) (left-free-eval m)
          ∙ sym (ΠP.pres· (gen (suc (double n))) (gen (suc (double m))))
          ∙ prod-fam0 n m n≠m

    left : BoolHom B∞ Q-prod
    left = QB.inducedHom Q-prod left-free left-free-respects

    -- Right embedding
    right-on-gen : ℕ → ⟨ Q-prod ⟩
    right-on-gen n = fst π-prod (gen (suc (suc (double n))))

    right-free : BoolHom (freeBA ℕ) Q-prod
    right-free = inducedBAHom ℕ Q-prod right-on-gen

    module RFH = IsCommRingHom (snd right-free)

    right-free-eval : (n : ℕ) → fst right-free (generator n) ≡ right-on-gen n
    right-free-eval n = funExt⁻ (evalBAInduce ℕ Q-prod right-on-gen) n

    right-free-respects : (k : ℕ) → fst right-free (relationsℕ k) ≡ QP.𝟘
    right-free-respects k = go (Iso.inv ℕ×ℕ≅ℕ k)
      where
        go : (p : ℕ × ℕ) → fst right-free (relations p) ≡ QP.𝟘
        go (n , m) with discreteℕ n m
        ... | yes _ = RFH.pres0
        ... | no n≠m =
          RFH.pres· (generator n) (generator m)
          ∙ cong₂ QP._·_ (right-free-eval n) (right-free-eval m)
          ∙ sym (ΠP.pres· (gen (suc (suc (double n)))) (gen (suc (suc (double m)))))
          ∙ prod-fam1 n m n≠m

    right : BoolHom B∞ Q-prod
    right = QB.inducedHom Q-prod right-free right-free-respects

  -- ψ(b, c) = left(b) · [e] + right(c) · [1+e]
  private
    ψ-fun : ⟨ B∞×B∞ ⟩ → ⟨ Q-prod ⟩
    ψ-fun (b , c) = QP._+_ (QP._·_ (fst left b) [e]) (QP._·_ (fst right c) [1+e])

    -- [e] · [1+e] = 0 (orthogonality of idempotents)
    -- [e] · (1 + [e]) = [e] + [e]·[e] = [e] + [e] = 0 (char 2 + idempotent)
    [e]·[1+e]≡0 : QP._·_ [e] [1+e] ≡ QP.𝟘
    [e]·[1+e]≡0 =
      QP.·DistR+ [e] QP.𝟙 [e]
      ∙ cong₂ QP._+_ (QP.·IdR [e]) (QP.·Idem [e])
      ∙ QPA.characteristic2

    -- [e] + [1+e] = [e] + 1 + [e] = 1 (in char 2, e + 1 + e = 1)
    [e]+[1+e]≡1 : QP._+_ [e] [1+e] ≡ QP.𝟙
    [e]+[1+e]≡1 =
      QP.+Assoc [e] QP.𝟙 [e]
      ∙ cong (λ z → QP._+_ z [e]) (QP.+Comm [e] QP.𝟙)
      ∙ sym (QP.+Assoc QP.𝟙 [e] [e])
      ∙ cong (QP._+_ QP.𝟙) QPA.characteristic2
      ∙ QP.+IdR QP.𝟙

    [1+e]·[e]≡0 : QP._·_ [1+e] [e] ≡ QP.𝟘
    [1+e]·[e]≡0 = QP.·Comm [1+e] [e] ∙ [e]·[1+e]≡0

    [1+e]-idem : QP._·_ [1+e] [1+e] ≡ [1+e]
    [1+e]-idem =
      -- (1+e)(1+e) = 1+e+e+e² = 1+e+e+e = 1+(e+e)+e = 1+0+e = 1+e
      QP.·DistR+ [1+e] QP.𝟙 [e]
      ∙ cong₂ QP._+_ (QP.·IdR [1+e])
          (QP.·DistL+ QP.𝟙 [e] [e]
          ∙ cong₂ QP._+_ (QP.·IdL [e]) (QP.·Idem [e]))
      -- now: [1+e] + ([e] + [e])
      ∙ cong (QP._+_ [1+e]) QPA.characteristic2
      ∙ QP.+IdR [1+e]

  -- Showing ψ-fun is a ring homomorphism
  ψ : BoolHom B∞×B∞ Q-prod
  fst ψ = ψ-fun
  snd ψ = makeIsCommRingHom ψ-pres1 ψ-pres+ ψ-pres·
    where
      module LH = IsCommRingHom (snd left)
      module RH = IsCommRingHom (snd right)

      -- ψ(1,1) = left(1)·[e] + right(1)·[1+e] = 1·[e] + 1·[1+e] = [e] + [1+e] = 1
      ψ-pres1 : ψ-fun (BR-B∞.𝟙 , BR-B∞.𝟙) ≡ QP.𝟙
      ψ-pres1 = cong₂ QP._+_
        (cong (λ z → QP._·_ z [e]) LH.pres1 ∙ QP.·IdL [e])
        (cong (λ z → QP._·_ z [1+e]) RH.pres1 ∙ QP.·IdL [1+e])
        ∙ [e]+[1+e]≡1

      -- For +: ψ(a₁+a₂, b₁+b₂) = left(a₁+a₂)·[e] + right(b₁+b₂)·[1+e]
      -- = (left a₁ + left a₂)·[e] + (right b₁ + right b₂)·[1+e]
      -- = left a₁·[e] + left a₂·[e] + right b₁·[1+e] + right b₂·[1+e]
      -- = ψ(a₁,b₁) + ψ(a₂,b₂)
      -- This works because + is commutative and associative
      -- + preserving: both sides reduce to
      -- left(a₁)·[e] + left(a₂)·[e] + right(b₁)·[1+e] + right(b₂)·[1+e]
      -- after using pres+ of left/right and distrib of · over +

      -- (a+b)·e + (c+d)·f = a·e + b·e + (c·f + d·f) = (a·e + c·f) + (b·e + d·f)
      ψ-pres+ : (x y : ⟨ B∞×B∞ ⟩) → ψ-fun (BR-prod._+_ x y) ≡ QP._+_ (ψ-fun x) (ψ-fun y)
      ψ-pres+ (a₁ , b₁) (a₂ , b₂) =
        let la₁ = fst left a₁ ; la₂ = fst left a₂
            rb₁ = fst right b₁ ; rb₂ = fst right b₂
        in
        cong₂ QP._+_
          (cong (λ z → QP._·_ z [e]) (LH.pres+ a₁ a₂) ∙ QP.·DistL+ la₁ la₂ [e])
          (cong (λ z → QP._·_ z [1+e]) (RH.pres+ b₁ b₂) ∙ QP.·DistL+ rb₁ rb₂ [1+e])
        ∙ swap4 (QP._·_ la₁ [e]) (QP._·_ la₂ [e]) (QP._·_ rb₁ [1+e]) (QP._·_ rb₂ [1+e])
        where
          -- (a + b) + (c + d) = (a + c) + (b + d)
          swap4 : (a b c d : ⟨ Q-prod ⟩) → QP._+_ (QP._+_ a b) (QP._+_ c d) ≡ QP._+_ (QP._+_ a c) (QP._+_ b d)
          swap4 a b c d =
            sym (QP.+Assoc a b (QP._+_ c d))
            ∙ cong (QP._+_ a)
                (QP.+Assoc b c d
                ∙ cong (λ z → QP._+_ z d) (QP.+Comm b c)
                ∙ sym (QP.+Assoc c b d))
            ∙ QP.+Assoc a c (QP._+_ b d)

      -- (ab)(cd) = (ac)(bd) in a commutative ring
      ·4-rearrange : (a b c d : ⟨ Q-prod ⟩) →
        QP._·_ (QP._·_ a b) (QP._·_ c d) ≡ QP._·_ (QP._·_ a c) (QP._·_ b d)
      ·4-rearrange a b c d =
        -- (ab)(cd) →sym-assoc a(b(cd)) →assoc a((bc)d) →comm a((cb)d) →sym-assoc a(c(bd)) →assoc (ac)(bd)
        sym (QP.·Assoc a b (QP._·_ c d))
        ∙ cong (QP._·_ a)
            (QP.·Assoc b c d
            ∙ cong (λ z → QP._·_ z d) (QP.·Comm b c)
            ∙ sym (QP.·Assoc c b d))
        ∙ QP.·Assoc a c (QP._·_ b d)

      -- Helper: (a·e + b·f)·(c·e + d·f) = a·c·e + b·d·f
      -- when e·f=0, f·e=0, e²=e, f²=f
      orth-idem-mul : (a b c d : ⟨ Q-prod ⟩) →
        QP._·_ (QP._+_ (QP._·_ a [e]) (QP._·_ b [1+e]))
               (QP._+_ (QP._·_ c [e]) (QP._·_ d [1+e]))
        ≡ QP._+_ (QP._·_ (QP._·_ a c) [e]) (QP._·_ (QP._·_ b d) [1+e])
      orth-idem-mul a b c d =
        let ae = QP._·_ a [e] ; bf = QP._·_ b [1+e]
            ce = QP._·_ c [e] ; df = QP._·_ d [1+e]
        in
        -- distribute: (ae+bf)(ce+df) = ae(ce+df) + bf(ce+df)
        QP.·DistL+ ae bf (QP._+_ ce df)
        -- = (ae·ce + ae·df) + (bf·ce + bf·df)
        ∙ cong₂ QP._+_
            (QP.·DistR+ ae ce df)
            (QP.·DistR+ bf ce df)
        -- simplify using ·4-rearrange: (ae)(ce) = (ac)(ee) = (ac)e, etc.
        ∙ cong₂ QP._+_
            (cong₂ QP._+_
              -- ae·ce = (ac)(ee) = (ac)e
              (·4-rearrange a [e] c [e] ∙ cong (QP._·_ (QP._·_ a c)) (QP.·Idem [e]))
              -- ae·df = (ad)(ef) = (ad)·0 = 0
              (·4-rearrange a [e] d [1+e] ∙ cong (QP._·_ (QP._·_ a d)) [e]·[1+e]≡0 ∙ QPA.∧AnnihilR)
            ∙ QP.+IdR (QP._·_ (QP._·_ a c) [e]))
            (cong₂ QP._+_
              -- bf·ce = (bc)(fe) = (bc)·0 = 0
              (·4-rearrange b [1+e] c [e] ∙ cong (QP._·_ (QP._·_ b c)) [1+e]·[e]≡0 ∙ QPA.∧AnnihilR)
              -- bf·df = (bd)(ff) = (bd)f
              (·4-rearrange b [1+e] d [1+e] ∙ cong (QP._·_ (QP._·_ b d)) [1+e]-idem)
            ∙ QP.+IdL (QP._·_ (QP._·_ b d) [1+e]))

      ψ-pres· : (x y : ⟨ B∞×B∞ ⟩) → ψ-fun (BR-prod._·_ x y) ≡ QP._·_ (ψ-fun x) (ψ-fun y)
      ψ-pres· (a₁ , b₁) (a₂ , b₂) =
        cong₂ QP._+_
          (cong (λ z → QP._·_ z [e]) (LH.pres· a₁ a₂))
          (cong (λ z → QP._·_ z [1+e]) (RH.pres· b₁ b₂))
        ∙ sym (orth-idem-mul (fst left a₁) (fst right b₁) (fst left a₂) (fst right b₂))

  -- Key relation consequences in Q-prod
  private
    module ΦB = IsCommRingHom (snd φ-bar)

    -- φ-bar evaluates on generators: φ-bar(π-prod(gen n)) = gen-target n
    φ-bar-comp : φ-bar ∘cr π-prod ≡ φ-free
    φ-bar-comp = QB.evalInduce {f = prod-relations} B∞×B∞

    -- left evaluates on generators: left(gB∞ k) = π-prod(gen(suc(2k)))
    left-comp : left ∘cr QB.quotientImageHom {f = relationsℕ} ≡ left-free
    left-comp = QB.evalInduce {f = relationsℕ} Q-prod

    left-eval : (k : ℕ) → fst left (gB∞ k) ≡ fst π-prod (gen (suc (double k)))
    left-eval k = funExt⁻ (cong fst left-comp) (generator k) ∙ left-free-eval k

    right-comp : right ∘cr QB.quotientImageHom {f = relationsℕ} ≡ right-free
    right-comp = QB.evalInduce {f = relationsℕ} Q-prod

    right-eval : (k : ℕ) → fst right (gB∞ k) ≡ fst π-prod (gen (suc (suc (double k))))
    right-eval k = funExt⁻ (cong fst right-comp) (generator k) ∙ right-free-eval k

    -- Helper: in char 2, a + b = 0 implies a = b
    char2-cancel : (a b : ⟨ Q-prod ⟩) → QP._+_ a b ≡ QP.𝟘 → a ≡ b
    char2-cancel a b p =
      a ≡⟨ sym (QP.+IdR a) ⟩
      QP._+_ a QP.𝟘 ≡⟨ cong (QP._+_ a) (sym QPA.characteristic2) ⟩
      QP._+_ a (QP._+_ b b) ≡⟨ QP.+Assoc a b b ⟩
      QP._+_ (QP._+_ a b) b ≡⟨ cong (λ z → QP._+_ z b) p ⟩
      QP._+_ QP.𝟘 b ≡⟨ QP.+IdL b ⟩
      b ∎

    -- Relation consequence helper: fst π-prod (case-family fam n m) ≡ 0
    cf-zero : (fam n m : ℕ) → fst π-prod (case-family fam n m) ≡ QP.𝟘
    cf-zero fam n m = cong (fst π-prod) (sym (pr-unfold fam n m))
      ∙ QB.zeroOnImage {f = prod-relations} _

    -- Family 3: [e]·left-gen + left-gen = 0, hence [e]·left-gen = left-gen
    [e]·left-gen : (n : ℕ) → QP._·_ [e] (fst π-prod (gen (suc (double n)))) ≡ fst π-prod (gen (suc (double n)))
    [e]·left-gen n = char2-cancel _ _ rel
      where
        rel : QP._+_ (QP._·_ [e] (fst π-prod (gen (suc (double n))))) (fst π-prod (gen (suc (double n)))) ≡ QP.𝟘
        rel = cong₂ QP._+_ (sym (ΠP.pres· (gen 0) (gen (suc (double n))))) refl
              ∙ sym (ΠP.pres+ (gen 0 ·f gen (suc (double n))) (gen (suc (double n))))
              ∙ cf-zero 3 n 0

    -- Family 4: [e]·right-gen = 0
    [e]·right-gen : (n : ℕ) → QP._·_ [e] (fst π-prod (gen (suc (suc (double n))))) ≡ QP.𝟘
    [e]·right-gen n =
      sym (ΠP.pres· (gen 0) (gen (suc (suc (double n)))))
      ∙ cf-zero 4 n 0

  -- Roundtrip 2: ψ(φ-bar(x)) = x for all x ∈ Q-prod
  -- By quotient epi: suffices to check on π-prod(gen n)
  roundtrip2 : (x : ⟨ Q-prod ⟩) → fst ψ (fst φ-bar x) ≡ x
  roundtrip2 = {! !}

  -- Roundtrip 1: φ-bar(ψ(x)) = x for all x ∈ B∞×B∞
  roundtrip1 : (x : ⟨ B∞×B∞ ⟩) → fst φ-bar (fst ψ x) ≡ x
  roundtrip1 = {! !}

  -- Assembly
  φ-bar-is-equiv : isEquiv (fst φ-bar)
  φ-bar-is-equiv = isoToIsEquiv (iso (fst φ-bar) (fst ψ) roundtrip1 roundtrip2)

  Q-prod-equiv : BooleanRingEquiv Q-prod B∞×B∞
  Q-prod-equiv = (fst φ-bar , φ-bar-is-equiv) , snd φ-bar

  B∞×B∞-equiv : BooleanRingEquiv B∞×B∞ Q-prod
  B∞×B∞-equiv = invBooleanRingEquiv Q-prod B∞×B∞ Q-prod-equiv

B∞×B∞-cp : is-countably-presented-alt B∞×B∞
B∞×B∞-cp = ∣ B∞×B∞-presentation.prod-relations , B∞×B∞-presentation.B∞×B∞-equiv ∣₁

B∞×B∞ω : Booleω
B∞×B∞ω = B∞×B∞ , B∞×B∞-cp

-- ═══════════════════════════════════════════════════════════════
-- Part 6: Key lemma about BoolHom out of products
-- ═══════════════════════════════════════════════════════════════

-- For γ : BoolHom (A×B) BoolBR, (1,0) and (0,1) are orthogonal idempotents
-- summing to 1. In Bool, this forces one to be true and the other false.
-- Consequence: γ kills either all (0,x) or all (x,0).

-- We don't need the full Sp(A×B) ≅ Sp(A) ⊎ Sp(B) iso for LLPO;
-- we only need the dichotomy on which component γ kills.

private
  module BoolStr = BooleanRingStr (snd BoolBR)

  -- (𝟘, 𝟙) · (𝟘, x) = (𝟘, x) in A×B
  prod-0x-factor : (x : ⟨ B∞ ⟩) →
    BR-prod._·_ (BR-B∞.𝟘 , BR-B∞.𝟙) (BR-B∞.𝟘 , x) ≡ (BR-B∞.𝟘 , x)
  prod-0x-factor x = ΣPathP (BA-B∞.∧AnnihilL , BR-B∞.·IdL x)

  -- (𝟙, 𝟘) · (x, 𝟘) = (x, 𝟘) in A×B
  prod-x0-factor : (x : ⟨ B∞ ⟩) →
    BR-prod._·_ (BR-B∞.𝟙 , BR-B∞.𝟘) (x , BR-B∞.𝟘) ≡ (x , BR-B∞.𝟘)
  prod-x0-factor x = ΣPathP (BR-B∞.·IdL x , BA-B∞.∧AnnihilL)

  -- (𝟙, 𝟘) + (𝟘, 𝟙) = (𝟙, 𝟙)
  prod-idem-sum : BR-prod._+_ (BR-B∞.𝟙 , BR-B∞.𝟘) (BR-B∞.𝟘 , BR-B∞.𝟙) ≡ (BR-B∞.𝟙 , BR-B∞.𝟙)
  prod-idem-sum = ΣPathP (BR-B∞.+IdR BR-B∞.𝟙 , BR-B∞.+IdL BR-B∞.𝟙)

  -- false and x = false (definitional, but useful as a lemma)
  false-and : (x : Bool) → false and x ≡ false
  false-and _ = refl

-- ═══════════════════════════════════════════════════════════════
-- Part 6b: Helper lemmas for evaluating f on generators
-- ═══════════════════════════════════════════════════════════════

-- interleave-gen on double k is evenGen k
interleave-gen-even : (k : ℕ) → interleave-gen (double k) ≡ evenGen k
interleave-gen-even k with isEven (double k) in eq
... | true = cong evenGen (half-double k)
... | false = ex-falso (false≢true (sym (builtin→Path eq) ∙ isEven-double k))

-- interleave-gen on suc(double k) is oddGen k
interleave-gen-odd : (k : ℕ) → interleave-gen (suc (double k)) ≡ oddGen k
interleave-gen-odd k with isEven (suc (double k)) in eq
... | true = ex-falso (true≢false (sym (builtin→Path eq) ∙ isOdd-double+1 k))
... | false = cong oddGen (half-double+1 k)

-- f evaluates on generators via QB.evalInduce
-- (moved to before f-injective section)

-- ═══════════════════════════════════════════════════════════════
-- Part 7: Apply the axiom and derive LLPO
-- ═══════════════════════════════════════════════════════════════

LLPO-statement : Type
LLPO-statement =
  (α : binarySequence) → hits1AtMostOnce α →
  ∥ ((n : ℕ) → α (double n) ≡ false) ⊎ ((n : ℕ) → α (suc (double n)) ≡ false) ∥₁

-- Orthogonality of α values when hits1AtMostOnce
private
  α-and-false : (α : binarySequence) → hits1AtMostOnce α →
    (n m : ℕ) → (n ≡ m → ⊥) → (α n) and (α m) ≡ false
  α-and-false α h1o n m n≠m = helper (α n) (α m) refl refl
    where
      helper : (a b : Bool) → α n ≡ a → α m ≡ b → a and b ≡ false
      helper false _ _ _ = refl
      helper true false _ _ = refl
      helper true true eqN eqM = ex-falso (n≠m (h1o n m eqN eqM))

-- The main theorem
LLPO : formalSurjectionsAreSurjectionsAxiom → LLPO-statement
LLPO axiom α h1o = PT.rec squash₁ analyze (surj φ_α)
  where
    -- Step 1: α defines a BoolHom freeBA ℕ → BoolBR via the universal property
    g_α : BoolHom (freeBA ℕ) BoolBR
    g_α = inducedBAHom ℕ BoolBR α

    module G_α = IsCommRingHom (snd g_α)

    g_α-eval : (n : ℕ) → fst g_α (generator n) ≡ α n
    g_α-eval n = funExt⁻ (evalBAInduce ℕ BoolBR α) n

    -- Step 2: g_α respects the relations of B∞
    g_α-respects : (k : ℕ) → fst g_α (relationsℕ k) ≡ false
    g_α-respects k = g_α-respects' (Iso.inv ℕ×ℕ≅ℕ k)
      where
        g_α-respects' : (p : ℕ × ℕ) → fst g_α (relations p) ≡ false
        g_α-respects' (n , m) with discreteℕ n m
        ... | yes _ = G_α.pres0
        ... | no n≠m =
          fst g_α (generator n · generator m)
            ≡⟨ G_α.pres· (generator n) (generator m) ⟩
          (fst g_α (generator n)) and (fst g_α (generator m))
            ≡⟨ cong₂ _and_ (g_α-eval n) (g_α-eval m) ⟩
          (α n) and (α m)
            ≡⟨ α-and-false α h1o n m n≠m ⟩
          false ∎

    -- Step 3: Descend to φ_α : BoolHom B∞ → BoolBR
    φ_α : BoolHom B∞ BoolBR
    φ_α = QB.inducedHom BoolBR g_α g_α-respects

    -- φ_α evaluates correctly on generators
    φ_α-eval-quotient : φ_α ∘cr π ≡ g_α
    φ_α-eval-quotient = QB.evalInduce BoolBR

    φ_α-eval : (n : ℕ) → fst φ_α (gB∞ n) ≡ α n
    φ_α-eval n =
      funExt⁻ (cong fst φ_α-eval-quotient) (generator n)
      ∙ g_α-eval n

    -- Step 4: Apply the axiom to get surjection Sp(B∞×B∞) ↠ Sp(B∞)
    surj : isSurjection (λ (γ : Sp B∞×B∞ω) → γ ∘cr f)
    surj = axiom B∞ω B∞×B∞ω f f-injective

    -- Step 5: Analyze γ ∈ Sp(B∞×B∞) by its value on (1,0)
    analyze : (Σ[ γ ∈ Sp B∞×B∞ω ] (γ ∘cr f) ≡ φ_α) →
      ∥ ((n : ℕ) → α (double n) ≡ false) ⊎ ((n : ℕ) → α (suc (double n)) ≡ false) ∥₁
    analyze (γ , γf≡φ) = dichotomy (fst γ (BR-B∞.𝟙 , BR-B∞.𝟘)) refl
      where
        module Γ = IsCommRingHom (snd γ)

        -- γ ∘ f agrees with φ_α pointwise
        γf-eq : (x : ⟨ B∞ ⟩) → fst γ (fst f x) ≡ fst φ_α x
        γf-eq x = funExt⁻ (cong fst γf≡φ) x

        -- Key: γ(1,0) ⊕ γ(0,1) = true (from pres+ and (1,0)+(0,1) = (1,1))
        γ-sum : fst γ (BR-B∞.𝟙 , BR-B∞.𝟘) ⊕ fst γ (BR-B∞.𝟘 , BR-B∞.𝟙) ≡ true
        γ-sum =
          sym (Γ.pres+ (BR-B∞.𝟙 , BR-B∞.𝟘) (BR-B∞.𝟘 , BR-B∞.𝟙))
          ∙ cong (fst γ) prod-idem-sum
          ∙ Γ.pres1

        -- If γ(0,1) = false, then γ(0,x) = false for all x
        γ-kills-right : fst γ (BR-B∞.𝟘 , BR-B∞.𝟙) ≡ false →
          (x : ⟨ B∞ ⟩) → fst γ (BR-B∞.𝟘 , x) ≡ false
        γ-kills-right p x =
          fst γ (BR-B∞.𝟘 , x)
            ≡⟨ cong (fst γ) (sym (prod-0x-factor x)) ⟩
          fst γ (BR-prod._·_ (BR-B∞.𝟘 , BR-B∞.𝟙) (BR-B∞.𝟘 , x))
            ≡⟨ Γ.pres· (BR-B∞.𝟘 , BR-B∞.𝟙) (BR-B∞.𝟘 , x) ⟩
          fst γ (BR-B∞.𝟘 , BR-B∞.𝟙) and fst γ (BR-B∞.𝟘 , x)
            ≡⟨ cong (_and fst γ (BR-B∞.𝟘 , x)) p ⟩
          false ∎

        -- If γ(1,0) = false, then γ(x,0) = false for all x
        γ-kills-left : fst γ (BR-B∞.𝟙 , BR-B∞.𝟘) ≡ false →
          (x : ⟨ B∞ ⟩) → fst γ (x , BR-B∞.𝟘) ≡ false
        γ-kills-left p x =
          fst γ (x , BR-B∞.𝟘)
            ≡⟨ cong (fst γ) (sym (prod-x0-factor x)) ⟩
          fst γ (BR-prod._·_ (BR-B∞.𝟙 , BR-B∞.𝟘) (x , BR-B∞.𝟘))
            ≡⟨ Γ.pres· (BR-B∞.𝟙 , BR-B∞.𝟘) (x , BR-B∞.𝟘) ⟩
          fst γ (BR-B∞.𝟙 , BR-B∞.𝟘) and fst γ (x , BR-B∞.𝟘)
            ≡⟨ cong (_and fst γ (x , BR-B∞.𝟘)) p ⟩
          false ∎

        -- α(double k) = γ(f(gB∞(double k))) = γ(0, gB∞ k)
        α-even-eq : (k : ℕ) → α (double k) ≡ fst γ (BR-B∞.𝟘 , gB∞ k)
        α-even-eq k =
          sym (φ_α-eval (double k))
          ∙ sym (γf-eq (gB∞ (double k)))
          ∙ cong (fst γ) (f-eval (double k) ∙ interleave-gen-even k)

        -- α(suc(double k)) = γ(f(gB∞(suc(double k)))) = γ(gB∞ k, 0)
        α-odd-eq : (k : ℕ) → α (suc (double k)) ≡ fst γ (gB∞ k , BR-B∞.𝟘)
        α-odd-eq k =
          sym (φ_α-eval (suc (double k)))
          ∙ sym (γf-eq (gB∞ (suc (double k))))
          ∙ cong (fst γ) (f-eval (suc (double k)) ∙ interleave-gen-odd k)

        -- true ⊕ e = true implies e = false
        xor-true-false : (e : Bool) → true ⊕ e ≡ true → e ≡ false
        xor-true-false false _ = refl
        xor-true-false true p = ex-falso (false≢true p)

        dichotomy : (e : Bool) → e ≡ fst γ (BR-B∞.𝟙 , BR-B∞.𝟘) →
          ∥ ((n : ℕ) → α (double n) ≡ false) ⊎ ((n : ℕ) → α (suc (double n)) ≡ false) ∥₁
        dichotomy true p =
          let γ01≡false : fst γ (BR-B∞.𝟘 , BR-B∞.𝟙) ≡ false
              γ01≡false = xor-true-false _
                (subst (λ x → x ⊕ fst γ (BR-B∞.𝟘 , BR-B∞.𝟙) ≡ true) (sym p) γ-sum)
          in ∣ inl (λ k → α-even-eq k ∙ γ-kills-right γ01≡false (gB∞ k)) ∣₁
        dichotomy false p = ∣ inr (λ k → α-odd-eq k ∙ γ-kills-left (sym p) (gB∞ k)) ∣₁
