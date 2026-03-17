{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module NxNDiagCount where

open import Countability.Properties

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (≡ᵇ→≡ ; ≡→≡ᵇ ; discreteℕ)
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Bool.Properties using (isSetBool ; false≢true ; true≢false ;
  ¬false→true)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥
open import Cubical.Data.Unit

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import BasicDefinitions

open Iso

-- ════════════════════════════════════════════════════════════════
-- Bool→Type ↔ ≡ true bridge lemmas
-- ════════════════════════════════════════════════════════════════

-- Bool→Type b is inhabited iff b ≡ true
Bool→Type→≡true : (b : Bool) → Bool→Type b → b ≡ true
Bool→Type→≡true true  _ = refl
Bool→Type→≡true false ()

≡true→Bool→Type : (b : Bool) → b ≡ true → Bool→Type b
≡true→Bool→Type true  _ = tt
≡true→Bool→Type false p = ⊥.rec (false≢true p)

-- not lemmas
not-false→orig-true : (b : Bool) → not b ≡ false → b ≡ true
not-false→orig-true true  _ = refl
not-false→orig-true false p = ⊥.rec (true≢false p)

orig-true→not-false : (b : Bool) → b ≡ true → not b ≡ false
orig-true→not-false true  _ = refl
orig-true→not-false false p = ⊥.rec (false≢true p)

-- ════════════════════════════════════════════════════════════════
-- ≡ᵇ ↔ ≡ via ≡ true (not Bool→Type)
-- ════════════════════════════════════════════════════════════════

≡ᵇ-true→≡ : (n m : ℕ) → (n ≡ᵇ m) ≡ true → n ≡ m
≡ᵇ-true→≡ n m p = ≡ᵇ→≡ (≡true→Bool→Type (n ≡ᵇ m) p)

≡→≡ᵇ-true : (n m : ℕ) → n ≡ m → (n ≡ᵇ m) ≡ true
≡→≡ᵇ-true n m p = Bool→Type→≡true (n ≡ᵇ m) (≡→≡ᵇ p)

-- ════════════════════════════════════════════════════════════════
-- The diagonal complement: Σ[ (n,m) ∈ ℕ×ℕ ] n ≢ m
-- ════════════════════════════════════════════════════════════════

ℕ×ℕ-Diag = Σ[ p ∈ ℕ × ℕ ] ((fst p ≡ snd p) → ⊥)

P : ℕ × ℕ → Bool
P (n , m) = not (n ≡ᵇ m)

ℕ×ℕ-Diag≃ΣℕP : Iso ℕ×ℕ-Diag (Σ[ p ∈ (ℕ × ℕ) ] P p ≡ true)
ℕ×ℕ-Diag≃ΣℕP .fun ((n , m) , n≢m) =
  (n , m) , ¬false→true (not (n ≡ᵇ m)) λ not-eq-false →
    n≢m (≡ᵇ-true→≡ n m (not-false→orig-true (n ≡ᵇ m) not-eq-false))
ℕ×ℕ-Diag≃ΣℕP .inv ((n , m) , Pnm=t) =
  (n , m) , λ n=m → true≢false (sym Pnm=t ∙ orig-true→not-false (n ≡ᵇ m) (≡→≡ᵇ-true n m n=m))
ℕ×ℕ-Diag≃ΣℕP .sec _ = Σ≡Prop (λ _ → isSetBool _ _) refl
ℕ×ℕ-Diag≃ΣℕP .ret _ = Σ≡Prop (λ _ → isPropΠ λ _ → isProp⊥) refl

-- Reproduce ℕcount and ℕ×ℕCount here (Countability.Instances has holes)
ℕcount : has-Countability-structure ℕ
ℕcount .fst _ = true
ℕcount .snd .fun n = n , refl
ℕcount .snd .inv (n , _) =  n
ℕcount .snd .sec (n , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
ℕcount .snd .ret n = refl

ℕ×ℕCount : has-Countability-structure (ℕ × ℕ)
ℕ×ℕCount = has-Countability-structure-× ℕcount ℕcount

ℕ×ℕ-Diag-Count : has-Countability-structure ℕ×ℕ-Diag
ℕ×ℕ-Diag-Count =
  has-Countability-structure-Iso
    (has-Countability-structure-Σ-Bool P ℕ×ℕCount)
    (invIso ℕ×ℕ-Diag≃ΣℕP)
