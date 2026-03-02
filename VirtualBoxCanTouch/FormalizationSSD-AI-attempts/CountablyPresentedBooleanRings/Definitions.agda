{-# OPTIONS --cubical --guardedness #-}
module CountablyPresentedBooleanRings.Definitions where 

open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso ; rec* to empty-func)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order 
open <-Reasoning
open import Cubical.Data.Nat.Bijections.Sum

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Powerset
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Algebra.BooleanRing

open import Cubical.HITs.PropositionalTruncation as PT

open  import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.FreeBooleanRing.FreeBool as FB

open  import BooleanRing.FreeBooleanRing.SurjectiveTerms
open  import BooleanRing.FreeBooleanRing.freeBATerms

open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
import Cubical.HITs.SetQuotients as SQ
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
open import Cubical.Algebra.CommRing.Ideal
import Cubical.Algebra.CommRing.Kernel as CK
open import Cubical.Algebra.Ring.Kernel as RK
open import Cubical.Algebra.CommRing.Quotient.Base
import Cubical.Algebra.CommRing.Quotient.Base as Quot
open import Cubical.Tactics.CommRingSolver

open import Cubical.Algebra.CommRing.Polynomials.Typevariate.UniversalProperty as UP
open import Cubical.Algebra.CommRing.Polynomials.Typevariate.Base
open import BasicDefinitions
open import CommRingQuotients.EmptyQuotient
open import BooleanRing.BooleanRingMaps

{- I freeA'≃freeA to define what is a countably presented BA before I can define what a Stone space is.
--
-- I think I want it to be a predicate on Boolean rings. If so, the following quotHom be examples:
--
-- BoolBR
-- freeBA ℕ 
-- the Boolean algebra underlying ℕ-infty. 
--
-- So far, I've shown the first two are quotients of freeBA ℕ by some function from ℕ. 
-- This definition carries the benefit that it's of type-level ℓ-zero. 
-- (which should be the case as our work should work independently from universes. 
--} 


_is-presented-by_/_ : {ℓ : Level} → (B : BooleanRing ℓ) → 
  (A : Type ℓ) → {X : Type ℓ} → (f : X → ⟨ freeBA A ⟩) → Type ℓ 
B is-presented-by A / f = BooleanRingEquiv B (freeBA A /Im f)

-- definition 1.3
has-countable-presentation : (B : BooleanRing ℓ-zero) → Type₁ 
has-countable-presentation B = 
   Σ[ A ∈ Type ] ((has-Countability-structure A) × 
  (Σ[ X ∈ Type ] ((has-Countability-structure X) ×
  (Σ[ f ∈ (X → ⟨ freeBA A ⟩) ] 
   B is-presented-by A / f))))

is-countably-presented : (B : BooleanRing ℓ-zero) → Type₁
is-countably-presented B = ∥ has-countable-presentation B ∥₁

has-quotient-of-freeℕ-presentation : (B : BooleanRing ℓ-zero) → Type₀
has-quotient-of-freeℕ-presentation B = Σ[ f ∈ (ℕ → ⟨ freeBA ℕ ⟩) ] B is-presented-by ℕ / f

is-countably-presented-alt : (B : BooleanRing ℓ-zero) → Type₀ 
is-countably-presented-alt B = ∥ has-quotient-of-freeℕ-presentation B ∥₁

countablyPresentedBooleanRing : Type (ℓ-suc ℓ-zero)
countablyPresentedBooleanRing = Σ[ B ∈ BooleanRing ℓ-zero ] (is-countably-presented B)

-- Remark 1.4 can also be in another file. Evertyhing that comes after this line should be put somewhere else at some point.
countℕ : has-Countability-structure ℕ
countℕ .fst _ = true
countℕ .snd .Iso.fun n       = n , refl
countℕ .snd .Iso.inv (n , _) = n
countℕ .snd .Iso.sec b  = Σ≡Prop (λ _ → isSetBool _ _) refl
countℕ .snd .Iso.ret  n  = refl 

has-Boole-ω : (B : BooleanRing ℓ-zero) → Type (ℓ-suc ℓ-zero) 
has-Boole-ω B = Σ[ A ∈ Type ] ( (has-Countability-structure A) × 
              (Σ[ X ∈ Type ] ( (has-Countability-structure X) ×
              (Σ[ f ∈ (X → ⟨ freeBA A ⟩) ] B is-presented-by A /( f)))))

has-Boole-ω' : (B : BooleanRing ℓ-zero) → Type ℓ-zero 
has-Boole-ω' B = Σ[ f ∈ (ℕ → ⟨ freeBA ℕ ⟩) ] (B is-presented-by ℕ / f)

has-Boole'→ : (B : BooleanRing ℓ-zero) → has-Boole-ω' B → has-Boole-ω B
has-Boole'→ B x = ℕ , countℕ , ℕ , countℕ , x


