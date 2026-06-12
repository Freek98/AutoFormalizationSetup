{-# OPTIONS --cubical --guardedness #-}

module CountableCover where

{- Freely generated Boolean algebras have a cover by a countable set.

   For A with a countability structure, the type CNF A of conjunctive
   normal forms over A is itself countable, and evaluation of CNFs at
   the generators is surjective onto freeBA A (cnfSurj in NormalForms).
   Hence CNF A is a countable cover of the free Boolean algebra, in the
   sense of hasCountableCover in OvertlyDiscrete/endgoal.agda.

   The countability of CNF A = List (List (A × Bool)) reduces to:
   * List A ≅ Σ[ n ∈ ℕ ] pow A n, counting lists by their length;
   * pow A n (the n-fold product) is countable by induction on n,
     using closure of countability under binary products
     (Countability.Properties.has-Countability-structure-×);
   * a ℕ-indexed family of countable sets has countable total space
     (ΣℕCount below, the dependent version of CountableProduct). -}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Unit
open import Cubical.Data.List.Base
import Cubical.Data.Empty as ⊥

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import Cubical.Functions.Surjection

open import BasicDefinitions
open import Countability.Properties

open import BooleanRing.FreeBooleanRing.FreeBool
open import NormalForms

open Iso

private
  variable
    ℓ : Level

-- ═══════════════════════════════════════════════════════════════
-- Basic countability instances
-- (re-derived here: Countability.Instances still contains holes)
-- ═══════════════════════════════════════════════════════════════

ℕcount : has-Countability-structure ℕ
ℕcount = (λ _ → true) , isoℕ
  where
  isoℕ : Iso ℕ (Σℕ (λ _ → true))
  fun isoℕ n = n , refl
  inv isoℕ = fst
  sec isoℕ (n , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
  ret isoℕ _ = refl

unitCount : has-Countability-structure Unit
unitCount = δSequence 0 , isoUnit
  where
  isoUnit : Iso Unit (Σℕ (δSequence 0))
  fun isoUnit _ = 0 , refl
  inv isoUnit _ = tt
  sec isoUnit (zero , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
  sec isoUnit (suc n , p) = ⊥.rec (false≢true p)
  ret isoUnit _ = refl

boolCount : has-Countability-structure Bool
boolCount =
  has-Countability-structure-Iso
    (has-Countability-structure-⊎ unitCount unitCount)
    (invIso Bool≅Unit⊎Unit)
  where
  Bool≅Unit⊎Unit : Iso Bool (Unit ⊎ Unit)
  fun Bool≅Unit⊎Unit false = inl tt
  fun Bool≅Unit⊎Unit true  = inr tt
  inv Bool≅Unit⊎Unit (inl _) = false
  inv Bool≅Unit⊎Unit (inr _) = true
  sec Bool≅Unit⊎Unit (inl _) = refl
  sec Bool≅Unit⊎Unit (inr _) = refl
  ret Bool≅Unit⊎Unit false = refl
  ret Bool≅Unit⊎Unit true  = refl

-- ═══════════════════════════════════════════════════════════════
-- A countable family of countable sets has countable total space
-- (dependent version of CountableProduct in Countability.Properties)
-- ═══════════════════════════════════════════════════════════════

module CountableFamily (γ : ℕ → binarySequence) where

  γΣ : binarySequence
  γΣ k = γ (fst (inv ℕ×ℕ≅ℕ k)) (snd (inv ℕ×ℕ≅ℕ k))

  ΣℕFam : Iso (Σ[ n ∈ ℕ ] Σℕ (γ n)) (Σℕ γΣ)
  fun ΣℕFam (n , m , p) = fun ℕ×ℕ≅ℕ (n , m) , proof
    where
    eq : inv ℕ×ℕ≅ℕ (fun ℕ×ℕ≅ℕ (n , m)) ≡ (n , m)
    eq = ret ℕ×ℕ≅ℕ (n , m)

    proof : γΣ (fun ℕ×ℕ≅ℕ (n , m)) ≡ true
    proof = cong₂ (λ x y → γ x y) (cong fst eq) (cong snd eq) ∙ p
  inv ΣℕFam (k , r) = fst (inv ℕ×ℕ≅ℕ k) , snd (inv ℕ×ℕ≅ℕ k) , r
  sec ΣℕFam (k , r) = ΣPathP (sec ℕ×ℕ≅ℕ k , toPathP (isSetBool _ _ _ _))
  ret ΣℕFam (n , m , p) =
    ΣPathP (cong fst eq , ΣPathP (cong snd eq , toPathP (isSetBool _ _ _ _)))
    where
    eq : inv ℕ×ℕ≅ℕ (fun ℕ×ℕ≅ℕ (n , m)) ≡ (n , m)
    eq = ret ℕ×ℕ≅ℕ (n , m)

ΣℕCount : {B : ℕ → Type} →
  ((n : ℕ) → has-Countability-structure (B n)) →
  has-Countability-structure (Σ[ n ∈ ℕ ] B n)
ΣℕCount {B} c = γΣ , compIso (Σ-cong-iso-snd (λ n → snd (c n))) ΣℕFam
  where open CountableFamily (λ n → fst (c n))

-- ═══════════════════════════════════════════════════════════════
-- Lists of a countable set form a countable set
-- ═══════════════════════════════════════════════════════════════

-- n-fold product
pow : Type → ℕ → Type
pow A zero    = Unit
pow A (suc n) = A × pow A n

powCount : {A : Type} → has-Countability-structure A →
  (n : ℕ) → has-Countability-structure (pow A n)
powCount cA zero    = unitCount
powCount cA (suc n) = has-Countability-structure-× cA (powCount cA n)

module _ {A : Type} where

  listToPow : List A → Σ[ n ∈ ℕ ] pow A n
  listToPow []      = 0 , tt
  listToPow (a ∷ l) = suc (fst (listToPow l)) , a , snd (listToPow l)

  powToList : (Σ[ n ∈ ℕ ] pow A n) → List A
  powToList (zero  , _)     = []
  powToList (suc n , a , v) = a ∷ powToList (n , v)

  powListSec : (x : Σ[ n ∈ ℕ ] pow A n) → listToPow (powToList x) ≡ x
  powListSec (zero  , _)     = refl
  powListSec (suc n , a , v) =
    cong (λ w → suc (fst w) , a , snd w) (powListSec (n , v))

  listPowRet : (l : List A) → powToList (listToPow l) ≡ l
  listPowRet []      = refl
  listPowRet (a ∷ l) = cong (a ∷_) (listPowRet l)

  List≅Σpow : Iso (List A) (Σ[ n ∈ ℕ ] pow A n)
  fun List≅Σpow = listToPow
  inv List≅Σpow = powToList
  sec List≅Σpow = powListSec
  ret List≅Σpow = listPowRet

listCount : {A : Type} → has-Countability-structure A →
  has-Countability-structure (List A)
listCount cA =
  has-Countability-structure-Iso (ΣℕCount (powCount cA)) (invIso List≅Σpow)

-- ═══════════════════════════════════════════════════════════════
-- The free Boolean algebra on a countable set has a countable cover
-- ═══════════════════════════════════════════════════════════════

-- as in OvertlyDiscrete/endgoal.agda
hasCountableCover : Type ℓ → Type (ℓ-suc ℓ)
hasCountableCover {ℓ} X = Σ[ B ∈ Type ℓ ] has-Countability-structure B × (B ↠ X)

module _ {A : Type} (cA : has-Countability-structure A) where
  open Surjectivity {A = A}
  open EvalCorrect (freeBA A)

  literalCount : has-Countability-structure (Literal A)
  literalCount = has-Countability-structure-× cA boolCount

  cnfCount : has-Countability-structure (CNF A)
  cnfCount = listCount (listCount literalCount)

  freeBACountableCover : hasCountableCover ⟨ freeBA A ⟩
  freeBACountableCover = CNF A , cnfCount , (evalCNF generator , cnfSurj)

-- in particular for 2[ℕ], the Boolean algebra underlying Cantor space
freeBAℕCountableCover : hasCountableCover ⟨ freeBA ℕ ⟩
freeBAℕCountableCover = freeBACountableCover ℕcount
