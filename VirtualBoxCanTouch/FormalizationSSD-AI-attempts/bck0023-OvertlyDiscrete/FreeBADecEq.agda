{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OvertlyDiscrete.FreeBADecEq where

-- Decidable equality for term-level elements of freeBA ℕ.
-- Strategy: project to freeBA(Fin n) for suitable n, check there.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (_≤_; ≤-refl; left-≤-max; right-≤-max; ≤-trans; _<_)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using ()

open import Cubical.Relation.Nullary using (Dec; yes; no; ¬_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing

open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.FreeBooleanRing.freeBATerms
open import BooleanRing.FreeBooleanRing.SurjectiveTerms

open import Cubical.Data.Nat.Properties using (discreteℕ)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool) renaming (_≟_ to discreteBool)

open Iso
open BooleanRingStr

-- ════════════════════════════════════════════════════════════════
-- Decidable equality for freeBATerms ℕ
-- ════════════════════════════════════════════════════════════════

-- freeBATerms is an inductive type with constructors:
-- Tvar ℕ, Tconst Bool, _+T_, -T_, _·T_
-- Since ℕ and Bool have decidable equality, and all constructors
-- are injective, freeBATerms ℕ has decidable equality.

freeBATerms-DecEq : (t s : freeBATerms ℕ) → Dec (t ≡ s)
freeBATerms-DecEq (Tvar m) (Tvar n) with discreteℕ m n
... | yes p = yes (cong Tvar p)
... | no ¬p = no (λ q → ¬p (cong (λ { (Tvar x) → x ; _ → 0 }) q))
freeBATerms-DecEq (Tvar _) (Tconst _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tvar _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tvar _) (_ +T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tvar _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tvar _) (-T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tvar _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tvar _) (_ ·T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tvar _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tconst _) (Tvar _) = no (λ p → ⊥.rec (subst distinguish p false))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tconst _) = Bool ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tconst a) (Tconst b) with discreteBool a b
... | yes p = yes (cong Tconst p)
... | no ¬p = no (λ q → ¬p (cong (λ { (Tconst x) → x ; _ → false }) q))
freeBATerms-DecEq (Tconst _) (_ +T _) = no (λ p → ⊥.rec (subst distinguish p false))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tconst _) = Bool ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tconst _) (-T _) = no (λ p → ⊥.rec (subst distinguish p false))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tconst _) = Bool ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (Tconst _) (_ ·T _) = no (λ p → ⊥.rec (subst distinguish p false))
  where distinguish : freeBATerms ℕ → Type ; distinguish (Tconst _) = Bool ; distinguish _ = ⊥.⊥
-- For compound terms, we recurse
freeBATerms-DecEq (t₁ +T t₂) (s₁ +T s₂) with freeBATerms-DecEq t₁ s₁ | freeBATerms-DecEq t₂ s₂
... | yes p | yes q = yes (cong₂ _+T_ p q)
... | no ¬p | _     = no (λ r → ¬p (cong (λ { (a +T _) → a ; x → x }) r))
... | _     | no ¬q = no (λ r → ¬q (cong (λ { (_ +T b) → b ; x → x }) r))
freeBATerms-DecEq (_ +T _) (Tvar _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ +T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (_ +T _) (Tconst _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ +T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (_ +T _) (-T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ +T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (_ +T _) (_ ·T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ +T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (-T t) (-T s) with freeBATerms-DecEq t s
... | yes p = yes (cong -T_ p)
... | no ¬p = no (λ r → ¬p (cong (λ { (-T x) → x ; x → x }) r))
freeBATerms-DecEq (-T _) (Tvar _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (-T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (-T _) (Tconst _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (-T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (-T _) (_ +T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (-T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (-T _) (_ ·T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (-T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (t₁ ·T t₂) (s₁ ·T s₂) with freeBATerms-DecEq t₁ s₁ | freeBATerms-DecEq t₂ s₂
... | yes p | yes q = yes (cong₂ _·T_ p q)
... | no ¬p | _     = no (λ r → ¬p (cong (λ { (a ·T _) → a ; x → x }) r))
... | _     | no ¬q = no (λ r → ¬q (cong (λ { (_ ·T b) → b ; x → x }) r))
freeBATerms-DecEq (_ ·T _) (Tvar _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ ·T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (_ ·T _) (Tconst _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ ·T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (_ ·T _) (_ +T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ ·T _) = ℕ ; distinguish _ = ⊥.⊥
freeBATerms-DecEq (_ ·T _) (-T _) = no (λ p → ⊥.rec (subst distinguish p 0))
  where distinguish : freeBATerms ℕ → Type ; distinguish (_ ·T _) = ℕ ; distinguish _ = ⊥.⊥

-- ════════════════════════════════════════════════════════════════
-- Infrastructure from test-boole-odisc (ι, π, maxGen, ιπ-on-term)
-- ════════════════════════════════════════════════════════════════

maxGen : freeBATerms ℕ → ℕ
maxGen (Tvar n) = suc n
maxGen (Tconst _) = zero
maxGen (t +T s) = max (maxGen t) (maxGen s)
maxGen (-T t) = maxGen t
maxGen (t ·T s) = max (maxGen t) (maxGen s)

open import Cubical.Data.Nat.Order using (<Dec)
open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ)

π-on-gen : (m : ℕ) → ℕ → ⟨ freeBA (Fin m) ⟩
π-on-gen m k with <Dec k m
... | yes p = generator (k , <→<ᵗ p)
... | no _  = 𝟘 (snd (freeBA (Fin m)))

π : (m : ℕ) → BoolHom (freeBA ℕ) (freeBA (Fin m))
π m = inducedBAHom ℕ (freeBA (Fin m)) (π-on-gen m)

ι : (m : ℕ) → BoolHom (freeBA (Fin m)) (freeBA ℕ)
ι m = inducedBAHom (Fin m) (freeBA ℕ) (generator ∘ fst)

ιπ-on-gen : (m k : ℕ) → (p : k < m) →
  fst (ι m) (fst (π m) (generator k)) ≡ generator k
ιπ-on-gen m k p =
  cong (fst (ι m)) (funExt⁻ (evalBAInduce ℕ (freeBA (Fin m)) (π-on-gen m)) k)
  ∙ ιπ-helper
  where
  ιπ-helper : fst (ι m) (π-on-gen m k) ≡ generator k
  ιπ-helper with <Dec k m
  ... | yes q = funExt⁻ (evalBAInduce (Fin m) (freeBA ℕ) (generator ∘ fst)) (k , <→<ᵗ q)
  ... | no ¬q = ⊥.rec (¬q p)

opaque
  unfolding includeBATermsSurj
  unfolding generator
  ιπ-on-term : (t : freeBATerms ℕ) → (m : ℕ) → maxGen t ≤ m →
    fst (ι m) (fst (π m) (fst includeBATermsSurj t)) ≡ fst includeBATermsSurj t
  ιπ-on-term (Tvar k) m p = ιπ-on-gen m k p
  ιπ-on-term (Tconst false) m p =
    cong (fst (ι m)) (IsCommRingHom.pres0 (snd (π m)))
    ∙ IsCommRingHom.pres0 (snd (ι m))
  ιπ-on-term (Tconst true) m p =
    cong (fst (ι m)) (IsCommRingHom.pres1 (snd (π m)))
    ∙ IsCommRingHom.pres1 (snd (ι m))
  ιπ-on-term (t₁ +T t₂) m p =
    let surj = fst includeBATermsSurj in
    cong (fst (ι m)) (IsCommRingHom.pres+ (snd (π m)) (surj t₁) (surj t₂))
    ∙ IsCommRingHom.pres+ (snd (ι m)) (fst (π m) (surj t₁)) (fst (π m) (surj t₂))
    ∙ cong₂ (_+_ (snd (freeBA ℕ)))
        (ιπ-on-term t₁ m (≤-trans (left-≤-max {maxGen t₁} {maxGen t₂}) p))
        (ιπ-on-term t₂ m (≤-trans (right-≤-max {maxGen t₂} {maxGen t₁}) p))
  ιπ-on-term (-T t) m p =
    let surj = fst includeBATermsSurj in
    cong (fst (ι m)) (IsCommRingHom.pres- (snd (π m)) (surj t))
    ∙ IsCommRingHom.pres- (snd (ι m)) (fst (π m) (surj t))
    ∙ cong (-_ (snd (freeBA ℕ))) (ιπ-on-term t m p)
  ιπ-on-term (t₁ ·T t₂) m p =
    let surj = fst includeBATermsSurj in
    cong (fst (ι m)) (IsCommRingHom.pres· (snd (π m)) (surj t₁) (surj t₂))
    ∙ IsCommRingHom.pres· (snd (ι m)) (fst (π m) (surj t₁)) (fst (π m) (surj t₂))
    ∙ cong₂ (_·_ (snd (freeBA ℕ)))
        (ιπ-on-term t₁ m (≤-trans (left-≤-max {maxGen t₁} {maxGen t₂}) p))
        (ιπ-on-term t₂ m (≤-trans (right-≤-max {maxGen t₂} {maxGen t₁}) p))

-- ════════════════════════════════════════════════════════════════
-- Decidable equality in freeBA(Fin n)
-- ════════════════════════════════════════════════════════════════

-- freeBA(Fin n) is a finite Boolean algebra (2^(2^n) elements).
-- Its elements are determined by their truth tables on (Fin n → Bool).
-- Since the truth table is a function from a finite set to Bool,
-- equality of truth tables is decidable, giving decidable equality.
--
-- A full proof requires showing the evaluation map
--   freeBA(Fin n) → ((Fin n → Bool) → Bool)
-- is injective (separation by Boolean points), which follows from
-- the DNF representation (every element has a canonical DNF form
-- that determines it uniquely).

postulate
  freeBA-Fin-DecEq : (n : ℕ) → (x y : ⟨ freeBA (Fin n) ⟩) → Dec (x ≡ y)

-- ════════════════════════════════════════════════════════════════
-- Decidable equality for term-level elements of freeBA ℕ
-- ════════════════════════════════════════════════════════════════

-- For terms t, s: project to freeBA(Fin m) where m = max(maxGen t, maxGen s).
-- By ιπ-on-term, the projection reflects equality back.

private
  eval : freeBATerms ℕ → ⟨ freeBA ℕ ⟩
  eval = fst includeBATermsSurj

freeBA-term-DecEq : (t s : freeBATerms ℕ) → Dec (eval t ≡ eval s)
freeBA-term-DecEq t s with freeBA-Fin-DecEq m (fst (π m) (eval t)) (fst (π m) (eval s))
  where m = max (maxGen t) (maxGen s)
... | yes πt=πs = yes (
    sym (ιπ-on-term t m (≤-trans left-≤-max ≤-refl))
    ∙ cong (fst (ι m)) πt=πs
    ∙ ιπ-on-term s m (≤-trans right-≤-max ≤-refl))
  where m = max (maxGen t) (maxGen s)
... | no ¬πt=πs = no (λ p → ¬πt=πs (cong (fst (π m)) p))
  where m = max (maxGen t) (maxGen s)
