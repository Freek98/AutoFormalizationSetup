{-# OPTIONS --cubical --guardedness #-}

module DecidableEquality where

{- Freely generated Boolean algebras have decidable equality.

   For a type A with decidable equality, we show Discrete ⟨ freeBA A ⟩,
   via a conjunctive normal form argument:

   * Every element of freeBA A merely has a CNF representative
     (Surjectivity.cnfSurj in NormalForms).
   * A CNF evaluates to 𝟙 iff each of its clauses contains a
     complementary pair of literals (a "tautological" clause).
     This is decidable when A is discrete.
     - If every clause is tautological, the CNF evaluates to 𝟙
       by the algebraic identity x ∨ ¬ x ≡ 𝟙.
     - If some clause has no complementary pair, that clause yields a
       Boolean assignment A → 2 falsifying it; the induced Boolean
       morphism freeBA A → 2 sends the CNF to 0 ≠ 1, so the CNF does
       not evaluate to 𝟙.
   * Finally x ≡ y iff 𝟙 + (x + y) ≡ 𝟙 (characteristic 2), and
     𝟙 + (x + y) is represented by negCNF of a CNF for x + y.

   This is the formal counterpart of the remark in monolithic.tex that
   (in)equality is decidable in the free Boolean algebra 2[I] for I a
   decidable (e.g. countable) set, which underlies the study of
   countably presented Boolean algebras 2[ℕ]/(r_n). -}

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.List.Base
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat using (ℕ ; discreteℕ)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BooleanRing.FreeBooleanRing.FreeBool
open import NormalForms

private
  variable
    ℓ ℓ' ℓa : Level

-- ═══════════════════════════════════════════════════════════════
-- List membership, with decidability
-- ═══════════════════════════════════════════════════════════════

infix 4 _∈ₗ_

data _∈ₗ_ {X : Type ℓ} (x : X) : List X → Type ℓ where
  here  : {y : X} {ys : List X} → x ≡ y → x ∈ₗ (y ∷ ys)
  there : {y : X} {ys : List X} → x ∈ₗ ys → x ∈ₗ (y ∷ ys)

¬∈ₗ[] : {X : Type ℓ} {x : X} → ¬ (x ∈ₗ [])
¬∈ₗ[] ()

∈ₗDec : {X : Type ℓ} → Discrete X → (x : X) (ys : List X) → Dec (x ∈ₗ ys)
∈ₗDec dX x [] = no ¬∈ₗ[]
∈ₗDec dX x (y ∷ ys) with dX x y
... | yes p = yes (here p)
... | no ¬p with ∈ₗDec dX x ys
...   | yes m = yes (there m)
...   | no ¬m = no λ { (here p) → ¬p p ; (there m) → ¬m m }

-- ═══════════════════════════════════════════════════════════════
-- Literals: basic facts
-- ═══════════════════════════════════════════════════════════════

negLitInvol : {A : Type ℓ} (l : Literal A) → negLit (negLit l) ≡ l
negLitInvol (a , b) = cong (a ,_) (notnot b)

lit≢negLit : {A : Type ℓ} (l : Literal A) → ¬ (l ≡ negLit l)
lit≢negLit (a , b) p = not≢const b (sym (cong snd p))

discreteLiteral : {A : Type ℓ} → Discrete A → Discrete (Literal A)
discreteLiteral dA = discreteΣ dA λ _ → _≟_

-- ═══════════════════════════════════════════════════════════════
-- Tautological clauses: clauses containing a complementary pair
-- ═══════════════════════════════════════════════════════════════

Taut : {A : Type ℓ} → List (Literal A) → Type ℓ
Taut {A = A} ls = Σ[ l ∈ Literal A ] (l ∈ₗ ls) × (negLit l ∈ₗ ls)

tautDec : {A : Type ℓ} → Discrete A → (ls : List (Literal A)) → Dec (Taut ls)
tautDec dA [] = no λ t → ¬∈ₗ[] (fst (snd t))
tautDec dA (l ∷ ls) with ∈ₗDec (discreteLiteral dA) (negLit l) ls
... | yes m = yes (l , here refl , there m)
... | no ¬m with tautDec dA ls
...   | yes (l' , p , q) = yes (l' , there p , there q)
...   | no ¬t = no bad
  where
  bad : ¬ Taut (l ∷ ls)
  bad (l' , here p , here q)   = lit≢negLit l' (p ∙ sym q)
  bad (l' , here p , there q)  = ¬m (subst (_∈ₗ ls) (cong negLit p) q)
  bad (l' , there p , here q)  = ¬m (subst (_∈ₗ ls) (sym (negLitInvol l') ∙ cong negLit q) p)
  bad (l' , there p , there q) = ¬t (l' , p , q)

-- Decide whether all clauses of a CNF are tautological,
-- producing a counterexample clause otherwise.
checkAllTaut : {A : Type ℓ} → Discrete A → (d : CNF A) →
  ((c : List (Literal A)) → c ∈ₗ d → Taut c)
  ⊎ (Σ[ c ∈ List (Literal A) ] (c ∈ₗ d) × (¬ Taut c))
checkAllTaut dA [] = inl λ c m → ex-falso (¬∈ₗ[] m)
checkAllTaut dA (c ∷ cs) with tautDec dA c
... | no ¬t = inr (c , here refl , ¬t)
... | yes t with checkAllTaut dA cs
...   | inl all = inl λ { c' (here p) → subst Taut (sym p) t
                        ; c' (there m) → all c' m }
...   | inr (c' , m , ¬t) = inr (c' , there m , ¬t)

-- ═══════════════════════════════════════════════════════════════
-- Clause evaluation facts, over an arbitrary Boolean ring
-- ═══════════════════════════════════════════════════════════════

module ClauseFacts (R : BooleanRing ℓ) where
  open BooleanRingStr (snd R)
  open BooleanAlgebraStr (snd R) renaming (_∨_ to _∨b_ ; _∧_ to _∧b_ ; ¬_ to ¬b_)
  open EvalCorrect R

  module _ {A : Type ℓa} (f : A → ⟨ R ⟩) where

    -- a literal occurring in a clause is absorbed by its disjunction
    evalDisjAbsorb : (l : Literal A) (ls : List (Literal A)) → l ∈ₗ ls →
      evalDisjLits f ls ≡ evalLit f l ∨b evalDisjLits f ls
    evalDisjAbsorb l (y ∷ ys) (here p) = sym (
      evalLit f l ∨b (evalLit f y ∨b evalDisjLits f ys)
        ≡⟨ cong (λ z → evalLit f z ∨b (evalLit f y ∨b evalDisjLits f ys)) p ⟩
      evalLit f y ∨b (evalLit f y ∨b evalDisjLits f ys)
        ≡⟨ ∨Assoc ⟩
      (evalLit f y ∨b evalLit f y) ∨b evalDisjLits f ys
        ≡⟨ cong (_∨b evalDisjLits f ys) ∨Idem ⟩
      evalLit f y ∨b evalDisjLits f ys ∎)
    evalDisjAbsorb l (y ∷ ys) (there m) =
      cong (evalLit f y ∨b_) (evalDisjAbsorb l ys m)
      ∙ ∨Assoc
      ∙ cong (_∨b evalDisjLits f ys) ∨Comm
      ∙ sym ∨Assoc

    -- a clause with a complementary pair evaluates to 𝟙
    tautEval1 : (ls : List (Literal A)) → Taut ls → evalDisjLits f ls ≡ 𝟙
    tautEval1 ls (l , m , n) =
      evalDisjLits f ls
        ≡⟨ evalDisjAbsorb l ls m ⟩
      evalLit f l ∨b evalDisjLits f ls
        ≡⟨ cong (evalLit f l ∨b_) (evalDisjAbsorb (negLit l) ls n) ⟩
      evalLit f l ∨b (evalLit f (negLit l) ∨b evalDisjLits f ls)
        ≡⟨ ∨Assoc ⟩
      (evalLit f l ∨b evalLit f (negLit l)) ∨b evalDisjLits f ls
        ≡⟨ cong (λ z → (evalLit f l ∨b z) ∨b evalDisjLits f ls) (evalLit-neg f l) ⟩
      (evalLit f l ∨b (𝟙 + evalLit f l)) ∨b evalDisjLits f ls
        ≡⟨ cong (_∨b evalDisjLits f ls) (¬Completes∨R {x = evalLit f l}) ⟩
      𝟙 ∨b evalDisjLits f ls
        ≡⟨ 1Absorbs∨L ⟩
      𝟙 ∎

    -- a CNF all of whose clauses are tautological evaluates to 𝟙
    allTautEval1 : (d : CNF A) →
      ((c : List (Literal A)) → c ∈ₗ d → Taut c) → evalCNF f d ≡ 𝟙
    allTautEval1 [] _ = refl
    allTautEval1 (c ∷ cs) all =
      cong₂ _·_ (tautEval1 c (all c (here refl)))
                (allTautEval1 cs (λ c' m → all c' (there m)))
      ∙ ·IdR 𝟙

    -- a CNF with a clause evaluating to 𝟘 evaluates to 𝟘
    deadClauseEval0 : (c : List (Literal A)) (d : CNF A) → c ∈ₗ d →
      evalDisjLits f c ≡ 𝟘 → evalCNF f d ≡ 𝟘
    deadClauseEval0 c (y ∷ ys) (here p) e =
      cong (_· evalCNF f ys) (cong (evalDisjLits f) (sym p) ∙ e) ∙ ∧AnnihilL
    deadClauseEval0 c (y ∷ ys) (there m) e =
      cong (evalDisjLits f y ·_) (deadClauseEval0 c ys m e) ∙ ∧AnnihilR

-- ═══════════════════════════════════════════════════════════════
-- Boolean morphisms commute with CNF evaluation
-- ═══════════════════════════════════════════════════════════════

module EvalHom (R : BooleanRing ℓ) (S : BooleanRing ℓ') (φ : BoolHom R S) where
  private
    module RS = BooleanRingStr (snd R)
    module SS = BooleanRingStr (snd S)
    module R∨ = BooleanAlgebraStr (snd R)
    module S∨ = BooleanAlgebraStr (snd S)
    module ER = EvalCorrect R
    module ES = EvalCorrect S
  open IsCommRingHom (snd φ)

  φ∨ : (x y : ⟨ R ⟩) → fst φ (R∨._∨_ x y) ≡ S∨._∨_ (fst φ x) (fst φ y)
  φ∨ x y =
    pres+ (RS._+_ x y) (RS._·_ x y)
    ∙ cong₂ SS._+_ (pres+ x y) (pres· x y)

  evalLitHom : {A : Type ℓa} (f : A → ⟨ R ⟩) (l : Literal A) →
    fst φ (ER.evalLit f l) ≡ ES.evalLit (fst φ ∘ f) l
  evalLitHom f (a , true)  = refl
  evalLitHom f (a , false) =
    pres+ RS.𝟙 (f a) ∙ cong (λ z → SS._+_ z (fst φ (f a))) pres1

  evalDisjLitsHom : {A : Type ℓa} (f : A → ⟨ R ⟩) (ls : List (Literal A)) →
    fst φ (ER.evalDisjLits f ls) ≡ ES.evalDisjLits (fst φ ∘ f) ls
  evalDisjLitsHom f [] = pres0
  evalDisjLitsHom f (l ∷ ls) =
    φ∨ (ER.evalLit f l) (ER.evalDisjLits f ls)
    ∙ cong₂ S∨._∨_ (evalLitHom f l) (evalDisjLitsHom f ls)

  evalCNFHom : {A : Type ℓa} (f : A → ⟨ R ⟩) (d : CNF A) →
    fst φ (ER.evalCNF f d) ≡ ES.evalCNF (fst φ ∘ f) d
  evalCNFHom f [] = pres1
  evalCNFHom f (c ∷ cs) =
    pres· (ER.evalDisjLits f c) (ER.evalCNF f cs)
    ∙ cong₂ SS._·_ (evalDisjLitsHom f c) (evalCNFHom f cs)

-- ═══════════════════════════════════════════════════════════════
-- A non-tautological clause is falsified by some assignment A → 2
-- ═══════════════════════════════════════════════════════════════

module Falsify {A : Type} (dA : Discrete A)
               (c : List (Literal A)) (¬t : ¬ Taut c) where
  open EvalCorrect BoolBR
  open BooleanAlgebraStr (snd BoolBR) renaming (_∨_ to _∨₂_ ; _∧_ to _∧₂_ ; ¬_ to ¬₂_)

  private
    dL : Discrete (Literal A)
    dL = discreteLiteral dA

  -- set a generator to true exactly when the clause asks it to be false
  badAssign : A → Bool
  badAssign a = Dec→Bool (∈ₗDec dL (a , false) c)

  litFalse : (l : Literal A) → l ∈ₗ c → evalLit badAssign l ≡ false
  litFalse (a , true) m = helper (∈ₗDec dL (a , false) c) refl
    where
    helper : (w : Dec ((a , false) ∈ₗ c)) →
             ∈ₗDec dL (a , false) c ≡ w → evalLit badAssign (a , true) ≡ false
    helper (yes n) _ = ex-falso (¬t ((a , true) , m , n))
    helper (no _)  e = cong Dec→Bool e
  litFalse (a , false) m = helper (∈ₗDec dL (a , false) c) refl
    where
    helper : (w : Dec ((a , false) ∈ₗ c)) →
             ∈ₗDec dL (a , false) c ≡ w → evalLit badAssign (a , false) ≡ false
    helper (yes n) e = cong (λ w' → not (Dec→Bool w')) e
    helper (no ¬n) _ = ex-falso (¬n m)

  allFalseDisj : (ls : List (Literal A)) →
    ((l : Literal A) → l ∈ₗ ls → evalLit badAssign l ≡ false) →
    evalDisjLits badAssign ls ≡ false
  allFalseDisj [] h = refl
  allFalseDisj (l ∷ ls) h =
    cong₂ _∨₂_ (h l (here refl)) (allFalseDisj ls (λ l' m → h l' (there m)))

  clauseDead : evalDisjLits badAssign c ≡ false
  clauseDead = allFalseDisj c litFalse

  killCNF : (d : CNF A) → c ∈ₗ d → evalCNF badAssign d ≡ false
  killCNF d m = ClauseFacts.deadClauseEval0 BoolBR badAssign c d m clauseDead

-- ═══════════════════════════════════════════════════════════════
-- Decidable equality of the free Boolean algebra
-- ═══════════════════════════════════════════════════════════════

module FreeBADecidableEquality {A : Type} (dA : Discrete A) where
  open Surjectivity {A = A}
  open EvalCorrect (freeBA A)
  open BooleanRingStr (snd (freeBA A))
  open BooleanAlgebraStr (snd (freeBA A)) using (characteristic2)

  private
    module CF = ClauseFacts (freeBA A)
    module EB = EvalCorrect BoolBR

  -- being 𝟙 is decidable for evaluated CNFs
  decTop : (d : CNF A) → Dec (evalCNF generator d ≡ 𝟙)
  decTop d with checkAllTaut dA d
  ... | inl all = yes (CF.allTautEval1 generator d all)
  ... | inr (c , m , ¬t) = no λ e → true≢false (
        true
          ≡⟨ sym (IsCommRingHom.pres1 (snd φ)) ⟩
        fst φ 𝟙
          ≡⟨ cong (fst φ) (sym e) ⟩
        fst φ (evalCNF generator d)
          ≡⟨ EH.evalCNFHom generator d ⟩
        EB.evalCNF (fst φ ∘ generator) d
          ≡⟨ cong (λ g → EB.evalCNF g d) (evalBAInduce A BoolBR F.badAssign) ⟩
        EB.evalCNF F.badAssign d
          ≡⟨ F.killCNF d m ⟩
        false ∎)
    where
    module F = Falsify dA c ¬t

    φ : BoolHom (freeBA A) BoolBR
    φ = inducedBAHom A BoolBR F.badAssign

    module EH = EvalHom (freeBA A) BoolBR φ

  discreteFreeBA : Discrete ⟨ freeBA A ⟩
  discreteFreeBA x y = PT.rec (isPropDec (is-set x y)) dec (cnfSurj (x + y))
    where
    dec : hasCNF (x + y) → Dec (x ≡ y)
    dec (c , p) with decTop (negCNF c)
    ... | yes e = yes (
          x
            ≡⟨ sym (+IdR x) ⟩
          x + 𝟘
            ≡⟨ cong (x +_) (sym (characteristic2 {x = y})) ⟩
          x + (y + y)
            ≡⟨ +Assoc x y y ⟩
          (x + y) + y
            ≡⟨ cong (_+ y) diff ⟩
          𝟘 + y
            ≡⟨ +IdL y ⟩
          y ∎)
      where
      step : 𝟙 + (x + y) ≡ 𝟙
      step = cong (𝟙 +_) (sym p) ∙ sym (negCNF-correct generator c) ∙ e

      diff : x + y ≡ 𝟘
      diff =
        sym (+IdL (x + y))
        ∙ cong (_+ (x + y)) (sym (characteristic2 {x = 𝟙}))
        ∙ sym (+Assoc 𝟙 𝟙 (x + y))
        ∙ cong (𝟙 +_) step
        ∙ characteristic2 {x = 𝟙}
    ... | no ne = no λ q → ne (
          negCNF-correct generator c
          ∙ cong (𝟙 +_) (p ∙ cong (_+ y) q ∙ characteristic2 {x = y})
          ∙ +IdR 𝟙)

-- The headline results

discreteFreeBA : {A : Type} → Discrete A → Discrete ⟨ freeBA A ⟩
discreteFreeBA dA = FreeBADecidableEquality.discreteFreeBA dA

-- in particular 2[ℕ], the Boolean algebra underlying Cantor space
discreteFreeBAℕ : Discrete ⟨ freeBA ℕ ⟩
discreteFreeBAℕ = discreteFreeBA discreteℕ
