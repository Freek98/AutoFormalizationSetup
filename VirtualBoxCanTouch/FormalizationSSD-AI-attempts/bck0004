{-# OPTIONS --cubical --guardedness #-}

module work where

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.List using (List; []; _∷_; _++_; map)
open import Cubical.Data.Bool using (Bool; true; false; not; isSetBool; true≢false; false≢true; _⊕_; _and_; if_then_else_)
open import Cubical.Data.Nat using (ℕ; zero; suc; discreteℕ)
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Functions.Surjection using (isSurjection; compSurjection)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce)
open import BooleanRing.FreeBooleanRing.freeBATerms using (includeBATermsSurj; freeBATerms)
open import BooleanRing.FreeBooleanRing.SurjectiveTerms using (Tvar; Tconst; _+T_; -T_; _·T_)

-- Convert builtin equality (from `with ... in eq`) to cubical Path
import Agda.Builtin.Equality as BEq
builtin→Path-Bool : {a b : Bool} → a BEq.≡ b → a ≡ b
builtin→Path-Bool BEq.refl = refl

-- ═══════════════════════════════════════════════════════════════
-- Part 1: General CNF/DNF Data Types for Free Boolean Algebras
-- ═══════════════════════════════════════════════════════════════

-- A literal: (generator index, is-positive?)
-- (n , true) represents generator n
-- (n , false) represents ¬(generator n)
Literal : Type₀
Literal = ℕ × Bool

-- A clause is a list of literals
Clause : Type₀
Clause = List Literal

-- DNF: disjunction (∨) of conjunction (∧) clauses
DNF : Type₀
DNF = List Clause

-- CNF: conjunction (∧) of disjunction (∨) clauses
CNF : Type₀
CNF = List Clause

-- ═══════════════════════════════════════════════════════════════
-- Part 2: Evaluation of CNF/DNF in any Boolean Ring
-- ═══════════════════════════════════════════════════════════════

module EvalNF (B : BooleanRing ℓ-zero) (gen : ℕ → ⟨ B ⟩) where
  private
    module BA = BooleanAlgebraStr B
    module BR = BooleanRingStr (snd B)

  _∧B_ : ⟨ B ⟩ → ⟨ B ⟩ → ⟨ B ⟩
  _∧B_ = BR._·_

  _∨B_ : ⟨ B ⟩ → ⟨ B ⟩ → ⟨ B ⟩
  _∨B_ = BA._∨_

  ¬B_ : ⟨ B ⟩ → ⟨ B ⟩
  ¬B_ = BA.¬_

  𝟘B : ⟨ B ⟩
  𝟘B = BR.𝟘

  𝟙B : ⟨ B ⟩
  𝟙B = BR.𝟙

  evalLit : Literal → ⟨ B ⟩
  evalLit (n , true)  = gen n
  evalLit (n , false) = ¬B (gen n)

  negateLit : Literal → Literal
  negateLit (n , b) = (n , not b)

  evalConjClause : Clause → ⟨ B ⟩
  evalConjClause [] = 𝟙B
  evalConjClause (l ∷ ls) = evalLit l ∧B evalConjClause ls

  evalDisjClause : Clause → ⟨ B ⟩
  evalDisjClause [] = 𝟘B
  evalDisjClause (l ∷ ls) = evalLit l ∨B evalDisjClause ls

  evalDNF : DNF → ⟨ B ⟩
  evalDNF [] = 𝟘B
  evalDNF (c ∷ cs) = evalConjClause c ∨B evalDNF cs

  evalCNF : CNF → ⟨ B ⟩
  evalCNF [] = 𝟙B
  evalCNF (c ∷ cs) = evalDisjClause c ∧B evalCNF cs

-- ═══════════════════════════════════════════════════════════════
-- Part 3: Boolean Expression Intermediate Representation
-- ═══════════════════════════════════════════════════════════════

data BoolExpr : Type₀ where
  BLit   : Literal → BoolExpr
  BTrue  : BoolExpr
  BFalse : BoolExpr
  BAnd   : BoolExpr → BoolExpr → BoolExpr
  BOr    : BoolExpr → BoolExpr → BoolExpr
  BNot   : BoolExpr → BoolExpr

module EvalBoolExpr (B : BooleanRing ℓ-zero) (gen : ℕ → ⟨ B ⟩) where
  open EvalNF B gen

  evalBE : BoolExpr → ⟨ B ⟩
  evalBE (BLit l) = evalLit l
  evalBE BTrue = 𝟙B
  evalBE BFalse = 𝟘B
  evalBE (BAnd a b) = evalBE a ∧B evalBE b
  evalBE (BOr a b) = evalBE a ∨B evalBE b
  evalBE (BNot a) = ¬B (evalBE a)

-- ═══════════════════════════════════════════════════════════════
-- Part 4: Conversion from freeBATerms to BoolExpr
-- ═══════════════════════════════════════════════════════════════

-- In a boolean ring: + is XOR, · is AND, - is identity
-- XOR(a,b) = (a ∧ ¬b) ∨ (¬a ∧ b)
termToBoolExpr : freeBATerms ℕ → BoolExpr
termToBoolExpr (Tvar n) = BLit (n , true)
termToBoolExpr (Tconst false) = BFalse
termToBoolExpr (Tconst true) = BTrue
termToBoolExpr (-T t) = termToBoolExpr t
termToBoolExpr (t ·T s) = BAnd (termToBoolExpr t) (termToBoolExpr s)
termToBoolExpr (t +T s) =
  let t' = termToBoolExpr t
      s' = termToBoolExpr s
  in BOr (BAnd t' (BNot s')) (BAnd (BNot t') s')

-- ═══════════════════════════════════════════════════════════════
-- Part 5: Negation Normal Form (NNF) Conversion
-- ═══════════════════════════════════════════════════════════════

toNNF : BoolExpr → BoolExpr
toNNFneg : BoolExpr → BoolExpr

toNNF (BLit l) = BLit l
toNNF BTrue = BTrue
toNNF BFalse = BFalse
toNNF (BAnd a b) = BAnd (toNNF a) (toNNF b)
toNNF (BOr a b) = BOr (toNNF a) (toNNF b)
toNNF (BNot a) = toNNFneg a

toNNFneg (BLit (n , b)) = BLit (n , not b)
toNNFneg BTrue = BFalse
toNNFneg BFalse = BTrue
toNNFneg (BAnd a b) = BOr (toNNFneg a) (toNNFneg b)
toNNFneg (BOr a b) = BAnd (toNNFneg a) (toNNFneg b)
toNNFneg (BNot a) = toNNF a

-- ═══════════════════════════════════════════════════════════════
-- Part 6: NNF to DNF Conversion
-- ═══════════════════════════════════════════════════════════════

singletonDNF : Literal → DNF
singletonDNF l = (l ∷ []) ∷ []

trueDNF : DNF
trueDNF = [] ∷ []

falseDNF : DNF
falseDNF = []

orDNF : DNF → DNF → DNF
orDNF = _++_

andDNF : DNF → DNF → DNF
andDNF [] _ = []
andDNF (_ ∷ _) [] = []
andDNF (c₁ ∷ cs₁) cs₂ = map (c₁ ++_) cs₂ ++ andDNF cs₁ cs₂

nnfToDNF : BoolExpr → DNF
nnfToDNFneg : BoolExpr → DNF

nnfToDNF (BLit l) = singletonDNF l
nnfToDNF BTrue = trueDNF
nnfToDNF BFalse = falseDNF
nnfToDNF (BAnd a b) = andDNF (nnfToDNF a) (nnfToDNF b)
nnfToDNF (BOr a b) = orDNF (nnfToDNF a) (nnfToDNF b)
nnfToDNF (BNot a) = nnfToDNFneg a

nnfToDNFneg (BLit (n , b)) = singletonDNF (n , not b)
nnfToDNFneg BTrue = falseDNF
nnfToDNFneg BFalse = trueDNF
nnfToDNFneg (BAnd a b) = orDNF (nnfToDNFneg a) (nnfToDNFneg b)
nnfToDNFneg (BOr a b) = andDNF (nnfToDNFneg a) (nnfToDNFneg b)
nnfToDNFneg (BNot a) = nnfToDNF a

-- ═══════════════════════════════════════════════════════════════
-- Part 7: NNF to CNF Conversion
-- ═══════════════════════════════════════════════════════════════

singletonCNF : Literal → CNF
singletonCNF l = (l ∷ []) ∷ []

trueCNF : CNF
trueCNF = []

falseCNF : CNF
falseCNF = [] ∷ []

andCNF : CNF → CNF → CNF
andCNF = _++_

orCNF : CNF → CNF → CNF
orCNF [] _ = []
orCNF (_ ∷ _) [] = []
orCNF (c₁ ∷ cs₁) cs₂ = map (c₁ ++_) cs₂ ++ orCNF cs₁ cs₂

nnfToCNF : BoolExpr → CNF
nnfToCNFneg : BoolExpr → CNF

nnfToCNF (BLit l) = singletonCNF l
nnfToCNF BTrue = trueCNF
nnfToCNF BFalse = falseCNF
nnfToCNF (BAnd a b) = andCNF (nnfToCNF a) (nnfToCNF b)
nnfToCNF (BOr a b) = orCNF (nnfToCNF a) (nnfToCNF b)
nnfToCNF (BNot a) = nnfToCNFneg a

nnfToCNFneg (BLit (n , b)) = singletonCNF (n , not b)
nnfToCNFneg BTrue = falseCNF
nnfToCNFneg BFalse = trueCNF
nnfToCNFneg (BAnd a b) = orCNF (nnfToCNFneg a) (nnfToCNFneg b)
nnfToCNFneg (BOr a b) = andCNF (nnfToCNFneg a) (nnfToCNFneg b)
nnfToCNFneg (BNot a) = nnfToCNF a

-- ═══════════════════════════════════════════════════════════════
-- Part 8: Full Pipeline: freeBATerms → DNF / CNF
-- ═══════════════════════════════════════════════════════════════

termToDNF : freeBATerms ℕ → DNF
termToDNF t = nnfToDNF (toNNF (termToBoolExpr t))

termToCNF : freeBATerms ℕ → CNF
termToCNF t = nnfToCNF (toNNF (termToBoolExpr t))

-- ═══════════════════════════════════════════════════════════════
-- Part 9: Correctness Proofs
-- ═══════════════════════════════════════════════════════════════

module Correctness (B : BooleanRing ℓ-zero) (gen : ℕ → ⟨ B ⟩) where
  open EvalNF B gen
  open EvalBoolExpr B gen

  private
    module BA = BooleanAlgebraStr B
    module BR = BooleanRingStr (snd B)
    module RT where
      open import Cubical.Algebra.Ring.Properties using (module RingTheory)
      open RingTheory (CommRing→Ring (BooleanRing→CommRing B)) public

  isSetB : isSet ⟨ B ⟩
  isSetB = BR.is-set

  -- Useful shorthands for identities
  0-absorbs-left : (x : ⟨ B ⟩) → 𝟘B ∧B x ≡ 𝟘B
  0-absorbs-left = RT.0LeftAnnihilates

  0-absorbs-right : (x : ⟨ B ⟩) → x ∧B 𝟘B ≡ 𝟘B
  0-absorbs-right = RT.0RightAnnihilates

  -- ═══ xor-as-bool: a + b = (a ∧ ¬b) ∨ (¬a ∧ b) ═══
  xor-as-bool : (a b : ⟨ B ⟩) → BR._+_ a b ≡ (a ∧B (¬B b)) ∨B ((¬B a) ∧B b)
  xor-as-bool a b = sym rhs≡lhs
    where
      ab  = a ∧B b
      a¬b = a ∧B (¬B b)
      ¬ab = (¬B a) ∧B b

      -- Cross product (a·¬b)·(¬a·b) = 0 by rearranging to (a·¬a)·... = 0
      cross-zero : a¬b ∧B ¬ab ≡ 𝟘B
      cross-zero =
        a¬b ∧B ¬ab
          ≡⟨ BR.·Assoc a¬b (¬B a) b ⟩
        (a¬b ∧B (¬B a)) ∧B b
          ≡⟨ cong (_∧B b) (sym (BR.·Assoc a (¬B b) (¬B a))) ⟩
        (a ∧B ((¬B b) ∧B (¬B a))) ∧B b
          ≡⟨ cong (λ z → (a ∧B z) ∧B b) (BR.·Comm (¬B b) (¬B a)) ⟩
        (a ∧B ((¬B a) ∧B (¬B b))) ∧B b
          ≡⟨ cong (_∧B b) (BR.·Assoc a (¬B a) (¬B b)) ⟩
        ((a ∧B (¬B a)) ∧B (¬B b)) ∧B b
          ≡⟨ cong (λ z → (z ∧B (¬B b)) ∧B b) BA.¬Cancels∧R ⟩
        (𝟘B ∧B (¬B b)) ∧B b
          ≡⟨ cong (_∧B b) (0-absorbs-left (¬B b)) ⟩
        𝟘B ∧B b
          ≡⟨ 0-absorbs-left b ⟩
        𝟘B ∎

      -- a·(1+b) = a + ab
      expand-a¬b : a¬b ≡ BR._+_ a ab
      expand-a¬b =
        a ∧B (¬B b)
          ≡⟨ BR.·DistR+ a 𝟙B b ⟩
        BR._+_ (a ∧B 𝟙B) ab
          ≡⟨ cong (λ z → BR._+_ z ab) (BR.·IdR a) ⟩
        BR._+_ a ab ∎

      -- (1+a)·b = b + ab
      expand-¬ab : ¬ab ≡ BR._+_ b ab
      expand-¬ab =
        (¬B a) ∧B b
          ≡⟨ BR.·DistL+ 𝟙B a b ⟩
        BR._+_ (𝟙B ∧B b) ab
          ≡⟨ cong (λ z → BR._+_ z ab) (BR.·IdL b) ⟩
        BR._+_ b ab ∎

      -- (a + ab) + (b + ab) = a + b  via reassociation and char 2
      sum-simplify : BR._+_ (BR._+_ a ab) (BR._+_ b ab) ≡ BR._+_ a b
      sum-simplify =
        BR._+_ (BR._+_ a ab) (BR._+_ b ab)
          ≡⟨ BR.+Assoc (BR._+_ a ab) b ab ⟩
        BR._+_ (BR._+_ (BR._+_ a ab) b) ab
          ≡⟨ cong (λ z → BR._+_ z ab) (sym (BR.+Assoc a ab b)) ⟩
        BR._+_ (BR._+_ a (BR._+_ ab b)) ab
          ≡⟨ cong (λ z → BR._+_ (BR._+_ a z) ab) (BR.+Comm ab b) ⟩
        BR._+_ (BR._+_ a (BR._+_ b ab)) ab
          ≡⟨ cong (λ z → BR._+_ z ab) (BR.+Assoc a b ab) ⟩
        BR._+_ (BR._+_ (BR._+_ a b) ab) ab
          ≡⟨ sym (BR.+Assoc (BR._+_ a b) ab ab) ⟩
        BR._+_ (BR._+_ a b) (BR._+_ ab ab)
          ≡⟨ cong (BR._+_ (BR._+_ a b)) BA.characteristic2 ⟩
        BR._+_ (BR._+_ a b) 𝟘B
          ≡⟨ BR.+IdR (BR._+_ a b) ⟩
        BR._+_ a b ∎

      -- Main chain: RHS → LHS
      rhs≡lhs : a¬b ∨B ¬ab ≡ BR._+_ a b
      rhs≡lhs =
        a¬b ∨B ¬ab
          ≡⟨ cong (BR._+_ (BR._+_ a¬b ¬ab)) cross-zero ⟩
        BR._+_ (BR._+_ a¬b ¬ab) 𝟘B
          ≡⟨ BR.+IdR (BR._+_ a¬b ¬ab) ⟩
        BR._+_ a¬b ¬ab
          ≡⟨ cong₂ BR._+_ expand-a¬b expand-¬ab ⟩
        BR._+_ (BR._+_ a ab) (BR._+_ b ab)
          ≡⟨ sum-simplify ⟩
        BR._+_ a b ∎

  negateLit-correct : (l : Literal) → evalLit (negateLit l) ≡ ¬B (evalLit l)
  negateLit-correct (n , true) = refl
  negateLit-correct (n , false) = sym BA.¬Invol

  -- Interpretation of freeBATerms in B
  interpretInB : freeBATerms ℕ → ⟨ B ⟩
  interpretInB (Tvar n) = gen n
  interpretInB (Tconst false) = 𝟘B
  interpretInB (Tconst true) = 𝟙B
  interpretInB (t +T s) = BR._+_ (interpretInB t) (interpretInB s)
  interpretInB (-T t) = interpretInB t
  interpretInB (t ·T s) = (interpretInB t) ∧B (interpretInB s)

  -- termToBoolExpr preserves semantics
  termToBoolExpr-correct : (t : freeBATerms ℕ) → evalBE (termToBoolExpr t) ≡ interpretInB t
  termToBoolExpr-correct (Tvar n) = refl
  termToBoolExpr-correct (Tconst false) = refl
  termToBoolExpr-correct (Tconst true) = refl
  termToBoolExpr-correct (-T t) = termToBoolExpr-correct t
  termToBoolExpr-correct (t ·T s) =
    cong₂ _∧B_ (termToBoolExpr-correct t) (termToBoolExpr-correct s)
  termToBoolExpr-correct (t +T s) =
    let t' = termToBoolExpr t ; s' = termToBoolExpr s
        tv = interpretInB t ; sv = interpretInB s
    in
    evalBE (BOr (BAnd t' (BNot s')) (BAnd (BNot t') s'))
      ≡⟨ cong₂ _∨B_ (cong₂ _∧B_ (termToBoolExpr-correct t) (cong ¬B_ (termToBoolExpr-correct s)))
                      (cong₂ _∧B_ (cong ¬B_ (termToBoolExpr-correct t)) (termToBoolExpr-correct s)) ⟩
    (tv ∧B (¬B sv)) ∨B ((¬B tv) ∧B sv)
      ≡⟨ sym (xor-as-bool tv sv) ⟩
    BR._+_ tv sv ∎

  -- toNNF / toNNFneg preserve semantics
  toNNF-correct : (e : BoolExpr) → evalBE (toNNF e) ≡ evalBE e
  toNNFneg-correct : (e : BoolExpr) → evalBE (toNNFneg e) ≡ ¬B (evalBE e)

  toNNF-correct (BLit l) = refl
  toNNF-correct BTrue = refl
  toNNF-correct BFalse = refl
  toNNF-correct (BAnd a b) = cong₂ _∧B_ (toNNF-correct a) (toNNF-correct b)
  toNNF-correct (BOr a b) = cong₂ _∨B_ (toNNF-correct a) (toNNF-correct b)
  toNNF-correct (BNot a) = toNNFneg-correct a

  toNNFneg-correct (BLit (n , true)) = refl
  toNNFneg-correct (BLit (n , false)) = sym BA.¬Invol
  toNNFneg-correct BTrue = sym BA.¬1≡0
  toNNFneg-correct BFalse = sym (BR.+IdR 𝟙B)
  toNNFneg-correct (BAnd a b) =
    evalBE (BOr (toNNFneg a) (toNNFneg b))
      ≡⟨ cong₂ _∨B_ (toNNFneg-correct a) (toNNFneg-correct b) ⟩
    (¬B evalBE a) ∨B (¬B evalBE b)
      ≡⟨ sym BA.DeMorgan¬∧ ⟩
    ¬B (evalBE a ∧B evalBE b) ∎
  toNNFneg-correct (BOr a b) =
    evalBE (BAnd (toNNFneg a) (toNNFneg b))
      ≡⟨ cong₂ _∧B_ (toNNFneg-correct a) (toNNFneg-correct b) ⟩
    (¬B evalBE a) ∧B (¬B evalBE b)
      ≡⟨ sym BA.DeMorgan¬∨ ⟩
    ¬B (evalBE a ∨B evalBE b) ∎
  toNNFneg-correct (BNot a) =
    evalBE (toNNF a)
      ≡⟨ toNNF-correct a ⟩
    evalBE a
      ≡⟨ sym BA.¬Invol ⟩
    ¬B (¬B evalBE a) ∎

  -- ═══ DNF correctness infrastructure ═══

  evalConjClause-++ : (c₁ c₂ : Clause) →
    evalConjClause (c₁ ++ c₂) ≡ evalConjClause c₁ ∧B evalConjClause c₂
  evalConjClause-++ [] c₂ = sym (BR.·IdL (evalConjClause c₂))
  evalConjClause-++ (l ∷ ls) c₂ =
    evalLit l ∧B evalConjClause (ls ++ c₂)
      ≡⟨ cong (evalLit l ∧B_) (evalConjClause-++ ls c₂) ⟩
    evalLit l ∧B (evalConjClause ls ∧B evalConjClause c₂)
      ≡⟨ BR.·Assoc (evalLit l) (evalConjClause ls) (evalConjClause c₂) ⟩
    (evalLit l ∧B evalConjClause ls) ∧B evalConjClause c₂ ∎

  evalDisjClause-++ : (c₁ c₂ : Clause) →
    evalDisjClause (c₁ ++ c₂) ≡ evalDisjClause c₁ ∨B evalDisjClause c₂
  evalDisjClause-++ [] c₂ = sym BA.∨IdL
  evalDisjClause-++ (l ∷ ls) c₂ =
    evalLit l ∨B evalDisjClause (ls ++ c₂)
      ≡⟨ cong (evalLit l ∨B_) (evalDisjClause-++ ls c₂) ⟩
    evalLit l ∨B (evalDisjClause ls ∨B evalDisjClause c₂)
      ≡⟨ BA.∨Assoc ⟩
    (evalLit l ∨B evalDisjClause ls) ∨B evalDisjClause c₂ ∎

  evalDNF-++ : (d₁ d₂ : DNF) →
    evalDNF (d₁ ++ d₂) ≡ evalDNF d₁ ∨B evalDNF d₂
  evalDNF-++ [] d₂ = sym BA.∨IdL
  evalDNF-++ (c ∷ cs) d₂ =
    evalConjClause c ∨B evalDNF (cs ++ d₂)
      ≡⟨ cong (evalConjClause c ∨B_) (evalDNF-++ cs d₂) ⟩
    evalConjClause c ∨B (evalDNF cs ∨B evalDNF d₂)
      ≡⟨ BA.∨Assoc ⟩
    (evalConjClause c ∨B evalDNF cs) ∨B evalDNF d₂ ∎

  evalDNF-map-prepend : (c₁ : Clause) (d₂ : DNF) →
    evalDNF (map (c₁ ++_) d₂) ≡ evalConjClause c₁ ∧B evalDNF d₂
  evalDNF-map-prepend c₁ [] = sym (0-absorbs-right (evalConjClause c₁))
  evalDNF-map-prepend c₁ (c₂ ∷ cs₂) =
    evalConjClause (c₁ ++ c₂) ∨B evalDNF (map (c₁ ++_) cs₂)
      ≡⟨ cong₂ _∨B_ (evalConjClause-++ c₁ c₂) (evalDNF-map-prepend c₁ cs₂) ⟩
    (evalConjClause c₁ ∧B evalConjClause c₂) ∨B (evalConjClause c₁ ∧B evalDNF cs₂)
      ≡⟨ sym BA.∧DistR∨ ⟩
    evalConjClause c₁ ∧B (evalConjClause c₂ ∨B evalDNF cs₂) ∎

  andDNF-correct : (d₁ d₂ : DNF) →
    evalDNF (andDNF d₁ d₂) ≡ evalDNF d₁ ∧B evalDNF d₂
  andDNF-correct [] d₂ = sym (0-absorbs-left (evalDNF d₂))
  andDNF-correct (c₁ ∷ cs₁) [] = sym (0-absorbs-right (evalConjClause c₁ ∨B evalDNF cs₁))
  andDNF-correct (c₁ ∷ cs₁) (c₂ ∷ cs₂) =
    evalDNF (map (c₁ ++_) (c₂ ∷ cs₂) ++ andDNF cs₁ (c₂ ∷ cs₂))
      ≡⟨ evalDNF-++ (map (c₁ ++_) (c₂ ∷ cs₂)) (andDNF cs₁ (c₂ ∷ cs₂)) ⟩
    evalDNF (map (c₁ ++_) (c₂ ∷ cs₂)) ∨B evalDNF (andDNF cs₁ (c₂ ∷ cs₂))
      ≡⟨ cong₂ _∨B_ (evalDNF-map-prepend c₁ (c₂ ∷ cs₂)) (andDNF-correct cs₁ (c₂ ∷ cs₂)) ⟩
    (evalConjClause c₁ ∧B evalDNF (c₂ ∷ cs₂)) ∨B (evalDNF cs₁ ∧B evalDNF (c₂ ∷ cs₂))
      ≡⟨ sym BA.∧DistL∨ ⟩
    (evalConjClause c₁ ∨B evalDNF cs₁) ∧B evalDNF (c₂ ∷ cs₂) ∎

  singletonDNF-eval : (l : Literal) → evalDNF (singletonDNF l) ≡ evalLit l
  singletonDNF-eval l =
    (evalLit l ∧B 𝟙B) ∨B 𝟘B
      ≡⟨ BA.∨IdR ⟩
    evalLit l ∧B 𝟙B
      ≡⟨ BR.·IdR (evalLit l) ⟩
    evalLit l ∎

  nnfToDNF-correct : (e : BoolExpr) → evalDNF (nnfToDNF e) ≡ evalBE e
  nnfToDNFneg-correct : (e : BoolExpr) → evalDNF (nnfToDNFneg e) ≡ ¬B (evalBE e)

  nnfToDNF-correct (BLit l) = singletonDNF-eval l
  nnfToDNF-correct BTrue =
    𝟙B ∨B 𝟘B
      ≡⟨ BA.∨IdR ⟩
    𝟙B ∎
  nnfToDNF-correct BFalse = refl
  nnfToDNF-correct (BAnd a b) =
    evalDNF (andDNF (nnfToDNF a) (nnfToDNF b))
      ≡⟨ andDNF-correct (nnfToDNF a) (nnfToDNF b) ⟩
    evalDNF (nnfToDNF a) ∧B evalDNF (nnfToDNF b)
      ≡⟨ cong₂ _∧B_ (nnfToDNF-correct a) (nnfToDNF-correct b) ⟩
    evalBE a ∧B evalBE b ∎
  nnfToDNF-correct (BOr a b) =
    evalDNF (nnfToDNF a ++ nnfToDNF b)
      ≡⟨ evalDNF-++ (nnfToDNF a) (nnfToDNF b) ⟩
    evalDNF (nnfToDNF a) ∨B evalDNF (nnfToDNF b)
      ≡⟨ cong₂ _∨B_ (nnfToDNF-correct a) (nnfToDNF-correct b) ⟩
    evalBE a ∨B evalBE b ∎
  nnfToDNF-correct (BNot a) = nnfToDNFneg-correct a

  nnfToDNFneg-correct (BLit (n , true)) =
    singletonDNF-eval (n , false)
  nnfToDNFneg-correct (BLit (n , false)) =
    evalDNF (singletonDNF (n , true))
      ≡⟨ singletonDNF-eval (n , true) ⟩
    gen n
      ≡⟨ sym BA.¬Invol ⟩
    ¬B (¬B (gen n)) ∎
  nnfToDNFneg-correct BTrue = sym BA.¬1≡0
  nnfToDNFneg-correct BFalse =
    𝟙B ∨B 𝟘B
      ≡⟨ BA.∨IdR ⟩
    𝟙B
      ≡⟨ sym (BR.+IdR 𝟙B) ⟩
    ¬B 𝟘B ∎
  nnfToDNFneg-correct (BAnd a b) =
    evalDNF (nnfToDNFneg a ++ nnfToDNFneg b)
      ≡⟨ evalDNF-++ (nnfToDNFneg a) (nnfToDNFneg b) ⟩
    evalDNF (nnfToDNFneg a) ∨B evalDNF (nnfToDNFneg b)
      ≡⟨ cong₂ _∨B_ (nnfToDNFneg-correct a) (nnfToDNFneg-correct b) ⟩
    (¬B (evalBE a)) ∨B (¬B (evalBE b))
      ≡⟨ sym BA.DeMorgan¬∧ ⟩
    ¬B (evalBE a ∧B evalBE b) ∎
  nnfToDNFneg-correct (BOr a b) =
    evalDNF (andDNF (nnfToDNFneg a) (nnfToDNFneg b))
      ≡⟨ andDNF-correct (nnfToDNFneg a) (nnfToDNFneg b) ⟩
    evalDNF (nnfToDNFneg a) ∧B evalDNF (nnfToDNFneg b)
      ≡⟨ cong₂ _∧B_ (nnfToDNFneg-correct a) (nnfToDNFneg-correct b) ⟩
    (¬B (evalBE a)) ∧B (¬B (evalBE b))
      ≡⟨ sym BA.DeMorgan¬∨ ⟩
    ¬B (evalBE a ∨B evalBE b) ∎
  nnfToDNFneg-correct (BNot a) =
    evalDNF (nnfToDNF a)
      ≡⟨ nnfToDNF-correct a ⟩
    evalBE a
      ≡⟨ sym BA.¬Invol ⟩
    ¬B (¬B (evalBE a)) ∎

  -- ═══ CNF correctness infrastructure ═══

  evalCNF-++ : (c₁ c₂ : CNF) →
    evalCNF (c₁ ++ c₂) ≡ evalCNF c₁ ∧B evalCNF c₂
  evalCNF-++ [] c₂ = sym (BR.·IdL (evalCNF c₂))
  evalCNF-++ (c ∷ cs) c₂ =
    evalDisjClause c ∧B evalCNF (cs ++ c₂)
      ≡⟨ cong (evalDisjClause c ∧B_) (evalCNF-++ cs c₂) ⟩
    evalDisjClause c ∧B (evalCNF cs ∧B evalCNF c₂)
      ≡⟨ BR.·Assoc (evalDisjClause c) (evalCNF cs) (evalCNF c₂) ⟩
    (evalDisjClause c ∧B evalCNF cs) ∧B evalCNF c₂ ∎

  evalCNF-map-prepend : (c₁ : Clause) (cnf₂ : CNF) →
    evalCNF (map (c₁ ++_) cnf₂) ≡ evalDisjClause c₁ ∨B evalCNF cnf₂
  evalCNF-map-prepend c₁ [] = sym BA.1Absorbs∨R
  evalCNF-map-prepend c₁ (c₂ ∷ cs₂) =
    evalDisjClause (c₁ ++ c₂) ∧B evalCNF (map (c₁ ++_) cs₂)
      ≡⟨ cong₂ _∧B_ (evalDisjClause-++ c₁ c₂) (evalCNF-map-prepend c₁ cs₂) ⟩
    (evalDisjClause c₁ ∨B evalDisjClause c₂) ∧B (evalDisjClause c₁ ∨B evalCNF cs₂)
      ≡⟨ sym BA.∨DistR∧ ⟩
    evalDisjClause c₁ ∨B (evalDisjClause c₂ ∧B evalCNF cs₂) ∎

  orCNF-correct : (cnf₁ cnf₂ : CNF) →
    evalCNF (orCNF cnf₁ cnf₂) ≡ evalCNF cnf₁ ∨B evalCNF cnf₂
  orCNF-correct [] cnf₂ = sym BA.1Absorbs∨L
  orCNF-correct (c₁ ∷ cs₁) [] = sym BA.1Absorbs∨R
  orCNF-correct (c₁ ∷ cs₁) (c₂ ∷ cs₂) =
    evalCNF (map (c₁ ++_) (c₂ ∷ cs₂) ++ orCNF cs₁ (c₂ ∷ cs₂))
      ≡⟨ evalCNF-++ (map (c₁ ++_) (c₂ ∷ cs₂)) (orCNF cs₁ (c₂ ∷ cs₂)) ⟩
    evalCNF (map (c₁ ++_) (c₂ ∷ cs₂)) ∧B evalCNF (orCNF cs₁ (c₂ ∷ cs₂))
      ≡⟨ cong₂ _∧B_ (evalCNF-map-prepend c₁ (c₂ ∷ cs₂)) (orCNF-correct cs₁ (c₂ ∷ cs₂)) ⟩
    (evalDisjClause c₁ ∨B evalCNF (c₂ ∷ cs₂)) ∧B (evalCNF cs₁ ∨B evalCNF (c₂ ∷ cs₂))
      ≡⟨ sym BA.∨Distr∧R ⟩
    (evalDisjClause c₁ ∧B evalCNF cs₁) ∨B evalCNF (c₂ ∷ cs₂) ∎

  singletonCNF-eval : (l : Literal) → evalCNF (singletonCNF l) ≡ evalLit l
  singletonCNF-eval l =
    (evalLit l ∨B 𝟘B) ∧B 𝟙B
      ≡⟨ BR.·IdR _ ⟩
    evalLit l ∨B 𝟘B
      ≡⟨ BA.∨IdR ⟩
    evalLit l ∎

  nnfToCNF-correct : (e : BoolExpr) → evalCNF (nnfToCNF e) ≡ evalBE e
  nnfToCNFneg-correct : (e : BoolExpr) → evalCNF (nnfToCNFneg e) ≡ ¬B (evalBE e)

  nnfToCNF-correct (BLit l) = singletonCNF-eval l
  nnfToCNF-correct BTrue = refl
  nnfToCNF-correct BFalse =
    𝟘B ∧B 𝟙B
      ≡⟨ 0-absorbs-left 𝟙B ⟩
    𝟘B ∎
  nnfToCNF-correct (BAnd a b) =
    evalCNF (nnfToCNF a ++ nnfToCNF b)
      ≡⟨ evalCNF-++ (nnfToCNF a) (nnfToCNF b) ⟩
    evalCNF (nnfToCNF a) ∧B evalCNF (nnfToCNF b)
      ≡⟨ cong₂ _∧B_ (nnfToCNF-correct a) (nnfToCNF-correct b) ⟩
    evalBE a ∧B evalBE b ∎
  nnfToCNF-correct (BOr a b) =
    evalCNF (orCNF (nnfToCNF a) (nnfToCNF b))
      ≡⟨ orCNF-correct (nnfToCNF a) (nnfToCNF b) ⟩
    evalCNF (nnfToCNF a) ∨B evalCNF (nnfToCNF b)
      ≡⟨ cong₂ _∨B_ (nnfToCNF-correct a) (nnfToCNF-correct b) ⟩
    evalBE a ∨B evalBE b ∎
  nnfToCNF-correct (BNot a) = nnfToCNFneg-correct a

  nnfToCNFneg-correct (BLit (n , true)) =
    singletonCNF-eval (n , false)
  nnfToCNFneg-correct (BLit (n , false)) =
    evalCNF (singletonCNF (n , true))
      ≡⟨ singletonCNF-eval (n , true) ⟩
    gen n
      ≡⟨ sym BA.¬Invol ⟩
    ¬B (¬B (gen n)) ∎
  nnfToCNFneg-correct BTrue =
    𝟘B ∧B 𝟙B
      ≡⟨ 0-absorbs-left 𝟙B ⟩
    𝟘B
      ≡⟨ sym BA.¬1≡0 ⟩
    ¬B 𝟙B ∎
  nnfToCNFneg-correct BFalse = sym (BR.+IdR 𝟙B)
  nnfToCNFneg-correct (BAnd a b) =
    evalCNF (orCNF (nnfToCNFneg a) (nnfToCNFneg b))
      ≡⟨ orCNF-correct (nnfToCNFneg a) (nnfToCNFneg b) ⟩
    evalCNF (nnfToCNFneg a) ∨B evalCNF (nnfToCNFneg b)
      ≡⟨ cong₂ _∨B_ (nnfToCNFneg-correct a) (nnfToCNFneg-correct b) ⟩
    (¬B (evalBE a)) ∨B (¬B (evalBE b))
      ≡⟨ sym BA.DeMorgan¬∧ ⟩
    ¬B (evalBE a ∧B evalBE b) ∎
  nnfToCNFneg-correct (BOr a b) =
    evalCNF (nnfToCNFneg a ++ nnfToCNFneg b)
      ≡⟨ evalCNF-++ (nnfToCNFneg a) (nnfToCNFneg b) ⟩
    evalCNF (nnfToCNFneg a) ∧B evalCNF (nnfToCNFneg b)
      ≡⟨ cong₂ _∧B_ (nnfToCNFneg-correct a) (nnfToCNFneg-correct b) ⟩
    (¬B (evalBE a)) ∧B (¬B (evalBE b))
      ≡⟨ sym BA.DeMorgan¬∨ ⟩
    ¬B (evalBE a ∨B evalBE b) ∎
  nnfToCNFneg-correct (BNot a) =
    evalCNF (nnfToCNF a)
      ≡⟨ nnfToCNF-correct a ⟩
    evalBE a
      ≡⟨ sym BA.¬Invol ⟩
    ¬B (¬B (evalBE a)) ∎

  -- ═══ Full pipeline correctness ═══

  termToDNF-correct : (t : freeBATerms ℕ) → evalDNF (termToDNF t) ≡ interpretInB t
  termToDNF-correct t =
    evalDNF (nnfToDNF (toNNF (termToBoolExpr t)))
      ≡⟨ nnfToDNF-correct (toNNF (termToBoolExpr t)) ⟩
    evalBE (toNNF (termToBoolExpr t))
      ≡⟨ toNNF-correct (termToBoolExpr t) ⟩
    evalBE (termToBoolExpr t)
      ≡⟨ termToBoolExpr-correct t ⟩
    interpretInB t ∎

  termToCNF-correct : (t : freeBATerms ℕ) → evalCNF (termToCNF t) ≡ interpretInB t
  termToCNF-correct t =
    evalCNF (nnfToCNF (toNNF (termToBoolExpr t)))
      ≡⟨ nnfToCNF-correct (toNNF (termToBoolExpr t)) ⟩
    evalBE (toNNF (termToBoolExpr t))
      ≡⟨ toNNF-correct (termToBoolExpr t) ⟩
    evalBE (termToBoolExpr t)
      ≡⟨ termToBoolExpr-correct t ⟩
    interpretInB t ∎

-- ═══════════════════════════════════════════════════════════════
-- Part 10: Surjectivity — Every element has a DNF/CNF
-- ═══════════════════════════════════════════════════════════════

module Surjectivity (B : BooleanRing ℓ-zero) (gen : ℕ → ⟨ B ⟩)
  (terms-surj : isSurjection (λ (t : freeBATerms ℕ) → Correctness.interpretInB B gen t))
  where
  open Correctness B gen
  open EvalNF B gen

  dnfExists : (x : ⟨ B ⟩) → ∥ Σ[ d ∈ DNF ] evalDNF d ≡ x ∥₁
  dnfExists x = PT.map
    (λ { (t , eq) → termToDNF t , termToDNF-correct t ∙ eq })
    (terms-surj x)

  cnfExists : (x : ⟨ B ⟩) → ∥ Σ[ c ∈ CNF ] evalCNF c ≡ x ∥₁
  cnfExists x = PT.map
    (λ { (t , eq) → termToCNF t , termToCNF-correct t ∙ eq })
    (terms-surj x)

-- ═══════════════════════════════════════════════════════════════
-- Part 11: Helper Functions
-- ═══════════════════════════════════════════════════════════════

-- Check if a clause contains only positive literals
allPositive : Clause → Bool
allPositive [] = true
allPositive ((_ , true)  ∷ ls) = allPositive ls
allPositive ((_ , false) ∷ ls) = false

-- Check if a clause contains only negative literals
allNegative : Clause → Bool
allNegative [] = true
allNegative ((_ , false) ∷ ls) = allNegative ls
allNegative ((_ , true)  ∷ ls) = false

-- Extract generator indices from a clause (discarding polarity)
generatorIndices : Clause → List ℕ
generatorIndices [] = []
generatorIndices ((n , _) ∷ ls) = n ∷ generatorIndices ls

-- A DNF where every clause has all positive literals = disjunction of conjunctions of generators
-- A CNF where every clause has all negative literals = conjunction of disjunctions of negated generators

-- For the NFinCofin application:
-- In B∞ (where distinct generators are orthogonal), the simplified form is either:
-- (a) joinForm: finJoin of generators (all-positive single-literal clauses in DNF)
-- (b) meetNegForm: finMeet of negated generators (all-negative single-literal clauses in CNF)

-- Convert a list of naturals to a clause of positive literals
positiveLiterals : List ℕ → Clause
positiveLiterals [] = []
positiveLiterals (n ∷ ns) = (n , true) ∷ positiveLiterals ns

-- Convert a list of naturals to a clause of negative literals
negativeLiterals : List ℕ → Clause
negativeLiterals [] = []
negativeLiterals (n ∷ ns) = (n , false) ∷ negativeLiterals ns

-- A "simple DNF" is a single clause of positive literals
-- Evaluates to: g_n₁ ∧ g_n₂ ∧ ... ∧ g_nₖ
-- In B∞ with orthogonal generators: this is 𝟘 unless the clause has ≤ 1 literal

-- A "join form DNF" has each clause being a single positive literal
-- i.e., ((n₁,true) ∷ []) ∷ ((n₂,true) ∷ []) ∷ ... ∷ []
-- Evaluates to: g_n₁ ∨ g_n₂ ∨ ... ∨ g_nₖ
joinFormDNF : List ℕ → DNF
joinFormDNF [] = []
joinFormDNF (n ∷ ns) = ((n , true) ∷ []) ∷ joinFormDNF ns

-- A "meet-neg form CNF" has each clause being a single negative literal
-- i.e., ((n₁,false) ∷ []) ∷ ((n₂,false) ∷ []) ∷ ... ∷ []
-- Evaluates to: ¬g_n₁ ∧ ¬g_n₂ ∧ ... ∧ ¬g_nₖ
meetNegFormCNF : List ℕ → CNF
meetNegFormCNF [] = []
meetNegFormCNF (n ∷ ns) = ((n , false) ∷ []) ∷ meetNegFormCNF ns

-- Evaluation lemmas for join/meet forms
module JoinMeetEval (B : BooleanRing ℓ-zero) (gen : ℕ → ⟨ B ⟩) where
  open EvalNF B gen
  private
    module BA = BooleanAlgebraStr B
    module BR = BooleanRingStr (snd B)

  evalDNF-joinForm : (ns : List ℕ) →
    evalDNF (joinFormDNF ns) ≡ evalDisjClause (positiveLiterals ns)
  evalDNF-joinForm [] = refl
  evalDNF-joinForm (n ∷ ns) =
    (gen n ∧B 𝟙B) ∨B evalDNF (joinFormDNF ns)
      ≡⟨ cong (_∨B evalDNF (joinFormDNF ns)) (BR.·IdR (gen n)) ⟩
    gen n ∨B evalDNF (joinFormDNF ns)
      ≡⟨ cong (gen n ∨B_) (evalDNF-joinForm ns) ⟩
    gen n ∨B evalDisjClause (positiveLiterals ns) ∎

  evalCNF-meetNegForm : (ns : List ℕ) →
    evalCNF (meetNegFormCNF ns) ≡ evalConjClause (negativeLiterals ns)
  evalCNF-meetNegForm [] = refl
  evalCNF-meetNegForm (n ∷ ns) =
    ((¬B gen n) ∨B 𝟘B) ∧B evalCNF (meetNegFormCNF ns)
      ≡⟨ cong (_∧B evalCNF (meetNegFormCNF ns)) BA.∨IdR ⟩
    (¬B gen n) ∧B evalCNF (meetNegFormCNF ns)
      ≡⟨ cong ((¬B gen n) ∧B_) (evalCNF-meetNegForm ns) ⟩
    (¬B gen n) ∧B evalConjClause (negativeLiterals ns) ∎

-- ═══════════════════════════════════════════════════════════════
-- Part 12: Orthogonal Generators — B∞-specific simplification
-- ═══════════════════════════════════════════════════════════════

-- In B∞ (or any boolean ring with orthogonal generators),
-- CNF/DNF clauses simplify dramatically.
-- This module provides the key lemmas.

module OrthogonalGens
  (B : BooleanRing ℓ-zero)
  (gen : ℕ → ⟨ B ⟩)
  (gen-ortho : (m n : ℕ) → ¬ (m ≡ n) → BooleanRingStr._·_ (snd B) (gen m) (gen n) ≡ BooleanRingStr.𝟘 (snd B))
  where

  open EvalNF B gen
  open EvalBoolExpr B gen
  open Correctness B gen
  open JoinMeetEval B gen

  private
    module BA = BooleanAlgebraStr B
    module BR = BooleanRingStr (snd B)

  -- ═══ Key orthogonality lemmas ═══

  -- Distinct generators are orthogonal (just the assumption, for readability)
  distinct-∧-zero : (m n : ℕ) → ¬ (m ≡ n) → gen m ∧B gen n ≡ 𝟘B
  distinct-∧-zero = gen-ortho

  -- gen m absorbs ¬(gen n) for distinct indices: gen m ∧ ¬(gen n) = gen m
  gen-absorb-neg : (m n : ℕ) → ¬ (m ≡ n) → gen m ∧B (¬B (gen n)) ≡ gen m
  gen-absorb-neg m n m≠n =
    gen m ∧B (¬B (gen n))
      ≡⟨ BR.·DistR+ (gen m) 𝟙B (gen n) ⟩
    BR._+_ (gen m ∧B 𝟙B) (gen m ∧B gen n)
      ≡⟨ cong₂ BR._+_ (BR.·IdR (gen m)) (gen-ortho m n m≠n) ⟩
    BR._+_ (gen m) 𝟘B
      ≡⟨ BR.+IdR (gen m) ⟩
    gen m ∎

  -- ¬(gen m) absorbs gen n for distinct indices: ¬(gen m) ∧ gen n = gen n
  neg-absorb-gen : (m n : ℕ) → ¬ (m ≡ n) → (¬B (gen m)) ∧B gen n ≡ gen n
  neg-absorb-gen m n m≠n =
    (¬B (gen m)) ∧B gen n
      ≡⟨ BR.·DistL+ 𝟙B (gen m) (gen n) ⟩
    BR._+_ (𝟙B ∧B gen n) (gen m ∧B gen n)
      ≡⟨ cong₂ BR._+_ (BR.·IdL (gen n)) (gen-ortho m n m≠n) ⟩
    BR._+_ (gen n) 𝟘B
      ≡⟨ BR.+IdR (gen n) ⟩
    gen n ∎

  -- Disjunction of negated generators of distinct indices = 1
  neg-∨-neg-is-1 : (m n : ℕ) → ¬ (m ≡ n) →
    (¬B (gen m)) ∨B (¬B (gen n)) ≡ 𝟙B
  neg-∨-neg-is-1 m n m≠n =
    (¬B (gen m)) ∨B (¬B (gen n))
      ≡⟨ sym BA.DeMorgan¬∧ ⟩
    ¬B (gen m ∧B gen n)
      ≡⟨ cong ¬B_ (gen-ortho m n m≠n) ⟩
    ¬B 𝟘B
      ≡⟨ BR.+IdR 𝟙B ⟩
    𝟙B ∎

  -- gen m idempotent: gen m ∧ gen m = gen m (from ring structure)
  gen-idem : (n : ℕ) → gen n ∧B gen n ≡ gen n
  gen-idem n = BA.∧Idem

  -- Complement law: gen n ∧ ¬(gen n) = 0
  gen-complement : (n : ℕ) → gen n ∧B (¬B (gen n)) ≡ 𝟘B
  gen-complement n = BA.¬Cancels∧R

  -- ═══ Normal form types using our general DNF/CNF ═══

  -- An "orthogonal normal form" is either:
  -- (a) A joinForm: g_n₁ ∨ g_n₂ ∨ ... ∨ g_nₖ (DNF with single positive literal per clause)
  -- (b) A meetNegForm: ¬g_n₁ ∧ ¬g_n₂ ∧ ... ∧ ¬g_nₖ (CNF with single negative literal per clause)
  data OrthoNF : Type₀ where
    orthoJoin    : List ℕ → OrthoNF
    orthoMeetNeg : List ℕ → OrthoNF

  -- Join of generators: g_n₁ ∨ g_n₂ ∨ ...
  finJoin : List ℕ → ⟨ B ⟩
  finJoin [] = 𝟘B
  finJoin (n ∷ ns) = gen n ∨B finJoin ns

  -- Meet of negated generators: ¬g_n₁ ∧ ¬g_n₂ ∧ ...
  finMeetNeg : List ℕ → ⟨ B ⟩
  finMeetNeg [] = 𝟙B
  finMeetNeg (n ∷ ns) = (¬B (gen n)) ∧B finMeetNeg ns

  evalOrthoNF : OrthoNF → ⟨ B ⟩
  evalOrthoNF (orthoJoin ns) = finJoin ns
  evalOrthoNF (orthoMeetNeg ns) = finMeetNeg ns

  -- Bridge to general DNF/CNF evaluation
  finJoin≡evalDNF : (ns : List ℕ) → finJoin ns ≡ evalDNF (joinFormDNF ns)
  finJoin≡evalDNF [] = refl
  finJoin≡evalDNF (n ∷ ns) =
    gen n ∨B finJoin ns
      ≡⟨ cong (gen n ∨B_) (finJoin≡evalDNF ns) ⟩
    gen n ∨B evalDNF (joinFormDNF ns)
      ≡⟨ cong (_∨B evalDNF (joinFormDNF ns)) (sym (BR.·IdR (gen n))) ⟩
    (gen n ∧B 𝟙B) ∨B evalDNF (joinFormDNF ns) ∎

  finMeetNeg≡evalCNF : (ns : List ℕ) → finMeetNeg ns ≡ evalCNF (meetNegFormCNF ns)
  finMeetNeg≡evalCNF [] = refl
  finMeetNeg≡evalCNF (n ∷ ns) =
    (¬B (gen n)) ∧B finMeetNeg ns
      ≡⟨ cong ((¬B (gen n)) ∧B_) (finMeetNeg≡evalCNF ns) ⟩
    (¬B (gen n)) ∧B evalCNF (meetNegFormCNF ns)
      ≡⟨ cong (_∧B evalCNF (meetNegFormCNF ns)) (sym BA.∨IdR) ⟩
    ((¬B (gen n)) ∨B 𝟘B) ∧B evalCNF (meetNegFormCNF ns) ∎

  -- ═══ List operations for orthogonal normal forms ═══

  _∈?_ : ℕ → List ℕ → Bool
  n ∈? [] = false
  n ∈? (m ∷ ms) with discreteℕ n m
  ... | yes _ = true
  ... | no  _ = n ∈? ms

  _∩L_ : List ℕ → List ℕ → List ℕ
  [] ∩L _ = []
  (n ∷ ns) ∩L ms with n ∈? ms
  ... | true  = n ∷ (ns ∩L ms)
  ... | false = ns ∩L ms

  _∖L_ : List ℕ → List ℕ → List ℕ
  [] ∖L _ = []
  (n ∷ ns) ∖L ms with n ∈? ms
  ... | true  = ns ∖L ms
  ... | false = n ∷ (ns ∖L ms)

  _△L_ : List ℕ → List ℕ → List ℕ
  ns △L ms = (ns ∖L ms) ++ (ms ∖L ns)

  -- ═══ XOR and AND on OrthoNF ═══
  -- These mirror xor-nf and meet-nf from FinCofinAlgebra.agda

  xor-onf : OrthoNF → OrthoNF → OrthoNF
  xor-onf (orthoJoin ns) (orthoJoin ms)     = orthoJoin (ns △L ms)
  xor-onf (orthoJoin ns) (orthoMeetNeg ms)  = orthoMeetNeg (ns △L ms)
  xor-onf (orthoMeetNeg ns) (orthoJoin ms)  = orthoMeetNeg (ms △L ns)
  xor-onf (orthoMeetNeg ns) (orthoMeetNeg ms) = orthoJoin (ns △L ms)

  meet-onf : OrthoNF → OrthoNF → OrthoNF
  meet-onf (orthoJoin ns) (orthoJoin ms)     = orthoJoin (ns ∩L ms)
  meet-onf (orthoJoin ns) (orthoMeetNeg ms)  = orthoJoin (ns ∖L ms)
  meet-onf (orthoMeetNeg ns) (orthoJoin ms)  = orthoJoin (ms ∖L ns)
  meet-onf (orthoMeetNeg ns) (orthoMeetNeg ms) = orthoMeetNeg (ns ++ ms)

  neg-onf : OrthoNF → OrthoNF
  neg-onf (orthoJoin ns) = orthoMeetNeg ns
  neg-onf (orthoMeetNeg ns) = orthoJoin ns

  -- ═══ Direct normalization: freeBATerms → OrthoNF ═══

  normalizeToONF : freeBATerms ℕ → OrthoNF
  normalizeToONF (Tvar n) = orthoJoin (n ∷ [])
  normalizeToONF (Tconst false) = orthoJoin []
  normalizeToONF (Tconst true) = orthoMeetNeg []
  normalizeToONF (t +T s) = xor-onf (normalizeToONF t) (normalizeToONF s)
  normalizeToONF (-T t) = normalizeToONF t
  normalizeToONF (t ·T s) = meet-onf (normalizeToONF t) (normalizeToONF s)

  -- ═══ Correctness infrastructure ═══
  -- Core lemmas connecting list operations to ring operations.
  -- These mirror FinCofinAlgebra's finJoin∞-∩L etc.

  -- De Morgan: finMeetNeg ns = ¬(finJoin ns)
  deMorgan-finMeetNeg : (ns : List ℕ) → finMeetNeg ns ≡ ¬B (finJoin ns)
  deMorgan-finMeetNeg [] = sym (BR.+IdR 𝟙B)
  deMorgan-finMeetNeg (n ∷ ns) =
    (¬B (gen n)) ∧B finMeetNeg ns
      ≡⟨ cong ((¬B (gen n)) ∧B_) (deMorgan-finMeetNeg ns) ⟩
    (¬B (gen n)) ∧B (¬B (finJoin ns))
      ≡⟨ sym BA.DeMorgan¬∨ ⟩
    ¬B (gen n ∨B finJoin ns) ∎

  -- neg-onf flips the evaluation
  neg-onf-correct : (nf : OrthoNF) → evalOrthoNF (neg-onf nf) ≡ ¬B (evalOrthoNF nf)
  neg-onf-correct (orthoJoin ns) = deMorgan-finMeetNeg ns
  neg-onf-correct (orthoMeetNeg ns) =
    finJoin ns
      ≡⟨ sym BA.¬Invol ⟩
    ¬B (¬B (finJoin ns))
      ≡⟨ cong ¬B_ (sym (deMorgan-finMeetNeg ns)) ⟩
    ¬B (finMeetNeg ns) ∎

  -- Generator membership and absorption lemmas
  gen-in-finJoin : (n : ℕ) (ms : List ℕ) → (n ∈? ms) ≡ true →
    gen n ∧B finJoin ms ≡ gen n
  gen-in-finJoin n [] p = ex-falso (false≢true p)
  gen-in-finJoin n (m ∷ ms) p with discreteℕ n m
  ... | yes n≡m =
    gen n ∧B (gen m ∨B finJoin ms)
      ≡⟨ cong (λ z → gen n ∧B (gen z ∨B finJoin ms)) (sym n≡m) ⟩
    gen n ∧B (gen n ∨B finJoin ms)
      ≡⟨ BA.∧AbsorbL∨ ⟩
    gen n ∎
  ... | no n≢m =
    gen n ∧B (gen m ∨B finJoin ms)
      ≡⟨ BA.∧DistR∨ ⟩
    (gen n ∧B gen m) ∨B (gen n ∧B finJoin ms)
      ≡⟨ cong₂ _∨B_ (gen-ortho n m n≢m) (gen-in-finJoin n ms p) ⟩
    𝟘B ∨B gen n
      ≡⟨ BA.∨IdL ⟩
    gen n ∎

  gen-notin-finJoin : (n : ℕ) (ms : List ℕ) → (n ∈? ms) ≡ false →
    gen n ∧B finJoin ms ≡ 𝟘B
  gen-notin-finJoin n [] _ = 0-absorbs-right (gen n)
  gen-notin-finJoin n (m ∷ ms) p with discreteℕ n m
  ... | yes _ = ex-falso (true≢false p)
  ... | no n≢m =
    gen n ∧B (gen m ∨B finJoin ms)
      ≡⟨ BA.∧DistR∨ ⟩
    (gen n ∧B gen m) ∨B (gen n ∧B finJoin ms)
      ≡⟨ cong₂ _∨B_ (gen-ortho n m n≢m) (gen-notin-finJoin n ms p) ⟩
    𝟘B ∨B 𝟘B
      ≡⟨ BA.∨IdL ⟩
    𝟘B ∎

  -- ═══ Core list-to-ring lemmas ═══

  -- Concatenation corresponds to join
  finJoin-++ : (ns ms : List ℕ) → finJoin (ns ++ ms) ≡ finJoin ns ∨B finJoin ms
  finJoin-++ [] ms = sym BA.∨IdL
  finJoin-++ (n ∷ ns) ms =
    gen n ∨B finJoin (ns ++ ms)
      ≡⟨ cong (gen n ∨B_) (finJoin-++ ns ms) ⟩
    gen n ∨B (finJoin ns ∨B finJoin ms)
      ≡⟨ BA.∨Assoc ⟩
    (gen n ∨B finJoin ns) ∨B finJoin ms ∎

  -- Intersection corresponds to meet of joins
  finJoin-∩L : (ns ms : List ℕ) → finJoin (ns ∩L ms) ≡ finJoin ns ∧B finJoin ms
  finJoin-∩L [] ms = sym (0-absorbs-left (finJoin ms))
  finJoin-∩L (n ∷ ns) ms with n ∈? ms in eq
  ... | true =
    gen n ∨B finJoin (ns ∩L ms)
      ≡⟨ cong (gen n ∨B_) (finJoin-∩L ns ms) ⟩
    gen n ∨B (finJoin ns ∧B finJoin ms)
      ≡⟨ cong (_∨B (finJoin ns ∧B finJoin ms)) (sym (gen-in-finJoin n ms (builtin→Path-Bool eq))) ⟩
    (gen n ∧B finJoin ms) ∨B (finJoin ns ∧B finJoin ms)
      ≡⟨ sym BA.∧DistL∨ ⟩
    (gen n ∨B finJoin ns) ∧B finJoin ms ∎
  ... | false =
    finJoin (ns ∩L ms)
      ≡⟨ finJoin-∩L ns ms ⟩
    finJoin ns ∧B finJoin ms
      ≡⟨ sym BA.∨IdL ⟩
    𝟘B ∨B (finJoin ns ∧B finJoin ms)
      ≡⟨ cong (_∨B (finJoin ns ∧B finJoin ms)) (sym (gen-notin-finJoin n ms (builtin→Path-Bool eq))) ⟩
    (gen n ∧B finJoin ms) ∨B (finJoin ns ∧B finJoin ms)
      ≡⟨ sym BA.∧DistL∨ ⟩
    (gen n ∨B finJoin ns) ∧B finJoin ms ∎

  -- ═══ Absorption lemmas for negation ═══

  -- If a·b = a then a·¬b = 0
  absorb→neg-zero : {a b : ⟨ B ⟩} → a ∧B b ≡ a → a ∧B (¬B b) ≡ 𝟘B
  absorb→neg-zero {a} {b} p =
    a ∧B (¬B b)
      ≡⟨ BR.·DistR+ a 𝟙B b ⟩
    BR._+_ (a ∧B 𝟙B) (a ∧B b)
      ≡⟨ cong₂ BR._+_ (BR.·IdR a) p ⟩
    BR._+_ a a
      ≡⟨ BA.characteristic2 ⟩
    𝟘B ∎

  -- If a·b = 0 then a·¬b = a
  orthog→neg-absorb : {a b : ⟨ B ⟩} → a ∧B b ≡ 𝟘B → a ∧B (¬B b) ≡ a
  orthog→neg-absorb {a} {b} p =
    a ∧B (¬B b)
      ≡⟨ BR.·DistR+ a 𝟙B b ⟩
    BR._+_ (a ∧B 𝟙B) (a ∧B b)
      ≡⟨ cong₂ BR._+_ (BR.·IdR a) p ⟩
    BR._+_ a 𝟘B
      ≡⟨ BR.+IdR a ⟩
    a ∎

  -- ═══ Set difference corresponds to meet with negation ═══

  finJoin-∖L : (ns ms : List ℕ) → finJoin (ns ∖L ms) ≡ finJoin ns ∧B (¬B (finJoin ms))
  finJoin-∖L [] ms = sym (0-absorbs-left (¬B (finJoin ms)))
  finJoin-∖L (n ∷ ns) ms with n ∈? ms in eq
  ... | true =
    finJoin (ns ∖L ms)
      ≡⟨ finJoin-∖L ns ms ⟩
    finJoin ns ∧B (¬B (finJoin ms))
      ≡⟨ sym BA.∨IdL ⟩
    𝟘B ∨B (finJoin ns ∧B (¬B (finJoin ms)))
      ≡⟨ cong (_∨B (finJoin ns ∧B (¬B (finJoin ms))))
              (sym (absorb→neg-zero (gen-in-finJoin n ms (builtin→Path-Bool eq)))) ⟩
    (gen n ∧B (¬B (finJoin ms))) ∨B (finJoin ns ∧B (¬B (finJoin ms)))
      ≡⟨ sym BA.∧DistL∨ ⟩
    (gen n ∨B finJoin ns) ∧B (¬B (finJoin ms)) ∎
  ... | false =
    gen n ∨B finJoin (ns ∖L ms)
      ≡⟨ cong (gen n ∨B_) (finJoin-∖L ns ms) ⟩
    gen n ∨B (finJoin ns ∧B (¬B (finJoin ms)))
      ≡⟨ cong (_∨B (finJoin ns ∧B (¬B (finJoin ms))))
              (sym (orthog→neg-absorb (gen-notin-finJoin n ms (builtin→Path-Bool eq)))) ⟩
    (gen n ∧B (¬B (finJoin ms))) ∨B (finJoin ns ∧B (¬B (finJoin ms)))
      ≡⟨ sym BA.∧DistL∨ ⟩
    (gen n ∨B finJoin ns) ∧B (¬B (finJoin ms)) ∎

  -- ═══ Symmetric difference corresponds to XOR ═══

  finJoin-△L : (ns ms : List ℕ) → finJoin (ns △L ms) ≡ BR._+_ (finJoin ns) (finJoin ms)
  finJoin-△L ns ms =
    finJoin ((ns ∖L ms) ++ (ms ∖L ns))
      ≡⟨ finJoin-++ (ns ∖L ms) (ms ∖L ns) ⟩
    finJoin (ns ∖L ms) ∨B finJoin (ms ∖L ns)
      ≡⟨ cong₂ _∨B_ (finJoin-∖L ns ms) (finJoin-∖L ms ns) ⟩
    (finJoin ns ∧B (¬B (finJoin ms))) ∨B (finJoin ms ∧B (¬B (finJoin ns)))
      ≡⟨ cong ((finJoin ns ∧B (¬B (finJoin ms))) ∨B_)
              (BR.·Comm (finJoin ms) (¬B (finJoin ns))) ⟩
    (finJoin ns ∧B (¬B (finJoin ms))) ∨B ((¬B (finJoin ns)) ∧B finJoin ms)
      ≡⟨ sym (xor-as-bool (finJoin ns) (finJoin ms)) ⟩
    BR._+_ (finJoin ns) (finJoin ms) ∎

  -- ═══ Concatenation of meet-neg corresponds to meet ═══

  finMeetNeg-++ : (ns ms : List ℕ) → finMeetNeg (ns ++ ms) ≡ finMeetNeg ns ∧B finMeetNeg ms
  finMeetNeg-++ [] ms = sym (BR.·IdL (finMeetNeg ms))
  finMeetNeg-++ (n ∷ ns) ms =
    (¬B (gen n)) ∧B finMeetNeg (ns ++ ms)
      ≡⟨ cong ((¬B (gen n)) ∧B_) (finMeetNeg-++ ns ms) ⟩
    (¬B (gen n)) ∧B (finMeetNeg ns ∧B finMeetNeg ms)
      ≡⟨ BR.·Assoc (¬B (gen n)) (finMeetNeg ns) (finMeetNeg ms) ⟩
    ((¬B (gen n)) ∧B finMeetNeg ns) ∧B finMeetNeg ms ∎

  -- ═══ Ring identities for XOR with negation ═══

  -- ¬a + b = a + ¬b  (negation can hop across XOR)
  ¬+b≡a+¬ : (a b : ⟨ B ⟩) → BR._+_ (¬B a) b ≡ BR._+_ a (¬B b)
  ¬+b≡a+¬ a b =
    BR._+_ (BR._+_ 𝟙B a) b
      ≡⟨ cong (λ z → BR._+_ z b) (BR.+Comm 𝟙B a) ⟩
    BR._+_ (BR._+_ a 𝟙B) b
      ≡⟨ sym (BR.+Assoc a 𝟙B b) ⟩
    BR._+_ a (BR._+_ 𝟙B b) ∎

  -- ¬(a + b) = a + ¬b
  ¬-+-left : (a b : ⟨ B ⟩) → ¬B (BR._+_ a b) ≡ BR._+_ a (¬B b)
  ¬-+-left a b =
    BR._+_ 𝟙B (BR._+_ a b)
      ≡⟨ BR.+Assoc 𝟙B a b ⟩
    BR._+_ (BR._+_ 𝟙B a) b
      ≡⟨ ¬+b≡a+¬ a b ⟩
    BR._+_ a (BR._+_ 𝟙B b) ∎

  -- ¬a + ¬b = a + b
  ¬+¬≡+ : (a b : ⟨ B ⟩) → BR._+_ (¬B a) (¬B b) ≡ BR._+_ a b
  ¬+¬≡+ a b =
    BR._+_ (¬B a) (¬B b)
      ≡⟨ ¬+b≡a+¬ a (¬B b) ⟩
    BR._+_ a (¬B (¬B b))
      ≡⟨ cong (BR._+_ a) BA.¬Invol ⟩
    BR._+_ a b ∎

  -- ═══ meet-onf correctness ═══

  meet-onf-correct : (nf₁ nf₂ : OrthoNF) →
    evalOrthoNF (meet-onf nf₁ nf₂) ≡ evalOrthoNF nf₁ ∧B evalOrthoNF nf₂
  meet-onf-correct (orthoJoin ns) (orthoJoin ms) = finJoin-∩L ns ms
  meet-onf-correct (orthoJoin ns) (orthoMeetNeg ms) =
    finJoin (ns ∖L ms)
      ≡⟨ finJoin-∖L ns ms ⟩
    finJoin ns ∧B (¬B (finJoin ms))
      ≡⟨ cong (finJoin ns ∧B_) (sym (deMorgan-finMeetNeg ms)) ⟩
    finJoin ns ∧B finMeetNeg ms ∎
  meet-onf-correct (orthoMeetNeg ns) (orthoJoin ms) =
    finJoin (ms ∖L ns)
      ≡⟨ finJoin-∖L ms ns ⟩
    finJoin ms ∧B (¬B (finJoin ns))
      ≡⟨ BR.·Comm (finJoin ms) (¬B (finJoin ns)) ⟩
    (¬B (finJoin ns)) ∧B finJoin ms
      ≡⟨ cong (_∧B finJoin ms) (sym (deMorgan-finMeetNeg ns)) ⟩
    finMeetNeg ns ∧B finJoin ms ∎
  meet-onf-correct (orthoMeetNeg ns) (orthoMeetNeg ms) = finMeetNeg-++ ns ms

  -- ═══ xor-onf correctness ═══

  xor-onf-correct : (nf₁ nf₂ : OrthoNF) →
    evalOrthoNF (xor-onf nf₁ nf₂) ≡ BR._+_ (evalOrthoNF nf₁) (evalOrthoNF nf₂)
  xor-onf-correct (orthoJoin ns) (orthoJoin ms) = finJoin-△L ns ms
  xor-onf-correct (orthoJoin ns) (orthoMeetNeg ms) =
    finMeetNeg (ns △L ms)
      ≡⟨ deMorgan-finMeetNeg (ns △L ms) ⟩
    ¬B (finJoin (ns △L ms))
      ≡⟨ cong ¬B_ (finJoin-△L ns ms) ⟩
    ¬B (BR._+_ (finJoin ns) (finJoin ms))
      ≡⟨ ¬-+-left (finJoin ns) (finJoin ms) ⟩
    BR._+_ (finJoin ns) (¬B (finJoin ms))
      ≡⟨ cong (BR._+_ (finJoin ns)) (sym (deMorgan-finMeetNeg ms)) ⟩
    BR._+_ (finJoin ns) (finMeetNeg ms) ∎
  xor-onf-correct (orthoMeetNeg ns) (orthoJoin ms) =
    finMeetNeg (ms △L ns)
      ≡⟨ deMorgan-finMeetNeg (ms △L ns) ⟩
    ¬B (finJoin (ms △L ns))
      ≡⟨ cong ¬B_ (finJoin-△L ms ns) ⟩
    ¬B (BR._+_ (finJoin ms) (finJoin ns))
      ≡⟨ ¬-+-left (finJoin ms) (finJoin ns) ⟩
    BR._+_ (finJoin ms) (¬B (finJoin ns))
      ≡⟨ cong (BR._+_ (finJoin ms)) (sym (deMorgan-finMeetNeg ns)) ⟩
    BR._+_ (finJoin ms) (finMeetNeg ns)
      ≡⟨ BR.+Comm (finJoin ms) (finMeetNeg ns) ⟩
    BR._+_ (finMeetNeg ns) (finJoin ms) ∎
  xor-onf-correct (orthoMeetNeg ns) (orthoMeetNeg ms) =
    finJoin (ns △L ms)
      ≡⟨ finJoin-△L ns ms ⟩
    BR._+_ (finJoin ns) (finJoin ms)
      ≡⟨ sym (¬+¬≡+ (finJoin ns) (finJoin ms)) ⟩
    BR._+_ (¬B (finJoin ns)) (¬B (finJoin ms))
      ≡⟨ cong₂ BR._+_ (sym (deMorgan-finMeetNeg ns)) (sym (deMorgan-finMeetNeg ms)) ⟩
    BR._+_ (finMeetNeg ns) (finMeetNeg ms) ∎

  -- ═══ Full normalization correctness ═══

  normalizeToONF-correct : (t : freeBATerms ℕ) →
    evalOrthoNF (normalizeToONF t) ≡ interpretInB t
  normalizeToONF-correct (Tvar n) =
    gen n ∨B 𝟘B
      ≡⟨ BA.∨IdR ⟩
    gen n ∎
  normalizeToONF-correct (Tconst false) = refl
  normalizeToONF-correct (Tconst true) = refl
  normalizeToONF-correct (t +T s) =
    evalOrthoNF (xor-onf (normalizeToONF t) (normalizeToONF s))
      ≡⟨ xor-onf-correct (normalizeToONF t) (normalizeToONF s) ⟩
    BR._+_ (evalOrthoNF (normalizeToONF t)) (evalOrthoNF (normalizeToONF s))
      ≡⟨ cong₂ BR._+_ (normalizeToONF-correct t) (normalizeToONF-correct s) ⟩
    BR._+_ (interpretInB t) (interpretInB s) ∎
  normalizeToONF-correct (-T t) = normalizeToONF-correct t
  normalizeToONF-correct (t ·T s) =
    evalOrthoNF (meet-onf (normalizeToONF t) (normalizeToONF s))
      ≡⟨ meet-onf-correct (normalizeToONF t) (normalizeToONF s) ⟩
    evalOrthoNF (normalizeToONF t) ∧B evalOrthoNF (normalizeToONF s)
      ≡⟨ cong₂ _∧B_ (normalizeToONF-correct t) (normalizeToONF-correct s) ⟩
    interpretInB t ∧B interpretInB s ∎

  -- ═══ Existence: every element has an orthogonal normal form ═══

  orthoNFExists : (terms-surj : isSurjection interpretInB) →
    (x : ⟨ B ⟩) → ∥ Σ[ nf ∈ OrthoNF ] evalOrthoNF nf ≡ x ∥₁
  orthoNFExists surj x = PT.map go (surj x)
    where
      go : Σ[ t ∈ freeBATerms ℕ ] interpretInB t ≡ x →
           Σ[ nf ∈ OrthoNF ] evalOrthoNF nf ≡ x
      go (t , p) = normalizeToONF t , (
        evalOrthoNF (normalizeToONF t)
          ≡⟨ normalizeToONF-correct t ⟩
        interpretInB t
          ≡⟨ p ⟩
        x ∎)

  -- ═══ Helper functions ═══

  -- Classification: every element is either a join of generators or a meet of negated generators
  classifyElement : (terms-surj : isSurjection interpretInB) → (x : ⟨ B ⟩) →
    ∥ (Σ[ ns ∈ List ℕ ] x ≡ finJoin ns) ⊎ (Σ[ ns ∈ List ℕ ] x ≡ finMeetNeg ns) ∥₁
  classifyElement surj x = PT.map extract (orthoNFExists surj x)
    where
      extract : Σ[ nf ∈ OrthoNF ] evalOrthoNF nf ≡ x →
                (Σ[ ns ∈ List ℕ ] x ≡ finJoin ns) ⊎ (Σ[ ns ∈ List ℕ ] x ≡ finMeetNeg ns)
      extract (orthoJoin ns , p) = inl (ns , sym p)
      extract (orthoMeetNeg ns , p) = inr (ns , sym p)

  -- Extract index list from an OrthoNF
  getIndices : OrthoNF → List ℕ
  getIndices (orthoJoin ns) = ns
  getIndices (orthoMeetNeg ns) = ns

  -- Check which form the OrthoNF is in
  isJoinForm : OrthoNF → Bool
  isJoinForm (orthoJoin _) = true
  isJoinForm (orthoMeetNeg _) = false

  -- Convert OrthoNF to general DNF (single positive literal per clause for joins)
  orthoNF-to-DNF : OrthoNF → DNF
  orthoNF-to-DNF (orthoJoin ns) = joinFormDNF ns
  orthoNF-to-DNF (orthoMeetNeg ns) = (negativeLiterals ns) ∷ []

  -- Convert OrthoNF to general CNF (single negative literal per clause for meets)
  orthoNF-to-CNF : OrthoNF → CNF
  orthoNF-to-CNF (orthoJoin ns) = (positiveLiterals ns) ∷ []
  orthoNF-to-CNF (orthoMeetNeg ns) = meetNegFormCNF ns

  -- Bridge: evalConjClause (negativeLiterals ns) = finMeetNeg ns
  evalConj-negLits : (ns : List ℕ) → evalConjClause (negativeLiterals ns) ≡ finMeetNeg ns
  evalConj-negLits [] = refl
  evalConj-negLits (n ∷ ns) = cong ((¬B (gen n)) ∧B_) (evalConj-negLits ns)

  -- Bridge: evalDisjClause (positiveLiterals ns) = finJoin ns
  evalDisj-posLits : (ns : List ℕ) → evalDisjClause (positiveLiterals ns) ≡ finJoin ns
  evalDisj-posLits [] = refl
  evalDisj-posLits (n ∷ ns) = cong (gen n ∨B_) (evalDisj-posLits ns)

  -- Evaluation bridges: orthoNF-to-DNF/CNF evaluate correctly
  orthoNF-to-DNF-correct : (nf : OrthoNF) →
    evalDNF (orthoNF-to-DNF nf) ≡ evalOrthoNF nf
  orthoNF-to-DNF-correct (orthoJoin ns) = sym (finJoin≡evalDNF ns)
  orthoNF-to-DNF-correct (orthoMeetNeg ns) =
    evalConjClause (negativeLiterals ns) ∨B 𝟘B
      ≡⟨ BA.∨IdR ⟩
    evalConjClause (negativeLiterals ns)
      ≡⟨ evalConj-negLits ns ⟩
    finMeetNeg ns ∎

  orthoNF-to-CNF-correct : (nf : OrthoNF) →
    evalCNF (orthoNF-to-CNF nf) ≡ evalOrthoNF nf
  orthoNF-to-CNF-correct (orthoJoin ns) =
    evalDisjClause (positiveLiterals ns) ∧B 𝟙B
      ≡⟨ BR.·IdR (evalDisjClause (positiveLiterals ns)) ⟩
    evalDisjClause (positiveLiterals ns)
      ≡⟨ evalDisj-posLits ns ⟩
    finJoin ns ∎
  orthoNF-to-CNF-correct (orthoMeetNeg ns) = sym (finMeetNeg≡evalCNF ns)

  -- ═══ Simplified CNF/DNF existence theorems ═══

  -- Every element has a DNF where each clause is either:
  --   a single positive literal (joinForm case), or
  --   a full conjunction of negated literals (meetNegForm case)
  simplifiedDNFExists : (terms-surj : isSurjection interpretInB) → (x : ⟨ B ⟩) →
    ∥ Σ[ d ∈ DNF ] evalDNF d ≡ x ∥₁
  simplifiedDNFExists surj x = PT.map
    (λ { (nf , p) → orthoNF-to-DNF nf , (
      evalDNF (orthoNF-to-DNF nf)
        ≡⟨ orthoNF-to-DNF-correct nf ⟩
      evalOrthoNF nf
        ≡⟨ p ⟩
      x ∎) })
    (orthoNFExists surj x)

  -- Every element has a CNF where each clause is either:
  --   a full disjunction of positive literals (joinForm case), or
  --   a single negative literal (meetNegForm case)
  simplifiedCNFExists : (terms-surj : isSurjection interpretInB) → (x : ⟨ B ⟩) →
    ∥ Σ[ c ∈ CNF ] evalCNF c ≡ x ∥₁
  simplifiedCNFExists surj x = PT.map
    (λ { (nf , p) → orthoNF-to-CNF nf , (
      evalCNF (orthoNF-to-CNF nf)
        ≡⟨ orthoNF-to-CNF-correct nf ⟩
      evalOrthoNF nf
        ≡⟨ p ⟩
      x ∎) })
    (orthoNFExists surj x)
