{-# OPTIONS --lossy-unification --allow-unsolved-metas #-}
-- Assuming dependent choice (the Tower form) and LLPO: derive weak König's lemma (WKL),
-- and then attempt propositional completeness (PC) from it.
--
--   LLPO  →  "an infinite node has an infinite child"   (the local dichotomy: ¬(both
--            children finite) ⇒ ∥ left-infinite ⊎ right-infinite ∥; "child finite" is an
--            OPEN proposition, so this is exactly DisjunctionClosed.deMorganHard under LLPO).
--   DC (Tower form)  →  assemble those choices into a *coherent* branch.  The tower form is
--            essential: `SequentialLimit` packages a branch with its coherence
--            (map(branch(suc n)) ≡ branch n), which the bare `(n) → P n` form does not.
--
-- The DC+LLPO wiring is filled in; the tree/`infNode` bookkeeping is left as typed holes.
module WKLfromDCLLPO where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Sigma
open import Cubical.Data.List using (List ; [] ; _∷_ ; _++_ ; length)
open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁)

open import Axioms.DependentChoice
  using (DependentChoiceTowerAxiom ; Tower ; tower ; SequentialLimit ; limitPoint
        ; allMapsSurjective ; projectionSurjective ; projection)
open import OmnisciencePrinciples.LLPO using (LLPO)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Relation.Nullary using () renaming (¬_ to ¬ᵗ_)
open import StoneSpaces.Spectrum using (StoneSpace ; Sp ; Booleω)
open Tower
open SequentialLimit

------------------------------------------------------------------------
-- finite binary strings, with `snoc` (extend by one bit) and `init` (drop last bit)
------------------------------------------------------------------------
_∷ʳ_ : List Bool → Bool → List Bool
s ∷ʳ b = s ++ (b ∷ [])

init : List Bool → List Bool
init []           = []
init (x ∷ [])     = []
init (x ∷ y ∷ xs) = x ∷ init (y ∷ xs)

-- the length-n prefix of a branch (head = first bit)
prefix : (ℕ → Bool) → ℕ → List Bool
prefix α zero    = []
prefix α (suc n) = α 0 ∷ prefix (α ∘ suc) n

isPrefix : List Bool → List Bool → Type
isPrefix s t = Σ[ u ∈ List Bool ] (t ≡ s ++ u)

------------------------------------------------------------------------
-- A binary tree: a decidable, prefix-closed, unbounded subset of binary strings.
------------------------------------------------------------------------
record Tree : Type where
  field
    mem       : List Bool → Bool
    rootIn    : mem [] ≡ true
    prefixCl  : (s : List Bool) (b : Bool) → mem (s ∷ʳ b) ≡ true → mem s ≡ true
    unbounded : (n : ℕ) → ∥ Σ[ s ∈ List Bool ] (length s ≡ n) × (mem s ≡ true) ∥₁

module _ (T : Tree) where
  open Tree T

  -- a node whose subtree is infinite (has extensions of every length)
  infNode : List Bool → Type
  infNode s = (k : ℕ) → ∥ Σ[ t ∈ List Bool ] (isPrefix s t × (length t ≡ length s + k) × (mem t ≡ true)) ∥₁

  -- a branch of T
  Branch : Type
  Branch = Σ[ α ∈ (ℕ → Bool) ] ((n : ℕ) → mem (prefix α n) ≡ true)

  module assuming (dc : DependentChoiceTowerAxiom {ℓ-zero}) (llpo : LLPO) where

    ----------------------------------------------------------------
    -- THE LLPO STEP: an infinite node has an infinite child.
    -- ¬(s∷ʳ0-subtree finite ∧ s∷ʳ1-subtree finite) holds because s is infinite, and
    -- "child finite" is an open proposition, so DisjunctionClosed.deMorganHard (under llpo)
    -- gives the truncated disjunction.
    ----------------------------------------------------------------
    infiniteChild : (s : List Bool) → infNode s → ∥ Σ[ b ∈ Bool ] infNode (s ∷ʳ b) ∥₁
    infiniteChild s sInf = {!!}

    ----------------------------------------------------------------
    -- The tower of infinite nodes; its maps are surjective (= infiniteChild), so DC
    -- gives a coherent branch through infinite nodes.
    ----------------------------------------------------------------
    objₙ : ℕ → Type
    objₙ n = Σ[ s ∈ List Bool ] (length s ≡ n) × infNode s

    mapₙ : {n : ℕ} → objₙ (suc n) → objₙ n
    mapₙ (s , lenpf , inf) = init s , {!!} , {!!}       -- drop last bit; length/infNode of init s

    infTower : Tower ℓ-zero
    infTower = tower objₙ mapₙ

    allSurj : allMapsSurjective infTower
    allSurj n (s , lenpf , sInf) =
      PT.map (λ { (b , childInf) → (s ∷ʳ b , {!!} , childInf) , {!!} }) (infiniteChild s sInf)
      -- a surjection onto (s,_) : an infinite child s∷ʳb mapping (init) back to s

    rootInf : objₙ 0
    rootInf = [] , refl , {!!}                          -- infNode [] from `unbounded`

    -- DC: the projection from sequential limits is surjective, so root has a coherent
    -- branch of infinite nodes above it.
    branchOfNodes : ∥ Σ[ lim ∈ SequentialLimit infTower ] (projection infTower 0 lim ≡ rootInf) ∥₁
    branchOfNodes = dc infTower allSurj rootInf

    -- extract the actual branch α : ℕ → Bool from the coherent nodes.
    WKL : ∥ Branch ∥₁
    WKL = PT.map (λ { (limitPoint branch _ , _) → {!!} }) branchOfNodes
      -- α n ≔ the (coherent) nodes' bits; prefix α n ≡ fst (branch n) ⇒ mem (prefix α n) ≡ true.

------------------------------------------------------------------------
-- … and propositional completeness follows from WKL (sketch).
--
-- A Stone space S is (the carrier of) Sp D for some D : Booleω = freeBA ℕ /Im r.  A point of
-- Sp D is a binary sequence on the generators respecting every relation r n.  Take the Tree
--   mem s = "the partial assignment s violates no relation checkable within length s"
-- (prefix-closed, decidable, with `unbounded` from ¬¬⟨S⟩: ¬¬ of a *decidable* level-non-empty
-- statement gives the statement).  Then `assuming.WKL` produces ∥ branch ∥, and a branch is
-- exactly a point, so ∥ Sp D ∥ ≅ ∥ ⟨ S ⟩ ∥.
------------------------------------------------------------------------
PropositionalCompleteness : Type₁
PropositionalCompleteness = (S : StoneSpace) → ¬ᵗ ¬ᵗ ⟨ S ⟩ → ∥ ⟨ S ⟩ ∥₁

module PCfromWKL (dc : DependentChoiceTowerAxiom {ℓ-zero}) (llpo : LLPO) where
  PC : PropositionalCompleteness
  PC S ¬¬S = {!!}
    -- build  treeOf S : Tree  (consistent-prefix tree of the presentation of ⟨S⟩ ≅ Sp D),
    -- unbounded by ¬¬S; then  assuming.WKL (treeOf S) dc llpo : ∥ Branch (treeOf S) ∥₁,
    -- and  Branch (treeOf S) ≃ ⟨ S ⟩  (a respecting branch ↔ a point).
