{-# OPTIONS --cubical --guardedness #-}

{-
  Sequential colimits of sets — clean results.
  Uses the library's Sequence and SeqColim.
  No postulates. No TERMINATING pragmas.
-}

module SetSeqColim2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence

open import Cubical.HITs.SequentialColimit.Base
open import Cubical.HITs.SequentialColimit.Properties
  using (converges→ColimIso; SeqColimIso; ShiftSequence+)
open import Cubical.HITs.PropositionalTruncation as PT hiding (map)

open Sequence
open Iso

private
  variable
    ℓ ℓ' : Level

-- ═══════════════════════════════════════════════════════════════════
-- §1. Convenience eliminators
-- ═══════════════════════════════════════════════════════════════════

module _ (X : Sequence ℓ) where

  SeqColim-elimProp : {P : SeqColim X → Type ℓ'}
    → ((x : SeqColim X) → isProp (P x))
    → ({n : ℕ} (a : obj X n) → P (incl a))
    → (x : SeqColim X) → P x
  SeqColim-elimProp hP f (incl x) = f x
  SeqColim-elimProp hP f (push x i) =
    isProp→PathP (λ i → hP (push x i)) (f x) (f (map X x)) i

  SeqColim-rec : {B : Type ℓ'} → isSet B
    → (f : {n : ℕ} → obj X n → B)
    → ({n : ℕ} (a : obj X n) → f a ≡ f (map X a))
    → SeqColim X → B
  SeqColim-rec hB f p (incl x) = f x
  SeqColim-rec hB f p (push x i) = p x i

-- ═══════════════════════════════════════════════════════════════════
-- §2. Iterated maps
-- ═══════════════════════════════════════════════════════════════════

iterMap : (X : Sequence ℓ) (k : ℕ) {n : ℕ} → obj X n → obj X (k + n)
iterMap X zero    x = x
iterMap X (suc k) x = map X (iterMap X k x)

push-fwd : (X : Sequence ℓ) (k : ℕ) {n : ℕ} (x : obj X n)
  → incl {X = X} x ≡ incl (iterMap X k x)
push-fwd X zero    x = refl
push-fwd X (suc k) x = push-fwd X k x ∙ push (iterMap X k x)

-- ═══════════════════════════════════════════════════════════════════
-- §3. Colimit of contractible types is contractible
-- ═══════════════════════════════════════════════════════════════════

contr→converges : (X : Sequence ℓ) → ((n : ℕ) → isContr (obj X n))
  → converges X 0
contr→converges X hC k =
  subst (λ m → isEquiv (map X {n = m})) (sym (+-zero k))
    (isEquivFromIsContr (map X) (hC k) (hC (suc k)))

colimitContr : (X : Sequence ℓ) → ((n : ℕ) → isContr (obj X n))
  → isContr (SeqColim X)
colimitContr X hC =
  isOfHLevelRespectEquiv 0
    (isoToEquiv (converges→ColimIso 0 (contr→converges X hC)))
    (hC 0)

-- ═══════════════════════════════════════════════════════════════════
-- §4. Truncated sequence
-- ═══════════════════════════════════════════════════════════════════

truncSeq : Sequence ℓ → Sequence ℓ
obj (truncSeq X) n = ∥ obj X n ∥₁
map (truncSeq X) = PT.map (map X)

-- Forward: SeqColim X → SeqColim (truncSeq X)
trunc-fwd : (X : Sequence ℓ) → SeqColim X → SeqColim (truncSeq X)
trunc-fwd X (incl x)   = incl ∣ x ∣₁
trunc-fwd X (push x i) = push ∣ x ∣₁ i

-- Backward: SeqColim (truncSeq X) → ∥ SeqColim X ∥₁
trunc-bwd : (X : Sequence ℓ) → SeqColim (truncSeq X) → ∥ SeqColim X ∥₁
trunc-bwd X = SeqColim-elimProp (truncSeq X)
  (λ _ → squash₁)
  (λ {n} ta → PT.rec squash₁ (λ a → ∣ incl {n = n} a ∣₁) ta)

-- ═══════════════════════════════════════════════════════════════════
-- §5. SeqColim of truncated sequence is a proposition
-- ═══════════════════════════════════════════════════════════════════

-- Key idea: if inhabited, then some level has a witness, and
-- pushing forward makes all subsequent levels inhabited. Using
-- the shift iso SeqColimIso, the colimit of the shifted
-- (all-contractible) sequence is contractible.

truncSeq-contr-from-incl : (X : Sequence ℓ) {n : ℕ} (a : obj X n)
  → isContr (SeqColim (truncSeq X))
truncSeq-contr-from-incl X {n} a =
  isOfHLevelRespectEquiv 0
    (isoToEquiv (invIso (SeqColimIso (truncSeq X) n)))
    (colimitContr (ShiftSequence+ (truncSeq X) n)
      (λ k → inhProp→isContr ∣ iterMap X k a ∣₁ squash₁))

SeqColim-truncSeq-isProp : (X : Sequence ℓ) → isProp (SeqColim (truncSeq X))
SeqColim-truncSeq-isProp X x y =
  sym (snd contr-x x) ∙ snd contr-x y
  where
    contr-x : isContr (SeqColim (truncSeq X))
    contr-x = SeqColim-elimProp (truncSeq X)
      (λ _ → isPropIsContr)
      (λ {n} ta → PT.rec isPropIsContr
        (λ a → truncSeq-contr-from-incl X a) ta)
      x

-- ═══════════════════════════════════════════════════════════════════
-- §6. Propositional truncation commutes with SeqColim (as Iso)
-- ═══════════════════════════════════════════════════════════════════

truncCommutes : (X : Sequence ℓ) → Iso ∥ SeqColim X ∥₁ (SeqColim (truncSeq X))
fun (truncCommutes X) = PT.rec (SeqColim-truncSeq-isProp X) (trunc-fwd X)
inv (truncCommutes X) = trunc-bwd X
sec (truncCommutes X) _ = SeqColim-truncSeq-isProp X _ _
ret (truncCommutes X) _ = squash₁ _ _

-- ═══════════════════════════════════════════════════════════════════
-- §7. Universal property of sequential colimits
-- ═══════════════════════════════════════════════════════════════════

-- A cocone from a sequence X into a type B consists of:
-- • a family of maps ι_n : X_n → B
-- • coherences: ι_n(a) ≡ ι_{n+1}(map a)
record Cocone (X : Sequence ℓ) (B : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  constructor cocone
  field
    leg  : {n : ℕ} → obj X n → B
    comm : {n : ℕ} (a : obj X n) → leg a ≡ leg (map X a)

open Cocone

-- The canonical cocone from X into SeqColim X
canonCocone : (X : Sequence ℓ) → Cocone X (SeqColim X)
leg  (canonCocone X) = incl
comm (canonCocone X) = push

-- ── Existence: a cocone induces a map from the colimit ──

coconeRec : (X : Sequence ℓ) {B : Type ℓ'} → Cocone X B → SeqColim X → B
coconeRec X c (incl x)   = leg c x
coconeRec X c (push x i) = comm c x i

-- ── Restriction: a map from the colimit gives a cocone ──

restrict : (X : Sequence ℓ) {B : Type ℓ'} → (SeqColim X → B) → Cocone X B
leg  (restrict X f) a = f (incl a)
comm (restrict X f) a = cong f (push a)

-- ── The universal property: (SeqColim X → B) ≃ Cocone X B ──

-- Roundtrip 1: restrict (coconeRec c) ≡ c
-- This holds definitionally (both leg and comm compute by pattern matching)
restrict∘rec : (X : Sequence ℓ) {B : Type ℓ'} (c : Cocone X B)
  → restrict X (coconeRec X c) ≡ c
restrict∘rec X c = refl

-- Roundtrip 2: coconeRec (restrict f) ≡ f
-- For each x : SeqColim X, coconeRec(restrict f)(x) = f(x) by HIT computation
rec∘restrict : (X : Sequence ℓ) {B : Type ℓ'} (f : SeqColim X → B)
  → coconeRec X (restrict X f) ≡ f
rec∘restrict X f = funExt (go X f)
  where
    go : (X : Sequence ℓ) {B : Type ℓ'} (f : SeqColim X → B)
      → (x : SeqColim X) → coconeRec X (restrict X f) x ≡ f x
    go X f (incl x)   = refl
    go X f (push x i) = refl

-- The equivalence
coconeEquiv : (X : Sequence ℓ) (B : Type ℓ')
  → (SeqColim X → B) ≃ Cocone X B
coconeEquiv X B = isoToEquiv e where
  e : Iso (SeqColim X → B) (Cocone X B)
  fun e = restrict X
  inv e = coconeRec X
  sec e = restrict∘rec X
  ret e = rec∘restrict X

-- ── Uniqueness: two maps from the colimit agreeing on incl are equal ──
-- (When B is a set, agreement on incl suffices; the push coherence is automatic.)

coconeRec-unique : (X : Sequence ℓ) {B : Type ℓ'} → isSet B
  → (f g : SeqColim X → B)
  → ((n : ℕ) (a : obj X n) → f (incl a) ≡ g (incl a))
  → f ≡ g
coconeRec-unique X hB f g agree = funExt (go X hB f g agree)
  where
    go : (X : Sequence ℓ) {B : Type ℓ'} → isSet B
      → (f g : SeqColim X → B)
      → ((n : ℕ) (a : obj X n) → f (incl a) ≡ g (incl a))
      → (x : SeqColim X) → f x ≡ g x
    go X hB f g agree (incl {n} x) = agree n x
    go X hB f g agree (push {n} x i) =
      isProp→PathP (λ i → hB (f (push x i)) (g (push x i)))
        (agree n x) (agree (suc n) (map X x)) i

-- ── Characterization: any type with the UP is equivalent to SeqColim X ──

-- If B has a cocone such that "mapping out of B" is equivalent to
-- "giving a cocone", then B ≃ SeqColim X.

-- More precisely: if B has a cocone c : Cocone X B such that
-- for any type C, precomposing with coconeRec c gives an equivalence
-- (B → C) ≃ Cocone X C, then B ≃ SeqColim X.

-- We give a direct proof: the cocone gives maps in both directions.

-- ── Characterization: if a cocone gives an equivalence, recover B ≃ SeqColim X ──

-- The simplest useful characterization: if coconeRec of a cocone into B
-- is an equivalence, then B ≃ SeqColim X.

cocone→equiv : (X : Sequence ℓ) {B : Type ℓ'}
  → (c : Cocone X B) → isEquiv (coconeRec X c)
  → B ≃ SeqColim X
cocone→equiv X c isE = invEquiv (coconeRec X c , isE)

-- The stronger universal characterization: B has the UP of the colimit
-- iff coconeRec c is an equivalence. Concretely:
-- If for every C, (B → C) ≃ Cocone X C (via restriction along c),
-- then B ≃ SeqColim X.

-- ── For sets: cocones are determined by their legs ──

-- When B is a set, two cocones with the same legs are equal
-- (the comm paths are automatically equal by isSet).
Cocone≡ : (X : Sequence ℓ) {B : Type ℓ'} → isSet B
  → {c d : Cocone X B} → ({n : ℕ} → leg c {n} ≡ leg d {n})
  → c ≡ d
leg  (Cocone≡ X hB {c} {d} p i) a = p i a
comm (Cocone≡ X hB {c} {d} p i) a =
  isProp→PathP (λ i → hB (p i a) (p i (map X a)))
    (comm c a) (comm d a) i

-- Restriction along a cocone
restrictFrom : {X : Sequence ℓ} {B : Type ℓ'} (c : Cocone X B)
  → {C : Type ℓ'} → (B → C) → Cocone X C
leg  (restrictFrom c f)   = f ∘ leg c
comm (restrictFrom c f) a = cong f (comm c a)

-- ── Full characterization for sets: B ≃ SeqColim X ──

-- When both B and SeqColim X are sets, the full characterization says:
-- if B has a cocone c and a recursor recB that is inverse to restrictFrom c,
-- then B ≃ SeqColim X. The proof constructs embed = recB(canonCocone) and
-- compare = coconeRec c, and shows the roundtrips using that cocones into
-- sets are determined by their legs (Cocone≡).

-- This requires isSet(SeqColim X) as a hypothesis (provable, but needs
-- the encode-decode argument which requires TERMINATING).

module ColimitCharacterization
  (X : Sequence ℓ) {B : Type ℓ}
  (hB : isSet B) (hS : isSet (SeqColim X))
  (c : Cocone X B)
  (recB : {C : Type ℓ} → isSet C → Cocone X C → (B → C))
  (secB : {C : Type ℓ} (hC : isSet C) (d : Cocone X C) → restrictFrom c (recB hC d) ≡ d)
  (retB : {C : Type ℓ} (hC : isSet C) (f : B → C) → recB hC (restrictFrom c f) ≡ f)
  where

  private
    compare : SeqColim X → B
    compare = coconeRec X c

    embed : B → SeqColim X
    embed = recB hS (canonCocone X)

    -- embed ∘ leg c ≡ incl (from secB)
    sec-path : restrictFrom c embed ≡ canonCocone X
    sec-path = secB hS (canonCocone X)

    embed∘leg≡incl : {n : ℕ} (a : obj X n) → embed (leg c a) ≡ incl a
    embed∘leg≡incl {n} a = cong (λ cc → leg cc {n} a) sec-path

    -- Roundtrip 1: compare ∘ embed ≡ id_B
    -- restrictFrom c (compare ∘ embed) has legs = compare ∘ embed ∘ leg c = compare ∘ incl = leg c
    -- restrictFrom c id has legs = leg c. Same legs → same cocones (by Cocone≡).
    -- Then retB gives compare ∘ embed = id.
    rt1-cocone : restrictFrom c (compare ∘ embed) ≡ restrictFrom c (idfun B)
    rt1-cocone = Cocone≡ X hB (funExt (λ a → cong compare (embed∘leg≡incl a)))

    roundtrip₁ : compare ∘ embed ≡ idfun B
    roundtrip₁ = sym (retB hB (compare ∘ embed)) ∙ cong (recB hB) rt1-cocone ∙ retB hB (idfun B)

    -- Roundtrip 2: embed ∘ compare ≡ id_SeqColim
    -- restrict X (embed ∘ compare) has legs = embed ∘ compare ∘ incl = embed ∘ leg c = incl = legs of canonCocone.
    -- By rec∘restrict, embed ∘ compare = id.
    rt2-restrict : restrict X (embed ∘ compare) ≡ restrict X (idfun (SeqColim X))
    rt2-restrict = Cocone≡ X hS (funExt embed∘leg≡incl)

    roundtrip₂ : embed ∘ compare ≡ idfun (SeqColim X)
    roundtrip₂ = sym (rec∘restrict X (embed ∘ compare)) ∙ cong (coconeRec X) rt2-restrict ∙ rec∘restrict X (idfun _)

  colimIso : Iso B (SeqColim X)
  fun colimIso = embed
  inv colimIso = compare
  sec colimIso = funExt⁻ roundtrip₂
  ret colimIso = funExt⁻ roundtrip₁

-- ═══════════════════════════════════════════════════════════════════
-- §8. First projection from Σ-sequence colimit
-- ═══════════════════════════════════════════════════════════════════

record SeqFib (A : Sequence ℓ) : Type (ℓ-suc ℓ) where
  field
    P    : (n : ℕ) → obj A n → Type ℓ
    Pmap : (n : ℕ) (a : obj A n) → P n a → P (suc n) (map A a)

open SeqFib

ΣSeq : (A : Sequence ℓ) → SeqFib A → Sequence ℓ
obj (ΣSeq A B) n = Σ (obj A n) (P B n)
map (ΣSeq A B) (a , b) = map A a , Pmap B _ a b

Σ-proj : (A : Sequence ℓ) (B : SeqFib A) → SeqColim (ΣSeq A B) → SeqColim A
Σ-proj A B (incl (a , _)) = incl a
Σ-proj A B (push (a , _) i) = push a i

-- ═══════════════════════════════════════════════════════════════════
-- §8. Colimit of the Σ-sequence for the singleton fibration is contractible
-- ═══════════════════════════════════════════════════════════════════

-- The "singleton fibration" at level k: P n a = (iterMap A k {0} x₀ transported to level n, ≡ a).
-- This is used in the path characterization / encode-decode argument.
-- We define a version that avoids the +-zero transport issue by
-- working with the Σ-sequence directly.

-- For any base point x₀ : obj A 0, define the singleton sequence:
-- Level n has type Σ (obj A n) (λ a → iterMap A n x₀ ≡ a) where
-- iterMap lands in obj A (n + 0). We accept the n+0 indexing.
singletonSeq : (A : Sequence ℓ) → obj A 0 → Sequence ℓ
obj (singletonSeq A x₀) n = Σ (obj A (n + 0)) (λ a → iterMap A n x₀ ≡ a)
map (singletonSeq A x₀) (a , p) = map A a , cong (map A) p

singletonSeq-contr : (A : Sequence ℓ) (x₀ : obj A 0) (n : ℕ)
  → isContr (obj (singletonSeq A x₀) n)
singletonSeq-contr A x₀ n =
  (iterMap A n x₀ , refl) ,
  λ { (a , p) i → p i , λ j → p (i ∧ j) }

singletonSeq-colim-contr : (A : Sequence ℓ) (x₀ : obj A 0)
  → isContr (SeqColim (singletonSeq A x₀))
singletonSeq-colim-contr A x₀ =
  colimitContr (singletonSeq A x₀) (singletonSeq-contr A x₀)
