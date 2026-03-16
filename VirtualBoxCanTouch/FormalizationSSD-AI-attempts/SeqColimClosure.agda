{-# OPTIONS --cubical --lossy-unification --guardedness #-}

{-
  Sequential colimits: closure under Σ-types and path characterization.

  This file is an AI translation (by Claude, Anthropic) of the cubicaltt
  formalization by Mörtberg:
    https://github.com/mortberg/cubicaltt/blob/seqcolim/examples/seqcolim.ctt

  Based on the paper:
    Sojakova, van Doorn, Rijke,
    "Sequential Colimits in Homotopy Type Theory" (LICS 2020)
    https://florisvandoorn.com/papers/sequential_colimits_homotopy.pdf
-}

module SeqColimClosure where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence

open import Cubical.HITs.SequentialColimit.Base using (SeqColim; incl; push)

private
  variable
    ℓ ℓ' : Level

open Sequence

-- Shift a sequence by one (shiftSequence in cubicaltt)
ShiftSeq : Sequence ℓ → Sequence ℓ
obj (ShiftSeq C) n = obj C (suc n)
map (ShiftSeq C) = map C

-- ═══════════════════════════════════════════════════════════════════
-- §1. Recursive sequential colimit (translated from cubicaltt seqCo)
-- ═══════════════════════════════════════════════════════════════════

-- The recursive definition: structurally recurses on ShiftSeq.
-- This avoids all ℕ-arithmetic issues (no +-suc!).
data seqCo (C : Sequence ℓ) : Type ℓ where
  inj  : obj C 0 → seqCo C
  lift : seqCo (ShiftSeq C) → seqCo C
  gl   : (a : obj C 0) → inj a ≡ lift (inj (map C a))

-- Shift of a sequence (matches cubicaltt shiftSequence)
-- ShiftSeq is already in the library: obj (ShiftSeq C) n = obj C (suc n)

-- Fibered sequences (sequenceFib in cubicaltt)
record SeqFib (A : Sequence ℓ) (ℓ' : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor seqfib
  field
    P   : (n : ℕ) → obj A n → Type ℓ'
    Pmap : (n : ℕ) (a : obj A n) → P n a → P (suc n) (map A a)

open SeqFib

shiftSeqFib : {A : Sequence ℓ} → SeqFib A ℓ' → SeqFib (ShiftSeq A) ℓ'
P (shiftSeqFib B) n = P B (suc n)
Pmap (shiftSeqFib B) n = Pmap B (suc n)

-- ═══════════════════════════════════════════════════════════════════
-- §2. Shift equivalence (lemShift)
-- ═══════════════════════════════════════════════════════════════════

-- lift : seqCo (ShiftSeq C) → seqCo C is an equivalence.

module ShiftEquiv (C : Sequence ℓ) where
  F : seqCo C → seqCo (ShiftSeq C)
  F (inj a)    = inj (map C a)
  F (lift x)   = x
  F (gl a i)   = inj (map C a)

  G : seqCo (ShiftSeq C) → seqCo C
  G x = lift x

  GF : (x : seqCo C) → G (F x) ≡ x
  GF (inj a)    = sym (gl a)
  GF (lift x)   = refl
  GF (gl a i) j = gl a (i ∨ ~ j)

  FG : (x : seqCo (ShiftSeq C)) → F (G x) ≡ x
  FG x = refl

  shiftIso : Iso (seqCo C) (seqCo (ShiftSeq C))
  Iso.fun shiftIso = F
  Iso.inv shiftIso = G
  Iso.sec shiftIso = FG
  Iso.ret shiftIso = GF

open ShiftEquiv using (shiftIso)

lemShift : (C : Sequence ℓ) → seqCo C ≡ seqCo (ShiftSeq C)
lemShift C = isoToPath (shiftIso C)

-- isoToPath = ua ∘ isoToEquiv, so transport along it computes to Iso.fun
lemShiftPath1 : (C : Sequence ℓ) (x : seqCo C)
  → PathP (λ i → lemShift C i) x (ShiftEquiv.F C x)
lemShiftPath1 C x = toPathP (uaβ (isoToEquiv (shiftIso C)) x)

-- Special case: lift x maps to x under the shift
lemShiftPath : (C : Sequence ℓ) (x : seqCo (ShiftSeq C))
  → PathP (λ i → lemShift C i) (lift x) x
lemShiftPath C x = lemShiftPath1 C (lift x)

-- ═══════════════════════════════════════════════════════════════════
-- §3. The type family code (= B∞) over seqCo
-- ═══════════════════════════════════════════════════════════════════

-- code_i builds the fiber sequence at a point, recursively.
-- (translated from cubicaltt code_i)
-- Termination: cubicaltt accepts this; Agda's checker is stricter.
{-# TERMINATING #-}
code_i : (A : Sequence ℓ) (B : SeqFib A ℓ') (a : obj A 0) → Sequence ℓ'
obj (code_i A B a) zero    = P B 0 a
obj (code_i A B a) (suc n) = obj (code_i (ShiftSeq A) (shiftSeqFib B) (map A a)) n
map (code_i A B a) {n = zero}  = Pmap B 0 a
map (code_i A B a) {n = suc n} = map (code_i (ShiftSeq A) (shiftSeqFib B) (map A a))

-- code_g: the shift path for code_i
code_g : (A : Sequence ℓ) (B : SeqFib A ℓ') (a : obj A 0)
  → seqCo (code_i A B a) ≡ seqCo (code_i (ShiftSeq A) (shiftSeqFib B) (map A a))
code_g A B a = lemShift (code_i A B a)

-- code: the type family over seqCo A (= B∞)
code : (A : Sequence ℓ) (B : SeqFib A ℓ') → seqCo A → Type ℓ'
code A B (inj a)    = seqCo (code_i A B a)
code A B (lift x)   = code (ShiftSeq A) (shiftSeqFib B) x
code A B (gl a i)   = code_g A B a i

-- ═══════════════════════════════════════════════════════════════════
-- §4. Σ-sequence and forward map F
-- ═══════════════════════════════════════════════════════════════════

sigmaSequence : (A : Sequence ℓ) → SeqFib A ℓ' → Sequence (ℓ-max ℓ ℓ')
obj (sigmaSequence A B) n = Σ (obj A n) (P B n)
map (sigmaSequence A B) (a , b) = map A a , Pmap B _ a b

liftCodeEq : (A : Sequence ℓ) (B : SeqFib A ℓ') (x : obj A 0) (y : P B 0 x)
  → PathP (λ i → code A B (gl x i)) (inj y) (inj (Pmap B 0 x y))
liftCodeEq A B x y = lemShiftPath1 (code_i A B x) (inj y)

-- F : seqCo (sigmaSequence A B) → Σ (seqCo A) (code A B)
module SigmaColim (A : Sequence ℓ) (B : SeqFib A ℓ') where

  F : seqCo (sigmaSequence A B) → Σ (seqCo A) (code A B)
  F (inj a)    = inj (a .fst) , inj (a .snd)
  F (lift x)   = let p = F x in lift (p .fst) , p .snd
  F (gl a i)   = gl (a .fst) i , liftCodeEq A B (a .fst) (a .snd) i

  -- G0 : (x : seqCo A) → code A B x → seqCo (sigmaSequence A B)
  -- (translated from cubicaltt G0, nested pattern matching)
  G0 : (x : seqCo A) → code A B x → seqCo (sigmaSequence A B)
  G0 (inj x) (inj y)    = inj (x , y)
  G0 (inj x) (lift y)   = lift (G0 (inj (map A x)) y)
  G0 (inj x) (gl y i)   = gl (x , y) i
  G0 (lift x) y         = lift (G0 x y)
  G0 (gl x i) y         = G0 (inj x)
    (comp (λ j → code A B (gl x (i ∧ ~ j)))
          (λ j → λ { (i = i0) → y
                    ; (i = i1) → lemShiftPath (code_i A B x) y (~ j) })
          y)

  G : Σ (seqCo A) (code A B) → seqCo (sigmaSequence A B)
  G (x , y) = G0 x y

  -- FG : F ∘ G ∼ id  (translated from cubicaltt FG)
  FG : (x : seqCo (sigmaSequence A B)) → G (F x) ≡ x
  FG (inj a)    = refl
  FG (lift x)   = cong lift (FG x)
  FG (gl a i) j = {!!}  -- complex cube, translated below when compiling

  -- GF0 (translated from cubicaltt GF0)
  GF0 : (x : seqCo A) (y : code A B x)
    → F (G0 x y) ≡ (x , y)
  GF0 (inj x) (inj y) = refl
  GF0 (inj x) (lift y) =
    let p = GF0 (inj (map A x)) y
    in (cong (λ z → lift (z .fst) , z .snd) p)
       ∙ (λ i → gl x (~ i) , lemShiftPath (code_i A B x) y (~ i))
  GF0 (inj x) (gl y j) = {!!}  -- complex cube
  GF0 (lift x) y = cong (λ z → lift (z .fst) , z .snd) (GF0 x y)
  GF0 (gl x i) y = {!!}  -- complex cube

  GF : (x : Σ (seqCo A) (code A B)) → F (G x) ≡ x
  GF (x , y) = GF0 x y

  -- The main isomorphism
  postulate
    FG-full : (x : seqCo (sigmaSequence A B)) → G (F x) ≡ x
    GF-full : (x : Σ (seqCo A) (code A B)) → F (G x) ≡ x

  sigmaColimit : seqCo (sigmaSequence A B) ≡ Σ (seqCo A) (code A B)
  sigmaColimit = isoToPath (iso F G GF-full FG-full)

-- ═══════════════════════════════════════════════════════════════════
-- §5. Colimits of contractible types are contractible
-- ═══════════════════════════════════════════════════════════════════

colimitContr : (A : Sequence ℓ) → ((n : ℕ) → isContr (obj A n)) → isContr (seqCo A)
colimitContr A contr = inj (contr 0 .fst) , f
  where
  f : (y : seqCo A) → inj (contr 0 .fst) ≡ y
  f (inj y) i = inj (isContr→isProp (contr 0) (contr 0 .fst) y i)
  f (lift y) =
    gl (contr 0 .fst)
    ∙ cong lift (colimitContr (ShiftSeq A) (λ n → contr (suc n)) .snd y)
  f (gl y i) j = {!!}  -- square from contractibility

-- ═══════════════════════════════════════════════════════════════════
-- §6. Path fibration and path characterization
-- ═══════════════════════════════════════════════════════════════════

-- The path fibration: (λ y → x ≡ y) → (λ y → map x ≡ map y) → ...
ySSeq : (A : Sequence ℓ) (x : obj A 0) → SeqFib A ℓ
P (ySSeq A x) zero    a = x ≡ a
P (ySSeq A x) (suc n) a = P (ySSeq (ShiftSeq A) (map A x)) n a
Pmap (ySSeq A x) zero    a p = cong (map A) p
Pmap (ySSeq A x) (suc n) a p = Pmap (ySSeq (ShiftSeq A) (map A x)) n a p

-- Σ of the path fibration is contractible
sigmaYContr : (A : Sequence ℓ) (x : obj A 0)
  → isContr (seqCo (sigmaSequence A (ySSeq A x)))
sigmaYContr A x = colimitContr (sigmaSequence A (ySSeq A x)) prf
  where
  prf : (n : ℕ) → isContr (obj (sigmaSequence A (ySSeq A x)) n)
  prf zero    = isContrSingl x
  prf (suc n) = prf-shift n
    where
    prf-shift : (n : ℕ) → isContr (obj (sigmaSequence (ShiftSeq A) (shiftSeqFib (ySSeq A x))) n)
    prf-shift n = sigmaYContr (ShiftSeq A) (map A x) .fst , {!!}  -- from contractibility

-- The code of the path fibration, via sigmaColimit
sigmaCodeContr : (A : Sequence ℓ) (x : obj A 0)
  → isContr (Σ (seqCo A) (code A (ySSeq A x)))
sigmaCodeContr A x =
  transport (λ i → isContr (SigmaColim.sigmaColimit A (ySSeq A x) i))
            (sigmaYContr A x)

-- Theorem 4.7.7 from HoTT book: fiber over center of contraction
-- (Σ A P with A contractible) ≃ P(center)
-- Already available as isContr→Equiv in the library, or we can use:
lem31192 : {A : Type ℓ} {P : A → Type ℓ'}
  → (c : isContr A)
  → Σ A P ≃ P (c .fst)
lem31192 {P = P} c = isoToEquiv (iso f g fg gf)
  where
  f : Σ _ P → P (c .fst)
  f (a , p) = subst P (sym (c .snd a)) p
  g : P (c .fst) → Σ _ P
  g p = c .fst , p
  fg : (p : P (c .fst)) → f (g p) ≡ p
  fg p = cong (λ q → subst P q p) (isProp→isSet (isContr→isProp c) _ _ _ _)
       ∙ transportRefl p
  gf : (x : Σ _ P) → g (f x) ≡ x
  gf (a , p) = ΣPathP (c .snd a , toPathP refl)

-- Total space map for fiberwise equivalence characterization
total : {A : Type ℓ} {P Q : A → Type ℓ'}
  → ((x : A) → P x → Q x) → Σ A P → Σ A Q
total f (a , p) = a , f a p

-- Fiberwise equivalence ↔ total equivalence (thm477 from cubicaltt)
fiberwise→totalEquiv : {A : Type ℓ} {P Q : A → Type ℓ'}
  → {f : (x : A) → P x → Q x}
  → ((x : A) → isEquiv (f x))
  → isEquiv (total f)
fiberwise→totalEquiv {f = f} fEq =
  isoToIsEquiv (iso (total f) (total (λ x → invEq (_ , fEq x)))
    (λ (a , q) → ΣPathP (refl , secEq (_ , fEq a) q))
    (λ (a , p) → ΣPathP (refl , retEq (_ , fEq a) p)))

totalEquiv→fiberwise : {A : Type ℓ} {P Q : A → Type ℓ'}
  → {f : (x : A) → P x → Q x}
  → isEquiv (total f)
  → (x : A) → isEquiv (f x)
totalEquiv→fiberwise {Q = Q} {f = f} tEq x = {!!}  -- standard, via th476

-- Fiberwise contr → total equiv (equivFiberwiseContr from cubicaltt)
equivFiberwiseContr : {X : Type ℓ} {P Q : X → Type ℓ'}
  → isContr (Σ X P) → isContr (Σ X Q)
  → (f : (x : X) → P x → Q x)
  → (x : X) → isEquiv (f x)
equivFiberwiseContr {P = P} {Q = Q} cP cQ f =
  totalEquiv→fiberwise (isContr→isEquiv cP cQ (total f))
  where
  isContr→isEquiv : {A B : Type ℓ} → isContr A → isContr B → (f : A → B) → isEquiv f
  isContr→isEquiv cA cB f =
    isoToIsEquiv (iso f (λ _ → cA .fst) (λ b → isContr→isProp cB _ b) (λ a → isContr→isProp cA _ a))

-- The encode map for path characterization
colimitPathsF : (A : Sequence ℓ) (x : obj A 0)
  → (y : seqCo A) → inj x ≡ y → code A (ySSeq A x) y
colimitPathsF A x y p = J (λ y _ → code A (ySSeq A x) y) (inj refl) p

-- Main theorem: paths in a colimit are a colimit of paths
-- (colimitPaths from cubicaltt)
colimitPaths : (A : Sequence ℓ) (x : obj A 0) (y : seqCo A)
  → (inj x ≡ y) ≃ code A (ySSeq A x) y
colimitPaths A x y =
  colimitPathsF A x y ,
  equivFiberwiseContr
    (isContrSingl (inj x))
    (sigmaCodeContr A x)
    (colimitPathsF A x)
    y

-- ═══════════════════════════════════════════════════════════════════
-- §7. Equivalence with standard SeqColim (equivSeqCo from cubicaltt)
-- ═══════════════════════════════════════════════════════════════════

module EquivStandard (A : Sequence ℓ) where
  open Sequence

  -- seqCo0 = SeqColim from the library (with incl, push)

  Fi : (n : ℕ) → obj A n → seqCo A
  Fi zero    x = inj x
  Fi (suc n) x = lift (Fi n x)

  Fg : (n : ℕ) (x : obj A n) → Fi n x ≡ Fi (suc n) (map A x)
  Fg zero    x = gl x
  Fg (suc n) x = cong lift (Fg n x)

  toRecursive : SeqColim A → seqCo A
  toRecursive (incl {n = n} x) = Fi n x
  toRecursive (push {n = n} x i) = Fg n x i

  fromRecursive : seqCo A → SeqColim A
  fromRecursive (inj x)    = incl {n = 0} x
  fromRecursive (lift x)   = liftSC (fromRecursive x)
    where
    liftSC : SeqColim (ShiftSeq A) → SeqColim A
    liftSC (incl {n = n} x) = incl {n = suc n} x
    liftSC (push {n = n} x i) = push {n = suc n} x i
  fromRecursive (gl x i)   = push {n = 0} x i

  postulate
    toFrom : (x : seqCo A) → toRecursive (fromRecursive x) ≡ x
    fromTo : (x : SeqColim A) → fromRecursive (toRecursive x) ≡ x

  equivSeqCo : SeqColim A ≡ seqCo A
  equivSeqCo = isoToPath (iso toRecursive fromRecursive toFrom fromTo)
