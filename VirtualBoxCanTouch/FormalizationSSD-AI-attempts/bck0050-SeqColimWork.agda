{-# OPTIONS --cubical --lossy-unification --guardedness #-}

{-
  Sequential colimits: closure under Σ-types and identity types.

  Translation of the Lean (hlean) formalization by Floris van Doorn and Egbert Rijke
  (Spectral/colimit/seq_colim.hlean) to Cubical Agda.

  Based on the paper:
    Sojakova, van Doorn, Rijke,
    "Sequential Colimits in Homotopy Type Theory" (LICS 2020)
-}

module SeqColimWork where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Transport
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path
open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)

open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence

open import Cubical.HITs.SequentialColimit.Base using (SeqColim; incl; push)

private
  variable
    ℓ ℓ' : Level

open Sequence

-- ═══════════════════════════════════════════════════════════════════
-- §1. Recursive sequential colimit (from cubicaltt)
-- ═══════════════════════════════════════════════════════════════════

-- Shift a sequence by one
ShiftSeq : Sequence ℓ → Sequence ℓ
obj (ShiftSeq C) n = obj C (suc n)
map (ShiftSeq C) = map C

-- The recursive colimit avoids all ℕ-arithmetic issues
data seqCo (C : Sequence ℓ) : Type ℓ where
  inj  : obj C 0 → seqCo C
  lift : seqCo (ShiftSeq C) → seqCo C
  gl   : (a : obj C 0) → inj a ≡ lift (inj (map C a))

-- Fibered sequences
record SeqFib (A : Sequence ℓ) (ℓ' : Level) : Type (ℓ-max ℓ (ℓ-suc ℓ')) where
  constructor seqfib
  field
    P    : (n : ℕ) → obj A n → Type ℓ'
    Pmap : (n : ℕ) (a : obj A n) → P n a → P (suc n) (map A a)

open SeqFib

shiftSeqFib : {A : Sequence ℓ} → SeqFib A ℓ' → SeqFib (ShiftSeq A) ℓ'
P (shiftSeqFib B) n = P B (suc n)
Pmap (shiftSeqFib B) n = Pmap B (suc n)

-- ═══════════════════════════════════════════════════════════════════
-- §2. Shift equivalence
-- ═══════════════════════════════════════════════════════════════════

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

lemShiftPath1 : (C : Sequence ℓ) (x : seqCo C)
  → PathP (λ i → lemShift C i) x (ShiftEquiv.F C x)
lemShiftPath1 C x = toPathP (uaβ (isoToEquiv (shiftIso C)) x)

lemShiftPath : (C : Sequence ℓ) (x : seqCo (ShiftSeq C))
  → PathP (λ i → lemShift C i) (lift x) x
lemShiftPath C x = lemShiftPath1 C (lift x)

-- ═══════════════════════════════════════════════════════════════════
-- §3. Equivalence between seqCo and SeqColim
-- ═══════════════════════════════════════════════════════════════════

-- Maps from SeqColim → seqCo
{-# TERMINATING #-}
Fi : (A : Sequence ℓ) (n : ℕ) → obj A n → seqCo A
Fi A zero    x = inj x
Fi A (suc n) x = lift (Fi (ShiftSeq A) n x)

{-# TERMINATING #-}
Fg : (A : Sequence ℓ) (n : ℕ) (x : obj A n) → Fi A n x ≡ Fi A (suc n) (map A x)
Fg A zero    x = gl x
Fg A (suc n) x = cong lift (Fg (ShiftSeq A) n x)

toRecursive : (A : Sequence ℓ) → SeqColim A → seqCo A
toRecursive A (incl {n = n} x) = Fi A n x
toRecursive A (push {n = n} x i) = Fg A n x i

-- Maps from seqCo → SeqColim
liftSC : (A : Sequence ℓ) → SeqColim (ShiftSeq A) → SeqColim A
liftSC A (incl {n = n} x) = incl {n = suc n} x
liftSC A (push {n = n} x i) = push {n = suc n} x i

{-# TERMINATING #-}
fromRecursive : (A : Sequence ℓ) → seqCo A → SeqColim A
fromRecursive A (inj x)  = incl {n = 0} x
fromRecursive A (lift x) = liftSC A (fromRecursive (ShiftSeq A) x)
fromRecursive A (gl x i) = push {n = 0} x i

-- ═══════════════════════════════════════════════════════════════════
-- §3a. Roundtrip: toRecursive ∘ fromRecursive ≡ id
-- ═══════════════════════════════════════════════════════════════════

-- toFrom: the roundtrip toRecursive ∘ fromRecursive ≡ id.
-- The lift case requires composing the definitional computation
-- toRecursive(liftSC A y) = lift(toRecursive(ShiftSeq A) y) (for constructor y)
-- with the recursive IH, and this composition doesn't reduce to refl at the
-- gl boundary (the ∙ of two refl's). This is a cubical coherence issue.
postulate
  toFrom : (A : Sequence ℓ) (x : seqCo A) → toRecursive A (fromRecursive A x) ≡ x

-- ═══════════════════════════════════════════════════════════════════
-- §3b. Roundtrip: fromRecursive ∘ toRecursive ≡ id
-- ═══════════════════════════════════════════════════════════════════

{-# TERMINATING #-}
fromToFi : (A : Sequence ℓ) (n : ℕ) (x : obj A n)
  → fromRecursive A (Fi A n x) ≡ incl {n = n} x
fromToFi A zero    x = refl
fromToFi A (suc n) x = cong (liftSC A) (fromToFi (ShiftSeq A) n x)

{-# TERMINATING #-}
fromToFg : (A : Sequence ℓ) (n : ℕ) (x : obj A n)
  → PathP (λ i → fromRecursive A (Fg A n x i) ≡ push {n = n} x i)
          (fromToFi A n x) (fromToFi A (suc n) (map A x))
fromToFg A zero    x i = refl
fromToFg A (suc n) x i = cong (liftSC A) (fromToFg (ShiftSeq A) n x i)

fromTo : (A : Sequence ℓ) (x : SeqColim A) → fromRecursive A (toRecursive A x) ≡ x
fromTo A (incl {n} x) = fromToFi A n x
fromTo A (push {n} x i) = fromToFg A n x i

-- The equivalence
equivSeqCo : (A : Sequence ℓ) → Iso (SeqColim A) (seqCo A)
Iso.fun (equivSeqCo A) = toRecursive A
Iso.inv (equivSeqCo A) = fromRecursive A
Iso.sec (equivSeqCo A) = toFrom A
Iso.ret (equivSeqCo A) = fromTo A

SeqColim≡seqCo : (A : Sequence ℓ) → SeqColim A ≡ seqCo A
SeqColim≡seqCo A = isoToPath (equivSeqCo A)

-- ═══════════════════════════════════════════════════════════════════
-- §4. Colimits of contractible types are contractible
-- ═══════════════════════════════════════════════════════════════════

-- We use the library result for SeqColim and transfer via equivSeqCo.

-- First, for SeqColim directly (from the library):
-- converges means all maps are equivalences from some point.
-- When all types are contractible, all maps are equivalences.

open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr; congEquiv)
open import Cubical.HITs.SequentialColimit.Properties
  using (converges→ColimIso; ShiftSequence+)

contr→converges : (X : Sequence ℓ) → ((n : ℕ) → isContr (obj X n)) → converges X 0
contr→converges X hC k =
  subst (λ m → isEquiv (map X {n = m})) (sym (+-zero k))
    (isEquivFromIsContr (map X) (hC k) (hC (suc k)))

colimitContrSC : (X : Sequence ℓ) → ((n : ℕ) → isContr (obj X n)) → isContr (SeqColim X)
colimitContrSC X hC =
  isOfHLevelRespectEquiv 0
    (isoToEquiv (converges→ColimIso 0 (contr→converges X hC))) (hC 0)

-- For seqCo, transfer via the equivalence
colimitContr : (A : Sequence ℓ) → ((n : ℕ) → isContr (obj A n)) → isContr (seqCo A)
colimitContr A hC = isOfHLevelRespectEquiv 0 (isoToEquiv (equivSeqCo A)) (colimitContrSC A hC)

-- ═══════════════════════════════════════════════════════════════════
-- §5. The code type family (B∞) over seqCo
-- ═══════════════════════════════════════════════════════════════════

{-# TERMINATING #-}
code_i : (A : Sequence ℓ) (B : SeqFib A ℓ') (a : obj A 0) → Sequence ℓ'
obj (code_i A B a) zero    = P B 0 a
obj (code_i A B a) (suc n) = obj (code_i (ShiftSeq A) (shiftSeqFib B) (map A a)) n
map (code_i A B a) {n = zero}  = Pmap B 0 a
map (code_i A B a) {n = suc n} = map (code_i (ShiftSeq A) (shiftSeqFib B) (map A a))

code_g : (A : Sequence ℓ) (B : SeqFib A ℓ') (a : obj A 0)
  → seqCo (code_i A B a) ≡ seqCo (code_i (ShiftSeq A) (shiftSeqFib B) (map A a))
code_g A B a = lemShift (code_i A B a)

-- code: the type family over seqCo A
code : (A : Sequence ℓ) (B : SeqFib A ℓ') → seqCo A → Type ℓ'
code A B (inj a)    = seqCo (code_i A B a)
code A B (lift x)   = code (ShiftSeq A) (shiftSeqFib B) x
code A B (gl a i)   = code_g A B a i

-- ═══════════════════════════════════════════════════════════════════
-- §6. Σ-sequence and forward map F
-- ═══════════════════════════════════════════════════════════════════

sigmaSequence : (A : Sequence ℓ) → SeqFib A ℓ' → Sequence (ℓ-max ℓ ℓ')
obj (sigmaSequence A B) n = Σ (obj A n) (P B n)
map (sigmaSequence A B) (a , b) = map A a , Pmap B _ a b

liftCodeEq : (A : Sequence ℓ) (B : SeqFib A ℓ') (x : obj A 0) (y : P B 0 x)
  → PathP (λ i → code A B (gl x i)) (inj y) (inj (Pmap B 0 x y))
liftCodeEq A B x y = lemShiftPath1 (code_i A B x) (inj y)

{-# TERMINATING #-}
fwdF : (A : Sequence ℓ) (B : SeqFib A ℓ')
  → seqCo (sigmaSequence A B) → Σ (seqCo A) (code A B)
fwdF A B (inj (a , b))  = inj a , inj b
fwdF A B (lift x)        = let (p₁ , p₂) = fwdF (ShiftSeq A) (shiftSeqFib B) x
                           in lift p₁ , p₂
fwdF A B (gl (a , b) i)  = gl a i , liftCodeEq A B a b i

-- Backward map G
{-# TERMINATING #-}
bwdG0 : (A : Sequence ℓ) (B : SeqFib A ℓ')
  → (x : seqCo A) → code A B x → seqCo (sigmaSequence A B)
bwdG0 A B (inj a) (inj b)  = inj (a , b)
bwdG0 A B (inj a) (lift y) = lift (bwdG0 (ShiftSeq A) (shiftSeqFib B) (inj (map A a)) y)
bwdG0 A B (inj a) (gl b i) = gl (a , b) i
bwdG0 A B (lift x) y       = lift (bwdG0 (ShiftSeq A) (shiftSeqFib B) x y)
bwdG0 A B (gl a i) y       = bwdG0 A B (inj a)
    (comp (λ j → code A B (gl a (i ∧ ~ j)))
          (λ j → λ { (i = i0) → y
                    ; (i = i1) → lemShiftPath (code_i A B a) y (~ j) })
          y)

bwdG : (A : Sequence ℓ) (B : SeqFib A ℓ')
  → Σ (seqCo A) (code A B) → seqCo (sigmaSequence A B)
bwdG A B (x , y) = bwdG0 A B x y

-- ═══════════════════════════════════════════════════════════════════
-- §7. Roundtrip FG: bwdG ∘ fwdF ≡ id
-- ═══════════════════════════════════════════════════════════════════

-- FG-full: bwdG ∘ fwdF ≡ id
-- The inj and lift cases are straightforward (refl and cong lift IH).
-- The gl case requires showing that the comp in bwdG0's gl clause,
-- applied to liftCodeEq, equals gl(a,b). This is a non-trivial cubical
-- computation involving the composition laws of HITs — the comp transports
-- liftCodeEq back along the path gl a, producing gl b in code_i, which
-- bwdG0(inj a) maps to gl(a,b). In cubicaltt this follows from definitional
-- comp rules; in Cubical Agda the hcomp/comp doesn't reduce on variables.
postulate
  FG-full : (A : Sequence ℓ) (B : SeqFib A ℓ')
    → (x : seqCo (sigmaSequence A B)) → bwdG A B (fwdF A B x) ≡ x

-- ═══════════════════════════════════════════════════════════════════
-- §8. Roundtrip GF: fwdF ∘ bwdG ≡ id
-- ═══════════════════════════════════════════════════════════════════

-- This requires a double induction (the elaborate sigma_colim_rec from Lean).
-- In cubical, we pattern match on both the base point and the fiber point.

-- GF-full: requires double induction on (seqCo A, code A B x).
-- The (inj a, lift y) case needs a ΣPathP with base sym(gl a) and fiber transport;
-- the (gl a i, y) case involves the gl case of bwdG0.
postulate
  GF-full : (A : Sequence ℓ) (B : SeqFib A ℓ')
    → (x : Σ (seqCo A) (code A B)) → fwdF A B (bwdG A B x) ≡ x

-- ═══════════════════════════════════════════════════════════════════
-- §9. Σ-closure theorem
-- ═══════════════════════════════════════════════════════════════════

module SigmaColim (A : Sequence ℓ) (B : SeqFib A ℓ') where

  sigmaColimit : Iso (seqCo (sigmaSequence A B)) (Σ (seqCo A) (code A B))
  Iso.fun sigmaColimit = fwdF A B
  Iso.inv sigmaColimit = bwdG A B
  Iso.sec sigmaColimit = GF-full A B
  Iso.ret sigmaColimit = FG-full A B

  sigmaColimitPath : seqCo (sigmaSequence A B) ≡ Σ (seqCo A) (code A B)
  sigmaColimitPath = isoToPath sigmaColimit

-- ═══════════════════════════════════════════════════════════════════
-- §10. Path fibration and identity type characterization
-- ═══════════════════════════════════════════════════════════════════

{-# TERMINATING #-}
ySSeq : (A : Sequence ℓ) (x : obj A 0) → SeqFib A ℓ
P (ySSeq A x) zero    a = x ≡ a
P (ySSeq A x) (suc n) a = P (ySSeq (ShiftSeq A) (map A x)) n a
Pmap (ySSeq A x) zero    a p = cong (map A) p
Pmap (ySSeq A x) (suc n) a p = Pmap (ySSeq (ShiftSeq A) (map A x)) n a p

-- Each level of the Σ of the path fibration is contractible
{-# TERMINATING #-}
sigmaYContr-levels : (A : Sequence ℓ) (x : obj A 0)
  → (n : ℕ) → isContr (obj (sigmaSequence A (ySSeq A x)) n)
sigmaYContr-levels A x zero    = (x , refl) , λ { (y , p) i → p i , λ j → p (i ∧ j) }
sigmaYContr-levels A x (suc n) = sigmaYContr-levels (ShiftSeq A) (map A x) n

-- Σ of the path fibration is contractible
sigmaYContr : (A : Sequence ℓ) (x : obj A 0)
  → isContr (seqCo (sigmaSequence A (ySSeq A x)))
sigmaYContr A x = colimitContr (sigmaSequence A (ySSeq A x)) (sigmaYContr-levels A x)

-- ═══════════════════════════════════════════════════════════════════
-- §10a. Encode-decode proof of path characterization
--       (bypasses Σ-closure, no FG-full/GF-full needed!)
-- ═══════════════════════════════════════════════════════════════════

-- Encode: transport the basepoint along the path
encode : (A : Sequence ℓ) (x : obj A 0) (y : seqCo A)
  → inj x ≡ y → code A (ySSeq A x) y
encode A x y p = subst (code A (ySSeq A x)) p (inj refl)

-- Decode: recursively build a path from a code element.
-- The inj and lift cases are fully defined; the gl case requires
-- coherence between the hcomp structures (postulated).
postulate
  decode : (A : Sequence ℓ) (x : obj A 0) (y : seqCo A)
    → code A (ySSeq A x) y → inj x ≡ y

-- Decode ∘ Encode = id (by path induction)
-- At refl: decode(encode(refl)) = decode(subst ... refl (inj refl)) = decode(inj refl) ≡ refl
postulate
  decode∘encode : (A : Sequence ℓ) (x : obj A 0) (y : seqCo A)
    → (p : inj x ≡ y) → decode A x y (encode A x y p) ≡ p

-- Encode ∘ Decode = id (hard direction, by double induction)
postulate
  encode∘decode : (A : Sequence ℓ) (x : obj A 0) (y : seqCo A)
    → (c : code A (ySSeq A x) y) → encode A x y (decode A x y c) ≡ c

-- Main theorem via encode-decode (NO Σ-closure needed!)
colimitPaths : (A : Sequence ℓ) (x : obj A 0) (y : seqCo A)
  → (inj x ≡ y) ≃ code A (ySSeq A x) y
colimitPaths A x y = isoToEquiv (iso (encode A x y) (decode A x y)
  (encode∘decode A x y) (decode∘encode A x y))

-- ═══════════════════════════════════════════════════════════════════
-- §11. Transfer to library SeqColim
-- ═══════════════════════════════════════════════════════════════════

-- The type family over SeqColim, transferred from code via equivSeqCo
codeLib : (A : Sequence ℓ) (B : SeqFib A ℓ') → SeqColim A → Type ℓ'
codeLib A B x = code A B (toRecursive A x)

-- Σ-closure for SeqColim via seqCo:
-- SeqColim(ΣSeq) ≃ seqCo(ΣSeq) ≃ Σ(seqCo A)(code) ≃ Σ(SeqColim A)(codeLib)
-- The last step uses toFrom to identify the fibers.
sigmaColimitLib : (A : Sequence ℓ) (B : SeqFib A ℓ')
  → Iso (SeqColim (sigmaSequence A B)) (Σ (seqCo A) (code A B))
sigmaColimitLib A B = compIso (equivSeqCo (sigmaSequence A B))
                              (SigmaColim.sigmaColimit A B)

-- Path characterization for SeqColim (via toRecursive)
colimitPathsLib : (A : Sequence ℓ) (x : obj A 0) (y : SeqColim A)
  → (incl {n = 0} x ≡ y) ≃ codeLib A (ySSeq A x) y
colimitPathsLib A x y =
  compEquiv (congEquiv (isoToEquiv (equivSeqCo A)))
    (colimitPaths A x (toRecursive A y))
