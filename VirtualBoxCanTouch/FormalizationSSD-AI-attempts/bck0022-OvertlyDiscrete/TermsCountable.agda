{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OvertlyDiscrete.TermsCountable where

-- Proof that freeBATerms ℕ has a surjection from ℕ.
-- We encode terms as natural numbers using the Cantor pairing function,
-- and decode with a fuel parameter for termination.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Nat using (ℕ; zero; suc; max)
open import Cubical.Data.Nat.Order using (left-≤-max; right-≤-max; ≤-refl; _≤_; ≤-suc; ≤-trans)
open import Cubical.Data.Bool using (Bool; true; false)
open import Cubical.Data.Sigma

open import Cubical.Functions.Surjection
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import Cubical.Algebra.CommRing.Instances.Bool using (BoolCR)

open import BooleanRing.FreeBooleanRing.SurjectiveTerms
open import BooleanRing.FreeBooleanRing.freeBATerms

open Iso

private
  pair : ℕ × ℕ → ℕ
  pair = fun ℕ×ℕ≅ℕ

  unpair : ℕ → ℕ × ℕ
  unpair = inv ℕ×ℕ≅ℕ

  up : (x : ℕ × ℕ) → unpair (pair x) ≡ x
  up = ret ℕ×ℕ≅ℕ

-- ════════════════════════════════════════════════════════════════
-- Decoding
-- ════════════════════════════════════════════════════════════════

default : freeBATerms ℕ
default = Tconst false

-- Top-level dispatch on (fuel, tag, arg)
decodeWith : ℕ → ℕ → ℕ → freeBATerms ℕ

decode : ℕ → ℕ → freeBATerms ℕ
decode fuel n = decodeWith fuel (fst (unpair n)) (snd (unpair n))

decodeWith zero _ _ = default
decodeWith (suc _) zero a = Tvar a
decodeWith (suc _) (suc zero) zero = Tconst false
decodeWith (suc _) (suc zero) (suc _) = Tconst true
decodeWith (suc f) (suc (suc zero)) a =
  decode f (fst (unpair a)) +T decode f (snd (unpair a))
decodeWith (suc f) (suc (suc (suc zero))) a = -T decode f a
decodeWith (suc f) (suc (suc (suc (suc zero)))) a =
  decode f (fst (unpair a)) ·T decode f (snd (unpair a))
decodeWith (suc _) _ _ = default

-- ════════════════════════════════════════════════════════════════
-- Encoding
-- ════════════════════════════════════════════════════════════════

encode : freeBATerms ℕ → ℕ
encode (Tvar n)       = pair (0 , n)
encode (Tconst false) = pair (1 , 0)
encode (Tconst true)  = pair (1 , 1)
encode (t +T s)       = pair (2 , pair (encode t , encode s))
encode (-T t)         = pair (3 , encode t)
encode (t ·T s)       = pair (4 , pair (encode t , encode s))

-- ════════════════════════════════════════════════════════════════
-- Depth
-- ════════════════════════════════════════════════════════════════

depth : freeBATerms ℕ → ℕ
depth (Tvar _)   = 1
depth (Tconst _) = 1
depth (t +T s)   = suc (max (depth t) (depth s))
depth (-T t)     = suc (depth t)
depth (t ·T s)   = suc (max (depth t) (depth s))

-- ════════════════════════════════════════════════════════════════
-- Helper: rewriting through the pairing roundtrip
-- ════════════════════════════════════════════════════════════════

private
  rd : (fuel : ℕ) (tag arg : ℕ)
    → decode fuel (pair (tag , arg)) ≡ decodeWith fuel tag arg
  rd fuel tag arg =
    cong₂ (decodeWith fuel)
      (cong fst (up (tag , arg)))
      (cong snd (up (tag , arg)))

-- ════════════════════════════════════════════════════════════════
-- Roundtrip: decode f (encode t) ≡ t for any f ≥ depth t
-- ════════════════════════════════════════════════════════════════

-- Proved by induction on t. The key: for compound terms,
-- the sub-terms have smaller depth, and the available fuel
-- (f - 1) is enough since depth(sub) ≤ max(...) ≤ f - 1.

open import Cubical.Data.Nat.Order using (pred-≤-pred; ¬-<-zero)
open import Cubical.Data.Empty as ⊥ using ()

roundtrip : (t : freeBATerms ℕ) (f : ℕ) → depth t ≤ f → decode f (encode t) ≡ t
roundtrip (Tvar _)   zero p = ⊥.rec (¬-<-zero p)
roundtrip (Tconst _) zero p = ⊥.rec (¬-<-zero p)
roundtrip (_ +T _)   zero p = ⊥.rec (¬-<-zero p)
roundtrip (-T _)     zero p = ⊥.rec (¬-<-zero p)
roundtrip (_ ·T _)   zero p = ⊥.rec (¬-<-zero p)
roundtrip (Tvar n) (suc f) _ = rd (suc f) 0 n
roundtrip (Tconst false) (suc f) _ = rd (suc f) 1 0
roundtrip (Tconst true) (suc f) _ = rd (suc f) 1 1
roundtrip (t +T s) (suc f) p =
  decode (suc f) (pair (2 , pair (encode t , encode s)))
    ≡⟨ rd (suc f) 2 (pair (encode t , encode s)) ⟩
  decode f (fst (unpair (pair (encode t , encode s)))) +T
  decode f (snd (unpair (pair (encode t , encode s))))
    ≡⟨ cong₂ (λ a b → decode f a +T decode f b)
         (cong fst (up (encode t , encode s)))
         (cong snd (up (encode t , encode s))) ⟩
  decode f (encode t) +T decode f (encode s)
    ≡⟨ cong₂ _+T_ (roundtrip t f (≤-trans left-≤-max (pred-≤-pred p)))
                   (roundtrip s f (≤-trans right-≤-max (pred-≤-pred p))) ⟩
  t +T s ∎
roundtrip (-T t) (suc f) p =
  decode (suc f) (pair (3 , encode t))
    ≡⟨ rd (suc f) 3 (encode t) ⟩
  -T decode f (encode t)
    ≡⟨ cong -T_ (roundtrip t f (pred-≤-pred p)) ⟩
  -T t ∎
roundtrip (t ·T s) (suc f) p =
  decode (suc f) (pair (4 , pair (encode t , encode s)))
    ≡⟨ rd (suc f) 4 (pair (encode t , encode s)) ⟩
  decode f (fst (unpair (pair (encode t , encode s)))) ·T
  decode f (snd (unpair (pair (encode t , encode s))))
    ≡⟨ cong₂ (λ a b → decode f a ·T decode f b)
         (cong fst (up (encode t , encode s)))
         (cong snd (up (encode t , encode s))) ⟩
  decode f (encode t) ·T decode f (encode s)
    ≡⟨ cong₂ _·T_ (roundtrip t f (≤-trans left-≤-max (pred-≤-pred p)))
                   (roundtrip s f (≤-trans right-≤-max (pred-≤-pred p))) ⟩
  t ·T s ∎

-- ════════════════════════════════════════════════════════════════
-- The surjection ℕ → freeBATerms ℕ
-- ════════════════════════════════════════════════════════════════

decodeSurj : ℕ → freeBATerms ℕ
decodeSurj n = decode (fst (unpair n)) (snd (unpair n))

decodeSurj-surjective : isSurjection decodeSurj
decodeSurj-surjective t = ∣ pair (depth t , encode t) , proof ∣₁
  where
  proof : decodeSurj (pair (depth t , encode t)) ≡ t
  proof =
    decode (fst (unpair (pair (depth t , encode t))))
           (snd (unpair (pair (depth t , encode t))))
      ≡⟨ cong₂ decode (cong fst (up _)) (cong snd (up _)) ⟩
    decode (depth t) (encode t)
      ≡⟨ roundtrip t (depth t) ≤-refl ⟩
    t ∎

freeBATerms-surj : Σ[ e ∈ (ℕ → freeBATerms ℕ) ] isSurjection e
freeBATerms-surj = decodeSurj , decodeSurj-surjective
