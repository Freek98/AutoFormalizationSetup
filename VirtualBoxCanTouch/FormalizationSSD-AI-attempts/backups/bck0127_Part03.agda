{-# OPTIONS --cubical --guardedness #-}

module work.Part03 where

open import work.Part02 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.DirectProd using (DirectProd-CommRing)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Bool using (Bool; true; false; _and_; true≢false)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; idBoolEquiv)
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

module B∞-construction where
  open import BooleanRing.FreeBooleanRing.FreeBool using (generator)
  open BooleanRingStr (snd (freeBA ℕ)) using (_·_ ; 𝟘)

  gen : ℕ → ⟨ freeBA ℕ ⟩
  gen = generator

  relB∞-from-pair : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  relB∞-from-pair (m , n) = gen m · gen (m +ℕ suc n)

  relB∞ : ℕ → ⟨ freeBA ℕ ⟩
  relB∞ k = relB∞-from-pair (cantorUnpair k)

  B∞ : BooleanRing ℓ-zero
  B∞ = freeBA ℕ QB./Im relB∞

  π∞ : BoolHom (freeBA ℕ) B∞
  π∞ = QB.quotientImageHom

  g∞ : ℕ → ⟨ B∞ ⟩
  g∞ n = fst π∞ (gen n)

  relB∞-is-zero : (k : ℕ) → fst π∞ (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞)
  relB∞-is-zero k = QB.zeroOnImage {B = freeBA ℕ} {f = relB∞} k

  open BooleanRingStr (snd B∞) renaming (_·_ to _·∞_ ; 𝟘 to 𝟘∞ ; 𝟙 to 𝟙∞)

open B∞-construction public

open BooleanRingStr (snd (freeBA ℕ)) using (_·_ ; 𝟘) public

open BooleanRingStr (snd B∞) renaming (_·_ to _·∞_ ; 𝟘 to 𝟘∞ ; 𝟙 to 𝟙∞) public

B∞-has-Boole-ω' : has-Boole-ω' B∞
B∞-has-Boole-ω' = relB∞ , idBoolEquiv B∞

B∞-Booleω : Booleω
B∞-Booleω = B∞ , ∣ B∞-has-Boole-ω' ∣₁

SpB∞-to-ℕ∞-seq : Sp B∞-Booleω → binarySequence
SpB∞-to-ℕ∞-seq h n = h $cr (g∞ n)

a+suc-d≡b : (a b : ℕ) → a < b → a +ℕ suc (b ∸ suc a) ≡ b
a+suc-d≡b a b a<b =
  let d = b ∸ suc a in
  a +ℕ suc d             ≡⟨ +-suc a d ⟩
  suc (a +ℕ d)           ≡⟨ cong suc (+-comm a d) ⟩
  suc (d +ℕ a)           ≡⟨ sym (+-suc d a) ⟩
  d +ℕ suc a             ≡⟨ ≤-∸-+-cancel a<b ⟩
  b ∎

relB∞-encodes : (a d : ℕ) → relB∞ (cantorPair a d) ≡ gen a · gen (a +ℕ suc d)
relB∞-encodes a d = cong relB∞-from-pair (cantorUnpair-pair a d)

open IsCommRingHom (snd π∞) renaming (pres· to π∞-pres·)

g∞-lt-mult-zero : (a b : ℕ) → a < b → g∞ a ·∞ g∞ b ≡ 𝟘∞
g∞-lt-mult-zero a b a<b =
  let d = b ∸ suc a
      k = cantorPair a d
  in
  g∞ a ·∞ g∞ b                        ≡⟨ sym (π∞-pres· (gen a) (gen b)) ⟩
  fst π∞ (gen a · gen b)              ≡⟨ cong (fst π∞) (cong (λ x → gen a · gen x) (sym (a+suc-d≡b a b a<b)) ∙ sym (relB∞-encodes a d)) ⟩
  fst π∞ (relB∞ k)                    ≡⟨ relB∞-is-zero k ⟩
  𝟘∞ ∎

g∞-distinct-mult-zero : (m n : ℕ) → ¬ (m ≡ n) →
  BooleanRingStr._·_ (snd B∞) (g∞ m) (g∞ n) ≡ BooleanRingStr.𝟘 (snd B∞)
g∞-distinct-mult-zero m n m≠n with Cubical.Data.Nat.Order.<Dec m n
... | yes m<n = g∞-lt-mult-zero m n m<n
... | no ¬m<n with Cubical.Data.Nat.Order.<Dec n m
...   | yes n<m =
  g∞ m ·∞ g∞ n
    ≡⟨ BooleanRingStr.·Comm (snd B∞) (g∞ m) (g∞ n) ⟩
  g∞ n ·∞ g∞ m
    ≡⟨ g∞-lt-mult-zero n m n<m ⟩
  𝟘∞ ∎
...   | no ¬n<m = ex-falso (m≠n (sym (≤-antisym (<-asym' ¬m<n) (<-asym' ¬n<m))))

SpB∞-seq-atMostOnce : (h : Sp B∞-Booleω) → hitsAtMostOnce (SpB∞-to-ℕ∞-seq h)
SpB∞-seq-atMostOnce h m n hm=true hn=true = m=n
  where
  open IsCommRingHom (snd h)

  m=n : m ≡ n
  m=n with discreteℕ m n
  ... | yes p = p
  ... | no m≠n =
    let
      and-is-false : (h $cr (g∞ m)) and (h $cr (g∞ n)) ≡ false
      and-is-false =
        (h $cr (g∞ m)) and (h $cr (g∞ n))
          ≡⟨ sym (pres· (g∞ m) (g∞ n)) ⟩
        h $cr (g∞ m ·∞ g∞ n)
          ≡⟨ cong (h $cr_) (g∞-distinct-mult-zero m n m≠n) ⟩
        h $cr 𝟘∞
          ≡⟨ IsCommRingHom.pres0 (snd h) ⟩
        false ∎
    in ex-falso (true≢false (cong₂ _and_ (sym hm=true) (sym hn=true) ∙ and-is-false))

SpB∞-to-ℕ∞ : Sp B∞-Booleω → ℕ∞
SpB∞-to-ℕ∞ h = SpB∞-to-ℕ∞-seq h , SpB∞-seq-atMostOnce h

module DirectProd-BooleanRing
  (A : BooleanRing ℓ-zero)
  (B : BooleanRing ℓ-zero)
  where

  private
    A-CR = BooleanRing→CommRing A
    B-CR = BooleanRing→CommRing B
    AB-CR = DirectProd-CommRing A-CR B-CR

  ·Idem-prod : (x : ⟨ A ⟩ × ⟨ B ⟩) →
    CommRingStr._·_ (snd AB-CR) x x ≡ x
  ·Idem-prod (a , b) =
    let open BooleanRingStr
        open CommRingStr (snd AB-CR)
    in cong₂ _,_ (BooleanRingStr.·Idem (snd A) a) (BooleanRingStr.·Idem (snd B) b)

  DirectProd-BooleanRing : BooleanRing ℓ-zero
  DirectProd-BooleanRing = idemCommRing→BR AB-CR ·Idem-prod

_×BR_ : BooleanRing ℓ-zero → BooleanRing ℓ-zero → BooleanRing ℓ-zero
A ×BR B = DirectProd-BooleanRing.DirectProd-BooleanRing A B

B∞×B∞ : BooleanRing ℓ-zero
B∞×B∞ = B∞ ×BR B∞

Bool² : BooleanRing ℓ-zero
Bool² = BoolBR ×BR BoolBR

Bool²-unit-left : ⟨ Bool² ⟩
Bool²-unit-left = true , false

Bool²-unit-right : ⟨ Bool² ⟩
Bool²-unit-right = false , true
