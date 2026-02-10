{-# OPTIONS --cubical --guardedness #-}

module work.Part05 where

open import work.Part04 public
open import work.Part05a using (f-injective-05a ; char2-B∞ ; char2-B∞×B∞) public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; _and_; true≢false; false≢true; isSetBool)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import Cubical.Functions.Embedding using (isEmbedding→Inj)
open import Cubical.Data.Sum.Properties using (isEmbedding-inl; isEmbedding-inr)
open import Cubical.Data.List using (List; []; _∷_; ¬cons≡nil)
open import Cubical.Data.Bool.Properties using (⊕-comm)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isSetΠ)

module B∞×B∞-Units where
  open BooleanRingStr (snd B∞×B∞) using () renaming (𝟙 to 𝟙×)
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

  unit-left : ⟨ B∞×B∞ ⟩
  unit-left = (𝟙B∞ , 𝟘∞)

  unit-right : ⟨ B∞×B∞ ⟩
  unit-right = (𝟘∞ , 𝟙B∞)

  unit-sum : unit-left ·× unit-right ≡ (𝟘∞ , 𝟘∞)
  unit-sum = cong₂ _,_ (0∞-absorbs-right 𝟙B∞) (0∞-absorbs-left 𝟙B∞)

open B∞×B∞-Units

module B∞×B∞-Presentation where
  open Iso

  ≮→≥ : {a b : ℕ} → ¬ (a < b) → b ≤ a
  ≮→≥ {zero} {zero} _ = ≤-refl
  ≮→≥ {zero} {suc b} ¬0<sb = ex-falso (¬0<sb (suc-≤-suc zero-≤))
  ≮→≥ {suc a} {zero} _ = zero-≤
  ≮→≥ {suc a} {suc b} ¬sa<sb = suc-≤-suc (≮→≥ (λ a<b → ¬sa<sb (suc-≤-suc a<b)))

  encode× : ℕ ⊎ ℕ → ℕ
  encode× = fun ℕ⊎ℕ≅ℕ

  decode× : ℕ → ℕ ⊎ ℕ
  decode× = inv ℕ⊎ℕ≅ℕ

  encode×∘decode× : (n : ℕ) → encode× (decode× n) ≡ n
  encode×∘decode× = sec ℕ⊎ℕ≅ℕ

  decode×∘encode× : (x : ℕ ⊎ ℕ) → decode× (encode× x) ≡ x
  decode×∘encode× = ret ℕ⊎ℕ≅ℕ

  genProd⊎ : ℕ ⊎ ℕ → ⟨ B∞×B∞ ⟩
  genProd⊎ (⊎.inl n) = (g∞ n , 𝟘∞)
  genProd⊎ (⊎.inr n) = (𝟘∞ , g∞ n)

  genProd : ℕ → ⟨ B∞×B∞ ⟩
  genProd n = genProd⊎ (decode× n)

  genProd⊎-orthog : (x y : ℕ ⊎ ℕ) → ¬ (x ≡ y) → genProd⊎ x ·× genProd⊎ y ≡ (𝟘∞ , 𝟘∞)
  genProd⊎-orthog (⊎.inl m) (⊎.inl n) m≠n =
    let m≠n' : ¬ (m ≡ n)
        m≠n' meq = m≠n (cong ⊎.inl meq)
    in cong₂ _,_ (g∞-distinct-mult-zero m n m≠n') (0∞-absorbs-left 𝟘∞)
  genProd⊎-orthog (⊎.inl m) (⊎.inr n) _ =
    inl-inr-mult-zero (g∞ m) (g∞ n)
  genProd⊎-orthog (⊎.inr m) (⊎.inl n) _ =
    inr-inl-mult-zero (g∞ m) (g∞ n)
  genProd⊎-orthog (⊎.inr m) (⊎.inr n) m≠n =
    let m≠n' : ¬ (m ≡ n)
        m≠n' meq = m≠n (cong ⊎.inr meq)
    in cong₂ _,_ (0∞-absorbs-left 𝟘∞) (g∞-distinct-mult-zero m n m≠n')

  genProd-orthog : (m n : ℕ) → ¬ (m ≡ n) → genProd m ·× genProd n ≡ (𝟘∞ , 𝟘∞)
  genProd-orthog m n m≠n = genProd⊎-orthog (decode× m) (decode× n) decode-neq
    where
    decode-neq : ¬ (decode× m ≡ decode× n)
    decode-neq deq = m≠n (
      m                    ≡⟨ sym (encode×∘decode× m) ⟩
      encode× (decode× m)  ≡⟨ cong encode× deq ⟩
      encode× (decode× n)  ≡⟨ encode×∘decode× n ⟩
      n                    ∎)

  relB∞×B∞-from-pair : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  relB∞×B∞-from-pair (m , d) = gen m · gen (m +ℕ suc d)

  relB∞×B∞ : ℕ → ⟨ freeBA ℕ ⟩
  relB∞×B∞ k = relB∞×B∞-from-pair (cantorUnpair k)

  B∞×B∞-quotient : BooleanRing ℓ-zero
  B∞×B∞-quotient = freeBA ℕ QB./Im relB∞×B∞

  π× : BoolHom (freeBA ℕ) B∞×B∞-quotient
  π× = QB.quotientImageHom

  g× : ℕ → ⟨ B∞×B∞-quotient ⟩
  g× n = fst π× (gen n)

  genProd-free : BoolHom (freeBA ℕ) B∞×B∞
  genProd-free = inducedBAHom ℕ B∞×B∞ genProd

  genProd-free-on-gen : fst genProd-free ∘ generator ≡ genProd
  genProd-free-on-gen = evalBAInduce ℕ B∞×B∞ genProd

  m≠m+suc-d : (m d : ℕ) → ¬ (m ≡ m +ℕ suc d)
  m≠m+suc-d zero d meq = snotz (sym meq)
  m≠m+suc-d (suc m) d meq = m≠m+suc-d m d (injSuc meq)

  i+suc[j∸suc-i]≡j : (i j : ℕ) → i < j → i +ℕ suc (j ∸ suc i) ≡ j
  i+suc[j∸suc-i]≡j i zero (k , p) = ex-falso (¬-<-zero (k , p))
  i+suc[j∸suc-i]≡j i (suc j) (k , p) =
    let eq : k +ℕ i ≡ j
        eq = injSuc (sym (+-suc k i) ∙ p)
        i≤j : i ≤ j
        i≤j = k , eq
    in i +ℕ suc (j ∸ i)
         ≡⟨ +-suc i (j ∸ i) ⟩
       suc (i +ℕ (j ∸ i))
         ≡⟨ cong suc (+-comm i (j ∸ i)) ⟩
       suc ((j ∸ i) +ℕ i)
         ≡⟨ cong suc (≤-∸-+-cancel i≤j) ⟩
       suc j ∎

  genProd-respects-rel-pair : (p : ℕ × ℕ) → fst genProd-free (relB∞×B∞-from-pair p) ≡ (𝟘∞ , 𝟘∞)
  genProd-respects-rel-pair (m , d) =
    let n = m +ℕ suc d
        m≠n = m≠m+suc-d m d
    in fst genProd-free (gen m · gen n)
         ≡⟨ IsCommRingHom.pres· (snd genProd-free) (gen m) (gen n) ⟩
       fst genProd-free (gen m) ·× fst genProd-free (gen n)
         ≡⟨ cong₂ _·×_ (funExt⁻ genProd-free-on-gen m) (funExt⁻ genProd-free-on-gen n) ⟩
       genProd m ·× genProd n
         ≡⟨ genProd-orthog m n m≠n ⟩
       (𝟘∞ , 𝟘∞) ∎

  genProd-respects-rel : (k : ℕ) → fst genProd-free (relB∞×B∞ k) ≡ (𝟘∞ , 𝟘∞)
  genProd-respects-rel k = genProd-respects-rel-pair (cantorUnpair k)

  φ : BoolHom B∞×B∞-quotient B∞×B∞
  φ = QB.inducedHom B∞×B∞ genProd-free genProd-respects-rel

  φ-on-g× : (n : ℕ) → fst φ (g× n) ≡ genProd n
  φ-on-g× n = funExt⁻ (cong fst (QB.evalInduce B∞×B∞ genProd-free genProd-respects-rel)) (gen n) ∙ funExt⁻ genProd-free-on-gen n

  g×-left-gen : ℕ → ⟨ B∞×B∞-quotient ⟩
  g×-left-gen n = g× (encode× (⊎.inl n))

  g×-right-gen : ℕ → ⟨ B∞×B∞-quotient ⟩
  g×-right-gen n = g× (encode× (⊎.inr n))

  ψ-left-free : BoolHom (freeBA ℕ) B∞×B∞-quotient
  ψ-left-free = inducedBAHom ℕ B∞×B∞-quotient g×-left-gen

  ψ-left-free-on-gen : fst ψ-left-free ∘ generator ≡ g×-left-gen
  ψ-left-free-on-gen = evalBAInduce ℕ B∞×B∞-quotient g×-left-gen

  encode×-inl-injective : (m n : ℕ) → encode× (⊎.inl m) ≡ encode× (⊎.inl n) → m ≡ n
  encode×-inl-injective m n = λ eq → isEmbedding→Inj isEmbedding-inl m n (
    ⊎.inl m            ≡⟨ sym (decode×∘encode× (⊎.inl m)) ⟩
    decode× (encode× (⊎.inl m))  ≡⟨ cong decode× eq ⟩
    decode× (encode× (⊎.inl n))  ≡⟨ decode×∘encode× (⊎.inl n) ⟩
    ⊎.inl n            ∎)

  g×-left-orthog : (m n : ℕ) → ¬ (m ≡ n) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-left-gen m) (g×-left-gen n) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-left-orthog m n m≠n =
    let i = encode× (⊎.inl m)
        j = encode× (⊎.inl n)
        i≠j : ¬ (i ≡ j)
        i≠j = λ eq → m≠n (encode×-inl-injective m n eq)
    in g×-orthog i j i≠j
    where
    g×-orthog-base : (i j : ℕ) → i < j →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-base i j i<j =
      let k = cantorPair i (j ∸ suc i)
          rel-eq : relB∞×B∞ k ≡ gen i · gen j
          rel-eq = cong relB∞×B∞-from-pair (cantorUnpair-pair i (j ∸ suc i))
                 ∙ cong (λ x → gen i · gen x) (i+suc[j∸suc-i]≡j i j i<j)
      in sym (IsCommRingHom.pres· (snd π×) (gen i) (gen j))
         ∙ cong (fst π×) (sym rel-eq)
         ∙ QB.zeroOnImage k

    g×-orthog : (i j : ℕ) → ¬ (i ≡ j) →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog i j i≠j with Cubical.Data.Nat.Order.<Dec i j
    ... | yes i<j = g×-orthog-base i j i<j
    ... | no ¬i<j with Cubical.Data.Nat.Order.<Dec j i
    ...   | yes j<i =
            BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g× i) (g× j)
            ∙ g×-orthog-base j i j<i
    ...   | no ¬j<i =
            ex-falso (i≠j (≤-antisym (≮→≥ ¬j<i) (≮→≥ ¬i<j)))

  ψ-left-respects-relB∞ : (k : ℕ) → fst ψ-left-free (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  ψ-left-respects-relB∞ k =
    let (m , d) = cantorUnpair k
        n = m +ℕ suc d
        m≠n = m≠m+suc-d m d
    in fst ψ-left-free (gen m · gen n)
         ≡⟨ IsCommRingHom.pres· (snd ψ-left-free) (gen m) (gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (fst ψ-left-free (gen m)) (fst ψ-left-free (gen n))
         ≡⟨ cong₂ (BooleanRingStr._·_ (snd B∞×B∞-quotient))
                  (funExt⁻ ψ-left-free-on-gen m) (funExt⁻ ψ-left-free-on-gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-left-gen m) (g×-left-gen n)
         ≡⟨ g×-left-orthog m n m≠n ⟩
       BooleanRingStr.𝟘 (snd B∞×B∞-quotient) ∎

  ψ-left : BoolHom B∞ B∞×B∞-quotient
  ψ-left = QB.inducedHom B∞×B∞-quotient ψ-left-free ψ-left-respects-relB∞

  ψ-right-free : BoolHom (freeBA ℕ) B∞×B∞-quotient
  ψ-right-free = inducedBAHom ℕ B∞×B∞-quotient g×-right-gen

  encode×-inr-injective : (m n : ℕ) → encode× (⊎.inr m) ≡ encode× (⊎.inr n) → m ≡ n
  encode×-inr-injective m n = λ eq → isEmbedding→Inj isEmbedding-inr m n (
    ⊎.inr m            ≡⟨ sym (decode×∘encode× (⊎.inr m)) ⟩
    decode× (encode× (⊎.inr m))  ≡⟨ cong decode× eq ⟩
    decode× (encode× (⊎.inr n))  ≡⟨ decode×∘encode× (⊎.inr n) ⟩
    ⊎.inr n            ∎)

  ψ-right-free-on-gen : fst ψ-right-free ∘ generator ≡ g×-right-gen
  ψ-right-free-on-gen = evalBAInduce ℕ B∞×B∞-quotient g×-right-gen

  g×-right-orthog : (m n : ℕ) → ¬ (m ≡ n) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-right-gen m) (g×-right-gen n) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-right-orthog m n m≠n =
    let i = encode× (⊎.inr m)
        j = encode× (⊎.inr n)
        i≠j : ¬ (i ≡ j)
        i≠j = λ eq → m≠n (encode×-inr-injective m n eq)
    in g×-orthog-helper i j i≠j
    where
    g×-orthog-helper-base : (i j : ℕ) → i < j →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-helper-base i j i<j =
      let k = cantorPair i (j ∸ suc i)
          rel-eq : relB∞×B∞ k ≡ gen i · gen j
          rel-eq = cong relB∞×B∞-from-pair (cantorUnpair-pair i (j ∸ suc i))
                 ∙ cong (λ x → gen i · gen x) (i+suc[j∸suc-i]≡j i j i<j)
      in sym (IsCommRingHom.pres· (snd π×) (gen i) (gen j))
         ∙ cong (fst π×) (sym rel-eq)
         ∙ QB.zeroOnImage k

    g×-orthog-helper : (i j : ℕ) → ¬ (i ≡ j) →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-helper i j i≠j with Cubical.Data.Nat.Order.<Dec i j
    ... | yes i<j = g×-orthog-helper-base i j i<j
    ... | no ¬i<j with Cubical.Data.Nat.Order.<Dec j i
    ...   | yes j<i =
            BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g× i) (g× j)
            ∙ g×-orthog-helper-base j i j<i
    ...   | no ¬j<i =
            ex-falso (i≠j (≤-antisym (≮→≥ ¬j<i) (≮→≥ ¬i<j)))

  ψ-right-respects-relB∞ : (k : ℕ) → fst ψ-right-free (relB∞ k) ≡ BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  ψ-right-respects-relB∞ k =
    let (m , d) = cantorUnpair k
        n = m +ℕ suc d
        m≠n = m≠m+suc-d m d
    in fst ψ-right-free (gen m · gen n)
         ≡⟨ IsCommRingHom.pres· (snd ψ-right-free) (gen m) (gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (fst ψ-right-free (gen m)) (fst ψ-right-free (gen n))
         ≡⟨ cong₂ (BooleanRingStr._·_ (snd B∞×B∞-quotient))
                  (funExt⁻ ψ-right-free-on-gen m) (funExt⁻ ψ-right-free-on-gen n) ⟩
       BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-right-gen m) (g×-right-gen n)
         ≡⟨ g×-right-orthog m n m≠n ⟩
       BooleanRingStr.𝟘 (snd B∞×B∞-quotient) ∎

  ψ-right : BoolHom B∞ B∞×B∞-quotient
  ψ-right = QB.inducedHom B∞×B∞-quotient ψ-right-free ψ-right-respects-relB∞

  encode×-inl-inr-distinct : (m n : ℕ) → ¬ (encode× (⊎.inl m) ≡ encode× (⊎.inr n))
  encode×-inl-inr-distinct m n = λ eq →
    lower (⊎Path.encode (⊎.inl m) (⊎.inr n)
           (sym (decode×∘encode× (⊎.inl m))
            ∙ cong decode× eq
            ∙ decode×∘encode× (⊎.inr n)))
    where
    open import Cubical.Data.Sum.Properties using (module ⊎Path)

  g×-cross-orthog : (m n : ℕ) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-left-gen m) (g×-right-gen n) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-cross-orthog m n =
    let i = encode× (⊎.inl m)
        j = encode× (⊎.inr n)
        i≠j : ¬ (i ≡ j)
        i≠j = encode×-inl-inr-distinct m n
    in g×-orthog i j i≠j
    where
    g×-orthog-base : (i j : ℕ) → i < j →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog-base i j i<j =
      let k = cantorPair i (j ∸ suc i)
          rel-eq : relB∞×B∞ k ≡ gen i · gen j
          rel-eq = cong relB∞×B∞-from-pair (cantorUnpair-pair i (j ∸ suc i))
                 ∙ cong (λ x → gen i · gen x) (i+suc[j∸suc-i]≡j i j i<j)
      in sym (IsCommRingHom.pres· (snd π×) (gen i) (gen j))
         ∙ cong (fst π×) (sym rel-eq)
         ∙ QB.zeroOnImage k

    g×-orthog : (i j : ℕ) → ¬ (i ≡ j) →
      BooleanRingStr._·_ (snd B∞×B∞-quotient) (g× i) (g× j) ≡
      BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
    g×-orthog i j i≠j with Cubical.Data.Nat.Order.<Dec i j
    ... | yes i<j = g×-orthog-base i j i<j
    ... | no ¬i<j with Cubical.Data.Nat.Order.<Dec j i
    ...   | yes j<i =
            BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g× i) (g× j)
            ∙ g×-orthog-base j i j<i
    ...   | no ¬j<i =
            ex-falso (i≠j (≤-antisym (≮→≥ ¬j<i) (≮→≥ ¬i<j)))

  g×-cross-orthog-sym : (m n : ℕ) →
    BooleanRingStr._·_ (snd B∞×B∞-quotient) (g×-right-gen n) (g×-left-gen m) ≡
    BooleanRingStr.𝟘 (snd B∞×B∞-quotient)
  g×-cross-orthog-sym m n =
    BooleanRingStr.·Comm (snd B∞×B∞-quotient) (g×-right-gen n) (g×-left-gen m)
    ∙ g×-cross-orthog m n

  module Q = BooleanRingStr (snd B∞×B∞-quotient)

  ψ-map : ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞-quotient ⟩
  ψ-map (x , y) = Q._+_ (fst ψ-left x) (fst ψ-right y)

  ψ-pres0 : ψ-map (𝟘∞ , 𝟘∞) ≡ Q.𝟘
  ψ-pres0 =
    Q._+_ (fst ψ-left 𝟘∞) (fst ψ-right 𝟘∞)
      ≡⟨ cong₂ Q._+_ (IsCommRingHom.pres0 (snd ψ-left)) (IsCommRingHom.pres0 (snd ψ-right)) ⟩
    Q._+_ Q.𝟘 Q.𝟘
      ≡⟨ Q.+IdR Q.𝟘 ⟩
    Q.𝟘 ∎

  φ-hits-left-gen : (m : ℕ) → fst φ (g×-left-gen m) ≡ (g∞ m , 𝟘∞)
  φ-hits-left-gen m =
    fst φ (g× (encode× (⊎.inl m)))
      ≡⟨ φ-on-g× (encode× (⊎.inl m)) ⟩
    genProd (encode× (⊎.inl m))
      ≡⟨ cong genProd⊎ (decode×∘encode× (⊎.inl m)) ⟩
    genProd⊎ (⊎.inl m)
      ≡⟨ refl ⟩
    (g∞ m , 𝟘∞) ∎

  φ-hits-right-gen : (m : ℕ) → fst φ (g×-right-gen m) ≡ (𝟘∞ , g∞ m)
  φ-hits-right-gen m =
    fst φ (g× (encode× (⊎.inr m)))
      ≡⟨ φ-on-g× (encode× (⊎.inr m)) ⟩
    genProd (encode× (⊎.inr m))
      ≡⟨ cong genProd⊎ (decode×∘encode× (⊎.inr m)) ⟩
    genProd⊎ (⊎.inr m)
      ≡⟨ refl ⟩
    (𝟘∞ , g∞ m) ∎

  ψ-left-on-gen : (m : ℕ) → fst ψ-left (g∞ m) ≡ g×-left-gen m
  ψ-left-on-gen m =
    fst ψ-left (g∞ m)
      ≡⟨ funExt⁻ (cong fst (QB.evalInduce B∞×B∞-quotient ψ-left-free ψ-left-respects-relB∞)) (gen m) ⟩
    fst ψ-left-free (gen m)
      ≡⟨ funExt⁻ ψ-left-free-on-gen m ⟩
    g×-left-gen m ∎

  ψ-right-on-gen : (m : ℕ) → fst ψ-right (g∞ m) ≡ g×-right-gen m
  ψ-right-on-gen m =
    fst ψ-right (g∞ m)
      ≡⟨ funExt⁻ (cong fst (QB.evalInduce B∞×B∞-quotient ψ-right-free ψ-right-respects-relB∞)) (gen m) ⟩
    fst ψ-right-free (gen m)
      ≡⟨ funExt⁻ ψ-right-free-on-gen m ⟩
    g×-right-gen m ∎

  φ∘ψ-left-on-gen : (m : ℕ) → fst φ (fst ψ-left (g∞ m)) ≡ (g∞ m , 𝟘∞)
  φ∘ψ-left-on-gen m = cong (fst φ) (ψ-left-on-gen m) ∙ φ-hits-left-gen m

  φ∘ψ-right-on-gen : (m : ℕ) → fst φ (fst ψ-right (g∞ m)) ≡ (𝟘∞ , g∞ m)
  φ∘ψ-right-on-gen m = cong (fst φ) (ψ-right-on-gen m) ∙ φ-hits-right-gen m

  postulate
    B∞×B∞≃quotient : BooleanRingEquiv B∞×B∞ B∞×B∞-quotient

open B∞×B∞-Presentation

B∞×B∞-has-Boole-ω' : has-Boole-ω' B∞×B∞
B∞×B∞-has-Boole-ω' = relB∞×B∞ , B∞×B∞≃quotient

B∞×B∞-Booleω : Booleω
B∞×B∞-Booleω = B∞×B∞ , ∣ B∞×B∞-has-Boole-ω' ∣₁

restrict-to-left : (h' : Sp B∞×B∞-Booleω) → h' $cr unit-left ≡ true → Sp B∞-Booleω
restrict-to-left h' h'-unit-left-true = h-on-left , h-on-left-is-hom
  where
  open IsCommRingHom (snd h') renaming (pres0 to h'-pres0 ; pres1 to h'-pres1 ; pres+ to h'-pres+ ; pres· to h'-pres·)
  open CommRingStr (snd (BooleanRing→CommRing B∞)) renaming (_+_ to _+B∞_ ; _·_ to _·B∞_ ; +IdL to +B∞-IdL)
  open CommRingStr (snd (BooleanRing→CommRing B∞×B∞)) renaming (_+_ to _+B∞×B∞_ ; _·_ to _·B∞×B∞_)
  open import Cubical.Algebra.CommRing using (makeIsCommRingHom)

  h-on-left : ⟨ B∞ ⟩ → Bool
  h-on-left x = h' $cr (x , 𝟘∞)

  h-on-left-pres0 : h-on-left 𝟘∞ ≡ false
  h-on-left-pres0 = h'-pres0

  h-on-left-pres1 : h-on-left 𝟙∞ ≡ true
  h-on-left-pres1 = h'-unit-left-true

  h-on-left-pres+ : (x y : ⟨ B∞ ⟩) → h-on-left (x +B∞ y) ≡ (h-on-left x) ⊕ (h-on-left y)
  h-on-left-pres+ x y =
    h' $cr (x +B∞ y , 𝟘∞)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ refl (sym (+B∞-IdL 𝟘∞))) ⟩
    h' $cr (_+B∞×B∞_ (x , 𝟘∞) (y , 𝟘∞))
      ≡⟨ h'-pres+ (x , 𝟘∞) (y , 𝟘∞) ⟩
    (h' $cr (x , 𝟘∞)) ⊕ (h' $cr (y , 𝟘∞)) ∎

  h-on-left-pres· : (x y : ⟨ B∞ ⟩) → h-on-left (x ·B∞ y) ≡ (h-on-left x) and (h-on-left y)
  h-on-left-pres· x y =
    h' $cr (x ·B∞ y , 𝟘∞)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ refl (sym (0∞-absorbs-left 𝟘∞))) ⟩
    h' $cr (_·B∞×B∞_ (x , 𝟘∞) (y , 𝟘∞))
      ≡⟨ h'-pres· (x , 𝟘∞) (y , 𝟘∞) ⟩
    (h' $cr (x , 𝟘∞)) and (h' $cr (y , 𝟘∞)) ∎

  h-on-left-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞)) h-on-left (snd (BooleanRing→CommRing BoolBR))
  h-on-left-is-hom = makeIsCommRingHom h-on-left-pres1 h-on-left-pres+ h-on-left-pres·

restrict-to-right : (h' : Sp B∞×B∞-Booleω) → h' $cr unit-left ≡ false → Sp B∞-Booleω
restrict-to-right h' h'-unit-left-false = h-on-right , h-on-right-is-hom
  where
  open IsCommRingHom (snd h') renaming (pres0 to h'-pres0 ; pres1 to h'-pres1 ; pres+ to h'-pres+ ; pres· to h'-pres·)
  open CommRingStr (snd (BooleanRing→CommRing B∞)) renaming (_+_ to _+B∞_ ; _·_ to _·B∞_ ; +IdL to +B∞-IdL ; +IdR to +B∞-IdR)
  open CommRingStr (snd (BooleanRing→CommRing B∞×B∞)) renaming (_+_ to _+B∞×B∞_ ; _·_ to _·B∞×B∞_)
  open import Cubical.Algebra.CommRing using (makeIsCommRingHom)

  h-on-right : ⟨ B∞ ⟩ → Bool
  h-on-right x = h' $cr (𝟘∞ , x)

  h-on-right-pres0 : h-on-right 𝟘∞ ≡ false
  h-on-right-pres0 = h'-pres0

  h-on-right-pres1 : h-on-right 𝟙∞ ≡ true
  h-on-right-pres1 =
    let
      h'-on-1 : h' $cr (𝟙∞ , 𝟙∞) ≡ true
      h'-on-1 = h'-pres1
      unit-sum' : (𝟙∞ , 𝟙∞) ≡ _+B∞×B∞_ (𝟙∞ , 𝟘∞) (𝟘∞ , 𝟙∞)
      unit-sum' = cong₂ _,_ (sym (+B∞-IdR 𝟙∞)) (sym (+B∞-IdL 𝟙∞))
      h'-sum : h' $cr (𝟙∞ , 𝟙∞) ≡ (h' $cr unit-left) ⊕ (h' $cr unit-right)
      h'-sum = cong (h' $cr_) unit-sum' ∙ h'-pres+ unit-left unit-right
      xor-eq : false ⊕ (h' $cr unit-right) ≡ true
      xor-eq = cong (λ b → b ⊕ (h' $cr unit-right)) (sym h'-unit-left-false) ∙ sym h'-sum ∙ h'-on-1
    in xor-eq

  h-on-right-pres+ : (x y : ⟨ B∞ ⟩) → h-on-right (x +B∞ y) ≡ (h-on-right x) ⊕ (h-on-right y)
  h-on-right-pres+ x y =
    h' $cr (𝟘∞ , x +B∞ y)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ (sym (+B∞-IdL 𝟘∞)) refl) ⟩
    h' $cr (_+B∞×B∞_ (𝟘∞ , x) (𝟘∞ , y))
      ≡⟨ h'-pres+ (𝟘∞ , x) (𝟘∞ , y) ⟩
    (h' $cr (𝟘∞ , x)) ⊕ (h' $cr (𝟘∞ , y)) ∎

  h-on-right-pres· : (x y : ⟨ B∞ ⟩) → h-on-right (x ·B∞ y) ≡ (h-on-right x) and (h-on-right y)
  h-on-right-pres· x y =
    h' $cr (𝟘∞ , x ·B∞ y)
      ≡⟨ cong (h' $cr_) (cong₂ _,_ (sym (0∞-absorbs-left 𝟘∞)) refl) ⟩
    h' $cr (_·B∞×B∞_ (𝟘∞ , x) (𝟘∞ , y))
      ≡⟨ h'-pres· (𝟘∞ , x) (𝟘∞ , y) ⟩
    (h' $cr (𝟘∞ , x)) and (h' $cr (𝟘∞ , y)) ∎

  h-on-right-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞)) h-on-right (snd (BooleanRing→CommRing BoolBR))
  h-on-right-is-hom = makeIsCommRingHom h-on-right-pres1 h-on-right-pres+ h-on-right-pres·

Sp-prod-to-sum : Sp B∞×B∞-Booleω → (Sp B∞-Booleω) ⊎.⊎ (Sp B∞-Booleω)
Sp-prod-to-sum h with h $cr unit-left in p
... | true = ⊎.inl (restrict-to-left h (builtin→Path-Bool p))
... | false = ⊎.inr (restrict-to-right h (builtin→Path-Bool p))

inject-left : Sp B∞-Booleω → Sp B∞×B∞-Booleω
inject-left h = h' , h'-is-hom
  where
  open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1 ; pres+ to h-pres+ ; pres· to h-pres·)

  h' : ⟨ B∞×B∞ ⟩ → Bool
  h' (x , y) = h $cr x

  h'-pres1 : h' (𝟙∞ , 𝟙∞) ≡ true
  h'-pres1 = h-pres1

  h'-pres+ : (a b : ⟨ B∞×B∞ ⟩) → h' (a +× b) ≡ (h' a) ⊕ (h' b)
  h'-pres+ (x1 , y1) (x2 , y2) = h-pres+ x1 x2

  h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' (a ·×' b) ≡ (h' a) and (h' b)
  h'-pres· (x1 , y1) (x2 , y2) = h-pres· x1 x2

  h'-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞×B∞)) h' (snd (BooleanRing→CommRing BoolBR))
  h'-is-hom = makeIsCommRingHom h'-pres1 h'-pres+ h'-pres·

inject-right : Sp B∞-Booleω → Sp B∞×B∞-Booleω
inject-right h = h' , h'-is-hom
  where
  open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1 ; pres+ to h-pres+ ; pres· to h-pres·)

  h' : ⟨ B∞×B∞ ⟩ → Bool
  h' (x , y) = h $cr y

  h'-pres1 : h' (𝟙∞ , 𝟙∞) ≡ true
  h'-pres1 = h-pres1

  h'-pres+ : (a b : ⟨ B∞×B∞ ⟩) → h' (a +× b) ≡ (h' a) ⊕ (h' b)
  h'-pres+ (x1 , y1) (x2 , y2) = h-pres+ y1 y2

  h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' (a ·×' b) ≡ (h' a) and (h' b)
  h'-pres· (x1 , y1) (x2 , y2) = h-pres· y1 y2

  h'-is-hom : IsCommRingHom (snd (BooleanRing→CommRing B∞×B∞)) h' (snd (BooleanRing→CommRing BoolBR))
  h'-is-hom = makeIsCommRingHom h'-pres1 h'-pres+ h'-pres·

Sp-sum-to-prod : (Sp B∞-Booleω) ⊎.⊎ (Sp B∞-Booleω) → Sp B∞×B∞-Booleω
Sp-sum-to-prod (⊎.inl h) = inject-left h
Sp-sum-to-prod (⊎.inr h) = inject-right h

inject-left-unit-left : (h : Sp B∞-Booleω) → inject-left h $cr unit-left ≡ true
inject-left-unit-left h = IsCommRingHom.pres1 (snd h)

inject-right-unit-left : (h : Sp B∞-Booleω) → inject-right h $cr unit-left ≡ false
inject-right-unit-left h = IsCommRingHom.pres0 (snd h)

restrict-inject-left : (h : Sp B∞-Booleω) → (pf : inject-left h $cr unit-left ≡ true)
                     → restrict-to-left (inject-left h) pf ≡ h
restrict-inject-left h pf = Σ≡Prop
  (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞)) f (snd (BooleanRing→CommRing BoolBR)))
  refl

restrict-inject-right : (h : Sp B∞-Booleω) → (pf : inject-right h $cr unit-left ≡ false)
                      → restrict-to-right (inject-right h) pf ≡ h
restrict-inject-right h pf = Σ≡Prop
  (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞)) f (snd (BooleanRing→CommRing BoolBR)))
  refl

private
  _=B'_ : (a b : Bool) → Dec (a ≡ b)
  _=B'_ = Bool-equality-decidable

  ¬true→false' : (b : Bool) → ¬ (b ≡ true) → b ≡ false
  ¬true→false' true ¬p = ex-falso (¬p refl)
  ¬true→false' false ¬p = refl

Sp-prod-to-sum' : Sp B∞×B∞-Booleω → (Sp B∞-Booleω) ⊎.⊎ (Sp B∞-Booleω)
Sp-prod-to-sum' h with (h $cr unit-left) =B' true
... | yes pf = ⊎.inl (restrict-to-left h pf)
... | no ¬pf = ⊎.inr (restrict-to-right h (¬true→false' (h $cr unit-left) ¬pf))

private
  Sp-prod-sum-roundtrip'-inl : (h : Sp B∞-Booleω) → Sp-prod-to-sum' (inject-left h) ≡ ⊎.inl h
  Sp-prod-sum-roundtrip'-inl h with (inject-left h $cr unit-left) =B' true
  ... | yes pf = cong ⊎.inl (restrict-inject-left h pf)
  ... | no ¬pf = ex-falso (¬pf (inject-left-unit-left h))

  Sp-prod-sum-roundtrip'-inr : (h : Sp B∞-Booleω) → Sp-prod-to-sum' (inject-right h) ≡ ⊎.inr h
  Sp-prod-sum-roundtrip'-inr h with (inject-right h $cr unit-left) =B' true
  ... | yes pf = ex-falso (true≢false (sym pf ∙ inject-right-unit-left h))
  ... | no ¬pf = cong ⊎.inr (Σ≡Prop
    (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞)) f (snd (BooleanRing→CommRing BoolBR)))
    refl)

Sp-prod-sum-roundtrip' : (x : (Sp B∞-Booleω) ⊎.⊎ (Sp B∞-Booleω)) → Sp-prod-to-sum' (Sp-sum-to-prod x) ≡ x
Sp-prod-sum-roundtrip' (⊎.inl h) = Sp-prod-sum-roundtrip'-inl h
Sp-prod-sum-roundtrip' (⊎.inr h) = Sp-prod-sum-roundtrip'-inr h

private
  units-sum-to-one : unit-left +× unit-right ≡ (𝟙∞ , 𝟙∞)
  units-sum-to-one = cong₂ _,_ (+right-unit 𝟙∞) (+left-unit 𝟙∞)
    where
    open CommRingStr (snd (BooleanRing→CommRing B∞)) using () renaming (+IdL to +left-unit ; +IdR to +right-unit)

  unit-left-true→unit-right-false : (h : Sp B∞×B∞-Booleω)
    → h $cr unit-left ≡ true → h $cr unit-right ≡ false
  unit-left-true→unit-right-false h pf = true-⊕-id (h $cr unit-right) chain
    where
    open CommRingStr (snd (BooleanRing→CommRing BoolBR)) using () renaming (_+_ to _⊕Bool_)
    h-sum : h $cr (unit-left +× unit-right) ≡ (h $cr unit-left) ⊕Bool (h $cr unit-right)
    h-sum = IsCommRingHom.pres+ (snd h) unit-left unit-right
    h-one : h $cr (𝟙∞ , 𝟙∞) ≡ true
    h-one = IsCommRingHom.pres1 (snd h)
    true-⊕-id : (b : Bool) → true ⊕Bool b ≡ true → b ≡ false
    true-⊕-id false _ = refl
    true-⊕-id true = λ eq → ex-falso (false≢true eq)
    chain : true ⊕Bool (h $cr unit-right) ≡ true
    chain = cong (λ b → b ⊕Bool (h $cr unit-right)) (sym pf) ∙
            sym h-sum ∙
            cong (h $cr_) units-sum-to-one ∙
            h-one

  unit-left-false→unit-right-true : (h : Sp B∞×B∞-Booleω)
    → h $cr unit-left ≡ false → h $cr unit-right ≡ true
  unit-left-false→unit-right-true h pf =
    let h-sum = IsCommRingHom.pres+ (snd h) unit-left unit-right
        h-one = IsCommRingHom.pres1 (snd h)
    in sym (xor-false-left (h $cr unit-right)) ∙
       cong (λ b → b ⊕ (h $cr unit-right)) (sym pf) ∙
       sym h-sum ∙
       cong (h $cr_) units-sum-to-one ∙
       h-one
    where
    xor-false-left : (b : Bool) → false ⊕ b ≡ b
    xor-false-left false = refl
    xor-false-left true = refl

Sp-f : Sp B∞×B∞-Booleω → Sp B∞-Booleω
Sp-f h = h ∘cr f

f-is-injective-hom : isInjectiveBoolHom B∞-Booleω B∞×B∞-Booleω f
f-is-injective-hom = f-injective-05a

Sp-f-surjective' : isSurjectiveSpHom B∞-Booleω B∞×B∞-Booleω f
Sp-f-surjective' = injective→Sp-surjective B∞-Booleω B∞×B∞-Booleω f f-is-injective-hom

Sp-f-surjective : (h : Sp B∞-Booleω) → ∥ Σ[ h' ∈ Sp B∞×B∞-Booleω ] Sp-f h' ≡ h ∥₁
Sp-f-surjective = Sp-f-surjective'

Sp-f-value : (h' : Sp B∞×B∞-Booleω) (x : ⟨ B∞ ⟩) →
  (Sp-f h') $cr x ≡ h' $cr (fst f x)
Sp-f-value h' x = refl

unit-left-right-orth : (y : ⟨ B∞ ⟩) → unit-left ·× (𝟘∞ , y) ≡ (𝟘∞ , 𝟘∞)
unit-left-right-orth y = cong₂ _,_ (0∞-absorbs-right 𝟙B∞) (0∞-absorbs-left y)
  where
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

unit-right-left-orth : (x : ⟨ B∞ ⟩) → unit-right ·× (x , 𝟘∞) ≡ (𝟘∞ , 𝟘∞)
unit-right-left-orth x = cong₂ _,_ (0∞-absorbs-left x) (0∞-absorbs-right 𝟙B∞)
  where
  open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞)

h'-left-true→right-false : (h' : Sp B∞×B∞-Booleω) → h' $cr unit-left ≡ true →
  (y : ⟨ B∞ ⟩) → h' $cr (𝟘∞ , y) ≡ false
h'-left-true→right-false h' h'-left-true y =
  let
    h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' $cr (a ·× b) ≡ (h' $cr a) and (h' $cr b)
    h'-pres· = IsCommRingHom.pres· (snd h')
    prod-zero : unit-left ·× (𝟘∞ , y) ≡ (𝟘∞ , 𝟘∞)
    prod-zero = unit-left-right-orth y
    h'-prod : h' $cr (unit-left ·× (𝟘∞ , y)) ≡ false
    h'-prod = cong (h' $cr_) prod-zero ∙ IsCommRingHom.pres0 (snd h')
    h'-and : (h' $cr unit-left) and (h' $cr (𝟘∞ , y)) ≡ false
    h'-and = sym (h'-pres· unit-left (𝟘∞ , y)) ∙ h'-prod
    result : (h' $cr (𝟘∞ , y)) ≡ false
    result = subst (λ b → b and (h' $cr (𝟘∞ , y)) ≡ false) h'-left-true h'-and
  in result

h'-right-true→left-false : (h' : Sp B∞×B∞-Booleω) → h' $cr unit-right ≡ true →
  (x : ⟨ B∞ ⟩) → h' $cr (x , 𝟘∞) ≡ false
h'-right-true→left-false h' h'-right-true x =
  let
    h'-pres· : (a b : ⟨ B∞×B∞ ⟩) → h' $cr (a ·× b) ≡ (h' $cr a) and (h' $cr b)
    h'-pres· = IsCommRingHom.pres· (snd h')
    prod-zero : unit-right ·× (x , 𝟘∞) ≡ (𝟘∞ , 𝟘∞)
    prod-zero = unit-right-left-orth x
    h'-prod : h' $cr (unit-right ·× (x , 𝟘∞)) ≡ false
    h'-prod = cong (h' $cr_) prod-zero ∙ IsCommRingHom.pres0 (snd h')
    h'-and : (h' $cr unit-right) and (h' $cr (x , 𝟘∞)) ≡ false
    h'-and = sym (h'-pres· unit-right (x , 𝟘∞)) ∙ h'-prod
    result : (h' $cr (x , 𝟘∞)) ≡ false
    result = subst (λ b → b and (h' $cr (x , 𝟘∞)) ≡ false) h'-right-true h'-and
  in result

ℕ∞-on-gen : ℕ∞ → ℕ → Bool
ℕ∞-on-gen α n = fst α n

ℕ∞-gen-respects-relations : (α : ℕ∞) → (m n : ℕ) → ¬ (m ≡ n) →
  (ℕ∞-on-gen α m) and (ℕ∞-on-gen α n) ≡ false
ℕ∞-gen-respects-relations α m n m≠n = lemma (fst α m) (fst α n) refl refl
  where
  lemma : (am an : Bool) → fst α m ≡ am → fst α n ≡ an → am and an ≡ false
  lemma false _ _ _ = refl
  lemma true false _ _ = refl
  lemma true true αm≡true αn≡true = ex-falso (m≠n (snd α m n αm≡true αn≡true))

ℕ∞-to-SpB∞-free : ℕ∞ → BoolHom (freeBA ℕ) BoolBR
ℕ∞-to-SpB∞-free α = inducedBAHom ℕ BoolBR (ℕ∞-on-gen α)

ℕ∞-to-SpB∞-free-on-gen : (α : ℕ∞) → fst (ℕ∞-to-SpB∞-free α) ∘ generator ≡ ℕ∞-on-gen α
ℕ∞-to-SpB∞-free-on-gen α = evalBAInduce ℕ BoolBR (ℕ∞-on-gen α)

ℕ∞-to-SpB∞-free-distinct-zero : (α : ℕ∞) (a b : ℕ) → ¬ (a ≡ b) →
  fst (ℕ∞-to-SpB∞-free α) (gen a · gen b) ≡ false
ℕ∞-to-SpB∞-free-distinct-zero α a b a≠b =
  fst (ℕ∞-to-SpB∞-free α) (gen a · gen b)
    ≡⟨ IsCommRingHom.pres· (snd (ℕ∞-to-SpB∞-free α)) (gen a) (gen b) ⟩
  (fst (ℕ∞-to-SpB∞-free α) (gen a)) and (fst (ℕ∞-to-SpB∞-free α) (gen b))
    ≡⟨ cong₂ _and_ (funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) a) (funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) b) ⟩
  (ℕ∞-on-gen α a) and (ℕ∞-on-gen α b)
    ≡⟨ ℕ∞-gen-respects-relations α a b a≠b ⟩
  false ∎

ℕ∞-to-SpB∞-respects-rel : (α : ℕ∞) (k : ℕ) →
  fst (ℕ∞-to-SpB∞-free α) (relB∞ k) ≡ false
ℕ∞-to-SpB∞-respects-rel α k =
  let (a , d) = cantorUnpair k
  in ℕ∞-to-SpB∞-free-distinct-zero α a (a +ℕ suc d) (a≠a+suc-d a d)

ℕ∞-to-SpB∞ : ℕ∞ → Sp B∞-Booleω
ℕ∞-to-SpB∞ α = QB.inducedHom {B = freeBA ℕ} {f = relB∞} BoolBR (ℕ∞-to-SpB∞-free α) (ℕ∞-to-SpB∞-respects-rel α)

opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  ℕ∞-to-SpB∞-eval : (α : ℕ∞) →
    (ℕ∞-to-SpB∞ α) ∘cr π∞ ≡ ℕ∞-to-SpB∞-free α
  ℕ∞-to-SpB∞-eval α = QB.evalInduce {B = freeBA ℕ} {f = relB∞}
                        BoolBR (ℕ∞-to-SpB∞-free α) (ℕ∞-to-SpB∞-respects-rel α)

SpB∞-roundtrip-seq : (α : ℕ∞) (n : ℕ) →
  SpB∞-to-ℕ∞-seq (ℕ∞-to-SpB∞ α) n ≡ fst α n
SpB∞-roundtrip-seq α n =
  SpB∞-to-ℕ∞-seq (ℕ∞-to-SpB∞ α) n
    ≡⟨ refl ⟩
  (ℕ∞-to-SpB∞ α) $cr (g∞ n)
    ≡⟨ refl ⟩
  (ℕ∞-to-SpB∞ α) $cr (fst π∞ (gen n))
    ≡⟨ funExt⁻ (cong fst (ℕ∞-to-SpB∞-eval α)) (gen n) ⟩
  fst (ℕ∞-to-SpB∞-free α) (gen n)
    ≡⟨ funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) n ⟩
  ℕ∞-on-gen α n
    ≡⟨ refl ⟩
  fst α n ∎

SpB∞-roundtrip : (α : ℕ∞) → SpB∞-to-ℕ∞ (ℕ∞-to-SpB∞ α) ≡ α
SpB∞-roundtrip α = Σ≡Prop
  (λ s → isPropHitsAtMostOnce s)
  (funExt (SpB∞-roundtrip-seq α))

g∞-has-witness : (n : ℕ) → (ℕ∞-to-SpB∞ (δ∞ n)) $cr (g∞ n) ≡ true
g∞-has-witness n = SpB∞-roundtrip-seq (δ∞ n) n ∙ δ∞-hits-n n

g∞-nonzero : (n : ℕ) → ¬ (g∞ n ≡ 𝟘∞)
g∞-nonzero n gn=0 =
  let h = ℕ∞-to-SpB∞ (δ∞ n)
      h-gn=t : h $cr (g∞ n) ≡ true
      h-gn=t = g∞-has-witness n
      h-0=f : h $cr 𝟘∞ ≡ false
      h-0=f = IsCommRingHom.pres0 (snd h)
      h-gn=f : h $cr (g∞ n) ≡ false
      h-gn=f = cong (h $cr_) gn=0 ∙ h-0=f
  in true≢false (sym h-gn=t ∙ h-gn=f)

_orBool_ : Bool → Bool → Bool
false orBool b = b
true orBool _ = true

xor-and-is-or : (a b : Bool) → (a ⊕ b) ⊕ (a and b) ≡ a orBool b
xor-and-is-or false false = refl
xor-and-is-or false true = refl
xor-and-is-or true false = refl
xor-and-is-or true true = refl

h-pres-join-Bool : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr (a ∨∞ b) ≡ (h $cr a) orBool (h $cr b)
h-pres-join-Bool h a b =
  let open IsCommRingHom (snd h) renaming (pres+ to h-pres+ ; pres· to h-pres·)
  in h $cr (a ∨∞ b)
       ≡⟨ refl ⟩
     h $cr (a +∞ b +∞ (a ·∞ b))
       ≡⟨ h-pres+ (a +∞ b) (a ·∞ b) ⟩
     (h $cr (a +∞ b)) ⊕ (h $cr (a ·∞ b))
       ≡⟨ cong₂ _⊕_ (h-pres+ a b) (h-pres· a b) ⟩
     ((h $cr a) ⊕ (h $cr b)) ⊕ ((h $cr a) and (h $cr b))
       ≡⟨ xor-and-is-or (h $cr a) (h $cr b) ⟩
     (h $cr a) orBool (h $cr b) ∎

h-join-monotone : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr a ≡ true → h $cr (a ∨∞ b) ≡ true
h-join-monotone h a b ha=t =
  h $cr (a ∨∞ b)
    ≡⟨ h-pres-join-Bool h a b ⟩
  (h $cr a) orBool (h $cr b)
    ≡⟨ cong (_orBool (h $cr b)) ha=t ⟩
  true orBool (h $cr b)
    ≡⟨ refl ⟩
  true ∎

finJoin∞-zero→empty : (ns : List ℕ) → finJoin∞ ns ≡ 𝟘∞ → ns ≡ []
finJoin∞-zero→empty [] _ = refl
finJoin∞-zero→empty (n ∷ rest) join=0 = ex-falso contradiction
  where
  h : Sp B∞-Booleω
  h = ℕ∞-to-SpB∞ (δ∞ n)

  h-gn=true : h $cr (g∞ n) ≡ true
  h-gn=true = g∞-has-witness n

  h-join=true : h $cr (finJoin∞ (n ∷ rest)) ≡ true
  h-join=true = h-join-monotone h (g∞ n) (finJoin∞ rest) h-gn=true

  h-0=false : h $cr 𝟘∞ ≡ false
  h-0=false = IsCommRingHom.pres0 (snd h)

  h-join=false : h $cr (finJoin∞ (n ∷ rest)) ≡ false
  h-join=false = cong (h $cr_) join=0 ∙ h-0=false

  contradiction : ⊥
  contradiction = true≢false (sym h-join=true ∙ h-join=false)

∞-seq : ℕ → Bool
∞-seq _ = false

∞-hamo : hitsAtMostOnce ∞-seq
∞-hamo m n ∞m=t _ = ex-falso (false≢true ∞m=t)

ℕ∞-∞ : ℕ∞
ℕ∞-∞ = ∞-seq , ∞-hamo

h₀ : Sp B∞-Booleω
h₀ = ℕ∞-to-SpB∞ ℕ∞-∞

h₀-on-gen : (n : ℕ) → h₀ $cr (g∞ n) ≡ false
h₀-on-gen n = SpB∞-roundtrip-seq ℕ∞-∞ n

notBool : Bool → Bool
notBool false = true
notBool true = false

h-pres-neg-Bool : (h : Sp B∞-Booleω) (x : ⟨ B∞ ⟩) →
  h $cr (¬∞ x) ≡ notBool (h $cr x)
h-pres-neg-Bool h x =
  let open IsCommRingHom (snd h) renaming (pres+ to h-pres+ ; pres1 to h-pres1)
  in h $cr (¬∞ x)
       ≡⟨ refl ⟩
     h $cr (𝟙∞ +∞ x)
       ≡⟨ h-pres+ 𝟙∞ x ⟩
     (h $cr 𝟙∞) ⊕ (h $cr x)
       ≡⟨ cong (_⊕ (h $cr x)) h-pres1 ⟩
     true ⊕ (h $cr x)
       ≡⟨ ⊕-comm true (h $cr x) ⟩
     (h $cr x) ⊕ true
       ≡⟨ helper (h $cr x) ⟩
     notBool (h $cr x) ∎
  where
  helper : (b : Bool) → b ⊕ true ≡ notBool b
  helper false = refl
  helper true = refl

h₀-on-neg-gen : (n : ℕ) → h₀ $cr (¬∞ (g∞ n)) ≡ true
h₀-on-neg-gen n =
  h₀ $cr (¬∞ (g∞ n))
    ≡⟨ h-pres-neg-Bool h₀ (g∞ n) ⟩
  notBool (h₀ $cr (g∞ n))
    ≡⟨ cong notBool (h₀-on-gen n) ⟩
  notBool false
    ≡⟨ refl ⟩
  true ∎

h-pres-meet-Bool : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr (a ∧∞ b) ≡ (h $cr a) and (h $cr b)
h-pres-meet-Bool h a b = IsCommRingHom.pres· (snd h) a b

h-meet-preserves-true : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr a ≡ true → h $cr b ≡ true → h $cr (a ∧∞ b) ≡ true
h-meet-preserves-true h a b ha=t hb=t =
  h $cr (a ∧∞ b)
    ≡⟨ h-pres-meet-Bool h a b ⟩
  (h $cr a) and (h $cr b)
    ≡⟨ cong₂ _and_ ha=t hb=t ⟩
  true and true
    ≡⟨ refl ⟩
  true ∎

h₀-on-finMeetNeg : (ns : List ℕ) → h₀ $cr (finMeetNeg∞ ns) ≡ true
h₀-on-finMeetNeg [] = IsCommRingHom.pres1 (snd h₀)
h₀-on-finMeetNeg (n ∷ ns) =
  h-meet-preserves-true h₀ (¬∞ (g∞ n)) (finMeetNeg∞ ns)
    (h₀-on-neg-gen n)
    (h₀-on-finMeetNeg ns)

finMeetNeg∞-nonzero : (ns : List ℕ) → ¬ (finMeetNeg∞ ns ≡ 𝟘∞)
finMeetNeg∞-nonzero ns meet=0 = contradiction
  where
  h₀-meet=true : h₀ $cr (finMeetNeg∞ ns) ≡ true
  h₀-meet=true = h₀-on-finMeetNeg ns

  h₀-0=false : h₀ $cr 𝟘∞ ≡ false
  h₀-0=false = IsCommRingHom.pres0 (snd h₀)

  h₀-meet=false : h₀ $cr (finMeetNeg∞ ns) ≡ false
  h₀-meet=false = cong (h₀ $cr_) meet=0 ∙ h₀-0=false

  contradiction : ⊥
  contradiction = true≢false (sym h₀-meet=true ∙ h₀-meet=false)

splitByParity-evens : List ℕ → List ℕ
splitByParity-evens ns = fst (splitByParity ns)

splitByParity-odds : List ℕ → List ℕ
splitByParity-odds ns = snd (splitByParity ns)

splitByParity-cons-even : (n : ℕ) (ns : List ℕ) → isEven n ≡ true →
  splitByParity-evens (n ∷ ns) ≡ half n ∷ splitByParity-evens ns
splitByParity-cons-even n ns even-n with isEven n | splitByParity ns
... | true  | (evens , odds) = refl
... | false | (evens , odds) = ex-falso (false≢true even-n)

splitByParity-cons-odd : (n : ℕ) (ns : List ℕ) → isEven n ≡ false →
  splitByParity-odds (n ∷ ns) ≡ half n ∷ splitByParity-odds ns
splitByParity-cons-odd n ns odd-n with isEven n | splitByParity ns
... | false | (evens , odds) = refl
... | true  | (evens , odds) = ex-falso (true≢false odd-n)

splitByParity-nonempty : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in evens ≡ [] → odds ≡ [] → ns ≡ []
splitByParity-nonempty [] _ _ = refl
splitByParity-nonempty (n ∷ ns) evens=[] odds=[] = splitByParity-nonempty-aux (isEven n) refl
  where
  splitByParity-nonempty-aux : (b : Bool) → isEven n ≡ b → (n ∷ ns) ≡ []
  splitByParity-nonempty-aux true parity =
    let evens-eq = splitByParity-cons-even n ns parity
        contradiction : half n ∷ splitByParity-evens ns ≡ []
        contradiction = sym evens-eq ∙ evens=[]
    in ex-falso (¬cons≡nil contradiction)
  splitByParity-nonempty-aux false parity =
    let odds-eq = splitByParity-cons-odd n ns parity
        contradiction : half n ∷ splitByParity-odds ns ≡ []
        contradiction = sym odds-eq ∙ odds=[]
    in ex-falso (¬cons≡nil contradiction)

splitByParity-ns-nonempty : (ns : List ℕ) → ¬ (ns ≡ []) →
  let (evens , odds) = splitByParity ns
  in ¬ ((evens ≡ []) × (odds ≡ []))
splitByParity-ns-nonempty ns ns≠[] (evens=[] , odds=[]) =
  ns≠[] (splitByParity-nonempty ns evens=[] odds=[])

f-kernel-joinForm : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in fst f (finJoin∞ ns) ≡ (𝟘∞ , 𝟘∞) → ns ≡ []
f-kernel-joinForm ns fx=0 =
  let evens = splitByParity-evens ns
      odds = splitByParity-odds ns

      f-eq : fst f (finJoin∞ ns) ≡ (finJoin∞ evens , finJoin∞ odds)
      f-eq = f-on-finJoin ns

      f-split : (finJoin∞ evens , finJoin∞ odds) ≡ (𝟘∞ , 𝟘∞)
      f-split = sym f-eq ∙ fx=0

      evens-join=0 : finJoin∞ evens ≡ 𝟘∞
      evens-join=0 = cong fst f-split

      odds-join=0 : finJoin∞ odds ≡ 𝟘∞
      odds-join=0 = cong snd f-split

      evens=[] : evens ≡ []
      evens=[] = finJoin∞-zero→empty evens evens-join=0

      odds=[] : odds ≡ []
      odds=[] = finJoin∞-zero→empty odds odds-join=0

  in splitByParity-nonempty ns evens=[] odds=[]

f-kernel-normalForm : (nf : B∞-NormalForm) → fst f ⟦ nf ⟧nf ≡ (𝟘∞ , 𝟘∞) → ⟦ nf ⟧nf ≡ 𝟘∞
f-kernel-normalForm (joinForm ns) fx=0 =
  let ns=[] : ns ≡ []
      ns=[] = f-kernel-joinForm ns fx=0
  in cong finJoin∞ ns=[]
f-kernel-normalForm (meetNegForm ns) fx=0 =
  ex-falso (f-meetNeg-nonzero fx=0)
  where
  h' : ⟨ B∞×B∞ ⟩ → Bool
  h' (a , b) = h₀ $cr a

  h'-on-f-neg-gen-even : (k : ℕ) → h' (fst f (¬∞ (g∞ (2 ·ℕ k)))) ≡ true
  h'-on-f-neg-gen-even k =
    h' (fst f (¬∞ (g∞ (2 ·ℕ k))))
      ≡⟨ cong h' (f-pres-neg (g∞ (2 ·ℕ k))) ⟩
    h' (¬∞ (fst (fst f (g∞ (2 ·ℕ k)))) , ¬∞ (snd (fst f (g∞ (2 ·ℕ k)))))
      ≡⟨ cong (λ x → h' (¬∞ (fst x) , ¬∞ (snd x))) (f-even-gen k) ⟩
    h' (¬∞ (g∞ k) , ¬∞ 𝟘∞)
      ≡⟨ refl ⟩
    h₀ $cr (¬∞ (g∞ k))
      ≡⟨ h₀-on-neg-gen k ⟩
    true ∎

  h'-on-f-neg-gen-odd : (k : ℕ) → h' (fst f (¬∞ (g∞ (suc (2 ·ℕ k))))) ≡ true
  h'-on-f-neg-gen-odd k =
    h' (fst f (¬∞ (g∞ (suc (2 ·ℕ k)))))
      ≡⟨ cong h' (f-pres-neg (g∞ (suc (2 ·ℕ k)))) ⟩
    h' (¬∞ (fst (fst f (g∞ (suc (2 ·ℕ k))))) , ¬∞ (snd (fst f (g∞ (suc (2 ·ℕ k))))))
      ≡⟨ cong (λ x → h' (¬∞ (fst x) , ¬∞ (snd x))) (f-odd-gen k) ⟩
    h' (¬∞ 𝟘∞ , ¬∞ (g∞ k))
      ≡⟨ refl ⟩
    h₀ $cr (¬∞ 𝟘∞)
      ≡⟨ h-pres-neg-Bool h₀ 𝟘∞ ⟩
    notBool (h₀ $cr 𝟘∞)
      ≡⟨ cong notBool (IsCommRingHom.pres0 (snd h₀)) ⟩
    notBool false
      ≡⟨ refl ⟩
    true ∎

  h'-on-f-neg-gen : (n : ℕ) → h' (fst f (¬∞ (g∞ n))) ≡ true
  h'-on-f-neg-gen n = h'-on-f-neg-gen-aux (isEven n) refl
    where
    h'-on-f-neg-gen-aux : (b : Bool) → isEven n ≡ b → h' (fst f (¬∞ (g∞ n))) ≡ true
    h'-on-f-neg-gen-aux true even-n =
      let k = half n
          n=2k : n ≡ 2 ·ℕ k
          n=2k = sym (isEven→even n even-n)
      in subst (λ m → h' (fst f (¬∞ (g∞ m))) ≡ true) (sym n=2k) (h'-on-f-neg-gen-even k)
    h'-on-f-neg-gen-aux false odd-n =
      let k = half n
          n=2k+1 : n ≡ suc (2 ·ℕ k)
          n=2k+1 = sym (isEven→odd n odd-n)
      in subst (λ m → h' (fst f (¬∞ (g∞ m))) ≡ true) (sym n=2k+1) (h'-on-f-neg-gen-odd k)

  h'-pres-· : (x y : ⟨ B∞×B∞ ⟩) → h' (x ·× y) ≡ (h' x) and (h' y)
  h'-pres-· (a₁ , b₁) (a₂ , b₂) = IsCommRingHom.pres· (snd h₀) a₁ a₂

  h'-on-f-finMeetNeg : (ms : List ℕ) → h' (fst f (finMeetNeg∞ ms)) ≡ true
  h'-on-f-finMeetNeg [] =
    h' (fst f 𝟙∞)
      ≡⟨ cong h' f-pres1 ⟩
    h' (𝟙∞ , 𝟙∞)
      ≡⟨ refl ⟩
    h₀ $cr 𝟙∞
      ≡⟨ IsCommRingHom.pres1 (snd h₀) ⟩
    true ∎
  h'-on-f-finMeetNeg (m ∷ ms) =
    h' (fst f (finMeetNeg∞ (m ∷ ms)))
      ≡⟨ refl ⟩
    h' (fst f ((¬∞ (g∞ m)) ∧∞ (finMeetNeg∞ ms)))
      ≡⟨ cong h' (IsCommRingHom.pres· (snd f) (¬∞ (g∞ m)) (finMeetNeg∞ ms)) ⟩
    h' ((fst f (¬∞ (g∞ m))) ·× (fst f (finMeetNeg∞ ms)))
      ≡⟨ h'-pres-· (fst f (¬∞ (g∞ m))) (fst f (finMeetNeg∞ ms)) ⟩
    (h' (fst f (¬∞ (g∞ m)))) and (h' (fst f (finMeetNeg∞ ms)))
      ≡⟨ cong₂ _and_ (h'-on-f-neg-gen m) (h'-on-f-finMeetNeg ms) ⟩
    true and true
      ≡⟨ refl ⟩
    true ∎

  f-meetNeg-nonzero : fst f (finMeetNeg∞ ns) ≡ (𝟘∞ , 𝟘∞) → ⊥
  f-meetNeg-nonzero f-meetNeg=0 = false≢true (sym h'-on-0 ∙ h'-on-f-meetNeg-eq-0)
    where
    h'-on-0 : h' (𝟘∞ , 𝟘∞) ≡ false
    h'-on-0 = IsCommRingHom.pres0 (snd h₀)

    h'-on-f-meetNeg : h' (fst f (finMeetNeg∞ ns)) ≡ true
    h'-on-f-meetNeg = h'-on-f-finMeetNeg ns

    h'-on-f-meetNeg-eq-0 : h' (𝟘∞ , 𝟘∞) ≡ true
    h'-on-f-meetNeg-eq-0 = subst (λ z → h' z ≡ true) f-meetNeg=0 h'-on-f-meetNeg

llpo-from-SD-aux : (h : Sp B∞-Booleω) →
  ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎ ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
llpo-from-SD-aux h = PT.rec llpo-is-prop go (Sp-f-surjective h)
  where
  open import Cubical.Data.Sum.Properties using (isProp⊎)

  evens-is-prop : isProp ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false)
  evens-is-prop = isPropΠ (λ k → isSetBool _ _)

  odds-is-prop : isProp ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
  odds-is-prop = isPropΠ (λ k → isSetBool _ _)

  postulate
    evens-odds-disjoint : ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) →
                          ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) → ⊥

  llpo-is-prop : isProp (((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
                         ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false))
  llpo-is-prop = isProp⊎ evens-is-prop odds-is-prop evens-odds-disjoint

  go : Σ[ h' ∈ Sp B∞×B∞-Booleω ] Sp-f h' ≡ h →
       ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
       ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
  go (h' , Sp-f-h'≡h) = go' (h' $cr unit-left) refl
    where
    go' : (b : Bool) → h' $cr unit-left ≡ b →
          ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
          ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
    go' true h'-left-true = ⊎.inr odds-zero-case
      where
      odds-zero-case : (k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false
      odds-zero-case k =
        h $cr (g∞ (suc (2 ·ℕ k)))
          ≡⟨ sym (funExt⁻ (cong fst Sp-f-h'≡h) (g∞ (suc (2 ·ℕ k)))) ⟩
        h' $cr (fst f (g∞ (suc (2 ·ℕ k))))
          ≡⟨ cong (h' $cr_) (f-odd-gen k) ⟩
        h' $cr (𝟘∞ , g∞ k)
          ≡⟨ h'-left-true→right-false h' h'-left-true (g∞ k) ⟩
        false ∎
    go' false h'-left-false = ⊎.inl evens-zero-case
      where
      open BooleanRingStr (snd B∞) using () renaming (𝟙 to 𝟙B∞ ; _+_ to _+B∞_)
      open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×local_)
      open BooleanRingStr (snd BoolBR) using () renaming (_+_ to _⊕Bool_)

      h'-pres1 : h' $cr (𝟙B∞ , 𝟙B∞) ≡ true
      h'-pres1 = IsCommRingHom.pres1 (snd h')

      open CommRingStr (snd (BooleanRing→CommRing B∞)) using () renaming (+IdL to +left-unit ; +IdR to +right-unit)

      unit-sum' : (𝟙B∞ , 𝟘∞) +×local (𝟘∞ , 𝟙B∞) ≡ (𝟙B∞ , 𝟙B∞)
      unit-sum' = cong₂ _,_ (+right-unit 𝟙B∞) (+left-unit 𝟙B∞)

      h'-pres+ : (a b : ⟨ B∞×B∞ ⟩) → h' $cr (a +×local b) ≡ (h' $cr a) ⊕Bool (h' $cr b)
      h'-pres+ = IsCommRingHom.pres+ (snd h')

      false-⊕-id : (b : Bool) → false ⊕Bool b ≡ b
      false-⊕-id = CommRingStr.+IdL (snd (BooleanRing→CommRing BoolBR))

      h'-right-true : h' $cr unit-right ≡ true
      h'-right-true =
        h' $cr unit-right
          ≡⟨ sym (false-⊕-id (h' $cr unit-right)) ⟩
        false ⊕Bool (h' $cr unit-right)
          ≡⟨ cong (λ b → b ⊕Bool (h' $cr unit-right)) (sym h'-left-false) ⟩
        (h' $cr unit-left) ⊕Bool (h' $cr unit-right)
          ≡⟨ sym (h'-pres+ unit-left unit-right) ⟩
        h' $cr (unit-left +× unit-right)
          ≡⟨ cong (h' $cr_) unit-sum' ⟩
        h' $cr (𝟙B∞ , 𝟙B∞)
          ≡⟨ h'-pres1 ⟩
        true ∎

      evens-zero-case : (k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false
      evens-zero-case k =
        h $cr (g∞ (2 ·ℕ k))
          ≡⟨ sym (funExt⁻ (cong fst Sp-f-h'≡h) (g∞ (2 ·ℕ k))) ⟩
        h' $cr (fst f (g∞ (2 ·ℕ k)))
          ≡⟨ cong (h' $cr_) (f-even-gen k) ⟩
        h' $cr (g∞ k , 𝟘∞)
          ≡⟨ h'-right-true→left-false h' h'-right-true (g∞ k) ⟩
        false ∎

llpo-from-SD : LLPO
llpo-from-SD α = transport-llpo (llpo-from-SD-aux h)
  where
  h : Sp B∞-Booleω
  h = ℕ∞-to-SpB∞ α

  roundtrip : SpB∞-to-ℕ∞ h ≡ α
  roundtrip = SpB∞-roundtrip α

  seq-eq : (n : ℕ) → h $cr (g∞ n) ≡ fst α n
  seq-eq n = funExt⁻ (cong fst roundtrip) n

  transport-llpo : ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
                   ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) →
                   ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎
                   ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false)
  transport-llpo (⊎.inl evens) = ⊎.inl (λ k → sym (seq-eq (2 ·ℕ k)) ∙ evens k)
  transport-llpo (⊎.inr odds) = ⊎.inr (λ k → sym (seq-eq (suc (2 ·ℕ k))) ∙ odds k)

g∞-nf : ℕ → B∞-NormalForm
g∞-nf n = joinForm (n ∷ [])

g∞-nf-correct : (n : ℕ) → ⟦ g∞-nf n ⟧nf ≡ g∞ n
g∞-nf-correct n =
  ⟦ joinForm (n ∷ []) ⟧nf
    ≡⟨ refl ⟩
  finJoin∞ (n ∷ [])
    ≡⟨ refl ⟩
  g∞ n ∨∞ finJoin∞ []
    ≡⟨ refl ⟩
  g∞ n ∨∞ 𝟘∞
    ≡⟨ zero-join-right (g∞ n) ⟩
  g∞ n ∎

𝟙∞-nf : B∞-NormalForm
𝟙∞-nf = meetNegForm []

𝟙∞-nf-correct : ⟦ 𝟙∞-nf ⟧nf ≡ 𝟙∞
𝟙∞-nf-correct = refl

𝟘∞-nf : B∞-NormalForm
𝟘∞-nf = joinForm []

𝟘∞-nf-correct : ⟦ 𝟘∞-nf ⟧nf ≡ 𝟘∞
𝟘∞-nf-correct = refl

neg-nf : B∞-NormalForm → B∞-NormalForm
neg-nf (joinForm ns) = meetNegForm ns
neg-nf (meetNegForm ns) = joinForm ns

pair-decomposition : (x y : ⟨ B∞ ⟩) → (x , y) ≡ (x , 𝟘∞) +× (𝟘∞ , y)
pair-decomposition x y = cong₂ _,_ (sym (+right-unit x)) (sym (+left-unit y))
  where
  open CommRingStr (snd (BooleanRing→CommRing B∞)) using () renaming (+IdL to +left-unit ; +IdR to +right-unit)

h-factors-left : (h : Sp B∞×B∞-Booleω) → (pf : h $cr unit-left ≡ true)
  → (x y : ⟨ B∞ ⟩) → h $cr (x , y) ≡ h $cr (x , 𝟘∞)
h-factors-left h pf x y =
  let h-pres+ = IsCommRingHom.pres+ (snd h)
      h-right-zero = h'-left-true→right-false h pf y
  in cong (h $cr_) (pair-decomposition x y) ∙
     h-pres+ (x , 𝟘∞) (𝟘∞ , y) ∙
     cong (λ b → (h $cr (x , 𝟘∞)) ⊕ b) h-right-zero ∙
     ⊕-false-right (h $cr (x , 𝟘∞))
  where
  ⊕-false-right : (b : Bool) → b ⊕ false ≡ b
  ⊕-false-right false = refl
  ⊕-false-right true = refl

h-factors-right : (h : Sp B∞×B∞-Booleω) → (pf : h $cr unit-left ≡ false)
  → (x y : ⟨ B∞ ⟩) → h $cr (x , y) ≡ h $cr (𝟘∞ , y)
h-factors-right h pf x y =
  let h-pres+ = IsCommRingHom.pres+ (snd h)
      h-right-true = unit-left-false→unit-right-true h pf
      h-left-zero = h'-right-true→left-false h h-right-true x
  in cong (h $cr_) (pair-decomposition x y) ∙
     h-pres+ (x , 𝟘∞) (𝟘∞ , y) ∙
     cong (λ b → b ⊕ (h $cr (𝟘∞ , y))) h-left-zero ∙
     ⊕-false-left (h $cr (𝟘∞ , y))
  where
  ⊕-false-left : (b : Bool) → false ⊕ b ≡ b
  ⊕-false-left false = refl
  ⊕-false-left true = refl

inject-left-restrict-left : (h : Sp B∞×B∞-Booleω) → (pf : h $cr unit-left ≡ true)
  → inject-left (restrict-to-left h pf) ≡ h
inject-left-restrict-left h pf = Σ≡Prop
  (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞×B∞)) f (snd (BooleanRing→CommRing BoolBR)))
  (funExt (λ { (x , y) → sym (h-factors-left h pf x y) }))

inject-right-restrict-right : (h : Sp B∞×B∞-Booleω) → (pf : h $cr unit-left ≡ false)
  → inject-right (restrict-to-right h pf) ≡ h
inject-right-restrict-right h pf = Σ≡Prop
  (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing B∞×B∞)) f (snd (BooleanRing→CommRing BoolBR)))
  (funExt (λ { (x , y) → sym (h-factors-right h pf x y) }))

Sp-sum-prod-roundtrip' : (h : Sp B∞×B∞-Booleω) → Sp-sum-to-prod (Sp-prod-to-sum' h) ≡ h
Sp-sum-prod-roundtrip' h with (h $cr unit-left) =B' true
... | yes pf = inject-left-restrict-left h pf
... | no ¬pf = inject-right-restrict-right h (¬true→false' (h $cr unit-left) ¬pf)
