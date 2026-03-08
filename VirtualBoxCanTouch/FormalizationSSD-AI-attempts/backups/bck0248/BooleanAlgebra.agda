{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneDuality.BooleanAlgebra (fa : FoundationalAxioms) where

open import formalization.StoneDuality.Axioms fa public

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
import formalization.Library.QuotientBool as QB
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce)
open import formalization.Library.CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; idBoolEquiv)
open import formalization.Library.Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)

module B∞-construction where
  open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool using (generator)
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

open IsCommRingHom (snd π∞) renaming (pres· to π∞-pres·)

g∞-lt-mult-zero : (a b : ℕ) → a < b → g∞ a ·∞ g∞ b ≡ 𝟘∞
g∞-lt-mult-zero a b a<b =
  let d = b ∸ suc a
      k = cantorPair a d
  in
  g∞ a ·∞ g∞ b                        ≡⟨ sym (π∞-pres· (gen a) (gen b)) ⟩
  fst π∞ (gen a · gen b)              ≡⟨ cong (fst π∞) (cong (λ x → gen a · gen x) (sym (a+suc-d≡b a b a<b)) ∙ sym (cong relB∞-from-pair (cantorUnpair-pair a d))) ⟩
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

  DirectProd-BooleanRing : BooleanRing ℓ-zero
  DirectProd-BooleanRing = idemCommRing→BR AB-CR
    λ { (a , b) → cong₂ _,_ (BooleanRingStr.·Idem (snd A) a) (BooleanRingStr.·Idem (snd B) b) }

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

-- FinCof: Boolean algebra of finite/cofinite subsets of ℕ
-- Represented as eventually-constant boolean functions
-- (tex: B∞ ≅ FinCof, separating out the LLPO structure)
module FinCofSubsets where
  open import Cubical.Data.Bool using (Bool; true; false; _⊕_; _and_; not; isSetBool;
    true≢false; notnot)
  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
  open import Cubical.Foundations.HLevels using (isSetΣ; isOfHLevelΠ)

  -- A boolean sequence is eventually constant if after some point it stays constant
  isEventuallyConst : (ℕ → Bool) → Type₀
  isEventuallyConst f = ∥ Σ[ N ∈ ℕ ] ((n : ℕ) → N ≤ n → f n ≡ f N) ∥₁

  -- The type of finite/cofinite subsets (eventually constant boolean functions)
  FinCof : Type₀
  FinCof = Σ[ f ∈ (ℕ → Bool) ] isEventuallyConst f

  -- FinCof is a set
  isSetFinCof : isSet FinCof
  isSetFinCof = isSetΣ (isOfHLevelΠ 2 (λ _ → isSetBool)) (λ _ → isProp→isSet squash₁)

  -- Membership: n ∈ S iff fst S n ≡ true
  _∈FC_ : ℕ → FinCof → Bool
  n ∈FC (f , _) = f n

  -- The empty set (finite, eventually false from the start)
  fcEmpty : FinCof
  fcEmpty = (λ _ → false) , ∣ 0 , (λ _ _ → refl) ∣₁

  -- The full set ℕ (cofinite, eventually true from the start)
  fcFull : FinCof
  fcFull = (λ _ → true) , ∣ 0 , (λ _ _ → refl) ∣₁

  -- Complement: swap true/false
  fcNot : FinCof → FinCof
  fcNot (f , ec) = (λ n → not (f n)) ,
    PT.map (λ { (N , stable) → N , (λ n N≤n → cong not (stable n N≤n)) }) ec

  -- Symmetric difference (XOR): the "addition" operation
  fcXor : FinCof → FinCof → FinCof
  fcXor (f , ef) (g , eg) = (λ n → f n ⊕ g n) ,
    PT.rec2 squash₁ (λ { (N₁ , s₁) (N₂ , s₂) →
      let N = N₁ +ℕ N₂ in
      ∣ N , (λ n N≤n →
        let n₁ : N₁ ≤ n
            n₁ = ≤-trans (≤SumLeft {n = N₁} {k = N₂}) N≤n
            n₂ : N₂ ≤ n
            n₂ = ≤-trans (subst (N₂ ≤_) (+-comm N₂ N₁) (≤SumLeft {n = N₂} {k = N₁})) N≤n
            nN₁ : N₁ ≤ N
            nN₁ = ≤SumLeft {n = N₁} {k = N₂}
            nN₂ : N₂ ≤ N
            nN₂ = subst (N₂ ≤_) (+-comm N₂ N₁) (≤SumLeft {n = N₂} {k = N₁})
        in cong₂ _⊕_ (s₁ n n₁) (s₂ n n₂) ∙ sym (cong₂ _⊕_ (s₁ N nN₁) (s₂ N nN₂))) ∣₁ })
    ef eg

  -- Intersection (AND): the "multiplication" operation
  fcAnd : FinCof → FinCof → FinCof
  fcAnd (f , ef) (g , eg) = (λ n → f n and g n) ,
    PT.rec2 squash₁ (λ { (N₁ , s₁) (N₂ , s₂) →
      let N = N₁ +ℕ N₂ in
      ∣ N , (λ n N≤n →
        let n₁ : N₁ ≤ n
            n₁ = ≤-trans (≤SumLeft {n = N₁} {k = N₂}) N≤n
            n₂ : N₂ ≤ n
            n₂ = ≤-trans (subst (N₂ ≤_) (+-comm N₂ N₁) (≤SumLeft {n = N₂} {k = N₁})) N≤n
            nN₁ : N₁ ≤ N
            nN₁ = ≤SumLeft {n = N₁} {k = N₂}
            nN₂ : N₂ ≤ N
            nN₂ = subst (N₂ ≤_) (+-comm N₂ N₁) (≤SumLeft {n = N₂} {k = N₁})
        in cong₂ _and_ (s₁ n n₁) (s₂ n n₂) ∙ sym (cong₂ _and_ (s₁ N nN₁) (s₂ N nN₂))) ∣₁ })
    ef eg

  decToBool : {A : Type₀} → Dec A → Bool
  decToBool (yes _) = true
  decToBool (no _) = false

  fcSingleton : ℕ → FinCof
  fcSingleton n = (λ m → decToBool (discreteℕ m n)) ,
    ∣ suc n , (λ m sn≤m → helper m sn≤m) ∣₁
    where
    helper : (m : ℕ) → suc n ≤ m → decToBool (discreteℕ m n) ≡ decToBool (discreteℕ (suc n) n)
    helper m sn≤m with discreteℕ m n | discreteℕ (suc n) n
    ... | yes m≡n | _ = ex-falso (¬m<m (subst (suc n ≤_) m≡n sn≤m))
    ... | no _ | yes sn≡n = ex-falso (¬m<m (subst (n <_) sn≡n ≤-refl))
    ... | no _ | no _ = refl

  open import Cubical.Data.Bool.Properties using
    (⊕-assoc; ⊕-identityʳ; ⊕-comm;
     and-assoc; and-identityʳ; and-comm; and-idem)

  private
    FC≡ : {a b : FinCof} → fst a ≡ fst b → a ≡ b
    FC≡ = Σ≡Prop (λ _ → squash₁)

    and-distR-⊕ : (x y z : Bool) → x and (y ⊕ z) ≡ (x and y) ⊕ (x and z)
    and-distR-⊕ false _ _ = refl
    and-distR-⊕ true y z = refl

    ⊕-invR : (x : Bool) → x ⊕ x ≡ false
    ⊕-invR false = refl
    ⊕-invR true = refl

  FinCofBR : BooleanRing ℓ-zero
  FinCofBR = idemCommRing→BR FinCofCR FinCof-idem
    where
    FinCofCR : CommRing ℓ-zero
    FinCofCR = makeCommRing {R = FinCof}
      fcEmpty fcFull fcXor fcAnd (λ x → x)
      isSetFinCof
      (λ x y z → FC≡ (funExt (λ n → ⊕-assoc (fst x n) (fst y n) (fst z n))))
      (λ x → FC≡ (funExt (λ n → ⊕-identityʳ (fst x n))))
      (λ x → FC≡ (funExt (λ n → ⊕-invR (fst x n))))
      (λ x y → FC≡ (funExt (λ n → ⊕-comm (fst x n) (fst y n))))
      (λ x y z → FC≡ (funExt (λ n → and-assoc (fst x n) (fst y n) (fst z n))))
      (λ x → FC≡ (funExt (λ n → and-identityʳ (fst x n))))
      (λ x y z → FC≡ (funExt (λ n → and-distR-⊕ (fst x n) (fst y n) (fst z n))))
      (λ x y → FC≡ (funExt (λ n → and-comm (fst x n) (fst y n))))

    FinCof-idem : isIdemRing FinCofCR
    FinCof-idem x = FC≡ (funExt (λ n → and-idem (fst x n)))

  fcSingleton-disjoint : (m n : ℕ) → ¬ (m ≡ n) →
    fcAnd (fcSingleton m) (fcSingleton n) ≡ fcEmpty
  fcSingleton-disjoint m n m≠n = FC≡ (funExt helper)
    where
    helper : (k : ℕ) → decToBool (discreteℕ k m) and decToBool (discreteℕ k n) ≡ false
    helper k with discreteℕ k m | discreteℕ k n
    ... | yes k≡m | yes k≡n = ex-falso (m≠n (sym k≡m ∙ k≡n))
    ... | yes _ | no _ = refl
    ... | no _ | yes _ = refl
    ... | no _ | no _ = refl

  fcSingleton-self : (n : ℕ) → decToBool (discreteℕ n n) ≡ true
  fcSingleton-self n with discreteℕ n n
  ... | yes _ = refl
  ... | no n≠n = ex-falso (n≠n refl)

open FinCofSubsets public

module B∞→FinCof where
  private
    φ-free : BoolHom (freeBA ℕ) FinCofBR
    φ-free = inducedBAHom ℕ FinCofBR fcSingleton

    φ-free-on-gen : (n : ℕ) → fst φ-free (gen n) ≡ fcSingleton n
    φ-free-on-gen n = funExt⁻ (evalBAInduce ℕ FinCofBR fcSingleton) n

    open IsCommRingHom (snd φ-free) renaming (pres· to φ-free-pres·)

    m<m+suc : (m d : ℕ) → m < m +ℕ suc d
    m<m+suc m d = d , +-suc d m ∙ cong suc (+-comm d m) ∙ sym (+-suc m d)

    m≠m+suc : (m d : ℕ) → ¬ (m ≡ m +ℕ suc d)
    m≠m+suc m d p = ¬m<m (subst (_< m +ℕ suc d) p (m<m+suc m d))

    φ-free-kills-rel : (k : ℕ) → fst φ-free (relB∞ k) ≡ BooleanRingStr.𝟘 (snd FinCofBR)
    φ-free-kills-rel k =
      let (m , d) = cantorUnpair k
          n = m +ℕ suc d
      in
      fst φ-free (gen m · gen n)
        ≡⟨ φ-free-pres· (gen m) (gen n) ⟩
      fcAnd (fst φ-free (gen m)) (fst φ-free (gen n))
        ≡⟨ cong₂ fcAnd (φ-free-on-gen m) (φ-free-on-gen n) ⟩
      fcAnd (fcSingleton m) (fcSingleton n)
        ≡⟨ fcSingleton-disjoint m n (m≠m+suc m d) ⟩
      fcEmpty ∎

  φ : BoolHom B∞ FinCofBR
  φ = QB.inducedHom FinCofBR φ-free φ-free-kills-rel

  φ-on-gen : (n : ℕ) → fst φ (g∞ n) ≡ fcSingleton n
  φ-on-gen n =
    fst φ (g∞ n)
      ≡⟨ cong (λ h → fst h (gen n)) (QB.evalInduce FinCofBR) ⟩
    fst φ-free (gen n)
      ≡⟨ φ-free-on-gen n ⟩
    fcSingleton n ∎

open B∞→FinCof public hiding (φ)
