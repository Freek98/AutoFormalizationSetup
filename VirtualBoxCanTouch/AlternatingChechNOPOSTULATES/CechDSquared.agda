{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection
open import Trichotomy

module CechDSquared
  {ℓ : Level}
  {S : Type ℓ}
  {X : Type ℓ}
  (_<S_ : S → S → Type ℓ)
  (isSTO : IsStrictTotalOrder _<S_)
  (isSetX : isSet X)
  (q : S → X)
  (isSurjQ : isSurjection q)
  (A : X → AbGroup ℓ)
  where

open import Cubical.Foundations.Function

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; znots ; snotz)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Fin.Base using (Fin ; fzero ; fsuc)
open import Cubical.Data.Nat.Order.Inductive using (_<ᵗ_ ; isProp<ᵗ)
open import Cubical.Data.Int.Base using (ℤ ; pos ; negsuc)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit ; tt ; Unit* ; tt*)

open import Cubical.Relation.Nullary

open import Cubical.Algebra.Group.ZAction

open import CechBase _<S_ isSTO isSetX q isSurjQ A
open import CechFaceMaps _<S_ isSTO isSetX q isSurjQ A

-- ============================================================
-- Distribute ℤ-action over sumFin
-- ============================================================

sumFin-ℤ· : {x : X} (s : ℤ) (m : ℕ) (f : Fin m → Ax x)
  → s ℤ· sumFin m f ≡ sumFin m (λ i → s ℤ· f i)
sumFin-ℤ· {x} s zero f = rUnitℤ· (AbGroup→Group (A x)) s
sumFin-ℤ· {x} s (suc m) f =
  ℤ·isHom s (A x) (f fzero) (sumFin m (f ∘ fsuc))
  ∙ cong (Gx._+_ x (s ℤ· f fzero)) (sumFin-ℤ· s m (f ∘ fsuc))

-- Sum of zeros is zero
sumFin-0 : {x : X} (m : ℕ) → sumFin {x} m (λ _ → Gx.0g x) ≡ Gx.0g x
sumFin-0 {x} zero = refl
sumFin-0 {x} (suc m) = Gx.+IdL x _ ∙ sumFin-0 m

-- Pointwise addition of sums
sumFin-add : {x : X} (m : ℕ) (f g : Fin m → Ax x)
  → Gx._+_ x (sumFin m f) (sumFin m g) ≡ sumFin m (λ i → Gx._+_ x (f i) (g i))
sumFin-add {x} zero f g = Gx.+IdL x _
sumFin-add {x} (suc m) f g =
  let _+_ = Gx._+_ x
      f0 = f fzero ; g0 = g fzero
      Σf = sumFin m (f ∘ fsuc) ; Σg = sumFin m (g ∘ fsuc)
  in sym (Gx.+Assoc x f0 Σf (g0 + Σg))
   ∙ cong (f0 +_) (Gx.+Assoc x Σf g0 Σg
     ∙ cong (_+ Σg) (Gx.+Comm x Σf g0)
     ∙ sym (Gx.+Assoc x g0 Σf Σg))
   ∙ Gx.+Assoc x f0 g0 (Σf + Σg)
   ∙ cong ((f0 + g0) +_) (sumFin-add m (f ∘ fsuc) (g ∘ fsuc))

-- ============================================================
-- Sign lemmas
-- ============================================================

signℤ-ss : (n : ℕ) → signℤ (suc (suc n)) ≡ signℤ n
signℤ-ss n with parityℕ n
... | true = refl
... | false = refl

sign-cancel : {x : X} (n : ℕ) (a : Ax x)
  → Gx._+_ x (signℤ n ℤ· a) (signℤ (suc n) ℤ· a) ≡ Gx.0g x
sign-cancel {x} zero a =
  sym (Gx.+Assoc x a (Gx.0g x) (Gx.-_ x a))
  ∙ cong (Gx._+_ x a) (Gx.+IdL x (Gx.-_ x a))
  ∙ Gx.+InvR x a
sign-cancel {x} (suc zero) a =
  cong (Gx._+_ x (Gx.-_ x a)) (Gx.+IdR x a)
  ∙ Gx.+InvL x a
sign-cancel {x} (suc (suc n)) a =
  cong₂ (Gx._+_ x) (cong (_ℤ· a) (signℤ-ss n)) (cong (_ℤ· a) (signℤ-ss (suc n)))
  ∙ sign-cancel n a

sign-comm : {x : X} (a b : ℕ) (v : Ax x)
  → signℤ a ℤ· (signℤ b ℤ· v) ≡ signℤ b ℤ· (signℤ a ℤ· v)
sign-comm {x} a b v with parityℕ a | parityℕ b
... | true  | true  = refl
... | true  | false =
  Gx.+IdR x (Gx.-_ x v) ∙ sym (cong (Gx.-_ x) (Gx.+IdR x v))
... | false | true  =
  cong (Gx.-_ x) (Gx.+IdR x v) ∙ sym (Gx.+IdR x (Gx.-_ x v))
... | false | false = refl

-- ============================================================
-- Rearrange a + (b + c) = b + (a + c)
-- ============================================================

+rearrange : {x : X} (a b c : Ax x)
  → Gx._+_ x a (Gx._+_ x b c) ≡ Gx._+_ x b (Gx._+_ x a c)
+rearrange {x} a b c =
  Gx.+Assoc x a b c
  ∙ cong (λ z → Gx._+_ x z c) (Gx.+Comm x a b)
  ∙ sym (Gx.+Assoc x b a c)

-- ============================================================
-- Remove position from index
-- ============================================================

removeIdx : {m : ℕ} → Fin (suc m) → Fin m → Fin (suc m)
removeIdx {zero} _ ()
removeIdx {suc m} (zero , _) k = fsuc k
removeIdx {suc m} (suc j , jp) (zero , _) = fzero
removeIdx {suc m} (suc j , jp) (suc k , kp) = fsuc (removeIdx (j , jp) (k , kp))

-- Extract element j from a sum (move it to front)
sumFin-extract : {x : X} (m : ℕ) (f : Fin (suc m) → Ax x) (j : Fin (suc m))
  → sumFin (suc m) f ≡ Gx._+_ x (f j) (sumFin m (f ∘ removeIdx j))
sumFin-extract zero f (zero , _) = refl
sumFin-extract (suc m) f (zero , _) = refl
sumFin-extract {x} (suc m) f (suc j , jp) =
  cong (Gx._+_ x (f fzero)) (sumFin-extract m (f ∘ fsuc) (j , jp))
  ∙ +rearrange (f fzero) (f (suc j , jp)) (sumFin m (f ∘ fsuc ∘ removeIdx (j , jp)))

-- ============================================================
-- Pair cancellation in d²
-- ============================================================

d²-pair-cancel : {n : ℕ} (α : Cochain n) (x : X) (t : Tuple (suc (suc n)) x)
  (i : Fin (suc (suc (suc n)))) (j : Fin (suc (suc n)))
  → (le : fst i ≤ fst j) → (ip' : fst i <ᵗ suc (suc n))
  → Gx._+_ x
      (signℤ (fst i) ℤ· (signℤ (fst j) ℤ· α x (t ∘ skip i ∘ skip j)))
      (signℤ (suc (fst j)) ℤ· (signℤ (fst i) ℤ· α x (t ∘ skip (fsuc j) ∘ skip (fst i , ip'))))
    ≡ Gx.0g x
d²-pair-cancel {n} α x t i j le ip' =
  let v = α x (t ∘ skip i ∘ skip j)
      v' = α x (t ∘ skip (fsuc j) ∘ skip (fst i , ip'))
      vp : v ≡ v'
      vp = cong (α x) (funExt (λ k → cong t (skip-skip i j le ip' k)))
      w = signℤ (fst i) ℤ· v'
  in cong₂ (Gx._+_ x)
       (cong (signℤ (fst i) ℤ·_) (cong (signℤ (fst j) ℤ·_) vp)
        ∙ sign-comm (fst i) (fst j) v')
       refl
     ∙ sign-cancel (fst j) w

-- ============================================================
-- Fin helpers for involution cancellation
-- ============================================================

fin1-unique : (x : Fin 1) → x ≡ fzero
fin1-unique (zero , _) = Fin≡ refl

fzero≢fsuc : {m : ℕ} (j : Fin m) → fzero ≡ fsuc j → ⊥
fzero≢fsuc _ p = znots (cong fst p)

fsuc-pred : {m : ℕ} (x : Fin (suc m)) → ¬ (x ≡ fzero)
  → Σ[ y ∈ Fin m ] fsuc y ≡ x
fsuc-pred (zero , p) nz = ⊥-rec (nz (Fin≡ refl))
fsuc-pred (suc k , p) _ = (k , p) , Fin≡ refl

-- ============================================================
-- removeIdx properties
-- ============================================================

removeIdx-inj : {m : ℕ} (j : Fin (suc m)) (a b : Fin m)
  → removeIdx j a ≡ removeIdx j b → a ≡ b
removeIdx-inj {zero} _ () ()
removeIdx-inj {suc m} (zero , _) a b p = fsuc-inj p
removeIdx-inj {suc m} (suc j , jp) (zero , _) (zero , _) _ = refl
removeIdx-inj {suc m} (suc j , jp) (zero , _) (suc b , bp) p =
  ⊥-rec (fzero≢fsuc _ p)
removeIdx-inj {suc m} (suc j , jp) (suc a , ap) (zero , _) p =
  ⊥-rec (fzero≢fsuc _ (sym p))
removeIdx-inj {suc m} (suc j , jp) (suc a , ap) (suc b , bp) p =
  cong fsuc (removeIdx-inj (j , jp) (a , ap) (b , bp) (fsuc-inj p))

removeIdx-misses : {m : ℕ} (j : Fin (suc m)) (k : Fin m)
  → ¬ (removeIdx j k ≡ j)
removeIdx-misses {zero} (zero , _) ()
removeIdx-misses {suc m} (zero , _) k p = fzero≢fsuc k (sym p)
removeIdx-misses {suc m} (suc j , jp) (zero , _) p =
  fzero≢fsuc (j , jp) p
removeIdx-misses {suc m} (suc j , jp) (suc k , kp) p =
  removeIdx-misses (j , jp) (k , kp) (fsuc-inj p)

removeIdx-surj : {m : ℕ} (j : Fin (suc m)) (y : Fin (suc m))
  → ¬ (y ≡ j) → Σ[ k ∈ Fin m ] removeIdx j k ≡ y
removeIdx-surj {zero} (zero , _) (zero , _) neq = ⊥-rec (neq (Fin≡ refl))
removeIdx-surj {suc m} (zero , _) (zero , _) neq = ⊥-rec (neq (Fin≡ refl))
removeIdx-surj {suc m} (zero , _) (suc k , kp) _ = (k , kp) , Fin≡ refl
removeIdx-surj {suc m} (suc j , jp) (zero , _) _ = fzero , Fin≡ refl
removeIdx-surj {suc m} (suc j , jp) (suc y , yp) neq =
  let rec = removeIdx-surj (j , jp) (y , yp) (λ q → neq (cong fsuc q))
  in fsuc (fst rec) , cong fsuc (snd rec)

-- ============================================================
-- Involution cancellation on sums
-- ============================================================

sumFin-invol-cancel : {x : X} (m : ℕ) (f : Fin m → Ax x)
  (φ : Fin m → Fin m)
  → (cancel : ∀ k → Gx._+_ x (f k) (f (φ k)) ≡ Gx.0g x)
  → (invol : ∀ k → φ (φ k) ≡ k)
  → (no-fix : ∀ k → ¬ (φ k ≡ k))
  → sumFin m f ≡ Gx.0g x
sumFin-invol-cancel zero _ _ _ _ _ = refl
sumFin-invol-cancel (suc zero) _ φ _ _ no-fix =
  ⊥-rec (no-fix fzero (fin1-unique (φ fzero)))
sumFin-invol-cancel {x} (suc (suc m)) f φ cancel invol no-fix =
  let j₀ = φ fzero
      j₀≢0 : ¬ (j₀ ≡ fzero)
      j₀≢0 = no-fix fzero
      pred-j₀ = fsuc-pred j₀ j₀≢0
      j₀' : Fin (suc m)
      j₀' = fst pred-j₀
      j₀'eq : fsuc j₀' ≡ j₀
      j₀'eq = snd pred-j₀
      embed : Fin m → Fin (suc (suc m))
      embed k = fsuc (removeIdx j₀' k)
      embed-inj : (a b : Fin m) → embed a ≡ embed b → a ≡ b
      embed-inj a b p = removeIdx-inj j₀' a b (fsuc-inj p)
      φ-embed≢0 : (k : Fin m) → ¬ (φ (embed k) ≡ fzero)
      φ-embed≢0 k p = removeIdx-misses j₀' k
        (fsuc-inj (sym (invol (embed k)) ∙ cong φ p ∙ sym j₀'eq))
      φ-embed≢j₀ : (k : Fin m) → ¬ (φ (embed k) ≡ j₀)
      φ-embed≢j₀ k p = snotz
        (cong fst (sym (invol (embed k)) ∙ cong φ p ∙ invol fzero))
      decode : (k : Fin m) → Σ[ r ∈ Fin m ] embed r ≡ φ (embed k)
      decode k =
        let z = φ (embed k)
            zpred = fsuc-pred z (φ-embed≢0 k)
            y = fst zpred
            yeq : fsuc y ≡ z
            yeq = snd zpred
            y≢j₀' : ¬ (y ≡ j₀')
            y≢j₀' q = φ-embed≢j₀ k (sym yeq ∙ cong fsuc q ∙ j₀'eq)
            rs = removeIdx-surj j₀' y y≢j₀'
        in fst rs , cong fsuc (snd rs) ∙ yeq
      φ' : Fin m → Fin m
      φ' k = fst (decode k)
      embed-φ' : (k : Fin m) → embed (φ' k) ≡ φ (embed k)
      embed-φ' k = snd (decode k)
      cancel' : (k : Fin m) → Gx._+_ x (f (embed k)) (f (embed (φ' k))) ≡ Gx.0g x
      cancel' k = cong (λ z → Gx._+_ x (f (embed k)) (f z)) (embed-φ' k)
        ∙ cancel (embed k)
      invol' : (k : Fin m) → φ' (φ' k) ≡ k
      invol' k = embed-inj (φ' (φ' k)) k
        (embed-φ' (φ' k) ∙ cong φ (embed-φ' k) ∙ invol (embed k))
      no-fix' : (k : Fin m) → ¬ (φ' k ≡ k)
      no-fix' k p = no-fix (embed k) (sym (embed-φ' k) ∙ cong embed p)
      extract-step : sumFin (suc m) (f ∘ fsuc) ≡
        Gx._+_ x (f j₀) (sumFin m (f ∘ embed))
      extract-step = sumFin-extract m (f ∘ fsuc) j₀'
        ∙ cong (λ z → Gx._+_ x (f z) (sumFin m (f ∘ embed)))
               j₀'eq
  in cong (Gx._+_ x (f fzero)) extract-step
     ∙ Gx.+Assoc x (f fzero) (f j₀) (sumFin m (f ∘ embed))
     ∙ cong (λ z → Gx._+_ x z (sumFin m (f ∘ embed)))
            (cancel fzero)
     ∙ Gx.+IdL x (sumFin m (f ∘ embed))
     ∙ sumFin-invol-cancel m (f ∘ embed) φ' cancel' invol' no-fix'

-- ============================================================
-- Double sum cancellation
-- ============================================================

doubleSum-cancel : {x : X} (M : ℕ) (F : Fin (suc M) → Fin M → Ax x)
  → (∀ (i : Fin (suc M)) (j : Fin M) → fst i ≤ fst j
     → (ip : fst i <ᵗ M)
     → Gx._+_ x (F i j) (F (fsuc j) (fst i , ip)) ≡ Gx.0g x)
  → sumFin (suc M) (λ i → sumFin M (F i)) ≡ Gx.0g x
doubleSum-cancel {x} zero F pc = Gx.+IdL x (Gx.0g x)
doubleSum-cancel {x} (suc M') F pc =
  let f : Fin (suc M') → Ax x
      f i = F (fsuc i) fzero
      g : Fin (suc M') → Ax x
      g i = sumFin M' (λ j → F (fsuc i) (fsuc j))
      Σf = sumFin (suc M') f
      Σg = sumFin (suc M') g
      pair0 : (k : Fin (suc M')) → Gx._+_ x (F fzero k) (F (fsuc k) fzero) ≡ Gx.0g x
      pair0 k = pc fzero k zero-≤ tt
      cancel-0 : Gx._+_ x (sumFin (suc M') (F fzero)) Σf ≡ Gx.0g x
      cancel-0 = sumFin-add (suc M') (F fzero) f
        ∙ cong (sumFin (suc M')) (funExt pair0) ∙ sumFin-0 (suc M')
      F' : Fin (suc M') → Fin M' → Ax x
      F' i j = F (fsuc i) (fsuc j)
      pc' : ∀ (i : Fin (suc M')) (j : Fin M') → fst i ≤ fst j
        → (ip : fst i <ᵗ M') → Gx._+_ x (F' i j) (F' (fsuc j) (fst i , ip)) ≡ Gx.0g x
      pc' i j le ip = pc (fsuc i) (fsuc j) (suc-≤-suc le) ip
      IH : sumFin (suc M') (λ i → sumFin M' (F' i)) ≡ Gx.0g x
      IH = doubleSum-cancel M' F' pc'
  in cong (Gx._+_ x (sumFin (suc M') (F fzero))) (sym (sumFin-add (suc M') f g))
     ∙ Gx.+Assoc x (sumFin (suc M') (F fzero)) Σf Σg
     ∙ cong (λ z → Gx._+_ x z Σg) cancel-0
     ∙ Gx.+IdL x Σg
     ∙ IH

-- ============================================================
-- d ∘ d = 0 on standard cochains
-- ============================================================

d²≡0 : {n : ℕ} → (α : Cochain n) → (x : X) → (t : Tuple (suc (suc n)) x)
  → cechDiff (cechDiff α) x t ≡ Gx.0g x
d²≡0 {n} α x t =
  let M = suc (suc n)
      F : Fin (suc M) → Fin M → Ax x
      F i j = signℤ (fst i) ℤ· (signℤ (fst j) ℤ· α x (t ∘ skip i ∘ skip j))
      step1 : cechDiff (cechDiff α) x t ≡ sumFin (suc M) (λ i → sumFin M (F i))
      step1 = cong (sumFin (suc M)) (funExt (λ i →
        sumFin-ℤ· (signℤ (fst i)) M (λ j → signℤ (fst j) ℤ· α x (t ∘ skip i ∘ skip j))))
  in step1 ∙ doubleSum-cancel M F (λ i j le ip → d²-pair-cancel α x t i j le ip)
