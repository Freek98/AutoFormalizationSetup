{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection
open import Trichotomy

module CechSorting
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

open import Cubical.Data.Nat using (ℕ ; zero ; suc ; znots)
open import Cubical.Data.Fin.Base using (Fin ; fzero ; fsuc)
open import Cubical.Data.Int.Base using (ℤ ; pos ; negsuc)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)


open import CechBase _<S_ isSTO isSetX q isSurjQ A
open import CechPermutations _<S_ isSTO isSetX q isSurjQ A

-- ============================================================
-- Sorting pairs
-- ============================================================

sort2 : {x : X} → Fiber x → Fiber x → Fiber x × Fiber x × ℤ
sort2 a b with triF a b
... | tri< _ _ _ = a , b , pos 1
... | tri≡ _ _ _ = a , b , pos 1
... | tri> _ _ _ = b , a , negsuc 0

-- ============================================================
-- Insertion sort
-- ============================================================

insert : {n : ℕ} {x : X} → (s : Fiber x) → (t : Tuple n x)
  → IsWeaklyOrdered t
  → Σ[ t' ∈ Tuple (suc n) x ]
      IsWeaklyOrdered t' × ℕ ×
      ((a : S) → a ≤S fst s → a ≤S fst (t fzero) → a ≤S fst (t' fzero))
insert {zero} {x} s t _ = go (triF s (t fzero))
  where
  b = t fzero

  go : Tri (s <F b) (fst s ≡ fst b) (b <F s)
     → Σ[ t' ∈ Tuple 1 x ]
         IsWeaklyOrdered t' × ℕ ×
         ((a : S) → a ≤S fst s → a ≤S fst b → a ≤S fst (t' fzero))
  go (tri< a<b _ _) =
    (λ { (zero , _) → s ; (suc zero , _) → b ; (suc (suc _) , ()) })
    , ((λ gt → is-asym _ _ a<b gt) , tt*) , 0
    , (λ _ a≤s _ → a≤s)
  go (tri≡ _ a≡b _) =
    (λ { (zero , _) → s ; (suc zero , _) → b ; (suc (suc _) , ()) })
    , ((λ gt → is-irrefl _ (subst (_<S fst s) (sym a≡b) gt)) , tt*) , 0
    , (λ _ a≤s _ → a≤s)
  go (tri> _ _ b<a) =
    (λ { (zero , _) → b ; (suc zero , _) → s ; (suc (suc _) , ()) })
    , ((λ gt → is-asym _ _ b<a gt) , tt*) , 1
    , (λ _ _ a≤h → a≤h)
insert {suc n} {x} s t wo =
  go (triF s (t fzero))
  where
  go : Tri (s <F t fzero) (fst s ≡ fst (t fzero)) (t fzero <F s)
     → Σ[ t' ∈ Tuple (suc (suc n)) x ]
         IsWeaklyOrdered t' × ℕ ×
         ((a : S) → a ≤S fst s → a ≤S fst (t fzero) → a ≤S fst (t' fzero))
  go (tri< s<h _ _) =
    (λ { (zero , _) → s ; (suc k , p) → t (k , p) })
    , ((λ h<s → is-asym _ _ s<h h<s) , wo)
    , 0 , (λ _ a≤s _ → a≤s)
  go (tri≡ _ s≡h _) =
    (λ { (zero , _) → s ; (suc k , p) → t (k , p) })
    , ((λ h<s → is-irrefl _ (subst (_<S fst s) (sym s≡h) h<s)) , wo)
    , 0 , (λ _ a≤s _ → a≤s)
  go (tri> _ _ h<s) =
    let rec = insert s (t ∘ fsuc) (snd wo)
        rest = fst rec
        restWO = fst (snd rec)
        restSwaps = fst (snd (snd rec))
        restMinPrf = snd (snd (snd rec))
        headPrf : fst (t fzero) ≤S fst (rest fzero)
        headPrf = restMinPrf (fst (t fzero))
          (is-asym _ _ h<s) (fst wo)
    in (λ { (zero , _) → t fzero ; (suc k , p) → rest (k , p) })
       , (headPrf , restWO)
       , suc restSwaps
       , (λ _ _ a≤h → a≤h)

-- Multiply signs
mulSign : ℤ → ℤ → ℤ
mulSign (pos 1) s = s
mulSign (negsuc 0) (pos 1) = negsuc 0
mulSign (negsuc 0) (negsuc 0) = pos 1
mulSign _ s = s

-- Sign from swap count
signFromSwaps : ℕ → ℤ
signFromSwaps n with parityℕ n
... | true  = pos 1
... | false = negsuc 0

-- Full sorting function
sortTuple : {n : ℕ} {x : X} → Tuple n x
  → Σ[ t' ∈ Tuple n x ]
    Σ[ sgn ∈ ℤ ]
    IsWeaklyOrdered t'
sortTuple {zero} t = t , pos 1 , tt*
sortTuple {suc n} t =
  let (tail-sorted , tail-sgn , tail-wo) = sortTuple (t ∘ fsuc)
      rec = insert (t fzero) tail-sorted tail-wo
      result = fst rec
      result-wo = fst (snd rec)
      swaps = fst (snd (snd rec))
  in result , mulSign (signFromSwaps swaps) tail-sgn , result-wo

-- ============================================================
-- Check weak → strict or has repeat
-- ============================================================

mapRepeatSucc : {n : ℕ} {x : X} {t : Tuple (suc n) x}
  → HasRepeat (t ∘ fsuc) → HasRepeat t
mapRepeatSucc (i , j , neq , p) =
  fsuc i , fsuc j , (λ q → neq (fsuc-inj q)) , p

weakToStrictDec : {n : ℕ} {x : X} → (t : Tuple n x)
  → IsWeaklyOrdered t
  → (IsStrictlyOrdered t) ⊎ (HasRepeat t)
weakToStrictDec {zero} t _ = inl tt*
weakToStrictDec {suc n} t (h≤ , rest) = go (is-tri (fst (t fzero)) (fst (t (fsuc fzero))))
  where
  go : Tri (fst (t fzero) <S fst (t (fsuc fzero)))
           (fst (t fzero) ≡ fst (t (fsuc fzero)))
           (fst (t (fsuc fzero)) <S fst (t fzero))
     → (IsStrictlyOrdered t) ⊎ (HasRepeat t)
  go (tri< a<b _ _) with weakToStrictDec (t ∘ fsuc) rest
  ... | inl strict = inl (a<b , strict)
  ... | inr rep    = inr (mapRepeatSucc {t = t} rep)
  go (tri≡ _ a≡b _) =
    inr (fzero , fsuc fzero ,
         (λ p → znots (cong fst p)) , a≡b)
  go (tri> _ _ b<a) = ⊥-rec (h≤ b<a)

-- ============================================================
-- The c map (ordered → standard cochain)
-- ============================================================

cMap-go : {n : ℕ} {x : X} → OrdCochain n → ℤ
  → (t' : Tuple n x) → IsStrictlyOrdered t' ⊎ HasRepeat t' → Ax x
cMap-go {x = x} β sgn t' (inl strict) = sgn ℤ· β x (t' , strict)
cMap-go {x = x} _ _ _ (inr _) = Gx.0g x

cMap : {n : ℕ} → OrdCochain n → Cochain n
cMap {n} β x t =
  let st = sortTuple t
  in cMap-go β (fst (snd st)) (fst st) (weakToStrictDec (fst st) (snd (snd st)))
