{-# OPTIONS --cubical --guardedness --lossy-unification #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Algebra.AbGroup
open import Cubical.Functions.Surjection
open import Trichotomy

module CechProperties
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

open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin.Base using (Fin ; fzero ; fsuc)
open import Cubical.Data.Nat.Order.Inductive using (_<ᵗ_ ; isProp<ᵗ)
open import Cubical.Data.Int.Base using (ℤ ; pos ; negsuc)
open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Unit using (Unit* ; tt* ; isPropUnit*)

open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.ZAction

open import CechBase _<S_ isSTO isSetX q isSurjQ A
open import CechPermutations _<S_ isSTO isSetX q isSurjQ A
open import CechSorting _<S_ isSTO isSetX q isSurjQ A

-- ============================================================
-- Convert strict ordering to weak ordering
-- ============================================================

strict→weak : {n : ℕ} {x : X} (t : Tuple n x) → IsStrictlyOrdered t → IsWeaklyOrdered t
strict→weak {zero} _ _ = tt*
strict→weak {suc n} t (h< , rest) = is-asym _ _ h< , strict→weak (t ∘ fsuc) rest

-- IsStrictlyOrdered is a proposition
isPropStrictOrd : {n : ℕ} {x : X} (t : Tuple n x) → isProp (IsStrictlyOrdered t)
isPropStrictOrd {zero} _ = isPropUnit*
isPropStrictOrd {suc n} t = isProp× (is-prop-valued _ _) (isPropStrictOrd (t ∘ fsuc))

-- ============================================================
-- Insert preserves sorted tuples
-- ============================================================

insert-result< : {n : ℕ} {x : X} (t : Tuple (suc n) x)
  (tw : IsWeaklyOrdered (t ∘ fsuc))
  → (h< : fst (t fzero) <S fst ((t ∘ fsuc) fzero))
  → (fst (insert (t fzero) (t ∘ fsuc) tw) ≡ t)
    × (fst (snd (snd (insert (t fzero) (t ∘ fsuc) tw))) ≡ 0)
insert-result< {zero} t tw h< with triF (t fzero) ((t ∘ fsuc) fzero)
... | tri< _ _ _ =
  funExt (λ { (zero , p) → cong (λ q → t (zero , q)) (isProp<ᵗ _ p)
            ; (suc zero , p) → cong (λ q → t (suc zero , q)) (isProp<ᵗ _ p)
            ; (suc (suc _) , ()) }) , refl
... | tri≡ ¬a _ _ = ⊥-rec (¬a h<)
... | tri> ¬a _ _ = ⊥-rec (¬a h<)
insert-result< {suc n} t tw h< with triF (t fzero) ((t ∘ fsuc) fzero)
... | tri< _ _ _ =
  funExt (λ { (zero , p) → cong (λ q → t (zero , q)) (isProp<ᵗ _ p)
            ; (suc k , p) → refl }) , refl
... | tri≡ ¬a _ _ = ⊥-rec (¬a h<)
... | tri> ¬a _ _ = ⊥-rec (¬a h<)

-- ============================================================
-- Sorting preserves strictly ordered tuples
-- ============================================================

sortTuple-sorted : {n : ℕ} {x : X} (t : Tuple n x) → (ord : IsStrictlyOrdered t)
  → (fst (sortTuple t) ≡ t) × (fst (snd (sortTuple t)) ≡ pos 1)
sortTuple-sorted {zero} t _ = refl , refl
sortTuple-sorted {suc n} t (h< , rest-ord) = fst ir , signProof
  where
  IH = sortTuple-sorted (t ∘ fsuc) rest-ord
  sortEq = fst IH
  sgn≡ = snd IH
  ts = fst (sortTuple (t ∘ fsuc))
  tail-sgn = fst (snd (sortTuple (t ∘ fsuc)))
  tw = snd (snd (sortTuple (t ∘ fsuc)))
  h<' = subst (λ u → fst (t fzero) <S fst (u fzero)) (sym sortEq) h<
  ir = J (λ u _ → (w : IsWeaklyOrdered u) → (h : fst (t fzero) <S fst (u fzero))
                 → (fst (insert (t fzero) u w) ≡ t)
                   × (fst (snd (snd (insert (t fzero) u w))) ≡ 0))
         (λ w h → insert-result< t w h)
         (sym sortEq) tw h<'
  signProof = cong (λ sw → mulSign (signFromSwaps sw) tail-sgn) (snd ir) ∙ sgn≡

-- ============================================================
-- Strictly ordered tuples have strictly increasing heads
-- ============================================================

strict-head-lt : {n : ℕ} {x : X} (t : Tuple (suc n) x) → IsStrictlyOrdered t
  → (j : Fin (suc n)) → fst (t fzero) <S fst (t (fsuc j))
strict-head-lt {zero} t (h< , _) (zero , tt) = h<
strict-head-lt {zero} t _ (suc _ , ())
strict-head-lt {suc n} t (h< , rest) (zero , tt) = h<
strict-head-lt {suc n} t (h< , rest) (suc k , p) =
  is-trans _ _ _ h< (strict-head-lt (t ∘ fsuc) rest (k , p))

-- ============================================================
-- Strictly ordered tuples have no repeats
-- ============================================================

strict-no-repeat : {n : ℕ} {x : X} (t : Tuple n x) → IsStrictlyOrdered t → HasRepeat t → ⊥
strict-no-repeat {zero} t _ ((zero , tt) , (zero , tt) , prf) = fst prf refl
strict-no-repeat {zero} t _ ((suc _ , ()) , _)
strict-no-repeat {zero} t _ ((zero , _) , (suc _ , ()) , _)
strict-no-repeat {suc n} t _ ((zero , tt) , (zero , tt) , prf) = fst prf refl
strict-no-repeat {suc n} t ord ((zero , tt) , (suc k , p₂) , prf) =
  is-irrefl _ (subst (fst (t fzero) <S_) (sym (snd prf)) (strict-head-lt t ord (k , p₂)))
strict-no-repeat {suc n} t ord ((suc k , p₁) , (zero , tt) , prf) =
  is-irrefl _ (subst (fst (t fzero) <S_) (snd prf) (strict-head-lt t ord (k , p₁)))
strict-no-repeat {suc n} t (_ , rest) ((suc k , p₁) , (suc l , p₂) , prf) =
  strict-no-repeat (t ∘ fsuc) rest
    ((k , p₁) , (l , p₂) , (λ q → fst prf (cong fsuc q)) , snd prf)

-- ============================================================
-- π ∘ c = id on ordered cochains
-- ============================================================

π∘c≡id : {n : ℕ} → (β : OrdCochain n)
  → (x : X) → (ot : OrdTuple n x)
  → π (cMap β) x ot ≡ β x ot
π∘c≡id {zero} β x (t , tt*) = Gx.+IdR x (β x (t , tt*))
π∘c≡id {suc n} β x (t , ord) = go (weakToStrictDec t' wo)
  where
  t' = fst (sortTuple t)
  sgn = fst (snd (sortTuple t))
  wo = snd (snd (sortTuple t))
  tEq = fst (sortTuple-sorted t ord)
  sEq = snd (sortTuple-sorted t ord)
  go : (wd : IsStrictlyOrdered t' ⊎ HasRepeat t')
     → cMap-go β sgn t' wd ≡ β x (t , ord)
  go (inl strict) =
    cong (λ s → s ℤ· β x (t' , strict)) sEq
    ∙ Gx.+IdR x (β x (t' , strict))
    ∙ J (λ u _ → (o : IsStrictlyOrdered u) → β x (t' , strict) ≡ β x (u , o))
        (λ o → cong (λ z → β x (t' , z)) (isPropStrictOrd t' strict o))
        tEq ord
  go (inr rep) = ⊥-rec (strict-no-repeat t ord (subst HasRepeat tEq rep))
    where open import Cubical.Data.Empty renaming (rec to ⊥-rec)
