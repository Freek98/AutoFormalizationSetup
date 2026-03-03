{-# OPTIONS --cubical --guardedness #-}
module work.test-isset where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2)
open import Cubical.Foundations.Equiv using (propBiimpl→Equiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.GroupoidLaws using (rUnit; rCancel; assoc; symDistr)
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_; +-suc)
open import Cubical.Data.Sequence using (Sequence)
open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
open import Cubical.HITs.SequentialColimit.Properties
  using (SeqColim→Prop; ElimDataShifted; elimShifted; elimdata-shift;
         ElimData; elimdata; elim; elimShiftedβ)
open Sequence

module _ (S' : Sequence ℓ-zero) (allSet : (n : ℕ) → isSet (obj S' n)) where
 private
  sh : (k : ℕ) {n : ℕ} → obj S' n → obj S' (k + n)
  sh zero x = x
  sh (suc k) x = map S' (sh k x)

  pc : (k : ℕ) {n : ℕ} (x : obj S' n) → Path (SeqColim S') (incl x) (incl (sh k x))
  pc zero x = refl
  pc (suc k) x = pc k x ∙ push (sh k x)

  shTr : (j : ℕ) {m : ℕ} (z : obj S' m)
    → PathP (λ i → obj S' (+-suc j m (~ i))) (sh (suc j) z) (sh j (map S' z))
  shTr zero z = refl
  shTr (suc j) z i = map S' (shTr j z i)

  fwdPath : {k n₀ : ℕ} (x₀ : obj S' n₀) (y : obj S' (k + n₀))
    → {j : ℕ} → sh j (sh k x₀) ≡ sh j y
    → sh j (sh (suc k) x₀) ≡ sh j (map S' y)
  fwdPath {k} {n₀} x₀ y {j} p i =
    comp (λ t → obj S' (+-suc j (k + n₀) (~ t)))
      (λ t → λ { (i = i0) → shTr j (sh k x₀) t
                ; (i = i1) → shTr j y t })
      (cong (map S') p i)

  bwdPath : {k n₀ : ℕ} (x₀ : obj S' n₀) (y : obj S' (k + n₀))
    → {j : ℕ} → sh j (sh (suc k) x₀) ≡ sh j (map S' y)
    → sh (suc j) (sh k x₀) ≡ sh (suc j) y
  bwdPath {k} {n₀} x₀ y {j} q i =
    comp (λ t → obj S' (+-suc j (k + n₀) t))
      (λ t → λ { (i = i0) → shTr j (sh k x₀) (~ t)
                ; (i = i1) → shTr j y (~ t) })
      (q i)

  postulate
    isPropSCP : (T : Sequence ℓ-zero) → ((n : ℕ) → isProp (obj T n)) → isProp (SeqColim T)

  module EncDec {n₀ : ℕ} (x₀ : obj S' n₀) where
    pathSeq : {k : ℕ} → obj S' (k + n₀) → Sequence ℓ-zero
    obj (pathSeq {k} y) j = sh j (sh k x₀) ≡ sh j y
    map (pathSeq {k} y) = cong (map S')

    Code-incl : {k : ℕ} → obj S' (k + n₀) → Type
    Code-incl y = SeqColim (pathSeq y)

    isPropCode : {k : ℕ} (y : obj S' (k + n₀)) → isProp (Code-incl y)
    isPropCode y = isPropSCP (pathSeq y) (λ j → allSet _ _ _)

    codePush : {k : ℕ} (y : obj S' (k + n₀)) → Code-incl y ≡ Code-incl (map S' y)
    codePush {k} y = ua (propBiimpl→Equiv (isPropCode y) (isPropCode (map S' y)) fwd bwd) where
      fwd : Code-incl y → Code-incl (map S' y)
      fwd = SeqColim→Prop (λ _ → isPropCode (map S' y))
        λ j p → incl {n = j} (fwdPath x₀ y p)
      bwd : Code-incl (map S' y) → Code-incl y
      bwd = SeqColim→Prop (λ _ → isPropCode y)
        λ j q → incl {n = suc j} (bwdPath x₀ y q)

    private
      code-datum : ElimDataShifted S' n₀ (λ _ → Type ℓ-zero)
      code-datum = elimdata-shift Code-incl (λ y → codePush y)

    Code : SeqColim S' → Type
    Code = elimShifted S' n₀ (λ _ → Type ℓ-zero) code-datum

    codeβ : {k : ℕ} (y : obj S' (k + n₀)) → Code (incl y) ≡ Code-incl y
    codeβ {k} y i = elimShiftedβ S' n₀ k (λ _ → Type ℓ-zero) code-datum i y

    isPropCode' : {k : ℕ} (y : obj S' (k + n₀)) → isProp (Code (incl y))
    isPropCode' y = subst isProp (sym (codeβ y)) (isPropCode y)

    isPropCodeFull : (c : SeqColim S') → isProp (Code c)
    isPropCodeFull = elimShifted S' n₀ (λ c → isProp (Code c))
      (elimdata-shift isPropCode' (λ y → isProp→PathP (λ _ → isPropIsProp) _ _))

    code-refl-raw : Code-incl {0} x₀
    code-refl-raw = incl {n = 0} refl

    code-refl : Code (incl x₀)
    code-refl = transport (sym (codeβ x₀)) code-refl-raw

    encode : (c : SeqColim S') → incl x₀ ≡ c → Code c
    encode c p = subst Code p code-refl

    di : {k : ℕ} {y : obj S' (k + n₀)} (j : ℕ)
      → sh j (sh k x₀) ≡ sh j y → Path (SeqColim S') (incl x₀) (incl y)
    di {k} {y} j p = pc k x₀ ∙ pc j (sh k x₀) ∙ cong incl p ∙ sym (pc j y)

    dp : {k : ℕ} {y : obj S' (k + n₀)} (j : ℕ)
      (p : sh j (sh k x₀) ≡ sh j y) → di j p ≡ di (suc j) (cong (map S') p)
    dp {k} {y} j p = cong (pc k x₀ ∙_) inner where
      CS = SeqColim S'
      β  : Path CS (incl (sh k x₀)) (incl (sh j (sh k x₀)))
      β  = pc j (sh k x₀)
      γ  : Path CS (incl (sh j (sh k x₀))) (incl (sh j y))
      γ  = cong incl p
      γ' : Path CS (incl (map S' (sh j (sh k x₀)))) (incl (map S' (sh j y)))
      γ' = cong (λ z → incl (map S' z)) p
      δ  : Path CS (incl y) (incl (sh j y))
      δ  = pc j y
      πa : Path CS (incl (sh j (sh k x₀))) (incl (map S' (sh j (sh k x₀))))
      πa = push (sh j (sh k x₀))
      πb : Path CS (incl (sh j y)) (incl (map S' (sh j y)))
      πb = push (sh j y)
      nat-eq : πa ∙ γ' ≡ γ ∙ πb
      nat-eq = sym (Square→compPath λ t i → push (p t) i)
      cancel : πa ∙ γ' ∙ sym πb ≡ γ
      cancel =
        πa ∙ γ' ∙ sym πb       ≡⟨ assoc πa γ' (sym πb) ⟩
        (πa ∙ γ') ∙ sym πb     ≡⟨ cong (_∙ sym πb) nat-eq ⟩
        (γ ∙ πb) ∙ sym πb      ≡⟨ sym (assoc γ πb (sym πb)) ⟩
        γ ∙ (πb ∙ sym πb)      ≡⟨ cong (γ ∙_) (rCancel πb) ⟩
        γ ∙ refl               ≡⟨ sym (rUnit γ) ⟩
        γ ∎
      inner : β ∙ γ ∙ sym δ ≡ (β ∙ πa) ∙ γ' ∙ sym (δ ∙ πb)
      inner =
        β ∙ γ ∙ sym δ
          ≡⟨ cong (β ∙_) (cong (_∙ sym δ) (sym cancel)) ⟩
        β ∙ (πa ∙ γ' ∙ sym πb) ∙ sym δ
          ≡⟨ cong (β ∙_) (sym (assoc πa (γ' ∙ sym πb) (sym δ))) ⟩
        β ∙ (πa ∙ ((γ' ∙ sym πb) ∙ sym δ))
          ≡⟨ cong (β ∙_) (cong (πa ∙_) (sym (assoc γ' (sym πb) (sym δ)))) ⟩
        β ∙ (πa ∙ (γ' ∙ (sym πb ∙ sym δ)))
          ≡⟨ assoc β πa (γ' ∙ (sym πb ∙ sym δ)) ⟩
        (β ∙ πa) ∙ (γ' ∙ (sym πb ∙ sym δ))
          ≡⟨ cong ((β ∙ πa) ∙_) (cong (γ' ∙_) (sym (symDistr δ πb))) ⟩
        (β ∙ πa) ∙ γ' ∙ sym (δ ∙ πb) ∎

    decode-incl : {k : ℕ} (y : obj S' (k + n₀)) → Code-incl y → Path (SeqColim S') (incl x₀) (incl y)
    decode-incl {k} y = elim (pathSeq y) (λ _ → Path (SeqColim S') (incl x₀) (incl y))
      (elimdata (λ {j} p → di j p) (λ {j} p → dp j p))

    decode-incl' : {k : ℕ} (y : obj S' (k + n₀)) → Code (incl y) → Path (SeqColim S') (incl x₀) (incl y)
    decode-incl' y c = decode-incl y (transport (codeβ y) c)

    decode : (c : SeqColim S') → Code c → Path (SeqColim S') (incl x₀) c
    decode = elimShifted S' n₀ (λ c → Code c → Path (SeqColim S') (incl x₀) c)
      (elimdata-shift (λ y → decode-incl' y) (λ y → decode-pushP y))
      where
      decode-pushP : {k : ℕ} (y : obj S' (k + n₀))
        → PathP (λ i → Code (push y i) → Path (SeqColim S') (incl x₀) (push y i))
                (decode-incl' y) (decode-incl' (map S' y))
      decode-pushP {k} y = toPathP (funExt lemma) where
        postulate
          lemma : (c : Code (incl (map S' y)))
            → transport (λ i → Code (push y i) → Path (SeqColim S') (incl x₀) (push y i)) (decode-incl' y) c
            ≡ decode-incl' (map S' y) c

    coll : (b : SeqColim S') → incl x₀ ≡ b → incl x₀ ≡ b
    coll b p = decode b (encode b p)

    coll-const : (b : SeqColim S') → (p q : incl x₀ ≡ b) → coll b p ≡ coll b q
    coll-const b p q = cong (decode b) (isPropCodeFull b (encode b p) (encode b q))

    isPropPathsFrom : (b : SeqColim S') → isProp (incl x₀ ≡ b)
    isPropPathsFrom b p q = p≡q where
      f : (x : SeqColim S') → incl x₀ ≡ x → incl x₀ ≡ x
      f = coll
      fConst : (x : SeqColim S') → (r s : incl x₀ ≡ x) → f x r ≡ f x s
      fConst = coll-const
      rem : (r : incl x₀ ≡ b)
        → PathP (λ i → incl x₀ ≡ r i) (f (incl x₀) refl) (f b r)
      rem r j = f (r j) (λ i → r (i ∧ j))
      p≡q : p ≡ q
      p≡q j i = hcomp (λ k → λ { (i = i0) → f (incl x₀) refl k
                               ; (i = i1) → fConst b p q j k
                               ; (j = i0) → rem p i k
                               ; (j = i1) → rem q i k }) (incl x₀)

 isSetSeqColimOfSets : isSet (SeqColim S')
 isSetSeqColimOfSets =
   SeqColim→Prop (λ a → isPropΠ (λ b → isPropIsProp))
     λ n x₀ → let open EncDec x₀ in isPropPathsFrom
