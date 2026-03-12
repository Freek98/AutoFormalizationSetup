{-# OPTIONS --cubical --guardedness #-}
-- AI generated, minor edits. 
module Countable.Properties where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport using (pathToIso)
open import Cubical.Foundations.Function

open import Cubical.Data.Nat
open import Cubical.Data.Bool hiding (_≟_)
open import Cubical.Data.Bool.Properties using (isSetBool ; false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty as ⊥ 

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)

open import Cubical.HITs.PropositionalTruncation as PT

open import BasicDefinitions

open Iso

private 
  boolGuard : (b : Bool) → (b ≡ true → Bool) → Bool
  boolGuard true  f = f refl
  boolGuard false _ = false
  
  -- If b ≡ true and f applied to that proof gives true, then boolGuard b f ≡ true
  boolGuard-intro : (b : Bool) (f : b ≡ true → Bool) (q : b ≡ true)
    → f q ≡ true → boolGuard b f ≡ true
  boolGuard-intro true f q fq =
    subst (λ r → f r ≡ true) (isSetBool _ _ q refl) fq
  boolGuard-intro false f q _ = ⊥.rec (false≢true q)
  
  -- If boolGuard b f ≡ true, then b ≡ true and f refl ≡ true
  boolGuard-elim : (b : Bool) (f : b ≡ true → Bool)
    → boolGuard b f ≡ true → Σ[ q ∈ b ≡ true ] f q ≡ true
  boolGuard-elim true  f p = refl , p
  boolGuard-elim false _ p = ⊥.rec (false≢true p)

-- ════════════════════════════════════════════════════════════════
-- Helpers for _and_
-- ════════════════════════════════════════════════════════════════

  and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
  and-true-left true  _ _ = refl
  and-true-left false _ p = ⊥.rec (false≢true p)
  
  and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
  and-true-right true  b p = p
  and-true-right false _ p = ⊥.rec (false≢true p)

-- ════════════════════════════════════════════════════════════════
-- Product of countable types
-- ════════════════════════════════════════════════════════════════

module CountableProduct (α β : binarySequence) where

  -- The characteristic function for the product
  γ× : binarySequence
  γ× n = α (fst (inv ℕ×ℕ≅ℕ n)) and β (snd (inv ℕ×ℕ≅ℕ n))

  -- Iso (Σℕ α × Σℕ β) (Σℕ γ×)
  ΣℕProd : Iso (Σℕ α × Σℕ β) (Σℕ γ×)
  fun ΣℕProd ((n , p) , (m , q)) = fun ℕ×ℕ≅ℕ (n , m) , proof
    where
      k = fun ℕ×ℕ≅ℕ (n , m)
      eq : inv ℕ×ℕ≅ℕ k ≡ (n , m)
      eq = ret ℕ×ℕ≅ℕ (n , m)

      proof : γ× k ≡ true
      proof =
        α (fst (inv ℕ×ℕ≅ℕ k)) and β (snd (inv ℕ×ℕ≅ℕ k))
          ≡⟨ cong₂ (λ x y → α x and β y) (cong fst eq) (cong snd eq) ⟩
        α n and β m
          ≡⟨ cong (_and β m) p ⟩
        true and β m
          ≡⟨ refl ⟩
        β m
          ≡⟨ q ⟩
        true ∎

  inv ΣℕProd (k , r) = (n , αn≡true) , (m , βm≡true)
    where
      n = fst (inv ℕ×ℕ≅ℕ k)
      m = snd (inv ℕ×ℕ≅ℕ k)
      -- r : α n and β m ≡ true
      αn≡true : α n ≡ true
      αn≡true = and-true-left (α n) (β m) r

      βm≡true : β m ≡ true
      βm≡true = and-true-right (α n) (β m) r

  sec ΣℕProd (k , r) = ΣPathP (lem , toPathP (isSetBool _ _ _ _))
    where
      n = fst (inv ℕ×ℕ≅ℕ k)
      m = snd (inv ℕ×ℕ≅ℕ k)
      lem : fun ℕ×ℕ≅ℕ (n , m) ≡ k
      lem = sec ℕ×ℕ≅ℕ k

  ret ΣℕProd ((n , p) , (m , q)) =
    ΣPathP (ΣPathP (cong fst eq , toPathP (isSetBool _ _ _ _)) ,
            ΣPathP (cong snd eq , toPathP (isSetBool _ _ _ _)))
    where
      eq : inv ℕ×ℕ≅ℕ (fun ℕ×ℕ≅ℕ (n , m)) ≡ (n , m)
      eq = ret ℕ×ℕ≅ℕ (n , m)

-- ════════════════════════════════════════════════════════════════
-- Sum of countable types
-- ════════════════════════════════════════════════════════════════

module CountableSum (α β : binarySequence) where
  γ⊎ : binarySequence
  γ⊎ n = ⊎.rec α β (inv ℕ⊎ℕ≅ℕ n)

  -- Step 1: Σℕ α ⊎ Σℕ β ≅ Σ (ℕ ⊎ ℕ) (λ s → ⊎.rec α β s ≡ true)
  flattenSum : Iso (Σℕ α ⊎ Σℕ β) (Σ (ℕ ⊎ ℕ) (λ s → ⊎.rec α β s ≡ true))
  fun flattenSum (inl (n , p)) = inl n , p
  fun flattenSum (inr (m , q)) = inr m , q
  inv flattenSum (inl n , p) = inl (n , p)
  inv flattenSum (inr m , q) = inr (m , q)
  sec flattenSum (inl n , p) = refl
  sec flattenSum (inr m , q) = refl
  ret flattenSum (inl (n , p)) = refl
  ret flattenSum (inr (m , q)) = refl

  ΣℕSum : Iso (Σℕ α ⊎ Σℕ β) (Σℕ γ⊎)
  ΣℕSum = compIso flattenSum (invIso (Σ-cong-iso-fst (invIso ℕ⊎ℕ≅ℕ)))

module ΣBoolCountable (α : binarySequence) where

  -- Given a predicate P on Σℕ α, define the characteristic function
  -- for the subtype Σ[ x ∈ Σℕ α ] P x ≡ true
  γΣ : (P : Σℕ α → Bool) → binarySequence
  γΣ P n = boolGuard (α n) (λ q → P (n , q))

  ΣℕBoolSub : (P : Σℕ α → Bool) → Iso (Σ[ x ∈ Σℕ α ] P x ≡ true) (Σℕ (γΣ P))
  fun (ΣℕBoolSub P) ((n , q) , r) = n , boolGuard-intro (α n) (λ q' → P (n , q')) q r
  fst (inv (ΣℕBoolSub P) (n , r)) = n , fst (boolGuard-elim (α n) (λ q → P (n , q)) r)
  snd (inv (ΣℕBoolSub P) (n , r)) = snd (boolGuard-elim (α n) (λ q → P (n , q)) r)
  sec (ΣℕBoolSub P) (n , r) = ΣPathP (refl , toPathP (isSetBool _ _ _ _))
  ret (ΣℕBoolSub P) ((n , q) , r) =
    ΣPathP (ΣPathP (refl , toPathP (isSetBool _ _ _ _)) ,
            toPathP (isSetBool _ _ _ _))

-- ════════════════════════════════════════════════════════════════
-- Main results: closure properties of is-countable
-- ════════════════════════════════════════════════════════════════

is-countable-× : {A B : Type}
  → is-countable A → is-countable B → is-countable (A × B)
is-countable-× cA cB = PT.map2 (λ (α , iA) (β , iB) →
    let open CountableProduct α β
    in γ× , compIso (prodIso iA iB) ΣℕProd
  ) cA cB

is-countable-⊎ : {A B : Type}
  → is-countable A → is-countable B → is-countable (A ⊎ B)
is-countable-⊎ cA cB = PT.map2 (λ (α , iA) (β , iB) →
    let open CountableSum α β
    in γ⊎ , compIso (⊎Iso iA iB) ΣℕSum
  ) cA cB

is-countable-Σ-Bool : {A : Type} (P : A → Bool)
  → is-countable A → is-countable (Σ[ a ∈ A ] P a ≡ true)
is-countable-Σ-Bool {A} P = PT.map (λ (α , iA) →
    let open ΣBoolCountable α
        P' : Σℕ α → Bool
        P' x = P (inv iA x)
    in γΣ P' , compIso (Σ-cong-iso iA (λ a →
           pathToIso (cong (λ z → P z ≡ true) (sym (ret iA a)))))
         (ΣℕBoolSub P')
  )
