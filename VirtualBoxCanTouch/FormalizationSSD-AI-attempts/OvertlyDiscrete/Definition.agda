{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module OvertlyDiscrete.Definition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false; _and_; isSetBool)
open import Cubical.Data.Bool.Properties using (false≢true)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using ()

open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import BasicDefinitions

open Iso

-- ════════════════════════════════════════════════════════════════
-- Open propositions
-- ════════════════════════════════════════════════════════════════

-- A proposition P is open if it is logically equivalent to
-- ∥ Σ[ n ∈ ℕ ] α n ≡ true ∥₁ for some binary sequence α.
-- Since both sides should be propositions, logical equivalence
-- suffices (we don't need a full equivalence).
isOpenProp : Type ℓ-zero → Type ℓ-zero
isOpenProp P = Σ[ α ∈ binarySequence ]
  (P → ∥ Σℕ α ∥₁) × (∥ Σℕ α ∥₁ → P)

-- ════════════════════════════════════════════════════════════════
-- Basic closure properties of open propositions
-- ════════════════════════════════════════════════════════════════

private
  and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
  and-true-left true  _ _ = refl
  and-true-left false _ p = ⊥.rec (false≢true p)

  and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
  and-true-right true  b p = p
  and-true-right false _ p = ⊥.rec (false≢true p)

-- Conjunction of open propositions is open,
-- provided the conjunction is itself a proposition
-- (e.g., both P and Q are propositions).
openProp-conj : {P Q : Type ℓ-zero}
  → isProp P → isProp Q
  → isOpenProp P → isOpenProp Q → isOpenProp (P × Q)
openProp-conj {P} {Q} isPropP isPropQ (α , fwdP , bwdP) (β , fwdQ , bwdQ) =
  γ , fwd , bwd
  where
  γ : binarySequence
  γ n = α (fst (inv ℕ×ℕ≅ℕ n)) and β (snd (inv ℕ×ℕ≅ℕ n))

  fwd : P × Q → ∥ Σℕ γ ∥₁
  fwd (p , q) = PT.map2 combine (fwdP p) (fwdQ q)
    where
    combine : Σℕ α → Σℕ β → Σℕ γ
    combine (m , αm) (n , βn) = fun ℕ×ℕ≅ℕ (m , n) , proof
      where
      k = fun ℕ×ℕ≅ℕ (m , n)
      eq : inv ℕ×ℕ≅ℕ k ≡ (m , n)
      eq = ret ℕ×ℕ≅ℕ (m , n)
      proof : γ k ≡ true
      proof =
        α (fst (inv ℕ×ℕ≅ℕ k)) and β (snd (inv ℕ×ℕ≅ℕ k))
          ≡⟨ cong₂ (λ x y → α x and β y) (cong fst eq) (cong snd eq) ⟩
        α m and β n
          ≡⟨ cong (_and β n) αm ⟩
        true and β n
          ≡⟨ βn ⟩
        true ∎

  bwd : ∥ Σℕ γ ∥₁ → P × Q
  bwd = PT.rec (isProp× isPropP isPropQ) extract
    where
    extract : Σℕ γ → P × Q
    extract (k , r) = bwdP ∣ m , αm ∣₁ , bwdQ ∣ n , βn ∣₁
      where
      m = fst (inv ℕ×ℕ≅ℕ k)
      n = snd (inv ℕ×ℕ≅ℕ k)
      αm : α m ≡ true
      αm = and-true-left (α m) (β n) r
      βn : β n ≡ true
      βn = and-true-right (α m) (β n) r

-- ════════════════════════════════════════════════════════════════
-- Overtly discrete types
-- ════════════════════════════════════════════════════════════════

-- A type X is overtly discrete if it is a set that is a quotient
-- of ℕ by an open equivalence relation. Equivalently: there is a
-- surjection from ℕ onto X and every equality in X is open.
record has-ODisc-structure (X : Type ℓ-zero) : Type ℓ-zero where
  field
    surj    : ℕ → X
    isSurj  : isSurjection surj
    setX    : isSet X
    openEq  : (x y : X) → isOpenProp (x ≡ y)

isOvertlyDiscrete : Type ℓ-zero → Type ℓ-zero
isOvertlyDiscrete X = ∥ has-ODisc-structure X ∥₁

-- ════════════════════════════════════════════════════════════════
-- Product of overtly discrete types is overtly discrete
-- ════════════════════════════════════════════════════════════════

module ODiscProduct
  {X Y : Type ℓ-zero}
  (odX : has-ODisc-structure X)
  (odY : has-ODisc-structure Y)
  where

  open has-ODisc-structure

  private
    eX = surj odX
    eY = surj odY

    setXY : isSet (X × Y)
    setXY = isSet× (setX odX) (setX odY)

    -- Surjection ℕ → X × Y via the pairing ℕ ≅ ℕ × ℕ
    e : ℕ → X × Y
    e n = eX (fst (inv ℕ×ℕ≅ℕ n)) , eY (snd (inv ℕ×ℕ≅ℕ n))

    e-surj : isSurjection e
    e-surj (x , y) = PT.map2 combine (isSurj odX x) (isSurj odY y)
      where
      combine : fiber eX x → fiber eY y → fiber e (x , y)
      combine (m , p) (n , q) = fun ℕ×ℕ≅ℕ (m , n) , ΣPathP (p' , q')
        where
        k = fun ℕ×ℕ≅ℕ (m , n)
        eq : inv ℕ×ℕ≅ℕ k ≡ (m , n)
        eq = ret ℕ×ℕ≅ℕ (m , n)
        p' : eX (fst (inv ℕ×ℕ≅ℕ k)) ≡ x
        p' = cong (eX ∘ fst) eq ∙ p
        q' : eY (snd (inv ℕ×ℕ≅ℕ k)) ≡ y
        q' = cong (eY ∘ snd) eq ∙ q

    -- Open equality for the product: (x₁,y₁) ≡ (x₂,y₂) ↔ (x₁≡x₂) × (y₁≡y₂)
    openEqProd : (p q : X × Y) → isOpenProp (p ≡ q)
    openEqProd (x₁ , y₁) (x₂ , y₂) = α , fwd , bwd
      where
      open-x = openEq odX x₁ x₂
      open-y = openEq odY y₁ y₂
      isProp-x = setX odX x₁ x₂
      isProp-y = setX odY y₁ y₂  -- Wait, this should be setY

      open-conj = openProp-conj isProp-x (setY y₁ y₂) open-x open-y
        where setY = setX odY  -- actually odY.setX gives isSet Y

      α = fst open-conj

      fwd : (x₁ , y₁) ≡ (x₂ , y₂) → ∥ Σℕ α ∥₁
      fwd p = fst (snd open-conj) (cong fst p , cong snd p)

      bwd : ∥ Σℕ α ∥₁ → (x₁ , y₁) ≡ (x₂ , y₂)
      bwd t = let (px , py) = snd (snd open-conj) t
              in ΣPathP (px , py)

  ODisc-× : has-ODisc-structure (X × Y)
  surj    ODisc-× = e
  isSurj  ODisc-× = e-surj
  setX    ODisc-× = setXY
  openEq  ODisc-× = openEqProd

isODisc-× : {X Y : Type ℓ-zero}
  → isOvertlyDiscrete X → isOvertlyDiscrete Y → isOvertlyDiscrete (X × Y)
isODisc-× = PT.map2 (λ ox oy → ODiscProduct.ODisc-× ox oy)
