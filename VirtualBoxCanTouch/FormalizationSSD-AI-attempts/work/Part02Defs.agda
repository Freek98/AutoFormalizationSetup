{-# OPTIONS --cubical --guardedness #-}

module work.Part02Defs where

open import work.Part01 public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Sum.Properties using (isProp⊎)

open import Cubical.Relation.Nullary

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import StoneSpaces.Spectrum using (Sp; Booleω)
open import Axioms.StoneDuality using (StoneDualityAxiom)

import OmnisciencePrinciples.Markov as MarkovLib

open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanRingEquiv; invBooleanRingEquiv; idBoolHom)
open import CountablyPresentedBooleanRings.Examples.Bool using (is-cp-2)
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
import QuotientBool as QB
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
import Cubical.Data.Sum as ⊎

-- Axiom-independent definitions

module SpectrumEmptyImpliesTrivial (SD : StoneDualityAxiom) (B : Booleω) (spEmpty : Sp B → ⊥) where
  open import StoneSpaces.Spectrum using (evaluationMap)

  emptyFunContr : isContr (Sp B → Bool)
  emptyFunContr = (λ sp → ex-falso (spEmpty sp)) , λ f → funExt (λ sp → ex-falso (spEmpty sp))

  B-contr : isContr ⟨ fst B ⟩
  B-contr = isOfHLevelRespectEquiv 0 (invEquiv (evaluationMap B , SD B)) emptyFunContr

  0≡1-in-B : BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
  0≡1-in-B = isContr→isProp B-contr _ _

open import Cubical.Algebra.CommRing.Properties using (compCommRingEquiv)

compBoolRingEquiv : (A B C : BooleanRing ℓ-zero)
                  → BooleanRingEquiv A B → BooleanRingEquiv B C → BooleanRingEquiv A C
compBoolRingEquiv A B C f g = compCommRingEquiv {A = BooleanRing→CommRing A} {B = BooleanRing→CommRing B} {C = BooleanRing→CommRing C} f g

open import Cubical.Algebra.CommRing.Univalence using (CommRingPath)

commRingPath→boolRingEquiv : (A B : BooleanRing ℓ-zero)
  → BooleanRing→CommRing A ≡ BooleanRing→CommRing B
  → BooleanRingEquiv A B
commRingPath→boolRingEquiv A B p =
  let e = invEq (CommRingPath _ _) p in fst e , snd e

Bool-Booleω : Booleω
Bool-Booleω = BoolBR , ∣ is-cp-2 ∣₁

Sp-Bool-inhabited : ∥ Sp Bool-Booleω ∥₁
Sp-Bool-inhabited = ∣ idBoolHom BoolBR ∣₁

-- Dependent Choice axiom type (tex Axiom 355, axDependentChoice)

SeqLimit : {ℓ : Level} → (E : ℕ → Type ℓ) → ((n : ℕ) → E (suc n) → E n) → Type ℓ
SeqLimit E p = Σ[ f ∈ ((n : ℕ) → E n) ] ((n : ℕ) → p n (f (suc n)) ≡ f n)

seqLim-proj₀ : {ℓ : Level} → (E : ℕ → Type ℓ) (p : (n : ℕ) → E (suc n) → E n)
             → SeqLimit E p → E 0
seqLim-proj₀ E p (f , _) = f 0

DependentChoiceAxiom : {ℓ : Level} → Type (ℓ-suc ℓ)
DependentChoiceAxiom {ℓ} = (E : ℕ → Type ℓ) (p : (n : ℕ) → E (suc n) → E n)
  → ((n : ℕ) → (y : E n) → ∥ Σ[ x ∈ E (suc n) ] p n x ≡ y ∥₁)
  → (e₀ : E 0) → ∥ Σ[ s ∈ SeqLimit E p ] seqLim-proj₀ E p s ≡ e₀ ∥₁

CountableChoiceAxiom : {ℓ : Level} → Type (ℓ-suc ℓ)
CountableChoiceAxiom {ℓ} = (A : ℕ → Type ℓ)
  → ((n : ℕ) → ∥ A n ∥₁)
  → ∥ ((n : ℕ) → A n) ∥₁

-- SurjectionsAreFormalSurjections axiom type (tex line 294-297)

isInjectiveBoolHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isInjectiveBoolHom B C g = (x y : ⟨ fst B ⟩) → fst g x ≡ fst g y → x ≡ y

open import Cubical.Algebra.CommRing.Properties using (_∘cr_)

isSurjectiveSpHom : (B C : Booleω) → BoolHom (fst B) (fst C) → Type ℓ-zero
isSurjectiveSpHom B C g = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] h' ∘cr g ≡ h ∥₁

SurjectionsAreFormalSurjectionsAxiom : Type (ℓ-suc ℓ-zero)
SurjectionsAreFormalSurjectionsAxiom = (B C : Booleω) (g : BoolHom (fst B) (fst C)) →
  isInjectiveBoolHom B C g ↔ isSurjectiveSpHom B C g

-- Local Choice axiom type (tex Axiom 348, AxLocalChoice)

isSurjectiveSpMap : {B C : Booleω} → (Sp C → Sp B) → Type ℓ-zero
isSurjectiveSpMap {B} {C} q = (h : Sp B) → ∥ Σ[ h' ∈ Sp C ] q h' ≡ h ∥₁

-- tex Remark 394 (LocalChoiceSurjectionForm): lifting diagram formulation of local choice
LocalChoiceAxiom : Type (ℓ-suc ℓ-zero)
LocalChoiceAxiom = (B : Booleω) (P : Sp B → Type ℓ-zero)
  → ((s : Sp B) → ∥ P s ∥₁)
  → ∥ Σ[ C ∈ Booleω ] Σ[ q ∈ (Sp C → Sp B) ]
      (isSurjectiveSpMap {B} {C} q × ((t : Sp C) → P (q t))) ∥₁

-- Utility definitions (axiom-independent)

data Reveal_·_is_ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) (y : B x) : Type₀ where
  [_] : f x ≡ y → Reveal f · x is y

inspect : ∀ {A : Type₀} {B : A → Type₀} (f : (x : A) → B x) (x : A) → Reveal f · x is (f x)
inspect f x = [ refl ]

open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

cantorPair : ℕ → ℕ → ℕ
cantorPair m n = Iso.fun ℕ×ℕ≅ℕ (m , n)

cantorUnpair : ℕ → ℕ × ℕ
cantorUnpair = Iso.inv ℕ×ℕ≅ℕ

cantorUnpair-pair : (m n : ℕ) → cantorUnpair (cantorPair m n) ≡ (m , n)
cantorUnpair-pair m n = Iso.ret ℕ×ℕ≅ℕ (m , n)

openAnd : (P Q : hProp ℓ-zero) → isOpenProp P → isOpenProp Q
        → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
openAnd P Q Popen Qopen = PT.rec2 squash₁ go Popen Qopen
  where
  go : isOpenWitness P → isOpenWitness Q
     → isOpenProp ((⟨ P ⟩ × ⟨ Q ⟩) , isProp× (snd P) (snd Q))
  go (α , P→∃α , ∃α→P) (β , Q→∃β , ∃β→Q) = ∣ γ , forward , backward ∣₁
    where
    γ : binarySequence
    γ k = let (n , m) = cantorUnpair k in α n and β m

    forward : ⟨ P ⟩ × ⟨ Q ⟩ → Σ[ k ∈ ℕ ] γ k ≡ true
    forward (p , q) =
      let (n , αn=t) = P→∃α p
          (m , βm=t) = Q→∃β q
          k = cantorPair n m
          γk=t : γ k ≡ true
          γk=t =
            γ k
              ≡⟨ cong (λ p → α (fst p) and β (snd p)) (cantorUnpair-pair n m) ⟩
            α n and β m
              ≡⟨ cong (λ x → x and β m) αn=t ⟩
            true and β m
              ≡⟨ cong (true and_) βm=t ⟩
            true ∎
      in (k , γk=t)

    backward : Σ[ k ∈ ℕ ] γ k ≡ true → ⟨ P ⟩ × ⟨ Q ⟩
    backward (k , γk=t) =
      let (n , m) = cantorUnpair k
          αn=t : α n ≡ true
          αn=t = and-true-left (α n) (β m) γk=t
          βm=t : β m ≡ true
          βm=t = and-true-right (α n) (β m) γk=t
      in (∃α→P (n , αn=t)) , (∃β→Q (m , βm=t))
      where
      and-true-left : (a b : Bool) → a and b ≡ true → a ≡ true
      and-true-left true  _ _ = refl
      and-true-left false _ p = ex-falso (false≢true p)

      and-true-right : (a b : Bool) → a and b ≡ true → b ≡ true
      and-true-right true  _ p = p
      and-true-right false _ p = ex-falso (false≢true p)

firstTrue : binarySequence → binarySequence
firstTrue α zero = α zero
firstTrue α (suc n) with α zero
... | true = false
... | false = firstTrue (α ∘ suc) n

firstTrue-preserves-allFalse : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
                             → (n : ℕ) → firstTrue α n ≡ false
firstTrue-preserves-allFalse α allF zero = allF zero
firstTrue-preserves-allFalse α allF (suc n) with α zero | allF zero
... | true  | α0=f = ex-falso (false≢true (sym α0=f))
... | false | _    = firstTrue-preserves-allFalse (α ∘ suc) (allF ∘ suc) n

firstTrue-hitsAtMostOnce : (α : binarySequence) → hitsAtMostOnce (firstTrue α)
firstTrue-hitsAtMostOnce α m n ftm=t ftn=t = aux α m n ftm=t ftn=t
  where
  aux : (α : binarySequence) → (m n : ℕ) → firstTrue α m ≡ true → firstTrue α n ≡ true → m ≡ n
  aux α zero zero _ _ = refl
  aux α zero (suc n) ft0=t ft-sn=t with α zero
  aux α zero (suc n) ft0=t ft-sn=t | true = ex-falso (false≢true ft-sn=t)
  aux α zero (suc n) ft0=t ft-sn=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) zero ft-sm=t ft0=t with α zero
  aux α (suc m) zero ft-sm=t ft0=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) zero ft-sm=t ft0=t | false = ex-falso (false≢true ft0=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t with α zero
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | true = ex-falso (false≢true ft-sm=t)
  aux α (suc m) (suc n) ft-sm=t ft-sn=t | false = cong suc (aux (α ∘ suc) m n ft-sm=t ft-sn=t)

firstTrue-true-implies-original-true : (α : binarySequence) (n : ℕ)
                                      → firstTrue α n ≡ true → α n ≡ true
firstTrue-true-implies-original-true α zero ft0=t = ft0=t
firstTrue-true-implies-original-true α (suc n) ft-sn=t with α zero
... | true  = ex-falso (false≢true ft-sn=t)
... | false = firstTrue-true-implies-original-true (α ∘ suc) n ft-sn=t

firstTrue-false-but-original-true : (α : binarySequence) (n : ℕ)
                                   → firstTrue α n ≡ false → α n ≡ true
                                   → Σ[ m ∈ ℕ ] (suc m ≤ n) × (α m ≡ true)
firstTrue-false-but-original-true α zero ft0=f α0=t = ex-falso (true≢false (sym α0=t ∙ ft0=f))
firstTrue-false-but-original-true α (suc n) ft-sn=f α-sn=t with α zero | inspect α zero
... | true  | [ α0=t ] = zero , suc-≤-suc zero-≤ , α0=t
... | false | _ =
  let (m , m<n , αsm=t) = firstTrue-false-but-original-true (α ∘ suc) n ft-sn=f α-sn=t
  in suc m , suc-≤-suc m<n , αsm=t

record FoundationalAxioms : Type (ℓ-suc (ℓ-suc ℓ-zero)) where
  field
    dependentChoice-axiom : DependentChoiceAxiom {ℓ-zero}
    dependentChoice-axiom₁ : DependentChoiceAxiom {ℓ-suc ℓ-zero}
    sd-axiom : StoneDualityAxiom
    surj-formal-axiom : SurjectionsAreFormalSurjectionsAxiom
    localChoice-axiom : LocalChoiceAxiom
