{-# OPTIONS --cubical --guardedness #-}

module work.Part06 where

open import work.Part05 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.Equiv using (_≃_; equivFun; invEq)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; isSetBool; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no; Discrete→isSet)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; elim; squash₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Data.List using (List; []; _∷_; _++_)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ2; isSetΠ)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; idBoolEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Data.Empty renaming (rec to ex-falso)

module B∞-BoolAlg = BooleanAlgebraStr B∞

neg-distrib-join : (a b : ⟨ B∞ ⟩) → ¬∞ (a ∨∞ b) ≡ (¬∞ a) ∧∞ (¬∞ b)
neg-distrib-join a b = B∞-BoolAlg.DeMorgan¬∨ {x = a} {y = b}

neg-finJoin : (ns : List ℕ) → ¬∞ (finJoin∞ ns) ≡ finMeetNeg∞ ns
neg-finJoin [] = BooleanRingStr.+IdR (snd B∞) 𝟙∞  -- ¬0 = 1 + 0 = 1
neg-finJoin (n ∷ ns) =
  ¬∞ (finJoin∞ (n ∷ ns))
    ≡⟨ refl ⟩
  ¬∞ (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ neg-distrib-join (g∞ n) (finJoin∞ ns) ⟩
  (¬∞ (g∞ n)) ∧∞ (¬∞ (finJoin∞ ns))
    ≡⟨ cong ((¬∞ (g∞ n)) ∧∞_) (neg-finJoin ns) ⟩
  (¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns
    ≡⟨ refl ⟩
  finMeetNeg∞ (n ∷ ns) ∎

neg-distrib-meet : (a b : ⟨ B∞ ⟩) → ¬∞ ((¬∞ a) ∧∞ (¬∞ b)) ≡ a ∨∞ b
neg-distrib-meet a b =
  ¬∞ ((¬∞ a) ∧∞ (¬∞ b))
    ≡⟨ B∞-BoolAlg.DeMorgan¬∧ {x = ¬∞ a} {y = ¬∞ b} ⟩
  (¬∞ (¬∞ a)) ∨∞ (¬∞ (¬∞ b))
    ≡⟨ cong₂ _∨∞_ (B∞-BoolAlg.¬Invol {x = a}) (B∞-BoolAlg.¬Invol {x = b}) ⟩
  a ∨∞ b ∎

neg-finMeetNeg : (ns : List ℕ) → ¬∞ (finMeetNeg∞ ns) ≡ finJoin∞ ns
neg-finMeetNeg [] = char2-B∞ 𝟙∞  -- ¬1 = 1 + 1 = 0
neg-finMeetNeg (n ∷ ns) =
  ¬∞ (finMeetNeg∞ (n ∷ ns))
    ≡⟨ refl ⟩
  ¬∞ ((¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns)
    ≡⟨ cong (λ z → ¬∞ ((¬∞ (g∞ n)) ∧∞ z)) (sym (neg-finJoin ns)) ⟩
  ¬∞ ((¬∞ (g∞ n)) ∧∞ (¬∞ (finJoin∞ ns)))
    ≡⟨ neg-distrib-meet (g∞ n) (finJoin∞ ns) ⟩
  (g∞ n) ∨∞ finJoin∞ ns
    ≡⟨ refl ⟩
  finJoin∞ (n ∷ ns) ∎

neg-nf-correct : (nf : B∞-NormalForm) → ⟦ neg-nf nf ⟧nf ≡ ¬∞ (⟦ nf ⟧nf)
neg-nf-correct (joinForm ns) = sym (neg-finJoin ns)
neg-nf-correct (meetNegForm ns) = sym (neg-finMeetNeg ns)

open import BooleanRing.FreeBooleanRing.freeBATerms using (equalityFromEqualityOnGenerators)

SpB∞-to-ℕ∞-injective : (h₁ h₂ : Sp B∞-Booleω) →
  SpB∞-to-ℕ∞ h₁ ≡ SpB∞-to-ℕ∞ h₂ → h₁ ≡ h₂
SpB∞-to-ℕ∞-injective h₁ h₂ seq-eq = B∞-hom-eq
  where
  seq-eq-pointwise : (n : ℕ) → h₁ $cr (g∞ n) ≡ h₂ $cr (g∞ n)
  seq-eq-pointwise n = funExt⁻ (cong fst seq-eq) n

  h₁-free h₂-free : BoolHom (freeBA ℕ) BoolBR
  h₁-free = h₁ ∘cr π∞
  h₂-free = h₂ ∘cr π∞

  agree-on-gens : (n : ℕ) → h₁-free $cr (generator n) ≡ h₂-free $cr (generator n)
  agree-on-gens n = seq-eq-pointwise n

  free-hom-eq : h₁-free ≡ h₂-free
  free-hom-eq = equalityFromEqualityOnGenerators BoolBR h₁-free h₂-free agree-on-gens

  fst-hom-eq : fst h₁ ≡ fst h₂
  fst-hom-eq = QB.quotientImageHomEpi {B = freeBA ℕ} {f = relB∞}
    (⟨ BoolBR ⟩ , BooleanRingStr.is-set (snd BoolBR))
    (cong fst free-hom-eq)

  B∞-hom-eq : h₁ ≡ h₂
  B∞-hom-eq = CommRingHom≡ fst-hom-eq

SpB∞-retraction : (h : Sp B∞-Booleω) → ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h) ≡ h
SpB∞-retraction h = SpB∞-to-ℕ∞-injective (ℕ∞-to-SpB∞ (SpB∞-to-ℕ∞ h)) h
  (SpB∞-roundtrip (SpB∞-to-ℕ∞ h))

SpB∞≅ℕ∞ : Iso (Sp B∞-Booleω) ℕ∞
SpB∞≅ℕ∞ = iso SpB∞-to-ℕ∞ ℕ∞-to-SpB∞ SpB∞-roundtrip SpB∞-retraction

SpB∞≃ℕ∞ : Sp B∞-Booleω ≃ ℕ∞
SpB∞≃ℕ∞ = isoToEquiv SpB∞≅ℕ∞

module ℕ∞IsStoneModule where
  open import Axioms.StoneDuality using (hasStoneStr)

  ℕ∞-has-StoneStr : hasStoneStr ℕ∞
  ℕ∞-has-StoneStr = B∞-Booleω , ua SpB∞≃ℕ∞

open ℕ∞IsStoneModule public

module ℕ∞⊎ℕ∞IsStoneModule where
  open import Axioms.StoneDuality using (hasStoneStr)
  open import Cubical.Data.Sum as ⊎

  SpB∞×B∞→ℕ∞⊎ℕ∞ : Sp B∞×B∞-Booleω → ℕ∞ ⊎.⊎ ℕ∞
  SpB∞×B∞→ℕ∞⊎ℕ∞ h = ⊎.map SpB∞-to-ℕ∞ SpB∞-to-ℕ∞ (Sp-prod-to-sum h)

  ℕ∞⊎ℕ∞→SpB∞×B∞ : ℕ∞ ⊎.⊎ ℕ∞ → Sp B∞×B∞-Booleω
  ℕ∞⊎ℕ∞→SpB∞×B∞ = Sp-sum-to-prod ∘ (⊎.map ℕ∞-to-SpB∞ ℕ∞-to-SpB∞)

open ℕ∞⊎ℕ∞IsStoneModule public

module BoolIsStoneModule where
  open import Axioms.StoneDuality using (hasStoneStr; Stone)
  open import Cubical.Data.Sum as ⊎

  -- Bool is Stone (tex line 1527)
  Bool-has-StoneStr : hasStoneStr Bool
  Bool-has-StoneStr = Bool²-Booleω , ua Sp-Bool²≃Bool

  -- tex Theorem 2214: If S:Stone and T:S→Stone, then Σ_{x:S} T(x) is Stone.
  private
    LocalSigmaStoneType : (S : Stone) → (T : fst S → Stone) → Type₀
    LocalSigmaStoneType S T = Σ[ x ∈ fst S ] fst (T x)

    postulate
      LocalStoneSigmaClosed : (S : Stone) (T : fst S → Stone)
        → hasStoneStr (LocalSigmaStoneType S T)

  Bool-Stone : Stone
  Bool-Stone = Bool , Bool-has-StoneStr

  ℕ∞-Stone : Stone
  ℕ∞-Stone = ℕ∞ , ℕ∞-has-StoneStr

  ℕ∞-const-family : Bool → Stone
  ℕ∞-const-family _ = ℕ∞-Stone

  ΣBool-ℕ∞-has-StoneStr : hasStoneStr (Σ Bool (λ _ → ℕ∞))
  ΣBool-ℕ∞-has-StoneStr = LocalStoneSigmaClosed Bool-Stone ℕ∞-const-family

  ⊎-as-Σ : (A : Type₀) → A ⊎.⊎ A ≃ Σ Bool (λ _ → A)
  ⊎-as-Σ A = isoToEquiv (iso to from to-from from-to)
    where
    to : A ⊎.⊎ A → Σ Bool (λ _ → A)
    to (⊎.inl a) = true , a
    to (⊎.inr a) = false , a
    from : Σ Bool (λ _ → A) → A ⊎.⊎ A
    from (true , a) = ⊎.inl a
    from (false , a) = ⊎.inr a
    to-from : (x : Σ Bool (λ _ → A)) → to (from x) ≡ x
    to-from (true , a) = refl
    to-from (false , a) = refl
    from-to : (x : A ⊎.⊎ A) → from (to x) ≡ x
    from-to (⊎.inl a) = refl
    from-to (⊎.inr a) = refl

  ℕ∞⊎ℕ∞≃ΣBool-ℕ∞ : ℕ∞ ⊎.⊎ ℕ∞ ≃ Σ Bool (λ _ → ℕ∞)
  ℕ∞⊎ℕ∞≃ΣBool-ℕ∞ = ⊎-as-Σ ℕ∞

  ℕ∞⊎ℕ∞-has-StoneStr-alt : hasStoneStr (ℕ∞ ⊎.⊎ ℕ∞)
  ℕ∞⊎ℕ∞-has-StoneStr-alt = subst hasStoneStr (sym (ua ℕ∞⊎ℕ∞≃ΣBool-ℕ∞)) ΣBool-ℕ∞-has-StoneStr

open BoolIsStoneModule public

_∈?_ : ℕ → List ℕ → Bool
n ∈? [] = false
n ∈? (m ∷ ms) with discreteℕ n m
... | yes _ = true
... | no _ = n ∈? ms

_∩L_ : List ℕ → List ℕ → List ℕ
[] ∩L ms = []
(n ∷ ns) ∩L ms with n ∈? ms
... | true = n ∷ (ns ∩L ms)
... | false = ns ∩L ms

meet-joinForm-joinForm : List ℕ → List ℕ → B∞-NormalForm
meet-joinForm-joinForm ns ms = joinForm (ns ∩L ms)

g∞-meet-finJoin-in : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ true →
  g∞ n ∧∞ finJoin∞ ms ≡ g∞ n
g∞-meet-finJoin-in n [] p = ex-falso (true≢false (sym p))  -- n ∈? [] ≡ false ≠ true
g∞-meet-finJoin-in n (m ∷ ms) p with discreteℕ n m
... | yes n=m =
  g∞ n ∧∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∧DistR∨ ⟩
  (g∞ n ∧∞ g∞ m) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (cong (g∞ n ∧∞_) (cong g∞ (sym n=m))) refl ⟩
  (g∞ n ∧∞ g∞ n) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong (_∨∞ (g∞ n ∧∞ finJoin∞ ms)) B∞-BoolAlg.∧Idem ⟩
  g∞ n ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∨AbsorbL∧ ⟩
  g∞ n ∎
... | no n≠m =
  g∞ n ∧∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∧DistR∨ ⟩
  (g∞ n ∧∞ g∞ m) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (gen-orthogonal n m n≠m) (g∞-meet-finJoin-in n ms p) ⟩
  𝟘∞ ∨∞ g∞ n
    ≡⟨ B∞-BoolAlg.∨IdL ⟩
  g∞ n ∎

g∞-meet-finJoin-notin : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ false →
  g∞ n ∧∞ finJoin∞ ms ≡ 𝟘∞
g∞-meet-finJoin-notin n [] _ =
  g∞ n ∧∞ 𝟘∞         ≡⟨ B∞-BoolAlg.∧AnnihilR ⟩
  𝟘∞ ∎
g∞-meet-finJoin-notin n (m ∷ ms) p with discreteℕ n m
... | yes n=m =
  ex-falso (true≢false p)
... | no n≠m =
  g∞ n ∧∞ (g∞ m ∨∞ finJoin∞ ms)
    ≡⟨ B∞-BoolAlg.∧DistR∨ ⟩
  (g∞ n ∧∞ g∞ m) ∨∞ (g∞ n ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (gen-orthogonal n m n≠m) (g∞-meet-finJoin-notin n ms p) ⟩
  𝟘∞ ∨∞ 𝟘∞
    ≡⟨ B∞-BoolAlg.∨IdR ⟩
  𝟘∞ ∎

meet-joinForm-joinForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns ∧∞ finJoin∞ ms ≡ finJoin∞ (ns ∩L ms)
meet-joinForm-joinForm-correct [] ms =
  𝟘∞ ∧∞ finJoin∞ ms     ≡⟨ B∞-BoolAlg.∧AnnihilL ⟩
  𝟘∞ ∎
meet-joinForm-joinForm-correct (n ∷ ns) ms with n ∈? ms | inspect (n ∈?_) ms
... | true | [ n∈ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finJoin∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  (g∞ n ∧∞ finJoin∞ ms) ∨∞ (finJoin∞ ns ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finJoin-in n ms n∈ms) (meet-joinForm-joinForm-correct ns ms) ⟩
  g∞ n ∨∞ finJoin∞ (ns ∩L ms) ∎
... | false | [ n∉ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finJoin∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  (g∞ n ∧∞ finJoin∞ ms) ∨∞ (finJoin∞ ns ∧∞ finJoin∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finJoin-notin n ms n∉ms) (meet-joinForm-joinForm-correct ns ms) ⟩
  𝟘∞ ∨∞ finJoin∞ (ns ∩L ms)
    ≡⟨ B∞-BoolAlg.∨IdL ⟩
  finJoin∞ (ns ∩L ms) ∎

join-joinForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns ∨∞ finJoin∞ ms ≡ finJoin∞ (ns ++ ms)
join-joinForm-correct [] ms =
  𝟘∞ ∨∞ finJoin∞ ms   ≡⟨ B∞-BoolAlg.∨IdL ⟩
  finJoin∞ ms ∎
join-joinForm-correct (n ∷ ns) ms =
  (g∞ n ∨∞ finJoin∞ ns) ∨∞ finJoin∞ ms
    ≡⟨ sym B∞-BoolAlg.∨Assoc ⟩
  g∞ n ∨∞ (finJoin∞ ns ∨∞ finJoin∞ ms)
    ≡⟨ cong (g∞ n ∨∞_) (join-joinForm-correct ns ms) ⟩
  g∞ n ∨∞ finJoin∞ (ns ++ ms) ∎

meet-meetNegForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns ∧∞ finMeetNeg∞ ms ≡ finMeetNeg∞ (ns ++ ms)
meet-meetNegForm-correct [] ms =
  𝟙∞ ∧∞ finMeetNeg∞ ms   ≡⟨ B∞-BoolAlg.∧IdL ⟩
  finMeetNeg∞ ms ∎
meet-meetNegForm-correct (n ∷ ns) ms =
  ((¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns) ∧∞ finMeetNeg∞ ms
    ≡⟨ sym B∞-BoolAlg.∧Assoc ⟩
  (¬∞ (g∞ n)) ∧∞ (finMeetNeg∞ ns ∧∞ finMeetNeg∞ ms)
    ≡⟨ cong ((¬∞ (g∞ n)) ∧∞_) (meet-meetNegForm-correct ns ms) ⟩
  (¬∞ (g∞ n)) ∧∞ finMeetNeg∞ (ns ++ ms) ∎

∧-neg-orthogonal : (a b : ⟨ B∞ ⟩) → a ·∞ b ≡ 𝟘∞ → a ∧∞ (¬∞ b) ≡ a
∧-neg-orthogonal a b ab=0 =
  a ∧∞ (¬∞ b)
    ≡⟨ refl ⟩  -- ∧ is ·, ¬b is 1+b
  a ·∞ (𝟙∞ +∞ b)
    ≡⟨ BooleanRingStr.·DistR+ (snd B∞) a 𝟙∞ b ⟩
  (a ·∞ 𝟙∞) +∞ (a ·∞ b)
    ≡⟨ cong₂ _+∞_ (BooleanRingStr.·IdR (snd B∞) a) ab=0 ⟩
  a +∞ 𝟘∞
    ≡⟨ BooleanRingStr.+IdR (snd B∞) a ⟩
  a ∎

g∞-meet-neg-g∞-neq : (n m : ℕ) → ¬ (n ≡ m) → (g∞ n) ∧∞ (¬∞ (g∞ m)) ≡ g∞ n
g∞-meet-neg-g∞-neq n m n≠m = ∧-neg-orthogonal (g∞ n) (g∞ m) (gen-orthogonal n m n≠m)

g∞-meet-neg-g∞-eq : (n : ℕ) → (g∞ n) ∧∞ (¬∞ (g∞ n)) ≡ 𝟘∞
g∞-meet-neg-g∞-eq n = B∞-BoolAlg.¬Cancels∧R

g∞-meet-finMeetNeg-notin : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ false →
  (g∞ n) ∧∞ finMeetNeg∞ ms ≡ g∞ n
g∞-meet-finMeetNeg-notin n [] _ =
  (g∞ n) ∧∞ 𝟙∞   ≡⟨ B∞-BoolAlg.∧IdR ⟩
  g∞ n ∎
g∞-meet-finMeetNeg-notin n (m ∷ ms) p with discreteℕ n m
... | yes n=m = ex-falso (true≢false p)  -- contradiction: n ∈? (n ∷ ms) = true
... | no n≠m =
  (g∞ n) ∧∞ ((¬∞ (g∞ m)) ∧∞ finMeetNeg∞ ms)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) (g∞ n) (¬∞ (g∞ m)) (finMeetNeg∞ ms) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ m))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (g∞-meet-neg-g∞-neq n m n≠m) ⟩
  (g∞ n) ∧∞ finMeetNeg∞ ms
    ≡⟨ g∞-meet-finMeetNeg-notin n ms p ⟩
  g∞ n ∎

g∞-meet-finMeetNeg-in : (n : ℕ) (ms : List ℕ) → n ∈? ms ≡ true →
  (g∞ n) ∧∞ finMeetNeg∞ ms ≡ 𝟘∞
g∞-meet-finMeetNeg-in n [] p = ex-falso (true≢false (sym p))
g∞-meet-finMeetNeg-in n (m ∷ ms) p with discreteℕ n m
... | yes n=m =
  (g∞ n) ∧∞ ((¬∞ (g∞ m)) ∧∞ finMeetNeg∞ ms)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) (g∞ n) (¬∞ (g∞ m)) (finMeetNeg∞ ms) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ m))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (cong ((g∞ n) ∧∞_) (cong (¬∞_ ∘ g∞) (sym n=m))) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ n))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (g∞-meet-neg-g∞-eq n) ⟩
  𝟘∞ ∧∞ finMeetNeg∞ ms
    ≡⟨ B∞-BoolAlg.∧AnnihilL ⟩
  𝟘∞ ∎
... | no n≠m =
  (g∞ n) ∧∞ ((¬∞ (g∞ m)) ∧∞ finMeetNeg∞ ms)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) (g∞ n) (¬∞ (g∞ m)) (finMeetNeg∞ ms) ⟩
  ((g∞ n) ∧∞ (¬∞ (g∞ m))) ∧∞ finMeetNeg∞ ms
    ≡⟨ cong (_∧∞ finMeetNeg∞ ms) (g∞-meet-neg-g∞-neq n m n≠m) ⟩
  (g∞ n) ∧∞ finMeetNeg∞ ms
    ≡⟨ g∞-meet-finMeetNeg-in n ms p ⟩
  𝟘∞ ∎

_∖L_ : List ℕ → List ℕ → List ℕ
[] ∖L ms = []
(n ∷ ns) ∖L ms with n ∈? ms
... | true = ns ∖L ms
... | false = n ∷ (ns ∖L ms)

meet-joinForm-meetNegForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns ∧∞ finMeetNeg∞ ms ≡ finJoin∞ (ns ∖L ms)
meet-joinForm-meetNegForm-correct [] ms =
  𝟘∞ ∧∞ finMeetNeg∞ ms   ≡⟨ B∞-BoolAlg.∧AnnihilL ⟩
  𝟘∞ ∎
meet-joinForm-meetNegForm-correct (n ∷ ns) ms with n ∈? ms | inspect (n ∈?_) ms
... | true | [ n∈ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finMeetNeg∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  ((g∞ n) ∧∞ finMeetNeg∞ ms) ∨∞ (finJoin∞ ns ∧∞ finMeetNeg∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finMeetNeg-in n ms n∈ms) (meet-joinForm-meetNegForm-correct ns ms) ⟩
  𝟘∞ ∨∞ finJoin∞ (ns ∖L ms)
    ≡⟨ B∞-BoolAlg.∨IdL ⟩
  finJoin∞ (ns ∖L ms) ∎
... | false | [ n∉ms ] =
  (g∞ n ∨∞ finJoin∞ ns) ∧∞ finMeetNeg∞ ms
    ≡⟨ B∞-BoolAlg.∧DistL∨ ⟩
  ((g∞ n) ∧∞ finMeetNeg∞ ms) ∨∞ (finJoin∞ ns ∧∞ finMeetNeg∞ ms)
    ≡⟨ cong₂ _∨∞_ (g∞-meet-finMeetNeg-notin n ms n∉ms) (meet-joinForm-meetNegForm-correct ns ms) ⟩
  g∞ n ∨∞ finJoin∞ (ns ∖L ms) ∎

_△L_ : List ℕ → List ℕ → List ℕ
ns △L ms = (ns ++ ms) ∖L (ns ∩L ms)

·-idem-left : (a b : ⟨ B∞ ⟩) → a ∧∞ (a ∧∞ b) ≡ a ∧∞ b
·-idem-left a b =
  a ∧∞ (a ∧∞ b)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) a a b ⟩
  (a ∧∞ a) ∧∞ b
    ≡⟨ cong (_∧∞ b) (BooleanRingStr.·Idem (snd B∞) a) ⟩
  a ∧∞ b ∎

·-idem-right : (a b : ⟨ B∞ ⟩) → b ∧∞ (a ∧∞ b) ≡ a ∧∞ b
·-idem-right a b =
  b ∧∞ (a ∧∞ b)
    ≡⟨ BooleanRingStr.·Comm (snd B∞) b (a ∧∞ b) ⟩
  (a ∧∞ b) ∧∞ b
    ≡⟨ sym (BooleanRingStr.·Assoc (snd B∞) a b b) ⟩
  a ∧∞ (b ∧∞ b)
    ≡⟨ cong (a ∧∞_) (BooleanRingStr.·Idem (snd B∞) b) ⟩
  a ∧∞ b ∎

·-absorb-left : (a b : ⟨ B∞ ⟩) → a ·∞ (a ·∞ b) ≡ a ·∞ b
·-absorb-left a b =
  a ·∞ (a ·∞ b)
    ≡⟨ BooleanRingStr.·Assoc (snd B∞) a a b ⟩
  (a ·∞ a) ·∞ b
    ≡⟨ cong (_·∞ b) (BooleanRingStr.·Idem (snd B∞) a) ⟩
  a ·∞ b ∎

·-absorb-right : (a b : ⟨ B∞ ⟩) → b ·∞ (a ·∞ b) ≡ a ·∞ b
·-absorb-right a b =
  b ·∞ (a ·∞ b)
    ≡⟨ BooleanRingStr.·Comm (snd B∞) b (a ·∞ b) ⟩
  (a ·∞ b) ·∞ b
    ≡⟨ sym (BooleanRingStr.·Assoc (snd B∞) a b b) ⟩
  a ·∞ (b ·∞ b)
    ≡⟨ cong (a ·∞_) (BooleanRingStr.·Idem (snd B∞) b) ⟩
  a ·∞ b ∎

·-prod-idem : (a b : ⟨ B∞ ⟩) → (a ·∞ b) ·∞ (a ·∞ b) ≡ a ·∞ b
·-prod-idem a b = BooleanRingStr.·Idem (snd B∞) (a ·∞ b)

xor-·-distL-+ : (a b c : ⟨ B∞ ⟩) → (a +∞ b) ·∞ c ≡ (a ·∞ c) +∞ (b ·∞ c)
xor-·-distL-+ a b c = BooleanRingStr.·DistL+ (snd B∞) a b c

xor-·-distR-+ : (c a b : ⟨ B∞ ⟩) → c ·∞ (a +∞ b) ≡ (c ·∞ a) +∞ (c ·∞ b)
xor-·-distR-+ c a b = BooleanRingStr.·DistR+ (snd B∞) c a b

xor-·-1R : (x : ⟨ B∞ ⟩) → x ·∞ 𝟙∞ ≡ x
xor-·-1R x = BooleanRingStr.·IdR (snd B∞) x

xor-+∞-assoc : (a b c : ⟨ B∞ ⟩) → (a +∞ b) +∞ c ≡ a +∞ (b +∞ c)
xor-+∞-assoc a b c = sym (BooleanRingStr.+Assoc (snd B∞) a b c)

xor-·∞-assoc : (a b c : ⟨ B∞ ⟩) → (a ·∞ b) ·∞ c ≡ a ·∞ (b ·∞ c)
xor-·∞-assoc a b c = sym (BooleanRingStr.·Assoc (snd B∞) a b c)

xor-·∞-comm : (a b : ⟨ B∞ ⟩) → a ·∞ b ≡ b ·∞ a
xor-·∞-comm a b = BooleanRingStr.·Comm (snd B∞) a b

xor-·∞-idem : (a : ⟨ B∞ ⟩) → a ·∞ a ≡ a
xor-·∞-idem a = BooleanRingStr.·Idem (snd B∞) a

xor-+∞-0L : (x : ⟨ B∞ ⟩) → 𝟘∞ +∞ x ≡ x
xor-+∞-0L x = BooleanRingStr.+IdL (snd B∞) x

xor-+∞-0R : (x : ⟨ B∞ ⟩) → x +∞ 𝟘∞ ≡ x
xor-+∞-0R x = BooleanRingStr.+IdR (snd B∞) x

xor-a·ab=ab : (a b : ⟨ B∞ ⟩) → a ·∞ (a ·∞ b) ≡ a ·∞ b
xor-a·ab=ab a b =
  a ·∞ (a ·∞ b)
    ≡⟨ sym (xor-·∞-assoc a a b) ⟩
  (a ·∞ a) ·∞ b
    ≡⟨ cong (_·∞ b) (xor-·∞-idem a) ⟩
  a ·∞ b ∎

xor-b·ab=ab : (a b : ⟨ B∞ ⟩) → b ·∞ (a ·∞ b) ≡ a ·∞ b
xor-b·ab=ab a b =
  b ·∞ (a ·∞ b)
    ≡⟨ xor-·∞-comm b (a ·∞ b) ⟩
  (a ·∞ b) ·∞ b
    ≡⟨ xor-·∞-assoc a b b ⟩
  a ·∞ (b ·∞ b)
    ≡⟨ cong (a ·∞_) (xor-·∞-idem b) ⟩
  a ·∞ b ∎

xor-triple-distL : (x y z w : ⟨ B∞ ⟩) → (x +∞ y +∞ z) ·∞ w ≡ (x ·∞ w) +∞ (y ·∞ w) +∞ (z ·∞ w)
xor-triple-distL x y z w =
  (x +∞ y +∞ z) ·∞ w
    ≡⟨ xor-·-distL-+ (x +∞ y) z w ⟩
  ((x +∞ y) ·∞ w) +∞ (z ·∞ w)
    ≡⟨ cong (_+∞ (z ·∞ w)) (xor-·-distL-+ x y w) ⟩
  ((x ·∞ w) +∞ (y ·∞ w)) +∞ (z ·∞ w) ∎

xor-symmdiff : (a b : ⟨ B∞ ⟩) → a +∞ b ≡ (a ∨∞ b) ∧∞ (¬∞ (a ∧∞ b))
xor-symmdiff a b =
  let ab = a ·∞ b
      step1 : (a +∞ b +∞ ab) ·∞ 𝟙∞ ≡ a +∞ b +∞ ab
      step1 = xor-·-1R (a +∞ b +∞ ab)

      step2-dist : (a +∞ b +∞ ab) ·∞ ab ≡ (a ·∞ ab) +∞ (b ·∞ ab) +∞ (ab ·∞ ab)
      step2-dist = xor-triple-distL a b ab ab

      step2-simplify : (a ·∞ ab) +∞ (b ·∞ ab) +∞ (ab ·∞ ab) ≡ ab +∞ ab +∞ ab
      step2-simplify =
        (a ·∞ ab) +∞ (b ·∞ ab) +∞ (ab ·∞ ab)
          ≡⟨ cong (λ t → t +∞ (b ·∞ ab) +∞ (ab ·∞ ab)) (xor-a·ab=ab a b) ⟩
        ab +∞ (b ·∞ ab) +∞ (ab ·∞ ab)
          ≡⟨ cong (λ t → ab +∞ t +∞ (ab ·∞ ab)) (xor-b·ab=ab a b) ⟩
        ab +∞ ab +∞ (ab ·∞ ab)
          ≡⟨ cong (λ t → ab +∞ ab +∞ t) (xor-·∞-idem ab) ⟩
        ab +∞ ab +∞ ab ∎

      step2 : (a +∞ b +∞ ab) ·∞ ab ≡ ab +∞ ab +∞ ab
      step2 = step2-dist ∙ step2-simplify

      main-dist : (a +∞ b +∞ ab) ·∞ (𝟙∞ +∞ ab) ≡ ((a +∞ b +∞ ab) ·∞ 𝟙∞) +∞ ((a +∞ b +∞ ab) ·∞ ab)
      main-dist = xor-·-distR-+ (a +∞ b +∞ ab) 𝟙∞ ab

      main-simplified : ((a +∞ b +∞ ab) ·∞ 𝟙∞) +∞ ((a +∞ b +∞ ab) ·∞ ab) ≡ (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab)
      main-simplified =
        ((a +∞ b +∞ ab) ·∞ 𝟙∞) +∞ ((a +∞ b +∞ ab) ·∞ ab)
          ≡⟨ cong (_+∞ ((a +∞ b +∞ ab) ·∞ ab)) step1 ⟩
        (a +∞ b +∞ ab) +∞ ((a +∞ b +∞ ab) ·∞ ab)
          ≡⟨ cong ((a +∞ b +∞ ab) +∞_) step2 ⟩
        (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab) ∎

      step-reassoc1 : (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab) ≡ (a +∞ b) +∞ (ab +∞ (ab +∞ ab +∞ ab))
      step-reassoc1 = xor-+∞-assoc (a +∞ b) ab (ab +∞ ab +∞ ab)

      step-reassoc2 : (a +∞ b) +∞ (ab +∞ (ab +∞ ab +∞ ab)) ≡ (a +∞ b) +∞ ((ab +∞ ab) +∞ (ab +∞ ab))
      step-reassoc2 = cong ((a +∞ b) +∞_) (
        ab +∞ (ab +∞ ab +∞ ab)
          ≡⟨ sym (xor-+∞-assoc ab (ab +∞ ab) ab) ⟩
        (ab +∞ (ab +∞ ab)) +∞ ab
          ≡⟨ cong (_+∞ ab) (sym (xor-+∞-assoc ab ab ab)) ⟩
        ((ab +∞ ab) +∞ ab) +∞ ab
          ≡⟨ xor-+∞-assoc (ab +∞ ab) ab ab ⟩
        (ab +∞ ab) +∞ (ab +∞ ab) ∎)

      step-cancel : (a +∞ b) +∞ ((ab +∞ ab) +∞ (ab +∞ ab)) ≡ (a +∞ b) +∞ 𝟘∞
      step-cancel = cong ((a +∞ b) +∞_) (
        (ab +∞ ab) +∞ (ab +∞ ab)
          ≡⟨ cong (_+∞ (ab +∞ ab)) (char2-B∞ ab) ⟩
        𝟘∞ +∞ (ab +∞ ab)
          ≡⟨ xor-+∞-0L (ab +∞ ab) ⟩
        ab +∞ ab
          ≡⟨ char2-B∞ ab ⟩
        𝟘∞ ∎)

      flatten : (a +∞ b +∞ ab) +∞ (ab +∞ ab +∞ ab) ≡ a +∞ b
      flatten = step-reassoc1 ∙ step-reassoc2 ∙ step-cancel ∙ xor-+∞-0R (a +∞ b)

      rhs-expanded : (a ∨∞ b) ∧∞ (¬∞ (a ∧∞ b)) ≡ (a +∞ b +∞ ab) ·∞ (𝟙∞ +∞ ab)
      rhs-expanded = refl

  in sym (rhs-expanded ∙ main-dist ∙ main-simplified ∙ flatten)

xor-joinForm-joinForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns +∞ finJoin∞ ms ≡ finJoin∞ (ns △L ms)
xor-joinForm-joinForm-correct ns ms =
  finJoin∞ ns +∞ finJoin∞ ms
    ≡⟨ xor-symmdiff (finJoin∞ ns) (finJoin∞ ms) ⟩
  (finJoin∞ ns ∨∞ finJoin∞ ms) ∧∞ (¬∞ (finJoin∞ ns ∧∞ finJoin∞ ms))
    ≡⟨ cong₂ (λ x y → x ∧∞ (¬∞ y)) (join-joinForm-correct ns ms) (meet-joinForm-joinForm-correct ns ms) ⟩
  finJoin∞ (ns ++ ms) ∧∞ (¬∞ (finJoin∞ (ns ∩L ms)))
    ≡⟨ cong (finJoin∞ (ns ++ ms) ∧∞_) (sym (neg-nf-correct (joinForm (ns ∩L ms)))) ⟩
  finJoin∞ (ns ++ ms) ∧∞ finMeetNeg∞ (ns ∩L ms)
    ≡⟨ meet-joinForm-meetNegForm-correct (ns ++ ms) (ns ∩L ms) ⟩
  finJoin∞ ((ns ++ ms) ∖L (ns ∩L ms))
    ≡⟨ refl ⟩
  finJoin∞ (ns △L ms) ∎

xor-meetNegForm-meetNegForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns +∞ finMeetNeg∞ ms ≡ finJoin∞ (ns △L ms)
xor-meetNegForm-meetNegForm-correct ns ms =
  finMeetNeg∞ ns +∞ finMeetNeg∞ ms
    ≡⟨ cong₂ _+∞_ (sym (neg-finJoin ns)) (sym (neg-finJoin ms)) ⟩
  ¬∞ (finJoin∞ ns) +∞ ¬∞ (finJoin∞ ms)
    ≡⟨ refl ⟩  -- ¬x = 1 + x, so this is (1 + a) + (1 + b)
  (𝟙∞ +∞ finJoin∞ ns) +∞ (𝟙∞ +∞ finJoin∞ ms)
    ≡⟨ xor-+∞-assoc 𝟙∞ (finJoin∞ ns) (𝟙∞ +∞ finJoin∞ ms) ⟩
  𝟙∞ +∞ (finJoin∞ ns +∞ (𝟙∞ +∞ finJoin∞ ms))
    ≡⟨ cong (𝟙∞ +∞_) (sym (xor-+∞-assoc (finJoin∞ ns) 𝟙∞ (finJoin∞ ms))) ⟩
  𝟙∞ +∞ ((finJoin∞ ns +∞ 𝟙∞) +∞ finJoin∞ ms)
    ≡⟨ cong (λ t → 𝟙∞ +∞ (t +∞ finJoin∞ ms)) (BooleanRingStr.+Comm (snd B∞) (finJoin∞ ns) 𝟙∞) ⟩
  𝟙∞ +∞ ((𝟙∞ +∞ finJoin∞ ns) +∞ finJoin∞ ms)
    ≡⟨ cong (𝟙∞ +∞_) (xor-+∞-assoc 𝟙∞ (finJoin∞ ns) (finJoin∞ ms)) ⟩
  𝟙∞ +∞ (𝟙∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms))
    ≡⟨ sym (xor-+∞-assoc 𝟙∞ 𝟙∞ (finJoin∞ ns +∞ finJoin∞ ms)) ⟩
  (𝟙∞ +∞ 𝟙∞) +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ cong (_+∞ (finJoin∞ ns +∞ finJoin∞ ms)) (char2-B∞ 𝟙∞) ⟩
  𝟘∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ xor-+∞-0L (finJoin∞ ns +∞ finJoin∞ ms) ⟩
  finJoin∞ ns +∞ finJoin∞ ms
    ≡⟨ xor-joinForm-joinForm-correct ns ms ⟩
  finJoin∞ (ns △L ms) ∎

xor-joinForm-meetNegForm-correct : (ns ms : List ℕ) →
  finJoin∞ ns +∞ finMeetNeg∞ ms ≡ finMeetNeg∞ (ns △L ms)
xor-joinForm-meetNegForm-correct ns ms =
  finJoin∞ ns +∞ finMeetNeg∞ ms
    ≡⟨ cong (finJoin∞ ns +∞_) (sym (neg-finJoin ms)) ⟩
  finJoin∞ ns +∞ ¬∞ (finJoin∞ ms)
    ≡⟨ refl ⟩  -- ¬x = 1 + x
  finJoin∞ ns +∞ (𝟙∞ +∞ finJoin∞ ms)
    ≡⟨ sym (xor-+∞-assoc (finJoin∞ ns) 𝟙∞ (finJoin∞ ms)) ⟩
  (finJoin∞ ns +∞ 𝟙∞) +∞ finJoin∞ ms
    ≡⟨ cong (_+∞ finJoin∞ ms) (BooleanRingStr.+Comm (snd B∞) (finJoin∞ ns) 𝟙∞) ⟩
  (𝟙∞ +∞ finJoin∞ ns) +∞ finJoin∞ ms
    ≡⟨ xor-+∞-assoc 𝟙∞ (finJoin∞ ns) (finJoin∞ ms) ⟩
  𝟙∞ +∞ (finJoin∞ ns +∞ finJoin∞ ms)
    ≡⟨ cong (𝟙∞ +∞_) (xor-joinForm-joinForm-correct ns ms) ⟩
  𝟙∞ +∞ finJoin∞ (ns △L ms)
    ≡⟨ refl ⟩  -- = ¬(finJoin∞ (ns △L ms))
  ¬∞ (finJoin∞ (ns △L ms))
    ≡⟨ neg-finJoin (ns △L ms) ⟩
  finMeetNeg∞ (ns △L ms) ∎

xor-meetNegForm-joinForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns +∞ finJoin∞ ms ≡ finMeetNeg∞ (ms △L ns)
xor-meetNegForm-joinForm-correct ns ms =
  finMeetNeg∞ ns +∞ finJoin∞ ms
    ≡⟨ BooleanRingStr.+Comm (snd B∞) (finMeetNeg∞ ns) (finJoin∞ ms) ⟩
  finJoin∞ ms +∞ finMeetNeg∞ ns
    ≡⟨ xor-joinForm-meetNegForm-correct ms ns ⟩
  finMeetNeg∞ (ms △L ns) ∎

meet-meetNegForm-joinForm-correct : (ns ms : List ℕ) →
  finMeetNeg∞ ns ∧∞ finJoin∞ ms ≡ finJoin∞ (ms ∖L ns)
meet-meetNegForm-joinForm-correct ns ms =
  finMeetNeg∞ ns ∧∞ finJoin∞ ms
    ≡⟨ BooleanRingStr.·Comm (snd B∞) (finMeetNeg∞ ns) (finJoin∞ ms) ⟩
  finJoin∞ ms ∧∞ finMeetNeg∞ ns
    ≡⟨ meet-joinForm-meetNegForm-correct ms ns ⟩
  finJoin∞ (ms ∖L ns) ∎

xor-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
xor-nf (joinForm ns) (joinForm ms) = joinForm (ns △L ms)
xor-nf (joinForm ns) (meetNegForm ms) = meetNegForm (ns △L ms)
xor-nf (meetNegForm ns) (joinForm ms) = meetNegForm (ms △L ns)
xor-nf (meetNegForm ns) (meetNegForm ms) = joinForm (ns △L ms)

xor-nf-correct : (nf1 nf2 : B∞-NormalForm) → ⟦ xor-nf nf1 nf2 ⟧nf ≡ ⟦ nf1 ⟧nf +∞ ⟦ nf2 ⟧nf
xor-nf-correct (joinForm ns) (joinForm ms) = sym (xor-joinForm-joinForm-correct ns ms)
xor-nf-correct (joinForm ns) (meetNegForm ms) = sym (xor-joinForm-meetNegForm-correct ns ms)
xor-nf-correct (meetNegForm ns) (joinForm ms) = sym (xor-meetNegForm-joinForm-correct ns ms)
xor-nf-correct (meetNegForm ns) (meetNegForm ms) = sym (xor-meetNegForm-meetNegForm-correct ns ms)

meet-nf : B∞-NormalForm → B∞-NormalForm → B∞-NormalForm
meet-nf (joinForm ns) (joinForm ms) = joinForm (ns ∩L ms)
meet-nf (joinForm ns) (meetNegForm ms) = joinForm (ns ∖L ms)
meet-nf (meetNegForm ns) (joinForm ms) = joinForm (ms ∖L ns)
meet-nf (meetNegForm ns) (meetNegForm ms) = meetNegForm (ns ++ ms)

meet-nf-correct : (nf1 nf2 : B∞-NormalForm) → ⟦ meet-nf nf1 nf2 ⟧nf ≡ ⟦ nf1 ⟧nf ∧∞ ⟦ nf2 ⟧nf
meet-nf-correct (joinForm ns) (joinForm ms) = sym (meet-joinForm-joinForm-correct ns ms)
meet-nf-correct (joinForm ns) (meetNegForm ms) = sym (meet-joinForm-meetNegForm-correct ns ms)
meet-nf-correct (meetNegForm ns) (joinForm ms) = sym (meet-meetNegForm-joinForm-correct ns ms)
meet-nf-correct (meetNegForm ns) (meetNegForm ms) = sym (meet-meetNegForm-correct ns ms)

open import BooleanRing.FreeBooleanRing.SurjectiveTerms using (TermsOf_[_]; Tvar; Tconst; _+T_; -T_; _·T_; includeTerm)
open import BooleanRing.FreeBooleanRing.freeBATerms using (freeBATerms; includeBATermsSurj)

normalizeTerm : freeBATerms ℕ → B∞-NormalForm
normalizeTerm (Tvar n) = joinForm (n ∷ [])  -- generator g_n
normalizeTerm (Tconst false) = joinForm []  -- 0
normalizeTerm (Tconst true) = meetNegForm []  -- 1
normalizeTerm (t +T s) = xor-nf (normalizeTerm t) (normalizeTerm s)
normalizeTerm (-T t) = normalizeTerm t  -- ring negation is identity in Boolean rings
normalizeTerm (t ·T s) = meet-nf (normalizeTerm t) (normalizeTerm s)

interpretB∞ : freeBATerms ℕ → ⟨ B∞ ⟩
interpretB∞ (Tvar n) = g∞ n
interpretB∞ (Tconst false) = 𝟘∞
interpretB∞ (Tconst true) = 𝟙∞
interpretB∞ (t +T s) = interpretB∞ t +∞ interpretB∞ s
interpretB∞ (-T t) = -∞ interpretB∞ t  -- ring negation (= identity in Boolean rings)
interpretB∞ (t ·T s) = interpretB∞ t ·∞ interpretB∞ s

negation-is-id-B∞ : (x : ⟨ B∞ ⟩) → -∞ x ≡ x
negation-is-id-B∞ x =
  -∞ x
    ≡⟨ sym (BooleanRingStr.+IdR (snd B∞) (-∞ x)) ⟩
  -∞ x +∞ 𝟘∞
    ≡⟨ cong (-∞ x +∞_) (sym (char2-B∞ x)) ⟩
  -∞ x +∞ (x +∞ x)
    ≡⟨ BooleanRingStr.+Assoc (snd B∞) (-∞ x) x x ⟩
  (-∞ x +∞ x) +∞ x
    ≡⟨ cong (_+∞ x) (BooleanRingStr.+InvL (snd B∞) x) ⟩
  𝟘∞ +∞ x
    ≡⟨ BooleanRingStr.+IdL (snd B∞) x ⟩
  x ∎

normalizeTerm-correct : (t : freeBATerms ℕ) → ⟦ normalizeTerm t ⟧nf ≡ interpretB∞ t
normalizeTerm-correct (Tvar n) =
  finJoin∞ (n ∷ [])
    ≡⟨ refl ⟩
  g∞ n ∨∞ finJoin∞ []
    ≡⟨ zero-join-right (g∞ n) ⟩
  g∞ n ∎
normalizeTerm-correct (Tconst false) =
  refl
normalizeTerm-correct (Tconst true) =
  refl
normalizeTerm-correct (t +T s) =
  ⟦ xor-nf (normalizeTerm t) (normalizeTerm s) ⟧nf
    ≡⟨ xor-nf-correct (normalizeTerm t) (normalizeTerm s) ⟩
  ⟦ normalizeTerm t ⟧nf +∞ ⟦ normalizeTerm s ⟧nf
    ≡⟨ cong₂ _+∞_ (normalizeTerm-correct t) (normalizeTerm-correct s) ⟩
  interpretB∞ t +∞ interpretB∞ s ∎
normalizeTerm-correct (-T t) =
  ⟦ normalizeTerm t ⟧nf
    ≡⟨ normalizeTerm-correct t ⟩
  interpretB∞ t
    ≡⟨ sym (negation-is-id-B∞ (interpretB∞ t)) ⟩
  -∞ interpretB∞ t ∎
normalizeTerm-correct (t ·T s) =
  ⟦ meet-nf (normalizeTerm t) (normalizeTerm s) ⟧nf
    ≡⟨ meet-nf-correct (normalizeTerm t) (normalizeTerm s) ⟩
  ⟦ normalizeTerm t ⟧nf ∧∞ ⟦ normalizeTerm s ⟧nf
    ≡⟨ cong₂ _∧∞_ (normalizeTerm-correct t) (normalizeTerm-correct s) ⟩
  interpretB∞ t ∧∞ interpretB∞ s
    ≡⟨ refl ⟩
  interpretB∞ t ·∞ interpretB∞ s ∎

open import Cubical.Functions.Surjection using (isSurjection ; compSurjection ; _↠_)
open import BooleanRing.FreeBooleanRing.freeBATerms using
  (includeBATermsSurj ; equalityFromEqualityOnGenerators ; includeBATerms-Tvar ;
   includeBATerms-+ ; includeBATerms-· ; includeBATerms-- ; includeBATerms-0 ; includeBATerms-1)

π∞-surj : isSurjection (fst π∞)
π∞-surj = QB.quotientImageHomSurjective

π∞-includeTerms-surj : isSurjection (fst π∞ ∘ fst includeBATermsSurj)
π∞-includeTerms-surj = compSurjection (fst includeBATermsSurj , snd includeBATermsSurj) (fst π∞ , π∞-surj) .snd

π∞-from-terms : freeBATerms ℕ → ⟨ B∞ ⟩
π∞-from-terms t = fst π∞ (fst includeBATermsSurj t)

private
  open module π∞-hom = IsCommRingHom (snd π∞) renaming
    (pres+ to π∞-+' ; pres· to π∞-·' ; pres- to π∞-neg' ; pres0 to π∞-0' ; pres1 to π∞-1')
  π∞-0 : fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ))) ≡ 𝟘∞
  π∞-0 = π∞-0'
  π∞-1 : fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ))) ≡ 𝟙∞
  π∞-1 = π∞-1'
  π∞-+ : (x y : ⟨ freeBA ℕ ⟩) → fst π∞ (BooleanRingStr._+_ (snd (freeBA ℕ)) x y) ≡ fst π∞ x +∞ fst π∞ y
  π∞-+ = π∞-+'
  π∞-· : (x y : ⟨ freeBA ℕ ⟩) → fst π∞ (BooleanRingStr._·_ (snd (freeBA ℕ)) x y) ≡ fst π∞ x ·∞ fst π∞ y
  π∞-· = π∞-·'
  π∞-neg : (x : ⟨ freeBA ℕ ⟩) → fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) x) ≡ -∞ fst π∞ x
  π∞-neg = π∞-neg'

interpretB∞-eq-composition : (t : freeBATerms ℕ) → interpretB∞ t ≡ π∞-from-terms t
interpretB∞-eq-composition (Tvar n) =
  g∞ n
    ≡⟨ refl ⟩
  fst π∞ (generator n)
    ≡⟨ cong (fst π∞) (sym (includeBATerms-Tvar n)) ⟩
  fst π∞ (fst includeBATermsSurj (Tvar n)) ∎
interpretB∞-eq-composition (Tconst false) =
  𝟘∞
    ≡⟨ sym π∞-0 ⟩
  fst π∞ (BooleanRingStr.𝟘 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-0) ⟩
  fst π∞ (fst includeBATermsSurj (Tconst false)) ∎

interpretB∞-eq-composition (Tconst true) =
  𝟙∞
    ≡⟨ sym π∞-1 ⟩
  fst π∞ (BooleanRingStr.𝟙 (snd (freeBA ℕ)))
    ≡⟨ cong (fst π∞) (sym includeBATerms-1) ⟩
  fst π∞ (fst includeBATermsSurj (Tconst true)) ∎

interpretB∞-eq-composition (t +T s) =
  interpretB∞ t +∞ interpretB∞ s
    ≡⟨ cong₂ _+∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t +∞ π∞-from-terms s
    ≡⟨ sym (π∞-+ (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._+_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-+ t s)) ⟩
  π∞-from-terms (t +T s) ∎

interpretB∞-eq-composition (-T t) =
  -∞ interpretB∞ t
    ≡⟨ cong -∞_ (interpretB∞-eq-composition t) ⟩
  -∞ π∞-from-terms t
    ≡⟨ sym (π∞-neg (fst includeBATermsSurj t)) ⟩
  fst π∞ (BooleanRingStr.-_ (snd (freeBA ℕ)) (fst includeBATermsSurj t))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-- t)) ⟩
  π∞-from-terms (-T t) ∎

interpretB∞-eq-composition (t ·T s) =
  interpretB∞ t ·∞ interpretB∞ s
    ≡⟨ cong₂ _·∞_ (interpretB∞-eq-composition t) (interpretB∞-eq-composition s) ⟩
  π∞-from-terms t ·∞ π∞-from-terms s
    ≡⟨ sym (π∞-· (fst includeBATermsSurj t) (fst includeBATermsSurj s)) ⟩
  fst π∞ (BooleanRingStr._·_ (snd (freeBA ℕ)) (fst includeBATermsSurj t) (fst includeBATermsSurj s))
    ≡⟨ cong (fst π∞) (sym (includeBATerms-· t s)) ⟩
  π∞-from-terms (t ·T s) ∎

interpretB∞-surjective : isSurjection interpretB∞
interpretB∞-surjective x = PT.map helper (π∞-includeTerms-surj x)
  where
  helper : Σ[ t ∈ freeBATerms ℕ ] π∞-from-terms t ≡ x → Σ[ t ∈ freeBATerms ℕ ] interpretB∞ t ≡ x
  helper pair = fst pair , interpretB∞-eq-composition (fst pair) ∙ snd pair

open import Cubical.Data.List using (isOfHLevelList)
open import Cubical.Data.Nat using (isSetℕ)

isSetListℕ : isSet (List ℕ)
isSetListℕ = isOfHLevelList 0 isSetℕ

isSetB∞-NormalForm : isSet B∞-NormalForm
isSetB∞-NormalForm = Discrete→isSet discreteNF
  where
  open import Cubical.Relation.Nullary using (Discrete; yes; no; Dec)
  open import Cubical.Data.List using (discreteList)
  open import Cubical.Data.Nat using (discreteℕ)

  discreteListℕ : Discrete (List ℕ)
  discreteListℕ = discreteList discreteℕ

  discreteNF : Discrete B∞-NormalForm
  discreteNF (joinForm ns) (joinForm ms) with discreteListℕ ns ms
  ... | yes p = yes (cong joinForm p)
  ... | no ¬p = no (λ eq → ¬p (joinForm-inj eq))
    where
    joinForm-inj : joinForm ns ≡ joinForm ms → ns ≡ ms
    joinForm-inj p = cong (λ { (joinForm x) → x ; (meetNegForm _) → [] }) p
  discreteNF (joinForm _) (meetNegForm _) = no (λ p → joinForm≢meetNegForm p)
    where
    joinForm≢meetNegForm : ∀ {ns ms} → joinForm ns ≡ meetNegForm ms → ⊥
    joinForm≢meetNegForm p = transport (cong (λ { (joinForm _) → Unit ; (meetNegForm _) → ⊥ }) p) tt
  discreteNF (meetNegForm _) (joinForm _) = no (λ p → meetNegForm≢joinForm p)
    where
    meetNegForm≢joinForm : ∀ {ns ms} → meetNegForm ns ≡ joinForm ms → ⊥
    meetNegForm≢joinForm p = transport (cong (λ { (joinForm _) → ⊥ ; (meetNegForm _) → Unit }) p) tt
  discreteNF (meetNegForm ns) (meetNegForm ms) with discreteListℕ ns ms
  ... | yes p = yes (cong meetNegForm p)
  ... | no ¬p = no (λ eq → ¬p (meetNegForm-inj eq))
    where
    meetNegForm-inj : meetNegForm ns ≡ meetNegForm ms → ns ≡ ms
    meetNegForm-inj p = cong (λ { (joinForm _) → [] ; (meetNegForm x) → x }) p

normalFormExists-trunc : (x : ⟨ B∞ ⟩) → ∥ Σ[ nf ∈ B∞-NormalForm ] ⟦ nf ⟧nf ≡ x ∥₁
normalFormExists-trunc x = PT.map
  (λ pair → normalizeTerm (fst pair) , normalizeTerm-correct (fst pair) ∙ snd pair)
  (interpretB∞-surjective x)

f-kernel-from-trunc : (x : ⟨ B∞ ⟩) → fst f x ≡ (𝟘∞ , 𝟘∞) → x ≡ 𝟘∞
f-kernel-from-trunc x fx=0 = PT.rec (BooleanRingStr.is-set (snd B∞) x 𝟘∞)
  (λ pair → let nf = fst pair
                eq = snd pair
            in sym eq ∙ f-kernel-normalForm nf (cong (fst f) eq ∙ fx=0))
  (normalFormExists-trunc x)

f-injective-from-trunc : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective-from-trunc x y fx=fy =
  let -- f is a ring homomorphism, so f(x - y) = f(x) - f(y) = 0
      xy-diff : ⟨ B∞ ⟩
      xy-diff = x +∞ y

      f-xy-diff : fst f xy-diff ≡ (𝟘∞ , 𝟘∞)
      f-xy-diff =
        fst f (x +∞ y)
          ≡⟨ f-pres+ x y ⟩
        (fst f x) +× (fst f y)
          ≡⟨ cong (_+× (fst f y)) fx=fy ⟩
        (fst f y) +× (fst f y)
          ≡⟨ char2-B∞×B∞ (fst f y) ⟩
        (𝟘∞ , 𝟘∞) ∎

      xy=0 : xy-diff ≡ 𝟘∞
      xy=0 = f-kernel-from-trunc xy-diff f-xy-diff

      x=y : x ≡ y
      x=y = BooleanRing-xor-eq-to-eq' x y xy=0

  in x=y
  where
  BooleanRing-xor-eq-to-eq' : (a b : ⟨ B∞ ⟩) → a +∞ b ≡ 𝟘∞ → a ≡ b
  BooleanRing-xor-eq-to-eq' a b ab=0 =
    a
      ≡⟨ sym (BooleanRingStr.+IdR (snd B∞) a) ⟩
    a +∞ 𝟘∞
      ≡⟨ cong (a +∞_) (sym (char2-B∞ b)) ⟩
    a +∞ (b +∞ b)
      ≡⟨ BooleanRingStr.+Assoc (snd B∞) a b b ⟩
    (a +∞ b) +∞ b
      ≡⟨ cong (_+∞ b) ab=0 ⟩
    𝟘∞ +∞ b
      ≡⟨ BooleanRingStr.+IdL (snd B∞) b ⟩
    b ∎

