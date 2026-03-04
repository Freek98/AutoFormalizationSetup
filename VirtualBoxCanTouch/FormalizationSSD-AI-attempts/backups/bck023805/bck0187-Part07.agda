{-# OPTIONS --cubical --guardedness #-}

module work.Part07 where

open import work.Part06 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; invEq; propBiimpl→Equiv; compEquiv; secEq; isEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false; if_then_else_)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Nullary.Properties using (isProp¬)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; squash₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΣ; isSetΣ; hProp; TypeOfHLevel≡)
import QuotientBool as QB
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import CountablyPresentedBooleanRings.PresentedBoole using (idBoolHom; has-Boole-ω')

-- tex Lemma 251 (ClosedPropAsSpectrum)
module ClosedPropAsSpectrum where
  open import Cubical.Algebra.CommRing.Quotient.ImageQuotient

  BoolBR-quotient : binarySequence → BooleanRing ℓ-zero
  BoolBR-quotient α = BoolBR QB./Im α

  all-false→Sp : (α : binarySequence) → ((n : ℕ) → α n ≡ false)
               → BoolHom (BoolBR-quotient α) BoolBR
  all-false→Sp α all-false = QB.inducedHom {B = BoolBR} {f = α} BoolBR (idBoolHom BoolBR) all-false

  Sp→all-false : (α : binarySequence) → BoolHom (BoolBR-quotient α) BoolBR
               → ((n : ℕ) → α n ≡ false)
  Sp→all-false α h n = αn-is-false (α n) refl
    where
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)

    π : ⟨ BoolBR ⟩ → ⟨ BoolBR-quotient α ⟩
    π = fst QB.quotientImageHom

    αn-is-false : (b : Bool) → α n ≡ b → b ≡ false
    αn-is-false false _ = refl
    αn-is-false true αn≡true = ex-falso (true≢false chain)
      where
      open BooleanRingStr (snd (BoolBR-quotient α)) using () renaming (𝟘 to 𝟘Q ; 𝟙 to 𝟙Q)
      chain : true ≡ false
      chain =
        true
          ≡⟨ sym h-pres1 ⟩
        fst h 𝟙Q
          ≡⟨ cong (fst h) (sym (IsCommRingHom.pres1 (snd QB.quotientImageHom))) ⟩
        fst h (π true)
          ≡⟨ cong (λ x → fst h (π x)) (sym αn≡true) ⟩
        fst h (π (α n))
          ≡⟨ cong (fst h) (QB.zeroOnImage {B = BoolBR} {f = α} n) ⟩
        fst h 𝟘Q
          ≡⟨ h-pres0 ⟩
        false ∎

  closedPropAsSpectrum : (α : binarySequence)
                       → ((n : ℕ) → α n ≡ false) ↔ BoolHom (BoolBR-quotient α) BoolBR
  closedPropAsSpectrum α = all-false→Sp α , Sp→all-false α

-- PropositionsClosedIffStone (tex Corollary 1628)

module ClosedPropIffStone where
  open import Axioms.StoneDuality using (hasStoneStr; Stone; isPropHasStoneStr)
  open ClosedPropAsSpectrum

  closedProp→hasStoneStr : (P : hProp ℓ-zero) → isClosedProp P → hasStoneStr (fst P)
  closedProp→hasStoneStr P Pclosed = PT.rec (isPropHasStoneStr sd-axiom _) go Pclosed
    where
    go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false) → hasStoneStr (fst P)
    go (α , P→∀ , ∀→P) = B-quotient-Booleω , sym (ua P≃Sp)
      where
      B-quotient : BooleanRing ℓ-zero
      B-quotient = BoolBR-quotient α

      Sp-quotient : Type ℓ-zero
      Sp-quotient = BoolHom B-quotient BoolBR

      all-false↔Sp : ((n : ℕ) → α n ≡ false) ↔ Sp-quotient
      all-false↔Sp = closedPropAsSpectrum α

      B-quotient-Booleω : Booleω
      B-quotient-Booleω = B-quotient , quotientPreservesBooleω α

      all-false-type : Type ℓ-zero
      all-false-type = (n : ℕ) → α n ≡ false

      isProp-all-false : isProp all-false-type
      isProp-all-false = isPropΠ (λ n → isSetBool (α n) false)

      P≃all-false : fst P ≃ all-false-type
      P≃all-false = propBiimpl→Equiv (snd P) isProp-all-false P→∀ ∀→P

      Sp-roundtrip : (h : Sp-quotient) → fst all-false↔Sp (snd all-false↔Sp h) ≡ h
      Sp-roundtrip h = QB.inducedHomUnique {B = BoolBR} {f = α} BoolBR (idBoolHom BoolBR) (snd all-false↔Sp h) h h-comp
        where
        π : ⟨ BoolBR ⟩ → ⟨ B-quotient ⟩
        π = fst QB.quotientImageHom

        open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
        open IsCommRingHom (snd QB.quotientImageHom) renaming (pres0 to π-pres0 ; pres1 to π-pres1)

        h∘π≡id-pointwise : (b : Bool) → fst h (π b) ≡ b
        h∘π≡id-pointwise false =
          fst h (π false)
            ≡⟨ cong (fst h) π-pres0 ⟩
          fst h (BooleanRingStr.𝟘 (snd B-quotient))
            ≡⟨ h-pres0 ⟩
          false ∎
        h∘π≡id-pointwise true =
          fst h (π true)
            ≡⟨ cong (fst h) π-pres1 ⟩
          fst h (BooleanRingStr.𝟙 (snd B-quotient))
            ≡⟨ h-pres1 ⟩
          true ∎

        h-comp : idBoolHom BoolBR ≡ (h ∘cr QB.quotientImageHom)
        h-comp = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing BoolBR)) f
                                                    (snd (BooleanRing→CommRing BoolBR)))
                        (sym (funExt h∘π≡id-pointwise))

      isProp-Sp-quotient : isProp Sp-quotient
      isProp-Sp-quotient h₁ h₂ =
        let all-f₁ = snd all-false↔Sp h₁
            all-f₂ = snd all-false↔Sp h₂
            all-f-eq : all-f₁ ≡ all-f₂
            all-f-eq = isProp-all-false all-f₁ all-f₂
        in h₁                                    ≡⟨ sym (Sp-roundtrip h₁) ⟩
           fst all-false↔Sp all-f₁               ≡⟨ cong (fst all-false↔Sp) all-f-eq ⟩
           fst all-false↔Sp all-f₂               ≡⟨ Sp-roundtrip h₂ ⟩
           h₂                                    ∎

      all-false≃Sp : all-false-type ≃ Sp-quotient
      all-false≃Sp = propBiimpl→Equiv isProp-all-false isProp-Sp-quotient
                      (fst all-false↔Sp) (snd all-false↔Sp)

      P≃Sp : fst P ≃ Sp-quotient
      P≃Sp = compEquiv P≃all-false all-false≃Sp

-- TruncationStoneClosed (tex Corollary 1613)

module TruncationStoneClosed where
  0=1→¬Sp : (B : Booleω) → BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))
           → ¬ Sp B
  0=1→¬Sp B 0≡1 h = true≢false chain
    where
    open BooleanRingStr (snd (fst B)) renaming (𝟘 to 𝟘B ; 𝟙 to 𝟙B)
    open IsCommRingHom (snd h) renaming (pres0 to h-pres0 ; pres1 to h-pres1)
    chain : true ≡ false
    chain =
      true
        ≡⟨ sym h-pres1 ⟩
      fst h 𝟙B
        ≡⟨ cong (fst h) (sym 0≡1) ⟩
      fst h 𝟘B
        ≡⟨ h-pres0 ⟩
      false ∎

-- SpectrumEmptyIff01Equal (tex Lemma 406)
-- For B:Boole, 0 =_B 1 iff ¬Sp(B)
SpectrumEmptyIff01Equal : (B : Booleω)
  → (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B))) ≃ (¬ Sp B)
SpectrumEmptyIff01Equal B = propBiimpl→Equiv
  (BooleanRingStr.is-set (snd (fst B)) _ _) (isProp¬ _)
  (TruncationStoneClosed.0=1→¬Sp B) (SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B)

-- LemSurjectionsFormalToCompleteness (tex Corollary 415)

module LemSurjectionsFormalToCompleteness where

  ¬¬Sp→0≢1 : (B : Booleω) → ¬ ¬ Sp B → ¬ (BooleanRingStr.𝟘 (snd (fst B)) ≡ BooleanRingStr.𝟙 (snd (fst B)))
  ¬¬Sp→0≢1 B ¬¬SpB 0≡1 = ¬¬SpB (TruncationStoneClosed.0=1→¬Sp B 0≡1)

  canonical-hom : (B : BooleanRing ℓ-zero) → BoolHom BoolBR B
  canonical-hom B = BoolBR→ B

  canonical-hom-injective : (B : BooleanRing ℓ-zero)
    → ¬ (BooleanRingStr.𝟘 (snd B) ≡ BooleanRingStr.𝟙 (snd B))
    → (b₁ b₂ : Bool) → fst (canonical-hom B) b₁ ≡ fst (canonical-hom B) b₂ → b₁ ≡ b₂
  canonical-hom-injective B 0≢1 false false _ = refl
  canonical-hom-injective B 0≢1 false true  p = ex-falso (0≢1 p)
  canonical-hom-injective B 0≢1 true  false p = ex-falso (0≢1 (sym p))
  canonical-hom-injective B 0≢1 true  true  _ = refl

  ¬¬Sp→truncSp : (B : Booleω) → ¬ ¬ Sp B → ∥ Sp B ∥₁
  ¬¬Sp→truncSp B ¬¬SpB = PT.rec squash₁
    (λ pt → PT.rec squash₁ (λ preimg → ∣ fst preimg ∣₁)
      (injective→Sp-surjective Bool-Booleω B (canonical-hom (fst B))
        (canonical-hom-injective (fst B) (¬¬Sp→0≢1 B ¬¬SpB)) pt))
    Sp-Bool-inhabited

  truncSp→¬¬Sp : (B : Booleω) → ∥ Sp B ∥₁ → ¬ ¬ Sp B
  truncSp→¬¬Sp B = PT.rec (isProp¬ _) (λ pt ¬SpB → ¬SpB pt)

  -- This is tex Corollary 415 (LemSurjectionsFormalToCompleteness)
  LemSurjectionsFormalToCompleteness-derived : (B : Booleω)
    → ⟨ ¬hProp ((¬ Sp B) , isProp¬ (Sp B)) ⟩ ≃ ∥ Sp B ∥₁
  LemSurjectionsFormalToCompleteness-derived B =
    propBiimpl→Equiv
      (isProp¬ (¬ Sp B))
      squash₁
      (¬¬Sp→truncSp B)
      (truncSp→¬¬Sp B)

-- ODisc Infrastructure (tex Definition 918, Lemma 1336)
module ODiscInfrastructure where
  open import BooleanRing.FreeBooleanRing.FreeBool
    using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
  open import BooleanRing.FreeBooleanRing.freeBATerms
    using (freeBATerms; includeBATermsSurj; equalityFromEqualityOnGenerators)
  open import BooleanRing.FreeBooleanRing.SurjectiveTerms
    using (TermsOf_[_]; Tvar; Tconst; _+T_; -T_; _·T_)
  open import CountablyPresentedBooleanRings.PresentedBoole
    using (has-Boole-ω'; idBoolHom; isPropIsBoolRingHom)
  open import BooleanRing.BoolRingUnivalence using (IsBoolRingHom)
  open import Axioms.StoneDuality using (SDHomVersion; evaluationMap)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
  open import Cubical.Foundations.Function using (_∘_; idfun)
  open import Cubical.Foundations.Equiv using (invEq; isEquiv; secEq; retEq; invEquiv)
  open import Cubical.Relation.Nullary using (Dec; yes; no)
  open import Cubical.Relation.Nullary.Properties using (isPropDec; Collapsible→SplitSupport)
  open import Cubical.Data.Bool using (Dec→Bool; _and_; _⊕_; not; true≢false; false≢true)
    renaming (true to tt; false to ff)
  open import Cubical.Algebra.CommRing.Instances.Bool using (BoolCR)
  open import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
    using (generatedIdeal)
  import QuotientBool as QB
  open import Cubical.Algebra.CommRing.Quotient.Base using (kernel≡I; zeroOnIdeal; quotientHomSurjective)
  import Cubical.Algebra.CommRing.Kernel as CK
  open import Cubical.Data.Nat using (zero; suc; max) renaming (_+_ to _+ℕ_)
  open import Cubical.Data.Nat.Properties using (discreteℕ; +-comm)
  open import Cubical.Data.List using (List; []; _∷_; _++_)
  open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)

  -- Part A: freeBA ℕ is Booleω (quotient by zero ideal ≅ original)
  private
    freeBA-ℕ = freeBA ℕ
    open BooleanRingStr (snd freeBA-ℕ) using (+IdR) renaming (𝟘 to 𝟘F; 𝟙 to 𝟙F; _+_ to _+F_; _·_ to _·F_; is-set to isSetF; ·DistL+ to ·DistL+F)
    R' = BooleanRing→CommRing freeBA-ℕ
    genI : (ℕ → ⟨ freeBA-ℕ ⟩) → ⟨ freeBA-ℕ ⟩ → Type
    genI = generatedIdeal R'

    f₀ : ℕ → ⟨ freeBA-ℕ ⟩
    f₀ _ = 𝟘F

    Q₀ : BooleanRing ℓ-zero
    Q₀ = freeBA-ℕ QB./Im f₀

    π₀ : BoolHom freeBA-ℕ Q₀
    π₀ = QB.quotientImageHom

    inv₀ : BoolHom Q₀ freeBA-ℕ
    inv₀ = QB.inducedHom freeBA-ℕ (idBoolHom freeBA-ℕ) (λ _ → refl)

    inv∘π≡id : inv₀ ∘cr π₀ ≡ idBoolHom freeBA-ℕ
    inv∘π≡id = QB.evalInduce freeBA-ℕ {g = idBoolHom freeBA-ℕ} {gfx=0 = λ _ → refl}

    π∘inv-fun : fst π₀ ∘ fst inv₀ ≡ idfun ⟨ Q₀ ⟩
    π∘inv-fun = QB.quotientImageHomEpi (⟨ Q₀ ⟩ , BooleanRingStr.is-set (snd Q₀))
                  (cong (fst π₀ ∘_) (cong fst inv∘π≡id))

    π₀-iso : Iso ⟨ freeBA-ℕ ⟩ ⟨ Q₀ ⟩
    π₀-iso = iso (fst π₀) (fst inv₀) (funExt⁻ π∘inv-fun) (funExt⁻ (cong fst inv∘π≡id))

  freeBA-ℕ-Booleω : Booleω
  freeBA-ℕ-Booleω = freeBA-ℕ , ∣ f₀ , isoToEquiv π₀-iso , snd π₀ ∣₁

  -- Part B: Term evaluation for decidability of freeBA ℕ equality
  termEval : (ℕ → Bool) → freeBATerms ℕ → Bool
  termEval ρ (Tvar n) = ρ n
  termEval ρ (Tconst b) = b
  termEval ρ (t₁ +T t₂) = termEval ρ t₁ ⊕ termEval ρ t₂
  termEval ρ (-T t) = termEval ρ t
  termEval ρ (t₁ ·T t₂) = termEval ρ t₁ and termEval ρ t₂

  -- Finite variable check: enumerate all assignments to a list of variables
  private
    update : (ℕ → Bool) → ℕ → Bool → (ℕ → Bool)
    update ρ v b n with discreteℕ n v
    ... | yes _ = b
    ... | no  _ = ρ n

    eqBool : Bool → Bool → Bool
    eqBool ff ff = tt
    eqBool tt tt = tt
    eqBool _  _  = ff

  checkVars : (ℕ → Bool) → freeBATerms ℕ → freeBATerms ℕ → List ℕ → Bool
  checkVars ρ t₁ t₂ [] = eqBool (termEval ρ t₁) (termEval ρ t₂)
  checkVars ρ t₁ t₂ (v ∷ vs) = checkVars (update ρ v ff) t₁ t₂ vs
                                 and checkVars (update ρ v tt) t₁ t₂ vs

  -- Variable extraction from terms
  vars : freeBATerms ℕ → List ℕ
  vars (Tvar n) = n ∷ []
  vars (Tconst _) = []
  vars (t₁ +T t₂) = vars t₁ ++ vars t₂
  vars (-T t) = vars t
  vars (t₁ ·T t₂) = vars t₁ ++ vars t₂

  -- Full check: check all assignments to all variables
  checkTerms : freeBATerms ℕ → freeBATerms ℕ → Bool
  checkTerms t₁ t₂ = checkVars (λ _ → ff) t₁ t₂ (vars t₁ ++ vars t₂)

  -- Part E: Decidability infrastructure
  private
    eqBool-sound : ∀ a b → eqBool a b ≡ tt → a ≡ b
    eqBool-sound ff ff _ = refl
    eqBool-sound ff tt p = ex-falso (false≢true p)
    eqBool-sound tt ff p = ex-falso (false≢true p)
    eqBool-sound tt tt _ = refl

    eqBool-refl : ∀ a → eqBool a a ≡ tt
    eqBool-refl ff = refl
    eqBool-refl tt = refl

    eqBool-complete : ∀ {a b} → a ≡ b → eqBool a b ≡ tt
    eqBool-complete {a} p = subst (λ b → eqBool a b ≡ tt) p (eqBool-refl a)

    and-tt-l : ∀ {a b} → (a and b) ≡ tt → a ≡ tt
    and-tt-l {tt} _ = refl
    and-tt-l {ff} p = ex-falso (false≢true p)

    and-tt-r : ∀ {a b} → (a and b) ≡ tt → b ≡ tt
    and-tt-r {tt} {tt} _ = refl
    and-tt-r {tt} {ff} p = ex-falso (false≢true p)
    and-tt-r {ff} p = ex-falso (false≢true p)

    and-intro : ∀ {a b} → a ≡ tt → b ≡ tt → (a and b) ≡ tt
    and-intro p q = cong₂ _and_ p q

    and-ff-l : ∀ {a b} → a ≡ ff → (a and b) ≡ ff
    and-ff-l {b = b} p = cong (_and b) p

    and-ff-r : ∀ {a b} → b ≡ ff → (a and b) ≡ ff
    and-ff-r {tt} p = p
    and-ff-r {ff} _ = refl

    eqBool-neq : ∀ a b → ¬ (a ≡ b) → eqBool a b ≡ ff
    eqBool-neq ff ff p = ex-falso (p refl)
    eqBool-neq ff tt _ = refl
    eqBool-neq tt ff _ = refl
    eqBool-neq tt tt p = ex-falso (p refl)

    -- outside σ ρ vs: σ agrees with ρ-updated-by-σ after exhausting variables in vs
    outside : (σ ρ : ℕ → Bool) → List ℕ → Type
    outside σ ρ [] = ∀ n → σ n ≡ ρ n
    outside σ ρ (v ∷ vs) = outside σ (update ρ v (σ v)) vs

    checkVars-sound : ∀ ρ t₁ t₂ vs σ
      → checkVars ρ t₁ t₂ vs ≡ tt → outside σ ρ vs
      → termEval σ t₁ ≡ termEval σ t₂
    checkVars-sound ρ t₁ t₂ [] σ h agree =
      eqBool-sound _ _ (subst (λ f → eqBool (termEval f t₁) (termEval f t₂) ≡ tt)
        (sym (funExt agree)) h)
    checkVars-sound ρ t₁ t₂ (v ∷ vs) σ h agree with σ v
    ... | ff = checkVars-sound (update ρ v ff) t₁ t₂ vs σ (and-tt-l h) agree
    ... | tt = checkVars-sound (update ρ v tt) t₁ t₂ vs σ (and-tt-r h) agree

    checkVars-gives-ff : ∀ ρ t₁ t₂ vs σ
      → ¬ (termEval σ t₁ ≡ termEval σ t₂) → outside σ ρ vs
      → checkVars ρ t₁ t₂ vs ≡ ff
    checkVars-gives-ff ρ t₁ t₂ [] σ neq agree =
      subst (λ f → eqBool (termEval f t₁) (termEval f t₂) ≡ ff) (funExt agree)
        (eqBool-neq _ _ neq)
    checkVars-gives-ff ρ t₁ t₂ (v ∷ vs) σ neq agree with σ v
    ... | ff = and-ff-l (checkVars-gives-ff (update ρ v ff) t₁ t₂ vs σ neq agree)
    ... | tt = and-ff-r (checkVars-gives-ff (update ρ v tt) t₁ t₂ vs σ neq agree)

    checkVars-complete : ∀ ρ t₁ t₂ vs
      → (∀ σ → termEval σ t₁ ≡ termEval σ t₂) → checkVars ρ t₁ t₂ vs ≡ tt
    checkVars-complete ρ t₁ t₂ [] hyp = eqBool-complete (hyp ρ)
    checkVars-complete ρ t₁ t₂ (v ∷ vs) hyp =
      and-intro (checkVars-complete (update ρ v ff) t₁ t₂ vs hyp)
                (checkVars-complete (update ρ v tt) t₁ t₂ vs hyp)

    -- buildAssignment: accumulate updates from σ into ρ for listed variables
    buildAssignment : (σ ρ : ℕ → Bool) → List ℕ → (ℕ → Bool)
    buildAssignment σ ρ [] = ρ
    buildAssignment σ ρ (v ∷ vs) = buildAssignment σ (update ρ v (σ v)) vs

    -- Key lemma: if σ v ≡ ρ v, then buildAssignment preserves σ v
    update-same : ∀ ρ' v' b → update ρ' v' b v' ≡ b
    update-same ρ' v' b with discreteℕ v' v'
    ... | yes _ = refl
    ... | no ¬p = ex-falso (¬p refl)

    update-other : ∀ ρ' v' b n → ¬ (n ≡ v') → update ρ' v' b n ≡ ρ' n
    update-other ρ' v' b n ¬p with discreteℕ n v'
    ... | yes p = ex-falso (¬p p)
    ... | no _ = refl

    update-agree : (σ ρ : ℕ → Bool) (m n : ℕ) → σ n ≡ ρ n → σ n ≡ update ρ m (σ m) n
    update-agree σ ρ m n h = go (discreteℕ n m)
      where
      go : Dec (n ≡ m) → σ n ≡ update ρ m (σ m) n
      go (yes p) = subst (λ k → σ k ≡ update ρ m (σ m) k) (sym p)
                     (sym (update-same ρ m (σ m)))
      go (no ¬p) = h ∙ sym (update-other ρ m (σ m) n ¬p)

    buildAssignment-σ : ∀ σ ρ vs n → σ n ≡ ρ n → buildAssignment σ ρ vs n ≡ σ n
    buildAssignment-σ σ ρ [] n h = sym h
    buildAssignment-σ σ ρ (m ∷ vs) n h =
      buildAssignment-σ σ (update ρ m (σ m)) vs n (update-agree σ ρ m n h)

    -- outside-build: buildAssignment σ ρ vs satisfies outside w.r.t. ρ and vs
    outside-build : ∀ σ ρ vs → outside (buildAssignment σ ρ vs) ρ vs
    outside-build σ ρ [] n = refl
    outside-build σ ρ (v ∷ vs) =
      subst (λ b → outside σ' (update ρ v b) vs) (sym σ'v≡σv) ih
      where
      σ' = buildAssignment σ (update ρ v (σ v)) vs
      ih = outside-build σ (update ρ v (σ v)) vs
      σ'v≡σv : σ' v ≡ σ v
      σ'v≡σv = buildAssignment-σ σ (update ρ v (σ v)) vs v
                 (sym (update-same ρ v (σ v)))

    -- appears: boolean membership test for variable lists
    appears : ℕ → List ℕ → Bool
    appears n [] = ff
    appears n (m ∷ vs) with discreteℕ n m
    ... | yes _ = tt
    ... | no  _ = appears n vs

    appears-here : ∀ n vs → appears n (n ∷ vs) ≡ tt
    appears-here n vs with discreteℕ n n
    ... | yes _ = refl
    ... | no ¬p = ex-falso (¬p refl)

    appears-++l : ∀ n xs ys → appears n xs ≡ tt → appears n (xs ++ ys) ≡ tt
    appears-++l n [] ys h = ex-falso (false≢true h)
    appears-++l n (m ∷ xs) ys h with discreteℕ n m
    ... | yes _ = refl
    ... | no  _ = appears-++l n xs ys h

    appears-++r : ∀ n xs ys → appears n ys ≡ tt → appears n (xs ++ ys) ≡ tt
    appears-++r n [] ys h = h
    appears-++r n (m ∷ xs) ys h with discreteℕ n m
    ... | yes _ = refl
    ... | no  _ = appears-++r n xs ys h

    -- termEval depends only on variables that appear in the term
    termEval-ext : ∀ t σ₁ σ₂
      → (∀ n → appears n (vars t) ≡ tt → σ₁ n ≡ σ₂ n)
      → termEval σ₁ t ≡ termEval σ₂ t
    termEval-ext (Tvar n) σ₁ σ₂ h = h n (appears-here n [])
    termEval-ext (Tconst _) _ _ _ = refl
    termEval-ext (t₁ +T t₂) σ₁ σ₂ h = cong₂ _⊕_
      (termEval-ext t₁ σ₁ σ₂ λ n p → h n (appears-++l n (vars t₁) (vars t₂) p))
      (termEval-ext t₂ σ₁ σ₂ λ n p → h n (appears-++r n (vars t₁) (vars t₂) p))
    termEval-ext (-T t) σ₁ σ₂ h = termEval-ext t σ₁ σ₂ h
    termEval-ext (t₁ ·T t₂) σ₁ σ₂ h = cong₂ _and_
      (termEval-ext t₁ σ₁ σ₂ λ n p → h n (appears-++l n (vars t₁) (vars t₂) p))
      (termEval-ext t₂ σ₁ σ₂ λ n p → h n (appears-++r n (vars t₁) (vars t₂) p))

    appears-cons-no : ∀ n m vs → ¬ (n ≡ m) → appears n (m ∷ vs) ≡ appears n vs
    appears-cons-no n m vs ¬p with discreteℕ n m
    ... | yes p = ex-falso (¬p p)
    ... | no _  = refl

    -- buildAssignment covers listed variables
    buildAssignment-appears : (σ ρ : ℕ → Bool) (vs : List ℕ) (n : ℕ)
      → appears n vs ≡ tt → buildAssignment σ ρ vs n ≡ σ n
    buildAssignment-appears σ ρ [] n h = ex-falso (false≢true h)
    buildAssignment-appears σ ρ (m ∷ vs) n h = go (discreteℕ n m)
      where
      go : Dec (n ≡ m) → buildAssignment σ (update ρ m (σ m)) vs n ≡ σ n
      go (yes p) = subst (λ k → buildAssignment σ (update ρ m (σ m)) vs k ≡ σ k) (sym p)
                     (buildAssignment-σ σ (update ρ m (σ m)) vs m (sym (update-same ρ m (σ m))))
      go (no ¬p) = buildAssignment-appears σ (update ρ m (σ m)) vs n
                     (subst (_≡ tt) (appears-cons-no n m vs ¬p) h)

  -- checkTerms soundness and completeness
  checkTerms-sound : ∀ t₁ t₂ → checkTerms t₁ t₂ ≡ tt
    → ∀ σ → termEval σ t₁ ≡ termEval σ t₂
  checkTerms-sound t₁ t₂ h σ =
    termEval σ t₁
      ≡⟨ ext₁ ⟩
    termEval σ' t₁
      ≡⟨ step ⟩
    termEval σ' t₂
      ≡⟨ sym ext₂ ⟩
    termEval σ t₂ ∎
    where
    vs = vars t₁ ++ vars t₂
    σ' = buildAssignment σ (λ _ → ff) vs
    step = checkVars-sound (λ _ → ff) t₁ t₂ vs σ' h
             (outside-build σ (λ _ → ff) vs)
    ext₁ = termEval-ext t₁ σ σ' λ n p →
      sym (buildAssignment-appears σ (λ _ → ff) vs n (appears-++l n (vars t₁) (vars t₂) p))
    ext₂ = termEval-ext t₂ σ σ' λ n p →
      sym (buildAssignment-appears σ (λ _ → ff) vs n (appears-++r n (vars t₁) (vars t₂) p))

  checkTerms-complete : ∀ t₁ t₂
    → (∀ σ → termEval σ t₁ ≡ termEval σ t₂) → checkTerms t₁ t₂ ≡ tt
  checkTerms-complete t₁ t₂ = checkVars-complete (λ _ → ff) t₁ t₂ (vars t₁ ++ vars t₂)

  -- Part C: SD injectivity for freeBA ℕ
  open import Cubical.Foundations.Equiv using (equivFun; retEq)

  private
    φ : (ℕ → Bool) → BoolHom freeBA-ℕ BoolBR
    φ = inducedBAHom ℕ BoolBR

    sd-eq = SDHomVersion sd-axiom freeBA-ℕ-Booleω

    freeBA-ℕ-injective : (a b : ⟨ freeBA-ℕ ⟩)
       → ((ρ : ℕ → Bool) → fst (φ ρ) a ≡ fst (φ ρ) b) → a ≡ b
    freeBA-ℕ-injective a b hyp =
      a
        ≡⟨ sym (retEq (fst sd-eq) a) ⟩
      invEq (fst sd-eq) (equivFun (fst sd-eq) a)
        ≡⟨ cong (invEq (fst sd-eq)) ev-eq ⟩
      invEq (fst sd-eq) (equivFun (fst sd-eq) b)
        ≡⟨ retEq (fst sd-eq) b ⟩
      b ∎
      where
      ev-eq : equivFun (fst sd-eq) a ≡ equivFun (fst sd-eq) b
      ev-eq = funExt λ h →
        fst h a
          ≡⟨ cong (λ g → fst g a) (sym (inducedBAHomUnique ℕ BoolBR _ h refl)) ⟩
        fst (φ (fst h ∘ generator)) a
          ≡⟨ hyp (fst h ∘ generator) ⟩
        fst (φ (fst h ∘ generator)) b
          ≡⟨ cong (λ g → fst g b) (inducedBAHomUnique ℕ BoolBR _ h refl) ⟩
        fst h b ∎

  -- Part D: termEval is sound (agrees with inducedBAHom on π-images)
  private
    π : freeBATerms ℕ → ⟨ freeBA-ℕ ⟩
    π = fst includeBATermsSurj

  opaque
    unfolding includeBATermsSurj generator

    termEval-sound : (ρ : ℕ → Bool) (t : freeBATerms ℕ)
      → fst (φ ρ) (π t) ≡ termEval ρ t
    termEval-sound ρ (Tvar n) = funExt⁻ (evalBAInduce ℕ BoolBR ρ) n
    termEval-sound ρ (Tconst false) = IsCommRingHom.pres0 (snd (φ ρ))
    termEval-sound ρ (Tconst true) = IsCommRingHom.pres1 (snd (φ ρ))
    termEval-sound ρ (t₁ +T t₂) =
      fst (φ ρ) (π (t₁ +T t₂))
        ≡⟨ IsCommRingHom.pres+ (snd (φ ρ)) (π t₁) (π t₂) ⟩
      fst (φ ρ) (π t₁) ⊕ fst (φ ρ) (π t₂)
        ≡⟨ cong₂ _⊕_ (termEval-sound ρ t₁) (termEval-sound ρ t₂) ⟩
      termEval ρ t₁ ⊕ termEval ρ t₂ ∎
    termEval-sound ρ (-T t) =
      fst (φ ρ) (π (-T t))
        ≡⟨ IsCommRingHom.pres- (snd (φ ρ)) (π t) ⟩
      fst (φ ρ) (π t)
        ≡⟨ termEval-sound ρ t ⟩
      termEval ρ t ∎
    termEval-sound ρ (t₁ ·T t₂) =
      fst (φ ρ) (π (t₁ ·T t₂))
        ≡⟨ IsCommRingHom.pres· (snd (φ ρ)) (π t₁) (π t₂) ⟩
      fst (φ ρ) (π t₁) and fst (φ ρ) (π t₂)
        ≡⟨ cong₂ _and_ (termEval-sound ρ t₁) (termEval-sound ρ t₂) ⟩
      termEval ρ t₁ and termEval ρ t₂ ∎

  -- Part F: DecEq for freeBA ℕ
  private
    decπEq : (t₁ t₂ : freeBATerms ℕ) → Dec (π t₁ ≡ π t₂)
    decπEq t₁ t₂ = go (checkTerms t₁ t₂) refl
      where
      go : (b : Bool) → checkTerms t₁ t₂ ≡ b → Dec (π t₁ ≡ π t₂)
      go tt h = yes (freeBA-ℕ-injective (π t₁) (π t₂) λ ρ →
        fst (φ ρ) (π t₁)
          ≡⟨ termEval-sound ρ t₁ ⟩
        termEval ρ t₁
          ≡⟨ checkTerms-sound t₁ t₂ h ρ ⟩
        termEval ρ t₂
          ≡⟨ sym (termEval-sound ρ t₂) ⟩
        fst (φ ρ) (π t₂) ∎)
      go ff h = no λ p → false≢true (sym h ∙ checkTerms-complete t₁ t₂ λ ρ →
        termEval ρ t₁
          ≡⟨ sym (termEval-sound ρ t₁) ⟩
        fst (φ ρ) (π t₁)
          ≡⟨ cong (fst (φ ρ)) p ⟩
        fst (φ ρ) (π t₂)
          ≡⟨ termEval-sound ρ t₂ ⟩
        termEval ρ t₂ ∎)

  freeBA-ℕ-DecEq : (a b : ⟨ freeBA-ℕ ⟩) → Dec (a ≡ b)
  freeBA-ℕ-DecEq a b = PT.rec2 (isPropDec (isSetF a b))
    (λ (ta , pa) (tb , pb) →
      transport (cong₂ (λ x y → Dec (x ≡ y)) pa pb) (decπEq ta tb))
    (snd includeBATermsSurj a) (snd includeBATermsSurj b)

  -- Part G: Finite join in freeBA ℕ and ideal characterization
  private
    open BooleanAlgebraStr freeBA-ℕ using (∧AbsorbL∨; ∨AbsorbL∧; ∧DistR∨; ∨Comm; ∨IdR; ∧AnnihilR; ∧AnnihilL; ∧Comm; characteristic2; ∧Idem) renaming (_∨_ to _∨F_)

    finJoinF : (ℕ → ⟨ freeBA-ℕ ⟩) → ℕ → ⟨ freeBA-ℕ ⟩
    finJoinF g zero = g zero
    finJoinF g (suc n) = finJoinF g n ∨F g (suc n)

    -- If x · a = x, then x · (a ∨ b) = x
    ·-mono-∨ : (x a b : ⟨ freeBA-ℕ ⟩) → x ·F a ≡ x → x ·F (a ∨F b) ≡ x
    ·-mono-∨ x a b h =
      x ·F (a ∨F b)
        ≡⟨ ∧DistR∨ ⟩
      (x ·F a) ∨F (x ·F b)
        ≡⟨ cong (_∨F (x ·F b)) h ⟩
      x ∨F (x ·F b)
        ≡⟨ ∨AbsorbL∧ ⟩
      x ∎

    -- step-to: if x · finJoinF f N = x, then x · finJoinF f (M + N) = x
    step-to : (f : ℕ → ⟨ freeBA-ℕ ⟩) (x : ⟨ freeBA-ℕ ⟩) (N M : ℕ)
      → x ·F finJoinF f N ≡ x → x ·F finJoinF f (M +ℕ N) ≡ x
    step-to f x N zero h = h
    step-to f x N (suc M) h = ·-mono-∨ x (finJoinF f (M +ℕ N)) (f (suc (M +ℕ N)))
                                 (step-to f x N M h)

    -- Single generator: f(n) · finJoinF f n = f(n)
    single-absorbed : (f : ℕ → ⟨ freeBA-ℕ ⟩) (n : ℕ) → f n ·F finJoinF f n ≡ f n
    single-absorbed f zero = ∧Idem
    single-absorbed f (suc n) =
      f (suc n) ·F (finJoinF f n ∨F f (suc n))
        ≡⟨ cong (f (suc n) ·F_) (∨Comm) ⟩
      f (suc n) ·F (f (suc n) ∨F finJoinF f n)
        ≡⟨ ∧AbsorbL∨ ⟩
      f (suc n) ∎

    -- Ideal forward: genI f c → ∥ Σ N. c · finJoinF f N ≡ c ∥₁
    idealForward : (f : ℕ → ⟨ freeBA-ℕ ⟩) (c : ⟨ freeBA-ℕ ⟩)
      → genI f c → ∥ Σ[ N ∈ ℕ ] c ·F finJoinF f N ≡ c ∥₁
    idealForward f ._ (IQ.single n) = ∣ n , single-absorbed f n ∣₁
    idealForward f ._ IQ.zero = ∣ zero , ∧AnnihilL ∣₁
    idealForward f ._ (IQ.add {x} {y} gx gy) = PT.rec2 squash₁
      (λ (N₁ , h₁) (N₂ , h₂) → ∣ (N₁ +ℕ N₂) ,
        ((x +F y) ·F finJoinF f (N₁ +ℕ N₂)
          ≡⟨ ·DistL+F x y (finJoinF f (N₁ +ℕ N₂)) ⟩
        (x ·F finJoinF f (N₁ +ℕ N₂)) +F (y ·F finJoinF f (N₁ +ℕ N₂))
          ≡⟨ cong₂ _+F_
               (subst (λ k → x ·F finJoinF f k ≡ x) (+-comm N₂ N₁) (step-to f x N₁ N₂ h₁))
               (step-to f y N₂ N₁ h₂) ⟩
        x +F y ∎) ∣₁)
      (idealForward f x gx) (idealForward f y gy)
    idealForward f ._ (IQ.mul {r} {x} gx) = PT.map
      (λ (N , h) → N , (
        (r ·F x) ·F finJoinF f N
          ≡⟨ sym (BooleanRingStr.·Assoc (snd freeBA-ℕ) r x _) ⟩
        r ·F (x ·F finJoinF f N)
          ≡⟨ cong (r ·F_) h ⟩
        r ·F x ∎))
      (idealForward f x gx)
    idealForward f c (IQ.squash gx gy i) = squash₁
      (idealForward f c gx) (idealForward f c gy) i

    -- Ideal backward: c · finJoinF f N ≡ c → genI f c
    idealBackward : (f : ℕ → ⟨ freeBA-ℕ ⟩) (c : ⟨ freeBA-ℕ ⟩) (N : ℕ)
      → c ·F finJoinF f N ≡ c → genI f c
    idealBackward f c zero h = subst (genI f) h (IQ.mul {r = c} (IQ.single zero))
    idealBackward f c (suc N) h = subst (genI f) h
      (IQ.mul {r = c} (join-in-ideal f (suc N)))
      where
      join-in-ideal : (f : ℕ → ⟨ freeBA-ℕ ⟩) (N : ℕ) → genI f (finJoinF f N)
      join-in-ideal f zero = IQ.single zero
      join-in-ideal f (suc N) = IQ.add
        (IQ.add (join-in-ideal f N) (IQ.single (suc N)))
        (IQ.mul {r = finJoinF f N} (IQ.single (suc N)))

  -- Main proof
  booleω-equality-open : (B : Booleω) → (a b : ⟨ fst B ⟩)
    → isOpenProp ((a ≡ b) , BooleanRingStr.is-set (snd (fst B)) a b)
  booleω-equality-open B a b = PT.rec squash₁ construct (snd B)
    where
    open BooleanRingStr (snd (fst B)) using () renaming (_+_ to _+B_; 𝟘 to 0B; is-set to isSetB; +IdR to +IdRB; +Comm to +CommB; +Assoc to +AssocB)
    char2B = BooleanAlgebraStr.characteristic2 (fst B)

    c : ⟨ fst B ⟩
    c = a +B b

    a≡b→c≡0 : a ≡ b → c ≡ 0B
    a≡b→c≡0 p = cong (a +B_) (sym p) ∙ char2B

    c≡0→a≡b : c ≡ 0B → a ≡ b
    c≡0→a≡b p =
      a
        ≡⟨ sym (+IdRB a) ⟩
      a +B 0B
        ≡⟨ cong (a +B_) (sym p) ⟩
      a +B (a +B b)
        ≡⟨ +AssocB a a b ⟩
      (a +B a) +B b
        ≡⟨ cong (_+B b) char2B ⟩
      0B +B b
        ≡⟨ +CommB 0B b ⟩
      b +B 0B
        ≡⟨ +IdRB b ⟩
      b ∎

    construct : has-Boole-ω' (fst B) → ∥ isOpenWitness ((a ≡ b) , isSetB a b) ∥₁
    construct (f , equiv) = PT.rec squash₁ go (πQ-surj (ψ c))
      where
      -- Quotient infrastructure
      Q-CR = R' IQ./Im f
      Iₐ = IQ.genIdeal R' f
      ψ : ⟨ fst B ⟩ → ⟨ freeBA-ℕ QB./Im f ⟩
      ψ = fst (fst equiv)
      ψ-hom = snd equiv
      πQ : ⟨ freeBA-ℕ ⟩ → ⟨ freeBA-ℕ QB./Im f ⟩
      πQ = fst (QB.quotientImageHom {B = freeBA-ℕ} {f = f})
      πQ-surj = QB.quotientImageHomSurjective {B = freeBA-ℕ} {f = f}
      0Q = BooleanRingStr.𝟘 (snd (freeBA-ℕ QB./Im f))

      -- ψ preserves 0
      ψ-pres0 : ψ 0B ≡ 0Q
      ψ-pres0 = IsCommRingHom.pres0 ψ-hom

      -- πQ preserves 0
      πQ-pres0 : πQ 𝟘F ≡ 0Q
      πQ-pres0 = IsCommRingHom.pres0 (snd (QB.quotientImageHom {B = freeBA-ℕ} {f = f}))

      -- genI f d → πQ d ≡ 0Q (ideal membership implies zero in quotient)
      inIdeal→πQ≡0 : (d : ⟨ freeBA-ℕ ⟩) → genI f d → πQ d ≡ 0Q
      inIdeal→πQ≡0 ._ (IQ.single n) = QB.zeroOnImage {B = freeBA-ℕ} {f = f} n
      inIdeal→πQ≡0 ._ IQ.zero = πQ-pres0
      inIdeal→πQ≡0 ._ (IQ.add {x} {y} gx gy) =
        IsCommRingHom.pres+ πQ-hom x y
        ∙ cong₂ (BooleanRingStr._+_ (snd (freeBA-ℕ QB./Im f))) (inIdeal→πQ≡0 x gx) (inIdeal→πQ≡0 y gy)
        ∙ BooleanRingStr.+IdR (snd (freeBA-ℕ QB./Im f)) 0Q
        where πQ-hom = snd (QB.quotientImageHom {B = freeBA-ℕ} {f = f})
      inIdeal→πQ≡0 ._ (IQ.mul {r} {x} gx) =
        IsCommRingHom.pres· πQ-hom r x
        ∙ cong (BooleanRingStr._·_ (snd (freeBA-ℕ QB./Im f)) (πQ r)) (inIdeal→πQ≡0 x gx)
        ∙ BooleanAlgebraStr.∧AnnihilR (freeBA-ℕ QB./Im f)
        where πQ-hom = snd (QB.quotientImageHom {B = freeBA-ℕ} {f = f})
      inIdeal→πQ≡0 _ (IQ.squash gx gy i) =
        BooleanRingStr.is-set (snd (freeBA-ℕ QB./Im f)) _ _ (inIdeal→πQ≡0 _ gx) (inIdeal→πQ≡0 _ gy) i

      -- πQ d ≡ 0Q → genI f d (quotient effectiveness via kernel≡I)
      opaque
        unfolding QB._/Im_ QB.quotientImageHom
        πQ≡0→inIdeal : (d : ⟨ freeBA-ℕ ⟩) → πQ d ≡ 0Q → genI f d
        πQ≡0→inIdeal d πQd≡0 = subst (λ P → fst (fst P d)) (kernel≡I Iₐ) πQd≡0

      go : (Σ[ d ∈ ⟨ freeBA-ℕ ⟩ ] πQ d ≡ ψ c) → ∥ isOpenWitness ((a ≡ b) , isSetB a b) ∥₁
      go (d , πQd≡ψc) = ∣ α , fwd , bwd ∣₁
        where
        α : binarySequence
        α N = Dec→Bool (freeBA-ℕ-DecEq (d ·F finJoinF f N) d)

        -- Extract concrete witness from truncated one using decidability
        extract : ∥ Σ[ N ∈ ℕ ] d ·F finJoinF f N ≡ d ∥₁ → Σ[ N ∈ ℕ ] d ·F finJoinF f N ≡ d
        extract = Collapsible→SplitSupport
          (Decidable→Collapsible (λ _ → isSetF _ _) (λ m → freeBA-ℕ-DecEq (d ·F finJoinF f m) d))

        -- Dec→Bool (yes p) ≡ true
        Dec→Bool-yes : ∀ {ℓ'} {P : Type ℓ'} (d : Dec P) → P → Dec→Bool d ≡ tt
        Dec→Bool-yes (yes _) _ = refl
        Dec→Bool-yes (no ¬p) p = ex-falso (¬p p)

        -- Dec→Bool d ≡ true → P
        Dec→Bool-true : ∀ {ℓ'} {P : Type ℓ'} (d : Dec P) → Dec→Bool d ≡ tt → P
        Dec→Bool-true (yes p) _ = p
        Dec→Bool-true (no _) h = ex-falso (false≢true h)

        fwd : a ≡ b → Σ[ n ∈ ℕ ] α n ≡ tt
        fwd p = let
          c≡0 = a≡b→c≡0 p
          ψc≡0 : ψ c ≡ 0Q
          ψc≡0 = cong ψ c≡0 ∙ ψ-pres0
          πQd≡0 : πQ d ≡ 0Q
          πQd≡0 = πQd≡ψc ∙ ψc≡0
          d-in-I : genI f d
          d-in-I = πQ≡0→inIdeal d πQd≡0
          trunc-witness : ∥ Σ[ N ∈ ℕ ] d ·F finJoinF f N ≡ d ∥₁
          trunc-witness = idealForward f d d-in-I
          N , h = extract trunc-witness
          in N , Dec→Bool-yes (freeBA-ℕ-DecEq (d ·F finJoinF f N) d) h

        bwd : Σ[ n ∈ ℕ ] α n ≡ tt → a ≡ b
        bwd (N , αN≡tt) = let
          h : d ·F finJoinF f N ≡ d
          h = Dec→Bool-true (freeBA-ℕ-DecEq (d ·F finJoinF f N) d) αN≡tt
          d-in-I : genI f d
          d-in-I = idealBackward f d N h
          πQd≡0 : πQ d ≡ 0Q
          πQd≡0 = inIdeal→πQ≡0 d d-in-I
          ψc≡0 : ψ c ≡ 0Q
          ψc≡0 = sym πQd≡ψc ∙ πQd≡0
          c≡0 : c ≡ 0B
          c≡0 = sym (retEq (fst equiv) c) ∙ cong (invEq (fst equiv)) (ψc≡0 ∙ sym ψ-pres0) ∙ retEq (fst equiv) 0B
          in c≡0→a≡b c≡0

  -- Generator bound infrastructure for tex Lemma 1396 (BooleIsODisc)
  -- freeBA(Fin m) where Fin is from Cubical.Data.Fin (= Σ ℕ (λ k → k <ᵗ m))
  import Cubical.Data.Fin as DF
  open import Cubical.Data.Nat.Order using (_<_; <Dec; ¬m+n<m; _≤_; ≤-refl; ≤-trans; left-≤-max; right-≤-max)
  open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ; <ᵗ→<; isProp<ᵗ)
  open IsCommRingHom

  -- Inclusion: freeBA(Fin m) → freeBA ℕ
  ι-inc : (m : ℕ) → BoolHom (freeBA (DF.Fin m)) freeBA-ℕ
  ι-inc m = inducedBAHom (DF.Fin m) freeBA-ℕ (generator ∘ fst)

  -- Projection: freeBA ℕ → freeBA(Fin m)
  π-on-gen : (m : ℕ) → ℕ → ⟨ freeBA (DF.Fin m) ⟩
  π-on-gen m k with <Dec k m
  ... | yes p = generator (k , <→<ᵗ p)
  ... | no _  = BooleanRingStr.𝟘 (snd (freeBA (DF.Fin m)))

  π-proj : (m : ℕ) → BoolHom freeBA-ℕ (freeBA (DF.Fin m))
  π-proj m = inducedBAHom ℕ (freeBA (DF.Fin m)) (π-on-gen m)

  -- maxGen: upper bound on generator indices in a term
  maxGenT : freeBATerms ℕ → ℕ
  maxGenT (Tvar n) = suc n
  maxGenT (Tconst _) = zero
  maxGenT (t +T s) = max (maxGenT t) (maxGenT s)
  maxGenT (-T t) = maxGenT t
  maxGenT (t ·T s) = max (maxGenT t) (maxGenT s)

  -- π-on-gen gives generator when index is below bound
  π-on-gen-below : (m n : ℕ) → (p : n < m) → π-on-gen m n ≡ generator (n , <→<ᵗ p)
  π-on-gen-below m n p with <Dec n m
  ... | yes q = cong (λ r → generator (n , r)) (isProp<ᵗ {n} {m} (<→<ᵗ q) (<→<ᵗ p))
  ... | no ¬q = ex-falso (¬q p)

  -- Lift a term with generators in ℕ to a term with generators in Fin m
  private
    max-≤L : (a b c : ℕ) → max a b ≤ c → a ≤ c
    max-≤L a b c p = ≤-trans (left-≤-max {a} {b}) p
    max-≤R : (a b c : ℕ) → max a b ≤ c → b ≤ c
    max-≤R a b c p = ≤-trans (right-≤-max {b} {a}) p

  liftTerm : (m : ℕ) → (t : freeBATerms ℕ) → maxGenT t ≤ m → freeBATerms (DF.Fin m)
  liftTerm m (Tvar k) p = Tvar (k , <→<ᵗ p)
  liftTerm m (Tconst b) _ = Tconst b
  liftTerm m (t +T s) p = liftTerm m t (max-≤L (maxGenT t) (maxGenT s) m p) +T liftTerm m s (max-≤R (maxGenT t) (maxGenT s) m p)
  liftTerm m (-T t) p = -T liftTerm m t p
  liftTerm m (t ·T s) p = liftTerm m t (max-≤L (maxGenT t) (maxGenT s) m p) ·T liftTerm m s (max-≤R (maxGenT t) (maxGenT s) m p)

  -- ι-inc(m)(include_Fin(liftTerm m t p)) ≡ include_ℕ(t)
  -- Only needs one ring hom (ι-inc), avoiding double-pres+ from π-proj
  opaque
    unfolding generator
    unfolding includeBATermsSurj
    ι-on-liftTerm : (m : ℕ) (t : freeBATerms ℕ) (p : maxGenT t ≤ m) →
      fst (ι-inc m) (fst (includeBATermsSurj {A = DF.Fin m}) (liftTerm m t p))
        ≡ fst includeBATermsSurj t
    ι-on-liftTerm m (Tvar k) p =
      cong (λ h → h (k , <→<ᵗ p)) (evalBAInduce (DF.Fin m) freeBA-ℕ (generator ∘ fst))
    ι-on-liftTerm m (Tconst false) _ = pres0 (snd (ι-inc m))
    ι-on-liftTerm m (Tconst true) _ = pres1 (snd (ι-inc m))
    ι-on-liftTerm m (t +T s) p =
      pres+ (snd (ι-inc m)) _ _
       ∙ cong₂ (BooleanRingStr._+_ (snd freeBA-ℕ))
               (ι-on-liftTerm m t (max-≤L (maxGenT t) (maxGenT s) m p))
               (ι-on-liftTerm m s (max-≤R (maxGenT t) (maxGenT s) m p))
    ι-on-liftTerm m (-T t) p =
      pres- (snd (ι-inc m)) _
       ∙ cong (BooleanRingStr.-_ (snd freeBA-ℕ)) (ι-on-liftTerm m t p)
    ι-on-liftTerm m (t ·T s) p =
      pres· (snd (ι-inc m)) _ _
       ∙ cong₂ (BooleanRingStr._·_ (snd freeBA-ℕ))
               (ι-on-liftTerm m t (max-≤L (maxGenT t) (maxGenT s) m p))
               (ι-on-liftTerm m s (max-≤R (maxGenT t) (maxGenT s) m p))

  -- genBound: every element of freeBA ℕ is in the image of some ι-inc m
  open import Cubical.Foundations.Equiv using (fiber)

  genBound : (x : ⟨ freeBA-ℕ ⟩) → ∥ Σ[ m ∈ ℕ ] fiber (fst (ι-inc m)) x ∥₁
  genBound x = PT.map go (snd includeBATermsSurj x) where
    go : fiber (fst includeBATermsSurj) x → Σ[ m ∈ ℕ ] fiber (fst (ι-inc m)) x
    go (t , eq) = m , fst (includeBATermsSurj {A = DF.Fin m}) (liftTerm m t ≤-refl) ,
      (ι-on-liftTerm m t ≤-refl ∙ eq) where
      m = maxGenT t

  -- Retraction: ι-inc(m₂) ∘ π-proj(m₂) ∘ ι-inc(m₁) = ι-inc(m₁) when m₁ ≤ m₂
  ιπι-retract : (m₁ m₂ : ℕ) → m₁ ≤ m₂
    → ι-inc m₂ ∘cr π-proj m₂ ∘cr ι-inc m₁ ≡ ι-inc m₁
  ιπι-retract m₁ m₂ le = sym (inducedBAHomUnique (DF.Fin m₁) freeBA-ℕ (generator ∘ fst)
    (ι-inc m₂ ∘cr π-proj m₂ ∘cr ι-inc m₁) (funExt on-gen)) where
    on-gen : (j : DF.Fin m₁) → fst (ι-inc m₂) (fst (π-proj m₂)
        (fst (ι-inc m₁) (generator j))) ≡ generator (fst j)
    on-gen (k , p) =
      fst (ι-inc m₂) (fst (π-proj m₂) (fst (ι-inc m₁) (generator (k , p))))
        ≡⟨ cong (fst (ι-inc m₂) ∘ fst (π-proj m₂))
             (funExt⁻ (evalBAInduce (DF.Fin m₁) freeBA-ℕ (generator ∘ fst)) (k , p)) ⟩
      fst (ι-inc m₂) (fst (π-proj m₂) (generator k))
        ≡⟨ cong (fst (ι-inc m₂))
             (funExt⁻ (evalBAInduce ℕ (freeBA (DF.Fin m₂)) (π-on-gen m₂)) k) ⟩
      fst (ι-inc m₂) (π-on-gen m₂ k)
        ≡⟨ cong (fst (ι-inc m₂)) (π-on-gen-below m₂ k (≤-trans (<ᵗ→< p) le)) ⟩
      fst (ι-inc m₂) (generator (k , <→<ᵗ (≤-trans (<ᵗ→< p) le)))
        ≡⟨ funExt⁻ (evalBAInduce (DF.Fin m₂) freeBA-ℕ (generator ∘ fst))
             (k , <→<ᵗ (≤-trans (<ᵗ→< p) le)) ⟩
      generator k ∎

-- TruncationStoneClosed completion (tex Corollary 1613)

module TruncationStoneClosedComplete where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open ODiscInfrastructure

  ¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬Sp-hProp B = (¬ Sp B) , isProp¬ (Sp B)

  ¬Sp-isOpen : (B : Booleω) → isOpenProp (¬Sp-hProp B)
  ¬Sp-isOpen B = transport (cong isOpenProp hProp-path)
    (booleω-equality-open B (BooleanRingStr.𝟘 (snd (fst B))) (BooleanRingStr.𝟙 (snd (fst B))))
    where
    0=1-Prop : hProp ℓ-zero
    0=1-Prop = _ , BooleanRingStr.is-set (snd (fst B)) _ _

    hProp-path : 0=1-Prop ≡ ¬Sp-hProp B
    hProp-path = TypeOfHLevel≡ 1 (ua (propBiimpl→Equiv (snd 0=1-Prop) (snd (¬Sp-hProp B))
      (TruncationStoneClosed.0=1→¬Sp B) (SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B)))

  ¬¬Sp-hProp : (B : Booleω) → hProp ℓ-zero
  ¬¬Sp-hProp B = ¬hProp (¬Sp-hProp B)

  ¬¬Sp-isClosed : (B : Booleω) → isClosedProp (¬¬Sp-hProp B)
  ¬¬Sp-isClosed B = negOpenIsClosed (¬Sp-hProp B) (¬Sp-isOpen B)

  truncSp-isClosed : (B : Booleω) → isClosedProp (∥ Sp B ∥₁ , squash₁)
  truncSp-isClosed B = transport (cong isClosedProp hProp-path) (¬¬Sp-isClosed B)
    where
    hProp-path : ¬¬Sp-hProp B ≡ (∥ Sp B ∥₁ , squash₁)
    hProp-path = TypeOfHLevel≡ 1
      (ua (LemSurjectionsFormalToCompleteness.LemSurjectionsFormalToCompleteness-derived B))

  TruncationStoneClosed : (S : Stone) → isClosedProp (∥ fst S ∥₁ , squash₁)
  TruncationStoneClosed (S , (B , p)) =
    transport (cong (λ X → isClosedProp (∥ X ∥₁ , squash₁)) p) (truncSp-isClosed B)

-- tex Corollary 1628: P is a closed prop ↔ P has Stone structure
module ClosedPropIffStone' where
  open import Axioms.StoneDuality using (hasStoneStr; Stone)
  hasStoneStr→closedProp : (P : hProp ℓ-zero) → hasStoneStr (fst P) → isClosedProp P
  hasStoneStr→closedProp P stoneP =
    transport (cong isClosedProp hpEq)
      (TruncationStoneClosedComplete.TruncationStoneClosed ((fst P) , stoneP))
    where
    hpEq : (∥ fst P ∥₁ , squash₁) ≡ P
    hpEq = TypeOfHLevel≡ 1 (ua (PT.propTruncIdempotent≃ (snd P)))

-- SDDecToElem: Stone Duality Correspondence (tex AxStoneDuality)

module SDDecToElemModule where
  open import Axioms.StoneDuality using (evaluationMap; StoneDualityAxiom; SDHomVersion)

  DecPredOnSp : (B : Booleω) → Type ℓ-zero
  DecPredOnSp B = Sp B → Bool

  elemFromDecPred : StoneDualityAxiom → (B : Booleω) → DecPredOnSp B → ⟨ fst B ⟩
  elemFromDecPred SD B D = invEq (fst (SDHomVersion SD B)) D

  decPredFromElem-roundtrip : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → evaluationMap B (elemFromDecPred SD B D) ≡ D
  decPredFromElem-roundtrip SD B D = secEq (fst (SDHomVersion SD B)) D

  decPred-elem-correspondence : (SD : StoneDualityAxiom) (B : Booleω) (D : DecPredOnSp B)
    → let d = elemFromDecPred SD B D
      in (x : Sp B) → fst x d ≡ D x
  decPred-elem-correspondence SD B D x =
    cong (λ f → f x) (decPredFromElem-roundtrip SD B D)

-- StoneEqualityClosed (tex Lemma 1636)

-- ODisc axioms (tex Section "Overtly discrete spaces", lines 906-1492)
module ODiscAxioms where
  open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
  open import Cubical.HITs.SequentialColimit.Properties
    using (converges→ColimIso; SeqColim→Prop; ElimDataShifted; elimShifted;
           elimdata-shift; ElimData; elimdata; elimShiftedβ; sequenceEquiv→ColimIso)
    renaming (elim to seqElim)
  open import Cubical.Data.Sequence using (Sequence; sequence; converges;
    SequenceIso; SequenceIso→SequenceEquiv)
  open import Cubical.Data.FinSet using (isFinSet)
  open import Cubical.Data.FinSet.Properties using (isFinSetBool; isFinSetFin; isDecProp→isFinSet; isFinSet→Dec∥∥; isFinSet→Discrete; EquivPresIsFinSet)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; invIso; isoToEquiv)
  open import Cubical.Foundations.Equiv using (idIsEquiv; idEquiv; equivFun; invEq; retEq; secEq; equivToIso; invEquiv)
  open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv; isPropIsSet)
  open import Cubical.Data.SumFin.Base using (Fin; fzero; fsuc; toℕ; fromℕ)
  open import Cubical.Data.Nat.Base using (zero; suc; _∸_)
  open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_) hiding (_<_; _-_)
  open import Cubical.Data.Bool.Base using (_or_; _≟_; Dec→Bool)
  open import Cubical.Data.Empty.Base using (⊥; ⊥*) renaming (rec to ⊥-rec; rec* to ⊥*-rec)
  open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
  open Sequence
  -- tex Definition 918: A type is overtly discrete if it is a sequential colimit of finite sets
  isODisc : Type ℓ-zero → Type (ℓ-suc ℓ-zero)
  isODisc A = ∥ Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A) ∥₁
  isProp-isODisc : (X : Type ℓ-zero) → isProp (isODisc X)
  isProp-isODisc _ = squash₁
  -- Sequential colimits of propositions are propositions
  -- Key idea: given a point at level n, converges→ColimIso shows SeqColim S ≃ obj S n
  isPropSeqColimProp : (S : Sequence ℓ-zero) → ((n : ℕ) → isProp (obj S n)) → isProp (SeqColim S)
  isPropSeqColimProp S allProp x y = inhab→isProp x x y where
    shiftS : (j : ℕ) {n : ℕ} → obj S n → obj S (j +ℕ n)
    shiftS zero a = a
    shiftS (suc j) {n} a = map S (shiftS j a)
    mapsAreEquiv : (n : ℕ) → obj S n → converges S n
    mapsAreEquiv n a j =
      snd (propBiimpl→Equiv (allProp (j +ℕ n)) (allProp (suc (j +ℕ n))) (map S) (λ _ → shiftS j a))
    inhab→isProp : SeqColim S → isProp (SeqColim S)
    inhab→isProp = SeqColim→Prop (λ _ → isPropIsProp) λ n a →
      isOfHLevelRespectEquiv 1 (isoToEquiv (converges→ColimIso n (mapsAreEquiv n a))) (allProp n)
  -- Bool is ODisc (finite type, hence ODisc by constant sequence)
  private
    BoolSeq : Sequence ℓ-zero
    obj BoolSeq _ = Bool
    map BoolSeq x = x
  ODiscBool : isODisc Bool
  ODiscBool = ∣ BoolSeq , (λ _ → isFinSetBool)
              , isoToEquiv (invIso (converges→ColimIso {seq = BoolSeq} 0 (λ _ → idIsEquiv Bool))) ∣₁
  -- tex Remark 924: ODisc types are sets (Corollary 7.7 of [SequentialColimitHoTT])
  -- Encode-decode proof: sequential colimits of sets are sets.
  private module SCSet (S' : Sequence ℓ-zero) (allSet : (n : ℕ) → isSet (obj S' n)) where
   open import Cubical.Data.Nat.Properties using (+-suc)
   open import Cubical.Foundations.GroupoidLaws using (rUnit; rCancel; assoc; symDistr)
   open import Cubical.Foundations.Path using (Square→compPath)
   CS = SeqColim S'
   sh : (k : ℕ) {n : ℕ} → obj S' n → obj S' (k +ℕ n)
   sh zero x = x
   sh (suc k) x = map S' (sh k x)
   pc : (k : ℕ) {n : ℕ} (x : obj S' n) → Path CS (incl x) (incl (sh k x))
   pc zero x = refl
   pc (suc k) x = pc k x ∙ push (sh k x)
   shTr : (j : ℕ) {m : ℕ} (z : obj S' m)
     → PathP (λ i → obj S' (+-suc j m (~ i))) (sh (suc j) z) (sh j (map S' z))
   shTr zero z = refl
   shTr (suc j) z i = map S' (shTr j z i)
   fwdPath : {k n₀ : ℕ} (x₀ : obj S' n₀) (y : obj S' (k +ℕ n₀))
     → {j : ℕ} → sh j (sh k x₀) ≡ sh j y → sh j (sh (suc k) x₀) ≡ sh j (map S' y)
   fwdPath {k} {n₀} x₀ y {j} p i =
     comp (λ t → obj S' (+-suc j (k +ℕ n₀) (~ t)))
       (λ t → λ { (i = i0) → shTr j (sh k x₀) t ; (i = i1) → shTr j y t })
       (cong (map S') p i)
   bwdPath : {k n₀ : ℕ} (x₀ : obj S' n₀) (y : obj S' (k +ℕ n₀))
     → {j : ℕ} → sh j (sh (suc k) x₀) ≡ sh j (map S' y) → sh (suc j) (sh k x₀) ≡ sh (suc j) y
   bwdPath {k} {n₀} x₀ y {j} q i =
     comp (λ t → obj S' (+-suc j (k +ℕ n₀) t))
       (λ t → λ { (i = i0) → shTr j (sh k x₀) (~ t) ; (i = i1) → shTr j y (~ t) })
       (q i)
   module EncDec {n₀ : ℕ} (x₀ : obj S' n₀) where
    pathSeq : {k : ℕ} → obj S' (k +ℕ n₀) → Sequence ℓ-zero
    obj (pathSeq {k} y) j = sh j (sh k x₀) ≡ sh j y
    map (pathSeq {k} y) = cong (map S')
    Code-incl : {k : ℕ} → obj S' (k +ℕ n₀) → Type
    Code-incl y = SeqColim (pathSeq y)
    isPropCode : {k : ℕ} (y : obj S' (k +ℕ n₀)) → isProp (Code-incl y)
    isPropCode y = isPropSeqColimProp (pathSeq y) (λ j → allSet _ _ _)
    codePush : {k : ℕ} (y : obj S' (k +ℕ n₀)) → Code-incl y ≡ Code-incl (map S' y)
    codePush {k} y = ua (propBiimpl→Equiv (isPropCode y) (isPropCode (map S' y)) fwd bwd) where
      fwd : Code-incl y → Code-incl (map S' y)
      fwd = SeqColim→Prop (λ _ → isPropCode (map S' y)) λ j p → incl {n = j} (fwdPath x₀ y p)
      bwd : Code-incl (map S' y) → Code-incl y
      bwd = SeqColim→Prop (λ _ → isPropCode y) λ j q → incl {n = suc j} (bwdPath x₀ y q)
    private
      code-datum : ElimDataShifted S' n₀ (λ _ → Type ℓ-zero)
      code-datum = elimdata-shift Code-incl (λ y → codePush y)
    Code : CS → Type
    Code = elimShifted S' n₀ (λ _ → Type ℓ-zero) code-datum
    codeβ : {k : ℕ} (y : obj S' (k +ℕ n₀)) → Code (incl y) ≡ Code-incl y
    codeβ {k} y i = elimShiftedβ S' n₀ k (λ _ → Type ℓ-zero) code-datum i y
    isPropCode' : {k : ℕ} (y : obj S' (k +ℕ n₀)) → isProp (Code (incl y))
    isPropCode' y = subst isProp (sym (codeβ y)) (isPropCode y)
    isPropCodeFull : (c : CS) → isProp (Code c)
    isPropCodeFull = elimShifted S' n₀ (λ c → isProp (Code c))
      (elimdata-shift isPropCode' (λ y → isProp→PathP (λ _ → isPropIsProp) _ _))
    code-refl : Code (incl x₀)
    code-refl = transport (sym (codeβ x₀)) (incl {n = 0} refl)
    encode : (c : CS) → incl x₀ ≡ c → Code c
    encode c p = subst Code p code-refl
    di : {k : ℕ} {y : obj S' (k +ℕ n₀)} (j : ℕ)
      → sh j (sh k x₀) ≡ sh j y → Path CS (incl x₀) (incl y)
    di {k} {y} j p = pc k x₀ ∙ pc j (sh k x₀) ∙ cong incl p ∙ sym (pc j y)
    dp : {k : ℕ} {y : obj S' (k +ℕ n₀)} (j : ℕ)
      (p : sh j (sh k x₀) ≡ sh j y) → di j p ≡ di (suc j) (cong (map S') p)
    dp {k} {y} j p = cong (pc k x₀ ∙_) inner where
      β = pc j (sh k x₀) ; γ : Path CS _ _ ; γ = cong incl p
      γ' : Path CS _ _ ; γ' = cong (λ z → incl (map S' z)) p
      δ = pc j y ; πa = push (sh j (sh k x₀)) ; πb = push (sh j y)
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
    decode-incl : {k : ℕ} (y : obj S' (k +ℕ n₀)) → Code-incl y → Path CS (incl x₀) (incl y)
    decode-incl {k} y = seqElim (pathSeq y) (λ _ → Path CS (incl x₀) (incl y))
      (elimdata (λ {j} p → di j p) (λ {j} p → dp j p))
    decode-incl' : {k : ℕ} (y : obj S' (k +ℕ n₀)) → Code (incl y) → Path CS (incl x₀) (incl y)
    decode-incl' y c = decode-incl y (transport (codeβ y) c)
    {-# TERMINATING #-}
    decode-pushP : {k : ℕ} (y : obj S' (k +ℕ n₀))
      → PathP (λ i → Code (push y i) → Path CS (incl x₀) (push y i))
              (decode-incl' y) (decode-incl' (map S' y))
    decode : (c : CS) → Code c → Path CS (incl x₀) c
    isPropPathsFrom : (b : CS) → isProp (Path CS (incl x₀) b)
    decode-pushP y = isProp→PathP (λ i → isPropΠ λ _ → isPropPathsFrom (push y i))
      (decode-incl' y) (decode-incl' (map S' y))
    decode = elimShifted S' n₀ (λ c → Code c → Path CS (incl x₀) c)
      (elimdata-shift decode-incl' decode-pushP)
    isPropPathsFrom b p q = p≡q where
      coll : (c : CS) → Path CS (incl x₀) c → Path CS (incl x₀) c
      coll c r = decode c (encode c r)
      coll-const : (c : CS) (r s : Path CS (incl x₀) c) → coll c r ≡ coll c s
      coll-const c r s = cong (decode c) (isPropCodeFull c (encode c r) (encode c s))
      rem : (r : Path CS (incl x₀) b)
        → PathP (λ i → Path CS (incl x₀) (r i)) (coll (incl x₀) refl) (coll b r)
      rem r j = coll (r j) (λ i → r (i ∧ j))
      p≡q : p ≡ q
      p≡q j i = hcomp (λ k → λ { (i = i0) → coll (incl x₀) refl k
                                ; (i = i1) → coll-const b p q j k
                                ; (j = i0) → rem p i k
                                ; (j = i1) → rem q i k }) (incl x₀)
   result : isSet CS
   result = SeqColim→Prop (λ a → isPropΠ (λ b → isPropIsProp))
     λ n x₀ → let open EncDec x₀ in isPropPathsFrom
  isSetSeqColimOfSets : (S' : Sequence ℓ-zero) → ((n : ℕ) → isSet (obj S' n))
    → isSet (SeqColim S')
  isSetSeqColimOfSets = SCSet.result
  isODiscIsSet : {A : Type ℓ-zero} → isODisc A → isSet A
  isODiscIsSet = PT.rec isPropIsSet λ (S' , finS , equiv) →
    isOfHLevelRespectEquiv 2 equiv
      (isSetSeqColimOfSets S' (λ n → isFinSet→isSet (finS n)))
    where open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
          open import Cubical.Foundations.HLevels using (isPropIsSet)
  -- Any finite set is ODisc (constant sequence)
  ODiscFinSet : {A : Type ℓ-zero} → isFinSet A → isODisc A
  ODiscFinSet {A} finA = ∣ S , (λ _ → finA) ,
    isoToEquiv (invIso (converges→ColimIso {seq = S} 0 (λ _ → idIsEquiv A))) ∣₁ where
    S : Sequence ℓ-zero
    obj S _ = A
    map S x = x
  -- isODisc transported along equivalences
  isODisc-equiv : {A B : Type ℓ-zero} → A ≃ B → isODisc A → isODisc B
  isODisc-equiv e = PT.map λ (S , finS , eA) → S , finS , compEquiv eA e
  -- Finite Σ of ODisc types is ODisc (fixed-base Σ-colim comm)
  finΣ-ODisc : {A : Type ℓ-zero} {B : A → Type ℓ-zero}
    → isFinSet A → ((a : A) → isODisc (B a)) → isODisc (Σ A B)
  finΣ-ODisc {A} {B} finA odiscB = PT.rec squash₁ go (choice (_ , finA) _ odiscB) where
    open import Cubical.Data.FinSet.FiniteChoice using (choice)
    open import Cubical.Data.FinSet.Constructors using (isFinSetΣ)
    go : ((a : A) → Σ[ S ∈ Sequence ℓ-zero ]
      ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ B a)) → isODisc (Σ A B)
    go wit = ∣ ΣSeq , finΣ , compEquiv colimEquiv (Σ-cong-equiv-snd eT) ∣₁ where
      T : A → Sequence ℓ-zero
      T a = fst (wit a)
      finT : (a : A) (n : ℕ) → isFinSet (obj (T a) n)
      finT a = fst (snd (wit a))
      eT : (a : A) → SeqColim (T a) ≃ B a
      eT a = snd (snd (wit a))
      ΣSeq : Sequence ℓ-zero
      obj ΣSeq n = Σ A (λ a → obj (T a) n)
      map ΣSeq (a , x) = a , map (T a) x
      finΣ : (n : ℕ) → isFinSet (obj ΣSeq n)
      finΣ n = isFinSetΣ (_ , finA) (λ a → _ , finT a n)
      fwd : SeqColim ΣSeq → Σ A (λ a → SeqColim (T a))
      fwd (incl (a , x)) = a , incl x
      fwd (push (a , x) i) = a , push x i
      bwd : Σ A (λ a → SeqColim (T a)) → SeqColim ΣSeq
      bwd (a , incl x) = incl (a , x)
      bwd (a , push x i) = push (a , x) i
      colimEquiv : SeqColim ΣSeq ≃ Σ A (λ a → SeqColim (T a))
      colimEquiv = isoToEquiv (iso fwd bwd
        (λ { (a , incl x) → refl ; (a , push x i) → refl })
        (λ { (incl _) → refl ; (push _ _) → refl }))
  -- freeBA(Fin k) is finite (uses SD)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom;
    inducedBAHomUnique; evalBAInduce)
  open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; idBoolHom; countℕ; BooleanRingEquiv)
  open import CountablyPresentedBooleanRings.Examples.FreeCase using (replacementFreeOnCountable)
  import Cubical.Data.Fin as DF
  open import Cubical.Foundations.Equiv using (fiber)
  open import Cubical.Data.Nat using (max) renaming (_+_ to _+ℕ_)
  open import Cubical.Data.Nat.Order using (_<_; _≤_; <Dec; ¬m+n<m; ¬m<m; ¬-<-zero; zero-≤; ≤-refl; ≤-trans; ≤-sucℕ; ≤-split; pred-≤-pred; isProp≤; left-≤-max; right-≤-max; suc-≤-suc; ≤SumLeft)
  open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ; isProp<ᵗ; <ᵗ→<)
  open import Cubical.Relation.Nullary using (Dec; yes; no)
  open import Cubical.Algebra.CommRing.Properties using (_∘cr_; invCommRingEquiv)
  open import Cubical.Foundations.Function using (_∘_; idfun)
  open import Cubical.Data.FinSet.Constructors using (isFinSet→; isFinSetΠ)
  open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
  open import Cubical.Data.FinSet.Quotients using (isFinSetQuot)
  open import Cubical.Relation.Binary.Base using (module BinaryRelation)
  open import Cubical.Relation.Nullary.DecidablePropositions using (isDecProp)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import Cubical.Algebra.CommRing.Quotient.Base using (zeroOnIdeal)
  open import Cubical.Data.Bool.Properties using (Dec≃DecBool)
  import Cubical.Data.Sum as ⊎
  open import Cubical.Functions.Surjection using (isSurjection; isEmbedding×isSurjection→isEquiv)
  open import Cubical.Functions.Embedding using (injEmbedding; isEmbedding; isEquiv→isEmbedding)
  open import Cubical.HITs.SetQuotients using (elimProp2)
  -- colimCompact: maps from finite types into sequential colimits factor through a stage
  -- Building block for tex Lemma 1160 (ODiscColimOfODisc)
  module ColimCompactHelpers (S' : Sequence ℓ-zero) where
    iterMap : (d : ℕ) {n : ℕ} → obj S' n → obj S' (d +ℕ n)
    iterMap zero x = x
    iterMap (suc d) x = map S' (iterMap d x)
    inclIter : (d : ℕ) {n : ℕ} (x : obj S' n)
      → Path (SeqColim S') (incl x) (incl (iterMap d x))
    inclIter zero x = refl
    inclIter (suc d) x = inclIter d x ∙ push (iterMap d x)
    liftTo : {n N : ℕ} → n ≤ N → obj S' n → obj S' N
    liftTo (d , p) x = subst (obj S') p (iterMap d x)
    inclLift : {n N : ℕ} (le : n ≤ N) (x : obj S' n)
      → Path (SeqColim S') (incl x) (incl (liftTo le x))
    inclLift {n} (d , p) x = inclIter d x ∙
      J (λ m q → Path (SeqColim S') (incl (iterMap d x)) (incl (subst (obj S') q (iterMap d x))))
        (cong incl (sym (transportRefl (iterMap d x)))) p
    inStage : (z : SeqColim S') → ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ obj S' n ] (incl x ≡ z) ∥₁
    inStage = SeqColim→Prop (λ _ → squash₁) λ n x → ∣ n , x , refl ∣₁
    open import Cubical.Data.Nat.Properties using (+-assoc)
    open import Cubical.Foundations.Transport using (substCommSlice)
    iterMap-comp : (d₁ d₂ : ℕ) {n : ℕ} (x : obj S' n)
      → subst (obj S') (sym (+-assoc d₂ d₁ n)) (iterMap (d₂ +ℕ d₁) x) ≡ iterMap d₂ (iterMap d₁ x)
    iterMap-comp d₁ zero x = transportRefl _
    iterMap-comp d₁ (suc d₂) {n} x =
      substCommSlice (obj S') (obj S' ∘ suc) (λ _ → map S') (sym (+-assoc d₂ d₁ n)) (iterMap (d₂ +ℕ d₁) x)
      ∙ cong (map S') (iterMap-comp d₁ d₂ x)
    liftTo-isProp : {n N : ℕ} (le₁ le₂ : n ≤ N) (x : obj S' n) → liftTo le₁ x ≡ liftTo le₂ x
    liftTo-isProp le₁ le₂ x = cong (λ le → liftTo le x) (isProp≤ le₁ le₂)
    liftTo-comp : {n m N : ℕ} (le₁ : n ≤ m) (le₂ : m ≤ N) (x : obj S' n)
      → liftTo le₂ (liftTo le₁ x) ≡ liftTo (≤-trans le₁ le₂) x
    liftTo-comp {n} (d₁ , p₁) (d₂ , p₂) x =
      J (λ _ p₂' → liftTo (d₂ , p₂') (liftTo (d₁ , p₁) x) ≡ liftTo (≤-trans (d₁ , p₁) (d₂ , p₂')) x)
        (J (λ _ p₁' → liftTo (d₂ , refl) (liftTo (d₁ , p₁') x) ≡ liftTo (≤-trans (d₁ , p₁') (d₂ , refl)) x)
          base p₁) p₂
      where
      base : liftTo (d₂ , refl) (liftTo (d₁ , refl) x) ≡ liftTo (≤-trans (d₁ , refl) (d₂ , refl)) x
      base =
        transportRefl (iterMap d₂ (subst (obj S') refl (iterMap d₁ x)))
        ∙ cong (iterMap d₂) (transportRefl (iterMap d₁ x))
        ∙ sym (iterMap-comp d₁ d₂ x)
        ∙ liftTo-isProp (d₂ +ℕ d₁ , sym (+-assoc d₂ d₁ n)) (≤-trans (d₁ , refl) (d₂ , refl)) x
  colimCompactFin : (S' : Sequence ℓ-zero) (k : ℕ) (f : Fin k → SeqColim S')
    → ∥ Σ[ N ∈ ℕ ] Σ[ g ∈ (Fin k → obj S' N) ] ((i : Fin k) → incl (g i) ≡ f i) ∥₁
  colimCompactFin S' zero f = ∣ 0 , (λ ()) , (λ ()) ∣₁
  colimCompactFin S' (suc k) f = PT.rec2 squash₁ combine
    (colimCompactFin S' k (f ∘ fsuc))
    (inStage (f fzero)) where
    open ColimCompactHelpers S'
    combine : Σ[ N₁ ∈ ℕ ] Σ[ g₁ ∈ (Fin k → obj S' N₁) ] ((i : Fin k) → incl (g₁ i) ≡ f (fsuc i))
      → Σ[ n₀ ∈ ℕ ] Σ[ x₀ ∈ obj S' n₀ ] (incl x₀ ≡ f fzero)
      → ∥ Σ[ N ∈ ℕ ] Σ[ g ∈ (Fin (suc k) → obj S' N) ] ((i : Fin (suc k)) → incl (g i) ≡ f i) ∥₁
    combine (N₁ , g₁ , ok₁) (n₀ , x₀ , ok₀) = ∣ N , g , gOk ∣₁ where
      N = max N₁ n₀
      g : Fin (suc k) → obj S' N
      r≤ : n₀ ≤ N
      r≤ = right-≤-max {n₀} {N₁}
      l≤ : N₁ ≤ N
      l≤ = left-≤-max {N₁} {n₀}
      g fzero = liftTo r≤ x₀
      g (fsuc i) = liftTo l≤ (g₁ i)
      gOk : (i : Fin (suc k)) → incl (g i) ≡ f i
      gOk fzero = sym (inclLift r≤ x₀) ∙ ok₀
      gOk (fsuc i) = sym (inclLift l≤ (g₁ i)) ∙ ok₁ i
  colimCompact : (S' : Sequence ℓ-zero) (A : Type ℓ-zero) → isFinSet A
    → (f : A → SeqColim S') → ∥ Σ[ N ∈ ℕ ] Σ[ g ∈ (A → obj S' N) ] ((a : A) → incl (g a) ≡ f a) ∥₁
  colimCompact S' A (k , e) f = PT.rec squash₁ go e where
    go : A ≃ Fin k → ∥ Σ[ N ∈ ℕ ] Σ[ g ∈ (A → obj S' N) ] ((a : A) → incl (g a) ≡ f a) ∥₁
    go eq = PT.map xfer (colimCompactFin S' k (f ∘ invEq eq)) where
      xfer : Σ[ N ∈ ℕ ] Σ[ g ∈ (Fin k → obj S' N) ] ((i : Fin k) → incl (g i) ≡ f (invEq eq i))
        → Σ[ N ∈ ℕ ] Σ[ g ∈ (A → obj S' N) ] ((a : A) → incl (g a) ≡ f a)
      xfer (N , g , ok) = N , g ∘ equivFun eq , λ a → ok (equivFun eq a) ∙ cong f (retEq eq a)
  -- Separation: if stages are sets, incl a ≡ incl b → eventual equality at some stage
  module ColimSep (S' : Sequence ℓ-zero) (setStages : (n : ℕ) → isSet (obj S' n)) where
    open ColimCompactHelpers S'
    open import Cubical.HITs.SetQuotients as SQ using (_/_; [_]; eq/)
    open import Cubical.HITs.SetQuotients.Properties using (effective)
    private
      Carrier = Σ ℕ (obj S')
      EvEq : Carrier → Carrier → Type
      EvEq (n , a) (m , b) = ∥ Σ[ N ∈ ℕ ] Σ[ le₁ ∈ n ≤ N ] Σ[ le₂ ∈ m ≤ N ] (liftTo le₁ a ≡ liftTo le₂ b) ∥₁
      isPropEvEq : BinaryRelation.isPropValued EvEq
      isPropEvEq _ _ = squash₁
      open BinaryRelation EvEq using (isEquivRel)
      isEquivRelEvEq : isEquivRel
      isEquivRelEvEq = BinaryRelation.equivRel refl' sym' trans' where
        refl' : BinaryRelation.isRefl EvEq
        refl' (n , a) = ∣ n , ≤-refl , ≤-refl , refl ∣₁
        sym' : BinaryRelation.isSym EvEq
        sym' _ _ = PT.map λ (N , le₁ , le₂ , p) → N , le₂ , le₁ , sym p
        trans' : BinaryRelation.isTrans EvEq
        trans' (n , a) (m , b) (k , c) = PT.rec2 squash₁ λ
          (N₁ , le₁ , le₂ , p₁) (N₂ , le₃ , le₄ , p₂) →
          let l≤ = left-≤-max {N₁} {N₂}
              r≤ = right-≤-max {N₂} {N₁}
          in ∣ max N₁ N₂ , ≤-trans le₁ l≤ , ≤-trans le₄ r≤ ,
               sym (liftTo-comp le₁ l≤ a) ∙ cong (liftTo l≤) p₁ ∙ liftTo-comp le₂ l≤ b
               ∙ liftTo-isProp _ _ b
               ∙ sym (liftTo-comp le₃ r≤ b) ∙ cong (liftTo r≤) p₂ ∙ liftTo-comp le₄ r≤ c ∣₁
      fwd : SeqColim S' → Carrier SQ./ EvEq
      fwd (incl {n} x) = SQ.[ n , x ]
      fwd (push {n} x i) = eq/ (n , x) (suc n , map S' x) ∣ suc n , ≤-sucℕ , ≤-refl , refl ∣₁ i
    colimSeparation : {n m : ℕ} (a : obj S' n) (b : obj S' m) → incl a ≡ incl b
      → ∥ Σ[ N ∈ ℕ ] Σ[ le₁ ∈ n ≤ N ] Σ[ le₂ ∈ m ≤ N ] (liftTo le₁ a ≡ liftTo le₂ b) ∥₁
    colimSeparation a b p = effective isPropEvEq isEquivRelEvEq _ _ (cong fwd p)
  -- isSetSeqColim is provided by isSetSeqColimOfSets above (line 1140, via SCSet.result)
  -- Subsequence equivalence: monotone unbounded reindexing preserves sequential colimit
  subSeqEquiv : (S' : Sequence ℓ-zero) (ℓ' : ℕ → ℕ)
    → (setStages : (n : ℕ) → isSet (obj S' n))
    → (mono : (k : ℕ) → ℓ' k ≤ ℓ' (suc k))
    → (grow : (k : ℕ) → k ≤ ℓ' k)
    → let open ColimCompactHelpers S'
          SubS : Sequence ℓ-zero
          SubS = record { obj = λ k → obj S' (ℓ' k)
                        ; map = λ {k} → liftTo (mono k) }
      in SeqColim SubS ≃ SeqColim S'
  subSeqEquiv S' ℓ' setStages mono grow = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)
    where
    open ColimCompactHelpers S' using (liftTo; inclLift; liftTo-isProp; liftTo-comp)
    SubS : Sequence ℓ-zero
    SubS = record { obj = λ k → obj S' (ℓ' k) ; map = λ {k} → liftTo (mono k) }
    module CHS = ColimCompactHelpers SubS
    -- liftTo in SubS corresponds to liftTo in S' (up to liftTo-isProp)
    subLift-is-lift : {k m : ℕ} (le : k ≤ m) (x : obj S' (ℓ' k))
      → Σ[ le' ∈ ℓ' k ≤ ℓ' m ] (CHS.liftTo le x ≡ liftTo le' x)
    -- Iterating SubS transitions d times = liftTo in S' (with some composed le)
    iterSub-eq : (d : ℕ) {k : ℕ} (x : obj S' (ℓ' k))
      → Σ[ le' ∈ ℓ' k ≤ ℓ' (d +ℕ k) ] (CHS.iterMap d x ≡ liftTo le' x)
    iterSub-eq zero x = ≤-refl , sym (transportRefl x)
    iterSub-eq (suc d) {k} x =
      let (le-prev , eq-prev) = iterSub-eq d x
      in ≤-trans le-prev (mono (d +ℕ k)) ,
         (cong (liftTo (mono (d +ℕ k))) eq-prev
          ∙ liftTo-comp le-prev (mono (d +ℕ k)) x
          ∙ liftTo-isProp _ _ x)
    subLift-is-lift {k} {m} (d , p) x =
      J (λ m' p' → Σ[ le' ∈ ℓ' k ≤ ℓ' m' ] (CHS.liftTo (d , p') x ≡ liftTo le' x))
        (let (le' , eq) = iterSub-eq d x
         in le' , transportRefl _ ∙ eq)
        p
    fwd : SeqColim SubS → SeqColim S'
    fwd (incl {k} x) = incl x
    fwd (push {k} x i) = inclLift (mono k) x i
    bwd : SeqColim S' → SeqColim SubS
    bwd (incl {n} y) = incl (liftTo (grow n) y)
    bwd (push {n} y i) = path i where
      mapAsLift : {n : ℕ} (y : obj S' n) → map S' y ≡ liftTo (1 , refl) y
      mapAsLift y = sym (transportRefl (map S' y))
      step1 : liftTo (mono n) (liftTo (grow n) y) ≡ liftTo (grow (suc n)) (map S' y)
      step1 =
        liftTo-comp (grow n) (mono n) y
        ∙ liftTo-isProp _ _ y
        ∙ sym (liftTo-comp (1 , refl) (grow (suc n)) y)
        ∙ cong (liftTo (grow (suc n))) (sym (mapAsLift y))
      path : Path (SeqColim SubS) (incl (liftTo (grow n) y))
                                   (incl (liftTo (grow (suc n)) (map S' y)))
      path = push (liftTo (grow n) y) ∙ cong (incl {n = suc n}) step1
    fwd-bwd : (z : SeqColim S') → fwd (bwd z) ≡ z
    fwd-bwd = SeqColim→Prop (λ _ → isSetSeqColimOfSets S' setStages _ _) go where
      go : (n : ℕ) (x : obj S' n) → fwd (bwd (incl x)) ≡ incl x
      go n x = sym (inclLift (grow n) x)
    bwd-fwd : (z : SeqColim SubS) → bwd (fwd z) ≡ z
    bwd-fwd = SeqColim→Prop (λ _ → isSetSeqColimOfSets SubS (λ n → setStages (ℓ' n)) _ _) go where
      go : (k : ℕ) (x : obj SubS k) → bwd (fwd (incl x)) ≡ incl x
      -- bwd (fwd (incl{k} x)) = bwd (incl{ℓ'k} x) = incl{ℓ'k}_SubS (liftTo_S' (grow (ℓ'k)) x)
      -- Need: incl{ℓ'k}_SubS (liftTo_S' (grow (ℓ'k)) x) ≡ incl{k}_SubS x
      -- Via: CHS.inclLift (grow k) x : incl{k} x ≡ incl{ℓ'k} (CHS.liftTo (grow k) x)
      -- And: liftTo (grow (ℓ'k)) x ≡ CHS.liftTo (grow k) x (via subLift-is-lift)
      go k x =
        let (le' , eq) = subLift-is-lift (grow k) x
        in cong (incl {n = ℓ' k}) (liftTo-isProp (grow (ℓ' k)) le' x ∙ sym eq)
           ∙ sym (CHS.inclLift (grow k) x)
  -- tex Lemma 933: A map between colimits of finite sets decomposes as colimit of maps
  open import Cubical.Data.FinSet.FiniteChoice as FC using ()
  -- Output record for lemDecompColimMorphisms
  record DecompData (B C : Sequence ℓ-zero) (f : SeqColim B → SeqColim C) : Type ℓ-zero where
    field
      lvl : ℕ → ℕ
      fMap : (k : ℕ) → obj B k → obj C (lvl k)
      fOk : (k : ℕ) (x : obj B k) → incl (fMap k x) ≡ f (incl x)
      lvlMono : (k : ℕ) → lvl k ≤ lvl (suc k)
      lvlGrow : (k : ℕ) → k ≤ lvl k
      fCompat : (k : ℕ) (x : obj B k) →
        ColimCompactHelpers.liftTo C (lvlMono k) (fMap k x) ≡ fMap (suc k) (map B x)
  lemDecompColimMorphisms : (B C : Sequence ℓ-zero)
    → ((k : ℕ) → isFinSet (obj B k))
    → ((k : ℕ) → isSet (obj C k))
    → (f : SeqColim B → SeqColim C)
    → ∥ DecompData B C f ∥₁
  lemDecompColimMorphisms B C finB setC f =
    PT.rec squash₁ step0 (colimCompact C _ (finB 0) (f ∘ incl))
    where
    open ColimCompactHelpers C
    open ColimSep C setC using (colimSeparation)
    -- maxFin: compute max of a function over Fin c
    maxFin : (c : ℕ) → (Fin c → ℕ) → ℕ
    maxFin zero _ = 0
    maxFin (suc c) h = max (h fzero) (maxFin c (h ∘ fsuc))
    maxFin-le : (c : ℕ) (h : Fin c → ℕ) (i : Fin c) → h i ≤ maxFin c h
    maxFin-le (suc c) h fzero = left-≤-max {h fzero}
    maxFin-le (suc c) h (fsuc i) =
      ≤-trans (maxFin-le c (h ∘ fsuc) i) (right-≤-max {maxFin c (h ∘ fsuc)} {h fzero})
    -- Factor f ∘ incl at stage 0, then use dep. choice for remaining stages
    step0 : Σ[ N₀ ∈ ℕ ] Σ[ g₀ ∈ (obj B 0 → obj C N₀) ]
            ((x : obj B 0) → incl (g₀ x) ≡ f (incl x))
          → ∥ DecompData B C f ∥₁
    step0 init₀ = PT.rec squash₁ (λ x → ∣ extract x ∣₁)
      (dependentChoice-axiom PD pdProj pdSurj pd₀) where
      PD : ℕ → Type ℓ-zero
      pdData : {k : ℕ} → PD k → Σ[ N ∈ ℕ ] Σ[ g ∈ (obj B k → obj C N) ]
               ((x : obj B k) → incl (g x) ≡ f (incl x))
      PD zero = ℕ
      PD (suc k) = Σ[ prev ∈ PD k ]
        let Np = fst (pdData prev) ; gp = fst (snd (pdData prev)) in
        Σ[ N ∈ ℕ ] Σ[ le ∈ Np ≤ N ] Σ[ _ ∈ suc k ≤ N ]
        Σ[ g ∈ (obj B (suc k) → obj C N) ]
        ((x : obj B (suc k)) → incl (g x) ≡ f (incl x)) ×
        ((x : obj B k) → liftTo le (gp x) ≡ g (map B x))
      pdData {zero} _ = init₀
      pdData {suc _} (_ , N , _ , _ , g , ok , _) = N , g , ok
      pdProj : (k : ℕ) → PD (suc k) → PD k
      pdProj _ (prev , _) = prev
      pdSurj : (k : ℕ) (y : PD k) → ∥ Σ[ x ∈ PD (suc k) ] pdProj k x ≡ y ∥₁
      pdSurj k y = PT.rec squash₁ combine
        (colimCompact C _ (finB (suc k)) (f ∘ incl)) where
        Ny = fst (pdData y) ; gy = fst (snd (pdData y)) ; oky = snd (snd (pdData y))
        combine : Σ[ N' ∈ ℕ ] Σ[ g' ∈ (obj B (suc k) → obj C N') ]
                  ((x : obj B (suc k)) → incl (g' x) ≡ f (incl x))
                → ∥ Σ[ x ∈ PD (suc k) ] pdProj k x ≡ y ∥₁
        combine (N' , g' , ok') = PT.rec squash₁ step2
          (FC.choice (_ , finB k) _ sepWit) where
          agree : (x : obj B k) → incl (gy x) ≡ incl (g' (map B x))
          agree x = oky x ∙ cong f (push x) ∙ sym (ok' (map B x))
          sepWit : (x : obj B k) →
            ∥ Σ[ M ∈ ℕ ] Σ[ le₁ ∈ Ny ≤ M ] Σ[ le₂ ∈ N' ≤ M ]
              (liftTo le₁ (gy x) ≡ liftTo le₂ (g' (map B x))) ∥₁
          sepWit x = colimSeparation (gy x) (g' (map B x)) (agree x)
          step2 : ((x : obj B k) → Σ[ M ∈ ℕ ] Σ[ le₁ ∈ Ny ≤ M ] Σ[ le₂ ∈ N' ≤ M ]
                   (liftTo le₁ (gy x) ≡ liftTo le₂ (g' (map B x))))
                → ∥ Σ[ x ∈ PD (suc k) ] pdProj k x ≡ y ∥₁
          step2 wit = PT.rec squash₁ (λ eq → ∣ mkPD eq , refl ∣₁) (snd (finB k)) where
            M : obj B k → ℕ
            M x = fst (wit x)
            mkPD : obj B k ≃ Fin (fst (finB k)) → PD (suc k)
            mkPD eq = (y , N , le , leSucK , gN , okN , compat) where
              c = fst (finB k)
              mFin : Fin c → ℕ
              mFin i = M (invEq eq i)
              Nmax = max (suc k) (max Ny (max N' (maxFin c mFin)))
              N = Nmax
              leSucK : suc k ≤ N
              leSucK = left-≤-max {suc k} {max Ny (max N' (maxFin c mFin))}
              le : Ny ≤ N
              le = ≤-trans (left-≤-max {Ny} {max N' (maxFin c mFin)})
                           (right-≤-max {max Ny (max N' (maxFin c mFin))} {suc k})
              leN' : N' ≤ N
              leN' = ≤-trans (left-≤-max {N'} {maxFin c mFin})
                     (≤-trans (right-≤-max {max N' (maxFin c mFin)} {Ny})
                              (right-≤-max {max Ny (max N' (maxFin c mFin))} {suc k}))
              leM : (x : obj B k) → M x ≤ N
              leM x = ≤-trans
                (subst (λ z → M z ≤ maxFin c mFin) (retEq eq x)
                  (maxFin-le c mFin (equivFun eq x)))
                (≤-trans (right-≤-max {maxFin c mFin} {N'})
                  (≤-trans (right-≤-max {max N' (maxFin c mFin)} {Ny})
                           (right-≤-max {max Ny (max N' (maxFin c mFin))} {suc k})))
              gN : obj B (suc k) → obj C N
              gN x = liftTo leN' (g' x)
              okN : (x : obj B (suc k)) → incl (gN x) ≡ f (incl x)
              okN x = sym (inclLift leN' (g' x)) ∙ ok' x
              compat : (x : obj B k) → liftTo le (gy x) ≡ gN (map B x)
              compat x =
                let (Mx , le₁ , le₂ , p) = wit x
                    mle : Mx ≤ N
                    mle = leM x
                in
                liftTo le (gy x)
                  ≡⟨ liftTo-isProp le (≤-trans le₁ mle) (gy x) ⟩
                liftTo (≤-trans le₁ mle) (gy x)
                  ≡⟨ sym (liftTo-comp le₁ mle (gy x)) ⟩
                liftTo mle (liftTo le₁ (gy x))
                  ≡⟨ cong (liftTo mle) p ⟩
                liftTo mle (liftTo le₂ (g' (map B x)))
                  ≡⟨ liftTo-comp le₂ mle (g' (map B x)) ⟩
                liftTo (≤-trans le₂ mle) (g' (map B x))
                  ≡⟨ liftTo-isProp (≤-trans le₂ mle) leN' (g' (map B x)) ⟩
                liftTo leN' (g' (map B x)) ∎
      pd₀ : PD 0
      pd₀ = 0
      extract : Σ[ s ∈ SeqLimit PD pdProj ] seqLim-proj₀ PD pdProj s ≡ pd₀
              → DecompData B C f
      extract ((p , compat) , _) = record
        { lvl = lvl ; fMap = fMap ; fOk = fOk
        ; lvlMono = lvlMono ; lvlGrow = lvlGrow ; fCompat = fCompat'
        } where
        lvl : ℕ → ℕ
        lvl k = fst (pdData (p k))
        fMap : (k : ℕ) → obj B k → obj C (lvl k)
        fMap k = fst (snd (pdData (p k)))
        fOk : (k : ℕ) (x : obj B k) → incl (fMap k x) ≡ f (incl x)
        fOk k = snd (snd (pdData (p k)))
        lvlGrow : (k : ℕ) → k ≤ lvl k
        lvlGrow zero = zero-≤
        lvlGrow (suc k) = fst (snd (snd (snd (p (suc k)))))
        prev : (k : ℕ) → PD k
        prev k = fst (p (suc k))
        rawLe : (k : ℕ) → fst (pdData (prev k)) ≤ lvl (suc k)
        rawLe k = fst (snd (snd (p (suc k))))
        rawCompat : (k : ℕ) (x : obj B k) →
          liftTo (rawLe k) (fst (snd (pdData (prev k))) x) ≡ fMap (suc k) (map B x)
        rawCompat k = snd (snd (snd (snd (snd (snd (p (suc k)))))))
        -- lvlMono and fCompat' by transport along compat k
        monoAndCompat : (k : ℕ) → Σ[ le ∈ lvl k ≤ lvl (suc k) ]
          ((x : obj B k) → liftTo le (fMap k x) ≡ fMap (suc k) (map B x))
        monoAndCompat k = subst (λ pk → Σ[ le ∈ fst (pdData pk) ≤ lvl (suc k) ]
            ((x : obj B k) → liftTo le (fst (snd (pdData pk)) x) ≡ fMap (suc k) (map B x)))
          (compat k) (rawLe k , rawCompat k)
        lvlMono : (k : ℕ) → lvl k ≤ lvl (suc k)
        lvlMono k = fst (monoAndCompat k)
        fCompat' : (k : ℕ) (x : obj B k) →
          liftTo (lvlMono k) (fMap k x) ≡ fMap (suc k) (map B x)
        fCompat' k x = snd (monoAndCompat k) x
  -- tex Lemma 1160: sequential colimits of ODisc types are ODisc
  -- Uses lemDecompColimMorphisms + dependent choice to build quarter-plane diagonal
  ODiscColimOfODisc : (S₀ : Sequence ℓ-zero)
    → ((n : ℕ) → isODisc (obj S₀ n)) → isODisc (SeqColim S₀)
  ODiscColimOfODisc S₀ odiscN =
    PT.rec squash₁ go (countableChoice₁ _ odiscN) where
    go : ((n : ℕ) → Σ[ T ∈ Sequence ℓ-zero ]
           ((k : ℕ) → isFinSet (obj T k)) × (SeqColim T ≃ obj S₀ n))
       → isODisc (SeqColim S₀)
    go w = PT.rec squash₁ buildDiag (dependentChoice-axiom QP qpProj qpSurj qp₀) where
      T : ℕ → Sequence ℓ-zero
      T n = fst (w n)
      finT : (n k : ℕ) → isFinSet (obj (T n) k)
      finT n = fst (snd (w n))
      eT : (n : ℕ) → SeqColim (T n) ≃ obj S₀ n
      eT n = snd (snd (w n))
      ψ : (n : ℕ) → SeqColim (T n) → SeqColim (T (suc n))
      ψ n c = invEq (eT (suc n)) (map S₀ (equivFun (eT n) c))
      setT : (n k : ℕ) → isSet (obj (T n) k)
      setT n k = isFinSet→isSet (finT n k)
        where open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
      -- Quarter-plane data at step n: decomposition of ψ(n-1) into level-wise maps
      QP : ℕ → Type ℓ-zero
      qpSeq : {n : ℕ} → QP n → Sequence ℓ-zero
      qpFin : {n : ℕ} (q : QP n) → (k : ℕ) → isFinSet (obj (qpSeq q) k)
      qpEquiv : {n : ℕ} (q : QP n) → SeqColim (qpSeq q) ≃ obj S₀ n
      transition : {n : ℕ} (q : QP n) → SeqColim (qpSeq q) → SeqColim (T (suc n))
      QP zero = ℕ
      QP (suc n) = Σ[ prev ∈ QP n ] DecompData (qpSeq prev) (T (suc n)) (transition prev)
      qpSeq {zero} _ = T 0
      qpSeq {suc n} (_ , dd) = record
        { obj = λ k → obj (T (suc n)) (DecompData.lvl dd k)
        ; map = λ {k} → ColimCompactHelpers.liftTo (T (suc n)) (DecompData.lvlMono dd k)
        }
      qpFin {zero} _ = finT 0
      qpFin {suc n} (_ , dd) k = finT (suc n) (DecompData.lvl dd k)
      qpEquiv {zero} _ = eT 0
      qpEquiv {suc n} (_ , dd) = compEquiv
        (subSeqEquiv (T (suc n)) (DecompData.lvl dd) (setT (suc n))
          (DecompData.lvlMono dd) (DecompData.lvlGrow dd))
        (eT (suc n))
      transition q = invEq (eT _) ∘ map S₀ ∘ equivFun (qpEquiv q)
      qpProj : (n : ℕ) → QP (suc n) → QP n
      qpProj _ (prev , _) = prev
      qpSurj : (n : ℕ) (y : QP n) → ∥ Σ[ x ∈ QP (suc n) ] qpProj n x ≡ y ∥₁
      qpSurj n y = PT.map (λ dd → (y , dd) , refl)
        (lemDecompColimMorphisms (qpSeq y) (T (suc n))
          (qpFin y) (setT (suc n)) (transition y))
      qp₀ : QP 0
      qp₀ = 0
      buildDiag : Σ[ s ∈ SeqLimit QP qpProj ] seqLim-proj₀ QP qpProj s ≡ qp₀
                → isODisc (SeqColim S₀)
      buildDiag ((q , qcompat) , _) = ∣ D , finD , diagEquiv ∣₁ where
        dd : (n : ℕ) → DecompData (qpSeq (fst (q (suc n)))) (T (suc n)) (transition (fst (q (suc n))))
        dd n = snd (q (suc n))
        -- Vertical map: row n, col k → row (suc n), col k
        vMap : (n k : ℕ) → obj (qpSeq (q n)) k → obj (qpSeq (q (suc n))) k
        vMap n k = DecompData.fMap (dd n) k ∘ subst (λ qn → obj (qpSeq qn) k) (sym (qcompat n))
        -- Diagonal sequence
        D : Sequence ℓ-zero
        D = record
          { obj = λ n → obj (qpSeq (q n)) n
          ; map = λ {n} x → vMap n (suc n) (map (qpSeq (q n)) x)
          }
        finD : (n : ℕ) → isFinSet (obj D n)
        finD n = qpFin (q n) n
        -- Key helper: qpEquiv is compatible with row transitions via fOk
        module _ (n : ℕ) (x : obj D n) where
          private
            qn = q n ; qsn = q (suc n)
            qn' = fst qsn
            ddn = dd n
            y = map (qpSeq qn) x
            y' = subst (λ qn₀ → obj (qpSeq qn₀) (suc n)) (sym (qcompat n)) y
          fwdD-coh : equivFun (qpEquiv qsn) (incl {n = suc n} (map D x))
                   ≡ map S₀ (equivFun (qpEquiv qn) (incl x))
          fwdD-coh =
            -- Step 1: subSeqEquiv fwd on incl = incl, so qpEquiv qsn on incl = eT on incl
            cong (equivFun (eT (suc n))) refl
            -- Step 2: fOk gives incl (fMap y') ≡ transition qn' (incl y') in SeqColim T(suc n)
            ∙ cong (equivFun (eT (suc n))) (DecompData.fOk ddn (suc n) y')
            -- Step 3: equivFun eT ∘ transition = map S₀ ∘ equivFun qpEquiv (by secEq)
            ∙ secEq (eT (suc n)) _
            -- Step 4: relate qpEquiv qn' (incl y') to qpEquiv qn (incl y) via qcompat
            ∙ cong (map S₀) step4
            -- Step 5: equivFun qpEquiv qn (incl y) ≡ equivFun qpEquiv qn (incl x) via push
            ∙ cong (map S₀) (sym (cong (equivFun (qpEquiv qn)) (push x)))
            where
            P = λ r → obj (qpSeq r) (suc n)
            yPathP : PathP (λ i → P (qcompat n i)) y' y
            yPathP = symP (transport-filler (cong P (sym (qcompat n))) y)
            step4 : equivFun (qpEquiv qn') (incl y') ≡ equivFun (qpEquiv qn) (incl y)
            step4 i = equivFun (qpEquiv (qcompat n i)) (incl (yPathP i))
        -- Forward: diagonal → SeqColim S₀
        fwdD : SeqColim D → SeqColim S₀
        fwdD (incl {n} x) = incl (equivFun (qpEquiv (q n)) (incl x))
        fwdD (push {n} x i) = (push (equivFun (qpEquiv (q n)) (incl x))
                               ∙ cong incl (sym (fwdD-coh n x))) i
        -- Column iteration: push from row n to row (d+n) at column k
        colIter : (d : ℕ) {n : ℕ} (k : ℕ)
          → obj (qpSeq (q n)) k → obj (qpSeq (q (d +ℕ n))) k
        colIter zero k x = x
        colIter (suc d) {n} k x = vMap (d +ℕ n) k (colIter d k x)
        open ColimCompactHelpers using (liftTo; inclLift; inStage)
        -- hv-swap₁: horizontal and vertical maps commute (one step)
        -- map (qpSeq (q (suc n))) (vMap n k v) ≡ vMap n (suc k) (map (qpSeq (q n)) v)
        hv-swap₁ : (n k : ℕ) (v : obj (qpSeq (q n)) k)
          → map (qpSeq (q (suc n))) (vMap n k v) ≡ vMap n (suc k) (map (qpSeq (q n)) v)
        hv-swap₁ n k v =
          DecompData.fCompat (dd n) k v'
          ∙ cong (DecompData.fMap (dd n) (suc k)) mapConn
          where
          v' = subst (λ qn → obj (qpSeq qn) k) (sym (qcompat n)) v
          P' = λ r → obj (qpSeq r) (suc k)
          -- mapConn: map (qpSeq prev) v' ≡ subst P' (sym qcompat) (map (qpSeq (q n)) v)
          -- follows from naturality of map w.r.t. transport along qcompat
          vPathP : PathP (λ i → obj (qpSeq (qcompat n i)) k) v' v
          vPathP = symP (transport-filler (cong (λ r → obj (qpSeq r) k) (sym (qcompat n))) v)
          mapPathP : PathP (λ i → P' (qcompat n i))
                       (map (qpSeq (fst (q (suc n)))) v')
                       (map (qpSeq (q n)) v)
          mapPathP i = map (qpSeq (qcompat n i)) (vPathP i)
          mapConn : map (qpSeq (fst (q (suc n)))) v'
                  ≡ subst P' (sym (qcompat n)) (map (qpSeq (q n)) v)
          mapConn = fromPathP≡ mapPathP
            where
            fromPathP≡ : PathP (λ i → P' (qcompat n i))
                           (map (qpSeq (fst (q (suc n)))) v')
                           (map (qpSeq (q n)) v)
              → map (qpSeq (fst (q (suc n)))) v'
                ≡ subst P' (sym (qcompat n)) (map (qpSeq (q n)) v)
            fromPathP≡ pp = sym (fromPathP (symP pp))
        -- multi-vmap-commute: d vertical steps commute with 1 horizontal step
        -- map (qpSeq (q (d+N))) (colIter d k w) ≡ colIter d (suc k) (map (qpSeq (q N)) w)
        multi-vmap-commute : (d : ℕ) {N : ℕ} (k : ℕ) (w : obj (qpSeq (q N)) k)
          → map (qpSeq (q (d +ℕ N))) {k} (colIter d k w)
          ≡ colIter d {N} (suc k) (map (qpSeq (q N)) w)
        multi-vmap-commute zero k w = refl
        multi-vmap-commute (suc d) {N} k w =
          hv-swap₁ (d +ℕ N) k (colIter d k w)
          ∙ cong (vMap (d +ℕ N) (suc k)) (multi-vmap-commute d k w)
        -- diag-eq-hv: diagonal iteration = horizontal then vertical
        diag-eq-hv : (d : ℕ) {N : ℕ} (z : obj D N)
          → ColimCompactHelpers.iterMap D d z
          ≡ colIter d (d +ℕ N) (ColimCompactHelpers.iterMap (qpSeq (q N)) d z)
        diag-eq-hv zero z = refl
        diag-eq-hv (suc d) {N} z =
          cong (vMap (d +ℕ N) (suc (d +ℕ N)))
               (cong (map (qpSeq (q (d +ℕ N)))) (diag-eq-hv d z)
                ∙ multi-vmap-commute d (d +ℕ N) (ColimCompactHelpers.iterMap (qpSeq (q N)) d z))
        -- Vertical coherence: vMap is compatible with qpEquiv
        vert-coh : (n k : ℕ) (x : obj (qpSeq (q n)) k)
          → equivFun (qpEquiv (q (suc n))) (incl {n = k} (vMap n k x))
          ≡ map S₀ (equivFun (qpEquiv (q n)) (incl {n = k} x))
        vert-coh n k x =
            cong (equivFun (eT (suc n))) refl
            ∙ cong (equivFun (eT (suc n))) (DecompData.fOk ddn k x')
            ∙ secEq (eT (suc n)) _
            ∙ cong (map S₀) step4
          where
          qn = q n ; qsn = q (suc n)
          qn' = fst qsn
          ddn = dd n
          x' = subst (λ qn₀ → obj (qpSeq qn₀) k) (sym (qcompat n)) x
          P = λ r → obj (qpSeq r) k
          xPathP : PathP (λ i → P (qcompat n i)) x' x
          xPathP = symP (transport-filler (cong P (sym (qcompat n))) x)
          step4 : equivFun (qpEquiv qn') (incl x') ≡ equivFun (qpEquiv qn) (incl x)
          step4 i = equivFun (qpEquiv (qcompat n i)) (incl (xPathP i))
        -- colIter coherence: iterating vertical maps, fwdD composes through
        colIter-coh : (d : ℕ) {n : ℕ} (k : ℕ) (x : obj (qpSeq (q n)) k)
          → Path (SeqColim S₀)
              (incl (equivFun (qpEquiv (q (d +ℕ n))) (incl (colIter d k x))))
              (incl (equivFun (qpEquiv (q n)) (incl x)))
        colIter-coh zero k x = refl
        colIter-coh (suc d) {n} k x =
            cong incl (vert-coh (d +ℕ n) k (colIter d k x))
            ∙ sym (push (equivFun (qpEquiv (q (d +ℕ n))) (incl (colIter d k x))))
            ∙ colIter-coh d k x
        -- Embed (row n, col k) → diagonal at stage (d+n)
        toDiag : (n : ℕ) {d : ℕ} (k : ℕ) (kle : k ≤ d +ℕ n)
          → obj (qpSeq (q n)) k → obj D (d +ℕ n)
        toDiag n {d} k kle z = colIter d (d +ℕ n) (liftTo (qpSeq (q n)) kle z)
        -- fwdD on toDiag gives incl of the original element
        fwdD-toDiag : (n : ℕ) {d : ℕ} (k : ℕ) (kle : k ≤ d +ℕ n)
          (z : obj (qpSeq (q n)) k)
          → Path (SeqColim S₀)
              (incl (equivFun (qpEquiv (q (d +ℕ n))) (incl (toDiag n k kle z))))
              (incl (equivFun (qpEquiv (q n)) (incl z)))
        fwdD-toDiag n {d} k kle z = step1 ∙ step2 where
          zLift = liftTo (qpSeq (q n)) kle z
          fwdN : SeqColim (qpSeq (q n)) → SeqColim S₀
          fwdN s = incl {X = S₀} {n = n} (equivFun (qpEquiv (q n)) s)
          step1 = colIter-coh d (d +ℕ n) zLift
          step2 : fwdN (incl {X = qpSeq (q n)} {n = d +ℕ n} zLift)
                ≡ fwdN (incl {X = qpSeq (q n)} {n = k} z)
          step2 = cong fwdN (sym (inclLift (qpSeq (q n)) kle z))
        diagEquiv : SeqColim D ≃ SeqColim S₀
        diagEquiv = fwdD , isEmbedding×isSurjection→isEquiv (fwdD-emb , fwdD-surj) where
          isSetS₀ : isSet (SeqColim S₀)
          isSetS₀ = isSetSeqColimOfSets S₀ λ n →
            isODiscIsSet (odiscN n)
          isSetD : isSet (SeqColim D)
          isSetD = isSetSeqColimOfSets D λ n →
            isFinSet→isSet (finD n) where
            open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
          -- Surjection: every element of SeqColim S₀ has a preimage
          fwdD-surj : isSurjection fwdD
          fwdD-surj = SeqColim→Prop (λ _ → squash₁) fwdD-surj-incl where
            fwdD-surj-incl : (n : ℕ) (y : obj S₀ n)
              → ∥ fiber fwdD (incl y) ∥₁
            fwdD-surj-incl n y = PT.rec squash₁ step
              (inStage (qpSeq (q n)) (invEq (qpEquiv (q n)) y)) where
              step : Σ[ k ∈ ℕ ] Σ[ z ∈ obj (qpSeq (q n)) k ] (incl z ≡ invEq (qpEquiv (q n)) y)
                → ∥ fiber fwdD (incl y) ∥₁
              step (k , z , p) = ∣ incl {X = D} {n = k +ℕ n} (toDiag n k ≤SumLeft z) , path ∣₁ where
                path : fwdD (incl (toDiag n k ≤SumLeft z)) ≡ incl y
                path =
                  fwdD-toDiag n k ≤SumLeft z
                  ∙ cong incl (cong (equivFun (qpEquiv (q n))) p
                              ∙ secEq (qpEquiv (q n)) y)
          -- fwdD-nat: fwdD commutes with diagonal iteration and S₀ transition
          open ColimCompactHelpers D renaming (iterMap to iterMapD; liftTo to liftToD; inclLift to inclLiftD)
          open ColimCompactHelpers S₀ renaming (iterMap to iterMapS₀; liftTo to liftToS₀)
          open ColimSep S₀ (λ n → isODiscIsSet (odiscN n)) using (colimSeparation)
          fwdD-nat : (d : ℕ) {n : ℕ} (x : obj D n)
            → equivFun (qpEquiv (q (d +ℕ n))) (incl (iterMapD d x))
            ≡ iterMapS₀ d (equivFun (qpEquiv (q n)) (incl x))
          fwdD-nat zero x = refl
          fwdD-nat (suc d) {n} x =
            fwdD-coh (d +ℕ n) (iterMapD d x)
            ∙ cong (map S₀) (fwdD-nat d x)
          -- Embedding: fwdD is injective
          -- Key: from row-colimit equality, use colimSeparation + diag-eq-hv
          -- to derive diagonal-colimit equality
          fwdD-emb : isEmbedding fwdD
          fwdD-emb = injEmbedding isSetS₀ fwdD-inj where
            open ColimCompactHelpers D using () renaming (inclIter to inclIterD)
            liftToS₀-via-nat : (d : ℕ) {n : ℕ} (x : obj D n)
              → liftToS₀ (d , refl) (equivFun (qpEquiv (q n)) (incl {X = qpSeq (q n)} x))
              ≡ equivFun (qpEquiv (q (d +ℕ n))) (incl {X = qpSeq (q (d +ℕ n))} (liftToD (d , refl) x))
            liftToS₀-via-nat d {n} x =
              transportRefl _
              ∙ sym (fwdD-nat d x)
              ∙ cong (equivFun (qpEquiv (q (d +ℕ n))) ∘ incl) (sym (transportRefl (iterMapD d x)))
            -- rowEq→diagEq: from incl z₁ ≡ incl z₂ in row-N colimit,
            -- derive incl z₁ ≡ incl z₂ in diagonal colimit via
            -- colimSeparation on row → cong colIter → diag-eq-hv → inclIter
            rowEq→diagEq : {N : ℕ} (z₁ z₂ : obj D N)
              → incl {X = qpSeq (q N)} {n = N} z₁ ≡ incl {n = N} z₂
              → incl {X = D} {n = N} z₁ ≡ incl {X = D} {n = N} z₂
            rowEq→diagEq {N} z₁ z₂ eqColim = PT.rec (isSetD _ _) step
              (rowSep z₁ z₂ eqColim) where
              open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
              open ColimSep (qpSeq (q N)) (λ k → isFinSet→isSet (qpFin (q N) k))
                renaming (colimSeparation to rowSep)
              open ColimCompactHelpers (qpSeq (q N)) using (liftTo-isProp) renaming (liftTo to liftToRow)
              step : Σ[ M ∈ ℕ ] Σ[ le₁ ∈ N ≤ M ] Σ[ le₂ ∈ N ≤ M ]
                  (liftToRow le₁ z₁ ≡ liftToRow le₂ z₂)
                → incl {X = D} {n = N} z₁ ≡ incl {X = D} {n = N} z₂
              step (M , le₁ , le₂ , eqM) =
                let le = le₁
                    eqM' : liftToRow le z₁ ≡ liftToRow le z₂
                    eqM' = eqM ∙ cong (λ l → liftToRow l z₂) (isProp≤ le₂ le)
                in J (λ M' p₁ →
                    (eqR : ColimCompactHelpers.liftTo (qpSeq (q N)) (fst le , p₁) z₁
                         ≡ ColimCompactHelpers.liftTo (qpSeq (q N)) (fst le , p₁) z₂)
                    → incl {X = D} {n = N} z₁ ≡ incl {X = D} {n = N} z₂)
                  (λ eqR →
                    let d = fst le
                        iterRow = ColimCompactHelpers.iterMap (qpSeq (q N))
                        eqW : iterRow d z₁ ≡ iterRow d z₂
                        eqW = sym (transportRefl (iterRow d z₁)) ∙ eqR ∙ transportRefl (iterRow d z₂)
                        eqV : ColimCompactHelpers.iterMap D d z₁
                            ≡ ColimCompactHelpers.iterMap D d z₂
                        eqV = diag-eq-hv d {N} z₁
                            ∙ cong (colIter d (d +ℕ N)) eqW
                            ∙ sym (diag-eq-hv d {N} z₂)
                    in inclIterD d z₁
                       ∙ cong (incl {X = D} {n = d +ℕ N}) eqV
                       ∙ sym (inclIterD d z₂))
                  (snd le) eqM'
            incl-inj : (n₁ n₂ : ℕ) (x₁ : obj D n₁) (x₂ : obj D n₂)
              → fwdD (incl x₁) ≡ fwdD (incl x₂) → incl {X = D} x₁ ≡ incl x₂
            incl-inj n₁ n₂ x₁ x₂ p = PT.rec (isSetD _ _) go'
              (colimSeparation y₁ y₂ p) where
              y₁ = equivFun (qpEquiv (q n₁)) (incl {X = qpSeq (q n₁)} x₁)
              y₂ = equivFun (qpEquiv (q n₂)) (incl {X = qpSeq (q n₂)} x₂)
              -- Generalized liftToS₀-via-nat for any ≤ proof (not just refl)
              liftToS₀-via-nat-gen : {n N : ℕ} (le : n ≤ N) (x : obj D n)
                → liftToS₀ le (equivFun (qpEquiv (q n)) (incl {X = qpSeq (q n)} x))
                ≡ equivFun (qpEquiv (q N)) (incl {X = qpSeq (q N)} (liftToD le x))
              liftToS₀-via-nat-gen (d , p) x =
                J (λ N' p' →
                    liftToS₀ (d , p') (equivFun (qpEquiv (q _)) (incl x))
                  ≡ equivFun (qpEquiv (q N')) (incl (liftToD (d , p') x)))
                  (liftToS₀-via-nat d x) p
              go' : Σ[ N ∈ ℕ ] Σ[ le₁ ∈ n₁ ≤ N ] Σ[ le₂ ∈ n₂ ≤ N ]
                   (liftToS₀ le₁ y₁ ≡ liftToS₀ le₂ y₂)
                 → incl {X = D} {n = n₁} x₁ ≡ incl {n = n₂} x₂
              go' (N , le₁ , le₂ , eqN) =
                inclLiftD le₁ x₁
                ∙ rowEq→diagEq {N} z₁ z₂ eqColim
                ∙ sym (inclLiftD le₂ x₂)
                where
                z₁ : obj D N
                z₁ = liftToD le₁ x₁
                z₂ : obj D N
                z₂ = liftToD le₂ x₂
                eqZ : equivFun (qpEquiv (q N)) (incl {X = qpSeq (q N)} z₁)
                    ≡ equivFun (qpEquiv (q N)) (incl z₂)
                eqZ = sym (liftToS₀-via-nat-gen le₁ x₁)
                    ∙ eqN
                    ∙ liftToS₀-via-nat-gen le₂ x₂
                eqColim : incl {X = qpSeq (q N)} z₁ ≡ incl z₂
                eqColim = invEq (_ , isEquiv→isEmbedding (snd (qpEquiv (q N))) _ _) eqZ
            fwdD-inj : ∀{d₁ d₂} → fwdD d₁ ≡ fwdD d₂ → d₁ ≡ d₂
            fwdD-inj {d₁} {d₂} = SeqColim→Prop {C = D}
              {B = λ d₁ → (d₂ : SeqColim D) → fwdD d₁ ≡ fwdD d₂ → d₁ ≡ d₂}
              (λ d₁ → isPropΠ λ d₂ → isPropΠ λ _ → isSetD d₁ d₂)
              (λ n₁ x₁ → SeqColim→Prop {C = D}
                {B = λ d₂ → fwdD (incl x₁) ≡ fwdD d₂ → incl x₁ ≡ d₂}
                (λ d₂ → isPropΠ λ _ → isSetD _ d₂)
                (λ n₂ x₂ → incl-inj n₁ n₂ x₁ x₂))
              d₁ d₂
  isFinSet-freeBA-Fin : (k : ℕ) → isFinSet ⟨ freeBA (DF.Fin k) ⟩
  isFinSet-freeBA-Fin k = EquivPresIsFinSet (invEquiv total-equiv) isFinSetTarget where
    open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
    open import Axioms.StoneDuality using (SDHomVersion)
    open BooleanRingStr
    freeBA-k = freeBA (DF.Fin k)
    freeBA-ℕ' = freeBA ℕ
    -- Step 1: Booleω structure for freeBA(Fin k) via killRel
    killRel : ℕ → ⟨ freeBA-ℕ' ⟩
    killRel j = generator (k +ℕ j)
    Qk : BooleanRing ℓ-zero
    Qk = freeBA-ℕ' QB./Im killRel
    πQ : ⟨ freeBA-ℕ' ⟩ → ⟨ Qk ⟩
    πQ = fst (QB.quotientImageHom {B = freeBA-ℕ'} {f = killRel})
    -- Forward: freeBA(Fin k) → Qk
    fwd-hom : BoolHom freeBA-k Qk
    fwd-hom = inducedBAHom (DF.Fin k) Qk (λ i → πQ (generator (fst i)))
    -- Backward: Qk → freeBA(Fin k)
    bwd-gen : ℕ → ⟨ freeBA-k ⟩
    bwd-gen j with <Dec j k
    ... | yes p = generator (j , <→<ᵗ p)
    ... | no _  = 𝟘 (snd freeBA-k)
    bwd-free : BoolHom freeBA-ℕ' freeBA-k
    bwd-free = inducedBAHom ℕ freeBA-k bwd-gen
    bwd-kills : (j : ℕ) → fst bwd-free (killRel j) ≡ 𝟘 (snd freeBA-k)
    bwd-kills j = cong (λ f → f (k +ℕ j)) (evalBAInduce ℕ freeBA-k bwd-gen) ∙ step₂ where
      step₂ : bwd-gen (k +ℕ j) ≡ 𝟘 (snd freeBA-k)
      step₂ with <Dec (k +ℕ j) k
      ... | yes p = ex-falso (¬m+n<m p)
      ... | no _  = refl
    bwd-hom : BoolHom Qk freeBA-k
    bwd-hom = QB.inducedHom {B = freeBA-ℕ'} {f = killRel} freeBA-k bwd-free bwd-kills
    -- Roundtrip 1: bwd ∘ fwd = id on freeBA(Fin k)
    -- Both BoolHoms agree on generators, so equal by universal property
    rt₁-on-gen : (i : DF.Fin k) → fst bwd-hom (fst fwd-hom (generator i)) ≡ generator i
    rt₁-on-gen i =
      cong (fst bwd-hom) (cong (λ f → f i) (evalBAInduce (DF.Fin k) Qk (λ i' → πQ (generator (fst i')))))
      ∙ cong (λ f → f (generator (fst i))) (cong fst (QB.evalInduce {B = freeBA-ℕ'} {f = killRel} freeBA-k {g = bwd-free}))
      ∙ cong (λ f → f (fst i)) (evalBAInduce ℕ freeBA-k bwd-gen)
      ∙ bwd-gen-at-i
      where
      bwd-gen-at-i : bwd-gen (fst i) ≡ generator i
      bwd-gen-at-i with <Dec (fst i) k
      ... | yes p = cong generator (Σ≡Prop (λ _ → isProp<ᵗ {_} {k}) refl)
      ... | no ¬p = ex-falso (¬p (<ᵗ→< (snd i)))
    roundtrip₁ : (x : ⟨ freeBA-k ⟩) → fst bwd-hom (fst fwd-hom x) ≡ x
    roundtrip₁ x = cong (λ h → fst h x) path where
      comp-hom : BoolHom freeBA-k freeBA-k
      comp-hom = bwd-hom ∘cr fwd-hom
      agree : fst comp-hom ∘ generator ≡ generator
      agree = funExt rt₁-on-gen
      path : comp-hom ≡ idBoolHom freeBA-k
      path = sym (inducedBAHomUnique (DF.Fin k) freeBA-k generator comp-hom agree)
           ∙ inducedBAHomUnique (DF.Fin k) freeBA-k generator (idBoolHom freeBA-k) refl
    -- Roundtrip 2: fwd ∘ bwd = id on Qk
    -- Both fwd ∘ bwd ∘ πQ and πQ = id ∘ πQ agree on generators of freeBA ℕ
    rt₂-on-gen : (j : ℕ) → fst fwd-hom (fst bwd-hom (πQ (generator j))) ≡ πQ (generator j)
    rt₂-on-gen j =
      cong (fst fwd-hom) (cong (λ f → f (generator j))
        (cong fst (QB.evalInduce {B = freeBA-ℕ'} {f = killRel} freeBA-k {g = bwd-free})))
      ∙ cong (fst fwd-hom) (cong (λ f → f j) (evalBAInduce ℕ freeBA-k bwd-gen))
      ∙ fwd-bwd-gen-j
      where
      fwd-bwd-gen-j : fst fwd-hom (bwd-gen j) ≡ πQ (generator j)
      fwd-bwd-gen-j with <Dec j k
      ... | yes p = cong (λ f → f (j , <→<ᵗ p)) (evalBAInduce (DF.Fin k) Qk (λ i → πQ (generator (fst i))))
      ... | no ¬p = IsCommRingHom.pres0 (snd fwd-hom)
                  ∙ sym (cong πQ (cong generator lem) ∙ QB.zeroOnImage {B = freeBA-ℕ'} {f = killRel} d)
        where
        open import Cubical.Data.Nat.Order using (<-asym')
        open import Cubical.Data.Nat.Properties using (+-comm)
        k≤j = <-asym' ¬p
        d = fst k≤j
        lem : j ≡ k +ℕ d
        lem = sym (snd k≤j) ∙ +-comm d k
    roundtrip₂ : (x : ⟨ Qk ⟩) → fst fwd-hom (fst bwd-hom x) ≡ x
    roundtrip₂ = funExt⁻ (QB.quotientImageHomEpi {B = freeBA-ℕ'} {f = killRel}
      (⟨ Qk ⟩ , is-set (snd Qk)) on-πQ)
      where
      πQ-hom : BoolHom freeBA-ℕ' Qk
      πQ-hom = QB.quotientImageHom {B = freeBA-ℕ'} {f = killRel}
      comp-hom : BoolHom freeBA-ℕ' Qk
      comp-hom = fwd-hom ∘cr bwd-hom ∘cr πQ-hom
      on-πQ : (fst fwd-hom ∘ fst bwd-hom) ∘ πQ ≡ idfun _ ∘ πQ
      on-πQ = cong fst
        (sym (inducedBAHomUnique ℕ Qk (πQ ∘ generator) comp-hom (funExt rt₂-on-gen))
         ∙ inducedBAHomUnique ℕ Qk (πQ ∘ generator) πQ-hom refl)
    -- Booleω structure
    booleω-k : Booleω
    booleω-k = freeBA-k , ∣ killRel , isoToEquiv (iso (fst fwd-hom) (fst bwd-hom) roundtrip₂ roundtrip₁) , snd fwd-hom ∣₁
    -- Step 2: Sp(freeBA(Fin k)) ≃ (Fin k → Bool) via universal property
    sp-equiv : Sp booleω-k ≃ (DF.Fin k → Bool)
    sp-equiv = isoToEquiv (iso
      (λ h → fst h ∘ generator)
      (λ f → inducedBAHom (DF.Fin k) BoolBR f)
      (evalBAInduce (DF.Fin k) BoolBR)
      (λ h → inducedBAHomUnique (DF.Fin k) BoolBR (fst h ∘ generator) h refl))
    -- Step 3: compose equivs, deduce finiteness
    sd-equiv : ⟨ freeBA-k ⟩ ≃ (Sp booleω-k → Bool)
    sd-equiv = fst (SDHomVersion sd-axiom booleω-k)
    total-equiv : ⟨ freeBA-k ⟩ ≃ ((DF.Fin k → Bool) → Bool)
    total-equiv = compEquiv sd-equiv (preCompEquiv (invEquiv sp-equiv))
    isFinSetDFFin : isFinSet (DF.Fin k)
    isFinSetDFFin = EquivPresIsFinSet (SumFin≃Fin k) isFinSetFin
    isFinSetTarget : isFinSet ((DF.Fin k → Bool) → Bool)
    isFinSetTarget = isFinSet→ (_ , isFinSet→ (_ , isFinSetDFFin) (_ , isFinSetBool)) (_ , isFinSetBool)
  -- Quotient of finite Boolean ring by finitely many relations is finite
  opaque
    unfolding QB._/Im_
    isFinSet-BRquot : (B' : BooleanRing ℓ-zero) (finB : isFinSet ⟨ B' ⟩)
      {n : ℕ} (g : DF.Fin n → ⟨ B' ⟩) → isFinSet ⟨ B' QB./Im g ⟩
    isFinSet-BRquot B' finB {n} g = BRQ.result where
      module BRQ where
        open BooleanAlgebraStr B' renaming (_∨_ to _∨B_; _∧_ to _·B_)
        CR : CommRing ℓ-zero
        CR = BooleanRing→CommRing B'
        private module CRS = CommRingStr (snd CR)
        infixl 6 _+B_
        _+B_ : ⟨ B' ⟩ → ⟨ B' ⟩ → ⟨ B' ⟩
        _+B_ = CRS._+_
        -B_ : ⟨ B' ⟩ → ⟨ B' ⟩
        -B_ = CRS.-_
        𝟘' : ⟨ B' ⟩
        𝟘' = CRS.0r
        genI : ⟨ B' ⟩ → Type
        genI = IQ.generatedIdeal CR g
        disc = isFinSet→Discrete finB
        go : (i : ℕ) → i ≤ n → ⟨ B' ⟩
        go zero _ = 𝟘'
        go (suc i) p = go i (≤-trans ≤-sucℕ p) ∨B g (i , <→<ᵗ p)
        genJ : ⟨ B' ⟩
        genJ = go n ≤-refl
        mono : ∀ {a b c} → a ·B b ≡ a → a ·B (b ∨B c) ≡ a
        mono {a} {b} {c} h =
          a ·B (b ∨B c)          ≡⟨ ∧DistR∨ ⟩
          (a ·B b) ∨B (a ·B c)  ≡⟨ cong (_∨B (a ·B c)) h ⟩
          a ∨B (a ·B c)          ≡⟨ ∨AbsorbL∧ ⟩
          a ∎
        gen-below-go : (j : DF.Fin n) (i : ℕ) (p : i ≤ n)
          → fst j < i → g j ·B go i p ≡ g j
        gen-below-go _ zero _ q = ⊥-rec (¬-<-zero q)
        gen-below-go j (suc i) p q with ≤-split (pred-≤-pred q)
        ... | ⊎.inl fj<i = mono (gen-below-go j i (≤-trans ≤-sucℕ p) fj<i)
        ... | ⊎.inr fj≡i =
          g j ·B (go i p' ∨B g (i , <→<ᵗ p))
            ≡⟨ cong (λ w → g j ·B (go i p' ∨B g w))
                 (sym (Σ≡Prop (λ _ → isProp<ᵗ {_} {n}) fj≡i)) ⟩
          g j ·B (go i p' ∨B g j)
            ≡⟨ cong (g j ·B_) ∨Comm ⟩
          g j ·B (g j ∨B go i p')
            ≡⟨ ∧AbsorbL∨ ⟩
          g j ∎
          where p' = ≤-trans ≤-sucℕ p
        gen-below : (j : DF.Fin n) → g j ·B genJ ≡ g j
        gen-below j = gen-below-go j n ≤-refl (<ᵗ→< (snd j))
        fwd : ∀ {z} → genI z → z ·B genJ ≡ z
        fwd (IQ.single x) = gen-below x
        fwd IQ.zero = ∧AnnihilL
        fwd (IQ.add {x} {y} gx gy) =
          (x +B y) ·B genJ              ≡⟨ CRS.·DistL+ x y genJ ⟩
          (x ·B genJ) +B (y ·B genJ)   ≡⟨ cong₂ _+B_ (fwd gx) (fwd gy) ⟩
          x +B y                         ∎
        fwd (IQ.mul {r} {x} gx) =
          (r ·B x) ·B genJ ≡⟨ sym (CRS.·Assoc r x genJ) ⟩
          r ·B (x ·B genJ) ≡⟨ cong (r ·B_) (fwd gx) ⟩
          r ·B x            ∎
        fwd (IQ.squash gx gy i) = CRS.is-set _ _ (fwd gx) (fwd gy) i
        go-in-ideal : (i : ℕ) (p : i ≤ n) → genI (go i p)
        go-in-ideal zero _ = IQ.zero
        go-in-ideal (suc i) p =
          IQ.add (IQ.add (go-in-ideal i _) (IQ.single (i , <→<ᵗ p)))
              (IQ.mul {r = go i _} (IQ.single (i , <→<ᵗ p)))
        bwd : ∀ {z} → z ·B genJ ≡ z → genI z
        bwd {z} p = subst genI p (IQ.mul {r = z} (go-in-ideal n ≤-refl))
        idealRel : ⟨ B' ⟩ → ⟨ B' ⟩ → Type
        idealRel x y = genI (x +B (-B y))
        equivR : BinaryRelation.isEquivRel idealRel
        equivR = let open BinaryRelation idealRel in equivRel
          (λ x → subst genI (sym (CRS.+InvR x)) IQ.zero)
          (λ x y gxy → subst genI
            (x +B (-B y) ≡⟨ cong (x +B_) (sym -IsId) ⟩
             x +B y      ≡⟨ CRS.+Comm x y ⟩
             y +B x      ≡⟨ cong (y +B_) -IsId ⟩
             y +B (-B x) ∎) gxy)
          (λ x y z gxy gyz → subst genI
            ((x +B (-B y)) +B (y +B (-B z))
              ≡⟨ cong₂ _+B_ (cong (x +B_) (sym -IsId)) (cong (y +B_) (sym -IsId)) ⟩
             (x +B y) +B (y +B z)
              ≡⟨ sym (CRS.+Assoc x y (y +B z)) ⟩
             x +B (y +B (y +B z))
              ≡⟨ cong (x +B_) (CRS.+Assoc y y z) ⟩
             x +B ((y +B y) +B z)
              ≡⟨ cong (x +B_) (cong (_+B z) characteristic2) ⟩
             x +B (𝟘' +B z)
              ≡⟨ cong (x +B_) (CRS.+IdL z) ⟩
             x +B z
              ≡⟨ cong (x +B_) -IsId ⟩
             x +B (-B z) ∎) (IQ.add gxy gyz))
        decR : (x y : ⟨ B' ⟩) → isDecProp (idealRel x y)
        decR x y = Dec→Bool d , Dec≃DecBool IQ.squash d where
          d : Dec (idealRel x y)
          d with disc ((x +B (-B y)) ·B genJ) (x +B (-B y))
          ... | yes p = yes (bwd p)
          ... | no ¬p = no (λ gI → ¬p (fwd gI))
        result : isFinSet ⟨ B' QB./Im g ⟩
        result = isFinSetQuot (⟨ B' ⟩ , finB) idealRel equivR decR
  -- Ring-structured ODisc decomposition data for a quotient of freeBA ℕ
  ODiscRingDecompSeq : (BN : ℕ → BooleanRing ℓ-zero)
    → ((n : ℕ) → ⟨ BN n ⟩ → ⟨ BN (suc n) ⟩) → Sequence ℓ-zero
  obj (ODiscRingDecompSeq BN mapBN) n = ⟨ BN n ⟩
  map (ODiscRingDecompSeq BN mapBN) = mapBN _
  record ODiscRingDecomp (Q : BooleanRing ℓ-zero) : Type (ℓ-suc ℓ-zero) where
    field
      BN : ℕ → BooleanRing ℓ-zero
      isFinSetBN : (n : ℕ) → isFinSet ⟨ BN n ⟩
      mapBN : (n : ℕ) → ⟨ BN n ⟩ → ⟨ BN (suc n) ⟩
      mapBNHom : (n : ℕ) → BoolHom (BN n) (BN (suc n))
      mapBN≡ : (n : ℕ) → mapBN n ≡ fst (mapBNHom n)
      fwdHom : (n : ℕ) → BoolHom (BN n) Q
      fwd-compat : (n : ℕ) (x : ⟨ BN n ⟩)
        → fst (fwdHom n) x ≡ fst (fwdHom (suc n)) (mapBN n x)
      colimEquiv : SeqColim (ODiscRingDecompSeq BN mapBN) ≃ ⟨ Q ⟩
      colimEquiv-incl : (n : ℕ) (x : ⟨ BN n ⟩)
        → equivFun colimEquiv (incl x) ≡ fst (fwdHom n) x
    seqB : Sequence ℓ-zero
    seqB = ODiscRingDecompSeq BN mapBN
    -- Compose mapBNHom d times: BoolHom (BN n) (BN (d + n))
    iterMapHom : (d : ℕ) {n : ℕ} → BoolHom (BN n) (BN (d +ℕ n))
    iterMapHom zero {n} = idBoolHom (BN n)
    iterMapHom (suc d) {n} = mapBNHom (d +ℕ n) ∘cr iterMapHom d
    -- iterMapHom agrees with iterMap on underlying functions
    iterMapHom≡iterMap : (d : ℕ) {n : ℕ} (x : ⟨ BN n ⟩)
      → fst (iterMapHom d {n}) x ≡ ColimCompactHelpers.iterMap seqB d x
    iterMapHom≡iterMap zero x = refl
    iterMapHom≡iterMap (suc d) {n} x =
      cong (fst (mapBNHom (d +ℕ n))) (iterMapHom≡iterMap d x)
      ∙ sym (funExt⁻ (mapBN≡ (d +ℕ n)) (ColimCompactHelpers.iterMap seqB d x))
    -- liftToHom: ring hom from BN n to BN N for n ≤ N
    liftToHom : {n N : ℕ} → n ≤ N → BoolHom (BN n) (BN N)
    liftToHom {n} {N} (d , p) = subst (λ m → BoolHom (BN n) (BN m)) p (iterMapHom d)
    -- fwdHom factors through levels via iterMapHom
    fwd-compat-hom : (d : ℕ) {n : ℕ} (x : ⟨ BN n ⟩)
      → fst (fwdHom n) x ≡ fst (fwdHom (d +ℕ n)) (fst (iterMapHom d) x)
    fwd-compat-hom zero x = refl
    fwd-compat-hom (suc d) {n} x =
      fst (fwdHom n) x
        ≡⟨ fwd-compat-hom d x ⟩
      fst (fwdHom (d +ℕ n)) (fst (iterMapHom d) x)
        ≡⟨ fwd-compat (d +ℕ n) (fst (iterMapHom d) x) ⟩
      fst (fwdHom (suc (d +ℕ n))) (mapBN (d +ℕ n) (fst (iterMapHom d) x))
        ≡⟨ cong (fst (fwdHom (suc d +ℕ n))) (funExt⁻ (mapBN≡ (d +ℕ n)) (fst (iterMapHom d) x)) ⟩
      fst (fwdHom (suc d +ℕ n)) (fst (mapBNHom (d +ℕ n)) (fst (iterMapHom d) x)) ∎
  -- tex Lemma 1396 (core): proved from ODiscColimOfODisc + countableChoice + genBound
  quotientFreeBA-ringDecomp : (f : ℕ → ⟨ freeBA ℕ ⟩)
    → ∥ ODiscRingDecomp (freeBA ℕ QB./Im f) ∥₁
  quotientFreeBA-ringDecomp f =
    PT.map go (countableChoice _ (λ k → ODiscInfrastructure.genBound (f k)))
    where
      open ODiscInfrastructure using (ι-inc; π-proj; ιπι-retract; π-on-gen-below)
      go : ((k : ℕ) → Σ[ m ∈ ℕ ] fiber (fst (ι-inc m)) (f k))
         → ODiscRingDecomp (freeBA ℕ QB./Im f)
      go choice = record
        { BN = BN ; isFinSetBN = isFinSetBN ; mapBN = mapBN
        ; mapBNHom = mapBNHom ; mapBN≡ = λ _ → refl
        ; fwdHom = fwdHom ; fwd-compat = fwd-compat ; colimEquiv = colimEquiv
        ; colimEquiv-incl = λ _ _ → refl } where
        -- M(n): monotone function bounding generators in first n+1 relations
        M : ℕ → ℕ
        M zero = max (suc zero) (fst (choice zero))
        M (suc n) = max (suc (M n)) (fst (choice (suc n)))
        -- Level n: freeBA(Fin(M n)) quotiented by first n+1 relations projected
        relN : (n : ℕ) → DF.Fin (suc n) → ⟨ freeBA (DF.Fin (M n)) ⟩
        relN n j = fst (π-proj (M n)) (f (fst j))
        BN : (n : ℕ) → BooleanRing ℓ-zero
        BN n = freeBA (DF.Fin (M n)) QB./Im relN n
        M-step : (i : ℕ) → M i ≤ M (suc i)
        M-step i = ≤-trans (≤-sucℕ {n = M i})
          (left-≤-max {m = suc (M i)} {n = fst (choice (suc i))})
        M-mono-go : (m₁ : ℕ) (d : ℕ) → M m₁ ≤ M (d +ℕ m₁)
        M-mono-go _ zero = ≤-refl
        M-mono-go m₁ (suc d) = ≤-trans (M-mono-go m₁ d) (M-step (d +ℕ m₁))
        M-mono' : {m₁ m₂ : ℕ} → m₁ ≤ m₂ → M m₁ ≤ M m₂
        M-mono' {m₁} (d , p) = subst (λ x → M m₁ ≤ M x) p (M-mono-go m₁ d)
        choice-le : (i : ℕ) → fst (choice i) ≤ M i
        choice-le zero = right-≤-max {m = suc zero}
        choice-le (suc i) = right-≤-max {m = suc (M i)}
        -- Map: BN(n) → BN(n+1) via πQ ∘ π-proj(M(n+1)) ∘ ι-inc(M(n))
        mapBNHom : (n : ℕ) → BoolHom (BN n) (BN (suc n))
        mapBNHom n = QB.inducedHom {B = freeBA (DF.Fin (M n))} {f = relN n}
          (BN (suc n)) g gfx=0 where
          g : BoolHom (freeBA (DF.Fin (M n))) (BN (suc n))
          g = QB.quotientImageHom ∘cr π-proj (M (suc n)) ∘cr ι-inc (M n)
          gfx=0 : (j : DF.Fin (suc n))
            → fst g (relN n j) ≡ BooleanRingStr.𝟘 (snd (BN (suc n)))
          gfx=0 j =
            cong (fst QB.quotientImageHom ∘ fst (π-proj (M (suc n)))) retract-step
            ∙ QB.zeroOnImage {B = freeBA (DF.Fin (M (suc n)))} {f = relN (suc n)} j'
            where
              k = fst j
              m_k = fst (choice k)
              x_k = fst (snd (choice k))
              eq_k = snd (snd (choice k))
              le_k : m_k ≤ M n
              le_k = ≤-trans (choice-le k)
                (M-mono' {m₁ = k} {m₂ = n} (pred-≤-pred (<ᵗ→< (snd j))))
              j' : DF.Fin (suc (suc n))
              j' = (k , <→<ᵗ (≤-trans (<ᵗ→< {n = k} (snd j)) (≤-sucℕ {n = suc n})))
              retract-step : fst (ι-inc (M n)) (fst (π-proj (M n)) (f k)) ≡ f k
              retract-step =
                cong (fst (ι-inc (M n)) ∘ fst (π-proj (M n))) (sym eq_k)
                ∙ funExt⁻ (cong fst (ιπι-retract m_k (M n) le_k)) x_k
                ∙ eq_k
        mapBN : (n : ℕ) → ⟨ BN n ⟩ → ⟨ BN (suc n) ⟩
        mapBN n = fst (mapBNHom n)
        seqB : Sequence ℓ-zero
        obj seqB n = ⟨ BN n ⟩
        map seqB = mapBN _
        -- Each level is ODisc (finite, hence ODisc)
        isFinSetBN : (n : ℕ) → isFinSet (obj seqB n)
        isFinSetBN n = isFinSet-BRquot (freeBA (DF.Fin (M n)))
          (isFinSet-freeBA-Fin (M n)) {suc n} (relN n)
        -- Colimit of BN ≃ freeBA ℕ /Im f
        Q = freeBA ℕ QB./Im f
        πQ : BoolHom (freeBA ℕ) Q
        πQ = QB.quotientImageHom {B = freeBA ℕ} {f = f}
        -- Forward hom at each level: BN(n) → Q
        fwdKills : (n : ℕ) (j : DF.Fin (suc n))
          → fst (πQ ∘cr ι-inc (M n)) (relN n j) ≡ BooleanRingStr.𝟘 (snd Q)
        fwdKills n j =
          fst πQ (fst (ι-inc (M n)) (fst (π-proj (M n)) (f k)))
            ≡⟨ cong (fst πQ) retract-step ⟩
          fst πQ (f k)
            ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = f} k ⟩
          BooleanRingStr.𝟘 (snd Q) ∎
          where
            k = fst j
            le_k : fst (choice k) ≤ M n
            le_k = ≤-trans (choice-le k)
              (M-mono' {m₁ = k} {m₂ = n} (pred-≤-pred (<ᵗ→< (snd j))))
            retract-step : fst (ι-inc (M n)) (fst (π-proj (M n)) (f k)) ≡ f k
            retract-step =
              cong (fst (ι-inc (M n)) ∘ fst (π-proj (M n))) (sym (snd (snd (choice k))))
              ∙ funExt⁻ (cong fst (ιπι-retract (fst (choice k)) (M n) le_k))
                  (fst (snd (choice k)))
              ∙ snd (snd (choice k))
        fwdHom : (n : ℕ) → BoolHom (BN n) Q
        fwdHom n = QB.inducedHom {B = freeBA (DF.Fin (M n))} {f = relN n}
          Q (πQ ∘cr ι-inc (M n)) (fwdKills n)
        -- Push compatibility: fwdHom n = fwdHom(n+1) ∘ mapBN n
        πBN : (n : ℕ) → ⟨ freeBA (DF.Fin (M n)) ⟩ → ⟨ BN n ⟩
        πBN n = fst (QB.quotientImageHom {B = freeBA (DF.Fin (M n))} {f = relN n})
        evalFwd : (n : ℕ) → fwdHom n ∘cr QB.quotientImageHom
          {B = freeBA (DF.Fin (M n))} {f = relN n} ≡ πQ ∘cr ι-inc (M n)
        evalFwd n = QB.evalInduce {B = freeBA (DF.Fin (M n))} {f = relN n} Q
        fwd-compat : (n : ℕ) (x : ⟨ BN n ⟩)
          → fst (fwdHom n) x ≡ fst (fwdHom (suc n)) (mapBN n x)
        fwd-compat n = funExt⁻ (QB.quotientImageHomEpi
          {B = freeBA (DF.Fin (M n))} {f = relN n}
          (⟨ Q ⟩ , BooleanRingStr.is-set (snd Q))
          (funExt λ a → sym (
            fst (fwdHom (suc n)) (mapBN n (πBN n a))
              ≡⟨ cong (fst (fwdHom (suc n)))
                   (funExt⁻ (cong fst (QB.evalInduce
                     {B = freeBA (DF.Fin (M n))} {f = relN n}
                     (BN (suc n)))) a) ⟩
            fst (fwdHom (suc n)) (πBN (suc n)
              (fst (π-proj (M (suc n))) (fst (ι-inc (M n)) a)))
              ≡⟨ funExt⁻ (cong fst (evalFwd (suc n)))
                   (fst (π-proj (M (suc n))) (fst (ι-inc (M n)) a)) ⟩
            fst πQ (fst (ι-inc (M (suc n)))
              (fst (π-proj (M (suc n))) (fst (ι-inc (M n)) a)))
              ≡⟨ cong (fst πQ)
                   (funExt⁻ (cong fst (ιπι-retract (M n) (M (suc n)) (M-step n))) a) ⟩
            fst πQ (fst (ι-inc (M n)) a)
              ≡⟨ sym (funExt⁻ (cong fst (evalFwd n)) a) ⟩
            fst (fwdHom n) (πBN n a) ∎)))
        -- Forward map
        fwd : SeqColim seqB → ⟨ Q ⟩
        fwd (incl {n} x) = fst (fwdHom n) x
        fwd (push {n} x i) = fwd-compat n x i
        -- Surjectivity of fwd
        M-ge-suc : (n : ℕ) → suc n ≤ M n
        M-ge-suc zero = left-≤-max {m = suc zero} {n = fst (choice zero)}
        M-ge-suc (suc n) = ≤-trans (suc-≤-suc (M-ge-suc n))
          (left-≤-max {m = suc (M n)} {n = fst (choice (suc n))})
        fwd-surj : isSurjection fwd
        fwd-surj q = PT.rec squash₁ (λ (b , eq) →
          PT.rec squash₁ (λ (m , x_m , eq_m) →
            let n = m
                le_m : m ≤ M n
                le_m = ≤-trans (≤-sucℕ {n = m}) (M-ge-suc n)
                y = fst (π-proj (M n)) b
            in ∣ incl {n = n} (fst (QB.quotientImageHom
                   {B = freeBA (DF.Fin (M n))} {f = relN n}) y) ,
                 (fst (fwdHom n) (fst (QB.quotientImageHom
                    {B = freeBA (DF.Fin (M n))} {f = relN n}) y)
                   ≡⟨ funExt⁻ (cong fst (QB.evalInduce
                        {B = freeBA (DF.Fin (M n))} {f = relN n} Q)) y ⟩
                  fst πQ (fst (ι-inc (M n)) (fst (π-proj (M n)) b))
                   ≡⟨ cong (fst πQ)
                        (fst (ι-inc (M n)) (fst (π-proj (M n)) b)
                          ≡⟨ cong (fst (ι-inc (M n)) ∘ fst (π-proj (M n))) (sym eq_m) ⟩
                         fst (ι-inc (M n)) (fst (π-proj (M n)) (fst (ι-inc m) x_m))
                          ≡⟨ funExt⁻ (cong fst (ιπι-retract m (M n) le_m)) x_m ⟩
                         fst (ι-inc m) x_m
                          ≡⟨ eq_m ⟩
                         b ∎) ⟩
                  fst πQ b
                   ≡⟨ eq ⟩
                  q ∎) ∣₁)
            (ODiscInfrastructure.genBound b))
          (QB.quotientImageHomSurjective {B = freeBA ℕ} {f = f} q)
        -- SeqColim of sets is a set
        isSetSC : isSet (SeqColim seqB)
        isSetSC = isSetSeqColimOfSets seqB (λ n → BooleanRingStr.is-set (snd (BN n)))
        -- mapBN evaluation: mapBN n ∘ πBN n = πBN(n+1) ∘ π-proj(M(n+1)) ∘ ι-inc(M n)
        mapBN-eval : (n : ℕ) (a : ⟨ freeBA (DF.Fin (M n)) ⟩)
          → mapBN n (πBN n a) ≡ πBN (suc n) (fst (π-proj (M (suc n))) (fst (ι-inc (M n)) a))
        mapBN-eval n a = funExt⁻ (cong fst (QB.evalInduce
          {B = freeBA (DF.Fin (M n))} {f = relN n} (BN (suc n)))) a
        -- Push to higher level: incl {n} (πBN n a) ≡ incl {suc d+n} (πBN ... (π-proj ∘ ι-inc $ a))
        G : (n k : ℕ) → ⟨ freeBA (DF.Fin (M n)) ⟩ → obj seqB k
        G n k a = πBN k (fst (π-proj (M k)) (fst (ι-inc (M n)) a))
        push-to-πBN : (d n : ℕ) (a : ⟨ freeBA (DF.Fin (M n)) ⟩)
          → Path (SeqColim seqB) (incl {n = n} (πBN n a))
              (incl {n = suc d +ℕ n} (G n (suc d +ℕ n) a))
        push-to-πBN zero n a =
          push (πBN n a) ∙ cong (incl {n = suc n}) (mapBN-eval n a)
        push-to-πBN (suc d) n a =
          let y = G n (suc d +ℕ n) a
              retract-step = funExt⁻ (cong fst (ιπι-retract (M n) (M (suc d +ℕ n))
                (M-mono' {m₁ = n} {m₂ = suc d +ℕ n} (suc d , refl)))) a
          in push-to-πBN d n a ∙ push y
            ∙ cong (incl {n = suc (suc d +ℕ n)})
                (mapBN-eval (suc d +ℕ n)
                  (fst (π-proj (M (suc d +ℕ n))) (fst (ι-inc (M n)) a))
                ∙ cong (πBN (suc (suc d +ℕ n)) ∘ fst (π-proj (M (suc (suc d +ℕ n))))) retract-step)
        -- Transport along level equality by J
        incl-level-eq : (n : ℕ) {m m' : ℕ} (p : m ≡ m') (a : ⟨ freeBA (DF.Fin (M n)) ⟩)
          → Path (SeqColim seqB) (incl {n = m} (G n m a))
              (incl {n = m'} (G n m' a))
        incl-level-eq n {m} p a =
          J (λ m' _ → Path (SeqColim seqB) (incl (G n m a)) (incl (G n m' a))) refl p
        -- Decompose n ≤ K' with suc n ≤ K' to get d' with suc d' + n ≡ K'
        suc-le-decomp : {n K' : ℕ} → n ≤ K' → suc n ≤ K'
          → Σ[ d' ∈ ℕ ] suc d' +ℕ n ≡ K'
        suc-le-decomp {n} (zero , p) sn≤K' =
          ex-falso (¬m<m (subst (suc n ≤_) (sym p) sn≤K'))
        suc-le-decomp (suc d' , p) _ = d' , p
        -- Finite support: genIdeal(f)(z) → ∃K. ∀K'≥K. genIdeal(relN K')(π-proj(M K')(z))
        CR-ℕ = BooleanRing→CommRing (freeBA ℕ)
        combined : {z : ⟨ freeBA ℕ ⟩}
          → IQ.generatedIdeal CR-ℕ f z
          → ∥ Σ[ K ∈ ℕ ] ((K' : ℕ) → K ≤ K'
            → IQ.generatedIdeal (BooleanRing→CommRing (freeBA (DF.Fin (M K'))))
                (relN K') (fst (π-proj (M K')) z)) ∥₁
        combined (IQ.single k) = ∣ k , (λ K' le →
          IQ.single (k , <→<ᵗ (suc-≤-suc le))) ∣₁
        combined IQ.zero = ∣ 0 , (λ K' _ →
          subst (IQ.generatedIdeal _ (relN K'))
            (sym (IsCommRingHom.pres0 (snd (π-proj (M K'))))) IQ.zero) ∣₁
        combined (IQ.add {x} {y} gx gy) = PT.rec2 squash₁
          (λ (Kx , hx) (Ky , hy) →
            ∣ max Kx Ky , (λ K' le →
              subst (IQ.generatedIdeal _ (relN K'))
                (sym (IsCommRingHom.pres+ (snd (π-proj (M K'))) x y))
                (IQ.add (hx K' (≤-trans (left-≤-max {Kx} {Ky}) le))
                        (hy K' (≤-trans (right-≤-max {Ky} {Kx}) le)))) ∣₁)
          (combined gx) (combined gy)
        combined (IQ.mul {r} {x} gx) = PT.map
          (λ (K , h) → K , (λ K' le →
            subst (IQ.generatedIdeal _ (relN K'))
              (sym (IsCommRingHom.pres· (snd (π-proj (M K'))) r x))
              (IQ.mul (h K' le)))) (combined gx)
        combined (IQ.squash gx gy i) = squash₁ (combined gx) (combined gy) i
        -- Characteristic 2: a + b = 0 → a = b (in any BooleanRing)
        char2-eq : {B' : BooleanRing ℓ-zero} (a b : ⟨ B' ⟩)
          → BooleanRingStr._+_ (snd B') a b ≡ BooleanRingStr.𝟘 (snd B')
          → a ≡ b
        char2-eq {B'} a b p =
          a ≡⟨ sym (BooleanRingStr.+IdR (snd B') a) ⟩
          a +B' BooleanRingStr.𝟘 (snd B')
            ≡⟨ cong (a +B'_) (sym (BooleanAlgebraStr.characteristic2 B' {b})) ⟩
          a +B' (b +B' b)
            ≡⟨ BooleanRingStr.+Assoc (snd B') a b b ⟩
          (a +B' b) +B' b ≡⟨ cong (_+B' b) p ⟩
          BooleanRingStr.𝟘 (snd B') +B' b
            ≡⟨ BooleanRingStr.+IdL (snd B') b ⟩
          b ∎ where _+B'_ = BooleanRingStr._+_ (snd B')
        -- Ideal elements project to zero in quotient
        ideal→zero : (K' : ℕ) {z : ⟨ freeBA (DF.Fin (M K')) ⟩}
          → IQ.generatedIdeal (BooleanRing→CommRing (freeBA (DF.Fin (M K')))) (relN K') z
          → πBN K' z ≡ BooleanRingStr.𝟘 (snd (BN K'))
        ideal→zero K' (IQ.single j) =
          QB.zeroOnImage {B = freeBA (DF.Fin (M K'))} {f = relN K'} j
        ideal→zero K' IQ.zero =
          IsCommRingHom.pres0 (snd (QB.quotientImageHom
            {B = freeBA (DF.Fin (M K'))} {f = relN K'}))
        ideal→zero K' (IQ.add {x} {y} gx gy) =
          IsCommRingHom.pres+ (snd (QB.quotientImageHom
            {B = freeBA (DF.Fin (M K'))} {f = relN K'})) x y
          ∙ cong₂ (BooleanRingStr._+_ (snd (BN K')))
              (ideal→zero K' gx) (ideal→zero K' gy)
          ∙ BooleanRingStr.+IdR (snd (BN K')) _
        ideal→zero K' (IQ.mul {r} {x} gx) =
          IsCommRingHom.pres· (snd (QB.quotientImageHom
            {B = freeBA (DF.Fin (M K'))} {f = relN K'})) r x
          ∙ cong (BooleanRingStr._·_ (snd (BN K')) (πBN K' r))
              (ideal→zero K' gx)
          ∙ BooleanAlgebraStr.∧AnnihilR (BN K')
        ideal→zero K' (IQ.squash gx gy i) =
          BooleanRingStr.is-set (snd (BN K')) _ _
            (ideal→zero K' gx) (ideal→zero K' gy) i
        -- Injectivity of fwd
        fwd-inj : (c₁ c₂ : SeqColim seqB)
          → fwd c₁ ≡ fwd c₂ → c₁ ≡ c₂
        fwd-inj = SeqColim→Prop (λ c₁ → isPropΠ λ c₂ → isPropΠ λ _ → isSetSC c₁ c₂)
          λ n₁ x₁ → SeqColim→Prop (λ c₂ → isPropΠ λ _ → isSetSC (incl x₁) c₂)
          λ n₂ x₂ eq →
          PT.rec2 (isSetSC _ _)
            (λ (a₁ , ea₁) (a₂ , ea₂) → let
              _+F_ = BooleanRingStr._+_ (snd (freeBA ℕ))
              _+Q_ = BooleanRingStr._+_ (snd Q)
              𝟘Q = BooleanRingStr.𝟘 (snd Q)
              ι₁a₁ = fst (ι-inc (M n₁)) a₁
              ι₂a₂ = fst (ι-inc (M n₂)) a₂
              d = ι₁a₁ +F ι₂a₂
              ev₁ : fst πQ ι₁a₁ ≡ fst (fwdHom n₁) x₁
              ev₁ = sym (funExt⁻ (cong fst (evalFwd n₁)) a₁)
                ∙ cong (fst (fwdHom n₁)) ea₁
              ev₂ : fst πQ ι₂a₂ ≡ fst (fwdHom n₂) x₂
              ev₂ = sym (funExt⁻ (cong fst (evalFwd n₂)) a₂)
                ∙ cong (fst (fwdHom n₂)) ea₂
              πQd≡0 : fst πQ d ≡ 𝟘Q
              πQd≡0 = IsCommRingHom.pres+ (snd πQ) ι₁a₁ ι₂a₂
                ∙ cong₂ _+Q_ ev₁ ev₂
                ∙ cong (_+Q fst (fwdHom n₂) x₂) eq
                ∙ BooleanAlgebraStr.characteristic2 Q
              d-in-I : IQ.generatedIdeal CR-ℕ f d
              d-in-I = QB.fromKernel {B = freeBA ℕ} {f = f} πQd≡0
              in PT.rec (isSetSC _ _)
                (λ (K , hK) → let
                  K' = suc (max (max n₁ n₂) K)
                  le-n₁ : n₁ ≤ K'
                  le-n₁ = ≤-trans (left-≤-max {n₁} {n₂})
                    (≤-trans (left-≤-max {max n₁ n₂} {K}) ≤-sucℕ)
                  le-n₂ : n₂ ≤ K'
                  le-n₂ = ≤-trans (right-≤-max {n₂} {n₁})
                    (≤-trans (left-≤-max {max n₁ n₂} {K}) ≤-sucℕ)
                  le-K : K ≤ K'
                  le-K = ≤-trans (right-≤-max {K} {max n₁ n₂}) ≤-sucℕ
                  sn₁≤K' : suc n₁ ≤ K'
                  sn₁≤K' = suc-≤-suc (≤-trans (left-≤-max {n₁} {n₂})
                    (left-≤-max {max n₁ n₂} {K}))
                  sn₂≤K' : suc n₂ ≤ K'
                  sn₂≤K' = suc-≤-suc (≤-trans (right-≤-max {n₂} {n₁})
                    (left-≤-max {max n₁ n₂} {K}))
                  -- Decompose ≤ proofs to get d' with suc d' + n ≡ K'
                  dec₁ = suc-le-decomp le-n₁ sn₁≤K'
                  dec₂ = suc-le-decomp le-n₂ sn₂≤K'
                  d₁' = fst dec₁; d₂' = fst dec₂
                  eq-level₁ : suc d₁' +ℕ n₁ ≡ K'
                  eq-level₁ = snd dec₁
                  eq-level₂ : suc d₂' +ℕ n₂ ≡ K'
                  eq-level₂ = snd dec₂
                  -- πBN K'(π-proj(d)) = πBN K'(π-proj(ι₁a₁)) + πBN K'(π-proj(ι₂a₂)) = 0
                  _+K'_ = BooleanRingStr._+_ (snd (BN K'))
                  πBN-split : πBN K' (fst (π-proj (M K')) ι₁a₁) +K'
                              πBN K' (fst (π-proj (M K')) ι₂a₂)
                              ≡ BooleanRingStr.𝟘 (snd (BN K'))
                  πBN-split =
                    sym (IsCommRingHom.pres+ (snd (QB.quotientImageHom
                      {B = freeBA (DF.Fin (M K'))} {f = relN K'})) _ _)
                    ∙ cong (πBN K') (sym (IsCommRingHom.pres+ (snd (π-proj (M K'))) ι₁a₁ ι₂a₂))
                    ∙ ideal→zero K' (hK K' le-K)
                  eq-at-K' : πBN K' (fst (π-proj (M K')) ι₁a₁)
                    ≡ πBN K' (fst (π-proj (M K')) ι₂a₂)
                  eq-at-K' = char2-eq {BN K'} _ _ πBN-split
                  in
                  incl x₁
                    ≡⟨ cong incl (sym ea₁) ⟩
                  incl (πBN n₁ a₁)
                    ≡⟨ push-to-πBN d₁' n₁ a₁ ⟩
                  incl (πBN (suc d₁' +ℕ n₁)
                    (fst (π-proj (M (suc d₁' +ℕ n₁))) (fst (ι-inc (M n₁)) a₁)))
                    ≡⟨ incl-level-eq n₁ eq-level₁ a₁ ⟩
                  incl (πBN K' (fst (π-proj (M K')) (fst (ι-inc (M n₁)) a₁)))
                    ≡⟨ cong incl eq-at-K' ⟩
                  incl (πBN K' (fst (π-proj (M K')) (fst (ι-inc (M n₂)) a₂)))
                    ≡⟨ sym (incl-level-eq n₂ eq-level₂ a₂) ⟩
                  incl (πBN (suc d₂' +ℕ n₂)
                    (fst (π-proj (M (suc d₂' +ℕ n₂))) (fst (ι-inc (M n₂)) a₂)))
                    ≡⟨ sym (push-to-πBN d₂' n₂ a₂) ⟩
                  incl (πBN n₂ a₂)
                    ≡⟨ cong incl ea₂ ⟩
                  incl x₂ ∎)
                (combined d-in-I))
            (QB.quotientImageHomSurjective {B = freeBA (DF.Fin (M n₁))} {f = relN n₁} x₁)
            (QB.quotientImageHomSurjective {B = freeBA (DF.Fin (M n₂))} {f = relN n₂} x₂)
        colimEquiv : SeqColim seqB ≃ ⟨ freeBA ℕ QB./Im f ⟩
        colimEquiv = fwd ,
          isEmbedding×isSurjection→isEquiv
            (injEmbedding (BooleanRingStr.is-set (snd Q))
              (λ {c₁} {c₂} → fwd-inj c₁ c₂) , fwd-surj)
  quotientFreeBA-isODisc : (f : ℕ → ⟨ freeBA ℕ ⟩) → isODisc ⟨ freeBA ℕ QB./Im f ⟩
  quotientFreeBA-isODisc f = PT.rec (isProp-isODisc _) extract (quotientFreeBA-ringDecomp f)
    where
    extract : ODiscRingDecomp (freeBA ℕ QB./Im f) → isODisc ⟨ freeBA ℕ QB./Im f ⟩
    extract rd = isODisc-equiv (ODiscRingDecomp.colimEquiv rd)
      ∣ ODiscRingDecomp.seqB rd , ODiscRingDecomp.isFinSetBN rd , idEquiv _ ∣₁
  -- tex Lemma 1396
  BooleIsODisc : (B : Booleω) → isODisc ⟨ fst B ⟩
  BooleIsODisc B = PT.rec (isProp-isODisc _) go (snd B) where
    go : has-Boole-ω' (fst B) → isODisc ⟨ fst B ⟩
    go (f , bEquiv) =
      isODisc-equiv (invEquiv (fst bEquiv)) (quotientFreeBA-isODisc f)
  -- Ring decomposition for a general Booleω algebra
  BooleωRingDecomp : (B : Booleω) → ∥ ODiscRingDecomp (fst B) ∥₁
  BooleωRingDecomp B = PT.rec squash₁ go (snd B) where
    go : has-Boole-ω' (fst B) → ∥ ODiscRingDecomp (fst B) ∥₁
    go (f , bEquiv) = PT.map transport-rd (quotientFreeBA-ringDecomp f)
      where
      Q = freeBA ℕ QB./Im f
      e⁻¹Hom : BoolHom Q (fst B)
      e⁻¹Hom = invEq (fst bEquiv) , isCommRingHomInv bEquiv
        where open import Cubical.Algebra.CommRing.Properties using (isCommRingHomInv)
      transport-rd : ODiscRingDecomp Q → ODiscRingDecomp (fst B)
      transport-rd rd = record
        { BN = ODiscRingDecomp.BN rd
        ; isFinSetBN = ODiscRingDecomp.isFinSetBN rd
        ; mapBN = ODiscRingDecomp.mapBN rd
        ; mapBNHom = ODiscRingDecomp.mapBNHom rd
        ; mapBN≡ = ODiscRingDecomp.mapBN≡ rd
        ; fwdHom = λ n → e⁻¹Hom ∘cr ODiscRingDecomp.fwdHom rd n
        ; fwd-compat = λ n x →
          fst e⁻¹Hom (fst (ODiscRingDecomp.fwdHom rd n) x)
            ≡⟨ cong (fst e⁻¹Hom) (ODiscRingDecomp.fwd-compat rd n x) ⟩
          fst e⁻¹Hom (fst (ODiscRingDecomp.fwdHom rd (suc n)) (ODiscRingDecomp.mapBN rd n x)) ∎
        ; colimEquiv = compEquiv (ODiscRingDecomp.colimEquiv rd) (invEquiv (fst bEquiv))
        ; colimEquiv-incl = λ n x →
          cong (invEq (fst bEquiv)) (ODiscRingDecomp.colimEquiv-incl rd n x)
        }
  -- Spectrum projection: Sp(B) → Sp(BN n) via fwdHom
  -- Given a ring decomposition, each stage BN(n) gives a finite approximation of |B|.
  -- The spectrum projection Sp(B) → Sp(BN n) is: φ ↦ φ ∘ fwdHom(n).
  -- Sp(BN n) is finite since BN n has finite carrier.
  open import Axioms.StoneDuality using (SpGeneralBooleanRing)
  SpProjection : {Q : BooleanRing ℓ-zero} (rd : ODiscRingDecomp Q) (n : ℕ)
    → SpGeneralBooleanRing Q → SpGeneralBooleanRing (ODiscRingDecomp.BN rd n)
  SpProjection rd n φ = φ ∘cr ODiscRingDecomp.fwdHom rd n
  -- tex Lemma 1558 (ScottFiniteCodomain):
  -- A BoolHom from a finite ring F to B factors through some stage BN(N).
  -- This gives: Sp(B) → Fin(k) factors through Sp(BN(N)) for some N.
  BoolHomFromFiniteFactors : {Q : BooleanRing ℓ-zero} (rd : ODiscRingDecomp Q)
    (F : BooleanRing ℓ-zero) (finF : isFinSet ⟨ F ⟩)
    (h : BoolHom F Q)
    → ∥ Σ[ N ∈ ℕ ] Σ[ g ∈ (⟨ F ⟩ → ⟨ ODiscRingDecomp.BN rd N ⟩) ]
        ((x : ⟨ F ⟩) → equivFun (ODiscRingDecomp.colimEquiv rd) (incl (g x))
                       ≡ fst h x) ∥₁
  BoolHomFromFiniteFactors rd F finF h =
    PT.map (λ (N , g , ok) → N , g , λ x →
      equivFun (ODiscRingDecomp.colimEquiv rd) (incl (g x))
        ≡⟨ cong (equivFun (ODiscRingDecomp.colimEquiv rd)) (ok x) ⟩
      equivFun (ODiscRingDecomp.colimEquiv rd)
        (invEq (ODiscRingDecomp.colimEquiv rd) (fst h x))
        ≡⟨ secEq (ODiscRingDecomp.colimEquiv rd) (fst h x) ⟩
      fst h x ∎)
    (colimCompact (ODiscRingDecomp.seqB rd) ⟨ F ⟩ finF
      (λ x → invEq (ODiscRingDecomp.colimEquiv rd) (fst h x)))

  -- Fiber of a DecompData map at level k
  -- Given dd : DecompData B C f with both B and C finite stages,
  -- the fiber of fMap k over s' is finite.
  module DecompFibers (B C : Sequence ℓ-zero)
      (finB : (k : ℕ) → isFinSet (obj B k))
      (finC : (k : ℕ) → isFinSet (obj C k))
      (f : SeqColim B → SeqColim C)
      (dd : DecompData B C f) where
    open DecompData dd
    open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
    open import Cubical.Data.FinSet.Properties using (isFinSet→Discrete)

    -- Fiber of fMap k over s' ∈ obj C (lvl k)
    DecompFiber : (k : ℕ) → obj C (lvl k) → Type ℓ-zero
    DecompFiber k s' = Σ[ e ∈ obj B k ] fMap k e ≡ s'

    -- Fibers are finite (fiber of map between finite sets)
    isFinSetDecompFiber : (k : ℕ) (s' : obj C (lvl k))
      → isFinSet (DecompFiber k s')
    isFinSetDecompFiber k s' =
      isFinSetFiber (_ , finB k) (_ , finC (lvl k)) (fMap k) s'
      where open import Cubical.Data.FinSet.Constructors using (isFinSetFiber)

  -- Sp(B) is finite when B has finite carrier
  -- SpGeneralBooleanRing B = BoolHom B BoolBR ⊂ (⟨B⟩ → Bool)
  -- The hom condition is a prop, and decidable over finite domain with discrete codomain.
  -- Hence BoolHom B BoolBR = Σ (⟨B⟩ → Bool) IsBoolRingHom is a subset of a finite set
  -- cut out by a decidable prop, hence finite.
  isFinSetSpFinRing : (B : BooleanRing ℓ-zero) → isFinSet ⟨ B ⟩
    → isFinSet (SpGeneralBooleanRing B)
  isFinSetSpFinRing B finB =
    isFinSetΣ (_ , isFinSet→ (_ , finB) (_ , isFinSetBool))
      (λ f → _ , isFinSetHomCond f)
    where
    open import Cubical.Data.FinSet.Constructors
      using (isFinSetΣ; isFinSet→; isFinSetΠ; isFinSetΠ2; isFinSet≡)
    open import Cubical.Data.FinSet.Properties using (isFinSetBool; EquivPresIsFinSet)
    open import Cubical.Data.FinSet.Base using (FinSet)
    open import Cubical.Algebra.CommRing.Base using (IsCommRingHom; IsCommRingHomIsoΣ)
    RS = BooleanRingStr→CommRingStr (snd B)
    SS = BooleanRingStr→CommRingStr (snd BoolBR)
    open CommRingStr RS renaming
      (0r to 0B; 1r to 1B; _+_ to _+B_; _·_ to _·B_; -_ to -B_)
    open CommRingStr SS renaming
      (0r to 0T; 1r to 1T; _+_ to _+T_; _·_ to _·T_; -_ to -T_)
    BFS = (_ , finB) -- ⟨ B ⟩ as FinSet
    BoolFS = (_ , isFinSetBool) -- Bool as FinSet
    isFinSetHomCond : (f : ⟨ B ⟩ → Bool) → isFinSet (IsCommRingHom RS f SS)
    isFinSetHomCond f = EquivPresIsFinSet (invEquiv (isoToEquiv IsCommRingHomIsoΣ)) finΣ where
      eq≡ : Bool → Bool → FinSet ℓ-zero
      eq≡ a b = (a ≡ b) , isFinSet≡ BoolFS a b
      F4 : FinSet ℓ-zero
      F4 = _ , isFinSetΠ BFS (λ x → eq≡ (f (-B x)) (-T (f x)))
      F3 : FinSet ℓ-zero
      F3 = _ , isFinSetΣ (_ , isFinSetΠ2 BFS (λ _ → BFS)
               (λ x y → eq≡ (f (x ·B y)) (f x ·T f y))) (λ _ → F4)
      F2 : FinSet ℓ-zero
      F2 = _ , isFinSetΣ (_ , isFinSetΠ2 BFS (λ _ → BFS)
               (λ x y → eq≡ (f (x +B y)) (f x +T f y))) (λ _ → F3)
      F1 : FinSet ℓ-zero
      F1 = _ , isFinSetΣ (eq≡ (f 1B) 1T) (λ _ → F2)
      finΣ : isFinSet _
      finΣ = isFinSetΣ (eq≡ (f 0B) 0T) (λ _ → F1)

  -- Finite partition of Stone space by finitely many elements
  -- Given B : Booleω and d : Fin k → ⟨ fst B ⟩, the map
  -- Sp(B) → (Fin k → Bool) given by h ↦ (i ↦ fst h (d i))
  -- partitions Sp(B) into ≤ 2^k clopen parts.
  StoneFinitePartition : (B : Booleω) (k : ℕ) (d : Fin k → ⟨ fst B ⟩)
    → Sp B → (Fin k → Bool)
  StoneFinitePartition B k d h i = fst h (d i)

  isFinSet-BoolFin : (k : ℕ) → isFinSet (Fin k → Bool)
  isFinSet-BoolFin k = isFinSet→ (_ , isFinSetFin) (_ , isFinSetBool)
    where open import Cubical.Data.FinSet.Constructors using (isFinSet→)

  -- tex Lemma 1558 (ScottFiniteCodomain):
  -- Functions from Sp(B) to a finite set factor through some SpProjection level.
  -- Proof: SDHomVersion converts f into finitely many ring elements,
  -- colimCompact factors them through level N, colimEquiv-incl connects to SpProjection.
  ScottFiniteCodomain : (B : Booleω) (rd : ODiscRingDecomp (fst B))
    (F : Type ℓ-zero) (finF : isFinSet F) (isSetF : isSet F)
    → (f : Sp B → F)
    → ∥ Σ[ N ∈ ℕ ] Σ[ f' ∈ (SpGeneralBooleanRing (ODiscRingDecomp.BN rd N) → F) ]
        ((x : Sp B) → f x ≡ f' (SpProjection rd N x)) ∥₁
  ScottFiniteCodomain B rd F finF isSetF f = PT.rec2 squash₁ go (snd finF) step1 where
    open ODiscRingDecomp rd
    open SDDecToElemModule
    open import Cubical.Data.FinSet.Properties using (isFinSet→Discrete)
    open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
    open import Cubical.Data.Bool using (true≢false)
    Q = fst B
    k = fst finF
    discF : (a b : F) → Dec (a ≡ b)
    discF = isFinSet→Discrete finF
    D : F → Sp B → Bool
    D c φ = Dec→Bool (discF (f φ) c)
    e : F → ⟨ Q ⟩
    e c = elemFromDecPred sd-axiom B (D c)
    e-ok : (c : F) (φ : Sp B) → fst φ (e c) ≡ D c φ
    e-ok c = decPred-elem-correspondence sd-axiom B (D c)
    e-in-colim : F → SeqColim seqB
    e-in-colim c = invEq colimEquiv (e c)
    step1 : ∥ Σ[ N ∈ ℕ ] Σ[ d ∈ (F → ⟨ BN N ⟩) ]
              ((c : F) → incl (d c) ≡ e-in-colim c) ∥₁
    step1 = colimCompact seqB F finF e-in-colim
    D-true→eq : (φ : Sp B) (c : F) → D c φ ≡ true → f φ ≡ c
    D-true→eq φ c h with discF (f φ) c
    ... | yes p = p
    ... | no _ = ex-falso (true≢false (sym h))
    D-self : (φ : Sp B) → D (f φ) φ ≡ true
    D-self φ with discF (f φ) (f φ)
    ... | yes _ = refl
    ... | no ¬p = ex-falso (¬p refl)
    -- Finite search: find first element where P is true, or return default.
    -- Defined via Bool case-split helper for transparency in proofs.
    caseBool : {A : Type ℓ-zero} → Bool → A → A → A
    caseBool true  x _ = x
    caseBool false _ y = y
    finSearch : {A : Type ℓ-zero} (n : ℕ) (enum : Fin n → A) (P : A → Bool) → A → A
    finSearch zero _ _ def = def
    finSearch (suc n) enum P def =
      caseBool (P (enum fzero)) (enum fzero) (finSearch n (enum ∘ fsuc) P def)
    -- Correctness: if some j has P(enum j) = true, then P(finSearch ...) = true.
    -- Proof: case-split on P(enum fzero) as a Bool value.
    finSearch-ok : {A : Type ℓ-zero} (n : ℕ) (enum : Fin n → A) (P : A → Bool) (def : A)
      → Σ[ j ∈ Fin n ] P (enum j) ≡ true
      → P (finSearch n enum P def) ≡ true
    finSearch-ok zero _ _ _ (j , _) = ex-falso j
    finSearch-ok {A} (suc n) enum P def wit =
      helper (P (enum fzero)) refl where
      helper : (b : Bool) → P (enum fzero) ≡ b
        → P (caseBool b (enum fzero) (finSearch n (enum ∘ fsuc) P def)) ≡ true
      helper true p = p
      helper false p = finSearch-ok n (enum ∘ fsuc) P def (shrink wit p) where
        shrink : Σ[ j ∈ Fin (suc n) ] P (enum j) ≡ true → P (enum fzero) ≡ false
          → Σ[ j ∈ Fin n ] P (enum (fsuc j)) ≡ true
        shrink (fzero , h) q = ex-falso (true≢false (sym h ∙ q))
        shrink (fsuc j , h) _ = j , h
    -- Helper: iterMap on seqB preserves 0
    iterMap-pres0 : (d n : ℕ)
      → ColimCompactHelpers.iterMap seqB d (BooleanRingStr.𝟘 (snd (BN n)))
        ≡ BooleanRingStr.𝟘 (snd (BN (d +ℕ n)))
    iterMap-pres0 zero n = refl
    iterMap-pres0 (suc d) n =
      cong (mapBN (d +ℕ n)) (iterMap-pres0 d n)
      ∙ funExt⁻ (mapBN≡ (d +ℕ n)) (BooleanRingStr.𝟘 (snd (BN (d +ℕ n))))
      ∙ IsCommRingHom.pres0 (snd (mapBNHom (d +ℕ n)))
    -- Helper: iterMap on seqB preserves 1
    iterMap-pres1 : (d n : ℕ)
      → ColimCompactHelpers.iterMap seqB d (BooleanRingStr.𝟙 (snd (BN n)))
        ≡ BooleanRingStr.𝟙 (snd (BN (d +ℕ n)))
    iterMap-pres1 zero n = refl
    iterMap-pres1 (suc d) n =
      cong (mapBN (d +ℕ n)) (iterMap-pres1 d n)
      ∙ funExt⁻ (mapBN≡ (d +ℕ n)) (BooleanRingStr.𝟙 (snd (BN (d +ℕ n))))
      ∙ IsCommRingHom.pres1 (snd (mapBNHom (d +ℕ n)))
    -- Helper: liftTo on seqB preserves 0
    open ColimCompactHelpers seqB using (liftTo)
    liftTo-pres0 : {n N : ℕ} (le : n ≤ N)
      → liftTo le (BooleanRingStr.𝟘 (snd (BN n))) ≡ BooleanRingStr.𝟘 (snd (BN N))
    liftTo-pres0 {n} (d , p) = J (λ N' p' → subst (obj seqB) p' (ColimCompactHelpers.iterMap seqB d (BooleanRingStr.𝟘 (snd (BN n))))
        ≡ BooleanRingStr.𝟘 (snd (BN N')))
      (transportRefl _ ∙ iterMap-pres0 d n) p
    -- Helper: liftTo on seqB preserves 1
    liftTo-pres1 : {n N : ℕ} (le : n ≤ N)
      → liftTo le (BooleanRingStr.𝟙 (snd (BN n))) ≡ BooleanRingStr.𝟙 (snd (BN N))
    liftTo-pres1 {n} (d , p) = J (λ N' p' → subst (obj seqB) p' (ColimCompactHelpers.iterMap seqB d (BooleanRingStr.𝟙 (snd (BN n))))
        ≡ BooleanRingStr.𝟙 (snd (BN N')))
      (transportRefl _ ∙ iterMap-pres1 d n) p
    go : F ≃ Fin k
       → Σ[ N ∈ ℕ ] Σ[ d ∈ (F → ⟨ BN N ⟩) ] ((c : F) → incl (d c) ≡ e-in-colim c)
       → ∥ Σ[ N ∈ ℕ ] Σ[ f' ∈ (SpGeneralBooleanRing (BN N) → F) ]
           ((x : Sp B) → f x ≡ f' (SpProjection rd N x)) ∥₁
    go eq (N , d , d-ok) = go-inner k eq N d d-ok where
      go-inner : (k' : ℕ) → F ≃ Fin k' → (N : ℕ) → (d : F → ⟨ BN N ⟩)
        → ((c : F) → incl (d c) ≡ e-in-colim c)
        → ∥ Σ[ N ∈ ℕ ] Σ[ f' ∈ (SpGeneralBooleanRing (BN N) → F) ]
            ((x : Sp B) → f x ≡ f' (SpProjection rd N x)) ∥₁
      -- k' = 0: F ≃ Fin 0 = ⊥, so Sp B is empty, find level where 0=1 in BN
      go-inner zero eq₀ N₀ _ _ = PT.rec squash₁ handle sep where
        spEmpty : Sp B → ⊥
        spEmpty φ = equivFun eq₀ (f φ)
        open BooleanRingStr (snd (fst B)) renaming (𝟘 to 𝟘Q ; 𝟙 to 𝟙Q)
        0≡1-Q : 𝟘Q ≡ 𝟙Q
        0≡1-Q = SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B (λ φ → ex-falso (spEmpty φ))
        fwd-eq : equivFun colimEquiv (incl (BooleanRingStr.𝟘 (snd (BN 0))))
               ≡ equivFun colimEquiv (incl (BooleanRingStr.𝟙 (snd (BN 0))))
        fwd-eq =
          equivFun colimEquiv (incl (BooleanRingStr.𝟘 (snd (BN 0))))
            ≡⟨ colimEquiv-incl 0 _ ⟩
          fst (fwdHom 0) (BooleanRingStr.𝟘 (snd (BN 0)))
            ≡⟨ IsCommRingHom.pres0 (snd (fwdHom 0)) ⟩
          𝟘Q ≡⟨ 0≡1-Q ⟩
          𝟙Q
            ≡⟨ sym (IsCommRingHom.pres1 (snd (fwdHom 0))) ⟩
          fst (fwdHom 0) (BooleanRingStr.𝟙 (snd (BN 0)))
            ≡⟨ sym (colimEquiv-incl 0 _) ⟩
          equivFun colimEquiv (incl (BooleanRingStr.𝟙 (snd (BN 0)))) ∎
        incl0≡incl1 : Path (SeqColim seqB) (incl (BooleanRingStr.𝟘 (snd (BN 0)))) (incl (BooleanRingStr.𝟙 (snd (BN 0))))
        incl0≡incl1 = sym (retEq colimEquiv _) ∙ cong (invEq colimEquiv) fwd-eq ∙ retEq colimEquiv _
        setStages : (n : ℕ) → isSet (obj seqB n)
        setStages n = isFinSet→isSet (isFinSetBN n)
        sep : ∥ Σ[ M ∈ ℕ ] Σ[ le₁ ∈ 0 ≤ M ] Σ[ le₂ ∈ 0 ≤ M ]
              (liftTo le₁ (BooleanRingStr.𝟘 (snd (BN 0))) ≡ liftTo le₂ (BooleanRingStr.𝟙 (snd (BN 0)))) ∥₁
        sep = ColimSep.colimSeparation seqB setStages _ _ incl0≡incl1
        handle : Σ[ M ∈ ℕ ] Σ[ le₁ ∈ 0 ≤ M ] Σ[ le₂ ∈ 0 ≤ M ]
              (liftTo le₁ (BooleanRingStr.𝟘 (snd (BN 0))) ≡ liftTo le₂ (BooleanRingStr.𝟙 (snd (BN 0))))
          → ∥ Σ[ N ∈ ℕ ] Σ[ f' ∈ (SpGeneralBooleanRing (BN N) → F) ]
              ((x : Sp B) → f x ≡ f' (SpProjection rd N x)) ∥₁
        handle (M , le₁ , le₂ , p) = ∣ M , f'₀ , (λ x → ex-falso (spEmpty x)) ∣₁ where
          0≡1-BNM : BooleanRingStr.𝟘 (snd (BN M)) ≡ BooleanRingStr.𝟙 (snd (BN M))
          0≡1-BNM = sym (liftTo-pres0 le₁) ∙ p ∙ liftTo-pres1 le₂
          ¬SpBNM : SpGeneralBooleanRing (BN M) → ⊥
          ¬SpBNM ψ = true≢false (sym (IsCommRingHom.pres1 (snd ψ))
            ∙ cong (fst ψ) (sym 0≡1-BNM) ∙ IsCommRingHom.pres0 (snd ψ))
          f'₀ : SpGeneralBooleanRing (BN M) → F
          f'₀ ψ = ex-falso (¬SpBNM ψ)
      -- k' ≥ 1: use invEq eq fzero as default for finSearch
      go-inner (suc k') eq₊ N₀ d d-ok = ∣ N₀ , f'₀ , f-ok ∣₁ where
        defF : F
        defF = invEq eq₊ fzero
        fwd-d : (c : F) → fst (fwdHom N₀) (d c) ≡ e c
        fwd-d c =
          fst (fwdHom N₀) (d c)
            ≡⟨ sym (colimEquiv-incl N₀ (d c)) ⟩
          equivFun colimEquiv (incl (d c))
            ≡⟨ cong (equivFun colimEquiv) (d-ok c) ⟩
          equivFun colimEquiv (e-in-colim c)
            ≡⟨ secEq colimEquiv (e c) ⟩
          e c ∎
        sp-d : (c : F) (φ : Sp B) → fst (SpProjection rd N₀ φ) (d c) ≡ D c φ
        sp-d c φ =
          fst (SpProjection rd N₀ φ) (d c)
            ≡⟨ cong (fst φ) (fwd-d c) ⟩
          fst φ (e c)
            ≡⟨ e-ok c φ ⟩
          D c φ ∎
        f'₀ : SpGeneralBooleanRing (BN N₀) → F
        f'₀ ψ = finSearch (suc k') (invEq eq₊) (λ c → fst ψ (d c)) defF
        f-ok : (x : Sp B) → f x ≡ f'₀ (SpProjection rd N₀ x)
        f-ok φ = D-true→eq φ (f'₀ ψ) sp-d-result where
          ψ = SpProjection rd N₀ φ
          P = λ c → fst ψ (d c)
          wit : Σ[ j ∈ Fin (suc k') ] P (invEq eq₊ j) ≡ true
          wit = equivFun eq₊ (f φ)
              , (P (invEq eq₊ (equivFun eq₊ (f φ)))
                  ≡⟨ cong (λ c → fst ψ (d c)) (retEq eq₊ (f φ)) ⟩
                 fst ψ (d (f φ))
                  ≡⟨ sp-d (f φ) φ ⟩
                 D (f φ) φ
                  ≡⟨ D-self φ ⟩
                 true ∎)
          search-ok : P (f'₀ ψ) ≡ true
          search-ok = finSearch-ok (suc k') (invEq eq₊) P defF wit
          sp-d-result : D (f'₀ ψ) φ ≡ true
          sp-d-result =
            D (f'₀ ψ) φ
              ≡⟨ sym (sp-d (f'₀ ψ) φ) ⟩
            P (f'₀ ψ)
              ≡⟨ search-ok ⟩
            true ∎
  -- tex Lemma 1568 (MapsStoneToNareBounded):
  -- Proved in Part09 (MapsStoneToNareBoundedModule) using Stone interface.

  -- tex Lemma 1184
  OdiscSigma : {A : Type ℓ-zero} {B : A → Type ℓ-zero}
    → isODisc A → ((a : A) → isODisc (B a)) → isODisc (Σ A B)
  OdiscSigma {A} {B} odiscA odiscB = PT.rec squash₁ go odiscA where
    go : Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A)
       → isODisc (Σ A B)
    go (SA , finSA , eA) = isODisc-equiv Σ-total-equiv sigmaODisc where
      open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
      open import Cubical.Foundations.Transport using (transportTransport⁻)
      B' : SeqColim SA → Type ℓ-zero
      B' c = B (equivFun eA c)
      ΣSA : Sequence ℓ-zero
      obj ΣSA n = Σ (obj SA n) (λ x → B' (incl x))
      map ΣSA (x , b) = map SA x , subst B' (push x) b
      levelODisc : (n : ℕ) → isODisc (obj ΣSA n)
      levelODisc n = finΣ-ODisc (finSA n) (λ x → odiscB (equivFun eA (incl x)))
      sigmaODisc : isODisc (SeqColim ΣSA)
      sigmaODisc = ODiscColimOfODisc ΣSA levelODisc
      -- Σ-colimit commutativity: SeqColim ΣSA ≃ Σ (SeqColim SA) B'
      isSetSA : isSet (SeqColim SA)
      isSetSA = isSetSeqColimOfSets SA (λ n → isFinSet→isSet (finSA n))
      isSetB' : (c : SeqColim SA) → isSet (B' c)
      isSetB' c = isODiscIsSet (odiscB (equivFun eA c))
      fwd : SeqColim ΣSA → Σ (SeqColim SA) B'
      fwd (incl (x , b)) = incl x , b
      fwd (push (x , b) i) = push x i , subst-filler B' (push x) b i
      bwd : Σ (SeqColim SA) B' → SeqColim ΣSA
      bwd (incl x , b) = incl (x , b)
      bwd (push {n = n} x i , b) =
        hcomp (λ j → λ { (i = i0) → incl {n = n} (x , b)
                        ; (i = i1) → incl {n = suc n} (map SA x ,
                            transportTransport⁻ (cong B' (push x)) b j) })
              (push {n = n} (x , b₀) i)
        where
          b₀ : B' (incl x)
          b₀ = transp (λ j → B' (push x (i ∧ ~ j))) (~ i) b
      isSetTarget : isSet (Σ (SeqColim SA) B')
      isSetTarget = isSetΣ isSetSA isSetB'
      isPropΠ' : {X : Type ℓ-zero} {Y : X → Type ℓ-zero}
        → ((a : X) → isProp (Y a)) → isProp ((a : X) → Y a)
      isPropΠ' h f g i a = h a (f a) (g a) i
      sec : (p : Σ (SeqColim SA) B') → fwd (bwd p) ≡ p
      sec (incl x , b) = refl
      sec (push {n = n} x i , b) = lemma i b where
        lemma : PathP (λ i → (b : B' (push x i)) → fwd (bwd (push x i , b)) ≡ (push x i , b))
                      (λ b → refl) (λ b → refl)
        lemma = isProp→PathP
          (λ j → isPropΠ' (λ b → isSetTarget (fwd (bwd (push x j , b))) (push x j , b)))
          (λ b → refl) (λ b → refl)
      isSetΣSAColim : isSet (SeqColim ΣSA)
      isSetΣSAColim = isSetSeqColimOfSets ΣSA (λ n →
        isSetΣ (isFinSet→isSet (finSA n))
               (λ x → isODiscIsSet (odiscB (equivFun eA (incl x)))))
      ret : (c : SeqColim ΣSA) → bwd (fwd c) ≡ c
      ret (incl _) = refl
      ret (push {n = n} (x , b) i) =
        isProp→PathP (λ j → isSetΣSAColim (bwd (fwd (push (x , b) j))) (push (x , b) j))
          refl refl i
      Σ-colim-equiv : SeqColim ΣSA ≃ Σ (SeqColim SA) B'
      Σ-colim-equiv = isoToEquiv (iso fwd bwd sec ret)
      Σ-total-equiv : SeqColim ΣSA ≃ Σ A B
      Σ-total-equiv = compEquiv Σ-colim-equiv (Σ-cong-equiv-fst eA)
  -- tex Lemma 1302 (forward: open prop is ODisc)
  PropOpenIffOdisc : (P : hProp ℓ-zero) → isOpenProp P → isODisc (fst P)
  PropOpenIffOdisc P = PT.rec (isProp-isODisc _) go where
    go : isOpenWitness P → isODisc (fst P)
    go (α , P→Σ , Σ→P) = ∣ S , fin , isoToEquiv (iso fwd bwd sec ret) ∣₁ where
      anyTrue : ℕ → Bool
      anyTrue zero = α zero
      anyTrue (suc n) = α (suc n) or anyTrue n
      anyTrue-mono : (n : ℕ) → anyTrue n ≡ true → anyTrue (suc n) ≡ true
      anyTrue-mono n p with α (suc n)
      ... | true = refl
      ... | false = p
      α-true→anyTrue : (k : ℕ) → α k ≡ true → anyTrue k ≡ true
      α-true→anyTrue zero p = p
      α-true→anyTrue (suc k) p = cong (_or anyTrue k) p
      S : Sequence ℓ-zero
      obj S n = anyTrue n ≡ true
      map S {n} = anyTrue-mono n
      fin : (n : ℕ) → isFinSet (obj S n)
      fin n = isDecProp→isFinSet (isSetBool _ _) (anyTrue n ≟ true)
      extractWitness : (n : ℕ) → anyTrue n ≡ true → Σ[ k ∈ ℕ ] α k ≡ true
      extractWitness zero p = zero , p
      extractWitness (suc n) = extract-suc (α (suc n)) refl where
        extract-suc : (b : Bool) → b ≡ α (suc n) → b or anyTrue n ≡ true → Σ[ k ∈ ℕ ] α k ≡ true
        extract-suc true eq _ = suc n , sym eq
        extract-suc false _ p = extractWitness n p
      fwd : SeqColim S → fst P
      fwd = SeqColim→Prop (λ _ → snd P) (λ n p → Σ→P (extractWitness n p))
      bwd : fst P → SeqColim S
      bwd x = let (k , αk) = P→Σ x in incl {n = k} (α-true→anyTrue k αk)
      sec : (x : fst P) → fwd (bwd x) ≡ x
      sec x = snd P _ x
      ret : (c : SeqColim S) → bwd (fwd c) ≡ c
      ret c = isPropSeqColimProp S (λ n → isSetBool _ _) _ c
  -- tex Lemma 1184 (propositional truncation): ∥ A ∥₁ of ODisc is ODisc
  OdiscTrunc : {A : Type ℓ-zero} → isODisc A → isODisc ∥ A ∥₁
  OdiscTrunc {A} odiscA = PropOpenIffOdisc (∥ A ∥₁ , squash₁) trunc-open where
    trunc-open : isOpenProp (∥ A ∥₁ , squash₁)
    trunc-open = PT.rec squash₁ go odiscA where
      go : Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A)
         → isOpenProp (∥ A ∥₁ , squash₁)
      go (S , finS , equiv) = openEquiv Q (∥ A ∥₁ , squash₁) Q→T T→Q Q-open where
        Q : hProp ℓ-zero
        Q = ∥ Σ[ n ∈ ℕ ] ∥ obj S n ∥₁ ∥₁ , squash₁
        T→Q : ∥ A ∥₁ → fst Q
        T→Q = PT.rec squash₁ λ a →
          SeqColim→Prop (λ _ → squash₁) (λ n x → ∣ n , ∣ x ∣₁ ∣₁) (invEq equiv a)
        Q→T : fst Q → ∥ A ∥₁
        Q→T = PT.rec squash₁ λ (n , hn) →
          PT.rec squash₁ (λ x → ∣ equivFun equiv (incl x) ∣₁) hn
        Q-open : isOpenProp Q
        Q-open = openCountableUnion (λ n → ∥ obj S n ∥₁ , squash₁)
                   (λ n → decIsOpen (∥ obj S n ∥₁ , squash₁) (isFinSet→Dec∥∥ (finS n)))
  -- tex Lemma 1302 (converse direction: ODisc proposition is open)
  ODiscPropIsOpen : (P : hProp ℓ-zero) → isODisc (fst P) → isOpenProp P
  ODiscPropIsOpen P = PT.rec squash₁ go where
    go : Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ fst P) → isOpenProp P
    go (S , finS , equiv) = openEquiv Q P Q→P P→Q Q-open where
      Q : hProp ℓ-zero
      Q = ∥ Σ[ n ∈ ℕ ] ∥ obj S n ∥₁ ∥₁ , squash₁
      P→Q : fst P → fst Q
      P→Q p = SeqColim→Prop (λ _ → squash₁) (λ n x → ∣ n , ∣ x ∣₁ ∣₁) (invEq equiv p)
      Q→P : fst Q → fst P
      Q→P = PT.rec (snd P) λ (n , hn) → PT.rec (snd P) (λ x → equivFun equiv (incl x)) hn
      Q-open : isOpenProp Q
      Q-open = openCountableUnion (λ n → ∥ obj S n ∥₁ , squash₁)
                 (λ n → decIsOpen (∥ obj S n ∥₁ , squash₁) (isFinSet→Dec∥∥ (finS n)))
  -- Derived from definition: ODisc types have surjection from ℕ (when inhabited)
  private
    fromℕ-toℕ : {k : ℕ} (x : Fin (suc k)) → fromℕ {k = k} (toℕ x) ≡ x
    fromℕ-toℕ {zero} fzero = refl
    fromℕ-toℕ {suc k} fzero = refl
    fromℕ-toℕ {suc k} (fsuc x) = cong fsuc (fromℕ-toℕ x)
  ODiscSurjFromN : {A : Type ℓ-zero} → isODisc A → ∥ A ∥₁
    → ∥ Σ[ e ∈ (ℕ → A) ] ((a : A) → ∥ Σ[ n ∈ ℕ ] e n ≡ a ∥₁) ∥₁
  ODiscSurjFromN {A} odiscA inhA = PT.rec2 squash₁ go odiscA inhA where
    go : Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A)
       → A → ∥ Σ[ e ∈ (ℕ → A) ] ((a : A) → ∥ Σ[ n ∈ ℕ ] e n ≡ a ∥₁) ∥₁
    go (S , finS , equiv) a₀ =
      PT.rec squash₁ go₂ (countableChoice _ (λ n → snd (finS n)))
      where
      go₂ : ((n : ℕ) → obj S n ≃ Fin (fst (finS n)))
           → ∥ Σ[ e ∈ (ℕ → A) ] ((a : A) → ∥ Σ[ n ∈ ℕ ] e n ≡ a ∥₁) ∥₁
      go₂ equivs = ∣ enum , surj ∣₁ where
        lookupFin : (n : ℕ) (k : ℕ) → obj S n ≃ Fin k → ℕ → A
        lookupFin _ zero _ _ = a₀
        lookupFin n (suc k) eq j = equivFun equiv (incl (invEq eq (fromℕ j)))
        enumPair : ℕ × ℕ → A
        enumPair (n , j) = lookupFin n (fst (finS n)) (equivs n) j
        enum : ℕ → A
        enum m = enumPair (Iso.inv ℕ×ℕ≅ℕ m)
        lookupFin-hit : (n : ℕ) (x : obj S n) →
          lookupFin n (fst (finS n)) (equivs n) (toℕ (equivFun (equivs n) x))
          ≡ equivFun equiv (incl x)
        lookupFin-hit n x with fst (finS n) | equivs n
        ... | zero  | eq = ⊥-rec (equivFun eq x)
        ... | suc k | eq =
          equivFun equiv (incl (invEq eq (fromℕ (toℕ (equivFun eq x)))))
            ≡⟨ cong (λ f → equivFun equiv (incl (invEq eq f))) (fromℕ-toℕ (equivFun eq x)) ⟩
          equivFun equiv (incl (invEq eq (equivFun eq x)))
            ≡⟨ cong (λ y → equivFun equiv (incl y)) (retEq eq x) ⟩
          equivFun equiv (incl x) ∎
        liftToLevel : (c : SeqColim S) → ∥ Σ[ n ∈ ℕ ] Σ[ x ∈ obj S n ] incl x ≡ c ∥₁
        liftToLevel = SeqColim→Prop (λ _ → squash₁) (λ n x → ∣ n , x , refl ∣₁)
        surj : (a : A) → ∥ Σ[ m ∈ ℕ ] enum m ≡ a ∥₁
        surj a = PT.rec squash₁ go₃ (liftToLevel (invEq equiv a)) where
          go₃ : Σ[ n ∈ ℕ ] Σ[ x ∈ obj S n ] incl x ≡ invEq equiv a
              → ∥ Σ[ m ∈ ℕ ] enum m ≡ a ∥₁
          go₃ (n , x , p) = ∣ Iso.fun ℕ×ℕ≅ℕ (n , toℕ fx) , path ∣₁ where
            fx = equivFun (equivs n) x
            path : enum (Iso.fun ℕ×ℕ≅ℕ (n , toℕ fx)) ≡ a
            path =
              enumPair (Iso.inv ℕ×ℕ≅ℕ (Iso.fun ℕ×ℕ≅ℕ (n , toℕ fx)))
                ≡⟨ cong enumPair (Iso.ret ℕ×ℕ≅ℕ (n , toℕ fx)) ⟩
              lookupFin n (fst (finS n)) (equivs n) (toℕ fx)
                ≡⟨ lookupFin-hit n x ⟩
              equivFun equiv (incl x)
                ≡⟨ cong (equivFun equiv) p ⟩
              equivFun equiv (invEq equiv a)
                ≡⟨ secEq equiv a ⟩
              a ∎
  -- tex Lemma 1184 (identity types): path types of ODisc types are ODisc
  OdiscPath : {A : Type ℓ-zero} → isODisc A → (a b : A) → isODisc (a ≡ b)
  OdiscPath {A} odiscA a b = PT.rec (isProp-isODisc _) go odiscA where
    open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
    open import Cubical.Data.Nat.Properties using (+-comm)
    go : Σ[ S ∈ Sequence ℓ-zero ] ((n : ℕ) → isFinSet (obj S n)) × (SeqColim S ≃ A) → isODisc (a ≡ b)
    go (S , finS , equiv) = PropOpenIffOdisc ab-hp (openEquiv sc-hp ab-hp sc→ab ab→sc sc-open) where
      allSetS = λ n → isFinSet→isSet (finS n)
      isSetSC = isSetSeqColimOfSets S allSetS
      isSetA = isOfHLevelRespectEquiv 2 equiv isSetSC
      ab-hp : hProp ℓ-zero
      ab-hp = (a ≡ b) , isSetA a b
      c₁ = invEq equiv a ; c₂ = invEq equiv b
      sc-hp : hProp ℓ-zero
      sc-hp = (c₁ ≡ c₂) , isSetSC c₁ c₂
      sc→ab : c₁ ≡ c₂ → a ≡ b
      sc→ab p = sym (secEq equiv a) ∙ cong (equivFun equiv) p ∙ secEq equiv b
      ab→sc = cong (invEq equiv)
      open SCSet S allSetS
      inclS : {n : ℕ} → obj S n → SeqColim S
      inclS = incl
      incl-tr : {n' m' : ℕ} (p : n' ≡ m') (x : obj S n')
        → Path (SeqColim S) (inclS x) (inclS (subst (obj S) p x))
      incl-tr {n'} = J (λ m' p → (x : obj S n') → inclS x ≡ inclS (subst (obj S) p x))
        λ x → cong inclS (sym (transportRefl x))
      oii : (n₁ : ℕ) (x₁ : obj S n₁) (n₂ : ℕ) (x₂ : obj S n₂)
          → isOpenProp ((incl x₁ ≡ incl x₂) , isSetSC (incl x₁) (incl x₂))
      oii n₁ x₁ n₂ x₂ = openEquiv (∥ Σ[ j ∈ ℕ ] fst (Pj j) ∥₁ , squash₁)
            ((incl x₁ ≡ incl x₂) , isSetSC _ _) bwd fwd union-open where
        N = n₁ +ℕ n₂
        a₀ = subst (obj S) (+-comm n₂ n₁) (sh n₂ x₁)
        b₀ = sh n₁ x₂
        open EncDec {n₀ = N} a₀
        Pj : (j : ℕ) → hProp ℓ-zero
        Pj j = (sh j a₀ ≡ sh j b₀) , allSetS (j +ℕ N) _ _
        union-open = openCountableUnion Pj
          (λ j → decIsOpen (Pj j) (isFinSet→Discrete (finS (j +ℕ N)) (sh j a₀) (sh j b₀)))
        fwd : incl x₁ ≡ incl x₂ → ∥ Σ[ j ∈ ℕ ] fst (Pj j) ∥₁
        fwd p = SeqColim→Prop {C = pathSeq {0} b₀} {B = λ _ → ∥ Σ[ j ∈ ℕ ] fst (Pj j) ∥₁}
          (λ _ → squash₁) (λ j eq → ∣ j , eq ∣₁)
          (transport (codeβ {0} b₀) (encode (incl b₀)
            (sym (incl-tr (+-comm n₂ n₁) (sh n₂ x₁)) ∙ sym (pc n₂ x₁) ∙ p ∙ pc n₁ x₂)))
        bwd : ∥ Σ[ j ∈ ℕ ] fst (Pj j) ∥₁ → incl x₁ ≡ incl x₂
        bwd = PT.rec (isSetSC _ _) λ (j , eq) →
          pc n₂ x₁ ∙ incl-tr (+-comm n₂ n₁) (sh n₂ x₁)
          ∙ pc j a₀ ∙ cong incl eq ∙ sym (pc j b₀) ∙ sym (pc n₁ x₂)
      sc-open : isOpenProp sc-hp
      sc-open = SeqColim→Prop
        {B = λ c → (c' : SeqColim S) → isOpenProp ((c ≡ c') , isSetSC c c')}
        (λ c → isPropΠ λ _ → squash₁)
        (λ n₁ x₁ → SeqColim→Prop (λ _ → squash₁) (λ n₂ x₂ → oii n₁ x₁ n₂ x₂))
        c₁ c₂
  -- tex Lemma 1160: ODisc stable under countable coproducts
  -- Proof: anti-diagonal construction. Given Sn with finite levels and SeqColim(Sn) ≃ A(n),
  -- build diagonal sequence T where T(k) = Σ[n≤k] obj(Sn(n))(k-n), show SeqColim T ≃ Σ ℕ A.
  ODiscClosedUnderSequentialColimits : {A : ℕ → Type ℓ-zero}
    → ((n : ℕ) → isODisc (A n)) → isODisc (Σ ℕ A)
  ODiscClosedUnderSequentialColimits {A} odiscAll =
    PT.rec squash₁ go (countableChoice _ (λ n → isODisc→FinSeqData (odiscAll n)))
   where
    open import Cubical.Foundations.Transport using (substCommSlice; substComposite)
    open import Cubical.Data.Nat using (isSetℕ)
    open import Cubical.Data.Nat.Properties using (+∸)
    open import Cubical.Data.Nat.Order using (_≤_; isProp≤; ≤-refl; ≤-suc; zero-≤; suc-≤-suc; pred-≤-pred; ¬-<-zero; ≤SumRight; ≤-∸-suc; ≤-∸-+-cancel)
    open import Cubical.Data.FinSet.Constructors using (isFinSetΣ)
    open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
    -- Fin-encoded sequence (lives at ℓ-zero, avoids universe issue with countableChoice)
    mkFinSeq : (sz : ℕ → ℕ) → ((m : ℕ) → Fin (sz m) → Fin (sz (suc m))) → Sequence ℓ-zero
    obj (mkFinSeq sz fmp) m = Fin (sz m)
    map (mkFinSeq sz fmp) = fmp _
    FinSeqData : Type ℓ-zero → Type ℓ-zero
    FinSeqData B = Σ[ sz ∈ (ℕ → ℕ) ]
      Σ[ fmp ∈ ((m : ℕ) → Fin (sz m) → Fin (sz (suc m))) ]
      SeqColim (mkFinSeq sz fmp) ≃ B
    isODisc→FinSeqData : {B : Type ℓ-zero} → isODisc B → ∥ FinSeqData B ∥₁
    isODisc→FinSeqData = PT.rec squash₁ go-outer where
      go-outer : Σ[ S ∈ Sequence ℓ-zero ] ((m : ℕ) → isFinSet (obj S m)) × (SeqColim S ≃ _)
        → ∥ FinSeqData _ ∥₁
      go-outer (S , finS , equiv) = PT.map go-inner (countableChoice _ (λ m → snd (finS m))) where
        sz : ℕ → ℕ
        sz m = fst (finS m)
        go-inner : ((m : ℕ) → obj S m ≃ Fin (sz m)) → FinSeqData _
        go-inner finEquivs = sz , fmp , compEquiv colimEquiv equiv where
          fmp : (m : ℕ) → Fin (sz m) → Fin (sz (suc m))
          fmp m x = equivFun (finEquivs (suc m)) (map S (invEq (finEquivs m) x))
          isos : (n : ℕ) → Iso (obj S n) (Fin (sz n))
          isos n = equivToIso (finEquivs n)
          comm : (n : ℕ) (a : obj S n) → fmp n (Iso.fun (isos n) a) ≡ Iso.fun (isos (suc n)) (map S a)
          comm n a = cong (λ z → equivFun (finEquivs (suc n)) (map S z)) (retEq (finEquivs n) a)
          seqIso : SequenceIso S (mkFinSeq sz fmp)
          seqIso = isos , comm
          colimEquiv : SeqColim (mkFinSeq sz fmp) ≃ SeqColim S
          colimEquiv = isoToEquiv (invIso (sequenceEquiv→ColimIso
            (SequenceIso→SequenceEquiv seqIso)))
    suc∸≤' : (n' k' : ℕ) → n' ≤ k' → suc k' ∸ n' ≡ suc (k' ∸ n')
    suc∸≤' n' k' le = sym (≤-∸-suc le)
    incl-tr' : {S' : Sequence ℓ-zero} {m₁ m₂ : ℕ} (p : m₁ ≡ m₂) (x : obj S' m₁)
      → Path (SeqColim S') (incl x) (incl (subst (obj S') p x))
    incl-tr' {S' = S'} = J (λ m₂ p → (x : obj S' _) → incl x ≡ incl (subst (obj S') p x))
      λ x → cong incl (sym (transportRefl x))
    go : ((n : ℕ) → FinSeqData (A n)) → isODisc (Σ ℕ A)
    go wit = ∣ T , isFinSetDiagObj , compEquiv equiv (Σ-cong-equiv-snd equivs) ∣₁ where
      Sn : ℕ → Sequence ℓ-zero
      Sn n = mkFinSeq (fst (wit n)) (fst (snd (wit n)))
      equivs : (n : ℕ) → SeqColim (Sn n) ≃ A n
      equivs n = snd (snd (wit n))
      -- Diagonal sequence
      DiagObj : ℕ → Type
      DiagObj k = Σ[ n ∈ ℕ ] (n ≤ k) × obj (Sn n) (k ∸ n)
      diagMap : {k : ℕ} → DiagObj k → DiagObj (suc k)
      diagMap {k} (n , p , x) =
        n , ≤-suc p , subst (obj (Sn n)) (sym (suc∸≤' n k p)) (map (Sn n) x)
      T : Sequence ℓ-zero
      obj T = DiagObj
      map T = diagMap
      -- Finiteness of DiagObj via equivalence with Fin-indexed version
      toℕ-fromℕ≤ : {k' : ℕ} (n' : ℕ) → n' ≤ k' → toℕ (fromℕ {k = k'} n') ≡ n'
      toℕ-fromℕ≤ {zero} zero _ = refl
      toℕ-fromℕ≤ {zero} (suc n') le = ⊥-rec (¬-<-zero le)
      toℕ-fromℕ≤ {suc k'} zero _ = refl
      toℕ-fromℕ≤ {suc k'} (suc n') le = cong suc (toℕ-fromℕ≤ n' (pred-≤-pred le))
      toℕ≤k : {k' : ℕ} (i : Fin (suc k')) → toℕ i ≤ k'
      toℕ≤k {zero} fzero = ≤-refl
      toℕ≤k {suc k'} fzero = zero-≤
      toℕ≤k {suc k'} (fsuc i) = suc-≤-suc (toℕ≤k i)
      isFinSetDiagObj : (k : ℕ) → isFinSet (DiagObj k)
      isFinSetDiagObj k = EquivPresIsFinSet diagIsoEquiv finFin where
        B = λ m → obj (Sn m) (k ∸ m)
        finFin = isFinSetΣ (_ , isFinSetFin) (λ i → _ , isFinSetFin)
        substCancel : {a b : ℕ} (q : a ≡ b) (y : B b)
          → subst B q (subst B (sym q) y) ≡ y
        substCancel q y =
          subst B q (subst B (sym q) y)
            ≡⟨ sym (substComposite B (sym q) q y) ⟩
          subst B (sym q ∙ q) y
            ≡⟨ cong (λ p → subst B p y) (isSetℕ _ _ _ refl) ⟩
          subst B refl y ≡⟨ transportRefl y ⟩ y ∎
        fwd' : Σ (Fin (suc k)) (λ i → B (toℕ i)) → DiagObj k
        fwd' (i , x) = toℕ i , toℕ≤k i , x
        bwd' : DiagObj k → Σ (Fin (suc k)) (λ i → B (toℕ i))
        bwd' (n , le , x) = fromℕ n , subst B (sym (toℕ-fromℕ≤ n le)) x
        sec' : (d : DiagObj k) → fwd' (bwd' d) ≡ d
        sec' (n , le , x) = ΣPathP (q , ΣPathP (isProp→PathP (λ _ → isProp≤) _ _ ,
          toPathP (substCancel q x))) where q = toℕ-fromℕ≤ n le
        ret' : (d : Σ (Fin (suc k)) (λ i → B (toℕ i))) → bwd' (fwd' d) ≡ d
        ret' (i , x) = ΣPathP (fromℕ-toℕ i , toPathP (
          subst B (cong toℕ (fromℕ-toℕ i)) (subst B (sym q') x)
            ≡⟨ cong (λ p → subst B p (subst B (sym q') x))
                 (isSetℕ _ _ (cong toℕ (fromℕ-toℕ i)) q') ⟩
          subst B q' (subst B (sym q') x) ≡⟨ substCancel q' x ⟩ x ∎)) where
          q' = toℕ-fromℕ≤ (toℕ i) (toℕ≤k i)
        diagIsoEquiv = isoToEquiv (iso fwd' bwd' sec' ret')
      -- Forward map: SeqColim T → Σ ℕ (SeqColim ∘ Sn)
      fwd : SeqColim T → Σ ℕ (λ n → SeqColim (Sn n))
      fwd (incl (n , _ , x)) = n , incl x
      fwd (push {n = k} (n , p , x) j) = ΣPathP {x = n , incl x}
        (refl , push {X = Sn n} x ∙ incl-tr' {S' = Sn n} (sym (suc∸≤' n k p)) (map (Sn n) x)) j
      -- Backward map: Σ ℕ (SeqColim ∘ Sn) → SeqColim T
      bwd-incl : (n m : ℕ) → obj (Sn n) m → SeqColim T
      bwd-incl n m y = incl {n = m +ℕ n} (n , ≤SumRight , subst (obj (Sn n)) (sym (+∸ m n)) y)
      bwd-push : (n m : ℕ) (y : obj (Sn n) m) → bwd-incl n m y ≡ bwd-incl n (suc m) (map (Sn n) y)
      bwd-push n m y = push d ∙ cong incl diagMap-eq where
        d = n , ≤SumRight , subst (obj (Sn n)) (sym (+∸ m n)) y
        z = subst (obj (Sn n)) (sym (+∸ m n)) y
        B = obj (Sn n)
        p₁ = cong suc (sym (+∸ m n))
        p₂ = sym (suc∸≤' n (m +ℕ n) ≤SumRight)
        elem-eq : subst B p₂ (map (Sn n) z)
                ≡ subst B (sym (+∸ (suc m) n)) (map (Sn n) y)
        elem-eq =
          subst B p₂ (map (Sn n) z)
            ≡⟨ cong (subst B p₂)
                 (sym (substCommSlice B (λ k → B (suc k)) (λ k → map (Sn n)) (sym (+∸ m n)) y)) ⟩
          subst B p₂ (subst B p₁ (map (Sn n) y))
            ≡⟨ sym (substComposite B p₁ p₂ (map (Sn n) y)) ⟩
          subst B (p₁ ∙ p₂) (map (Sn n) y)
            ≡⟨ cong (λ q → subst B q (map (Sn n) y)) (isSetℕ _ _ _ _) ⟩
          subst B (sym (+∸ (suc m) n)) (map (Sn n) y) ∎
        diagMap-eq : diagMap d ≡ (n , ≤SumRight , subst B (sym (+∸ (suc m) n)) (map (Sn n) y))
        diagMap-eq = ΣPathP (refl , ΣPathP (isProp≤ _ _ , elem-eq))
      bwd : Σ ℕ (λ n → SeqColim (Sn n)) → SeqColim T
      bwd (n , incl {n = m} y) = bwd-incl n m y
      bwd (n , push {n = m} y j) = bwd-push n m y j
      -- Roundtrip fwd ∘ bwd
      fwd-bwd-incl : (n m : ℕ) (y : obj (Sn n) m)
        → fwd (bwd-incl n m y) ≡ (n , incl y)
      fwd-bwd-incl n m y = ΣPathP (refl , sym (incl-tr' {S' = Sn n} (sym (+∸ m n)) y))
      -- Roundtrip bwd ∘ fwd
      bwd-fwd-incl : (k : ℕ) (d : DiagObj k) → bwd (fwd (incl {n = k} d)) ≡ incl {n = k} d
      bwd-fwd-incl k (n , p , x) = λ i → incl {n = q i} (diag-pathp i) where
        q = ≤-∸-+-cancel p
        x₁ = subst (obj (Sn n)) (sym (+∸ (k ∸ n) n)) x
        obj-pathp : PathP (λ i → obj (Sn n) (q i ∸ n)) x₁ x
        obj-pathp = toPathP (
          subst (obj (Sn n)) (cong (_∸ n) q) (subst (obj (Sn n)) (sym (+∸ (k ∸ n) n)) x)
            ≡⟨ sym (substComposite (obj (Sn n)) _ _ x) ⟩
          subst (obj (Sn n)) (sym (+∸ (k ∸ n) n) ∙ cong (_∸ n) q) x
            ≡⟨ cong (λ r → subst (obj (Sn n)) r x) (isSetℕ _ _ _ refl) ⟩
          subst (obj (Sn n)) refl x ≡⟨ transportRefl x ⟩ x ∎)
        diag-pathp : PathP (λ i → DiagObj (q i))
          (n , ≤SumRight , x₁) (n , p , x)
        diag-pathp i = n , isProp→PathP {B = λ i → n ≤ q i} (λ _ → isProp≤) ≤SumRight p i , obj-pathp i
      -- Set-ness for push coherences
      allSetSn : (n : ℕ) → isSet (SeqColim (Sn n))
      allSetSn n = isSetSeqColimOfSets (Sn n) (λ m → isFinSet→isSet isFinSetFin)
      isSetSCT : isSet (SeqColim T)
      isSetSCT = isSetSeqColimOfSets T (λ k → isFinSet→isSet (isFinSetDiagObj k))
      isSetTarget : isSet (Σ ℕ (λ n → SeqColim (Sn n)))
      isSetTarget = isSetΣ isSetℕ (λ n → allSetSn n)
      -- Full roundtrip proofs (push cases by isProp→PathP)
      sec : (x : Σ ℕ (λ n → SeqColim (Sn n))) → fwd (bwd x) ≡ x
      sec (n , incl y) = fwd-bwd-incl n _ y
      sec (n , push {n = m} y j) =
        isProp→PathP (λ j → isSetTarget (fwd (bwd (n , push y j))) (n , push y j))
          (fwd-bwd-incl n m y) (fwd-bwd-incl n (suc m) (map (Sn n) y)) j
      ret : (c : SeqColim T) → bwd (fwd c) ≡ c
      ret (incl {n = k} d) = bwd-fwd-incl k d
      ret (push {n = k} d j) =
        isProp→PathP (λ j → isSetSCT (bwd (fwd (push d j))) (push d j))
          (bwd-fwd-incl k d) (bwd-fwd-incl (suc k) (diagMap d)) j
      equiv : SeqColim T ≃ Σ ℕ (λ n → SeqColim (Sn n))
      equiv = isoToEquiv (iso fwd bwd sec ret)
  -- tex Lemma 1335: ODisc types have open equality (ODiscEqualityOpen)
  ODiscEqualityOpen : {A : Type ℓ-zero} (odiscA : isODisc A) (a b : A)
    → isOpenProp ((a ≡ b) , isODiscIsSet odiscA a b)
  ODiscEqualityOpen odiscA a b =
    ODiscPropIsOpen ((a ≡ b) , isODiscIsSet odiscA a b) (OdiscPath odiscA a b)
  -- tex Lemma 1335 (OdiscQuotientCountableByOpen, forward direction):
  -- If B is ODisc, then B is a quotient of Σ_{n:ℕ} B_n (countable) by an open relation.
  -- The surjection is incl, and the kernel is open by ODiscEqualityOpen.
  ODiscIsOpenQuotientOfCountable : {B : Type ℓ-zero} (odiscB : isODisc B)
    → ∥ Σ[ S ∈ Sequence ℓ-zero ] Σ[ finS ∈ ((n : ℕ) → isFinSet (obj S n)) ]
        Σ[ e ∈ (SeqColim S ≃ B) ]
        ((x y : SeqColim S) → isOpenProp ((equivFun e x ≡ equivFun e y) , isODiscIsSet odiscB _ _)) ∥₁
  ODiscIsOpenQuotientOfCountable odiscB = PT.map
    (λ { (S , finS , e) → S , finS , e ,
      λ x y → ODiscEqualityOpen odiscB (equivFun e x) (equivFun e y) })
    odiscB
    where open import Cubical.Foundations.Equiv using (equivFun)

  -- tex Corollary 1441: ODisc Boolean algebras are countably presented (Boole)
  freeBAℕ-isODisc : isODisc ⟨ freeBA ℕ ⟩
  freeBAℕ-isODisc = BooleIsODisc (freeBA ℕ , ∣ replacementFreeOnCountable ℕ countℕ ∣₁)
  ODiscBAareBoole : (B : BooleanRing ℓ-zero) → isODisc ⟨ B ⟩ → ∥ has-Boole-ω' B ∥₁
  ODiscBAareBoole B odiscB =
    PT.rec squash₁ go₁ (ODiscSurjFromN odiscB ∣ BooleanRingStr.𝟘 (snd B) ∣₁)
   where
    open BooleanRingStr (snd B) renaming (𝟘 to 0B; is-set to isSetB)
    open IsCommRingHom
    freeBA-surj : ∥ Σ[ e' ∈ (ℕ → ⟨ freeBA ℕ ⟩) ]
      ((a : ⟨ freeBA ℕ ⟩) → ∥ Σ[ n ∈ ℕ ] e' n ≡ a ∥₁) ∥₁
    freeBA-surj = ODiscSurjFromN freeBAℕ-isODisc ∣ generator zero ∣₁
    go₁ : Σ[ e ∈ (ℕ → ⟨ B ⟩) ] ((a : ⟨ B ⟩) → ∥ Σ[ n ∈ ℕ ] e n ≡ a ∥₁)
        → ∥ has-Boole-ω' B ∥₁
    go₁ (e , surjE) = PT.rec squash₁ go₂ freeBA-surj where
      φ : BoolHom (freeBA ℕ) B
      φ = inducedBAHom ℕ B e
      φ-eval : (n : ℕ) → fst φ (generator n) ≡ e n
      φ-eval n = funExt⁻ (evalBAInduce ℕ B e) n
      go₂ : Σ[ e' ∈ (ℕ → ⟨ freeBA ℕ ⟩) ]
        ((a : ⟨ freeBA ℕ ⟩) → ∥ Σ[ n ∈ ℕ ] e' n ≡ a ∥₁)
        → ∥ has-Boole-ω' B ∥₁
      go₂ (e' , surjE') = PT.rec squash₁ go₃
        (countableChoice _
          (λ n → ODiscEqualityOpen odiscB (fst φ (e' n)) 0B)) where
        go₃ : ((n : ℕ) → isOpenWitness ((fst φ (e' n) ≡ 0B) , isSetB _ _))
            → ∥ has-Boole-ω' B ∥₁
        go₃ openWit = ∣ r , ψ-equiv ∣₁ where
          α : ℕ → binarySequence
          α n = fst (openWit n)
          φ0→Σ : (n : ℕ) → fst φ (e' n) ≡ 0B → Σ[ k ∈ ℕ ] α n k ≡ true
          φ0→Σ n = fst (snd (openWit n))
          Σ→φ0 : (n : ℕ) → Σ[ k ∈ ℕ ] α n k ≡ true → fst φ (e' n) ≡ 0B
          Σ→φ0 n = snd (snd (openWit n))
          pair : ℕ × ℕ → ℕ
          pair = Iso.fun ℕ×ℕ≅ℕ
          unpair : ℕ → ℕ × ℕ
          unpair = Iso.inv ℕ×ℕ≅ℕ
          0F = BooleanRingStr.𝟘 (snd (freeBA ℕ))
          r : ℕ → ⟨ freeBA ℕ ⟩
          r m = let (n , k) = unpair m in
            if α n k then e' n else 0F
          φ-kills-r : (m : ℕ) → fst φ (r m) ≡ 0B
          φ-kills-r m with α (fst (unpair m)) (snd (unpair m))
                         in eq
          ... | true  = Σ→φ0 (fst (unpair m))
                          (snd (unpair m) , builtin→Path-Bool eq)
          ... | false = pres0 (snd φ)
          Q = freeBA ℕ QB./Im r
          ψ : BoolHom Q B
          ψ = QB.inducedHom {f = r} B φ φ-kills-r
          ψ-surj : isSurjection (fst ψ)
          ψ-surj b = PT.map (λ (n , p) →
            fst QB.quotientImageHom (generator n) ,
            funExt⁻ (cong fst (QB.evalInduce {f = r} B)) (generator n)
            ∙ φ-eval n ∙ p) (surjE b)
          ker⊆ideal : (c : ⟨ freeBA ℕ ⟩) → fst φ c ≡ 0B
            → IQ.generatedIdeal (BooleanRing→CommRing (freeBA ℕ)) r c
          ker⊆ideal c p = PT.rec IQ.squash go-ker (surjE' c) where
            go-ker : Σ[ n ∈ ℕ ] e' n ≡ c
              → IQ.generatedIdeal (BooleanRing→CommRing (freeBA ℕ)) r c
            go-ker (n , q) = subst (IQ.generatedIdeal _ r) q r-in-ideal where
              φe'n=0 : fst φ (e' n) ≡ 0B
              φe'n=0 = cong (fst φ) q ∙ p
              witness : Σ[ k ∈ ℕ ] α n k ≡ true
              witness = φ0→Σ n φe'n=0
              k' = fst witness
              αnk=true : α n k' ≡ true
              αnk=true = snd witness
              m = pair (n , k')
              unpair-pair : unpair m ≡ (n , k')
              unpair-pair = Iso.ret ℕ×ℕ≅ℕ (n , k')
              r-is-e'n : r m ≡ e' n
              r-is-e'n with α (fst (unpair m)) (snd (unpair m))
                         in eq
              ... | true  = cong e' (cong fst unpair-pair)
              ... | false = ⊥-rec (true≢false
                  (sym αnk=true
                   ∙ sym (cong₂ α (cong fst unpair-pair) (cong snd unpair-pair))
                   ∙ builtin→Path-Bool eq))
              r-in-ideal : IQ.generatedIdeal _ r (e' n)
              r-in-ideal = subst (IQ.generatedIdeal _ r) r-is-e'n (IQ.single m)
          isSetQ = BooleanRingStr.is-set (snd Q)
          π = fst QB.quotientImageHom
          πHom = snd QB.quotientImageHom
          πSurj : isSurjection π
          πSurj = QB.quotientImageHomSurjective {f = r}
          ψπ≡φ : (x : ⟨ freeBA ℕ ⟩) → fst ψ (π x) ≡ fst φ x
          ψπ≡φ x = funExt⁻ (cong fst (QB.evalInduce {f = r} B)) x
          ψ-inj-lift : (a b : ⟨ freeBA ℕ ⟩) → fst ψ (π a) ≡ fst ψ (π b)
            → π a ≡ π b
          ψ-inj-lift a b p = let
              φa≡φb : fst φ a ≡ fst φ b
              φa≡φb = sym (ψπ≡φ a) ∙ p ∙ ψπ≡φ b
              diff = BooleanRingStr._+_ (snd (freeBA ℕ)) a b
              φ-diff=0 : fst φ diff ≡ 0B
              φ-diff=0 = pres+ (snd φ) a b
                ∙ cong₂ (BooleanRingStr._+_ (snd B)) φa≡φb refl
                ∙ BooleanAlgebraStr.characteristic2 B
              diff-in-ideal = ker⊆ideal diff φ-diff=0
              πdiff=0 : π diff ≡ BooleanRingStr.𝟘 (snd Q)
              πdiff=0 = QB.toKernel {f = r} diff-in-ideal
              πa+πb=0 : BooleanRingStr._+_ (snd Q) (π a) (π b)
                ≡ BooleanRingStr.𝟘 (snd Q)
              πa+πb=0 = sym (pres+ πHom a b) ∙ πdiff=0
            in sym (BooleanRingStr.+IdR (snd Q) _)
              ∙ cong (BooleanRingStr._+_ (snd Q) (π a))
                  (sym (BooleanAlgebraStr.characteristic2 Q))
              ∙ BooleanRingStr.+Assoc (snd Q) _ _ _
              ∙ cong (λ z → BooleanRingStr._+_ (snd Q) z (π b)) πa+πb=0
              ∙ BooleanRingStr.+IdL (snd Q) _
          ψ-inj : (x y : ⟨ Q ⟩) → fst ψ x ≡ fst ψ y → x ≡ y
          ψ-inj x y hyp = PT.rec2 (isSetQ x y) go (πSurj x) (πSurj y) where
            go : Σ[ a ∈ _ ] π a ≡ x → Σ[ b ∈ _ ] π b ≡ y → x ≡ y
            go (a , pa) (b , pb) = sym pa ∙ ψ-inj-lift a b
              (cong (fst ψ) pa ∙ hyp ∙ cong (fst ψ) (sym pb)) ∙ pb
          ψ-equiv : BooleanRingEquiv B Q
          ψ-equiv = invCommRingEquiv
            (BooleanRing→CommRing Q) (BooleanRing→CommRing B)
            ((fst ψ , isEmbedding×isSurjection→isEquiv
              (injEmbedding isSetB (λ {x} {y} → ψ-inj x y) , ψ-surj))
            , snd ψ)
  -- ℕ is ODisc (colimit of Fin 1 → Fin 2 → Fin 3 → ...)
  private
    NatSeq : Sequence ℓ-zero
    obj NatSeq n = Fin (suc n)
    map NatSeq x = fsuc x

    nat-backward : SeqColim NatSeq → ℕ
    nat-backward (incl {n} x) = n ∸ toℕ x
    nat-backward (push {n} x i) = n ∸ toℕ x

    nat-forward : ℕ → SeqColim NatSeq
    nat-forward n = incl {n = n} fzero

    sec-incl : (n : ℕ) (x : Fin (suc n)) → nat-forward (n ∸ toℕ x) ≡ incl {n = n} x
    sec-incl n fzero = refl
    sec-incl (suc n) (fsuc x) = sec-incl n x ∙ push x

    nat-sec : (c : SeqColim NatSeq) → nat-forward (nat-backward c) ≡ c
    nat-sec (incl x) = sec-incl _ x
    nat-sec (push {n = n} x i) = compPath-filler (sec-incl n x) (push x) i

  ODiscNat : isODisc ℕ
  ODiscNat = ∣ NatSeq , (λ _ → isFinSetFin) , isoToEquiv (iso nat-backward nat-forward (λ _ → refl) nat-sec) ∣₁
  -- tex Lemma 933 (lemDecompositionOfColimitMorphisms):
  --   Maps between ODisc sets decompose as colimits of maps of finite sets.
  -- tex Corollary 939 (lemDecompositionOfEpiMonoFactorization):
  --   Epi-mono factorization decomposes as colimit of epi-mono factorizations of finite maps.
  -- tex Corollary 1134 (decompositionInjectionSurjectionOfOdisc):
  --   Injective/surjective maps between ODisc types decompose similarly.
  -- tex Remark 1486 (decompositionBooleMaps):
  --   Morphisms in Boole are sequential colimits of morphisms between finite BAs.
  -- tex Remark 1540 (ProFiniteMapsFactorization):
  --   Maps of Stone spaces are sequential limits of maps of finite sets.
  -- tex Lemma 1520 (StoneAreProfinite):
  --   Sequential limit of finite sets is Stone.
  -- tex Lemma 1558 (ScottFiniteCodomain):
  --   Fin(k)^S is colimit of Fin(k)^{S_n}.
  -- tex Corollary 1590 (scott-continuity):
  --   ℕ^S is the sequential colimit of ℕ^{S_n} for S = lim S_n.
  -- tex Lemma 1520: Finite sets are Stone
  module FiniteIsStoneModule where
    open import Axioms.StoneDuality using (hasStoneStr; 2^; isPropHasStoneStr; SDHomVersion)
    open import Cubical.Data.FinSet.Constructors using (isFinSet→)
    open import Cubical.Data.FinSet.Properties using (isFinSetBool)
    open import Cubical.Data.FinSet.Base using (card; isFinSet→isSet)
    open import Cubical.Data.FinSet.Cardinality using (cardEquiv; cardInj; card→)
    open import Cubical.Data.Fin.Properties using (Fin-inj)
    open import Cubical.Data.Nat using (_^_)
    open import Cubical.Data.Nat.Properties using (inj-sm·)

    FiniteBooleω : (F : Type ℓ-zero) → isFinSet F → Booleω
    FiniteBooleω F finF = 2^ F , ODiscBAareBoole (2^ F)
      (ODiscFinSet (isFinSet→ (_ , finF) (_ , isFinSetBool)))

    open import Cubical.Data.Nat.Properties using (inj-sm·; injSuc; znots)
    open import Cubical.Data.Nat using (+-suc) renaming (_+_ to _+ℕ_)
    private
      2^-positive : (n : ℕ) → Σ[ k ∈ ℕ ] 2 ^ n ≡ suc k
      2^-positive zero = 0 , refl
      2^-positive (suc n) with 2^-positive n
      ... | k , q = k +ℕ suc (k +ℕ 0) , cong₂ _+ℕ_ q (cong (_+ℕ 0) q)
      1≢2^suc : (n : ℕ) → ¬ (1 ≡ 2 ^ suc n)
      1≢2^suc n p with 2^-positive n
      ... | k , q = znots (injSuc (p ∙ cong₂ _+ℕ_ q (cong (_+ℕ 0) q)) ∙ +-suc k (k +ℕ 0))
    ^-inj-2 : (n m : ℕ) → 2 ^ n ≡ 2 ^ m → n ≡ m
    ^-inj-2 zero zero _ = refl
    ^-inj-2 zero (suc m) p = ex-falso (1≢2^suc m p)
    ^-inj-2 (suc n) zero p = ex-falso (1≢2^suc n (sym p))
    ^-inj-2 (suc n) (suc m) p = cong suc (^-inj-2 n m (inj-sm· {1} p))

    FiniteIsStone : (F : Type ℓ-zero) → isFinSet F → hasStoneStr F
    FiniteIsStone F finF = PT.rec (isPropHasStoneStr sd-axiom _) go mereEquiv where
      BF = FiniteBooleω F finF
      FFS : Σ _ isFinSet
      FFS = F , finF
      fin2F : isFinSet (F → Bool)
      fin2F = isFinSet→ FFS (_ , isFinSetBool)
      SpFS : Σ _ isFinSet
      SpFS = Sp BF , isFinSetSpFinRing (2^ F) fin2F
      fin2Sp : isFinSet (Sp BF → Bool)
      fin2Sp = isFinSet→ SpFS (_ , isFinSetBool)
      sdEquiv : (F → Bool) ≃ (Sp BF → Bool)
      sdEquiv = fst (SDHomVersion sd-axiom BF)
      card-eq : card FFS ≡ card SpFS
      card-eq = ^-inj-2 (card FFS) (card SpFS)
        (sym (card→ FFS (_ , isFinSetBool))
         ∙ cardEquiv (_ , fin2F) (_ , fin2Sp) ∣ sdEquiv ∣₁
         ∙ card→ SpFS (_ , isFinSetBool))
      mereEquiv : ∥ F ≃ Sp BF ∥₁
      mereEquiv = cardInj {X = FFS} {Y = SpFS} card-eq
      go : F ≃ Sp BF → hasStoneStr F
      go e = BF , sym (ua e)
  -- Derived: transport isODisc along equality
  isODisc-path : {A B : Type ℓ-zero} → A ≡ B → isODisc A → isODisc B
  isODisc-path p = transport (cong isODisc p)
  -- tex Corollary OpenDependentSums (after Lemma 1302)
  openDependentSums : (P : hProp ℓ-zero) (Q : fst P → hProp ℓ-zero)
    → isOpenProp P → ((p : fst P) → isOpenProp (Q p))
    → isOpenProp ((Σ (fst P) (λ p → fst (Q p))) , isPropΣ (snd P) (λ p → snd (Q p)))
  openDependentSums P Q Popen Qopen =
    ODiscPropIsOpen ΣPQ (OdiscSigma (PropOpenIffOdisc P Popen) (λ p → PropOpenIffOdisc (Q p) (Qopen p)))
    where ΣPQ : hProp ℓ-zero
          ΣPQ = (Σ (fst P) (λ p → fst (Q p))) , isPropΣ (snd P) (λ p → snd (Q p))
  -- tex Corollary OpenTransitive (after OpenDependentSums)
  openTransitive : {T : Type ℓ-zero} (V : T → hProp ℓ-zero) (W : Σ T (λ t → fst (V t)) → hProp ℓ-zero)
    → ((t : T) → isOpenProp (V t))
    → ((tv : Σ T (λ t → fst (V t))) → isOpenProp (W tv))
    → (t : T) → isOpenProp ((Σ[ v ∈ fst (V t) ] fst (W (t , v))) , isPropΣ (snd (V t)) (λ v → snd (W (t , v))))
  openTransitive V W Vopen Wopen t =
    openDependentSums (V t) (λ v → W (t , v)) (Vopen t) (λ v → Wopen (t , v))
  -- tex Remark 1475 (BooleEpiMono consequence):
  -- Image of a map between spectra is a countable intersection of decidable subsets.
  ImageStoneMapDecidableIntersection : (B C : Booleω) (f : Sp C → Sp B)
    → ∥ Σ[ d ∈ (ℕ → ⟨ fst B ⟩) ]
        ((x : Sp B) → (∥ Σ[ c ∈ Sp C ] f c ≡ x ∥₁) ↔ ((n : ℕ) → fst x (d n) ≡ false)) ∥₁
  ImageStoneMapDecidableIntersection B C f = PT.rec squash₁ step1 kerEnum where
    open import Axioms.StoneDuality using (SDHomVersion; evaluationMap; 2^)
    open BooleanRingStr
    open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanEquivToHom; BooleanEquivToHomInv; BooleanEquivRightInv)
    -- Step 0: Get dual BoolHom g : B → C from f : Sp C → Sp B
    -- g = eC⁻¹ ∘ precomp(f) ∘ eB where eB, eC are SD evaluation equivs
    eB : BooleanRingEquiv (fst B) (2^ (Sp B))
    eB = SDHomVersion sd-axiom B
    eC : BooleanRingEquiv (fst C) (2^ (Sp C))
    eC = SDHomVersion sd-axiom C
    precompF : BoolHom (2^ (Sp B)) (2^ (Sp C))
    precompF .fst φ c = φ (f c)
    precompF .snd .IsCommRingHom.pres0 = refl
    precompF .snd .IsCommRingHom.pres1 = refl
    precompF .snd .IsCommRingHom.pres+ _ _ = refl
    precompF .snd .IsCommRingHom.pres· _ _ = refl
    precompF .snd .IsCommRingHom.pres- _ = refl
    eCinv : BoolHom (2^ (Sp C)) (fst C)
    eCinv = BooleanEquivToHomInv (fst C) (2^ (Sp C)) eC
    eBhom : BoolHom (fst B) (2^ (Sp B))
    eBhom = BooleanEquivToHom (fst B) (2^ (Sp B)) eB
    g : BoolHom (fst B) (fst C)
    g = eCinv ∘cr precompF ∘cr eBhom
    -- g-spec: for all c : Sp C, c ∘cr g ≡ f c
    -- Key: fst c (fst g b) = fst c (invEq eC (eB(b) ∘ f))
    --     = (eB(b) ∘ f)(c)  [by roundtrip: eC(eC⁻¹(φ)) = φ, hence fst h (eC⁻¹(φ)) = φ(h)]
    --     = eB(b)(f c) = fst (f c) b
    g-spec : (c : Sp C) → c ∘cr g ≡ f c
    g-spec c = CommRingHom≡ (funExt λ b →
      fst c (fst g b)
        ≡⟨ cong (fst c) refl ⟩
      fst c (fst eCinv (fst precompF (evaluationMap B b)))
        ≡⟨ refl ⟩
      fst c (fst eCinv (λ c' → evaluationMap B b (f c')))
        ≡⟨ refl ⟩
      fst c (invEq (fst eC) (λ c' → fst (f c') b))
        ≡⟨ cong (λ φ → φ c) (secEq (fst eC) (λ c' → fst (f c') b)) ⟩
      fst (f c) b ∎)
    -- Step 1: Kernel of g is ODisc, enumerate it
    0C : ⟨ fst C ⟩
    0C = 𝟘 (snd (fst C))
    KerG : Type ℓ-zero
    KerG = Σ[ b ∈ ⟨ fst B ⟩ ] fst g b ≡ 0C
    odiscKer : isODisc KerG
    odiscKer = OdiscSigma (BooleIsODisc B) (λ b → OdiscPath (BooleIsODisc C) (fst g b) 0C)
    kerEnum : ∥ Σ[ e ∈ (ℕ → KerG) ] ((k : KerG) → ∥ Σ[ n ∈ ℕ ] e n ≡ k ∥₁) ∥₁
    kerEnum = ODiscSurjFromN odiscKer ∣ 𝟘 (snd (fst B)) , IsCommRingHom.pres0 (snd g) ∣₁
    -- Main construction given enumeration
    step1 : Σ[ e ∈ (ℕ → KerG) ] ((k : KerG) → ∥ Σ[ n ∈ ℕ ] e n ≡ k ∥₁)
      → ∥ Σ[ d ∈ (ℕ → ⟨ fst B ⟩) ]
          ((x : Sp B) → (∥ Σ[ c ∈ Sp C ] f c ≡ x ∥₁) ↔ ((n : ℕ) → fst x (d n) ≡ false)) ∥₁
    step1 (e , surjE) = ∣ d , (λ x → forward x , backward x) ∣₁
      where
      d : ℕ → ⟨ fst B ⟩
      d n = fst (e n)
      d-inKer : (n : ℕ) → fst g (d n) ≡ 0C
      d-inKer n = snd (e n)
      d-surjKer : (b : ⟨ fst B ⟩) → fst g b ≡ 0C → ∥ Σ[ n ∈ ℕ ] d n ≡ b ∥₁
      d-surjKer b gb=0 = PT.map (λ { (n , p) → n , cong fst p }) (surjE (b , gb=0))
      forward : (x : Sp B) → ∥ Σ[ c ∈ Sp C ] f c ≡ x ∥₁ → (n : ℕ) → fst x (d n) ≡ false
      forward x inImg n = PT.rec (isSetBool _ _) go inImg where
        go : Σ[ c ∈ Sp C ] f c ≡ x → fst x (d n) ≡ false
        go (c , fc≡x) =
          fst x (d n)
            ≡⟨ cong (λ h → fst h (d n)) (sym fc≡x) ⟩
          fst (f c) (d n)
            ≡⟨ cong (λ h → fst h (d n)) (sym (g-spec c)) ⟩
          fst c (fst g (d n))
            ≡⟨ cong (fst c) (d-inKer n) ⟩
          fst c 0C
            ≡⟨ IsCommRingHom.pres0 (snd c) ⟩
          false ∎
      -- Backward: if ∀n. x(d n) = false, then x ∈ Image(f)
      B/d : BooleanRing ℓ-zero
      B/d = fst B QB./Im d
      π : BoolHom (fst B) B/d
      π = QB.quotientImageHom
      isSetQ : isSet ⟨ B/d ⟩
      isSetQ = BooleanRingStr.is-set (snd B/d)
      ḡ : BoolHom B/d (fst C)
      ḡ = QB.inducedHom (fst C) g d-inKer
      ḡ∘π≡g : ḡ ∘cr π ≡ g
      ḡ∘π≡g = QB.evalInduce (fst C)
      -- char2-eq: a + b = 0 → a = b in any BooleanRing
      char2-eq : {B' : BooleanRing ℓ-zero} (a b : ⟨ B' ⟩)
        → BooleanRingStr._+_ (snd B') a b ≡ BooleanRingStr.𝟘 (snd B')
        → a ≡ b
      char2-eq {B'} a b p =
        a ≡⟨ sym (BooleanRingStr.+IdR (snd B') a) ⟩
        (a +Q BooleanRingStr.𝟘 (snd B'))
          ≡⟨ cong (a +Q_) (sym (BooleanAlgebraStr.characteristic2 B' {b})) ⟩
        (a +Q (b +Q b))
          ≡⟨ BooleanRingStr.+Assoc (snd B') a b b ⟩
        ((a +Q b) +Q b)
          ≡⟨ cong (_+Q b) p ⟩
        (BooleanRingStr.𝟘 (snd B') +Q b)
          ≡⟨ BooleanRingStr.+IdL (snd B') b ⟩
        b ∎ where _+Q_ = BooleanRingStr._+_ (snd B')
      -- a = b → a + b = 0 in any BooleanRing
      eq→sum0 : {B' : BooleanRing ℓ-zero} (a b : ⟨ B' ⟩)
        → a ≡ b → BooleanRingStr._+_ (snd B') a b ≡ BooleanRingStr.𝟘 (snd B')
      eq→sum0 {B'} a b p = cong (BooleanRingStr._+_ (snd B') a) (sym p)
        ∙ BooleanAlgebraStr.characteristic2 B'
      -- π-kills-ker: elements in Ker(g) map to 0 under π
      π-kills-gen : (n : ℕ) → fst π (d n) ≡ BooleanRingStr.𝟘 (snd B/d)
      π-kills-gen n = QB.zeroOnImage n
      π-kills-ker : (b : ⟨ fst B ⟩) → fst g b ≡ 0C → fst π b ≡ BooleanRingStr.𝟘 (snd B/d)
      π-kills-ker b gb=0 = PT.rec (isSetQ _ _) go (d-surjKer b gb=0) where
        go : Σ[ n ∈ ℕ ] d n ≡ b → fst π b ≡ BooleanRingStr.𝟘 (snd B/d)
        go (n , dn≡b) = subst (λ z → fst π z ≡ BooleanRingStr.𝟘 (snd B/d)) dn≡b (π-kills-gen n)
      -- ḡ is injective: uses epi property of π + π-kills-ker
      ḡ-inj : (q₁ q₂ : ⟨ B/d ⟩) → fst ḡ q₁ ≡ fst ḡ q₂ → q₁ ≡ q₂
      ḡ-inj q₁ q₂ eq = PT.rec2 (isSetQ _ _) go
        (QB.quotientImageHomSurjective q₁) (QB.quotientImageHomSurjective q₂) where
        go : Σ[ b₁ ∈ ⟨ fst B ⟩ ] fst π b₁ ≡ q₁
           → Σ[ b₂ ∈ ⟨ fst B ⟩ ] fst π b₂ ≡ q₂ → q₁ ≡ q₂
        go (b₁ , πb₁≡q₁) (b₂ , πb₂≡q₂) =
          sym πb₁≡q₁ ∙ char2-eq {B/d} (fst π b₁) (fst π b₂) πsum≡0 ∙ πb₂≡q₂
          where
          _+B_ = BooleanRingStr._+_ (snd (fst B))
          _+C_ = BooleanRingStr._+_ (snd (fst C))
          gb₁≡gb₂ : fst g b₁ ≡ fst g b₂
          gb₁≡gb₂ =
            fst g b₁ ≡⟨ sym (cong (λ h → fst h b₁) ḡ∘π≡g) ⟩
            fst ḡ (fst π b₁) ≡⟨ cong (fst ḡ) πb₁≡q₁ ⟩
            fst ḡ q₁ ≡⟨ eq ⟩
            fst ḡ q₂ ≡⟨ cong (fst ḡ) (sym πb₂≡q₂) ⟩
            fst ḡ (fst π b₂) ≡⟨ cong (λ h → fst h b₂) ḡ∘π≡g ⟩
            fst g b₂ ∎
          gsum≡0 : fst g (b₁ +B b₂) ≡ 0C
          gsum≡0 =
            fst g (b₁ +B b₂)
              ≡⟨ IsCommRingHom.pres+ (snd g) b₁ b₂ ⟩
            (fst g b₁ +C fst g b₂)
              ≡⟨ eq→sum0 {fst C} (fst g b₁) (fst g b₂) gb₁≡gb₂ ⟩
            0C ∎
          πsum≡0 : BooleanRingStr._+_ (snd B/d) (fst π b₁) (fst π b₂)
                 ≡ BooleanRingStr.𝟘 (snd B/d)
          πsum≡0 =
            BooleanRingStr._+_ (snd B/d) (fst π b₁) (fst π b₂)
              ≡⟨ sym (IsCommRingHom.pres+ (snd π) b₁ b₂) ⟩
            fst π (b₁ +B b₂)
              ≡⟨ π-kills-ker (b₁ +B b₂) gsum≡0 ⟩
            BooleanRingStr.𝟘 (snd B/d) ∎
      backward : (x : Sp B) → ((n : ℕ) → fst x (d n) ≡ false) → ∥ Σ[ c ∈ Sp C ] f c ≡ x ∥₁
      backward x allZero = PT.rec squash₁ bwd-step (quotientBySeqHasBooleω B d) where
        x̄ : BoolHom B/d BoolBR
        x̄ = QB.inducedHom BoolBR x allZero
        x̄∘π≡x : x̄ ∘cr π ≡ x
        x̄∘π≡x = QB.evalInduce BoolBR
        bwd-step : has-Boole-ω' B/d → ∥ Σ[ c ∈ Sp C ] f c ≡ x ∥₁
        bwd-step booleQ = PT.map finish (injective→Sp-surjective Q-Booleω C ḡ ḡ-inj x̄)
          where
          Q-Booleω : Booleω
          Q-Booleω = B/d , ∣ booleQ ∣₁
          finish : Σ[ c ∈ Sp C ] c ∘cr ḡ ≡ x̄ → Σ[ c ∈ Sp C ] f c ≡ x
          finish (c , c∘ḡ≡x̄) = c , fc≡x where
            fc≡x : f c ≡ x
            fc≡x =
              f c
                ≡⟨ sym (g-spec c) ⟩
              c ∘cr g
                ≡⟨ cong (c ∘cr_) (sym ḡ∘π≡g) ⟩
              c ∘cr (ḡ ∘cr π)
                ≡⟨ CommRingHom≡ refl ⟩
              (c ∘cr ḡ) ∘cr π
                ≡⟨ cong (_∘cr π) c∘ḡ≡x̄ ⟩
              x̄ ∘cr π
                ≡⟨ x̄∘π≡x ⟩
              x ∎
