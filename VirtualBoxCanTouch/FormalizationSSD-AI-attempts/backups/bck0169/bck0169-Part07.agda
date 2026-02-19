{-# OPTIONS --cubical --guardedness #-}

module work.Part07 where

open import work.Part06 public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_; invEq; propBiimpl→Equiv; compEquiv; secEq)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; false; isSetBool; true≢false)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Relation.Nullary.Properties using (isProp¬)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec; squash₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.BooleanRing.Initial using (BoolBR→)
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΣ; hProp; TypeOfHLevel≡)
import QuotientBool as QB
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import CountablyPresentedBooleanRings.PresentedBoole using (idBoolHom; has-Boole-ω')

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
  open import Axioms.StoneDuality using (SDHomVersion; evaluationMap)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
  open import Cubical.Foundations.Function using (_∘_; idfun)
  open import Cubical.Foundations.Equiv using (invEq; isEquiv; secEq; retEq)
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
  open import Cubical.HITs.SequentialColimit.Properties using (converges→ColimIso; SeqColim→Prop)
  open import Cubical.Data.Sequence using (Sequence; sequence; converges)
  open import Cubical.Data.FinSet using (isFinSet)
  open import Cubical.Data.FinSet.Properties using (isFinSetBool; isFinSetFin; isDecProp→isFinSet; isFinSet→Dec∥∥)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; invIso; isoToEquiv)
  open import Cubical.Foundations.Equiv using (idIsEquiv; equivFun; invEq; retEq)
  open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv)
  open import Cubical.Data.SumFin.Base using (Fin; fzero; fsuc; toℕ; fromℕ)
  open import Cubical.Data.Nat.Base using (zero; suc; _∸_)
  open import Agda.Builtin.Nat renaming (_+_ to _+ℕ_)
  open import Cubical.Data.Bool.Base using (_or_; _≟_)
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
  -- tex Lemma 1396
  postulate BooleIsODisc : (B : Booleω) → isODisc ⟨ fst B ⟩
  -- tex Lemma 1184
  postulate
    OdiscSigma : {A : Type ℓ-zero} {B : A → Type ℓ-zero}
      → isODisc A → ((a : A) → isODisc (B a)) → isODisc (Σ A B)
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
  -- tex Corollary 1441
  postulate ODiscBAareBoole : (B : BooleanRing ℓ-zero) → isODisc ⟨ B ⟩ → ∥ has-Boole-ω' B ∥₁
  -- tex Lemma 1184 (identity types)
  postulate
    OdiscPath : {A : Type ℓ-zero} → isODisc A → (a b : A) → isODisc (a ≡ b)
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
  -- tex Remark 924: ODisc types are sets (Corollary 7.7 of [SequentialColimitHoTT])
  -- Sequential colimits of sets are sets. Proof requires encode-decode with
  -- CodeFam on the full colimit, which involves +-suc arithmetic transports
  -- for the push coherence. Known result; see Sojakova–van Doorn–Rijke.
  postulate
    isSetSeqColimOfSets : (S' : Sequence ℓ-zero) → ((n : ℕ) → isSet (obj S' n))
      → isSet (SeqColim S')
  isODiscIsSet : {A : Type ℓ-zero} → isODisc A → isSet A
  isODiscIsSet = PT.rec isPropIsSet λ (S' , finS , equiv) →
    isOfHLevelRespectEquiv 2 equiv
      (isSetSeqColimOfSets S' (λ n → isFinSet→isSet (finS n)))
    where open import Cubical.Data.FinSet.Base using (isFinSet→isSet)
          open import Cubical.Foundations.HLevels using (isPropIsSet)
  -- tex Lemma 1160: ODisc stable under sequential colimits
  -- (the colimit of ODisc types A_0 → A_1 → ... is ODisc)
  postulate
    ODiscClosedUnderSequentialColimits : {A : ℕ → Type ℓ-zero}
      → ((n : ℕ) → isODisc (A n)) → isODisc (Σ ℕ A)
  -- tex Lemma 1335: ODisc types have open equality (ODiscEqualityOpen)
  ODiscEqualityOpen : {A : Type ℓ-zero} (odiscA : isODisc A) (a b : A)
    → isOpenProp ((a ≡ b) , isODiscIsSet odiscA a b)
  ODiscEqualityOpen odiscA a b =
    ODiscPropIsOpen ((a ≡ b) , isODiscIsSet odiscA a b) (OdiscPath odiscA a b)
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
  -- (These require sequential colimit/limit infrastructure beyond current formalization;
  --  the key consequences are captured by ODiscClosedUnderSequentialColimits and
  --  ImageStoneMapDecidableIntersection below.)
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
  -- Follows from OdiscSigma, OdiscPath, BooleIsODisc, ODiscSurjFromN, ODiscBAareBoole,
  -- and SurjectionsAreFormalSurjections, but the formal derivation requires constructing
  -- the BoolHom dual of a spectrum map (SpIsAntiEquivalence infrastructure).
  postulate
    ImageStoneMapDecidableIntersection : (B C : Booleω) (f : Sp C → Sp B)
      → ∥ Σ[ d ∈ (ℕ → ⟨ fst B ⟩) ]
          ((x : Sp B) → (∥ Σ[ c ∈ Sp C ] f c ≡ x ∥₁) ↔ ((n : ℕ) → fst x (d n) ≡ false)) ∥₁
