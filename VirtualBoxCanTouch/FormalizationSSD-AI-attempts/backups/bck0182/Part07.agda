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
open import Cubical.Foundations.HLevels using (isPropΠ; isPropΣ; isSetΣ; hProp; TypeOfHLevel≡)
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
  open import Cubical.Foundations.Equiv using (idIsEquiv; equivFun; invEq; retEq; secEq; equivToIso; invEquiv)
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
  -- tex Lemma 1160: sequential colimits of ODisc types are ODisc
  postulate
    ODiscColimOfODisc : (S : Sequence ℓ-zero)
      → ((n : ℕ) → isODisc (obj S n)) → isODisc (SeqColim S)
  -- freeBA(Fin k) is finite (uses SD)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom;
    inducedBAHomUnique; evalBAInduce)
  open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; idBoolHom)
  import Cubical.Data.Fin as DF
  open import Cubical.Foundations.Equiv using (fiber)
  open import Cubical.Data.Nat using (max) renaming (_+_ to _+ℕ_)
  open import Cubical.Data.Nat.Order using (_<_; _≤_; <Dec; ¬m+n<m; ¬m<m; ¬-<-zero; ≤-refl; ≤-trans; ≤-sucℕ; ≤-split; pred-≤-pred; isProp≤; left-≤-max; right-≤-max; suc-≤-suc)
  open import Cubical.Data.Nat.Order.Inductive using (<→<ᵗ; isProp<ᵗ; <ᵗ→<)
  open import Cubical.Relation.Nullary using (Dec; yes; no)
  open import Cubical.Algebra.CommRing.Properties using (_∘cr_)
  open import Cubical.Foundations.Function using (_∘_; idfun)
  open import Cubical.Data.FinSet.Constructors using (isFinSet→; isFinSetΠ)
  open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
  open import Cubical.Data.FinSet.Quotients using (isFinSetQuot)
  open import Cubical.Relation.Binary.Base using (module BinaryRelation)
  open import Cubical.Relation.Nullary.DecidablePropositions using (isDecProp)
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import Cubical.Data.Bool.Properties using (Dec≃DecBool)
  import Cubical.Data.Sum as ⊎
  open import Cubical.Functions.Surjection using (isSurjection; isEmbedding×isSurjection→isEquiv)
  open import Cubical.Functions.Embedding using (injEmbedding)
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
  -- tex Lemma 1396 (core): proved from ODiscColimOfODisc + countableChoice + genBound
  quotientFreeBA-isODisc : (f : ℕ → ⟨ freeBA ℕ ⟩) → isODisc ⟨ freeBA ℕ QB./Im f ⟩
  quotientFreeBA-isODisc f =
    PT.rec (isProp-isODisc _) go
      (countableChoice _ (λ k → ODiscInfrastructure.genBound (f k)))
    where
      open ODiscInfrastructure using (ι-inc; π-proj; ιπι-retract; π-on-gen-below)
      go : ((k : ℕ) → Σ[ m ∈ ℕ ] fiber (fst (ι-inc m)) (f k))
         → isODisc ⟨ freeBA ℕ QB./Im f ⟩
      go choice = isODisc-equiv colimEquiv (ODiscColimOfODisc seqB odiscLevels) where
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
        mapBN : (n : ℕ) → ⟨ BN n ⟩ → ⟨ BN (suc n) ⟩
        mapBN n = fst (QB.inducedHom {B = freeBA (DF.Fin (M n))} {f = relN n}
          (BN (suc n)) g gfx=0) where
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
        seqB : Sequence ℓ-zero
        obj seqB n = ⟨ BN n ⟩
        map seqB = mapBN _
        -- Each level is ODisc (finite, hence ODisc)
        isFinSetBN : (n : ℕ) → isFinSet (obj seqB n)
        isFinSetBN n = isFinSet-BRquot (freeBA (DF.Fin (M n)))
          (isFinSet-freeBA-Fin (M n)) {suc n} (relN n)
        odiscLevels : (n : ℕ) → isODisc (obj seqB n)
        odiscLevels n = ODiscFinSet (isFinSetBN n)
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
  -- tex Lemma 1396
  BooleIsODisc : (B : Booleω) → isODisc ⟨ fst B ⟩
  BooleIsODisc B = PT.rec (isProp-isODisc _) go (snd B) where
    go : has-Boole-ω' (fst B) → isODisc ⟨ fst B ⟩
    go (f , bEquiv) =
      isODisc-equiv (invEquiv (fst bEquiv)) (quotientFreeBA-isODisc f)
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
  -- tex Corollary 1441
  postulate ODiscBAareBoole : (B : BooleanRing ℓ-zero) → isODisc ⟨ B ⟩ → ∥ has-Boole-ω' B ∥₁
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
