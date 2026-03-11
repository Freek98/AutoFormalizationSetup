{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneSpaces.Profinite (fa : FoundationalAxioms) where

open import formalization.StoneSpaces.ClosedInStone fa public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp)
open import Cubical.Foundations.Equiv using (_≃_; secEq; retEq; invEquiv)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Isomorphism using (Iso; isoToEquiv)
open import Cubical.Foundations.Structure
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; isSetBool) renaming (_≟_ to _=B_)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
open import Cubical.Algebra.CommRing using (CommRing; _∘cr_; CommRingHom≡)
open import Axioms.StoneDuality using (Sp)

module StoneAsClosedSubsetOfCantorModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Foundations.Equiv using (compEquiv)
  open ClosedInStoneIsStoneModule
  open StoneClosedSubsetsModule
  open CantorIsStoneModule

  ClosedSubsetOfCantor : Type₁
  ClosedSubsetOfCantor = Σ[ A ∈ (CantorSpace → hProp ℓ-zero) ] ((x : CantorSpace) → isClosedProp (A x))

  module Stone→ClosedInCantorProof where
    open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω')
    open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA)
    open import Axioms.StoneDuality using (SpGeneralBooleanRing)
    import QuotientBool as QB
    open StoneClosedSubsetsModule.SpOfQuotientBySeq

    Stone→Closed-from-pres : (B : BooleanRing ℓ-zero)
      → (pres : has-Boole-ω' B)
      → Σ[ A ∈ ClosedSubsetOfCantor ] (Sp (B , ∣ pres ∣₁) ≃ (Σ[ x ∈ CantorSpace ] fst (fst A x)))

    Stone→Closed-from-pres B (f , equiv) = (A , A-closed) , SpB≃ΣA
      where
      Q : BooleanRing ℓ-zero
      Q = freeBA ℕ QB./Im f

      B≃Q : ⟨ B ⟩ ≃ ⟨ Q ⟩
      B≃Q = fst equiv

      Cantor-to-Sp : CantorSpace → SpGeneralBooleanRing (freeBA ℕ)
      Cantor-to-Sp = Iso.inv Sp-freeBA-ℕ-Iso

      A-pred : CantorSpace → Type ℓ-zero
      A-pred α = (n : ℕ) → fst (Cantor-to-Sp α) (f n) ≡ false

      A-isProp : (α : CantorSpace) → isProp (A-pred α)
      A-isProp α = isPropΠ (λ n → isSetBool _ _)

      A : CantorSpace → hProp ℓ-zero
      A α = A-pred α , A-isProp α

      A-closed : (α : CantorSpace) → isClosedProp (A α)
      A-closed α = closedCountableIntersection P P-closed
        where
        h : SpGeneralBooleanRing (freeBA ℕ)
        h = Cantor-to-Sp α

        P : ℕ → hProp ℓ-zero
        P n = (fst h (f n) ≡ false) , isSetBool _ _

        P-closed : (n : ℕ) → isClosedProp (P n)
        P-closed n = Bool-equality-closed (fst h (f n)) false

      module SQS = SpOfQuotientBySeq (freeBA ℕ) f

      ClosedSubsetSp≃ΣA : SQS.ClosedSubset ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      ClosedSubsetSp≃ΣA = Σ-cong-equiv (isoToEquiv Sp-freeBA-ℕ-Iso)
        (λ h → pathToEquiv (cong (λ h' → (n : ℕ) → fst h' (f n) ≡ false) (sym (Iso.ret Sp-freeBA-ℕ-Iso h))))

      open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanEquivToHomInv)

      SpB≃SpQ : Sp (B , ∣ (f , equiv) ∣₁) ≃ BoolHom Q BoolBR
      SpB≃SpQ = isoToEquiv SpB-SpQ-Iso
        where
        forward : BoolHom B BoolBR → BoolHom Q BoolBR
        forward h = h ∘cr BooleanEquivToHomInv B Q equiv

        backward : BoolHom Q BoolBR → BoolHom B BoolBR
        backward k = k ∘cr (fst B≃Q , snd equiv)

        fwd∘bwd : (k : BoolHom Q BoolBR) → forward (backward k) ≡ k
        fwd∘bwd k = CommRingHom≡ (funExt λ q →
          cong (fst k) (secEq B≃Q q))

        bwd∘fwd : (h : BoolHom B BoolBR) → backward (forward h) ≡ h
        bwd∘fwd h = CommRingHom≡ (funExt λ b →
          cong (fst h) (retEq B≃Q b))

        SpB-SpQ-Iso : Iso (BoolHom B BoolBR) (BoolHom Q BoolBR)
        Iso.fun SpB-SpQ-Iso = forward
        Iso.inv SpB-SpQ-Iso = backward
        Iso.sec SpB-SpQ-Iso = fwd∘bwd
        Iso.ret SpB-SpQ-Iso = bwd∘fwd

      SpB≃ΣA : Sp (B , ∣ (f , equiv) ∣₁) ≃ (Σ[ α ∈ CantorSpace ] fst (A α))
      SpB≃ΣA = compEquiv SpB≃SpQ (compEquiv SQS.Sp-quotient-≃ ClosedSubsetSp≃ΣA)

    Stone→ClosedInCantor : (S : Stone)
      → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (fst S ≃ (Σ[ x ∈ CantorSpace ] fst (fst A x))) ∥₁
    Stone→ClosedInCantor (|S| , ((B , trunc-pres) , SpB≡S)) =
      PT.rec squash₁ go trunc-pres
      where
      go : has-Boole-ω' B → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (|S| ≃ (Σ[ α ∈ CantorSpace ] fst (fst A α))) ∥₁
      go pres = ∣ fst (Stone→Closed-from-pres B pres) ,
                  compEquiv (pathToEquiv (sym SpB≡S)) (snd (Stone→Closed-from-pres B pres)) ∣₁

  open Stone→ClosedInCantorProof using (Stone→ClosedInCantor) public

  ClosedInCantor→Stone : (A : ClosedSubsetOfCantor)
    → hasStoneStr (Σ[ x ∈ CantorSpace ] (fst (fst A x)))
  ClosedInCantor→Stone (A , Aclosed) = ClosedInStoneIsStone (CantorSpace , CantorIsStone) A Aclosed

-- tex Corollary 1537 (part): product of Stone spaces is Stone
-- StoneProduct: product of Stone spaces is Stone
module StoneProductModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr; isPropHasStoneStr)
  open import Cubical.Foundations.Equiv using (_≃_; compEquiv; propBiimpl→Equiv)
  open import Cubical.Foundations.HLevels using (isProp×)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
  open import Cubical.Foundations.Univalence using (ua)
  open import Cubical.Data.Nat using (suc) renaming (_·_ to _·ℕ_)
  open import Cubical.Data.Empty renaming (rec to ex-falso)
  open import Cubical.Data.Bool using (true≢false; false≢true)
  open StoneAsClosedSubsetOfCantorModule
  open CantorIsStoneModule

  pairCantor : CantorSpace → CantorSpace → CantorSpace
  pairCantor α β n with isEvenB n
  ... | true = α (half n)
  ... | false = β (half n)

  unpairL : CantorSpace → CantorSpace
  unpairL γ n = γ (2 ·ℕ n)

  unpairR : CantorSpace → CantorSpace
  unpairR γ n = γ (suc (2 ·ℕ n))

  pairCantor-sec : (γ : CantorSpace) → pairCantor (unpairL γ) (unpairR γ) ≡ γ
  pairCantor-sec γ = funExt sec-n
    where
    sec-n : (n : ℕ) → pairCantor (unpairL γ) (unpairR γ) n ≡ γ n
    sec-n n with isEvenB n | inspect isEvenB n
    ... | true  | [ eq ] = cong γ (2·half-even n eq)
    ... | false | [ eq ] = cong γ (suc-2·half-odd n eq)

  pairCantor-retL : (α β : CantorSpace) → unpairL (pairCantor α β) ≡ α
  pairCantor-retL α β = funExt retL-n
    where
    retL-n : (n : ℕ) → pairCantor α β (2 ·ℕ n) ≡ α n
    retL-n n with isEvenB (2 ·ℕ n) | inspect isEvenB (2 ·ℕ n)
    ... | true  | [ _ ]  = cong α (half-2k n)
    ... | false | [ eq ] = ex-falso (true≢false (sym (isEvenB-2k n) ∙ eq))

  pairCantor-retR : (α β : CantorSpace) → unpairR (pairCantor α β) ≡ β
  pairCantor-retR α β = funExt retR-n
    where
    retR-n : (n : ℕ) → pairCantor α β (suc (2 ·ℕ n)) ≡ β n
    retR-n n with isEvenB (suc (2 ·ℕ n)) | inspect isEvenB (suc (2 ·ℕ n))
    ... | true  | [ eq ] = ex-falso (false≢true (sym (isEvenB-2k+1 n) ∙ eq))
    ... | false | [ _ ]  = cong β (half-2k+1 n)

  CantorPair-Iso : Iso (CantorSpace × CantorSpace) CantorSpace
  Iso.fun CantorPair-Iso (α , β) = pairCantor α β
  Iso.inv CantorPair-Iso γ = unpairL γ , unpairR γ
  Iso.sec CantorPair-Iso = pairCantor-sec
  Iso.ret CantorPair-Iso (α , β) = ΣPathP (pairCantor-retL α β , pairCantor-retR α β)

  CantorPair-≃ : (CantorSpace × CantorSpace) ≃ CantorSpace
  CantorPair-≃ = isoToEquiv CantorPair-Iso

  -- Rearrange (Σ A_S) × (Σ A_T) ≃ Σ_{(α,β)} A_S(α) × A_T(β)
  Σ×Σ-Iso : {A C : Type ℓ-zero} {B : A → Type ℓ-zero} {D : C → Type ℓ-zero}
    → Iso (Σ A B × Σ C D) (Σ[ p ∈ A × C ] B (fst p) × D (snd p))
  Iso.fun Σ×Σ-Iso ((a , b) , (c , d)) = (a , c) , (b , d)
  Iso.inv Σ×Σ-Iso ((a , c) , (b , d)) = (a , b) , (c , d)
  Iso.sec Σ×Σ-Iso _ = refl
  Iso.ret Σ×Σ-Iso _ = refl

  StoneProduct : (S T : Stone) → hasStoneStr (fst S × fst T)
  StoneProduct S T = PT.rec2 (isPropHasStoneStr sd-axiom _) construct
    (Stone→ClosedInCantor S) (Stone→ClosedInCantor T)
    where
    construct : Σ[ A ∈ ClosedSubsetOfCantor ] (fst S ≃ (Σ[ α ∈ CantorSpace ] fst (fst A α)))
              → Σ[ B ∈ ClosedSubsetOfCantor ] (fst T ≃ (Σ[ β ∈ CantorSpace ] fst (fst B β)))
              → hasStoneStr (fst S × fst T)
    construct ((A_S , AS-cl) , S≃ΣA) ((A_T , AT-cl) , T≃ΣB) =
      subst hasStoneStr (sym (ua combined-≃)) (ClosedInCantor→Stone (C , C-closed))
      where
      C : CantorSpace → hProp ℓ-zero
      C γ = (fst (A_S (unpairL γ)) × fst (A_T (unpairR γ))) ,
            isProp× (snd (A_S (unpairL γ))) (snd (A_T (unpairR γ)))

      C-closed : (γ : CantorSpace) → isClosedProp (C γ)
      C-closed γ = closedAnd (A_S (unpairL γ)) (A_T (unpairR γ))
                     (AS-cl (unpairL γ)) (AT-cl (unpairR γ))

      -- step1: fst S × fst T ≃ ΣA_S × ΣA_T
      step1 : fst S × fst T ≃ (Σ[ α ∈ CantorSpace ] fst (A_S α)) × (Σ[ β ∈ CantorSpace ] fst (A_T β))
      step1 = ≃-× S≃ΣA T≃ΣB

      -- step2: ΣA_S × ΣA_T ≃ Σ_{(α,β)} A_S(α) × A_T(β)
      step2 : (Σ[ α ∈ CantorSpace ] fst (A_S α)) × (Σ[ β ∈ CantorSpace ] fst (A_T β))
            ≃ (Σ[ p ∈ CantorSpace × CantorSpace ] (fst (A_S (fst p)) × fst (A_T (snd p))))
      step2 = isoToEquiv Σ×Σ-Iso

      -- step3: via CantorPair, Σ_{(α,β)} ≃ Σ_γ with fiber transport
      fiberEquiv : (p : CantorSpace × CantorSpace)
        → fst (A_S (fst p)) × fst (A_T (snd p))
        ≃ fst (A_S (unpairL (pairCantor (fst p) (snd p))))
            × fst (A_T (unpairR (pairCantor (fst p) (snd p))))
      fiberEquiv (α , β) = propBiimpl→Equiv
        (isProp× (snd (A_S α)) (snd (A_T β)))
        (isProp× (snd (A_S (unpairL (pairCantor α β)))) (snd (A_T (unpairR (pairCantor α β)))))
        (λ (as , at) → subst (λ x → fst (A_S x)) (sym (pairCantor-retL α β)) as ,
                        subst (λ x → fst (A_T x)) (sym (pairCantor-retR α β)) at)
        (λ (as' , at') → subst (λ x → fst (A_S x)) (pairCantor-retL α β) as' ,
                          subst (λ x → fst (A_T x)) (pairCantor-retR α β) at')

      step3 : (Σ[ p ∈ CantorSpace × CantorSpace ] (fst (A_S (fst p)) × fst (A_T (snd p))))
            ≃ (Σ[ γ ∈ CantorSpace ] fst (C γ))
      step3 = Σ-cong-equiv CantorPair-≃ fiberEquiv

      combined-≃ : (fst S × fst T) ≃ (Σ[ γ ∈ CantorSpace ] fst (C γ))
      combined-≃ = compEquiv step1 (compEquiv step2 step3)

-- tex Lemma 1520: Sequential limit of finite sets is Stone
module StoneAreProfiniteModule where
  open import Axioms.StoneDuality using (hasStoneStr; isPropHasStoneStr)
  open CantorIsStoneModule
  open ClosedInStoneIsStoneModule using (ClosedInStoneIsStone)
  open import Cubical.Data.FinSet.Base using (isFinSet; isFinSet→isSet)
  open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
  open import Cubical.Data.SumFin.Base using (Fin; toℕ; toℕ-injective)
  open import Cubical.Data.Bool using (false≢true)
  open import Cubical.Data.Empty renaming (rec to ex-falso)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
  open import Cubical.Foundations.HLevels using (isProp×; TypeOfHLevel≡)
  open import Cubical.Foundations.Equiv using (compEquiv; equivFun; invEq; secEq; retEq; propBiimpl→Equiv)
  open import Cubical.Foundations.Univalence using (ua)
  open import Cubical.Data.Nat using (zero; suc) renaming (_+_ to _+ℕ_)
  open ODiscAxioms.FiniteIsStoneModule using (FiniteIsStone)

  module ProfiniteEncoding
    (F : ℕ → Type ℓ-zero) (finF : (n : ℕ) → isFinSet (F n))
    (π : (n : ℕ) → F (suc n) → F n)
    (equivs : (n : ℕ) → F n ≃ Fin (fst (finF n))) where
    kn : ℕ → ℕ
    kn n = fst (finF n)
    enc : ℕ × ℕ → ℕ
    enc = Iso.fun ℕ×ℕ≅ℕ
    dec : ℕ → ℕ × ℕ
    dec = Iso.inv ℕ×ℕ≅ℕ
    dec-enc : (p : ℕ × ℕ) → dec (enc p) ≡ p
    dec-enc = Iso.ret ℕ×ℕ≅ℕ
    enc-dec : (k : ℕ) → enc (dec k) ≡ k
    enc-dec = Iso.sec ℕ×ℕ≅ℕ
    toIdx : (n : ℕ) → F n → ℕ
    toIdx n x = toℕ (equivFun (equivs n) x)
    fromIdx : (n : ℕ) → Fin (kn n) → F n
    fromIdx n = invEq (equivs n)
    isSetF : (n : ℕ) → isSet (F n)
    isSetF n = isFinSet→isSet (finF n)
    -- Kronecker-delta encoding
    boolEq : ℕ → ℕ → Bool
    boolEq zero zero = true
    boolEq zero (suc _) = false
    boolEq (suc _) zero = false
    boolEq (suc a) (suc b) = boolEq a b
    boolEq-refl : (n : ℕ) → boolEq n n ≡ true
    boolEq-refl zero = refl
    boolEq-refl (suc n) = boolEq-refl n
    boolEq-true→≡ : (a b : ℕ) → boolEq a b ≡ true → a ≡ b
    boolEq-true→≡ zero zero _ = refl
    boolEq-true→≡ zero (suc _) p = ex-falso (false≢true p)
    boolEq-true→≡ (suc _) zero p = ex-falso (false≢true p)
    boolEq-true→≡ (suc a) (suc b) p = cong suc (boolEq-true→≡ a b p)
    boolEq-≡→true : (a b : ℕ) → a ≡ b → boolEq a b ≡ true
    boolEq-≡→true a b p = subst (λ x → boolEq a x ≡ true) p (boolEq-refl a)
    encode : ((n : ℕ) → F n) → CantorSpace
    encode x k = boolEq (toIdx (fst (dec k)) (x (fst (dec k)))) (snd (dec k))
    -- The closed predicate: a countable conjunction of decidable conditions
    -- Condition (n, m): α(enc(n, kn(n) + m)) ≡ false  (tail zeros)
    -- This is equivalent to: for each level n, α encodes exactly one j ∈ Fin(kn n).
    -- We also need compatibility. We handle this by having two families of conditions,
    -- interleaved via the even/odd trick.
    -- Family A (tail zeros): at index k = enc(n, m), require α(enc(n, kn(n) + m)) = false
    -- Family B (compatibility): at index k = enc(n, enc(j, j')),
    --   if α(enc(n,j))=true ∧ α(enc(suc n,j'))=true then π-compatible
    --   expressed as: ¬(α(enc(n,j))=true ∧ α(enc(suc n,j'))=true ∧ ¬(π-compat))
    -- Both families are decidable conditions. Interleaved = closed.
    -- For simplicity, define closedPred using the standard formulation with
    -- validAt + compat, and prove closedness separately.
    validAt : ℕ → CantorSpace → Type ℓ-zero
    validAt n α = Σ[ j ∈ Fin (kn n) ] ((m : ℕ) → α (enc (n , m)) ≡ boolEq (toℕ j) m)
    isPropValidAt : (n : ℕ) (α : CantorSpace) → isProp (validAt n α)
    isPropValidAt n α (j₁ , p₁) (j₂ , p₂) = Σ≡Prop
      (λ j → isPropΠ λ m → isSetBool _ _) j-eq where
      open import Cubical.Data.Sigma using (Σ≡Prop)
      idx-eq : toℕ j₁ ≡ toℕ j₂
      idx-eq = boolEq-true→≡ _ _ (sym (p₁ (toℕ j₂)) ∙ p₂ (toℕ j₂) ∙ boolEq-refl (toℕ j₂))
      j-eq : j₁ ≡ j₂
      j-eq = toℕ-injective idx-eq
    extractIdx : (n : ℕ) (α : CantorSpace) → validAt n α → F n
    extractIdx n _ (j , _) = fromIdx n j
    -- The full predicate: validity at each level + compatibility
    closedPred : CantorSpace → hProp ℓ-zero
    closedPred α = (((n : ℕ) → validAt n α) ×
      ((n : ℕ) → (v : validAt n α) → (v' : validAt (suc n) α)
        → π n (extractIdx (suc n) α v') ≡ extractIdx n α v)) ,
      isProp× (isPropΠ (λ n → isPropValidAt n α))
        (isPropΠ λ n → isPropΠ λ v → isPropΠ λ v' → isSetF n _ _)

  open import Cubical.Data.SumFin.Properties using (DecΣ)
  open import Cubical.Data.SumFin.Base using (discreteFin; fzero; fsuc)
  open import Cubical.Data.Sum using (_⊎_; inl; inr)
  open import Cubical.Data.Nat.Order using (≤Dec; <Dec)
  open import Cubical.Relation.Nullary using (Dec; yes; no; mapDec; decRec; Dec→Stable)

  -- Closed propositional Σ over Fin: if P(j) is closed for each j and Σ is a prop, it's closed
  closedFinΣ : (k : ℕ) (P : Fin k → hProp ℓ-zero)
    → ((j : Fin k) → isClosedProp (P j))
    → (propΣ : isProp (Σ (Fin k) (λ j → fst (P j))))
    → isClosedProp ((Σ (Fin k) (λ j → fst (P j))) , propΣ)
  closedFinΣ zero P _ propΣ = decIsClosed ((Σ (Fin zero) (λ j → fst (P j))) , propΣ)
    (no (λ x → fst x))
  closedFinΣ (suc k) P Pcl propΣ = subst isClosedProp hProp-eq combined
    where
    P₀ : hProp ℓ-zero
    P₀ = P fzero
    Ptail : Fin k → hProp ℓ-zero
    Ptail j = P (fsuc j)
    fsuc-inj : {j₁ j₂ : Fin k} → fsuc j₁ ≡ fsuc j₂ → j₁ ≡ j₂
    fsuc-inj {j₁} {j₂} p = toℕ-injective (injSuc (cong toℕ p))
      where
      open import Cubical.Data.Nat using (injSuc)
    isPropΣtail : isProp (Σ (Fin k) (λ j → fst (Ptail j)))
    isPropΣtail (j₁ , p₁) (j₂ , p₂) =
      let eq = propΣ (fsuc j₁ , p₁) (fsuc j₂ , p₂)
      in Σ≡Prop (λ j → snd (Ptail j)) (fsuc-inj (cong fst eq))
    tailClosed : isClosedProp ((Σ (Fin k) (λ j → fst (Ptail j))) , isPropΣtail)
    tailClosed = closedFinΣ k Ptail (λ j → Pcl (fsuc j)) isPropΣtail
    combined : isClosedProp (∥ fst P₀ ⊎ Σ (Fin k) (λ j → fst (Ptail j)) ∥₁ , squash₁)
    combined = closedOr P₀ (_ , isPropΣtail) (Pcl fzero) tailClosed
    split-equiv : (Σ (Fin (suc k)) (λ j → fst (P j))) ≃ ∥ fst P₀ ⊎ Σ (Fin k) (λ j → fst (Ptail j)) ∥₁
    split-fwd : Σ (Fin (suc k)) (λ j → fst (P j)) → ∥ fst P₀ ⊎ Σ (Fin k) (λ j → fst (Ptail j)) ∥₁
    split-fwd (fzero , p) = ∣ inl p ∣₁
    split-fwd (fsuc j , p) = ∣ inr (j , p) ∣₁
    split-bwd : ∥ fst P₀ ⊎ Σ (Fin k) (λ j → fst (Ptail j)) ∥₁ → Σ (Fin (suc k)) (λ j → fst (P j))
    split-bwd = PT.rec propΣ go where
      go : fst P₀ ⊎ Σ (Fin k) (λ j → fst (Ptail j)) → Σ (Fin (suc k)) (λ j → fst (P j))
      go (inl p) = fzero , p
      go (inr (j , p)) = fsuc j , p
    split-equiv = propBiimpl→Equiv propΣ squash₁ split-fwd split-bwd
    hProp-eq : _≡_ {A = hProp ℓ-zero}
      (∥ fst P₀ ⊎ Σ (Fin k) (λ j → fst (Ptail j)) ∥₁ , squash₁)
      ((Σ (Fin (suc k)) (λ j → fst (P j))) , propΣ)
    hProp-eq = TypeOfHLevel≡ 1 (sym (ua split-equiv))

  -- Decidable finite Π: if each P j is decidable, then (∀ j → P j) is decidable
  decFinΠ : (k : ℕ) (P : Fin k → Type ℓ-zero)
    → ((j : Fin k) → Dec (P j)) → Dec ((j : Fin k) → P j)
  decFinΠ zero _ _ = yes λ()
  decFinΠ (suc k) P decP with decP fzero | decFinΠ k (λ j → P (fsuc j)) (λ j → decP (fsuc j))
  ... | yes p₀ | yes prest = yes allP where
    allP : (j : Fin (suc k)) → P j
    allP fzero = p₀
    allP (fsuc j) = prest j
  ... | no ¬p₀ | _         = no (λ f → ¬p₀ (f fzero))
  ... | _      | no ¬prest = no (λ f → ¬prest (λ j → f (fsuc j)))

  closedPredIsClosed :
      (F : ℕ → Type ℓ-zero) (finF : (n : ℕ) → isFinSet (F n))
      (π : (n : ℕ) → F (suc n) → F n)
      (equivs : (n : ℕ) → F n ≃ Fin (fst (finF n)))
      (α : CantorSpace)
      → isClosedProp (ProfiniteEncoding.closedPred F finF π equivs α)
  closedPredIsClosed F finF π equivs α = result where
    open ProfiniteEncoding F finF π equivs
    open import Cubical.Relation.Nullary using (Discrete)
    open import Cubical.Relation.Nullary.Properties using (EquivPresDiscrete)
    discF : (n : ℕ) → Discrete (F n)
    discF n = EquivPresDiscrete (invEquiv (equivs n)) discreteFin
    -- Part 1: ∀n. validAt n α is closed
    -- For fixed n and j, inner(n,j) = ∀m. α(enc(n,m)) ≡ boolEq(toℕ j) m  is closed
    innerClosed : (n : ℕ) (j : Fin (kn n))
      → isClosedProp ((∀ m → α (enc (n , m)) ≡ boolEq (toℕ j) m) , isPropΠ λ m → isSetBool _ _)
    innerClosed n j = closedCountableIntersection
      (λ m → (α (enc (n , m)) ≡ boolEq (toℕ j) m) , isSetBool _ _)
      (λ m → Bool-equality-closed (α (enc (n , m))) (boolEq (toℕ j) m))
    validAtClosed : (n : ℕ) → isClosedProp ((validAt n α) , isPropValidAt n α)
    validAtClosed n = closedFinΣ (kn n)
      (λ j → (∀ m → α (enc (n , m)) ≡ boolEq (toℕ j) m) , isPropΠ λ m → isSetBool _ _)
      (innerClosed n)
      (isPropValidAt n α)
    allValidClosed : isClosedProp (((n : ℕ) → validAt n α) , isPropΠ (λ n → isPropValidAt n α))
    allValidClosed = closedCountableIntersection
      (λ n → (validAt n α) , isPropValidAt n α)
      validAtClosed
    -- Part 2: compat condition is closed
    -- Reformulate: ∀n j j'. α(enc(n,toℕ j))≡true → α(enc(suc n,toℕ j'))≡true → π n (fromIdx(suc n) j') ≡ fromIdx n j
    -- For fixed n, this is a finite Π over j ∈ Fin(kn n) and j' ∈ Fin(kn(suc n)) of a decidable condition
    compatCond : (n : ℕ) → Fin (kn n) → Fin (kn (suc n)) → Type ℓ-zero
    compatCond n j j' = α (enc (n , toℕ j)) ≡ true → α (enc (suc n , toℕ j')) ≡ true
      → π n (fromIdx (suc n) j') ≡ fromIdx n j
    decCompatCond : (n : ℕ) (j : Fin (kn n)) (j' : Fin (kn (suc n))) → Dec (compatCond n j j')
    decCompatCond n j j' with α (enc (n , toℕ j)) =B true | α (enc (suc n , toℕ j')) =B true
    ... | no ¬p  | _     = yes λ p → ex-falso (¬p p)
    ... | _      | no ¬q = yes λ _ q → ex-falso (¬q q)
    ... | yes p  | yes q with discF n (π n (fromIdx (suc n) j')) (fromIdx n j)
    ...   | yes eq = yes λ _ _ → eq
    ...   | no ¬eq = no λ f → ¬eq (f p q)
    isPropCompatCond : (n : ℕ) (j : Fin (kn n)) (j' : Fin (kn (suc n))) → isProp (compatCond n j j')
    isPropCompatCond n j j' = isPropΠ λ _ → isPropΠ λ _ → isSetF n _ _
    allCompatClosed : isClosedProp
      (((n : ℕ) → (j : Fin (kn n)) → (j' : Fin (kn (suc n))) → compatCond n j j') ,
       isPropΠ λ n → isPropΠ λ j → isPropΠ λ j' → isPropCompatCond n j j')
    allCompatClosed = closedCountableIntersection (λ n → Pn n , isPropPn n) (λ n → Pn-closed n)
      where
      Pn : ℕ → Type ℓ-zero
      Pn n = (j : Fin (kn n)) → (j' : Fin (kn (suc n))) → compatCond n j j'
      isPropPn : (n : ℕ) → isProp (Pn n)
      isPropPn n = isPropΠ λ j → isPropΠ λ j' → isPropCompatCond n j j'
      Pn-closed : (n : ℕ) → isClosedProp (Pn n , isPropPn n)
      Pn-closed n = decIsClosed (Pn n , isPropPn n) (decFinΠ (kn n) _ λ j →
        decFinΠ (kn (suc n)) _ λ j' → decCompatCond n j j')
    -- Part 3: Combine. closedPred α ↔ allValid × allCompat
    -- Need to show the compat reformulation matches the original
    -- The full closedPred is: allValid × compat-with-witnesses
    -- We show it's ↔ allValid × allCompat (without witnesses), which is closedAnd of two closed things.
    -- Forward direction of compat reformulation:
    origToAlt : ((n : ℕ) → validAt n α)
      → ((n : ℕ) → (v : validAt n α) → (v' : validAt (suc n) α)
        → π n (extractIdx (suc n) α v') ≡ extractIdx n α v)
      → ((n : ℕ) → (j : Fin (kn n)) → (j' : Fin (kn (suc n))) → compatCond n j j')
    origToAlt allValid origCompat n j j' αnj≡t αsn-j'≡t = goal where
      v = allValid n
      v' = allValid (suc n)
      jv≡j : fst v ≡ j
      jv≡j = toℕ-injective (boolEq-true→≡ _ _ (sym (snd v (toℕ j)) ∙ αnj≡t))
      jv'≡j' : fst v' ≡ j'
      jv'≡j' = toℕ-injective (boolEq-true→≡ _ _ (sym (snd v' (toℕ j')) ∙ αsn-j'≡t))
      goal : π n (fromIdx (suc n) j') ≡ fromIdx n j
      goal =
        π n (fromIdx (suc n) j')
          ≡⟨ cong (λ j → π n (fromIdx (suc n) j)) (sym jv'≡j') ⟩
        π n (fromIdx (suc n) (fst v'))
          ≡⟨ origCompat n v v' ⟩
        fromIdx n (fst v)
          ≡⟨ cong (fromIdx n) jv≡j ⟩
        fromIdx n j ∎
    -- Backward direction:
    altToOrig : ((n : ℕ) → (j : Fin (kn n)) → (j' : Fin (kn (suc n))) → compatCond n j j')
      → (n : ℕ) → (v : validAt n α) → (v' : validAt (suc n) α)
        → π n (extractIdx (suc n) α v') ≡ extractIdx n α v
    altToOrig altCompat n v v' =
      altCompat n (fst v) (fst v')
        (snd v (toℕ (fst v)) ∙ boolEq-refl (toℕ (fst v)))
        (snd v' (toℕ (fst v')) ∙ boolEq-refl (toℕ (fst v')))
    -- Now combine
    altPred : hProp ℓ-zero
    altPred = (((n : ℕ) → validAt n α) ×
      ((n : ℕ) → (j : Fin (kn n)) → (j' : Fin (kn (suc n))) → compatCond n j j')) ,
      isProp× (isPropΠ (λ n → isPropValidAt n α))
        (isPropΠ λ n → isPropΠ λ j → isPropΠ λ j' → isPropCompatCond n j j')
    altPred↔closedPred : fst altPred ↔ fst (closedPred α)
    fst altPred↔closedPred (av , ac) = av , altToOrig ac
    snd altPred↔closedPred (av , oc) = av , origToAlt av oc
    altPredClosed : isClosedProp altPred
    altPredClosed = closedAnd
      (((n : ℕ) → validAt n α) , isPropΠ (λ n → isPropValidAt n α))
      (((n : ℕ) → (j : Fin (kn n)) → (j' : Fin (kn (suc n))) → compatCond n j j') ,
       isPropΠ λ n → isPropΠ λ j → isPropΠ λ j' → isPropCompatCond n j j')
      allValidClosed allCompatClosed
    result : isClosedProp (ProfiniteEncoding.closedPred F finF π equivs α)
    result = subst isClosedProp eq altPredClosed where
      eq : _≡_ {A = hProp ℓ-zero} altPred (closedPred α)
      eq = TypeOfHLevel≡ 1 (ua (propBiimpl→Equiv
        (snd altPred) (snd (closedPred α)) (fst altPred↔closedPred) (snd altPred↔closedPred)))

  StoneAreProfinite : (F : ℕ → Type ℓ-zero) (finF : (n : ℕ) → isFinSet (F n))
    (π : (n : ℕ) → F (suc n) → F n)
    → hasStoneStr (SeqLimit F π)
  StoneAreProfinite F finF π =
    PT.rec (isPropHasStoneStr sd-axiom _) go
      (countableChoice _ (λ n → snd (finF n)))
    where
    go : ((n : ℕ) → F n ≃ Fin (fst (finF n))) → hasStoneStr (SeqLimit F π)
    go equivs = subst hasStoneStr (ua seqLim≃) closedSubStone where
      open ProfiniteEncoding F finF π equivs
      -- closedPredIsClosed: reformulate as countable ∧ of decidable conditions
      -- Condition family P indexed by ℕ:
      --   decode k → (type, n, m) using ℕ×ℕ×ℕ pairing
      --   type 0: tail zeros α(enc(n, kn(n)+m)) ≡ false
      --   type 1: at-most-one ¬(α(enc(n,fst m))=true ∧ α(enc(n,snd m))=true) for fst m < snd m < kn(n)
      --   type 2: at-least-one + compat (decidable since Fin is finite)
      -- For now, closedness holds because closedPred α is propositionally equivalent
      -- to a countable intersection of closed (decidable) propositions.
      closedPredIsClosed' : (α : CantorSpace) → isClosedProp (closedPred α)
      closedPredIsClosed' = closedPredIsClosed F finF π equivs
      -- seqLim≃: the closed subset of Cantor space is equivalent to SeqLimit F π
      -- Forward: (α, valid, compat) ↦ (n ↦ extractIdx n α (valid n), compat)
      -- Backward: (x, coherent) ↦ (encode x, validity-proof, compat-proof)
      seqLim≃ : Σ CantorSpace (λ α → fst (closedPred α)) ≃ SeqLimit F π
      seqLim≃ = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd) where
        fwd : Σ CantorSpace (λ α → fst (closedPred α)) → SeqLimit F π
        fwd (α , valid , compat) = (λ n → extractIdx n α (valid n)) ,
          (λ n → compat n (valid n) (valid (suc n)))
        bwd : SeqLimit F π → Σ CantorSpace (λ α → fst (closedPred α))
        bwd (x , coh) = encode x , bwd-valid , bwd-compat where
          bwd-valid : (n : ℕ) → validAt n (encode x)
          bwd-valid n = equivFun (equivs n) (x n) , λ m →
            encode x (enc (n , m))
              ≡⟨ cong (λ p → boolEq (toIdx (fst p) (x (fst p))) (snd p)) (dec-enc (n , m)) ⟩
            boolEq (toIdx n (x n)) m ∎
          bwd-compat : (n : ℕ) → (v : validAt n (encode x)) → (v' : validAt (suc n) (encode x))
            → π n (extractIdx (suc n) (encode x) v') ≡ extractIdx n (encode x) v
          bwd-compat n v v' =
            π n (fromIdx (suc n) (fst v'))
              ≡⟨ cong (π n) (cong (fromIdx (suc n)) v'-eq) ⟩
            π n (fromIdx (suc n) (equivFun (equivs (suc n)) (x (suc n))))
              ≡⟨ cong (π n) (retEq (equivs (suc n)) (x (suc n))) ⟩
            π n (x (suc n))
              ≡⟨ coh n ⟩
            x n
              ≡⟨ sym (retEq (equivs n) (x n)) ⟩
            fromIdx n (equivFun (equivs n) (x n))
              ≡⟨ cong (fromIdx n) (sym v-eq) ⟩
            fromIdx n (fst v) ∎
            where
            v-eq : fst v ≡ equivFun (equivs n) (x n)
            v-eq = cong fst (isPropValidAt n (encode x) v (bwd-valid n))
            v'-eq : fst v' ≡ equivFun (equivs (suc n)) (x (suc n))
            v'-eq = cong fst (isPropValidAt (suc n) (encode x) v' (bwd-valid (suc n)))
        fwd-bwd : (sl : SeqLimit F π) → fwd (bwd sl) ≡ sl
        fwd-bwd (x , coh) = ΣPathP (x-eq , toPathP (funExt λ n → isSetF n _ _ _ _))
          where x-eq = funExt (λ n → retEq (equivs n) (x n))
        bwd-fwd : (p : Σ CantorSpace (λ α → fst (closedPred α))) → bwd (fwd p) ≡ p
        bwd-fwd (α , valid , compat) = ΣPathP (encode-eq ,
          isProp→PathP (λ i → snd (closedPred (encode-eq i))) _ _)
          where
          encode-eq : encode (λ n → extractIdx n α (valid n)) ≡ α
          encode-eq = funExt λ k → step1 k ∙ step2 k ∙ step3 k where
            n' : ℕ → ℕ
            n' k = fst (dec k)
            m' : ℕ → ℕ
            m' k = snd (dec k)
            step1 : (k : ℕ) → encode (λ n → fromIdx n (fst (valid n))) k
              ≡ boolEq (toℕ (fst (valid (n' k)))) (m' k)
            step1 k = cong (λ j → boolEq (toℕ j) (m' k))
              (secEq (equivs (n' k)) (fst (valid (n' k))))
            step2 : (k : ℕ) → boolEq (toℕ (fst (valid (n' k)))) (m' k)
              ≡ α (enc (n' k , m' k))
            step2 k = sym (snd (valid (n' k)) (m' k))
            step3 : (k : ℕ) → α (enc (n' k , m' k)) ≡ α k
            step3 k = cong α (enc-dec k)
      closedSubStone : hasStoneStr (Σ CantorSpace (λ α → fst (closedPred α)))
      closedSubStone = ClosedInStoneIsStone (CantorSpace , CantorIsStone) closedPred closedPredIsClosed'

-- tex Lemma 1512: Any Stone space is a sequential limit of finite sets
-- Sp(Q) ≃ SeqLimit (λ n → Sp(BN n)) (λ n → _∘cr mapBNHom n)
module SpColimToSeqLimModule where
  open import Axioms.StoneDuality using (SpGeneralBooleanRing; hasStoneStr; isPropHasStoneStr)
  open import Cubical.Foundations.Equiv using (compEquiv; equivFun; invEq; secEq; retEq)
  open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToEquiv)
  open import Cubical.Foundations.HLevels using (isPropΠ; isPropΠ3)
  open import Cubical.Foundations.Univalence using (ua)
  open import Cubical.Data.Nat using (zero; suc) renaming (_+_ to _+ℕ_)
  open import Cubical.Data.Nat.Properties using (+-comm)
  open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
  open import Cubical.Algebra.CommRing using (_∘cr_; CommRingHom≡; IsCommRingHom; CommRingStr)
  open import Cubical.Data.Sequence using (Sequence)
  open import Cubical.HITs.SequentialColimit.Properties using (SeqColim→Prop)
  open import Axioms.StoneDuality using (isSetSp)
  open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
  open import Cubical.Algebra.BooleanRing using (BooleanRing→CommRing)

  module SpColimToSeqLim {Q : BooleanRing ℓ-zero} (rd : ODiscAxioms.ODiscRingDecomp Q) where
    open ODiscAxioms.ODiscRingDecomp rd

    SpBN : ℕ → Type ℓ-zero
    SpBN n = SpGeneralBooleanRing (BN n)

    πSp : (n : ℕ) → SpBN (suc n) → SpBN n
    πSp n φ = φ ∘cr mapBNHom n

    -- Forward: Sp(Q) → SeqLimit SpBN πSp
    fwd : SpGeneralBooleanRing Q → SeqLimit SpBN πSp
    fwd φ = (λ n → ODiscAxioms.SpProjection rd n φ) , λ n → CommRingHom≡ (funExt λ x →
      fst φ (fst (fwdHom (suc n)) (fst (mapBNHom n) x))
        ≡⟨ cong (λ g → fst φ (fst (fwdHom (suc n)) (g x))) (sym (mapBN≡ n)) ⟩
      fst φ (fst (fwdHom (suc n)) (mapBN n x))
        ≡⟨ cong (fst φ) (sym (fwd-compat n x)) ⟩
      fst φ (fst (fwdHom n) x) ∎)

    -- Backward: SeqLimit SpBN πSp → Sp(Q)
    -- Given compatible (φ_n)_n, define φ : Q → Bool by φ(q) = φ_n(b) where q = fwdHom n b
    -- Use SeqColim eliminator via colimEquiv
    bwd-on-colim : SeqLimit SpBN πSp → SeqColim seqB → Bool
    bwd-on-colim (φs , _) (incl {n} b) = fst (φs n) b
    bwd-on-colim (φs , compat) (push {n} b i) = path i where
      path : fst (φs n) b ≡ fst (φs (suc n)) (mapBN n b)
      path =
        fst (φs n) b
          ≡⟨ cong (λ h → fst h b) (sym (compat n)) ⟩
        fst (φs (suc n)) (fst (mapBNHom n) b)
          ≡⟨ cong (fst (φs (suc n))) (sym (funExt⁻ (mapBN≡ n) b)) ⟩
        fst (φs (suc n)) (mapBN n b) ∎

    -- bwd: construct ring hom Q → Bool from compatible family
    module BwdConstruction (sl : SeqLimit SpBN πSp) where
      φs = fst sl
      compat = snd sl
      bwd-fun : ⟨ Q ⟩ → Bool
      bwd-fun q = bwd-on-colim sl (invEq colimEquiv q)
      -- Key: bwd-fun ∘ equivFun colimEquiv ≡ bwd-on-colim sl
      bwd-key : (c : SeqColim seqB) → bwd-fun (equivFun colimEquiv c) ≡ bwd-on-colim sl c
      bwd-key c = cong (bwd-on-colim sl) (retEq colimEquiv c)
      -- Key at incl level
      bwd-at-incl : (n : ℕ) (b : ⟨ BN n ⟩) → bwd-fun (fst (fwdHom n) b) ≡ fst (φs n) b
      bwd-at-incl n b =
        cong (bwd-on-colim sl) (cong (invEq colimEquiv) (sym (colimEquiv-incl n b))
           ∙ retEq colimEquiv (incl b))
      open IsCommRingHom
      -- pres0
      bwd-pres0 : bwd-fun (BooleanRingStr.𝟘 (snd Q)) ≡ false
      bwd-pres0 =
        cong bwd-fun (sym (pres0 (snd (fwdHom 0))))
        ∙ bwd-at-incl 0 (BooleanRingStr.𝟘 (snd (BN 0)))
        ∙ pres0 (snd (φs 0))
      -- pres1
      bwd-pres1 : bwd-fun (BooleanRingStr.𝟙 (snd Q)) ≡ true
      bwd-pres1 =
        cong bwd-fun (sym (pres1 (snd (fwdHom 0))))
        ∙ bwd-at-incl 0 (BooleanRingStr.𝟙 (snd (BN 0)))
        ∙ pres1 (snd (φs 0))
      -- Compatible family property: φs n b ≡ φs (d + n) (iterMapHom d b)
      φs-compat-hom : (d : ℕ) {n : ℕ} (b : ⟨ BN n ⟩)
        → fst (φs n) b ≡ fst (φs (d +ℕ n)) (fst (iterMapHom d) b)
      φs-compat-hom zero b = refl
      φs-compat-hom (suc d) {n} b =
        fst (φs n) b
          ≡⟨ φs-compat-hom d b ⟩
        fst (φs (d +ℕ n)) (fst (iterMapHom d) b)
          ≡⟨ cong (λ h → fst h (fst (iterMapHom d) b)) (sym (compat (d +ℕ n))) ⟩
        fst (φs (suc (d +ℕ n))) (fst (mapBNHom (d +ℕ n)) (fst (iterMapHom d) b)) ∎
      -- Binary operation proof: generic for +, ·
      -- Strategy: double SeqColim→Prop, lift to same level, use ring hom property
      isSetBool' : isSet Bool
      isSetBool' = BooleanRingStr.is-set (snd BoolBR)
      open import Cubical.Foundations.Transport using (constSubstCommSlice)
      -- Subst helper: transport BN across +-comm
      BN-carrier : ℕ → Type ℓ-zero
      BN-carrier m = ⟨ BN m ⟩
      -- Key: fst (fwdHom n) b ≡ fst (fwdHom m) (subst BN-carrier p b) for p : n ≡ m
      fwdHom-subst : {n m : ℕ} (p : n ≡ m) (b : ⟨ BN n ⟩)
        → fst (fwdHom n) b ≡ fst (fwdHom m) (subst BN-carrier p b)
      fwdHom-subst p b = constSubstCommSlice BN-carrier ⟨ Q ⟩ (λ m → fst (fwdHom m)) p b
      φs-subst : {n m : ℕ} (p : n ≡ m) (b : ⟨ BN n ⟩)
        → fst (φs n) b ≡ fst (φs m) (subst BN-carrier p b)
      φs-subst p b = constSubstCommSlice BN-carrier Bool (λ m → fst (φs m)) p b
      -- Same-level helper: when both args are at the same BN n level
      go-same : (op-Q : ⟨ Q ⟩ → ⟨ Q ⟩ → ⟨ Q ⟩)
                (op-BN : (n : ℕ) → ⟨ BN n ⟩ → ⟨ BN n ⟩ → ⟨ BN n ⟩)
                (op-Bool : Bool → Bool → Bool)
                (fwdHom-pres : (n : ℕ) (a b : ⟨ BN n ⟩) →
                  op-Q (fst (fwdHom n) a) (fst (fwdHom n) b) ≡ fst (fwdHom n) (op-BN n a b))
                (φs-pres : (n : ℕ) (a b : ⟨ BN n ⟩) →
                  fst (φs n) (op-BN n a b) ≡ op-Bool (fst (φs n) a) (fst (φs n) b))
                (q₁ q₂ : ⟨ Q ⟩) (n : ℕ) (b₁ b₂ : ⟨ BN n ⟩)
              → equivFun colimEquiv (incl b₁) ≡ q₁
              → equivFun colimEquiv (incl b₂) ≡ q₂
              → bwd-fun (op-Q q₁ q₂) ≡ op-Bool (bwd-fun q₁) (bwd-fun q₂)
      go-same op-Q op-BN op-Bool fwdHom-pres φs-pres q₁ q₂ n b₁ b₂ eq₁ eq₂ =
        let e₁ = colimEquiv-incl n b₁ ; e₂ = colimEquiv-incl n b₂
        in cong₂ (λ x y → bwd-fun (op-Q x y)) (sym eq₁ ∙ e₁) (sym eq₂ ∙ e₂)
           ∙ cong bwd-fun (fwdHom-pres n b₁ b₂)
           ∙ bwd-at-incl n (op-BN n b₁ b₂) ∙ φs-pres n b₁ b₂
           ∙ cong₂ op-Bool (sym (bwd-at-incl n b₁) ∙ cong bwd-fun (sym e₁ ∙ eq₁))
                           (sym (bwd-at-incl n b₂) ∙ cong bwd-fun (sym e₂ ∙ eq₂))
      -- lift-incl-eq: equivFun colimEquiv (incl b) ≡ equivFun colimEquiv (incl (iterMapHom d b))
      lift-incl-eq : (d : ℕ) {n : ℕ} (b : ⟨ BN n ⟩)
        → equivFun colimEquiv (incl b)
          ≡ equivFun colimEquiv (incl {n = d +ℕ n} (fst (iterMapHom d) b))
      lift-incl-eq d {n} b =
        colimEquiv-incl n b ∙ fwd-compat-hom d b
        ∙ sym (colimEquiv-incl (d +ℕ n) (fst (iterMapHom d) b))
      lift-subst-eq : (d : ℕ) {n : ℕ} (b : ⟨ BN n ⟩) (p : d +ℕ n ≡ n +ℕ d)
        → equivFun colimEquiv (incl b)
          ≡ equivFun colimEquiv (incl {n = n +ℕ d} (subst BN-carrier p (fst (iterMapHom d) b)))
      lift-subst-eq d {n} b p =
        lift-incl-eq d b
        ∙ colimEquiv-incl (d +ℕ n) (fst (iterMapHom d) b)
        ∙ fwdHom-subst p (fst (iterMapHom d) b)
        ∙ sym (colimEquiv-incl (n +ℕ d) (subst BN-carrier p (fst (iterMapHom d) b)))
      bwd-pres-bin : (op-Q : ⟨ Q ⟩ → ⟨ Q ⟩ → ⟨ Q ⟩)
                     (op-BN : (n : ℕ) → ⟨ BN n ⟩ → ⟨ BN n ⟩ → ⟨ BN n ⟩)
                     (op-Bool : Bool → Bool → Bool)
                     (fwdHom-pres : (n : ℕ) (a b : ⟨ BN n ⟩) →
                       op-Q (fst (fwdHom n) a) (fst (fwdHom n) b) ≡ fst (fwdHom n) (op-BN n a b))
                     (φs-pres : (n : ℕ) (a b : ⟨ BN n ⟩) →
                       fst (φs n) (op-BN n a b) ≡ op-Bool (fst (φs n) a) (fst (φs n) b))
                     → (q₁ q₂ : ⟨ Q ⟩) → bwd-fun (op-Q q₁ q₂) ≡ op-Bool (bwd-fun q₁) (bwd-fun q₂)
      bwd-pres-bin op-Q op-BN op-Bool fwdHom-pres φs-pres q₁ q₂ =
        let goal = bwd-fun (op-Q q₁ q₂) ≡ op-Bool (bwd-fun q₁) (bwd-fun q₂)
        in SeqColim→Prop {B = λ c → equivFun colimEquiv c ≡ q₁ → goal}
          (λ _ → isPropΠ (λ _ → isSetBool' _ _))
          (λ n₁ b₁ eq₁ →
            SeqColim→Prop {B = λ c → equivFun colimEquiv c ≡ q₂ → goal}
              (λ _ → isPropΠ (λ _ → isSetBool' _ _))
              (λ n₂ b₂ eq₂ →
                let N = n₂ +ℕ n₁
                    b₁' = fst (iterMapHom n₂) b₁
                    b₂' = subst BN-carrier (+-comm n₁ n₂) (fst (iterMapHom n₁) b₂)
                    eq₁' : equivFun colimEquiv (incl b₁) ≡ equivFun colimEquiv (incl {n = N} b₁')
                    eq₁' = lift-incl-eq n₂ b₁
                    eq₂' : equivFun colimEquiv (incl b₂) ≡ equivFun colimEquiv (incl {n = N} b₂')
                    eq₂' = lift-subst-eq n₁ b₂ (+-comm n₁ n₂)
                in go-same op-Q op-BN op-Bool fwdHom-pres φs-pres q₁ q₂ N b₁' b₂'
                     (sym eq₁' ∙ eq₁) (sym eq₂' ∙ eq₂))
              (invEq colimEquiv q₂) (secEq colimEquiv q₂))
          (invEq colimEquiv q₁) (secEq colimEquiv q₁)
      -- CommRing versions for homomorphism goals
      QC = BooleanRing→CommRing Q
      BC = BooleanRing→CommRing BoolBR
      BNC : ℕ → CommRing ℓ-zero
      BNC n = BooleanRing→CommRing (BN n)
      module QR = CommRingStr (snd QC)
      module BR = CommRingStr (snd BC)
      module BNR (n : ℕ) = CommRingStr (snd (BNC n))
      -- pres-
      bwd-pres- : (q : ⟨ Q ⟩) → bwd-fun (QR.- q) ≡ bwd-fun q
      bwd-pres- q = step₂ (invEq colimEquiv q) (secEq colimEquiv q) where
        step₂ : (c : SeqColim seqB) → equivFun colimEquiv c ≡ q
              → bwd-fun (QR.- q) ≡ bwd-fun q
        step₂ = SeqColim→Prop (λ _ → isPropΠ (λ _ → isSetBool' _ _))
          (λ n b eq →
            cong (λ x → bwd-fun (QR.- x)) (sym eq)
            ∙ cong (λ x → bwd-fun (QR.- x)) (colimEquiv-incl n b)
            ∙ cong bwd-fun (sym (pres- (snd (fwdHom n)) b))
            ∙ bwd-at-incl n (CommRingStr.-_ (snd (BNC n)) b)
            ∙ pres- (snd (φs n)) b
            ∙ sym (bwd-at-incl n b)
            ∙ cong bwd-fun (sym (colimEquiv-incl n b))
            ∙ cong bwd-fun eq)
      bwd-hom : IsCommRingHom (snd QC) bwd-fun (snd BC)
      pres0 bwd-hom = bwd-pres0
      pres1 bwd-hom = bwd-pres1
      pres+ bwd-hom q₁ q₂ = bwd-pres-bin QR._+_ (λ n → BNR._+_ n) BR._+_
        (λ n a b → sym (pres+ (snd (fwdHom n)) a b))
        (λ n a b → pres+ (snd (φs n)) a b) q₁ q₂
      pres· bwd-hom q₁ q₂ = bwd-pres-bin QR._·_ (λ n → BNR._·_ n) BR._·_
        (λ n a b → sym (pres· (snd (fwdHom n)) a b))
        (λ n a b → pres· (snd (φs n)) a b) q₁ q₂
      pres- bwd-hom q = bwd-pres- q

    bwd : SeqLimit SpBN πSp → SpGeneralBooleanRing Q
    bwd sl = BwdConstruction.bwd-fun sl , BwdConstruction.bwd-hom sl

    -- fwd-bwd: bwd produces compatible family matching original
    fwd-bwd : (sl : SeqLimit SpBN πSp) → fwd (bwd sl) ≡ sl
    fwd-bwd sl = Σ≡Prop (λ _ → isPropΠ (λ n → isSetSp (BN n) _ _)) (funExt (λ n →
      CommRingHom≡ (funExt (λ b → BwdConstruction.bwd-at-incl sl n b))))
    -- bwd-fwd: ring hom from Q equals original φ
    bwd-fwd : (φ : SpGeneralBooleanRing Q) → bwd (fwd φ) ≡ φ
    bwd-fwd φ = CommRingHom≡ (funExt (λ q →
      let step : (c : SeqColim seqB) → bwd-on-colim (fwd φ) c ≡ fst φ (equivFun colimEquiv c)
          step = SeqColim→Prop (λ _ → BooleanRingStr.is-set (snd BoolBR) _ _)
            (λ n b → cong (fst φ) (sym (colimEquiv-incl n b)))
      in step (invEq colimEquiv q) ∙ cong (fst φ) (secEq colimEquiv q)))
      where open IsCommRingHom

    SpColim≃SeqLim : SpGeneralBooleanRing Q ≃ SeqLimit SpBN πSp
    SpColim≃SeqLim = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

-- tex Corollary 1537 (part): equalizer of Stone maps is Stone
module StoneEqualizerModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open StoneEqualityClosedModule using (StoneEqualityClosed)
  open ClosedInStoneIsStoneModule using (ClosedInStoneIsStone)

  StoneEqualizer : (S T : Stone) (f g : fst S → fst T)
    → hasStoneStr (Σ[ s ∈ fst S ] f s ≡ g s)
  StoneEqualizer S T f g = ClosedInStoneIsStone S A A-closed
    where
    A : fst S → hProp ℓ-zero
    A s = (f s ≡ g s) , StoneEqualityClosedModule.hasStoneStr→isSet T (f s) (g s)
    A-closed : (s : fst S) → isClosedProp (A s)
    A-closed s = StoneEqualityClosed T (f s) (g s)

-- tex Corollary 1537 (part): pullback of Stone maps is Stone
module StonePullbackModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open StoneProductModule using (StoneProduct)
  open StoneEqualizerModule using (StoneEqualizer)

  StonePullback : (A B C : Stone) (f : fst A → fst C) (g : fst B → fst C)
    → hasStoneStr (Σ[ p ∈ fst A × fst B ] f (fst p) ≡ g (snd p))
  StonePullback A B C f g =
    StoneEqualizer (fst A × fst B , StoneProduct A B) C
      (λ p → f (fst p)) (λ p → g (snd p))
