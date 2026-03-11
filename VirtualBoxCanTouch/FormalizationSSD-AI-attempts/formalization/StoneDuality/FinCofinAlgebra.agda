{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneDuality.FinCofinAlgebra (fa : FoundationalAxioms) where

open import formalization.StoneDuality.BooleanAlgebra fa public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv; isoToIsEquiv; Iso)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; not)
open import Cubical.Data.Bool.Properties using (true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import QuotientBool as QB
open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; has-Boole-ω')
open import Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Empty renaming (rec to ex-falso)

module Bool²-presentation where
  open BooleanRingStr (snd (freeBA ℕ)) using (𝟙) renaming (_+_ to _+free_ ; _·_ to _·free_)

  g₀ : ⟨ freeBA ℕ ⟩
  g₀ = generator 0

  g₁ : ⟨ freeBA ℕ ⟩
  g₁ = generator 1

  relBool² : ℕ → ⟨ freeBA ℕ ⟩
  relBool² 0 = g₀ ·free g₁
  relBool² 1 = 𝟙 +free g₀ +free g₁
  relBool² (suc (suc n)) = generator (suc (suc n))

  Bool²-quotient : BooleanRing ℓ-zero
  Bool²-quotient = freeBA ℕ QB./Im relBool²

  π : BoolHom (freeBA ℕ) Bool²-quotient
  π = QB.quotientImageHom

  gens→Bool² : ℕ → ⟨ Bool² ⟩
  gens→Bool² 0 = (true , false)
  gens→Bool² 1 = (false , true)
  gens→Bool² (suc (suc n)) = (false , false)

  freeBool→Bool² : BoolHom (freeBA ℕ) Bool²
  freeBool→Bool² = inducedBAHom ℕ Bool² gens→Bool²

  open BooleanRingStr (snd Bool²) using () renaming (_+_ to _+²_ ; _·_ to _·²_ ; 𝟘 to 𝟘² ; 𝟙 to 𝟙²)
  open IsCommRingHom (snd freeBool→Bool²) renaming (pres1 to presB1 ; pres+ to presB+ ; pres· to presB·)

  freeBool→Bool²-on-rels : (n : ℕ) → fst freeBool→Bool² (relBool² n) ≡ 𝟘²
  freeBool→Bool²-on-rels 0 =
    fst freeBool→Bool² (g₀ ·free g₁)
      ≡⟨ presB· g₀ g₁ ⟩
    fst freeBool→Bool² g₀ ·² fst freeBool→Bool² g₁
      ≡⟨ cong₂ _·²_ (evalBAInduce ℕ Bool² gens→Bool² ≡$ 0) (evalBAInduce ℕ Bool² gens→Bool² ≡$ 1) ⟩
    𝟘² ∎
  freeBool→Bool²-on-rels 1 =
    fst freeBool→Bool² (𝟙 +free g₀ +free g₁)
      ≡⟨ presB+ (𝟙 +free g₀) g₁ ⟩
    fst freeBool→Bool² (𝟙 +free g₀) +² fst freeBool→Bool² g₁
      ≡⟨ cong₂ _+²_ (presB+ 𝟙 g₀) (evalBAInduce ℕ Bool² gens→Bool² ≡$ 1) ⟩
    (fst freeBool→Bool² 𝟙 +² fst freeBool→Bool² g₀) +² (false , true)
      ≡⟨ cong₂ _+²_ (cong₂ _+²_ presB1 (evalBAInduce ℕ Bool² gens→Bool² ≡$ 0)) refl ⟩
    𝟘² ∎
  freeBool→Bool²-on-rels (suc (suc n)) =
    fst freeBool→Bool² (generator (suc (suc n)))
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ (suc (suc n)) ⟩
    𝟘² ∎

  quotient→Bool² : BoolHom Bool²-quotient Bool²
  quotient→Bool² = QB.inducedHom Bool² freeBool→Bool² freeBool→Bool²-on-rels

  Bool²→quotient-fun : ⟨ Bool² ⟩ → ⟨ Bool²-quotient ⟩
  Bool²→quotient-fun (false , false) = BooleanRingStr.𝟘 (snd Bool²-quotient)
  Bool²→quotient-fun (false , true)  = fst π g₁
  Bool²→quotient-fun (true , false)  = fst π g₀
  Bool²→quotient-fun (true , true)   = BooleanRingStr.𝟙 (snd Bool²-quotient)

  private
    open BooleanRingStr (snd Bool²-quotient) using () renaming (_+_ to _+Q_ ; _·_ to _·Q_ ; 𝟘 to 𝟘Q ; 𝟙 to 𝟙Q)
    open BooleanAlgebraStr (snd Bool²-quotient) using () renaming (characteristic2 to char2Q-raw ; ∧AnnihilL to annihilLQ ; ∧AnnihilR to annihilRQ)
    open import Cubical.Tactics.CommRingSolver
    open import Cubical.HITs.SetQuotients as SQ

    char2Q : (x : ⟨ Bool²-quotient ⟩) → x +Q x ≡ 𝟘Q
    char2Q x = char2Q-raw {x}

    g₀+g₁≡𝟙Q : fst π g₀ +Q fst π g₁ ≡ 𝟙Q
    g₀+g₁≡𝟙Q =
      fst π g₀ +Q fst π g₁
        ≡⟨ cong (_+Q fst π g₁) (sym (BooleanRingStr.+IdL (snd Bool²-quotient) (fst π g₀))) ⟩
      𝟘Q +Q fst π g₀ +Q fst π g₁
        ≡⟨ cong (λ z → z +Q fst π g₀ +Q fst π g₁) (sym (char2Q 𝟙Q)) ⟩
      (𝟙Q +Q 𝟙Q) +Q fst π g₀ +Q fst π g₁
        ≡⟨ solve! (BooleanRing→CommRing Bool²-quotient) ⟩
      𝟙Q +Q (𝟙Q +Q fst π g₀ +Q fst π g₁)
        ≡⟨ cong (𝟙Q +Q_) combined ⟩
      𝟙Q +Q 𝟘Q
        ≡⟨ BooleanRingStr.+IdR (snd Bool²-quotient) 𝟙Q ⟩
      𝟙Q ∎
      where
        combined : 𝟙Q +Q fst π g₀ +Q fst π g₁ ≡ 𝟘Q
        combined =
          𝟙Q +Q fst π g₀ +Q fst π g₁
            ≡⟨ cong (λ z → z +Q fst π g₀ +Q fst π g₁) (sym (IsCommRingHom.pres1 (snd π))) ⟩
          fst π 𝟙 +Q fst π g₀ +Q fst π g₁
            ≡⟨ cong (_+Q fst π g₁) (sym (IsCommRingHom.pres+ (snd π) 𝟙 g₀)) ⟩
          fst π (𝟙 +free g₀) +Q fst π g₁
            ≡⟨ sym (IsCommRingHom.pres+ (snd π) (𝟙 +free g₀) g₁) ⟩
          fst π (𝟙 +free g₀ +free g₁)
            ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} 1 ⟩
          𝟘Q ∎

    g₁+g₀≡𝟙Q : fst π g₁ +Q fst π g₀ ≡ 𝟙Q
    g₁+g₀≡𝟙Q =
      fst π g₁ +Q fst π g₀
        ≡⟨ BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀) ⟩
      fst π g₀ +Q fst π g₁
        ≡⟨ g₀+g₁≡𝟙Q ⟩
      𝟙Q ∎

    g₀≡g₁+𝟙Q : fst π g₀ ≡ fst π g₁ +Q 𝟙Q
    g₀≡g₁+𝟙Q =
      fst π g₀
        ≡⟨ sym (BooleanRingStr.+IdL (snd Bool²-quotient) (fst π g₀)) ⟩
      𝟘Q +Q fst π g₀
        ≡⟨ cong (_+Q fst π g₀) (sym (char2Q (fst π g₁))) ⟩
      (fst π g₁ +Q fst π g₁) +Q fst π g₀
        ≡⟨ solve! (BooleanRing→CommRing Bool²-quotient) ⟩
      fst π g₁ +Q (fst π g₁ +Q fst π g₀)
        ≡⟨ cong (fst π g₁ +Q_) g₁+g₀≡𝟙Q ⟩
      fst π g₁ +Q 𝟙Q ∎

    g₁≡g₀+𝟙Q : fst π g₁ ≡ fst π g₀ +Q 𝟙Q
    g₁≡g₀+𝟙Q =
      fst π g₁
        ≡⟨ sym (BooleanRingStr.+IdL (snd Bool²-quotient) (fst π g₁)) ⟩
      𝟘Q +Q fst π g₁
        ≡⟨ cong (_+Q fst π g₁) (sym (char2Q (fst π g₀))) ⟩
      (fst π g₀ +Q fst π g₀) +Q fst π g₁
        ≡⟨ solve! (BooleanRing→CommRing Bool²-quotient) ⟩
      fst π g₀ +Q (fst π g₀ +Q fst π g₁)
        ≡⟨ cong (fst π g₀ +Q_) g₀+g₁≡𝟙Q ⟩
      fst π g₀ +Q 𝟙Q ∎

    g₀·g₁≡𝟘Q : fst π g₀ ·Q fst π g₁ ≡ 𝟘Q
    g₀·g₁≡𝟘Q =
      fst π g₀ ·Q fst π g₁
        ≡⟨ sym (IsCommRingHom.pres· (snd π) g₀ g₁) ⟩
      fst π (g₀ ·free g₁)
        ≡⟨ QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} 0 ⟩
      𝟘Q ∎

    g₁·g₀≡𝟘Q : fst π g₁ ·Q fst π g₀ ≡ 𝟘Q
    g₁·g₀≡𝟘Q =
      fst π g₁ ·Q fst π g₀
        ≡⟨ BooleanRingStr.·Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀) ⟩
      fst π g₀ ·Q fst π g₁
        ≡⟨ g₀·g₁≡𝟘Q ⟩
      𝟘Q ∎

  Bool²→quotient-pres+ : (x y : ⟨ Bool² ⟩) → Bool²→quotient-fun (x +² y) ≡ Bool²→quotient-fun x +Q Bool²→quotient-fun y
  Bool²→quotient-pres+ (false , false) (false , false) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , false) (false , true) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , false) (true , false) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , false) (true , true) = sym (BooleanRingStr.+IdL (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , true) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (false , true) (false , true) =
    sym (char2Q (fst π g₁))
  Bool²→quotient-pres+ (false , true) (true , false) =
    sym g₁+g₀≡𝟙Q
  Bool²→quotient-pres+ (false , true) (true , true) =
    g₀≡g₁+𝟙Q
  Bool²→quotient-pres+ (true , false) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (true , false) (false , true) =
    Bool²→quotient-pres+ (false , true) (true , false) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) (fst π g₀)
  Bool²→quotient-pres+ (true , false) (true , false) =
    sym (char2Q (fst π g₀))
  Bool²→quotient-pres+ (true , false) (true , true) =
    g₁≡g₀+𝟙Q
  Bool²→quotient-pres+ (true , true) (false , false) = sym (BooleanRingStr.+IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres+ (true , true) (false , true) =
    Bool²→quotient-pres+ (false , true) (true , true) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₁) 𝟙Q
  Bool²→quotient-pres+ (true , true) (true , false) =
    Bool²→quotient-pres+ (true , false) (true , true) ∙
    BooleanRingStr.+Comm (snd Bool²-quotient) (fst π g₀) 𝟙Q
  Bool²→quotient-pres+ (true , true) (true , true) =
    sym (char2Q 𝟙Q)

  Bool²→quotient-pres· : (x y : ⟨ Bool² ⟩) → Bool²→quotient-fun (x ·² y) ≡ Bool²→quotient-fun x ·Q Bool²→quotient-fun y
  Bool²→quotient-pres· (false , false) y = sym annihilLQ
  Bool²→quotient-pres· (false , true) (false , false) = sym annihilRQ
  Bool²→quotient-pres· (false , true) (false , true) =
    sym (BooleanRingStr.·Idem (snd Bool²-quotient) (fst π g₁))
  Bool²→quotient-pres· (false , true) (true , false) =
    sym g₁·g₀≡𝟘Q
  Bool²→quotient-pres· (false , true) (true , true) =
    sym (BooleanRingStr.·IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres· (true , false) (false , false) = sym annihilRQ
  Bool²→quotient-pres· (true , false) (false , true) =
    Bool²→quotient-pres· (false , true) (true , false) ∙
    BooleanRingStr.·Comm (snd Bool²-quotient) _ _
  Bool²→quotient-pres· (true , false) (true , false) =
    sym (BooleanRingStr.·Idem (snd Bool²-quotient) (fst π g₀))
  Bool²→quotient-pres· (true , false) (true , true) =
    sym (BooleanRingStr.·IdR (snd Bool²-quotient) _)
  Bool²→quotient-pres· (true , true) y = sym (BooleanRingStr.·IdL (snd Bool²-quotient) _)

  Bool²→quotient : BoolHom Bool² Bool²-quotient
  Bool²→quotient = Bool²→quotient-fun , record
    { pres0 = refl
    ; pres1 = refl
    ; pres+ = Bool²→quotient-pres+
    ; pres· = Bool²→quotient-pres·
    ; pres- = λ _ → BooleanAlgebraStr.-IsId (snd Bool²-quotient)
    }

  roundtrip-Bool² : (x : ⟨ Bool² ⟩) → fst quotient→Bool² (Bool²→quotient-fun x) ≡ x
  roundtrip-Bool² (false , false) = IsCommRingHom.pres0 (snd quotient→Bool²)
  roundtrip-Bool² (false , true) =
    fst (quotient→Bool² ∘cr π) g₁
      ≡⟨ cong (λ h → fst h g₁) (QB.evalInduce Bool²) ⟩
    fst freeBool→Bool² g₁
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ 1 ⟩
    (false , true) ∎
  roundtrip-Bool² (true , false) =
    fst (quotient→Bool² ∘cr π) g₀
      ≡⟨ cong (λ h → fst h g₀) (QB.evalInduce Bool²) ⟩
    fst freeBool→Bool² g₀
      ≡⟨ evalBAInduce ℕ Bool² gens→Bool² ≡$ 0 ⟩
    (true , false) ∎
  roundtrip-Bool² (true , true) = IsCommRingHom.pres1 (snd quotient→Bool²)

  composite-on-gens : (n : ℕ) → fst Bool²→quotient (fst quotient→Bool² (fst π (generator n))) ≡ fst π (generator n)
  composite-on-gens 0 =
    fst Bool²→quotient (fst quotient→Bool² (fst π g₀))
      ≡⟨ cong (fst Bool²→quotient) (roundtrip-Bool² (true , false)) ⟩
    fst π g₀ ∎
  composite-on-gens 1 =
    fst Bool²→quotient (fst quotient→Bool² (fst π g₁))
      ≡⟨ cong (fst Bool²→quotient) (roundtrip-Bool² (false , true)) ⟩
    fst π g₁ ∎
  composite-on-gens (suc (suc n)) =
    fst Bool²→quotient (fst quotient→Bool² (fst π (generator (suc (suc n)))))
      ≡⟨ cong (fst Bool²→quotient ∘ fst quotient→Bool²) (QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} (suc (suc n))) ⟩
    fst Bool²→quotient (fst quotient→Bool² 𝟘Q)
      ≡⟨ cong (fst Bool²→quotient) (IsCommRingHom.pres0 (snd quotient→Bool²)) ⟩
    fst Bool²→quotient 𝟘²
      ≡⟨ IsCommRingHom.pres0 (snd Bool²→quotient) ⟩
    𝟘Q
      ≡⟨ sym (QB.zeroOnImage {B = freeBA ℕ} {f = relBool²} (suc (suc n))) ⟩
    fst π (generator (suc (suc n))) ∎

  composite-eq-π : Bool²→quotient ∘cr quotient→Bool² ∘cr π ≡ π
  composite-eq-π = sym (inducedBAHomUnique ℕ Bool²-quotient (fst π ∘ generator)
                                      (Bool²→quotient ∘cr quotient→Bool² ∘cr π)
                                      (funExt composite-on-gens)) ∙
                   inducedBAHomUnique ℕ Bool²-quotient (fst π ∘ generator) π refl

  opaque
    unfolding QB._/Im_
    unfolding QB.quotientImageHom
    roundtrip-quotient : (x : ⟨ Bool²-quotient ⟩) → fst Bool²→quotient (fst quotient→Bool² x) ≡ x
    roundtrip-quotient = SQ.elimProp (λ _ → BooleanRingStr.is-set (snd Bool²-quotient) _ _)
                         (λ a → funExt⁻ (cong fst composite-eq-π) a)

  Bool²≃quotient : BooleanRingEquiv Bool² Bool²-quotient
  Bool²≃quotient = (fst Bool²→quotient , isoToIsEquiv (iso (fst Bool²→quotient) (fst quotient→Bool²) roundtrip-quotient roundtrip-Bool²)) ,
                   snd Bool²→quotient

open Bool²-presentation hiding (π)

Bool²-has-Boole-ω' : has-Boole-ω' Bool²
Bool²-has-Boole-ω' = relBool² , Bool²≃quotient

Bool²-Booleω : Booleω
Bool²-Booleω = Bool² , ∣ Bool²-has-Boole-ω' ∣₁

proj₁-Bool²-hom : BoolHom Bool² BoolBR
fst proj₁-Bool²-hom = fst
snd proj₁-Bool²-hom .IsCommRingHom.pres0 = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres1 = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres+ _ _ = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres· _ _ = refl
snd proj₁-Bool²-hom .IsCommRingHom.pres- _ = refl

proj₂-Bool²-hom : BoolHom Bool² BoolBR
fst proj₂-Bool²-hom = snd
snd proj₂-Bool²-hom .IsCommRingHom.pres0 = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres1 = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres+ _ _ = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres· _ _ = refl
snd proj₂-Bool²-hom .IsCommRingHom.pres- _ = refl

classify-Bool²-hom : (h : Sp Bool²-Booleω) → (h ≡ proj₁-Bool²-hom) ⊎.⊎ (h ≡ proj₂-Bool²-hom)
classify-Bool²-hom h = helper (fst h Bool²-unit-left) refl
  where
  h-ur-complement : (b : Bool) → fst h Bool²-unit-left ≡ b
                   → fst h Bool²-unit-right ≡ not b
  h-ur-complement b h-ul-b =
    fst h (false , true)
      ≡⟨ IsCommRingHom.pres+ (snd h) (true , true) (true , false) ⟩
    (fst h (true , true)) ⊕ (fst h (true , false))
      ≡⟨ cong₂ _⊕_ (IsCommRingHom.pres1 (snd h)) h-ul-b ⟩
    not b ∎

  h≡proj₁ : fst h Bool²-unit-left ≡ true → h ≡ proj₁-Bool²-hom
  h≡proj₁ h-ul-true = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing Bool²)) f (snd (BooleanRing→CommRing BoolBR)))
    (sym (funExt λ { (false , false) → sym (IsCommRingHom.pres0 (snd h))
                   ; (false , true) → sym (h-ur-complement true h-ul-true)
                   ; (true , false) → sym h-ul-true
                   ; (true , true) → sym (IsCommRingHom.pres1 (snd h)) }))

  h≡proj₂ : fst h Bool²-unit-left ≡ false → h ≡ proj₂-Bool²-hom
  h≡proj₂ h-ul-false = Σ≡Prop (λ f → isPropIsCommRingHom (snd (BooleanRing→CommRing Bool²)) f (snd (BooleanRing→CommRing BoolBR)))
    (sym (funExt λ { (false , false) → sym (IsCommRingHom.pres0 (snd h))
                   ; (false , true) → sym (h-ur-complement false h-ul-false)
                   ; (true , false) → sym h-ul-false
                   ; (true , true) → sym (IsCommRingHom.pres1 (snd h)) }))

  helper : (b : Bool) → fst h Bool²-unit-left ≡ b → (h ≡ proj₁-Bool²-hom) ⊎.⊎ (h ≡ proj₂-Bool²-hom)
  helper true = λ eq → ⊎.inl (h≡proj₁ eq)
  helper false = λ eq → ⊎.inr (h≡proj₂ eq)

Sp-Bool²→Bool : Sp Bool²-Booleω → Bool
Sp-Bool²→Bool h = fst h Bool²-unit-left

Bool→Sp-Bool² : Bool → Sp Bool²-Booleω
Bool→Sp-Bool² true = proj₁-Bool²-hom
Bool→Sp-Bool² false = proj₂-Bool²-hom

Sp-Bool²→Bool→Sp-Bool² : (h : Sp Bool²-Booleω) → Bool→Sp-Bool² (Sp-Bool²→Bool h) ≡ h
Sp-Bool²→Bool→Sp-Bool² h with classify-Bool²-hom h
... | ⊎.inl h≡proj₁ =
  Bool→Sp-Bool² (Sp-Bool²→Bool h)
    ≡⟨ cong Bool→Sp-Bool² (cong (λ g → fst g Bool²-unit-left) h≡proj₁) ⟩
  proj₁-Bool²-hom
    ≡⟨ sym h≡proj₁ ⟩
  h ∎
... | ⊎.inr h≡proj₂ =
  Bool→Sp-Bool² (Sp-Bool²→Bool h)
    ≡⟨ cong Bool→Sp-Bool² (cong (λ g → fst g Bool²-unit-left) h≡proj₂) ⟩
  proj₂-Bool²-hom
    ≡⟨ sym h≡proj₂ ⟩
  h ∎

Bool→Sp-Bool²→Bool : (b : Bool) → Sp-Bool²→Bool (Bool→Sp-Bool² b) ≡ b
Bool→Sp-Bool²→Bool true = refl
Bool→Sp-Bool²→Bool false = refl

Sp-Bool²≃Bool : Sp Bool²-Booleω ≃ Bool
Sp-Bool²≃Bool = isoToEquiv (iso Sp-Bool²→Bool Bool→Sp-Bool² Bool→Sp-Bool²→Bool Sp-Bool²→Bool→Sp-Bool²)

-- tex definition (line 554-559): div2 ≡ half, parity ≡ isEvenB (from Part01)

f-on-gen : ℕ → ⟨ B∞×B∞ ⟩
f-on-gen n with isEvenB n
... | true  = g∞ (half n) , 𝟘∞
... | false = 𝟘∞ , g∞ (half n)

open BooleanRingStr (snd B∞×B∞) using () renaming (_·_ to _·×_ ; 𝟘 to 𝟘×) public

open import Cubical.Algebra.Ring.Properties using (module RingTheory)

private
  B∞-Ring = CommRing→Ring (BooleanRing→CommRing B∞)
  module B∞-RT = RingTheory B∞-Ring

0∞-absorbs-left : (x : ⟨ B∞ ⟩) → 𝟘∞ ·∞ x ≡ 𝟘∞
0∞-absorbs-left x = B∞-RT.0LeftAnnihilates x

0∞-absorbs-right : (x : ⟨ B∞ ⟩) → x ·∞ 𝟘∞ ≡ 𝟘∞
0∞-absorbs-right x = B∞-RT.0RightAnnihilates x

inl-inr-mult-zero : (x y : ⟨ B∞ ⟩) → (x , 𝟘∞) ·× (𝟘∞ , y) ≡ (𝟘∞ , 𝟘∞)
inl-inr-mult-zero x y =
  (x ·∞ 𝟘∞ , 𝟘∞ ·∞ y)  ≡⟨ cong₂ _,_ (0∞-absorbs-right x) (0∞-absorbs-left y) ⟩
  (𝟘∞ , 𝟘∞) ∎

inr-inl-mult-zero : (x y : ⟨ B∞ ⟩) → (𝟘∞ , x) ·× (y , 𝟘∞) ≡ (𝟘∞ , 𝟘∞)
inr-inl-mult-zero x y =
  (𝟘∞ ·∞ y , x ·∞ 𝟘∞)  ≡⟨ cong₂ _,_ (0∞-absorbs-left y) (0∞-absorbs-right x) ⟩
  (𝟘∞ , 𝟘∞) ∎

double-half-even : (n : ℕ) → isEvenB n ≡ true → n ≡ half n +ℕ half n
double-half-even n p =
  n                ≡⟨ sym (2·half-even n p) ⟩
  2 ·ℕ (half n)    ≡⟨ cong (half n +ℕ_) (+-zero (half n)) ⟩
  half n +ℕ half n ∎

double-half-odd : (n : ℕ) → isEvenB n ≡ false → n ≡ suc (half n +ℕ half n)
double-half-odd n p =
  n                        ≡⟨ sym (suc-2·half-odd n p) ⟩
  suc (2 ·ℕ (half n))      ≡⟨ cong (suc ∘ (half n +ℕ_)) (+-zero (half n)) ⟩
  suc (half n +ℕ half n)   ∎

import Agda.Builtin.Equality as BEq
builtin→Path-Bool : {a b : Bool} → a BEq.≡ b → a ≡ b
builtin→Path-Bool BEq.refl = refl

half-injective-even : (m n : ℕ) → isEvenB m BEq.≡ true → isEvenB n BEq.≡ true →
  half m ≡ half n → m ≡ n
half-injective-even m n pm pn = λ eq →
  double-half-even m (builtin→Path-Bool pm) ∙ cong₂ _+ℕ_ eq eq ∙ sym (double-half-even n (builtin→Path-Bool pn))

half-injective-odd : (m n : ℕ) → isEvenB m BEq.≡ false → isEvenB n BEq.≡ false →
  half m ≡ half n → m ≡ n
half-injective-odd m n pm pn = λ eq →
  double-half-odd m (builtin→Path-Bool pm) ∙ cong₂ (λ a b → suc (a +ℕ b)) eq eq ∙ sym (double-half-odd n (builtin→Path-Bool pn))

f-respects-relations : (m n : ℕ) → ¬ (m ≡ n) →
  (f-on-gen m) ·× (f-on-gen n) ≡ (𝟘∞ , 𝟘∞)
f-respects-relations m n m≠n with isEvenB m in pm | isEvenB n in pn
... | true | true = cong₂ _,_
  (g∞-distinct-mult-zero (half m) (half n) λ eq → m≠n (half-injective-even m n pm pn eq))
  (0∞-absorbs-left 𝟘∞)
... | false | false = cong₂ _,_ (0∞-absorbs-left 𝟘∞)
  (g∞-distinct-mult-zero (half m) (half n) λ eq → m≠n (half-injective-odd m n pm pn eq))
... | true | false = inl-inr-mult-zero (g∞ (half m)) (g∞ (half n))
... | false | true = inr-inl-mult-zero (g∞ (half m)) (g∞ (half n))

f-free : BoolHom (freeBA ℕ) B∞×B∞
f-free = inducedBAHom ℕ B∞×B∞ f-on-gen

f-free-on-gen : fst f-free ∘ generator ≡ f-on-gen
f-free-on-gen = evalBAInduce ℕ B∞×B∞ f-on-gen

open BooleanRingStr (snd (freeBA ℕ)) using () renaming (_·_ to _·free_)

f-free-distinct-zero : (m n : ℕ) → ¬ (m ≡ n) →
  fst f-free (gen m ·free gen n) ≡ (𝟘∞ , 𝟘∞)
f-free-distinct-zero m n m≠n =
  fst f-free (gen m ·free gen n)             ≡⟨ IsCommRingHom.pres· (snd f-free) (gen m) (gen n) ⟩
  (fst f-free (gen m)) ·× (fst f-free (gen n)) ≡⟨ cong₂ _·×_ (funExt⁻ f-free-on-gen m) (funExt⁻ f-free-on-gen n) ⟩
  f-on-gen m ·× f-on-gen n                    ≡⟨ f-respects-relations m n m≠n ⟩
  (𝟘∞ , 𝟘∞) ∎

a≠a+suc-d : (a d : ℕ) → ¬ (a ≡ a +ℕ suc d)
a≠a+suc-d a d eq = znots (inj-m+ (+-zero a ∙ eq))

f-free-on-relB∞ : (k : ℕ) → fst f-free (relB∞ k) ≡ (𝟘∞ , 𝟘∞)
f-free-on-relB∞ k =
  let (a , d) = cantorUnpair k
  in f-free-distinct-zero a (a +ℕ suc d) (a≠a+suc-d a d)

f : BoolHom B∞ B∞×B∞
f = QB.inducedHom B∞×B∞ f-free f-free-on-relB∞

opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  f-eval : f ∘cr π∞ ≡ f-free
  f-eval = QB.evalInduce {B = freeBA ℕ} {f = relB∞} B∞×B∞

f-on-gen-eq : (n : ℕ) → fst f (g∞ n) ≡ f-on-gen n
f-on-gen-eq n =
  fst f (fst π∞ (gen n))              ≡⟨ funExt⁻ (cong fst f-eval) (gen n) ⟩
  fst f-free (gen n)                  ≡⟨ funExt⁻ f-free-on-gen n ⟩
  f-on-gen n ∎

f-odd-gen : (k : ℕ) → fst f (g∞ (suc (2 ·ℕ k))) ≡ (𝟘∞ , g∞ k)
f-odd-gen k =
  fst f (g∞ (suc (2 ·ℕ k)))
    ≡⟨ f-on-gen-eq (suc (2 ·ℕ k)) ⟩
  f-on-gen (suc (2 ·ℕ k))
    ≡⟨ f-on-gen-odd k ⟩
  (𝟘∞ , g∞ k) ∎
  where
  f-on-gen-odd : (k : ℕ) → f-on-gen (suc (2 ·ℕ k)) ≡ (𝟘∞ , g∞ k)
  f-on-gen-odd k with isEvenB (suc (2 ·ℕ k)) in par-eq
  ... | false = cong (𝟘∞ ,_) (cong g∞ (half-2k+1 k))
  ... | true = ex-falso (false≢true (sym (isEvenB-2k+1 k) ∙ builtin→Path-Bool par-eq))

f-even-gen : (k : ℕ) → fst f (g∞ (2 ·ℕ k)) ≡ (g∞ k , 𝟘∞)
f-even-gen k =
  fst f (g∞ (2 ·ℕ k))
    ≡⟨ f-on-gen-eq (2 ·ℕ k) ⟩
  f-on-gen (2 ·ℕ k)
    ≡⟨ f-on-gen-even k ⟩
  (g∞ k , 𝟘∞) ∎
  where
  f-on-gen-even : (k : ℕ) → f-on-gen (2 ·ℕ k) ≡ (g∞ k , 𝟘∞)
  f-on-gen-even k with isEvenB (2 ·ℕ k) in par-eq
  ... | true = cong (_, 𝟘∞) (cong g∞ (half-2k k))
  ... | false = ex-falso (true≢false (sym (isEvenB-2k k) ∙ builtin→Path-Bool par-eq))

-- tex Injectivity of f (tex line 567-583)

open BooleanRingStr (snd B∞) using () renaming (_+_ to _+∞_ ; -_ to -∞_) public

_∨∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
a ∨∞ b = a +∞ b +∞ (a ·∞ b)

_∧∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
a ∧∞ b = a ·∞ b

¬∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩
¬∞ a = 𝟙∞ +∞ a

open import Cubical.Data.List hiding (map)

finJoin∞ : List ℕ → ⟨ B∞ ⟩
finJoin∞ [] = 𝟘∞
finJoin∞ (n ∷ ns) = g∞ n ∨∞ finJoin∞ ns

finMeetNeg∞ : List ℕ → ⟨ B∞ ⟩
finMeetNeg∞ [] = 𝟙∞
finMeetNeg∞ (n ∷ ns) = (¬∞ g∞ n) ∧∞ finMeetNeg∞ ns

data B∞-NormalForm : Type₀ where
  joinForm : List ℕ → B∞-NormalForm
  meetNegForm : List ℕ → B∞-NormalForm

⟦_⟧nf : B∞-NormalForm → ⟨ B∞ ⟩
⟦ joinForm ns ⟧nf = finJoin∞ ns
⟦ meetNegForm ns ⟧nf = finMeetNeg∞ ns

splitByParity : List ℕ → List ℕ × List ℕ
splitByParity [] = [] , []
splitByParity (n ∷ ns) with isEven n | splitByParity ns
... | true  | (evens , odds) = half n ∷ evens , odds
... | false | (evens , odds) = evens , half n ∷ odds

open BooleanRingStr (snd B∞×B∞) using () renaming (_+_ to _+×_ ; _·_ to _·×'_ ; 𝟘 to 𝟘× ; 𝟙 to 𝟙×) public

_∨×_ : ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞ ⟩
(a₁ , a₂) ∨× (b₁ , b₂) = (a₁ ∨∞ b₁ , a₂ ∨∞ b₂)

f-pres+ : (a b : ⟨ B∞ ⟩) → fst f (a +∞ b) ≡ (fst f a) +× (fst f b)
f-pres+ a b = IsCommRingHom.pres+ (snd f) a b

f-pres-join : (a b : ⟨ B∞ ⟩) → fst f (a ∨∞ b) ≡ ((fst f a) ∨× (fst f b))
f-pres-join a b =
  fst f (a ∨∞ b)
    ≡⟨ f-pres+ (a +∞ b) (a ·∞ b) ⟩
  fst f (a +∞ b) +× fst f (a ·∞ b)
    ≡⟨ cong₂ _+×_ (f-pres+ a b) (IsCommRingHom.pres· (snd f) a b) ⟩
  (fst f a) ∨× (fst f b) ∎

zero-join-left : (x : ⟨ B∞ ⟩) → 𝟘∞ ∨∞ x ≡ x
zero-join-left _ = BooleanAlgebraStr.∨IdL (snd B∞)

zero-join-right : (x : ⟨ B∞ ⟩) → x ∨∞ 𝟘∞ ≡ x
zero-join-right _ = BooleanAlgebraStr.∨IdR (snd B∞)

isEven≡isEvenB : (n : ℕ) → isEven n ≡ isEvenB n
isEven≡isEvenB zero = refl
isEven≡isEvenB (suc zero) = refl
isEven≡isEvenB (suc (suc n)) = isEven≡isEvenB n

isEven→even : (n : ℕ) → isEven n ≡ true → 2 ·ℕ (half n) ≡ n
isEven→even n prf = 2·half-even n (sym (isEven≡isEvenB n) ∙ prf)

isEven→odd : (n : ℕ) → isEven n ≡ false → suc (2 ·ℕ (half n)) ≡ n
isEven→odd n prf = suc-2·half-odd n (sym (isEven≡isEvenB n) ∙ prf)

f-on-gen-even : (n : ℕ) → isEven n ≡ true → fst f (g∞ n) ≡ (g∞ (half n) , 𝟘∞)
f-on-gen-even n even-prf =
  fst f (g∞ n)                    ≡⟨ cong (λ m → fst f (g∞ m)) (sym (isEven→even n even-prf)) ⟩
  fst f (g∞ (2 ·ℕ (half n)))      ≡⟨ f-even-gen (half n) ⟩
  (g∞ (half n) , 𝟘∞) ∎

f-on-gen-odd : (n : ℕ) → isEven n ≡ false → fst f (g∞ n) ≡ (𝟘∞ , g∞ (half n))
f-on-gen-odd n odd-prf =
  fst f (g∞ n)                         ≡⟨ cong (λ m → fst f (g∞ m)) (sym (isEven→odd n odd-prf)) ⟩
  fst f (g∞ (suc (2 ·ℕ (half n))))     ≡⟨ f-odd-gen (half n) ⟩
  (𝟘∞ , g∞ (half n)) ∎

f-on-finJoin : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in fst f (finJoin∞ ns) ≡ (finJoin∞ evens , finJoin∞ odds)
f-on-finJoin [] = IsCommRingHom.pres0 (snd f)
f-on-finJoin (n ∷ ns) with isEven n in isEvenB-eq | splitByParity ns | f-on-finJoin ns
... | true  | (evens , odds) | ih =
  fst f (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ f-pres-join (g∞ n) (finJoin∞ ns) ⟩
  (fst f (g∞ n)) ∨× (fst f (finJoin∞ ns))
    ≡⟨ cong₂ _∨×_ (f-on-gen-even n (builtin→Path-Bool isEvenB-eq)) ih ⟩
  (g∞ (half n) ∨∞ finJoin∞ evens , 𝟘∞ ∨∞ finJoin∞ odds)
    ≡⟨ cong (g∞ (half n) ∨∞ finJoin∞ evens ,_) (zero-join-left (finJoin∞ odds)) ⟩
  (finJoin∞ (half n ∷ evens) , finJoin∞ odds) ∎
... | false | (evens , odds) | ih =
  fst f (g∞ n ∨∞ finJoin∞ ns)
    ≡⟨ f-pres-join (g∞ n) (finJoin∞ ns) ⟩
  (fst f (g∞ n)) ∨× (fst f (finJoin∞ ns))
    ≡⟨ cong₂ _∨×_ (f-on-gen-odd n (builtin→Path-Bool isEvenB-eq)) ih ⟩
  (𝟘∞ ∨∞ finJoin∞ evens , g∞ (half n) ∨∞ finJoin∞ odds)
    ≡⟨ cong (_, g∞ (half n) ∨∞ finJoin∞ odds) (zero-join-left (finJoin∞ evens)) ⟩
  (finJoin∞ evens , finJoin∞ (half n ∷ odds)) ∎

f-pres1 : fst f 𝟙∞ ≡ (𝟙∞ , 𝟙∞)
f-pres1 = IsCommRingHom.pres1 (snd f)

f-pres-neg : (x : ⟨ B∞ ⟩) → fst f (¬∞ x) ≡ (¬∞ (fst (fst f x)) , ¬∞ (snd (fst f x)))
f-pres-neg x =
  fst f (𝟙∞ +∞ x)
    ≡⟨ f-pres+ 𝟙∞ x ⟩
  (fst f 𝟙∞) +× (fst f x)
    ≡⟨ cong (_+× (fst f x)) f-pres1 ⟩
  (¬∞ (fst (fst f x)) , ¬∞ (snd (fst f x))) ∎

δ-seq : ℕ → ℕ → Bool
δ-seq n m with discreteℕ n m
... | yes _ = true
... | no _ = false

δ-seq-hamo : (n : ℕ) → hitsAtMostOnce (δ-seq n)
δ-seq-hamo n i j δi=t δj=t with discreteℕ n i | discreteℕ n j
... | yes n=i | yes n=j =
  i ≡⟨ sym n=i ⟩
  n ≡⟨ n=j ⟩
  j ∎
... | yes _ | no n≠j = ex-falso (true≢false (sym δj=t))
... | no n≠i | _ = ex-falso (true≢false (sym δi=t))

δ∞ : ℕ → ℕ∞
δ∞ n = δ-seq n , δ-seq-hamo n

δ∞-hits-n : (n : ℕ) → fst (δ∞ n) n ≡ true
δ∞-hits-n n with discreteℕ n n
... | yes _ = refl
... | no n≠n = ex-falso (n≠n refl)

module FinCof→B∞ where
  open B∞→FinCof using (φ)
  open import Cubical.Data.List hiding (map)
  open import Cubical.HITs.PropositionalTruncation as PT using (∥_∥₁; ∣_∣₁; squash₁)
  open import Cubical.Data.Bool using (_⊕_; not; if_then_else_) renaming (elim to bool-elim)
  open import Cubical.Data.Nat.Order using (_≤_)
  open import Cubical.Foundations.Function using (2-Constant)

  filterTrue : (f : ℕ → Bool) → ℕ → List ℕ
  filterTrue f zero = []
  filterTrue f (suc n) = if f n then (n ∷ filterTrue f n) else (filterTrue f n)

  filterFalse : (f : ℕ → Bool) → ℕ → List ℕ
  filterFalse f N = filterTrue (λ n → not (f n)) N

  ψ-raw : (f : ℕ → Bool) → (N : ℕ) → f N ≡ false → ⟨ B∞ ⟩
  ψ-raw f N _ = finJoin∞ (filterTrue f N)

  ψ-raw-cofin : (f : ℕ → Bool) → (N : ℕ) → f N ≡ true → ⟨ B∞ ⟩
  ψ-raw-cofin f N _ = finMeetNeg∞ (filterFalse f N)

  filterTrue-stable : (f : ℕ → Bool) (N : ℕ) → f N ≡ false →
    filterTrue f (suc N) ≡ filterTrue f N
  filterTrue-stable f N fN=false =
    cong (λ b → if b then (N ∷ filterTrue f N) else (filterTrue f N)) fN=false

  filterTrue-extend : (f : ℕ → Bool) (N k : ℕ) →
    ((n : ℕ) → N ≤ n → f n ≡ false) →
    filterTrue f (k +ℕ N) ≡ filterTrue f N
  filterTrue-extend f N zero _ = refl
  filterTrue-extend f N (suc k) all-false =
    filterTrue-stable f (k +ℕ N) (all-false (k +ℕ N) (k , refl)) ∙
    filterTrue-extend f N k all-false

  filterFalse-stable : (f : ℕ → Bool) (N : ℕ) → f N ≡ true →
    filterFalse f (suc N) ≡ filterFalse f N
  filterFalse-stable f N fN=true =
    let g = λ n → not (f n)
    in cong (λ b → if b then (N ∷ filterTrue g N) else (filterTrue g N)) (cong not fN=true)

  filterFalse-extend : (f : ℕ → Bool) (N k : ℕ) →
    ((n : ℕ) → N ≤ n → f n ≡ true) →
    filterFalse f (k +ℕ N) ≡ filterFalse f N
  filterFalse-extend f N zero _ = refl
  filterFalse-extend f N (suc k) all-true =
    filterFalse-stable f (k +ℕ N) (all-true (k +ℕ N) (k , refl)) ∙
    filterFalse-extend f N k all-true

  ψ-by-val : (f : ℕ → Bool) → (N : ℕ) → Bool → ⟨ B∞ ⟩
  ψ-by-val f N false = finJoin∞ (filterTrue f N)
  ψ-by-val f N true = finMeetNeg∞ (filterFalse f N)

  ψ-from-witness : (f : ℕ → Bool) → (N : ℕ) → ((n : ℕ) → N ≤ n → f n ≡ f N) → ⟨ B∞ ⟩
  ψ-from-witness f N _ = ψ-by-val f N (f N)

  ψ-by-val-extend : (f : ℕ → Bool) (N k : ℕ) (v : Bool) →
    ((n : ℕ) → N ≤ n → f n ≡ v) →
    ψ-by-val f (k +ℕ N) v ≡ ψ-by-val f N v
  ψ-by-val-extend f N k false all-false =
    cong finJoin∞ (filterTrue-extend f N k (λ n n≥N → all-false n n≥N))
  ψ-by-val-extend f N k true all-true =
    cong finMeetNeg∞ (filterFalse-extend f N k (λ n n≥N → all-true n n≥N))

  ψ-witness-indep : (f : ℕ → Bool) →
    (N₁ : ℕ) → (s₁ : (n : ℕ) → N₁ ≤ n → f n ≡ f N₁) →
    (N₂ : ℕ) → (s₂ : (n : ℕ) → N₂ ≤ n → f n ≡ f N₂) →
    ψ-from-witness f N₁ s₁ ≡ ψ-from-witness f N₂ s₂
  ψ-witness-indep f N₁ s₁ N₂ s₂ = step₁ ∙ sym step₂
    where
    open import Cubical.Data.Nat.Order using (≤SumLeft)

    N = N₁ +ℕ N₂

    N₁≤N : N₁ ≤ N
    N₁≤N = ≤SumLeft {n = N₁} {k = N₂}

    N₂≤N : N₂ ≤ N
    N₂≤N = subst (N₂ ≤_) (+-comm N₂ N₁) (≤SumLeft {n = N₂} {k = N₁})

    fN₁≡fN : f N₁ ≡ f N
    fN₁≡fN = sym (s₁ N N₁≤N)

    fN₂≡fN : f N₂ ≡ f N
    fN₂≡fN = sym (s₂ N N₂≤N)

    fN₁≡fN₂ : f N₁ ≡ f N₂
    fN₁≡fN₂ = fN₁≡fN ∙ sym fN₂≡fN

    s₁' : (n : ℕ) → N₁ ≤ n → f n ≡ f N₁
    s₁' = s₁

    step₁ : ψ-by-val f N₁ (f N₁) ≡ ψ-by-val f N (f N)
    step₁ =
      ψ-by-val f N₁ (f N₁)
        ≡⟨ cong (ψ-by-val f N₁) fN₁≡fN ⟩
      ψ-by-val f N₁ (f N)
        ≡⟨ sym (ψ-by-val-extend f N₁ N₂ (f N) (λ n n≥N₁ → s₁ n n≥N₁ ∙ fN₁≡fN)) ⟩
      ψ-by-val f (N₂ +ℕ N₁) (f N)
        ≡⟨ cong (λ m → ψ-by-val f m (f N)) (+-comm N₂ N₁) ⟩
      ψ-by-val f N (f N) ∎

    step₂ : ψ-by-val f N₂ (f N₂) ≡ ψ-by-val f N (f N)
    step₂ =
      ψ-by-val f N₂ (f N₂)
        ≡⟨ cong (ψ-by-val f N₂) fN₂≡fN ⟩
      ψ-by-val f N₂ (f N)
        ≡⟨ sym (ψ-by-val-extend f N₂ N₁ (f N) (λ n n≥N₂ → s₂ n n≥N₂ ∙ fN₂≡fN)) ⟩
      ψ-by-val f N (f N) ∎

  open import Cubical.Data.Bool using (_or_; _and_)
  open import Cubical.Data.Bool.Properties using (or-zeroʳ; or-comm; or-assoc; or-idem; and-zeroʳ; or-identityʳ)

  fcOr : FinCof → FinCof → FinCof
  fcOr a b = fcXor (fcXor a b) (fcAnd a b)

  fcFinJoin : List ℕ → FinCof
  fcFinJoin [] = fcEmpty
  fcFinJoin (n ∷ ns) = fcOr (fcSingleton n) (fcFinJoin ns)

  xor-and-is-or : (x y : Bool) → (x ⊕ y) ⊕ (x and y) ≡ x or y
  xor-and-is-or false false = refl
  xor-and-is-or false true = refl
  xor-and-is-or true false = refl
  xor-and-is-or true true = refl

  fcOr-pointwise : (a b : FinCof) (m : ℕ) → fst (fcOr a b) m ≡ (fst a m) or (fst b m)
  fcOr-pointwise a b m = xor-and-is-or (fst a m) (fst b m)

  memberOf : List ℕ → ℕ → Bool
  memberOf [] m = false
  memberOf (n ∷ ns) m = decToBool (discreteℕ m n) or memberOf ns m

  fcFinJoin-eval : (ns : List ℕ) (m : ℕ) → fst (fcFinJoin ns) m ≡ memberOf ns m
  fcFinJoin-eval [] m = refl
  fcFinJoin-eval (n ∷ ns) m =
    fst (fcOr (fcSingleton n) (fcFinJoin ns)) m
      ≡⟨ fcOr-pointwise (fcSingleton n) (fcFinJoin ns) m ⟩
    fst (fcSingleton n) m or fst (fcFinJoin ns) m
      ≡⟨ cong (fst (fcSingleton n) m or_) (fcFinJoin-eval ns m) ⟩
    decToBool (discreteℕ m n) or memberOf ns m ∎

  open import Cubical.Data.Bool.Properties using (or-identityˡ)
  open import Cubical.Data.Nat.Order using (≤-refl; ≤-suc; ¬m<m; ≤-antisym; <-asym'; <Dec; _<_; ≤-trans; pred-≤-pred; <-weaken; ¬-<-zero)

  m≠n→decToBool-false : (m n : ℕ) → ¬ (m ≡ n) → decToBool (discreteℕ m n) ≡ false
  m≠n→decToBool-false m n m≠n with discreteℕ m n
  ... | yes p = ex-falso (m≠n p)
  ... | no _ = refl

  filterTrue-outside : (f : ℕ → Bool) (N m : ℕ) → N ≤ m →
    memberOf (filterTrue f N) m ≡ false
  filterTrue-outside f zero m _ = refl
  filterTrue-outside f (suc N) m sN≤m with f N in fNeq
  ... | false = filterTrue-outside f N m (<-weaken sN≤m)
  ... | true =
    let N≤m : N ≤ m
        N≤m = <-weaken sN≤m
        m≠N : ¬ (m ≡ N)
        m≠N p = ¬m<m {N} (subst (suc N ≤_) p sN≤m)
    in
    decToBool (discreteℕ m N) or memberOf (filterTrue f N) m
      ≡⟨ cong (_or memberOf (filterTrue f N) m) (m≠n→decToBool-false m N m≠N) ⟩
    false or memberOf (filterTrue f N) m
      ≡⟨ or-identityˡ _ ⟩
    memberOf (filterTrue f N) m
      ≡⟨ filterTrue-outside f N m N≤m ⟩
    false ∎

  filterTrue-suc : (f : ℕ → Bool) (N m : ℕ) →
    memberOf (if f N then (N ∷ filterTrue f N) else filterTrue f N) m ≡
    (f N and decToBool (discreteℕ m N)) or memberOf (filterTrue f N) m
  filterTrue-suc f N m with f N
  ... | true  = refl
  ... | false = refl

  and-true-right : (b : Bool) → b and true ≡ b
  and-true-right false = refl
  and-true-right true = refl

  filterTrue-spec : (f : ℕ → Bool) (N m : ℕ) → m < N →
    memberOf (filterTrue f N) m ≡ f m
  filterTrue-spec f zero m m<0 = ex-falso (¬-<-zero m<0)
  filterTrue-spec f (suc N) m m<sN with <Dec m N
  ... | yes m<N =
    memberOf (filterTrue f (suc N)) m
      ≡⟨ filterTrue-suc f N m ⟩
    (f N and decToBool (discreteℕ m N)) or memberOf (filterTrue f N) m
      ≡⟨ cong (λ d → (f N and d) or memberOf (filterTrue f N) m) (m≠n→decToBool-false m N (λ p → ¬m<m (subst (_< N) p m<N))) ⟩
    (f N and false) or memberOf (filterTrue f N) m
      ≡⟨ cong (_or memberOf (filterTrue f N) m) (and-zeroʳ (f N)) ⟩
    false or memberOf (filterTrue f N) m
      ≡⟨ or-identityˡ _ ⟩
    memberOf (filterTrue f N) m
      ≡⟨ filterTrue-spec f N m m<N ⟩
    f m ∎
  ... | no ¬m<N =
    let m≡N : m ≡ N
        m≡N = ≤-antisym (pred-≤-pred m<sN) (<-asym' ¬m<N)
    in
    memberOf (filterTrue f (suc N)) m
      ≡⟨ filterTrue-suc f N m ⟩
    (f N and decToBool (discreteℕ m N)) or memberOf (filterTrue f N) m
      ≡⟨ cong (λ k → (f N and decToBool (discreteℕ k N)) or memberOf (filterTrue f N) k) m≡N ⟩
    (f N and decToBool (discreteℕ N N)) or memberOf (filterTrue f N) N
      ≡⟨ cong (λ d → (f N and d) or memberOf (filterTrue f N) N) (fcSingleton-self N) ⟩
    (f N and true) or memberOf (filterTrue f N) N
      ≡⟨ cong (_or memberOf (filterTrue f N) N) (and-true-right (f N)) ⟩
    f N or memberOf (filterTrue f N) N
      ≡⟨ cong (f N or_) (filterTrue-outside f N N ≤-refl) ⟩
    f N or false
      ≡⟨ or-identityʳ (f N) ⟩
    f N
      ≡⟨ sym (cong f m≡N) ⟩
    f m ∎

  opaque
    φ-pres-finJoin : (ns : List ℕ) → fst φ (finJoin∞ ns) ≡ fcFinJoin ns
    φ-pres-finJoin [] = IsCommRingHom.pres0 (snd φ)
    φ-pres-finJoin (n ∷ ns) =
      let open IsCommRingHom (snd φ) renaming (pres+ to φ-pres+; pres· to φ-pres·)
      in
      fst φ (g∞ n ∨∞ finJoin∞ ns)
        ≡⟨ refl ⟩
      fst φ ((g∞ n +∞ finJoin∞ ns) +∞ (g∞ n ·∞ finJoin∞ ns))
        ≡⟨ φ-pres+ (g∞ n +∞ finJoin∞ ns) (g∞ n ·∞ finJoin∞ ns) ⟩
      fcXor (fst φ (g∞ n +∞ finJoin∞ ns)) (fst φ (g∞ n ·∞ finJoin∞ ns))
        ≡⟨ cong₂ fcXor (φ-pres+ (g∞ n) (finJoin∞ ns)) (φ-pres· (g∞ n) (finJoin∞ ns)) ⟩
      fcXor (fcXor (fst φ (g∞ n)) (fst φ (finJoin∞ ns)))
            (fcAnd (fst φ (g∞ n)) (fst φ (finJoin∞ ns)))
        ≡⟨ cong₂ (λ a b → fcXor (fcXor a b) (fcAnd a b)) (φ-on-gen n) (φ-pres-finJoin ns) ⟩
      fcOr (fcSingleton n) (fcFinJoin ns) ∎

  private
    isSetB∞ : isSet ⟨ B∞ ⟩
    isSetB∞ = BooleanRingStr.is-set (snd B∞)

  open PT.SetElim isSetB∞ using (rec→Set)

  ψ-const : (f : ℕ → Bool) →
    2-Constant (λ (w : Σ[ N ∈ ℕ ] ((n : ℕ) → N ≤ n → f n ≡ f N)) → ψ-from-witness f (fst w) (snd w))
  ψ-const f (N₁ , s₁) (N₂ , s₂) = ψ-witness-indep f N₁ s₁ N₂ s₂

  ψ-fun : FinCof → ⟨ B∞ ⟩
  ψ-fun (f , ec) = rec→Set
    (λ w → ψ-from-witness f (fst w) (snd w))
    (ψ-const f)
    ec

  FC≡ : {a b : FinCof} → fst a ≡ fst b → a ≡ b
  FC≡ = Σ≡Prop (λ _ → squash₁)

  fcFinMeetNeg : List ℕ → FinCof
  fcFinMeetNeg [] = fcFull
  fcFinMeetNeg (n ∷ ns) = fcAnd (fcNot (fcSingleton n)) (fcFinMeetNeg ns)

  notMemberOf : List ℕ → ℕ → Bool
  notMemberOf [] m = true
  notMemberOf (n ∷ ns) m = not (decToBool (discreteℕ m n)) and notMemberOf ns m

  fcFinMeetNeg-eval : (ns : List ℕ) (m : ℕ) → fst (fcFinMeetNeg ns) m ≡ notMemberOf ns m
  fcFinMeetNeg-eval [] m = refl
  fcFinMeetNeg-eval (n ∷ ns) m =
    cong (fst (fcNot (fcSingleton n)) m and_) (fcFinMeetNeg-eval ns m)

  fcXor-fcFull≡fcNot : (x : FinCof) → fcXor fcFull x ≡ fcNot x
  fcXor-fcFull≡fcNot x = FC≡ refl

  opaque
    φ-pres-neg : (x : ⟨ B∞ ⟩) → fst φ (¬∞ x) ≡ fcNot (fst φ x)
    φ-pres-neg x =
      IsCommRingHom.pres+ (snd φ) 𝟙∞ x
      ∙ cong (λ a → fcXor a (fst φ x)) (IsCommRingHom.pres1 (snd φ))
      ∙ fcXor-fcFull≡fcNot (fst φ x)

  opaque
    φ-pres-finMeetNeg : (ns : List ℕ) → fst φ (finMeetNeg∞ ns) ≡ fcFinMeetNeg ns
    φ-pres-finMeetNeg [] = IsCommRingHom.pres1 (snd φ)
    φ-pres-finMeetNeg (n ∷ ns) =
      IsCommRingHom.pres· (snd φ) (¬∞ g∞ n) (finMeetNeg∞ ns)
      ∙ cong₂ fcAnd (φ-pres-neg (g∞ n) ∙ cong fcNot (φ-on-gen n)) (φ-pres-finMeetNeg ns)

  not-or-and : (a b : Bool) → not (a or b) ≡ not a and not b
  not-or-and false false = refl
  not-or-and false true  = refl
  not-or-and true  false = refl
  not-or-and true  true  = refl

  notMemberOf≡not-memberOf : (ns : List ℕ) (m : ℕ) →
    notMemberOf ns m ≡ not (memberOf ns m)
  notMemberOf≡not-memberOf [] m = refl
  notMemberOf≡not-memberOf (n ∷ ns) m =
    cong (not (decToBool (discreteℕ m n)) and_) (notMemberOf≡not-memberOf ns m)
    ∙ sym (not-or-and (decToBool (discreteℕ m n)) (memberOf ns m))

  not-not : (b : Bool) → not (not b) ≡ b
  not-not false = refl
  not-not true = refl

  filterFalse-spec : (f : ℕ → Bool) (N m : ℕ) → m < N →
    notMemberOf (filterFalse f N) m ≡ f m
  filterFalse-spec f N m m<N =
    notMemberOf≡not-memberOf (filterTrue (not ∘ f) N) m
    ∙ cong not (filterTrue-spec (not ∘ f) N m m<N)
    ∙ not-not (f m)

  open import Cubical.Data.Nat.Order using (zero-≤)

  filterFalse-outside : (f : ℕ → Bool) (N m : ℕ) → N ≤ m →
    notMemberOf (filterFalse f N) m ≡ true
  filterFalse-outside f N m N≤m =
    notMemberOf≡not-memberOf (filterTrue (not ∘ f) N) m
    ∙ cong not (filterTrue-outside (not ∘ f) N m N≤m)

  memberOf-filterTrue-eq : (f : ℕ → Bool) (N : ℕ) →
    ((n : ℕ) → N ≤ n → f n ≡ false) →
    (m : ℕ) → memberOf (filterTrue f N) m ≡ f m
  memberOf-filterTrue-eq f zero stab m = sym (stab m zero-≤)
  memberOf-filterTrue-eq f (suc N') stab m with <Dec m (suc N')
  ... | yes m<sN = filterTrue-spec f (suc N') m m<sN
  ... | no ¬m<sN =
    filterTrue-outside f (suc N') m (<-asym' ¬m<sN) ∙
    sym (stab m (<-asym' ¬m<sN))

  notMemberOf-filterFalse-eq : (f : ℕ → Bool) (N : ℕ) →
    ((n : ℕ) → N ≤ n → f n ≡ true) →
    (m : ℕ) → notMemberOf (filterFalse f N) m ≡ f m
  notMemberOf-filterFalse-eq f zero stab m = sym (stab m zero-≤)
  notMemberOf-filterFalse-eq f (suc N') stab m with <Dec m (suc N')
  ... | yes m<sN = filterFalse-spec f (suc N') m m<sN
  ... | no ¬m<sN =
    filterFalse-outside f (suc N') m (<-asym' ¬m<sN) ∙
    sym (stab m (<-asym' ¬m<sN))

  opaque
    unfolding φ-pres-finJoin
    φ∘ψ-finite : (f : ℕ → Bool) (N : ℕ) →
      ((n : ℕ) → N ≤ n → f n ≡ false) →
      (m : ℕ) → fst (fst φ (finJoin∞ (filterTrue f N))) m ≡ f m
    φ∘ψ-finite f N stab m =
      fst (fst φ (finJoin∞ (filterTrue f N))) m
        ≡⟨ cong (λ z → fst z m) (φ-pres-finJoin (filterTrue f N)) ⟩
      fst (fcFinJoin (filterTrue f N)) m
        ≡⟨ fcFinJoin-eval (filterTrue f N) m ⟩
      memberOf (filterTrue f N) m
        ≡⟨ memberOf-filterTrue-eq f N stab m ⟩
      f m ∎

  opaque
    unfolding φ-pres-finMeetNeg
    φ∘ψ-cofinite : (f : ℕ → Bool) (N : ℕ) →
      ((n : ℕ) → N ≤ n → f n ≡ true) →
      (m : ℕ) → fst (fst φ (finMeetNeg∞ (filterFalse f N))) m ≡ f m
    φ∘ψ-cofinite f N stab m =
      fst (fst φ (finMeetNeg∞ (filterFalse f N))) m
        ≡⟨ cong (λ z → fst z m) (φ-pres-finMeetNeg (filterFalse f N)) ⟩
      fst (fcFinMeetNeg (filterFalse f N)) m
        ≡⟨ fcFinMeetNeg-eval (filterFalse f N) m ⟩
      notMemberOf (filterFalse f N) m
        ≡⟨ notMemberOf-filterFalse-eq f N stab m ⟩
      f m ∎

  opaque
    unfolding φ∘ψ-finite
    unfolding φ∘ψ-cofinite
    φ∘ψ-by-val : (f : ℕ → Bool) (N : ℕ) (v : Bool) →
      ((n : ℕ) → N ≤ n → f n ≡ v) →
      (m : ℕ) → fst (fst φ (ψ-by-val f N v)) m ≡ f m
    φ∘ψ-by-val f N false stab = φ∘ψ-finite f N stab
    φ∘ψ-by-val f N true stab = φ∘ψ-cofinite f N stab

  opaque
    unfolding φ∘ψ-by-val
    φ∘ψ-on-witness : (f : ℕ → Bool) (N : ℕ) (stab : (n : ℕ) → N ≤ n → f n ≡ f N) →
      fst φ (ψ-from-witness f N stab) ≡ (f , ∣ N , stab ∣₁)
    φ∘ψ-on-witness f N stab =
      FC≡ {a = fst φ (ψ-by-val f N (f N))} {b = (f , ∣ N , stab ∣₁)}
          (funExt (φ∘ψ-by-val f N (f N) (λ n n≥N → stab n n≥N)))

  φ∘ψ : (x : FinCof) → fst φ (ψ-fun x) ≡ x
  φ∘ψ (f , ec) = PT.elim {P = λ e → fst φ (ψ-fun (f , e)) ≡ (f , e)}
    (λ _ → isSetFinCof _ _)
    (λ (N , stab) → φ∘ψ-on-witness f N stab)
    ec


open FinCof→B∞ public hiding (ψ-fun)

