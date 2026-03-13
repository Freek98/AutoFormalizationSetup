{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module Categorywork.work where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Unit
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as ⊥ using (⊥)

open import Cubical.Algebra.Ring
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Univalence
open import Cubical.Algebra.CommRing.FiberedProduct
open import Cubical.Algebra.BooleanRing

open import Cubical.Categories.Category
open import Cubical.Categories.Functor
open import Cubical.Categories.Instances.Sets
open import Cubical.Categories.Instances.CommRings using (CommRingsCategory ; LimitsCommRingsCategory)
open import Cubical.Categories.Limits.Terminal
open import Cubical.Categories.Limits.Pullback
open import Cubical.Categories.Limits.Limits

open import Cubical.HITs.PropositionalTruncation

open import Cubical.Algebra.CommRing.Instances.Unit

open import Cubical.Data.Sum
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)

open import Cubical.Algebra.CommRing.Properties using (_∘cr_ ; compCommRingEquiv)
open import Cubical.Algebra.Ring.Properties
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

open import BooleanRing.BoolRingUnivalence
open import BooleanRing.BooleanRingMaps
open import BooleanRing.ProductBA using (_×BR_)
open import BooleanRing.Products using (pr₁-BR ; pr₂-BR ; ⟨_,_⟩BR)
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB

open import CountablyPresentedBooleanRings.Definitions
  using (is-countably-presented ; has-countable-presentation ;
         _is-presented-by_/_)
open import BasicDefinitions using (binarySequence ; Σℕ ; has-Countability-structure)
open import Countability.Properties
open import CommRingQuotients.EquivHelper using (isoToCommRingEquiv)

open Category hiding (_∘_)
open isUnivalent
open isIso
open Functor
open BooleanRingStr
open IsCommRingHom

private
  variable
    ℓ ℓ' ℓ'' : Level

-- ═══════════════════════════════════════════════════════════════
-- Unit Boolean ring (terminal object carrier)
-- ═══════════════════════════════════════════════════════════════

UnitBR : BooleanRing ℓ-zero
UnitBR = idemCommRing→BR UnitCommRing (λ _ → refl)

-- ═══════════════════════════════════════════════════════════════
-- The category of Boolean rings
-- ═══════════════════════════════════════════════════════════════

BooleanRingsCategory : Category (ℓ-suc ℓ) ℓ
ob BooleanRingsCategory           = BooleanRing _
Hom[_,_] BooleanRingsCategory     = BoolHom
id BooleanRingsCategory {R}       = idBoolHom R
_⋆_ BooleanRingsCategory f g      = g ∘cr f
⋆IdL BooleanRingsCategory _       = CommRingHom≡ refl
⋆IdR BooleanRingsCategory _       = CommRingHom≡ refl
⋆Assoc BooleanRingsCategory _ _ _ = CommRingHom≡ refl
isSetHom BooleanRingsCategory     = isSetCommRingHom _ _

-- ═══════════════════════════════════════════════════════════════
-- Forgetful functor to Set
-- ═══════════════════════════════════════════════════════════════

ForgetfulBooleanRing→Set : Functor (BooleanRingsCategory {ℓ}) (SET ℓ)
F-ob ForgetfulBooleanRing→Set R    = R .fst , is-set (snd R)
F-hom ForgetfulBooleanRing→Set f x = f .fst x
F-id ForgetfulBooleanRing→Set      = funExt (λ _ → refl)
F-seq ForgetfulBooleanRing→Set f g = funExt (λ _ → refl)

-- ═══════════════════════════════════════════════════════════════
-- Forgetful functor to CommRings
-- ═══════════════════════════════════════════════════════════════

ForgetfulBooleanRing→CommRing : Functor (BooleanRingsCategory {ℓ}) CommRingsCategory
F-ob ForgetfulBooleanRing→CommRing  = BooleanRing→CommRing
F-hom ForgetfulBooleanRing→CommRing = idfun _
F-id ForgetfulBooleanRing→CommRing  = CommRingHom≡ refl
F-seq ForgetfulBooleanRing→CommRing _ _ = CommRingHom≡ refl

-- ═══════════════════════════════════════════════════════════════
-- BooleanRing isomorphisms ↔ categorical isomorphisms
-- ═══════════════════════════════════════════════════════════════

open Iso

module _ {R S : BooleanRing ℓ} where
  private
    R' = BooleanRing→CommRing R
    S' = BooleanRing→CommRing S

  BoolRingIsoIsoCatIso : Iso (BoolRingEquiv R S) (CatIso BooleanRingsCategory R S)
  -- forward: equiv → cat iso
  fun BoolRingIsoIsoCatIso ((f , fEqu) , fHom) .fst = f , fHom
  fun BoolRingIsoIsoCatIso ((f , fEqu) , fHom) .snd .inv =
    invEq (f , fEqu) , invCommRingEquiv R' S' ((f , fEqu) , fHom) .snd
  fun BoolRingIsoIsoCatIso ((f , fEqu) , fHom) .snd .sec =
    CommRingHom≡ (funExt (secEq (f , fEqu)))
  fun BoolRingIsoIsoCatIso ((f , fEqu) , fHom) .snd .ret =
    CommRingHom≡ (funExt (retEq (f , fEqu)))
  -- backward: cat iso → equiv
  fst (inv BoolRingIsoIsoCatIso e) =
    isoToEquiv (iso (e .fst .fst) (e .snd .inv .fst)
                    (λ x i → fst (e .snd .sec i) x)
                    (λ x i → fst (e .snd .ret i) x))
  snd (inv BoolRingIsoIsoCatIso e) = e .fst .snd
  -- roundtrips
  sec BoolRingIsoIsoCatIso x = CatIso≡ _ _ (CommRingHom≡ refl)
  ret BoolRingIsoIsoCatIso x =
    Σ≡Prop (λ x → isPropIsCommRingHom
                     (BooleanRingStr→CommRingStr (snd R))
                     (fst x)
                     (BooleanRingStr→CommRingStr (snd S)))
           (Σ≡Prop isPropIsEquiv (funExt (λ _ → refl)))

-- ═══════════════════════════════════════════════════════════════
-- Univalence
-- ═══════════════════════════════════════════════════════════════

-- Univalence at level zero (matching existing infrastructure)
private
  pathToIsoDecomp' : (R S : BooleanRing ℓ-zero) → (R ≡ S) ≃ (CatIso BooleanRingsCategory R S)
  pathToIsoDecomp' R S = compEquiv (invEquiv (BoolRingPath R S))
                                   (isoToEquiv BoolRingIsoIsoCatIso)

  pathToIsoDecompAtRefl' : (R : BooleanRing ℓ-zero) → fst (pathToIsoDecomp' R R) refl ≡ idCatIso
  pathToIsoDecompAtRefl' R = CatIso≡ _ _
    (CommRingHom≡ (BoolRingPathInvRefl≡Idfun R))

  pathToIsoDecompIsDecomp' : (R S : BooleanRing ℓ-zero)
    → pathToIso {x = R} {y = S} ≡ fst (pathToIsoDecomp' R S)
  pathToIsoDecompIsDecomp' R S = funExt $
    J (λ S' p → pathToIso {x = R} {y = S'} p ≡ fst (pathToIsoDecomp' R S') p)
      (pathToIso-refl ∙ sym (pathToIsoDecompAtRefl' R))

isUnivalentBooleanRingsCategory₀ : isUnivalent (BooleanRingsCategory {ℓ = ℓ-zero})
isUnivalentBooleanRingsCategory₀ .univ R S =
  subst isEquiv (sym (pathToIsoDecompIsDecomp' R S)) (snd (pathToIsoDecomp' R S))

-- ═══════════════════════════════════════════════════════════════
-- Terminal object
-- ═══════════════════════════════════════════════════════════════

TerminalBooleanRing : Terminal (BooleanRingsCategory {ℓ = ℓ-zero})
fst TerminalBooleanRing = UnitBR
fst (snd TerminalBooleanRing y) = mapToUnitCommRing (BooleanRing→CommRing y)
snd (snd TerminalBooleanRing y) f = isPropMapToUnitCommRing (BooleanRing→CommRing y) _ f

-- ═══════════════════════════════════════════════════════════════
-- Fibered product of Boolean rings
-- ═══════════════════════════════════════════════════════════════

module _ (A B C : BooleanRing ℓ) (α : BoolHom A C) (β : BoolHom B C) where

  private
    A' = BooleanRing→CommRing A
    B' = BooleanRing→CommRing B
    C' = BooleanRing→CommRing C

    -- The fibered product as a CommRing
    fbCR : CommRing ℓ
    fbCR = fiberedProduct A' B' C' α β

  -- The fibered product is a BooleanRing (idempotency holds componentwise)
  fiberedProductBR : BooleanRing ℓ
  fiberedProductBR = idemCommRing→BR fbCR idem
    where
    idem : isIdemRing fbCR
    idem ((a , b) , hab) = Σ≡Prop (λ _ → is-set (snd C) _ _)
      (λ i → ·Idem (snd A) a i , ·Idem (snd B) b i)

  fiberedProductBRPr₁ : BoolHom fiberedProductBR A
  fiberedProductBRPr₁ = fiberedProductPr₁ A' B' C' α β

  fiberedProductBRPr₂ : BoolHom fiberedProductBR B
  fiberedProductBRPr₂ = fiberedProductPr₂ A' B' C' α β

  fiberedProductBRPr₁₂Commutes :
    compCommRingHom fiberedProductBRPr₁ α ≡ compCommRingHom fiberedProductBRPr₂ β
  fiberedProductBRPr₁₂Commutes = fiberedProductPr₁₂Commutes A' B' C' α β

  fiberedProductBRUnivProp :
    (D : BooleanRing ℓ) (h : BoolHom D A) (k : BoolHom D B) →
    compCommRingHom h α ≡ compCommRingHom k β →
    ∃![ l ∈ BoolHom D fiberedProductBR ]
        (h ≡ compCommRingHom l fiberedProductBRPr₁)
      × (k ≡ compCommRingHom l fiberedProductBRPr₂)
  fiberedProductBRUnivProp D h k H =
    fiberedProductUnivProp A' B' C' α β (BooleanRing→CommRing D) h k H

-- ═══════════════════════════════════════════════════════════════
-- Pullbacks
-- ═══════════════════════════════════════════════════════════════

open Pullback

PullbackBooleanRingsCategory : Pullbacks {ℓ-suc ℓ} BooleanRingsCategory
pbOb (PullbackBooleanRingsCategory (cospan A C B α β))       =
  fiberedProductBR A B C α β
pbPr₁ (PullbackBooleanRingsCategory (cospan A C B α β))      =
  fiberedProductBRPr₁ A B C α β
pbPr₂ (PullbackBooleanRingsCategory (cospan A C B α β))      =
  fiberedProductBRPr₂ A B C α β
pbCommutes (PullbackBooleanRingsCategory (cospan A C B α β))  =
  fiberedProductBRPr₁₂Commutes A B C α β
univProp (PullbackBooleanRingsCategory (cospan A C B α β)) {d = D} =
  fiberedProductBRUnivProp A B C α β D

-- ═══════════════════════════════════════════════════════════════
-- General limits
-- ═══════════════════════════════════════════════════════════════

module _ {ℓJ ℓJ' : Level} where

  open LimCone
  open Cone

  private
    theℓ = ℓ-max ℓJ ℓJ'

  LimitsBooleanRingsCategory : Limits {ℓJ} {ℓJ'} (BooleanRingsCategory {ℓ = theℓ})
  LimitsBooleanRingsCategory J D = limBR
    where
    -- The diagram in CommRings via the forgetful functor
    D' = funcComp ForgetfulBooleanRing→CommRing D

    -- The CommRing limit
    limCR = LimitsCommRingsCategory J D'
    limCRObj = lim limCR

    -- The limit CommRing is idempotent, so it's a BooleanRing
    limBRObj : BooleanRing theℓ
    limBRObj = idemCommRing→BR limCRObj
      (λ x → cone≡ (λ v → funExt (λ _ → ·Idem (snd (F-ob D v)) _)))

    -- Convert a BooleanRing cone to a CommRing cone
    brCone→crCone : ∀ {c} → Cone D c → Cone D' (BooleanRing→CommRing c)
    coneOut (brCone→crCone cc) v = coneOut cc v
    coneOutCommutes (brCone→crCone cc) e = coneOutCommutes cc e

    limBR : LimCone D
    -- The limit object
    lim limBR = limBRObj
    -- The limit cone (same projections as the CommRing limit)
    coneOut (limCone limBR) v = coneOut (limCone limCR) v
    coneOutCommutes (limCone limBR) e = coneOutCommutes (limCone limCR) e
    -- Universal property (same as for the CommRing limit)
    univProp limBR c cc = univProp limCR (BooleanRing→CommRing c) (brCone→crCone cc)

-- ═══════════════════════════════════════════════════════════════
-- Countable presentation is closed under binary products
-- ═══════════════════════════════════════════════════════════════

-- Countability closure under ⊎
private
  has-CS-⊎ : {A B : Type} →
    has-Countability-structure A → has-Countability-structure B →
    has-Countability-structure (A ⊎ B)
  has-CS-⊎ (α , iA) (β , iB) =
    let open CountableSum α β
    in γ⊎ , compIso (⊎Iso iA iB) ΣℕSum

  has-CS-Unit : has-Countability-structure Unit
  has-CS-Unit = αU , theIso
    where
    αU : binarySequence
    αU zero = true
    αU (suc _) = false
    open Iso
    theIso : Iso Unit (Σℕ αU)
    fun theIso tt = zero , refl
    inv theIso _ = tt
    sec theIso (zero , p) = Σ≡Prop (λ _ → isSetBool _ _) refl
    sec theIso (suc n , p) = ⊥.rec (false≢true p)
    ret theIso tt = refl

-- ×BR preserves equivalences
×BR-resp-equiv : (A A' B B' : BooleanRing ℓ-zero) →
  BooleanRingEquiv A A' → BooleanRingEquiv B B' →
  BooleanRingEquiv (A ×BR B) (A' ×BR B')
fst (fst (×BR-resp-equiv A A' B B' eA eB)) (a , b) =
  fst (fst eA) a , fst (fst eB) b
snd (fst (×BR-resp-equiv A A' B B' eA eB)) =
  isoToIsEquiv theIso
  where
  theIso : Iso (⟨ A ⟩ × ⟨ B ⟩) (⟨ A' ⟩ × ⟨ B' ⟩)
  Iso.fun theIso (a , b) = fst (fst eA) a , fst (fst eB) b
  Iso.inv theIso (a' , b') = invEq (fst eA) a' , invEq (fst eB) b'
  Iso.sec theIso (a' , b') = ΣPathP (secEq (fst eA) a' , secEq (fst eB) b')
  Iso.ret theIso (a , b) = ΣPathP (retEq (fst eA) a , retEq (fst eB) b)
snd (×BR-resp-equiv A A' B B' eA eB) = makeIsCommRingHom
  (ΣPathP (pres1 (snd eA) , pres1 (snd eB)))
  (λ x y → ΣPathP (pres+ (snd eA) _ _ , pres+ (snd eB) _ _))
  (λ x y → ΣPathP (pres· (snd eA) _ _ , pres· (snd eB) _ _))

-- ─── The key algebraic construction ───
-- Given presentations B₁ = freeBA A₁ / Im f₁ and B₂ = freeBA A₂ / Im f₂,
-- we construct a presentation of B₁ ×BR B₂.
--
-- The idea: introduce an idempotent separator e.
-- Generators: A₁ ⊎ (A₂ ⊎ Unit), where the Unit element is e.
-- Relations:
--   (1) e · liftL(f₁ x)     for each x : X₁  (A₁-relations multiplied by e)
--   (2) (1+e) · liftR(f₂ x) for each x : X₂  (A₂-relations multiplied by 1+e)
--   (3) e · aₙ + aₙ         for each a : A₁  (e acts as identity on A₁-generators)
--   (4) e · bₙ              for each a : A₂  (e kills A₂-generators)
--
-- Then Q = freeBA G / Im rel  ≅  B₁ ×BR B₂
-- via φ(q) = (q₁(q), q₂(q)) and ψ(a,b) = α(a) + β(b)
-- where α(a) = e·a and β(b) = (1+e)·b in Q.

module ProductPresentation
  {A₁ A₂ : Type} {X₁ X₂ : Type}
  (f₁ : X₁ → ⟨ freeBA A₁ ⟩) (f₂ : X₂ → ⟨ freeBA A₂ ⟩) where

  G : Type
  G = A₁ ⊎ (A₂ ⊎ Unit)

  R : Type
  R = (X₁ ⊎ X₂) ⊎ (A₁ ⊎ A₂)

  private
    module FG = BooleanRingStr (snd (freeBA G))

    e-gen : ⟨ freeBA G ⟩
    e-gen = generator (inr (inr tt))

    left-gen : A₁ → ⟨ freeBA G ⟩
    left-gen a = generator (inl a)

    right-gen : A₂ → ⟨ freeBA G ⟩
    right-gen a = generator (inr (inl a))

    liftL : BoolHom (freeBA A₁) (freeBA G)
    liftL = inducedBAHom A₁ (freeBA G) left-gen

    liftR : BoolHom (freeBA A₂) (freeBA G)
    liftR = inducedBAHom A₂ (freeBA G) right-gen

  rel : R → ⟨ freeBA G ⟩
  rel (inl (inl x)) = e-gen FG.· fst liftL (f₁ x)
  rel (inl (inr x)) = (FG.𝟙 FG.+ e-gen) FG.· fst liftR (f₂ x)
  rel (inr (inl a)) = (e-gen FG.· left-gen a) FG.+ left-gen a
  rel (inr (inr a)) = e-gen FG.· right-gen a

  Q : BooleanRing ℓ-zero
  Q = freeBA G QB./Im rel

  -- The isomorphism Q ≅ B₁ ×BR B₂ (postulated; to be filled in)
  postulate
    product-equiv : BooleanRingEquiv Q ((freeBA A₁ QB./Im f₁) ×BR (freeBA A₂ QB./Im f₂))

-- ─── The main theorem ───

is-countably-presented-closed-×BR :
  (B C : BooleanRing ℓ-zero) →
  is-countably-presented B → is-countably-presented C →
  is-countably-presented (B ×BR C)
is-countably-presented-closed-×BR B C =
  rec2 isPropPropTrunc go
  where
  open ProductPresentation

  go : has-countable-presentation B → has-countable-presentation C →
       is-countably-presented (B ×BR C)
  go (A₁ , cA₁ , X₁ , cX₁ , f₁ , eB) (A₂ , cA₂ , X₂ , cX₂ , f₂ , eC) =
    ∣ G f₁ f₂
    , has-CS-⊎ cA₁ (has-CS-⊎ cA₂ has-CS-Unit)
    , R f₁ f₂
    , has-CS-⊎ (has-CS-⊎ cX₁ cX₂) (has-CS-⊎ cA₁ cA₂)
    , rel f₁ f₂
    , compCommRingEquiv
        (×BR-resp-equiv _ _ _ _ eB eC)
        (invCommRingEquiv _ _ (product-equiv f₁ f₂))
    ∣₁
