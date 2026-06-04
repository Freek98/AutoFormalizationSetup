{-# OPTIONS --cubical --guardedness --lossy-unification #-}
-- The spectrum sends binary products of Boolean rings to binary sums of
-- spectra.  Writing the spectrum as  SpGeneralBooleanRing C = BoolHom C 2
-- (maps into the dualising object 2 = BoolBR), this is
--
--     SpGeneralBooleanRing (A ×BR B)  ≅  SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
--
-- read off the universal property of the product A ×BR B (from
-- `BooleanRing.ProductBA`): the two coproduct injections are precomposition
-- with the two projections `fstBA`, `sndBA` — i.e. the images of the
-- universal-property data under the contravariant spectrum, so `bwd` is the
-- copairing of `Sp fstBA` and `Sp sndBA`.  Conversely a map φ : A ×BR B → 2
-- factors through exactly one projection because 2 is indecomposable: the
-- complementary idempotents e = (𝟙,𝟘), e' = (𝟘,𝟙) (with e·e' = 𝟘, e+e' = 𝟙)
-- are sent to complementary booleans, so exactly one of φ e, φ e' is `true`,
-- and that selects the factor.  No Stone-duality axiom is used — only that 2
-- is connected.
module StoneSums where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism

open import Cubical.Data.Sigma
open import Cubical.Data.Sum as ⊎ using (_⊎_ ; inl ; inr)
open import Cubical.Data.Bool hiding (_≤_ ; _≥_)

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingTheory)
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import BooleanRing.BooleanRingMaps
open import BooleanRing.ProductBA
open import StoneSpaces.Spectrum

private
  variable
    ℓ ℓ' : Level

  -- 2 is indecomposable, in the two forms we use it.
  killʳ : (x y : Bool) → x ≡ true → x and y ≡ false → y ≡ false
  killʳ x y xp p = sym (cong (_and y) xp) ∙ p

  recoverʳ : (x y : Bool) → x ≡ false → x ⊕ y ≡ true → y ≡ true
  recoverʳ x y xp p = sym (cong (_⊕ y) xp) ∙ p

module _ (A : BooleanRing ℓ) (B : BooleanRing ℓ') where
  -- The product, its projections and universal property, from ProductBA.
  open BRProduct A B using (product ; fstBA ; sndBA)
  private
    module A = BooleanRingStr (snd A)
    module B = BooleanRingStr (snd B)
    module P = BooleanRingStr (snd product)
    open IsCommRingHom

    -- Annihilator laws in each factor (the only non-definitional facts about 𝟘).
    0RA : (x : ⟨ A ⟩) → x A.· A.𝟘 ≡ A.𝟘
    0RA = RingTheory.0RightAnnihilates (CommRing→Ring (BooleanRing→CommRing A))
    0LA : (x : ⟨ A ⟩) → A.𝟘 A.· x ≡ A.𝟘
    0LA = RingTheory.0LeftAnnihilates (CommRing→Ring (BooleanRing→CommRing A))
    0RB : (x : ⟨ B ⟩) → x B.· B.𝟘 ≡ B.𝟘
    0RB = RingTheory.0RightAnnihilates (CommRing→Ring (BooleanRing→CommRing B))
    0LB : (x : ⟨ B ⟩) → B.𝟘 B.· x ≡ B.𝟘
    0LB = RingTheory.0LeftAnnihilates (CommRing→Ring (BooleanRing→CommRing B))

    -- The complementary idempotents in the product.
    e  : ⟨ product ⟩
    e  = A.𝟙 , B.𝟘
    e' : ⟨ product ⟩
    e' = A.𝟘 , B.𝟙

    -- ── bwd: the copairing of the two projections ─────────────────────────────
    -- bwd = [ _∘ fstBA , _∘ sndBA ] = [ Sp fstBA , Sp sndBA ], the map out of the
    -- sum induced by the universal property of the product A ×BR B.
    bwd : SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B → SpGeneralBooleanRing product
    bwd = ⊎.rec (_∘cr fstBA) (_∘cr sndBA)

    -- ── Restriction of φ to a factor, when φ picks out that factor ─────────────
    -- φ e ≡ true  ⇒  a ↦ φ (a , 𝟘)  is a hom A → 2 (it is φ ∘ fstBA on the nose).
    restrA : (φ : SpGeneralBooleanRing product) → φ $cr e ≡ true → SpGeneralBooleanRing A
    restrA φ etrue .fst a = φ $cr (a , B.𝟘)
    restrA φ etrue .snd = makeIsCommRingHom
      etrue
      (λ a a' → cong (φ .fst) (ΣPathP (refl , sym (B.+IdR B.𝟘)))
              ∙ φ .snd .pres+ (a , B.𝟘) (a' , B.𝟘))
      (λ a a' → cong (φ .fst) (ΣPathP (refl , sym (0LB B.𝟘)))
              ∙ φ .snd .pres· (a , B.𝟘) (a' , B.𝟘))

    -- φ e' ≡ true  ⇒  b ↦ φ (𝟘 , b)  is a hom B → 2.
    restrB : (φ : SpGeneralBooleanRing product) → φ $cr e' ≡ true → SpGeneralBooleanRing B
    restrB φ e'true .fst b = φ $cr (A.𝟘 , b)
    restrB φ e'true .snd = makeIsCommRingHom
      e'true
      (λ b b' → cong (φ .fst) (ΣPathP (sym (A.+IdR A.𝟘) , refl))
              ∙ φ .snd .pres+ (A.𝟘 , b) (A.𝟘 , b'))
      (λ b b' → cong (φ .fst) (ΣPathP (sym (0LA A.𝟘) , refl))
              ∙ φ .snd .pres· (A.𝟘 , b) (A.𝟘 , b'))

    -- e , e' are complementary, hence so are φ e , φ e' in 2.
    e+e'≡1 : e P.+ e' ≡ P.𝟙
    e+e'≡1 = ΣPathP (A.+IdR A.𝟙 , B.+IdL B.𝟙)

    φe⊕φe' : (φ : SpGeneralBooleanRing product) → (φ $cr e) ⊕ (φ $cr e') ≡ true
    φe⊕φe' φ = sym (φ .snd .pres+ e e') ∙ cong (φ .fst) e+e'≡1 ∙ φ .snd .pres1

    -- ── fwd: branch on φ e (2 is indecomposable) ──────────────────────────────
    fwdAux : (φ : SpGeneralBooleanRing product) → Σ[ b ∈ Bool ] (φ $cr e ≡ b)
      → SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
    fwdAux φ (true  , etrue)  = inl (restrA φ etrue)
    fwdAux φ (false , efalse) =
      inr (restrB φ (recoverʳ (φ $cr e) (φ $cr e') efalse (φe⊕φe' φ)))

    fwd : SpGeneralBooleanRing product → SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B
    fwd φ = fwdAux φ (φ $cr e , refl)

    -- ── retraction  bwd ∘ fwd ≡ id ────────────────────────────────────────────
    -- φ (a , b) = φ (a , 𝟘) ⊕ φ (𝟘 , b), and the off-factor summand vanishes.
    φ-split : (φ : SpGeneralBooleanRing product) (a : ⟨ A ⟩) (b : ⟨ B ⟩)
      → φ $cr (a , b) ≡ (φ $cr (a , B.𝟘)) ⊕ (φ $cr (A.𝟘 , b))
    φ-split φ a b = cong (φ .fst) (ΣPathP (sym (A.+IdR a) , sym (B.+IdL b)))
      ∙ φ .snd .pres+ (a , B.𝟘) (A.𝟘 , b)

    rB≡false : (φ : SpGeneralBooleanRing product) → φ $cr e ≡ true → (b : ⟨ B ⟩)
      → φ $cr (A.𝟘 , b) ≡ false
    rB≡false φ etrue b = killʳ (φ $cr e) (φ $cr (A.𝟘 , b)) etrue
      (sym (φ .snd .pres· e (A.𝟘 , b)) ∙ cong (φ .fst) (ΣPathP (0RA A.𝟙 , 0LB b)) ∙ φ .snd .pres0)

    rA≡false : (φ : SpGeneralBooleanRing product) → φ $cr e' ≡ true → (a : ⟨ A ⟩)
      → φ $cr (a , B.𝟘) ≡ false
    rA≡false φ e'true a = killʳ (φ $cr e') (φ $cr (a , B.𝟘)) e'true
      (sym (φ .snd .pres· e' (a , B.𝟘)) ∙ cong (φ .fst) (ΣPathP (0LA a , 0RB B.𝟙)) ∙ φ .snd .pres0)

    retAux : (φ : SpGeneralBooleanRing product) (s : Σ[ b ∈ Bool ] (φ $cr e ≡ b))
      → bwd (fwdAux φ s) ≡ φ
    retAux φ (true , etrue) = CommRingHom≡ (funExt λ (a , b) →
      sym (φ-split φ a b
        ∙ cong ((φ $cr (a , B.𝟘)) ⊕_) (rB≡false φ etrue b)
        ∙ ⊕-identityʳ (φ $cr (a , B.𝟘))))
    retAux φ (false , efalse) = CommRingHom≡ (funExt λ (a , b) →
      sym (φ-split φ a b
        ∙ cong (_⊕ (φ $cr (A.𝟘 , b))) (rA≡false φ e'true a)))
      where
        e'true : φ $cr e' ≡ true
        e'true = recoverʳ (φ $cr e) (φ $cr e') efalse (φe⊕φe' φ)

    ret : (φ : SpGeneralBooleanRing product) → bwd (fwd φ) ≡ φ
    ret φ = retAux φ (φ $cr e , refl)

    -- ── section  fwd ∘ bwd ≡ id ───────────────────────────────────────────────
    -- bwd (inl ψ) sends e ↦ ψ 𝟙 = true, so fwd takes the `inl` branch; the
    -- recovered restriction is ψ on the nose.  Dually for inr.
    sec : (s : SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B) → fwd (bwd s) ≡ s
    sec (inl ψ) =
      cong (fwdAux (bwd (inl ψ)))
        (isContr→isProp (isContrSingl (bwd (inl ψ) $cr e))
          (bwd (inl ψ) $cr e , refl) (true , ψ .snd .pres1))
      ∙ cong inl (CommRingHom≡ refl)
    sec (inr χ) =
      cong (fwdAux (bwd (inr χ)))
        (isContr→isProp (isContrSingl (bwd (inr χ) $cr e))
          (bwd (inr χ) $cr e , refl) (false , χ .snd .pres0))
      ∙ cong inr (CommRingHom≡ refl)

  -- ── The product-to-sum iso on spectra ───────────────────────────────────────
  SpProd≅SpSum : Iso (SpGeneralBooleanRing (A ×BR B))
                     (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
  SpProd≅SpSum .Iso.fun = fwd
  SpProd≅SpSum .Iso.inv = bwd
  SpProd≅SpSum .Iso.sec = sec
  SpProd≅SpSum .Iso.ret = ret
