{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module LLPOAttemptLLMAided where
-- An LLM-aided rework of OmnisciencePrinciples.LLPO.
--
-- The original phrased the missing infrastructure as parameters of nested
-- modules (universal properties, product universal properties, an abstract
-- `prodIso`, ...).  Here we instead spell the *whole* argument out as a flat
-- sequence of definitions and leave the still-missing mathematical inputs as
-- ordinary holes `{! !}`.  The point that *is* now infrastructure — the Stone
-- duality axioms — is used concretely:
--
--   * `fs` (formal surjections are surjections) turns the injectivity of the
--     inducing map `f : B∞ → B∞ ×BR B∞` into a surjection on spectra.
--   * That surjection is transported across the two Stone isos
--     (Sp B∞ ≅ ℕ∞ and Sp (B∞ ×BR B∞) ≅ ℕ∞ ⊎ ℕ∞) to the concrete map `e`.
--
-- The remaining holes are exactly the facts that still need a proof:
--   - the spectrum iso `Sp B∞ ≅ ℕ∞` (`B∞` itself is now the NFinCofin
--     presentation, and its countable presentation `presented` is filled);
--   - that overtly discrete spaces are closed under products
--     (`odiscClosedUnderProducts`): via "countably presented ⟺ overtly
--     discrete", this is the substantive half of closing countably presented
--     Boolean algebras under products.  Its companion half — Boolean algebras
--     are closed under products (`baClosedUnderProducts`, the carrier of
--     `A ×BR B` is `⟨A⟩ × ⟨B⟩`) — is filled by `refl`.  Together they give
--     `prodPresented : is-countably-presented-alt (B∞ ×BR B∞)`;
--   - that Stone duality sends a product of Boolean algebras to a sum of Stone
--     spaces (`SpProd≅SpSum`, i.e. `Sp (A ×BR B) ≅ Sp A ⊎ Sp B`); composing it
--     with two copies of `Sp B∞ ≅ ℕ∞` fills `Sp (B∞ ×BR B∞) ≅ ℕ∞ ⊎ ℕ∞`;
--   - the inducing map `f`, its injectivity, and the naturality equation
--     saying its spectrum action *is* `e`.

open import CountablyPresentedBooleanRings.Examples.NFinCofin
open import BooleanRing.SubBooleanRing
open import Parity
open import CategoryTheory.StuffFromStoneAboutBAs
open import Cubical.Categories.Functor
open import Cubical.Data.Bool renaming (_≟_ to _=B_) hiding (_≤_ ; _≥_)
open import Cubical.Algebra.BooleanRing.Instances.Bool

open import QuickFixes

open import BooleanRing.BooleanRingMaps
open import BooleanRing.FreeBooleanRing.FreeBool
import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.BooleanRingQuotients.UniversalProperty
open import BooleanRing.BoolAlgMorphism

open import BasicDefinitions

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Functions.Surjection
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Isomorphism

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring.Properties using (module RingHomTheory)
open import Cubical.Tactics.CommRingSolver

open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sum as ⊎
open import Cubical.Data.Nat renaming (_·_ to _·ℕ_ ; _+_ to _+ℕ_)
open import Cubical.Data.Nat.IsEven
open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Relation.Nullary hiding (¬_)
open import Cubical.Data.Nat.Order renaming (_≟_ to _=ℕ_)
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
open import Cubical.Data.List
open import Cubical.HITs.PropositionalTruncation using (∣_∣₁)
open import CountablyPresentedBooleanRings.Definitions
open import BooleanRing.ProductBA
open import Axioms.SurjectionsAreFormalSurjections
open import Axioms.StoneDuality
open import StoneSpaces.Spectrum
-- ℕ∞ and friends come from the library example; `neededIso` (the Stone iso
-- Sp B∞ ≅ ℕ∞) is supplied by the local NinftyExtras, which re-exports Ninfty.
-- This keeps the FormalizationSSD library untouched (see LIBRARY_CHANGES.md).
open import NinftyExtras
  using (ℕ∞ ; hits1NotTwice ; atMostOnce→NotTwice ; notTwice→AtMostOnce ; neededIso)
-- Sp (A ×BR B) ≅ Sp A ⊎ Sp B, supplied by the local StoneSums (intended upstream
-- as AntiEquivalence.StoneSums); see LIBRARY_CHANGES.md.
import StoneSums
-- Algebraic closure of countably presented Boolean algebras under binary
-- products, ported portably from CountablyPresentedBooleanRings.ProductClosure.
import ProductClosureLocal
open import BooleanRing.BoolRingUnivalence
-- The model map `splitFC : ℕfinCofinBA → ℕfinCofinBA × ℕfinCofinBA`, its trivial
-- kernel, the naturality of its spectrum action (the evens/odds split), and the
-- Stone iso σ : Sp(ℕfinCofinBA) ≅ ℕ∞.  These conclude LLPO directly.
open import EvenOddSplit using (splitFC ; splitFC-kernel)
open import SplitNaturality using (evenNaturality ; oddNaturality)
open import SpℕfcIso using (σ)

module LLPOProof (sd : StoneDualityAxiom) (fs : formalSurjectionsAreSurjectionsAxiom) where

  ----------------------------------------------------------------------------
  -- The statement of LLPO over ℕ∞.  We reuse the ℕ∞ from
  -- StoneSpaces.Examples.Ninfty (sequences hitting 1 at most once), so that the
  -- Stone iso `ℕ∞=SpB∞` below is exactly the `neededIso` of that example.
  ----------------------------------------------------------------------------

  LLPOExplicitAt : ℕ∞ → Type
  LLPOExplicitAt (α , _) =
    (∀ (n : ℕ) → α (double n) ≡ false) ⊎ (∀ (n : ℕ) → α (suc $ double n) ≡ false)

  LLPO : Type
  LLPO = (x : ℕ∞) → ∥ LLPOExplicitAt x ∥₁

  ----------------------------------------------------------------------------
  -- The concrete map e : ℕ∞ ⊎ ℕ∞ → ℕ∞ and the reduction of LLPO to its
  -- surjectivity.  Copied unchanged from OmnisciencePrinciples.LLPO.
  ----------------------------------------------------------------------------

  module HowWeDoIt where
    splitIntoEvens : binarySequence → binarySequence
    splitIntoEvens α = evenOddElim (λ n ((k , n=2k)) → α k) (λ n oddn → false)

    splitIntoEvensℕ∞ : ℕ∞ → ℕ∞
    splitIntoEvensℕ∞ (α , α1) .fst = splitIntoEvens α
    splitIntoEvensℕ∞ (α , α1) .snd =
      notTwice→AtMostOnce (splitIntoEvens α) goal
      where
        α2 : hits1NotTwice α
        α2 = atMostOnce→NotTwice α α1
        goal : (n m : ℕ) → (m ≡ n → ⊥) → splitIntoEvens α m and splitIntoEvens α n ≡ false
        goal n m m≠n with (even-or-odd m) | (even-or-odd n)
        ... | inl (k , m=2k) | inl (l , n=2l) = α2 l k λ k=l → m≠n $
          m ≡⟨ m=2k ⟩ double k ≡⟨ cong double k=l ⟩ double l ≡⟨ sym n=2l ⟩ n ∎
        ... | inl (k , _) | inr _ = and-zeroʳ (α k)
        ... | inr modd  | _ = refl

    splitIntoOdds : binarySequence → binarySequence
    splitIntoOdds α = evenOddElim (λ n evenn → false) (λ n ((k , n=2k+1)) → α k)

    splitIntoOddsℕ∞ : ℕ∞ → ℕ∞
    splitIntoOddsℕ∞ (α , α1) .fst = splitIntoOdds α
    splitIntoOddsℕ∞ (α , α1) .snd =
      notTwice→AtMostOnce (splitIntoOdds α) goal
      where
        α2 : hits1NotTwice α
        α2 = atMostOnce→NotTwice α α1
        goal : (n m : ℕ) → (m ≡ n → ⊥) → splitIntoOdds α m and splitIntoOdds α n ≡ false
        goal n m m≠n with (even-or-odd m) | (even-or-odd n)
        ... | inr (k , m=2k+1) | inr (l , n=2l+1) = α2 l k λ k=l → m≠n $
          m              ≡⟨ m=2k+1 ⟩
          suc (double k) ≡⟨ cong (suc ∘ double) k=l ⟩
          suc (double l) ≡⟨ sym n=2l+1 ⟩
          n              ∎
        ... | inr (k , _) | inl _ = and-zeroʳ (α k)
        ... | inl modd  | _ = refl

    e : ℕ∞ ⊎ ℕ∞ → ℕ∞
    e = ⊎.rec splitIntoEvensℕ∞ splitIntoOddsℕ∞

    e-fibers→LLPO-explicit : ∀ (x : ℕ∞) → fiber e x → LLPOExplicitAt x
    e-fibers→LLPO-explicit x (inl β , eβ=α) = inr λ k →
     (sym $ cong (λ x' → fst x' (suc (double k))) eβ=α) ∙ evenOddElim-odd k
    e-fibers→LLPO-explicit x (inr β , eβ=α) = inl λ k →
     (sym $ cong (λ x' → fst x' (double k)) eβ=α) ∙ evenOddElim-even k

    e-surj→LLPO : isSurjection e → LLPO
    e-surj→LLPO esurj x = PT.map (e-fibers→LLPO-explicit x) (esurj x)

  open HowWeDoIt

  ----------------------------------------------------------------------------
  -- The still-missing inputs, as holes.
  ----------------------------------------------------------------------------

  -- The Boolean algebra whose spectrum is ℕ∞: the NFinCofin presentation
  -- (freeBA ℕ /Im relationsℕ), exactly the `presentation` used by
  -- StoneSpaces.Examples.Ninfty (where SpB∞ = SpGeneralBooleanRing presentation).
  B∞ : BooleanRing ℓ-zero
  B∞ = presentation

  -- presentation is countably presented: it is equivalent to ℕfinCofinBA, which
  -- is, so transport the witness across that equivalence.
  presented : is-countably-presented-alt B∞
  presented = subst is-countably-presented-alt
    (sym (uaBoolRing {A = presentation} {B = ℕfinCofinBA} ℕFinCof=Presentation))
    ℕfinCofinIsCountablyPresented

  -- The Stone iso Sp B∞ ≅ ℕ∞.  This is the `neededIso` of
  -- StoneSpaces.Examples.Ninfty (now completed there): its `fun` reads a point
  -- of Sp B∞ off as the binary sequence n ↦ (γ ∘ quotientImageHom)(gₙ), and its
  -- `inv` is the universal-property hom induced by such a sequence.
  ℕ∞=SpB∞ : Iso (SpGeneralBooleanRing B∞) ℕ∞
  ℕ∞=SpB∞ = neededIso

  ----------------------------------------------------------------------------
  -- Closure of countably presented Boolean algebras under (binary) products.
  --
  -- The reason B∞ ×BR B∞ is again countably presented splits into the two
  -- facts the argument really rests on:
  --
  --   (1) Boolean algebras are closed under products — concretely, the carrier
  --       of the product Boolean algebra is the product of the carriers.  This
  --       is the algebraic half, and `_×BR_` makes it hold definitionally.
  --
  --   (2) Overtly discrete spaces are closed under products.  Via the
  --       correspondence "a Boolean algebra is countably presented iff it is
  --       overtly discrete" (the corollary ODiscBAareBoole / BooleIsODisc),
  --       (1) and (2) together upgrade a product of countably presented
  --       Boolean algebras to a countably presented one.  Pinned for now.
  ----------------------------------------------------------------------------

  -- (1) Boolean algebras are closed under products: the carrier of A ×BR B is
  -- the product of the carriers.  (Holds definitionally for `_×BR_`.)
  baClosedUnderProducts : (A B : BooleanRing ℓ-zero) → ⟨ A ×BR B ⟩ ≡ (⟨ A ⟩ × ⟨ B ⟩)
  baClosedUnderProducts A B = refl

  -- (2) Overtly discrete spaces are closed under products; via CP ⟺ ODisc this
  -- is closure of countably presented Boolean algebras under products. [PIN]
  --
  -- SUPERSEDED (for now): this ODisc-spaces route is replaced by the direct
  -- algebraic closure proof `ProductClosureLocal.Booleω-closed-×BR` (the
  -- orthogonal-idempotent decomposition), which proves the same statement
  -- `is-countably-presented-alt (A ×BR B)` purely algebraically.  Kept here,
  -- commented out, as documentation of the intended ODisc/overtly-discrete view.
  --
  -- odiscClosedUnderProducts : (A B : BooleanRing ℓ-zero)
  --   → is-countably-presented-alt A → is-countably-presented-alt B
  --   → is-countably-presented-alt (A ×BR B)
  -- odiscClosedUnderProducts A B cpA cpB = {! !}

  -- So B∞ ×BR B∞ is again countably presented.  `fst (B∞ , presented) ×BR
  -- fst (B∞ , presented)` is definitionally `B∞ ×BR B∞` (same ProductBA `_×BR_`).
  prodPresented : is-countably-presented-alt (B∞ ×BR B∞)
  prodPresented = ProductClosureLocal.Booleω-closed-×BR (B∞ , presented) (B∞ , presented)

  -- Stone duality sends a product of Boolean algebras to a sum (coproduct) of
  -- Stone spaces: Sp (A ×BR B) ≅ Sp A ⊎ Sp B.  The spectrum is contravariant, so
  -- the product becomes a coproduct; concretely a map A ×BR B → 2 factors through
  -- exactly one projection (2 is connected).
  --
  -- TEMPORARY HOTFIX: this uses the local `StoneSums`, which proves the iso
  -- directly via idempotents in 2.  It is not the nicest solution — the proper
  -- statement is categorical (Sp is an anti-equivalence Booleω ≃ Stone^op, so
  -- products in Booleω are coproducts/sums in Stone "an sich").  That cleaner
  -- version is being developed separately (see CategoricalSumsProducts); swap
  -- this over once it lands.
  SpProd≅SpSum : (A B : BooleanRing ℓ-zero)
    → Iso (SpGeneralBooleanRing (A ×BR B))
          (SpGeneralBooleanRing A ⊎ SpGeneralBooleanRing B)
  SpProd≅SpSum = StoneSums.SpProd≅SpSum

  -- ...so the spectrum of B∞ ×BR B∞ is ℕ∞ ⊎ ℕ∞, transporting the two copies of
  -- the Stone iso Sp B∞ ≅ ℕ∞ across the product-to-sum equivalence.
  ℕ∞+ℕ∞=SpProd : Iso (SpGeneralBooleanRing (B∞ ×BR B∞)) (ℕ∞ ⊎ ℕ∞)
  ℕ∞+ℕ∞=SpProd = compIso (SpProd≅SpSum B∞ B∞) (⊎Iso ℕ∞=SpB∞ ℕ∞=SpB∞)

  -- Infrastructure for the inducing map f, lifted to module level so that its
  -- action on generators (`fOnGenerators`) can be reused (e.g. by `fInj`).
  private
    𝟘∞ : ⟨ B∞ ⟩
    𝟘∞ = BooleanRingStr.𝟘 (snd B∞)
    _·∞_ : ⟨ B∞ ⟩ → ⟨ B∞ ⟩ → ⟨ B∞ ⟩
    _·∞_ = BooleanRingStr._·_ (snd B∞)
    𝟘prod : ⟨ B∞ ×BR B∞ ⟩
    𝟘prod = BooleanRingStr.𝟘 (snd (B∞ ×BR B∞))
    _·prod_ : ⟨ B∞ ×BR B∞ ⟩ → ⟨ B∞ ×BR B∞ ⟩ → ⟨ B∞ ×BR B∞ ⟩
    _·prod_ = BooleanRingStr._·_ (snd (B∞ ×BR B∞))

    -- the generators of B∞ = images of the free generators
    γ : ℕ → ⟨ B∞ ⟩
    γ k = fst NFinCofinPresentation.π (generator k)

    -- the per-generator values of f, by parity
    fgen : ℕ → ⟨ B∞ ×BR B∞ ⟩
    fgen = evenOddElim (λ _ p → (γ (fst p) , 𝟘∞)) (λ _ p → (𝟘∞ , γ (fst p)))

    ffree : BoolHom (freeBA ℕ) (B∞ ×BR B∞)
    ffree = inducedBAHom ℕ (B∞ ×BR B∞) fgen
    module FF = IsCommRingHom (snd ffree)

    ffree-gen : (n : ℕ) → fst ffree (generator n) ≡ fgen n
    ffree-gen n = funExt⁻ (evalBAInduce ℕ (B∞ ×BR B∞) fgen) n

    -- orthogonality of the generators of B∞ (from gen-orth, via π a hom)
    γ-orth : (k l : ℕ) → (k ≡ l → ⊥) → γ k ·∞ γ l ≡ 𝟘∞
    γ-orth k l k≠l =
      sym (NFinCofinPresentation.ΠH.pres· (generator k) (generator l))
      ∙ NFinCofinPresentation.gen-orth k l k≠l

    -- annihilation of 0, from the Boolean-algebra structure (∧ = ·)
    module AB∞ = BooleanAlgebraStr (snd B∞)
    annR : (a : ⟨ B∞ ⟩) → a ·∞ 𝟘∞ ≡ 𝟘∞
    annR a = AB∞.∧AnnihilR
    annL : (a : ⟨ B∞ ⟩) → 𝟘∞ ·∞ a ≡ 𝟘∞
    annL a = AB∞.∧AnnihilL

    -- f(gₙ) · f(gₘ) = (0,0) for n ≠ m.  Splitting on the parity of n and m,
    -- the with-abstraction reduces `fgen n`, `fgen m` to their concrete pair
    -- values, leaving a componentwise goal closed by orthogonality of the
    -- generators (γ-orth) in the matching-parity slot and annihilation of 0
    -- elsewhere.
    orthog : (n m : ℕ) → (n ≡ m → ⊥) → fgen n ·prod fgen m ≡ 𝟘prod
    orthog n m n≠m with even-or-odd n | even-or-odd m
    ... | inl (k , n2k) | inl (l , m2l)  =
          cong₂ _,_ (γ-orth k l (λ k=l → n≠m (n2k ∙ cong double k=l ∙ sym m2l))) (annR 𝟘∞)
    ... | inl (k , n2k) | inr (l , m2l1) =
          cong₂ _,_ (annR (γ k)) (annL (γ l))
    ... | inr (k , n2k1) | inl (l , m2l) =
          cong₂ _,_ (annL (γ l)) (annR (γ k))
    ... | inr (k , n2k1) | inr (l , m2l1) =
          cong₂ _,_ (annR 𝟘∞) (γ-orth k l (λ k=l → n≠m (n2k1 ∙ cong (suc ∘ double) k=l ∙ sym m2l1)))

    fRespects : (n : ℕ) → ffree $cr relationsℕ n ≡ 𝟘prod
    fRespects n = goal (Iso.inv ℕ×ℕ≅ℕ n)
      where
        goal : (p : ℕ × ℕ) → ffree $cr relations p ≡ 𝟘prod
        goal (a , b) with discreteℕ a b
        ... | yes _  = FF.pres0
        ... | no a≠b = FF.pres· (generator a) (generator b)
                       ∙ cong₂ _·prod_ (ffree-gen a) (ffree-gen b)
                       ∙ orthog a b a≠b

  -- The Boolean-algebra map inducing e.  Following the paper, f is induced on
  -- the generators gₙ of B∞ = freeBA ℕ /Im relationsℕ by
  --     f(g_{2k})   = (gₖ , 0)        f(g_{2k+1}) = (0 , gₖ),
  -- and is a well-defined morphism because the images are pairwise orthogonal:
  -- f(gₙ) · f(gₘ) = (0,0) for n ≠ m, so f sends each relation gₙ · gₘ (n ≠ m) to 0.
  f : BoolHom B∞ (B∞ ×BR B∞)
  f = QB.inducedHom (B∞ ×BR B∞) ffree fRespects

  -- f's action on the generators γ m = π(generator m) of B∞.  By the quotient
  -- universal property f ∘cr π ≡ ffree, so f(γ m) = ffree(generator m) = fgen m.
  fOnGenerators : (m : ℕ) → fst f (γ m) ≡ fgen m
  fOnGenerators m =
    cong (λ h → fst h (generator m))
         (QB.evalInduce (B∞ ×BR B∞) {g = ffree} {gfx=0 = fRespects})
    ∙ ffree-gen m

  ----------------------------------------------------------------------------
  -- Concluding LLPO directly from the model map `splitFC` (EvenOddSplit) and
  -- the naturality of its spectrum action (SplitNaturality) — NOT via the
  -- abstract f-route above (`f`/`Spf`/`eFromSp`, which are no longer used).
  --
  -- `splitFC : ℕfc → ℕfc × ℕfc` (ℕfc = ℕfinCofinBA, the finite/cofinite model)
  -- has a trivial kernel (`splitFC-kernel`), hence is injective; by `fs` its
  -- spectrum action is a surjection; transported across the Stone isos σ and σ⊎
  -- it is a map e' : ℕ∞ ⊎ ℕ∞ → ℕ∞.  We do NOT prove e' ≡ e — instead a fibre of
  -- e' over x directly yields the LLPO disjunct for x (its image is 0 on all
  -- odds, resp. all evens), exactly the reasoning of `HowWeDoIt`.
  ----------------------------------------------------------------------------

  private ℕfc = ℕfinCofinBA

  ℕfcω : Booleω
  ℕfcω = ℕfc , ℕfinCofinIsCountablyPresented
  ℕfcProdω : Booleω
  ℕfcProdω = (ℕfc ×BR ℕfc) , ProductClosureLocal.Booleω-closed-×BR ℕfcω ℕfcω

  -- splitFC has trivial kernel (EvenOddSplit.splitFC-kernel) ⇒ injective.
  splitInj : isInjectiveBoolHom ℕfcω ℕfcProdω splitFC
  splitInj x y = RingHomTheory.ker≡0→inj (CommRingHom→RingHom splitFC)
                   (λ {z} → splitFC-kernel z) {x} {y}

  -- ⇒ its spectrum action γ ↦ γ ∘cr splitFC is surjective (this is `fs`).
  SpSplit : SpGeneralBooleanRing (ℕfc ×BR ℕfc) → SpGeneralBooleanRing ℕfc
  SpSplit γ = γ ∘cr splitFC
  SpSplitSurj : isSurjection SpSplit
  SpSplitSurj = fs ℕfcω ℕfcProdω splitFC splitInj

  -- the Stone iso for the product: Sp(ℕfc × ℕfc) ≅ ℕ∞ ⊎ ℕ∞.
  σ⊎ : Iso (SpGeneralBooleanRing (ℕfc ×BR ℕfc)) (ℕ∞ ⊎ ℕ∞)
  σ⊎ = compIso (StoneSums.SpProd≅SpSum ℕfc ℕfc) (⊎Iso σ σ)

  -- the transported surjection e' : ℕ∞ ⊎ ℕ∞ → ℕ∞.
  e' : ℕ∞ ⊎ ℕ∞ → ℕ∞
  e' = Iso.fun σ ∘ SpSplit ∘ Iso.inv σ⊎

  e'Surj : isSurjection e'
  e'Surj = snd
    (compSurjection
      (Iso.inv σ⊎ , isEquiv→isSurjection (snd (isoToEquiv (invIso σ⊎))))
      (compSurjection
        (SpSplit , SpSplitSurj)
        (Iso.fun σ , isEquiv→isSurjection (snd (isoToEquiv σ)))))

  -- A fibre of e' over x gives the LLPO disjunct for x.  By the naturality of
  -- SplitNaturality, e'(inl β) is the even split (0 on every odd index) and
  -- e'(inr β) the odd split (0 on every even index).  Only ONE coordinate of the
  -- fibre is inspected, so this stays light (no e' ≡ e, no funExt over ℕ∞).
  e'-fibre→LLPO : (x : ℕ∞) → fiber e' x → LLPOExplicitAt x
  e'-fibre→LLPO x (inl β , p) = inr λ k →
    sym (cong (λ y → fst y (suc (double k))) p)
    ∙ funExt⁻ (evenNaturality (Iso.inv σ β)) (suc (double k))
    ∙ evenOddElim-odd k
  e'-fibre→LLPO x (inr β , p) = inl λ k →
    sym (cong (λ y → fst y (double k)) p)
    ∙ funExt⁻ (oddNaturality (Iso.inv σ β)) (double k)
    ∙ evenOddElim-even k

  llpo : LLPO
  llpo x = PT.map (e'-fibre→LLPO x) (e'Surj x)
