{-# OPTIONS --cubical --guardedness --lossy-unification #-}
module ProductClosure where

-- Countably presented Boolean rings are closed under binary products.
-- The proof uses the orthogonal idempotent decomposition: given presentations
-- A ≅ freeBA(GA)/fA and B ≅ freeBA(GB)/fB, the product A ×BR B is presented
-- by generators GA ⊎ (GB ⊎ Unit) (with the extra generator e as separator)
-- and relations (RA ⊎ RB) ⊎ (GA ⊎ GB).
-- Countability of the generator and relation types follows from closure of
-- countable types under disjoint union (has-Countability-structure-⊎).

open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Data.Sigma hiding (_∨_ ; _∧_)
open import Cubical.Data.Sum
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Unit
open import Cubical.Data.Bool hiding (_≤_ ; _≥_) renaming (_≟_ to _=B_)

open import Cubical.HITs.PropositionalTruncation as PT
import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.Ring.Properties
open import Cubical.Tactics.CommRingSolver

open import BasicDefinitions
open import BooleanRing.BooleanRingMaps
open import BooleanRing.BoolRingUnivalence
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.FreeBooleanRing.freeBATerms
open import BooleanRing.BooleanRingQuotients.QuotientBool as QB
open import BooleanRing.Products

open import CountablyPresentedBooleanRings.Definitions
open import CountablyPresentedBooleanRings.EquivalenceOfCountablyPresentedDefinitions
open import Countability.Properties
open import CountablyPresentedBooleanRings.Examples.TrivialBA using (countUnit)
open import CommRingQuotients.EquivHelper
open import StoneSpaces.Spectrum using (Booleω)

open BooleanRingStr ⦃...⦄

-- ═══════════════════════════════════════════════════════════════
-- Product presentation, generalized over arbitrary types
-- ═══════════════════════════════════════════════════════════════

module ProductPresentation {GA GB RA RB : Type₀}
  (fA : RA → ⟨ freeBA GA ⟩) (fB : RB → ⟨ freeBA GB ⟩) where

  -- Generator type: left gens ⊎ right gens ⊎ separator
  G : Type₀
  G = GA ⊎ (GB ⊎ Unit)

  -- Relation index: A-rels ⊎ B-rels ⊎ idempotent conditions
  RelIdx : Type₀
  RelIdx = (RA ⊎ RB) ⊎ (GA ⊎ GB)

  -- Generator embeddings
  e-gen : ⟨ freeBA G ⟩
  e-gen = generator (inr (inr tt))

  left-gen : GA → ⟨ freeBA G ⟩
  left-gen a = generator (inl a)

  right-gen : GB → ⟨ freeBA G ⟩
  right-gen b = generator (inr (inl b))

  -- Lift maps: freeBA GA → freeBA G and freeBA GB → freeBA G
  liftL : BoolHom (freeBA GA) (freeBA G)
  liftL = inducedBAHom GA (freeBA G) left-gen

  liftR : BoolHom (freeBA GB) (freeBA G)
  liftR = inducedBAHom GB (freeBA G) right-gen

  private
    A = freeBA GA QB./Im fA
    B = freeBA GB QB./Im fB

    instance
      _ = snd (freeBA G)
      _ = snd A
      _ = snd B
      _ = snd (A ×BR B)

  -- 4 families of relations
  rel4 : RelIdx → ⟨ freeBA G ⟩
  rel4 (inl (inl r)) = e-gen · fst liftL (fA r)           -- e · A-relations
  rel4 (inl (inr r)) = (𝟙 + e-gen) · fst liftR (fB r)    -- (1+e) · B-relations
  rel4 (inr (inl a)) = (e-gen · left-gen a) + left-gen a   -- e·aₐ = aₐ
  rel4 (inr (inr b)) = e-gen · right-gen b                 -- e·bᵦ = 0

  Q : BooleanRing ℓ-zero
  Q = freeBA G QB./Im rel4

  -- Q has a countable presentation (from countability closure under ⊎)
  Q-has-cp :
    has-Countability-structure GA → has-Countability-structure GB →
    has-Countability-structure RA → has-Countability-structure RB →
    has-countable-presentation Q
  Q-has-cp cGA cGB cRA cRB =
    G ,
    has-Countability-structure-⊎ cGA (has-Countability-structure-⊎ cGB countUnit) ,
    RelIdx ,
    has-Countability-structure-⊎ (has-Countability-structure-⊎ cRA cRB)
                                  (has-Countability-structure-⊎ cGA cGB) ,
    rel4 , idBoolEquiv Q

  private instance _ = snd Q

  -- Ring theory helpers
  private
    module RTA = RingTheory (CommRing→Ring (BooleanRing→CommRing A))
    module RTB = RingTheory (CommRing→Ring (BooleanRing→CommRing B))

    x+x=0-A : (x : ⟨ A ⟩) → x + x ≡ 𝟘
    x+x=0-A x = BooleanAlgebraStr.characteristic2 (snd A)

  -- ─── Forward: φ : Q → A ×BR B via projections ───

  private
    qA : BoolHom (freeBA GA) A
    qA = QB.quotientImageHom

    qB : BoolHom (freeBA GB) B
    qB = QB.quotientImageHom

    qG : BoolHom (freeBA G) Q
    qG = QB.quotientImageHom

  -- Projection q₁ : Q → A
  -- Sends: aₐ ↦ qA(gen a), bᵦ ↦ 0, e ↦ 1
  q₁-on-gens : G → ⟨ A ⟩
  q₁-on-gens (inl a) = qA $cr generator a
  q₁-on-gens (inr (inl b)) = 𝟘
  q₁-on-gens (inr (inr tt)) = 𝟙

  q₁-free : BoolHom (freeBA G) A
  q₁-free = inducedBAHom G A q₁-on-gens

  private
    q₁-eval : (x : G) → q₁-free $cr generator x ≡ q₁-on-gens x
    q₁-eval = funExt⁻ (evalBAInduce G A q₁-on-gens)

    -- q₁-free ∘ liftL = qA (they agree on generators)
    q₁∘liftL≡qA : q₁-free ∘cr liftL ≡ qA
    q₁∘liftL≡qA =
      sym (inducedBAHomUnique GA A (λ k → qA $cr generator k)
        (q₁-free ∘cr liftL)
        (funExt (λ k →
          cong (fst q₁-free) (funExt⁻ (evalBAInduce GA (freeBA G) left-gen) k)
          ∙ q₁-eval (inl k))))
      ∙ inducedBAHomUnique GA A (λ k → qA $cr generator k) qA refl

    -- q₁-free kills all relations
    q₁-kills : (x : RelIdx) → q₁-free $cr rel4 x ≡ 𝟘
    -- e · liftL(fA r): q₁(e) · q₁(liftL(fA r)) = 1 · qA(fA r) = 0
    q₁-kills (inl (inl r)) =
      IsCommRingHom.pres· (snd q₁-free) e-gen (fst liftL (fA r))
      ∙ cong₂ _·_ (q₁-eval (inr (inr tt))) (funExt⁻ (cong fst q₁∘liftL≡qA) (fA r))
      ∙ ·IdL (qA $cr fA r)
      ∙ QB.zeroOnImage {f = fA} r
    -- (1+e) · liftR(fB r): q₁(1+e) · q₁(liftR(fB r)) = (1+1) · ... = 0 · ... = 0
    q₁-kills (inl (inr r)) =
      IsCommRingHom.pres· (snd q₁-free) (𝟙 + e-gen) (fst liftR (fB r))
      ∙ cong₂ _·_
          (IsCommRingHom.pres+ (snd q₁-free) 𝟙 e-gen
           ∙ cong₂ _+_ (IsCommRingHom.pres1 (snd q₁-free)) (q₁-eval (inr (inr tt)))
           ∙ x+x=0-A 𝟙)
          refl
      ∙ RTA.0LeftAnnihilates _
    -- e · aₐ + aₐ: 1 · qA(gen a) + qA(gen a) = 0
    q₁-kills (inr (inl a)) =
      IsCommRingHom.pres+ (snd q₁-free) (e-gen · left-gen a) (left-gen a)
      ∙ cong₂ _+_
          (IsCommRingHom.pres· (snd q₁-free) e-gen (left-gen a)
           ∙ cong₂ _·_ (q₁-eval (inr (inr tt))) (q₁-eval (inl a))
           ∙ ·IdL (qA $cr generator a))
          (q₁-eval (inl a))
      ∙ x+x=0-A (qA $cr generator a)
    -- e · bᵦ: 1 · 0 = 0
    q₁-kills (inr (inr b)) =
      IsCommRingHom.pres· (snd q₁-free) e-gen (right-gen b)
      ∙ cong₂ _·_ (q₁-eval (inr (inr tt))) (q₁-eval (inr (inl b)))
      ∙ ·IdL 𝟘

  q₁ : BoolHom Q A
  q₁ = QB.inducedHom A q₁-free q₁-kills

  -- Projection q₂ : Q → B
  -- Sends: aₐ ↦ 0, bᵦ ↦ qB(gen b), e ↦ 0
  q₂-on-gens : G → ⟨ B ⟩
  q₂-on-gens (inl a) = 𝟘
  q₂-on-gens (inr (inl b)) = qB $cr generator b
  q₂-on-gens (inr (inr tt)) = 𝟘

  q₂-free : BoolHom (freeBA G) B
  q₂-free = inducedBAHom G B q₂-on-gens

  private
    q₂-eval : (x : G) → q₂-free $cr generator x ≡ q₂-on-gens x
    q₂-eval = funExt⁻ (evalBAInduce G B q₂-on-gens)

    -- q₂-free ∘ liftR = qB
    q₂∘liftR≡qB : q₂-free ∘cr liftR ≡ qB
    q₂∘liftR≡qB =
      sym (inducedBAHomUnique GB B (λ k → qB $cr generator k)
        (q₂-free ∘cr liftR)
        (funExt (λ k →
          cong (fst q₂-free) (funExt⁻ (evalBAInduce GB (freeBA G) right-gen) k)
          ∙ q₂-eval (inr (inl k)))))
      ∙ inducedBAHomUnique GB B (λ k → qB $cr generator k) qB refl

    -- q₂-free kills all relations
    q₂-kills : (x : RelIdx) → q₂-free $cr rel4 x ≡ 𝟘
    -- e · liftL(fA r): q₂(e) · ... = 0 · ... = 0
    q₂-kills (inl (inl r)) =
      IsCommRingHom.pres· (snd q₂-free) e-gen (fst liftL (fA r))
      ∙ cong₂ _·_ (q₂-eval (inr (inr tt))) refl
      ∙ RTB.0LeftAnnihilates _
    -- (1+e) · liftR(fB r): (1+0) · qB(fB r) = 1 · 0 = 0
    q₂-kills (inl (inr r)) =
      IsCommRingHom.pres· (snd q₂-free) (𝟙 + e-gen) (fst liftR (fB r))
      ∙ cong₂ _·_
          (IsCommRingHom.pres+ (snd q₂-free) 𝟙 e-gen
           ∙ cong₂ _+_ (IsCommRingHom.pres1 (snd q₂-free)) (q₂-eval (inr (inr tt)))
           ∙ +IdR 𝟙)
          (funExt⁻ (cong fst q₂∘liftR≡qB) (fB r))
      ∙ ·IdL (qB $cr fB r)
      ∙ QB.zeroOnImage {f = fB} r
    -- e · aₐ + aₐ: 0 · 0 + 0 = 0
    q₂-kills (inr (inl a)) =
      IsCommRingHom.pres+ (snd q₂-free) (e-gen · left-gen a) (left-gen a)
      ∙ cong₂ _+_
          (IsCommRingHom.pres· (snd q₂-free) e-gen (left-gen a)
           ∙ cong₂ _·_ (q₂-eval (inr (inr tt))) (q₂-eval (inl a))
           ∙ RTB.0LeftAnnihilates 𝟘)
          (q₂-eval (inl a))
      ∙ +IdL 𝟘
    -- e · bᵦ: 0 · qB(gen b) = 0
    q₂-kills (inr (inr b)) =
      IsCommRingHom.pres· (snd q₂-free) e-gen (right-gen b)
      ∙ cong₂ _·_ (q₂-eval (inr (inr tt))) (q₂-eval (inr (inl b)))
      ∙ RTB.0LeftAnnihilates _

  q₂ : BoolHom Q B
  q₂ = QB.inducedHom B q₂-free q₂-kills

  -- Forward map: φ = ⟨q₁, q₂⟩
  φ : BoolHom Q (A ×BR B)
  φ = ⟨ A , B ⟩BR q₁ q₂

  -- ─── Backward: ψ : A ×BR B → Q ───
  -- ψ(a, b) = α(a) + β(b) where α, β defined by quotient elimination
  -- α(qA(x)) = eQ · qG(liftL(x)), β(qB(y)) = (1+eQ) · qG(liftR(y))

  private
    R-freeGA = BooleanRing→CommRing (freeBA GA)
    R-freeGB = BooleanRing→CommRing (freeBA GB)
    R-freeG = BooleanRing→CommRing (freeBA G)
    eQ : ⟨ Q ⟩
    eQ = qG $cr e-gen
    e'Q : ⟨ Q ⟩
    e'Q = 𝟙 + eQ

    isSetQ : isSet ⟨ Q ⟩
    isSetQ = is-set
      where instance _ = snd (BooleanRing→CommRing Q)

    module RTQ = RingTheory (CommRing→Ring (BooleanRing→CommRing Q))
    module BAQ = BooleanAlgebraStr (snd Q)

    -- In char 2: a + b = 0 → a = b
    char2-cancel : {a b : ⟨ Q ⟩} → a + b ≡ 𝟘 → a ≡ b
    char2-cancel {a} {b} p =
      sym (+IdR a)
      ∙ cong (a +_) (sym BAQ.characteristic2)
      ∙ +Assoc a b b
      ∙ cong (_+ b) p
      ∙ +IdL b

    -- Shorthand for the composed ring homs
    FL : BoolHom (freeBA GA) Q
    FL = qG ∘cr liftL

    FR : BoolHom (freeBA GB) Q
    FR = qG ∘cr liftR

    -- Key lemma: eQ · FL(d) = 0 when d is in ideal generated by fA
    eQ-kills-ideal : (d : ⟨ freeBA GA ⟩) →
      IQ.generatedIdeal R-freeGA fA d → eQ · (FL $cr d) ≡ 𝟘
    eQ-kills-ideal .(fA x) (IQ.single x) =
      sym (IsCommRingHom.pres· (snd qG) e-gen (fst liftL (fA x)))
      ∙ QB.zeroOnImage {f = rel4} (inl (inl x))
    eQ-kills-ideal _ IQ.zero =
      cong (eQ ·_) (IsCommRingHom.pres0 (snd FL))
      ∙ RTQ.0RightAnnihilates eQ
    eQ-kills-ideal _ (IQ.add {x} {y} dx dy) =
      cong (eQ ·_) (IsCommRingHom.pres+ (snd FL) x y)
      ∙ ·DistR+ eQ (FL $cr x) (FL $cr y)
      ∙ cong₂ _+_ (eQ-kills-ideal x dx) (eQ-kills-ideal y dy)
      ∙ +IdL 𝟘
    eQ-kills-ideal _ (IQ.mul {r} {x} dx) =
      cong (eQ ·_) (IsCommRingHom.pres· (snd FL) r x)
      ∙ ·Assoc eQ (FL $cr r) (FL $cr x)
      ∙ cong (_· (FL $cr x)) (·Comm eQ (FL $cr r))
      ∙ sym (·Assoc (FL $cr r) eQ (FL $cr x))
      ∙ cong ((FL $cr r) ·_) (eQ-kills-ideal x dx)
      ∙ RTQ.0RightAnnihilates (FL $cr r)
    eQ-kills-ideal _ (IQ.squash p q i) =
      isSetQ _ _ (eQ-kills-ideal _ p) (eQ-kills-ideal _ q) i

    instance
      _ = snd (freeBA GA)
      _ = snd (freeBA GB)

    -- In freeBA GA: x + y = x - y (since -y = y in Boolean rings)
    char2-freeGA : (a b : ⟨ freeBA GA ⟩) →
      a + b ≡ CommRingStr._-_ (snd R-freeGA) a b
    char2-freeGA a b = cong (a +_) (BooleanAlgebraStr.-IsId (snd (freeBA GA)))

    -- Well-definedness for α: if x - y ∈ ideal(fA), then eQ·FL(x) = eQ·FL(y)
    α-wd : (x y : ⟨ freeBA GA ⟩) →
      IQ.generatedIdeal R-freeGA fA (CommRingStr._-_ (snd R-freeGA) x y) →
      eQ · (FL $cr x) ≡ eQ · (FL $cr y)
    α-wd x y gid = char2-cancel
      (sym (·DistR+ eQ (FL $cr x) (FL $cr y))
       ∙ cong (eQ ·_) (sym (IsCommRingHom.pres+ (snd FL) x y))
       ∙ cong (λ z → eQ · (FL $cr z)) (char2-freeGA x y)
       ∙ eQ-kills-ideal _ gid)

    -- Similarly for β with e'Q · FR
    e'Q-kills-ideal : (d : ⟨ freeBA GB ⟩) →
      IQ.generatedIdeal R-freeGB fB d → e'Q · (FR $cr d) ≡ 𝟘
    e'Q-kills-ideal .(fB x) (IQ.single x) =
      cong (_· (FR $cr fB x)) (sym e'Q-is-qG)
      ∙ sym (IsCommRingHom.pres· (snd qG) (𝟙 + e-gen) (fst liftR (fB x)))
      ∙ QB.zeroOnImage {f = rel4} (inl (inr x))
      where
        e'Q-is-qG : qG $cr (𝟙 + e-gen) ≡ e'Q
        e'Q-is-qG = IsCommRingHom.pres+ (snd qG) 𝟙 e-gen
                   ∙ cong (_+ eQ) (IsCommRingHom.pres1 (snd qG))
    e'Q-kills-ideal _ IQ.zero =
      cong (e'Q ·_) (IsCommRingHom.pres0 (snd FR))
      ∙ RTQ.0RightAnnihilates e'Q
    e'Q-kills-ideal _ (IQ.add {x} {y} dx dy) =
      cong (e'Q ·_) (IsCommRingHom.pres+ (snd FR) x y)
      ∙ ·DistR+ e'Q (FR $cr x) (FR $cr y)
      ∙ cong₂ _+_ (e'Q-kills-ideal x dx) (e'Q-kills-ideal y dy)
      ∙ +IdL 𝟘
    e'Q-kills-ideal _ (IQ.mul {r} {x} dx) =
      cong (e'Q ·_) (IsCommRingHom.pres· (snd FR) r x)
      ∙ ·Assoc e'Q (FR $cr r) (FR $cr x)
      ∙ cong (_· (FR $cr x)) (·Comm e'Q (FR $cr r))
      ∙ sym (·Assoc (FR $cr r) e'Q (FR $cr x))
      ∙ cong ((FR $cr r) ·_) (e'Q-kills-ideal x dx)
      ∙ RTQ.0RightAnnihilates (FR $cr r)
    e'Q-kills-ideal _ (IQ.squash p q i) =
      isSetQ _ _ (e'Q-kills-ideal _ p) (e'Q-kills-ideal _ q) i

    char2-freeGB : (a b : ⟨ freeBA GB ⟩) →
      a + b ≡ CommRingStr._-_ (snd R-freeGB) a b
    char2-freeGB a b = cong (a +_) (BooleanAlgebraStr.-IsId (snd (freeBA GB)))

    β-wd : (x y : ⟨ freeBA GB ⟩) →
      IQ.generatedIdeal R-freeGB fB (CommRingStr._-_ (snd R-freeGB) x y) →
      e'Q · (FR $cr x) ≡ e'Q · (FR $cr y)
    β-wd x y gid = char2-cancel
      (sym (·DistR+ e'Q (FR $cr x) (FR $cr y))
       ∙ cong (e'Q ·_) (sym (IsCommRingHom.pres+ (snd FR) x y))
       ∙ cong (λ z → e'Q · (FR $cr z)) (char2-freeGB x y)
       ∙ e'Q-kills-ideal _ gid)

  -- α : A → Q via quotient elimination
  α : ⟨ A ⟩ → ⟨ Q ⟩
  α = QB.quotientRec {f = fA} isSetQ (λ x → eQ · (FL $cr x)) α-wd

  -- β : B → Q via quotient elimination
  β : ⟨ B ⟩ → ⟨ Q ⟩
  β = QB.quotientRec {f = fB} isSetQ (λ y → e'Q · (FR $cr y)) β-wd

  -- Computation rules
  private
    α-β : (x : ⟨ freeBA GA ⟩) → α (qA $cr x) ≡ eQ · (FL $cr x)
    α-β x = QB.quotientRecβ {f = fA} x

    β-β : (y : ⟨ freeBA GB ⟩) → β (qB $cr y) ≡ e'Q · (FR $cr y)
    β-β y = QB.quotientRecβ {f = fB} y

  -- ψ underlying function
  private
    ψ-fun : ⟨ A ⟩ × ⟨ B ⟩ → ⟨ Q ⟩
    ψ-fun (a , b) = α a + β b

  -- Helper: α and β are additive
  private
    α-additive : (a₁ a₂ : ⟨ A ⟩) → α (a₁ + a₂) ≡ α a₁ + α a₂
    α-additive = QB.quotientElimProp {f = fA}
      (λ _ → isPropΠ (λ _ → isSetQ _ _))
      (λ x₁ → QB.quotientElimProp {f = fA}
        (λ _ → isSetQ _ _)
        (λ x₂ →
          cong α (sym (IsCommRingHom.pres+ (snd qA) x₁ x₂))
          ∙ α-β (x₁ + x₂)
          ∙ cong (eQ ·_) (IsCommRingHom.pres+ (snd FL) x₁ x₂)
          ∙ ·DistR+ eQ (FL $cr x₁) (FL $cr x₂)
          ∙ cong₂ _+_ (sym (α-β x₁)) (sym (α-β x₂))))

    β-additive : (b₁ b₂ : ⟨ B ⟩) → β (b₁ + b₂) ≡ β b₁ + β b₂
    β-additive = QB.quotientElimProp {f = fB}
      (λ _ → isPropΠ (λ _ → isSetQ _ _))
      (λ y₁ → QB.quotientElimProp {f = fB}
        (λ _ → isSetQ _ _)
        (λ y₂ →
          cong β (sym (IsCommRingHom.pres+ (snd qB) y₁ y₂))
          ∙ β-β (y₁ + y₂)
          ∙ cong (e'Q ·_) (IsCommRingHom.pres+ (snd FR) y₁ y₂)
          ∙ ·DistR+ e'Q (FR $cr y₁) (FR $cr y₂)
          ∙ cong₂ _+_ (sym (β-β y₁)) (sym (β-β y₂))))

    -- eQ + e'Q = 1 (idempotent decomposition)
    eQ+e'Q=1 : eQ + e'Q ≡ 𝟙
    eQ+e'Q=1 =
      +Comm eQ (𝟙 + eQ)
      ∙ sym (+Assoc 𝟙 eQ eQ)
      ∙ cong (𝟙 +_) BAQ.characteristic2
      ∙ +IdR 𝟙

    -- α(1_A) = eQ, β(1_B) = e'Q
    α-1 : α 𝟙 ≡ eQ
    α-1 = cong α (sym (IsCommRingHom.pres1 (snd qA)))
         ∙ α-β 𝟙
         ∙ cong (eQ ·_) (IsCommRingHom.pres1 (snd FL))
         ∙ ·IdR eQ

    β-1 : β 𝟙 ≡ e'Q
    β-1 = cong β (sym (IsCommRingHom.pres1 (snd qB)))
         ∙ β-β 𝟙
         ∙ cong (e'Q ·_) (IsCommRingHom.pres1 (snd FR))
         ∙ ·IdR e'Q

    ψ-pres1 : ψ-fun (𝟙 , 𝟙) ≡ 𝟙
    ψ-pres1 = cong₂ _+_ α-1 β-1 ∙ eQ+e'Q=1

    -- (a+b)+(c+d) = (a+c)+(b+d) in any commutative group
    +swap : (a b c d : ⟨ Q ⟩) → (a + b) + (c + d) ≡ (a + c) + (b + d)
    +swap a b c d =
      sym (+Assoc a b (c + d))
      ∙ cong (a +_) (+Assoc b c d ∙ cong (_+ d) (+Comm b c) ∙ sym (+Assoc c b d))
      ∙ +Assoc a c (b + d)

    ψ-pres+ : (x y : ⟨ A ⟩ × ⟨ B ⟩) →
      ψ-fun (fst x + fst y , snd x + snd y) ≡ ψ-fun x + ψ-fun y
    ψ-pres+ (a₁ , b₁) (a₂ , b₂) =
      cong₂ _+_ (α-additive a₁ a₂) (β-additive b₁ b₂)
      ∙ +swap (α a₁) (α a₂) (β b₁) (β b₂)

    -- eQ · e'Q = 0 (orthogonal idempotents)
    eQ·e'Q=0 : eQ · e'Q ≡ 𝟘
    eQ·e'Q=0 = ·DistR+ eQ 𝟙 eQ
             ∙ cong₂ _+_ (·IdR eQ) (·Idem eQ)
             ∙ BAQ.characteristic2

    -- (e·a)·(e·b) = (e·a)·b when e² = e
    eQ-absorb : (a b : ⟨ Q ⟩) → (eQ · a) · (eQ · b) ≡ (eQ · a) · b
    eQ-absorb a b =
      ·Assoc (eQ · a) eQ b
      ∙ cong (_· b) (·Comm (eQ · a) eQ ∙ ·Assoc eQ eQ a ∙ cong (_· a) (·Idem eQ))

    e'Q-absorb : (a b : ⟨ Q ⟩) → (e'Q · a) · (e'Q · b) ≡ (e'Q · a) · b
    e'Q-absorb a b =
      ·Assoc (e'Q · a) e'Q b
      ∙ cong (_· b) (·Comm (e'Q · a) e'Q ∙ ·Assoc e'Q e'Q a ∙ cong (_· a) (·Idem e'Q))

    -- α is multiplicative
    α-mult : (a₁ a₂ : ⟨ A ⟩) → α (a₁ · a₂) ≡ α a₁ · α a₂
    α-mult = QB.quotientElimProp {f = fA}
      (λ _ → isPropΠ (λ _ → isSetQ _ _))
      (λ x₁ → QB.quotientElimProp {f = fA}
        (λ _ → isSetQ _ _)
        (λ x₂ →
          cong α (sym (IsCommRingHom.pres· (snd qA) x₁ x₂))
          ∙ α-β (x₁ · x₂)
          ∙ cong (eQ ·_) (IsCommRingHom.pres· (snd FL) x₁ x₂)
          ∙ ·Assoc eQ (FL $cr x₁) (FL $cr x₂)
          ∙ sym (eQ-absorb (FL $cr x₁) (FL $cr x₂))
          ∙ cong₂ _·_ (sym (α-β x₁)) (sym (α-β x₂))))

    β-mult : (b₁ b₂ : ⟨ B ⟩) → β (b₁ · b₂) ≡ β b₁ · β b₂
    β-mult = QB.quotientElimProp {f = fB}
      (λ _ → isPropΠ (λ _ → isSetQ _ _))
      (λ y₁ → QB.quotientElimProp {f = fB}
        (λ _ → isSetQ _ _)
        (λ y₂ →
          cong β (sym (IsCommRingHom.pres· (snd qB) y₁ y₂))
          ∙ β-β (y₁ · y₂)
          ∙ cong (e'Q ·_) (IsCommRingHom.pres· (snd FR) y₁ y₂)
          ∙ ·Assoc e'Q (FR $cr y₁) (FR $cr y₂)
          ∙ sym (e'Q-absorb (FR $cr y₁) (FR $cr y₂))
          ∙ cong₂ _·_ (sym (β-β y₁)) (sym (β-β y₂))))

    -- Cross terms vanish: α(a) · β(b) = 0
    αβ-zero : (a : ⟨ A ⟩) (b : ⟨ B ⟩) → α a · β b ≡ 𝟘
    αβ-zero = QB.quotientElimProp {f = fA}
      (λ _ → isPropΠ (λ _ → isSetQ _ _))
      (λ x → QB.quotientElimProp {f = fB}
        (λ _ → isSetQ _ _)
        (λ y →
          cong₂ _·_ (α-β x) (β-β y)
          ∙ ·Assoc (eQ · (FL $cr x)) e'Q (FR $cr y)
          ∙ cong (_· (FR $cr y))
              (·Comm (eQ · (FL $cr x)) e'Q
               ∙ ·Assoc e'Q eQ (FL $cr x)
               ∙ cong (_· (FL $cr x)) (·Comm e'Q eQ ∙ eQ·e'Q=0)
               ∙ RTQ.0LeftAnnihilates (FL $cr x))
          ∙ RTQ.0LeftAnnihilates (FR $cr y)))

    -- (x + y) · z = x·z + y·z via ·Comm + ·DistR+
    ·distL : (x y z : ⟨ Q ⟩) → (x + y) · z ≡ x · z + y · z
    ·distL x y z = ·Comm (x + y) z ∙ ·DistR+ z x y ∙ cong₂ _+_ (·Comm z x) (·Comm z y)

    ψ-pres· : (x y : ⟨ A ⟩ × ⟨ B ⟩) →
      ψ-fun (fst x · fst y , snd x · snd y) ≡ ψ-fun x · ψ-fun y
    ψ-pres· (a₁ , b₁) (a₂ , b₂) = sym (
      ·distL (α a₁) (β b₁) (α a₂ + β b₂)
      ∙ cong₂ _+_ (·DistR+ (α a₁) (α a₂) (β b₂))
                   (·DistR+ (β b₁) (α a₂) (β b₂))
      ∙ cong₂ _+_ (cong ((α a₁ · α a₂) +_) (αβ-zero a₁ b₂) ∙ +IdR _)
                   (cong₂ _+_ (·Comm (β b₁) (α a₂) ∙ αβ-zero a₂ b₁) refl ∙ +IdL _)
      ∙ sym (cong₂ _+_ (α-mult a₁ a₂) (β-mult b₁ b₂)))

  ψ : BoolHom (A ×BR B) Q
  fst ψ = ψ-fun
  snd ψ = makeIsCommRingHom ψ-pres1
    (λ x y → ψ-pres+ x y) (λ x y → ψ-pres· x y)

  -- ─── Roundtrips ───
  private
    -- Computation: q₁ ∘ qG = q₁-free, q₂ ∘ qG = q₂-free
    q₁-comp : q₁ ∘cr qG ≡ q₁-free
    q₁-comp = QB.evalInduce A

    q₂-comp : q₂ ∘cr qG ≡ q₂-free
    q₂-comp = QB.evalInduce B

    q₁-on-eQ : q₁ $cr eQ ≡ 𝟙
    q₁-on-eQ = funExt⁻ (cong fst q₁-comp) e-gen ∙ q₁-eval (inr (inr tt))

    q₂-on-eQ : q₂ $cr eQ ≡ 𝟘
    q₂-on-eQ = funExt⁻ (cong fst q₂-comp) e-gen ∙ q₂-eval (inr (inr tt))

    q₁-on-FL : (x : ⟨ freeBA GA ⟩) → q₁ $cr (FL $cr x) ≡ qA $cr x
    q₁-on-FL x = funExt⁻ (cong fst q₁-comp) (liftL $cr x)
               ∙ funExt⁻ (cong fst q₁∘liftL≡qA) x

    q₂-on-FR : (y : ⟨ freeBA GB ⟩) → q₂ $cr (FR $cr y) ≡ qB $cr y
    q₂-on-FR y = funExt⁻ (cong fst q₂-comp) (liftR $cr y)
               ∙ funExt⁻ (cong fst q₂∘liftR≡qB) y

    -- q₁ ∘ α = id on A
    q₁α : (a : ⟨ A ⟩) → q₁ $cr (α a) ≡ a
    q₁α = QB.quotientElimProp {f = fA}
      (λ _ → is-set _ _)
      (λ x →
        cong (q₁ $cr_) (α-β x)
        ∙ IsCommRingHom.pres· (snd q₁) eQ (FL $cr x)
        ∙ cong₂ _·_ q₁-on-eQ (q₁-on-FL x)
        ∙ ·IdL (qA $cr x))

    -- q₁ ∘ β = 0
    q₁β : (b : ⟨ B ⟩) → q₁ $cr (β b) ≡ 𝟘
    q₁β = QB.quotientElimProp {f = fB}
      (λ _ → is-set _ _)
      (λ y →
        cong (q₁ $cr_) (β-β y)
        ∙ IsCommRingHom.pres· (snd q₁) e'Q (FR $cr y)
        ∙ cong (_· (q₁ $cr (FR $cr y)))
            (IsCommRingHom.pres+ (snd q₁) 𝟙 eQ
             ∙ cong₂ _+_ (IsCommRingHom.pres1 (snd q₁)) q₁-on-eQ
             ∙ x+x=0-A 𝟙)
        ∙ RTA.0LeftAnnihilates _)

    -- q₂ ∘ α = 0
    q₂α : (a : ⟨ A ⟩) → q₂ $cr (α a) ≡ 𝟘
    q₂α = QB.quotientElimProp {f = fA}
      (λ _ → is-set _ _)
      (λ x →
        cong (q₂ $cr_) (α-β x)
        ∙ IsCommRingHom.pres· (snd q₂) eQ (FL $cr x)
        ∙ cong (_· (q₂ $cr (FL $cr x))) q₂-on-eQ
        ∙ RTB.0LeftAnnihilates _)

    -- q₂ ∘ β = id on B
    q₂β : (b : ⟨ B ⟩) → q₂ $cr (β b) ≡ b
    q₂β = QB.quotientElimProp {f = fB}
      (λ _ → is-set _ _)
      (λ y →
        cong (q₂ $cr_) (β-β y)
        ∙ IsCommRingHom.pres· (snd q₂) e'Q (FR $cr y)
        ∙ cong₂ _·_
            (IsCommRingHom.pres+ (snd q₂) 𝟙 eQ
             ∙ cong₂ _+_ (IsCommRingHom.pres1 (snd q₂)) q₂-on-eQ
             ∙ +IdR 𝟙)
            (q₂-on-FR y)
        ∙ ·IdL (qB $cr y))

  φ∘ψ=id : φ ∘cr ψ ≡ idCommRingHom (BooleanRing→CommRing (A ×BR B))
  φ∘ψ=id = CommRingHom≡ (funExt (λ { (a , b) → ΣPathP
    ( IsCommRingHom.pres+ (snd q₁) (α a) (β b)
      ∙ cong₂ _+_ (q₁α a) (q₁β b) ∙ +IdR a
    , IsCommRingHom.pres+ (snd q₂) (α a) (β b)
      ∙ cong₂ _+_ (q₂α a) (q₂β b) ∙ +IdL b
    ) }))

  ψ∘φ=id : ψ ∘cr φ ≡ idCommRingHom (BooleanRing→CommRing Q)
  ψ∘φ=id = CommRingHom≡ (QB.quotientImageHomEpi {f = rel4} (⟨ Q ⟩ , isSetQ)
    (cong fst (sym (inducedBAHomUnique G Q gen-map (ψ ∘cr φ ∘cr qG) gen-agree)
              ∙ inducedBAHomUnique G Q gen-map qG refl)))
    where
      gen-map = fst qG ∘ generator

      α-0 : α 𝟘 ≡ 𝟘
      α-0 = cong α (sym (+IdL 𝟘)) ∙ α-additive 𝟘 𝟘 ∙ BAQ.characteristic2

      β-0 : β 𝟘 ≡ 𝟘
      β-0 = cong β (sym (+IdL 𝟘)) ∙ β-additive 𝟘 𝟘 ∙ BAQ.characteristic2

      eQ·aₐ=aₐ : (a : GA) → eQ · (qG $cr left-gen a) ≡ qG $cr left-gen a
      eQ·aₐ=aₐ a = char2-cancel
        (cong₂ _+_ (sym (IsCommRingHom.pres· (snd qG) e-gen (left-gen a))) refl
         ∙ sym (IsCommRingHom.pres+ (snd qG) (e-gen · left-gen a) (left-gen a))
         ∙ QB.zeroOnImage {f = rel4} (inr (inl a)))

      eQ·bᵦ=0 : (b : GB) → eQ · (qG $cr right-gen b) ≡ 𝟘
      eQ·bᵦ=0 b = sym (IsCommRingHom.pres· (snd qG) e-gen (right-gen b))
                 ∙ QB.zeroOnImage {f = rel4} (inr (inr b))

      e'Q·bᵦ=bᵦ : (b : GB) → e'Q · (qG $cr right-gen b) ≡ qG $cr right-gen b
      e'Q·bᵦ=bᵦ b =
        ·distL 𝟙 eQ (qG $cr right-gen b)
        ∙ cong₂ _+_ (·IdL (qG $cr right-gen b)) (eQ·bᵦ=0 b)
        ∙ +IdR (qG $cr right-gen b)

      gen-agree : fst (ψ ∘cr φ ∘cr qG) ∘ generator ≡ gen-map
      gen-agree = funExt λ {
        (inl a) →
          cong₂ _+_
            (cong α (funExt⁻ (cong fst q₁-comp) (left-gen a) ∙ q₁-eval (inl a))
             ∙ α-β (generator a)
             ∙ cong (eQ ·_) (cong (qG $cr_) (funExt⁻ (evalBAInduce GA (freeBA G) left-gen) a))
             ∙ eQ·aₐ=aₐ a)
            (cong β (funExt⁻ (cong fst q₂-comp) (left-gen a) ∙ q₂-eval (inl a))
             ∙ β-0)
          ∙ +IdR (qG $cr left-gen a) ;
        (inr (inl b)) →
          cong₂ _+_
            (cong α (funExt⁻ (cong fst q₁-comp) (right-gen b) ∙ q₁-eval (inr (inl b)))
             ∙ α-0)
            (cong β (funExt⁻ (cong fst q₂-comp) (right-gen b) ∙ q₂-eval (inr (inl b)))
             ∙ β-β (generator b)
             ∙ cong (e'Q ·_) (cong (qG $cr_) (funExt⁻ (evalBAInduce GB (freeBA G) right-gen) b))
             ∙ e'Q·bᵦ=bᵦ b)
          ∙ +IdL (qG $cr right-gen b) ;
        (inr (inr tt)) →
          cong₂ _+_
            (cong α (funExt⁻ (cong fst q₁-comp) e-gen ∙ q₁-eval (inr (inr tt)))
             ∙ α-1)
            (cong β (funExt⁻ (cong fst q₂-comp) e-gen ∙ q₂-eval (inr (inr tt)))
             ∙ β-0)
          ∙ +IdR eQ
        }

  -- The equivalence
  Q≃A×B : BooleanRingEquiv Q (A ×BR B)
  Q≃A×B = isoToCommRingEquiv φ (fst ψ)
    (funExt⁻ (cong fst φ∘ψ=id))
    (funExt⁻ (cong fst ψ∘φ=id))

  -- A ×BR B has a countable presentation (given countability of GA, GB, RA, RB)
  A×B-has-countable-pres :
    has-Countability-structure GA → has-Countability-structure GB →
    has-Countability-structure RA → has-Countability-structure RB →
    has-countable-presentation (A ×BR B)
  A×B-has-countable-pres cGA cGB cRA cRB =
    subst has-countable-presentation
      (uaBoolRing Q≃A×B)
      (Q-has-cp cGA cGB cRA cRB)

-- ═══════════════════════════════════════════════════════════════
-- Product preserves equivalences
-- ═══════════════════════════════════════════════════════════════

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
  (ΣPathP (IsCommRingHom.pres1 (snd eA) , IsCommRingHom.pres1 (snd eB)))
  (λ x y → ΣPathP (IsCommRingHom.pres+ (snd eA) _ _ , IsCommRingHom.pres+ (snd eB) _ _))
  (λ x y → ΣPathP (IsCommRingHom.pres· (snd eA) _ _ , IsCommRingHom.pres· (snd eB) _ _))

-- ═══════════════════════════════════════════════════════════════
-- The main result: is-countably-presented is closed under ×BR
-- ═══════════════════════════════════════════════════════════════

is-countably-presented-×BR : (A B : BooleanRing ℓ-zero) →
  is-countably-presented A → is-countably-presented B →
  is-countably-presented (A ×BR B)
is-countably-presented-×BR A B = PT.map2 go
  where
    go : has-countable-presentation A →
         has-countable-presentation B →
         has-countable-presentation (A ×BR B)
    go (GA , cGA , RA , cRA , fA , eA) (GB , cGB , RB , cRB , fB , eB) =
      subst has-countable-presentation
        (uaBoolRing (×BR-resp-equiv
          _ A _ B
          (invBooleanRingEquiv A _ eA)
          (invBooleanRingEquiv B _ eB)))
        (ProductPresentation.A×B-has-countable-pres fA fB cGA cGB cRA cRB)

-- Backward-compatible version using Booleω and is-countably-presented-alt
Booleω-closed-×BR : (X Y : Booleω) → is-countably-presented-alt (fst X ×BR fst Y)
Booleω-closed-×BR (A , cpA) (B , cpB) =
  countably-presented-equivalence (A ×BR B) .fst
    (is-countably-presented-×BR A B
      (countably-presented-equivalence A .snd cpA)
      (countably-presented-equivalence B .snd cpB))
