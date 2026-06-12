-- "Surjections are formally surjective": the converse of
-- Axioms.SurjectionsAreFormalSurjections.formalSurjectionsAreSurjectionsAxiom.
--
--   Sp(g) : Sp C → Sp B  surjective   ⟹   g : B → C  injective (mono in BACat)
--
-- where Sp(g) γ = γ ∘cr g  (the action of Sp = BoolHom(−, Bool) on g).
--
-- IMPORTANT — this is NOT axiom-free.  It needs Bool to be a cogenerator / "enough
-- points" / Sp faithful, which in this development *is* the Stone-duality axiom
-- (`StoneDualityAxiom`: evaluationMap B is an equivalence, i.e. B ≅ 2^(Sp B)).
-- Counterexample without it: take a nontrivial B with *no* points (Sp B = ∅) — which is
-- constructively consistent for a countably presented BA, and is exactly the phenomenon
-- the LLPO result exploits — and let g : B → 0 be the map to the trivial algebra.
-- Then Sp 0 = ∅ as well, so Sp(g) : ∅ → ∅ is (vacuously) surjective, yet g collapses all
-- of B and is not injective.  So the "standard categorical fact" silently uses that Sp is
-- faithful, and faithfulness of Sp = BoolHom(−,Bool) is precisely separation by points =
-- StoneDuality.  See the note at the bottom for how this matches the epi/mono phrasing.
module SurjectionsAreFormallySurjective where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Foundations.Equiv using (_≃_ ; invEq ; retEq)
open import Cubical.Data.Bool using (Bool ; isSetBool)
open import Cubical.Data.Sigma
open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing using (_$cr_ ; _∘cr_)
open import Cubical.Algebra.BooleanRing using (BoolHom)

open import StoneSpaces.Spectrum using (Booleω ; Sp ; evaluationMap)
open import Axioms.StoneDuality using (StoneDualityAxiom)
open import Axioms.SurjectionsAreFormalSurjections using (isInjectiveBoolHom ; isSurjectiveSpHom)

module _ (SD : StoneDualityAxiom) where

  -- Separation from Stone duality: evaluationMap B is an equivalence, hence injective,
  -- so x ≡ y as soon as every point γ : Sp B agrees on x and y.
  separatedByPoints : (B : Booleω) (x y : ⟨ fst B ⟩)
                    → ((γ : Sp B) → γ $cr x ≡ γ $cr y) → x ≡ y
  separatedByPoints B x y agree =
    sym (retEq e x) ∙ cong (invEq e) (funExt agree) ∙ retEq e y
    where
      e : ⟨ fst B ⟩ ≃ (Sp B → Bool)
      e = evaluationMap B , SD B

  -- The headline.  For g(x) = g(y), every point γ of B lifts (Sp(g) surjective) to a
  -- point δ of C, and then  γ x = (δ∘g) x = δ(g x) = δ(g y) = (δ∘g) y = γ y.
  surjectionsAreFormallySurjective :
    (B C : Booleω) (g : BoolHom (fst B) (fst C))
    → isSurjectiveSpHom B C g → isInjectiveBoolHom (fst B) (fst C) g
  surjectionsAreFormallySurjective B C g Spg-surj x y gx≡gy =
    separatedByPoints B x y λ γ →
      PT.rec (isSetBool (γ $cr x) (γ $cr y))
        (λ (δ , δg≡γ) →                    -- δ : Sp C ,  δg≡γ : δ ∘cr g ≡ γ
            sym (cong (_$cr x) δg≡γ)        -- γ x        ≡ (δ ∘cr g) x
          ∙ cong (δ $cr_) gx≡gy            -- = δ (g x)  ≡ δ (g y)     [(δ∘cr g) x ≐ δ (g x)]
          ∙ cong (_$cr y) δg≡γ)            -- = (δ ∘cr g) y ≡ γ y
        (Spg-surj γ)

------------------------------------------------------------------------
-- Note: your categorical phrasing, and where the axiom hides in it.
--
-- Sp = BoolHom(−, Bool) is the contravariant representable functor at Bool
-- (SpFunctor in CategoryTheory.StuffFromStoneAboutBAs), and Sp(g) = (− ∘cr g).
--
--   • "surjective and epic are the same":  for the SET-map Sp(g),  surjective ⟹ epic
--     (epis in SET are surjections).  Dually, Sp(g) is monic in SETᵒᵖ.
--   • "if postcomposition is mono you are epic":  the standard fact is
--        g is EPIC  ⟺  for every X, (g ⋆ −) = (− ∘cr g) : Hom(C,X) → Hom(B,X) is injective
--     (Cubical.Categories.Morphism.isEpic).  Here Sp(g) is that map at the single object
--     X = Bool, and we have it SURJECTIVE, not injective — so this fact alone does not
--     close the goal.  What actually turns "Sp(g) epic in SET" into "g monic in BACat" is
--     that a FAITHFUL functor reflects monos/epis (Sp contravariant: Sp(g) epic ⟹ g monic).
--   • g monic in BACat ⟹ g injective (concretely: ker≡0→injBoolHom).
--
-- The load-bearing step is "Sp faithful".  But Sp = BoolHom(−,Bool) is faithful iff Bool
-- separates parallel maps iff Bool is a cogenerator — i.e. iff StoneDuality holds.  In the
-- library this is exactly `Axioms.StoneDuality.SpFullyFaithful`, which is proved *inside*
-- `module _ (SD : StoneDualityAxiom)`.  So the categorical route and the direct proof above
-- consume the same hypothesis; there is no axiom-free shortcut (cf. the counterexample).
--
-- If you'd rather have the proof literally as "Sp(g) epic ⇒ g monic via SpFullyFaithful",
-- say so and I'll build it on `SpFunctor` / `SpFullyFaithful`; it is longer and buys
-- nothing mathematically over `surjectionsAreFormallySurjective`.
