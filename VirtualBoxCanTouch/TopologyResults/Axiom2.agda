-- Project-local completion of FormalizationSSD/Axioms/Axiom2.agda (currently on
-- origin/BooleanAlgebraRefactor, commit 0ef1b03, not yet pulled here).  Verbatim copy
-- except: this module is named `Axiom2` (not `Axioms.Axiom2`) so it can sit in the
-- project beside the library, and the two holes are filled:
--
--   * isSurjective→1                                    (was {! !} at line 50)
--   * FormalSurjectionsToPropositionalCompleteness body (was {! !} at line 56)
--
-- Transplant the two filled clauses back into Axioms/Axiom2.agda when convenient.
--
-- Hole 1: FS (formal surjections are surjections) applied to the injective initial map
--   BoolBR→ (fst B) : BoolCP → B  says Sp of it,  Sp B → Sp BoolCP, is a surjection.
--   Sp BoolCP is the point space (BoolCP is initial), so picking its point and forgetting
--   the fibre yields ∥ Sp B ∥₁ — whence Sp B ↠ Unit.
-- Hole 2: a Stone space S is Sp B for some B with Sp B ≡ S; transport ∥ Sp B ∥₁ (from the
--   module, fed ¬¬ Sp B obtained from ¬¬ ⟨S⟩) along that path.
module Axiom2 where
-- Axiom 2 states that surjections are formal surjections.
-- Another way to phrase this axiom is in propositional completeness.
-- At some point I also thought this was equivalent to LLPO, I'm not sure about that exactly.
-- So it would be good to have written down the implications between these.
open import BasicDefinitions
open import Cubical.Foundations.Prelude
open import BooleanRing.FreeBooleanRing.FreeBool
open import Axioms.SurjectionsAreFormalSurjections
open import Axioms.StoneDuality
open import StoneSpaces.Spectrum
open import AntiEquivalence
open import CountablyPresentedBooleanRings.Examples.Bool
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Function

open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Bool
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation as PT

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Ring
open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Algebra.BooleanRing.Initial
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Relation.Nullary

PropositonalCompleteness : Type _
PropositonalCompleteness = (S : StoneSpace) → ¬ ¬ ⟨ S ⟩ → ∥ ⟨ S ⟩ ∥₁

module surjectionsAxiomToPropositionalCompleteness
  (SD : StoneDualityAxiom)
  (FS : formalSurjectionsAreSurjectionsAxiom)
  (B : Booleω) (SpBnonEmpty : ¬ ¬ Sp B) where
  open BooleanRingStr (snd (fst B))
  0≠1 : ¬ (𝟘 ≡ 𝟙)
  0≠1 = SpBnonEmpty ∘ TrivialImpliesSpEmpty.spEmpty B
  open IsCommRingHom (snd $ BoolBR→ (fst B))
  isInjective! : isInjectiveBoolHom BoolCP B (BoolBR→ (fst B))
  isInjective! false false = λ _ → refl
  isInjective! false true  = ex-falso ∘ 0≠1
  isInjective! true false  = ex-falso ∘ 0≠1 ∘ sym
  isInjective! true true   = λ _ → refl

  isSurjective→1 : isSurjection {A = Sp B} {B = Unit} λ _ → tt
  isSurjective→1 t = PT.map (λ s → s , isPropUnit tt t) spB
    where
      -- Sp BoolCP is the point space; FS makes  Sp B → Sp BoolCP  a surjection, so the
      -- fibre over its point (BoolBR→ BoolBR : Sp BoolCP) gives a point of Sp B.
      spB : ∥ Sp B ∥₁
      spB = PT.map fst (FS BoolCP B (BoolBR→ (fst B)) isInjective! (BoolBR→ BoolBR))

  SpBInhabited : ∥ Sp B ∥₁
  SpBInhabited = PT.map fst (isSurjective→1 tt)

FormalSurjectionsToPropositionalCompleteness : StoneDualityAxiom → formalSurjectionsAreSurjectionsAxiom → PropositonalCompleteness
FormalSurjectionsToPropositionalCompleteness SD FS (S , B , SpB=S) ¬¬S =
  subst (λ T → ∥ T ∥₁) SpB=S (SpBInhabited ¬¬SpB) where
  open surjectionsAxiomToPropositionalCompleteness SD FS B
  ¬¬SpB : ¬ ¬ Sp B
  ¬¬SpB = subst (λ T → ¬ ¬ T) (sym SpB=S) ¬¬S
