module NinftyExtras where
-- Local addition to StoneSpaces.Examples.Ninfty, kept here so that the
-- FormalizationSSD library can stay byte-for-byte identical to its git version
-- while this folder remains self-contained.  The only content is `neededIso`,
-- the Stone iso  Sp B∞ ≅ ℕ∞,  whose definition is commented out (and left with
-- two holes) in the library file.  Everything it uses is already exported from
-- StoneSpaces.Examples.Ninfty, which we re-export here so downstream code can
-- depend on this module alone.
--
-- LIBRARY TASK: uncomment `neededIso` in StoneSpaces/Examples/Ninfty.agda and
-- fill its two holes exactly as below (see LIBRARY_CHANGES.md).

open import StoneSpaces.Examples.Ninfty public

open import Cubical.Data.Bool hiding ( _≤_ ; _≥_ ) renaming ( _≟_ to _=B_)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma hiding (_∧_)
open import Cubical.Algebra.BooleanRing.Instances.Bool
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (_∨_ ; _∧_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)

open import Cubical.Algebra.CommRing
open import BooleanRing.BooleanRingMaps
open import BooleanRing.FreeBooleanRing.FreeBool
open import BooleanRing.BooleanRingQuotients.QuotientBool

neededIso : Iso SpB∞ ℕ∞
neededIso .Iso.fun f = Sp→BinarySequence f , SpHits1AtMostOnce f
neededIso .Iso.inv (α , α1atmostOnce) = inducedHom BoolBR (BinarySequence→SpFreeℕ α)
  λ n → hits1AtMostOnce→respectsRelations α α1atmostOnce (fst $ Iso.inv ℕ×ℕ≅ℕ n) (snd $ Iso.inv ℕ×ℕ≅ℕ n)
-- fun (inv (α , _)) ≡ (α , _): second components agree by isPropHits1AtMostOnce,
-- and on underlying sequences the induced hom satisfies
--   inv (α , _) ∘cr quotientImageHom ≡ BinarySequence→SpFreeℕ α   (evalInduce),
-- so it agrees with α on each generator (evalBAInduce).
neededIso .Iso.sec (α , α1atmostOnce) = Σ≡Prop isPropHits1AtMostOnce
  (funExt (λ n → cong (λ h → h $cr generator n) (evalInduce BoolBR)) ∙ evalBAInduce ℕ BoolBR α)
-- inv (fun f) ≡ f: a hom out of the quotient is determined by its precomposition
-- with quotientImageHom (inducedHomUnique).  That precomposition is
-- inducedBAHom ℕ BoolBR (Sp→BinarySequence f), which agrees with f ∘cr
-- quotientImageHom on generators definitionally (inducedBAHomUnique … refl).
neededIso .Iso.ret f = inducedHomUnique BoolBR _ _ f
  (inducedBAHomUnique ℕ BoolBR (Sp→BinarySequence f) (f ∘cr quotientImageHom) refl)
