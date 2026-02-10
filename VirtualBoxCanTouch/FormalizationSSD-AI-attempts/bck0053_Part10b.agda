{-# OPTIONS --cubical --guardedness #-}

module work.Part10b where

open import work.Part10 public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Structure public using (⟨_⟩)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Equiv public using (_≃_; compEquiv; equivToIso; invEquiv; isEquiv)
open import Cubical.Foundations.Univalence public using (ua)
open import Cubical.Foundations.Transport public using (transport⁻; transportTransport⁻)
open import Cubical.Foundations.Isomorphism public using (iso; isoToEquiv; Iso)
open import Cubical.Foundations.GroupoidLaws public using (lUnit; rUnit; rCancel; lCancel)
open import Cubical.Data.Sigma public
open import Cubical.Data.Nat public using (ℕ; zero; suc)
open import Cubical.Data.Fin public using (Fin)
open import Cubical.Data.Bool public using (Bool; true; false; isSetBool; true≢false; false≢true)
open import Cubical.Data.Empty public renaming (rec to ex-falso)
open import Cubical.Data.Unit public using (Unit)
open import Cubical.Data.Sum public using (_⊎_)
open import Cubical.Relation.Nullary public using (¬_)
open import Cubical.HITs.PropositionalTruncation public using (∥_∥₁; squash₁; ∣_∣₁)

open import Axioms.StoneDuality public using (Booleω; Sp)
open import Cubical.Algebra.BooleanRing public using (BoolHom; BooleanRingStr)
open import Cubical.Algebra.BooleanRing.Instances.Bool public using (BoolBR)
open import Cubical.Algebra.CommRing public using (_∘cr_)
open import CountablyPresentedBooleanRings.PresentedBoole public using (has-Boole-ω'; _is-presented-by_/_; BooleanRingEquiv; invBooleanRingEquiv; idBoolEquiv; has-Countability-structure)
