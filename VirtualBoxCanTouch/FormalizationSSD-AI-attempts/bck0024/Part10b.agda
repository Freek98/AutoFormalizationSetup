{-# OPTIONS --cubical --guardedness #-}

module work.Part10b where

open import work.Part10 public

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Structure public using (⟨_⟩)
open import Cubical.Foundations.HLevels public
open import Cubical.Foundations.Equiv public using (_≃_; compEquiv; equivToIso; invEquiv; isEquiv)
open import Cubical.Foundations.Univalence public using (ua)
open import Cubical.Foundations.Transport public using (transport⁻; transportTransport⁻)
open import Cubical.Foundations.Isomorphism public using (iso; isoToEquiv; Iso; isoToPath)
open import Cubical.Foundations.GroupoidLaws public using (lUnit; rUnit; rCancel; lCancel) renaming (assoc to ∙assoc)
open import Cubical.Data.Sigma public
open import Cubical.Data.Nat public using (ℕ; zero; suc)
open import Cubical.Data.Fin public using (Fin)
open import Cubical.Data.Bool public using (Bool; true; false; isSetBool; true≢false; false≢true)
open import Cubical.Data.Empty public renaming (rec to ex-falso)
open import Cubical.Data.Unit public using (Unit; tt)
open import Cubical.Data.Sum public using (_⊎_; inl; inr)
import Cubical.Data.Sum as ⊎
open import Cubical.Relation.Nullary public using (¬_)
open import Cubical.HITs.PropositionalTruncation public using (∥_∥₁; squash₁; ∣_∣₁)
open import Cubical.HITs.SetTruncation public using (∥_∥₂; ∣_∣₂; squash₂)

open import Axioms.StoneDuality public using (Booleω; Sp)
open import Cubical.Algebra.BooleanRing public using (BoolHom; BooleanRingStr)
open import Cubical.Algebra.BooleanRing.Instances.Bool public using (BoolBR)
open import Cubical.Algebra.CommRing public using (_∘cr_)
open import CountablyPresentedBooleanRings.PresentedBoole public using (has-Boole-ω'; _is-presented-by_/_; BooleanRingEquiv; invBooleanRingEquiv; idBoolEquiv; has-Countability-structure)

import Cubical.HITs.PropositionalTruncation as PT

module StoneAsClosedSubsetOfCantorModule2 where
  open import Axioms.StoneDuality using (Stone)
  open StoneAsClosedSubsetOfCantorModule

  ClosedSubsetWithType : Type₁
  ClosedSubsetWithType = Σ[ A ∈ ClosedSubsetOfCantor ] Type₀

  closedSubsetType : ClosedSubsetOfCantor → Type₀
  closedSubsetType (A , _) = Σ[ x ∈ CantorSpace ] fst (A x)

  ClosedSubsetOfCantor→Stone : ClosedSubsetOfCantor → Stone
  ClosedSubsetOfCantor→Stone A = closedSubsetType A , ClosedInCantor→Stone A

  Stone→ClosedWithEquiv : (S : Stone)
    → ∥ Σ[ A ∈ ClosedSubsetOfCantor ] (fst S ≃ closedSubsetType A) ∥₁
  Stone→ClosedWithEquiv = Stone→ClosedInCantor

  ClosedSubset-roundtrip : (A : ClosedSubsetOfCantor)
    → fst (ClosedSubsetOfCantor→Stone A) ≡ closedSubsetType A
  ClosedSubset-roundtrip A = refl

  ClosedSubsetIntersection : (A' B' : ClosedSubsetOfCantor) → ClosedSubsetOfCantor
  ClosedSubsetIntersection (A , Aclosed) (B , Bclosed) =
    (λ x → (fst (A x) × fst (B x)) , isProp× (snd (A x)) (snd (B x))) ,
    (λ x → closedAnd (A x) (B x) (Aclosed x) (Bclosed x))

  EmptyClosedSubset : ClosedSubsetOfCantor
  EmptyClosedSubset = (λ _ → ⊥-hProp) , (λ _ → ⊥-isClosed)

  FullClosedSubset : ClosedSubsetOfCantor
  FullClosedSubset = (λ _ → ⊤-hProp) , (λ _ → ⊤-isClosed)

  ClosedSubsetUnion : (A' B' : ClosedSubsetOfCantor) → ClosedSubsetOfCantor
  ClosedSubsetUnion (A , Aclosed) (B , Bclosed) =
    (λ x → (∥ fst (A x) ⊎ fst (B x) ∥₁) , squash₁) ,
    (λ x → closedOr (A x) (B x) (Aclosed x) (Bclosed x))

  ClosedSubsetCountableIntersection : (An : ℕ → ClosedSubsetOfCantor) → ClosedSubsetOfCantor
  ClosedSubsetCountableIntersection An =
    (λ x → ((n : ℕ) → fst (fst (An n) x)) , isPropΠ (λ n → snd (fst (An n) x))) ,
    (λ x → closedCountableIntersection (λ n → fst (An n) x) (λ n → snd (An n) x))

  CantorFullCorrespondence : fst (ClosedSubsetOfCantor→Stone FullClosedSubset) ≡ CantorSpace
  CantorFullCorrespondence = ua (isoToEquiv (iso to-cantor from-cantor to-from from-to))
    where
    to-cantor : (Σ[ x ∈ CantorSpace ] Unit) → CantorSpace
    to-cantor = fst
    from-cantor : CantorSpace → Σ[ x ∈ CantorSpace ] Unit
    from-cantor x = x , tt
    to-from : (x : CantorSpace) → to-cantor (from-cantor x) ≡ x
    to-from x = refl
    from-to : (y : Σ[ x ∈ CantorSpace ] Unit) → from-cantor (to-cantor y) ≡ y
    from-to (x , tt) = refl

  EmptyCorrespondence : closedSubsetType EmptyClosedSubset ≡ ⊥
  EmptyCorrespondence = ua (isoToEquiv (iso to-empty from-empty (λ ()) (λ ())))
    where
    to-empty : (Σ[ x ∈ CantorSpace ] ⊥) → ⊥
    to-empty (_ , bot) = bot
    from-empty : ⊥ → Σ[ x ∈ CantorSpace ] ⊥
    from-empty ()

  ClosedSubsetPreimageCantor : (f : CantorSpace → CantorSpace)
    → ClosedSubsetOfCantor → ClosedSubsetOfCantor
  ClosedSubsetPreimageCantor f (A , Aclosed) =
    (λ x → A (f x)) , (λ x → Aclosed (f x))

  OpenSubsetOfCantor : Type₁
  OpenSubsetOfCantor = Σ[ A ∈ (CantorSpace → hProp ℓ-zero) ] ((x : CantorSpace) → isOpenProp (A x))

  postulate
    isPropIsOpenProp : (P : hProp ℓ-zero) → isProp (isOpenProp P)

  ClosedSubsetComplement : ClosedSubsetOfCantor → OpenSubsetOfCantor
  ClosedSubsetComplement (A , Aclosed) =
    (λ x → ¬hProp (A x)) , (λ x → negClosedIsOpen mp (A x) (Aclosed x))

  OpenSubsetComplement : OpenSubsetOfCantor → ClosedSubsetOfCantor
  OpenSubsetComplement (A , Aopen) =
    (λ x → ¬hProp (A x)) , (λ x → negOpenIsClosed (A x) (Aopen x))

  OpenSubsetIntersection : (A' B' : OpenSubsetOfCantor) → OpenSubsetOfCantor
  OpenSubsetIntersection (A , Aopen) (B , Bopen) =
    (λ x → (fst (A x) × fst (B x)) , isProp× (snd (A x)) (snd (B x))) ,
    (λ x → openAnd (A x) (B x) (Aopen x) (Bopen x))

  OpenSubsetUnion : (A' B' : OpenSubsetOfCantor) → OpenSubsetOfCantor
  OpenSubsetUnion (A , Aopen) (B , Bopen) =
    (λ x → (∥ fst (A x) ⊎ fst (B x) ∥₁) , squash₁) ,
    (λ x → openOr (A x) (B x) (Aopen x) (Bopen x))

  EmptyOpenSubset : OpenSubsetOfCantor
  EmptyOpenSubset = (λ _ → ⊥-hProp) , (λ _ → ⊥-isOpen)

  FullOpenSubset : OpenSubsetOfCantor
  FullOpenSubset = (λ _ → ⊤-hProp) , (λ _ → ⊤-isOpen)

  OpenSubsetPreimageCantor : (f : CantorSpace → CantorSpace)
    → OpenSubsetOfCantor → OpenSubsetOfCantor
  OpenSubsetPreimageCantor f (A , Aopen) =
    (λ x → A (f x)) , (λ x → Aopen (f x))
