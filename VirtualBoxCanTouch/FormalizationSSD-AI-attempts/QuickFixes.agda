{-# OPTIONS --cubical --guardedness --allow-unsolved-metas #-}
module QuickFixes where
-- Idea : this was necessary but shouldn't be in any particularly file where they're used. 
open import CountablyPresentedBooleanRings.PresentedBoole
open import BooleanRing.BoolRingUnivalence
open import Cubical.Data.Sigma
open import Cubical.Foundations.HLevels

open import Cubical.Foundations.Structure
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Functions.Embedding
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv

open import Cubical.Algebra.CommRing
open import Cubical.Algebra.Monoid
open import Cubical.Algebra.Semigroup
open import Cubical.Algebra.Ring.Base
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.Group
open import Cubical.Algebra.BooleanRing


module invEquivFact {ℓ ℓ' : Level} {A : Type ℓ} {B : Type ℓ'} 
                    (f : A ≃ B ) where
  inv = fst (invEquiv f)
  knownInfo : (a : A) → (b : B) → fst f a ≡ b → inv b ≡ a
  knownInfo a b p = inv b ≡⟨ cong inv (sym p) ⟩ 
                    inv (fst f a) ≡⟨ cong (λ e → fst e a) (invEquiv-is-rinv f) ⟩ 
                    a ∎ 
  embedding : (a a' : A) → fst f a ≡ fst f a' → a ≡ a'
  embedding a a' p = a              ≡⟨ (sym $ cong (λ e → fst e a) (invEquiv-is-rinv f)) ⟩ 
                     inv (fst f a)  ≡⟨ cong inv p ⟩ 
                     inv (fst f a') ≡⟨ cong (λ e → fst e a') (invEquiv-is-rinv f) ⟩  
                     a' ∎

module 2/3 {ℓ ℓ' ℓ'' : Level} {A : Type ℓ} {B : Type ℓ'} { C : Type ℓ''} 
         (f : A → C) (g : A → B) (h : B → C) (hg≡f : h ∘ g ≡ f) where

--     f
-- A ----> C
--  \    / \
--  g\|  /h
--   _. /
--     B
--
  ghEqu : isEquiv g → isEquiv h → isEquiv f
  ghEqu gEqu hEqu = subst isEquiv hg≡f (snd (compEquiv (g , gEqu) (h , hEqu))) 

  fhEqu : isEquiv f → isEquiv h → isEquiv g
  fhEqu fEqu hEqu = subst isEquiv g'≡g (snd g'Equiv) where
    g'Equiv : A ≃ B 
    g'Equiv = compEquiv (f , fEqu)  (invEquiv (h , hEqu)) 
    hinv : C → B
    hinv = fst (invEquiv (h , hEqu)) 
    g'≡g : fst g'Equiv  ≡ g
    g'≡g = hinv ∘ f     ≡⟨ cong (λ f → hinv ∘ f) (sym hg≡f) ⟩ 
           hinv ∘ h ∘ g ≡⟨ cong (λ e → (fst e) ∘ g) (invEquiv-is-rinv (h , hEqu)) ⟩ 
           idfun B ∘ g  ≡⟨ funExt (λ _ → refl) ⟩ 
           g            ∎ 
  
  fgEqu : isEquiv f → isEquiv g → isEquiv h 
  fgEqu fEqu gEqu = subst isEquiv h'≡h (snd h'Equiv) where
    h'Equiv : B ≃ C 
    h'Equiv = compEquiv (invEquiv (g , gEqu)) (f , fEqu)  
    ginv : B → A
    ginv = fst (invEquiv (g , gEqu)) 
    h'≡h : fst h'Equiv  ≡ h
    h'≡h = f ∘     ginv ≡⟨ cong (λ f → f ∘ ginv ) (sym hg≡f) ⟩ 
           h ∘ g ∘ ginv ≡⟨ cong (λ e → h ∘ fst e) (invEquiv-is-linv (g , gEqu)) ⟩
           h ∘ idfun B  ≡⟨ funExt (λ _ → refl) ⟩
           h ∎ 

module _ {ℓ ℓ' : Level} {A : Type ℓ} (P : A → Type ℓ') (Pprop : (a : A) → isProp (P a)) where
  fstEmbedding : isEmbedding (fst :> (Σ A P → A))
  fstEmbedding _ _ = isEmbeddingFstΣProp Pprop 
  ΣpropEmbedding : Σ A P ↪ A
  ΣpropEmbedding = fst , λ _ _ → isEmbeddingFstΣProp Pprop 



module _ {ℓ ℓ' ℓ'' ℓ''' : Level} {A : Type ℓ} {B : Type ℓ'} 
        (iso : Iso A B) (AP : A → Type ℓ'') (BP : B → Type ℓ''') 
        (APprop : (a : A) → isProp (AP a)) (BPprop : (b : B) → isProp $ BP b) 
        (AP→BP : (a : A) → AP a → BP (Iso.fun iso a))
        (BP→AP : (b : B) → BP b → AP (Iso.inv iso b))
        where
  open Iso
  IsoΣ : Iso (Σ A AP) (Σ B BP) 
  IsoΣ .fun (a , ap) = fun iso a , AP→BP a ap
  IsoΣ .inv (b , bp) = inv iso b , BP→AP b bp
  IsoΣ .sec (b , bp) = Σ≡Prop BPprop (sec iso b)
  IsoΣ .ret  (a , ap) = Σ≡Prop APprop (ret  iso a) 

open import Cubical.Algebra.CommRing.Instances.Pointwise using (pointwiseRing)

-- Pointwise BooleanRing structure, factored through the library's pointwiseRing for CommRing.
-- The CommRing part comes from the library; we only add ·Idem.
pointwiseBooleanRing : {ℓ ℓ' : Level} (X : Type ℓ) (B : BooleanRing ℓ') → BooleanRing _
pointwiseBooleanRing X B = idemCommRing→BR (pointwiseRing X (BooleanRing→CommRing B))
  λ f → funExt λ x → IsBooleanRing.·Idem (BooleanRingStr.isBooleanRing (str B)) (f x)

-- Dependent pointwise BooleanRing, factored through idemCommRing→BR + makeIsCommRing.
pointWiseStructure : {ℓ ℓ' : Level} (A : Type ℓ) (B : A → Type ℓ') →
    ((a : A) → BooleanRingStr (B a)) → BooleanRingStr ((a : A) → B a)
pointWiseStructure A B f = str (idemCommRing→BR
  (_ , commringstr _ _ _ _ _ (makeIsCommRing
    (isSetΠ λ a → BooleanRingStr.is-set (f a))
    (λ x y z → funExt λ a → BooleanRingStr.+Assoc (f a) (x a) (y a) (z a))
    (λ x → funExt λ a → BooleanRingStr.+IdR (f a) (x a))
    (λ x → funExt λ a → BooleanRingStr.+InvR (f a) (x a))
    (λ x y → funExt λ a → BooleanRingStr.+Comm (f a) (x a) (y a))
    (λ x y z → funExt λ a → BooleanRingStr.·Assoc (f a) (x a) (y a) (z a))
    (λ x → funExt λ a → BooleanRingStr.·IdR (f a) (x a))
    (λ x y z → funExt λ a → BooleanRingStr.·DistR+ (f a) (x a) (y a) (z a))
    (λ x y → funExt λ a → BooleanRingStr.·Comm (f a) (x a) (y a))))
  (λ x → funExt λ a → BooleanRingStr.·Idem (f a) (x a)))

mkBooleanRingEquiv : {ℓ ℓ' : Level} → (A : BooleanRing ℓ) → (B : BooleanRing ℓ') → 
                     (f : BoolHom A B) → isEquiv (fst f) → BooleanRingEquiv A B 
mkBooleanRingEquiv _ _ (f , fHom) fequ = (f , fequ) , fHom 

EquivalentBooleanRingEquiv : {ℓ ℓ' : Level} → (A : BooleanRing ℓ) → (B : BooleanRing ℓ') → 
                             Iso (Σ[ f ∈ BoolHom A B ] (isEquiv (fst f))) (BooleanRingEquiv A B)
EquivalentBooleanRingEquiv A B .Iso.fun ((f , fHom) , fequ) = (f , fequ) , fHom
EquivalentBooleanRingEquiv A B .Iso.inv ((f , fequ) , fHom) = (f , fHom) , fequ
EquivalentBooleanRingEquiv A B .Iso.sec e = refl
EquivalentBooleanRingEquiv A B .Iso.ret  e = refl 

module _ {ℓ ℓ' : Level} (A : BooleanRing ℓ) (B : BooleanRing ℓ') (f : BoolHom A B) (fIso : isIso (fst f)) where
  private 
    fun : ⟨ A ⟩ → ⟨ B ⟩
    fun = fst f 

    inv : ⟨ B ⟩ → ⟨ A ⟩
    inv = fst fIso 
    
    sec : (b : ⟨ B ⟩) → fun (inv b) ≡ b 
    sec = fst $ snd fIso

    ret : (a : ⟨ A ⟩) → inv (fun a) ≡ a 
    ret = snd $ snd fIso

  open IsCommRingHom ⦃...⦄
  instance 
    _ = snd f
  open BooleanRingStr ⦃...⦄
  instance 
    _ = snd A 
    _ = snd B
  invIsHom : IsBoolRingHom (snd B) inv (snd A)
  invIsHom .pres0 = inv 𝟘 ≡⟨ cong inv (sym pres0) ⟩ inv (fun 𝟘)  ≡⟨ ret 𝟘 ⟩ 𝟘  ∎
  invIsHom .pres1 = inv 𝟙 ≡⟨ cong inv (sym pres1) ⟩ inv (fun 𝟙)  ≡⟨ ret 𝟙 ⟩ 𝟙  ∎
  invIsHom .pres+ a b = inv (a + b) 
                          ≡⟨ cong₂ (λ a b → inv (a + b)) (sym $ sec a) (sym $ sec b) ⟩ 
                        inv (fun (inv a) + fun (inv b)) 
                          ≡⟨ cong (λ x → inv x) (sym $ pres+ (inv a) (inv b)) ⟩ 
                        inv (fun (inv a + inv b)) 
                          ≡⟨ ret (inv a + inv b) ⟩ 
                        inv a + inv b ∎ 
  invIsHom .pres· a b = inv (a · b) 
                          ≡⟨ cong₂ (λ a b → inv (a · b)) (sym $ sec a) (sym $ sec b) ⟩ 
                        inv (fun (inv a) · fun (inv b)) 
                          ≡⟨ cong (λ x → inv x) (sym $ pres· (inv a) (inv b)) ⟩ 
                        inv (fun (inv a · inv b)) 
                          ≡⟨ ret (inv a · inv b) ⟩ 
                        inv a · inv b ∎ 
  invIsHom .pres- a = inv (- a) 
                          ≡⟨ cong (λ a → inv (- a)) (sym (sec a)) ⟩ 
                      inv (- fun (inv a))
                          ≡⟨ cong inv (sym $ pres- (inv a)) ⟩ 
                      inv (fun ( - inv a))
                          ≡⟨ ret (- inv a) ⟩ 
                      - (inv a) ∎


module _ {ℓ ℓ' ℓ'' : Level  } (A : BooleanRing ℓ)
         (B : BooleanRing ℓ') (C : BooleanRing ℓ'')
         (f : BooleanRingEquiv A B) where
  composeLWithBoolEquivIsIso : Iso (BoolHom C A) (BoolHom C B)
  composeLWithBoolEquivIsIso .Iso.fun g      = BooleanEquivToHom A B f ∘cr g
  composeLWithBoolEquivIsIso .Iso.inv g      = (BooleanEquivToHom B A $ invBooleanRingEquiv A B f) ∘cr g
  composeLWithBoolEquivIsIso .Iso.sec g = CommRingHom≡ $ funExt λ c → 
      cong (λ h → (h ∘ fst g) c) $ cong fst $ BooleanEquivRightInv A B f
  composeLWithBoolEquivIsIso .Iso.ret  g = CommRingHom≡ $ funExt λ c → 
      cong (λ h → (h ∘ fst g) c) $ cong fst $ BooleanEquivLeftInv A B f

