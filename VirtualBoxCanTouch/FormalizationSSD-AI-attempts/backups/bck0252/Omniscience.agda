{-# OPTIONS --cubical --guardedness #-}

open import formalization.StoneDuality.AxiomDefs using (FoundationalAxioms)

module formalization.StoneDuality.Omniscience (fa : FoundationalAxioms) where

open import formalization.StoneDuality.FinCofinAlgebra fa public

open import Cubical.Algebra.BooleanRing
open import Cubical.Algebra.CommRing
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

-- char2 lemmas (trivial from Boolean ring structure)
char2-B∞ : (x : ⟨ B∞ ⟩) → x +∞ x ≡ 𝟘∞
char2-B∞ x = BooleanAlgebraStr.characteristic2 (snd B∞) {x}

char2-B∞×B∞ : (z : ⟨ B∞×B∞ ⟩) → z +× z ≡ (𝟘∞ , 𝟘∞)
char2-B∞×B∞ (a , b) = cong₂ _,_ (char2-B∞ a) (char2-B∞ b)

-- Import the B∞ ≅ ℕfinCofinBA isomorphism from the Bridge module
import formalization.StoneDuality.NFinCofin.Bridge fa as Bridge
import formalization.StoneDuality.NFinCofin.Definitions as NFC
import formalization.StoneDuality.NFinCofin.Presentation as Pres
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat renaming (_+_ to _+ℕ_ ; _·_ to _·ℕ_)
open import Cubical.Data.Bool using (Bool; true; false; _⊕_; _and_; _or_; not; true≢false; false≢true)
open import Cubical.Relation.Nullary using (¬_; Dec; yes; no)
import formalization.Library.QuotientBool as QB
open import formalization.Library.BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator; inducedBAHom; evalBAInduce; inducedBAHomUnique)
open import formalization.Library.CountablyPresentedBooleanRings.PresentedBoole using (BooleanRingEquiv; has-Boole-ω')
open import formalization.Library.Axioms.StoneDuality using (Booleω; Sp)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; rec)
open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
import Cubical.Data.Sum as ⊎
open import Cubical.Data.Sum using (_⊎_; inl; inr)
open import Cubical.Foundations.Isomorphism using (Iso; iso; isoToIsEquiv; isoFunInjective; isoInvInjective)
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Nat.Bijections.Sum using (ℕ⊎ℕ≅ℕ)
open import Cubical.Functions.Embedding using (isEmbedding→Inj)
open import Cubical.Data.Sum.Properties using (isEmbedding-inl; isEmbedding-inr)
open import Cubical.Data.List using (List; []; _∷_; _++_; ¬cons≡nil)

module B∞×B∞-Units where
  unit-left : ⟨ B∞×B∞ ⟩
  unit-left = (𝟙∞ , 𝟘∞)

  unit-right : ⟨ B∞×B∞ ⟩
  unit-right = (𝟘∞ , 𝟙∞)

open B∞×B∞-Units

module B∞×B∞-Presentation where
  open Iso
  open BooleanRingStr (snd (freeBA ℕ)) using (𝟙) renaming (_·_ to _·f_ ; _+_ to _+f_)
  encode× : ℕ ⊎ ℕ → ℕ
  encode× = fun ℕ⊎ℕ≅ℕ

  decode× : ℕ → ℕ ⊎ ℕ
  decode× = inv ℕ⊎ℕ≅ℕ

  decode×∘encode× : (x : ℕ ⊎ ℕ) → decode× (encode× x) ≡ x
  decode×∘encode× = ret ℕ⊎ℕ≅ℕ

  genProd⊎ : ℕ ⊎ ℕ → ⟨ B∞×B∞ ⟩
  genProd⊎ (⊎.inl n) = (g∞ n , 𝟘∞)
  genProd⊎ (⊎.inr n) = (𝟘∞ , g∞ n)

  prodGenMap : ℕ → ⟨ B∞×B∞ ⟩
  prodGenMap 0 = unit-left
  prodGenMap (suc n) = genProd⊎ (decode× n)

  prodGenMap-on-left : (m : ℕ) → prodGenMap (suc (encode× (⊎.inl m))) ≡ (g∞ m , 𝟘∞)
  prodGenMap-on-left m = cong genProd⊎ (decode×∘encode× (⊎.inl m))

  prodGenMap-on-right : (n : ℕ) → prodGenMap (suc (encode× (⊎.inr n))) ≡ (𝟘∞ , g∞ n)
  prodGenMap-on-right n = cong genProd⊎ (decode×∘encode× (⊎.inr n))

  prodRelAB : ℕ ⊎ ℕ → ⟨ freeBA ℕ ⟩
  prodRelAB (⊎.inl n) = gen 0 ·f gen (suc (encode× (⊎.inr n)))
  prodRelAB (⊎.inr m) = gen (suc (encode× (⊎.inl m))) ·f (𝟙 +f gen 0)

  prodRelFromPair : ℕ × ℕ → ⟨ freeBA ℕ ⟩
  prodRelFromPair (i , d) = gen (suc i) ·f gen (suc (i +ℕ suc d))

  prodRelOuter : ℕ ⊎ ℕ → ⟨ freeBA ℕ ⟩
  prodRelOuter (⊎.inl ab) = prodRelAB (decode× ab)
  prodRelOuter (⊎.inr p) = prodRelFromPair (cantorUnpair p)

  prodRel : ℕ → ⟨ freeBA ℕ ⟩
  prodRel k = prodRelOuter (decode× k)

  B∞×B∞-Q : BooleanRing ℓ-zero
  B∞×B∞-Q = freeBA ℕ QB./Im prodRel

  πQ : BoolHom (freeBA ℕ) B∞×B∞-Q
  πQ = QB.quotientImageHom

  prodGenMap-free : BoolHom (freeBA ℕ) B∞×B∞
  prodGenMap-free = inducedBAHom ℕ B∞×B∞ prodGenMap

  prodGenMap-free-eval : fst prodGenMap-free ∘ generator ≡ prodGenMap
  prodGenMap-free-eval = evalBAInduce ℕ B∞×B∞ prodGenMap

  private
    genProd⊎-orthog : (x y : ℕ ⊎ ℕ) → ¬ (x ≡ y) → genProd⊎ x ·× genProd⊎ y ≡ (𝟘∞ , 𝟘∞)
    genProd⊎-orthog (⊎.inl m) (⊎.inl n) m≠n =
      cong₂ _,_ (g∞-distinct-mult-zero m n (λ eq → m≠n (cong ⊎.inl eq)))
                 (0∞-absorbs-left 𝟘∞)
    genProd⊎-orthog (⊎.inl m) (⊎.inr n) _ = inl-inr-mult-zero (g∞ m) (g∞ n)
    genProd⊎-orthog (⊎.inr m) (⊎.inl n) _ = inr-inl-mult-zero (g∞ m) (g∞ n)
    genProd⊎-orthog (⊎.inr m) (⊎.inr n) m≠n =
      cong₂ _,_ (0∞-absorbs-left 𝟘∞)
                 (g∞-distinct-mult-zero m n (λ eq → m≠n (cong ⊎.inr eq)))

    suc-gen-orthog : (i j : ℕ) → ¬ (i ≡ j) → genProd⊎ (decode× i) ·× genProd⊎ (decode× j) ≡ (𝟘∞ , 𝟘∞)
    suc-gen-orthog i j i≠j = genProd⊎-orthog (decode× i) (decode× j) (i≠j ∘ isoInvInjective ℕ⊎ℕ≅ℕ i j)

  prodGenMap-respects-rel : (k : ℕ) → fst prodGenMap-free (prodRel k) ≡ (𝟘∞ , 𝟘∞)
  prodGenMap-respects-rel k with decode× k
  ... | ⊎.inl ab with decode× ab
  ...   | ⊎.inl n =
    fst prodGenMap-free (gen 0 ·f gen (suc (encode× (⊎.inr n))))
      ≡⟨ IsCommRingHom.pres· (snd prodGenMap-free) (gen 0) (gen (suc (encode× (⊎.inr n)))) ⟩
    fst prodGenMap-free (gen 0) ·× fst prodGenMap-free (gen (suc (encode× (⊎.inr n))))
      ≡⟨ cong₂ _·×_ (funExt⁻ prodGenMap-free-eval 0) (funExt⁻ prodGenMap-free-eval (suc (encode× (⊎.inr n)))) ⟩
    unit-left ·× prodGenMap (suc (encode× (⊎.inr n)))
      ≡⟨ cong (unit-left ·×_) (prodGenMap-on-right n) ⟩
    unit-left ·× (𝟘∞ , g∞ n)
      ≡⟨ cong₂ _,_ (0∞-absorbs-right 𝟙∞) (0∞-absorbs-left (g∞ n)) ⟩
    (𝟘∞ , 𝟘∞) ∎
  ...   | ⊎.inr m =
    fst prodGenMap-free (gen (suc (encode× (⊎.inl m))) ·f (𝟙 +f gen 0))
      ≡⟨ IsCommRingHom.pres· (snd prodGenMap-free) (gen (suc (encode× (⊎.inl m)))) (𝟙 +f gen 0) ⟩
    fst prodGenMap-free (gen (suc (encode× (⊎.inl m)))) ·× fst prodGenMap-free (𝟙 +f gen 0)
      ≡⟨ cong₂ _·×_
           (funExt⁻ prodGenMap-free-eval (suc (encode× (⊎.inl m))))
           (IsCommRingHom.pres+ (snd prodGenMap-free) 𝟙 (gen 0)
            ∙ cong₂ _+×_ (IsCommRingHom.pres1 (snd prodGenMap-free)) (funExt⁻ prodGenMap-free-eval 0)) ⟩
    prodGenMap (suc (encode× (⊎.inl m))) ·× ((𝟙∞ , 𝟙∞) +× unit-left)
      ≡⟨ cong₂ _·×_ (prodGenMap-on-left m) refl ⟩
    (g∞ m , 𝟘∞) ·× ((𝟙∞ , 𝟙∞) +× (𝟙∞ , 𝟘∞))
      ≡⟨ cong ((g∞ m , 𝟘∞) ·×_) (cong₂ _,_ (char2-B∞ 𝟙∞) (BooleanRingStr.+IdR (snd B∞) 𝟙∞)) ⟩
    (g∞ m , 𝟘∞) ·× (𝟘∞ , 𝟙∞)
      ≡⟨ inl-inr-mult-zero (g∞ m) 𝟙∞ ⟩
    (𝟘∞ , 𝟘∞) ∎
  prodGenMap-respects-rel k | ⊎.inr p =
    let (i , d) = cantorUnpair p
        i≠i+sd : ¬ (i ≡ i +ℕ suc d)
        i≠i+sd = a≠a+suc-d i d
    in fst prodGenMap-free (gen (suc i) ·f gen (suc (i +ℕ suc d)))
         ≡⟨ IsCommRingHom.pres· (snd prodGenMap-free) (gen (suc i)) (gen (suc (i +ℕ suc d))) ⟩
       fst prodGenMap-free (gen (suc i)) ·× fst prodGenMap-free (gen (suc (i +ℕ suc d)))
         ≡⟨ cong₂ _·×_ (funExt⁻ prodGenMap-free-eval (suc i))
                        (funExt⁻ prodGenMap-free-eval (suc (i +ℕ suc d))) ⟩
       genProd⊎ (decode× i) ·× genProd⊎ (decode× (i +ℕ suc d))
         ≡⟨ suc-gen-orthog i (i +ℕ suc d) i≠i+sd ⟩
       (𝟘∞ , 𝟘∞) ∎

  φQ : BoolHom B∞×B∞-Q B∞×B∞
  φQ = QB.inducedHom B∞×B∞ prodGenMap-free prodGenMap-respects-rel

  prodRel-encodes-C : (i d : ℕ) →
    prodRel (encode× (⊎.inr (cantorPair i d))) ≡ gen (suc i) ·f gen (suc (i +ℕ suc d))
  prodRel-encodes-C i d =
    prodRel (encode× (⊎.inr (cantorPair i d)))
      ≡⟨ cong prodRelOuter (decode×∘encode× (⊎.inr (cantorPair i d))) ⟩
    prodRelFromPair (cantorUnpair (cantorPair i d))
      ≡⟨ cong prodRelFromPair (cantorUnpair-pair i d) ⟩
    gen (suc i) ·f gen (suc (i +ℕ suc d)) ∎

  private
    𝟘Q = BooleanRingStr.𝟘 (snd B∞×B∞-Q)
    infixl 7 _·Q_
    infixl 6 _+Q_
    _·Q_ = BooleanRingStr._·_ (snd B∞×B∞-Q)
    _+Q_ = BooleanRingStr._+_ (snd B∞×B∞-Q)
    encode×-inj : (x y : ℕ ⊎ ℕ) → encode× x ≡ encode× y → x ≡ y
    encode×-inj = isoFunInjective ℕ⊎ℕ≅ℕ

    ≠-diff : (a b : ℕ) → ¬(a ≡ b) → (Σ[ d ∈ ℕ ] b ≡ a +ℕ suc d) ⊎ (Σ[ d ∈ ℕ ] a ≡ b +ℕ suc d)
    ≠-diff zero zero neq = ex-falso (neq refl)
    ≠-diff zero (suc b) _ = ⊎.inl (b , refl)
    ≠-diff (suc a) zero _ = ⊎.inr (a , refl)
    ≠-diff (suc a) (suc b) neq with ≠-diff a b (λ p → neq (cong suc p))
    ... | ⊎.inl r = ⊎.inl (fst r , cong suc (snd r))
    ... | ⊎.inr r = ⊎.inr (fst r , cong suc (snd r))

  πQ-kills-type-C : (i d : ℕ) → fst πQ (gen (suc i) ·f gen (suc (i +ℕ suc d))) ≡ 𝟘Q
  πQ-kills-type-C i d = subst (λ x → fst πQ x ≡ 𝟘Q)
    (prodRel-encodes-C i d)
    (QB.zeroOnImage {B = freeBA ℕ} {f = prodRel} (encode× (⊎.inr (cantorPair i d))))

  πQ-suc-gens-zero : (a b : ℕ) → ¬(a ≡ b) →
    fst πQ (gen (suc a)) ·Q fst πQ (gen (suc b)) ≡ 𝟘Q
  πQ-suc-gens-zero a b neq =
    fst πQ (gen (suc a)) ·Q fst πQ (gen (suc b))
      ≡⟨ sym (IsCommRingHom.pres· (snd πQ) (gen (suc a)) (gen (suc b))) ⟩
    fst πQ (gen (suc a) ·f gen (suc b))
      ≡⟨ go ⟩
    𝟘Q ∎
    where
    go : fst πQ (gen (suc a) ·f gen (suc b)) ≡ 𝟘Q
    go with ≠-diff a b neq
    ... | ⊎.inl r =
      fst πQ (gen (suc a) ·f gen (suc b))
        ≡⟨ cong (λ x → fst πQ (gen (suc a) ·f gen (suc x))) (snd r) ⟩
      fst πQ (gen (suc a) ·f gen (suc (a +ℕ suc (fst r))))
        ≡⟨ πQ-kills-type-C a (fst r) ⟩
      𝟘Q ∎
    ... | ⊎.inr r =
      fst πQ (gen (suc a) ·f gen (suc b))
        ≡⟨ cong (fst πQ) (BooleanRingStr.·Comm (snd (freeBA ℕ)) (gen (suc a)) (gen (suc b))) ⟩
      fst πQ (gen (suc b) ·f gen (suc a))
        ≡⟨ cong (λ x → fst πQ (gen (suc b) ·f gen (suc x))) (snd r) ⟩
      fst πQ (gen (suc b) ·f gen (suc (b +ℕ suc (fst r))))
        ≡⟨ πQ-kills-type-C b (fst r) ⟩
      𝟘Q ∎

  genL : ℕ → ⟨ B∞×B∞-Q ⟩
  genL n = fst πQ (gen (suc (encode× (⊎.inl n))))

  genL-free : BoolHom (freeBA ℕ) B∞×B∞-Q
  genL-free = inducedBAHom ℕ B∞×B∞-Q genL

  genL-free-eval : fst genL-free ∘ generator ≡ genL
  genL-free-eval = evalBAInduce ℕ B∞×B∞-Q genL

  genL-respects-relB∞ : (k : ℕ) → fst genL-free (relB∞ k) ≡ 𝟘Q
  genL-respects-relB∞ k =
    let (a , d) = cantorUnpair k
    in fst genL-free (gen a · gen (a +ℕ suc d))
      ≡⟨ IsCommRingHom.pres· (snd genL-free) (gen a) (gen (a +ℕ suc d)) ⟩
    fst genL-free (gen a) ·Q fst genL-free (gen (a +ℕ suc d))
      ≡⟨ cong₂ _·Q_ (funExt⁻ genL-free-eval a) (funExt⁻ genL-free-eval (a +ℕ suc d)) ⟩
    genL a ·Q genL (a +ℕ suc d)
      ≡⟨ πQ-suc-gens-zero (encode× (⊎.inl a)) (encode× (⊎.inl (a +ℕ suc d)))
          (λ eq → a≠a+suc-d a d (isEmbedding→Inj isEmbedding-inl a (a +ℕ suc d) (encode×-inj _ _ eq))) ⟩
    𝟘Q ∎

  ψL : BoolHom B∞ B∞×B∞-Q
  ψL = QB.inducedHom B∞×B∞-Q genL-free genL-respects-relB∞

  genR : ℕ → ⟨ B∞×B∞-Q ⟩
  genR n = fst πQ (gen (suc (encode× (⊎.inr n))))

  genR-free : BoolHom (freeBA ℕ) B∞×B∞-Q
  genR-free = inducedBAHom ℕ B∞×B∞-Q genR

  genR-free-eval : fst genR-free ∘ generator ≡ genR
  genR-free-eval = evalBAInduce ℕ B∞×B∞-Q genR

  genR-respects-relB∞ : (k : ℕ) → fst genR-free (relB∞ k) ≡ 𝟘Q
  genR-respects-relB∞ k =
    let (a , d) = cantorUnpair k
    in fst genR-free (gen a · gen (a +ℕ suc d))
      ≡⟨ IsCommRingHom.pres· (snd genR-free) (gen a) (gen (a +ℕ suc d)) ⟩
    fst genR-free (gen a) ·Q fst genR-free (gen (a +ℕ suc d))
      ≡⟨ cong₂ _·Q_ (funExt⁻ genR-free-eval a) (funExt⁻ genR-free-eval (a +ℕ suc d)) ⟩
    genR a ·Q genR (a +ℕ suc d)
      ≡⟨ πQ-suc-gens-zero (encode× (⊎.inr a)) (encode× (⊎.inr (a +ℕ suc d)))
          (λ eq → a≠a+suc-d a d (isEmbedding→Inj isEmbedding-inr a (a +ℕ suc d) (encode×-inj _ _ eq))) ⟩
    𝟘Q ∎

  ψR : BoolHom B∞ B∞×B∞-Q
  ψR = QB.inducedHom B∞×B∞-Q genR-free genR-respects-relB∞

  opaque
    unfolding QB.inducedHom
    unfolding QB.quotientImageHom
    ψL-eval : ψL ∘cr π∞ ≡ genL-free
    ψL-eval = QB.evalInduce {B = freeBA ℕ} {f = relB∞} B∞×B∞-Q

    ψR-eval : ψR ∘cr π∞ ≡ genR-free
    ψR-eval = QB.evalInduce {B = freeBA ℕ} {f = relB∞} B∞×B∞-Q

    φQ-eval : φQ ∘cr πQ ≡ prodGenMap-free
    φQ-eval = QB.evalInduce {B = freeBA ℕ} {f = prodRel} B∞×B∞

  eQ : ⟨ B∞×B∞-Q ⟩
  eQ = fst πQ (gen 0)

  private
    𝟙Q = BooleanRingStr.𝟙 (snd B∞×B∞-Q)
    eQ' : ⟨ B∞×B∞-Q ⟩
    eQ' = 𝟙Q +Q eQ

  ψ-fun : ⟨ B∞×B∞ ⟩ → ⟨ B∞×B∞-Q ⟩
  ψ-fun (a , b) = (eQ ·Q fst ψL a) +Q (eQ' ·Q fst ψR b)

  private
    open BooleanRingStr (snd B∞×B∞-Q) using ()
      renaming (·Idem to ·IdemQ ; ·Comm to ·CommQ ; ·Assoc to ·AssocQ ;
                +Assoc to +AssocQ ; +Comm to +CommQ ;
                ·DistR+ to ·DistR+Q ; ·DistL+ to ·DistL+Q ;
                ·IdR to ·IdRQ ; ·IdL to ·IdLQ ;
                +IdR to +IdRQ ; +IdL to +IdLQ ;
                +InvR to +InvRQ)
    open BooleanAlgebraStr (snd B∞×B∞-Q) using ()
      renaming (∧AnnihilR to AnnihilRQ ; ∧AnnihilL to AnnihilLQ ;
                characteristic2 to char2Q)
    _+B_ = BooleanRingStr._+_ (snd B∞)
    _·B_ = BooleanRingStr._·_ (snd B∞)

    eQ·eQ' : eQ ·Q eQ' ≡ 𝟘Q
    eQ·eQ' =
      eQ ·Q (𝟙Q +Q eQ)
        ≡⟨ ·DistR+Q eQ 𝟙Q eQ ⟩
      (eQ ·Q 𝟙Q) +Q (eQ ·Q eQ)
        ≡⟨ cong₂ _+Q_ (·IdRQ eQ) (·IdemQ eQ) ⟩
      eQ +Q eQ
        ≡⟨ char2Q ⟩
      𝟘Q ∎

    eQ'·eQ : eQ' ·Q eQ ≡ 𝟘Q
    eQ'·eQ =
      eQ' ·Q eQ
        ≡⟨ ·CommQ eQ' eQ ⟩
      eQ ·Q eQ'
        ≡⟨ eQ·eQ' ⟩
      𝟘Q ∎

    eQ'-idem : eQ' ·Q eQ' ≡ eQ'
    eQ'-idem =
      (𝟙Q +Q eQ) ·Q (𝟙Q +Q eQ)
        ≡⟨ ·DistR+Q (𝟙Q +Q eQ) 𝟙Q eQ ⟩
      ((𝟙Q +Q eQ) ·Q 𝟙Q) +Q ((𝟙Q +Q eQ) ·Q eQ)
        ≡⟨ cong₂ _+Q_ (·IdRQ (𝟙Q +Q eQ)) eQ'·eQ ⟩
      (𝟙Q +Q eQ) +Q 𝟘Q
        ≡⟨ +IdRQ (𝟙Q +Q eQ) ⟩
      𝟙Q +Q eQ ∎

  ψ-hom : IsCommRingHom (BooleanRingStr→CommRingStr (snd B∞×B∞))
                         ψ-fun
                         (BooleanRingStr→CommRingStr (snd B∞×B∞-Q))
  IsCommRingHom.pres0 ψ-hom =
    eQ ·Q fst ψL 𝟘∞ +Q eQ' ·Q fst ψR 𝟘∞
      ≡⟨ cong₂ (λ x y → eQ ·Q x +Q eQ' ·Q y)
           (IsCommRingHom.pres0 (snd ψL)) (IsCommRingHom.pres0 (snd ψR)) ⟩
    eQ ·Q 𝟘Q +Q eQ' ·Q 𝟘Q
      ≡⟨ cong₂ _+Q_ AnnihilRQ AnnihilRQ ⟩
    𝟘Q +Q 𝟘Q
      ≡⟨ +IdLQ 𝟘Q ⟩
    𝟘Q ∎
  IsCommRingHom.pres1 ψ-hom =
    (eQ ·Q fst ψL 𝟙∞) +Q (eQ' ·Q fst ψR 𝟙∞)
      ≡⟨ cong₂ (λ x y → (eQ ·Q x) +Q (eQ' ·Q y))
           (IsCommRingHom.pres1 (snd ψL)) (IsCommRingHom.pres1 (snd ψR)) ⟩
    (eQ ·Q 𝟙Q) +Q (eQ' ·Q 𝟙Q)
      ≡⟨ cong₂ _+Q_ (·IdRQ eQ) (·IdRQ eQ') ⟩
    eQ +Q (𝟙Q +Q eQ)
      ≡⟨ +AssocQ eQ 𝟙Q eQ ⟩
    (eQ +Q 𝟙Q) +Q eQ
      ≡⟨ cong (_+Q eQ) (+CommQ eQ 𝟙Q) ⟩
    (𝟙Q +Q eQ) +Q eQ
      ≡⟨ sym (+AssocQ 𝟙Q eQ eQ) ⟩
    𝟙Q +Q (eQ +Q eQ)
      ≡⟨ cong (𝟙Q +Q_) char2Q ⟩
    𝟙Q +Q 𝟘Q
      ≡⟨ +IdRQ 𝟙Q ⟩
    𝟙Q ∎
  IsCommRingHom.pres+ ψ-hom (a₁ , b₁) (a₂ , b₂) =
    eQ ·Q fst ψL (a₁ +B a₂) +Q eQ' ·Q fst ψR (b₁ +B b₂)
      ≡⟨ cong₂ (λ x y → eQ ·Q x +Q eQ' ·Q y)
           (IsCommRingHom.pres+ (snd ψL) a₁ a₂) (IsCommRingHom.pres+ (snd ψR) b₁ b₂) ⟩
    eQ ·Q (fst ψL a₁ +Q fst ψL a₂) +Q eQ' ·Q (fst ψR b₁ +Q fst ψR b₂)
      ≡⟨ cong₂ _+Q_ (·DistR+Q eQ (fst ψL a₁) (fst ψL a₂))
                      (·DistR+Q eQ' (fst ψR b₁) (fst ψR b₂)) ⟩
    (eQ ·Q fst ψL a₁ +Q eQ ·Q fst ψL a₂) +Q (eQ' ·Q fst ψR b₁ +Q eQ' ·Q fst ψR b₂)
      ≡⟨ +4-swap (eQ ·Q fst ψL a₁) (eQ ·Q fst ψL a₂) (eQ' ·Q fst ψR b₁) (eQ' ·Q fst ψR b₂) ⟩
    (eQ ·Q fst ψL a₁ +Q eQ' ·Q fst ψR b₁) +Q (eQ ·Q fst ψL a₂ +Q eQ' ·Q fst ψR b₂) ∎
    where
    +4-swap : (a b c d : ⟨ B∞×B∞-Q ⟩) → (a +Q b) +Q (c +Q d) ≡ (a +Q c) +Q (b +Q d)
    +4-swap a b c d =
      (a +Q b) +Q (c +Q d)
        ≡⟨ sym (+AssocQ a b (c +Q d)) ⟩
      a +Q (b +Q (c +Q d))
        ≡⟨ cong (a +Q_) (+AssocQ b c d) ⟩
      a +Q ((b +Q c) +Q d)
        ≡⟨ cong (λ x → a +Q (x +Q d)) (+CommQ b c) ⟩
      a +Q ((c +Q b) +Q d)
        ≡⟨ cong (a +Q_) (sym (+AssocQ c b d)) ⟩
      a +Q (c +Q (b +Q d))
        ≡⟨ +AssocQ a c (b +Q d) ⟩
      (a +Q c) +Q (b +Q d) ∎
  IsCommRingHom.pres- ψ-hom (a , b) =
    cong ψ-fun (sym (BooleanAlgebraStr.-IsId (snd B∞×B∞))) ∙ BooleanAlgebraStr.-IsId (snd B∞×B∞-Q)
  IsCommRingHom.pres· ψ-hom (a₁ , b₁) (a₂ , b₂) =
    eQ ·Q fst ψL (a₁ ·B a₂) +Q eQ' ·Q fst ψR (b₁ ·B b₂)
      ≡⟨ cong₂ (λ x y → eQ ·Q x +Q eQ' ·Q y)
           (IsCommRingHom.pres· (snd ψL) a₁ a₂) (IsCommRingHom.pres· (snd ψR) b₁ b₂) ⟩
    eQ ·Q (fst ψL a₁ ·Q fst ψL a₂) +Q eQ' ·Q (fst ψR b₁ ·Q fst ψR b₂)
      ≡⟨ sym (pres·-expand (fst ψL a₁) (fst ψL a₂) (fst ψR b₁) (fst ψR b₂)) ⟩
    (eQ ·Q fst ψL a₁ +Q eQ' ·Q fst ψR b₁) ·Q (eQ ·Q fst ψL a₂ +Q eQ' ·Q fst ψR b₂) ∎
    where
    pres·-expand : (x₁ x₂ y₁ y₂ : ⟨ B∞×B∞-Q ⟩) →
      (eQ ·Q x₁ +Q eQ' ·Q y₁) ·Q (eQ ·Q x₂ +Q eQ' ·Q y₂) ≡
      eQ ·Q (x₁ ·Q x₂) +Q eQ' ·Q (y₁ ·Q y₂)
    pres·-expand x₁ x₂ y₁ y₂ =
      (eQ ·Q x₁ +Q eQ' ·Q y₁) ·Q (eQ ·Q x₂ +Q eQ' ·Q y₂)
        ≡⟨ ·DistL+Q (eQ ·Q x₁) (eQ' ·Q y₁) (eQ ·Q x₂ +Q eQ' ·Q y₂) ⟩
      (eQ ·Q x₁) ·Q (eQ ·Q x₂ +Q eQ' ·Q y₂) +Q (eQ' ·Q y₁) ·Q (eQ ·Q x₂ +Q eQ' ·Q y₂)
        ≡⟨ cong₂ _+Q_
             (·DistR+Q (eQ ·Q x₁) (eQ ·Q x₂) (eQ' ·Q y₂))
             (·DistR+Q (eQ' ·Q y₁) (eQ ·Q x₂) (eQ' ·Q y₂)) ⟩
      ((eQ ·Q x₁) ·Q (eQ ·Q x₂) +Q (eQ ·Q x₁) ·Q (eQ' ·Q y₂)) +Q
      ((eQ' ·Q y₁) ·Q (eQ ·Q x₂) +Q (eQ' ·Q y₁) ·Q (eQ' ·Q y₂))
        ≡⟨ cong₂ (λ p q → (p +Q (eQ ·Q x₁) ·Q (eQ' ·Q y₂)) +Q
                           ((eQ' ·Q y₁) ·Q (eQ ·Q x₂) +Q q))
             (reassoc-4 eQ x₁ eQ x₂ (·IdemQ eQ))
             (reassoc-4 eQ' y₁ eQ' y₂ (eQ'-idem)) ⟩
      (eQ ·Q (x₁ ·Q x₂) +Q cross1) +Q (cross2 +Q eQ' ·Q (y₁ ·Q y₂))
        ≡⟨ cong₂ (λ p q → (eQ ·Q (x₁ ·Q x₂) +Q p) +Q (q +Q eQ' ·Q (y₁ ·Q y₂)))
             (cross-annihil x₁ y₂) (·CommQ (eQ' ·Q y₁) (eQ ·Q x₂) ∙ cross-annihil x₂ y₁) ⟩
      (eQ ·Q (x₁ ·Q x₂) +Q 𝟘Q) +Q (𝟘Q +Q eQ' ·Q (y₁ ·Q y₂))
        ≡⟨ cong₂ _+Q_ (+IdRQ (eQ ·Q (x₁ ·Q x₂))) (+IdLQ (eQ' ·Q (y₁ ·Q y₂))) ⟩
      eQ ·Q (x₁ ·Q x₂) +Q eQ' ·Q (y₁ ·Q y₂) ∎
      where
      cross1 = (eQ ·Q x₁) ·Q (eQ' ·Q y₂)
      cross2 = (eQ' ·Q y₁) ·Q (eQ ·Q x₂)
      reassoc-4 : (e a f b : ⟨ B∞×B∞-Q ⟩) → e ·Q f ≡ e →
        (e ·Q a) ·Q (f ·Q b) ≡ e ·Q (a ·Q b)
      reassoc-4 e a f b ef=e =
        (e ·Q a) ·Q (f ·Q b)
          ≡⟨ ·AssocQ (e ·Q a) f b ⟩
        ((e ·Q a) ·Q f) ·Q b
          ≡⟨ cong (_·Q b) (sym (·AssocQ e a f)) ⟩
        (e ·Q (a ·Q f)) ·Q b
          ≡⟨ cong (λ z → (e ·Q z) ·Q b) (·CommQ a f) ⟩
        (e ·Q (f ·Q a)) ·Q b
          ≡⟨ cong (_·Q b) (·AssocQ e f a) ⟩
        ((e ·Q f) ·Q a) ·Q b
          ≡⟨ cong (λ z → (z ·Q a) ·Q b) ef=e ⟩
        (e ·Q a) ·Q b
          ≡⟨ sym (·AssocQ e a b) ⟩
        e ·Q (a ·Q b) ∎
      cross-annihil : (a b : ⟨ B∞×B∞-Q ⟩) → (eQ ·Q a) ·Q (eQ' ·Q b) ≡ 𝟘Q
      cross-annihil a b =
        (eQ ·Q a) ·Q (eQ' ·Q b)
          ≡⟨ ·AssocQ (eQ ·Q a) eQ' b ⟩
        ((eQ ·Q a) ·Q eQ') ·Q b
          ≡⟨ cong (_·Q b) (sym (·AssocQ eQ a eQ')) ⟩
        (eQ ·Q (a ·Q eQ')) ·Q b
          ≡⟨ cong (λ z → (eQ ·Q z) ·Q b) (·CommQ a eQ') ⟩
        (eQ ·Q (eQ' ·Q a)) ·Q b
          ≡⟨ cong (_·Q b) (·AssocQ eQ eQ' a) ⟩
        ((eQ ·Q eQ') ·Q a) ·Q b
          ≡⟨ cong (λ z → (z ·Q a) ·Q b) eQ·eQ' ⟩
        (𝟘Q ·Q a) ·Q b
          ≡⟨ cong (_·Q b) AnnihilLQ ⟩
        𝟘Q ·Q b
          ≡⟨ AnnihilLQ ⟩
        𝟘Q ∎

  ψ : BoolHom B∞×B∞ B∞×B∞-Q
  ψ = ψ-fun , ψ-hom

  private

    opaque
      unfolding QB.inducedHom
      unfolding QB.quotientImageHom
      φQ-πQ-gen : (k : ℕ) → fst φQ (fst πQ (gen k)) ≡ prodGenMap k
      φQ-πQ-gen k =
        fst φQ (fst πQ (gen k))
          ≡⟨ funExt⁻ (cong fst φQ-eval) (gen k) ⟩
        fst prodGenMap-free (gen k)
          ≡⟨ funExt⁻ prodGenMap-free-eval k ⟩
        prodGenMap k ∎

      φQ-on-eQ : fst φQ eQ ≡ unit-left
      φQ-on-eQ = φQ-πQ-gen 0

      ψL-gen : (n : ℕ) → fst ψL (g∞ n) ≡ fst πQ (gen (suc (encode× (⊎.inl n))))
      ψL-gen n =
        fst ψL (g∞ n)
          ≡⟨ funExt⁻ (cong fst ψL-eval) (gen n) ⟩
        fst genL-free (gen n)
          ≡⟨ funExt⁻ genL-free-eval n ⟩
        fst πQ (gen (suc (encode× (⊎.inl n)))) ∎

      ψR-gen : (n : ℕ) → fst ψR (g∞ n) ≡ fst πQ (gen (suc (encode× (⊎.inr n))))
      ψR-gen n =
        fst ψR (g∞ n)
          ≡⟨ funExt⁻ (cong fst ψR-eval) (gen n) ⟩
        fst genR-free (gen n)
          ≡⟨ funExt⁻ genR-free-eval n ⟩
        fst πQ (gen (suc (encode× (⊎.inr n)))) ∎

    𝟙B = BooleanRingStr.𝟙 (snd B∞)
    unit-decompose : (x y : ⟨ B∞×B∞ ⟩) → (unit-left ·×' x) +× (((𝟙B , 𝟙B) +× unit-left) ·×' y) ≡ (fst x , snd y)
    unit-decompose (xa , xb) (ya , yb) =
      cong₂ _,_
        ((𝟙B ·B xa) +B ((𝟙B +B 𝟙B) ·B ya)
          ≡⟨ cong₂ _+B_ (BooleanRingStr.·IdL (snd B∞) xa) (cong (_·B ya) (char2-B∞ 𝟙B) ∙ 0∞-absorbs-left ya) ⟩
        xa +B 𝟘∞
          ≡⟨ BooleanRingStr.+IdR (snd B∞) xa ⟩
        xa ∎)
        ((𝟘∞ ·B xb) +B ((𝟙B +B 𝟘∞) ·B yb)
          ≡⟨ cong₂ _+B_ (0∞-absorbs-left xb) (cong (_·B yb) (BooleanRingStr.+IdR (snd B∞) 𝟙B) ∙ BooleanRingStr.·IdL (snd B∞) yb) ⟩
        𝟘∞ +B yb
          ≡⟨ BooleanRingStr.+IdL (snd B∞) yb ⟩
        yb ∎)

  roundtrip-B∞×B∞ : (p : ⟨ B∞×B∞ ⟩) → fst φQ (ψ-fun p) ≡ p
  roundtrip-B∞×B∞ (a , b) =
    fst φQ ((eQ ·Q fst ψL a) +Q (eQ' ·Q fst ψR b))
      ≡⟨ IsCommRingHom.pres+ (snd φQ) (eQ ·Q fst ψL a) (eQ' ·Q fst ψR b) ⟩
    fst φQ (eQ ·Q fst ψL a) +× fst φQ (eQ' ·Q fst ψR b)
      ≡⟨ cong₂ _+×_
           (IsCommRingHom.pres· (snd φQ) eQ (fst ψL a))
           (IsCommRingHom.pres· (snd φQ) eQ' (fst ψR b)) ⟩
    (fst φQ eQ ·×' fst φQ (fst ψL a)) +× (fst φQ eQ' ·×' fst φQ (fst ψR b))
      ≡⟨ cong₂ (λ u v → (u ·×' fst φQ (fst ψL a)) +× (v ·×' fst φQ (fst ψR b)))
           φQ-on-eQ
           (IsCommRingHom.pres+ (snd φQ) 𝟙Q eQ ∙ cong (_+× fst φQ eQ) (IsCommRingHom.pres1 (snd φQ)) ∙ cong ((𝟙B , 𝟙B) +×_) φQ-on-eQ) ⟩
    (unit-left ·×' fst φQ (fst ψL a)) +× (((𝟙B , 𝟙B) +× unit-left) ·×' fst φQ (fst ψR b))
      ≡⟨ unit-decompose (fst φQ (fst ψL a)) (fst φQ (fst ψR b)) ⟩
    (fst (fst φQ (fst ψL a)) , snd (fst φQ (fst ψR b)))
      ≡⟨ roundtrip-components a b ⟩
    (a , b) ∎
    where
    opaque
      unfolding QB.inducedHom
      unfolding QB.quotientImageHom
      fst∘φQ∘ψL∘π∞-on-gen : (n : ℕ) → fst (fst φQ (fst (ψL ∘cr π∞) (gen n))) ≡ fst π∞ (gen n)
      fst∘φQ∘ψL∘π∞-on-gen n =
        cong (fst ∘ fst φQ) (funExt⁻ (cong fst ψL-eval) (gen n) ∙ funExt⁻ genL-free-eval n)
        ∙ cong fst (funExt⁻ (cong fst φQ-eval) (gen (suc (encode× (⊎.inl n)))) ∙ funExt⁻ prodGenMap-free-eval (suc (encode× (⊎.inl n))) ∙ prodGenMap-on-left n)

      snd∘φQ∘ψR∘π∞-on-gen : (n : ℕ) → snd (fst φQ (fst (ψR ∘cr π∞) (gen n))) ≡ fst π∞ (gen n)
      snd∘φQ∘ψR∘π∞-on-gen n =
        cong (snd ∘ fst φQ) (funExt⁻ (cong fst ψR-eval) (gen n) ∙ funExt⁻ genR-free-eval n)
        ∙ cong snd (funExt⁻ (cong fst φQ-eval) (gen (suc (encode× (⊎.inr n)))) ∙ funExt⁻ prodGenMap-free-eval (suc (encode× (⊎.inr n))) ∙ prodGenMap-on-right n)

      fst-hom : BoolHom B∞×B∞ B∞
      fst-hom = fst , record { pres0 = refl ; pres1 = refl ; pres+ = λ _ _ → refl ; pres· = λ _ _ → refl ; pres- = λ _ → refl }

      snd-hom : BoolHom B∞×B∞ B∞
      snd-hom = snd , record { pres0 = refl ; pres1 = refl ; pres+ = λ _ _ → refl ; pres· = λ _ _ → refl ; pres- = λ _ → refl }

      fst∘φQ∘ψL∘π∞-hom : BoolHom (freeBA ℕ) B∞
      fst∘φQ∘ψL∘π∞-hom = fst-hom ∘cr φQ ∘cr ψL ∘cr π∞

      fst∘φQ∘ψL∘π∞≡π∞ : fst∘φQ∘ψL∘π∞-hom ≡ π∞
      fst∘φQ∘ψL∘π∞≡π∞ =
        sym (inducedBAHomUnique ℕ B∞ g∞ fst∘φQ∘ψL∘π∞-hom (funExt fst∘φQ∘ψL∘π∞-on-gen)) ∙
        inducedBAHomUnique ℕ B∞ g∞ π∞ refl

      snd∘φQ∘ψR∘π∞-hom : BoolHom (freeBA ℕ) B∞
      snd∘φQ∘ψR∘π∞-hom = snd-hom ∘cr φQ ∘cr ψR ∘cr π∞

      snd∘φQ∘ψR∘π∞≡π∞ : snd∘φQ∘ψR∘π∞-hom ≡ π∞
      snd∘φQ∘ψR∘π∞≡π∞ =
        sym (inducedBAHomUnique ℕ B∞ g∞ snd∘φQ∘ψR∘π∞-hom (funExt snd∘φQ∘ψR∘π∞-on-gen)) ∙
        inducedBAHomUnique ℕ B∞ g∞ π∞ refl

      fst∘φQ∘ψL-eq : fst ∘ fst φQ ∘ fst ψL ≡ (λ x → x)
      fst∘φQ∘ψL-eq = QB.quotientImageHomEpi {B = freeBA ℕ} {f = relB∞}
        (⟨ B∞ ⟩ , BooleanRingStr.is-set (snd B∞))
        (cong fst fst∘φQ∘ψL∘π∞≡π∞)

      snd∘φQ∘ψR-eq : snd ∘ fst φQ ∘ fst ψR ≡ (λ x → x)
      snd∘φQ∘ψR-eq = QB.quotientImageHomEpi {B = freeBA ℕ} {f = relB∞}
        (⟨ B∞ ⟩ , BooleanRingStr.is-set (snd B∞))
        (cong fst snd∘φQ∘ψR∘π∞≡π∞)

    roundtrip-components : (a b : ⟨ B∞ ⟩) → (fst (fst φQ (fst ψL a)) , snd (fst φQ (fst ψR b))) ≡ (a , b)
    roundtrip-components a b = cong₂ _,_ (funExt⁻ fst∘φQ∘ψL-eq a) (funExt⁻ snd∘φQ∘ψR-eq b)

  private
    typeA-encode : (n : ℕ) → prodRel (encode× (⊎.inl (encode× (⊎.inl n)))) ≡
                              gen 0 ·f gen (suc (encode× (⊎.inr n)))
    typeA-encode n =
      prodRel (encode× (⊎.inl (encode× (⊎.inl n))))
        ≡⟨ cong prodRelOuter (decode×∘encode× (⊎.inl (encode× (⊎.inl n)))) ⟩
      prodRelAB (decode× (encode× (⊎.inl n)))
        ≡⟨ cong prodRelAB (decode×∘encode× (⊎.inl n)) ⟩
      gen 0 ·f gen (suc (encode× (⊎.inr n))) ∎

    typeB-encode : (m : ℕ) → prodRel (encode× (⊎.inl (encode× (⊎.inr m)))) ≡
                              gen (suc (encode× (⊎.inl m))) ·f (𝟙 +f gen 0)
    typeB-encode m =
      prodRel (encode× (⊎.inl (encode× (⊎.inr m))))
        ≡⟨ cong prodRelOuter (decode×∘encode× (⊎.inl (encode× (⊎.inr m)))) ⟩
      prodRelAB (decode× (encode× (⊎.inr m)))
        ≡⟨ cong prodRelAB (decode×∘encode× (⊎.inr m)) ⟩
      gen (suc (encode× (⊎.inl m))) ·f (𝟙 +f gen 0) ∎

    typeA-in-Q : (n : ℕ) → fst πQ (gen 0 ·f gen (suc (encode× (⊎.inr n)))) ≡ 𝟘Q
    typeA-in-Q n = subst (λ x → fst πQ x ≡ 𝟘Q) (typeA-encode n)
                   (QB.zeroOnImage {B = freeBA ℕ} {f = prodRel} (encode× (⊎.inl (encode× (⊎.inl n)))))

    typeB-in-Q : (m : ℕ) → fst πQ (gen (suc (encode× (⊎.inl m))) ·f (𝟙 +f gen 0)) ≡ 𝟘Q
    typeB-in-Q m = subst (λ x → fst πQ x ≡ 𝟘Q) (typeB-encode m)
                   (QB.zeroOnImage {B = freeBA ℕ} {f = prodRel} (encode× (⊎.inl (encode× (⊎.inr m)))))

  private
    gen-f = BooleanRingStr.𝟙 (snd (freeBA ℕ))

    opaque
      eQ·genR≡𝟘 : (n : ℕ) → eQ ·Q fst πQ (gen (suc (encode× (⊎.inr n)))) ≡ 𝟘Q
      eQ·genR≡𝟘 n =
        eQ ·Q fst πQ (gen (suc (encode× (⊎.inr n))))
          ≡⟨ sym (IsCommRingHom.pres· (snd πQ) (gen 0) (gen (suc (encode× (⊎.inr n))))) ⟩
        fst πQ (gen 0 ·f gen (suc (encode× (⊎.inr n))))
          ≡⟨ typeA-in-Q n ⟩
        𝟘Q ∎

    opaque
      genL·eQ'≡𝟘 : (m : ℕ) → fst πQ (gen (suc (encode× (⊎.inl m)))) ·Q eQ' ≡ 𝟘Q
      genL·eQ'≡𝟘 m =
        fst πQ (gen (suc (encode× (⊎.inl m)))) ·Q eQ'
          ≡⟨ cong (fst πQ (gen (suc (encode× (⊎.inl m)))) ·Q_)
               (sym (cong (_+Q eQ) (IsCommRingHom.pres1 (snd πQ)))
                ∙ sym (IsCommRingHom.pres+ (snd πQ) gen-f (gen 0))) ⟩
        fst πQ (gen (suc (encode× (⊎.inl m)))) ·Q fst πQ (gen-f +f gen 0)
          ≡⟨ sym (IsCommRingHom.pres· (snd πQ) (gen (suc (encode× (⊎.inl m)))) (gen-f +f gen 0)) ⟩
        fst πQ (gen (suc (encode× (⊎.inl m))) ·f (gen-f +f gen 0))
          ≡⟨ typeB-in-Q m ⟩
        𝟘Q ∎

    opaque
      eQ+eQ'≡𝟙Q : eQ +Q eQ' ≡ 𝟙Q
      eQ+eQ'≡𝟙Q =
        eQ +Q eQ'
          ≡⟨ +AssocQ eQ 𝟙Q eQ ⟩
        (eQ +Q 𝟙Q) +Q eQ
          ≡⟨ cong (_+Q eQ) (+CommQ eQ 𝟙Q) ⟩
        (𝟙Q +Q eQ) +Q eQ
          ≡⟨ sym (+AssocQ 𝟙Q eQ eQ) ⟩
        𝟙Q +Q (eQ +Q eQ)
          ≡⟨ cong (𝟙Q +Q_) char2Q ⟩
        𝟙Q +Q 𝟘Q
          ≡⟨ +IdRQ 𝟙Q ⟩
        𝟙Q ∎

    absorb-by-complement : (e e' x : ⟨ B∞×B∞-Q ⟩) → e +Q e' ≡ 𝟙Q → x ·Q e' ≡ 𝟘Q → e ·Q x ≡ x
    absorb-by-complement e e' x sum=1 cross=0 = sym (
      x
        ≡⟨ sym (·IdRQ x) ⟩
      x ·Q 𝟙Q
        ≡⟨ cong (x ·Q_) (sym sum=1) ⟩
      x ·Q (e +Q e')
        ≡⟨ ·DistR+Q x e e' ⟩
      (x ·Q e) +Q (x ·Q e')
        ≡⟨ cong ((x ·Q e) +Q_) cross=0 ⟩
      (x ·Q e) +Q 𝟘Q
        ≡⟨ +IdRQ (x ·Q e) ⟩
      x ·Q e
        ≡⟨ ·CommQ x e ⟩
      e ·Q x ∎)

    opaque
      unfolding genL·eQ'≡𝟘
      unfolding eQ+eQ'≡𝟙Q
      eQ-absorbs-genL : (m : ℕ) → eQ ·Q fst πQ (gen (suc (encode× (⊎.inl m)))) ≡ fst πQ (gen (suc (encode× (⊎.inl m))))
      eQ-absorbs-genL m = absorb-by-complement eQ eQ' _ eQ+eQ'≡𝟙Q (genL·eQ'≡𝟘 m)

    opaque
      unfolding eQ·genR≡𝟘
      unfolding eQ+eQ'≡𝟙Q
      eQ'-absorbs-genR : (n : ℕ) → eQ' ·Q fst πQ (gen (suc (encode× (⊎.inr n)))) ≡ fst πQ (gen (suc (encode× (⊎.inr n))))
      eQ'-absorbs-genR n = absorb-by-complement eQ' eQ _ (+CommQ eQ' eQ ∙ eQ+eQ'≡𝟙Q) (·CommQ _ eQ ∙ eQ·genR≡𝟘 n)

  private
    opaque
      unfolding eQ-absorbs-genL
      ψ-on-unit-left : ψ-fun unit-left ≡ eQ
      ψ-on-unit-left =
        ψ-fun unit-left
          ≡⟨ cong₂ (λ u v → (eQ ·Q u) +Q (eQ' ·Q v))
               (IsCommRingHom.pres1 (snd ψL))
               (IsCommRingHom.pres0 (snd ψR)) ⟩
        (eQ ·Q 𝟙Q) +Q (eQ' ·Q 𝟘Q)
          ≡⟨ cong₂ _+Q_ (·IdRQ eQ) AnnihilRQ ⟩
        eQ +Q 𝟘Q
          ≡⟨ +IdRQ eQ ⟩
        eQ ∎

    opaque
      unfolding eQ-absorbs-genL
      ψ-on-genL : (m : ℕ) → ψ-fun (g∞ m , 𝟘∞) ≡ fst πQ (gen (suc (encode× (⊎.inl m))))
      ψ-on-genL m =
        ψ-fun (g∞ m , 𝟘∞)
          ≡⟨ cong₂ (λ u v → (eQ ·Q u) +Q (eQ' ·Q v))
               (ψL-gen m) (IsCommRingHom.pres0 (snd ψR)) ⟩
        (eQ ·Q fst πQ (gen (suc (encode× (⊎.inl m))))) +Q (eQ' ·Q 𝟘Q)
          ≡⟨ cong₂ _+Q_ (eQ-absorbs-genL m) AnnihilRQ ⟩
        fst πQ (gen (suc (encode× (⊎.inl m)))) +Q 𝟘Q
          ≡⟨ +IdRQ (fst πQ (gen (suc (encode× (⊎.inl m))))) ⟩
        fst πQ (gen (suc (encode× (⊎.inl m)))) ∎

    opaque
      unfolding eQ'-absorbs-genR
      ψ-on-genR : (n : ℕ) → ψ-fun (𝟘∞ , g∞ n) ≡ fst πQ (gen (suc (encode× (⊎.inr n))))
      ψ-on-genR n =
        ψ-fun (𝟘∞ , g∞ n)
          ≡⟨ cong₂ (λ u v → (eQ ·Q u) +Q (eQ' ·Q v))
               (IsCommRingHom.pres0 (snd ψL)) (ψR-gen n) ⟩
        (eQ ·Q 𝟘Q) +Q (eQ' ·Q fst πQ (gen (suc (encode× (⊎.inr n)))))
          ≡⟨ cong₂ _+Q_ AnnihilRQ (eQ'-absorbs-genR n) ⟩
        𝟘Q +Q fst πQ (gen (suc (encode× (⊎.inr n))))
          ≡⟨ +IdLQ (fst πQ (gen (suc (encode× (⊎.inr n))))) ⟩
        fst πQ (gen (suc (encode× (⊎.inr n)))) ∎

    opaque
      unfolding ψ-on-genL
      unfolding ψ-on-genR
      ψ-on-genProd : (x : ℕ ⊎ ℕ) → ψ-fun (genProd⊎ x) ≡ fst πQ (gen (suc (encode× x)))
      ψ-on-genProd (⊎.inl m) = ψ-on-genL m
      ψ-on-genProd (⊎.inr n) = ψ-on-genR n

    opaque
      unfolding ψ-on-unit-left
      unfolding ψ-on-genProd
      ψ∘φQ∘πQ-on-gen : (n : ℕ) → ψ-fun (fst φQ (fst πQ (gen n))) ≡ fst πQ (gen n)
      ψ∘φQ∘πQ-on-gen zero =
        ψ-fun (fst φQ (fst πQ (gen 0)))
          ≡⟨ cong ψ-fun (φQ-πQ-gen 0) ⟩
        ψ-fun (prodGenMap 0)
          ≡⟨ ψ-on-unit-left ⟩
        fst πQ (gen 0) ∎
      ψ∘φQ∘πQ-on-gen (suc k) =
        ψ-fun (fst φQ (fst πQ (gen (suc k))))
          ≡⟨ cong ψ-fun (φQ-πQ-gen (suc k)) ⟩
        ψ-fun (genProd⊎ (decode× k))
          ≡⟨ ψ-on-genProd (decode× k) ⟩
        fst πQ (gen (suc (encode× (decode× k))))
          ≡⟨ cong (λ i → fst πQ (gen (suc i))) (sec ℕ⊎ℕ≅ℕ k) ⟩
        fst πQ (gen (suc k)) ∎

    ψ∘φQ∘πQ-hom : BoolHom (freeBA ℕ) B∞×B∞-Q
    ψ∘φQ∘πQ-hom = ψ ∘cr (φQ ∘cr πQ)

    ψ∘φQ∘πQ≡πQ : ψ∘φQ∘πQ-hom ≡ πQ
    ψ∘φQ∘πQ≡πQ =
      let gQ = λ n → fst πQ (gen n)
      in sym (inducedBAHomUnique ℕ B∞×B∞-Q gQ ψ∘φQ∘πQ-hom (funExt ψ∘φQ∘πQ-on-gen)) ∙
         inducedBAHomUnique ℕ B∞×B∞-Q gQ πQ refl

  opaque
    unfolding QB._/Im_
    unfolding QB.quotientImageHom
    roundtrip-Q : (x : ⟨ B∞×B∞-Q ⟩) → ψ-fun (fst φQ x) ≡ x
    roundtrip-Q = SQ.elimProp (λ _ → BooleanRingStr.is-set (snd B∞×B∞-Q) _ _)
                   (λ a → funExt⁻ (cong fst ψ∘φQ∘πQ≡πQ) a)

  B∞×B∞≃Q : BooleanRingEquiv B∞×B∞ B∞×B∞-Q
  B∞×B∞≃Q = (ψ-fun , isoToIsEquiv (iso ψ-fun (fst φQ) roundtrip-Q roundtrip-B∞×B∞)) , ψ-hom

open B∞×B∞-Presentation

B∞×B∞-has-Boole-ω' : has-Boole-ω' B∞×B∞
B∞×B∞-has-Boole-ω' = prodRel , B∞×B∞≃Q

B∞×B∞-Booleω : Booleω
B∞×B∞-Booleω = B∞×B∞ , ∣ B∞×B∞-has-Boole-ω' ∣₁

private
  units-sum-to-one : unit-left +× unit-right ≡ (𝟙∞ , 𝟙∞)
  units-sum-to-one = cong₂ _,_ (+right-unit 𝟙∞) (+left-unit 𝟙∞)
    where
    open CommRingStr (snd (BooleanRing→CommRing B∞)) using () renaming (+IdL to +left-unit ; +IdR to +right-unit)

  unit-left-true→unit-right-false : (h : Sp B∞×B∞-Booleω)
    → h $cr unit-left ≡ true → h $cr unit-right ≡ false
  unit-left-true→unit-right-false h pf = true-⊕-id (h $cr unit-right) chain
    where
    open CommRingStr (snd (BooleanRing→CommRing BoolBR)) using () renaming (_+_ to _⊕Bool_)
    h-sum : h $cr (unit-left +× unit-right) ≡ (h $cr unit-left) ⊕Bool (h $cr unit-right)
    h-sum = IsCommRingHom.pres+ (snd h) unit-left unit-right
    h-one : h $cr (𝟙∞ , 𝟙∞) ≡ true
    h-one = IsCommRingHom.pres1 (snd h)
    true-⊕-id : (b : Bool) → true ⊕Bool b ≡ true → b ≡ false
    true-⊕-id false _ = refl
    true-⊕-id true = λ eq → ex-falso (false≢true eq)
    chain : true ⊕Bool (h $cr unit-right) ≡ true
    chain =
      true ⊕Bool (h $cr unit-right)
        ≡⟨ cong (λ b → b ⊕Bool (h $cr unit-right)) (sym pf) ⟩
      (h $cr unit-left) ⊕Bool (h $cr unit-right)
        ≡⟨ sym h-sum ⟩
      h $cr (unit-left +× unit-right)
        ≡⟨ cong (h $cr_) units-sum-to-one ⟩
      h $cr (𝟙∞ , 𝟙∞)
        ≡⟨ h-one ⟩
      true ∎

  unit-left-false→unit-right-true : (h : Sp B∞×B∞-Booleω)
    → h $cr unit-left ≡ false → h $cr unit-right ≡ true
  unit-left-false→unit-right-true h pf =
    h $cr unit-right
      ≡⟨ cong (λ b → b ⊕ (h $cr unit-right)) (sym pf) ⟩
    (h $cr unit-left) ⊕ (h $cr unit-right)
      ≡⟨ sym (IsCommRingHom.pres+ (snd h) unit-left unit-right) ⟩
    h $cr (unit-left +× unit-right)
      ≡⟨ cong (h $cr_) units-sum-to-one ⟩
    h $cr (𝟙∞ , 𝟙∞)
      ≡⟨ IsCommRingHom.pres1 (snd h) ⟩
    true ∎

Sp-f : Sp B∞×B∞-Booleω → Sp B∞-Booleω
Sp-f h = h ∘cr f

private
  hom-orth-implies-false : (h' : Sp B∞×B∞-Booleω) (u v : ⟨ B∞×B∞ ⟩)
    → h' $cr u ≡ true → u ·× v ≡ (𝟘∞ , 𝟘∞) → h' $cr v ≡ false
  hom-orth-implies-false h' u v h'u=true uv=0 =
    subst (λ b → b and (h' $cr v) ≡ false) h'u=true h'-and
    where
    h'-and : (h' $cr u) and (h' $cr v) ≡ false
    h'-and =
      (h' $cr u) and (h' $cr v)
        ≡⟨ sym (IsCommRingHom.pres· (snd h') u v) ⟩
      h' $cr (u ·× v)
        ≡⟨ cong (h' $cr_) uv=0 ⟩
      h' $cr (𝟘∞ , 𝟘∞)
        ≡⟨ IsCommRingHom.pres0 (snd h') ⟩
      false ∎

h'-left-true→right-false : (h' : Sp B∞×B∞-Booleω) → h' $cr unit-left ≡ true →
  (y : ⟨ B∞ ⟩) → h' $cr (𝟘∞ , y) ≡ false
h'-left-true→right-false h' h'-left-true y =
  hom-orth-implies-false h' unit-left (𝟘∞ , y) h'-left-true (cong₂ _,_ (0∞-absorbs-right 𝟙∞) (0∞-absorbs-left y))

h'-right-true→left-false : (h' : Sp B∞×B∞-Booleω) → h' $cr unit-right ≡ true →
  (x : ⟨ B∞ ⟩) → h' $cr (x , 𝟘∞) ≡ false
h'-right-true→left-false h' h'-right-true x =
  hom-orth-implies-false h' unit-right (x , 𝟘∞) h'-right-true (cong₂ _,_ (0∞-absorbs-left x) (0∞-absorbs-right 𝟙∞))

ℕ∞-on-gen : ℕ∞ → ℕ → Bool
ℕ∞-on-gen α n = fst α n

ℕ∞-gen-respects-relations : (α : ℕ∞) → (m n : ℕ) → ¬ (m ≡ n) →
  (ℕ∞-on-gen α m) and (ℕ∞-on-gen α n) ≡ false
ℕ∞-gen-respects-relations α m n m≠n with fst α m in eq-m | fst α n in eq-n
... | false | _ = refl
... | true | false = refl
... | true | true = ex-falso (m≠n (snd α m n (builtin→Path-Bool eq-m) (builtin→Path-Bool eq-n)))

ℕ∞-to-SpB∞-free : ℕ∞ → BoolHom (freeBA ℕ) BoolBR
ℕ∞-to-SpB∞-free α = inducedBAHom ℕ BoolBR (ℕ∞-on-gen α)

ℕ∞-to-SpB∞-free-on-gen : (α : ℕ∞) → fst (ℕ∞-to-SpB∞-free α) ∘ generator ≡ ℕ∞-on-gen α
ℕ∞-to-SpB∞-free-on-gen α = evalBAInduce ℕ BoolBR (ℕ∞-on-gen α)

ℕ∞-to-SpB∞-free-distinct-zero : (α : ℕ∞) (a b : ℕ) → ¬ (a ≡ b) →
  fst (ℕ∞-to-SpB∞-free α) (gen a · gen b) ≡ false
ℕ∞-to-SpB∞-free-distinct-zero α a b a≠b =
  fst (ℕ∞-to-SpB∞-free α) (gen a · gen b)
    ≡⟨ IsCommRingHom.pres· (snd (ℕ∞-to-SpB∞-free α)) (gen a) (gen b) ⟩
  (fst (ℕ∞-to-SpB∞-free α) (gen a)) and (fst (ℕ∞-to-SpB∞-free α) (gen b))
    ≡⟨ cong₂ _and_ (funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) a) (funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) b) ⟩
  (ℕ∞-on-gen α a) and (ℕ∞-on-gen α b)
    ≡⟨ ℕ∞-gen-respects-relations α a b a≠b ⟩
  false ∎

ℕ∞-to-SpB∞-respects-rel : (α : ℕ∞) (k : ℕ) →
  fst (ℕ∞-to-SpB∞-free α) (relB∞ k) ≡ false
ℕ∞-to-SpB∞-respects-rel α k =
  let (a , d) = cantorUnpair k
  in ℕ∞-to-SpB∞-free-distinct-zero α a (a +ℕ suc d) (a≠a+suc-d a d)

ℕ∞-to-SpB∞ : ℕ∞ → Sp B∞-Booleω
ℕ∞-to-SpB∞ α = QB.inducedHom {B = freeBA ℕ} {f = relB∞} BoolBR (ℕ∞-to-SpB∞-free α) (ℕ∞-to-SpB∞-respects-rel α)

opaque
  unfolding QB.inducedHom
  unfolding QB.quotientImageHom
  ℕ∞-to-SpB∞-eval : (α : ℕ∞) →
    (ℕ∞-to-SpB∞ α) ∘cr π∞ ≡ ℕ∞-to-SpB∞-free α
  ℕ∞-to-SpB∞-eval α = QB.evalInduce {B = freeBA ℕ} {f = relB∞} BoolBR

SpB∞-roundtrip-seq : (α : ℕ∞) (n : ℕ) →
  SpB∞-to-ℕ∞-seq (ℕ∞-to-SpB∞ α) n ≡ fst α n
SpB∞-roundtrip-seq α n =
  (ℕ∞-to-SpB∞ α) $cr (fst π∞ (gen n))
    ≡⟨ funExt⁻ (cong fst (ℕ∞-to-SpB∞-eval α)) (gen n) ⟩
  fst (ℕ∞-to-SpB∞-free α) (gen n)
    ≡⟨ funExt⁻ (ℕ∞-to-SpB∞-free-on-gen α) n ⟩
  fst α n ∎

SpB∞-roundtrip : (α : ℕ∞) → SpB∞-to-ℕ∞ (ℕ∞-to-SpB∞ α) ≡ α
SpB∞-roundtrip α = Σ≡Prop
  (λ s → isPropHitsAtMostOnce s)
  (funExt (SpB∞-roundtrip-seq α))

g∞-has-witness : (n : ℕ) → (ℕ∞-to-SpB∞ (δ∞ n)) $cr (g∞ n) ≡ true
g∞-has-witness n =
  (ℕ∞-to-SpB∞ (δ∞ n)) $cr (g∞ n)
    ≡⟨ SpB∞-roundtrip-seq (δ∞ n) n ⟩
  fst (δ∞ n) n
    ≡⟨ δ∞-hits-n n ⟩
  true ∎

g∞-nonzero : (n : ℕ) → ¬ (g∞ n ≡ 𝟘∞)
g∞-nonzero n gn=0 =
  let h = ℕ∞-to-SpB∞ (δ∞ n)
      h-gn=t : h $cr (g∞ n) ≡ true
      h-gn=t = g∞-has-witness n
      h-0=f : h $cr 𝟘∞ ≡ false
      h-0=f = IsCommRingHom.pres0 (snd h)
      h-gn=f : h $cr (g∞ n) ≡ false
      h-gn=f =
        h $cr (g∞ n)
          ≡⟨ cong (h $cr_) gn=0 ⟩
        h $cr 𝟘∞
          ≡⟨ h-0=f ⟩
        false ∎
  in true≢false (sym h-gn=t ∙ h-gn=f)

h-pres-join-Bool : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr (a ∨∞ b) ≡ (h $cr a) or (h $cr b)
h-pres-join-Bool h a b =
  let open IsCommRingHom (snd h) renaming (pres+ to h-pres+ ; pres· to h-pres·)
  in h $cr (a +∞ b +∞ (a ·∞ b))
       ≡⟨ h-pres+ (a +∞ b) (a ·∞ b) ⟩
     (h $cr (a +∞ b)) ⊕ (h $cr (a ·∞ b))
       ≡⟨ cong₂ _⊕_ (h-pres+ a b) (h-pres· a b) ⟩
     ((h $cr a) ⊕ (h $cr b)) ⊕ ((h $cr a) and (h $cr b))
       ≡⟨ xor-and-is-or (h $cr a) (h $cr b) ⟩
     (h $cr a) or (h $cr b) ∎

h-join-monotone : (h : Sp B∞-Booleω) (a b : ⟨ B∞ ⟩) →
  h $cr a ≡ true → h $cr (a ∨∞ b) ≡ true
h-join-monotone h a b ha=t =
  h $cr (a ∨∞ b)
    ≡⟨ h-pres-join-Bool h a b ⟩
  (h $cr a) or (h $cr b)
    ≡⟨ cong (_or (h $cr b)) ha=t ⟩
  true ∎

finJoin∞-zero→empty : (ns : List ℕ) → finJoin∞ ns ≡ 𝟘∞ → ns ≡ []
finJoin∞-zero→empty [] _ = refl
finJoin∞-zero→empty (n ∷ rest) join=0 = ex-falso contradiction
  where
  h : Sp B∞-Booleω
  h = ℕ∞-to-SpB∞ (δ∞ n)

  h-gn=true : h $cr (g∞ n) ≡ true
  h-gn=true = g∞-has-witness n

  h-join=true : h $cr (finJoin∞ (n ∷ rest)) ≡ true
  h-join=true = h-join-monotone h (g∞ n) (finJoin∞ rest) h-gn=true

  h-0=false : h $cr 𝟘∞ ≡ false
  h-0=false = IsCommRingHom.pres0 (snd h)

  h-join=false : h $cr (finJoin∞ (n ∷ rest)) ≡ false
  h-join=false =
    h $cr (finJoin∞ (n ∷ rest))
      ≡⟨ cong (h $cr_) join=0 ⟩
    h $cr 𝟘∞
      ≡⟨ h-0=false ⟩
    false ∎

  contradiction : ⊥
  contradiction = true≢false (sym h-join=true ∙ h-join=false)

h₀ : Sp B∞-Booleω
h₀ = ℕ∞-to-SpB∞ ∞

h-pres-neg-Bool : (h : Sp B∞-Booleω) (x : ⟨ B∞ ⟩) →
  h $cr (¬∞ x) ≡ not (h $cr x)
h-pres-neg-Bool h x =
  let open IsCommRingHom (snd h) renaming (pres+ to h-pres+ ; pres1 to h-pres1)
  in h $cr (𝟙∞ +∞ x)
       ≡⟨ h-pres+ 𝟙∞ x ⟩
     (h $cr 𝟙∞) ⊕ (h $cr x)
       ≡⟨ cong (_⊕ (h $cr x)) h-pres1 ⟩
     not (h $cr x) ∎

h₀-on-neg-gen : (n : ℕ) → h₀ $cr (¬∞ (g∞ n)) ≡ true
h₀-on-neg-gen n =
  h₀ $cr (¬∞ (g∞ n))
    ≡⟨ h-pres-neg-Bool h₀ (g∞ n) ⟩
  not (h₀ $cr (g∞ n))
    ≡⟨ cong not (SpB∞-roundtrip-seq ∞ n) ⟩
  true ∎

h₀-on-finMeetNeg : (ns : List ℕ) → h₀ $cr (finMeetNeg∞ ns) ≡ true
h₀-on-finMeetNeg [] = IsCommRingHom.pres1 (snd h₀)
h₀-on-finMeetNeg (n ∷ ns) =
  h₀ $cr ((¬∞ (g∞ n)) ∧∞ finMeetNeg∞ ns)
    ≡⟨ IsCommRingHom.pres· (snd h₀) (¬∞ (g∞ n)) (finMeetNeg∞ ns) ⟩
  (h₀ $cr (¬∞ (g∞ n))) and (h₀ $cr finMeetNeg∞ ns)
    ≡⟨ cong₂ _and_ (h₀-on-neg-gen n) (h₀-on-finMeetNeg ns) ⟩
  true ∎

finMeetNeg∞-nonzero : (ns : List ℕ) → ¬ (finMeetNeg∞ ns ≡ 𝟘∞)
finMeetNeg∞-nonzero ns meet=0 = contradiction
  where
  h₀-meet=true : h₀ $cr (finMeetNeg∞ ns) ≡ true
  h₀-meet=true = h₀-on-finMeetNeg ns

  h₀-0=false : h₀ $cr 𝟘∞ ≡ false
  h₀-0=false = IsCommRingHom.pres0 (snd h₀)

  h₀-meet=false : h₀ $cr (finMeetNeg∞ ns) ≡ false
  h₀-meet=false =
    h₀ $cr (finMeetNeg∞ ns)
      ≡⟨ cong (h₀ $cr_) meet=0 ⟩
    h₀ $cr 𝟘∞
      ≡⟨ h₀-0=false ⟩
    false ∎

  contradiction : ⊥
  contradiction = true≢false (sym h₀-meet=true ∙ h₀-meet=false)

splitByParity-evens : List ℕ → List ℕ
splitByParity-evens ns = fst (splitByParity ns)

splitByParity-odds : List ℕ → List ℕ
splitByParity-odds ns = snd (splitByParity ns)

splitByParity-cons-even : (n : ℕ) (ns : List ℕ) → isEven n ≡ true →
  splitByParity-evens (n ∷ ns) ≡ half n ∷ splitByParity-evens ns
splitByParity-cons-even n ns even-n with isEven n | splitByParity ns
... | true  | (evens , odds) = refl
... | false | (evens , odds) = ex-falso (false≢true even-n)

splitByParity-cons-odd : (n : ℕ) (ns : List ℕ) → isEven n ≡ false →
  splitByParity-odds (n ∷ ns) ≡ half n ∷ splitByParity-odds ns
splitByParity-cons-odd n ns odd-n with isEven n | splitByParity ns
... | false | (evens , odds) = refl
... | true  | (evens , odds) = ex-falso (true≢false odd-n)

splitByParity-nonempty : (ns : List ℕ) →
  let (evens , odds) = splitByParity ns
  in evens ≡ [] → odds ≡ [] → ns ≡ []
splitByParity-nonempty [] _ _ = refl
splitByParity-nonempty (n ∷ ns) evens=[] odds=[] = splitByParity-nonempty-aux (isEven n) refl
  where
  splitByParity-nonempty-aux : (b : Bool) → isEven n ≡ b → (n ∷ ns) ≡ []
  splitByParity-nonempty-aux true parity =
    let contradiction : half n ∷ splitByParity-evens ns ≡ []
        contradiction =
          half n ∷ splitByParity-evens ns
            ≡⟨ sym (splitByParity-cons-even n ns parity) ⟩
          splitByParity-evens (n ∷ ns)
            ≡⟨ evens=[] ⟩
          [] ∎
    in ex-falso (¬cons≡nil contradiction)
  splitByParity-nonempty-aux false parity =
    let contradiction : half n ∷ splitByParity-odds ns ≡ []
        contradiction =
          half n ∷ splitByParity-odds ns
            ≡⟨ sym (splitByParity-cons-odd n ns parity) ⟩
          splitByParity-odds (n ∷ ns)
            ≡⟨ odds=[] ⟩
          [] ∎
    in ex-falso (¬cons≡nil contradiction)

-- Via B∞ ≅ ℕfinCofinBA: the "characteristic sequence" of x ∈ B∞
private
  module FC = BooleanRingStr (snd NFC.ℕfinCofinBA)
  FC-eq : {a b : ⟨ NFC.ℕfinCofinBA ⟩} → fst a ≡ fst b → a ≡ b
  FC-eq = Σ≡Prop NFC.isPropisFiniteOrCofinite

  φ-seq : ⟨ B∞ ⟩ → (ℕ → Bool)
  φ-seq x = fst (fst Bridge.φ_FC x)

  φ_FC-injective : (x y : ⟨ B∞ ⟩) → fst Bridge.φ_FC x ≡ fst Bridge.φ_FC y → x ≡ y
  φ_FC-injective x y p =
    sym (Bridge.roundtrip-B∞ x) ∙ cong (fst Bridge.ψ_FC) p ∙ Bridge.roundtrip-B∞ y

  -- Key lemma: g∞(n) · x = g∞(n) implies φ-seq(x)(n) = true
  -- Proof: apply φ_FC to both sides; singleton(n) · φ_FC(x) = singleton(n);
  --        at position n: δ(n,n) and α(n) = δ(n,n), hence α(n) = true
  gen-absorb→bit-true : (x : ⟨ B∞ ⟩) (n : ℕ) → g∞ n ·∞ x ≡ g∞ n → φ-seq x n ≡ true
  gen-absorb→bit-true x n absorb =
    let mul-in-FC : FC._·_ (Pres.singleton n) (fst Bridge.φ_FC x) ≡ Pres.singleton n
        mul-in-FC =
          cong (λ z → FC._·_ z (fst Bridge.φ_FC x)) (sym (Bridge.φ_FC-on-gen n))
          ∙ sym (IsCommRingHom.pres· (snd Bridge.φ_FC) (g∞ n) x)
          ∙ cong (fst Bridge.φ_FC) absorb
          ∙ Bridge.φ_FC-on-gen n
        -- At position n: δ(n,n) and α(n) = δ(n,n)
        at-n : fst (FC._·_ (Pres.singleton n) (fst Bridge.φ_FC x)) n ≡ fst (Pres.singleton n) n
        at-n = funExt⁻ (cong fst mul-in-FC) n
        -- Substitute true for δ(n,n): true and α(n) = true, i.e., α(n) = true
    in subst (λ d → d and φ-seq x n ≡ d) (Pres.δnn=1 n) at-n

  -- Reverse direction: if φ-seq(x)(n) = true, then g∞(n) · x = g∞(n)
  -- Proof: in ℕfinCofinBA, singleton(n) · α = singleton(n) when α(n) = true
  --        since φ_FC is injective, this lifts to B∞
  αn-true→gen-absorb : (x : ⟨ B∞ ⟩) (n : ℕ) → φ-seq x n ≡ true → g∞ n ·∞ x ≡ g∞ n
  αn-true→gen-absorb x n αn=true = φ_FC-injective (g∞ n ·∞ x) (g∞ n) eq-in-FC
    where
    singleton-absorb : FC._·_ (Pres.singleton n) (fst Bridge.φ_FC x) ≡ Pres.singleton n
    singleton-absorb = FC-eq (funExt helper)
      where
      helper : (k : ℕ) → fst (FC._·_ (Pres.singleton n) (fst Bridge.φ_FC x)) k
                        ≡ fst (Pres.singleton n) k
      helper k with discreteℕ n k
      ... | yes refl =
        cong (_and φ-seq x n) (Pres.δnn=1 n)
        ∙ αn=true
        ∙ sym (Pres.δnn=1 n)
      ... | no n≢k =
        cong (_and φ-seq x k) (Pres.δnm=0 n k n≢k)
        ∙ sym (Pres.δnm=0 n k n≢k)

    eq-in-FC : fst Bridge.φ_FC (g∞ n ·∞ x) ≡ fst Bridge.φ_FC (g∞ n)
    eq-in-FC =
      fst Bridge.φ_FC (g∞ n ·∞ x)
        ≡⟨ IsCommRingHom.pres· (snd Bridge.φ_FC) (g∞ n) x ⟩
      FC._·_ (fst Bridge.φ_FC (g∞ n)) (fst Bridge.φ_FC x)
        ≡⟨ cong (λ z → FC._·_ z (fst Bridge.φ_FC x)) (Bridge.φ_FC-on-gen n) ⟩
      FC._·_ (Pres.singleton n) (fst Bridge.φ_FC x)
        ≡⟨ singleton-absorb ⟩
      Pres.singleton n
        ≡⟨ sym (Bridge.φ_FC-on-gen n) ⟩
      fst Bridge.φ_FC (g∞ n) ∎

-- f has trivial kernel: f(x) = (0,0) → x = 0
-- Proof via B∞ ≅ ℕfinCofinBA: if any bit α(n) of φ_FC(x) were true,
-- then g∞(n) · x = g∞(n), so f(g∞(n)) = f(g∞(n) · x) = f(g∞(n)) · f(x) = 0,
-- contradicting g∞(n) ≠ 0.
f-kernel : (x : ⟨ B∞ ⟩) → fst f x ≡ (𝟘∞ , 𝟘∞) → x ≡ 𝟘∞
f-kernel x fx=0 = φ_FC-injective x 𝟘∞
    (FC-eq (funExt all-bits-false) ∙ sym (IsCommRingHom.pres0 (snd Bridge.φ_FC)))
  where
  α = φ-seq x

  all-bits-false : (n : ℕ) → α n ≡ false
  all-bits-false n with α n in αn-eq
  ... | false = refl
  ... | true = ex-falso (g∞-nonzero n gen-n=0)
    where
    gen-absorb : g∞ n ·∞ x ≡ g∞ n
    gen-absorb = αn-true→gen-absorb x n (builtin→Path-Bool αn-eq)

    f-gen-n=0 : fst f (g∞ n) ≡ (𝟘∞ , 𝟘∞)
    f-gen-n=0 =
      fst f (g∞ n)
        ≡⟨ cong (fst f) (sym gen-absorb) ⟩
      fst f (g∞ n ·∞ x)
        ≡⟨ IsCommRingHom.pres· (snd f) (g∞ n) x ⟩
      (fst f (g∞ n)) ·× (fst f x)
        ≡⟨ cong ((fst f (g∞ n)) ·×_) fx=0 ⟩
      (fst f (g∞ n)) ·× (𝟘∞ , 𝟘∞)
        ≡⟨ cong₂ _,_ (0∞-absorbs-right (fst (fst f (g∞ n))))
                      (0∞-absorbs-right (snd (fst f (g∞ n)))) ⟩
      (𝟘∞ , 𝟘∞) ∎

    gen-n=0 : g∞ n ≡ 𝟘∞
    gen-n=0 with isEven n in parity
    ... | true =
      let k = half n
          eq : fst f (g∞ n) ≡ (g∞ k , 𝟘∞)
          eq = subst (λ m → fst f (g∞ m) ≡ (g∞ k , 𝟘∞)) (sym (isEven→even n parity)) (f-even-gen k)
      in ex-falso (g∞-nonzero k (cong fst (sym eq ∙ f-gen-n=0)))
    ... | false =
      let k = half n
          eq : fst f (g∞ n) ≡ (𝟘∞ , g∞ k)
          eq = subst (λ m → fst f (g∞ m) ≡ (𝟘∞ , g∞ k)) (sym (isEven→odd n parity)) (f-odd-gen k)
      in ex-falso (g∞-nonzero k (cong snd (sym eq ∙ f-gen-n=0)))

f-injective : (x y : ⟨ B∞ ⟩) → fst f x ≡ fst f y → x ≡ y
f-injective x y fx=fy =
  let xy-diff : ⟨ B∞ ⟩
      xy-diff = x +∞ y

      f-xy-diff : fst f xy-diff ≡ (𝟘∞ , 𝟘∞)
      f-xy-diff =
        fst f (x +∞ y)
          ≡⟨ f-pres+ x y ⟩
        (fst f x) +× (fst f y)
          ≡⟨ cong (_+× (fst f y)) fx=fy ⟩
        (fst f y) +× (fst f y)
          ≡⟨ char2-B∞×B∞ (fst f y) ⟩
        (𝟘∞ , 𝟘∞) ∎

      xy=0 : xy-diff ≡ 𝟘∞
      xy=0 = f-kernel xy-diff f-xy-diff

      x=y : x ≡ y
      x=y =
        x
          ≡⟨ sym (BooleanRingStr.+IdR (snd B∞) x) ⟩
        x +∞ 𝟘∞
          ≡⟨ cong (x +∞_) (sym (char2-B∞ y)) ⟩
        x +∞ (y +∞ y)
          ≡⟨ BooleanRingStr.+Assoc (snd B∞) x y y ⟩
        (x +∞ y) +∞ y
          ≡⟨ cong (_+∞ y) xy=0 ⟩
        𝟘∞ +∞ y
          ≡⟨ BooleanRingStr.+IdL (snd B∞) y ⟩
        y ∎

  in x=y

llpo-from-SD-aux : (h : Sp B∞-Booleω) →
  ∥ ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎ ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) ∥₁
llpo-from-SD-aux h = PT.rec PT.squash₁ go (injective→Sp-surjective B∞-Booleω B∞×B∞-Booleω f f-injective h)
  where
  go : Σ[ h' ∈ Sp B∞×B∞-Booleω ] Sp-f h' ≡ h →
       ∥ ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎ ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) ∥₁
  go (h' , Sp-f-h'≡h) = ∣ go' (h' $cr unit-left) refl ∣₁
    where
    go' : (b : Bool) → h' $cr unit-left ≡ b →
          ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
          ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false)
    go' true h'-left-true = ⊎.inr odds-zero-case
      where
      odds-zero-case : (k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false
      odds-zero-case k =
        h $cr (g∞ (suc (2 ·ℕ k)))
          ≡⟨ sym (funExt⁻ (cong fst Sp-f-h'≡h) (g∞ (suc (2 ·ℕ k)))) ⟩
        h' $cr (fst f (g∞ (suc (2 ·ℕ k))))
          ≡⟨ cong (h' $cr_) (f-odd-gen k) ⟩
        h' $cr (𝟘∞ , g∞ k)
          ≡⟨ h'-left-true→right-false h' h'-left-true (g∞ k) ⟩
        false ∎
    go' false h'-left-false = ⊎.inl evens-zero-case
      where
      h'-right-true : h' $cr unit-right ≡ true
      h'-right-true = unit-left-false→unit-right-true h' h'-left-false

      evens-zero-case : (k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false
      evens-zero-case k =
        h $cr (g∞ (2 ·ℕ k))
          ≡⟨ sym (funExt⁻ (cong fst Sp-f-h'≡h) (g∞ (2 ·ℕ k))) ⟩
        h' $cr (fst f (g∞ (2 ·ℕ k)))
          ≡⟨ cong (h' $cr_) (f-even-gen k) ⟩
        h' $cr (g∞ k , 𝟘∞)
          ≡⟨ h'-right-true→left-false h' h'-right-true (g∞ k) ⟩
        false ∎

-- tex Theorem 541, equation 544 (eqnLLPO), equation 555 (eqnLLPOProofMap)
llpo-from-SD : LLPO
llpo-from-SD α = PT.map transport-llpo (llpo-from-SD-aux h)
  where
  h : Sp B∞-Booleω
  h = ℕ∞-to-SpB∞ α

  seq-eq : (n : ℕ) → h $cr (g∞ n) ≡ fst α n
  seq-eq n = funExt⁻ (cong fst (SpB∞-roundtrip α)) n

  transport-llpo : ((k : ℕ) → h $cr (g∞ (2 ·ℕ k)) ≡ false) ⊎
                   ((k : ℕ) → h $cr (g∞ (suc (2 ·ℕ k))) ≡ false) →
                   ((k : ℕ) → fst α (2 ·ℕ k) ≡ false) ⊎
                   ((k : ℕ) → fst α (suc (2 ·ℕ k)) ≡ false)
  transport-llpo (⊎.inl evens) = ⊎.inl (λ k → sym (seq-eq (2 ·ℕ k)) ∙ evens k)
  transport-llpo (⊎.inr odds) = ⊎.inr (λ k → sym (seq-eq (suc (2 ·ℕ k))) ∙ odds k)

-- tex Lemma 600: The map f : B∞ → B∞×B∞ does not have a retraction
-- Proof via B∞ ≅ ℕfinCofinBA: r(0,1) and r(1,0) can be classified as finite or cofinite.
-- If either is finite: its support is bounded, but the retraction forces infinitely many
-- odd (resp. even) generators to be in the support. Contradiction.
-- If both cofinite: their product is cofinite (hence nonzero), but r(0,1)·r(1,0) = 0. Contradiction.

open import Cubical.Data.Nat.Order using (_<_; _≤_; ¬m<m; ≤-refl; ≤-suc; ≤-trans; zero-≤)

f-no-retraction : (r : BoolHom B∞×B∞ B∞) → ¬ ((x : ⟨ B∞ ⟩) → fst r (fst f x) ≡ x)
f-no-retraction r retract = go (snd (fst Bridge.φ_FC r01)) (snd (fst Bridge.φ_FC r10))
  where
  r01 = fst r (𝟘∞ , 𝟙∞)
  r10 = fst r (𝟙∞ , 𝟘∞)

  α₁ = φ-seq r01
  α₂ = φ-seq r10

  r-on-gen-odd : (k : ℕ) → fst r (𝟘∞ , g∞ k) ≡ g∞ (suc (2 ·ℕ k))
  r-on-gen-odd k =
    fst r (𝟘∞ , g∞ k)
      ≡⟨ cong (fst r) (sym (f-odd-gen k)) ⟩
    fst r (fst f (g∞ (suc (2 ·ℕ k))))
      ≡⟨ retract (g∞ (suc (2 ·ℕ k))) ⟩
    g∞ (suc (2 ·ℕ k)) ∎

  r-on-gen-even : (k : ℕ) → fst r (g∞ k , 𝟘∞) ≡ g∞ (2 ·ℕ k)
  r-on-gen-even k =
    fst r (g∞ k , 𝟘∞)
      ≡⟨ cong (fst r) (sym (f-even-gen k)) ⟩
    fst r (fst f (g∞ (2 ·ℕ k)))
      ≡⟨ retract (g∞ (2 ·ℕ k)) ⟩
    g∞ (2 ·ℕ k) ∎

  -- g_{2k+1} · r(0,1) = g_{2k+1}
  odd-gen-below-r01 : (k : ℕ) → g∞ (suc (2 ·ℕ k)) ·∞ r01 ≡ g∞ (suc (2 ·ℕ k))
  odd-gen-below-r01 k =
    g∞ (suc (2 ·ℕ k)) ·∞ r01
      ≡⟨ cong₂ _·∞_ (sym (r-on-gen-odd k)) refl ⟩
    fst r (𝟘∞ , g∞ k) ·∞ fst r (𝟘∞ , 𝟙∞)
      ≡⟨ sym (IsCommRingHom.pres· (snd r) (𝟘∞ , g∞ k) (𝟘∞ , 𝟙∞)) ⟩
    fst r ((𝟘∞ , g∞ k) ·× (𝟘∞ , 𝟙∞))
      ≡⟨ cong (fst r) (cong₂ _,_ (0∞-absorbs-left 𝟘∞) (BooleanRingStr.·IdR (snd B∞) (g∞ k))) ⟩
    fst r (𝟘∞ , g∞ k)
      ≡⟨ r-on-gen-odd k ⟩
    g∞ (suc (2 ·ℕ k)) ∎

  even-gen-below-r10 : (k : ℕ) → g∞ (2 ·ℕ k) ·∞ r10 ≡ g∞ (2 ·ℕ k)
  even-gen-below-r10 k =
    g∞ (2 ·ℕ k) ·∞ r10
      ≡⟨ cong₂ _·∞_ (sym (r-on-gen-even k)) refl ⟩
    fst r (g∞ k , 𝟘∞) ·∞ fst r (𝟙∞ , 𝟘∞)
      ≡⟨ sym (IsCommRingHom.pres· (snd r) (g∞ k , 𝟘∞) (𝟙∞ , 𝟘∞)) ⟩
    fst r ((g∞ k , 𝟘∞) ·× (𝟙∞ , 𝟘∞))
      ≡⟨ cong (fst r) (cong₂ _,_ (BooleanRingStr.·IdR (snd B∞) (g∞ k)) (0∞-absorbs-left 𝟘∞)) ⟩
    fst r (g∞ k , 𝟘∞)
      ≡⟨ r-on-gen-even k ⟩
    g∞ (2 ·ℕ k) ∎

  -- r(0,1) · r(1,0) = r(0,0) = 0
  r01·r10≡0 : r01 ·∞ r10 ≡ 𝟘∞
  r01·r10≡0 =
    r01 ·∞ r10
      ≡⟨ sym (IsCommRingHom.pres· (snd r) (𝟘∞ , 𝟙∞) (𝟙∞ , 𝟘∞)) ⟩
    fst r ((𝟘∞ , 𝟙∞) ·× (𝟙∞ , 𝟘∞))
      ≡⟨ cong (fst r) (cong₂ _,_ (0∞-absorbs-left 𝟙∞) (0∞-absorbs-right 𝟙∞)) ⟩
    fst r (𝟘∞ , 𝟘∞)
      ≡⟨ IsCommRingHom.pres0 (snd r) ⟩
    𝟘∞ ∎

  -- Via ℕfinCofinBA: odd generators are "in" r01, even generators are "in" r10
  α₁-odd-true : (k : ℕ) → α₁ (suc (2 ·ℕ k)) ≡ true
  α₁-odd-true k = gen-absorb→bit-true r01 (suc (2 ·ℕ k)) (odd-gen-below-r01 k)

  α₂-even-true : (k : ℕ) → α₂ (2 ·ℕ k) ≡ true
  α₂-even-true k = gen-absorb→bit-true r10 (2 ·ℕ k) (even-gen-below-r10 k)

  go : NFC.isFiniteOrCofinite α₁ → NFC.isFiniteOrCofinite α₂ → ⊥
  -- Both cofinite: product of cofinite elements is cofinite, hence nonzero
  go (NFC.Cof c₁) (NFC.Cof c₂) = NFC.Finite≢Cofinite (α₁ NFC.∧ α₂) fin-prod cof-prod
    where
    -- r01 · r10 = 0, so φ_FC(r01) · φ_FC(r10) = 0, meaning α₁ ∧ α₂ is finite (= zero = constant0)
    prod-zero : FC._·_ (fst Bridge.φ_FC r01) (fst Bridge.φ_FC r10) ≡ FC.𝟘
    prod-zero =
      FC._·_ (fst Bridge.φ_FC r01) (fst Bridge.φ_FC r10)
        ≡⟨ sym (IsCommRingHom.pres· (snd Bridge.φ_FC) r01 r10) ⟩
      fst Bridge.φ_FC (r01 ·∞ r10)
        ≡⟨ cong (fst Bridge.φ_FC) r01·r10≡0 ⟩
      fst Bridge.φ_FC 𝟘∞
        ≡⟨ IsCommRingHom.pres0 (snd Bridge.φ_FC) ⟩
      FC.𝟘 ∎
    fin-prod : NFC.isFinite (α₁ NFC.∧ α₂)
    fin-prod = NFC.constant0 (λ k _ → funExt⁻ (cong fst prod-zero) k)
    cof-prod : NFC.isCofinite (α₁ NFC.∧ α₂)
    cof-prod = let NFC.Cof c = NFC.FinCofin-∧-cl α₁ α₂ (NFC.Cof c₁) (NFC.Cof c₂) in c
  -- r01 finite: bounded support, but α₁(2k+1) = true for all k → contradiction
  go (NFC.Fin fin₁) _ = bound-contradiction fin₁
    where
    bound-contradiction : NFC.isFinite α₁ → ⊥
    bound-contradiction fin₁ =
      let (N , bound) = NFC.finite→Bounded α₁ fin₁
          -- Pick k = N, so 2k+1 = 2N+1 ≥ N
          k = N
          big-enough : N ≤ suc (2 ·ℕ k)
          big-enough = suc (N +ℕ 0) , cong suc (+-comm (N +ℕ 0) N)
          α₁-false : α₁ (suc (2 ·ℕ k)) ≡ false
          α₁-false = bound (suc (2 ·ℕ k)) big-enough
          α₁-true : α₁ (suc (2 ·ℕ k)) ≡ true
          α₁-true = α₁-odd-true k
      in true≢false (sym α₁-true ∙ α₁-false)
  -- r10 finite: bounded support, but α₂(2k) = true for all k → contradiction
  go _ (NFC.Fin fin₂) = bound-contradiction fin₂
    where
    bound-contradiction : NFC.isFinite α₂ → ⊥
    bound-contradiction fin₂ =
      let (N , bound) = NFC.finite→Bounded α₂ fin₂
          k = N
          big-enough : N ≤ 2 ·ℕ k
          big-enough = (N +ℕ 0) , +-comm (N +ℕ 0) N
          α₂-false : α₂ (2 ·ℕ k) ≡ false
          α₂-false = bound (2 ·ℕ k) big-enough
          α₂-true : α₂ (2 ·ℕ k) ≡ true
          α₂-true = α₂-even-true k
      in true≢false (sym α₂-true ∙ α₂-false)
