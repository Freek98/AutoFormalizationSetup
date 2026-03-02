{-# OPTIONS --cubical --guardedness #-}

module work.Part11 where

open import work.Part10b public

import Cubical.HITs.PropositionalTruncation as PT

-- Compact Hausdorff Spaces (tex Definition at line 1898)

module CompactHausdorffModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)

  record hasCHausStr (X : Type₀) : Type₁ where
    field
      isSetX : isSet X
      equalityClosed : (x y : X) → isClosedProp ((x ≡ y) , isSetX x y)
      stoneCover : ∥ Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → X) ] isSurjection q ∥₁

  CHaus : Type₁
  CHaus = Σ[ X ∈ Type₀ ] hasCHausStr X

  Stone→CHaus : Stone → CHaus
  Stone→CHaus S = fst S , record
    { isSetX = hasStoneStr→isSet S
    ; equalityClosed = StoneEqualityClosed S
    ; stoneCover = ∣ S , (λ x → x) , (λ x → ∣ x , refl ∣₁) ∣₁
    }
    where
    open StoneEqualityClosedModule

-- CompactHausdorffClosed (tex Lemma 1906)

module CompactHausdorffClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedModule

  CompactHausdorffClosed-backward : (X : CHaus) (S : Stone)
    → (q : fst S → fst X) → isSurjection q
    → (B : fst S → hProp ℓ-zero) → ((s : fst S) → isClosedProp (B s))
    → (x : fst X) → isClosedProp (∥ Σ[ s ∈ fst S ] fst (B s) × (q s ≡ x) ∥₁ , squash₁)
  CompactHausdorffClosed-backward X S q q-surj B B-closed x = InhabitedClosedSubSpaceClosed S Aₓ Aₓ-closed
    where
    open hasCHausStr (snd X)
    Aₓ : fst S → hProp ℓ-zero
    Aₓ s = (fst (B s) × (q s ≡ x)) , isProp× (snd (B s)) (isSetX (q s) x)

    Aₓ-closed : (s : fst S) → isClosedProp (Aₓ s)
    Aₓ-closed s = closedAnd (B s) ((q s ≡ x) , isSetX (q s) x) (B-closed s) (equalityClosed (q s) x)

-- InhabitedClosedSubSpaceClosedCHaus (tex Corollary 1930)

module InhabitedClosedSubSpaceClosedCHausModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedModule
  open StoneEqualityClosedModule

  InhabitedClosedSubSpaceClosedCHaus : (X : CHaus)
    → (A : fst X → hProp ℓ-zero) → ((x : fst X) → isClosedProp (A x))
    → isClosedProp (∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁)
  InhabitedClosedSubSpaceClosedCHaus X A A-closed =
    PT.rec (isPropIsClosedProp {∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁}) construct (hasCHausStr.stoneCover (snd X))
    where
    open hasCHausStr (snd X)

    construct : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
              → isClosedProp (∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁)
    construct (S , q , q-surj) = closedEquiv ∥ΣSB∥₁ ∥ΣXA∥₁ forward backward ∥ΣSB∥₁-closed
      where
      B : fst S → hProp ℓ-zero
      B s = A (q s)

      B-closed : (s : fst S) → isClosedProp (B s)
      B-closed s = A-closed (q s)

      ∥ΣSB∥₁ : hProp ℓ-zero
      ∥ΣSB∥₁ = ∥ Σ[ s ∈ fst S ] fst (B s) ∥₁ , squash₁

      ∥ΣSB∥₁-closed : isClosedProp ∥ΣSB∥₁
      ∥ΣSB∥₁-closed = InhabitedClosedSubSpaceClosed S B B-closed

      ∥ΣXA∥₁ : hProp ℓ-zero
      ∥ΣXA∥₁ = ∥ Σ[ x ∈ fst X ] fst (A x) ∥₁ , squash₁

      forward : fst ∥ΣSB∥₁ → fst ∥ΣXA∥₁
      forward = PT.map (λ { (s , Bs) → q s , Bs })

      backward : fst ∥ΣXA∥₁ → fst ∥ΣSB∥₁
      backward = PT.rec squash₁ (λ { (x , Ax) →
        PT.map (λ { (s , qs≡x) → s , subst (λ y → fst (A y)) (sym qs≡x) Ax }) (q-surj x) })

-- AllOpenSubspaceOpen (tex Corollary 1967)

module AllOpenSubspaceOpenModule where
  open CompactHausdorffModule
  open InhabitedClosedSubSpaceClosedCHausModule

  AllOpenSubspaceOpen : (X : CHaus)
    → (U : fst X → hProp ℓ-zero) → ((x : fst X) → isOpenProp (U x))
    → isOpenProp (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x)))
  AllOpenSubspaceOpen X U Uopen = PT.rec squash₁ go exists-¬U-closed
    where
    ¬U : fst X → hProp ℓ-zero
    ¬U x = ¬hProp (U x)

    ¬Uclosed : (x : fst X) → isClosedProp (¬U x)
    ¬Uclosed x = negOpenIsClosed (U x) (Uopen x)

    exists-¬U : hProp ℓ-zero
    exists-¬U = ∥ Σ[ x ∈ fst X ] (¬ fst (U x)) ∥₁ , squash₁

    exists-¬U-closed : isClosedProp exists-¬U
    exists-¬U-closed = InhabitedClosedSubSpaceClosedCHaus X ¬U ¬Uclosed

    ¬exists-¬U : hProp ℓ-zero
    ¬exists-¬U = ¬hProp exists-¬U

    forward : ((x : fst X) → fst (U x)) → fst ¬exists-¬U
    forward all-U exists-¬U' = PT.rec isProp⊥ (λ { (x , ¬Ux) → ¬Ux (all-U x) }) exists-¬U'

    backward : fst ¬exists-¬U → (x : fst X) → fst (U x)
    backward ¬∃¬U x = openIsStable mp (U x) (Uopen x) (λ ¬Ux → ¬∃¬U ∣ x , ¬Ux ∣₁)

    go : Σ[ β ∈ binarySequence ] ⟨ exists-¬U ⟩ ↔ ((n : ℕ) → β n ≡ false)
       → isOpenProp (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x)))
    go (β , β-fwd , β-bwd) = openEquiv ¬exists-¬U (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x)))
              backward forward (negClosedIsOpen mp exists-¬U β (β-fwd , β-bwd))

-- CHausFiniteIntersectionProperty (tex Lemma 1981)

module CHausFiniteIntersectionPropertyModule where
  open CompactHausdorffModule
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Axioms.StoneDuality using (Stone; hasStoneStr; Booleω; Sp)
  open import Cubical.Data.Nat.Bijections.Product using (ℕ×ℕ≅ℕ)
  open ClosedInStoneIsStoneModule using (closedFamilyChoice)
  open SDDecToElemModule
  open StoneClosedSubsetsModule
  -- finJoinBR and 0≡1-quotient→1∈ideal are now top-level in Part09
  import Cubical.Algebra.CommRing.Quotient.ImageQuotient as IQ
  open import CommRingQuotients.IdealTerms using (isInIdeal; isImage; iszero; isSum; isMul; idealDecomp)
  import QuotientBool as QB
  open import Cubical.Algebra.CommRing using (_$cr_; CommRingStr; IsCommRingHom; CommRing→Ring)
  open import Cubical.Algebra.BooleanRing using (BooleanRing; BooleanRingStr; BoolHom; BooleanRing→CommRing; module BooleanAlgebraStr)
  open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
  open import Cubical.Algebra.Ring.Properties using (module RingTheory)
  open import Cubical.Data.Nat using (ℕ; zero; suc; max; snotz; injSuc) renaming (_+_ to _+ℕ_; _∸_ to _∸ℕ_)
  open import Cubical.Data.Nat.Order using (_≤_; _<_; left-≤-max; right-≤-max; ≤-refl; ≤-suc; ≤-trans; pred-≤-pred; ≤-∸-+-cancel)
  open import Cubical.Foundations.Transport using (transportTransport⁻)
  open import Cubical.Foundations.Equiv using (equivFun)
  open import Cubical.Data.Empty as ⊥ using (⊥)
  import Cubical.HITs.PropositionalTruncation as PT

  finiteIntersectionClosed : {X : Type₀}
    → (C : ℕ → (X → hProp ℓ-zero))
    → (n : ℕ)
    → X → hProp ℓ-zero
  finiteIntersectionClosed C zero x = C zero x
  finiteIntersectionClosed C (suc n) x =
    (fst (C (suc n) x) × fst (finiteIntersectionClosed C n x)) ,
    isProp× (snd (C (suc n) x)) (snd (finiteIntersectionClosed C n x))

  countableIntersectionClosed : {X : Type₀}
    → (C : ℕ → (X → hProp ℓ-zero))
    → X → hProp ℓ-zero
  countableIntersectionClosed C x =
    ((n : ℕ) → fst (C n x)) , isPropΠ (λ n → snd (C n x))

  -- Extract C n x from the finite intersection C₀ ∩ ... ∩ C_k
  allC : {X : Type₀} (C : ℕ → (X → hProp ℓ-zero))
       → (k : ℕ) (x : X) → fst (finiteIntersectionClosed C k x) → (n : ℕ) → n ≤ k → fst (C n x)
  allC C zero x p n (zero , q) = subst (λ m → fst (C m x)) (sym q) p
  allC C zero x p n (suc j , q) = ⊥.rec (snotz q)
  allC C (suc k) x (csk , fink) n (zero , q) = subst (λ m → fst (C m x)) (sym q) csk
  allC C (suc k) x (csk , fink) n (suc j , q) = allC C k x fink n (j , injSuc q)

  CHausFiniteIntersectionProperty : (X : CHaus)
    → (C : ℕ → (fst X → hProp ℓ-zero))
    → ((n : ℕ) → (x : fst X) → isClosedProp (C n x))
    → ((x : fst X) → ¬ fst (countableIntersectionClosed C x))
    → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁
  CHausFiniteIntersectionProperty X C C-closed allEmpty =
    PT.rec squash₁ fromCover (hasCHausStr.stoneCover (snd X))
    where
    open hasCHausStr (snd X)

    fromCover : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
              → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁
    fromCover (S , q , q-surj) =
      PT.rec squash₁ fromWitnesses combined
      where
      C' : ℕ → fst S → hProp ℓ-zero
      C' n s = C n (q s)

      C'-closed : (n : ℕ) (s : fst S) → isClosedProp (C' n s)
      C'-closed n s = C-closed n (q s)

      combined : ∥ ((n : ℕ) → (s : fst S) → Σ[ α ∈ binarySequence ] fst (C' n s) ↔ ((m : ℕ) → α m ≡ false)) ∥₁
      combined = countableChoice _ (λ n → closedFamilyChoice S (C' n) (C'-closed n))

      fromWitnesses : ((n : ℕ) → (s : fst S) → Σ[ α ∈ binarySequence ] fst (C' n s) ↔ ((m : ℕ) → α m ≡ false))
                    → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁
      fromWitnesses wit = PT.rec squash₁ fromIdealMem idealMem
        where
        -- Stone duality data
        Bω : Booleω
        Bω = fst (snd S)
        B : BooleanRing ℓ-zero
        B = fst Bω
        SpB≡S = snd (snd S)

        -- For each (n,m), the decidable predicate and its Boolean ring element
        α-pred : ℕ → ℕ → Sp Bω → Bool
        α-pred n m x = fst (wit n (transport SpB≡S x)) m

        elem : ℕ → ℕ → ⟨ B ⟩
        elem n m = elemFromDecPred sd-axiom Bω (α-pred n m)

        elem-prop : (n m : ℕ) (x : Sp Bω) → fst x (elem n m) ≡ α-pred n m x
        elem-prop n m x = decPred-elem-correspondence sd-axiom Bω (α-pred n m) x

        -- Encode ℕ×ℕ as ℕ
        enc : ℕ × ℕ → ℕ
        enc = Iso.fun ℕ×ℕ≅ℕ

        dec : ℕ → ℕ × ℕ
        dec = Iso.inv ℕ×ℕ≅ℕ

        dec-enc : (p : ℕ × ℕ) → dec (enc p) ≡ p
        dec-enc = Iso.ret ℕ×ℕ≅ℕ

        -- Combined sequence d : ℕ → ⟨B⟩ encoding all (n,m) pairs
        d : ℕ → ⟨ B ⟩
        d k = elem (fst (dec k)) (snd (dec k))

        d-at : (n m : ℕ) → d (enc (n , m)) ≡ elem n m
        d-at n m = cong (λ p → elem (fst p) (snd p)) (dec-enc (n , m))

        -- Quotient B/d and its spectrum
        B/d-Booleω : Booleω
        B/d-Booleω = B QB./Im d , quotientBySeqHasBooleω Bω d

        open SpOfQuotientBySeq B d using (Sp-quotient-≃)

        -- Sp(B/d) is empty (corresponds to ∩_n C_n = ∅)
        spEmpty : Sp B/d-Booleω → ⊥
        spEmpty sp-hom =
          let (x , allZero) = equivFun Sp-quotient-≃ sp-hom
              s = transport SpB≡S x
          in allEmpty (q s) (λ n →
            snd (snd (wit n s)) (λ m →
              α-pred n m x
                ≡⟨ sym (elem-prop n m x) ⟩
              fst x (elem n m)
                ≡⟨ cong (fst x) (sym (d-at n m)) ⟩
              fst x (d (enc (n , m)))
                ≡⟨ allZero (enc (n , m)) ⟩
              false ∎))

        -- 0 ≡ 1 in B/d
        0≡1 : BooleanRingStr.𝟘 (snd (fst B/d-Booleω)) ≡ BooleanRingStr.𝟙 (snd (fst B/d-Booleω))
        0≡1 = SpectrumEmptyImpliesTrivial.0≡1-in-B sd-axiom B/d-Booleω spEmpty

        -- 1 ∈ ideal(d)
        1∈ideal : IQ.generatedIdeal (BooleanRing→CommRing B) d
                    (CommRingStr.1r (snd (BooleanRing→CommRing B)))
        1∈ideal = 0≡1-quotient→1∈ideal B d 0≡1

        idealMem : ∥ isInIdeal (BooleanRing→CommRing B) d
                       (CommRingStr.1r (snd (BooleanRing→CommRing B))) ∥₁
        idealMem = idealDecomp (BooleanRing→CommRing B) d _ 1∈ideal

        -- Algebraic abbreviations
        private
          module BA = BooleanAlgebraStr B
          R = BooleanRing→CommRing B
          module CRS = CommRingStr (snd R)
          𝟘B = BooleanRingStr.𝟘 (snd B)
          𝟙B = BooleanRingStr.𝟙 (snd B)
          _∨B_ = BA._∨_
          _·B_ = CRS._·_
          _+B_ = CRS._+_
          fJ = finJoinBR B
          _∨Bool_ = BooleanAlgebraStr._∨_ BoolBR

        -- r · fJ d N = r  →  r · fJ d (suc N) = r
        leq-suc : {r : ⟨ B ⟩} (N : ℕ) → r ·B fJ d N ≡ r → r ·B fJ d (suc N) ≡ r
        leq-suc {r} N p =
          r ·B (d N ∨B fJ d N)
            ≡⟨ sym (cong (_·B (d N ∨B fJ d N)) p) ⟩
          (r ·B fJ d N) ·B (d N ∨B fJ d N)
            ≡⟨ sym (CRS.·Assoc r (fJ d N) (d N ∨B fJ d N)) ⟩
          r ·B (fJ d N ·B (d N ∨B fJ d N))
            ≡⟨ cong (r ·B_) (cong (fJ d N ·B_) BA.∨Comm) ⟩
          r ·B (fJ d N ·B (fJ d N ∨B d N))
            ≡⟨ cong (r ·B_) BA.∧AbsorbL∨ ⟩
          r ·B fJ d N
            ≡⟨ p ⟩
          r ∎

        leq-extend : {r : ⟨ B ⟩} (N k : ℕ) → r ·B fJ d N ≡ r → r ·B fJ d (k +ℕ N) ≡ r
        leq-extend N zero p = p
        leq-extend N (suc k) p = leq-suc (k +ℕ N) (leq-extend N k p)

        leq-max-left : {r : ⟨ B ⟩} (N₁ N₂ : ℕ) → r ·B fJ d N₁ ≡ r → r ·B fJ d (max N₁ N₂) ≡ r
        leq-max-left {r} N₁ N₂ p =
          subst (λ M → r ·B fJ d M ≡ r) (≤-∸-+-cancel {N₁} {max N₁ N₂} (left-≤-max {N₁} {N₂}))
                (leq-extend N₁ (max N₁ N₂ ∸ℕ N₁) p)

        leq-max-right : {r : ⟨ B ⟩} (N₁ N₂ : ℕ) → r ·B fJ d N₂ ≡ r → r ·B fJ d (max N₁ N₂) ≡ r
        leq-max-right {r} N₁ N₂ p =
          subst (λ M → r ·B fJ d M ≡ r) (≤-∸-+-cancel {N₂} {max N₁ N₂} (right-≤-max {N₂} {N₁}))
                (leq-extend N₂ (max N₁ N₂ ∸ℕ N₂) p)

        idealBound : {r : ⟨ B ⟩} → isInIdeal R d r → Σ[ N ∈ ℕ ] (r ·B fJ d N ≡ r)
        idealBound (isImage r n p) = suc n ,
          (r ·B (d n ∨B fJ d n)
            ≡⟨ cong (λ z → z ·B (d n ∨B fJ d n)) (sym p) ⟩
          d n ·B (d n ∨B fJ d n)
            ≡⟨ BA.∧AbsorbL∨ ⟩
          d n
            ≡⟨ p ⟩
          r ∎)
        idealBound (iszero r p) = zero ,
          (r ·B 𝟘B
            ≡⟨ cong (λ z → z ·B 𝟘B) (sym p) ⟩
          𝟘B ·B 𝟘B
            ≡⟨ RingTheory.0LeftAnnihilates (CommRing→Ring R) 𝟘B ⟩
          𝟘B
            ≡⟨ p ⟩
          r ∎)
        idealBound (isSum r s t r=s+t sI tI) =
          let (N₁ , p₁) = idealBound sI
              (N₂ , p₂) = idealBound tI
              M = max N₁ N₂
          in M ,
            (r ·B fJ d M
              ≡⟨ cong (_·B fJ d M) r=s+t ⟩
            (s +B t) ·B fJ d M
              ≡⟨ CRS.·Comm (s +B t) (fJ d M) ⟩
            fJ d M ·B (s +B t)
              ≡⟨ CRS.·DistR+ (fJ d M) s t ⟩
            (fJ d M ·B s) +B (fJ d M ·B t)
              ≡⟨ cong₂ _+B_ (CRS.·Comm (fJ d M) s) (CRS.·Comm (fJ d M) t) ⟩
            (s ·B fJ d M) +B (t ·B fJ d M)
              ≡⟨ cong₂ _+B_ (leq-max-left {s} N₁ N₂ p₁) (leq-max-right {t} N₁ N₂ p₂) ⟩
            s +B t
              ≡⟨ sym r=s+t ⟩
            r ∎)
        idealBound (isMul r s t r=st tI) =
          let (N , p) = idealBound tI
          in N ,
            (r ·B fJ d N
              ≡⟨ cong (_·B fJ d N) r=st ⟩
            (s ·B t) ·B fJ d N
              ≡⟨ sym (CRS.·Assoc s t (fJ d N)) ⟩
            s ·B (t ·B fJ d N)
              ≡⟨ cong (s ·B_) p ⟩
            s ·B t
              ≡⟨ sym r=st ⟩
            r ∎)

        -- BoolHom preserves ∨
        boolhom-∨ : (x : Sp Bω) (a b : ⟨ B ⟩) → fst x (a ∨B b) ≡ fst x a ∨Bool fst x b
        boolhom-∨ x a b =
          let _+S_ = CommRingStr._+_ (snd (BooleanRing→CommRing BoolBR))
          in fst x (a ∨B b)
            ≡⟨ IsCommRingHom.pres+ (snd x) (a +B b) (a ·B b) ⟩
          fst x (a +B b) +S fst x (a ·B b)
            ≡⟨ cong₂ _+S_ (IsCommRingHom.pres+ (snd x) a b) (IsCommRingHom.pres· (snd x) a b) ⟩
          fst x a ∨Bool fst x b ∎

        -- If all d(k) for k<N map to false, then fJ d N maps to false
        finJoin-false : (x : Sp Bω) (N : ℕ) → ((k : ℕ) → k < N → fst x (d k) ≡ false)
                      → fst x (fJ d N) ≡ false
        finJoin-false x zero _ = IsCommRingHom.pres0 (snd x)
        finJoin-false x (suc n) h =
          fst x (d n ∨B fJ d n)
            ≡⟨ boolhom-∨ x (d n) (fJ d n) ⟩
          fst x (d n) ∨Bool fst x (fJ d n)
            ≡⟨ cong₂ _∨Bool_ (h n ≤-refl) (finJoin-false x n (λ k k<n → h k (≤-suc k<n))) ⟩
          false ∎

        -- Max of first coordinates of dec(0),...,dec(N-1)
        maxFst : ℕ → ℕ
        maxFst zero = 0
        maxFst (suc k) = max (fst (dec k)) (maxFst k)

        open import Cubical.Data.Nat.Properties using (+-suc)

        maxFst-bound : (N k : ℕ) → k < N → fst (dec k) ≤ maxFst N
        maxFst-bound zero k (j , p) = ⊥.rec (snotz (sym (+-suc j k) ∙ p))
        maxFst-bound (suc N) k k<sN with pred-≤-pred k<sN
        ... | (zero , p) = subst (λ j → fst (dec j) ≤ maxFst (suc N)) (sym p) (left-≤-max {fst (dec N)} {maxFst N})
        ... | (suc j , p) = ≤-trans (maxFst-bound N k (j , +-suc j k ∙ p)) (right-≤-max {maxFst N} {fst (dec N)})

        -- From isInIdeal 1, construct the finite bound
        fromIdealMem : isInIdeal R d CRS.1r
                     → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁
        fromIdealMem iI = ∣ K , conclusion ∣₁
          where
          N = fst (idealBound iI)
          fJ-eq : fJ d N ≡ 𝟙B
          fJ-eq =
            fJ d N        ≡⟨ sym (CRS.·IdL (fJ d N)) ⟩
            𝟙B ·B fJ d N ≡⟨ snd (idealBound iI) ⟩
            𝟙B ∎

          K : ℕ
          K = maxFst N

          conclusion : (x : fst X) → ¬ fst (finiteIntersectionClosed C K x)
          conclusion x finK =
            PT.rec isProp⊥ (λ { (s , qs≡x) → contradiction s qs≡x }) (q-surj x)
            where
            contradiction : (s : fst S) → q s ≡ x → ⊥
            contradiction s qs≡x = true≢false contra
              where
              x' : Sp Bω
              x' = transport (sym SpB≡S) s

              x'-has-Cn : (n : ℕ) → n ≤ K → fst (C n (q s))
              x'-has-Cn n n≤K = allC C K (q s) (subst (λ y → fst (finiteIntersectionClosed C K y)) (sym qs≡x) finK) n n≤K

              x'-d-false : (k : ℕ) → k < N → fst x' (d k) ≡ false
              x'-d-false k k<N =
                let n₀ = fst (dec k)
                    m₀ = snd (dec k)
                    n₀≤K : n₀ ≤ K
                    n₀≤K = maxFst-bound N k k<N
                    cn₀ : fst (C n₀ (q s))
                    cn₀ = x'-has-Cn n₀ n₀≤K
                    all-false : (m : ℕ) → fst (wit n₀ s) m ≡ false
                    all-false = fst (snd (wit n₀ s)) cn₀
                in fst x' (d k)
                  ≡⟨ elem-prop n₀ m₀ x' ⟩
                α-pred n₀ m₀ x'
                  ≡⟨ cong (λ z → fst (wit n₀ z) m₀) (transportTransport⁻ SpB≡S s) ⟩
                fst (wit n₀ s) m₀
                  ≡⟨ all-false m₀ ⟩
                false ∎

              contra : true ≡ false
              contra =
                true
                  ≡⟨ sym (IsCommRingHom.pres1 (snd x')) ⟩
                fst x' 𝟙B
                  ≡⟨ cong (fst x') (sym fJ-eq) ⟩
                fst x' (fJ d N)
                  ≡⟨ finJoin-false x' N x'-d-false ⟩
                false ∎

-- ChausMapsPreserveIntersectionOfClosed (tex Corollary 2003)

module ChausMapsPreserveIntersectionOfClosedModule where
  open CompactHausdorffModule
  open CHausFiniteIntersectionPropertyModule
  open InhabitedClosedSubSpaceClosedCHausModule
  open import Cubical.Foundations.Univalence using (hPropExt)

  imageSubset : {X Y : Type₀} → (f : X → Y)
    → (A : X → hProp ℓ-zero) → Y → hProp ℓ-zero
  imageSubset f A y = ∥ Σ[ x ∈ _ ] fst (A x) × (f x ≡ y) ∥₁ , squash₁

  isDecreasingSeq : {X : Type₀}
    → (G : ℕ → (X → hProp ℓ-zero)) → Type₀
  isDecreasingSeq {X} G = (n : ℕ) → (x : X) → fst (G (suc n) x) → fst (G n x)

  ChausMapsPreserveIntersectionOfClosed : (X Y : CHaus)
    → (f : fst X → fst Y)
    → (G : ℕ → (fst X → hProp ℓ-zero))
    → ((n : ℕ) → (x : fst X) → isClosedProp (G n x))
    → isDecreasingSeq G
    → (y : fst Y)
    → fst (imageSubset f (countableIntersectionClosed G) y)
      ≡ fst (countableIntersectionClosed (λ n → imageSubset f (G n)) y)
  ChausMapsPreserveIntersectionOfClosed X Y f G G-closed G-decr y =
    hPropExt squash₁ (isPropΠ (λ _ → squash₁)) forward backward
    where
    isSetY : isSet (fst Y)
    isSetY = hasCHausStr.isSetX (snd Y)

    forward : fst (imageSubset f (countableIntersectionClosed G) y)
            → fst (countableIntersectionClosed (λ n → imageSubset f (G n)) y)
    forward = PT.rec (isPropΠ (λ _ → squash₁))
      λ { (x , allG , fx≡y) n → ∣ x , allG n , fx≡y ∣₁ }

    backward : fst (countableIntersectionClosed (λ n → imageSubset f (G n)) y)
             → fst (imageSubset f (countableIntersectionClosed G) y)
    backward hyp = closedIsStable target-prop target-closed ¬¬target
      where
      -- C_n(x) = G_n(x) ∧ (f x ≡ y)
      C : ℕ → (fst X → hProp ℓ-zero)
      C n x = (fst (G n x) × (f x ≡ y)) , isProp× (snd (G n x)) (isSetY (f x) y)

      C-closed : (n : ℕ) → (x : fst X) → isClosedProp (C n x)
      C-closed n x = closedAnd (G n x) ((f x ≡ y) , isSetY (f x) y)
                       (G-closed n x) (hasCHausStr.equalityClosed (snd Y) (f x) y)

      -- Build finite intersection witness from G_k witness + decreasingness
      buildFinInt : (k : ℕ) (x : fst X)
                  → fst (G k x) → f x ≡ y
                  → fst (finiteIntersectionClosed C k x)
      buildFinInt zero x gkx fx≡y = gkx , fx≡y
      buildFinInt (suc k) x gkx fx≡y =
        (gkx , fx≡y) , buildFinInt k x (G-decr k x gkx) fx≡y

      -- Each finite intersection is nonempty
      finInt-nonempty : (k : ℕ) → ¬ ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x))
      finInt-nonempty k allEmpty-k =
        PT.rec isProp⊥
          (λ { (x , gkx , fx≡y) → allEmpty-k x (buildFinInt k x gkx fx≡y) })
          (hyp k)

      -- Countable intersection is nonempty (contrapositive of CHausFIP)
      ¬countInt-empty : ¬ ((x : fst X) → ¬ fst (countableIntersectionClosed C x))
      ¬countInt-empty allEmpty =
        PT.rec isProp⊥
          (λ { (k , finEmpty-k) → finInt-nonempty k finEmpty-k })
          (CHausFiniteIntersectionProperty X C C-closed allEmpty)

      target-prop : hProp ℓ-zero
      target-prop = imageSubset f (countableIntersectionClosed G) y

      -- ∥ Σ x. (∀n. G_n x) × (f x ≡ y) ∥₁ is closed
      A-bwd : fst X → hProp ℓ-zero
      A-bwd x = (((n : ℕ) → fst (G n x)) × (f x ≡ y)) ,
                isProp× (isPropΠ (λ n → snd (G n x))) (isSetY (f x) y)

      A-bwd-closed : (x : fst X) → isClosedProp (A-bwd x)
      A-bwd-closed x = closedAnd
        (countableIntersectionClosed G x)
        ((f x ≡ y) , isSetY (f x) y)
        (closedCountableIntersection (λ n → G n x) (λ n → G-closed n x))
        (hasCHausStr.equalityClosed (snd Y) (f x) y)

      target-closed : isClosedProp target-prop
      target-closed = InhabitedClosedSubSpaceClosedCHaus X A-bwd A-bwd-closed

      ¬¬target : ¬ ¬ fst target-prop
      ¬¬target ¬tgt = ¬countInt-empty λ x countInt-C-x →
        ¬tgt ∣ x , (λ n → fst (countInt-C-x n)) , snd (countInt-C-x 0) ∣₁

-- CompactHausdorffTopology (tex Corollary 2019)

module CompactHausdorffTopologyModule where
  open CompactHausdorffModule
  open CompactHausdorffClosedModule
  open ChausMapsPreserveIntersectionOfClosedModule
  open CHausFiniteIntersectionPropertyModule using (countableIntersectionClosed)
  open ClosedInStoneIsStoneModule using (closedFamilyChoice)
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Axioms.StoneDuality using (Stone)
  open import Cubical.Data.Bool using (not; _and_)
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Foundations.Univalence using (hPropExt)
  open import Cubical.Data.Empty as ⊥ using (⊥)
  import Cubical.HITs.PropositionalTruncation as PT

  private
    -- Cumulative conjunction: D₀ ∧ D₁ ∧ ... ∧ D_n
    cumAnd : {A : Type₀} (D : ℕ → A → Bool) → ℕ → A → Bool
    cumAnd D zero s = D zero s
    cumAnd D (suc n) s = D (suc n) s and cumAnd D n s

    cumAnd-decr : {A : Type₀} (D : ℕ → A → Bool) (n : ℕ) (s : A)
      → cumAnd D (suc n) s ≡ true → cumAnd D n s ≡ true
    cumAnd-decr D n s eq with D (suc n) s
    ... | true = eq
    ... | false = ⊥.rec (true≢false (sym eq))

    cumAnd-extract : {A : Type₀} (D : ℕ → A → Bool) (n : ℕ) (s : A)
      → cumAnd D n s ≡ true → D n s ≡ true
    cumAnd-extract D zero s eq = eq
    cumAnd-extract D (suc n) s eq with D (suc n) s
    ... | true = refl
    ... | false = ⊥.rec (true≢false (sym eq))

    all-to-cumAnd : {A : Type₀} (D : ℕ → A → Bool) (n : ℕ) (s : A)
      → ((k : ℕ) → D k s ≡ true) → cumAnd D n s ≡ true
    all-to-cumAnd D zero s hyp = hyp zero
    all-to-cumAnd D (suc n) s hyp =
      subst (λ b → b and cumAnd D n s ≡ true) (sym (hyp (suc n)))
        (all-to-cumAnd D n s hyp)

  -- Closed characterization: backward direction
  -- If A = ∩_n q(D_n) for decidable D_n, then A is closed
  CHTopClosed-backward : (X : CHaus) (S : Stone)
    → (q : fst S → fst X) → isSurjection q
    → (D : ℕ → fst S → Bool) → (y : fst X)
    → isClosedProp (((n : ℕ) → ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁) ,
                    isPropΠ (λ _ → squash₁))
  CHTopClosed-backward X S q q-surj D y = closedCountableIntersection
    (λ n → ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁ , squash₁)
    (λ n → CompactHausdorffClosed-backward X S q q-surj
      (λ s → (D n s ≡ true) , isSetBool _ _) (λ s → Bool-equality-closed (D n s) true) y)

  -- Closed characterization: forward direction
  -- If A is closed, then ∃ D_n decidable with A(y) ≡ ∩_n q(D_n)(y)
  CHTopClosed-forward : (X : CHaus) (S : Stone)
    → (q : fst S → fst X) → isSurjection q
    → (A : fst X → hProp ℓ-zero) → ((x : fst X) → isClosedProp (A x))
    → ∥ Σ[ D ∈ (ℕ → fst S → Bool) ]
         ((y : fst X) → fst (A y) ≡ ((n : ℕ) → ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁)) ∥₁
  CHTopClosed-forward X S q q-surj A A-closed =
    PT.rec squash₁ (λ w → ∣ construct w ∣₁) (closedFamilyChoice S A' A'-closed)
    where
    A' : fst S → hProp ℓ-zero
    A' s = A (q s)

    A'-closed : (s : fst S) → isClosedProp (A' s)
    A'-closed s = A-closed (q s)

    construct : ((s : fst S) → Σ[ α ∈ binarySequence ] fst (A' s) ↔ ((n : ℕ) → α n ≡ false))
              → Σ[ D ∈ (ℕ → fst S → Bool) ]
                  ((y : fst X) → fst (A y) ≡ ((n : ℕ) → ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁))
    construct witness = E , characterization
      where
      α : fst S → binarySequence
      α s = fst (witness s)

      α-fwd : (s : fst S) → fst (A (q s)) → (n : ℕ) → α s n ≡ false
      α-fwd s = fst (snd (witness s))

      α-bwd : (s : fst S) → ((n : ℕ) → α s n ≡ false) → fst (A (q s))
      α-bwd s = snd (snd (witness s))

      -- D_n(s) = not(α(s,n)), so D_n(s) = true ↔ α(s,n) = false
      D : ℕ → fst S → Bool
      D n s = not (α s n)

      D-true→α-false : (n : ℕ) (s : fst S) → D n s ≡ true → α s n ≡ false
      D-true→α-false n s eq with α s n
      ... | false = refl
      ... | true = ⊥.rec (true≢false (sym eq))

      α-false→D-true : (n : ℕ) (s : fst S) → α s n ≡ false → D n s ≡ true
      α-false→D-true n s eq with α s n
      ... | false = refl
      ... | true = ⊥.rec (true≢false eq)

      -- Output: cumulative intersection (decreasing and decidable)
      E : ℕ → fst S → Bool
      E = cumAnd D

      -- hProp version for CMPIC
      G : ℕ → (fst S → hProp ℓ-zero)
      G n s = (E n s ≡ true) , isSetBool _ _

      G-closed : (n : ℕ) → (s : fst S) → isClosedProp (G n s)
      G-closed n s = Bool-equality-closed (E n s) true

      G-decr : isDecreasingSeq G
      G-decr n s = cumAnd-decr D n s

      -- ∩_n G_n(s) ↔ A'(s)
      countG→A' : (s : fst S) → ((n : ℕ) → fst (G n s)) → fst (A' s)
      countG→A' s hyp = α-bwd s (λ n → D-true→α-false n s (cumAnd-extract D n s (hyp n)))

      A'→countG : (s : fst S) → fst (A' s) → (n : ℕ) → fst (G n s)
      A'→countG s a's n = all-to-cumAnd D n s (λ k → α-false→D-true k s (α-fwd s a's k))

      -- A(y) → imageSubset q (∩_n G) y
      A→img : (y : fst X) → fst (A y)
        → fst (imageSubset q (countableIntersectionClosed G) y)
      A→img y ay = PT.rec squash₁
        (λ (s , qs≡y) → ∣ s , A'→countG s (subst (fst ∘ A) (sym qs≡y) ay) , qs≡y ∣₁)
        (q-surj y)

      -- imageSubset q (∩_n G) y → A(y)
      img→A : (y : fst X) → fst (imageSubset q (countableIntersectionClosed G) y) → fst (A y)
      img→A y = PT.rec (snd (A y))
        (λ (s , allG , qs≡y) → subst (fst ∘ A) qs≡y (countG→A' s allG))

      -- CMPIC: q(∩_n G) = ∩_n q(G_n)
      cmpic : (y : fst X)
        → fst (imageSubset q (countableIntersectionClosed G) y)
          ≡ fst (countableIntersectionClosed (λ n → imageSubset q (G n)) y)
      cmpic = ChausMapsPreserveIntersectionOfClosed (Stone→CHaus S) X q G G-closed G-decr

      characterization : (y : fst X) → fst (A y)
        ≡ ((n : ℕ) → ∥ Σ[ s ∈ fst S ] (E n s ≡ true) × (q s ≡ y) ∥₁)
      characterization y = hPropExt (snd (A y)) (isPropΠ (λ _ → squash₁))
        (λ ay → transport (cmpic y) (A→img y ay))
        (λ hyp → img→A y (transport (sym (cmpic y)) hyp))

  -- Open characterization: backward direction
  -- If A = ∪_n ¬q(D_n) for decidable D_n, then A is open
  CHTopOpen-backward : (X : CHaus) (S : Stone)
    → (q : fst S → fst X) → isSurjection q
    → (D : ℕ → fst S → Bool) → (y : fst X)
    → isOpenProp (∥ Σ[ n ∈ ℕ ] (¬ ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁) ∥₁ , squash₁)
  CHTopOpen-backward X S q q-surj D y = openCountableUnion
    (λ n → (¬ ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁) , isPropΠ (λ _ → isProp⊥))
    (λ n → PT.rec squash₁
      (λ (β , fwd , bwd) → negClosedIsOpen mp
        (∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁ , squash₁) β (fwd , bwd))
      (CompactHausdorffClosed-backward X S q q-surj
        (λ s → (D n s ≡ true) , isSetBool _ _) (λ s → Bool-equality-closed (D n s) true) y))

  -- Open characterization: forward direction
  -- If A is open, then ∃ D_n decidable with A(y) ≡ ∪_n ¬q(D_n)(y)
  CHTopOpen-forward : (X : CHaus) (S : Stone)
    → (q : fst S → fst X) → isSurjection q
    → (A : fst X → hProp ℓ-zero) → ((x : fst X) → isOpenProp (A x))
    → ∥ Σ[ D ∈ (ℕ → fst S → Bool) ]
         ((y : fst X) → fst (A y) ≡ ∥ Σ[ n ∈ ℕ ] (¬ ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁) ∥₁) ∥₁
  CHTopOpen-forward X S q q-surj A A-open =
    PT.rec squash₁ open-construct (CHTopClosed-forward X S q q-surj ¬A ¬A-closed)
    where
    ¬A : fst X → hProp ℓ-zero
    ¬A x = ¬hProp (A x)

    ¬A-closed : (x : fst X) → isClosedProp (¬A x)
    ¬A-closed x = negOpenIsClosed (A x) (A-open x)

    open-construct : Σ[ E ∈ (ℕ → fst S → Bool) ]
                       ((y : fst X) → (¬ fst (A y)) ≡ ((n : ℕ) → ∥ Σ[ s ∈ fst S ] (E n s ≡ true) × (q s ≡ y) ∥₁))
                   → ∥ Σ[ D ∈ (ℕ → fst S → Bool) ]
                       ((y : fst X) → fst (A y) ≡ ∥ Σ[ n ∈ ℕ ] (¬ ∥ Σ[ s ∈ fst S ] (D n s ≡ true) × (q s ≡ y) ∥₁) ∥₁) ∥₁
    open-construct (E , char) = ∣ E , open-char ∣₁
      where
      qE : ℕ → fst X → hProp ℓ-zero
      qE n y = ∥ Σ[ s ∈ fst S ] (E n s ≡ true) × (q s ≡ y) ∥₁ , squash₁

      qE-closed : (n : ℕ) (y : fst X) → isClosedProp (qE n y)
      qE-closed n y = CompactHausdorffClosed-backward X S q q-surj
        (λ s → (E n s ≡ true) , isSetBool _ _) (λ s → Bool-equality-closed (E n s) true) y

      markov : (y : fst X) → (¬ ((n : ℕ) → fst (qE n y))) ↔ ∥ Σ[ n ∈ ℕ ] (¬ fst (qE n y)) ∥₁
      markov y = closedMarkovTex (λ n → qE n y) (λ n → qE-closed n y)

      open-char : (y : fst X) → fst (A y) ≡ ∥ Σ[ n ∈ ℕ ] (¬ fst (qE n y)) ∥₁
      open-char y = hPropExt (snd (A y)) squash₁ fwd bwd
        where
        fwd : fst (A y) → ∥ Σ[ n ∈ ℕ ] (¬ fst (qE n y)) ∥₁
        fwd ay = fst (markov y) (λ allqE → transport (sym (char y)) allqE ay)

        bwd : ∥ Σ[ n ∈ ℕ ] (¬ fst (qE n y)) ∥₁ → fst (A y)
        bwd ex = openIsStable mp (A y) (A-open y)
          (λ ¬ay → snd (markov y) ex (transport (char y) ¬ay))

-- CHausSeperationOfClosedByOpens (tex Lemma 2058)

module CHausSeperationOfClosedByOpensModule where
  open CompactHausdorffModule
  open CompactHausdorffClosedModule
  open StoneSeparatedModule
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Axioms.StoneDuality using (Stone; hasStoneStr)

  areDisjoint : {X : Type₀}
    → (A B : X → hProp ℓ-zero) → Type₀
  areDisjoint {X} A B = (x : X) → ¬ (fst (A x) × fst (B x))

  subsetOf : {X : Type₀}
    → (A B : X → hProp ℓ-zero) → Type₀
  subsetOf {X} A B = (x : X) → fst (A x) → fst (B x)

  CHausSeperationOfClosedByOpens : (X : CHaus)
    → (A B : fst X → hProp ℓ-zero)
    → ((x : fst X) → isClosedProp (A x))
    → ((x : fst X) → isClosedProp (B x))
    → areDisjoint A B
    → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
        ((x : fst X) → isOpenProp (U x)) ×
        ((x : fst X) → isOpenProp (V x)) ×
        subsetOf A U × subsetOf B V × areDisjoint U V ∥₁
  CHausSeperationOfClosedByOpens X A B A-closed B-closed AB-disjoint =
    PT.rec squash₁ fromCover (hasCHausStr.stoneCover (snd X))
    where
    open hasCHausStr (snd X)

    fromCover : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
              → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
                  ((x : fst X) → isOpenProp (U x)) ×
                  ((x : fst X) → isOpenProp (V x)) ×
                  subsetOf A U × subsetOf B V × areDisjoint U V ∥₁
    fromCover (S , q , q-surj) = PT.rec squash₁ fromSeparator separated
      where
      -- Pull back A and B to S
      A' : fst S → hProp ℓ-zero
      A' s = A (q s)

      B' : fst S → hProp ℓ-zero
      B' s = B (q s)

      A'-closed : (s : fst S) → isClosedProp (A' s)
      A'-closed s = A-closed (q s)

      B'-closed : (s : fst S) → isClosedProp (B' s)
      B'-closed s = B-closed (q s)

      A'B'-disjoint : ClosedSubsetsDisjoint S (A' , A'-closed) (B' , B'-closed)
      A'B'-disjoint s a'x b'x = AB-disjoint (q s) (a'x , b'x)

      separated : ∥ Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S (A' , A'-closed) D) × (ClosedSubNotDec S (B' , B'-closed) D) ∥₁
      separated = StoneSeparated S (A' , A'-closed) (B' , B'-closed) A'B'-disjoint

      fromSeparator : Σ[ D ∈ DecSubsetOfStone S ] (ClosedSubDec S (A' , A'-closed) D) × (ClosedSubNotDec S (B' , B'-closed) D)
                    → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
                        ((x : fst X) → isOpenProp (U x)) ×
                        ((x : fst X) → isOpenProp (V x)) ×
                        subsetOf A U × subsetOf B V × areDisjoint U V ∥₁
      fromSeparator (D , D-sep-A , D-sep-B) = ∣ U , V , U-open , V-open , A⊆U , B⊆V , UV-disjoint ∣₁
        where
        -- D-subset: {s : S | D s = true}
        D-true : fst S → hProp ℓ-zero
        D-true s = (D s ≡ true) , isSetBool (D s) true

        D-false : fst S → hProp ℓ-zero
        D-false s = (D s ≡ false) , isSetBool (D s) false

        D-true-closed : (s : fst S) → isClosedProp (D-true s)
        D-true-closed s = Bool-equality-closed (D s) true

        D-false-closed : (s : fst S) → isClosedProp (D-false s)
        D-false-closed s = Bool-equality-closed (D s) false

        -- q(D) and q(¬D) as closed subsets of X
        qD : fst X → hProp ℓ-zero
        qD x = ∥ Σ[ s ∈ fst S ] (D s ≡ true) × (q s ≡ x) ∥₁ , squash₁

        q¬D : fst X → hProp ℓ-zero
        q¬D x = ∥ Σ[ s ∈ fst S ] (D s ≡ false) × (q s ≡ x) ∥₁ , squash₁

        qD-closed : (x : fst X) → isClosedProp (qD x)
        qD-closed = CompactHausdorffClosed-backward X S q q-surj D-true D-true-closed

        q¬D-closed : (x : fst X) → isClosedProp (q¬D x)
        q¬D-closed = CompactHausdorffClosed-backward X S q q-surj D-false D-false-closed

        -- U = ¬q(¬D), V = ¬q(D)
        U : fst X → hProp ℓ-zero
        U x = ¬hProp (q¬D x)

        V : fst X → hProp ℓ-zero
        V x = ¬hProp (qD x)

        U-open : (x : fst X) → isOpenProp (U x)
        U-open x = PT.rec squash₁
          (λ (β , fwd , bwd) → negClosedIsOpen mp (q¬D x) β (fwd , bwd))
          (q¬D-closed x)

        V-open : (x : fst X) → isOpenProp (V x)
        V-open x = PT.rec squash₁
          (λ (β , fwd , bwd) → negClosedIsOpen mp (qD x) β (fwd , bwd))
          (qD-closed x)

        -- A ⊆ U: if x ∈ A, then ¬∃s, D(s)=false ∧ q(s)=x
        A⊆U : subsetOf A U
        A⊆U x ax = PT.rec isProp⊥ λ { (s , ds≡false , qs≡x) →
          true≢false (sym (D-sep-A s (subst (λ y → fst (A y)) (sym qs≡x) ax)) ∙ ds≡false) }

        -- B ⊆ V: if x ∈ B, then ¬∃s, D(s)=true ∧ q(s)=x
        B⊆V : subsetOf B V
        B⊆V x bx = PT.rec isProp⊥ λ { (s , ds≡true , qs≡x) →
          true≢false (sym ds≡true ∙ D-sep-B s (subst (λ y → fst (B y)) (sym qs≡x) bx)) }

        -- U ∩ V = ∅: ¬q(¬D)(x) ∧ ¬q(D)(x) → ⊥
        UV-disjoint : areDisjoint U V
        UV-disjoint x (ux , vx) = PT.rec isProp⊥ helper (q-surj x)
          where
          helper : Σ[ s ∈ fst S ] q s ≡ x → ⊥
          helper (s , qs≡x) = case-bool (D s) refl
            where
            case-bool : (b : Bool) → D s ≡ b → ⊥
            case-bool true  eq = vx ∣ s , eq , qs≡x ∣₁
            case-bool false eq = ux ∣ s , eq , qs≡x ∣₁

-- SigmaCompactHausdorff (tex Lemma 2098)

module SigmaCompactHausdorffModule where
  open CompactHausdorffModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Cubical.Foundations.Equiv using (equivFun; invEq; retEq)
  open StoneAsClosedSubsetOfCantorModule
  open StoneProductModule
  open ClosedSigmaClosedDerived
  open CantorIsStoneModule
  open ClosedInStoneIsStoneModule using (ClosedInStoneIsStone; closedFamilyChoice)

  SigmaCHausType : (X : CHaus) → (Y : fst X → CHaus) → Type₀
  SigmaCHausType X Y = Σ[ x ∈ fst X ] fst (Y x)

  SigmaCompactHausdorff : (X : CHaus) (Y : fst X → CHaus)
    → hasCHausStr (SigmaCHausType X Y)
  SigmaCompactHausdorff X Y = record
    { isSetX = isSetΣXY
    ; equalityClosed = σ-eq-closed
    ; stoneCover = σ-stoneCover
    }
    where
    open hasCHausStr (snd X) renaming (isSetX to isSetXbase; equalityClosed to X-eq-cl; stoneCover to X-sc)

    isSetΣXY : isSet (SigmaCHausType X Y)
    isSetΣXY = isSetΣ isSetXbase (λ x → hasCHausStr.isSetX (snd (Y x)))

    -- Equality in Σ X Y is closed (tex ClosedDependentSums 1785)
    σ-eq-closed : (σ₁ σ₂ : SigmaCHausType X Y)
      → isClosedProp ((σ₁ ≡ σ₂) , isSetΣXY σ₁ σ₂)
    σ-eq-closed (x₁ , y₁) (x₂ , y₂) =
      closedEquiv
        (∥ Σ[ p ∈ x₁ ≡ x₂ ] PathP (λ i → fst (Y (p i))) y₁ y₂ ∥₁ , squash₁)
        (((x₁ , y₁) ≡ (x₂ , y₂)) , isSetΣXY (x₁ , y₁) (x₂ , y₂))
        (PT.rec (isSetΣXY _ _) (λ { (p , q) → ΣPathP (p , q) }))
        (λ eq → ∣ cong fst eq , cong snd eq ∣₁)
        trunc-sigma-closed
      where
      eq-x-closed : isClosedProp ((x₁ ≡ x₂) , isSetXbase x₁ x₂)
      eq-x-closed = X-eq-cl x₁ x₂

      pathP-closed : (p : x₁ ≡ x₂) → isClosedProp (PathP (λ i → fst (Y (p i))) y₁ y₂ ,
                       isOfHLevelPathP' 1 (hasCHausStr.isSetX (snd (Y x₂))) y₁ y₂)
      pathP-closed p = closedEquiv
        ((subst (λ z → fst (Y z)) p y₁ ≡ y₂) , hasCHausStr.isSetX (snd (Y x₂)) _ _)
        (PathP (λ i → fst (Y (p i))) y₁ y₂ ,
         isOfHLevelPathP' 1 (hasCHausStr.isSetX (snd (Y x₂))) y₁ y₂)
        toPathP fromPathP
        (hasCHausStr.equalityClosed (snd (Y x₂)) (subst (λ z → fst (Y z)) p y₁) y₂)

      trunc-sigma-closed : isClosedProp (∥ Σ[ p ∈ x₁ ≡ x₂ ] PathP (λ i → fst (Y (p i))) y₁ y₂ ∥₁ , squash₁)
      trunc-sigma-closed = closedSigmaClosed-derived
        ((x₁ ≡ x₂) , isSetXbase x₁ x₂) eq-x-closed
        (λ p → PathP (λ i → fst (Y (p i))) y₁ y₂ ,
               isOfHLevelPathP' 1 (hasCHausStr.isSetX (snd (Y x₂))) y₁ y₂)
        pathP-closed

    -- Stone cover of Σ X Y (tex proof of Lemma 2098)
    -- Uses localChoice with Type₀ encoding of closed subsets (binary sequences)
    σ-stoneCover : ∥ Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → SigmaCHausType X Y) ] isSurjection q ∥₁
    σ-stoneCover = PT.rec squash₁ build-cover X-sc
      where
      build-cover : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
        → ∥ Σ[ S' ∈ Stone ] Σ[ q' ∈ (fst S' → SigmaCHausType X Y) ] isSurjection q' ∥₁
      build-cover (S_X , q_X , surj_X) =
        PT.rec squash₁ build-from-lc
          (localChoice-axiom (fst (snd S_X)) P' P'-all)
        where
        p_X : Sp (fst (snd S_X)) ≡ fst S_X
        p_X = snd (snd S_X)

        -- Type₀ encoding: binary sequence per Cantor point + surjection to Y(q_X s)
        FiberData : fst S_X → Type₀
        FiberData s = Σ[ enc ∈ (CantorSpace → binarySequence) ]
                      Σ[ f ∈ ((Σ[ γ ∈ CantorSpace ] ((n : ℕ) → enc γ n ≡ false)) → fst (Y (q_X s))) ]
                      isSurjection f

        FiberData-all : (s : fst S_X) → ∥ FiberData s ∥₁
        FiberData-all s = PT.rec squash₁ step1 (hasCHausStr.stoneCover (snd (Y (q_X s))))
          where
          step1 : Σ[ T ∈ Stone ] Σ[ r ∈ (fst T → fst (Y (q_X s))) ] isSurjection r
                → ∥ FiberData s ∥₁
          step1 (T_s , r_s , surj_s) = PT.rec squash₁ step2 (Stone→ClosedInCantor T_s)
            where
            step2 : Σ[ A ∈ ClosedSubsetOfCantor ] (fst T_s ≃ (Σ[ γ ∈ CantorSpace ] fst (fst A γ)))
                  → ∥ FiberData s ∥₁
            step2 (A , equiv) = PT.map step3
              (closedFamilyChoice (CantorSpace , CantorIsStone) (fst A) (snd A))
              where
              step3 : ((γ : CantorSpace) → Σ[ β ∈ binarySequence ] fst (fst A γ) ↔ ((n : ℕ) → β n ≡ false))
                    → FiberData s
              step3 witness = enc , g , g-surj
                where
                enc : CantorSpace → binarySequence
                enc γ = fst (witness γ)
                toA : (γ : CantorSpace) → ((n : ℕ) → enc γ n ≡ false) → fst (fst A γ)
                toA γ = snd (snd (witness γ))
                fromA : (γ : CantorSpace) → fst (fst A γ) → ((n : ℕ) → enc γ n ≡ false)
                fromA γ = fst (snd (witness γ))
                g : (Σ[ γ ∈ CantorSpace ] ((n : ℕ) → enc γ n ≡ false)) → fst (Y (q_X s))
                g (γ , prf) = r_s (invEq equiv (γ , toA γ prf))
                g-surj : isSurjection g
                g-surj y = PT.map (λ { (t , rt≡y) →
                  let γ' = fst (equivFun equiv t)
                      a = snd (equivFun equiv t)
                  in (γ' , fromA γ' a) ,
                    (r_s (invEq equiv (γ' , toA γ' (fromA γ' a)))
                      ≡⟨ cong (λ z → r_s (invEq equiv (γ' , z))) (snd (fst A γ') _ _) ⟩
                     r_s (invEq equiv (equivFun equiv t))
                      ≡⟨ cong r_s (retEq equiv t) ⟩
                     r_s t
                      ≡⟨ rt≡y ⟩
                     y ∎)
                  }) (surj_s y)

        P' : Sp (fst (snd S_X)) → Type₀
        P' h = FiberData (transport p_X h)

        P'-all : (h : Sp (fst (snd S_X))) → ∥ P' h ∥₁
        P'-all h = FiberData-all (transport p_X h)

        build-from-lc :
          Σ[ Dlc ∈ Booleω ] Σ[ φ ∈ (Sp Dlc → Sp (fst (snd S_X))) ]
            (isSurjectiveSpMap {fst (snd S_X)} {Dlc} φ × ((t : Sp Dlc) → P' (φ t)))
          → ∥ Σ[ S' ∈ Stone ] Σ[ q' ∈ (fst S' → SigmaCHausType X Y) ] isSurjection q' ∥₁
        build-from-lc (Dlc , φ , surjφ , datT) =
          ∣ total-Stone , total-map , total-surj ∣₁
          where
          qT : Sp Dlc → fst S_X
          qT t = transport p_X (φ t)

          enc-of : (t : Sp Dlc) → CantorSpace → binarySequence
          enc-of t = fst (datT t)

          f-of : (t : Sp Dlc) → (Σ[ γ ∈ CantorSpace ] ((n : ℕ) → enc-of t γ n ≡ false))
               → fst (Y (q_X (qT t)))
          f-of t = fst (snd (datT t))

          surj-f : (t : Sp Dlc) → isSurjection (f-of t)
          surj-f t = snd (snd (datT t))

          SpDlc-Stone : Stone
          SpDlc-Stone = Sp Dlc , Dlc , refl

          product-Stone : Stone
          product-Stone = Sp Dlc × CantorSpace , StoneProduct SpDlc-Stone (CantorSpace , CantorIsStone)

          C-pred : Sp Dlc × CantorSpace → hProp ℓ-zero
          C-pred (t , γ) = ((n : ℕ) → enc-of t γ n ≡ false) , isPropΠ (λ _ → isSetBool _ _)

          C-closed : (p : Sp Dlc × CantorSpace) → isClosedProp (C-pred p)
          C-closed (t , γ) = closedCountableIntersection
            (λ n → (enc-of t γ n ≡ false) , isSetBool _ _)
            (λ n → Bool-equality-closed (enc-of t γ n) false)

          total-Stone : Stone
          total-Stone = Σ (Sp Dlc × CantorSpace) (λ p → fst (C-pred p)) ,
                        ClosedInStoneIsStone product-Stone C-pred C-closed

          total-map : fst total-Stone → SigmaCHausType X Y
          total-map ((t , γ) , prf) = q_X (qT t) , f-of t (γ , prf)

          total-surj : isSurjection total-map
          total-surj (x , y) = PT.rec squash₁
            (λ { (s , qs≡x) → PT.rec squash₁
              (λ { (t , φt≡h) →
                let qt≡s : qT t ≡ s
                    qt≡s = cong (transport p_X) φt≡h ∙ transportTransport⁻ p_X s
                    path-to-x : q_X (qT t) ≡ x
                    path-to-x = cong q_X qt≡s ∙ qs≡x
                    y' : fst (Y (q_X (qT t)))
                    y' = subst (λ z → fst (Y z)) (sym path-to-x) y
                in PT.map
                  (λ { ((γ , prf) , fac≡y') →
                    ((t , γ) , prf) , ΣPathP (path-to-x , toPathP (
                      subst (λ z → fst (Y z)) path-to-x (f-of t (γ , prf))
                        ≡⟨ cong (subst (λ z → fst (Y z)) path-to-x) fac≡y' ⟩
                      subst (λ z → fst (Y z)) path-to-x (subst (λ z → fst (Y z)) (sym path-to-x) y)
                        ≡⟨ transportTransport⁻ (cong (λ z → fst (Y z)) path-to-x) y ⟩
                      y ∎))
                  }) (surj-f t y')
              }) (surjφ (transport (sym p_X) s))
            }) (surj_X x)

  CHausΣ : (X : CHaus) → (Y : fst X → CHaus) → CHaus
  CHausΣ X Y = SigmaCHausType X Y , SigmaCompactHausdorff X Y

-- AlgebraCompactHausdorffCountablyPresented (tex Lemma 2112)

module AlgebraCompactHausdorffCountablyPresentedModule where
  open CompactHausdorffModule
  open AllOpenSubspaceOpenModule
  open ODiscAxioms
  open import Axioms.StoneDuality using (2^; Stone; hasStoneStr; SDHomVersion)
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Cubical.Relation.Nullary using (Dec; yes; no)
  open import Cubical.Data.Bool using (_≟_)
  open import Cubical.HITs.PropositionalTruncation.Properties using (rec→Set)

  -- Helper: if P is closed and Q is decidable, (P → Q) is open
  closedImplDecIsOpen : (P Q : hProp ℓ-zero) → isClosedProp P → Dec ⟨ Q ⟩
    → isOpenProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
  closedImplDecIsOpen P Q Pclosed (yes q) =
    ∣ (λ _ → true) , (λ _ → 0 , refl) , (λ _ _ → q) ∣₁
  closedImplDecIsOpen P Q Pclosed (no ¬q) = PT.rec squash₁ go Pclosed
    where
    go : Σ[ α ∈ binarySequence ] ⟨ P ⟩ ↔ ((n : ℕ) → α n ≡ false)
       → isOpenProp ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
    go (α , P→∀ , ∀→P) = openEquiv (¬hProp P)
      ((⟨ P ⟩ → ⟨ Q ⟩) , isPropΠ (λ _ → snd Q))
      (λ ¬p p → ex-falso (¬p p))
      (λ f p → ¬q (f p))
      (negClosedIsOpen mp P α (P→∀ , ∀→P))

  AlgebraCompactHausdorffCountablyPresented : (X : CHaus)
    → ∥ has-Boole-ω' (2^ (fst X)) ∥₁
  AlgebraCompactHausdorffCountablyPresented X =
    PT.rec squash₁ go (hasCHausStr.stoneCover (snd X))
    where
    go : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
       → ∥ has-Boole-ω' (2^ (fst X)) ∥₁
    go (S , q , q-surj) = ODiscBAareBoole (2^ (fst X)) 2^X-isODisc
      where
      B : Booleω
      B = fst (snd S)
      p : Sp B ≡ fst S
      p = snd (snd S)

      -- (fst S → Bool) is ODisc via Stone duality
      2^S-isODisc : isODisc (fst S → Bool)
      2^S-isODisc = isODisc-path
        (ua (fst (SDHomVersion sd-axiom B)) ∙ cong (λ T → T → Bool) p)
        (BooleIsODisc B)

      -- compatibility predicate
      compatible : (fst S → Bool) → Type ℓ-zero
      compatible b = (s t : fst S) → q s ≡ q t → b s ≡ b t

      isProp-compatible : (b : fst S → Bool) → isProp (compatible b)
      isProp-compatible b =
        isPropΠ λ s → isPropΠ λ t → isPropΠ λ _ → isSetBool (b s) (b t)

      -- each (q s ≡ q t → b s ≡ b t) is open
      S-CHaus : CHaus
      S-CHaus = Stone→CHaus S

      impl-open : (b : fst S → Bool) (s t : fst S)
        → isOpenProp ((q s ≡ q t → b s ≡ b t) , isPropΠ (λ _ → isSetBool (b s) (b t)))
      impl-open b s t = closedImplDecIsOpen
        ((q s ≡ q t) , hasCHausStr.isSetX (snd X) (q s) (q t))
        ((b s ≡ b t) , isSetBool (b s) (b t))
        (hasCHausStr.equalityClosed (snd X) (q s) (q t))
        ((b s) ≟ (b t))

      -- compatible b is open for each b
      compatible-open : (b : fst S → Bool)
        → isOpenProp (compatible b , isProp-compatible b)
      compatible-open b = AllOpenSubspaceOpen S-CHaus
        (λ s → ((t : fst S) → q s ≡ q t → b s ≡ b t) ,
               isPropΠ λ t → isPropΠ λ _ → isSetBool (b s) (b t))
        (λ s → AllOpenSubspaceOpen S-CHaus
          (λ t → (q s ≡ q t → b s ≡ b t) ,
                 isPropΠ (λ _ → isSetBool (b s) (b t)))
          (λ t → impl-open b s t))

      -- (fst X → Bool) ≃ Σ (fst S → Bool) compatible
      fwd : (fst X → Bool) → Σ[ b ∈ (fst S → Bool) ] compatible b
      fwd a = (λ s → a (q s)) , (λ s t e → cong a e)

      bwd : (Σ[ b ∈ (fst S → Bool) ] compatible b) → fst X → Bool
      bwd (b , comp) x = rec→Set isSetBool
        (λ { (s , _) → b s })
        (λ { (s₁ , p₁) (s₂ , p₂) → comp s₁ s₂ (p₁ ∙ sym p₂) })
        (q-surj x)

      fwd-bwd : (bc : Σ[ b ∈ (fst S → Bool) ] compatible b) → fwd (bwd bc) ≡ bc
      fwd-bwd (b , comp) = Σ≡Prop isProp-compatible (funExt λ s →
        PT.elim
          {P = λ w → rec→Set isSetBool
                       (λ { (s' , _) → b s' })
                       (λ { (s₁ , p₁) (s₂ , p₂) → comp s₁ s₂ (p₁ ∙ sym p₂) })
                       w
                     ≡ b s}
          (λ _ → isSetBool _ _)
          (λ { (s' , p') → comp s' s p' }) (q-surj (q s)))

      bwd-fwd : (a : fst X → Bool) → bwd (fwd a) ≡ a
      bwd-fwd a = funExt λ x →
        PT.elim
          {P = λ w → rec→Set isSetBool
                       (λ { (s , _) → a (q s) })
                       (λ { (s₁ , p₁) (s₂ , p₂) → cong a (p₁ ∙ sym p₂) })
                       w
                     ≡ a x}
          (λ _ → isSetBool _ _)
          (λ { (s , e) → cong a e }) (q-surj x)

      2^X≃Σ : (fst X → Bool) ≃ (Σ[ b ∈ (fst S → Bool) ] compatible b)
      2^X≃Σ = isoToEquiv (iso fwd bwd fwd-bwd bwd-fwd)

      -- Σ (fst S → Bool) compatible is ODisc
      Σ-isODisc : isODisc (Σ[ b ∈ (fst S → Bool) ] (compatible b))
      Σ-isODisc = OdiscSigma 2^S-isODisc
        (λ b → PropOpenIffOdisc (compatible b , isProp-compatible b) (compatible-open b))

      -- (fst X → Bool) is ODisc
      2^X-isODisc : isODisc (fst X → Bool)
      2^X-isODisc = isODisc-path (sym (ua 2^X≃Σ)) Σ-isODisc

-- ConnectedComponentModule (tex 2138-2171)

module ConnectedComponentModule where
  open CompactHausdorffModule
  open AlgebraCompactHausdorffCountablyPresentedModule
  open import Axioms.StoneDuality using (2^)
  open import CountablyPresentedBooleanRings.PresentedBoole using (has-Boole-ω'; BooleanEquivToHomInv)
  open import BooleanRing.FreeBooleanRing.FreeBool using (freeBA; generator)
  open import BooleanRing.FreeBooleanRing.freeBATerms using (equalityFromEqualityOnGenerators)
  open import QuotientBool using (quotientImageHom; quotientImageHomSurjective; _/Im_)
  open import Cubical.Algebra.CommRing using (_∘cr_; IsCommRingHom)
  open import Cubical.Algebra.BooleanRing using (BoolHom)
  open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
  open import Cubical.Functions.Surjection using (isSurjection)
  open import Cubical.Foundations.Univalence using (hPropExt)
  open import Cubical.Foundations.Equiv using (equivFun; invEq; retEq)
  import Cubical.HITs.PropositionalTruncation as PT
  open CHausFiniteIntersectionPropertyModule
  open import Cubical.Data.Bool using (_and_)

  DecSubsetCHaus : CHaus → Type₀
  DecSubsetCHaus X = fst X → Bool

  inDec : (X : CHaus) → fst X → DecSubsetCHaus X → Type₀
  inDec X x D = D x ≡ true

  ConnectedComponent : (X : CHaus) → fst X → fst X → hProp ℓ-zero
  ConnectedComponent X x y =
    ((D : DecSubsetCHaus X) → inDec X x D → inDec X y D) ,
    isPropΠ (λ D → isPropΠ (λ _ → isSetBool (D y) true))

  private
    bool-eq : Bool → Bool → Bool
    bool-eq true  true  = true
    bool-eq true  false = false
    bool-eq false true  = false
    bool-eq false false = true

    bool-eq-refl : (b : Bool) → bool-eq b b ≡ true
    bool-eq-refl true  = refl
    bool-eq-refl false = refl

    bool-eq-eq : (a b : Bool) → bool-eq a b ≡ true → a ≡ b
    bool-eq-eq true  true  _ = refl
    bool-eq-eq true  false p = sym p
    bool-eq-eq false true  p = p
    bool-eq-eq false false _ = refl

  -- tex Lemma 2144 (ConnectedComponentClosedInCompactHausdorff)
  ConnectedComponentClosedInCompactHausdorff : (X : CHaus) (x : fst X)
    → ∥ Σ[ D ∈ (ℕ → DecSubsetCHaus X) ]
        ((y : fst X) → fst (ConnectedComponent X x y)
          ≡ ((n : ℕ) → inDec X y (D n))) ∥₁
  ConnectedComponentClosedInCompactHausdorff X x =
    PT.rec squash₁ construct (AlgebraCompactHausdorffCountablyPresented X)
    where
    construct : has-Boole-ω' (2^ (fst X))
      → ∥ Σ[ D ∈ (ℕ → DecSubsetCHaus X) ]
          ((y : fst X) → fst (ConnectedComponent X x y)
            ≡ ((n : ℕ) → inDec X y (D n))) ∥₁
    construct (rel , equiv) = ∣ D , proof ∣₁
      where
      Q = freeBA ℕ /Im rel

      inv-hom : BoolHom Q (2^ (fst X))
      inv-hom = BooleanEquivToHomInv (2^ (fst X)) Q equiv

      Φ : BoolHom (freeBA ℕ) (2^ (fst X))
      Φ = inv-hom ∘cr quotientImageHom

      g : ℕ → DecSubsetCHaus X
      g n = fst Φ (generator n)

      D : ℕ → DecSubsetCHaus X
      D n y = bool-eq (g n x) (g n y)

      open IsCommRingHom

      ev : fst X → BoolHom (2^ (fst X)) BoolBR
      fst (ev z) h = h z
      pres0 (snd (ev z)) = refl
      pres1 (snd (ev z)) = refl
      pres+ (snd (ev z)) _ _ = refl
      pres· (snd (ev z)) _ _ = refl
      pres- (snd (ev z)) _ = refl

      proof : (y : fst X) → fst (ConnectedComponent X x y)
            ≡ ((n : ℕ) → inDec X y (D n))
      proof y = hPropExt
        (isPropΠ (λ _ → isPropΠ (λ _ → isSetBool _ _)))
        (isPropΠ (λ _ → isSetBool _ _))
        forward backward
        where
        forward : fst (ConnectedComponent X x y) → (n : ℕ) → inDec X y (D n)
        forward qxy n = qxy (D n) (bool-eq-refl (g n x))

        backward : ((n : ℕ) → inDec X y (D n)) → fst (ConnectedComponent X x y)
        backward allDn E Ex≡true =
          PT.rec (isSetBool _ _) step (quotientImageHomSurjective (equivFun (fst equiv) E))
          where
          gn-eq : (n : ℕ) → g n x ≡ g n y
          gn-eq n = bool-eq-eq (g n x) (g n y) (allDn n)

          hom-eq : ev x ∘cr Φ ≡ ev y ∘cr Φ
          hom-eq = equalityFromEqualityOnGenerators BoolBR (ev x ∘cr Φ) (ev y ∘cr Φ) gn-eq

          step : Σ[ t ∈ ⟨ freeBA ℕ ⟩ ] fst quotientImageHom t ≡ equivFun (fst equiv) E
               → E y ≡ true
          step (t , qt≡q) =
            E y
              ≡⟨ cong (λ h → h y) (sym Φt≡E) ⟩
            fst Φ t y
              ≡⟨ sym (funExt⁻ (cong fst hom-eq) t) ⟩
            fst Φ t x
              ≡⟨ cong (λ h → h x) Φt≡E ⟩
            E x
              ≡⟨ Ex≡true ⟩
            true ∎
            where
            Φt≡E : fst Φ t ≡ E
            Φt≡E = cong (invEq (fst equiv)) qt≡q ∙ retEq (fst equiv) E

  -- tex Lemma 2156 (ConnectedComponentSubOpenHasDecidableInbetween)
  ConnectedComponentSubOpenHasDecidableInbetween : (X : CHaus) (x : fst X)
    → (U : fst X → hProp ℓ-zero) → ((y : fst X) → isOpenProp (U y))
    → ((y : fst X) → fst (ConnectedComponent X x y) → fst (U y))
    → ∥ Σ[ E ∈ DecSubsetCHaus X ] inDec X x E × ((y : fst X) → inDec X y E → fst (U y)) ∥₁
  ConnectedComponentSubOpenHasDecidableInbetween X x U Uopen Qx⊆U =
    PT.rec squash₁ construct (ConnectedComponentClosedInCompactHausdorff X x)
    where
    construct : Σ[ D ∈ (ℕ → DecSubsetCHaus X) ]
        ((y : fst X) → fst (ConnectedComponent X x y) ≡ ((n : ℕ) → inDec X y (D n)))
      → ∥ Σ[ E ∈ DecSubsetCHaus X ] inDec X x E × ((y : fst X) → inDec X y E → fst (U y)) ∥₁
    construct (D , Deq) = PT.rec squash₁ fromK getK
      where
      C : ℕ → (fst X → hProp ℓ-zero)
      C n y = ((D n y ≡ true) × (¬ fst (U y))) ,
              isProp× (isSetBool _ _) (isPropΠ (λ _ → isProp⊥))

      C-closed : (n : ℕ) → (y : fst X) → isClosedProp (C n y)
      C-closed n y = closedAnd ((D n y ≡ true) , isSetBool _ _) (¬hProp (U y))
                     (Bool-equality-closed (D n y) true) (negOpenIsClosed (U y) (Uopen y))

      countInt-empty : (y : fst X) → ¬ fst (countableIntersectionClosed C y)
      countInt-empty y allCn = snd (allCn 0) (Qx⊆U y qxy)
        where
        qxy : fst (ConnectedComponent X x y)
        qxy = transport (sym (Deq y)) (λ n → fst (allCn n))

      getK : ∥ Σ[ k ∈ ℕ ] ((y : fst X) → ¬ fst (finiteIntersectionClosed C k y)) ∥₁
      getK = CHausFiniteIntersectionProperty X C C-closed countInt-empty

      finBoolAnd : ℕ → fst X → Bool
      finBoolAnd zero y = D zero y
      finBoolAnd (suc j) y = D (suc j) y and finBoolAnd j y

      and-true-l : (a b : Bool) → a and b ≡ true → a ≡ true
      and-true-l true  _ _ = refl
      and-true-l false _ p = p

      and-true-r : (a b : Bool) → a and b ≡ true → b ≡ true
      and-true-r true  _ p = p
      and-true-r false _ p = ex-falso (false≢true p)

      build-finInt : (j : ℕ) (y : fst X)
        → finBoolAnd j y ≡ true → ¬ fst (U y) → fst (finiteIntersectionClosed C j y)
      build-finInt zero y p ¬Uy = p , ¬Uy
      build-finInt (suc j) y p ¬Uy =
        (and-true-l (D (suc j) y) (finBoolAnd j y) p , ¬Uy) ,
        build-finInt j y (and-true-r (D (suc j) y) (finBoolAnd j y) p) ¬Uy

      fromK : Σ[ k ∈ ℕ ] ((y : fst X) → ¬ fst (finiteIntersectionClosed C k y))
        → ∥ Σ[ E ∈ DecSubsetCHaus X ] inDec X x E × ((y : fst X) → inDec X y E → fst (U y)) ∥₁
      fromK (k , kEmpty) = ∣ finBoolAnd k , x-in-E , E-sub-U ∣₁
        where
        x-in-all-D : (n : ℕ) → D n x ≡ true
        x-in-all-D = transport (Deq x) (λ _ xInD → xInD)

        x-in-E : inDec X x (finBoolAnd k)
        x-in-E = go k
          where
          go : (j : ℕ) → finBoolAnd j x ≡ true
          go zero = x-in-all-D 0
          go (suc j) = cong₂ _and_ (x-in-all-D (suc j)) (go j)

        E-sub-U : (y : fst X) → inDec X y (finBoolAnd k) → fst (U y)
        E-sub-U y Ey = openIsStable mp (U y) (Uopen y) ¬¬Uy
          where
          ¬¬Uy : ¬ ¬ fst (U y)
          ¬¬Uy ¬Uy = kEmpty y (build-finInt k y Ey ¬Uy)

-- ConnectedComponentConnectedModule (tex Lemma 2173)

module ConnectedComponentConnectedModule where
  open CompactHausdorffModule
  open ConnectedComponentModule
  open CHausSeperationOfClosedByOpensModule
    using (CHausSeperationOfClosedByOpens; areDisjoint; subsetOf)
  open ClosedSigmaClosedDerived using (closedSigmaClosed-derived)
  import Cubical.Data.Sum as ⊎
  open import Cubical.Data.Bool using (Dec→Bool; not; _≟_)
  open import Cubical.Relation.Nullary using (Dec; yes; no)

  private
    self≢not : (b : Bool) → b ≡ not b → ⊥
    self≢not true = true≢false
    self≢not false = false≢true

    Bool-dichotomy : (b1 b2 : Bool) → (b1 ≡ b2) ⊎ (b1 ≡ not b2)
    Bool-dichotomy true true = ⊎.inl refl
    Bool-dichotomy true false = ⊎.inr refl
    Bool-dichotomy false true = ⊎.inr refl
    Bool-dichotomy false false = ⊎.inl refl

    Dec→Bool-true : {A : Type₀} → A → (d : Dec A) → Dec→Bool d ≡ true
    Dec→Bool-true a (yes _) = refl
    Dec→Bool-true a (no ¬a) = ex-falso (¬a a)

    Dec→Bool-extract : {A : Type₀} → (d : Dec A) → Dec→Bool d ≡ true → A
    Dec→Bool-extract (yes a) _ = a
    Dec→Bool-extract (no _) p = ex-falso (false≢true p)

  ConnectedComponentConnected : (X : CHaus) (x : fst X)
    → (f : (Σ[ y ∈ fst X ] fst (ConnectedComponent X x y)) → Bool)
    → (y z : Σ[ y ∈ fst X ] fst (ConnectedComponent X x y))
    → f y ≡ f z
  ConnectedComponentConnected X x f (y , qy) (z , qz) =
    f (y , qy) ≡⟨ sym (from-x (y , qy)) ⟩
    fval ≡⟨ from-x (z , qz) ⟩
    f (z , qz) ∎
    where
    fval : Bool
    fval = f (x , (λ D p → p))
    from-x : (a : Σ[ w ∈ fst X ] fst (ConnectedComponent X x w)) → fval ≡ f a
    from-x (a , qa) = PT.rec (isSetBool fval (f (a , qa))) step1
      (ConnectedComponentClosedInCompactHausdorff X x)
      where
      step1 : Σ[ D ∈ (ℕ → DecSubsetCHaus X) ]
              ((w : fst X) → fst (ConnectedComponent X x w) ≡ ((n : ℕ) → inDec X w (D n)))
            → fval ≡ f (a , qa)
      step1 (D , Deq) = PT.rec (isSetBool fval (f (a , qa))) step2
        (CHausSeperationOfClosedByOpens X A_X B_X A-closed B-closed AB-disjoint)
        where
        Qx-closed : (w : fst X) → isClosedProp (ConnectedComponent X x w)
        Qx-closed w = closedEquiv
          (((n : ℕ) → D n w ≡ true) , isPropΠ (λ n → isSetBool (D n w) true))
          (ConnectedComponent X x w)
          (transport (sym (Deq w)))
          (transport (Deq w))
          (closedCountableIntersection (λ n → (D n w ≡ true) , isSetBool (D n w) true)
            (λ n → Bool-equality-closed (D n w) true))
        A_X : fst X → hProp ℓ-zero
        A_X w = ∥ Σ[ q ∈ fst (ConnectedComponent X x w) ] (f (w , q) ≡ fval) ∥₁ , squash₁
        A-closed : (w : fst X) → isClosedProp (A_X w)
        A-closed w = closedSigmaClosed-derived (ConnectedComponent X x w) (Qx-closed w)
          (λ q → (f (w , q) ≡ fval) , isSetBool (f (w , q)) fval)
          (λ q → Bool-equality-closed (f (w , q)) fval)
        B_X : fst X → hProp ℓ-zero
        B_X w = ∥ Σ[ q ∈ fst (ConnectedComponent X x w) ] (f (w , q) ≡ not fval) ∥₁ , squash₁
        B-closed : (w : fst X) → isClosedProp (B_X w)
        B-closed w = closedSigmaClosed-derived (ConnectedComponent X x w) (Qx-closed w)
          (λ q → (f (w , q) ≡ not fval) , isSetBool (f (w , q)) (not fval))
          (λ q → Bool-equality-closed (f (w , q)) (not fval))
        AB-disjoint : areDisjoint A_X B_X
        AB-disjoint w (aw , bw) = PT.rec2 isProp⊥
          (λ (q1 , eq1) (q2 , eq2) → self≢not fval
            (fval ≡⟨ sym eq1 ⟩
             f (w , q1) ≡⟨ cong (λ q → f (w , q)) (snd (ConnectedComponent X x w) q1 q2) ⟩
             f (w , q2) ≡⟨ eq2 ⟩
             not fval ∎))
          aw bw
        step2 : Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
                ((w : fst X) → isOpenProp (U w)) ×
                ((w : fst X) → isOpenProp (V w)) ×
                subsetOf A_X U × subsetOf B_X V × areDisjoint U V
              → fval ≡ f (a , qa)
        step2 (U , V , Uopen , Vopen , A⊆U , B⊆V , UV-disj) =
          PT.rec (isSetBool fval (f (a , qa))) step3
            (ConnectedComponentSubOpenHasDecidableInbetween X x UV UV-open Qx⊆UV)
          where
          UV : fst X → hProp ℓ-zero
          UV w = ∥ fst (U w) ⊎ fst (V w) ∥₁ , squash₁
          UV-open : (w : fst X) → isOpenProp (UV w)
          UV-open w = openOrMP mp (U w) (V w) (Uopen w) (Vopen w)
          Qx⊆UV : (w : fst X) → fst (ConnectedComponent X x w) → fst (UV w)
          Qx⊆UV w qw with Bool-dichotomy (f (w , qw)) fval
          ... | ⊎.inl p = ∣ ⊎.inl (A⊆U w ∣ qw , p ∣₁) ∣₁
          ... | ⊎.inr p = ∣ ⊎.inr (B⊆V w ∣ qw , p ∣₁) ∣₁
          step3 : Σ[ E ∈ DecSubsetCHaus X ] inDec X x E ×
                  ((w : fst X) → inDec X w E → fst (UV w))
                → fval ≡ f (a , qa)
          step3 (E , x-in-E , E⊆UV) = conclusion
            where
            x-in-U : fst (U x)
            x-in-U = A⊆U x ∣ (λ D p → p) , refl ∣₁
            x-not-in-V : ¬ fst (V x)
            x-not-in-V vx = UV-disj x (x-in-U , vx)
            E'-prop : fst X → hProp ℓ-zero
            E'-prop w = (E w ≡ true) × (¬ fst (V w)) ,
                        isProp× (isSetBool _ _) (snd (¬hProp (V w)))
            E'-closed : (w : fst X) → isClosedProp (E'-prop w)
            E'-closed w = closedAnd ((E w ≡ true) , isSetBool _ _) (¬hProp (V w))
                          (Bool-equality-closed (E w) true) (negOpenIsClosed (V w) (Vopen w))
            E'-open : (w : fst X) → isOpenProp (E'-prop w)
            E'-open w = openEquiv
              ((E w ≡ true) × fst (U w) , isProp× (isSetBool _ _) (snd (U w)))
              (E'-prop w)
              (λ (ew , uw) → ew , λ vw → UV-disj w (uw , vw))
              (λ (ew , ¬vw) → ew , openIsStable mp (U w) (Uopen w)
                (λ ¬uw → PT.rec isProp⊥
                  (λ { (⊎.inl uw) → ¬uw uw ; (⊎.inr vw) → ¬vw vw })
                  (E⊆UV w ew)))
              (openAnd ((E w ≡ true) , isSetBool _ _) (U w)
                (decIsOpen ((E w ≡ true) , isSetBool _ _) (E w ≟ true)) (Uopen w))
            E'bool : DecSubsetCHaus X
            E'bool w = Dec→Bool (clopenIsDecidable (E'-prop w) (E'-open w) (E'-closed w))
            x-in-E' : E'bool x ≡ true
            x-in-E' = Dec→Bool-true (x-in-E , x-not-in-V)
              (clopenIsDecidable (E'-prop x) (E'-open x) (E'-closed x))
            a-in-E' : E'bool a ≡ true
            a-in-E' = qa E'bool x-in-E'
            a-not-in-V : ¬ fst (V a)
            a-not-in-V = snd (Dec→Bool-extract
              (clopenIsDecidable (E'-prop a) (E'-open a) (E'-closed a)) a-in-E')
            conclusion : fval ≡ f (a , qa)
            conclusion with Bool-dichotomy (f (a , qa)) fval
            ... | ⊎.inl p = sym p
            ... | ⊎.inr p = ex-falso (a-not-in-V (B⊆V a ∣ qa , p ∣₁))

-- StoneCompactHausdorffTotallyDisconnectedModule (tex Lemma 2186)

module StoneCompactHausdorffTotallyDisconnectedModule where
  open CompactHausdorffModule
  open ConnectedComponentModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr; Sp; Booleω; evaluationMap; isPropHasStoneStr; 2^; SDHomVersion; isSetBoolHom)

  isTotallyDisconnected : CHaus → Type₀
  isTotallyDisconnected X =
    (x : fst X) → (y : fst X) → fst (ConnectedComponent X x y) → x ≡ y
  open import Cubical.Algebra.CommRing using (_$cr_; CommRingStr; IsCommRingHom; CommRingHom≡)
  open import Cubical.Algebra.BooleanRing using (BooleanRingStr; BooleanRing→CommRing)
  open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
  open import Cubical.Data.Bool using (true; false; false≢true)
  open import Cubical.Data.Empty as ⊥ using (⊥)
  open AlgebraCompactHausdorffCountablyPresentedModule
  open import Cubical.Foundations.Function using (_∘_)
  open import Cubical.Functions.Surjection using (isSurjection; isEmbedding×isSurjection→isEquiv)
  open import Cubical.Functions.Embedding using (injEmbedding)
  open import Cubical.Foundations.Equiv using (invEq; secEq)

  StoneCompactHausdorffTotallyDisconnected-forward : (S : Stone)
    → isTotallyDisconnected (Stone→CHaus S)
  StoneCompactHausdorffTotallyDisconnected-forward S x y qxy = goal
    where
    B : Booleω
    B = snd S .fst

    p : Sp B ≡ fst S
    p = snd S .snd

    x' : Sp B
    x' = transport (sym p) x

    y' : Sp B
    y' = transport (sym p) y

    D_b : ⟨ fst B ⟩ → DecSubsetCHaus (Stone→CHaus S)
    D_b b z = evaluationMap B b (transport (sym p) z)

    agree-on-true : (b : ⟨ fst B ⟩) → x' $cr b ≡ true → y' $cr b ≡ true
    agree-on-true b x'b≡true = qxy (D_b b) x'b≡true

    open BooleanRingStr (snd (fst B)) renaming (𝟙 to 1B; _-_ to _-B_)
    open CommRingStr (snd (BooleanRing→CommRing BoolBR)) renaming (1r to 1Bool; _-_ to _-Bool_)
    open IsCommRingHom

    agree-on-all : (b : ⟨ fst B ⟩) → x' $cr b ≡ y' $cr b
    agree-on-all b with x' $cr b | inspect (x' $cr_) b
    ... | true  | [ eq ] = sym (agree-on-true b eq)
    ... | false | [ eq ] with y' $cr b | inspect (y' $cr_) b
    ...   | false | [ eq' ] = refl
    ...   | true  | [ eq' ] = ⊥.rec (false≢true contra)
      where
      open BooleanRingStr (snd (fst B)) using (_+_) renaming (-_ to negB)
      open CommRingStr (snd (BooleanRing→CommRing BoolBR)) using () renaming (_+_ to _+Bool_; -_ to negBool)

      ¬b : ⟨ fst B ⟩
      ¬b = 1B -B b

      neg-eval : ∀ h → h $cr ¬b ≡ true +Bool (negBool (h $cr b))
      neg-eval h =
        h $cr ¬b
          ≡⟨ pres+ (snd h) 1B (negB b) ⟩
        (h $cr 1B) +Bool (h $cr (negB b))
          ≡⟨ cong₂ _+Bool_ (pres1 (snd h)) (pres- (snd h) b) ⟩
        true +Bool (negBool (h $cr b)) ∎

      x'-¬b-true : x' $cr ¬b ≡ true
      x'-¬b-true =
        x' $cr ¬b
          ≡⟨ neg-eval x' ⟩
        true +Bool (negBool (x' $cr b))
          ≡⟨ cong (λ z → true +Bool (negBool z)) eq ⟩
        true ∎

      y'-¬b-false : y' $cr ¬b ≡ false
      y'-¬b-false =
        y' $cr ¬b
          ≡⟨ neg-eval y' ⟩
        true +Bool (negBool (y' $cr b))
          ≡⟨ cong (λ z → true +Bool (negBool z)) eq' ⟩
        false ∎

      contra : false ≡ true
      contra =
        false
          ≡⟨ sym y'-¬b-false ⟩
        y' $cr ¬b
          ≡⟨ agree-on-true ¬b x'-¬b-true ⟩
        true ∎

    x'≡y' : x' ≡ y'
    x'≡y' = CommRingHom≡ (funExt agree-on-all)

    goal : x ≡ y
    goal =
      x
        ≡⟨ sym (transportTransport⁻ p x) ⟩
      transport p (transport (sym p) x)
        ≡⟨ cong (transport p) x'≡y' ⟩
      transport p (transport (sym p) y)
        ≡⟨ transportTransport⁻ p y ⟩
      y ∎

  -- tex Lemma 2186 backward direction, depends on tex Lemma 2112
  StoneCompactHausdorffTotallyDisconnected-backward : (X : CHaus)
    → isTotallyDisconnected X
    → hasStoneStr (fst X)
  StoneCompactHausdorffTotallyDisconnected-backward X td =
    PT.rec (isPropHasStoneStr sd-axiom _) mainConstruct
      (AlgebraCompactHausdorffCountablyPresented X)
    where
    mainConstruct : has-Boole-ω' (2^ (fst X)) → hasStoneStr (fst X)
    mainConstruct countPresX = BX , sym (ua ev-equiv)
      where
      BX : Booleω
      BX = 2^ (fst X) , ∣ countPresX ∣₁

      open IsCommRingHom

      ev : fst X → Sp BX
      fst (ev z) D = D z
      pres0 (snd (ev z)) = refl
      pres1 (snd (ev z)) = refl
      pres+ (snd (ev z)) _ _ = refl
      pres· (snd (ev z)) _ _ = refl
      pres- (snd (ev z)) _ = refl

      ev-inj : (x y : fst X) → ev x ≡ ev y → x ≡ y
      ev-inj x y p = td x y (λ D xInD →
        subst (_≡ true) (funExt⁻ (cong fst p) D) xInD)

      ev-surj : isSurjection ev
      ev-surj h = PT.rec squash₁ withCover (hasCHausStr.stoneCover (snd X))
        where
        withCover : Σ[ S ∈ Stone ] Σ[ q ∈ (fst S → fst X) ] isSurjection q
          → ∥ Σ[ x ∈ fst X ] ev x ≡ h ∥₁
        withCover (S , q , q-surj) = PT.rec squash₁ withCountPresS
          (AlgebraCompactHausdorffCountablyPresented (Stone→CHaus S))
          where
          withCountPresS : has-Boole-ω' (2^ (fst S)) → ∥ Σ[ x ∈ fst X ] ev x ≡ h ∥₁
          withCountPresS countPresS = PT.rec squash₁ withH'
            (injective→Sp-surjective BX BSo q* q*-inj h)
            where
            BSo : Booleω
            BSo = 2^ (fst S) , ∣ countPresS ∣₁

            q* : BoolHom (fst BX) (fst BSo)
            fst q* D s' = D (q s')
            pres0 (snd q*) = refl
            pres1 (snd q*) = refl
            pres+ (snd q*) _ _ = refl
            pres· (snd q*) _ _ = refl
            pres- (snd q*) _ = refl

            q*-inj : isInjectiveBoolHom BX BSo q*
            q*-inj D1 D2 eq = funExt (λ x →
              PT.rec (isSetBool _ _)
                (λ { (s' , qs'≡x) →
                  D1 x       ≡⟨ cong D1 (sym qs'≡x) ⟩
                  D1 (q s')  ≡⟨ funExt⁻ eq s' ⟩
                  D2 (q s')  ≡⟨ cong D2 qs'≡x ⟩
                  D2 x ∎ })
                (q-surj x))

            B_S : Booleω
            B_S = snd S .fst

            p_S : Sp B_S ≡ fst S
            p_S = snd S .snd

            coord : BoolHom (fst B_S) (fst BSo)
            fst coord b s' = evaluationMap B_S b (transport (sym p_S) s')
            pres0 (snd coord) = funExt (λ s' → pres0 (snd (transport (sym p_S) s')))
            pres1 (snd coord) = funExt (λ s' → pres1 (snd (transport (sym p_S) s')))
            pres+ (snd coord) a b = funExt (λ s' → pres+ (snd (transport (sym p_S) s')) a b)
            pres· (snd coord) a b = funExt (λ s' → pres· (snd (transport (sym p_S) s')) a b)
            pres- (snd coord) a = funExt (λ s' → pres- (snd (transport (sym p_S) s')) a)

            sdEquiv : ⟨ fst B_S ⟩ ≃ (Sp B_S → Bool)
            sdEquiv = fst (SDHomVersion sd-axiom B_S)

            withH' : Σ[ h' ∈ Sp BSo ] h' ∘cr q* ≡ h → ∥ Σ[ x ∈ fst X ] ev x ≡ h ∥₁
            withH' (h' , h'q*≡h) = ∣ q s , CommRingHom≡ (funExt pointwise) ∣₁
              where
              ψ : Sp B_S
              ψ = h' ∘cr coord

              s : fst S
              s = transport p_S ψ

              bE : (E : fst S → Bool) → ⟨ fst B_S ⟩
              bE E = invEq sdEquiv (E ∘ transport p_S)

              coordb≡ : (E : fst S → Bool) → fst coord (bE E) ≡ E
              coordb≡ E = funExt (λ s' →
                fst coord (bE E) s'
                  ≡⟨ funExt⁻ (secEq sdEquiv (E ∘ transport p_S)) (transport (sym p_S) s') ⟩
                E (transport p_S (transport (sym p_S) s'))
                  ≡⟨ cong E (transportTransport⁻ p_S s') ⟩
                E s' ∎)

              pointwise : (D : fst X → Bool) → D (q s) ≡ fst h D
              pointwise D =
                D (q s)
                  ≡⟨ sym (funExt⁻ (secEq sdEquiv ((D ∘ q) ∘ transport p_S)) ψ) ⟩
                fst h' (fst coord (bE (D ∘ q)))
                  ≡⟨ cong (fst h') (coordb≡ (D ∘ q)) ⟩
                fst h' (D ∘ q)
                  ≡⟨ funExt⁻ (cong fst h'q*≡h) D ⟩
                fst h D ∎

      ev-emb = injEmbedding (isSetBoolHom (fst BX) BoolBR) (λ {x} {y} → ev-inj x y)

      ev-equiv : fst X ≃ Sp BX
      ev-equiv = ev , isEmbedding×isSurjection→isEquiv (ev-emb , ev-surj)

-- StoneSigmaClosedModule (tex Theorem 2214, stone-sigma-closed)

module StoneSigmaClosedModule where
  open import Axioms.StoneDuality using (Stone; hasStoneStr)
  open CompactHausdorffModule
  open SigmaCompactHausdorffModule
  open StoneCompactHausdorffTotallyDisconnectedModule
  open ConnectedComponentModule
  open ConnectedComponentConnectedModule

  SigmaStoneType : (S : Stone) → (T : fst S → Stone) → Type₀
  SigmaStoneType S T = Σ[ x ∈ fst S ] fst (T x)

  ΣStoneCHaus : (S : Stone) → (T : fst S → Stone) → CHaus
  ΣStoneCHaus S T = CHausΣ (Stone→CHaus S) (λ x → Stone→CHaus (T x))

  proj₁-preserves-CC : (S : Stone) (T : fst S → Stone)
    → (x : fst S) (y : fst (T x)) (x' : fst S) (y' : fst (T x'))
    → fst (ConnectedComponent (ΣStoneCHaus S T) (x , y) (x' , y'))
    → fst (ConnectedComponent (Stone→CHaus S) x x')
  proj₁-preserves-CC S T x y x' y' ccσ D xInD = ccσ (λ (a , b) → D a) xInD

  -- Proof of ΣStone-isTotallyDisconnected following tex Theorem 2214
  ΣStone-isTotallyDisconnected : (S : Stone) (T : fst S → Stone)
    → isTotallyDisconnected (ΣStoneCHaus S T)
  ΣStone-isTotallyDisconnected S T (x , y) (x' , y') ccσ = goal
    where
    x'InQx : fst (ConnectedComponent (Stone→CHaus S) x x')
    x'InQx = proj₁-preserves-CC S T x y x' y' ccσ

    x≡x' : x ≡ x'
    x≡x' = StoneCompactHausdorffTotallyDisconnected-forward S x x' x'InQx

    y'-in-Tx : fst (T x)
    y'-in-Tx = subst (λ z → fst (T z)) (sym x≡x') y'

    Qσ : Type₀
    Qσ = Σ[ p ∈ SigmaStoneType S T ] fst (ConnectedComponent (ΣStoneCHaus S T) (x , y) p)

    xy-in-Qσ : Qσ
    xy-in-Qσ = (x , y) , λ D xInD → xInD

    x'y'-in-Qσ : Qσ
    x'y'-in-Qσ = (x' , y') , ccσ

    make-f : (g : fst (T x) → Bool) → Qσ → Bool
    make-f g ((a , b) , cc) = g (subst (λ z → fst (T z))
      (sym (StoneCompactHausdorffTotallyDisconnected-forward S x a
            (proj₁-preserves-CC S T x y a b cc))) b)

    f-constant : (g : fst (T x) → Bool) → make-f g xy-in-Qσ ≡ make-f g x'y'-in-Qσ
    f-constant g = ConnectedComponentConnected (ΣStoneCHaus S T) (x , y) (make-f g) xy-in-Qσ x'y'-in-Qσ

    isSetS : isSet (fst S)
    isSetS = StoneEqualityClosedModule.hasStoneStr→isSet S

    p_x : x ≡ x
    p_x = StoneCompactHausdorffTotallyDisconnected-forward S x x
          (proj₁-preserves-CC S T x y x y (λ D xInD → xInD))

    p_x' : x ≡ x'
    p_x' = StoneCompactHausdorffTotallyDisconnected-forward S x x'
           (proj₁-preserves-CC S T x y x' y' ccσ)

    make-f-xy : (g : fst (T x) → Bool) → make-f g xy-in-Qσ ≡ g y
    make-f-xy g =
      make-f g xy-in-Qσ
        ≡⟨ cong (λ p → g (subst (λ z → fst (T z)) (sym p) y)) (isSetS x x p_x refl) ⟩
      g (transport refl y)
        ≡⟨ cong g (transportRefl y) ⟩
      g y ∎

    make-f-x'y' : (g : fst (T x) → Bool) → make-f g x'y'-in-Qσ ≡ g y'-in-Tx
    make-f-x'y' g = cong (λ p → g (subst (λ z → fst (T z)) (sym p) y')) (isSetS x x' p_x' x≡x')

    g-agrees : (g : fst (T x) → Bool) → g y ≡ g y'-in-Tx
    g-agrees g =
      g y
        ≡⟨ sym (make-f-xy g) ⟩
      make-f g xy-in-Qσ
        ≡⟨ f-constant g ⟩
      make-f g x'y'-in-Qσ
        ≡⟨ make-f-x'y' g ⟩
      g y'-in-Tx ∎

    y≡y'-in-Tx : y ≡ y'-in-Tx
    y≡y'-in-Tx = StoneCompactHausdorffTotallyDisconnected-forward (T x) y y'-in-Tx
      (λ D yInD → sym (g-agrees D) ∙ yInD)

    goal : (x , y) ≡ (x' , y')
    goal = ΣPathP (x≡x' , toPathP (cong (subst (λ z → fst (T z)) x≡x') y≡y'-in-Tx
              ∙ transportTransport⁻ (cong (λ z → fst (T z)) x≡x') y'))

  StoneSigmaClosed : (S : Stone) (T : fst S → Stone)
    → hasStoneStr (SigmaStoneType S T)
  StoneSigmaClosed S T = StoneCompactHausdorffTotallyDisconnected-backward
    (ΣStoneCHaus S T)
    (ΣStone-isTotallyDisconnected S T)

-- IntervalIsCHausModule (tex Theorem 2272)
