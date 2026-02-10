{-# OPTIONS --cubical --guardedness #-}

module work.Part10a where

open import work.Part10b public

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isPropΠ; hProp; isProp×)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using (⊥; isProp⊥)
open import Cubical.Data.Sum using (_⊎_; inl; inr; isProp⊎)
open import Cubical.HITs.PropositionalTruncation as PT using (∣_∣₁; ∥_∥₁; squash₁)
open import Cubical.Data.Unit using (tt)
open import Cubical.Relation.Nullary using (¬_)

module BooleanAlgebraLawsModule where
  open StoneAsClosedSubsetOfCantorModule
  open StoneAsClosedSubsetOfCantorModule2
  open StoneEqualityClosedModule using (isPropIsClosedProp)

  hPropExt : {A B : Type₀} → isProp A → isProp B → (A → B) → (B → A) → A ≡ B
  hPropExt pA pB f g = ua (isoToEquiv (iso f g (λ b → pB _ _) (λ a → pA _ _)))

  hProp≡ : (P Q : hProp ℓ-zero) → (⟨ P ⟩ → ⟨ Q ⟩) → (⟨ Q ⟩ → ⟨ P ⟩) → P ≡ Q
  hProp≡ P Q f g = Σ≡Prop (λ _ → isPropIsProp) (hPropExt (snd P) (snd Q) f g)

  ×-hProp-comm : (P Q : hProp ℓ-zero)
    → ((fst P × fst Q) , isProp× (snd P) (snd Q))
      ≡ ((fst Q × fst P) , isProp× (snd Q) (snd P))
  ×-hProp-comm P Q = hProp≡ _ _ (λ (p , q) → q , p) (λ (q , p) → p , q)

  closedIntersectionComm : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A B ≡ ClosedSubsetIntersection B A
  closedIntersectionComm (A , Aclosed) (B , Bclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (B x)) , isProp× (snd (A x)) (snd (B x)))
             ≡ (λ x → (fst (B x) × fst (A x)) , isProp× (snd (B x)) (snd (A x)))
    fst-path = funExt (λ x → ×-hProp-comm (A x) (B x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) (B x) (Aclosed x) (Bclosed x))
                     (λ x → closedAnd (B x) (A x) (Bclosed x) (Aclosed x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x}))
                            _ _

  closedUnionComm : (A B : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A B ≡ ClosedSubsetUnion B A
  closedUnionComm (A , Aclosed) (B , Bclosed) = ΣPathP (fst-path , snd-path)
    where
    ⊎-swap : {P Q : Type₀} → ∥ P ⊎ Q ∥₁ → ∥ Q ⊎ P ∥₁
    ⊎-swap = PT.map (λ { (inl p) → inr p ; (inr q) → inl q })

    fst-path : (λ x → (∥ fst (A x) ⊎ fst (B x) ∥₁) , squash₁)
             ≡ (λ x → (∥ fst (B x) ⊎ fst (A x) ∥₁) , squash₁)
    fst-path = funExt (λ x → hProp≡ _ _ ⊎-swap ⊎-swap)

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) (B x) (Aclosed x) (Bclosed x))
                     (λ x → closedOr (B x) (A x) (Bclosed x) (Aclosed x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x}))
                            _ _

  ×-hProp-idem : (P : hProp ℓ-zero)
    → ((fst P × fst P) , isProp× (snd P) (snd P)) ≡ P
  ×-hProp-idem P = hProp≡ _ _ (λ (p , _) → p) (λ p → p , p)

  ⊎-hProp-idem : (P : hProp ℓ-zero)
    → (∥ fst P ⊎ fst P ∥₁ , squash₁) ≡ P
  ⊎-hProp-idem P = hProp≡ _ _
    (PT.rec (snd P) (λ { (inl p) → p ; (inr p) → p }))
    (λ p → ∣ inl p ∣₁)

  closedIntersectionIdem : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A A ≡ A
  closedIntersectionIdem (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (A x)) , isProp× (snd (A x)) (snd (A x))) ≡ A
    fst-path = funExt (λ x → ×-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) (A x) (Aclosed x) (Aclosed x))
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  closedUnionIdem : (A : ClosedSubsetOfCantor)
    → ClosedSubsetUnion A A ≡ A
  closedUnionIdem (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ fst (A x) ∥₁) , squash₁) ≡ A
    fst-path = funExt (λ x → ⊎-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedOr (A x) (A x) (Aclosed x) (Aclosed x))
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  ×-hProp-empty : (P : hProp ℓ-zero)
    → ((fst P × ⊥) , isProp× (snd P) isProp⊥) ≡ ⊥-hProp
  ×-hProp-empty P = hProp≡ _ _ (λ (_ , bot) → bot) (λ bot → ex-falso bot , bot)

  ×-hProp-full : (P : hProp ℓ-zero)
    → ((fst P × Unit) , isProp× (snd P) (λ _ _ → refl)) ≡ P
  ×-hProp-full P = hProp≡ _ _ (λ (p , _) → p) (λ p → p , tt)

  ×-hProp-assoc : (P Q R : hProp ℓ-zero)
    → ((fst P × fst Q) × fst R , isProp× (isProp× (snd P) (snd Q)) (snd R))
      ≡ (fst P × (fst Q × fst R) , isProp× (snd P) (isProp× (snd Q) (snd R)))
  ×-hProp-assoc P Q R = hProp≡ _ _
    (λ ((p , q) , r) → p , (q , r))
    (λ (p , (q , r)) → (p , q) , r)

  closedIntersectionEmpty : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A EmptyClosedSubset ≡ EmptyClosedSubset
  closedIntersectionEmpty (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × ⊥) , isProp× (snd (A x)) isProp⊥) ≡ (λ _ → ⊥-hProp)
    fst-path = funExt (λ x → ×-hProp-empty (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊥-hProp (Aclosed x) ⊥-isClosed)
                     (λ _ → ⊥-isClosed)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  closedIntersectionFull : (A : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A FullClosedSubset ≡ A
  closedIntersectionFull (A , Aclosed) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × Unit) , isProp× (snd (A x)) (λ _ _ → refl)) ≡ A
    fst-path = funExt (λ x → ×-hProp-full (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ⊤-hProp (Aclosed x) ⊤-isClosed)
                     Aclosed
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  closedIntersectionAssoc : (A B C : ClosedSubsetOfCantor)
    → ClosedSubsetIntersection A (ClosedSubsetIntersection B C)
      ≡ ClosedSubsetIntersection (ClosedSubsetIntersection A B) C
  closedIntersectionAssoc (A , Acl) (B , Bcl) (C , Ccl) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × (fst (B x) × fst (C x))) ,
                      isProp× (snd (A x)) (isProp× (snd (B x)) (snd (C x))))
             ≡ (λ x → ((fst (A x) × fst (B x)) × fst (C x)) ,
                      isProp× (isProp× (snd (A x)) (snd (B x))) (snd (C x)))
    fst-path = funExt (λ x → sym (×-hProp-assoc (A x) (B x) (C x)))

    snd-path : PathP (λ i → (x : CantorSpace) → isClosedProp (fst-path i x))
                     (λ x → closedAnd (A x) ((fst (B x) × fst (C x)) ,
                              isProp× (snd (B x)) (snd (C x))) (Acl x)
                              (closedAnd (B x) (C x) (Bcl x) (Ccl x)))
                     (λ x → closedAnd ((fst (A x) × fst (B x)) ,
                              isProp× (snd (A x)) (snd (B x))) (C x)
                              (closedAnd (A x) (B x) (Acl x) (Bcl x)) (Ccl x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsClosedProp {fst-path i x})) _ _

  postulate
    closedAbsorption1 : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetUnion A B) ≡ A

    closedAbsorption2 : (A B : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (ClosedSubsetIntersection A B) ≡ A

    closedUnionEmpty : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A EmptyClosedSubset ≡ A

    closedUnionFull : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A FullClosedSubset ≡ FullClosedSubset

    closedUnionAssoc : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (ClosedSubsetUnion B C)
        ≡ ClosedSubsetUnion (ClosedSubsetUnion A B) C

    closedDistributiveIntersection : (A B C : ClosedSubsetOfCantor)
      → ClosedSubsetIntersection A (ClosedSubsetUnion B C)
        ≡ ClosedSubsetUnion (ClosedSubsetIntersection A B) (ClosedSubsetIntersection A C)

  openIntersectionEmpty : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A EmptyOpenSubset ≡ EmptyOpenSubset
  openIntersectionEmpty (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × ⊥) , isProp× (snd (A x)) isProp⊥) ≡ (λ _ → ⊥-hProp)
    fst-path = funExt (λ x → ×-hProp-empty (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) ⊥-hProp (Aopen x) ⊥-isOpen)
                     (λ _ → ⊥-isOpen)
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  openIntersectionComm : (A B : OpenSubsetOfCantor)
    → OpenSubsetIntersection A B ≡ OpenSubsetIntersection B A
  openIntersectionComm (A , Aopen) (B , Bopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (B x)) , isProp× (snd (A x)) (snd (B x)))
             ≡ (λ x → (fst (B x) × fst (A x)) , isProp× (snd (B x)) (snd (A x)))
    fst-path = funExt (λ x → ×-hProp-comm (A x) (B x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) (B x) (Aopen x) (Bopen x))
                     (λ x → openAnd (B x) (A x) (Bopen x) (Aopen x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  openUnionComm : (A B : OpenSubsetOfCantor)
    → OpenSubsetUnion A B ≡ OpenSubsetUnion B A
  openUnionComm (A , Aopen) (B , Bopen) = ΣPathP (fst-path , snd-path)
    where
    ⊎-swap : {P Q : Type₀} → ∥ P ⊎ Q ∥₁ → ∥ Q ⊎ P ∥₁
    ⊎-swap = PT.map (λ { (inl p) → inr p ; (inr q) → inl q })

    fst-path : (λ x → (∥ fst (A x) ⊎ fst (B x) ∥₁) , squash₁)
             ≡ (λ x → (∥ fst (B x) ⊎ fst (A x) ∥₁) , squash₁)
    fst-path = funExt (λ x → hProp≡ _ _ ⊎-swap ⊎-swap)

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openOr (A x) (B x) (Aopen x) (Bopen x))
                     (λ x → openOr (B x) (A x) (Bopen x) (Aopen x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  openIntersectionIdem : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A A ≡ A
  openIntersectionIdem (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × fst (A x)) , isProp× (snd (A x)) (snd (A x))) ≡ A
    fst-path = funExt (λ x → ×-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) (A x) (Aopen x) (Aopen x))
                     Aopen
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  openUnionIdem : (A : OpenSubsetOfCantor)
    → OpenSubsetUnion A A ≡ A
  openUnionIdem (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (∥ fst (A x) ⊎ fst (A x) ∥₁) , squash₁) ≡ A
    fst-path = funExt (λ x → ⊎-hProp-idem (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openOr (A x) (A x) (Aopen x) (Aopen x))
                     Aopen
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  openIntersectionFull : (A : OpenSubsetOfCantor)
    → OpenSubsetIntersection A FullOpenSubset ≡ A
  openIntersectionFull (A , Aopen) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × Unit) , isProp× (snd (A x)) (λ _ _ → refl)) ≡ A
    fst-path = funExt (λ x → ×-hProp-full (A x))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) ⊤-hProp (Aopen x) ⊤-isOpen)
                     Aopen
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  openIntersectionAssoc : (A B C : OpenSubsetOfCantor)
    → OpenSubsetIntersection A (OpenSubsetIntersection B C)
      ≡ OpenSubsetIntersection (OpenSubsetIntersection A B) C
  openIntersectionAssoc (A , Aop) (B , Bop) (C , Cop) = ΣPathP (fst-path , snd-path)
    where
    fst-path : (λ x → (fst (A x) × (fst (B x) × fst (C x))) ,
                      isProp× (snd (A x)) (isProp× (snd (B x)) (snd (C x))))
             ≡ (λ x → ((fst (A x) × fst (B x)) × fst (C x)) ,
                      isProp× (isProp× (snd (A x)) (snd (B x))) (snd (C x)))
    fst-path = funExt (λ x → sym (×-hProp-assoc (A x) (B x) (C x)))

    snd-path : PathP (λ i → (x : CantorSpace) → isOpenProp (fst-path i x))
                     (λ x → openAnd (A x) ((fst (B x) × fst (C x)) ,
                              isProp× (snd (B x)) (snd (C x))) (Aop x)
                              (openAnd (B x) (C x) (Bop x) (Cop x)))
                     (λ x → openAnd ((fst (A x) × fst (B x)) ,
                              isProp× (snd (A x)) (snd (B x))) (C x)
                              (openAnd (A x) (B x) (Aop x) (Bop x)) (Cop x))
    snd-path = isProp→PathP (λ i → isPropΠ (λ x → isPropIsOpenProp (fst-path i x))) _ _

  postulate
    openAbsorption1 : (A B : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetUnion A B) ≡ A

    openAbsorption2 : (A B : OpenSubsetOfCantor)
      → OpenSubsetUnion A (OpenSubsetIntersection A B) ≡ A

    openUnionEmpty : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A EmptyOpenSubset ≡ A

    openUnionFull : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A FullOpenSubset ≡ FullOpenSubset

    openUnionAssoc : (A B C : OpenSubsetOfCantor)
      → OpenSubsetUnion A (OpenSubsetUnion B C)
        ≡ OpenSubsetUnion (OpenSubsetUnion A B) C

    openDistributiveIntersection : (A B C : OpenSubsetOfCantor)
      → OpenSubsetIntersection A (OpenSubsetUnion B C)
        ≡ OpenSubsetUnion (OpenSubsetIntersection A B) (OpenSubsetIntersection A C)

  postulate
    closedDoubleComplementInvolution : (A : ClosedSubsetOfCantor)
      → OpenSubsetComplement (ClosedSubsetComplement A) ≡ A

    openDoubleComplementInvolution : (A : OpenSubsetOfCantor)
      → ClosedSubsetComplement (OpenSubsetComplement A) ≡ A

    closedUnionComplement : (A : ClosedSubsetOfCantor)
      → ClosedSubsetUnion A (OpenSubsetComplement (ClosedSubsetComplement A))
        ≡ FullClosedSubset

    openUnionComplement : (A : OpenSubsetOfCantor)
      → OpenSubsetUnion A (ClosedSubsetComplement (OpenSubsetComplement A))
        ≡ FullOpenSubset

  closedDeMorganUnion-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
    → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
  closedDeMorganUnion-fwd (A , _) (B , _) x ¬AorB =
    (λ ax → ¬AorB ∣ inl ax ∣₁) , (λ bx → ¬AorB ∣ inr bx ∣₁)

  closedDeMorganUnion-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetIntersection (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetUnion A B)) x)
  closedDeMorganUnion-bwd (A , _) (B , _) x (¬ax , ¬bx) =
    PT.rec isProp⊥ (λ { (inl ax) → ¬ax ax ; (inr bx) → ¬bx bx })

  openDeMorganUnion-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
    → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
  openDeMorganUnion-fwd (A , _) (B , _) x ¬AorB =
    (λ ax → ¬AorB ∣ inl ax ∣₁) , (λ bx → ¬AorB ∣ inr bx ∣₁)

  openDeMorganUnion-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetIntersection (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetUnion A B)) x)
  openDeMorganUnion-bwd (A , _) (B , _) x (¬ax , ¬bx) =
    PT.rec isProp⊥ (λ { (inl ax) → ¬ax ax ; (inr bx) → ¬bx bx })

  postulate
    closedDeMorganIntersection-fwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
      → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
      → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)

  closedDeMorganIntersection-bwd : (A B : ClosedSubsetOfCantor) (x : CantorSpace)
    → fst (fst (OpenSubsetUnion (ClosedSubsetComplement A) (ClosedSubsetComplement B)) x)
    → fst (fst (ClosedSubsetComplement (ClosedSubsetIntersection A B)) x)
  closedDeMorganIntersection-bwd (A , _) (B , _) x =
    λ (h : ∥ (fst (A x) → ⊥) ⊎ (fst (B x) → ⊥) ∥₁) →
    λ ((ax , bx) : fst (A x) × fst (B x)) →
    PT.rec isProp⊥ (λ { (inl ¬ax) → ¬ax ax ; (inr ¬bx) → ¬bx bx }) h

  postulate
    openDeMorganIntersection-fwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
      → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
      → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)

  openDeMorganIntersection-bwd : (A B : OpenSubsetOfCantor) (x : CantorSpace)
    → fst (fst (ClosedSubsetUnion (OpenSubsetComplement A) (OpenSubsetComplement B)) x)
    → fst (fst (OpenSubsetComplement (OpenSubsetIntersection A B)) x)
  openDeMorganIntersection-bwd (A , _) (B , _) x =
    λ (h : ∥ (fst (A x) → ⊥) ⊎ (fst (B x) → ⊥) ∥₁) →
    λ ((ax , bx) : fst (A x) × fst (B x)) →
    PT.rec isProp⊥ (λ { (inl ¬ax) → ¬ax ax ; (inr ¬bx) → ¬bx bx }) h

-- BooleEpiMono (tex Remark 1475)
