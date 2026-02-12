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
    → ∥ isOpenProp (((x : fst X) → fst (U x)) , isPropΠ (λ x → snd (U x))) ∥₁
  AllOpenSubspaceOpen X U Uopen = PT.map go exists-¬U-closed
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

  postulate
    CHausFiniteIntersectionProperty : (X : CHaus)
      → (C : ℕ → (fst X → hProp ℓ-zero))
      → ((n : ℕ) → (x : fst X) → isClosedProp (C n x))
      → ((x : fst X) → ¬ fst (countableIntersectionClosed C x))
      → ∥ Σ[ k ∈ ℕ ] ((x : fst X) → ¬ fst (finiteIntersectionClosed C k x)) ∥₁

-- ChausMapsPreserveIntersectionOfClosed (tex Corollary 2003)

module ChausMapsPreserveIntersectionOfClosedModule where
  open CompactHausdorffModule
  open CHausFiniteIntersectionPropertyModule

  imageSubset : {X Y : Type₀} → (f : X → Y)
    → (A : X → hProp ℓ-zero) → Y → hProp ℓ-zero
  imageSubset f A y = ∥ Σ[ x ∈ _ ] fst (A x) × (f x ≡ y) ∥₁ , squash₁

  isDecreasingSeq : {X : Type₀}
    → (G : ℕ → (X → hProp ℓ-zero)) → Type₀
  isDecreasingSeq {X} G = (n : ℕ) → (x : X) → fst (G (suc n) x) → fst (G n x)

  postulate
    ChausMapsPreserveIntersectionOfClosed : (X Y : CHaus)
      → (f : fst X → fst Y)
      → (G : ℕ → (fst X → hProp ℓ-zero))
      → ((n : ℕ) → (x : fst X) → isClosedProp (G n x))
      → isDecreasingSeq G
      → (y : fst Y)
      → fst (imageSubset f (countableIntersectionClosed G) y)
        ≡ fst (countableIntersectionClosed (λ n → imageSubset f (G n)) y)

-- CHausSeperationOfClosedByOpens (tex Lemma 2058)

module CHausSeperationOfClosedByOpensModule where
  open CompactHausdorffModule

  areDisjoint : {X : Type₀}
    → (A B : X → hProp ℓ-zero) → Type₀
  areDisjoint {X} A B = (x : X) → ¬ (fst (A x) × fst (B x))

  subsetOf : {X : Type₀}
    → (A B : X → hProp ℓ-zero) → Type₀
  subsetOf {X} A B = (x : X) → fst (A x) → fst (B x)

  postulate
    CHausSeperationOfClosedByOpens : (X : CHaus)
      → (A B : fst X → hProp ℓ-zero)
      → ((x : fst X) → isClosedProp (A x))
      → ((x : fst X) → isClosedProp (B x))
      → areDisjoint A B
      → ∥ Σ[ U ∈ (fst X → hProp ℓ-zero) ] Σ[ V ∈ (fst X → hProp ℓ-zero) ]
          ((x : fst X) → isOpenProp (U x)) ×
          ((x : fst X) → isOpenProp (V x)) ×
          subsetOf A U × subsetOf B V × areDisjoint U V ∥₁

-- SigmaCompactHausdorff (tex Lemma 2098)

module SigmaCompactHausdorffModule where
  open CompactHausdorffModule

  SigmaCHausType : (X : CHaus) → (Y : fst X → CHaus) → Type₀
  SigmaCHausType X Y = Σ[ x ∈ fst X ] fst (Y x)

  postulate
    SigmaCompactHausdorff : (X : CHaus) (Y : fst X → CHaus)
      → hasCHausStr (SigmaCHausType X Y)

  CHausΣ : (X : CHaus) → (Y : fst X → CHaus) → CHaus
  CHausΣ X Y = SigmaCHausType X Y , SigmaCompactHausdorff X Y

-- AlgebraCompactHausdorffCountablyPresented (tex Lemma 2112)

module AlgebraCompactHausdorffCountablyPresentedModule where
  open CompactHausdorffModule

  BoolAlgOfCHaus : CHaus → Type₀
  BoolAlgOfCHaus X = fst X → Bool

  postulate
    AlgebraCompactHausdorffCountablyPresented : (X : CHaus)
      → ∥ Σ[ B ∈ Booleω ] ⟨ fst B ⟩ ≡ BoolAlgOfCHaus X ∥₁

-- ConnectedComponentModule (tex 2138-2171)

module ConnectedComponentModule where
  open CompactHausdorffModule

  DecSubsetCHaus : CHaus → Type₀
  DecSubsetCHaus X = fst X → Bool

  inDec : (X : CHaus) → fst X → DecSubsetCHaus X → Type₀
  inDec X x D = D x ≡ true

  ConnectedComponent : (X : CHaus) → fst X → fst X → hProp ℓ-zero
  ConnectedComponent X x y =
    ((D : DecSubsetCHaus X) → inDec X x D → inDec X y D) ,
    isPropΠ (λ D → isPropΠ (λ _ → isSetBool (D y) true))

  postulate
    ConnectedComponentClosedInCompactHausdorff : (X : CHaus) (x : fst X)
      → ∥ Σ[ D ∈ (ℕ → DecSubsetCHaus X) ]
          ((y : fst X) → fst (ConnectedComponent X x y)
            ≡ ((n : ℕ) → inDec X y (D n))) ∥₁
    ConnectedComponentSubOpenHasDecidableInbetween : (X : CHaus) (x : fst X)
      → (U : fst X → hProp ℓ-zero) → ((y : fst X) → isOpenProp (U y))
      → ((y : fst X) → fst (ConnectedComponent X x y) → fst (U y))
      → ∥ Σ[ E ∈ DecSubsetCHaus X ] inDec X x E × ((y : fst X) → inDec X y E → fst (U y)) ∥₁

-- ConnectedComponentConnectedModule (tex Lemma 2173)

module ConnectedComponentConnectedModule where
  open CompactHausdorffModule
  open ConnectedComponentModule

  postulate
    ConnectedComponentConnected : (X : CHaus) (x : fst X)
      → (f : (Σ[ y ∈ fst X ] fst (ConnectedComponent X x y)) → Bool)
      → (y z : Σ[ y ∈ fst X ] fst (ConnectedComponent X x y))
      → f y ≡ f z

-- StoneCompactHausdorffTotallyDisconnectedModule (tex Lemma 2186)

module StoneCompactHausdorffTotallyDisconnectedModule where
  open CompactHausdorffModule
  open ConnectedComponentModule
  open import Axioms.StoneDuality using (Stone; hasStoneStr; Sp; Booleω; evaluationMap)

  isTotallyDisconnected : CHaus → Type₀
  isTotallyDisconnected X =
    (x : fst X) → (y : fst X) → fst (ConnectedComponent X x y) → x ≡ y
  open import Cubical.Algebra.CommRing using (_$cr_; CommRingStr; IsCommRingHom; CommRingHom≡)
  open import Cubical.Algebra.BooleanRing using (BooleanRingStr; BooleanRing→CommRing)
  open import Cubical.Algebra.BooleanRing.Instances.Bool using (BoolBR)
  open import Cubical.Data.Bool using (true; false; false≢true)
  open import Cubical.Data.Empty as ⊥ using (⊥)

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
  postulate
    StoneCompactHausdorffTotallyDisconnected-backward : (X : CHaus)
      → isTotallyDisconnected X
      → hasStoneStr (fst X)

-- StoneSigmaClosedModule (tex Theorem 2214)

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
