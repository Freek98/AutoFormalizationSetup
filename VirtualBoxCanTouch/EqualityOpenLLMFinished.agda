{-# OPTIONS --lossy-unification #-}
-- Goal of this file: for a sequential colimit of finite sets, equality is
-- open: the path type (incl x ≡ y) is equivalent to the proposition
-- ∥ Σ k . EqualAt x y k ∥₁, a countable join of decidable propositions.
-- As a corollary, the colimit is a set (isSetX∞).
-- The connection to PropositionalTopology.Definitions is provided by
--   equalityIsOpen : (x y : X∞) → isOpen (x ≡ y)
-- via the binary sequence of decision bits of EqualAt; at incl-points the
-- open structure is given untruncated (hasOpenStrEqualityIncl).
--
-- Proof outline (encode/decode):
--   * Code n x y := ∥ EqWitness x y ∥₁, where an EqWitness is a level k
--     together with a proof that x and y have become equal in X k.
--   * EqualAt x y k is a decidable proposition, so ℕ-search
--     (Decidable→Collapsible) extracts an actual witness from the
--     truncation; decode turns the (standardized) witness into a path.
--   * decode's coherence over push reduces to two computations:
--       - EqWitnessDon'tCare: the path produced from a witness does not
--         depend on the witness.  Witnesses at the same level agree
--         because EqualAt is a prop; witnesses at different levels embed
--         into their max, and a one-step lift only changes the path by a
--         cancelling push (naturality of push).
--       - pushPath: composing with push moves a witness one level up.
--
-- This is the completed version of EqualityOpen.agda / EqualityOpenAlt.agda;
-- the remaining holes were finished by claude fable 5.
module LLMGeneratedFixes.EqualityOpenLLMFinished where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Path using (PathP≡compPath)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Bool hiding (_≤_ ; _≥_ ; isProp≤)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty renaming (rec to ex-falso)
open import Cubical.Data.Sequence
open import Cubical.HITs.SequentialColimit
open import Cubical.Relation.Nullary
open import Cubical.Data.FinSet
open import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Data.Nat.Order.Recursive using (Decidable→Collapsible)
open import PropositionalTopology.Definitions

-- ════════════════════════════════════════════════════════════════
-- § Inductively defined ≤. Standard ≤ is defined using the
-- difference, but it's annoying to do induction over the difference.
-- ════════════════════════════════════════════════════════════════

data _≤E_ : ℕ → ℕ → Type where
  ≤E-refl : {n : ℕ} → n ≤E n
  ≤E-step : {n m : ℕ} → n ≤E m → n ≤E suc m

≤E-trans : {n m k : ℕ} → n ≤E m → m ≤E k → n ≤E k
≤E-trans p ≤E-refl = p
≤E-trans p (≤E-step q) = ≤E-step (≤E-trans p q)

≤E-suc : {n m : ℕ} → n ≤E m → suc n ≤E suc m
≤E-suc ≤E-refl = ≤E-refl
≤E-suc (≤E-step p) = ≤E-step (≤E-suc p)

≤E→≤ : {n m : ℕ} → n ≤E m → n ≤ m
≤E→≤ ≤E-refl = ≤-refl
≤E→≤ (≤E-step p) = ≤-suc (≤E→≤ p)

≤→≤E : {n m : ℕ} → n ≤ m → n ≤E m
≤→≤E {n} {m} (k , p) = go n m k p where
  go : (n m k : ℕ) → k + n ≡ m → n ≤E m
  go n m zero p = subst (n ≤E_) p ≤E-refl
  go n zero (suc k) p = ex-falso (¬-<-zero (n , +-comm n (suc k) ∙ p))
  go n (suc m) (suc k) p = ≤E-step (go n m k (cong predℕ p))

≤E-retract : {n m : ℕ} (p : n ≤E m) → ≤→≤E (≤E→≤ p) ≡ p
≤E-retract ≤E-refl = transportRefl ≤E-refl
≤E-retract (≤E-step q) = ≤→≤E-suc (≤E→≤ q) ∙ cong ≤E-step (≤E-retract q) where
  ≤→≤E-suc : {n m : ℕ} (p : n ≤ m) → ≤→≤E (≤-suc p) ≡ ≤E-step (≤→≤E p)
  ≤→≤E-suc (k , e) = refl

isProp≤E : {n m : ℕ} → isProp (n ≤E m)
isProp≤E = isPropRetract ≤E→≤ ≤→≤E ≤E-retract isProp≤

≤E-Dec : (n m : ℕ) → Dec (n ≤E m)
≤E-Dec n m with ≤Dec n m
... | yes p = yes (≤→≤E p)
... | no ¬p = no (¬p ∘ ≤E→≤)

-- ════════════════════════════════════════════════════════════════
-- § Sequential colimits: iterated maps and their compatibility
-- with incl and push.
-- ════════════════════════════════════════════════════════════════

module SeqColimMaps {ℓ : Level} (S : Sequence ℓ) where
  private
    X = Sequence.obj S
    f = Sequence.map S

  ι : {n m : ℕ} → n ≤E m → X n → X m
  ι ≤E-refl x = x
  ι (≤E-step p) x = f (ι p x)

  ι-propIrrel : {n m : ℕ} (n≤m n≤m' : n ≤E m) (x : X n) → ι n≤m x ≡ ι n≤m' x
  ι-propIrrel n≤m n≤m' x = cong (λ r → ι r x) (isProp≤E n≤m n≤m')

  ι-comp : {n m k : ℕ} (p : n ≤E m) (q : m ≤E k) (x : X n)
    → ι q (ι p x) ≡ ι (≤E-trans p q) x
  ι-comp p ≤E-refl x = refl
  ι-comp p (≤E-step q) x = cong f (ι-comp p q x)

  -- ι-incl is an iterated composition of pushes; it is the only source
  -- of equalities in the colimit that we use.
  ι-incl : {n m : ℕ} (p : n ≤E m) (x : X n)
    → incl {X = S} x ≡ incl (ι p x)
  ι-incl ≤E-refl x = refl
  ι-incl (≤E-step p) x = ι-incl p x ∙ push (ι p x)

  -- ι commutes with the sequence map (along ≤E-suc) ...
  ι-suc : {n m : ℕ} (p : n ≤E m) (x : X n)
    → ι (≤E-suc p) (f x) ≡ f (ι p x)
  ι-suc ≤E-refl x = refl
  ι-suc (≤E-step p) x = cong f (ι-suc p x)

  -- ... and so does ι-incl: going up via push first and then iterating
  -- is the same as iterating first and then going up via push.
  ι-incl-suc : {n m : ℕ} (p : n ≤E m) (x : X n)
    → push x ∙ ι-incl (≤E-suc p) (f x) ∙ cong incl (ι-suc p x)
      ≡ ι-incl p x ∙ push (ι p x)
  ι-incl-suc ≤E-refl x =
      push x ∙ refl ∙ refl ≡⟨ cong (push x ∙_) (sym (lUnit refl)) ⟩
      push x ∙ refl        ≡⟨ sym (rUnit (push x)) ⟩
      push x               ≡⟨ lUnit (push x) ⟩
      refl ∙ push x ∎
  ι-incl-suc (≤E-step p) x =
      push x ∙ (W ∙ P) ∙ Cf ≡⟨ cong (push x ∙_) (sym (assoc W P Cf)) ⟩
      push x ∙ W ∙ P ∙ Cf   ≡⟨ cong (λ h → push x ∙ W ∙ h) (homotopyNatural push (ι-suc p x)) ⟩
      push x ∙ W ∙ Ci ∙ Q   ≡⟨ cong (push x ∙_) (assoc W Ci Q) ⟩
      push x ∙ (W ∙ Ci) ∙ Q ≡⟨ assoc (push x) (W ∙ Ci) Q ⟩
      (push x ∙ W ∙ Ci) ∙ Q ≡⟨ cong (_∙ Q) (ι-incl-suc p x) ⟩
      (ι-incl p x ∙ push (ι p x)) ∙ Q ∎
    where
      W  = ι-incl (≤E-suc p) (f x)
      P  = push (ι (≤E-suc p) (f x))
      Cf = cong (λ z → incl (f z)) (ι-suc p x)
      Ci = cong incl (ι-suc p x)
      Q  = push (f (ι p x))

  ι-pres : {n m k l : ℕ}
    (p : n ≤E k) (q : m ≤E k) (r : k ≤E l)
    (s : n ≤E l) (t : m ≤E l)
    (x : X n) (y : X m)
    → ι p x ≡ ι q y → ι s x ≡ ι t y
  ι-pres {n} {m} {k} {l} p q r s t x y e =
    ι s x                ≡⟨ ι-propIrrel s (≤E-trans p r) x ⟩
    ι (≤E-trans p r) x   ≡⟨ sym (ι-comp p r x) ⟩
    ι r (ι p x)          ≡⟨ cong (ι r) e ⟩
    ι r (ι q y)          ≡⟨ ι-comp q r y ⟩
    ι (≤E-trans q r) y   ≡⟨ ι-propIrrel (≤E-trans q r) t y ⟩
    ι t y               ∎

-- decidability of Σ-types of propositions
decΣProp : {ℓ ℓ' : Level} {A : Type ℓ } {B : A → Type ℓ'}
  → isProp A → ((a : A) → isProp (B a))
  → Dec A → ((a : A) → Dec (B a)) → Dec (Σ A B)
decΣProp Ap Bp (yes a) Bd with Bd a
... | yes b = yes (a , b)
... | no ¬b = no λ (a' , b) → ¬b (subst _ (Ap a' a) b)
decΣProp Ap Bp (no ¬a) Bd = no (¬a ∘ fst)

-- a decidable proposition holds iff its decision bit is true
Dec→Bool-true : {ℓ : Level} {A : Type ℓ} (d : Dec A) → Dec→Bool d ≡ true → A
Dec→Bool-true (yes a) _ = a
Dec→Bool-true (no ¬a) e = ex-falso (false≢true e)

Dec→Bool-complete : {ℓ : Level} {A : Type ℓ} (d : Dec A) → A → Dec→Bool d ≡ true
Dec→Bool-complete (yes _) _ = refl
Dec→Bool-complete (no ¬a) a = ex-falso (¬a a)

-- ════════════════════════════════════════════════════════════════
-- § Sequential colimits of finite sets: equality is open.
-- ════════════════════════════════════════════════════════════════

module FiniteSeqColim
  {ℓ : Level} (X : ℕ → Type ℓ) (Xmap : {n : ℕ} → X n → X (suc n))
  (isFin : (n : ℕ) → isFinSet (X n)) where

  Xseq : Sequence _
  Xseq .Sequence.obj = X
  Xseq .Sequence.map = Xmap

  open SeqColimMaps Xseq

  X∞ : Type _
  X∞ = SeqColim Xseq

  -- "x and y have become equal at level k": a decidable proposition.
  EqualAt : {n m : ℕ} → X n → X m → ℕ → Type _
  EqualAt {n} {m} x y k =
    Σ[ p ∈ n ≤E k ] Σ[ q ∈ m ≤E k ] ι p x ≡ ι q y

  isPropEqualAt : {n m : ℕ} {x : X n} {y : X m} (k : ℕ) → isProp (EqualAt x y k)
  isPropEqualAt k =
    isPropΣ isProp≤E λ _ →
    isPropΣ isProp≤E λ _ →
    isFinSet→isSet (isFin k) _ _

  isDecEqualAt : {n m : ℕ} {x : X n} {y : X m} (k : ℕ) → Dec (EqualAt x y k)
  isDecEqualAt {n} {m} k =
    decΣProp isProp≤E (λ _ → isPropΣ isProp≤E λ _ → isFinSet→isSet (isFin k) _ _)
      (≤E-Dec n k) λ _ →
    decΣProp isProp≤E (λ _ → isFinSet→isSet (isFin k) _ _)
      (≤E-Dec m k) λ _ →
    isFinSet→Discrete (isFin k) _ _

  EqWitness : {n m : ℕ} → X n → X m → Type _
  EqWitness x y = Σ[ k ∈ ℕ ] EqualAt x y k

  -- ℕ-search: a witness can be extracted from the truncation.
  EqWitness-splitSupport : {n m : ℕ} (x : X n) (y : X m) → SplitSupport (EqWitness x y)
  EqWitness-splitSupport x y =
    Collapsible→SplitSupport (Decidable→Collapsible isPropEqualAt isDecEqualAt)

  -- replace a witness by the canonical one found by the search
  standardizeEqWitness : {n m : ℕ} {x : X n} {y : X m} → EqWitness x y → EqWitness x y
  standardizeEqWitness {n} {m} {x} {y} = EqWitness-splitSupport x y ∘ ∣_∣₁

  EqWitness-refl : {n : ℕ} (x : X n) → EqWitness x x
  EqWitness-refl x = _ , ≤E-refl , ≤E-refl , refl

  EqWitness-sym : {n m : ℕ} (x : X n) (y : X m) → EqWitness x y → EqWitness y x
  EqWitness-sym _ _ (k , p , q , e) = k , q , p , sym e

  EqWitness-suc : {n : ℕ} (x : X n) → EqWitness x (Xmap x)
  EqWitness-suc {n = n} x = suc n , ≤E-step ≤E-refl , ≤E-refl , refl

  EqWitness-trans : {n m l : ℕ} (x : X n) (y : X m) (z : X l)
    → EqWitness x y → EqWitness y z → EqWitness x z
  EqWitness-trans x y z (j , n≤j , m≤j , ιx≡ιy) (k , m≤k , l≤k , ιy≡ιz) =
    max j k ,
    n≤max ,
    l≤max ,
    ι-pres n≤j m≤j j≤max n≤max m≤max x y ιx≡ιy
    ∙
    ι-pres m≤k l≤k k≤max m≤max l≤max y z ιy≡ιz
    where
    j≤max = ≤→≤E (left-≤-max {m = j})
    k≤max = ≤→≤E (right-≤-max {m = j})
    n≤max = ≤E-trans n≤j j≤max
    m≤max = ≤E-trans m≤j j≤max
    l≤max = ≤E-trans l≤k k≤max

  EqWitness→Path : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → incl x ≡ incl y
  EqWitness→Path {n = n} {m} x y (k , n≤k , m≤k , p) =
    ι-incl n≤k x ∙ cong incl p ∙ sym (ι-incl m≤k y)

  EqWitness→StandardPath : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → incl x ≡ incl y
  EqWitness→StandardPath x y = EqWitness→Path x y ∘ standardizeEqWitness

  EqWitness-push→ : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → EqWitness x (Xmap y)
  EqWitness-push→ x y w =
    EqWitness-trans x y _ w (EqWitness-suc y)

  EqWitness-push→standard : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x y → EqWitness x (Xmap y)
  EqWitness-push→standard x y w =
    standardizeEqWitness (EqWitness-push→ x y w)

  EqWitness-push← : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x (Xmap y) → EqWitness x y
  EqWitness-push← x y w =
    EqWitness-trans x (Xmap y) y w
    (EqWitness-sym y _ (EqWitness-suc y))

  EqWitness-push←standard : {n m : ℕ} (x : X n) (y : X m)
    → EqWitness x (Xmap y) → EqWitness x y
  EqWitness-push←standard x y w = standardizeEqWitness (EqWitness-push← x y w)

  -- ════════════════════════════════════════════════════════════════
  -- § EqWitness→Path does not depend on the witness ("don't care").
  -- Strategy: EqualAt x y k is a prop for each fixed k, so the only
  -- content is comparing levels; any two levels embed in their max,
  -- and a one-step lift changes the path by a cancelling push.
  -- ════════════════════════════════════════════════════════════════

  liftEqualAt : {n m k : ℕ} {x : X n} {y : X m}
    → EqualAt x y k → EqualAt x y (suc k)
  liftEqualAt (p , q , e) = ≤E-step p , ≤E-step q , cong Xmap e

  liftEqualAt* : {n m k k' : ℕ} {x : X n} {y : X m} (r : k ≤E k')
    → EqualAt x y k → EqualAt x y k'
  liftEqualAt* {x = x} {y = y} r (p , q , e) =
    ≤E-trans p r , ≤E-trans q r ,
    sym (ι-comp p r x) ∙ cong (ι r) e ∙ ι-comp q r y

  -- one-step lift: the two extra pushes cancel by naturality of push
  liftPath : {n m k : ℕ} (x : X n) (y : X m) (w : EqualAt x y k)
    → EqWitness→Path x y (k , w) ≡ EqWitness→Path x y (suc k , liftEqualAt w)
  liftPath x y (p , q , e) = sym (
      (A ∙ B) ∙ Cf ∙ sym (D ∙ E)
        ≡⟨ cong (λ h → (A ∙ B) ∙ Cf ∙ h) (symDistr D E) ⟩
      (A ∙ B) ∙ Cf ∙ sym E ∙ sym D
        ≡⟨ cong ((A ∙ B) ∙_) (assoc Cf (sym E) (sym D)) ⟩
      (A ∙ B) ∙ (Cf ∙ sym E) ∙ sym D
        ≡⟨ sym (assoc A B ((Cf ∙ sym E) ∙ sym D)) ⟩
      A ∙ B ∙ (Cf ∙ sym E) ∙ sym D
        ≡⟨ cong (A ∙_) (assoc B (Cf ∙ sym E) (sym D)) ⟩
      A ∙ (B ∙ Cf ∙ sym E) ∙ sym D
        ≡⟨ cong (λ h → A ∙ h ∙ sym D) middle ⟩
      A ∙ Ce ∙ sym D ∎)
    where
      A  = ι-incl p x
      B  = push (ι p x)
      Ce = cong incl e
      Cf = cong (λ z → incl (Xmap z)) e
      D  = ι-incl q y
      E  = push (ι q y)
      middle : B ∙ Cf ∙ sym E ≡ Ce
      middle =
        B ∙ Cf ∙ sym E   ≡⟨ assoc B Cf (sym E) ⟩
        (B ∙ Cf) ∙ sym E ≡⟨ cong (_∙ sym E) (homotopyNatural push e) ⟩
        (Ce ∙ E) ∙ sym E ≡⟨ sym (assoc Ce E (sym E)) ⟩
        Ce ∙ E ∙ sym E   ≡⟨ cong (Ce ∙_) (rCancel E) ⟩
        Ce ∙ refl        ≡⟨ sym (rUnit Ce) ⟩
        Ce ∎

  -- many-step lift, by induction on ≤E; prop-ness of EqualAt absorbs
  -- the witness mismatch at each end
  liftPath* : {n m k k' : ℕ} (x : X n) (y : X m) (r : k ≤E k')
    (w : EqualAt x y k) (w' : EqualAt x y k')
    → EqWitness→Path x y (k , w) ≡ EqWitness→Path x y (k' , w')
  liftPath* {k = k} x y ≤E-refl w w' =
    cong (λ u → EqWitness→Path x y (k , u)) (isPropEqualAt k w w')
  liftPath* {k = k} x y (≤E-step {m = k₀} r) w w' =
    liftPath* x y r w wᵣ
    ∙ liftPath x y wᵣ
    ∙ cong (λ u → EqWitness→Path x y (suc k₀ , u))
        (isPropEqualAt (suc k₀) (liftEqualAt wᵣ) w')
    where
      wᵣ = liftEqualAt* r w

  EqWitnessDon'tCare : {n m : ℕ} (x : X n) (y : X m)
    (a b : EqWitness x y) → EqWitness→Path x y a ≡ EqWitness→Path x y b
  EqWitnessDon'tCare x y (k , w) (k' , w') =
    liftPath* x y k≤K w wK ∙ sym (liftPath* x y k'≤K w' wK)
    where
      k≤K  = ≤→≤E (left-≤-max {m = k} {n = k'})
      k'≤K = ≤→≤E (right-≤-max {n = k'} {m = k})
      wK   = liftEqualAt* k≤K w

  -- ════════════════════════════════════════════════════════════════
  -- § Composing with push moves a witness one level up.
  -- For the canonical successor witness this is a direct computation;
  -- don't-care then gives it for every witness.
  -- ════════════════════════════════════════════════════════════════

  pushPath : {n m k : ℕ} (x : X n) (y : X m)
    (p : n ≤E k) (q : m ≤E k) (e : ι p x ≡ ι q y)
    → EqWitness→Path x y (k , p , q , e) ∙ push y
      ≡ EqWitness→Path x (Xmap y)
          (suc k , ≤E-step p , ≤E-suc q , cong Xmap e ∙ sym (ι-suc q y))
  pushPath x y p q e = sym (
      (A ∙ B) ∙ cong incl (cong Xmap e ∙ sym (ι-suc q y)) ∙ sym G
        ≡⟨ cong (λ h → (A ∙ B) ∙ h ∙ sym G) (cong-∙ incl (cong Xmap e) (sym (ι-suc q y))) ⟩
      (A ∙ B) ∙ (Cf ∙ sym S) ∙ sym G
        ≡⟨ cong ((A ∙ B) ∙_) (sym (assoc Cf (sym S) (sym G))) ⟩
      (A ∙ B) ∙ Cf ∙ sym S ∙ sym G
        ≡⟨ sym (assoc A B (Cf ∙ sym S ∙ sym G)) ⟩
      A ∙ B ∙ Cf ∙ sym S ∙ sym G
        ≡⟨ cong (A ∙_) (assoc B Cf (sym S ∙ sym G)) ⟩
      A ∙ (B ∙ Cf) ∙ sym S ∙ sym G
        ≡⟨ cong (λ h → A ∙ h ∙ sym S ∙ sym G) (homotopyNatural push e) ⟩
      A ∙ (Ce ∙ E) ∙ sym S ∙ sym G
        ≡⟨ cong (A ∙_) (sym (assoc Ce E (sym S ∙ sym G))) ⟩
      A ∙ Ce ∙ E ∙ sym S ∙ sym G
        ≡⟨ cong (λ h → A ∙ Ce ∙ h) cancelTail ⟩
      A ∙ Ce ∙ sym D ∙ Py
        ≡⟨ cong (A ∙_) (assoc Ce (sym D) Py) ⟩
      A ∙ (Ce ∙ sym D) ∙ Py
        ≡⟨ assoc A (Ce ∙ sym D) Py ⟩
      (A ∙ Ce ∙ sym D) ∙ Py ∎)
    where
      A  = ι-incl p x
      B  = push (ι p x)
      Ce = cong incl e
      Cf = cong (λ z → incl (Xmap z)) e
      D  = ι-incl q y
      E  = push (ι q y)
      G  = ι-incl (≤E-suc q) (Xmap y)
      S  = cong incl (ι-suc q y)
      Py = push y
      E≡ : E ≡ sym D ∙ Py ∙ G ∙ S
      E≡ =
        E               ≡⟨ lUnit E ⟩
        refl ∙ E        ≡⟨ cong (_∙ E) (sym (lCancel D)) ⟩
        (sym D ∙ D) ∙ E ≡⟨ sym (assoc (sym D) D E) ⟩
        sym D ∙ D ∙ E   ≡⟨ cong (sym D ∙_) (sym (ι-incl-suc q y)) ⟩
        sym D ∙ Py ∙ G ∙ S ∎
      cancelTail : E ∙ sym S ∙ sym G ≡ sym D ∙ Py
      cancelTail =
        E ∙ sym S ∙ sym G
          ≡⟨ cong (_∙ sym S ∙ sym G) E≡ ⟩
        (sym D ∙ Py ∙ G ∙ S) ∙ sym S ∙ sym G
          ≡⟨ sym (assoc (sym D) (Py ∙ G ∙ S) (sym S ∙ sym G)) ⟩
        sym D ∙ (Py ∙ G ∙ S) ∙ sym S ∙ sym G
          ≡⟨ cong (sym D ∙_) (sym (assoc Py (G ∙ S) (sym S ∙ sym G))) ⟩
        sym D ∙ Py ∙ (G ∙ S) ∙ sym S ∙ sym G
          ≡⟨ cong (λ h → sym D ∙ Py ∙ (G ∙ S) ∙ h) (sym (symDistr G S)) ⟩
        sym D ∙ Py ∙ (G ∙ S) ∙ sym (G ∙ S)
          ≡⟨ cong (λ h → sym D ∙ Py ∙ h) (rCancel (G ∙ S)) ⟩
        sym D ∙ Py ∙ refl
          ≡⟨ cong (sym D ∙_) (sym (rUnit Py)) ⟩
        sym D ∙ Py ∎

  EqWitnessPathIsPushComposition : {n m : ℕ} (x : X n) (y : X m)
    (k  : ℕ) → (n≤k  : n ≤E k ) → (m≤k  : m ≤E k ) → (p : ι n≤k  x ≡ ι m≤k  y) →
    (k' : ℕ) → (n≤k' : n ≤E k') → (m≤k' : suc m ≤E k') → (q : ι n≤k' x ≡ ι m≤k' (Xmap y)) →
    EqWitness→Path x y (k , n≤k , m≤k , p) ∙ push y ≡
    EqWitness→Path x (Xmap y) (k' , n≤k' , m≤k' , q)
  EqWitnessPathIsPushComposition x y k n≤k m≤k p k' n≤k' m≤k' q =
    pushPath x y n≤k m≤k p
    ∙ EqWitnessDon'tCare x (Xmap y)
        (suc k , ≤E-step n≤k , ≤E-suc m≤k , cong Xmap p ∙ sym (ι-suc m≤k y))
        (k' , n≤k' , m≤k' , q)

  EqWitnessPathComp : {n m : ℕ} (x : X n) (y : X m) →
   (a : EqWitness x y) → (b : EqWitness x (Xmap y)) →
   EqWitness→Path x y a ∙ push y ≡ EqWitness→Path x (Xmap y) b
  EqWitnessPathComp x y (k , n≤k , m≤k , p) (k' , n≤k' , m≤k' , q) =
    EqWitnessPathIsPushComposition x y k n≤k m≤k p k' n≤k' m≤k' q

  -- ════════════════════════════════════════════════════════════════
  -- § encode/decode.
  -- ════════════════════════════════════════════════════════════════

  Code : (n : ℕ) → X n → X∞ → Type _
  Code n x (incl y) = ∥ EqWitness x y ∥₁
  Code n x (push y i) =
    hPropExt squash₁ squash₁
      (PT.map (EqWitness-push→standard x y))
      (PT.map (EqWitness-push←standard x y)) i

  encode : (n : ℕ) (x : X n) (y : X∞) → incl x ≡ y → Code n x y
  encode n x y p = J (λ y _ → Code n x y) ∣ EqWitness-refl x ∣₁ p

  decode : (n : ℕ) (x : X n) (y : X∞) → Code n x y → incl x ≡ y
  decode n x (incl y) c = EqWitness→StandardPath x y (EqWitness-splitSupport x y c)
  decode n x (push {n = m} y i) c =
    ua→ {A₀ = ∥ EqWitness x y ∥₁ } {A₁ = ∥ EqWitness x (Xmap y) ∥₁ }
        {e = propBiimpl→Equiv squash₁ squash₁
        (PT.map $ EqWitness-push→standard x y) (PT.map $ EqWitness-push←standard x y)  }
        {B = λ j → incl x ≡ (push y j) }
        {f₀ = λ c → EqWitness→StandardPath x y (EqWitness-splitSupport x y c)}
        {f₁ = λ c → EqWitness→StandardPath x (Xmap y) (EqWitness-splitSupport x (Xmap y) c )}
        f i c where
          f : (a : ∥ EqWitness x y ∥₁) → PathP (λ j → incl x ≡ push y j)
            (EqWitness→StandardPath x y        (EqWitness-splitSupport x y a))
            (EqWitness→StandardPath x (Xmap y) (EqWitness-splitSupport x (Xmap y)
            (PT.map (EqWitness-push→standard x y) a)))
          f a = transport (sym (PathP≡compPath _ (push y) _))
            (EqWitnessPathComp x y
              (standardizeEqWitness (EqWitness-splitSupport x y a))
              (standardizeEqWitness (EqWitness-splitSupport x (Xmap y)
                (PT.map (EqWitness-push→standard x y) a))))

  -- ════════════════════════════════════════════════════════════════
  -- § encode and decode are mutually inverse, so equality in X∞ is
  -- (equivalent to) a countable join of decidable propositions.
  -- ════════════════════════════════════════════════════════════════

  isPropCode : (n : ℕ) (x : X n) (y : X∞) → isProp (Code n x y)
  isPropCode n x = SeqColim→Prop (λ _ → isPropIsProp) (λ _ _ → squash₁)

  encode-decode : (n : ℕ) (x : X n) (y : X∞) (c : Code n x y)
    → encode n x y (decode n x y c) ≡ c
  encode-decode n x y c = isPropCode n x y _ c

  decode-encode : (n : ℕ) (x : X n) (y : X∞) (p : incl x ≡ y)
    → decode n x y (encode n x y p) ≡ p
  decode-encode n x y p =
    J (λ y p → decode n x y (encode n x y p) ≡ p)
      (cong (decode n x (incl x))
         (JRefl (λ y _ → Code n x y) ∣ EqWitness-refl x ∣₁)
       ∙ decodeRefl) p
    where
      decodeRefl : decode n x (incl x) ∣ EqWitness-refl x ∣₁ ≡ refl
      decodeRefl =
        EqWitnessDon'tCare x x
          (standardizeEqWitness (EqWitness-splitSupport x x ∣ EqWitness-refl x ∣₁))
          (EqWitness-refl x)
        ∙ sym (lUnit (refl ∙ refl))
        ∙ sym (lUnit refl)

  Path≃Code : (n : ℕ) (x : X n) (y : X∞) → (incl x ≡ y) ≃ Code n x y
  Path≃Code n x y =
    isoToEquiv (iso (encode n x y) (decode n x y)
      (encode-decode n x y) (decode-encode n x y))

  isPropPathFromIncl : (n : ℕ) (x : X n) (y : X∞) → isProp (incl x ≡ y)
  isPropPathFromIncl n x y =
    isOfHLevelRespectEquiv 1 (invEquiv (Path≃Code n x y)) (isPropCode n x y)

  isSetX∞ : isSet X∞
  isSetX∞ =
    SeqColim→Prop (λ _ → isPropΠ λ _ → isPropIsProp)
      (λ n x → isPropPathFromIncl n x)

  -- ════════════════════════════════════════════════════════════════
  -- § Equality is open in the sense of PropositionalTopology:
  -- the sequence of decision bits of EqualAt x y is a binary sequence
  -- whose hitting true is equivalent to incl x ≡ incl y.
  -- ════════════════════════════════════════════════════════════════

  EqualAtBool : {n m : ℕ} (x : X n) (y : X m) → ℕ → Bool
  EqualAtBool x y k = Dec→Bool (isDecEqualAt {x = x} {y = y} k)

  -- at incl-points the open structure is given untruncated
  hasOpenStrEqualityIncl : {n m : ℕ} (x : X n) (y : X m)
    → hasOpenStr (Path X∞ (incl x) (incl y))
  hasOpenStrEqualityIncl {n = n} x y =
    isPropPathFromIncl n x (incl y) ,
    EqualAtBool x y ,
    (λ p → witnessBit (EqWitness-splitSupport x y (encode n x (incl y) p))) ,
    (λ (k , e) → EqWitness→Path x y (k , Dec→Bool-true (isDecEqualAt {x = x} {y = y} k) e))
    where
      witnessBit : EqWitness x y → Σ[ k ∈ ℕ ] EqualAtBool x y k ≡ true
      witnessBit (k , w) = k , Dec→Bool-complete (isDecEqualAt {x = x} {y = y} k) w

  equalityIsOpen : (x y : X∞) → isOpen (x ≡ y)
  equalityIsOpen =
    SeqColim→Prop (λ _ → isPropΠ λ _ → squash₁) λ n x →
    SeqColim→Prop (λ _ → squash₁) λ m y →
    ∣ hasOpenStrEqualityIncl x y ∣₁
