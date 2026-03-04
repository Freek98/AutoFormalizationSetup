{-# OPTIONS --cubical --guardedness #-}
module work.test-seqcolim-set where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat using (ℕ; zero; suc)
open import Cubical.Data.Nat.Properties using (+-assoc; +-comm; +-suc; +-zero; isSetℕ)
open import Cubical.Data.Sequence using (Sequence)
open import Cubical.HITs.SequentialColimit using (SeqColim; incl; push)
open import Cubical.HITs.SequentialColimit.Properties using (SeqColim→Prop; elimShifted; ElimDataShifted; elimdata-shift)

open Sequence

module SetColim (S : Sequence ℓ-zero) (allSet : (n : ℕ) → isSet (obj S n)) where

  shiftS : (k : ℕ) {n : ℕ} → obj S n → obj S (k + n)
  shiftS zero x = x
  shiftS (suc k) x = map S (shiftS k x)

  pushChain : (k : ℕ) {n : ℕ} (x : obj S n) → incl x ≡ incl (shiftS k x)
  pushChain zero x = refl
  pushChain (suc k) x = pushChain k x ∙ push (shiftS k x)

  -- shiftS composes: shiftS j (shiftS k x) = shiftS (j + k) x (definitionally!)
  -- because shiftS 0 (shiftS k x) = shiftS k x = shiftS (0+k) x
  -- and shiftS (suc j) (shiftS k x) = map (shiftS j (shiftS k x))
  --   = map (shiftS (j+k) x) = shiftS (suc (j+k)) x = shiftS ((suc j)+k) x

  -- Code family for encode-decode
  -- For fixed n₀, x₀, define Code at level k + n₀:
  --   Code_{k} x = shiftS k x₀ ≡ x  (equality in obj S (k + n₀))
  -- This is a proposition by allSet.
  -- Push coherence: need (shiftS k x₀ ≡ x) →P (map (shiftS k x₀) ≡ map x)
  --   as a PathP over push x. Since both are hProps, isProp→PathP gives this.

  -- But the push coherence uses the universe, so P(push x i) needs to be
  -- identified. With elimShifted, the library handles the transport.

  -- Let's try: define Code as a function into hProp using elimShifted
  module _ (n₀ : ℕ) (x₀ : obj S n₀) where

    -- The code data shifted by n₀
    CodeDataHProp : ElimDataShifted S n₀ (λ _ → hProp ℓ-zero)
    ElimDataShifted.inclP CodeDataHProp {k} x =
      (shiftS k x₀ ≡ x) , allSet (k + n₀) (shiftS k x₀) x
    ElimDataShifted.pushP CodeDataHProp {k} x =
      isProp→PathP (λ i → isSetHProp _ _) _ _

    -- Hmm wait: pushP needs PathP (λ i → hProp) not PathP (λ i → isProp (hProp ...))
    -- pushP : {k : ℕ} (x : obj S (k + n₀))
    --   → PathP (λ i → hProp ℓ-zero) (inclP x) (inclP (map S x))
    -- where inclP x = (shiftS k x₀ ≡ x, ...) and inclP (map x) = (shiftS (suc k) x₀ ≡ map x, ...)
    -- The type is: (shiftS k x₀ ≡ x, ...) ≡ (map (shiftS k x₀) ≡ map x, ...) as hProps.
    -- Two hProps are equal iff logically equivalent.
    -- Forward: cong map. Backward: ???
    -- We DON'T have the backward direction without injectivity.
    -- So isProp→PathP won't work here — the types aren't over the same universe path.

    -- Wait: PathP (λ i → hProp ℓ-zero) P Q = P ≡ Q (since the base is constant)
    -- And P ≡ Q for hProps means P ≃ Q (by univalence restricted to hProps)
    -- which means P → Q and Q → P.

    -- We DON'T have Q → P (map (shiftS k x₀) ≡ map x → shiftS k x₀ ≡ x)

    -- CONCLUSION: This simple code doesn't work without injective maps.
    -- Need a different approach.

  -- Alternative: use TRUNCATED code
  -- Code at level k + n₀ for x is: ∥ Σ j. shiftS (j+k) x₀ ≡ shiftS j x ∥₁
  -- But this has the +-assoc issue: shiftS (j+k) x₀ is at level (j+k)+n₀
  -- and shiftS j x is at level j+(k+n₀) which differ by +-assoc.

  -- Let's try the simplest possible approach: use SeqColim of path types
  module _ (n₀ : ℕ) (x₀ : obj S n₀) where

    -- Path sequence: for fixed x at level k+n₀,
    -- the paths at increasing levels
    pathSeq : {k : ℕ} → obj S (k + n₀) → Sequence ℓ-zero
    obj (pathSeq {k} x) j = shiftS j (shiftS k x₀) ≡ shiftS j x
    map (pathSeq {k} x) = cong (map S)
    -- Types: shiftS j (shiftS k x₀) : obj S (j + (k + n₀))
    --        shiftS j x : obj S (j + (k + n₀))
    -- These ARE at the same level! ✓ (because both are shiftS j of things at level k+n₀)

    -- isProp of SeqColim of path types:
    -- Each level is a prop (by allSet at level j + (k + n₀))
    -- So SeqColim pathSeq is a prop (by isPropSeqColimProp)

    Code : {k : ℕ} → obj S (k + n₀) → Type
    Code {k} x = SeqColim (pathSeq x)

    isPropCode : {k : ℕ} (x : obj S (k + n₀)) → isProp (Code x)
    isPropCode {k} x = isPropSeqColimProp (pathSeq x)
      (λ j → allSet (j + (k + n₀)) _ _)
      where
      open import work.Part07

    -- Wait, I need isPropSeqColimProp from Part07, not from the library.
    -- Let me import it. Actually, let me just reprove it inline.
    -- Or better yet, let me use SeqColim→Prop.

    -- Actually I need to think about this more. The Code uses SeqColim
    -- of a sequence of props. This IS a prop by a SeqColim→Prop argument.
    -- But we need isPropSeqColimProp, which is in Part07 (custom).
    -- Let me just state it as a hole for now.

    -- code-refl: the reflexivity witness
    code-refl : Code {k = 0} x₀
    code-refl = incl {n = 0} refl

    -- encode: transport of code-refl
    -- encode : incl {n₀} x₀ ≡ c → Code... c
    -- This requires Code to be defined on ALL of SeqColim, using elimShifted.

    -- The full Code family on SeqColim:
    CodeFull : SeqColim S → Type
    CodeFull = elimShifted S n₀ (λ _ → Type ℓ-zero) codeData where
      codeData : ElimDataShifted S n₀ (λ _ → Type ℓ-zero)
      ElimDataShifted.inclP codeData {k} x = Code x
      ElimDataShifted.pushP codeData {k} x = ua equiv where
        -- Need: Code x ≃ Code (map S x)
        -- Code x = SeqColim (pathSeq {k} x)
        -- Code (map S x) = SeqColim (pathSeq {suc k} (map S x))
        -- obj (pathSeq {k} x) j = shiftS j (shiftS k x₀) ≡ shiftS j x
        -- obj (pathSeq {suc k} (map S x)) j = shiftS j (shiftS (suc k) x₀) ≡ shiftS j (map S x)
        --   = shiftS j (map S (shiftS k x₀)) ≡ shiftS j (map S x)
        -- So obj (pathSeq {suc k} (map S x)) j = shiftS j (map S (shiftS k x₀)) ≡ shiftS j (map S x)
        -- And obj (pathSeq {k} x) (suc j) = shiftS (suc j) (shiftS k x₀) ≡ shiftS (suc j) x
        --   = map S (shiftS j (shiftS k x₀)) ≡ map S (shiftS j x)
        -- So pathSeq {suc k} (map S x) is the SHIFT of pathSeq {k} x by one level!
        -- And SeqColim of a shifted sequence ≃ SeqColim of original!
        equiv : Code x ≃ Code (map S x)
        equiv = {!!}
        -- THIS IS THE KEY: Code (map x) = SeqColim (shift pathSeq x)
        -- ≃ SeqColim (pathSeq x) = Code x
        -- The shifting iso exists in the library!
</content>
</invoke>