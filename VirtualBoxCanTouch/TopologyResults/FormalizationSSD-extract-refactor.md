# Refactoring `extract` to run on `noHitBefore` / `firstHitOnly`

This is the suggestion you asked for after the build was fixed: rebuild
`BinarySequences.Properties.extractFirstHitInBinarySequence.extract` so it is assembled
from the binary sequences `noHitBefore` and `firstHitOnly` (the ones you started in
`BinarySequences/HitsInTheSequence.agda`), rather than from the `firstHitAt` /
`firstSeenBefore` / `decidableFirst` predicate machinery.

Everything below is **type-checked** — see `ExtractRefactorProposal.agda`
(module `ExtractViaFirstHitOnly`), which compiles against your library with
`agda 2.6.4.3` / `cubical-0.9`. It is written self-contained (re-stating the two
sequence definitions) only so it can be checked without depending on the open holes
currently in `HitsInTheSequence`.

## The idea in one line

`firstHitOnly α` hits 1 **at most once**, therefore `Σℕ (firstHitOnly α)` is a
**proposition**, therefore split support comes for free from idempotence of `∥_∥₁`:

```
∥ Σℕ α ∥₁                                   -- hypothesis
  → ∥ Σℕ (firstHitOnly α) ∥₁                 -- PT.map findFirst   (the only search)
  → Σℕ (firstHitOnly α)                       -- PT.rec isProp id   (truncated prop = prop)
  → Σℕ α                                       -- forget the noHitBefore conjunct
```

The middle arrow, `PT.rec isPropΣfirstHitOnly (idfun _)`, is the crux. The current
`extract` cannot do this because `Σℕ α` is not a proposition (α may hit many times), so
it laboriously builds the *first-hit predicate* `firstHitAt` and proves it decidable and
propositional. Replacing `α` by `firstHitOnly α` makes the target a genuine proposition
and the elimination trivial.

## Why this matches the comment you left in `Properties.agda`

Your note above the module (lines 80–82) says:

> firstHitAt is actually a binary sequence … the conjunction of the binary sequence
> witnessing that there have only been zeros before n and alpha itself … I think it's
> better to define those sequences and derive the noHitBefore property on itself.

Exactly. `firstHitAt m = (α m ≡ true) × (∀ k < m → α k ≡ false)` is the *propositional*
shadow of the *Boolean* sequence `firstHitOnly m = α m and noHitBefore m`. Once you work
with the Boolean sequence, "the first-hit predicate is a proposition" stops being a
bespoke proof (`isPropFirstHit`, via the `lt`/`eq`/`gt` case split) and becomes the
generic fact "a sequence that hits at most once has a propositional `Σℕ`".

## The pieces, and where they go

| ingredient | what it is | lives in |
|---|---|---|
| `noHitBefore`, `firstHitOnly` | the two sequences | `HitsInTheSequence` (already there) |
| `noHitBefore-spec` | `noHitBefore n ≡ true → ∀ k<n. α k ≡ false` | `HitsInTheSequence` (new, 4 lines) |
| `atMostOneFirstHit` | `hits1AtMostOnce (firstHitOnly α)` | **fills HOLE #1** |
| `isPropΣfirstHitOnly` | `isProp (Σℕ (firstHitOnly α))` | **fills HOLE #2** |
| `findFirst` | `Σℕ α → Σℕ (firstHitOnly α)` (bounded search) | `Properties` |
| `extract` | `∥ Σℕ α ∥₁ → Σℕ α` | `Properties` (replaces the module) |

### Filling your two holes in `HitsInTheSequence`

Your current skeleton there induces on both indices and tries to descend with `shift`,
which gets awkward. The proposal proves both directly:

* **`atMostOneFirstHit`** — `firstHitOnly n ≡ true` unpacks (via `and-true→×`) to
  `α n ≡ true` together with `noHitBefore n ≡ true`. Trichotomy `n ≟ m`: the `eq` case is
  done; in the `lt` case `noHitBefore-spec m … n (n<m)` forces `α n ≡ false`, contradicting
  `α n ≡ true`; `gt` is symmetric. No induction on the indices, no `shift`.

* **`isPropFirstHitOnly`** — once you have at-most-once it is one line:
  `Σ≡Prop (λ k → isSetBool (firstHitOnly k) true) (atMostOneFirstHit n m fn fm)`.
  (This is also exactly the generic lemma "`hits1AtMostOnce α → isProp (Σℕ α)`", which
  might be worth stating on its own next to `isPropHits1AtMostOnce`.)

### The one remaining search, now bounded and structural

The current module finds the first hit with `decidableFirst` (an *un*bounded `Dec`
search) plus `notSeenAtToNoHitBefore`, `findFirst`, `extractFirst`. In the new version the
only search is `findFirst : Σℕ α → Σℕ (firstHitOnly α)`, and it is a **structural**
induction on a fuel argument, because the witness index `n` is an explicit upper bound:

```agda
earlierHit : noHitBefore n ≡ false → Σ[ k ] (k < n) × (α k ≡ true)
   -- if noHitBefore is false, some earlier index already hit; read it off by
   -- induction on n using  a and b ≡ false → (a ≡ false) ⊎ (b ≡ false).

findFirstAux (suc b) n (n<sb) αn with  noHitBefore n =B true
   ... | yes nhb = n , …                       -- n is itself the first hit
   ... | no  ¬nhb = findFirstAux b k … αk        -- k < n ≤ b, recurse with less fuel

findFirst (n , αn) = findFirstAux (suc n) n ≤-refl αn
```

No `Cubical.Induction.WellFounded`, no accessibility predicate — the decrease `k < n ≤ b`
is visible to the termination checker.

## What gets deleted

In `extractFirstHitInBinarySequence`, the refactor removes `firstHitAt`, `first-hit`,
`firstSeenBefore`, `pred¬firstSeenBefore`, `isPropFirstHitAt`, `isPropFirstHit`,
`notSeenAtToNoHitBefore`, `decidableFirst`, `findFirst` (old), `extractFirst`,
`firstHit→Witness` — roughly 60 lines — and replaces them with the table above
(`findFirst` + `forget` + `extract`, ~12 lines, the heavy lemmas living in
`HitsInTheSequence`).

`hasSplitSupportΣℕ` at the bottom of `Properties.agda` keeps the same type
(`SplitSupport (Σℕ1 α)`); only its right-hand side changes to the new `extract`.

## Drop-in shape for the library

```agda
-- BinarySequences/HitsInTheSequence.agda
noHitBefore      : binarySequence → ℕ → Bool         -- as you have it
firstHitOnly     : binarySequence → binarySequence    -- as you have it
noHitBefore-spec : (α : _) (n : _) → noHitBefore α n ≡ true → (k : _) → k < n → α k ≡ false
atMostOneFirstHit   : (α : _) → hits1AtMostOnce (firstHitOnly α)        -- HOLE #1
isPropFirstHitOnly  : (α : _) → isProp (Σℕ (firstHitOnly α))            -- HOLE #2

-- BinarySequences/Properties.agda  (module extractFirstHitInBinarySequence α)
findFirst : Σℕ α → Σℕ (firstHitOnly α)
extract   : ∥ Σℕ α ∥₁ → Σℕ α
extract   = forget ∘ PT.rec (isPropFirstHitOnly α) (idfun _) ∘ PT.map findFirst
```

Note `Σα↔ΣfirstHitOnly` in the project file `AtMostOnce.agda` currently proves its
forward direction *via the old `extractFirst`*. If you adopt this, that forward direction
is just `findFirst`, so `AtMostOnce` can drop its dependency on the old machinery too —
and `firstHitOnlyAtMostOnce` there becomes a one-liner `atMostOneFirstHit α`.

## Open choice for you

`noHitBefore` is currently defined by `noHitBefore (suc n) = noHitBefore n and not (α n)`
— it looks *backwards* over the prefix. The dual definition
`noHitBefore' (suc n) = not (α 0) and noHitBefore' (shift α) n` looks *forwards* and is
what your `shift`-based skeleton was reaching for. Both work; the backward one makes
`noHitBefore-spec` a clean two-case induction (shown here), the forward one composes more
nicely with `shift`. I'd keep the backward one unless you specifically want the
`shift`-recursion elsewhere.
