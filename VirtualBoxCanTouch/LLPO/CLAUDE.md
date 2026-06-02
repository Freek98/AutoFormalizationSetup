# LLPO — Cubical Agda formalization

A self-contained folder formalizing LLPO via Stone duality. It depends on the
`FormalizationSSD-Library` and `cubical-0.9` but **does not modify either**, so the
folder stays portable against a clean checkout.

## Typechecking

- Agda **2.6.4.3**. Run from this directory: `agda LLPOAttemptLLMAided.agda`.
- Project flags live in `LLPO.agda-lib` (`--cubical --guardedness`); per-file flags
  (e.g. `--lossy-unification`) sit in the file's `{-# OPTIONS #-}` pragma.
- Typechecking is slow — allow long timeouts (cold runs can take minutes).
- Dependencies are resolved via the registered libraries file
  (`~/.config/agda/libraries`): `cubical`, `FormalizationSSD-Library`. If a name
  that should exist reports **"not in scope"** (e.g. `ker≡0→injBoolHom`), the
  `FormalizationSSD` repo is probably not pulled/registered — fix that before
  assuming the proof is broken.

## Portability convention (important)

Never edit files under `FormalizationSSD-Library`. When a proof really belongs
upstream, develop it in a **local module here** and record the intended upstream
edit in `LIBRARY_CHANGES.md`. Current local stand-ins:

- `NinftyExtras` — re-exports `StoneSpaces.Examples.Ninfty`, adds the finished `neededIso` (and `ℕ∞`).
- `StoneSums` — `Sp(A ×BR B) ≅ Sp A ⊎ Sp B` (used for `σ⊎`).
- `ProductClosureLocal` — algebraic product-closure of countably-presented BAs.

Likewise, prefer small one-off helpers in a **local `where` block** over adding
lemmas to the cubical library. Example: `SpfSurj` defines `Iso→↠`
(`Iso X Y → X ↠ Y`, built from `isEquiv→isSurjection ∘ isoToEquiv`) locally rather
than upstreaming it — `Cubical.Functions.Surjection` only ships the predicate-level
`isEquiv→isSurjection`, not the packaged `≃→↠`/`Iso→↠` (unlike `Equiv→Embedding`).

## Proof style

- Prefer **equational reasoning** (`a ≡⟨ p ⟩ b ≡⟨ q ⟩ c ∎`, from
  `Cubical.Foundations.Prelude`) over bare `∙`-chains when the intermediate terms
  are illuminating — spell out each node so the argument reads top-to-bottom. See
  `Spf-fibre→LLPO`. Note some joints between steps are *definitional* (judgemental)
  and stay implicit; making them explicit would need extra imports.
- When a reasoning node names a helper (`splitIntoEvens`, `toℕ∞seq`, …), add it to
  the relevant `open import ... using (...)` list rather than fully-qualifying.

## Finding definitions

Prefer the typechecker-backed lookup over name-grep, since many names are
re-exported or `renaming`-aliased across modules:

- In-editor: Cornelis (Neovim agda-mode) **go-to-definition**.
- Non-interactive: `agda --html` produces clickable cross-referenced HTML.

Plain `grep` is fine for a quick first pass, but verify through the type checker
when a name might be re-exported.
