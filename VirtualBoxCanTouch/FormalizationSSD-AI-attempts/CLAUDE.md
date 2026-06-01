# Rules for Working 
1. I will ask you to formalize some results via my starting prompt. 
2. If I ask for a result, you should search first in the cubical agda repo, then in the formalizationSSD repo, and then in your own work before writing anything new. 
3. If you cannot find the result, you can create a new file. On the top of this file, make clear that is it AI generated and has not been read by a human yet. 

## STRICT PROHIBITIONS

## Never throw away useful work
1. You should almost never revert to previous backups (you can use temporary admits when something is hard).
2. If there is a really major reason for reverting, you have to salvage all the useful work done in between.
3. In particular, you have to ensure that all compiling theorems and definitions added since are kept.
4. If you later discover such screwup, you have to immedially start working on salvaging the lost work.
5. **SIMPLE CHECK**: after each backup, run wc on the current and previous backup. If the current backup is smaller, you have to explicitly justify (in the CHANGES file) the decrease and explain that you have not thrown out useful work.

### Logic System (Agda)

* **This is Agda** (dependent type theory; constructive by default).
* **Law of excluded middle is *not* available by default.**
* **Proof by contradiction is *not* free by default.**
  You can always do **refutation/negation proofs** constructively
* **Use the library as your first move:** search existing definitions/lemmas before reinventing them.
  Grep/ripgrep the codebase frequently (especially the relevant folders/modules) to find reusable lemmas.
* Prefer reusing established infrastructure (relations, equality reasoning, algebraic structures, etc.) rather than rolling your own.
* You should **avoid duplicating lemmas** that already exist in the library unless there’s a clear payoff (local specialization, clearer naming, performance, or pedagogy).

### Proof Style

* **Prefer equational reasoning** (`≡⟨ ⟩` chains) over composition of equalities (`∙`), so intermediate steps are visible.
  * Keep proofs readable: small lemmas + step-by-step rewrites.
* If a proof is blocked, **don’t handwave**:

  * factor out the missing step as a lemma with a clear statement,
  * or temporarily leave a hole open, and come back to it later. 
  * You have a tendency to proof things in the comments. Comments do not count, they are not trustworthy. **Only** agda-code that has been checked is trustworthy. 

### Coding Preferences

* **Instance resolution over module renaming**: Use `open BooleanRingStr ⦃...⦄` with `instance _ = snd R` instead of `module M = BooleanRingStr (snd R) ; open M renaming (...)`. Bare names like `_+_`, `∨IdL` disambiguate by argument type.
* **Two-way splits over Trichotomy**: Use `splitℕ-≤` or `Dichotomyℕ` when only two cases are needed (e.g., `k ≤ n` vs `k > n`), instead of three-way `_≟_` / Trichotomy.
* **Incremental edits**: For renamings, use find-and-replace (Edit with replace_all) rather than full file rewrites. Make small batches of changes and compile-check after each.
* **Use Agda holes for diagnostics**: When unsure about a goal type, insert `{! !}` and compile to see the goal and context.
* **Use `solve!` for ring identities**: For equations that hold in any CommRing (rearranging sums, distributing products, etc.), use `solve! (BooleanRing→CommRing R)` from `Cubical.Tactics.CommRingSolver` instead of manual associativity/commutativity chains.
* **No `private` blocks inside enclosing modules**: When implementation details are wrapped in a named module (e.g., `module NFinCofinPresentation where`), don't use `private` inside it — the module itself controls visibility. Users who `open` the module get everything; users who don't get nothing.

### Using Agda as Feedback

* **Time compilations**: Use `time /project/agda file.agda` after changes to detect performance regressions. If type-checking gets dramatically slower, investigate (e.g., bad unfolding in opaque blocks, expensive normalizations).
* **Holes for goal inspection**: Insert `{! !}` and compile to see the expected type and context — don't guess.
* **Error messages as guidance**: When unification fails, read the error carefully ("Cannot unify X with Y") to understand exactly what Agda sees vs expects, rather than guessing at fixes.

### Syntax Rules (Agda)

* **Only use `--` and `{- … -}` for comments** (Agda’s comment syntaxes).
  Prefer `--` for line comments and `{- -}` for blocks.
* When a proof gets stuck and you don’t know the goal, use Agda’s interactive features:

  * Put a hole `{! !}` and load/refine to see the goal and context.
  * Common commands (editor-dependent): *case split*, *refine*, *auto*, *show goal*.
* Agda errors are reported with **file:line:column** locations and a message describing the mismatch (e.g., “Cannot unify … with …”, “Not in scope …”).


## Work Strategy (Cubical Agda)

- You may do the following tasks in any order, but you should **always make forward progress** and produce additional Cubical Agda code.
- Continuously fix incorrect or poorly designed **definitions, lemmas, and theorems**.
  - This may require updating downstream proofs that depend on them.
- Gradually eliminate **placeholders**:
  - Replace `postulate`s, unfinished holes `{! !}`, or marked TODOs with real definitions and proofs.
  - Partial or staged approaches are acceptable when necessary.
- Incrementally replace **admitted or placeholder proofs** with more complete ones.
  - This may require introducing auxiliary lemmas or reorganizing proof structure.

While doing the above, keep the following principles in mind:

- Doing easy or mechanical steps first is acceptable, but **do not endlessly optimize trivialities**.
  - Engage with hard theorems early, even if initially only partially formalized.
- Maintain a balance between:
  - small structural lemmas (about paths, transport, equivalences), and
  - substantial mathematical results.
- Your **primary focus** should be on completing the **major, well-known theorems** as early as possible.
  - Prioritize these over examples or minor corollaries, even when technically demanding.
- For difficult theorems:
  - Use **gradual or partial proofs** when needed.
  - Do not delete partially completed work—keep it and refine it.
  - Decompose large proofs into **top-level statements and helper lemmas** with explicit interfaces.

### Cubical-Specific Proof Discipline

- Prefer **path-based reasoning** over propositional equality rewriting:
  - Use `Path`, `PathP`, `≡` (as paths), and `transport` explicitly and deliberately.
- Use **equivalence-based reasoning** where appropriate:
  - Prefer `Equiv` and `≃` over raw isomorphisms.
  - Apply univalence (`ua`) only when it simplifies structure, not as a default hammer.
- Exploit **higher inductive types (HITs)** and **cubical primitives** when they clarify constructions
  (e.g. quotients, truncations, colimits), but avoid unnecessary complexity.
- Avoid proof patterns that rely on UIP, K, or proof-irrelevance unless provided via truncation.

### Library Discipline

- Frequently search the Cubical Agda library:
  - Reuse existing notions of spaces, paths, truncations, equivalences, and algebraic structures.
  - Treat core Cubical modules as trusted foundations.
- Always search the current development before defining something new.
  - Avoid duplicated definitions, especially for:
    - equality/path lemmas,
    - equivalence constructions,
    - standard HITs or truncations.
- **You can introduce new axioms but only those mentioned in the tex file.**
  - Temporary `postulate`s are acceptable only as placeholders and must be eliminated.
- Any newly introduced definitions or lemmas must:
  - respect Cubical Agda’s definitional equality and computation rules,
  - be compatible with path-based equality and univalence.

### Formalization Goal

- The larger formalization target is the file **main-monolithic.tex** 
- The task you're working on today is in the top of this file. 
- Note that you can import stuff from the Cubical Agda and also from
  the current library FormalizationSSD (you may need to fix some of
  the files in FormalizationSSD)
- Follow the intended mathematical structure given in the that file.
- The development is considered **finished** only when:
  - the main definitions are properly stated and the main theorems are fully proved in Cubical Agda, and
  - there are **no remaining placeholders** (`postulate`s and holes).

> “Building up infrastructure” is **not** a sufficient justification for duplicating lemmas or definitions that already exist in the Cubical Agda library.


### PROOF STRATEGY RULES (Cubical Agda)

- Introduce helper lemmas **only when the main proof genuinely requires them**.
- Strongly prefer **existing infrastructure** over new constructions.

### Proof Style Discipline (Cubical Agda)

- Prefer **equational / path-based reasoning** over ad-hoc rewriting.
  - Use `begin … ∎`, `≡⟨ ⟩`, `Path`, `PathP`, and `transport` explicitly.
- Keep the **proof toolbox small and stable**, relying mainly on:
  - definitional reduction and β/η-normalization,
  - rewriting via paths (`subst`, `transport`, `cong`, `cong₂`),
  - function extensionality (built-in via cubical paths),
  - equivalence transport (`ua`, `Equiv.funExt`) when appropriate.
- Avoid clever or exotic constructions unless unavoidable.
  - Prefer clarity and robustness over brevity or trickiness.
- Use **pattern matching and abstraction** (`λ`, `where`, `let`) instead of tactics.
- Use holes `{! !}` deliberately to inspect goals and contexts, then discharge them systematically.

### Structural Discipline

- Structure longer arguments into **many top-level lemmas** with short, readable proofs.
  - Long monolithic proofs are hard to maintain and debug in Cubical Agda.
- Each lemma should:
  - have a clear mathematical meaning,
  - expose a useful interface,
  - minimize dependencies on implementation details.
- Keep proof terms small and transparent whenever possible.

> If a proof step feels like it “should be automatic”, it probably already exists in the Cubical Agda library—search before proving it yourself.


## Compilation Checking
- **Run the checking frequently** to check for compilation errors
- After any significant change, check your work like this: 
  # Quick check (scope/parse errors - note that this will time out when no quick errors are there):
`timeout 60 /project/agda work.agda 2>&1; RC=$?; if [ $RC -eq 124 ]; then echo "TIMEOUT after 1min"; elif [ $RC -eq 0 ]; then echo "SUCCESS"; else echo "FAILED with code $RC"; fi`
  # Full verification (expensive, only when needed):
`timeout 1800 /project/agda work.agda 2>&1; RC=$?; if [ $RC -eq 124 ]; then echo "TIMEOUT after 30min"; elif [ $RC -eq 0 ]; then echo "SUCCESS"; else echo "FAILED with code $RC"; fi`

- Often do numbered backups of work.agda like bck0007. Even when work.agda doesn't compile. Saving you partial attempts is important for not running in circles!
- With each numbered backup, also write the numbered summary changes file like CHANGES0007 (it should really be a summary, not just a simple diff).
- You can lookup your previous work in these CHANGES files when unsure how to continue.
- Never overwrite an older backup file. The numbering has to continue from the latest number. You must find it by running: ls bck* | sed 's/[^0-9]*//g' | sort -n | tail -n 1.

