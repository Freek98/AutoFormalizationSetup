# LLPO Formalization Plan

## Goal
Formalize the proof that LLPO follows from Stone duality axioms + surjections are formal surjections.

## Proof Outline (from LLPO.tex)

### Step 1: B∞ and ℕ∞
- B∞ = NFinCofin presentation (countably presented Boolean ring)
- Sp(B∞) ≅ ℕ∞ (binary sequences hitting 1 at most once)
- **Status**: Mostly done in `StoneSpaces/Examples/Ninfty.agda`, but the isomorphism `neededIso` has 2 holes (sec, ret)
- **TODO**: Complete the isomorphism or work around it

### Step 2: B∞ × B∞
- Need: direct product of Boolean rings
- Need: product of countably presented Boolean rings is countably presented
- Sp(B∞ × B∞) = Sp(B∞) + Sp(B∞) = ℕ∞ + ℕ∞
- **Status**: DirectProd-CommRing exists in cubical. Need Boolean ring version.
- **TODO**: Build `_×BR_` for Boolean rings, show countably presented closure, show Sp sends products to coproducts

### Step 3: The injection B∞ → B∞ × B∞
- Define map on generators: g_n ↦ (g_{(n-1)/2}, 0) if n odd, (0, g_{n/2}) if n even
- Show this is a Boolean ring homomorphism (orthogonality of distinct generators)
- Show injectivity: if f(x) = 0 then x = 0 (using normal form / lattice argument)
- **TODO**: Define the map, prove it's a homomorphism, prove injectivity

### Step 4: Apply surjections are formal surjections
- The injection B∞ ↪ B∞ × B∞ gives a surjection Sp(B∞ × B∞) → Sp(B∞)
- i.e., ℕ∞ + ℕ∞ ↠ ℕ∞
- The surjection sends (α, left) to interleaving on odds, (β, right) to interleaving on evens
- **TODO**: Apply the axiom, characterize the resulting map

### Step 5: Derive LLPO
- Every α ∈ ℕ∞ is merely in the image of left or right
- = merely (α is 0 on all evens) or (α is 0 on all odds)
- This is LLPO for sequences in ℕ∞
- **TODO**: State and prove LLPO

## File Structure
- `LLPOwork/LLPO.agda` - Main formalization file
- `LLPOwork/PLAN.md` - This plan
- `LLPOwork/CHANGES*` - Progress summaries

## Key Dependencies
- `CountablyPresentedBooleanRings.Examples.NFinCofin` (B∞, presentation, NFinCofinPresentation)
- `StoneSpaces.Examples.Ninfty` (ℕ∞, SpB∞, neededIso)
- `StoneSpaces.Spectrum` (SpGeneralBooleanRing, Sp, Booleω)
- `Axioms.SurjectionsAreFormalSurjections` (the axiom)
- `BooleanRing.FreeBooleanRing.FreeBool` (freeBA, generator, inducedBAHom)
- `BooleanRing.BooleanRingQuotients.QuotientBool` (quotients, inducedHom)
- `Cubical.Algebra.CommRing.DirectProd` (DirectProd-CommRing)
