# Sequential Colimits: Σ-closure and Identity Type Characterization

## Formalization Goal

Formalize the main results of:

> Kristina Sojakova, Floris van Doorn, and Egbert Rijke.
> *Sequential Colimits in Homotopy Type Theory.* LICS 2020.
> Paper: `/home/workprison/Spectral/sequential_colimits_homotopy.pdf`
> Lean source: `/home/workprison/Spectral/colimit/seq_colim.hlean`

### Main Results to Formalize

1. **Theorem 5.1 (Σ-closure)**: `colim(Σ(A,B)) ≃ Σ_{x:A∞} B∞(x)`
   - Sequential colimits commute with Σ-types

2. **Theorem 7.1 (Identity types)**: `(ι(n,a₀) ≡ ι(n,a₁)) ≃ colim(k ↦ rep(k,a₀) ≡ rep(k,a₁))`
   - Identity types of sequential colimits are sequential colimits of identity types

### Approach

- Work directly with the Cubical Agda library's `SeqColim` HIT (no custom recursive HIT)
- Define fiber sequences with recursion on k (avoids ℕ-arithmetic issues AND termination issues)
- Use `Iso-SeqColim→SeqColimSuc` from the library for the shift equivalence
- Use `ua→` for type family coherence at push
- Use `recognizeId` for identity type characterization

### Completion Criteria

- **No `postulate`s**
- **No `{-# TERMINATING #-}` flags**
- Full compilation with `--cubical --lossy-unification`

## Compilation

```bash
# Quick check:
timeout 60 /usr/bin/agda SeqColimSigmaId/work.agda 2>&1; RC=$?; if [ $RC -eq 124 ]; then echo "TIMEOUT after 1min"; elif [ $RC -eq 0 ]; then echo "SUCCESS"; else echo "FAILED with code $RC"; fi

# Full verification:
timeout 1800 /usr/bin/agda SeqColimSigmaId/work.agda 2>&1; RC=$?; if [ $RC -eq 124 ]; then echo "TIMEOUT after 30min"; elif [ $RC -eq 0 ]; then echo "SUCCESS"; else echo "FAILED with code $RC"; fi
```
