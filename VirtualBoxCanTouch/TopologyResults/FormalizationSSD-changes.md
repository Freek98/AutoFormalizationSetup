# Changes I made inside the FormalizationSSD library

While making the `TopologyResults` project compile against your refactored
`formalizationSSD`, I found that **two library files were themselves broken** by the
rename/move of `extractFirstHitInBinarySequence`. You moved that module out of the
top-level `BinarySequences` and into `BinarySequences/Properties.agda` (line 84), but
two consumers still expected to find it via `open import BinarySequences`. They no
longer type-checked.

Both fixes are a single added import line each — purely re-pointing the import, no
logic touched. These are the only edits I made in `~/FormalizationSSD`.

## 1. `PropositionalTopology/Properties.agda`

`extractFirstHitInBinarySequence.extract` is used at lines 36 and 224, but the file
only opened `BinarySequences`. Added (just after `open import BinarySequences`):

```agda
open import BinarySequences.Properties using (module extractFirstHitInBinarySequence)
```

Before the fix Agda reported:

```
PropositionalTopology/Properties.agda:36,12-51
Not in scope: extractFirstHitInBinarySequence.extract
```

## 2. `OmnisciencePrinciples/Markov.agda`

`weakMP→MP` (line ~62) uses `extractFirstHitInBinarySequence.extract`, same problem.
Added (just after `open import BinarySequences`):

```agda
open import BinarySequences.Properties using (module extractFirstHitInBinarySequence)
```

## Files I did NOT touch (but you may want to)

* `BinarySequences/HitsInTheSequence.agda` — this is your work-in-progress. It still
  has two open holes (`atMostOneFirstHit`, `isPropFirstHitOnly`) and is not imported
  by anything yet, so it does not break the build. The refactoring note
  (`FormalizationSSD-extract-refactor.md`) fills both holes — see
  `ExtractRefactorProposal.agda` for the type-checked proofs.

## A naming note for you to decide

The breakage came from consumers importing the *whole* `BinarySequences` and assuming
`extractFirstHitInBinarySequence` lived there. If you would rather not update every
consumer when you move things between `BinarySequences` and `BinarySequences.Properties`,
an alternative to my fix is to make the top-level module a re-export hub:

```agda
-- in BinarySequences.agda
open import BinarySequences.Properties public
```

(No import cycle: `Properties` only depends on `BinarySequences.Definitions`, not on the
top-level `BinarySequences`.) That single line would have fixed both files above and is
also what the old `TopologyResults` files assumed. I went with the explicit per-consumer
import instead, since it looked more in line with the split you started. Your call which
convention to keep.

## How everything was verified

All of these type-check with `agda 2.6.4.3` against `cubical-0.9`:

* library: `PropositionalTopology/Properties.agda`, `OmnisciencePrinciples/Markov.agda`
* project: `AtMostOnce.agda`, `ClosedNegationOpen.agda`, `DCTopologyApplications.agda`,
  `DisjunctionClosed.agda`, `TempAxioms/DependentChoice.agda`,
  `ExtractRefactorProposal.agda`

The corresponding `TopologyResults` import fixes (which only touched project files, not
the library) were:

* `AtMostOnce.agda`: `extractFirstHitInBinarySequence` now imported from
  `BinarySequences.Properties`; dropped the now-unnecessary `StoneSpaces.Examples.Ninfty`
  import (`hits1AtMostOnce` already comes from `BasicDefinitions`); and updated two member
  names to your new ones — `firstProp → isPropFirstHit`, `is-first-hit → firstHitAt`.
* `ClosedNegationOpen.agda`: `extractFirstHitInBinarySequence` imported from
  `BinarySequences.Properties`.
