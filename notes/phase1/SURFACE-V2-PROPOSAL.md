# Surface v2: proposal (2026-10-11)

## Situation

Root-C now follows in Lean from one statement the RG flow must deliver:
`Balaban.Correlations.rootC_of_rootFAndC1Star : RootFAndC1Star d N hN → RootCStatement d N`
(axioms standard; `RootCStatement` checked definitionally equal to the frozen Root-C). The Green's
function layer (G-1, G-2(i)–(vi′), G-4, G-5), the polymer expansion and the background-field
Prop 5.1 are landed as proved theorems.

## Cost of freezing the candidate interfaces

The statement-closure rule requires every project definition in a frozen statement to be frozen
itself (one declaration per file). Measured closures:

- C-1* (`RootFAndC1Star`): **44** non-frozen project definitions (`C1Star`, `C1StarF1–F3`,
  `LimAlong`, `RootFClauses`, `RootFFamily`, `termKernel`, `fluctTerm`, `stepOp`, `stepProlong`,
  `blockAverageMatrix`, `latticeLaplacian`, `betaSeq`, `gammaSeq`, `deltaSeq`, `blockM`,
  `blockGtr`, `blockGlg`, …), in addition to the 8 frozen model definitions.
- A Green's function interface (e.g. `global_g2iv`): the multiscale layer (`GeneratingSet`,
  `dirichletOperator`, `pathDist`, `spacing`, `layerIndex`, `zeroExt`, …), of the same order.

## Proposal

1. **Do not freeze interfaces whose consumer is already proved.** A proved chain ending at a frozen
   root protects itself: if someone weakened `C1Star` or a Green statement, the proved consumer
   (`rootC_of_rootFAndC1Star`, the background-field proofs) would stop compiling, and `land.sh`
   rejects any landing that breaks the build. Freezing them would add ~40–80 frozen definitions for
   no gain in soundness.
2. **Freeze only cross-team contracts whose consumer is not yet proved**, when they arise:
   Def-7 / LF-4 (between the large-field and flow work; after the reconstruction document Parts I–II),
   the small-field step I-9, and the background-field `∃!` theorem with the definitions `bgField`,
   `bgFieldC` (following the definition-by-characterization rule) once the localization and
   small-field Lean work start consuming them.
3. Keep the two roots and the 8 model definitions as the frozen surface until then (10 anchors).

Decision requested from the author: approve 1–3 (no surface v2 freeze now).
