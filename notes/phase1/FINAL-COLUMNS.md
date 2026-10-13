# Final parametrix: column contraction without a loss of rate

13 October 2026. This addresses the optional same-rate column estimate in
`FINALFAM2.md`, T1 and T5. It uses the proposed reference family already defined
in `FinalBoxResolvent.lean`; it does not identify that family with a construction
printed in P7. The starting repository revision is `9edd09f9`.

## The missing estimate

Keep exactly the mass-window, positive macro-scale, and parameter hypotheses of
`taggedK_row_sum`. Write

\[
\epsilon=\mathrm{pdEps}(d,L),\quad g=\mathrm{finalGap}(d,L),\quad
B=\mathrm{pdB}(d,L),\quad H=\mathrm{pdH}(d).
\]

For \(0\le r\le\epsilon/8\), \(\kappa\ge0\),
\(\kappa7^d\le\epsilon M/8\), and \(|s_p|\le e^\kappa\), the target is

\[
\sup_y\sum_x e^{r d(x,y)}|K(s,t)_{xy}|
\le \frac{Be^{H\kappa}}{M}.
\]

It follows from the existing pointwise bound, without a right parametrix.
The old row proof's intermediate bound is now exported as
`taggedK_entry_le_sum`. Set \(\sigma=r+\kappa7^d/M\le\epsilon/4\).
After the tag bound and the overlap count \(2\cdot7^d\), the same scalar
majorant appears in both the row and column calculations:

\[
e^{\sigma d(x,y)}d(x,w)e^{-\epsilon(d(x,w)+d(w,y))}
\le \frac4\epsilon
 e^{-\epsilon d(x,w)/2}e^{-3\epsilon d(w,y)/4}.
\]

For columns, first sum over \(x\), then over \(w\). The torus ball-sum bound
gives

\[
\sum_x\sum_w e^{\sigma d(x,y)}d(x,w)
 e^{-\epsilon(d(x,w)+d(w,y))}
\le \frac4\epsilon\,
 \mathrm{ballConst}(d,\epsilon/2)
 \mathrm{ballConst}(d,3\epsilon/4).
\]

These are exactly the two factors in the row constant. The distance moment
stays on the \((x,w)\) leg; it does not need to be moved by a commutator
identity. No equality between `macTags z x y` and `macTags z y x`, or between
a tagged matrix and its transpose, is used.

## Consequences and Lean declarations

`Balaban/Green/FinalTagColumn.lean` proves:

- `pd_double_sum_column`: the scalar estimate above;
- `taggedK_column_sum`: the column contraction with the existing constant;
- `taggedG_column_sum`: the approximate Green family has column bound
  \(A_0(t)=2e^{H\kappa}\mathrm{ballConst}(d,\epsilon/2)/(g+t)\);
- `taggedGfin_column_bound_same_rate`: if additionally
  \(4Be^{H\kappa}\le M\), the final family has column bound
  \((4/3)A_0(t)\) at the same rate \(r\).

The generic lemmas `weightedColumn_inv_le` and `weightedColumn_mul_le` transpose
arbitrary matrices in the row-norm algebra. This does not assert symmetry of
the actual tagged family. The inverse lemma supplies the bound \(4/3\) from
column contraction \(q\le1/4\).

`Balaban/Green/FinalTagColumnSqrt.lean` proves
`taggedCfin_column_bound_same_rate`: integrating the resolvent estimate gives

\[
\sup_y\sum_x e^{r d(x,y)}|C_{\rm fin}(s)_{xy}|
\le \frac{8e^{H\kappa}\mathrm{ballConst}(d,\epsilon/2)}{3\sqrt g},
\qquad 0\le r\le\epsilon/8.
\]

The old column theorems required \(r'<r\) and multiplied the bound by
\(\mathrm{ballConst}(d,r-r')\). The new theorems remove both losses with no
additional assumptions. The existing row statements and old column statements
are unchanged. Two internal pointwise estimates were extracted from the row
proofs to share the argument.

## What remains open

This completes the optional same-rate column estimate of FINALFAM2, not blocker
5 as a whole. In particular it supplies neither the physical Hessian/action
identification and complex chart, nor physical coefficient locality, a localized
determinant, nor equality across nonwinding tori. The existing `LocalityAE`
encoding declares every family connected; its coefficient sum is not a proof
of geometric connectedness of polymer supports. Those obligations remain.

The claim in FINALFAM2 T5 that a separate right-parametrix construction is
needed for same-rate columns is superseded by the direct double-sum argument
above. The warning that one cannot obtain the result merely by asserting
symmetry remains valid.

## Validation

- `lake build Balaban.Green.FinalTagColumnSqrt` passes with zero warnings and
  builds both new modules and the refactored row proofs.
- `#print axioms` for both extracted pointwise estimates, the column inverse
  lemma, and the three main column estimates returns only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Every pre-existing theorem header in `FinalPathDefect.lean` and
  `FinalTaggedRow.lean` is unchanged; no frozen file is edited.
- The module checker passes across the repository. The frozen-anchor checker
  with `--no-statement-closure` passes; this is the lexical/manifest check,
  distinct from the new theorems' axiom checks above.
- The full default-target `lake build` passes after merging upstream `main`
  at `ee0e0a9c` (10,846 jobs). Its only warnings are the two registered
  `DRAFT_SORRY` root theorems; none comes from the changed proof files.
