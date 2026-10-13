# OFFFIBRE5 — coefficient families at a free datum

The coefficient parameter is `physParam = rawSub × source`; its raw coordinate contains both
the spin and the external field. `E1CoeffFamily`, `ObsCoeffFamily`, `ObsCoeffLocal`, and
`ObsSourceLocal` already prove analytic, exact-local, decay, and support clauses on this whole
parameter space. `MarkedEvParam` and `MarkedEvJoint` expand the marked functional at `rawOf D`
for arbitrary chart datum `D`; `ObsCoeffFibreValue.obsCoeffParam_fibre` compares coefficients
with a fixed-datum record for arbitrary `D`. These results do not require `D.h = h₀`.
The missing clauses are values. `ZeroSourceActivityCommon` identifies its activity sum with
`(S.withDatum D hDh).WoneC`; `E1ParamFibreValue` identifies the derivative marks with
`(S.withDatum D hDh).Phi1C`; `ObsFamilyJoint` constructs its observable record using
`Jr.withDatum D hDh`. Consequently `e1CoeffFamily_value_fromTower`,
`e0CoeffFamily_value_fromTower`, `obsFamily_*_fromTower`, and the `renE1/E0/M0_siteRecord_*`
conclusions quantify over the constant-field fibre. Their existing locality and bounds need
no replacement, but their value proofs do.
Agreement on that fibre cannot imply an off-fibre value equality by analytic continuation:
the fibre is a proper subspace of `rawSub` when the external field varies. Reprove the activity
and marked expansions at each free `D`, using `StepSettingH.dataUCH` for the composed old datum,
`JointRep.W1/W2/McJ` for the raw exponents, and the same coefficient cores.
Ordered leaves (each at most 300 Lean lines):
1. Raw masked E1 derivative identity using `fderiv_W1_dataUCH`; this first pointwise leaf is
   proved in `OffFibreCoeffFirst.lean` and assumes only that `D` belongs to the chart.
2. Raw `W1` activity and E1 derivative-mark identities at `rawOf D`; then the E1 coefficient
   sum equals the raw localized derivative integral, with fibre results as corollaries.
3. Raw `W2` activity and observable-ray identities for the same `Ev` and `ObsMarks` core;
   then the M0 coefficient sum equals `√β_U · avgJ W1 W2 McJ` at `rawOf D`.
4. Assemble the E1 and M0 off-fibre analytic, local, bounded value families; extend E0 with
   the already datum-generic determinant term and pass the site records through the families.
Fibre value identities alone give no free-datum value clause.

## W689 status (2026-10-13)

`OffFibreE1Marks.lean` proves two free-datum identities without assuming `D.h = h₀`:
`e1_param_marks_sum_decMarkCorr_raw` identifies the parameter-mark sum at
`(rawOf D, 0)` with the corrected decoupled block-mark sum, and
`e1_param_marks_taylor_raw` identifies it with `−β` times the first Taylor
remainder of the summed decoupled block-energy mark. Both use the existing
`MarkedBlockExpansionDecPair` clauses at an arbitrary chart datum and the tower's
mark-radius bound.

The comparison of this Taylor remainder with the masked derivative of
`Jr.W1 C (rawOf D, ·)` is still open. `OffFibreCoeffFirst.lean` supplies the
raw derivative as a derivative of the composed old action, but the existing
`fderiv_mask_corrected_total_fromTower` and
`mark_eq_deriv_blockEnergy_fromTower` compare the block marks to that action
only for `S.withDatum D hDh`. Their off-fibre replacements must use
`StepSettingH.dataUCH`, the free-datum critical point, and the raw ray/domain
lemmas. Consequently no raw E1 coefficient-sum value theorem or fibre
proof-body refactor is claimed here.

## W690 status (2026-10-13)

`OffFibreE1Compare.lean` proves the free-datum block-energy comparison through
`StepSettingH.dataUCH`: `blockEnergy_mark_taylor_eq_fderiv_W1_raw` identifies the first
Taylor remainder of the summed block energy with the derivative of `Jr.W1` in an arbitrary
hat direction. The proof uses the raw marked disc, ray and domain, vanishing first jets,
and the quadratic correction. `OffFibreE1Value.lean` applies this core and the W689
parameter-mark Taylor identity to prove `e1_param_marks_eq_raw_deriv` at every datum
satisfying `XiCData`, without a constant-field hypothesis.

`OffFibreE1CoeffSum.lean` proves `e1_param_coeff_sum_eq_raw_deriv_of_activity`:
for the common E1 labels and parameter marks at `(rawOf D, 0)`, their total `gsumCoeff`
equals the interpolation integral of the localized derivative of raw `Jr.W1`.
The free-datum activity identity is the named hypothesis `hact`; fixed-datum
analyticity, measurability, locality, and bounds are stated explicitly. The theorem
does not yet derive `hact` from W684's activity family, so a fully unconditional
off-fibre coefficient family is still open. The old fibre comparison proofs remain
unchanged because their lower modules cannot import this shared core without a cycle.
