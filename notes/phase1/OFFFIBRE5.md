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
