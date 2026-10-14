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

## W696 status (2026-10-13)

`Fluctuation/OffFibreBlockEnergyCore.lean` now holds the common block-energy identity
given a marked line domain. Both the raw free-datum comparison and the unchanged
`StepSetting.sum_blockEnergyOne_eq_VkC_add_delta` declaration apply it; the latter
was moved below the tower file. The original raw domain and energy theorems were
also moved with their statements unchanged. This removes 174 lines from the two
old modules (apart from two replacement import lines).

`Fluctuation/OffFibreM0Ray.lean` proves the zero-class composed-observable path
identity and its derivative for any incoming chart field, then the almost-everywhere
observable-ray identity. `obsCoeff_sum_eq_raw_M0J_zeroClass` identifies the
`ObsMarks` coefficient sum with `√β_U · avgJ W1 W2 McJ` at `rawOf D`.
`Inhabited/OffFibreM0CoeffSum.lean` applies the same `Ev` and `ObsMarks` construction
with an explicitly named free-datum activity premise `hact`, and returns both the
coefficient formula and this raw value. The existing `JointRep.W2_eq_val_sub` is
already a free-datum source identity, and `obsEv_fromTower_rawY` supplies the
free-datum `ObsMarkHalf` and `ObsRayIdentity` premises.

The premise `hact` remains open: `SourceExponentFamily.lean` currently proves its
value clause only on `physFibre`, and no all-chart activity theorem for the same
labels has landed. Consequently this branch does not assert an unconditional
off-fibre M0 coefficient family or site record.

## W707 progress (2026-10-13)

`OffFibreE1Activity.lean` proves `e1_common_activity_freeDatum_of_directTerms` and its
tower-level witness theorem. The former identifies the *same common-label activity*
obtained from the direct-term family with raw `Jr.W1` at every chart datum. Applying it to
`e1_param_coeff_sum_eq_raw_deriv_of_activity`, `OffFibreE1CoeffValue.lean` proves
`e1_param_coeff_sum_eq_raw_deriv_of_directTerms` with no free-datum activity premise.

`OffFibreM0Activity.lean` proves `obs_physAct_raw_of_directTerms`: the direct-term sum of
the analytic activity identifies the raw `Jr.W1 + Jr.W2` at an arbitrary chart datum.
`obs_physAct_raw_fromTower` obtains such an analytic activity and a uniform amplitude
bound from the tower, and `obs_tiltAct_raw_of_physAct` transfers its value to the
observable scalar tilt. Thus a free-datum analytic activity for the M0 exponent exists.

The all-datum E1 and M0 **coefficient families** and the E0 extension remain open. The
existing `e1CoeffFamily_value_fromTower` and `obsFamily_full_fromTower` each hide their
chosen activity in an existential conclusion that records only fibre values. The new
free-datum activity witnesses cannot be identified with those family witnesses from
the exported statements. A completion must construct the bounded coefficient families
and the free-datum value together from one direct-term witness; an equality on the
constant-field fibre does not identify the hidden witness away from that fibre.

## W730 activity audit (2026-10-13)


W708 identifies the direct-term domains and terms inside each source-chain witness.
It does not identify witnesses returned by separate existential theorem calls.
Their total values agree, but that does not imply equality of their labelled activities.
The E1 general proof retains `val`, `I`, `hF`, `A`, and the chosen common activity `A₀`.
The observable label proof retains its own `val`, `I`, `hF`, and `A`.
Thus the raw identities must be proved for those retained choices before the witnesses are hidden.

Planned appended-conjunct chain: `e1CoeffFamily_value_fromTowerG`,
`e0CoeffFamily_value_fromTowerG`, `obsTiltLabels_local_fromTowerG`,
and `obsFamily_full_fromTowerG`; extend a direct chooser only if its witness is lost earlier.
The E1/E0 conjuncts must expose `Lab₀`, `A₀`, and the explicit determinant term `dz` where applicable.
Existing statement clauses remain textually unchanged; physical specializations consume the exports.

## W761 status (2026-10-14)

- WIP of W730 re-applied on current main: `Inhabited/OffFibreM0ActivityG.lean` (`obs_physAct_raw_of_directTermsG_rho` and its `ρ = 1` case, for `StepTowerG`).
- `obsTiltLabels_local_fromTowerG` and `_rho`: appended conjunct `∃ Jr`, `W₁ + W₂ =` label sum of the same `A` at every chart datum (the `∃ 𝒴 …` conjunct is now parenthesised).
- `obsFamily_full_fromTowerG` and `_rho`: appended conjunct (per site) `∃ Jr`, the same activity identity and `√β_U · avgJ(W₁, W₂, ℳ₀(y)_i)(rawOf D) = √β_U · ∑_{T'} obsCoeffParam … (rawOf D, g) T'` at every datum of `XiCData` and every `g` in the radius-`q` ball; proof by `obsRecord_raw_M0_of_activity`.
- `Inhabited/OffFibreM0Family.lean`: `obsM0Family_full_fromTower_rho` (shared tower, value, analyticity, locality, bound, activity identity, avgJ identity). Downstream proof bodies repaired (`hv.1`).
