# ENERGYFAM — exponent and zero-class energy family

**PROVED. Snapshot.** Read-only audit of `/home/scott/Balaban` at `9955f646e069b686a01740d67fb2bcb6312a8532` (2026-10-13). Existing Lean names below were checked by search and their declarations inspected.
`PROVED` is a narrow landed claim; `PROVED CONDITIONAL ON` retains the displayed inputs; `OPEN` denotes a missing physical conclusion; `REFUTED` rejects a false join. No Lean build or source edit is
claimed.

## 1. The source exponent family

**OPEN. Proposed `sourceExponent_family` binder order.** Fix `κmin` and `T : StepTower κmin` with `stepHullMin≤κmin`; let `O := stepOutputPhysical T h`. Choose `β₀,CE,CF` and final activity smallness at
`O.Ktot` before scales. Then quantify `k hk N₁ [NeZero N₁] h3N hN5 ν hνpos hν β hβ p₁ hp hpLog`, and `P : StepScaleData T k hk N₁ ν β p₁`. Put `S := T.step …`, `C := zeroClass …`, `BS := S.blockSplit 1
hp`, `V := physV S 1 ν T.t`. Only then choose one finite domain family `𝒴`, `hdom : ∀Y∈𝒴, IsDj 1 (k+1) Y`, base label type/`CubeLabels`, and activities `Aseg` on `V × stepSegments` plus a complex-`u`
zero-source family `A0` on `V × 𝒰`. These choices precede `∀ e∈V`, its source `g=e.2`, and `∀` root `z`. Do not choose a new label type within `∀g` or `∀z`. The source construction may start at `KcSource`;
its extension to the common root labels must prove `KcSource + rootUnionK ≤ O.Ktot` and transport the activity bound and identity before using `O.Ktot` below.

**OPEN. Exact two-parameter value clause.** For every `e=(q,g)∈V`, `p=(s,t)∈stepSegments`, the same `Aseg e p : LabelAct Lab BS.Ωb εH O.kH O.k0 O.Ktot` should obey

```text
∀ᵐ x ∂S.nuFl,
  Jr.W1 C (q, (s:ℂ) • yhat x) + Jr.W2 C g (q, (t:ℂ) • yhat x)
    = ∑ y, (Aseg e p).H y (BS.restr x).
```

**OPEN. Slice clause.** At the chosen physical datum `q=rawOf S.D'` and admissible `g`, use `Jr.W1_withDatum` and `Jr.W2_withDatum` on the ray to change the left side to `S.WoneC C s x + S.WtwoC C g t x`.
This is exactly `StepActivityBoundC.hW`, whose quantifiers are `∀p∈stepSegments, ∀ᵐ x ∂S.nuFl`. The same `Lab,BS,εH,κH,κ0,κ',Kc` must fill the resulting `StepActivityBoundC`; its present type has no chart
parameter and no joint analytic field.

**OPEN. Zero-source restriction for marks.** For every `q` take `g=0`, `p=(s,0)`, and choose `A0(q,u)` holomorphic in `u` on `𝒰⊃[0,1]`, with the physical datum jointly analytic on `V`. On the fixed datum
its `hW` must become `∀s∈[0,1], ∀ᵐ x ∂S.nuFl, S.WoneC C s x = ∑y (A0(q,(s:ℂ))).H y (BS.restr x)`. This is the `hW` of `InterpMarks S.nuFl BS (S.WoneC C) f`, where the energy mark `f` is the masked `fderiv`
of `Phi1C`. `InterpMarks.hF` separately needs `f s x = ∑i G i (s:ℂ) (BS.restr x)` almost everywhere under that same `S.nuFl`.

**PROVED. Parameter-family type.** `Fluctuation/Thm31CoeffAnalytic.lean:ParamMarkFamily` uses an open `V`, a complex segment neighbourhood `𝒰`, `A : E→ℂ→LabelAct`, and `G : E→ι→ℂ→…`; it requires `holA`,
`holG`, `contA`, `contG`, a compact carried set `Q`, and bounds uniform in the parameter. It does *not* contain `hW` or `hF`; a physical witness must prove them on each slice.
`Fluctuation/ParamActivitySubspace.lean:physParam`, `physV`, `isOpen_physV`, `DirectTermsFamilyOn`, `labelActFamilyOn_analytic` provide the correct relative chart and abstract activity regularity.

**PROVED. Common labels.** `Fluctuation/MarkedCommonLabels.lean:commonLabels`, `commonAct`, `commonAct_hW_interp`, `paramMarkFamily_common` extend one base activity by zero over all root-bridge labels.
`commonAct_hW_interp` transports an *already proved* `hW`; it does not construct exponent matching. Its entropy cost is `Kc+rootUnionK`, and `exists_beta0_commonLabels` provides the later amplitude
threshold. `Polymer/LabelRootUnion.lean:rootUnion_entropy` needs `aEnt+2≤κ0`, now supplied by `T.κ0_two`.

| Source-family clause | Landed or in flight | Remaining bridge |
|---|---|---|
| One tower, chart, source terms | `Inhabited/StepTowerScale.lean:StepTower.scale`; `ExpSourceChartFromTower.lean:expSourceChart_scale_fromTower`; `SourceFamilyRelativeFromTower.lean:sourceFamilyRelative_scale_fromTower` | **PROVED** on one `T`; the source family has fixed direct-term domains before each source. |
| One activity label type before `∀g` | `Inhabited/SourceActivityFromTower.lean:sourceActivityC_scale_fromTower`, `stepActivityBound_zeroClass_source_of_directTerms_shared` | **PROVED** at the fixed step: `𝒴`, doubled label type, thick labels, block split, rates, and entropy constant are fixed before `∀g∈l1Ball`. **OPEN** extension into one chart family and common root labels. |
| Physical `physVal`/chart exponent identity | `PhysicalTerms.lean:physVal`; `Fluctuation/SourcePhysValBridge.lean:W2_eq_physVal_sub`, `sourcePhysVal_W2_fromTower`; `StepComplexJoint.lean:W1_withDatum`, `W2_withDatum` | **PROVED** W2 equals a difference of `physVal` values at source `g/β` and zero on the ray. **OPEN** W1/background value match and the combined chart-wide `Jr.W1+Jr.W2` identity. |
| Label sum to `physVal` | `ParamActivitySubspace.lean:labelActFamilyOn_eq_dtAct`; `SourceFamilyRelative.lean:directTermsFamilyOn_scaled`; `HatLabelsTerms.lean:StepSetting.ae_hatOf_restr` | **PROVED CONDITIONAL ON** the previous value identity, common domains, radius and segment hypotheses; rewrite the finite direct-term sum on the support of `S.nuFl`. |
| Physical `hW` at every chart point | `StepComplexOutAnalytic.lean:JointRep.ae_W1_path`, `JointRep.ae_W2_path`; `StepComplexNonvanish.lean:StepActivityBoundC.hW` | **OPEN** combined family statement. The landed a.e. chart identities are under `S.nuFl` at admissible data, not a new measure indexed by `e`. |
| Root marks on same `A0` | `MarkedCommonLabels.lean:paramMarkFamily_common`; `MarkRealDomain.lean:markReal_hdomT_of_disc`; `MarkRealRegular.lean:markReal_fderiv_mask_eq_neg_beta_sum` | **OPEN** common physical `G`, `hF`, `holG`, `contG` and exact activity identity; W422 root assembly and W436 marked-disc slice are in flight. |

**PROVED. Which almost-everywhere facts apply.** `StepSetting.ae_hatOf_restr` states `S.hatOf … (BS.restr x)=S.hatC x` for `S.nuFl`-a.e. `x` when `0<p₁≤ρ`; `S.ae_ball` supplies `χ_fl=1` there.
`ObsRemainderMarks.lean:ae_obsHat_eq_true` instead lives under `Measure.pi BS.μ` and equates a clipped observable hat with its true version; it does not prove the energy/source exponent identity.
`StepActivityBoundC.hW`, `InterpMarks.hW`, and `InterpMarks.hF` are all `S.nuFl`-a.e. statements at a *fixed* step. They cannot be read as joint analyticity on `V`.

**OPEN. Analytic-family check.** `DirectTermsFamilyOn` gives analyticity of the label activity in the relative physical parameter. The piecewise real `segAct` constructs the two `stepSegments` values, but
`ParamMarkFamily.holA` demands analyticity in complex `u` on `V×𝒰` for the zero-source branch. A direct-term family and a central-datum `StepActivityBoundC` do not by themselves supply that complex-`u`
continuation or the same-label `hW` at every chart point.

## 2. Energy output terms fixed by consumers

**PROVED. No current `EnergyOutputTerms` or `OutputTerms` record exists in `Balaban/Fluctuation`.** `SmallField/Def6.lean:Terms` is the later all-scale class data and is not a one-step energy witness. The
exact current one-step identity is `StepComplexOut.lean:StepSetting.E0locC`: `E0locC C z = -½∑_{y∈S.blockU z}tr(logAC(y,y)) + E1locC C z`. Accordingly `ParamDatumFamily.lean:e1CoeffC` is definitionally
`D.term T + interpCoeff I T`; `thm31aC_coeff` gives its fixed-datum sum and rate conditional on `I : E1MarksC` and `D : DetExpansionC`.

**REFUTED. Triple additive energy formula.** The source/activity cluster is used *inside* `interpCoeff I T` through `I.A` and the marked `G`; it is not a third term beside `interpCoeff` and the
determinant. Adding an independent Prop 2.6 cluster contribution to those two would double count. Nor does `∑_X e⁺_z(X)` alone equal the logarithm of the full step integral: it equals `E0locC C z`;
`StepComplexSource.lean:sum_E0locC_zeroClass` yields `∑z E0locC=E0C`, while `prop26C_zeroClass_of_activity` has the separate `-β AnewC`, inherited/background, `Eppp`, and source `F0C` terms in the
exponential.

**OPEN. Proposed `energyOutputTerms_zero` statement.** Under the same `T,O,β₀` and per-scale `P` as §1, choose for *all* block roots one physical `I_z : E1MarksC S C BS z` by restricting the common
`ParamMarkFamily`, and one `D_z : DetExpansionLocC S 1 z T.t (towerDetRate T.κ) (towerDetConst T.κ)` from `detPackage_fromTower`. Let `e_mark(z,U,q)=gsumCoeff BS.μ Lab (A0 q) y0 (G q) U`,
`e_det(z,U,q)=(D_z).term (bgOfRaw q) U`, and `e_raw=e_mark+e_det` on `Finset (CubeB …)`. At `q=rawOf S.D'`, require `e_raw=e1CoeffC I_z (D_z.toDetExpansionC …)` and `∑_U e_raw=S.E0locC C z`; at other
constant-`h` data use `D_z.atDatum` and `S.withDatum`. Require the same family jointly analytic on the relative chart, externally local, anchored, covariant, torus-uniform, and bounded after a declared map
to output polymer sets `X` at `O.kout`. This is a target conjunction, not a landed record or a new hypothesis to `thm31aC_coeff`.

**PROVED. Determinant producer.** `Inhabited/DetPackageFromTower.lean:detPackage_fromTower` supplies one family `z↦D_z` for the same `T` and every scale: actual term formula, root-trace sum, grouped hull
bound, root anchor, locality on the hull, generated lattice covariance, and spin rotation invariance. `towerDetHullRate_ge` and `StepTower.kout_le_hullRate` give the class rate when `stepHullMin≤κmin`.
`Fluctuation/DetOutputTerms.lean:DetExpansionLocC.analyticOnNhd_rawSub` gives raw-chart analyticity of the ungrouped term. `Fluctuation/DetGroupedAnalytic.lean:detGrouped_chart_family_fromTower` now gives
analyticity of the grouped terms on `physV`, their hull bound, and locality on the hull, conditional on the chart hypotheses in its type.

**PROVED CONDITIONAL ON marks.** `Thm31CoeffA.lean:interpCoeff_spec` gives the canonical interpolation sum and `CPE·Σ_i F0_i e^{-κ0 dl(y0_i)} e^{-κ' dExt(T)}` bound.
`Thm31CoeffAnalytic.lean:gsumCoeff_analyticOnNhd` and `gsumCoeff_ext_congr` give parameter analyticity and locality from an actual `ParamMarkFamily` and its activity/mark dependence premises.
`MarkedSharpCount.lean:marked_count_scaled` has rooted `2κdec−1` count bounds under its marked disc and cover hypotheses; it is not the full physical `E1MarksC` family.

**OPEN. Reindexing to one `X`.** Raw mark and determinant coefficients share the `CubeB` index `T`; their final locality sets do not. For the determinant use `H_det(T)=detCollarHull T`, with fibre
`detCollarFibre X`. `DetCollarHull.lean:detCollarHull_fibre` bounds its count by `2^{c1(1+sizeJ X)}`; `DetExpansionLocC.detGrouped_bound` already pays that count and the collar size loss. For marks choose
a rooted `IsDj` support map `H_mark(T)` containing the `Yhat(sitesOf T)` read set of `gsumCoeff_ext_congr`; prove its fibre count and decay transfer separately. Set
`e⁺_z(X,q)=∑_{H_mark(T)=X}e_mark(z,T,q)+∑_{H_det(T)=X}e_det(z,T,q)`. Sum identities follow only after both maps are total and all nonzero terms have legal rooted supports. The theorem `rootUnion_entropy`
bounds the *activity label budget*, not the number of `T` in either output fibre; `entropy_thick` pays the base thick-label budget, not the collar count.

**OPEN. Common-index alternative.** One may use `H_det` for marks as well only after proving `Yhat(sitesOf T)⊆detCollarHull T` and a new mark bound after the collar/fibre loss. No such inclusion or
inequality is currently a field of `stepOutputPhysical`. Keeping two maps avoids silently charging the determinant's favourable raw rate to the marked term.

| Summand / stage | Input rate and index | Needed `O.kout=3T.κdec/2` inequality; status |
|---|---|---|
| Base activity for exponent | `O.kH=2T.κdec−1`, thick labels, then root-union labels | **PROVED** `O.kH≥O.k'+3O.k0+c1 3 3+3/2` (`StepOutputConsts.kH_ge`); `O.Kall≥rootUnionK` (`rootUnionK_le_stepOutputPhysical`). This controls expansion smallness, not an additive energy output term. |
| Root mark before Mayer sum | `κG=2T.κdec−1` proposed from `marked_count_scaled`, rooted bridge labels | **PROVED** numerical `O.kH≤κG` if that physical family uses this choice; **OPEN** the actual common family and its amplitude `F0`/`Ktot` smallness. |
| Canonical interpolation coefficient | `O.k'=3T.κdec/2+T.κ0+1`, `CubeB T` | **PROVED** `O.kout≤O.k'−O.k0−1` (`StepOutputConsts.kout_le`, equality here). **OPEN** a justified `H_mark` size/fibre estimate that spends no more than `O.k0+1` of rate, and the required amplitude comparison. |
| Raw determinant | `O.kdet=towerDetRate T.κ`, `CubeB T` | **PROVED** `O.k'≤O.kdet` (`StepOutputConsts.kdet_ge`); a raw coefficient at the common index can use `O.k'`, subject to locality transfer. |
| Grouped determinant | `O.lhull=hullRate 3 3 O.kdet`, hull `X` | **PROVED** `O.kout≤O.lhull` (`StepOutputConsts.lhull_ge`); `detPackage_fromTower` proves its grouped estimate and `detGrouped_chart_family_fromTower` its chart analyticity. **OPEN** class-domain inclusion. |

**OPEN. Prefactor.** The determinant prefactor `towerDetConst T.κ` is order one; it is part of the new energy/vacuum ledger, not a small source activity. The marked amplitude is `CPE·Σ_i F0_i exp(-κ0 dl)`
and must be combined with the determinant bound as in `thm31aC_coeff`. Any advertised `BE0` or class coefficient constant requires a proof after the chosen reindexing, not an equation copied from
`StepOutputConsts`.

## 3. The consumers and mismatched carriers

**PROVED CONDITIONAL ON fixed-datum records.** `thm31aC_coeff` consumes `E1MarksC` and `DetExpansionC` at one `S.D'`; `DetExpansionLocC.toDetExpansionC` is that map, while `atDatum` requires another datum
with the same constant `h₀`. Neither yields a choice analytic across `physV`. `StepComplexThm31.lean:sum_E0locC_of_sum_E1locC` and `sum_E0locC_zeroClass` supply the root sum under their
regularity/nonvanishing premises.

**PROVED CONDITIONAL ON activity/nonvanishing.** `StepComplexProp26.lean:prop26C_step` concerns the full `TstepC C g` and needs `StepRegularC,StepNonvanishingC`; `prop26C_zeroClass_of_activity` discharges
the latter from a physical `StepActivityBoundC` at the chosen datum. Its source term `F0C C g` is separate from `E0C`. The energy family should be connected to this exponent through `∑z E0locC=E0C`, not by
replacing the entire logarithm with `∑e⁺`.

**PROVED CONDITIONAL ON distinct marks.** `Thm31cde.lean:thm31c_of_input`, `thm31d_of_input`, `thm31e_of_input` each take `InterpMarks` for their own P5 integrand and separate size bound; their conclusions
are not fields of the zero-class energy term. At zero class inherited P5 terms vanish, but a new energy `E1MarksC` witness does not inhabit those unrelated `InterpMarks` types. The shared `WoneC` exponent
can be reused when those integrands arise in a later class step.

**REFUTED. Full-chart `S.withDatum` shortcut.** `physV` allows varying complex `h`, while `StepSetting.withDatum` and `DetExpansionLocC.atDatum` require `D.h=S.h₀`. Use `JointRep.W1/W2` and raw-subspace
analytic terms for the full family; restrict to the fixed-`h` physical slice when applying a consumer tied to `S.withDatum`. The determinant package is on `XiCData`; inclusion of every desired class datum
into that chart is still an obligation. `ParamMarkFamily` is analytic in its parameter and `u`, while `StepActivityBoundC` only records a real-segment a.e. identity; neither implies the other's missing
variable by coercion.

**REFUTED. Class-locality shortcut.** `DetExpansionLocC.local_resDep` reads a cell neighbourhood beyond `sitesOf T`; raw `e1CoeffC` therefore is not local on its `CubeB T` alone. The grouped determinant is
local on `detCollarHull T`; mark locality must be transported to the chosen `H_mark(T)`. The later `SmallField.Def6.Terms.localE` quantifies over its class-domain fields and output polymer `X`, which is
stronger than chart-relative equality at one datum.

## 4. Frontier after the in-flight work

| Priority / bounded leaf | Statement sketch in landed vocabulary | Inputs, size, worker, start |
|---|---|---|
| 1 `sourceExponent_family` | With one `T,P,BS,𝒴,Lab`, construct `Aseg` over `physV` whose sum has the `JointRep.W1+W2` a.e. identity on both segments, and its zero-source complex `A0`; specialize to `StepActivityBoundC.hW` at the physical slice without changing labels. | `sourceActivityC_scale_fromTower`, `W2_eq_physVal_sub`, `DirectTermsFamilyOn`, `ae_hatOf_restr`; ≤280, strong; **start now** on W1 matching and chart assembly. |
| 2 `energyMarkFamily_zero` | For the same `A0`, all roots `z`, and one common rooted label type, build the physical `ParamMarkFamily`, prove each `InterpMarks.hW/hF`, then give `I_z : E1MarksC S C BS z` by restriction, with `κG=O.kH`, `I_z.κ'=O.k'`. | W422 root output, W436 slice, `MarkedCommonLabels`, `MarkRealRegular`, `marked_count_scaled`; ≤300, strong; **start now** on the fixed-name interface, close after those inputs. |
| 3 `energyMarkCoeff_family` | Define one `e_mark(z,T,q)=gsumCoeff …` for all roots and chart points; prove sum `E1locC`, joint `AnalyticOnNhd`, `Yhat(sitesOf T)` locality, root support and the displayed `CPE·ΣF0` bound. | `ParamMarkFamily`, `gsumCoeff_analyticOnNhd`, `gsumCoeff_ext_congr`, `interpCoeff_spec`; ≤260, Sonnet; **wait** for leaf 2. |
| 4 `energyMark_fibre` | Choose a legal rooted `H_mark(T) : IsDj` containing the mark read set, prove `∑_{H_mark(T)=X}‖e_mark‖≤Bmark·exp(-O.kout·sizeJ X)` with explicit count and `O.k'−O.kout=O.k0+1`. | Leaf 3, polymer geometry and label entropy; ≤300, strong; **start now** on the geometry, coefficient application waits. |
| 5 `energyOutputTerms_zero` | Choose `D_z` from `detPackage_fromTower`, regroup marked and determinant terms on one `X`, prove `∑_X e⁺_z(X,q)=E0locC` on physical slices, analytic/local/root/covariant bounds and `∑z E0locC=E0C`; keep the exact `prop26C_step` exponent as a separate conjunct. | Leaves 1–4, `detGrouped_chart_family_fromTower`, `thm31aC_coeff`, `sum_E0locC_zeroClass`; ≤300, strong; **wait** for the family and fibre bounds. |

**OPEN. Acceptance check.** At one nonzero source and two chart data with the same restriction to a proposed `X`, verify the source-labelled activity uses the same pre-source labels, the energy
coefficients agree whenever the required local read sets agree, and the fixed-datum sum is exactly `E0locC`. Repeat at two scales using the one `T,O,β₀`; a separate tower or per-root `Lab` fails the
intended output statement.
