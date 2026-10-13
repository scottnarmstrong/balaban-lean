# W742 — inherited terms: decoupled locality (research note, 2026-10-13)

**Scope / frozen evidence.** Focused, refute-first source/Lean design audit. Initial branch
`490f122b` (P2/P3/P5/P6 PDFs SHA256 prefixes `13686c29/091adb3c/b3f0ef34/ee0ca061`);
main fast-forwarded to `7dafe6bf` for W739. No Lean declaration changed. `PROVED`
means an inspected landed declaration or paper identity, not the proposed bridge.

## Verdict and refutation attempts

**REFUTED — raw-label exact block locality.** `C.Tm.E j y X` is local *in its two
field arguments* (`SmallField/Def6v2.lean`, `SFTermClauses.localE`). After composing
with `composedPairAtC`, those arguments contain `bgFieldC` from a global variational
problem. Two fluctuation fields equal on `X` can change the background on `X` through
data outside `X`. The landed `fderiv_classLabel_eq_zero_of_local`
(`Fluctuation/GeneralEnergyMarksBounds.lean`) explicitly assumes `hbg`, equality of
backgrounds along the complex line. Thus `localE` + a mask avoiding `X` cannot prove
`hbg`, `hlocxs`, or `hfac` for the unexpanded label. The same applies to `localM`.

**REFUTED — exact agreement with an independently decoupled solution at finite
distance.** P2 p. 621 after Lemma 3.1 calls the approximate solution *almost local*;
P3 pp. 56–57, (2.57) and Proposition 2.2, bounds the difference between the
decoupled extension and the original solution by an exponentially small quantity.
There is exact agreement at the all-couplings-one endpoint, and exact locality when
intervening couplings are zero, but no general equality of a global background and a
finite-domain background on `X`. `GsSpecAgree.localPairAt_agree` is exact on `X`,
yet `localPairAt` still uses the *global* top background (`SmallField/GsSpecAgree.lean`);
it does not resolve this objection.

**PROVED — the papers re-expand the composed old terms.** P5 pp. 489–490 (H.2),
(1.6)–(1.8), retains each `E^(j)(y,X)` with its scale-`j` domain and evaluates it at
the new composed field. P3 pp. 77–80, (4.41)–(4.45), writes an *identity* by
interpolating the localization parameters from zero to one: the original composed
term equals a sum over connected `Y₁`, then over localization domains `Y`.
Each summand, with couplings outside `Y₁` zero, reads the data in `Y`; its value
need not equal the original label value. Cauchy bounds (4.47)–(4.50) pay for the
new domains. P6 pp. 29–31, (4.15)–(4.21), applies this to the inherited energy
fluctuation *difference*, keeping `(j,y,X)` until the final sum over `Y` in (4.20);
the bound (4.19) retains `exp(-κ₀ d_j(X)-2κ d_{k+1}(Y))`. P6 p. 34, (4.32)–(4.34),
does the analogous boundary expansion, with a `β_k^{-2}` factor before resummation.
P5 pp. 496–497, (1.33)–(1.39), concerns the boundary class and its modified
distance; it is not a theorem that an interior old label is already local at scale `k+1`.

**PROVED — exact identity has two stages.** At the physical endpoint the *sum* of
decoupled contributions equals the original `flComp` term (P3 (4.41), P6 (4.18));
`Fluctuation/SharpENu.lean:eterm_expansion_hat_rawY` already returns exactly
`flComp hB hF E = ∑_Y Ev Y` with raw-`Y` locality, analyticity and a bound
`E_b exp(-κ₀ d_j(X)-2κ_dec d(Y))`, conditional on `BgSetting`, `FlSetting`,
cover/row/geometry and chart bounds. `ClassOldTermInputE.classOldEnergy_analytic_bound`
supplies the last two from class clauses plus an explicit chart inclusion. Then a
*pointwise physical-endpoint bridge* must identify this `flComp` with the label at
`composedPairAt(C)` on the admissible real chart. `StepActivityHatLevel.hatFun_flComp_level_real`
does this for whole-level `G_k=Gj=stepG/levelGS`; its proof cannot be applied to the
local `G_k=Tm.gs j X` without a new restriction/compatibility result. Likewise
`oldEnergyHatMatch_of_label_identity` and its M analogue merely consume `hid`.

**OPEN — marked observable route.** `eterm_expansion_hat_rawY` handles arbitrary
analytic scalar `E`, so fixed-source `M(j,y,X,·,·,g)_i` can enter given its `analyticM`,
bound, source-support and chart premises. It does not prove derivative/tilt marks or
source scaling. `FFmarked`, `evDec` and fan locality for the step's own terms do not
automatically instantiate class labels or `hbg`.

## Q4 — geometry and the volume factor

**PROVED — persistence of old scale.** P5 (1.7)–(1.8) keeps `j≤k` terms in `D_j`;
P6 p. 7 (2.19) retains `E_k` on the new small-field region and sends boundary
corrections to (2.20). P6 (4.15)–(4.21) resums fluctuation corrections into
`D_{k+1}` only after derivative/Cauchy and decay estimates, with small `β_k`
factors. Old class terms persist at `j`; newly generated differences become
`k+1` polymer contributions.

**PROVED / risk.** W739 `exists_oldEnergyCoeffFamily` (`Fluctuation/GeneralOldCoeffFamily.lean`)
is a correct conditional finite regrouping of *raw* labels into `k+1` cube sets `T`;
its locality is in `physRestrict(sitesOf T)`, before composing with the global
background. Its bound is `B=c₁ (cellSide L m₀ m₁ (k+1))^d ρE`, and its sum identity
is global, with no per-new-root identity. The growing volume is real: every `T`
can collect all old roots in its sites (`fibre_weight_le`). **REFUTED** as a
scale-uniform input from H.4/H.7 alone: a fixed old-root prefactor supplies no
factor cancelling this cube volume; neither exact locality after composition nor
the small fluctuation factor follows from W739. The theorem remains usable for a
fixed step if an independent uniform or compensating bound is proved.

**OPEN — W736 interface decision.** Keep `RenormExpInputOn.expOld/expOldM` and
`thm31g_Eu_on`/`thm31h_on`: they accept any localized expansion of the *difference*
`f(D,ξ)-f(D,0)` with a verified budget; `GeneralRenormInput.IsLocExp.sub_at_zero`
then gives the factor `2B`. Feed them P6-style source-labelled expansions indexed
first by `(j,y,X)` (and `(j,y,i,X)`), then by decoupled `Y` with `Y⊇X₁(X)`;
resum at a fixed new root/site only after proving the joint `d_j(X),d_{k+1}(Y)`
entropy estimate and physical rooting identity. W736's abstract record need not
change; its `exists_locExp_renTheta_of_coeffFamily` cube-set adapter (and W739's
adapter) needs a label-plus-`Y` alternative for a uniform general-class proof.

## Four Lean leaves, in dependency order (all OPEN)

1. **ClassOldDecInputE/M.** For each admissible label `τ`, define
`Eτ(raw)=β⁻¹ C.Tm.E τ.j τ.y τ.X raw.1 raw.2` (M with `g,i`), and prove the
`hEan/hEbd` or M analogues on `XiCRaw (C.Tm.gs τ.j τ.X)` from
`SFTermClausesStrong`, `classOldEnergy_analytic_bound`/`classOldObs_analytic_bound`,
and *explicit* chart inclusion; construct `BgSetting`, `FlSetting`, cover and row
data for that local generator. Risk: chart/geometry and level compatibility.
2. **ClassOldDecExpansionE/M.** For each `τ`, produce `Evτ(Y,raw,ψ̂)` with
`flComp Eτ = ∑_{Y∈polymerDomains(X₁τ)} Evτ Y`, `Evτ Y` raw-`Y` local,
analytic, and bounded by `Bτ exp(-κ₀ d_j(Xτ)-2κ_dec d(Y))` (M includes the
source factor). Use leaf 1 and `eterm_expansion_hat_rawY`; no statement asserts
`Evτ Y = Eτ(global pair)`. Risk: M source dependence and mark differentiation.
3. **ClassOldEndpointAndMarks.** On the real ray, prove
`hatFun(flComp Eτ)(rawOf D',hatC x) = Eτ(composedPairAt τ.j (dataU(psiAt 1 x)))`,
and the M counterpart, by local-to-whole restriction plus the landed whole-level
`hatFun_flComp_level_real`; this is per-label `hid`, while leaf 2 gives the sum identity.
Replace `Mk τ` in `GeneralEnergyMarksAssembly` by the `Y`-marked derivatives:
if a mask avoids `Y`, its derivative vanishes; `hlocxs/hfac` are then proved on
`Y`'s blocks and `hbg` is unnecessary. Risk: analytic differentiation of the
finite expansion and the root/anchor map for `E1`/`M0`.
4. **ClassOldRenormLabelFamily.** Prove a per-root `IsLocExp` for the inherited
*renormalization difference*, via `∑_{τ,Y}` with `Y⊇X₁τ`, exact value/rooting,
raw-`Y` locality, source support, and a scale-uniform `B_old`; then instantiate
`RenormExpInputOn.expOld/expOldM` and W736 with `2B_old ε_R/r₀`. Depends on
leaves 1–3 and P6-style entropy estimates; highest risk is the budget/volume
summation, not the algebraic `sub_at_zero` step.

**Closeout.** Design verdict only. `localE` and `GsSpecAgree` do not remove global dependence.

## W745 status (leaf 1 energy, leaf 2 first statement) — `Fluctuation/ClassOldDecInputE.lean`

- Supplied by the class: `hEan`/`hEbd` for `Eτ = β⁻¹ C.Tm.E j y X` (`classOldDecEnergy_chart`, from `analyticE`, `boundE`); `hq : 𝔹_j(X) ≺ 𝔹_k` (`classOldDec_precedes`, from `gs_spec`) and `colj` (`classOldDec_collar`).
- `classOldDec_bgSetting`: `BgSetting` for `Gj = C.Tm.gs j X` from `BgSetting` for any other `Gj0` (e.g. `levelGS j`); `HBj` does not depend on the generator. `FlSetting` does not mention `Gj`.
- Explicit: the chart inclusion `hchart` (chart in `Dom`), `hB0`/`hF` numerics and `X₁f`, `hcov`, `hX₁`, `hopt` (`IsPolyDom` gives only `CovSetup.chosen`), `hconn`, `hrow`, `κ`-constants. `Gk = 𝔹_k(X)` is taken as any `Gk` with `𝔹_j(X) ≺ Gk` (the whole level `stepG` in the landed results).
- `classOldDec_expansion` (leaf 2, first statement): `flComp hB hF Eτ = ∑_{Y ∈ polymerDomains(X₁)} Ev Y`, raw-`Y` locality, analyticity, bound `β⁻¹E₀ exp(-κ₀ d_j(X) - 2κ_dec d(Y))`. Not done: the endpoint bridge (leaf 3), `CovSetup`/`hopt` from `IsPolyDom`, the M analogue.

## W747 status (leaf 3, energy endpoint) — `Fluctuation/ClassOldEndpointE.lean`

- `composeData_agree_on_X`: for `GsSpecStrong j _ X Gj`, `composeData` of `Gj` over `stepG` and of `levelGS j` over `stepG` (any `φ`, `D`) have the same field and source at every site of `X`.
- `classOldEndpoint_complex`, `classOldEndpoint_real`: for a label `(j, y, X)` with `GsSpecStrong` of `Gj` (`BgSetting` with generator `Gj`, `Gk = stepG`), `hatFun (flComp hB hF Eτ) (rawOf D', hatC z) = β⁻¹ Tm.E j y X (composedPairAt… (dataU (psiAt 1 z)))` for `‖z‖ < pp` (complex: `composedPairAtC`, `dataUC`, `psiAtC`). Proof: the landed whole-level steps (`flDatumOne_stepG`, `psiAtC_eq`, `composedPairAtC_eq_of_bg`) plus `localE` and the agreement on `X`. This is `hid` of `oldEnergyHatMatch_of_label_identity` for each label; only `SFTermClauses` (`localE`) and `GsSpecStrong` of the term generator are used.
- Not done: the marks consequence (replace `Mk τ` of `GeneralEnergyMarksAssembly` by the `Y`-marked derivatives of the expansion; needs the complex-line derivative of the finite sum `∑_Y Ev Y` and a statement of `hlocxs/hfac` on `Y`'s blocks); the M analogue.

## W749 status (leaves 1-3, observable terms) — `Fluctuation/ClassOldDecInputM.lean`, `ClassOldEndpointM.lean`

- `classOldDecObs_chart`: `hEan`/`hEbd` for `Mτ = C.Tm.M j y X · · g i` on `𝔹_j(X)` (singleton instance of `classOldObs_analytic_bound`); `classOldDecObs_expansion`: `eterm_expansion_hat_rawY` at `Mτ`, bound `c₉ (L^j)^{-((d-2)/2+γ-α₁)} exp(-κ₀ d_j(X) - 2κ_dec d(Y))`. The source factor `g_{y,i}` is outside the functional; the source is fixed (`Def6.l1 g < 1`), so no linear-in-g expansion (`mterms_locInt_hat_dm_dir`) is needed here.
- `classOldEndpointM_complex`/`_real`: `hatFun (flComp Mτ) (rawOf D', hatC z) = Tm.M j y X (composedPairAt…) g i`, from `localM` (same `g`) and `composeData_agree_on_X`; this is `hid` of `oldObsHatMatch_of_label_identity`.
- Not done: the marks consequence; `CovSetup`/`hopt` from `IsPolyDom`; the chart inclusion `hchart` stays explicit.
