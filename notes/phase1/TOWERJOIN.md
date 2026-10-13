# TOWERJOIN — one rate tower, one output ledger, one source label family

Read-only source paths below are relative to `/home/scott/Balaban/Balaban/` at the current tree. **PROVED** means a cited declaration has the stated output; **OPEN** means a proposed interface or proof; **REFUTED** means the stated join is impossible with the landed record fields. This note specifies the physical $d=L=3$, $N=2$ zero-class witness, not the general RG root.

## 1. The $kappa_0$ choice

**PROVED.** `Inhabited/StepTower.lean:34–38,82–93` fixes `T.κ0 = aEnt 3 3 + 1`; `Fluctuation/StepOutputConsts.lean:68,104–108` requires `aEnt 3 3 + 2 ≤ C.k0` and constructs `C.k0 = aEnt 3 3 + 2`. Thus **REFUTED:** a landed `T : StepTower κmin` and `C : StepOutputConsts 3 3` can satisfy `C.k0 = T.κ0`; their fields imply $a_{\rm ent}+2\le a_{\rm ent}+1$.

| Consumer | Needed condition | Equality used in the *landed public proof*? |
|---|---|---|
| `TowerCoreRatesAtLeast.tower_core_rates_at_least` (`:33–52`) | `aEnt+1≤κ0`, `3κ0+c1+5≤κdec` | No. Its proof is parameterized in both rates (`:53–130`). |
| `StepTower.hκ0`, `hκdec`, `tower_conj` (`:143–175`) | The first inequality and rate arithmetic | `hκdec` uses `κdec_eq`; none needs `κ0_eq`. |
| `SourceDirectTermsScale.sourceDirectTerms_slice` (`:119–173,193–217`) | `0≤κ₀`, `3κ₀+3≤κdec`; the label assembler at `:300–304` needs `aEnt+1≤κ0`, `K0+1≤Kc'`, `κ'≥0`, and the rate/DA bounds | No equality in these leaf signatures. |
| `HatLabelsDirect.labelAct_of_directTerms` (`:79–90`) and `ParamActivityPhysical.dtAct` (`:170–178`) | `aEnt+1≤κ0` | No. |
| `SourceActivityScale.stepActivityBound_zeroClass_source_scale_cutoff` (`:87–110,136–150,222–256`) | Same lower bound, rate equations, DA threshold | Yes: public binder `hκ0def : κ0=aEnt+1`; `hκ0def` discharges the tower call at `:110`; `hκdecdef`,`hκ'def` discharge arithmetic. The leaf body uses `hκE`, not the exact value. |
| `DetStepScale.stepActivityBound_detExpansionLocC_scale` (`:72–104,132–159`) | Tower lower bound; $kappa'$, determinant and class rate inequalities | Yes in its public binder and tower call. The determinant leaf `DetOutputTermsWitness.detExpansionLocC_scale_of_tower` (`:194–244`) has no $kappa_0$ binder. |
| `ScaleActivityFinal.stepActivityBound_zeroClass_direct_physical_scale_cutoff` (`:87–107,135–146`) | `aEnt+1≤κ0`, rate/DA arithmetic | Public `hκ0def` only fixes the old witness; the scale assembler uses inequalities. |
| `UniformChartMargins.scale_markedDisc_mem_flBallLC` (`:216–251`) | A tower at some rates | It directly chooses `aEnt+1`, but the marked-disc leaf needs only `FlCore` and margins. `scale_chart_det_joint` (`:290–341`) inherits the public `+1` binder. |
| `SourceFamilyRelative.sourceFamilyRelative_scale` (`:156–210,235–241`), `SourceAmpNonneg.sourceFamilyRelative_scale_nonneg` (`:121–186,339–344`), `ExpSourceChart.expSourceChart_scale` (`:353–389`) | `aEnt+1≤κ0` at their leaf constructors | Their public theorems fix `+1`; the former two use `hκ0def.ge` inside the proof, so substitute the new tower inequality. |
| `LabelRootUnion.rootUnion_entropy` (`:194–203,240–283`) | **`aEnt+2≤κ0`**, because the factor `1+d(Y)` for root multiplicity spends one unit in `e^{-(κ0-1)d(Y)}` | No equality, but the stronger inequality is essential. `LabelAct.extendRootUnion` (`:296–304`) passes it through. |

**Recommended option (ii), OPEN implementation.** Retune the physical tower from `+1` to `+2`: replace `StepTower.κ0_eq` by `κ0_eq : κ0 = aEnt 3 3 + 2`, and choose that value in `exists_stepTower`. This is the smallest fixed specialization of a parameterized tower that admits the required entropy bound and keeps the one-parameter `StepTower κmin` type. More generally replace the equation by `κ0_two : aEnt+2≤κ0` and parameterize the hull requirement by $kappa_0$; an unbounded $kappa_0$ cannot use the closed fixed `κmin` below. `StepTower.lean:17–20,34–38,82–93,143–175` needs re-elaboration of its witness/arithmetic; `TowerCoreRatesAtLeast.lean` and `DetOutputTermsWitness.detExpansionLocC_scale_of_tower` stay untouched. Keep the old public `+1` scale theorems intact; the new from-tower source, determinant, chart, relative-family, and exponential-chart proofs must be factored/re-run with `T.κ0` and `T.κ0_ent`. If public scale statements themselves are to consume `T`, their exact-equality binders in `SourceActivityScale`, `DetStepScale`, `ScaleActivityFinal`, `SourceDirectTermsScale`, `SourceAmpNonneg`, `SourceFamilyRelative`, `ExpSourceChart`, and `UniformChartMargins` must be generalized; simply applying the old public theorems is invalid.

**REFUTED option (i) at the same $kappa_0$.** The factor $1+d(Y)$ in `LabelRootUnion.lean:254–283` consumes a full unit of label decay before `entropy_thick`. With `κ0=aEnt+1`, the residual rate is `aEnt`, below that theorem's input `aEnt+1`; increasing only the determinant rate, or choosing a larger $\beta$, does not discharge it. One could prove a separate root-count/entropy theorem with a new rate ledger, but no such lemma is landed.

## 2. Numerical join and the genuine label-constant obstruction

**OPEN definition, closed in landed constants** (the extra `+1` is the strict margin used in `StepOutputConsts.lean:121–136`; `detDeg 3 3+1=214991878` at `:100–102`):

```lean
noncomputable def stepHullMin : ℝ :=
  18 * 60751 *
    (3 / 2 * (100 * (aEnt 3 3 + 2 + c1 3 3 + 10)) +
      3375 * Real.log 2) +
  Real.log 2 + 2 * Real.log ((detDeg 3 3 : ℝ) + 1) + 1
```

**OPEN theorem after the `+2` retuning:** `stepOutput_consts_physical (T : StepTower stepHullMin)` constructs `C : StepOutputConsts 3 3` with these exact data. The constructor assignments, hence equalities `C.k0=T.κ0`, `C.kdec=T.κdec`, `C.k'=T.κ'`, `C.kapp=T.κ`, are definitional; so are `C.kout=3/2*T.κdec`, `C.kH=2*T.κdec-1`, `C.kdet=(T.κ-log 2-2*log((detDeg 3 3:ℝ)+1))/18`, `C.Bhull=collarB 3 3`, `C.lhull=hullRate 3 3 C.kdet`, `C.Kc=2*(K0 3 3 T.κ0+1)`, and `C.Ktot=C.Kc+C.Kall` when chosen by those formulas. `C.k0_ent` is `T.κ0_eq`; `kdec_ge,kdec_ge',kdec_le_kout,kout_le,kH_ge` need arithmetic from `T.κdec_eq,T.κ'_eq`, positivity, and the large factor 100 (the weaker `T.rate_rel` alone does **not** imply `kH_ge`). `kapp_ge` is `T.κ_lower`; `kdet_ge` is `T.det_rate` after `norm_cast`; `z_lt` is `T.det_z` after `Real.exp_neg`; `Bhull_eq` unfolds `collarB`; `lhull_eq` unfolds `hullRate`. `lhull_ge` uses `T.κmin_le` and `stepHullMin`, not merely `T.det_rate`. `StepOutputConsts.stepOutput_consts_exists_ge` (`:106–173`) independently picks a new κ, so it cannot prove `C.kapp=T.κ`.

After the two record edits, the proposed exact constructor statement is:

```lean
theorem stepOutput_consts_physical (T : StepTower stepHullMin) :
  ∃ C : StepOutputConsts 3 3, C.k0 = T.κ0 ∧ C.kdec = T.κdec ∧
    C.k' = T.κ' ∧ C.kout = 3 / 2 * T.κdec ∧ C.kH = 2 * T.κdec - 1 ∧
    C.kapp = T.κ ∧ C.kdet = (T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18 ∧
    C.Bhull = collarB 3 3 ∧ C.lhull = hullRate 3 3 C.kdet ∧
    C.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧
    C.Kall = max (2 * K0 3 3 T.κ0) (rootUnionK 3 3 1 T.m₁ T.κ0) ∧ C.Ktot = C.Kc + C.Kall
```

**PROVED numerical formula, OPEN joined Lean corollary.** Let `lamT := (T.κ - Real.log 2 - 2*Real.log((detDeg 3 3:ℝ)+1))/18`. After retuning, `T.κmin_le : stepHullMin≤T.κ` implies `3/2*T.κdec ≤ hullRate 3 3 lamT` by `c1_three=3375`, `cG_three=18`, `collarB=60750`, and `T.κdec_eq`; division by $18$ and $60751$ is positive. The exact proposed corollary is:

```lean
theorem StepTower.kout_le_hullRate (T : StepTower stepHullMin) :
  3 / 2 * T.κdec ≤ hullRate 3 3
    ((T.κ - Real.log 2 - 2 * Real.log ((detDeg 3 3 : ℝ) + 1)) / 18) := by
  sorry -- OPEN Lean proof; the scalar derivation is below.
```

This is the **OPEN-RATE** inequality of `DETFIT.md` as a numerical consequence once both records use the same tower. `DetCollarHull.hullRate` (`:239–241`) and `detCollarGrouped_bound` (`:265–306`) are **PROVED**; applying that rate to a class output still needs the chart/class bridge and output terms.

Here is the scalar calculation a Lean proof should mirror, with $D=(\operatorname{detDeg}(3,3):\mathbb R)+1$, $B=60750$, $u=\tfrac32 T.\kappa_{\rm dec}$, and $\ell=\log2$:

$$
\begin{aligned}
T.\kappa&\ge 18(1+B)(u+3375\ell)+\ell+2\log D+1,\\
\lambda_T&=\frac{T.\kappa-\ell-2\log D}{18}\ge (1+B)(u+3375\ell)+\frac1{18},\\
\operatorname{hullRate}(3,3,\lambda_T)&=\frac{\lambda_T}{1+B}-3375\ell\ge u+\frac1{18(1+B)}>u.
\end{aligned}
$$

For `kH_ge`, substitute `T.κ'_eq` and `T.κdec_eq`: the target reduces to $\kappa_{\rm dec}/2\ge4\kappa_0+c_1+7/2$. The fixed factor $100$ proves this from $\kappa_0\ge0$ and $c_1\ge1$; `T.rate_rel` is a weaker statement with zero in place of $\kappa'$. The other output-rate field is an equality: `kout = k' - k0 - 1` after the constructor equations.

**Second mismatch, REFUTED as a physical label budget.** Landed `StepOutputConsts.Kall_eq` (`:85`) fixes `Kall=2*K0 3 3 k0`. But `LabelRootUnion.rootUnion_entropy` (`:175–177,194–203`) bounds the all-root labels by `rootUnionK 3 3 1 T.m₁ T.κ0 = c1 3 3 * (3^(1+T.m₁))^3 * K0 3 3 (T.κ0-1)`. `SizeModEntropy.K0` (`:40`) ignores its rate argument, and `T.m₁_four` makes this factor strictly larger than 2. Thus the landed `Kall` cannot pay for `LabelAct.extendRootUnion` (`:296–304`), even after the $kappa_0$ repair. Replace `Kall_eq` by `Kall_ge : 2*K0 d L k0 ≤ Kall`; in the physical constructor set `Kall := max (2*K0 3 3 T.κ0) (rootUnionK 3 3 1 T.m₁ T.κ0)`. Then `Ktot=Kc+Kall`; `exists_beta0_stepOutput` (`StepOutputConsts.lean:195–212`) only needs `Ktot>0` and works after re-proving `theta_pos` (`:180–189`). Without this record change, call `stepOutput_consts_physical` a numerical join only, never a common-root physical closure.

## 3. The common source labels

**PROVED location of the choices.** `SourceDirectTermsScale.sourceDirectTerms_slice` (`:177–219`) picks one `𝒴,Tterms` *before* a chart point/source; `interaction_expansion_hat_dm_core_dir_eta_scaled` is called at `:219–235`. `DirectTerms.atThetaOn` (`ParamActivitySubspace.lean:79–90`) changes only point-dependent fields and keeps `𝒴,T`; `labelActFamilyOn` (`:96–103`) has fixed `thickLabels I.𝒴 I.dom`, fixed `S.blockSplit m₀ hp`, and analytic activities (`:129–144`). `SourceFamilyRelative.sourceFamilyRelative_scale` (`:209–241`) and `SourceAmpNonneg.sourceFamilyRelative_scale_nonneg` (`:289–344`) construct that family over `physVq`; their `𝒴,Tterms` are chosen before `∀ g`. `HatLabelsDirect.labelAct_of_directTerms` (`:79–90`) and `ParamActivityPhysical.dtAct` (`:170–178`) use the same domain-label construction. `StepActivityBound.toC_of_ae` (`StepComplexNonvanish.lean:148–165`) copies `BS,Lb,Lab,κ0,κ',Kc` exactly.

**PROVED where the public endpoint loses sharing.** `SourceActivityScale.lean:226–255` calls `stepActivityBound_zeroClass_source_scaled` *inside* `∀g`; that leaf calls `sourceDirectTerms_slice` anew (`SourceDirectTermsScale.lean:318–344`). Its `I₀,Ig` are therefore selected anew for each source. `StepActivityDirectBound.lean:271–272,326–336` chooses `Lb={Y//Y∈I₀.𝒴} ⊕ {Y//Y∈Ig.𝒴}`, `Lab=(thickLabels I₀.𝒴 I₀.dom).sum (thickLabels Ig.𝒴 Ig.dom)`, and `BS=S.blockSplit m₀ hp`; `StepActivityDirectGeneral.lean:283–300` makes the same choice for its scaled assembler. Shared `𝒴` in the separate family theorem does not imply that these independently chosen existential records are equal.

**OPEN exact endpoint shape.** With `S := T.step k hk N₁ ν β p₁`, `hp : 0<p₁`, `C := zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)`, first choose `β₀,CE,CF` after `T`; for every admissible `k hk N₁ [NeZero N₁] h3N hN ν hνpos hν β hβ p₁ hp hpLog` and `D : StepScaleData T k hk N₁ ν β p₁`, choose a single `𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k+1)))` and `hdom : ∀Y∈𝒴, IsDj 1 (k+1) Y` before `∀g`. Define `Lb := {Y//Y∈𝒴} ⊕ {Y//Y∈𝒴}`, `Lab := (thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)`, `BS := S.blockSplit 1 hp`. Then `sourceActivityC_scale_fromTower` returns, for every `g ∈ l1Ball 3 3 N₁ T.m₁ (k+1) 2`, records `BR : StepActivityBound S C g` and `BC : StepActivityBoundC S C g` with `BR.Lb=BC.Lb=Lb`, `HEq BR.Lab Lab`, `HEq BC.Lab Lab`, `HEq BR.BS BS`, `HEq BC.BS BS`, `BR.κ0=BC.κ0=T.κ0`, `BR.κ'=BC.κ'=T.κ'`, `BR.Kc=BC.Kc=2*(K0 3 3 T.κ0+1)`, `BR.κH=BC.κH=2*T.κdec-1`, and equal `εH≤CE(log b)^(3p)/√b+CF(log b)^p/√b`, $b=\beta3^k$. `HEq` is needed because `Lab` depends on the equality of the two subtype label types. This is stronger than the landed public theorem; no common-label endpoint is proved yet.

One syntactically explicit target (after the tower retuning) is:

```lean
theorem sourceActivityC_scale_fromTower (T : StepTower stepHullMin)
    {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
  ∃ β₀ CE CF : ℝ, 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
  ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ → 5 < N₁ →
  ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 →
  ∀ β : ℝ, β₀ ≤ β → ∀ (p₁ : ℝ) (hp : 0 < p₁),
  p₁ ≤ pLog A₁ p (β * 3 ^ k) → StepScaleData T k hk N₁ ν β p₁ →
  ∃ 𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))),
  ∃ hdom : ∀ Y ∈ 𝒴, IsDj 1 (k + 1) Y,
  ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, g ∈ l1Ball 3 3 N₁ T.m₁ (k + 1) 2 →
  ∃ BR : StepActivityBound (T.step k hk N₁ ν β p₁) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
  ∃ BC : StepActivityBoundC (T.step k hk N₁ ν β p₁) (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g,
    BR.m₀ = 1 ∧ BC.m₀ = 1 ∧ BR.Lb = ({Y // Y ∈ 𝒴} ⊕ {Y // Y ∈ 𝒴}) ∧ BC.Lb = BR.Lb ∧
    HEq BR.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom)) ∧ HEq BC.Lab BR.Lab ∧
    HEq BR.BS ((T.step k hk N₁ ν β p₁).blockSplit 1 hp) ∧ HEq BC.BS BR.BS ∧
    BR.κ0 = T.κ0 ∧ BC.κ0 = T.κ0 ∧ BR.κ' = T.κ' ∧ BC.κ' = T.κ' ∧
    BR.κH = 2 * T.κdec - 1 ∧ BC.κH = BR.κH ∧
    BR.Kc = 2 * (K0 3 3 T.κ0 + 1) ∧ BC.Kc = BR.Kc ∧ BR.εH = BC.εH ∧
    BR.εH ≤ CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
      CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k)
```

**OPEN leaves for that endpoint.** (a) `directTermsFamily_shared_labels`: under `I : DirectTerms ...`, `hF : DirectTermsFamilyOn ... I V`, `e₀,e∈V`, prove `(I.atThetaOn ... hF e₀).𝒴=I.𝒴 ∧ (I.atThetaOn ... hF e).𝒴=I.𝒴` and the analogous `T` equalities; `rfl` after unfolding the record update (`ParamActivitySubspace.lean:79–90`), about 25 lines. (b) `stepActivityBound_zeroClass_source_of_directTerms_shared`: with the same section hypotheses as the landed theorem at `StepActivityDirectBound.lean:259–345`, add `h𝒴₀ : I₀.𝒴=𝒴`, `h𝒴g : Ig.𝒴=𝒴`, `hdom : ∀Y∈𝒴, IsDj m₀ (k+1) Y`; return its `B` plus `B.κ0=κ0`, `B.κ'=κ'`, `HEq B.BS (S.blockSplit m₀ hp)`, `B.Lb=({Y//Y∈𝒴} ⊕ {Y//Y∈𝒴})`, `HEq B.Lab ((thickLabels 𝒴 hdom).sum (thickLabels 𝒴 hdom))`. Copy the final constructor at `:326–336`, rewrite `h𝒴₀,h𝒴g`, and use proof irrelevance for the two `dom` proofs; about 80–130 lines. (c) One from-tower source file (about 220–280 lines): set $q=1$ before `∀g`, call the direct-term family once, get `I₀` and `Ig=I.atThetaOn e_g`, apply (b), then `stepActivityBoundC_of_activityBound`; choose $\beta_0$ from `scale_C_items`, `sourceAmp_scale`, `daThreshold` after $T$ and at the final `Ktot` if root labels are appended. Do not infer fixed labels from the existing public `sourceActivityC_scale`.

## 4. Exact cuts for the other endpoints

| New endpoint | Landed tower/scale prologue to replace | First retained line and data still needed |
|---|---|---|
| `scale_chart_det_joint_fromTower` | `UniformChartMargins.lean:340–344` obtains a separate determinant/activity tower and its scale triple. | `:345` (`hβpos`), then `hatStepK_chartBall` `:347`, `scale_markedDisc_margin` `:348–352`. Supply `hact` from the from-tower real source/activity leaf, `hXi` from `D.xi`, `hdet` from the from-tower determinant leaf. No further tower witness. |
| `sourceFamilyRelative_scale_fromTower` | `SourceFamilyRelative.lean:209–220` invokes `sourceDirectTerms_scale` and then selects the scale terms. | `:221` (`refine`), then `:222–241` uses `val,𝒴,Tterms,I`, `hcont`, `hmem0`, `hmemg`, `h3N`, `hβ1`, and `bgHyp_lv`; these are **not all fields of `StepScaleData`**. Supply a from-tower direct-terms family leaf, or re-run its `SourceDirectTermsScale.lean:421–505` proof from `T,D`. |
| `sourceFamilyRelative_scale_nonneg_fromTower` | `SourceAmpNonneg.lean:180–255` constructs the tower, ray, `FlCore`, chart datum and covers. | `:256` (`hBh0`); retain/recreate `Q,P,β₁,hA'`, log/positivity and `hBh` from `:208–240` since `T,D` hold none of the amplitude constants or `hBh`. The direct-term call starts `:289`. |
| `expSourceChart_scale_fromTower` | `ExpSourceChart.lean:381–409` chooses old rates, radii and tower, then derives ray/core/`XiCData`. | `:410` (`hβ0`), then `:411–440` builds `JointRep` and the `W2` identity. `D` supplies ray/core/xi; `hHB=bgHyp_lv`, `compWeight_three_mem`, `covSupConstC_nonneg` and `T`'s `large_block,dom_margin,coer_margin,δc_small,c7_cap,bg1_cap,t_cap,bg0_cap,cK2_cap,cK2'_cap` are still needed. |

**PROVED supporting ranges.** The from-tower determinant can wrap `DetOutputTermsWitness.detExpansionLocC_scale_of_tower` (`:194–244`) after `T.det_z`. The chart marked-disc wrapper at `UniformChartMargins.lean:242–271` has its own tower choice and must similarly be factored. None of these proofs requires a new `exists_witness_params` once `T.δ,T.δ'` are used. `D` does not contain the source amplitude majorant, `Q,P`, `β₁`, `hBh_of_xi`, or the source `𝒴,Tterms` family; a prover must reconstruct them instead of claiming they are fields.

## 5. Leaf order

1. **OPEN, serial:** retune `StepTower.lean` to $kappa_0=a_{\rm ent}+2$ and add the numerical `stepHullMin`/`StepTower.kout_le_hullRate` lemma (about 120–180 lines combined). The existing generic tower is **PROVED** and untouched.
2. **OPEN, serial:** replace `StepOutputConsts.Kall_eq` by a lower-bound field, preserve its existential witness, prove `theta_pos`, and construct the joined `stepOutput_consts_physical` record with `Kall=max(...)` (two files, each ≤250 lines). This follows leaf 1; the numerical hull proof can be developed alongside the label-budget record change.
3. **OPEN, parallel after leaf 1 and the landed `StepScaleData`:** factor the determinant endpoint (≤130 lines), the exponential-chart endpoint (≤180), and the source direct-term family endpoint (≤280). They read the same immutable `T,D` and need no common source labels yet.
4. **OPEN, parallel after the direct-term family:** prove `directTermsFamily_shared_labels` (≤50 lines) and the enriched source assembler (≤150). Then build `sourceActivityC_scale_fromTower` (≤300) using one family before the source quantifier.
5. **OPEN, final joins:** re-run `sourceFamilyRelative_scale_nonneg` (≤300) and `scale_chart_det_joint` (≤120), take one maximum of all thresholds, and use `StepOutputConsts.theta` at the corrected `Ktot`. The grouped determinant rate then meets `κout` numerically; class-domain locality, symmetry, and physical output terms remain separate open inputs.
