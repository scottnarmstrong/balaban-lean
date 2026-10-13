# The scaled datum in the step chart

**Status convention.** PROVED means a cited Lean declaration has the stated conclusion or the displayed consequence follows by unfolding. PROVED CONDITIONAL ON names all remaining premises. OPEN is an unlanded assertion. REFUTED identifies an invalid proposed implication. The writable deliverable is this note; all cited Lean files under `/home/scott/Balaban` were read only. Source reference for the class enlargement is P4, printed p. 704, (4.19); for the new terms it is P4 (4.17)–(4.18). The pertinent P3 (Ξ2) implementation is `SmallField/XiPerturb.lean:xiC_perturb`.

## 1. The exact class predicates

**PROVED.** At top level $K=k+1$, `Fluctuation/RenormExpBounds.lean:XiCOneReal G a ν ε D` is
```lean
∃ (Ψ₀ : Torus d (N₀ * L ^ K) → Fin N → ℝ) (h₀ : Fin N → ℝ)
  (Ψ'' : Torus d (N₀ * L ^ K) → Fin N → ℂ),
  XiC G a ν K 1 ε Ψ₀ h₀ Ψ'' 0 ∧ RealizesC D Ψ₀ h₀ Ψ'' 0
```
`Localization/I5Chain.lean:XiCData G a ν K 1 ε D` is the same existential with an arbitrary `h''`; `Fluctuation/RenormDomainParams.lean:xiCData_of_xiCOneReal` sets `h''=0`. In `SmallField/Xi.lean`, the full `XiC` predicate is exactly
```lean
0 < σ ∧ 0 < ε ∧ ∃ Dr Dc : BgData G N,
  XiAt G a ν n σ ε Dr Ψ₀ h₀ ∧ RealizesC Dc Ψ₀ h₀ Ψ'' h'' ∧
  InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν Dc ∧
  XiCBounds G ν σ ε Dr Dc Ψ'' h''
    (bgField G a ν Dr) (bgFieldC G a ν (bgC0 d L N) Dc)
    (bgMult G a ν Dr) (bgMultC G a ν (bgC0 d L N) Dc)
```
`XiAt` is `Realizes Dr Ψ₀ h₀ ∧ InUnionDomainR G (bgC1 d L N) ν Dr ∧ XiBounds G ν n σ ε Dr h₀ (bgField G a ν Dr) (bgMult G a ν Dr)`; `RealizesC` asserts $D^c.\Psi=\Psi_0+\Psi''$ on `dataSites G` and $D^c.h=h_0+h''$ on $G.\Omega 1$. Its two union-domain constants are **`bgC0` and `bgC1`**, not `c7` or `thm73C2`.

**PROVED (real center clauses, exact bounds from `XiBounds`).** With $\phi_r=\mathrm{bgField}(D^r)$, $\alpha_r=\mathrm{bgMult}(D^r)$ and $\ell(x)=G.\mathrm{spacing}(x)$, the seven fields are:
```lean
grad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
  vn (fun i => barField G Dr.Ψ φr (x + Pi.single μ 1) i - barField G Dr.Ψ φr x i) <
    σ * ε / G.spacing x ∧
  vn (fun i => barField G Dr.Ψ φr (x - Pi.single μ 1) i - barField G Dr.Ψ φr x i) <
    σ * ε / G.spacing x
lap : ∀ x ∈ G.Ω 1, vn (fun i => ∑ μ : Fin d,
  (barField G Dr.Ψ φr (x + Pi.single μ 1) i +
   barField G Dr.Ψ φr (x - Pi.single μ 1) i - 2 * barField G Dr.Ψ φr x i)) <
    σ ^ 2 * ε / G.spacing x ^ 2
mult : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖αr x‖ < σ ^ 2 * ε
close : ∀ x ∈ G.Ω 1, vn (fun i => Dr.Ψ x i - blockAvg G φr x i) < σ ^ 2 * ε
collarBond : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' →
  vn (fun i => Dr.Ψ z i - Dr.Ψ z' i) < σ * ε
mass : ∀ x : G.Ω 1, Real.sqrt ν * G.spacing (x : Torus d (N₀ * L ^ K)) *
  vn (fun i => φr (x,i) - (h₀ i : ℂ)) < σ * ε
hnorm : ν * ((L : ℝ) ^ n) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (σ * ε) ^ 2
```
`XiAt` also requires `InUnionDomainR`; increasing $\varepsilon$ leaves its datum and union witness unchanged. `SmallField/XiPerturb.lean:xiBounds_mono` proves monotonicity of these seven bounds when $0\le\sigma$, $0\le\varepsilon\le\varepsilon_2$.

**PROVED (complex clauses, exact bounds from `XiCBounds`).** Set $F=\overline\phi_c-\overline\phi_r$, $v=\phi_c-\phi_r$, $b=\alpha_c-\alpha_r$. The eight fields are:
```lean
grad : ∀ x ∈ G.Ω 1, ∀ μ : Fin d,
  vn (fun i => (F (x + Pi.single μ 1) i) - F x i) < σ * ε / G.spacing x ∧
  vn (fun i => (F (x - Pi.single μ 1) i) - F x i) < σ * ε / G.spacing x
lap : ∀ x ∈ G.Ω 1, vn (fun i => ∑ μ : Fin d,
  (F (x + Pi.single μ 1) i + F (x - Pi.single μ 1) i - 2 * F x i)) <
    σ ^ 2 * ε / G.spacing x ^ 2
mult : ∀ x : G.Ω 1, G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 * ‖b x‖ < σ ^ 2 * ε
val : ∀ x : G.Ω 1, vn (fun i => v (x,i)) < ε
close : ∀ x ∈ G.Ω 1, vn (fun i => Ψ'' x i - blockAvg G v x i) < σ ^ 2 * ε
collarBond : ∀ z ∈ collar G, ∀ z' ∈ collar G, Adj z z' →
  vn (fun i => Ψ'' z i - Ψ'' z' i) < σ * ε
hAbs : ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn (h'' x) <
  (σ * ε) ^ 2 / ε
hDot : ∀ x : G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex (x : Torus d (N₀ * L ^ K))) ^ 2 *
  ‖∑ i, φr (x,i) * h'' x i‖ < (σ * ε) ^ 2
```
Here $F,v,b$ are definitional abbreviations for the exact differences in `Xi.lean:XiCBounds`; the source uses those differences inline.
These are **not** a single bound on $\|\Psi''\|$: `grad`, `lap`, `mult`, `val`, and `close` use the *new nonlinear background solution*. The $h$ component is unchanged by $\theta$; choosing $h''=0$ keeps `hAbs` and `hDot` automatic, but does not remove the real-center `mass` and `hnorm` clauses.

**PROVED.** `Background/Data.lean:InUnionDomainC` means $\exists\delta,\epsilon>0$ with $\delta\le\epsilon\le bgC0$, $\delta\le bgC1$, $\nu L^{2K}\epsilon^2\le\delta^2$, and `InDomainC G ν δ ε Dc`. `Background/Def5Response.lean:InUnionDomainC.mono` only enlarges the **constant** $c_1$ for the *same datum*; it does not transport membership to $\theta D$. `Fluctuation/StepComplexHat.lean:isDecBg_one_of_xiCData` derives membership at $c_7$ **after** `XiCData` is known. Using either as the perturbation proof is **REFUTED**. `xiC_perturb` itself builds the new `InDomainC` and `InUnionDomainC` from `perturb_inPsiTildeC`, `Background/Prop51`'s landed `theorem52_perturb_eq`, and `bgBounds_of_parts`.

## 2. One quantitative perturbation, not eight separate estimates

**PROVED.** Fix $D\in\mathrm{XiCOneReal}(G,a,\nu,\varepsilon_r)$, $\|\xi\|<r_0$, and $\zeta=\mathrm{renZeta}(\varepsilon_r,\xi)$. Put $\delta\Psi(x,i)=\zeta D.\Psi(x,i)$ and $\Delta_3=\frac32\varepsilon_r r_0$. `renMassU` is irrelevant to this fixed-mass class inclusion. `RenormExpLemma35.lean:norm_renZeta_le` gives $|\zeta|\le\varepsilon_r\|\xi\|$. Under `XiCOneReal.factors` (its `BgHyp`, `small1`, `xiC1 εr ≤ bgC1` premises), $\mathrm{vn}(D.\Psi(x))\le3/2$ on `dataSites G`; `vn_smul_complex` then gives $\mathrm{vn}(\delta\Psi(x))\le\Delta_3$. Scalar multiplication preserves `IsLayerConstant`, directly from `D.Ψ_layerConst`.

**PROVED.** Take the **same** real center $(\Psi_0,h_0)$ and the new displacement $\Psi''_\theta=\Psi''+\delta\Psi$, $h''_\theta=0$. On `dataSites G`, where realization is asserted, this is $(1+\zeta)\Psi''+\zeta\Psi_0$. Outside those sites no identity $D.\Psi=\Psi_0+\Psi''$ is required by `RealizesC`, so the globally safe witness is $\Psi''+\delta\Psi`. The h-realization is unchanged. `Localization/I5FluctChain.lean:xiCData_perturb` applies `xiC_perturb` and proves *all* real, complex, and union-domain clauses at radius $\varepsilon_r+\mathrm{xiK2}(d,L,N)\Delta_3$; `xiK2` is exactly $1+L+2dL^2+(N+1)cK2(d,L,N)$. Thus the tempting scalar inequality $\|\Psi''_\theta\|\le(1+|\zeta|)\|\Psi''\|+|\zeta|\|\Psi_0\|$ is only a preliminary norm estimate, **not** a proof of `XiCData`.

**OPEN (`ThetaChartMargin`, proposed declaration).** The following record has precisely the numeric premises of `xiCData_perturb`; $H:BgHyp$ is a separate theorem hypothesis. Taking the target radius to be the exact sum avoids an additional unlanded `XiCData` radius-monotonicity lemma.
```lean
structure ThetaChartMargin (d L N : ℕ) [NeZero L]
    (εren εstep r₀ : ℝ) : Prop where
  ε_pos : 0 < εren
  r_pos : 0 < r₀
  δ_nonneg : 0 ≤ (3/2:ℝ) * εren * r₀
  δ_one : (3/2:ℝ) * εren * r₀ ≤ 1
  small : (4*d+6) * ((2*d+1) * εren) ≤ 1
  data : xiC1 d * εren + 5 * ((3/2:ℝ)*εren*r₀) ≤ bgC1 d L N
  star : (3/2:ℝ)*εren*r₀ ≤ deltaStar d L N
  K₁ : bgK1 d L N * (xiC1 d * εren) ≤ deltaStar d L N
  c₀ : bgK1 d L N * (xiC1 d * εren) +
       cK2 d L N * ((3/2:ℝ)*εren*r₀) < bgC0 d L N
  radius : εstep = εren + xiK2 d L N * ((3/2:ℝ)*εren*r₀)
```
The fields `δ_nonneg` and `δ_one` can later be derived from `ε_pos`, `r_pos`, `star`, and `deltaStar_le_one`; keeping them explicit makes the first theorem a direct call to `xiCData_perturb`. An equivalent record may use a radius inequality, but then prove `xiCData_mono_radius` separately (all `XiBounds`/`XiCBounds` right sides grow at $\sigma=1$ and $h''=0$).

**PROVED CONDITIONAL ON OPEN `ThetaChartMargin` and the elementary datum-identification lemma.** With $\delta\Psi=\zeta D.\Psi$, use `xiCData_of_xiCOneReal hD`, `XiCOneReal.factors` for $3/2$, `norm_renZeta_le`, and `xiCData_perturb H` with $\delta_3=\Delta_3$. It returns `XiCData … εstep (perturbData G D δΨ hδΨc)` after rewriting `margin.radius`. The identity `perturbData G D δΨ hδΨc = renThetaDatum εren D ξ` follows by `BgData.eq_of_raw`: on `dataSites` use `perturbData_Ψ`, elsewhere use `D.Ψ_zero`; both h components are $D.h$. This is the only datum bridge missing from landed declarations. There is no need to reproved the background gradient or union-domain estimates.

## 3. One tower, two chart radii

**Recommendation: keep the renormalization radius $\varepsilon_r=T.t$ and enlarge only the step chart to $\varepsilon_s=T.t+\mathrm{xiK2}(3,3,2)\frac32T.tR.r_0$.** This is P4 (4.19)'s direction of inclusion and keeps $\zeta=\mathrm{renZeta}(T.t,\xi)$, the physical renormalization coordinate. For a fixed `R : StepTowerRenSol`, the *numeric* fields of `ThetaChartMargin 3 3 2 R.t εs R.r₀` follow from landed margins: `R.core` gives `small` and `xiC1*R.t ≤ c7 ≤ bgC1`; `R.bg1_cap` gives `data` using `compC4_ge`, `bgK1_ge_one`, and `R.r₀_le`; `R.sol_ζ` gives `star`; `R.sol_margin` gives `K₁`; `bgC1_facts` and `R.bg0_cap` give `c₀`; `deltaStar_le_one` gives `δ_one`. These are finite real inequalities; a Lean assembly lemma is OPEN, but no new field-theoretic assertion is needed.

**OPEN (the step chart package).** `StepTower.core` and `FlCore` are at **`T.t`**, as are `Inhabited/StepTowerScale.lean:detExpansionLocC_scale_fromTower`, `Inhabited/DetPackageFromTower.lean:detPackage_fromTower`, and `Fluctuation/DetGroupedAnalytic.lean:detGrouped_chart_family_fromTower`. None gives the determinant record at $\varepsilon_s>T.t$. For any arbitrary existing tower, the needed `FlCore` at $\varepsilon_s$ cannot be deduced from its non-strict `c7le` and `small1` fields. Add a refined tower with a second `stepRadius`, `FlCore` there, `decDomMargin 3 3 2 BG κ (xiC1 3 * stepRadius) < δc`, and `K4 3 3 2 BG κ * (xiC1 3 * stepRadius) < coerciveConst 3 / 2`; `detExpansionLocC_scale_fromTower` consumes these last two margins. Then generalize these **three producer theorems** to accept the new radius; future marked energy and observable families use the same enlarged chart. Existing `renLocC1_scale_of_tower`, `renDec_sharp_scale_of_tower`, `exists_isRenSol_scale_of_tower`, `renEndpoint_scale_of_tower`, and `RenormExpInput` keep their current $T.t$ and $R.r_0$ types.

**PROVED CONDITIONAL ON OPEN refined-tower existence.** Such a refinement is mathematically satisfiable, but is **not a property of every landed `StepTowerRenSol`**. At the tower-construction stage `TowerCoreRatesRenSol.lean:tower_core_rates_at_least_renSol` chooses $t>0$ from eventual inequalities at $t=0$; add `FlCore` at $2t$ and the two determinant margins at $2t$ to that finite intersection, using `flCore_level_eventually` under $t\mapsto2t$ and continuity of `decDomMargin` at zero. The former gives its `δ₁=2t`; replacing it by $t$ preserves `FlCore.δ₁_pos` and `.δ₁_le`. Shrink the subsequently chosen $r_0$ until $\frac32\mathrm{xiK2}(3,3,2)r_0\le1$; the fields of `StepTowerRenSol` are upper bounds in $r_0$, and `StepTowerRen.shrink` already proves the base part. Then $\varepsilon_s\le2t$. A short `FlCore.mono_eps` transports the $2t$ core to $\varepsilon_s$; monotonicity of the polynomial `decDomMargin` transports the two determinant margins; `flCore_level_transfer` transports the core to every scale. The new radius-cap and step-core construction remain **OPEN** Lean leaves.

**Alternative, more invasive.** Set $\varepsilon_r<t$ while keeping the step chart at $t$. To preserve P4's scaling $\zeta=t\xi_0$, the current one-radius `RenormExpInput` must split its class radius from the `renC1On`/`IsRenSol` scaling radius; otherwise one must reparametrize $\xi_0$ and pull back all analytic and locality terms. `renLocC1_scale_of_tower` and `renLocC1_scale_of_tower_of_le` currently fix `XiCOneReal … T.t` and `renC1On … T.t`; `renDec_sharp_scale_of_tower`, `renEndpoint_scale_of_tower`, `exists_isRenSol_scale_of_tower`, and the `RenormExpInput` consumers are likewise tied to $T.t$. A simple restriction of `HasLocPrinciple` is insufficient for its universal transfer bound at the smaller class constant; `HasLocPrinciple.mono_class` enlarges the class, not this reverse transfer. This alternative requires a domain restriction plus constants audit, or a two-radius version of those theorems. It changes more existing renormalization interfaces than the recommended step-chart extension.

## 4. Exact theorem target and analyticity

**OPEN (`renE0_theta_domain`), with the now explicit proof path:**
```lean
theorem renE0_theta_domain (S : StepSetting d L N₁ m₁ k N ϱ)
    (H : BgHyp d L (k+1) ϱ S.a S.ν) (εren εstep r₀ : ℝ)
    (hM : ThetaChartMargin d L N εren εstep r₀)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν εren D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k+1) 1 εstep (renThetaDatum εren D ξ)
```
The proof has four steps: get the original `XiCData` by `xiCData_of_xiCOneReal`; prove the $3/2$ datum bound from `XiCOneReal.factors`; apply `xiCData_perturb` with `hM` and the layer-constant $\delta\Psi$; rewrite its perturb datum by the bridge above. The real-center, $h$, nonlinear displacement, and union-domain clauses are thereby supplied by the **proved** `xiC_perturb` proof, conditional only on these explicit numeric premises. Splitting into leaves: (1) `renTheta_delta_layerConst`/`renTheta_delta_bound` (80–130 lines, Sonnet, start now); (2) `renTheta_eq_perturbData` (70–120, Sonnet, start now); (3) `thetaMargin_of_stepTowerRenSol` (120–220, strong, start now); (4) `renE0_theta_domain` (80–140, Sonnet, after 1–2); (5) `stepCore_two_radius` and generalized determinant package (separate leaves, each ≤300, strong, after the tower refinement).

**REFUTED (relative analytic composition alone).** `DetExpansionLocC.detGrouped_analyticOnNhd_rawSub` has source type `rawSub N S.G'`, while `IsLocExp.analytic` in `RenormExpCauchy.lean` asks `AnalyticOnNhd` on **ambient** `RawData × (Fin 3 → ℂ)` at points of `expDom`. A function defined only on `rawSub` cannot be composed directly to obtain that ambient statement.

**PROVED CONDITIONAL ON OPEN chart inclusion; analytic extension construction.** `Fluctuation/DetOutputTerms.lean:DetExpansionLocC.analyticAt_raw` supplies, for each cube set $T$, an ambient $A_T:\mathrm{RawData}\to\mathbb C$, analytic at each chart raw datum and equal there to `E.term D T`. Choose these $A_T$ once. For a fixed hull $X$, set $\widehat G_X(p)=\sum_{T\in\mathrm{detCollarFibre}(1,X)}A_T(p)$ and define the ambient term $q\mapsto\widehat G_X(\Theta_{\rm raw}(q))$, where $\Theta_{\rm raw}((\Psi,h),\xi)=((1+\varepsilon_r\xi_0)\Psi,h)$ is polynomial on all ambient raw data. At every $q\in\mathrm{expDom}$, `renE0_theta_domain` places $\Theta_{\rm raw}(q)$ in the step chart, so every $A_T$ is `AnalyticAt` there. `Finset.analyticAt_fun_sum` and `AnalyticAt.comp` give `AnalyticOnNhd ℂ` of the ambient term on `expDom`; equality on `expDom` with `E.detGrouped (renThetaDatum …) X` follows from each `analyticAt_raw` value clause. The relative `detGrouped_analyticOnNhd_rawSub` remains useful for step-side work but is **not** the final `IsLocExp.analytic` proof. This is E0THETA leaf 5, after the enlarged determinant family and chart inclusion.

**Confidence.** High that `xiCData_perturb` is exactly the missing field-theoretic theorem and that the numeric margin can be assembled from `StepTowerRenSol`. Medium that the least-change tower extension is the recommended enlarged step chart: its finite-radius existence argument is clear, while its Lean producer refactor and marked-family use are open. High that an ambient extension is required for `IsLocExp.analytic` as currently typed.
