# MARKREAL: physical marked derivative and global marks

**Scope and status.** All cited Lean paths are relative to `/home/scott/Balaban/Balaban`; that tree was read only.
**PROVED** means a landed declaration or its stated elementary consequence.
**PROVED CONDITIONAL ON** means a landed theorem with its explicit hypotheses.
**OPEN** is a missing producer or bridge; **REFUTED** identifies an invalid shortcut.
The old ledger in `notes/phase1/MARKPARAM.md` predates `MarkedEvJoint.lean`, `MarkedCubicJoint.lean`, and `Polymer/LabelRootUnion.lean` in their present form.

## A. What the real-slice premise says

Fix a step $S$, old generating set $H_m=\mathrm{stepG}$, zero class, a root $z$, a physical datum $D$ with $D.h=h_0$, and $S_D=S.\mathrm{withDatum}(D,h_D)$.
Put $v_t=u\,S_D.\mathrm{shiftUC}(x)+t\,S_D.\mathrm{maskUC}_z(S_D.\mathrm{shiftUC}(x))$ and $\Theta=\mathrm{rawOf}(D)$.
The target mark is $D\Phi_1^{\mathbb C}(u\,\mathrm{shiftUC}(x))[\mathrm{maskUC}_z(\mathrm{shiftUC}(x))]$ for real $u\in[0,1]$.

`Fluctuation/MarkedSharpCount.lean:hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` has the following typed premises, in addition to $S,z,u,x$:

| Premise | Exact type or content | Status |
|---|---|---|
| `ha₁`, `H` | `0 < S.a₁`; `BgHyp d L (k+1) ϱ S.a S.ν`. | **PROVED CONDITIONAL ON** physical `FlCore`/`bgHyp_lv` and $a_1>0$. |
| `hD2` | `InUnionDomainC S.G' (bgC0 d L N) (thm73C2 d L N) S.ν S.D'`. | **PROVED CONDITIONAL ON** `XiCData` and `FlCore`: `StepComplexHat.lean:isDecBg_one_of_xiCData` followed by `InUnionDomainC.mono` and `thm73C3_le_thm73C2` (as used in `isUnit_opHk_bgC`). |
| `hC`, `hc7` | `FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁`; `c7 d L N BG κ ≤ thm73C3 d L N`. | **PROVED CONDITIONAL ON** `tower_core_rates`, `flCore_level_transfer`, and the same tower witness. |
| `hR`, `hRs`, `hsmall`, `hnum`, `hnum'` | $2\le R$; $R\delta_1\le\mathrm{deltaStar}$; $\mathrm{cK2}R\delta_1<\mathrm{bgC0}/2$; $\mathrm{cK2}\delta_1\le c6'$; $\mathrm{cK2'}\delta_1\le c6'$, with `famConst(BG₂,κ)` and `gamma1/8` in both $c6'$ terms. | **PROVED CONDITIONAL ON** `Inhabited/StepActivityDirectPhysicalRates.lean:tower_core_rates` at $R=2$, $\delta_1=\varepsilon=t$; its displayed five inequalities are literal fields. |
| `hD` | `XiCData S.G' S.a S.ν (k+1) 1 eps S.D'`. | **PROVED CONDITIONAL ON** the datum component of `physV`; `physSΛ` is `XiCRaw × l1Ball` (`Fluctuation/PhysicalTerms.lean:physSΛ`). |
| `hreal` | Every $\psi'\in\mathrm{FlBall}(H_m,\delta_1)$ that is `IsLayerConstant` has a lower datum with the **same $h$**, exact `compTangent = ψ'`, and a `lineAt` in `InUnionDomainC Hm bgC0 bgC1` for every $|t|<R$. | **PROVED CONDITIONAL ON** the preceding numeric fields by `Fluctuation/Prop33CloseReal.lean:hreal_level`; its extra inequality is $2\,\mathrm{compC4}(d)\,\mathrm{bgK1}\,\mathrm{xiC1}\,\varepsilon+5R\delta_1\le\mathrm{bgC1}$, landed in `tower_core_rates` for $R=2$. |
| `𝒴`, `Ev`, `han`, `hsum` | Finite old-block domains; `Ev` analytic on `XiCRaw × FlBall`; `blockEnergyOne = Σ_{Y∈𝒴} Ev` for every chart datum and fluctuation field. | **PROVED CONDITIONAL ON** the cover/rate hypotheses of `Fluctuation/MarkedSharpCount.lean:marked_count_scaled`; its one `Ev` and `hsum` are uniform in datum. `MarkedCubicJoint.lean:markedCubic_joint_param` supplies the same shape for one old block. |
| `hR₁`, `hr`, `ht₁` | $1<R_1$, $0<r$, $0<t_1$. | **PROVED** for $R_1=17/16$, $t_1=1/16$, and the scale-dependent $r=\mathrm{lvR}(\kappa,t,\beta_k,p_1)/4>0$ from `StepScaleData.r_pos`. |
| `hdisc` | For $|t|<t_1$, $|\sigma|<R_1+r$: $\sigma\,\mathrm{liftC}(v_t)\in\mathrm{FlBall}(H_m,\delta_1)$. | **PROVED CONDITIONAL ON** a uniform pointwise bound $Y_0$ for `shiftUC x` and $(R_1+r)(|u|+t_1)Y_0<\delta_1`, by `Fluctuation/MarkedTangent.lean:markedDisc_hdom`; `MarkedCubicJoint.lean:markedDisc_field_mem_flBall` is the arbitrary unit-field version. |
| `hdomT` | For every $|t|<t_1$ and real $s\in[0,1]$, eventually in complex $\zeta\to s$, `InUnionDomainC Hm bgC0 bgC1 S.ν (S.dataUC (S.psiAtV ζ v_t))`. | **OPEN** as a named uniform wrapper; fixed-datum proof from `hreal_level`, `hdisc`, `isLayerConstant_liftC`, and the affine identity `MarkedCubicTaylor.lean:dataUC_psiAtV_eq_lineAt` is given below. |

The conclusion is a `HasDerivAt` at $t=0$ for $t\mapsto S.\mathrm{Phi1C}(\mathrm{zeroClass},v_t)$ with derivative $-\beta\sum_{b,Y}\partial_t\mathrm{markedBlockTerm}(Ev_{b,Y},\omega,\ldots,\Theta,0)$.
It is a **fixed-datum theorem**: its hypotheses do not themselves quantify over the physical slice.
**PROVED CONDITIONAL ON** `hdomT`, `hdisc`, `hreal`, `han`, and `hsum`: `MarkedCubicTaylor.lean:VkC_marked_eq_block_terms` gives $V_k^\mathbb C(\psi_0+v_t)=\sum_{b,Y}\mathrm{markedBlockTerm}_{b,Y}(t)$ for every $|t|<t_1$; `Phi1C_zeroClass` makes $\Phi_1^\mathbb C=-\beta\sum_{b,Y}\mathrm{markedBlockTerm}_{b,Y}$ on that disc. `analyticOnNhd_markedBlockTerm` makes the finite sum differentiable there, so the derivative identity follows by eventual equality, exactly as the proof of `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` does.
`marked_count_scaled` supplies a single $Ev$, a finite bridge identity, a rooted bound, and the root/domain facts; its estimate separately assumes $Y_0\ge0$, $\|\mathrm{shiftUC}(x)(b)\|\le Y_0$, $(R_1+r)(|u|+t_1)Y_0<\delta_1$, $0<t_0<t_1$, and $\Theta\in\mathrm{XiCRaw}$.
The resulting rooted rate is $a=2\kappa_{\rm dec}-1$ and its per-root coefficient is $3\|E_*\|c_1M^dn_F e^{a c_{Br}}/(r^3t_0)$, before multiplication by $\beta$.

The derivative in `E1MarksC` is an **ambient `fderiv`**, so the line derivative alone does not identify its integrand.
**PROVED CONDITIONAL ON** `ClassRegularLocC (zeroClass)` and $\|x\|\le p_1$: `MarkedCubicTaylor.lean:differentiableAt_Phi1C_of_classRegularLocC`, `hasDerivAt_Phi1C_marked`, and `deriv_Phi1C_marked_eq_E1MarksC_integrand` identify it for every real $u\in[0,1]$, including $u=0$.
`StepComplexLocal.lean:classRegularLocC_zeroClass` is landed with chart, covariance, $p_1<p^+$, and numeric hypotheses; it must be re-instantiated for **each** $S_D$.
**REFUTED:** replacing this `fderiv` identification by `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` alone; the latter only determines a one-dimensional derivative.

## A2. Uniform producer on the constant-$h_0$ slice

Let $V=\mathrm{physV}(S,1,\nu,t)\subset\mathrm{physParam}(N,S)$ and define the slice by $e\in V$, $e.1=\mathrm{rawOf}(D)$, and $D.h(y,i)=(S.h_0(i):\mathbb C)$ for all $y,i$.
**PROVED:** `Fluctuation/ParamActivitySubspace.lean:physV` is open in `physParam=rawSub×sources` and its datum lies in `XiCRaw`; `Inhabited/UniformChartMargins.lean:hatStepK_chartBall` gives a positive chart radius independent of $\beta,p_1,\delta$ at fixed $k,N_1,\nu$.
The chart-ball theorem describes a neighbourhood of the step datum; it does **not** say all of `physV` lies in that ball.
All slice data already have `XiCData` by `physV`, and the tower bounds above are independent of $D$.
`UniformChartMargins.lean:scale_markedDisc_margin` proves $B\le t\,C_{\max}/[2(C_{\max}+1)]<t/2$ and $(9/8)^2B\le81t/128<t$, with $B=\sqrt2\,|\beta_k^{-1/2}|\,C_k c_\psi$.
For $|u|\le1$, $R_1=17/16$, $r=t_1=1/16$, this pays a fixed small `hdisc` uniformly once `shiftUC x` has the chart-wide bound $Y_0\le B$.
The sharp cubic estimate uses the larger **formula** $r_{\rm cub}=\mathrm{lvR}(\kappa,t,\beta_k,p_1)/4$, selected before the scale although its value depends on $\beta_k,p_1$.
**PROVED CONDITIONAL ON** the common `Inhabited/StepTowerScale.lean:StepScaleData` fields `r_pos`, `fl_radius`, `ray_margin`: with $\rho=p_1$ and $Y_0=\mathrm{markedRad}(\rho)$, $(17/16+r_{\rm cub})(17/16+1/16)\le4+\mathrm{lvR}$, so the ray margin $(4+\mathrm{lvR})\rho<c_\psi$ and the fluctuation radius $\mathrm{markedRad}(c_\psi)<t$ give $(R_1+r_{\rm cub})(R_\sigma+t_1)Y_0<t$.
This keeps the $r_{\rm cub}^{-3}$ gain; fixing $r=1/16$ in the final rooted bound would lose it.
**PROVED CONDITIONAL ON** `FlCore` and its own background identification: `scale_markedDisc_mem_flBallLC` gives a uniform marked `FlBallLC` conclusion; **OPEN** is treating its existential tower witness as identical to another tower witness. Use the explicit `scale_markedDisc_margin` with the common tower instead.
**PROVED:** `Fluctuation/MarkedCubicJoint.lean:StepSetting.exists_analytic_shiftUC_chart`, instantiated with its hat bound $c_\psi=p_1$ from $\|x\|\le p_1$, constructs one analytic $Q(\Theta)$ with coordinate bound $\mathrm{markedRad}(p_1)$ for **every** $\Theta\in\mathrm{XiCRaw}$ and $Q(\mathrm{rawOf}D)=(S_D).\mathrm{shiftUC}(x)$ for every constant-$h_0$ slice datum $D$ satisfying its `hD` and `XiCData` premises.
This chart-wide bound is the correct source of $Y_0$ for joint datum/mark analyticity; a bound only at the central datum would not suffice.

**OPEN — proposed `markReal_slice`.** Fix the common physical tower, $R=2$, $R_1=R_\sigma=17/16$, $t_1=1/16$, $t_0=1/32$, the radius rule $r=r_{\rm cub}$ above, the `marked_count_scaled` cover and rate hypotheses, and one $(𝒴,Ev,han,hsum)$ supplied by that theorem **before** $D,x,u$.
For every $e\in V$ on the constant-$h_0$ slice, every `BgData D` represented by $e.1$, every $x:S_D.E$ with $\|x\|\le p_1$, every root $z$, and every real $u\in[0,1]$, return the exact `hD2`, `hD`, `hreal`, `hdisc`, `hdomT`, and `DifferentiableAt ℂ (S_D.Phi1C zeroClass) ((u:ℂ) • S_D.shiftUC x)` required above, and the equality
$$D\Phi_1^{\mathbb C}((u:\mathbb C)\,\mathrm{shiftUC}x)[\mathrm{maskUC}_z(\mathrm{shiftUC}x)]
=-\beta\sum_{b,Y}\partial_t\mathrm{markedBlockTerm}(Ev_{b,Y},\omega,\ldots,\mathrm{rawOf}D,0).$$
The conclusion is uniform in $D$: the same radii, $Ev$, and numeric constants work for every slice datum; the background and covariance are evaluated at that datum.

Proof route, with the only new Lean bridges named explicitly:

1. From $e\in V$, obtain `XiCData D` by `physSΛ`; use `isDecBg_one_of_xiCData`, `c7≤thm73C3`, `thm73C3_le_thm73C2` for `hD2`. This is **PROVED CONDITIONAL ON** landed theorems and the shared `FlCore`.
2. Apply `hreal_level` with $R=2$ to every $D$: `tower_core_rates` provides its $2\mathrm{compC4}\mathrm{bgK1}\mathrm{xiC1}t+10t\le\mathrm{bgC1}$ margin. This is **PROVED CONDITIONAL ON** the tower instance.
3. Use `exists_analytic_shiftUC_chart`, `StepScaleData.ray_margin/fl_radius`, and the displayed $r_{\rm cub}$ inequality to obtain `hdisc` via `markedDisc_hdom`. This is **PROVED CONDITIONAL ON** the common-tower parameter/field identification; the short wrapper `markReal_disc_slice` is **OPEN**.
4. For $|t|<t_1$ and real $s\in[0,1]$, choose a complex neighbourhood with $|\zeta|<R_1$. The disc puts $\psi'=\zeta\,\mathrm{liftC}(v_t)$ in `FlBall`; `isLayerConstant_liftC` gives layer constancy. Apply `hreal_level` and its line bound at scalar $1<2$; `dataUC_psiAtV_eq_lineAt` plus `compTangent_dataUC` identifies that line with `dataUC(psiAtV ζ v_t)`. This proves `hdomT` and is the **OPEN** wrapper `markReal_hdomT_of_disc` (no new domain estimate).
5. Instantiate `classRegularLocC_zeroClass` for $S_D$ using $p_1<p^+$ and the same chart constants, then `differentiableAt_Phi1C_of_classRegularLocC`. The needed per-datum application is **OPEN** as `markReal_classRegular_slice` if its `p^+` margin is not already bundled with the physical tower.
6. Apply `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`, then `deriv_Phi1C_marked_eq_E1MarksC_integrand`; rewrite the common finite sum using the first conclusion of `marked_count_scaled`. This final family wrapper is **OPEN** until steps 3–5 and the common $Ev$ are assembled.

The chart-ball and disc estimates alone do not prove `hdomT` or `ClassRegularLocC`; naming these premises prevents a silent appeal to analyticity of the physical functional outside its domain.

## B. Global clamped marks and common labels

`Fluctuation/StepComplexThm31.lean:E1MarksC` abbreviates `InterpMarks S.nuFl BS (S.WoneC C)` with mark function $f(s,x)=\mathrm{fderiv}_{\mathbb C}(S.\mathrm{Phi1C}\,C)((s:\mathbb C)\mathrm{shiftUC}x)(\mathrm{maskUC}_z(\mathrm{shiftUC}x))$.
`Fluctuation/Thm31cde.lean:InterpMarks` has the following five global mark fields:

| Field | Exact quantification and type |
|---|---|
| `meas` | $\forall i,u$, `Measurable (G i u)` on the entire block configuration space. |
| `dep` | $\forall i,u$, `DepOn (blocksOf m₀ K univ (Lab.ysite (y0 i))) (G i u)`. |
| `bound` | $\forall i,u,\Phi$, $\|G(i,u,\Phi)\|\le F_0(i)e^{-\kappa_G\mathrm{Lab.dl}(y_0i)}$, globally. |
| `holG` | $\forall i,\Phi$, `DifferentiableOn ℂ (fun u => G i u Φ) 𝒰`. |
| `hF` | $\forall s\in[0,1]$, almost every physical $x$: $f(s,x)=\sum_iG(i,(s:\mathbb C),BS.\mathrm{restr}\,x)$. |

`Fluctuation/Thm31CoeffAnalytic.lean:ParamMarkFamily` takes $G:E\to\iota\to\mathbb C\to\mathrm{Config}\to\mathbb C$ and replaces `holG` by $\forall i,\Phi\in Q$, `AnalyticOnNhd ℂ (fun p:E×ℂ => G p.1 i p.2 Φ) (V×𝒰)`; it adds `contG`: $\forall i,\theta\in V,u\in\mathcal U$, `ContinuousOn (G θ i u) Q`.
Its `meas` and `bound` are still global in $\theta,i,u,\Phi$; it has no `dep` or `hF` field.
`Fluctuation/ParamActivitySubspace.lean:paramMarkFamilyOn_of_marks` asks for precisely these `hGmeas`, `hGbound`, `hGhol`, `hGcont` inputs and supplies the activity, open-set, compact-carrier, and carried fields; it does not construct the marks.

Construct one root output $\mathcal R_{z,Y'}(e,u,\psi_h)$ from the cubic `markedOut` of a **single common** $Ev$; let $\psi_h=S.\mathrm{hatOf}(m_0,\rho,h_p,\Phi)$ and set
$$G_{z,Y'}(e,u,\Phi)=\begin{cases}-\beta\,\mathcal R_{z,Y'}(e,u,\psi_h),&e\in V,\ |u|<R_\sigma,\\0,&\text{otherwise.}\end{cases}$$
Use the **one** matrix $M(\Theta)$ of `Fluctuation/MarkedCubicJoint.lean:exists_analytic_hatCovSqrt_bdd` to define the unit tangent $Q(\Theta,\psi_h)=\beta_k^{-1/2}M(\Theta)\psi_h$ for every datum and hat field; its chart-wide bound and `analyticOnNhd_smul_mulVec` avoid choosing a separate, potentially discontinuous $Q$ for each $\Phi$.
Take $\rho=p_1>0$ and $c_\psi'=2p_1$. The `StepScaleData` ray margin implies $c_\psi'<\mathrm{lvCpsi}$ and, for $r=r_{\rm cub}$, $(R_1+r)(R_\sigma+t_1)\mathrm{markedRad}(c_\psi')<\delta_1$: indeed $(17/16+\mathrm{lvR}/4)(9/8)\cdot2\le4+\mathrm{lvR}$. This reserves an open radial neighbourhood around every clamped hat value, including $|\psi_h|=\rho$.
**PROVED:** `HatLabelsDep.lean:StepSetting.hatOf_mem`, `measurable_hatOf`, `hatOf_restr` give the uniform clamp, measurability, and almost-everywhere physical identification (`HatLabelsTerms.lean:ae_hatOf_restr`); `ParamActivityPhysical.lean:StepSetting.continuous_hatOf` proves continuity of $\Phi\mapsto\psi_h$.
For `meas`, compose a measurable/continuous root-output map on the closed hat disk with `measurable_hatOf`, then split on the parameter predicate; **OPEN** is that root-output map for the actual cubic `Ev`.
For `dep`, use `PhysicalTerms.lean:StepSetting.agHatFDir_hatOf` to turn agreement of block configurations on `blocksOf(Y')` into agreement of clamped hats on the root output's read set; **OPEN** is the rooted output's exact `AgHatFDir` locality after the bridge sum.
For `bound`, `MarkedCubicJoint.lean:norm_deriv_markedBlockTerm_field_le` gives $3E_*e^{-2\kappa_{dec}d(Y)}/(r^3t_0)$ for arbitrary bounded unit field, and `marked_count_scaled` gives the rooted fibre factor. **OPEN** is packaging that count for all clamped $\Phi$ and all $e\in V$, then taking $F_0>0$ at $\kappa_G=2\kappa_{\rm dec}-1$; the zero branch trivially obeys the global bound.
For `holG`, clauses 2–3 of `Fluctuation/MarkedEvJoint.lean:MarkedEvJointPhysV` give joint analytic `evDec` in datum, hat field and marks; clauses 4–5 give its $t$-derivative analytic in `(physV,u)` and jointly with the hat field. `markedCubic_joint_param` separately gives joint datum/$u$/$t$ analyticity and the cubic derivative bound for `markedBlockTerm(Ev)` once an analytic chart field $Q$ is supplied.
**OPEN:** prove that these clauses control the **same rooted cubic output** (or prove `markedBlockTerm` derivative joint/continuous in the free hat variable directly); the present statements do not identify the `evDec` witness with the `Ev` chosen by `marked_count_scaled`.
For `contG`, combine that free-hat continuity with `continuous_hatOf`; `MarkedEvJointPhysV` clause 5 provides the pattern for derivative continuity but not by itself the cubic witness identification. The strict $c_\psi'>\rho$ margin supports the boundary points of the clamped disk.
**PROVED:** zero extension outside $V×\mathcal U$ is compatible with the types: `InterpMarks.holG` only tests $u\in\mathcal U$, `ParamMarkFamily.holG` only tests $V×\mathcal U$, and `contG` only tests $\theta\in V,u\in\mathcal U$; none asks continuity across the artificial boundary. Global `meas` and `bound` are handled branchwise.
`physV` need not be ambient open in `RawData`: `ParamActivitySubspace.lean:isOpen_physV` proves openness in the finite-dimensional complex `physParam` subspace, and `AnalyticOnNhd` is evaluated there at points of $V×\mathcal U$.

For all roots simultaneously use $\mathrm{Lab}^{\rm all}=\mathrm{Lab}^{\rm act}.\mathrm{sum}(\mathrm{rootUnionLabels}(h_N,h_L,\mathrm{reads},\mathrm{dom},h_{\rm dom}))$, with root index $z$ and bridge label $Y'\in\mathrm{bridgeFamily}(z)$; the root mark anchor is `Sum.inr (rootUnionIncl reads dom z Y')`.
Set activities on the new labels to zero by `Polymer/LabelRootUnion.lean:LabelAct.extendRootUnion`; `extendRootUnion_total` and `extendRootUnion_hW_interp` preserve the activity sum and `hW`, and `rootUnion_marks_fields` transports `dep` and `bound` for each root.
**PROVED CONDITIONAL ON** $L^{m_0}\mid N_1$, $2\le L$, `IsDj` of every old domain, $\varepsilon_H\ge0$, and $\kappa_0\ge a_{\rm Ent}(d,L)+2$: `LabelRootUnion.lean:rootUnion_entropy` proves, for each block $b$,
$$\sum_{y\in\mathrm{RootUnionLb}}\mathbf1\{\mathrm{box}(b)\subset\mathrm{ysite}(y)\}e^{-\kappa_0\mathrm{dl}(y)}\le\mathrm{rootUnionK}=c_1(d,L)L^{d(m_0+m_1)}K_0(d,L,\kappa_0-1).$$
Thus the enlarged activity entropy constant is $K_c+\mathrm{rootUnionK}$. `Polymer/LabelExtend.lean:cubeLabels` adds single-cube labels only if a separate block mark needs them; they are unnecessary for these rooted bridge marks.
**OPEN numeric integration:** `InterpMarks.hKc` and `hε` must be checked with the enlarged $K_c'=K_c+\mathrm{rootUnionK}$, in particular $\varepsilon_H\le[8(K_c')^3c_1\exp((\kappa_H-2\kappa_0)c_G+c_1+\kappa'c_G)]^{-1}$.
The older proposed choice $\kappa_0=a_{\rm Ent}+1$ is **REFUTED** for `rootUnion_entropy`, whose hypothesis is $\kappa_0\ge a_{\rm Ent}+2$; choose this larger $\kappa_0$ before the tower and then verify the rate and $\varepsilon_H$ margins with the new $K_c'$.
**REFUTED:** using a different label type or activity family for each root in the one `ParamMarkFamily`; its `Lab` and $A$ fields are shared before the root is chosen.

## C. Ordered Lean leaves (proposed names; none is a landed citation)

| Order | Exact target and landed inputs | Size / assignment / start |
|---|---|---|
| 1 | `markReal_hdomT_of_disc`: for a fixed $S_D$, `hreal_level`, `hdisc`, $R>1$, layer constancy and `dataUC_psiAtV_eq_lineAt` imply the exact `hdomT` field of `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`. | 120–220; strong; start now. |
| 2 | `markReal_disc_slice`: for every $D$ in the constant-$h_0$ slice and $\|x\|\le p_1$, choose $Y_0=\mathrm{markedRad}(p_1)$ and prove `hdisc` with $R_1=R_\sigma=17/16$, $t_1=1/16$, $r=r_{\rm cub}$ from `StepScaleData.ray_margin/fl_radius`, `markedDisc_hdom`, and `exists_analytic_shiftUC_chart`. | 130–220; strong; start now with shared-tower hypotheses. |
| 3 | `markReal_classRegular_slice`: instantiate `classRegularLocC_zeroClass` for every $S_D$ and infer the exact ambient `DifferentiableAt` by `differentiableAt_Phi1C_of_classRegularLocC`; expose $p_1<p^+$ and every numerical premise. | 120–200; strong; start now. |
| 4 | `markReal_slice`: package steps 1–3, `hreal_level`, `physV` chart inclusion, `marked_count_scaled`'s common $Ev$, both marked derivative lemmas, and the displayed identity, uniformly over the slice. | 160–260; strong; after 1–3 and W422's common family. |
| 5 | `markedRoot_freeHat`: for the **same** $Ev$ as W422's rooted output, show analytic/continuous dependence on a free hat field on the closed $\rho$ disk using `MarkedEvJointPhysV` where witnesses coincide, or a direct Cauchy argument from `markedCubic_joint_param`; prove measurable root output and exact `AgHatFDir` locality. Split analytic, continuity, locality if needed. | 180–280 each; strong; start direct generic lemmas now; witness matching waits for W422. |
| 6 | `markedGlobalFields_zero`: define the displayed clamp/extension and discharge `InterpMarks.meas/dep/bound/holG` and `ParamMarkFamily.meas/bound/holG/contG`, with the common $F_0$ and positive fixed $t_0$; use `hatOf_mem`, `measurable_hatOf`, `continuous_hatOf`, `ae_hatOf_restr`, `rootUnion_marks_fields`. | 220–290, split if needed; strong; start clamp/zero-extension wrappers now; root clauses wait for 5 and W422. |
| 7 | `markedCommonLabels_zero`: use `rootUnionLabels`, `extendRootUnion`, `rootUnion_entropy`, and `extendRootUnion_hW_interp` for one shared activity system and all roots; enforce $\kappa_0\ge a_{\rm Ent}+2$, $K_c'=K_c+\mathrm{rootUnionK}$, and the strengthened `hε`. | 140–230; strong; start now with numeric inequalities explicit. |
| 8 | `e1MarksC_zeroClass_family`: call `paramMarkFamilyOn_of_marks`, prove `InterpMarks.hF` on the physical slice via `markReal_slice` and W422's rooted finite sum, and construct `E1MarksC (S.withDatum D hD) zeroClass BS z` for each root with the **same** $BS,Lab,A,V,\mathcal U,Q$. | 180–280; strong; after 4–7, W422, and the source-free activity equality for `WoneC`. |

**Open boundary.** The landed results establish the fixed-datum cubic count, relative chart, analytic shift family, clamp, and common rooted label mechanism. The uniform line-domain wrapper, per-datum regularity wrapper, free-hat rooted cubic continuity/locality, and final physical `hF` assembly remain **OPEN**. Confidence is high for the typed premises and common-label choice; medium for the proposed `hdomT` proof until its line-at equality is checked in Lean; medium-low for the free-hat witness comparison.
