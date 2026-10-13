# MARKPARAM: a common analytic family of rooted cubic marks

13 October 2026. The tree `/home/scott/Balaban` was read only. **PROVED** denotes a landed statement or the displayed deduction; **PROVED CONDITIONAL ON** lists extra inputs; **OPEN** denotes a physical assertion still missing; **REFUTED** denotes an invalid implication. This audits STEPOUT packages 3–5 at the zero class and the notes `MARKASM.md`, `MARKCUBIC.md`, `MARKS.md`, `STEPOUT.md` and `SRCACT.md`.

## Exact consumer records

`StepComplexThm31.E1MarksC S C BS z` is exactly `InterpMarks S.nuFl BS (S.WoneC C) (fun s x => (fderiv ℂ (S.Phi1C C) ((s : ℂ) • S.shiftUC x)) (S.maskUC z (S.shiftUC x)))`. Its full record in `Thm31cde.lean` is:

```lean
structure InterpMarks (ν : Measure X) {m₀ : ℕ} (BS : ProdSplit ν d L N₁ m₁ K m₀)
    (W : ℝ → X → ℂ) (f : ℝ → X → ℂ) where
  Lb : Type
  [fin : Fintype Lb]
  Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ K Set.univ Lb
  ι : Type
  [finι : Fintype ι]
  nonempty : Nonempty ι
  εH : ℝ
  κH : ℝ
  κG : ℝ
  κ0 : ℝ
  κ' : ℝ
  Kc : ℝ
  F0 : ι → ℝ
  hN : L ^ m₀ ∣ N₁
  𝒰 : Set ℂ
  isOpen : IsOpen 𝒰
  seg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰
  A : ℂ → LabelAct Lab BS.Ωb εH κH κ0 Kc
  y0 : ι → Lb
  G : ι → ℂ → (∀ b, BS.Ωb b) → ℂ
  meas : ∀ i u, Measurable (G i u)
  dep : ∀ i u, DepOn (blocksOf m₀ K Set.univ (Lab.ysite (y0 i))) (G i u)
  bound : ∀ i u Φ, ‖G i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i))
  holA : ∀ y Φ, DifferentiableOn ℂ (fun u => (A u).H y Φ) 𝒰
  holG : ∀ i Φ, DifferentiableOn ℂ (fun u => G i u Φ) 𝒰
  hκ0 : aEnt d L + 1 ≤ κ0
  hKc : K0 d L κ0 + 1 ≤ Kc
  hεpos : 0 < εH
  hF0 : ∀ i, 0 < F0 i
  hκ' : 0 ≤ κ'
  hκG : κH ≤ κG
  hκ : κ' + 3 * κ0 + c1 d L + 3 / 2 ≤ κH
  hε : εH ≤ 1 / (8 * Kc ^ 3 * c1 d L *
    Real.exp ((κH - 2 * κ0) * cG d L + c1 d L + κ' * cG d L))
  hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    W s x = ∑ y, (A (s : ℂ)).H y (BS.restr x)
  hF : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
    f s x = ∑ i, G i (s : ℂ) (BS.restr x)
```

`Thm31CoeffAnalytic.ParamMarkFamily` has the following complete field list; here $E$ is a finite-dimensional complex parameter space when its coefficient theorem is applied, $V\subset E$, $\mathcal U\subset\mathbb C$, and $Q$ is the configuration carrier:

```lean
structure ParamMarkFamily {Ωb : 𝔅 → Type*} [∀ b, MeasurableSpace (Ωb b)]
    [∀ b, TopologicalSpace (Ωb b)] (μ : ∀ b, Measure (Ωb b)) [∀ b, IsProbabilityMeasure (μ b)]
    (Lab : CubeLabels m₀ j Ω Lb) {εH κH κ0 Kc : ℝ}
    (A : E → ℂ → LabelAct Lab Ωb εH κH κ0 Kc) (y0 : ι → Lb)
    (G : E → ι → ℂ → (∀ b, Ωb b) → ℂ) (κG : ℝ) (F0 : ι → ℝ)
    (V : Set E) (𝒰 : Set ℂ) (Q : Set (∀ b, Ωb b)) : Prop where
  isOpenV : IsOpen V
  isOpenU : IsOpen 𝒰
  seg : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → (s : ℂ) ∈ 𝒰
  compact : IsCompact Q
  measQ : MeasurableSet Q
  carried : ∀ᵐ Φ ∂(Measure.pi μ), Φ ∈ Q
  meas : ∀ θ i u, Measurable (G θ i u)
  bound : ∀ θ i u Φ, ‖G θ i u Φ‖ ≤ F0 i * Real.exp (-κG * Lab.dl (y0 i))
  holA : ∀ y, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => (A p.1 p.2).H y Φ) (V ×ˢ 𝒰)
  holG : ∀ i, ∀ Φ ∈ Q, AnalyticOnNhd ℂ (fun p : E × ℂ => G p.1 i p.2 Φ) (V ×ˢ 𝒰)
  contA : ∀ y, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn ((A θ u).H y) Q
  contG : ∀ i, ∀ θ ∈ V, ∀ u ∈ 𝒰, ContinuousOn (G θ i u) Q
```

| Fields | Status at current main and exact reuse |
|---|---|
| `Lb`, `fin`, `Lab`, `ι`, `finι`, `nonempty`, `y0`, `hN` | **OPEN** one common enlarged label system and physical mark indices; `MarkedRootGeometry.bridge_isDj_and_le`, `rootCube_mem_blocksOf_bridge` and `fibre_weighted_le` prove geometry under their divisibility hypotheses. Add a dummy zero mark on an `IsDj` domain if the index is empty. |
| `εH`, `κH`, `κ0`, `κ'`, `Kc`, `hκ0`, `hKc`, `hεpos`, `hκ'`, `hκ`, `hε` | **PROVED CONDITIONAL ON** the physical `DirectTerms`/activity numerics and one shared system: `ScaleActivityFinal.stepActivityBound_zeroClass_direct_physical_scale` chooses constants before the scale and bounds `εH`; `ParamActivitySubspace.physical_paramMarkFamily_exists` constructs only zero marks. The actual common energy activity still must be selected. |
| `κG`, `F0`, `hF0`, `hκG` | **OPEN** choose $\kappa_G=a=2\kappa_{dec}-1$ and a positive $F_0$ from the cubic rooted bound, then check $\kappa_H\le a$. The fixed-datum cubic bound is **PROVED CONDITIONAL ON** the hypotheses of `MarkedSharpCount.marked_count_scaled`. |
| `𝒰`, `isOpen`, `seg`; family `isOpenV`, `isOpenU`, `seg`, `compact`, `measQ`, `carried` | **PROVED CONDITIONAL ON** $1<R_\sigma$, the physical cutoff and chart hypotheses: `ParamActivitySubspace.isOpen_physV`, `Inhabited.UniformChartRelative.hatStepK_physV`, `ParamCarrierLocal.isCompact_physCarrier`, and `paramMarkFamilyOn_of_marks` package them. The chart is open in `physParam`, not in full `RawData`. |
| `A`, `hW`, `holA`; family `holA`, `contA` | **PROVED CONDITIONAL ON** a selected physical `DirectTermsFamilyOn` whose real exponent is exactly `S.WoneC C`, plus its numerical hypotheses; `ParamActivitySubspace.paramMarkFamilyOn_of_marks` supplies regularity. Source-dependent `WoneC+WtwoC` labels require a zero-source restriction or a separate exponent matching proof. |
| `G`, `meas`, `dep`, `bound`, `holG`, `hF`; family `meas`, `bound`, `holG`, `contG` | **OPEN** for physical rooted marks. `MarkedVBlockDec.vblock_expansion_hat_marked_scaled` and `MarkedScaledCountDec.marked_count_scaled_dec` give fixed-datum marked clauses; the latter's sum over retained labels still has a vanishing antecedent. `MarkedSharpCount.marked_count_scaled` gives the stronger cubic fixed-datum bound and rooted count; `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` gives the physical derivative sum only under its chart, realization and disc hypotheses. None constructs `ParamMarkFamily.holG`/`contG` or `InterpMarks.hF` for all slice data. |

## Joint analyticity: direct product parameter, then Cauchy

**PROVED entry points.** `MarkedDecAnalytic.analyticOnNhd_markedHatPsiF` and `MarkedFanAnalytic.fanH_analytic_marked` already treat data, hat field, cuts and both marks as **one** complex parameter. `MarkedFanLocal.fanHL_local_marked_radius` supplies the fixed-mark comparison. `Localization.I5Expansion.localization_expansion` already assumes analyticity in $(U,s)$ and returns analyticity in all of $U$; `MarkedEvParam.expansion_of_AE_hat_dir_exposed` is a wrapper with a canonical `evTerm`. Thus no theorem about separate analyticity of an arbitrary function is needed at the AE stage.

**OPEN exact joint lemma (`evDec_joint_physV`).** Fix the `F₁,Sol` witnesses and $W=\{(u,t):(|u|+|t|)\,	exttt{markedRad}<\delta_1\}$, and put $U_0=\texttt{XiCRaw}\times B_{hat}$. For each block $b$ and polymer $Y$, prove
$$\operatorname{AnalyticOnNhd}_{\mathbb C}\big((q,w)\mapsto\texttt{evDec}(b,Y,w.1,w.2,q),\ U_0\times W\big).\tag{J}$$
Apply `localization_expansion` to $F((q,w),s)=\texttt{FFmarked}(q,s,w)$, with $U=U_0\times W$ and agreement `Ag C` requiring equal marks and `AgHatDir` on the original component. `fanH_analytic_marked` supplies joint $(q,s,w)$ analyticity; the closed-bidisc estimate of `MarkedBlockExpansionDec` supplies its uniform bound; `fanHL_local_marked_radius` supplies `LocalityAEOn` when marks agree. The coefficient is the **same** `evTerm` as in `MarkedVBlockDec`, by unfolding `evDec`/`FFmarked`; this avoids selecting a new family at each mark. `localization_expansion` performs finite cut-coefficient sums and proves (J), then `physIncl` composes (J) onto the relatively open `physV`. This is **PROVED CONDITIONAL ON** the displayed `FlCore`, cover, strict marked-disc, localization and chart hypotheses; the combined instantiation (J) is **OPEN** in Lean.

**PROVED alternative for the needed derivative.** `Polymer.MarkedHoloParam.analyticOnNhd_deriv_zero` states: on an open finite-dimensional complex $V$, if $f(q,t)$ is analytic in $q$ for each $|t|<r$, differentiable in $t$ for each $q$, and uniformly bounded by $M$, then $q\mapsto\partial_t f(q,0)$ is analytic. Use $q=(e,u)\in\texttt{physV}\times B(0,R_\sigma)$ and $f(q,t)=R_{z,Y}(e,u,t,\Phi)$ on one fixed $t$-disc. The lemma proves the precise `ParamMarkFamily.holG` field after the coefficient and cubic constructions; (J) supplies its fixed-$t$ hypothesis. Its proof uses Cauchy's $t$-circle and `continuousOn_prod_of_analytic_bdd`. For `contG`, use the same circle with $R_{z,Y}$ continuous in $\Phi$ on `physCarrier`, uniformly bounded there; Cauchy's integral is then continuous in $\Phi$. Measurability on **all** configurations needs the explicit clamped formula or a measurable extension, not merely continuity on `physCarrier`.

**REFUTED shortcut.** Continuity in the datum plus holomorphy in the marks does not imply `ParamMarkFamily.holG`: $G(e,u)=\overline e$ is continuous in $e$ and entire in $u$, but is not holomorphic in $(e,u)$. Separate holomorphy on a complex open product with local bounds would suffice analytically, but no landed Hartogs/Osgood theorem for this exact relative chart was found; (J) gives a direct proof. `physParam=rawSub\times\text{sources}` is a finite-dimensional **complex** subspace, so `physV` is an ordinary open set in that space. The `StepSetting.withDatum` identity holds only where $h\equiv h_0$; `MarkedTangent.exists_analytic_markedTangentC` and `exists_analytic_markedTangentC_physV` give an ambient analytic extension, but physical `hF` must be asserted on the constant-$h_0$ slice unless a varying-$h$ step theorem is proved.

## Cubic marked chain and constants

Let $E_* =\texttt{energyBdScaled}\ d\ L\ N\ (\texttt{compWeight}\ L\ a_1)\ k\ (\texttt{cK2'}\,\delta_1)\ \delta_1\ \rho_4$ with the exact `cK2'`/`famConst` and `rho4` arguments of `SharpAssemblyScaled`; $M=L^{m_0+m_1}$, $a=2\kappa_{dec}-1$, $c_{Br}=\texttt{cBr}\,d\,L=2dL^{d+1}$, and $n_F=\texttt{nFibre}\,d\,L=2^{L^{2d}}$. Choose $1<R_1$, $r>0$, $0<t_0<t_1$, and the strict radial inclusion $(R_1+r)(R_\sigma+t_1)Y_0<\delta_1$ for every datum in the family. The marks act **after** the covariance square root: $v_t=u\psi'+tM_z\psi'$.

| Unmarked chain and required marked statement | Analytic step and bound | Status |
|---|---|---|
| `SharpAssemblyScaled.vblock_locInt_hat_dir_scaled`: replace its `hatFun`/`Ev` by one marked block coefficient $E_{b,Y}(\Theta,u,t)$, with one family of original $Y$, sharp `AgHatDir` at equal marks, and analytic dependence on $(\Theta,u,t)$ on `physV×W`. | `MarkedVBlockDec.vblock_expansion_hat_marked_scaled` proves sum, fixed-mark locality, closed-bidisc bound $E_*e^{-2\kappa_{dec}d(Y)}$, mark analyticity at fixed data and Cauchy in $t$; (J) supplies missing joint output. For the cubic version, `InteractionVBlockScaled.vblock_expansion_scaled` has $E_{b,Y}(\Theta,v)$ jointly analytic in datum and general tangent. | **PROVED CONDITIONAL ON** fixed block hypotheses; **OPEN** joint marked packaging. |
| `SharpAssemblyScaled.vpart_locInt_hat_dir_dm_scaled`: take the third radial derivative of each $E_{b,Y}$ at $\sigma v_t$, integrate $\omega(s)=(1-s)^2/2$, retain the same label for $v_t$ and $v_0$, and sum over old blocks. | `MarkedCubicTaylor.analyticOnNhd_markedBlockTerm` proves $t$ analyticity at fixed datum; `norm_deriv_markedBlockTerm_taylorWeight_le` proves $3E_*e^{-2\kappa_{dec}d(Y)}/(r^3t_0)$. Joint $\Theta,u,t$ follows from the analytic general-tangent coefficient and the analytic marked tangent (`exists_analytic_liftC_markedTangentC`) by composition and differentiation under the compact $s$ integral, with the common strict radial disc. | **PROVED CONDITIONAL ON** the common chart/disc and general-tangent expansion; **OPEN** family lemma in Lean. |
| `SharpAssemblyScaled.hat_vpart_bound_dm_dir_scaled`: count contributing old blocks, absorb $(1+d(Y))$, bridge each $Y$ to the root and sum its finite fibre; differentiate the physical zero-class cubic identity. | `MarkedSharpCount.marked_count_scaled` already gives the rooted fixed-datum count and bound. The old-block factor is $c_1(d,L)M^d(1+d(Y))$; $(1+d)e^{-2\kappa_{dec}d}\le e^{-a d}$; `fibre_weighted_le` adds $n_Fe^{a c_{Br}}$. `MarkedCubicTaylor.VkC_marked_eq_block_terms` and `MarkedSharpCount.hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom` give the finite derivative identity under `MARK-REAL` and marked disc hypotheses. | **PROVED CONDITIONAL ON** those hypotheses at fixed datum; **OPEN** uniform family and full `hF`. |

The resulting *mark of* $\Phi_1^\mathbb C=-\beta V_k^\mathbb C$ has, per rooted output label $Y'$, the exact proposed bound
$$\|G_{z,Y'}(e,u,\Phi)\|\le F_*e^{-a d(Y')},\quad F_*={3\beta\|E_*\|\over r^3t_0}\,c_1(d,L)M^d\,n_F e^{a c_{Br}}.\tag{B}$$
The factor $3/r^3$ is $6/r^3$ times the Taylor weight bound $1/2$. There is **no extra factor two** for the $t$ derivative of $P(v_t)-P(v_0)$, since $P(v_0)$ is constant in $t$; `norm_deriv_markedBlockTerm_taylorWeight_le` proves precisely this. Multiplication by $\beta$ occurs after the cubic block count. `MarkedScaledCountDec.marked_count_scaled_dec` instead yields $E_*/t_0$ before multiplying by $\beta$; its bound alone loses the cubic $r^{-3}$ gain and its retained-label identity assumes `hzero`.

At $d=L=3$, $b=\beta_k=\beta3^k$, $p_1=A_1(\log b)^p$ and the physical choice of $r$, the numerical premise used in `SRCACT.md` gives $\beta\|E_*\|\le b\,C_{E,*}$ and $b/r^3\le(4A_1/\kappa_1)^3(\log b)^{3p}/\sqrt b$. Thus (B) is bounded by $[n_Fe^{a c_{Br}}/t_0]P(4A_1/\kappa_1)^3(\log b)^{3p}/\sqrt b$, where $P$ is the explicit $3c_1M^d$ energy constant of `SRCACT.md` §Complex chart. The activity prefactor there is $C_E=4[P(4A_1/\kappa_1)^3+1]$; $F_*$ has the additional fixed root/fibre and $t_0^{-1}$ costs. **OPEN** is the common choice of $t_0$ and all strict discs before $k,N_1,\nu,\beta$; if $t_0$ shrinks with $b$, the claimed $O((\log b)^{3p}/\sqrt b)$ mark bound does not follow.

## Exact physical targets and ordered leaves

The quantifier template is **OPEN for marks**: for each $A_1>0,p$, with $\kappa_0=aEnt(3,3)+1$, $\kappa_{dec}=100(\kappa_0+c_1(3,3)+10)$ and $\kappa'=\tfrac32\kappa_{dec}+\kappa_0+1$, choose $m_1,t,\delta,\beta_0,C_M,t_0,R_\sigma,R_1$ and a fixed coefficient defining the scale-dependent radial radius $r$ **before** $k\ge1$, $3\mid N_1>5$, $0<\nu$, $\nu3^{2(k+1)}\le1$, and $\beta\ge\beta_0$. Then for $S=\texttt{hatStepK}$, $C=\texttt{zeroClass}$ and $V=\texttt{physV}\,S\,1\,\nu\,t$, construct one split $BS=S.blockSplit\,m_0$, a common finite label activity $A$ with `hW` for `S.WoneC C`, and for every root $z$ a family $G_z$, index $\iota_z$, anchor $y_{0,z}$, and an `E1MarksC S C BS z` whose `hF` is the physical masked derivative. The same $A,BS,V,\mathcal U,Q$ must serve every $z$. The fixed-datum activity theorem `stepActivityBound_zeroClass_direct_physical_scale` has exactly the stated outer order but does not yield these marks.

**OPEN proposed `markedRootAssembly_zero`.** Under the fixed constants, a common `Ev`, the strict chart, `MARK-REAL` on every marked disc, the selected `DirectTermsFamilyOn` for `WoneC`, and the exact `marked_count_scaled` cover hypotheses, produce $\mathcal Y_z=\texttt{bridgeFamily}$ and $G_{z,Y'}(e,u,\Phi)=-\beta\,\texttt{markedOut}(z,Y')$ with: finite sum equal to the `E1MarksC` integrand for every real $u\in[0,1]$ and almost every physical $\Phi$ on the constant-$h_0$ slice; the global bound (B) after clamping/zero extension; `DepOn (blocksOf (Lab.ysite Y'))`; $Y'\in\mathcal D_{k+1}$ with `rootCube z ∈ blocksOf Y'` whenever $G\ne0$; `AnalyticOnNhd ℂ (fun (e,u) => G_{z,Y'} e u Φ) (V×B(0,Rσ))` for $\Phi\in Q$; and `ContinuousOn (G_{z,Y'} e u) Q`. The *fixed-datum* bound, root and finite sum are **PROVED CONDITIONAL ON** the hypotheses of `marked_count_scaled` and `hasDerivAt_Phi1C_marked_eq_neg_beta_sum_of_hdom`; family analyticity, configuration continuity, common labels and physical slice matching are **OPEN**.

**OPEN proposed `e1MarksC_zeroClass_family`.** Given that assembly, a common zero-source `DirectTermsFamilyOn` whose `hW` equals `S.WoneC C` at each physical slice, the global activity bounds, and the `InterpMarks` numerical inequalities above, construct `ParamMarkFamily (S.blockSplit m₀ hp).μ Lab A y0 G κG F0 V (ball 0 Rσ) (physCarrier S m₀ hp)` by `ParamActivitySubspace.paramMarkFamilyOn_of_marks`, and for each $z$ and admissible constant-$h_0$ datum construct `E1MarksC (S.withDatum D hD) (zeroClass …) BS z`, with `hF` from the rooted finite identity. Extend the common activity system by zero on added mark labels; prove its entropy bound and `A`/`G` datum locality on `Yhat(sitesOf T)`. `ParamCarrierLocal.paramMarked_analytic_local_bound` then gives analytic, local and bounded `gsumCoeff`; `ParamDatumFamily.thm31aC_coeff` consumes each `E1MarksC` **only after** a determinant input. This assembly is **PROVED CONDITIONAL ON** the named OPEN hypotheses; no physical `E1MarksC` inhabitant was found in current main.

| Leaf, all Z/GN; each at most 300 Lean lines | Exact target and dependency | Assignment/start |
|---|---|---|
| `markedEv_joint_param` | Prove (J) for `evDec` with the same `F₁,Sol`, using `fanH_analytic_marked` and `localization_expansion`; keep mark equality in `Ag`. | strong; start now under explicit `FlCore`/cover hypotheses. |
| `markedCubic_joint_param` | For the common `Ev` of `vblock_expansion_scaled`, prove joint analyticity of $(e,u,t)\mapsto\texttt{markedBlockTerm}(Ev,\omega,v_t(e),e,t)$ on the strict `physV` product disc, and (B)'s per-old-block $3E_*/(r^3t_0)$ derivative bound; use `exists_analytic_liftC_markedTangentC_physV`. | strong; start now with explicit radial margin. |
| `markedRoot_zero_family` | Prove the full `markedRootAssembly_zero` clauses above, including `hzero`/root, the $c_1M^dn_Fe^{ac_{Br}}$ bound, and `hF` on the physical slice; use `marked_count_scaled`, `VkC_marked_eq_block_terms`. | strong; after cubic family and `MARK-REAL` uniformization. |
| `markedGlobalFields_zero` | Define clamped/zero-extended $G$ and prove global `bound`, `meas`, `dep`, `holG`, `contG` exactly as the two record types require, with a fixed $t_0>0$. | strong; start extension and continuity lemmas now. |
| `markedCommonLabels_zero` | Enlarge the unmarked label system with all $\mathcal Y_z$, zero activities on new labels, unchanged `hW`, entropy/DA, nonempty mark index and positive $F_0$; establish a single `BS,Lab,A` for all roots. | Sonnet; start now from geometry, then insert physical families. |
| `e1MarksC_zeroClass_family` | Produce the stated `ParamMarkFamily` and each `E1MarksC` with all record fields, using `paramMarkFamilyOn_of_marks`; preserve outer scale quantifiers and the constant-$h_0$ identity. | strong integration; after preceding leaves and source-free activity match. |

**Report on tension.** `MarkedFanAnalytic.fanH_analytic_marked` already proves joint fan analyticity, so older notes calling all of MARK-AN open are stale; the coefficient-level product theorem (J) remains open. `marked_count_scaled_dec` is correctly stated with its `hzero` antecedent, so its full derivative identity cannot be cited without that proof. `MarkedSharpCount.marked_count_scaled` gives a separate fixed-datum cubic route with the required $r^{-3}$ and root factor, but does not give family `holG`/`contG`. The factor two in `MARKASM.md`/`MARKCUBIC.md` is a valid coarse bound for a difference's *value*, yet the derivative of its constant second term is zero, as the landed `norm_deriv_markedBlockTerm_taylorWeight_le` confirms. `ParamMarkFamily.bound` and `InterpMarks.bound` quantify over every parameter/configuration, so a carrier-only Cauchy estimate needs the clamp and explicit extension. Finally, an activity expansion for `WoneC+WtwoC` cannot satisfy `E1MarksC.hW` for `WoneC` without an equality or zero-source restriction.
