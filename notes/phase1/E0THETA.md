# The new step terms under the renormalization map

**Scope and status.** This note treats the physical new energy and observable needed for the `expE0` and `expM0` fields of `RenormExpInput`. “PROVED” means a cited declaration is landed, or the displayed algebra follows from its definition. “PROVED CONDITIONAL ON” names a landed implication whose hypotheses remain to be supplied. “OPEN” names a missing mathematical or Lean assertion. “REFUTED” marks a proposed identification contradicted by the source definitions. No full physical `RenormExpInput` is claimed.

## 1. Physical functions and their parameters

**PROVED (source identification).** In P4, printed pp. 694–695, (2.52)–(2.60), the step creates the observable $\mathcal M_0^{(k+1)}(x;g)$ and the energy $\mathcal E_0^{(k+1)}=\frac12\log\det C^{(k)}+\mathcal E_1^{(k+1)}$; the rooted energy is the block trace plus $\mathcal E_1^{(k+1)}(z)$. These are represented in `Fluctuation/StepComplexOut.lean` by `StepSetting.M0C`, `E0C`, and `E0locC`. `StepSetting.E0locC` is $-\frac12\sum_{y\in B(z),i}\log A_C(y,i)(y,i)+E1locC(z)$.

**PROVED (source identification).** P4, printed p. 704, (4.17)–(4.18), evaluates those *already produced* new terms at $z_{k+1}\psi_{k+1}$, and multiplies the new observable by $\beta_k^{-1/2}$. P6, §2, (2.8)–(2.9), applies the same scaling before retaining the new energy terms on $Z_{k+1}^c$. In the present variables put $\zeta(\xi)=\mathrm{renZeta}(\varepsilon,\xi)=\varepsilon\xi_0$ and $\theta(D,\xi)=((1+\zeta(\xi))D.\Psi,D.h)$. Thus, for the fixed step family $S$ and fixed source $g$,
$$E_{0,\theta}(z,D,\xi)=E^{S}_{0,\mathrm{loc}}(z;\theta(D,\xi)),\qquad M_{0,\theta}(p,D,\xi;g)=\beta_k^{-1/2}M^{S}_{0}(g,p;\theta(D,\xi)).$$
Only $\Psi$ is rescaled; $h$ and $g$ are unchanged. The energy for the whole torus is $\sum_zE_{0,\theta}(z,D,\xi)$, while `RenormExpInput.E0θ` is *rooted*, indexed by $z$.

**PROVED (source and code); REFUTED (mass substitution).** P4 (4.17)–(4.18) has no $\nu_u$ argument in the new step terms. The mass $\nu_u=\mathrm{renMassU}(\nu,\xi)=\nu(1+\xi_1)/(1+\xi_2)$ changes the unrenormalized variational equation and the separate $C_2$ correction in P4 (4.14)–(4.15); `Fluctuation/RenormExpG.lean:RenormExpInput.locC2` passes `renMassU ν ξ` to `renC2On`, while `StepSetting` has one fixed real `ν` (`StepObjects.lean`). Replacing `S.ν` by $\nu_u$ inside `E0C` or `M0C` is not the composition in (4.17)–(4.18), and is not supported by the landed fixed-step definitions. The mass dependence of the *older* terms is handled by their own renormalization differences.

**OPEN (source parameter).** P4's $\mathcal M_0(x;g)$ depends on $g$; `RenormExpInput.M0θ` has no source binder. It can encode a **fixed $g$ slice** when $g$ is bound outside the record. A theorem for the full H7 family needs a source-parametrized input and joint analyticity in $g$ on the source domain of P4 Proposition 4.2 (printed p. 706); `M0θ p` by itself does not provide that quantifier. It is not valid to silently set $g=0$ and call the resulting function the full observable.

**PROVED (source target); OPEN (Lean bound).** P4 Proposition 4.1, printed p. 706, gives $NL^d B_4+1+C_5 E_0\varepsilon$ for the whole new energy contribution; (4.24) then uses $C_5E_0\varepsilon\le1$. Proposition 4.2 gives the observable constant $\frac12\beta_k^{-1/4}+C_6\varepsilon L^{(k+1)(2\gamma-\alpha_1)}$. Those are physical targets after marked terms and fibres are summed, not constants proved by the determinant record alone.

## 2. Exact input type and the chart obstruction

**PROVED.** The two parameters of `RenormExpInput` in `Fluctuation/RenormExpG.lean` have these exact types (with its implicit $G,N,\iota$):
```lean
(E0θ oldE : ι → BgData G N → (Fin 3 → ℂ) → ℂ)
(M0θ oldM : G.Ω 1 × Fin N → BgData G N → (Fin 3 → ℂ) → ℂ)
expE0 : ∀ z, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀
  (Ys z) dY κa BE0 (E0θ z) term
expM0 : ∀ p, ∃ term, IsLocExp (N := N) G (XiCOneReal G a ν ε) r₀
  (YsM p) dY κb BM0 (M0θ p) term
```
`Fluctuation/RenormExpCauchy.lean:expDom` is the set of $((D.\Psi,D.h),\xi)$ with $D\in\mathrm{XiCOneReal}(G,a,\nu,\varepsilon)$ and $\|\xi\|<r_0$. `IsLocExp` requires, for every such $D,\xi$, a sum over the finite `Ys z` or `YsM p`; for each $Y$ in that finset, `AnalyticOnNhd ℂ (term Y)` on `expDom`, the `RawAgree Y` locality law at equal $\xi$, and $\|\mathrm{term}_Y\|\le B e^{-\kappa dY(Y)}$. `RawAgree` checks both raw components at every site of $Y$. The root covers from `Fluctuation/RenormLocFibre.lean` are `renYs`; their size `renDY G m₀ Y` is `treeLenCov G m₀ (↑Y)`.

**PROVED.** `XiCOneReal G a ν ε D` gives a real center $(\Psi_0,h_0)$ and complex spin displacement $\Psi''$, with zero external displacement, satisfying `XiC G a ν K 1 ε` when $G$ has top level $K$. `XiCOneReal.xiCOne` supplies the same witnesses to `XiCOne`; `Localization/I5Chain.lean:XiCData` has the identical existential predicate with $n=K,\sigma=1$. Consequently, at the shared tower step $G=S.G'$ and $K=k+1$, $D$ itself belongs to `XiCData S.G' S.a S.ν (k+1) 1 ε`, hence its raw data belong to `XiCRaw` at that radius. The datum $\theta(D,0)$ equals $D$.

The complete proof of this base case, after fixing $G=S.G'$ and unfolding the two predicates, is:
```lean
theorem renTheta_zero_chart (D : BgData S.G' N)
    (hD : XiCOneReal S.G' S.a S.ν ε D) :
    XiCData S.G' S.a S.ν (k + 1) 1 ε D := by
  exact hD.xiCOne
```

**OPEN (`renE0_theta_domain`).** The useful theorem has the following exact conclusion and quantifiers, after defining `renThetaDatum` by scaling $D.\Psi$ and retaining $D.h$:
```lean
theorem renE0_theta_domain (S : StepSetting d L N₁ m₁ k N ϱ)
    (εren εstep r₀ : ℝ) (hΞ2 : ThetaChartMargin S εren εstep r₀)
    (D : BgData S.G' N) (hD : XiCOneReal S.G' S.a S.ν εren D)
    (ξ : Fin 3 → ℂ) (hξ : ‖ξ‖ < r₀) :
    XiCData S.G' S.a S.ν (k + 1) 1 εstep
      (renThetaDatum εren D ξ)
```
`ThetaChartMargin` is a proposed explicit record of the smallness and class enlargement required by P4 (4.19), **not a landed declaration**. Its proof must include the real-center inequalities, complex background differences, and `InUnionDomainC` in `SmallField/Xi.lean:XiC`; a bare inequality $\varepsilon_{\rm step}>\varepsilon_{\rm ren}$ is not its definition. At $\xi=0$ the conclusion with $\varepsilon_{\rm step}=\varepsilon_{\rm ren}$ follows directly from `XiCOneReal.xiCOne` by unfolding `XiCOne` and `XiCData`; this is the proved base case. For nonzero $\xi$, `XiCOneReal.xiCOne` alone says nothing about the scaled datum. P4 (4.19) uses an enlarged unrenormalized radius $\varepsilon_{j,u}$; the determinant tower theorem below is stated at radius `T.t`, with no such enlargement. This radius mismatch is **OPEN**, not hidden by `withDatum`.

**PROVED.** Scaling preserves the raw-data submodule: `Localization/XiCRawOpen.lean:rawSub` is a complex submodule, and `rawOf_mem_rawSub`, `bgOfRaw`, `rawOf_bgOfRaw` give the datum constructor. Hence `renThetaDatum` is an elementary new definition, with a one-page proof of raw-submodule membership; it does not establish `XiCData` membership. `renMassU_sub_norm_le` in `RenormExpLemma35.lean` gives $|\nu_u-\nu|\le(32/15)\nu\|\xi\|$ when $\nu\ge0,\|\xi\|\le1/16$; this controls $C_2$, not the fixed-step `E0θ` chart.

**OPEN (step family domain).** `StepSetting.withDatum` in `StepComplexAnalytic.lean` takes a proof $\forall x,i, D.h(x,i)=S.h_0(i)$, so it cannot vary over every `XiCOneReal` datum, whose real $h_0$ can vary. `Fluctuation/DetGroupedAnalytic.lean:detGrouped_chart_family_fromTower` does vary the determinant with the chart datum, but no corresponding full marked energy and observable family on the entire `XiCOneReal` domain is landed. `physV` in `ParamActivitySubspace.lean` is a relative open chart for a fixed step and fixed real $\nu$, not a replacement for the missing $\theta$ inclusion.

## 3. Joint analyticity and determinant-first regrouping

**PROVED (elementary map).** On the ambient `rawSub × (Fin 3 → ℂ)`, $((\Psi,h),\xi)\mapsto((1+\varepsilon\xi_0)\Psi,h)$ is a polynomial map, hence analytic at every point. The rational $\nu_u$ is analytic for $\|\xi\|<1/16$ because $|1+\xi_2|\ge15/16$; this fact is needed for $C_2$ but not for this step-term composition.

**PROVED CONDITIONAL ON OPEN `renE0_theta_domain` and a full step family.** The composition lemma takes `AnalyticOnNhd ℂ f V`, an analytic map $\Theta$ from the ambient raw-data/parameter product, and $\Theta(q)\in V$ for every $q\in\mathrm{expDom}$. It concludes `AnalyticOnNhd ℂ (f ∘ Θ) (expDom …)`, pointwise by `AnalyticAt.comp`. The determinant theorem supplies `AnalyticOnNhd` on the relative `rawSub` chart and on `physV`, so its ambient target is adequate once the map into that chart is proved. The corresponding ambient family for the full marked $E_1$ and source-dependent $M_0$ is **OPEN**; a bound or sum at a fixed datum does not imply joint analyticity in $\xi$.

**PROVED.** `detGrouped_chart_family_fromTower` (shared `T : StepTower`, $k\ge1$, $3\mid N_1$, $N_1>5$, $\nu\ge0$, $\nu3^{2(k+1)}\le1$) produces one `E z : DetExpansionLocC ... 1 z T.t (towerDetRate T.κ) (towerDetConst T.κ)` for every root. Its `detGrouped` is analytic on the relative `XiCRaw`/`physV`, local on the collar hull $X$, and bounded by $H e^{-\lambda\operatorname{sizeJ}_1(X)}$, where $H=\mathrm{hullConst}(3,3,\mathrm{towerDetRate}(T.\kappa),\mathrm{towerDetConst}(T.\kappa))$ and $\lambda=\mathrm{hullRate}(3,3,\mathrm{towerDetRate}(T.\kappa))$. `DetExpansionLocC.detGrouped_sum` recovers `rootTrace`; `detGrouped_anchor` roots every nonzero hull at the root cube. `RootDetChart.lean:rootTrace_one_eq_logAC` identifies this sum at $D=S.D'$ with the trace part of `S.E0locC`. None of these declarations includes $E1locC$.

**REFUTED (automatic hull-as-$Y$).** The $X$ of `detGrouped` is a collar hull, a **set** of next-scale sites; `renYs c G 1 X₁` consists of finite `Ysites` of connected label families rooted on $X₁$ (`RenormLocFibre.lean:renYs`, `Localization/I5Expansion.lean:polymerDomains`). A hull containing the root cube need not equal such a `Ysites`, and `sizeJ 1 (k+1) X = treeLenCovOne 1 (k+1) X` is not definitionally the multiscale `renDY G 1 Y = treeLenCov G 1 Y`. No landed declaration gives $X\in\mathrm{renYs}$ or the required size comparison.

**OPEN (`renE0_fibre_det`), with an exact sufficient interface.** For each root $z$ choose a fixed, datum-independent map $\Phi_z$ from relevant collar hulls to `renYs z` such that $X\subseteq\Phi_z(X)$, $\operatorname{renDY}(\Phi_z(X))\le A\operatorname{sizeJ}_1(X)+C$, and $\#\{X:\Phi_z(X)=Y\}\le C_f e^{\sigma\operatorname{renDY}(Y)}$, with $A>0,C,C_f\ge0$. Define $t_Y(q)=\sum_{X:\Phi_z(X)=Y}\mathrm{detGrouped}_X(\theta(q))$. Under the chart inclusion above, finite-sum reindexing gives the determinant trace; $X\subseteq Y$ gives `RawAgree Y` locality; finite sums and composition give analyticity; and for $\kappa_a\le\lambda/A-\sigma$,
$$\|t_Y\|\le H C_f e^{\lambda C/A}e^{-\kappa_a\operatorname{renDY}(Y)}.$$
Thus the proposed exact conclusion is `IsLocExp … (Ys z) (renDY G 1) κa (H*C_f*exp (λ*C/A)) (renE0θ_det z) t`, with the listed premises and $\lambda\ge0$. The proof is **PROVED CONDITIONAL ON OPEN** $\Phi_z$, chart inclusion, and relative analytic composition; the landed determinant theorem supplies the other inputs. A weighted-fibre estimate may replace the displayed cardinal estimate, with the same final rate inequality. This is a determinant-only first case, not `expE0`.

## 4. Definitions to freeze and proof leaves

**PROVED (definition-level target for the determinant component).** The following is Lean-shaped code in a section with the standard dimension and `S` variables; `renThetaDatum` and its elementary submodule proof are new, while the operations on the right are landed. The sum ranges over all finite cube sets at $m_0=1$; `sum_detCollarGrouped` reindexes it by collar hulls.
```lean
noncomputable def renThetaDatum (ε : ℝ) (D : BgData S.G' N) (ξ : Fin 3 → ℂ) :
    BgData S.G' N :=
  bgOfRaw ((fun x i => (1 + renZeta ε ξ) * D.Ψ x i), D.h)
    (renThetaRaw_mem_rawSub ε D ξ) -- new elementary lemma
noncomputable def renE0θ_det
    (εren : ℝ)
    (E : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      DetExpansionLocC S 1 z εstep κdet cdet)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (D : BgData S.G' N) (ξ : Fin 3 → ℂ) : ℂ :=
  ∑ T : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (K := k + 1) 1 (k + 1) Set.univ), (E z).term (renThetaDatum εren D ξ) T
```
The zero-parameter identity is `renE0θ_det εren E z S.D' 0 = -(1/2 : ℂ) * ∑ y ∈ S.blockU z, ∑ i, S.logAC (y,i) (y,i)`, conditional on the chart hypothesis for `S.D'` at radius $\varepsilon_{\rm step}$; prove it by `renZeta` at zero, `(E z).sum_eq`, then `rootTrace_one_eq_logAC`. This equality checks the **determinant part only**.

**OPEN (full definitions).** A physical `renE0θ z D ξ` must add the jointly defined marked $E1locC$ family to `renE0θ_det`, then prove equality with `S.E0locC` at $\xi=0$ and with the actual step output for every chart datum. `ParamDatumFamily.lean:thm31aC_coeff` gives a fixed-datum coefficient sum **conditional on** `E1MarksC` and `DetExpansionC`; it does not construct that joint family. A physical `renM0θ g p D ξ` must evaluate the source-dependent `S.M0C` family at the scaled datum and multiply by $\beta_k^{-1/2}$; `StepComplexThm31.lean:thm31bC_of_input_M0` gives the fixed-datum coefficient sum **conditional on** `ObsMarks`, not this family. `StepComplexProp26.lean:prop26C_step` proves the step identity under its regularity and nonvanishing premises, not these chart-wide definitions. Accordingly no full `renE0θ` or `renM0θ` can be frozen *from landed objects alone* without either supplying the missing family records or passing arbitrary functions as binders. The latter admits a zero witness and misses the physical statement.

**Ordered Lean leaves (estimated new lines; “start now” means independent of later open analytic estimates).**

| Order | Leaf and exact work | Inputs and status | Size / model |
|---|---|---|---|
| 1 | `renThetaRaw_mem_rawSub`, `renThetaDatum`, `renThetaDatum_zero`, raw locality of $\theta$ at equal $\xi$ | `rawSub`, `bgOfRaw`, `renZeta`; **start now** | 80–140 / Sonnet |
| 2 | `renTheta_zero_chart`: `XiCOneReal → XiCData` at $K=k+1$, $\xi=0$; split the `XiC` clauses needed at positive $\xi$ | `XiCOneReal.xiCOne`, `XiCData`; **start now** | 60–110 / Sonnet |
| 3 | `renE0θ_det` and its $\xi=0$ trace equality, with explicit `allHulls` | `detGrouped_sum`, `rootTrace_one_eq_logAC`; **start now** | 120–190 / Sonnet |
| 4 | `renE0_theta_domain` at enlarged $\varepsilon_{\rm step}$, with a concrete `ThetaChartMargin` and ambient chart map | P4 (4.19), `XiC`, `XiCRaw`; **OPEN** | 220–300 / strong |
| 5 | `renE0_det_analytic_theta`: relative `AnalyticOnNhd` composition and hull locality after $\theta$ | leaves 1, 4; `detGrouped_chart_family_fromTower`; **OPEN** | 120–210 / strong |
| 6 | `renE0_det_fibre_map`: rooted $\Phi_z$, support, `renDY` comparison, and fibre count | `renYs`, `renDY`, `detGrouped_anchor`; **OPEN** | 220–300 / strong |
| 7 | `renE0_fibre_det`: reindexing and bound $HC_f e^{\lambda C/A}$ at rate $\kappa_a$ | leaves 5–6, `IsLocExp`; **OPEN** | 170–260 / strong |
| 8 | Full `renE0θ` marked family and `renM0θ g` observable family; $\xi=0$ physical identities, then their fibre expansions | `thm31aC_coeff`, `thm31bC_of_input_M0`, source chart; **OPEN** | separate leaves ≤300 / strong |

**Confidence.** High for the fixed-mass reading of P4 (4.17)–(4.18), the exact record types, the zero-chart inclusion, and the determinant theorem's stated outputs. Medium for the proposed geometric fibre interface: it is sufficient, while the cheapest construction of $\Phi_z$ and its sharp constants remain open. Low for an unqualified full-chart `expE0`/`expM0` claim until the enlarged chart, marked family, source parameter, and fibre estimates are supplied.
