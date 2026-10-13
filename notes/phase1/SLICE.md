# SLICE: which parameter chart the fluctuation step needs

13 October 2026. Lean references were checked in the read-only main tree. Status words apply to the exact claims below. Put $K=k+1$, $S=\texttt{hatStepK}$, $q_0=\texttt{rawOf}\,S.D'$, and $V=\texttt{physV}\,S\,1\,\nu\,t$; $V$ already contains the unscaled source $g$ with $\|g\|_1<1$.

## 1. Consumers and verdict

**REFUTED as a full induction design:** a family only on $h(x)\equiv h_0$ cannot furnish the present small-field output class.
**PROVED:** `SmallField/Def6Terms.lean:XiDom` consists of $(\Psi_0+\Psi'',h_0+h'')$, with $h''$ a complex site field.
`SmallField/Def6.lean:IsSF.analyticE/analyticM` demand holomorphy in $(\Psi,h)$, and in $(\Psi,h,g)$ for the observable, on that domain.
Its `boundE/boundM`, `localE/localM`, and symmetry clauses also quantify over $h$ as a field.
Analyticity on one frozen $h_0$ fibre cannot prove these clauses: $h\mapsto\overline{h(x)_i}$ is constant on that fibre but nonholomorphic off it.

**PROVED:** `SmallField/Def6v2.lean:SFTermClauses.analyticE/analyticM` make the same joint demand on `FieldDom.dom`, with bounds, symmetry and locality in $h$.
`SmallField/Def6v2Domain.lean:Pin` fixes a real unit centre $h_*$ but allows site-dependent complex $h''$ with $\sup_x\|h''(x)\|<r_h$; `Pin.xiDom` includes it in `XiDom`.
`pinFieldDom` and `pinAllFieldDom` are draft class-domain choices pending the Q13 ruling, not assertions that $h''=0$.
At zero background mass, a bounded holomorphic class on unbounded full-`XiDom` $h''$ directions faces the Liouville issue in `notes/phase1/Q13-ANSWER-astra.md` §2.

**PROVED:** `Fluctuation/Thm31CoeffAnalytic.lean:ParamMarkFamily` accepts a complex normed parameter $E$ (the coefficient theorem later requires finite-dimensional $E$), open $V_E\subset E$, open auxiliary $\mathcal U\subset\mathbb C$, and joint `AnalyticOnNhd` on $V_E\times\mathcal U$.
`ParamCarrierLocal.lean:paramMarked_analytic_local_bound` consumes that record; neither declaration itself requires $h$ to vary.
`ParamDatumFamily.lean:e1CoeffC` and `thm31aC_coeff` are fixed-step coefficients; `thm31aC_coeff_withDatum` applies when $D.h\equiv S.h_0$.

**PROVED:** `Fluctuation/RenormExpBounds.lean:XiCOneReal` is exactly
$$\exists \Psi_0:\mathbb T\to\mathbb R^N,\ h_0\in\mathbb R^N,\ \Psi'':\mathbb T\to\mathbb C^N:
\quad\texttt{XiC}\,G\,a\,\nu\,k\,1\,\varepsilon\,\Psi_0\,h_0\,\Psi''\,0
\ \land\ \texttt{RealizesC}\,D\,\Psi_0\,h_0\,\Psi''\,0.$$
Thus $D.h(x)=h_0$ is real and constant, but the existential $h_0$ varies with $D$.
Every `Fluctuation/RenormExpG.lean:RenormExpInput` localization/expansion field uses this domain.
One fixed $h_0$ fibre cannot supply the whole record; joint continuation can be restricted to each real fibre.

**PROVED:** `Frozen/Roots/LogPartitionMultiscale.lean:logPartition_multiscale` and `Frozen/Roots/LowTemperatureCorrelations.lean:lowTemperature_correlations` quantify over every real unit $h$ and state physical conclusions.
Both proof bodies contain `sorry`. Their outer quantifier allows separate physical runs at each real $h$, but says nothing that removes the complex class clauses needed for the current induction.

P3, §4, (4.25)–(4.28), printed pp. 73–74, defines complex $(\psi+\psi',h+h')$ with $h'$ a complex field on $\mathbb B_j$, and its $\Xi_j^c$ contains that pair; PDF images were checked because the P3 OCR is unreliable.
P4, (H.4), printed p. 677, requires analytic energy terms on $\Xi_j^c(\mathbb B_j(X);1,\varepsilon_j)$.
P4, (H.7), printed p. 679, requires analytic observable terms on the same complex domain times $\|g\|_1<1$, explicitly reading $(\psi+\psi',h+h',g)|_X$.
P5, printed pp. 489–491, inherits P4 (H.4)/(H.7) through (1.6)–(1.13); (1.16)–(1.17) restrict localized terms retaining those properties.
P5 (1.18)–(1.19) is the cutoff, and (1.20), printed p. 492, is nested geometry; these do not define a frozen-$h$ analytic chart.

**Verdict:** keep full relative complex $h$ dependence for output terms and marks, and restrict to constant real $h$ when identifying a physical `StepSetting` or using `XiCOneReal`.
If Q13 selects a pinned class, estimate on the corresponding open pinned subchart, not on $h''=0$.
For a single fixed physical identity, the $h_0$ slice is sufficient once its complex-$\Psi$ exponent identity is supplied.

## 2. Exact slice and the available full-chart step

**PROVED:** `ParamActivitySubspace.lean:physParam` is `rawSub N S.G' × sources`; `physIncl` is continuous complex-linear, and `isOpen_physV` makes $V=\texttt{physIncl}^{-1}(\texttt{physSΛ})$ open.
`Inhabited/UniformChartRelative.lean:hatStepK_physV` puts $(q_0,g)$ in $V$ for every $\|g\|_1<1$.
Define $W_\psi=\ker(\operatorname{pr}_h:\texttt{rawSub}\to H_{\mathbb C})$ and $E_0=W_\psi\times\text{sources}$.
Set $J_0(v,g)=(q_0+v,g)$ and $V_0=J_0^{-1}(V)$; then $V_0$ is open in the finite-dimensional complex normed space $E_0$, and $J_0(V_0)=\{(q,g)\in V:q_h\equiv S.h_0\}$.
This is **PROVED CONDITIONAL ON PROVED** linearity of `rawSub`, $q_0\in\texttt{rawSub}$, and `isOpen_physV`; the elementary affine-preimage wrapper has not been packaged in Lean.

**PROVED:** `ParamDatumFamily.lean:paramSlice`, `existsUnique_datum_of_slice`, `sliceDatum_spec` and `sliceStep` give every $q$ in this fibre a unique `XiCData` datum $D$ with $D.h=S.h_0$.
`StepSetting.withDatum D hD` keeps $G',a_1,\nu,\beta,p_1,\delta,\nu_{p_1}$, the fluctuation space and block split (`withDatum_G'`, `withDatum_numbers`, `withDatum_nuFl`, `withDatum_blockSplit`).
Its complex covariance and shift vary with $D$ (`withDatum_covSqrtC`, `withDatum_shiftUC`).
A full-chart `AnalyticOnNhd` family restricts along complex-affine $J_0\times\mathrm{id}$; bounds and locality restrict by subset. The converse is false.

**OPEN slice-only Lean bridge:** `ParamActivitySubspace.DirectTermsFamilyOn` requires a *linear* $J:E\to_L[\mathbb C]\Lambda$, while $J_0$ is affine.
A slice-only campaign would generalize that record and `labelActFamilyOn` to affine maps, or recenter `DirectTerms.val` and its parameter set.
The full-chart route keeps `physV`, `physIncl`, `labelActFamilyOn`, `paramMarkFamilyOn_of_marks`, `physCarrier`, `hatStepK_physV` and `DetOutputTerms.analyticOnNhd_rawSub`.
`physical_directTermsFamilyOn` is kept where its base set is `physSΛ`; `DetExpansionLocC.atDatum` supplies the fixed-step determinant on each physical fibre.

**PROVED:** `Fluctuation/StepComplexJoint.lean:JointRep` already contains analytic representatives `F₀`, `Mx`, `Pc` and `Fb` on complex raw-data domains under `nonempty_jointRep`'s `FlCore` and margin hypotheses.
Its `gJ` carries the raw complex $h$, `PJ` passes it to the old class terms, and `W1`/`W2` are the datum-parameterized complex exponents.
`JointRep.W1_withDatum` and `W2_withDatum` identify them along admissible paths on $V_0$ with $(S.withDatum D hD).\texttt{WoneC/WtwoC}$.
`StepComplexOutAnalytic.lean:TstepJ_withDatum`, `E1J_withDatum`, `F0J_withDatum`, `M0J_withDatum` use the same full continuation/fibre matching.
`MarkedTangent.lean:exists_analytic_markedTangentC_physV` gives a full-chart analytic marked tangent with fibre matching.
Thus UNICHART leaf 5 `complexStepAtDatum` should be replaced by selecting and packaging one landed `JointRep`, not by building a complex `StepSetting`.

**OPEN exponent bridge:** for $e=(q,g)\in V$, a chosen $J_r:\texttt{JointRep}$, a carried $\Phi$, and $(s,t')\in\texttt{stepSegments}$, build one common label activity satisfying
$$\sum_y A_e(s,t').H_y(\Phi)
=J_r.W1\,C\,(q,s\widehat\psi(\Phi))
 +J_r.W2\,C\,g\,(q,t'\widehat\psi(\Phi))
\quad\text{for almost every }\Phi.$$
This is defined for complex, varying $h$ without `StepSetting.withDatum`.
On $V_0$, `W1_withDatum` and `W2_withDatum` turn it into `StepActivityBoundC.hW` for $S.withDatum D$; at $q_0$ it is the original physical step.
`StepComplexNonvanish.lean:ae_exponentsC_eq` assumes the original real step and real-ray hypotheses; it does not prove this identity at a complex-$\Psi$ datum or at varying $h$.

**PROVED:** `SharpAssemblyScaled.lean:physical_directTerms_eta_scaled` constructs `DirectTerms` with `PhysicalTerms.lean:physVal` on `physSΛEta S 1 ν t (1/β)` for all complex raw data in that set.
`physVal` is the complex five-part formula for interaction, old energy, source, old observable and mass terms.
`SourceSliceScaled.lean:sourceSlice_mem` sends $g\in\texttt{l1Ball}$ to $g/\beta\in\texttt{l1BallEta}(1/\beta)$ for $\beta\ge1$.
Define continuous complex-linear $J_\beta(q,g)=(q,g/\beta)$; then $J_\beta(V)\subseteq\texttt{physSΛEta}(1/\beta)$.
The generic `DirectTermsFamilyOn S m₀ Jβ I V` is the right interface after supplying `DiagCont` on the image.
`physical_directTermsFamilyOn` itself expects base `physSΛ` and is not directly the eta-scaled constructor.

**OPEN:** prove `DiagCont` after source scaling, and identify the assembled `physVal` evaluations with $J_r.W1+J_r.W2$ after $g/\beta$ substitution and the old-term matching hypotheses, on *all* $V$.
`StepActivityDirectGeneral.lean:physVal_eq_stepExponent_of_oldHatMatch` gives the fixed-step physical identity under its old-term matching premise for real segment parameters; it is not the full raw-datum family theorem.

## 3. Radius, targets and status

**PROVED locally at $q_0$:** on the affine slice, keep the unit datum's real centre $(\Psi_0,h_0)$ fixed and set $h''=0$; hence variation in $h$ consumes none of the `XiCBounds` $h''$-dot $t^2$ margin. This choice is justified on a sufficiently small complex-$\Psi$ neighbourhood, not at every point of $V_0$.
Complex $\Psi$ still moves background, bilinear and gradient inequalities.
`hatStepK_physV` gives a positive scale-dependent datum radius, hence so does its affine slice.
**OPEN-RESPONSE-UNIFORM-SLICE:** a scale- and volume-independent raw-sup radius would require weighted *field and multiplier* response and strict segment inclusion for complex $\Psi$ variations with $h''=0$, uniformly in $k,N_1,\nu,\beta$.
This is weaker than full-chart OPEN-RESPONSE-UNIFORM in `UNICHART.md` §2; `theorem72_linearResponse` alone does not supply it.
No listed pointwise class or `ParamMarkFamily` consumer requires a uniform raw radius; uniform datum Cauchy derivatives would.

**REFUTED:** freezing $h$ does not remove the source product-sup obstruction.
With $M$ source coordinates, a sup ball about $g=0$ inside $\|g\|_1<1$ has radius at most $1/M$; no common radius works near every boundary point.
Use source $\ell^1$ neighbourhoods. Auxiliary $\sigma$ and marked fluctuation discs have separate fixed numerical margins; `UNICHART.md` §1 records the marked-disc arithmetic.

| Order | Lean leaf, each at most 300 lines | Assignment and status |
|---|---|---|
| 1 | `jointRep_scale_choice`: choose one `JointRep` under tower `FlCore`, covariance and path margins; expose `W1/W2` and fibre matching. | Strong; start now. **PROVED CONDITIONAL ON** the displayed scale hypotheses via `nonempty_jointRep` and `W1_withDatum` and `W2_withDatum`. Replaces UNICHART leaf 5. |
| 2 | `sourceScale_relative`: construct $J_\beta$, prove $J_\beta(V)\subseteq\texttt{physSΛEta}(1/\beta)$, source agreement and `DiagCont` on its image. | Strong; start now. Membership **PROVED CONDITIONAL ON PROVED** `sourceSlice_mem`; `DiagCont` **OPEN**. Refines leaf 6. |
| 3 | `sourcePhysVal_jointRep`: for every $q\in V$, carried $\Phi$, real $s,t'\in[0,1]$, identify matching `physVal` evaluations at $J_\beta(q,g)$ with `JointRep.W1/W2`, including old sums and zero-source subtraction. | Strong; after 1–2 and old-term matching; **OPEN**. |
| 4 | `sourceExponent_family`: use `labelActFamilyOn_eq_dtAct`, leaf 3 and one zero-extended common label set for the displayed full-$V$ identity, then fibre and original-step `hW`. | Strong; after 3 and common labels; **OPEN**. Refines UNICHART leaf 7. |
| 5 | `classTerms_joint_chart`: transfer coefficients, determinant and observable marks to `IsSF` or chosen pinned `SFTermClauses` on the required $(\Psi,h,g)$ domain, with locality, symmetry and bounds. | Strong; after 4, MARKPARAM, OBSMARKS and LOCREN; **OPEN**. |
| 6 | `sliceAffine_bridge`, only for a separate slice proof: construct $E_0,V_0,J_0$ and an affine family record or recentered terms. | Sonnet; defer. Existing linear-map binder prevents direct reuse. |
| 7 | `uniformResponse_slice`, only for uniform datum Cauchy derivatives: prove OPEN-RESPONSE-UNIFORM-SLICE. | Strong; defer; no present pointwise consumer needs it. |

Keep UNICHART leaves 1–3 for the qualitative chart and fixed disc/tower arithmetic; its leaf 4 remains optional research, and leaf 8 follows the physical source identity and amplitude threshold.
`markedEv_joint_param` and `markedCubic_joint_param` retain full-`physV` joint analyticity; `markedCommonLabels_zero` keeps one full-chart activity and verifies `hW` on the physical fibre (MARKPARAM).
`sourceDirectTerms_relative` becomes leaf 2 plus `sourcePhysVal_jointRep`; `sourceExponent_family` is leaf 4.
Keep `DetExpansionLocC` and `analyticOnNhd_rawSub` full-chart and use `atDatum` on the fibre.
OBSMARKS 8.6/8.7 keep full-chart analytic tilt/mark families but assert the `StepSetting` identity on the fibre.
LOCREN 10–13 range over *all* `XiCOneReal` real-$h_0$ fibres; strict mass-shift and local expansion inputs remain OPEN and cannot follow from a single fixed fibre.

**Open items:** full `DiagCont` after source scaling; exact `physVal`–`JointRep` match with old terms; common label and mark families; output-class transfer and Q13 pinned-domain decision; renormalization mass and localization; optional uniform response.
**Confidence:** high for the consumer verdict and existing `JointRep` reuse; medium for the scaled relative-family bridge; the full exponent match remains OPEN.
