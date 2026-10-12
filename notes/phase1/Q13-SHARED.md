# Q13 round 20: shared work at parameterized background mass

## Summary

The sharp LF cutoffs and the $R$ centre stay massless. Let $m_{\rm bg}\in\{0,m_{\rm phys}\}$ denote the mass used for the background of the LF action. The support algebra and assignment of old terms are common to A and A0′. The complete-background analytic bounds required by A0′ are additional. A0′ and A are therefore not ordered by inclusion of open statements.

P6 first splits and localizes inherited $E,F$ terms, including the P5 (1.8) correction. It then bounds the grouped term inside a new LF component by volume (P6 (2.18)–(2.21), (2.31)–(2.33)). Crossing terms need D7 decay. The physical-mass $R$ reference-density correction is common to both schemes; its real denominator bound reduces to a missing localized derivative estimate.

## 1. Shared assignment

Put $Y_{\rm old}=Z_k^c$, $Y_{\rm new}=Z_{k+1}^c$, and $X=Y_{\rm old}\cap Z_{k+1}$. Both schemes start from complete SF data. The parameter $m_{\rm bg}$ specifies the *target LF action*: zero for A, physical for A0′. The regional subtraction in Q13-REEXPAND (1.1), with analogous $F,R$, vacuum and half-star splits, is **PROVED algebraically** under nested supports and absolute convergence. At $m_{\rm bg}=0$, add the complete-to-massless conversion on $X$; at $m_{\rm bg}=m_{\rm phys}$, that conversion is zero.

Suppose every residual term has an exact absolutely summable localization expansion $t=\sum_U t_U^{m_{\rm bg}}$, with $U$ recording every field variable and history label it reads. D7 history locality cancels terms disjoint from $X$. Assign $t_U$ to the first new component $Z$ in a fixed order only if its support lies in the allowed kernel halo and all its variables are available there. Assign other labels to the next boundary family. Write $B_Z=\sum_{U\mapsto Z}t_U$ and $\mathcal B_{\rm next}=\mathcal B_{\rm retained}+\sum_{U\mapsto\partial}t_U$. Then
$$V_{\rm old}+\mathcal B_{\rm old}=V_{\rm new}+\sum_Z B_Z+\mathcal B_{\rm next},\qquad
e^{V_{\rm old}+\mathcal B_{\rm old}}\prod_ZK_Z^0
=e^{V_{\rm new}}\prod_Z(K_Z^0e^{B_Z})e^{\mathcal B_{\rm next}}. \tag{1.1}$$
This is **PROVED CONDITIONAL ON exact localization and allowed-variable support**: partition the labels once, sum and exponentiate. Integrability then permits the conditional Gaussian integration. The identity does not prove the required locality or estimates.

The following analytic operations are independent of the *value* of $m_{\rm bg}$ once their class hypotheses hold.

1. **Cutoff and measure — PROVED algebraically, conditional on integrability.** The one massless-predicate partition $1=\prod_C(\chi_C^0+1-\chi_C^0)$ and Fubini assign a real branch to each history. The fluctuation cutoff and reference measure have no action-background mass.
2. **Old D7 boundary terms — PROVED CONDITIONAL ON D7, P6 geometry and its localization theorem.** Terms away from $X$ cancel by history locality. Terms touching old LF and the new fluctuation region have the old $B_0e^{-\kappa d_k^{\rm cov}}$ bound. The collar separation in LF-RECONSTRUCTION IV.1.5 gives $e^{-\kappa L[\hat R_k]/2}$, absorbing $B_0$ under $(\Lambda28)$. P6 §4 (4.32)–(4.34) prelocalizes the Gaussian quadratic and surface terms, then resums old boundary labels with bound $\beta_k^{-3/2}e^{-(2\kappa-1)d_{k+1}}$. The geometry and resummation do not use the value of $m_{\rm bg}$ once D7 and analytic domains are uniform. This complete localization is cited, not landed as a Lean step theorem.
3. **Assignment of localized labels — PROVED CONDITIONAL ON support and norm hypotheses.** Triangle inequality gives $|B_Z|\le\sum_{U\mapsto Z}|t_U|$, paid by the (S2) volume allowance. P6 resummation sends straddling bounds to D7 with the stated one-unit tree-rate loss. Producing the $t_U$ with admissible support and bounds for the complete inherited SF input is **OPEN**.

The background-dependent estimates are as follows.

| Piece | $m_{\rm bg}=0$ | $m_{\rm bg}=m_{\rm phys}$ |
|---|---|---|
| Main action and half-star at a changed regional field | P6 (2.11)–(2.17), (2.31); LF-RECONSTRUCTION IV.1.3 (O-2′), **PROVED CONDITIONAL ON** FLUCTUATION Theorem 4.2, LOC I-4a/b, AE, GM and auxiliary cover. Its bound is $C_Fp_0(\beta_k)^2e^{-\gamma_wD_k}e^{-(2\kappa-1-\kappa_0)d_{k+1}^{\rm cov}(U)}$. No landed Lean step theorem constructs this full kernel. | A complete-mass O-2′ for the *regional-data* change is **OPEN**. For the separate *same-datum mass* change on $n$ verified cubes, landed massChange_region_bound_cubes gives the **real** cost $q_kn$ with $q_k=C_D\beta_km_{\rm bg}^2+C_W\beta_km_{\rm bg}\delta_0$, $C_D=(d+2)M^dL^2K_m^2B_h^2$, $C_W=2dM^{d-1}L^2K_mB_h$. This needs cube assignment and quiet refund for (S2); it gives no complex D7 estimate. |
| Old $E$, including P5 (1.8) | P6 (2.18)–(2.20), Proposition 2.1, **cited conditional estimate** at a massless composed field: old-scale labels $\le{\rm const.}E_0e^{-(\kappa-1)d_k}$, new-scale labels $\le{\rm const.}E_0e^{-(2\kappa-\kappa_0-1)d_{k+1}}$. P6 explicitly includes correction flux. LF-RECONSTRUCTION IV.1.1(e) cites this; no Lean declaration proves the full construction. | Finite support split **PROVED**. Complete-$\Xi^c$ analytic localization and response to a changed regional datum **OPEN**. The landed same-datum mass response gives real field difference $O(K_mB_hm_{\rm bg})$, but not $E_j$ derivatives on a common complex domain or boundary-distance decay. |
| Old $F$, including $g\phi$ | P6 Proposition 2.2, **cited conditional estimate**, same geometry as $E$ with $E_0$ replaced by $2$, and $g$ in its $\ell^1$ disc. | Exact support split **PROVED**; complete-background marked-function bounds and regional response **OPEN**. The real mass response alone does not bound marked polymer sums. |
| Old $R_n$ | P5 (1.16)–(1.17) bounds localized coefficients by $\beta_k^{-n-1}$; P6 (2.21), (2.32) carries the restricted remainder, **cited conditional** on SF flow. | Exact support split unchanged; complete SF remainder bounds and local-history dependence **OPEN**. |
| Rotation and $h$ dependence | LF-RECONSTRUCTION IV.1.6 has $C_{\rm S5}=3$ because a massless background has no $h$ dependence, **PROVED CONDITIONAL ON** LF-3 inputs. | Cutoff support remains invariant. The exponent reads $h$ through $\phi^{m_{\rm phys}}$ and the mass term; a complete-background $D_h\phi$ bound and revised $C_{\rm S5}$ are **OPEN**. |

Here $m_{\rm bg}$ in $q_k$ is dimensionless $\nu_k$; its fine action coefficient is $m_{\rm bg}L^{-2k}$. At zero mass $q_k=0$. The landed massChange_sameData_response_unit has a **distributed** source and no distance-to-boundary factor, so it cannot replace the same-mass far-data response in O-2′. LF-RECONSTRUCTION IV.1.4 derives full massless (S2) from P6 (3.4)–(3.9). At positive $m_{\rm bg}$, the real extra action cost is at most $q_kn$ under its cube hypotheses, while complete analytic (S5), $E,F,R$ inputs and refund remain **OPEN**.

**The old $E,F$ question.** P6 p. 7 (2.19) defines residual old $E$ from deleted centres and retained centres whose polymer support crosses $(Y_{\rm new})^\approx$; it includes P5 (1.8) counterterms with $x\in(Y_{\rm old})^\approx\setminus(Y_{\rm new})^\approx$. The remaining $E$ is re-evaluated at the new composed field, with a first-order integral for the difference. Proposition 2.1 localizes both pieces into old-scale and next-scale boundary terms. P6 p. 8 Proposition 2.2 does the analogous work for $F$, including $g\phi$, with constant $2$.

P6 pp. 13–15 (2.31)–(2.33) then groups terms within new LF into $B^{(k)}$, bounded by $(\mathrm{const.})B_0(|Y_{\rm old}\cap\Omega_{k+1}^c|_\eta+|Z_{k+1}\cap\Omega_{k+1}|)$; it says a localization representation of this *kept* term is no longer needed. P6 p. 13 (2.30) sends the new antisymmetric counterterm crossing the boundary to the next-scale boundary family. Thus **PROVED from source formulas:** inner old terms are eventually paid crudely in (S2), but their assignment requires the preceding split/localization; crossing terms and re-evaluation require analytic expansion. P5 pp. 490–491 (1.10)–(1.17) give definitions and class bounds, not an unconditional bound for an arbitrary regional difference.

## 2. Physical mass variation on the $R$ core

Use the massless solver $\phi^0(\psi)$ and fixed real unit $h$. In fine units the added action is
$$P_{\nu,h}(\psi)=\frac{\nu_k}{2L^{kd}}\sum_{x\in D_Z^{\rm sites}}|\phi_x^0(\psi)-h|^2. \tag{2.1}$$
The half-star bond is **independent of $\nu_k$** when evaluated at the *same* massless field. It cancels in $F_{\rm ph}-F_0=P_{\nu,h}$; its derivatives are already in the massless Hessian estimates. This accounting is **PROVED**, conditional on identifying P7's action support $D_Z$.

The needed bound of Q13-REEXPAND (3.4) is
$$\|DP_{\nu,h}(\psi^0)\|_{\ell^2(Z_0)}\le C_1\nu_k\sqrt n,\qquad
|D^2P_{\nu,h}(\psi)[v,v]|\le C_2\nu_k\|v\|_2^2,\qquad n=|Z_0|, \tag{2.2}$$
uniformly in $|Z|$, $k\le k_0$ and the cutoff ball. Finite differentiation, assuming a $C^2$ solver, gives
$$DP[v]=\nu_kL^{-kd}\sum_x\langle\phi_x^0-h,D\phi_x^0[v]\rangle,\quad
D^2P[v,v]=\nu_kL^{-kd}\sum_x\bigl(|D\phi_x^0[v]|^2+
\langle\phi_x^0-h,D^2\phi_x^0[v,v]\rangle\bigr). \tag{2.3}$$
These identities are **PROVED** under that regularity. Fluctuation/WeightedProp51.lean:weightedProp51S_exists and FarDecayUncond.lean:lemma41_uncond give exponential response to a *finite supported datum change* at one mass, with Dec2.OpSetting and full Proposition 5.1 premises. Background/Prop51Mass.lean:prop51_analytic_small supplies analytic dependence on data. R/MassResponseHyp.lean:massChange_sameData_response_unit compares masses at the *same* datum; it is not a derivative in $Z_0$ variables.

The **single missing estimate** is a uniform core-to-action differential response, including the actual $Z_0$ lift, collar and P7 site weights. For $z,z'\in Z_0$ let $J_{xz}=D_{\psi_z}\phi_x^0$ and $H_{xzz'}=D_{\psi_z}D_{\psi_{z'}}\phi_x^0$. Require
$$L^{-kd}\sup_z\sum_{x\in D_Z^{\rm sites}}|J_{xz}|\le A_1,\qquad
L^{-kd}\sup_z\sum_x|J_{xz}|^2\le A_2,\qquad
L^{-kd}\sup_z\sum_x\sum_{z'\in Z_0}|H_{xzz'}|\le A_3, \tag{2.4}$$
and the opposite-index Schur bounds controlling the quadratic forms uniformly. Constants must be independent of $Z,k$. Weighted Proposition 5.1 suggests exponential one-site kernels, but its stated FarBounds does not include (2.4), the second derivative, or summability across the *whole* action region. Consequently (2.2) is **OPEN**, reduced to coreToActionDifferentialResponse (2.4). Given corresponding operator-form norms, $|\phi^0-h|\le2$, Cauchy–Schwarz and Schur give $C_1=2A_1$ and $C_2=A_2+2A_3$; this implication is **PROVED CONDITIONAL ON (2.4)**. A global pointwise response would sum over $|Z|$ and cannot give the required $D_0^d$ denominator constant.

## 3. Lean-ready physical reference and denominator

R/PsiZeroData.lean:effAction calls Background/Data.lean:action with mass zero; R/RhoZero.lean:rhoZeroWith uses effActionNorm, so Denominator.lean:denominator_eq is a zero-mass theorem. Define a real background datum $\operatorname{dataRH}(G,\psi,h)$ with the *same* lifted block field as dataR and constant fine field $h$. Define
$$\begin{aligned}
\phi_{\rm ref}(\psi)&:=\operatorname{bgField}(G,a,0,\operatorname{dataR}(G,\psi)),\\
F_{\rm ph}(\psi,h)&:=
\frac{\operatorname{action}(G,a,\nu_kL^{-2k},
   \operatorname{dataRH}(G,\psi,h),\phi_{\rm ref}(\psi))}
 {L^{k(d-2)}},\\
\rhoZeroPhysicalWith(Z_f,\psi_0,\psi_k,\nu_k,h,C_6,\beta_k,p_0,u)&:=
\operatorname{chiZeroCut}(\psi_0,C_6\beta_k^{-1/2}p_0,u)
\cdot\exp[-\beta_k F_{\rm ph}(\operatorname{mergeField}(Z_f,\psi_k,u),h)].
\tag{3.1}
\end{aligned}$$
This is an **exact definition-level correction to the landed effActionNorm model**: the block datum and massless solver stay fixed; action adds (2.1) when its support is the whole generating set. To identify it with P7 Definition III.8.1 one must identify the action region and half-star convention with P7's restricted $A_k^*(Z)$. The landed effAction uses the whole generating set and does not encode that restricted support. That identification is **OPEN**. A P7-specific implementation uses actionRegionR on the true $D_Z$ plus its exact half-star term, retaining the same $\phi_{\rm ref}$.

Put $u_0=\psi_k^0|_{Z_0}$, $n=|Z_0|$, $I_{\rm ph}=\int\rhoZeroPhysicalWith\,du$, and
$$\widetilde E^{\rm ph}_0=\log I_{\rm ph}+\beta_kF_{\rm ph}(\psi_k^0,h)+\tfrac N2n\log\beta_k. \tag{3.2}$$
The real denominator statement is: under the current denominator_eq geometry, radius and $\beta_k>0$ hypotheses, plus (2.2), $g_D-C_2\nu_k=:g_*>0$, $H_*:=2+C_2\nu_k$,
$$I_{\rm ph}=\exp\{-\beta_kF_{\rm ph}(\psi_k^0,h)-\tfrac N2n\log\beta_k+\widetilde E^{\rm ph}_0\}>0,\qquad
|\widetilde E^{\rm ph}_0|\le C_{\widetilde E}^{\rm ph}D_0^d, \tag{3.3}$$
where one explicit constant is
$$C_{\widetilde E}^{\rm ph}=
\left|N\log2-\tfrac N2\log N-H_*\right|
+\frac{C_1^2E^2}{2H_*\beta_k}
+\frac N2\left|\log\frac{4\pi}{g_*}\right|
+\frac{C_1^2E^2}{g_*\beta_k},\qquad E=e^{2\epsilon}. \tag{3.4}$$
Use $g_D/2$, $2+C_2E/\beta_{\min}$ and $\beta_{\min}^{-1}$ for a uniform majorant after $C_2E/\beta_{\min}\le g_D/2$. This is **PROVED CONDITIONAL ON (2.2)** by Q13-REEXPAND (3.5)–(3.7): the massless Hessian lies in $[g_D,2]$, while the physical Hessian lies in $[g_*,H_*]$ and has a nonzero linear term bounded by $C_1\nu_k\sqrt n$. Taylor and Young give a Gaussian upper bound and a lower bound on the coordinate cube inside the cutoff. DenominatorTaylor.lean, DenominatorGauss.lean and the translation/cutoff part of Denominator.lean:denominator_eq are reusable. DenominatorSqueeze.lean:effAction_squeeze applies **only to the massless part**; its critical-point conclusion fails for $F_{\rm ph}$. The numerical bound and cTildeE need a new lemma. Positivity and the logarithmic equality follow from the lower cube bound.

The extra mass term is continuous in the real core variable if the massless BG solver is continuous, so its exponential is Borel. RopNorm.lean:R_normalization_of_indep requires integrability and one positive common denominator. The file RopConcreteMeas.lean and declaration measurable_rhoZeroTot mentioned in the request are **not present in the read-only checkout examined here**; their reuse cannot be verified from this tree. DenominatorRot.lean:rhoZero_rot, integral_rhoZero_rot and tildeE0_rot have no $h$ input and cannot be reused at fixed $h$. The physical statements rotate $(\psi_k,h,u)$ **jointly**:
$$\rho^{\rm ph}(Q\psi_k,Qh;Qu)=\rho^{\rm ph}(\psi_k,h;u),\quad
I_{\rm ph}(Q\psi_k,Qh)=I_{\rm ph}(\psi_k,h),\quad
\widetilde E^{\rm ph}_0(Q\psi_k,Qh)=\widetilde E^{\rm ph}_0(\psi_k,h). \tag{3.5}$$
They are **PROVED CONDITIONAL ON** BG equivariance and exact action support, by the measure-preserving substitution of DenominatorRot.lean. Analyticity of $\widetilde E^{\rm ph}_0$ on complex exterior data remains **OPEN** under physicalMassCoreVariationComplex and a nonzero analytic denominator; see Q13-REEXPAND §3.

## 4. Verdict in five lines

1. Regional support algebra, P5 correction flux, localized assignment, old-boundary decay and the physical reference denominator are shared work.
2. The **hardest shared OPEN statement** is exact analytic localization/assignment of complete inherited $E,F,R$ and the changed regional field with D7 and (S2) bounds.
3. The cheapest A-specific test is one regional complete-to-massless $E$ correction with omitted-polymer and P5 flux bounds on a common complex domain.
4. The cheapest A0′-specific test is one-cube complete-action LF (S2)/(S5), with a massless cutoff, its mass-response action cost and $h$ derivative.
5. A0 remains ruled out; A stands until the A0′ factorization and its extra estimates are proved.

## 5. Shared Lean worker list

These are proposed modules of roughly 300 lines or less. No read-only source file is changed.

1. RegionalSupportSub — **PROVED algebraically; Lean OPEN.** Formalize Q13-REEXPAND (1.1) with finset/tsum splitting, including the restricted correction, then $F,R$, vacuum and half-star analogues. Parameterize target evaluation by $m_{\rm bg}$.
2. AssignLocalizedTerms — **PROVED CONDITIONAL ON exact expansions and allowed support; Lean OPEN.** Give each label a deterministic owner, prove its partition and (1.1), and propagate local history and $g$ dependence.
3. OldBoundarySeparation — **PROVED CONDITIONAL ON D7 and LF-RECONSTRUCTION IV.1.5 geometry; Lean OPEN.** Prove the $\kappa L[\hat R_k]/2$ gain and $B_0$ absorption; record P6 (4.34) localization as a named input.
4. GroupedKeptBound — **PROVED CONDITIONAL ON P6 Propositions 2.1–2.2 and (2.33); Lean OPEN.** Sum inner $E,F$ and action-change labels into $B^{(k)}$, bound it by P6's volume expression, and reserve crossing labels for D7. Parameterize uniform local bounds by $m_{\rm bg}$.
5. PhysicalReferenceDef — **PROVED at definition level; Lean OPEN.** Add dataRH, effActionPhysicalNorm, rhoZeroPhysicalWith; prove the difference from the landed zero-mass action is (2.1). Keep P7 restricted-support identification **OPEN**.
6. CoreMassDerivativeReduction — **PROVED CONDITIONAL ON coreToActionDifferentialResponse; Lean OPEN.** Differentiate (2.1), use Schur and $|\phi^0-h|\le2$ to derive (2.2). The kernel bound (2.4) itself is **OPEN**.
7. DenominatorPhysicalReal — **PROVED CONDITIONAL ON (2.2); Lean OPEN.** Reuse massless squeeze, translation and Gaussian integral, retain the linear term, and prove (3.3)–(3.4).
8. PhysicalReferenceJointRot — **PROVED CONDITIONAL ON exact action support and BG equivariance; Lean OPEN.** Rotate $(\psi,h,u)$ together, then use the positive common denominator in R_normalization_of_indep.

## Source anchors

P5 pp. 490–491, (1.8), (1.10)–(1.17), and p. 512, (2.47); P6 pp. 6–9, (2.11)–(2.21), Propositions 2.1–2.2, pp. 13–15, (2.30)–(2.33), and pp. 33–35, (4.32)–(4.34). LF-RECONSTRUCTION IV.1.1–IV.1.6 and III.8.1–III.8.4. Landed proof points: Fluctuation/WeightedProp51.lean:weightedProp51S_exists, Fluctuation/FarDecayUncond.lean:lemma41_uncond, Background/Prop51Mass.lean:prop51_analytic_small, LargeField/R/MassResponseHyp.lean:massChange_sameData_response_unit, LargeField/R/MassChangeCrossing.lean:massChange_region_bound_cubes, LargeField/R/RhoZero.lean:rhoZeroWith, LargeField/R/Denominator*.lean, and LargeField/R/DenominatorRot.lean.
