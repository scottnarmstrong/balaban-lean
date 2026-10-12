# Q13 round 19: re-expansion shared by the two viable conventions

## Summary and ruling

The author has ruled out A0: the sharp large-field cutoffs and the $R$ reference remain massless. The re-expansion of old terms when the small-field set shrinks is required by **both** variant A and the proposed hybrid A0′. Its finite-sum subtraction is proved below. Its local, decaying assignment to new LF kernels and next-scale boundary terms is still an analytic theorem, conditional on the same sort of localization used in P5–P6 and LF-RECONSTRUCTION LF-3. P6 (4.32)–(4.34) treats the old *boundary terms and Gaussian/surface terms* touching the new region; it is not by itself a proof for every inherited $E,F,R$ term.

The open-statement set for A0′ is **not literally a subset** of that for A. A additionally needs a regional complete-to-massless conversion, its marginal remainder, and possibly sharp-cutoff glue. A0′ instead needs LF (S2), (S5), and action-conversion estimates with **complete action backgrounds** and massless sharp cutoffs; A's LF estimates use massless action backgrounds. A0′ also has the extra complete-field response in the $R$ window. The common re-expansion work is reusable in either scheme, but the two analytic packages are not ordered by inclusion. The physical-mass $R$ reference-density repair below is shared by both.

## 1. Exact regional algebra and an assignment theorem

Use the notation of `Q13-FACTOR.md` (1.1)–(1.3). The old small-field region is $Y$, the new one $Y'\subset Y$, and $X=Y\setminus Y'$ is assigned to new LF components $Z_1,\ldots,Z_s$. At inherited scale $j$, $R'\subset R$ are the centre sets and $B'\subset B$ the thickened polymer supports. The exact $E$ difference is
$$\begin{aligned}
\Delta E_j={}&\sum_{y\in R\setminus R'}\sum_{P\ni y,\,P\subset B}E_j(y,P;\psi_Y)
+\sum_{y\in R'}\sum_{P\ni y,\,P\subset B,\,P\not\subset B'}E_j(y,P;\psi_Y)\\
&-\operatorname{Corr}(R\setminus R',B;\psi_Y)
-\operatorname{Corr}(R',B\setminus B';\psi_Y)
+\bigl[E_j(R',B';\psi_Y)-E_j(R',B';\psi_{Y'})\bigr]. \tag{1.1}
\end{aligned}$$
This is **PROVED**, assuming the actual supports are nested and the polymer sums absolutely converge. `Def7v2Corr.lean:corrSum_singleton,corrSum_ne_zero_example` show the restricted correction flux can be nonzero. There are analogous exact differences for the leading $\sum_{x\in Y}g_x\phi_Y(x)$ and the marked $F$ polymers ($x\in Y$, $P\subset Y^\approx$), the $R$ polymers ($P\subset Y$), the vacuum count $-E_k|Y|_k$, and the half-star action. Every such difference has deleted supports, crossing supports, and the old-to-new evaluation change on retained supports. Write their sum, including old boundary terms that touch $X$, as $\Delta V=V_Y-V_{Y'}+\Delta\mathcal B_{\rm old}$. This identity is **PROVED algebraically**; it is not yet a localized expansion.

Here is the precise assignment theorem that would turn it into the LF step. For each summand $t$ of $\Delta V$, assume an **exact** localization expansion $t=\sum_{U\in\mathcal U_t}t_U$ with absolutely summable labels, such that $t_U$ depends only on the field, history, $h$, and $g$ restricted to the labelled support $U$. Assume terms whose supports miss $X$ cancel by history locality. Fix a deterministic order on the new components. For each surviving $U$, assign it to the first component $Z_i$ for which $U$ lies entirely in its prescribed kernel halo and meets $Z_i$; put every other $t_U$ into the boundary family $\mathcal B^{\rm next}(U)$. Then, with the exact Gaussian and indicators included in $K_i^0$,
$$\boxed{\quad e^{V_Y+\mathcal B_{\rm old}}\prod_iK_i^0
=e^{V_{Y'}}\prod_i\bigl(K_i^0e^{\sum_{U\mapsto i}t_U}\bigr)
\exp\!\left(\sum_{U\mapsto\partial}t_U+\mathcal B_{\rm retained}\right).\quad} \tag{1.2}$$
For overlapping halos the deterministic rule assigns a support only when the chosen LF kernel is allowed to read all of its variables; otherwise it goes to the boundary family. The equality is **PROVED CONDITIONAL ON exact localized expansions and allowed-variable support**: substitute each $t=\sum_Ut_U$, partition the labels, and use $e^{a+b}=e^ae^b$. The subsequent conditional Gaussian integration is legal under the stated absolute summability/integrability. No estimate or locality follows from that algebra. The analytic version must prove
$$\sum_{U\mapsto i}|t_U|\le C_{\rm step}(Z_i)\quad\text{with its (S2) charge},\qquad
|\mathcal B^{\rm next}(U)|\le B_{\rm st}e^{-\kappa_+d^{\rm cov}(U\bmod\Omega^c)} \tag{1.3}$$
and (S0), (S4), (S5), the observable $g$ domain, and torus coherence. That version is **OPEN** for either convention. One cannot prove it by defining $K_i=e^{\Delta V}K_i^0$: $\Delta V$ may depend on forbidden old variables or on several components, and the D7 bound is not automatic.

Under **A**, the fields in $V_Y$ are complete but the LF action and inherited factors on the new component are massless. Its difference therefore has (i) (1.1) and the $F,R$, action-support analogues, (ii) re-evaluation $\psi_Y^m\to\psi_{Y'}^m$, and (iii) a complete-to-massless change on the new component and boundary halo. The last is `REGIONAL.md:regionalEnergyIdentity`, `regionalMarginalRemainder`, and the cutoff/reference glue. Under **A0′**, (i)–(ii) remain and (iii) is absent: both sides evaluate the inherited terms at complete backgrounds. Its LF action, new-component bounds, and $R$ numerator must instead be redone for $\phi^m$ while its sharp cutoffs and $R$ reference remain massless. **PROVED comparison of obligations:** common algebra is shared; **OPEN comparison of estimates:** no implication from A's massless LF (S2)/(S5) estimates to A0′'s complete LF estimates has been established. This complete-action LF estimate is the requested statement A0′ needs and A does not.

## 2. What the sources actually re-expand

P6 §4, pp. 33–35, (4.32) writes the remaining fluctuation interaction as a Gaussian quadratic term, a surface term, and $u\mathcal B''^{(k)}$ evaluated at the old localized field. Its $\mathcal B''^{(k)}$ sums old boundary domains meeting both the old LF set $Z_k$ and the new fluctuation region $\Omega_{k+1}$. The first two terms are prelocalized in cubes and star-bond intersections; the last is expanded and resummed over domains containing the old support, yielding (4.33) and the $\beta_k^{-3/2}e^{-(2\kappa-1)d_{k+1}}$ estimate (4.34). This directly handles the **old boundary and Gaussian/surface** pieces of (1.2), including crossing supports. It does **not** directly state (1.1) for the P5 restricted correction or the entire $F,R$ exponent. P6 §2, P5 Propositions 3.1–3.4, and the small-field I-8/I-9 expansions are the cited route for those terms. The published estimates were derived in the below-$k_0$ massless background convention; using the same algebra with complete backgrounds requires corresponding analytic domain, derivative, and decay bounds. Masslessness is not used in the finite support subtraction; it is used in the stated source hypotheses and in the free-flow coefficient bounds, so the analytic transplant is **OPEN**.

LF-RECONSTRUCTION IV.1, Theorem IV.1.1 (LF-3), sends one step's local terms supported entirely in a new $Z'$ to its $b_k$/kernel, and terms straddling components or the small-field complement to $\mathcal B^{(k+1)}$. Lemma IV.1.3 (O-2′) expands the change from the boundary generating set $\mathbb B_{k+1}(\partial\Omega_{k+1})$ to local generating sets. Its exact equation (IV.1.1) and decay bound produce local background-change terms $\Delta(U)$, assigning inner supports to $b_k$ and the others to the boundary. This is the proposed treatment of the **re-evaluation** term in (1.1) and the action-background part of (1.2). It is **PROVED CONDITIONAL ON** FLUCTUATION Theorem 4.2's LOC I-4a/b, AE, GM, weighted response, and auxiliary-cover hypotheses, for the **massless** below-$k_0$ class. The displayed proof uses equality of generating sets away from the boundary and decay of the response; the *logic* does not require zero mass, but its cited BG/LOC/FLUCTUATION estimates are not instantiated at the complete mass for this hybrid. Moreover a uniform distributed mass response alone has no boundary-distance decay, so `massChange_sameData_response_unit` cannot replace O-2′.

LF-RECONSTRUCTION III.10.3, (3.26′), P15 `expansion_326`, and III.10.4 `newBoundary` carry out the analogous re-expansion during $R$: after *removing* ripe components, the small-field set grows, and old terms plus the removed reference actions are re-expressed at the retained region's background. Its new $\mathcal B'(U)$ are supported on domains meeting a removed component and have D7-type decay; `newBoundary` combines them with retained old boundary terms and polymer activities. This is a close structural model for (1.2), **not** a direct proof for the shrinking-region LF step. The reconstruction explicitly cites P7 (3.20)–(3.25), P6 §2, P1 Corollary 3.10, P3 Proposition 4.3 and O-2′. Its analytic application remains conditional. All of its below-$k_0$ backgrounds are massless; the support partition and resummation are convention-neutral, while the bounds must be redone for complete backgrounds.

Thus the proposed assignment theorem consists of two parts: the algebra (1.2), **PROVED CONDITIONAL ON exact expansions and support**, and the analytic expansion plus (1.3), **OPEN** in the complete convention. The same analytic task occurs under A before its additional free/complete conversion. P6 (4.34) and LFR IV.1.3 give the expected *shape* of the D7 bound, but neither can be cited as a complete-mass theorem without checking its hypotheses.

## 3. Correcting the $R$ reference density

`R/PsiZeroData.lean:effAction` is `action G a 0 (dataR ψ) (bgField G a 0 (dataR ψ))`; `RhoZero.lean:effActionNorm` and `rhoZeroWith` inherit mass zero. `Denominator.lean:denominator_eq` and `DenominatorRot.lean:tildeE0_rot` therefore prove a theorem for a *different reference density* from P7 (3.1)–(3.5) and LF-RECONSTRUCTION III.8.1, which retain the physical $\nu_k$ term while the reference background is massless. The physical definition, on P7's actual action region $D_Z$ (including its half-star convention), is
$$\begin{aligned}
\phi^0(\psi)&:=\operatorname{bgField}(G,a,0,\operatorname{dataR}\psi),\\
F_0(\psi)&:=L^{-k(d-2)}A^*_{0}(D_Z;\psi,\phi^0(\psi)),\\
P_{\nu,h}(\psi)&:=\frac{\nu_k}{2L^{kd}}\sum_{x\in D_Z^{\rm sites}}|\phi^0_x(\psi)-h|^2,\\
F_{\rm ph}(\psi,h)&:=F_0(\psi)+P_{\nu,h}(\psi),\\
\rho_{k,0}^{\rm ph}(Z;\psi_k,h;u)&:=\mathbf1_{\{|u_z-\psi^0_k(z)|<C_6\beta_k^{-1/2}p_0,\ z\in Z_0\}}
\exp[-\beta_k F_{\rm ph}(\operatorname{merge}_{Z_0}(\psi_k,u),h)]. \tag{3.1}
\end{aligned}$$
If P7's `A*` places any action site outside `D_Z^{sites}`, its exact site set must replace that set in $P_{\nu,h}$; the coefficient $\nu_kL^{-kd}/2$ follows from $m_k=\nu_kL^{-2k}$ and the $L^{-k(d-2)}$ normalization. The star term is already in $F_0$ and is mass-independent. Formula (3.1) is a **PROVED definition-level correction** after identifying the action support; that support identification is a bounded Lean task, not a change of estimate.

Define $I_{\rm ph}:=\int\rho_{k,0}^{\rm ph}\,du$ and
$$\widetilde E_{0}^{\rm ph}:=\log I_{\rm ph}+\beta_kF_{\rm ph}(\psi^0_k,h)+\frac N2|Z_0|\log\beta_k. \tag{3.2}$$
The equality
$$I_{\rm ph}=\exp[-\beta_kF_{\rm ph}(\psi^0_k,h)-\tfrac N2|Z_0|\log\beta_k+\widetilde E_{0}^{\rm ph}] \tag{3.3}$$
is **PROVED CONDITIONAL ON** $I_{\rm ph}>0$; positivity follows on a nonempty cutoff from the positive real exponential, exactly as in `denominator_eq`. `R_normalization_of_indep` only requires an integrable positive common denominator, so its algebraic Fubini proof remains valid after replacing every occurrence of the old reference density by (3.1). This replacement is needed under A and A0′ alike.

One must **not** reuse `effAction_squeeze` verbatim: $\psi^0_k$ is stationary for $F_0$, but generally $DF_{\rm ph}(\psi^0_k)=DP_{\nu,h}(\psi^0_k)\ne0$. A precise bounded worker input is `physicalMassCoreVariation`: for $n=|Z_0|$, on the full cutoff ball and the P7 exterior-data tube,
$$\|DP_{\nu,h}(\psi^0_k)\|\le C_1\nu_k\sqrt n,\qquad
|D^2P_{\nu,h}(\psi)[v,v]|\le C_2\nu_k\|v\|^2, \tag{3.4}$$
with $C_1,C_2$ independent of the *size of $Z$*. They require a localized response of $\phi^0$ to perturbations in $Z_0$, including the action wall; the global bound $0\le P_{\nu,h}\le2\nu_k|D_Z|_k$ is insufficient because $|D_Z|_k$ need not be $O(D_0^d)$. The proof of (3.4) from BG Green decay is **OPEN**. It is shared by A and A0′.

Here is the changed **quadratic/Hessian sandwich, PROVED CONDITIONAL ON (3.4)**. Put $g_D=\operatorname{gaussConst}(d,D_0)$, $g_*=g_D-C_2\nu_k>0$, $H_*=2+C_2\nu_k$, $y=u-u_0$. The massless normalized effective action has Hessian between $g_D$ and $2$ by `DenominatorSqueeze.lean:effAction_squeeze` and `DenominatorHess.lean:effOn_hess_le`. Taylor's formula gives
$$\frac{g_*}{2}\|y\|^2-C_1\nu_k\sqrt n\|y\|
\le F_{\rm ph}(u_0+y,h)-F_{\rm ph}(u_0,h)
\le\frac{H_*}{2}\|y\|^2+C_1\nu_k\sqrt n\|y\|. \tag{3.5}$$
The **Hessian** itself lies in $[g_*,H_*]$; (3.5) retains the nonzero first derivative. With $t=\sqrt{\beta_k}y$, $\ell=C_1\sqrt n\,\sqrt{\beta_k}\nu_k\le C_1E\sqrt{n/\beta_k}$ and Young's inequality, (3.5) yields lower and upper bounds $g_*\|t\|^2/4-\ell^2/g_*$ and $H_*\|t\|^2+\ell^2/(2H_*)$ for $\beta_k(F_{\rm ph}-F_{\rm ph}(u_0))$. If $C_6p_0\ge1$, the coordinate cube $|t_{zi}|\le1/\sqrt N$ lies in the cutoff. The same Gaussian comparison as `Denominator.lean:denominator_eq` gives
$$\begin{aligned}
&n\bigl(N\log2-\tfrac N2\log N-H_*\bigr)-\frac{\ell^2}{2H_*}
\le \widetilde E_{0}^{\rm ph}\\
&\hspace{28mm}\le n\frac N2\log\frac{4\pi}{g_*}+\frac{\ell^2}{g_*}. \tag{3.6}
\end{aligned}$$
Here the upper Gaussian integral uses $g_*\|t\|^2/4$; the lower integral uses the stated coordinate cube. Consequently $|\widetilde E_{0}^{\rm ph}|\le C_{\widetilde E}^{\rm ph}D_0^d$, with for example
$$C_{\widetilde E}^{\rm ph}:=
\left|N\log2-\tfrac N2\log N-H_*\right|+\frac{C_1^2E^2}{2H_*\beta_k}
+\frac N2\left|\log\frac{4\pi}{g_*}\right|+\frac{C_1^2E^2}{g_*\beta_k}. \tag{3.7}$$
For a uniform constant replace $g_*$ by $g_D/2$, $H_*$ by $2+C_2E/\beta_{\min}$, and $1/\beta_k$ by $1/\beta_{\min}$ after choosing $C_2E/\beta_{\min}\le g_D/2$. The old `cTildeE` is **not** unchanged: its $g_D$ becomes $g_*$ in the Hessian, the massless critical-point argument gains the linear term, and the explicit majorant is (3.7). A direct P7 (3.3) expansion may give a sharper constant; (3.7) suffices for a bounded worker.

For $Q\in O(N)$, $F_{\rm ph}(Q\psi,Qh)=F_{\rm ph}(\psi,h)$ because the massless solver is equivariant and $|Q\phi-Qh|=|\phi-h|$. Rotating the integration variable proves $I_{\rm ph}(Q\psi_k,Qh)=I_{\rm ph}(\psi_k,h)$ and $\widetilde E_{0}^{\rm ph}(Q\psi_k,Qh)=\widetilde E_{0}^{\rm ph}(\psi_k,h)$. This is **PROVED CONDITIONAL ON** solver equivariance and the exact action support. The landed `tildeE0_rot` has no $h$ parameter and proves fixed-field rotation invariance; that statement is generally false for the physical density with fixed $h$. The correct statement is **joint** covariance.

The real proof of (3.3)–(3.7) does not establish the complex exterior-data analyticity required in P7 Lemma III.8.2. A precise remaining input is `physicalMassCoreVariationComplex`: after translating the moving cutoff to a fixed real core ball, analytically continue $P_{\nu,h}$ on the P7 exterior-data tube and bound $|\beta_k(P(u)-P(u_0))|\le\theta$ there. Also require a nonzero analytic massless integral $I_0$ and a uniform condition number $M_0:=\int_{\rm core}|w_0(u)|\,du/|I_0|$, where $w_0$ is the analytically continued massless integrand. If $(e^\theta-1)M_0<1$, then
$$\left|\frac{e^{\beta_kP(u_0)}I_{\rm ph}}{I_0}-1\right|\le(e^\theta-1)M_0<1,$$
so the physical integral is nonzero and its logarithm, hence (3.2), is analytic. This implication is **PROVED CONDITIONAL ON** those named inputs; the inputs are **OPEN**. On the real contour $M_0=1$ by positivity; on a complex tube one cannot silently use that value. The real bound (3.4) alone cannot justify the analytic logarithm.

## 4. Five-line close

1. **Hardest shared OPEN statement:** exact local, decaying assignment (1.2)–(1.3) for the *actual* complete SF exponent on a changing region, including P5 (1.8), $F$, $R$, and the composed backgrounds.
2. A adds the complete-to-massless regional conversion after that assignment; A0′ instead adds complete-action LF kernel and $R$ window estimates.
3. The physical reference denominator and its joint $O(N)$ statement are shared repairs; (3.4) and its complex version remain OPEN.
4. Neither P6 (4.32)–(4.34) nor P15 `expansion_326` alone supplies the shared assignment for the complete convention.
5. A0 remains ruled out; A0′ is adopted only after its factorization and estimates are proved, otherwise A stands.

## 5. Lean worker list

Each item is a module of about 300 lines or less; “proved” describes the mathematical derivation here, not an edit to the read-only Lean tree.

1. `regionalCorrSub` / `regionalMarkedSub` — **PROVED algebraically; Lean OPEN.** Split the centre and thick-support finsets and the absolutely convergent polymer sums to formalize (1.1); do the leading/marked $F$, $R$, vacuum, and half-star analogues. Input: `Def7v2Form.EresJ2`, `Def7v2Corr.corrSum`.
2. `assignLocalizedTerms` — **PROVED CONDITIONAL ON exact local expansions and support; Lean OPEN.** Give each localization label one deterministic owner, prove the disjoint partition and exponent/product identity (1.2), and retain boundary labels with full history dependence. No D7 estimate is asserted.
3. `hybridRegionalLocalization` — **OPEN.** Instantiate P5–P6 localization, LF-RECONSTRUCTION O-2′, FLUCTUATION Theorem 4.2/LOC/AE/GM in the complete background convention; prove (1.3), (S0), (S2), (S4), (S5). Under A, add the regional mass conversion after this shared module.
4. `rhoZeroPhysical` / `physicalMassActionSupport` — **PROVED at definition level conditional on actual P7 support; Lean OPEN.** Reuse `psiZero` as the massless centre, add the physical mass functional in (3.1), and prove positivity and integrability on the same cutoff.
5. `physicalMassCoreVariation` — **OPEN.** From BG localized Green response prove (3.4) including the half-star wall, with constants uniform in the size of $Z$ and in $k\le k_0$.
6. `denominatorPhysicalReal` — **PROVED CONDITIONAL ON item 5; Lean OPEN.** Combine massless Hessian bounds, Taylor, Young, `zeroDensity_bounds` style Gaussian/cube integration, and (3.6)–(3.7). Retain the linear term.
7. `denominatorPhysicalRot` / `R_normalizationPhysical` — **PROVED CONDITIONAL ON item 4 and positivity; Lean OPEN.** Rotate $(\psi,h,u)$ jointly, then reuse `R_normalization_of_indep` with the physical common denominator.
8. `denominatorPhysicalAnalytic` — **PROVED CONDITIONAL ON `physicalMassCoreVariationComplex`, a nonzero massless complex denominator, and $(e^\theta-1)M_0<1$; inputs OPEN.** Factor the centre value, bound the residual integral by $(e^\theta-1)M_0$, and choose its analytic logarithm.

## Source anchors

P5 (1.8)–(1.19), pp. 489–490; P6 §4, pp. 33–35, (4.32)–(4.34); P7 pp. 517–518, (3.1)–(3.5), and pp. 525–528, (3.20)–(3.26). LF-RECONSTRUCTION IV.1.1–IV.1.3 (LF-3/O-2′), III.8.1–III.8.4, III.10.3–III.10.4 (P15 `expansion_326`/`newBoundary`). Lean sources: `LargeField/Def7v2Form.lean`, `Def7SmallField.lean`, `Def7v2Corr.lean`, `Operators/Quiet.lean`, `Operators/StepData.lean`, `R/PsiZeroData.lean`, `R/RhoZero.lean`, `R/Denominator.lean`, `R/DenominatorRot.lean`, and `R/RopNorm.lean`.
