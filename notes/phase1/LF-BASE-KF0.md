# The hard-spin base step and the one-scale massive case

**Status (12 October 2026).** This is a source-bound proof audit and a set of exact reductions. It proves the chart and conditional-energy identities, a fixed-operator covariance estimate, a raw Peierls witness estimate, and the assembly of Root-F from stated one-scale analytic estimates. Part C checks the proposed extra-scale witness and identifies its mass-cap and horizon failures; A.5 checks the newly landed localization interface. This note does **not** prove Proposition II.7.9 or Root-F for the large-mass interval: the base covariance localization, the first small-field expectation, the needed remainder budget, and the normalized heavy-object estimate remain open below. In particular, none of the conditional statements in this note may be used as a provider of the frozen Lean theorem.

## Sources and contract

The exact target is `Balaban/Frozen/Roots/LogPartitionMultiscale.lean`, SHA-256 `21833bea3211257ac51d0879ef9f692acb0021fb04e792375cf5257104380e40`, read-only under `/home/scott/Balaban`. Its model is `Frozen/Model/{Energy,AprioriMeasure,PartitionFunction}.lean`: $H(\phi)=\frac12\sum_{x,\mu}|\phi_{x+e_\mu}-\phi_x|^2+\frac\nu2\sum_x|\phi_x-h|^2$, $|\phi_x|=|h|=1$, and the source is $+\sum_{x,i}g_i(x)\phi_i(x)$. The prior construction is `notes/phase1/LF-RECONSTRUCTION.md` §§II.7.3–II.7.5, IV.4.2, IV.5.2–IV.5.3, current SHA-256 `26b902a2bfd8f71c3e79ae32972c095f98efd29a60a4496840e0d6e3270eb101` (Part A/B were initially drafted against revision `be3e616a9a94b458d17a02606022fc7ce579b320b2ffaf8cb4a392757f52a0e6`); its audit is `LFR-PART4-AUDIT-astra.md`, findings P4-02, P4-03, P4-06. Paper keys are those of `review/SOURCES.md`: P4 (2.42)–(2.50), pp. 691–694, P5 Proposition 3.2, p. 517, P6 §4, and P7 (4.15)–(4.17), p. 533. P4 treats the first transformation in the whole-lattice small field; it does not state the large-field base case or the $k_f=0$ last step here. `GREEN.md` §4.4(ii), `LOCALIZATION.md` §3.4 (I-4c), `FLUCTUATION.md` §§2.4, 5.5, and `SMALLFIELD.md` §§3, 4–5 are paper-level reconstructions, with the statuses given in those notes.

The frozen quantifiers are $\exists\delta>0\;\forall\kappa>0\;\forall c_9>0\;\exists L\ge2,M\ge1,\beta_0\;\forall\beta\ge\beta_0\;\forall\nu\in(0,1]$. For $k_f=0$ the witness inequalities become $\sqrt\nu\le L$ and $1/2\le L\sqrt\nu$; the proposed regime $\nu>\frac78L^{-2}$ satisfies both. Only $j=1$ may be nonzero, and an allowed polymer $X$ is a connected union of complete blocks of side $ML$, containing the marked site $x$. Its size in the bound is exactly $n(X)=|X|/(ML)^d$. The required norm is the Euclidean norm on $\mathbb C^N$; the source domain is the open $\ell^1$ ball $\sum_{x,i}|g_i(x)|<1$.

## Part A. Proposition II.7.9

### A.1. Exact real chart, including measure and determinant

Let $D\subset\mathbb Z^d$ be the finite set of spins to be integrated at the first step. Fix exterior spins and real coarse data, and let $e_x\in S^{N-1}$ be the constrained small-field background at $x\in D$. Put $P_x=e_xe_x^{\mathsf T}$, $Q_x=I-P_x$, and $P=\oplus_xP_x$, $Q=I-P$. On the hemisphere $\phi_x\cdot e_x>0$, the unique coordinate is $\xi_x=Q_x\phi_x\in e_x^\perp$, $|\xi_x|<1$, with

$$\phi_x=e_x\sqrt{1-|\xi_x|^2}+\xi_x,\qquad d\sigma(\phi_x)=(1-|\xi_x|^2)^{-1/2}d^{N-1}\xi_x.\tag{A.1}$$

The inverse is $\phi\mapsto Q_x\phi$. The graph derivative is $a\mapsto a-e_x(\xi_x\cdot a)/\sqrt{1-|\xi_x|^2}$, so its Gram determinant is $1/(1-|\xi_x|^2)$ (one nontrivial eigenvalue, all others $1$). This proves (A.1) for the geometric surface measure. The identification of Mathlib's `toSphere` with this graph measure still needs its `toSphere_eq_graph` proof in Lean, as noted at LF-RECONSTRUCTION §IV.L Q2; the frozen measure is not declared to be a probability measure. The constant total sphere mass cancels only after taking $Z(g)/Z(0)$.

Set $m=(N-1)|D|$ and $v_x=\sqrt\beta\,\xi_x$. Then $w_x:=\phi_x-e_x=\beta^{-1/2}(v_x+z_x(v))$, where

$$z_x(v)=\sqrt\beta\big(\sqrt{1-\beta^{-1}|v_x|^2}-1\big)e_x,\quad |v_x|<\sqrt\beta,\quad J_\beta(v)=\prod_{x\in D}(1-\beta^{-1}|v_x|^2)^{-1/2}.\tag{A.2}$$

Suppose the real conditional action is $A(\phi)=\frac12\langle\phi,H_0\phi\rangle-\langle S,\phi\rangle+\text{constant}$, and $H_0e-S=-\alpha e$ is its constrained Euler–Lagrange equation. Then $2e_x\cdot w_x=-|w_x|^2$ gives the exact chord identity $A(\phi)-A(e)=\frac12\langle\phi-e,H(\phi-e)\rangle$ with $H=H_0+\operatorname{diag}\alpha$; this is LF-RECONSTRUCTION Lemma II.7.3. Assume $H$ is positive on the allowed fluctuations. Define $A_e=QHQ+P$ on $(\mathbb R^N)^D$ and $C_e=A_e^{-1}$. Its normal block is the identity and its tangent block is $QHQ$. If $\gamma_{N|D|}$ is standard Gaussian probability measure on the full real vector space, the following is an **exact** equality for every integrable real observable $F$ supported in the chart:

$$\begin{aligned}
&\int_{(S^{N-1})^D}F(\phi)e^{-\beta[A(\phi)-A(e)]}\prod_{x\in D}d\sigma(\phi_x)\\
&\quad=\beta^{-m/2}(2\pi)^{m/2}(\det C_e)^{1/2}
\int_{\mathbb R^{N|D|}}\mathbf1_{\{|v_x|<\sqrt\beta\ \forall x\}}J_\beta(v)
e^{-\langle v,Hz(v)\rangle-\frac12\langle z(v),Hz(v)\rangle}
F\big(e+\beta^{-1/2}(v+z(v))\big)\,d\gamma_{N|D|}(\psi),\quad v=QC_e^{1/2}\psi.
\end{aligned}\tag{A.3}$$

Indeed (A.1) and $\xi=\beta^{-1/2}v$ give $\beta^{-m/2}J_\beta(v)dv$ on the tangent space. Insert independent standard Gaussian normal coordinates, whose integral is $1$; this gives $\exp[-\langle u,A_eu\rangle/2]du$ for $u=v+Pu$. Change variables $u=C_e^{1/2}\psi$. The full Gaussian normalizer is $(2\pi)^{m/2}(\det C_e)^{1/2}$ because the normal block of $A_e$ has determinant $1$. Thus its logarithmic vacuum contribution is $\frac m2\log(2\pi/\beta)+\frac12\log\det C_e$, to be included in the base $b_0$, rather than silently discarded. Expanding $\langle v+z,H(v+z)\rangle/2$ gives the two displayed interaction terms. For variable $e_x$, the mixed term $\langle v,Hz(v)\rangle$ generally does not vanish. For the constant background $e_x=h$ and scalar $H=-\Delta+\nu$, tangent and normal sectors are orthogonal, so it does vanish. The source factor $\exp\sum g_x\cdot\phi_x$ and all **real** characteristic functions belong in $F$.

The local small-field indicators of LF-RECONSTRUCTION Lemma II.7.5 ensure $|\phi_x-e_x|\le1/4$ on the retained region, so (A.1) covers every retained spin. Formula (A.3) is finite-volume and exact; it is not yet a localization or cluster expansion.

### A.2. Replacement for Lemma II.7.4(c)

The real Gaussian identity of Lemma II.7.4(b), $\int_{e^\perp}f(\xi)d\xi=(s/2\pi)^{1/2}\int_{\mathbb R^N}f(Q_eu)e^{-s(e\cdot u)^2/2}du$, holds for real unit $e$ and integrable $f$. Its printed continuation for arbitrary Borel $f$ and complex $e$ is false (audit P4-02): $f(Q_eu)$ may be undefined, and the separated normal Gaussian can grow on the fixed real contour.

**Corrected II.7.4(c).** Fix a real background $e^0$ and a real fluctuation cutoff $D_\psi\subset\mathbb R^{N|D|}$ with $|\psi_x|\le p$ independent of the complex parameters. For complex $e$ near $e^0$, put $E=e/\sqrt{e\cdot e}$ with the branch equal to $1$ at $e^0$, and $Q_e=I-ee^{\mathsf T}/(e\cdot e)=I-EE^{\mathsf T}$; on the hard-spin background manifold $e\cdot e=1$ this is simply $E=e$. Let the *complete* integrand on $D_\psi$ be the analytic continuation of (A.3), with the determinant branch positive at $e^0$, these bilinear projections, the analytic square-root branch at $v=0$, the full quadratic factor, the chart Jacobian, and the source. Assume in a complex neighbourhood that $A_e$ is invertible, $\operatorname{Re}\langle u,A_eu\rangle\ge c|u|^2$ on the real contour, and $|\beta^{-1}v_x\cdot v_x|\le1/4$ on $D_\psi$. Then the integral over the **fixed real** $\psi$ contour of $\mathbf1_{D_\psi}$ times that complete integrand is holomorphic in $e$, the other complex background data, and $g$. Here $v\cdot v$ is bilinear, without complex conjugation. A real indicator that depends on the physical spin or on the background must first be eliminated on the chosen subdomain or retained solely as a fixed indicator of the real integration variables; it has no asserted complex continuation.

**Proof.** In finite dimension the matrix inverse, its principal square root and the determinant branch are holomorphic on a sufficiently small neighbourhood of $e^0$ with the stated spectral gap. The chart square root and $J_\beta$ are holomorphic because their arguments stay in a compact subset of the disc $|z|<1$. On the bounded $D_\psi$, every parameter derivative of the complete integrand is uniformly bounded by an integrable constant times the Gaussian density. Differentiation under the fixed real integral proves holomorphy. For an unbounded real contour the same argument requires a single integrable majorant for the *combined* quadratic exponent; the isolated normal identity supplies none. This corrected statement is deliberately about the actual bounded fluctuation integral, not arbitrary $f$. The passage from the original real indicators to fixed $D_\psi$ is a separate first-step lemma, using the analogue of FLUCTUATION Lemma 2.5.

### A.3. What follows from a fixed covariance and what does not

For the first-step background, GREEN §4.4(ii) and LF-RECONSTRUCTION Lemma II.7.3 claim that $H=G_\alpha^{-1}$ has range at most $L$ and that $A_e=QG_\alpha^{-1}Q+P$ has real part at least $\frac14L^{-2}$. These are paper-level inputs; I do not identify them with a landed Lean theorem. Given these claims, the following elementary fixed-operator estimate is proved.

**Lemma A.4 (fixed resolvent, inverse square root, logarithm).** Suppose $A$ is a finite matrix on a torus or Dirichlet set, $\operatorname{Re}\langle u,Au\rangle\ge a|u|^2$, $a>0$, $A_{xy}=0$ for $d(x,y)>R$, and the absolute row and column sums of $A$ are at most $J$. Choose $\theta>0$ with $J(e^{\theta R}-1)\le a/2$. Then, uniformly in $t\ge0$,

$$|(A+t)^{-1}_{xy}|\le(a/2+t)^{-1}e^{-\theta d(x,y)},\qquad |A^{-1/2}_{xy}|\le\sqrt{2/a}\,e^{-\theta d(x,y)}.\tag{A.4}$$

Also the off-diagonal entries of $\log A$ decay exponentially (with a constant depending on $a,J,R$), and all three matrix functions are analytic under small analytic perturbations preserving the gap.

**Proof.** Fix $y$ and conjugate by $W_x=e^{\theta d(x,y)}$. By the Schur bound, $\|WAW^{-1}-A\|\le J(e^{\theta R}-1)\le a/2$, so the conjugated $A+t$ has inverse norm at most $(a/2+t)^{-1}$. Its $(x,y)$ entry yields the first inequality. The Stieltjes formula $A^{-1/2}=\pi^{-1}\int_0^\infty t^{-1/2}(A+t)^{-1}dt$ gives the second because the scalar integral is $\pi\sqrt{2/a}$. For the logarithm use $\log A=\int_0^\infty[(1+t)^{-1}I-(A+t)^{-1}]dt$. Away from the diagonal, rewrite the integrand as $(1+t)^{-1}(A-I)(A+t)^{-1}$; its weighted kernel is bounded by a constant times $[(1+t)(a/2+t)]^{-1}e^{-\theta(d(x,y)-R)}$, which is integrable. The same formulas and local uniform domination prove analytic dependence. $\square$

For a complex nonnormal matrix the stated hypotheses include both absolute Schur sums; symmetry is not needed. For $A_e$ one may take $a=L^{-2}/4$ and the actual finite row bound $J(d,N,L)$, giving a positive rate $\theta_A$; summability of the kernel then gives the $\ell^\infty$ bound needed in FLUCTUATION Lemma 2.4(c). This proves decay and analyticity at the physical point $s=1$. Exponential decay is **not** exact localization: an entry of $A^{-1/2}$ generally reads coefficients everywhere. It does not imply the comparison and polydisc statements of LOC I-4c.

The needed first-step analogue of LOC I-4c is an explicit family $C^{(0)}_t(s)$ for cube-decoupling parameters $s$ on $|s_Q|<e^{\kappa_1}$, with (i) a uniformly accretive resolvent for every $t\ge0$; (ii) an integrable bound for $\int t^{-1/2}C^{(0)}_t(s)dt$ and the logarithm integral; (iii) holomorphy jointly in $s$ and the background; (iv) equality to $(QG_\alpha^{-1}Q+P)^{-1/2}$ and $\log(QG_\alpha^{-1}Q+P)$ at $s=1$; (v) exact equality of the local kernels when the decoupling parameters and input data agree on the thickened core; and (vi) exponential closeness to the physical kernels away from changed cubes, with constants uniform in torus and base record. These are the six parts of `LOCALIZATION.md` Theorem I-4c, §3.4, transported to the first-step operator. The landed `Localization/DecoupledX*.lean` files supply x-variant Green parametrices and bounds for their own multiscale operator, and `Multiscale/XVariantIdentities.lean` supplies `xVariant_constrained_reduction`; no landed declaration I found identifies their $C_t(s)$ with this particular $QG_\alpha^{-1}Q+P$ or proves (i)–(vi) for it. A source-level reuse requires that identification, the range and gap hypotheses on every local Dirichlet box, and the cutoff comparison on the exact first-step generating set. Merely citing LOC I-4c is not a proof of the analogue.

### A.4. The intended first-step expansion and its remaining estimates

The target Proposition II.7.9 is exactly LF-RECONSTRUCTION §II.7.5: for each base record, the result on $Z_1^c$ must have (D1) at scale $1$, Def-6 in regime (A) or (D2-flat) in regime (B), the real $\chi_1$, boundary terms $\mathcal B^{(1)}(X)$ at rate $\kappa_+=3\kappa/2$ with a constant $B_{\rm st}$ independent of the heavy budget, $\mathcal R_n^{(1)}=0$ for $n<m$, $|\mathcal R_m^{(1)}|\le\frac12\beta_1^{-m-1}$, and the first RG coefficients $(\beta_1,\nu_1,z_1,E_1)$ solving I-7. The base kernels $K_0(Z')$ and $b_0(Z')$ are the exact objects of Definition II.7.6, with the witness factorization (II.7.4) and real bound (II.7.5) from Lemmas II.7.7–II.7.8. Formula (A.3) supplies their missing chart-measure factor on the small-field sites; it does not establish (S1)–(S5) or the boundary split for those kernels.

If the analogue of LOC I-4c and the indicator-removal lemma above are proved, the interaction after $v=C^{(0)1/2}\psi$ has the chart terms $\log J_\beta$, $\langle v,Hz(v)\rangle$, $\langle z,Hz\rangle/2$, and in regime (A) the explicit $\nu$ variation. On $|\psi_x|<p_1(\beta)$, $z=O(\beta^{-1/2}|v|^2)$, so the local interaction is $O(\beta^{-1/2}p_1^3+\beta^{-1}p_1^4)$ per site, with fixed $L$ and the covariance sup norm included in the constant. Exact localization of $C^{1/2}(s)$ and $\log A(s)$ would produce P6 §4 local interactions, after which `Polymer/Mayer.lean` and `MayerPE.lean` can exponentiate an independently proved small activity bound. The marked expansion gives source terms. One must still prove the specific P6 (4.28), (4.43), (4.49), (4.51) type bounds on the first-step domain, with the boundary-hole compatibility and real indicators. `MayerPE.mayer_pe` accepts such bounds; it does not derive them from the chart.

Regime (A) uses $\nu$-free backgrounds and keeps $\frac{\beta\nu}{2}(|\phi-h|^2-|e-h|^2)$ as an explicit perturbation. Its I-7 equations are (E1-free)–(E3-free) in SMALLFIELD §3.7, not P4's complete-background equations. Regime (B) puts the field in the constrained minimizer and uses SMALLFIELD §3.4/P4 §5. For either convention, the three normalization equations remove the constant, radial/source, and transverse-gradient relevant coefficients of the new $\mathscr E^{(1)}$; the fourth (H.5) condition and the first-step field/source renormalization still require the localization and symmetry arguments in SMALLFIELD §4. The two systems cannot be interchanged by declaring their coefficients equal. The $\nu\downarrow0$ family limit belongs only to regime (A) and needs uniform domination after the corrected chart continuation.

**The half-budget is unresolved.** P5 Proposition 3.2, p. 517, prints a local bound $\frac12\beta_0^{-m-1}$ for its function (3.9). Proposition II.7.9 asks for $\frac12\beta_1^{-m-1}$; $\beta_1/\beta_0\asymp L^{d-2}>1$. The printed bound is weaker by a factor of order $L^{(d-2)(m+1)}$. P5 p. 516 says the whole function can be bounded by an arbitrary power of $\beta_0^{-1}$, but no checked source supplies the localized coefficient at the next-scale power for *all* domains, including whole-torus terms. Audit P4-04 also records this issue later in the flow. The required repair is a quantitative first-step localization of (3.9) with coefficient $\le\frac12\beta_1^{-m-1}$ uniformly in record, torus, domain and $g$; a bound only on differences near the large-field boundary does not suffice.

### A.5. Addendum: the landed I-4c covariance does not specialize to the base covariance

The Lean implementation of LOC Theorem I-4c for the **step covariance** is now present in `Balaban/Localization/DecoupledCov*.lean`. In particular `DecoupledIdentMain.decCov_one_eq` identifies its decoupled covariance at $s\equiv1$ with $(x+\mathcal A_k)^{-1}$; `DecoupledCovPrincipal.decCovSqrt_one_eq_sqrtMat` and `decLog_one_eq_logMat` identify the principal functions; `DecoupledCovAnalyticFull.analyticOnNhd_decCovSqrt_entry` and `analyticOnNhd_decLog_entry` give parameter analyticity; `DecoupledCovWeighted.I4c_close_sqrt_entry`, `I4c_close_log_entry`, and `DecoupledCovLocal.I4c_local_sqrt`, `I4c_local_log` supply comparison and locality. FLUCTUATION Lemma 2.4(d) identifies the ordinary $C^{(k)}$ with that step family at $s=1$.

This does **not** make the base $C^{(0)}$ of FLUCTUATION §5.5 an instance. The Lean `Localization.XSetting` used in the decoupled $x$-variant has the explicit field `hk : 1 ≤ k`, so setting the step index to $k=0$ fails a hypothesis before any estimate is used. More substantively, the operator identified by `decCov_one_eq` is the unit-lattice Schur complement
$$\mathcal A_k=a_k I+a_TL^{-2}P_{\rm block}-a_k^2L^{-2k}Q_k(G_{k,0}-\Pi_{k,0})Q_k^*,\tag{A.5}$$
as written in `Localization/DecoupledIdentMain.lean` (`covOp`). The hard-spin base operator is instead the **fine-site tangent Hessian**
$$H^{\rm base}_\perp=P_e^\perp G_\alpha^{-1}P_e^\perp+P_e,\qquad G_\alpha^{-1}=-\Delta+aL^{-2}Q^*Q+\nu+\alpha,\qquad C^{(0)}=(H^{\rm base}_\perp)^{-1}.\tag{A.6}$$
Here $P_e=e\otimes e$ is site-diagonal; $P_{\rm block}$ in (A.5) projects onto block constants, and $Q_k(G-\Pi)Q_k^*$ is absent from (A.6). Even if a one-layer level-zero generating set is constructed and the unit-lattice index is identified with fine sites, these formulas are not equal by specialization. GREEN §4.4(ii) supplies the real gap and finite-range/Combes–Thomas decay for (A.6); it does not identify its complex decoupling or local determinant expansion with (A.5).

The precise replacement obligation is a base-family $H^{\rm base}_\perp(s)$ obtained by decoupling the finite-range terms of $G_\alpha^{-1}$ and the site-diagonal tangent projection, together with: (i) the uniform accretive gap for complex $s$ in the LOC discs; (ii) weighted resolvent and differences under distant changes of $e,\alpha$; (iii) analytic principal square root and logarithm; (iv) exact agreement on cores and the torus lift, with the constants needed by FLUCTUATION Proposition 3.3 and Theorem 3.4. The generic principal-function arguments of `DecoupledCovPrincipal.lean` and the landed weighted/local proof patterns can be reused **after** the base-specific resolvent and comparison estimates are proved. This is a new identification and localization theorem, not a corollary of the current I-4c declarations. In the A-plan, A4–A5 remain open; their analytic matrix sublemmas are now landed for the step operator, but the base operator and its LOC hypotheses must be supplied.

## Part B. Root-F when $k_f=0$

### B.1. The boundary term that the earlier sketch loses

Let $G$ be any region whose spins are integrated and let $B=G^c$ carry fixed spins $q_y$. Write $\phi_x=h+w_x$ for $x\in G$ and keep each bond once. The exact conditional energy, up to a term involving only $q$, is

$$\begin{aligned}
H_G(\phi_G\mid q)
={}&\frac12\sum_{\substack{\{x,z\}\subset G\\x\sim z}}|w_x-w_z|^2
+\frac12\sum_{\substack{x\in G,\ y\in B\\x\sim y}}|w_x|^2
+\frac\nu2\sum_{x\in G}|w_x|^2\\
&+\sum_{\substack{x\in G,\ y\in B\\x\sim y}}(h-q_y)\cdot w_x
+\frac12\sum_{\substack{x\in G,\ y\in B\\x\sim y}}|h-q_y|^2.
\end{aligned}\tag{B.1}$$

This follows by expanding $|h+w_x-q_y|^2$ on every crossing bond. In the chart $w_x=\xi_x+[\sqrt{1-|\xi_x|^2}-1]h$, its linear tangent part is $-q_y\cdot\xi_x$. If $q_y$ has a nonzero component perpendicular to $h$, the derivative at $\xi=0$ is nonzero; therefore $h$ is not the conditional minimizer. The normal part $(1-h\cdot q_y)[\sqrt{1-|\xi_x|^2}-1]$ also survives. Proposition IV.4.3's existing route, LF-RECONSTRUCTION §IV.4.2(iii), omits these terms. This is the counterexample of audit P4-06.

There are two mathematically sound *forms* for a repair. One can retain the last two sums of (B.1) and the crossing-bond Boltzmann factor as a boundary activity attached to the bad-spin object; its support must contain both endpoints and its activity bound must be proved after normalization. Or one can first condition on a good collar whose outer boundary spins are within the $h$ chart, solve the massive constrained Euler–Lagrange equation in the remaining good region with those boundary data, and use (A.3) around that conditional solution. The bad core and collar are then one heavy object. Either route must keep the crossing bonds in the exact integral, including those to a spin designated large field. The second route cannot assert a small conditional background when its boundary data are arbitrary; the collar's real small-field condition is needed.

The full-torus reference is simpler. With no hole and $e_x=h$, $H=-\Delta+\nu$ is scalar in the spin indices, $P H Q=0$, and the exact chord energy is $H(\phi)=\frac12\langle\phi-h,(-\Delta+\nu)(\phi-h)\rangle$. In (A.3) the mixed chart term vanishes, while $\langle z,Hz\rangle/2$ and $\log J_\beta$ are even in the tangent Gaussian variable and start at order $\beta^{-1}$ on a fixed bounded fluctuation set. The tangent source has an order-$\beta^{-1/2}$ term, but its Gaussian expectation is zero by $v\mapsto-v$. This explains the expected $O(\beta^{-1})$ coefficient; it is not a volume-uniform cluster estimate for the actual model with holes.

### B.2. A uniform massive resolvent in the reference problem

For $\nu>\nu_*:=7/(8L^2)$ let $K_\nu=-\Delta+\nu$ on the torus or a Dirichlet region. Put

$$\theta_L=\log\left(1+\frac{7}{64dL^2}\right)>0.\tag{B.2}$$

Conjugation by $e^{\theta_Ld(x,y)}$ changes the nearest-neighbour matrix by operator norm at most $2d(e^{\theta_L}-1)=7/(32L^2)=\nu_*/4$. Thus $K_\nu+t$ stays accretive with real part at least $3\nu_*/4+t$, uniformly in volume, boundary shape, and $\nu\in(\nu_*,1]$. The proof of Lemma A.4 gives

$$|(K_\nu+t)^{-1}_{xy}|\le(3\nu_*/4+t)^{-1}e^{-\theta_Ld(x,y)},\quad |K_\nu^{-1/2}(x,y)|\le(3\nu_*/4)^{-1/2}e^{-\theta_Ld(x,y)}.\tag{B.3}$$

The rate in (B.2) is deliberately conservative; it is enough because $M$ is chosen after $L$ and $\kappa$. A positive mass also bounds the real conditional Hessian in a chart when its coefficient perturbation has norm below $\nu_*/4$. Such a perturbation bound depends on the collar and conditional-minimizer construction and is **not** implied by (B.3). The $O(L^{-1})$ mass decay stated in the old sketch is plausible but not needed for this fixed-operator estimate.

### B.3. What the energy alone pays for a bad cube

Choose a real threshold $r>0$. Suppose each declared bad cube has a witness: either a bond with $|\phi_x-\phi_y|\ge r$, or a site with $|\phi_x-h|\ge r/\sqrt\nu$. Suppose each bond or site can witness at most $D$ declared cubes; for a specified finite cube cover, $D$ is its actual maximum overlap number. For the simple partition into disjoint $s=ML$ blocks, if a cube tests its sites and all bonds touching it, one may take $D=2$: a site belongs to one block and a nearest-neighbour bond touches at most two. If there are $n$ bad cubes, then

$$H(\phi)\ge\frac{nr^2}{2D},\qquad e^{-\beta H(\phi)}\le e^{-\beta H(\phi)/2}\,e^{-\beta nr^2/(4D)}.\tag{B.4}$$

For each chosen witness its corresponding nonnegative term in $H$ is at least $r^2/2$. Summing the witness terms over cubes counts any energy term at most $D$ times, so $D H\ge nr^2/2$; split the exponent to get (B.4). With $D=2$ the last gain is $e^{-\beta nr^2/8}$. The one-block neighbourhood of $n$ bad blocks has at most $3^dn$ blocks, so its raw gain per block remains at least $\beta r^2/(8\cdot3^d)$. This is uniform in $\nu$ and uses the **full** energy, including crossing bonds. With $r=\delta_0=(\beta a)^{-1/2}p_0(\beta)$ and $p_0(\beta)=A_0(\log(\beta a))^{p_0}$ from LF-RECONSTRUCTION §IV.0, the gain per selected cube grows like $(\log\beta)^{2p_0}$. It is the raw analogue of Lemma II.7.8's bond and site witness factors.

Equation (B.4) does **not** imply the heavy activity bound needed by `GasOperator.gasOp_pe`. Dividing by the good-region partition function creates a ratio of fluctuation integrals, and the residual $e^{-\beta H/2}$ cannot be bounded by a product of locally normalized Gaussian factors without a hole/collar comparison. The crossing source in (B.1) can be of order $\beta$ before that comparison. A required theorem is, for every connected heavy object $Z$ with its chart-controlled collar and every $\|g\|_1<1$,

$$\int |\tau_Z(\Phi;g)|\,d\mu_{\rm ref}(\Phi)
\le \exp[-p_\beta-H_\beta|Z|_{\rm block}],\quad p_\beta\longrightarrow\infty,\quad H_\beta\longrightarrow\infty,\tag{B.5}$$

Here $\mu_{\rm ref}$ must be the product probability measure used by the gas, including the spins of the heavy object and the whitened good-region Gaussian variables. The support, compatibility, measurability and source analyticity must match `GasOperator.gasOp_activity_bound`/`gasOp_pe`. The activity $\tau_Z$ includes every crossing bond and the ratio of conditional to unrestricted good-region determinants. The constants must be uniform over the torus, $\nu\in(\nu_*,1]$ and heavy-object shape; a conditional variant may hold uniformly over **good** collar data, but no pointwise estimate for arbitrary fixed bad spins is asserted. Neither P4–P7 nor the cited phase-1 notes prove (B.5) for $k_f=0$. `Localization/Peierls.lean` proves the combinatorial sum once a charged-cube gain has been established; it cannot turn the raw pointwise inequality (B.4) into (B.5).

### B.4. The exact analytic input that would close the one-scale proof

Write $s=ML$ and let $\mathscr P_s(\ell)$ denote the connected unions of complete $s$-blocks in the torus. The missing one-scale theorem can be stated without referring to an RG iteration:

> **One-scale input (open).** For fixed $d,N,L,M,\kappa$ and $\nu\in(\nu_*,1]$, there is $B_\beta\to0$, uniform in $\ell$ divisible by $s$, $h$, $\nu$, and $\|g\|_1<1$, and functions $p_\ell(X;g)$ for $X\in\mathscr P_s(\ell)$ such that: (i) $p_\ell(X;\cdot)$ is holomorphic on the full open $\ell^1$ ball and reads only $g|_X$; (ii) $|p_\ell(X;g)|\le B_\beta e^{-\kappa n(X)}$ on that whole ball; (iii) the $p$ terms, extended by zero to all finite sets, agree under the precise non-winding torus embedding of Root-F, including agreement of polymer membership; and (iv) $Z(g)/Z(0)=\exp(\langle g,h\rangle+\sum_X[p_\ell(X;g)-p_\ell(X;0)])$.

The first proposed derivation is a massive chart expansion on the good region, including the conditional background or explicit boundary activity from (B.1), followed by the heavy-object estimate (B.5), `Polymer/MayerPE.lean` on the product Gaussian variables, `Polymer/GasOperator.lean` for the heavy objects, and `Polymer/BlockTorus.lean`/`FrozenTorus.lean` for exponentiation. If a hole is left unintegrated, the compatibility and Steiner-size estimates of `Polymer/Hole.lean` and `HoleOperator.lean` are needed. The exact-lift clause (iii) needs a **localized** walk or decoupling formula: the raw finite-torus covariance in (B.3) has winding contributions, so its entry on a small set is generally not identical between tori. `Polymer/BoxTransport.lean` transports local activities after that analytic locality has been proved.

**Conditional assembly lemma (proved).** The one-scale input with $4\sqrt N B_\beta\le c_9 L^{-((d-2)/2+\delta)}$ implies every $k_f=0$ clause of the frozen Root-F, with $T_\ell(j,x,X;g)=0$ unless $j=1$, $X\in\mathscr P_s(\ell)$ and $x\in X$, and otherwise

$$T_\ell(1,x,X;g)_i=\int_0^1\partial_{g_i(x)}p_\ell(X;t g)\,dt.\tag{B.6}$$

To prove it, the finite-dimensional chain rule gives $p_X(g)-p_X(0)=\sum_{x\in X,i}g_i(x)\int_0^1\partial_{g_i(x)}p_X(tg)dt$. Locality and holomorphy pass to (B.6); on any compact subset of the open ball differentiation under the $t$ integral is uniform. If $\|g\|_1\le1/2$, the coordinate Cauchy circle of radius $1/4$ about $tg$ stays inside the open ball. Therefore each component derivative has modulus at most $4B_\beta e^{-\kappa n(X)}$, giving $\|T\|\le4\sqrt N B_\beta e^{-\kappa n(X)}$. Since $X$ is a union of $s$-blocks, $n(X)=|X|/s^d$, exactly the frozen exponent. Clause (iii) passes to the derivative and then the $t$ integral; values at arbitrary source fields outside $X$ agree by locality.

For completeness, the principal complex logarithm in Root-F introduces no further small-field theorem. For $\|g\|_1<1$, the normalized positive Gibbs measure at $g=0$ gives $Z(g)/Z(0)=\mathbb E_0e^{\langle g,\phi\rangle}$. Since $|\operatorname{Im}\langle g,\phi\rangle|\le\|g\|_1<1<\pi/2$ and $\operatorname{Re}\langle g,\phi\rangle>-1$, the ratio has real part at least $e^{-1}\cos1>0$. Hence its principal log is analytic on the whole open ball. The exponent in input (iv) is another analytic logarithm of the same nonzero function; their difference is a continuous $2\pi i\mathbb Z$-valued function, zero at $g=0$, so they agree. This proves the exact log identity, with no branch change.

The conditional lemma is an assembly result, **not** a proof of the one-scale input. In particular, the already landed PE/GAS/Hole/Peierls theorems accept activity hypotheses; they do not prove the analytic and heavy estimates from the $O(N)$ model.

### B.5. Constants and quantifier order

The exponent can be fixed as $\delta=1/8$ before $\kappa,c_9$, as in LF-RECONSTRUCTION §IV.5.3. The global campaign must first choose an integer $L\ge3$ satisfying its other flow inequalities; the one-scale argument must then work for this same $L$. For the reference massive resolvent, (B.2) is an explicit rate. After $L$ and $\kappa$ are fixed, a sufficient **covariance-spacing target** is

$$M\ge\max\left\{1,\left\lceil\frac{4(\kappa+2)}{\theta_L L}\right\rceil\right\};\tag{B.7}$$

this makes $\theta_L ML\ge4(\kappa+2)$. Further lower bounds on $M$ imposed by the localized Gaussian and heavy-object geometry must be added before $\beta_0$ is selected. No value of those bounds is presently proved. Finally $\beta_0$ must make the chart radius $\sqrt{8/7}L\delta_0(\beta)\le1/4$, the first-step interaction and heavy-object hypotheses valid, and $4\sqrt N B_\beta\le c_9 L^{-((d-2)/2+1/8)}$ for all $\beta\ge\beta_0$. Equation (B.7) is **not** a complete choice of $M$ or $\beta_0$; assigning numerical values to the missing activity constants would invent a proof. This order matches the frozen binders and keeps $M,\beta_0$ independent of $\nu,h,\ell$.

## Part B′. Adversarial check of the proposed sitewise, one-scale route

This section tests the route in `followup1.txt` against the actual hard-spin integral and the hypotheses of the landed polymer theorems. The exact sector and walk identities below are useful. The proposed derivation of the one-scale input in B.4 does **not** follow from them: two required estimates are false in the proposed form, and two further localization estimates remain unproved. Consequently Part B′ does not turn the conditional assembly (B.6) into an unconditional proof of Root-F.

### B′.1. Exact sector identity and the boundary interaction

Fix a finite periodic torus $\Lambda$, $\nu_*:=7/(8L^2)<\nu\le1$, a unit $h$, and $0<r<1/2$. Write $S=\{x:|\phi_x-h|<r\}$ and $B=\Lambda\setminus S$. There is an exact disjoint partition of the real integration domain by these sets, up to null boundaries. On $S$, write $\phi_x=h+\xi_x+n_xh$, where $\xi_x\perp h$, $n_x=\sqrt{1-|\xi_x|^2}-1$. The exact chart domain is $\{\xi:2(1-\sqrt{1-|\xi|^2})<r^2\}$, equivalently $|\xi|<r\sqrt{1-r^2/4}$. Since $r<1/2$, this domain lies entirely in the upper hemisphere; the opposite hemisphere belongs to $B$. The spherical density is $(1-|\xi_x|^2)^{-1/2}d\xi_x/|\mathbb S^{N-1}|$ in the normalized surface measure convention of A.1.

Let $E(S)$ and $E(B)$ be the bonds with both endpoints in $S$ and $B$, respectively, and $\partial S$ those with one endpoint in $S$. With $K_S=-\Delta_S^{\rm free}+\nu I$, acting on each of the $N-1$ tangent components, the exact real energy is

$$\begin{aligned}H(\phi)={}&\tfrac12\langle\xi,K_S\xi\rangle
+\tfrac12\sum_{\{x,y\}\in E(S)}(n_x-n_y)^2
+\tfrac\nu2\sum_{x\in S}n_x^2\\
&+\tfrac12\sum_{\{x,y\}\in\partial S}|h+\xi_x+n_xh-\phi_y|^2
+\tfrac12\sum_{\{x,y\}\in E(B)}|\phi_x-\phi_y|^2
+\tfrac\nu2\sum_{y\in B}|\phi_y-h|^2.\tag{B′.1}
\end{aligned}$$

Indeed, on an internal good bond the tangent and normal components are orthogonal, and $|\phi_x-h|^2=|\xi_x|^2+n_x^2$; all remaining terms are literally those of the original energy. This proves that the crossing factors $\exp[-\beta|\phi_x-\phi_y|^2/2]$ lie in $(0,1]$. It does **not** remove the boundary source: for a fixed bad spin $q=\phi_y$, their exponent contains $-\beta q\cdot\xi_x$ after expansion. The global constant $h$ minimizes the unrestricted energy, but need not minimize the conditional energy on $S$ for fixed $q$. Keeping the full positive crossing energy is a legitimate exact splitting; a normalized polymer estimate for that splitting is still needed.

For a fixed $S$, the uncut tangent Gaussian normalization is
$$Z_{G,S}=\left(\frac{2\pi}{\beta}\right)^{(N-1)|S|/2}(\det K_S)^{-(N-1)/2}.\tag{B′.2}$$
The actual sector integral multiplies this by the real chart cutoff, the Jacobians, the three nonquadratic terms in (B′.1), the bad-spin integrals, and $\exp(\sum_xg_x\cdot\phi_x)$. The last factor is entire in the finitely many complex coordinates of $g$, and has modulus at most $e^{\|g\|_1}<e$ on the frozen open ball. Indicators remain functions of real spins. Dominated differentiation proves analyticity of the **complete fixed-sector integral**; it does not prove analyticity of a separately continued chart integral in a complex background $e$, the false assertion of P4 Lemma II.7.4(c) discussed in A.2.

### B′.2. The sitewise normalized estimate is false

The proposed comparison $\beta^{(N-1)/2}\exp(-\beta\nu r^2/2)$ uses a pointwise factor from the numerator and an unconditioned small-site Gaussian normalization from the denominator. These quantities belong to different conditional measures. Here is a direct counterexample to the required uniform sitewise estimate. Fix the $2d$ neighbours of $x$ to $-h$, and let $u=\phi_x\cdot h$. The conditional energy involving $x$ is
$$E_x(\phi_x)=\tfrac12\sum_{y\sim x}|\phi_x+h|^2+\tfrac\nu2|\phi_x-h|^2=(2d+\nu)+(2d-\nu)u.\tag{B′.3}$$
Because $d\ge3$ and $\nu\le1$, the unique conditional minimizer is $\phi_x=-h$. In particular $E_x(h)=4d$ and $E_x(-h)=2\nu$. For every fixed $0<r<1$, the conditional probability of $|\phi_x-h|\ge r$ tends to one as $\beta\to\infty$; this follows directly by Laplace concentration on the compact sphere, since the unique minimum lies in the interior of that bad event. Thus no uniform conditional penalty $\exp(-c\beta\nu r^2)$ per bad site can hold. A bounded source on the frozen $\ell^1$ ball does not change this conclusion.

The global pointwise inequality $H\ge\nu r^2|B|/2$ is true, and (B.4) gives a better witness version. Neither inequality compares the sector integral with its Gaussian reference after removing bad sites. The determinant $(\det K_S)^{-(N-1)/2}$, the shifted conditional good-spin integral, and bonds in $\partial S$ all vary with the shape and the prescribed bad spins. A valid replacement is the connected heavy-core/collar estimate (B.5), which charges **a connected object** while retaining every crossing bond and its conditional partition-function ratio. One may instead solve the conditional massive background problem and prove the same integrated bound around that background. `Localization/Peierls.lean` sums charged contours after such a normalized bound; its combinatorial conclusion cannot establish the bound.

### B′.3. The chart radius must shrink with temperature

Even in the all-good sector, a fixed chart radius does not give a perturbatively small local potential. Set $|\xi_x|=r/2$ at one site. Since $1-\sqrt{1-t}\ge t/2$ for $0\le t<1$, its normal mass term satisfies
$$\frac{\beta\nu}{2}n_x^2\ge\frac{\beta\nu r^4}{128}\ge\frac{7\beta r^4}{1024L^2}.\tag{B′.4}$$
For fixed $r,L$, this diverges with $\beta$. The chart interaction $H_t$ required by `Polymer/Mayer.mayer_activity_bound` therefore fails the uniform pointwise hypothesis $|H_t|\le H_0e^{-(\kappa_0+\kappa_1)d(\operatorname{supp}t)}$ with $H_0\le\log2$. Writing $e^{-H_t}-1$ instead does not make it small: at that configuration it approaches $-1$. The hard cutoff also cannot be inserted as the logarithm of a bounded local interaction.

A mathematically consistent cutoff scale is $r_\beta=A\log(\beta a)/\sqrt\beta$ with fixed $a>1$ and $A>0$, once $\beta$ is large enough that $r_\beta<1/4$. For $|\xi_x|\le r_\beta$, $|n_x|\le|\xi_x|^2$, so the normal-bond and normal-mass terms in (B′.1) are bounded, sitewise, by $C(d)\beta r_\beta^4=O_{d,A}(\log^4(\beta a)/\beta)$; the logarithmic Jacobian is $O_A(\log^2(\beta a)/\beta)$. A bad site has raw mass energy at least $\beta\nu r_\beta^2/2\ge 7A^2\log^2(\beta a)/(16L^2)$. This is a superpolynomial raw weight, not $e^{-c\beta}$, and B′.2 still prevents promoting it to a uniform normalized sitewise weight. On the shrinking chart the Gaussian tail, cutoff removal, boundary-source treatment, and heavy-object normalization must be proved together.

### B′.4. Exact massive walk identities and their limit

For each $S$, let $d_S(x)$ be the number of neighbours of $x$ in $S$, $D_S(x)=\nu+d_S(x)$, $A_S$ the adjacency matrix, and $T_S=D_S^{-1}A_S$. Then $K_S=D_S(I-T_S)$. Set $q_L:=2d/(2d+\nu_*)<1$. Every row sum of $T_S$ is at most $q_L$: $d_S(x)/(d_S(x)+\nu)$ is increasing in $d_S(x)$ and is at most $2d/(2d+\nu_*)$. The nonnegative walk series converge absolutely and uniformly in $S,\ell,\nu$:
$$K_S^{-1}=\sum_{n\ge0}T_S^nD_S^{-1},\qquad
\log\det K_S=\sum_{x\in S}\log D_S(x)-\sum_{n\ge1}\frac{\operatorname{tr}(T_S^n)}{n}.\tag{B′.5}$$
The second identity follows from the power series for $\log\det(I-T_S)$, since the spectral radius is below one. If $m=d_S(x,y)$ is graph distance within $S$, terms of length below $m$ vanish. Consequently
$$0\le K_S^{-1}(x,y)\le\frac{q_L^m}{\nu_*(1-q_L)},\qquad
\sum_{n\ge1}\frac{|\operatorname{tr}(T_S^n)|}{n}\le |S|[-\log(1-q_L)].\tag{B′.6}$$
The harmless first constant can be sharpened; it is chosen uniform in all sets $S$. The Stieltjes formula $K_S^{-1/2}=\pi^{-1}\int_0^\infty t^{-1/2}(K_S+tI)^{-1}dt$ and the same walks with $\nu$ replaced by $\nu+t$ show $|K_S^{-1/2}(x,y)|\le C(d,L)q_L^m$, with $C(d,L)<\infty$ given by the resulting one-dimensional integral. These are valid massive estimates, including for disconnected $S$ (cross-component entries vanish).

Two locality details defeat the proposed immediate polymer conclusion. First, even the length-zero term $D_S(x)^{-1}$ depends on which neighbours of $x$ belong to $S$; a walk activity must carry the one-step occupancy halo of every visited vertex. Second, (B′.5) has **infinite** walk sums even on a finite torus; only each individual walk has finite support. A candidate for exact torus independence would group walks and their occupancy halos by a lifted finite support and assign winding walks to winding supports. This grouping, its absolute convergence after all interactions and sector summations, and the exact identification of lifted polymer membership remain to be proved. Mere exponential closeness of two finite-torus Green functions does not give Root-F's equality clause.

There is also a geometric error in the suggested $e^{-c_LML}$ **per-block** bound. A walk whose endpoints are separated by one full block width may have length at least $ML$, giving such a distance factor. A walk can enter an adjacent $ML$-block through one edge; thus visiting two blocks need not cost even two steps, much less $ML$ steps per block. In larger clusters the minimum length depends on the shape and cannot be replaced by $ML$ times the number of blocks without a separate geometric lemma. Consequently (B′.6) alone does not give arbitrary prescribed $\kappa$ per block. That requires a small-activity and support-counting estimate, possibly after allocating interactions to cores and collars. The spacing target (B.7) controls widely separated pieces only; it does not solve adjacent-block entropy.

### B′.5. Where the landed theorems apply

`Polymer/Mayer.mayer_integral_eq` starts from a **product probability measure** and bounded, measurable interactions $H_t$ with finite `DepOn` supports. `mayer_activity_bound` additionally asks $H_0\le\log2$, pointwise exponential support decay, the geometry and entropy hypotheses (G1)–(G3), and $2H_0K_0e^{\kappa_1c}c_1\le1/2$. `MayerPE.mayer_pe` adds the PE summability and exponent inequalities. The Gaussian in (B′.2) is correlated, so these declarations cannot be applied directly. Whitening $\xi=\beta^{-1/2}K_S^{-1/2}\psi$ gives a product Gaussian in $\psi$, but each $\xi_x$ reads arbitrarily distant $\psi_y$ by (B′.5), and its real cutoff is no longer a finite `DepOn` event. The fact that matrix entries decay does not meet the exact support hypothesis.

`Polymer/GasOperator.gasOp_pe` requires the integrated heavy estimate $\int|\tau_z|\,d\mu\le e^{-p-h|Z|}$ against its product reference measure, as well as pointwise bounded ordinary activities, exact support, entropy/counting, and a collection of explicit inequalities between $p,h$ and the polymer rates. The raw energy estimate is not that integrated hypothesis. `Polymer/BlockTorus.pe_blockTorus` and `FrozenTorus.pe_blockTorus_frozen` start with already constructed activities $|K(X)|\le\varepsilon e^{-\kappa|X|_{\rm block}}$ and explicit convergence inequalities. `Polymer/Holomorphic.pe_PY_analyticOnNhd` propagates analyticity once analytic activities and uniform KP bounds are given. `Polymer/KP.lean` supplies summability for an activity satisfying its KP condition. `Polymer/BoxTransport.frozenPY_boxMap` transports exactly equal local activities; it cannot manufacture equality from Green-function decay. These theorem hypotheses are the precise point at which the proposed direct invocation stops.

One repair is to prove a new **Gaussian-with-holes localization theorem** for (B′.1): decouple or expand $K_S^{-1/2}$ into finite-support terms including their occupancy halos; treat the shrinking real indicators within the real integrals; bound the resulting ordinary activities, their support entropy, and source derivatives uniformly on the open $\ell^1$ ball. A second theorem must prove (B.5) for connected bad cores and their collars with the crossing energies retained and with the determinant/conditional-integral ratio included. Only after these two results is it legitimate to instantiate `mayer_pe`, `gasOp_pe`, `pe_blockTorus_frozen`, `pe_PY_analyticOnNhd`, and `frozenPY_boxMap` to derive B.4. The present sources and landed Lean declarations do not furnish those two theorems. This is a specified proof obligation, not a proved one-scale expansion.

### B′.6. Constants and Lean dependency plan

The frozen binder order is: choose $\delta=1/8>0$; then receive arbitrary $\kappa,c_9>0$; then choose the common campaign integer $L\ge3$ and $M\ge1$; finally choose $\beta_0$, uniformly for all $\beta\ge\beta_0$, $\nu\in(\nu_*,1]$, unit $h$, and admissible tori. In the $k_f=0$ branch one chooses $k_f=0$ because $\sqrt\nu\le1\le L$ and $L\sqrt\nu>\sqrt{7/8}>1/2$. After $L$ is fixed, $q_L$ is as in B′.4. After $M$ is fixed, choose $A,a$ for the shrinking chart and make $\beta_0$ large enough for $r_\beta<1/4$, the desired ordinary and heavy activity inequalities, and $4\sqrt N B_\beta\le c_9L^{-((d-2)/2+\delta)}$. The last two requirements have no proved threshold, so a numerical $M$ or $\beta_0$ meeting every condition cannot be stated. Formula (B.7) is only a distance-spacing target and must not be presented as a complete selection.

| Order | Lean lemma or group | Estimated lines | Landed reuse and remaining work |
|---|---|---:|---|
| B′1 | `kf0_mass_range`, `siteSector_partition`, exact chart Jacobian and `(B′.1)` | 800–1,600 | `Frozen/Model/Energy`; chart measure from A1 |
| B′2 | `fixedBadNeighbor_counterexample`, shrinking-radius estimates and source domination | 700–1,300 | elementary sphere concentration and `Frozen/Model/PartitionFunction`; new |
| B′3 | `freeHoleWalk_inverse`, `freeHoleWalk_logdet`, square-root decay, halo support | 1,500–3,000 | finite matrix lemmas, `Green/OneScaleDecay.lean`; support decomposition new |
| B′4 | `kf0_gaussianWithHoles_local` with exact lift, cutoff and uniform small ordinary activities | 5,000–10,000 | `Localization/DecoupledX*.lean`, `Mayer.mayer_integral_eq`; **open** |
| B′5 | `kf0_connectedHeavy_bound` proving (B.5), including crossing bonds and normalized determinants | 5,000–10,000 | `Localization/Peierls.lean`, `Polymer/HoleOperator.lean`; **open** |
| B′6 | `kf0_mayer_gas_pe` checking (G1)–(G3), KP, PE and source analyticity | 2,500–5,000 | `MayerPE.mayer_pe`, `GasOperator.gasOp_pe`, `KP.lean`, `Holomorphic.pe_PY_analyticOnNhd`; depends on B′4–5 |
| B′7 | `kf0_exactTorusLift`, `kf0_to_rootF` with (B.6) and principal log | 1,500–3,000 | `FrozenTorus.pe_blockTorus_frozen`, `BoxTransport.frozenPY_boxMap`; depends on B′4–6 |

**Status and confidence.** Equations (B′.1)–(B′.6), the conditional counterexample, and the failure of the direct theorem instantiations are high confidence. The proposed repair is mathematically specific but lacks the two stated model estimates. Thus the one-scale input (B.4), the heavy-object bound (B.5), and the unconditional $k_f=0$ branch of Root-F remain open here.

## Part C. Can the frozen witness use one extra scale?

### C.1. The numerical witness works, but it changes the flow

Keep the two indices distinct. In LF-RECONSTRUCTION (I.1), $\hat k_f(\nu)=\min\{k:\nu L^{2k+2}\ge1\}$ is an a priori horizon. The **running stopping index** in §I.1.1 and §IV.4 is $k_f^{\rm run}=\min\{k:\nu_k>\frac78L^{-2}\}$. On the interval $\nu\in(\frac78L^{-2},1]$ the latter equals zero. The former is $0$ when $\nu\ge L^{-2}$ and $1$ when $\frac78L^{-2}<\nu<L^{-2}$.

The frozen Root-F theorem does not say that its existential witness must equal either of these indices. For every $\nu$ in the interval, $k_f^{\rm wit}:=\max(\hat k_f,1)=1$ satisfies its two numerical conditions:
$$L^{k_f^{\rm wit}}\sqrt\nu=L\sqrt\nu\le L,\qquad
L^{k_f^{\rm wit}+1}\sqrt\nu=L^2\sqrt\nu>L\sqrt{7/8}>1/2.\tag{C.1}$$
It asks for $T_1,T_2$ on tori with $ML^2\mid\ell$. This divisibility implies the reconstruction's $ML^{\hat k_f+1}\mid\ell$, including when $\hat k_f=0$. Thus the witness and torus arithmetic present no obstruction. They do **not** turn the running stopping index into one: applying the base map $0\to1$ would deliberately continue beyond the prescribed stop.

For sufficiently large $\beta_0$ (take $\beta_0>8L^2/7$), $\beta\nu>1$ throughout this interval. D-IV.11 therefore sets the a priori regime index $k_0=0$ by convention. The algebraic base operation would be the regime-(B) complete-background operation of II.7.1; no $\nu$-free or two-step switch is called for. However the **stated** Proposition II.7.9 and Theorem II.7.10 are assumed under $k_f^{\rm run}\ge1$. Their proof of the target class uses that assumption quantitatively, so they are not an already available theorem for this interval.

### C.2. The mass cap is a genuine failed hypothesis

The running mass after the proposed extra step is $\nu_1=\nu L^2\delta_1$, with $|\log\delta_1|\le\epsilon\le1/20$ in the perturbative flow (LF-RECONSTRUCTION (I.2)). At $\nu=1$ this would give
$$\nu_1\ge e^{-1/20}L^2>1.\tag{C.2}$$
For $L\ge3$ it is far outside the class $\mathrm{IsRep}^{\flat}_1$: its clause (D9$^\flat$) **requires** $0<\nu_1\le1$ (§II.6.3). The proof of LF-6, Theorem II.7.10, checks that clause using $k_f^{\rm run}\ge1$, which forces $\nu\le\frac78L^{-2}$ and hence $\nu_1\le\frac78e^{2\epsilon}<1$ (the displayed (D9)/(D9$^\flat$) check at the end of its proof). That line has no analogue at $\nu=1$. The same upper cap enters BG Theorem 5.2 through $0\le\mu\le L^{-2k}$, equivalently dimensionless mass $\mu L^{2k}\le1$, and its complex data domain; LF-RECONSTRUCTION Definition II.3.5 builds the H7 domains from that BG domain. Enlarging the final Gaussian gap does not extend those analytic background statements or preserve their fixed $\varepsilon_j$ domains.

There is a separate bookkeeping obstruction on $\nu\ge L^{-2}$. Then $\hat k_f=0$, whereas the abstract LF-2/Theorem I.5.4 has the typing range $k_0\le K\le\hat k_f$ (§I.5.2). Obtaining the heavy-object invariant at the proposed scale $K=1$ would violate $1\le0$. LF-6 uses LF-2(ii) with $k_0=0$ for its (H6$^\flat$) base budget, so that invocation cannot simply be repeated with the old horizon. One could define a new horizon $\max(\hat k_f,1)$ and reprove the bookkeeping and its locality/torus hypotheses; this has not been done in the cited results.

These are failures of the **available theorem hypotheses**, not a counterexample to Root-F. For the narrow subinterval $\frac78L^{-2}<\nu<L^{-2}$ the old horizon is one, but $\nu_1$ can still exceed one near its upper endpoint because $\delta_1$ need not be at most one. Even where a particular $\nu_1\le1$ happens to hold, Proposition II.7.9 is stated only for $k_f^{\rm run}\ge1$ and its application beyond the stop needs a separate proof. Thus the required base case is the same kind of $k=0$ integral, but it is **not exactly the already stated base-step theorem**.

### C.3. Audit of the proposed use of LF-8 at $k=1$

P7 §4, pp. 529–533, does the final integral for the flow's last $k=k_f^{\rm run}\ge1$ and uses the lower bound $\nu_k>\frac78L^{-2}$ in its massive variational problem (4.3)–(4.5). LF-RECONSTRUCTION §IV.4 states Theorem IV.4.1 with input $\mathrm{IsRep}^{\flat}_k$, and Lemma IV.4.2 with the frozen heavy threshold $\frac12p_2(\beta_{k_0})$. The input class forces $\nu_k\le1$; §II.6.3 proves preservation only while $k<k_f^{\rm run}$. Hence P7's lower-mass sentence does not imply the **upper-mass extension** of Theorem IV.4.1 to $\nu_1\in(7/8,L^2e^\epsilon]$. P9 p. 515 describes the last covariance as massive with mass of its stopping-scale order, and its (4.7)–(4.9) are observable identities after that last integral; they give no high-mass extension.

For the scalar reference $(-\Delta+m)^{-1}$, increasing $m$ improves the resolvent norm and the random-walk decay rate. The actual final calculation also uses the complete constrained background, its complex H7 domain, local covariance square root and determinant, characteristic functions, and the integration/renormalization bounds of P7 (4.1)–(4.9). Their constants and admissible data are controlled in the cited $\nu_k\le1$ class. The scalar monotonicity proves none of those upper-mass claims.

The remaining checks separate arithmetic from the missing analysis:

| Item | What follows for the artificial $k=1$ endpoint | Missing hypothesis |
|---|---|---|
| Massive gap | Granting the usual recursion, $\nu_1>(7/8)e^{-\epsilon}$; the scalar Gaussian is massive. | Uniform complex-background, covariance, determinant and H7 estimates for $\nu_1$ up to $L^2e^\epsilon$. |
| Frozen threshold | With $k_0=0$, $p_2(\beta_{k_0})=p_2(\beta)$ grows faster than $\log\beta_1$; the logarithmic comparison in (Λ31) is arithmetically viable. | Lemma IV.4.2's (H6$^\flat$) input at $K=1$ when $\hat k_f=0$, and the corresponding normalized heavy operator estimate. |
| H7 and $\varepsilon_j$ | The prescribed $j=1$ radii are unchanged by renaming the Root-F witness. | BG/Def-6/Def-7 analyticity and domain inclusions above the dimensionless mass cap one. |
| Root-F bound | If the usual H7 and last-step activities held at $j=1,2$, the $\delta=1/8$ and Cauchy/regrouping arithmetic of IV.5.3 item 5 would give $c_9L^{-j((d-2)/2+\delta)}e^{-\kappa|X|/(ML^j)^d}$; for the remainder $2(d-2)\ge2((d-2)/2+1/8)$ when $d\ge3$. | Those uniform activities and derivative bounds in the enlarged mass range. |
| Torus agreement | $ML^2\mid\ell$ is sufficient for every index-0 or index-1 construction already defined on an admissible torus. | The extra-step data and last-step activities must satisfy exact D-IV.9/PE transport on both tori. |

The constant order can remain the frozen one: $\delta=1/8$; then arbitrary $\kappa,c_9>0$; then $L,M$ as in LF-RECONSTRUCTION §I.1.3; finally $\beta_0$ enlarged to force $\beta\nu>1$ and the existing (Λ30)–(Λ32) inequalities. This order has no numerical conflict. It does not provide thresholds for the absent high-mass analytic and bookkeeping estimates.

### C.4. Conditional assembly after genuine extensions

There is a precise conditional statement, but its premises are **stronger** than the named Proposition II.7.9 and Theorem IV.4.1. Suppose an extended base theorem on $\nu\in(7/(8L^2),1]$ produces a torus-coherent $\rho_1$ with $\int\rho_1=Z(g)$, the full (D1) representation and H7 bounds at $j=1$, complete-background analytic data up to $\nu_1\le L^2e^\epsilon$, the half-budget for $\mathcal R_m^{(1)}$, and the frozen (H6$^\flat$) heavy threshold at scale one even when $\hat k_f=0$. Suppose an extended LF-8 theorem accepts exactly that input at $k=1$ and proves IV.4.2 and IV.4.1, with bounds and torus-coherent localized activities uniform over the same enlarged mass range. These are two new theorems, not established consequences of the current ones.

Under those two premises, Root-F on this interval follows with $k_f^{\rm wit}=1$. Define $T_1(x,X;g)=\mathscr M^{(1)}(x,X;h,h,g)$ on scale-one polymers, and define $T_2$ as in LF-RECONSTRUCTION Definition IV.5.2: $\mathscr M^{(2)}_0$ plus the line-integral source derivatives of the localized $\mathcal R^{(2)}_n$ and $\mathcal P^{(2)}$, grouped by their scale-two block hull. Extend by zero off the supported indices, points and polymers and on non-admissible tori. This gives frozen locality and dependence only on $g|_X$. H7 plus the uniform Cauchy bound for the line-integral derivatives gives analyticity on $\|g\|_1<1$ and the scale-one/two bounds exactly as in IV.5.3 item 5, with $\beta_0$ large enough for its (Λ32) coefficient. The extended LF-8 identity (IV.4.3), the source-increment formula, and the principal-log argument of B.4 give the frozen log identity for every $\|g\|_1<1$. Exact D-IV.9 locality and PE transport give the frozen equality between tori for finite sets in the $\ell/4$ boxes. This verifies every Root-F clause **conditional on the extended interfaces**. It cannot be labelled a theorem conditional only on the currently stated II.7.9 and LF-8.

Accordingly, the amended IV.5.1(a) choice $k_f^{\rm wit}=\max(\hat k_f,1)$ is valid as a statement about the two *numbers* in Root-F, but cannot replace the operative choice in IV.5.3 until the extended base, horizon budget and high-mass LF-8 are proved. This shortcut presently does not remove P4-06.

### C.5. Lean plan and confidence

| Order | Proposed Lean declaration | Estimated lines | Existing theorem or open extension |
|---|---|---:|---|
| C1 | `kfWitness_one_of_mass_gt`, `hatKf_le_one`, `kf0_regimeIndex_zero`, torus divisor | 150–350 | Frozen Root-F binders; elementary arithmetic |
| C2 | `massAtOne_exceeds_one` at $\nu=1$ from the perturbative recursion; show old `IsRepFlat₁` cannot be constructed with (D9$^\flat$) | 200–450 | LF-RECONSTRUCTION (I.2), Def-7; diagnostic |
| C3 | `baseCovOp`, `baseCovDecoupled` and LOC I-4c-style bounds for (A.6) | 3,000–6,000 | `Green` gap/decay; reuse generic `DecoupledCovPrincipal`; **open** |
| C4 | `lf6_highMass` with a new admissible complete-background domain and frozen budget at horizon one | 6,000–12,000 | II.7.9/II.7.10 pattern, LF-2 geometry; **open** |
| C5 | `lf8_highMass_one` including H7, frozen $p_2(\beta)$, GAS/PE and exact torus lift | 6,000–12,000 | IV.4.1/IV.4.2 pattern and landed polymer theorems; **open** |
| C6 | `rootF_one_of_extended_base_final` with the two supported scales | 500–900 | IV.5.2/IV.5.3 assembly, B.4 principal log; conditional on C4–C5 |

Confidence is high in (C.1), the mass-cap and horizon failures, and the distinction between the two covariances in A.5. The high-mass extension itself is unproved. The extra-step choice is therefore an algebraic option for the frozen existential statement, not an available proof of its large-mass branch.

## Lean plan, in dependency order

Sizes are estimates in lines of Lean, not proof-status claims. The provider modules listed below must live below the frozen anchor and must not import its `by sorry` proof. No file under `/home/scott/Balaban` was edited for this note.

| Order | Proposed lemma or group | Estimated size | Landed reuse / unproved premise |
|---|---|---:|---|
| A1 | `toSphere_eq_graph`, hemisphere inverse, Jacobian, real Gaussian normal disintegration | 800–1,500 | Mathlib `HaarToSphere`; LF-RECONSTRUCTION Q2 is still open |
| A2 | `hardSpin_chord_identity`, chart energy and exact determinant formula (A.3) on a finite region | 900–1,800 | `Frozen/Model/Energy`, `Background` Euler–Lagrange identities; first-step normalization new |
| A3 | `chartCompleteIntegrand_analytic` with fixed real cutoff and real-data identification | 900–1,600 | Mathlib matrix holomorphy and dominated integral; no continuation of indicators |
| A4 | `baseCovariance_gap`, weighted resolvent, square root, logarithm | 1,500–3,000 | `Green/CauchyInverse.lean`, `Multiscale/XVariantIdentities.lean`; need the exact base operator and gap |
| A5 | `baseCovariance_decoupled` with LOC I-4c (i)–(vi) and torus-family comparison | 4,000–8,000 | `Localization/DecoupledX*.lean`, `DecoupledMain.lean`, `XCommutator.lean`; identification and bounds new |
| A6 | Real indicator elimination, base local interactions, hole-aware first expectation and boundary split | 5,000–10,000 | `Polymer/Mayer.lean`, `MayerPE.lean`, `MayerMarked.lean`, `HoleOperator.lean`; P6 §4 hypotheses new |
| A7 | Regime (A) free and regime (B) complete RG equations, first (H.5), $\nu\downarrow0$ family limit | 4,000–8,000 | `Flow/RGEquations.lean`, `RGParam.lean`, `RGInfty.lean`; data estimates and free-system identification new |
| A8 | Strengthened localized P5 Proposition 3.2 remainder, $\frac12\beta_1^{-m-1}$ for all domains; `lf_base` assembly | 3,000–6,000 | P5 pp. 516–517; not furnished by the printed proposition |
| B1 | `conditional_crossing_energy`, real witness allocation (B.4), collar geometry | 1,500–3,000 | `Frozen/Model/Energy`, `Localization/Peierls.lean` for later counting |
| B2 | Massive conditional background and chart/Hessian bounds, or an explicit crossing-bond activity construction | 5,000–10,000 | `Background/Contraction*.lean`, `Green/OneScaleDecay.lean`; boundary data premise must be proved |
| B3 | Normalized heavy activity (B.5), uniform small-field local activities, analytic source and exact torus lift | 8,000–15,000 | `Polymer/GasOperator.lean`, `HoleOperator.lean`, `MayerPE.lean`, `BoxTransport.lean`; these are the main missing model estimates |
| B4 | One-scale input, `kf0_to_rootF` via (B.6), principal-log and frozen torus agreement | 1,500–3,000 | `Polymer/BlockTorus.lean`, `FrozenTorus.lean`, `Holomorphic.lean`, `BoxTransport.lean`; requires B3 |

## Open items and confidence

1. **A: localization.** Prove the first-step $C^{(0)}$ analogue of LOC I-4c with complex decoupling discs, exact core comparison, and the fixed real cutoff. Lemma A.4 supplies only the physical fixed covariance.
2. **A: expectation and RG.** Derive the P6 §4 bounds from the chart on each base record, then verify both different RG systems and (H.5), including the $\nu\downarrow0$ family clause. The quoted P5 Proposition 3.2 does not supply the requested half-budget.
3. **B: crossing bonds and heavy objects.** Prove (B.5) with the full crossing activity (B.1) or with a collar-controlled conditional minimizer. The raw energy gain (B.4) is insufficient after normalization.
4. **B: locality and torus agreement.** Construct local activities whose coefficients are *exactly* independent of the torus on non-winding supports, not merely exponentially close. Then verify the uniform $B_\beta$ required in B.4 and the remaining $M,\beta_0$ inequalities.

Confidence is high in the elementary identities (A.1)–(A.4), (B.1)–(B.4), the principal-log argument, and the conditional Root-F assembly (B.6). Confidence in the proposed analytic routes is moderate; the source and landed Lean interfaces do not currently close their load-bearing estimates. Consequently the requested unconditional proofs of Proposition II.7.9 and the $k_f=0$ Root-F branch are **open in this document**.

## Part D. Choice of the high-mass route and a normalized connected-core theorem

### D.1. Cost and dependencies of the two routes

Here $\nu_*:=7/(8L^2)$ and $\nu\in(\nu_*,1]$. The word *complete* in the route estimates includes the frozen source ball, exact torus agreement, and every quantitative hypothesis of the landed polymer-gas theorems. Line counts are estimates for new Lean proof, not claims that the corresponding mathematical theorem has been proved.

| Route | New theorems that cannot be omitted | Landed reuse | Estimated new Lean lines |
|---|---|---|---:|
| H, one extra RG step | High-mass real and complex BG existence/uniqueness with a new nonempty complex domain; Green and localization constants through mass $L^2e^\epsilon$; Def-6/Def-7 H7 domain transport; high-mass II.7.9 base and LF-8 at index one; LF-2 horizon $\max(\hat k_f,1)$ and the frozen heavy budget | `Background/*`, `Green/*`, `Localization/*`, `Flow/*`, `Polymer/GasOperator`, `MayerPE`, `Hole`, `Peierls` | At least 25,000–50,000, with several existing theorem statements changed |
| D, direct one-scale | A normalized connected-core estimate retaining crossing bonds; Gaussian-with-holes localization with shrinking real chart cutoff; pointwise small ordinary interactions after exact finite-support localization; polymer counting and exact non-winding torus lifts | `Frozen/Model/Energy`, `Polymer/Mayer`, `MayerPE`, `GasOperator`, `Hole`, `HoleOperator`, `BlockTorus`, `BoxTransport`, `Localization/Peierls` | About 13,000–30,000 if the conditional comparison below can be integrated into a hole-aware gas construction |

The H estimate has a structural lower bound beyond line counting. `Background/ExistenceSetup.lean` sets `BgHyp.massLe` to $B:=\nu L^{2k}\le1$ and sends it both to `GreenSetting.massLe` and `ApproxSetting.hν1`. `Background/ApproxLocal.lean` uses $B\le1$ to bound each block mass and invokes `LocalSolution.local_solution` with local mass at most one. `Background/Approximate.lean` uses $\sqrt B\le1$ in its mass term; `ApproxResidual.lean` and `Calculus.lean` use $B\le1$ in the residual and nonlinear bounds, so their constants grow at least with $B$ if the same radii are retained. `Contraction.lean` passes the cap into `Rvec_bound` and bounds $\nu g$ by the old small parameter. `Mass116.lean` and `Def5.lean` make the complex witness with $\delta=\varepsilon$, requiring $B\delta^2\le\delta^2$. The localization chain is affected too: `Localization/ReflectionSource.lean`, `NC3Small.lean`, and `DecoupledClose.lean` explicitly pass the dimensionless cap to source and cut-Laplacian bounds. Positive mass improves coercivity, but it does not justify their unchanged upper source bounds. A valid H proof would need new constants $C_{\rm loc}(B),C_{53}(B),C_{\rm Green}(B)$ and radii at most a constant times $1/B$ in the $h$ perturbation direction, with $B\le L^2e^\epsilon$ inserted before the BG contraction thresholds are fixed. The present files do not give formulas from which those constants can be asserted.

There is an exact obstruction to extending **the existing complex domain**: `Background/Data.lean` defines `InUnionDomainC` by $0<\delta\le\varepsilon$ and $B\varepsilon^2\le\delta^2$. If $B>1$, these inequalities imply $B\varepsilon^2\le\varepsilon^2$ with $\varepsilon>0$, a contradiction. Thus the domain is empty. This affects `Theorem52Analytic.lean` and the H7 domains derived from BG in LF-RECONSTRUCTION Definition II.3.5. Merely replacing `massLe` by $B\le L^2e^\epsilon$ yields a vacuous analyticity theorem. A new anisotropic domain, with separate radii for $\Psi$ and $h$, and a new theorem proving its nonempty real slice are necessary. It must then be propagated through Def-6/Def-7 and LF-8. The high-mass class also must replace (D9$^\flat$), which caps the running mass at one, and LF-2 must be reproved when $\hat k_f=0$; see C.2–C.4. This audit rules out Route H as a short reuse of the landed BG theorem.

I therefore choose Route D. It keeps the mass parameter in a fixed positive interval after $L$ is selected and avoids extending all BG/H7 interfaces. The first quantitative obstacle is the connected bad-core normalization. The following theorem settles its *conditional-core magnitude* with all crossing bonds present. The theorem is deliberately stated before a polymer activity is defined: its last subsection records exactly what remains between this result and (B.5).

### D.2. A complete conditional connected-core estimate

Let $\Lambda$ be a finite nearest-neighbour $d$-torus of side at least three, so every vertex has $2d$ distinct neighbours. Let $C\subset\Lambda$ be any nonempty set, and prescribe unit spins $q_y$ at $y\notin C$. Only the neighbours of $C$ matter. For unit spins $\phi_x$, $x\in C$, set
$$E_C(\phi\mid q)=\sum_{\{x,z\}\subset C,\ x\sim z}(1-\phi_x\cdot\phi_z)+\sum_{x\in C,\ y\notin C,\ x\sim y}(1-\phi_x\cdot q_y)+\nu\sum_{x\in C}(1-\phi_x\cdot h).\tag{D.1}$$
This is the exact conditional energy; the second sum is retained. Write $\sigma$ for normalized surface measure on $\mathbb S^{N-1}$, $m=N-1$, and
$$I_C(q):=\int e^{-\beta E_C(\phi\mid q)}d\sigma^C(\phi),\qquad I_C^{\rm bad}(q;g):=\int_{\forall x\in C:\ |\phi_x-h|\ge r}e^{-\beta E_C(\phi\mid q)+\sum_{x\in C}g_x\cdot\phi_x}d\sigma^C(\phi).\tag{D.2}$$
Take $r=r_\beta=A\log(\beta a)/\sqrt\beta$, with fixed $A>0,a>1$, and assume $|q_y-h|<r$ for every exterior neighbour of $C$. Put
$$c_{d,L}:=\frac{\nu_*^3}{64(2d+1)^2},\qquad c_N:=\frac{\operatorname{vol}(B_m(1))}{2^m|\mathbb S^{N-1}|},\qquad P_\beta:=c_{d,L}A^2\log^2(\beta a)-\frac m2\log\beta-\frac{4d+1}{2}-\log(c_N^{-1}).\tag{D.3}$$

**Theorem D.1 (uniform normalized bad core).** There is an explicit threshold $\beta_{\rm core}(d,N,L,A,a)$ such that, for $\beta\ge\beta_{\rm core}$, $\nu\in(\nu_*,1]$, every $C$ and all exterior data just specified,
$$\frac{|I_C^{\rm bad}(q;g)|}{I_C(q)}\le \exp\{1-P_\beta|C|\}\quad(\|g\|_1<1).\tag{D.4}$$
In particular $P_\beta\to\infty$. The same inequality holds for a connected maximal bad component $C$ of the real sector $\{x:|\phi_x-h|\ge r\}$, because its exterior neighbours are good. The ratio in (D.4) is holomorphic in every complex source coordinate on the entire $\ell^1$ ball, for fixed *real* $q$. No complex continuation of the indicator or of $q$ is used.

One may take $\beta_{\rm core}$ to be any number such that for all $\beta$ above it,
$$\beta\ge16,\qquad r_\beta\le\tfrac14,\qquad (4d+\tfrac12)r_\beta^2\le\tfrac12\nu_* .\tag{D.5}$$
These conditions have a solution because $\log^2(\beta a)/\beta\to0$; increasing the threshold also makes $P_\beta>0$.

*Proof.* Compactness gives a minimizer $u=(u_x)_{x\in C}$ of $E_C(\cdot\mid q)$. First, $u_x\cdot h\ge0$ for all $x$. If a spin has negative $h$ component, reflect **all** such spins across the hyperplane $h^\perp$. An internal bond with both endpoints reflected is unchanged. For a bond with only one reflected endpoint, the dot product increases because the other endpoint has nonnegative $h$ component; the same holds at a crossing bond because $q_y\cdot h>0$. At every reflected site the mass energy decreases strictly since $\nu>0$. Thus a minimizer cannot contain a negative component. Keeping all other sites fixed, minimization over $u_x$ aligns it with
$$b_x:=\sum_{z\in C:z\sim x}u_z+\sum_{y\notin C:y\sim x}q_y+\nu h.\tag{D.6}$$
Its $h$ component is at least $\nu>0$, so $u_x=b_x/|b_x|$ and $u_x\cdot h>0$.

Let $\theta_r:=2\arcsin(r/2)<\pi/2$, and let $\theta_x\in[0,\pi/2)$ be the angle between $u_x$ and $h$. If $\Theta:=\max(\theta_r,\max_x\theta_x)$ exceeded $\theta_r$, choose $x$ with $\theta_x=\Theta$. All its $2d$ neighbours, including prescribed spins, have angle at most $\Theta$. Resolving (D.6) parallel and perpendicular to $h$ gives $b_x\cdot h\ge2d\cos\Theta+\nu$ and $|P_h^\perp b_x|\le2d\sin\Theta$. Hence
$$\tan\theta_x\le\frac{2d\sin\Theta}{2d\cos\Theta+\nu}<\tan\Theta,$$
a contradiction. Therefore every $\theta_x\le\theta_r$. Applying the same estimate once more gives
$$\theta_x\le\theta_*:=\arctan\frac{2d\sin\theta_r}{2d\cos\theta_r+\nu}<\theta_r.\tag{D.7}$$
For $r\le1/4$, $\sin\theta_r\ge3r/4$, $\cos\theta_r\ge3/4$, and $\cos(\theta_r/2)\ge3/4$. The mean-value inequality for $\arctan$ applied between $\tan\theta_r$ and $\tan\theta_* =\tan\theta_r/(1+\nu/(2d\cos\theta_r))$ yields
$$\theta_r-\theta_*\ge\frac{\nu\sin\theta_r\cos\theta_r}{2d\cos\theta_r+\nu}\ge\frac{9\nu r}{16(2d+1)}.$$
Applying the mean-value inequality to $2\sin(\theta/2)$ and weakening $27/64$ to $1/4$ gives the uniform inward gap
$$r-|u_x-h|\ge\frac{\nu r}{4(2d+1)}.\tag{D.8}$$

Let $K_C$ be the Dirichlet graph Laplacian on $C$ plus $\nu I$: its diagonal is $2d+\nu$, its off-diagonal entries are $-1$ on internal nearest-neighbour bonds. The exterior spins occur only in the linear term of (D.1). Thus $\nu I\le K_C\le(4d+1)I$. At the minimizer, $K_Cu-b=\alpha_xu_x$ sitewise, where
$$\alpha_x=\sum_{z\sim x}(1-u_x\cdot v_z)+\nu(1-u_x\cdot h),\qquad v_z=\begin{cases}u_z&z\in C,\\q_z&z\notin C.\end{cases}$$
Every $u_x$ and every $v_z$ lies within chord distance $r$ of $h$, so $0\le\alpha_x\le(4d+\tfrac12)r^2\le\nu_*/2$. For any other sphere-valued $\phi$ and $w=\phi-u$, the identity $u_x\cdot w_x=-|w_x|^2/2$ gives the **exact** constrained energy difference
$$E_C(\phi\mid q)-E_C(u\mid q)=\tfrac12\langle w,(K_C-\operatorname{diag}\alpha)w\rangle.\tag{D.9}$$
Consequently $E_C(\phi\mid q)-E_C(u\mid q)\ge(\nu_*/4)\sum_x|w_x|^2$. If all $\phi_x$ are bad, (D.8) implies $|w_x|\ge\nu_*r/[4(2d+1)]$, and therefore
$$E_C(\phi\mid q)-E_C(u\mid q)\ge c_{d,L}r^2|C|.\tag{D.10}$$
This gap holds for bad spins anywhere on the sphere; no chart approximation entered the numerator.

For the denominator, restrict each spin to the chord cap $|\phi_x-u_x|\le b:=\beta^{-1/2}\le1/4$. Since $\alpha_x\ge0$, (D.9) and $K_C\le(4d+1)I$ give $E_C(\phi\mid q)-E_C(u\mid q)\le(4d+1)b^2|C|/2$ on this product cap. The sphere chart about $u_x$ contains the tangent ball of radius $b/2$ in that chord cap, and its density is at least $|\mathbb S^{N-1}|^{-1}$; hence the normalized cap measure is at least $c_Nb^m$. It follows that
$$I_C(q)\ge e^{-\beta E_C(u\mid q)}e^{-(4d+1)|C|/2}\big(c_N\beta^{-m/2}\big)^{|C|}.\tag{D.11}$$
The bad numerator at $g=0$ is at most $e^{-\beta E_C(u\mid q)}e^{-\beta c_{d,L}r^2|C|}$ because $\sigma^C$ has total mass one. Dividing by (D.11) gives $e^{-P_\beta|C|}$. For complex $g$, $|e^{\sum g_x\cdot\phi_x}|\le e^{\|g\|_1}<e$, proving (D.4). The fixed finite integral is entire in $g$ by dominated differentiation. All constants are independent of $C$, its shape, the exterior spins within the good cap, and the torus. $\square$

The proof uses the conditional minimizer required by P4-06; (D.6) contains every crossing spin. It also shows why the counterexample in B′.2 does not apply: its exterior neighbours $-h$ violate the good-boundary condition of a *maximal* bad component.

### D.3. What D.1 supplies to a polymer activity, and what it does not

For a proposed connected-core activity, the local function $W_C(q;g):=I_C^{\rm bad}(q;g)/I_C(q)$ is defined on good real boundary data, reads only the external neighbours of $C$ and $g|_C$, and obeys (D.4) pointwise. Thus integration of $|W_C|$ against **any probability measure supported on good boundary data** preserves the same bound. For disjoint $s$-blocks, the blocks meeting $C$ number at most $|C|$, and their one-block neighbourhood numbers at most $3^d|C|$; a thicker collar needs its own corresponding count. A determinant factor bounded by $e^{D_L|C|}$ can be absorbed with this block entropy: $P_\beta-D_L-3^dH_\beta\to\infty$ for any fixed desired $H_\beta=o(\log^2\beta)$. The determinant claim is available for a *specified* positive Dirichlet matrix $K$ with spectrum in $[\nu_*,4d+1]$: deleting $C$ gives a Schur complement $S_C$, and $v^*S_Cv=\min_w(v,w)^*K(v,w)$ lies between $\nu_*|v|^2$ and $(4d+1)|v|^2$. Since $\det K/\det K_{C^c}=\det S_C$, its determinant ratio costs at most $((4d+1)/\nu_*)^{|C|}$. This finite-matrix fact does not say that the full nonlinear good-region ratio has already been reduced to that determinant.

The activity $\tau_Z$ in (B.5) has **not** been constructed by defining $W_C$. In the exact sector identity, $I_C^{\rm bad}=W_C I_C$; the factor $I_C$ remains and couples to the good region through the boundary. The good-region Gaussian determinant, nonlinear chart integral, shrinking indicators, and their hole ratios must be localized before an exact product-reference gas is available. A collar can also contain good or intermediate sites, so $|Z|_{\rm block}\le a_d|C|$ requires a stated assignment and proof, not just a connectedness assertion. D.1 completes the conditional-core magnitude theorem and supplies its source analyticity, but it does **not** by itself prove the full integrated (B.5) with the actual $\tau_Z$ required by `GasOperator.gasOp_pe`. Accordingly the first missing piece of Route D is solved only at the conditional-core level; the full activity statement requested in `followup3.txt` remains open. Claiming Root-F from D.1 would skip exactly the hole normalization and finite-support hypotheses identified in B′.5.

The remaining order is now concrete. First construct the exact core/collar sector identity and a product Gaussian with holes, keeping the real cutoff and every crossing bond. Next show that its activity is $W_C$ multiplied by factors whose absolute value is at most $e^{D_L|C|}$, with a proved $|Z|_{\rm block}\le a_d|C|$ assignment; D.1 then proves (B.5) after choosing $\beta_0$ so that $P_\beta-D_L$ dominates the `gasOp_pe` thresholds. Then establish localized finite-support walk activities and exact torus lifts; the landed `MayerPE`, `GasOperator`, `Hole`, `Peierls`, `BlockTorus`, and `BoxTransport` theorems can be invoked only after their stated inputs are checked. Finally B.4–B.6 assemble Root-F. The $\delta=1/8$, $\kappa,c_9$, $L,M$, $\beta_0$ order remains the frozen order; $A,a$ are fixed after $L,M$ and before $\beta_0$.

| Order | Lean lemma | Estimated lines | Status and reuse |
|---|---|---:|---|
| D1 | `conditionalMinimizer_exists`, `minimizer_hemisphere`, `minimizer_strictCap` proving (D.6)–(D.8) | 800–1,600 | Mathematical proof above; `Frozen/Model/Energy`, finite sphere compactness |
| D2 | `conditionalEnergy_quadratic`, `badCore_energyGap` proving (D.9)–(D.10) | 600–1,200 | Mathematical proof above; finite graph Laplacian |
| D3 | `sphereCap_measureLower`, `badCore_normalized`, holomorphic source proving (D.11)–(D.4) | 700–1,400 | Mathematical proof above; chart Jacobian from A.1 |
| D4 | `holeSchur_detRatio`, core/collar assignment, exact sector activity with a product reference | 2,000–5,000 | Matrix determinant part standard; full nonlinear hole ratio **open**; `Polymer/HoleOperator` |
| D5 | `kf0_gaussianWithHoles_local`, source and cutoff localization, exact torus lift | 5,000–10,000 | **Open**; `Localization/DecoupledX*`, `MayerPE`, `BoxTransport` |
| D6 | Check `gasOp_pe`, `pe_blockTorus_frozen`, then B.6 | 2,500–5,000 | Conditional on D4–D5; landed GAS/PE and frozen Root-F |

Confidence is high in Theorem D.1 and the empty-domain obstruction for literal Route H. The comparison in D.3 identifies the precise unsolved part of the selected route. The note therefore does not claim an unconditional proof of (B.5), Proposition II.7.9, or Root-F in the $k_f=0$ regime.
