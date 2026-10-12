# The hard-spin base step and the one-scale massive case

**Status (12 October 2026).** This is a source-bound proof audit and a set of exact reductions. It proves the chart and conditional-energy identities, a fixed-operator covariance estimate, a raw Peierls witness estimate, and the assembly of Root-F from stated one-scale analytic estimates. It does **not** prove Proposition II.7.9 or Root-F for $k_f=0$: the localized covariance, the first small-field expectation, the needed remainder budget, and the normalized heavy-object estimate remain open below. In particular, none of the conditional statements in this note may be used as a provider of the frozen Lean theorem.

## Sources and contract

The exact target is `Balaban/Frozen/Roots/LogPartitionMultiscale.lean`, SHA-256 `21833bea3211257ac51d0879ef9f692acb0021fb04e792375cf5257104380e40`, read-only under `/home/scott/Balaban`. Its model is `Frozen/Model/{Energy,AprioriMeasure,PartitionFunction}.lean`: $H(\phi)=\frac12\sum_{x,\mu}|\phi_{x+e_\mu}-\phi_x|^2+\frac\nu2\sum_x|\phi_x-h|^2$, $|\phi_x|=|h|=1$, and the source is $+\sum_{x,i}g_i(x)\phi_i(x)$. The prior construction is `notes/phase1/LF-RECONSTRUCTION.md` §§II.7.3–II.7.5, IV.4.2, IV.5.2–IV.5.3, SHA-256 `be3e616a9a94b458d17a02606022fc7ce579b320b2ffaf8cb4a392757f52a0e6`; its audit is `LFR-PART4-AUDIT-astra.md`, findings P4-02, P4-03, P4-06. Paper keys are those of `review/SOURCES.md`: P4 (2.42)–(2.50), pp. 691–694, P5 Proposition 3.2, p. 517, P6 §4, and P7 (4.15)–(4.17), p. 533. P4 treats the first transformation in the whole-lattice small field; it does not state the large-field base case or the $k_f=0$ last step here. `GREEN.md` §4.4(ii), `LOCALIZATION.md` §3.4 (I-4c), `FLUCTUATION.md` §§2.4, 5.5, and `SMALLFIELD.md` §§3, 4–5 are paper-level reconstructions, with the statuses given in those notes.

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
