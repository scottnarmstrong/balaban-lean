# The first hard-spin fluctuation: localization, cutoffs, and the remainder

**Status, 12 October 2026.** The three obligations in the orchestrator's follow-up are **not proved in full** by the cited papers, notes, or landed Lean declarations. This note proves the finite-dimensional constrained-inverse identity, a quantitative real cutoff-removal lemma, fixed-contour finite-volume analyticity, and the arithmetic that turns a localized first-step mark of order $\beta_0^{-m-2}$ into the requested half-budget. It identifies the exact missing estimates and geometry that prevent these lemmas from constituting Proposition II.7.9. In particular, the existing Dec2 pair interface does not by itself produce the hard-spin base covariance or its localized square root.

The source is LF-RECONSTRUCTION v1.3, §§II.7.3--II.7.5 and IV.1.2 (especially Lemma IV.1.8), with BASE-KERNEL.md §§1--3 and 6, LF-BASE-KF0.md §§A.1--A.5, FLUCTUATION.md §§2.4--2.6, P5 (2.39)--(2.47), (3.5)--(3.9), Proposition 3.2, pp. 511--517, and P6 §2 and Lemma 4.2. Paper keys are those of review/SOURCES.md. References to Lean below name declarations in the read-only Balaban repository; no claim of elaboration is made for a new declaration.

## 1. The base covariance and Dec2

### 1.1 Exact constrained inverse

Let $D$ be the fine-site chart domain of one base-record generating set, a union of complete first blocks, with exterior spins held fixed. Put
$$H_{\rm sc}:=-\Delta_D+aL^{-2}Q_D^*Q_D+\mu_{\rm bg}+\alpha,\qquad
\mu_{\rm bg}=\begin{cases}0&\text{in regime (A)},\\ \nu&\text{in regime (B)}.\end{cases}\tag{1.1}$$
Here $\alpha$ is multiplication by the constrained multiplier. The scalar operator acts componentwise on $W=(\mathbb C^N)^D$. Write $e_x=\phi^{\rm b}(x)$, $E:\mathbb C^D\to W$, $(Ef)_x=e_xf_x$, $P=EE^{\mathsf T}$, and $Q=I-P$. For real unit backgrounds, $E^{\mathsf T}E=I$. The base operator and covariance are
$$A_e=Q(H_{\rm sc}\otimes I_N)Q+P,\qquad C^{(0)}=A_e^{-1}.\tag{1.2}$$
These are BASE-KERNEL.md (2.1)--(2.2), with the regime-(A) physical $\nu$ interaction kept outside $H_{\rm sc}$.

**Lemma 1.1 (proved, finite matrices).** Suppose $H_{\rm sc}$ is real symmetric positive definite. With $G=H_{\rm sc}^{-1}\otimes I_N$ and $M=E^{\mathsf T}GE$,
$$C^{(0)}=G-GE\,M^{-1}E^{\mathsf T}G+P.\tag{1.3}$$
The same equality holds analytically for complex data in any connected neighbourhood of the real data on which $e_x\cdot e_x=1$, $H_{\rm sc}$, $M$, and $A_e$ remain invertible.

*Proof.* $M$ is positive definite, since $\langle f,Mf\rangle=\langle Ef,GEf\rangle>0$ for $f\ne0$. Let $T=\ker E^{\mathsf T}$ and choose an orthonormal inclusion $J:T\hookrightarrow W$; then $JJ^{\mathsf T}=Q$. The landed theorem Balaban.Multiscale.constrained_green_eq in Multiscale/XVariantIdentities.lean, applied with $B=E^{\mathsf T}$ and $J$ as its kernel embedding, gives
$$J(J^{\mathsf T}(H_{\rm sc}\otimes I_N)J)^{-1}J^{\mathsf T}
=G-GE(E^{\mathsf T}GE)^{-1}E^{\mathsf T}G.$$
The left side is the inverse of $Q(H_{\rm sc}\otimes I_N)Q$ on $T$ and zero on the normal space $\operatorname{ran}E$. On that normal space $A_e=I$, and $A_e$ preserves $T$ because $P Q=0$. Adding $P$ therefore gives the inverse of $A_e$. Both sides are rational matrix functions of the entries where the listed inverses exist. Equality on real data, or the same algebra over $\mathbb C$, gives the complex statement. The source theorem's bridge Multiscale.XVariantIdentities.constrainedOp_eq_constraintPi identifies the middle term with Multiscale.Constrained.constrainedOp. $\square$

In Lean terms, $E$ is Multiscale.fieldMul $e$, $G$ is Multiscale.liftOp $N$ of the scalar inverse, $M$ is Multiscale.constraintForm, and the middle term is Multiscale.constrainedOp. A tangent frame $J$ is only a device for the proof; formula (1.3) is frame independent. A separate measure and chart argument remains necessary for the determinant and $\frac{N-1}{2}|D|\log(2\pi/\beta)$ in BASE-KERNEL.md (2.3).

**Lemma 1.2 (physical-point decay, conditional on the real gap).** Suppose, as asserted in GREEN §4.4(ii) and LF-RECONSTRUCTION Lemma II.7.3, that $A_e$ is real symmetric with $A_e\ge a_0I$, $a_0=L^{-2}/4$, and has finite site range $R$. Let $J_{\rm row}$ be the larger of its absolute block-row and block-column sums, with each $N\times N$ block measured in operator norm. Choose $\theta>0$ with $J_{\rm row}(e^{\theta R}-1)\le a_0/2$. Then for all $t\ge0$,
$$\|(A_e+t)^{-1}(x,y)\|_{\rm op}\le(a_0/2+t)^{-1}e^{-\theta d(x,y)},\qquad
\|A_e^{-1/2}(x,y)\|_{\rm op}\le\sqrt{2/a_0}\,e^{-\theta d(x,y)}.\tag{1.5}$$
The constants are independent of the number of sites if $J,R,a_0$ are uniform. The same integral gives a weighted off-diagonal bound for $\log A_e$.

*Proof.* For fixed $y$ conjugate by the diagonal weight $W_x=e^{\theta d(x,y)}$. The Schur bound gives $\|WA_eW^{-1}-A_e\|\le J_{\rm row}(e^{\theta R}-1)\le a_0/2$. Hence the conjugated $A_e+t$ has inverse norm at most $(a_0/2+t)^{-1}$. Taking its $(x,y)$ block yields the first bound. The Stieltjes identity $A_e^{-1/2}=\pi^{-1}\int_0^\infty t^{-1/2}(A_e+t)^{-1}dt$ gives the second after the scalar integral. For the logarithm use the subtracted-resolvent integral and the finite range of $A_e-I$, as in LF-BASE-KF0 Lemma A.4. $\square$

This is decay of the physical matrix at $s=1$. It does not give exact vanishing or exact agreement under a change of a distant parameter, which are separate I-4c clauses.

### 1.2 What the cover/operator pair supplies

For a one-layer generating set $H_{\rm B}$ with $H_{\rm B}.\Omega(1)=D$, $H_{\rm B}.\Omega(2)=\varnothing$, the scalar Dirichlet operator Multiscale.dirichletOperator $H_{\rm B}\,a_\bullet\,\mu_{\rm bg}\,\alpha$ has the form (1.1) when $a_\bullet(1)=a$ and the block normalization agrees with $Q_D^*Q_D$. Such a generating set exists mathematically whenever $D$ is a union of first blocks: set $\Omega(1)=D$ and $\Omega(j)=\varnothing$ for $j\ge2$. The top and nesting clauses are immediate, blockUnion is the hypothesis on $D$, and the separation clause $1\le j<1$ is empty. The operator identity and the identification of the base record's local $D$ with this one-layer object are **not landed**. The natural cover is Localization.coverOf $H_{\rm B}$, or a separately constructed DecCover $C_{\rm B}$ whose interaction cubes and parameter cubes match the first-step localization domains.

Dec2.Gs $C_{\rm B}\,H_{\rm B}$ is a decoupled **scalar Green operator**. At $s\equiv1$, Dec2.Gs_one_of_unit identifies it with $H_{\rm sc}^{-1}$, provided its hypotheses hold. Equation (1.3) then identifies the *physical* base covariance as a constrained function of that scalar inverse. It does **not** identify $C^{(0)}$ with Dec2.Gs, and Localization.decCov at $s=1$ is the inverse of the different step operator Localization.covOp in DecoupledIdentMain.lean. The latter contains a block Schur complement; its declaration cannot be specialized by putting the step index $k=0$, because Localization.XSetting.hk and Dec2.XCover.hk require $1\le k$ (Decoupled2X.lean). This corrects the possible reading of LF-BASE-KF0 §A.5: Dec2 provides a useful scalar entry point, not an already proved base I-4c.

Here is the exact pair checklist. To use the non-$x$ Dec2.Gs layer one must construct $C_{\rm B}$ and $H_{\rm B}$ and prove Dec2.CoverBase $C_{\rm B}\,H_{\rm B}\,a_\bullet\,\mu_{\rm bg}\,K_c\,C_\chi$. Its inherited Dec2.OpSetting fields are $d\ge3$, $L\ge3$, $\mu_{\rm bg}\ge0$, $\mu_{\rm bg}L^2\le1$ when the number of layers is one, admissible $a_\bullet$, and $2d\log L\le\gamma_{\rm Agmon}(d)(\varrho-1)/16$. Its Dec2.CoverGeom fields are blockAligned, chi_unit, sum_chi, chi_smooth, inner_near, card_box, and card_qset. The added CoverBase.nc is the uniform CubeBlockBounds for each cut cube. For exact component locality one also needs Dec2.CoverLocalGeom.idx_range, idx_base, chi_supp, cubeP_sub, own_cover, then Dec2.CoverLocal.row_mem_hat and Dec2.HatConn. The quantitative Dec2 estimates additionally require the displayed large-cover inequality $c_\star e^{N_0\kappa_1}\le L^{m_1}$ and the admissible-potential bound Localization.AdmPot $H_{\rm B}\,\alpha$. For the self-cover $C_{\rm B}=\mathrm{coverOf}(H_{\rm B})$, Dec2.coverBase_self and Dec2.coverLocal_self discharge the listed cover and cut fields from Localization.DGSetting, whose additional concrete fields are CubeAligned, $4L^2\le L^{m_1}$, $4dL^{m_1+1}\le\varrho$, and $5<N_1$. One still has to verify those fields for the base geometry and prove that the resulting cover has the required P5/P6 localization footprints.

The mass field is a real obstruction in regime (B): $\mu_{\rm bg}=\nu$ may satisfy $\nu L^2>1$, whereas Dec2.OpSetting.massLe requires $\nu L^2\le1$ at one layer. Moving such a $\nu$ into the potential $\alpha$ violates AdmPot's $O(L^{-2})$ bound. A mass-monotone extension of the cube and weighted Green estimates, or another operator theorem, is required for those records. In regime (A), $\mu_{\rm bg}=0$, so this particular obstruction vanishes; the cover, cut-operator, potential, and chart-constraint fields still need proof. The whole-torus GeneratingSet.single of Background/SingleScale.lean has $\Omega(1)$ equal to the whole torus and cannot represent a component with a hole.

Even after CoverBase is supplied, the normal constraint must be carried through the decoupling. If one substitutes $G_s=\mathrm{Dec2.Gs}(s)$ into the right side of (1.3), $E^{\mathsf T}G_sE$ is singular at $s=0$, since Dec2.Gs is then zero. The unmodified Schur formula does not define a holomorphic polydisc family. Multiscale.Constrained.constraintM and constraintN instead define
$$M_s=E^{\mathsf T}E-K_e\widehat G_sE,\quad
N_s=E^{\mathsf T}-K_e\widehat G_s,\quad
\Pi_s=\widehat G_sE M_s^{-1}N_s,\quad
K_e=E^{\mathsf T}(H_{\rm sc}\otimes I_N)-H_{\rm sc}E^{\mathsf T},\tag{1.4}$$
where $\widehat G_s=G_s\otimes I_N$. At $s=0$, $M_s=I$. At $s=1$, write $G_s=H_{\rm sc}^{-1}$ and $S=E^{\mathsf T}\widehat G_sE$. Direct multiplication gives $M_s=H_{\rm sc}S$ and $N_s=H_{\rm sc}E^{\mathsf T}\widehat G_s$, whence $\Pi_s=\widehat G_sE S^{-1}E^{\mathsf T}\widehat G_s$, the middle term in (1.3). This is the same algebra used in DecoupledIdentMain, but its $k\ge1$ declaration is not being instantiated. Formula (1.4) is the non-$x$ analogue of Localization.decM, decN, decPi, **not a landed base family**. It still needs uniform invertibility, weighted response, background analyticity, and component locality.

For I-4c itself one needs an $x$-resolvent family with value $(A_e+x)^{-1}$ at $s=1$, a nondegenerate reference at zero parameters, an integrable $x^{-1/2}$ bound for the principal inverse square root, an integrable subtracted resolvent for the logarithm, and exact core and torus-lift identities. Simply adding $P/(1+x)$ to $\widehat G_s-\Pi_s$ leaves zero tangent covariance at $s=0$; its subtracted logarithm integral diverges there. The DecoupledCovPrincipal matrix-function theorems apply once a base family with these properties is constructed. They do not construct it. Thus the answer to the follow-up's instance question is: **the scalar Hessian can be represented by a Dec2 cover/operator pair after its fields are proved; the hard-spin base covariance is a constrained inverse of that scalar operator and is not an instance of the landed Dec2 decoupled covariance.**

## 2. Exact real cutoff transfer

Let $D_+$ be the sites integrated in the first small-field expectation, $D_-=\Omega_1\setminus\Omega''_1$ the retained chart sites, and $D_{\rm out}=\Omega_1^c$ the retained spins, all intersected with a component when appropriate (BASE-KERNEL.md §1). For a cube $c$, $A_c$ is chiBlockA and $B_c$ is chiBondB of LargeField/Base/BaseRecord.lean. The latter tests every bond with an endpoint in $c$, including a bond crossing the cube boundary, and in regime (B) the sites in $c$. The exact record factor is
$$\mathcal I_{\rm old}=
\prod_{c\in\mathsf P_1}(1-A_cB_c)\,
\prod_{c\notin\mathsf P_1}A_cB_c.\tag{2.1}$$
There is no independent old $\chi_0$ factor in the initial density. LargeField.chiPrimeZero_decomposition proves the decomposition yielding (2.1), and LargeField.BaseWitness.baseF_decomposition proves the outside block-witness split. The landed base_P_nbhd_compl/base_bond_comp show that a bond witnessing a $\mathsf P_1$ cube is in the retained outside component; hence no such failed factor may be silently moved into $D_+$.

For every good cube $c\notin\mathsf P_1$ whose block, bond, or site test reads a site of $D_+$, let $F(c)$ contain **all** sites in its tested blocks and both endpoints of each tested bond. Denote the family of such cubes by $\mathcal J_+$. The following is the precise transfer lemma, formulated without a claim that its premises follow from the base record.

**Lemma 2.1 (proved, real cutoffs).** Suppose $e_x$ is the real unit background on every $F(c)\cap\Omega_1$, extended by $e_x=\phi_x$ at retained sites outside $\Omega_1$, and $|\phi_x-e_x|\le r$ on every $F(c)$, $c\in\mathcal J_+$. Suppose, for every tested block $y$, bond $\{x,x'\}$, and regime-(B) site $x$ in those cubes,
$$|\theta_y-(Qe)_y|<2\delta_0-r,\qquad
|e_x-e_{x'}|<\delta_0-2r,\qquad
\sqrt\nu\,|e_x-h|<\delta_0-\sqrt\nu\,r.\tag{2.2}$$
Then $A_cB_c=1$ for every $c\in\mathcal J_+$. On this real domain, (2.1) equals the same product with all $c\in\mathcal J_+$ deleted. Every remaining old factor is independent of the spins in $D_+$, provided the definition of $\mathcal J_+$ includes every factor with that dependence.

*Proof.* Block averaging is a contraction in the sup norm, so $|\theta_y-(Q\phi)_y|\le|\theta_y-(Qe)_y|+r<2\delta_0$. The triangle inequality gives $|\phi_x-\phi_{x'}|\le|e_x-e_{x'}|+2r<\delta_0$. The site inequality is $\sqrt\nu|\phi_x-h|\le\sqrt\nu|e_x-h|+\sqrt\nu r<\delta_0$. Thus every defining test of $A_cB_c$ holds. Such a factor is one, and deletion changes neither product. By the definition of $\mathcal J_+$, a remaining factor reads no integrated spin. $\square$

A convenient sufficient margin is
$$|\theta_y-(Qe)_y|<\tfrac32\delta_0,\quad
|e_x-e_{x'}|<\tfrac12\delta_0,\quad
\sqrt\nu|e_x-h|<\tfrac12\delta_0,\quad
r\le\tfrac14\delta_0,\quad 0\le\nu\le1.\tag{2.3}$$
All three inequalities of (2.2) then hold strictly. The chart displacement is not exactly its tangent coordinate: if $|\xi_x|\le t\le1/4$, the chord formula gives $|\phi_x-e_x|\le2t$. Hence a localized covariance sup bound $|\xi_x|\le B_5\beta_0^{-1/2}p_1(\beta_0)$ gives (2.3) when $2B_5p_1/p_0\le1/4$ in the convention $\delta_0=\beta_0^{-1/2}p_0$. Under the additional choice $K_2\ge2$, the LF-RECONSTRUCTION row-9 ratio $p_1/p_0=A_1/A_0=1/(4K_2B_5)$ meets this inequality. If the convention includes the factor $a^{-1/2}$ in $\delta_0$, the same inequality must be checked with that factor; it is not automatic from a copied ratio.

The missing geometric premise is that the output $\chi_{1,u}$ and the record imply the three **background** margins in (2.3) on the whole union $\bigcup_{c\in\mathcal J_+}F(c)$, including each bond crossing $\partial\Omega''_1$. FLUCTUATION Lemma 2.5 proves a corresponding whole-lattice margin statement for a different fluctuation and output cutoff; it does not identify this first-step footprint. P5 Lemma 2.1, p. 511, states the indicator removal and expressly defers its proof to the next paper. P6 (2.2), p. 4, removes the next cutoff on its own support, but supplies no base-record map from $\mathcal J_+$ to (2.3). If a boundary bond has one endpoint in $D_+$ and one in $D_-$, omitting it without (2.2) can change the integral: choose real unit background spins whose bond difference is just below $\delta_0$, then perturb the integrated endpoint tangentially in the increasing direction by an arbitrarily small amount allowed by its fluctuation cutoff. Thus the separation of that cross-boundary condition is an actual theorem to prove, not a bookkeeping convention.

The remaining cutoff on $D_+$ may be the fixed real product $\prod_{x\in D_+}\mathbf1[|\psi'_0(x)|<p_1(\beta_0)]$. This indicator is independent of complex background parameters and can be kept inside a fixed-contour analytic integral. Conditions depending on the physical spins must first be removed by Lemma 2.1; they cannot be holomorphically continued as characteristic functions.

## 3. The first small-field integral

### 3.1 Exact finite-volume reduction

Fix the retained spins, retained chart variables, output block data, and a real base background. For $D_+$ use BASE-KERNEL.md (2.3) and LF-BASE-KF0 (A.3), with $v=Q_eC^{(0)1/2}\psi'_0$ and
$$z_x(v)=\sqrt{\beta_0}\big(\sqrt{1-\beta_0^{-1}|v_x|^2}-1\big)e_x,\qquad
J_{\beta_0,D_+}(v)=\prod_{x\in D_+}(1-\beta_0^{-1}|v_x|^2)^{-1/2}.\tag{3.1}$$
For the **full** chart domain $D=D_+\cup D_-$, LF-BASE-KF0 (A.3) gives the vacuum term $V_D=\frac{N-1}{2}|D|\log(2\pi/\beta_0)+\frac12\log\det C^{(0)}$ and the Gaussian expectation of $J_{\beta_0,D}\exp[-\langle v,H_Dz(v)\rangle-\frac12\langle z(v),H_Dz(v)\rangle]$, the physical regime-(A) $\nu$ factor, the source, and the real cutoffs. The first small-field integral is the conditional integration over the $D_+$ variables in this **full-domain** equality. Its determinant cannot be assigned the factor $\frac12\log\det C^{(0)}$ independently of $D_-$: Gaussian conditioning produces a block Schur complement, and the full $C^{(0)1/2}$ may mix $D_+$ and $D_-$. A local square-root substitution additionally creates the determinant difference between the local and physical covariance; that difference must be counted once, as in P5 (2.34), (2.41). The mixed $\langle v,H_Dz\rangle$ term is generally nonzero. These are equalities of finite real integrals before localization or exponentiation; a local factorization needs the missing covariance theorem.

**Lemma 3.1 (proved, finite-volume analyticity).** Suppose Lemma 2.1 has removed all parameter-dependent old indicators on $D_+$, the chart square root in (3.1) stays in $|\beta_0^{-1}v_x\cdot v_x|<1$ on the fixed truncated real Gaussian contour, and the background, covariance square root, determinant branch, and source are holomorphic in a complex neighbourhood of one real datum. Then the conditional integral is holomorphic in that neighbourhood. At the real datum it is strictly positive, and hence it has a holomorphic logarithm on some, possibly datum- and volume-dependent, smaller neighbourhood.

*Proof.* The contour is a finite product of bounded balls, and its indicator is fixed. On a compact smaller parameter neighbourhood the continuous complete integrand and all its complex derivatives have an integrable bound against the Gaussian density. Differentiate under the integral. On real data the Jacobian, Boltzmann factor, source exponential for real source, and Gaussian density are positive on an open set of positive measure. A holomorphic function nonzero at a point has a holomorphic logarithm on a sufficiently small neighbourhood. $\square$

The lemma proves no H7-sized zero-free domain and no volume-independent coefficient bound. Those require a local interaction expansion with the P6 (4.28), (4.43), (4.49), (4.51) estimates and the hole-aware marked polymer theorem. In regime (A) the $\nu$-free RG equations of SMALLFIELD §3.7 must be used; in regime (B) the complete-background equations of §3.4 apply. A bound for the logarithm on one finite chart does not produce either equation or the boundary family $\mathcal B^{(1)}$.

### 3.2 The half-budget calculation

Let $m$ now denote the fixed irrelevant-order index of Proposition II.7.9, not the chart dimension. P5 (3.9) is a marked expectation. At the base step the old $\delta\mathscr E_0$, $\delta\mathscr F_0$, and $\delta\mathcal R^{(0)}$ marks vanish because those old functions are absent; the local-versus-physical chart interaction $\delta V_{\rm eff}^{(0)}$, including the local covariance/background difference, remains. The determinant difference of P5 (2.41) must also be localized. P5 Proposition 3.2, p. 517, prints $\frac12\beta_0^{-m-1}$, which by itself does not imply the scale-one target $\frac12\beta_1^{-m-1}$.

**Lemma 3.2 (proved, budget conversion).** Assume the *localized* marked expansion, for every base record and every allowed localization domain $Y$, gives
$$|\mathcal R^{(1)}_m(Y)|\le C_\star\beta_0^{-m-2}e^{-\kappa_b d^{\rm cov}_1(Y\bmod\Omega_1^c)},\qquad
C_\star=C_{\rm PE}K_0+1,\tag{3.2}$$
where the determinant contribution is at most $\beta_0^{-m-3}$ and $\beta_0\ge1$. If $\beta_1/\beta_0\le B_L:=2L^{d-2}$ and
$$\beta_0\ge2C_\star B_L^{m+1},\tag{3.3}$$
then every coefficient satisfies the requested half-budget
$$|\mathcal R^{(1)}_m(Y)|\le\tfrac12\beta_1^{-m-1}
e^{-\kappa_b d^{\rm cov}_1(Y\bmod\Omega_1^c)}.\tag{3.4}$$

*Proof.* From (3.3), $C_\star\beta_0^{-1}\le\frac12B_L^{-(m+1)}\le\frac12(\beta_0/\beta_1)^{m+1}$. Multiply by $\beta_0^{-m-1}$ and the decay factor. The determinant term is bounded by $\beta_0^{-m-2}$ because $\beta_0\ge1$, so its coefficient is included in $C_\star$. $\square$

The premise (3.2), rather than the arithmetic, is open at $k=0$. LF-RECONSTRUCTION Lemma IV.1.8 proves this conversion for a later step conditional on FLUCTUATION Theorem 3.1(d),(e), P6 Lemma 4.2, the marked expansion, LOC I-4c, and the collar inequality (Λ29). To use it here one must prove a first-step chart-mark estimate at order $\beta_0^{-m-2}$ **after localization**, uniformly over records, tori, retained data, and every $Y$, with the modified hard-spin Jacobian and mixed normal term. One must prove the determinant estimate with the base local covariance, and the same marked polymer resummation with holes. A statement that the *whole function* P5 (3.9) is smaller than every power of $\beta_0^{-1}$ (p. 516) does not bound each localized coefficient; large coefficients may cancel in the sum. A bound only for boundary-dependent differences does not control a whole-torus coefficient, even if a separate symmetry argument later makes some of those coefficients vanish. The exact whole-torus equality clause of P5 Proposition 3.2 must be established for the base local family before any such vanishing can be used.

## 4. Closure ledger for Proposition II.7.9

1. **Covariance localization remains open.** Construct the one-layer base generating set and cover, verify every Dec2 pair field above where applicable, and extend the scalar/constraint estimates to the regime-(B) mass range. Define a nondegenerate decoupled resolvent for $A_e+x$, then prove its uniform complex-polydisc bound, principal square root and logarithm, comparison, exact core locality, and torus lift. Lemma 1.1 supplies its physical-point identification only.
2. **Cutoff transfer remains open.** Identify $\mathcal J_+$ for the actual $\Omega''_1$ and prove the background margins (2.3) on every block, site, and cross-boundary bond in its full footprint. Then Lemma 2.1 deletes precisely those old indicators and leaves the fixed real $\psi'_0$ cutoff. The landed chiPrimeZero and baseF declarations provide the record algebra but not these margins.
3. **The integral remains open.** Localize and exponentiate the complete chart interaction with the first-step vacuum and determinant allocation, derive the $E''_0,E'''_0$ constants and the inside/crossing split of P6 (2.32)--(2.33), prove the H7 zero-free and source bounds, and solve the appropriate I-7 system. Lemma 3.1 provides finite-volume analyticity only.
4. **The half-budget remains open at its analytic premise.** Prove (3.2) uniformly, including all domains identified with whole-torus terms; (3.3) then supplies (3.4). P5 Proposition 3.2's printed coefficient and its unlocalized arbitrary-power remark do not discharge (3.2).

Accordingly BASE-KERNEL.md remains a conditional base-kernel interface. No theorem in this note is a replacement provider for Proposition II.7.9 or for Lemmas II.7.7--II.7.8.
