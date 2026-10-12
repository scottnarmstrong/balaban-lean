# The base resolvent and the marked first integral

**Status, 12 October 2026.** This note proves a nondegenerate finite-volume base decoupling by cutting only bonds between first blocks. It also proves an exact one-mark summation and a half-budget criterion using the exponent $\beta_0^{-m-3/2}$ printed in P6 Lemma 4.2. The record-wide cutoff implication and the model-specific first-step activity bounds remain open. Thus the three obligations do not yet prove Proposition II.7.9. No Lean declaration is added here.

References: LF-RECONSTRUCTION v1.3, Definition II.7.1, Lemma II.7.2(d), Proposition II.7.9 and Lemma III.7.1; LF-BASE-KF0 (A.3), (A.5); BASE-KERNEL.md and BASE-KERNEL-2.md; P5 Lemma 2.1, (2.44), (3.9), Proposition 3.2; P6 (2.2), (4.29)--(4.31), Lemma 4.2 and its proof of P5 Proposition 3.2. Paper keys are those of review/SOURCES.md. Named Lean declarations below are in the read-only Balaban tree.

## 1. A direct base decoupled resolvent

Let $D$ be the fine-site chart domain, a union of complete first blocks of side $L$, with exterior spins held fixed. In the notation of BASE-KERNEL-2.md (1.1), let
$$H=-\Delta_D+aL^{-2}Q_D^*Q_D+\mu_{\rm bg}+\alpha,\qquad
\mu_{\rm bg}=0\ \text{in (A)},\quad \mu_{\rm bg}=\nu\ge0\ \text{in (B)}. \tag{1.1}$$
Here $Q_D^*Q_D$ is the **orthogonal block projection** with the normalization of Multiscale.avgMatrix, layerProjMatrix, and blockProjMatrix, rather than the unweighted adjoint square of an averaging map in counting measure. Let $\mathcal E$ be the nearest-neighbour bonds with both endpoints in $D$ but in different first blocks. A Dirichlet boundary bond with its other endpoint outside $D$ is not in $\mathcal E$: its diagonal contribution stays at every parameter value. For $b=\{z,w\}$ put $D_bu=u_z-u_w$ and $T_b=D_b^*D_b$. Define
$$H(s)=H_{\rm cut}+\sum_{b\in\mathcal E}s_bT_b,\qquad
H_{\rm cut}=H-\sum_{b\in\mathcal E}T_b. \tag{1.2}$$
Then $H(\mathbf1)=H$ and $H(\mathbf0)=H_{\rm cut}$. The averaging projection and $\alpha$ are site or first-block local, so $H_{\rm cut}$ is a direct sum over first blocks. This is an edge-parameter construction, not an identification with Dec2.Gs.

For a real unit background $e=(e_z)_{z\in D}$ let $P_e(z)=e_ze_z^{\mathsf T}$, $Q_e=I-P_e$, and
$$A_e(s)=Q_e(H(s)\otimes I_N)Q_e+P_e,\qquad
\mathcal C_{e,x}(s)=(A_e(s)+xI)^{-1}\quad(x\ge0). \tag{1.3}$$

**Theorem 1.1 (proved under the displayed potential bound).** Assume the first-block operator is the one-layer Multiscale.dirichletOperator, its weights satisfy IsAdmissibleWeights $1\,a$, $L\ge3$, and
$$\|\alpha_z\|\le {1\over8L^2}\qquad(z\in D). \tag{1.4}$$
Put $c=1/(4L^2)$. For real $s_b\in[0,1]$ and real unit $e$,
$$\operatorname{Re}\langle u,A_e(s)u\rangle\ge c\|u\|^2. \tag{1.5}$$
If each complex $s_b$ is within $\eta\le c/(8d)$ of a real $r_b\in[0,1]$, then
$$\operatorname{Re}\langle u,A_e(s)u\rangle\ge {c\over2}\|u\|^2,\qquad
\|\mathcal C_{e,x}(s)\|\le(c/2+x)^{-1}. \tag{1.6}$$
The resolvent, principal inverse square root and principal logarithm are holomorphic in these parameters. There are volume-independent $J,R<\infty$ bounding the block row sums and site range of $A_e(s)$. If $\gamma>0$ and $J(e^{\gamma R}-1)\le c/4$, then
$$\|\mathcal C_{e,x}(s)(z,w)\|_{\rm op}\le(c/4+x)^{-1}e^{-\gamma d(z,w)},\qquad
\|A_e(s)^{-1/2}(z,w)\|_{\rm op}\le\sqrt{4/c}\,e^{-\gamma d(z,w)}. \tag{1.7}$$
At $s=\mathbf1$, $A_e(s)^{-1}$ is $C^{(0)}$ of BASE-KERNEL-2.md (1.2). If the nonzero-parameter bonds disconnect $D$ into unions of complete first blocks, $A_e(s)$ and its resolvent, square root and logarithm are direct sums over those unions. Data outside one union cannot change their entries inside it.

*Proof.* Cutting $\mathcal E$ removes no bond internal to a first block, so the cut is Multiscale.CutAligned for the one-layer generating set. The landed Multiscale.cutOperator_isCoercive_min_sharp in Multiscale/CutCoercivity.lean, with coerciveConstSharp $=1/4$, gives
$$\operatorname{Re}\langle v,H_{\rm cut}v\rangle\ge c\|v\|^2. \tag{1.8}$$
Its potential hypothesis is (1.4) at spacing $L$; it assumes only $\mu_{\rm bg}\ge0$. Each $T_b$ is positive semidefinite. Thus (1.8) holds for $H(r)$ when $0\le r_b\le1$. Since $P_e,Q_e$ are complementary orthogonal projections,
$$\operatorname{Re}\langle u,A_e(r)u\rangle
=\operatorname{Re}\langle Q_eu,H(r)Q_eu\rangle+\|P_eu\|^2
\ge c\|Q_eu\|^2+\|P_eu\|^2\ge c\|u\|^2.$$
Each bond matrix has absolute row sum two at either endpoint. At most $2d$ bonds meet a site, so the row and column sums of $H(s)-H(r)$ are at most $4d\eta$; the Schur bound gives operator norm at most $4d\eta\le c/2$. Projecting by $Q_e$ cannot increase it. This proves (1.6); finite-matrix inversion is holomorphic wherever its determinant is nonzero.

The range $R$ is finite because bonds have range one, the block projection has at most first-block diameter, and $P_e,Q_e,\alpha$ are site diagonal. The row sum $J$ depends on $d,L,N,a,\mu_{\rm bg}$ and (1.4), but not on the number of blocks; no uniform bound over unbounded $\nu$ is asserted. Conjugate $A_e(s)+x$ by $z\mapsto e^{\gamma d(z,w)}$. Its change in norm is at most $J(e^{\gamma R}-1)\le c/4$, so the inverse norm is at most $(c/4+x)^{-1}$. Its $(z,w)$ entry gives the first estimate in (1.7). The Stieltjes identity
$$A_e(s)^{-1/2}={1\over\pi}\int_0^\infty x^{-1/2}(A_e(s)+x)^{-1}\,dx$$
gives the second estimate and holomorphy. The subtracted resolvent identity
$$\log A_e(s)=\int_0^\infty[(1+x)^{-1}I-(A_e(s)+x)^{-1}]\,dx$$
converges at infinity as $x^{-2}$ and gives the principal logarithm. When all bonds joining selected unions have parameter zero, (1.2) is a direct sum, as are $P_e,Q_e$; inversion and these integrals preserve direct sums. The endpoint identity follows from $H(\mathbf1)=H$ and BASE-KERNEL-2.md Lemma 1.1. $\square$

For a complex background satisfying $e_z\cdot e_z=1$, the same family is analytic in $(e,\alpha,s)$ on any neighbourhood where
$$\|A_e(s)-A_{e^0}(r)\|\le c/2 \tag{1.9}$$
for a real unit reference $e^0$ and real $r\in[0,1]^{\mathcal E}$. The proof is the same accretivity perturbation. This is a norm criterion, not a claim that the H7 domain satisfies it. The actual chart multiplier must be shown to meet (1.4) or another uniform coercivity condition.

This theorem supplies a nondegenerate reference at $s=\mathbf0$ and exact block-component locality, including in regime (B) with large nonnegative $\nu$. It avoids the $k\ge1$ premise of Localization.XSetting.hk and Dec2.XCover.hk and the one-layer mass ceiling Dec2.OpSetting.massLe. The footprint declarations Dec2.FootLocalGeom, FootLocal, Gs_local_fp, dg5'_fp and i4b_local_fp in Localization/Decoupled2Fp*.lean instead give exact locality for scalar Dec2.Gs after CoverBase, AdmPot, incidence-union and parameter-agreement premises are met. Dec2.XFootLocal retains $k\ge1$. None identifies its output with (1.3). Conversely, Theorem 1.1 does not prove Balaban's chosen cube-parameter norm, background response, torus-lift identity or H7 radius. Converting the edge parameters to the source's cube-labelled localization remains work.

## 2. The exact cutoff footprint

Let $D_+=\Omega''_1$ be the integrated chart sites and $D_-=\Omega_1\setminus\Omega''_1$ the retained chart sites, intersected with the component. The old base factor is
$$\prod_{c\in P_1}(1-A_cB_c)\prod_{c\notin P_1}A_cB_c, \tag{2.1}$$
where $A_c=$ chiBlockA, $B_c=$ chiBondB, and $A_cB_c=$ chiPrimeZero in LargeField/Base/BaseRecord.lean. Every bond with an endpoint in $c$ is tested. The landed BaseHistory.base_P_nbhd_compl and base_bond_comp imply that a failed $P_1$ factor tests only retained spins: $P_1^{\sim3}\subset\Omega_1^c$, and a bond touching a $P_1$ cube lies in that outside component. No factor in the first product of (2.1) is deleted by integration over $D_+$.

For $c\notin P_1$, let its full test footprint $F(c)$ contain all fine sites in blocks used by $A_c$, both endpoints of bonds used by $B_c$, and every site in its regime-(B) test. Put
$$\mathcal J_+=\{c\notin P_1:F(c)\cap D_+\ne\varnothing\}. \tag{2.2}$$
This includes a good cube outside $D_+$ if a tested bond crosses $\partial D_+$. If the three strict background margins of BASE-KERNEL-2.md Lemma 2.1 hold on every $F(c)$, $c\in\mathcal J_+$, then $A_cB_c=1$ there. Deleting precisely those good factors leaves an old factor independent of integrated spins. This is the exact real pointwise identity proved in that lemma by block-average contraction and bond/site triangle inequalities.

**The missing record-wide implication is quantitative.** BaseSupport.baseSpinSupport_of_baseRecord in LargeField/Base/BaseSupport.lean derives strict old tests on the data sites from chiPrimeZero $=1$ off $P_1$. It does not strengthen $|\partial\phi|<\delta_0$ to the $\delta_0-2r$ margin of BASE-KERNEL-2.md (2.2), nor does BaseRecord contain a chart-displacement bound. For $0<r<\delta_0$, real unit spins on one bond can have a difference in $(\delta_0-r,\delta_0)$, so the old strict test alone has no uniform slack. This refutes only a deduction from the old test; an implication from additional output and fluctuation restrictions may still hold.

LF-RECONSTRUCTION Lemma III.7.1 supplies a later window implication with response estimates and says it also proves P5 Lemma 2.1. Its retained factors are $N=\tilde\chi_k\chi_S\chi^0\chi''$, at scales $k_1\le j\le k$, with a composed background. To apply that proof to the first step, one must give the base substitutions and check both cases for every footprint (2.2), including both ends of a bond crossing $\partial\Omega''_1$. P6 (2.2) removes the next old function where the new one is present; it alone does not establish the base footprint implication. No landed BaseRecord, baseF or chiPrimeZero theorem states the requisite margins. The real identity, once proved, permits a holomorphic extension of the *reduced integral* as in BASE-KERNEL-2.md Lemma 3.1; the characteristic functions themselves are not extended.

## 3. Exact transfer from the landed marked theorem

Use the notation of Polymer/MarkedCubes.lean and Polymer/MarkedCubesLocal.lean: $\mathfrak B$ is CubeB, $\Omega$ is the union of fluctuation blocks, $Lb$ is a finite label type, $\mathrm{Lab}$ is CubeLabels $m_0\,j\,\Omega\,Lb$, $\mu=\bigotimes_{b\in\mathfrak B}\mu_b$ is a product of probability measures on measurable block spaces, and $A$ is LabelAct $\mathrm{Lab}\,\Omega_b\,\epsilon_H\,\kappa_H\,\kappa_0\,K_c$. For each mark label $y$, suppose a measurable $G_y$ satisfies
$$\operatorname{DepOn}(\operatorname{blocksOf}(y))G_y,\qquad
\|G_y(\Phi)\|\le F_0e^{-\kappa_G\,\mathrm{dl}(y)}. \tag{3.1}$$
Assume $L^{m_0}\mid N_1$, $j\le K$, IsPiUnion $m_0\,j\,\Omega$, and the exact numerical premises of Fluctuation.marked_cubes_explicit:
$$\begin{gathered}
\kappa_0\ge a_{\rm Ent}(d,L)+1,\quad K_c\ge K_0(d,L,\kappa_0)+1,\quad
\epsilon_H,F_0>0,\quad \kappa'\ge0,\quad \kappa_G\ge\kappa_H,\\
\kappa_H\ge\kappa'+3\kappa_0+c_1(d,L)+\tfrac32,\\
\epsilon_H\le[8K_c^3c_1(d,L)
\exp\{(\kappa_H-2\kappa_0)c_G(d,L)+c_1(d,L)+\kappa'c_G(d,L)\}]^{-1}.
\end{gathered} \tag{3.2}$$
These are theorem premises, not consequences of the base record.

**Lemma 3.1 (proved, summing one-mark coefficients).** If $\kappa'\ge1$ and $\kappa_b=\kappa'-1$, then for every nonempty finite $Y\subset\mathfrak B$, the sum of the canonical Gst coefficients furnished by marked_cubes_explicit,
$$R(Y)=\sum_{y\in Lb}\operatorname{Gst}(\mu,\mathrm{Lab},A.H,\operatorname{blocksOf}(y),G_y;Y), \tag{3.3}$$
vanishes unless $Y$ contains the block support of at least one mark, and
$$|R(Y)|\le C_{\rm PE}(d,L,K_c,\kappa_H,\kappa_0,\kappa')K_cc_1(d,L)F_0
e^{-\kappa_b d_{\rm Ext}(Y)}. \tag{3.4}$$
If dOmega $m_0\,j\,\Omega\,(\operatorname{sitesOf}Y)\ne\top$, CubeSystem.dExt_eq_toReal identifies $d_{\rm Ext}(Y)$ with the finite modular covering size $d_\Omega(\operatorname{sitesOf}Y)$.

*Proof.* The one-mark theorem makes a term zero unless $\operatorname{blocksOf}(y)\subset Y$, and otherwise bounds it by $C_{\rm PE}F_0e^{-\kappa_0\mathrm{dl}(y)}e^{-\kappa'd_{\rm Ext}(Y)}$. Every contributing mark has a block in its nonempty support, by CubeLabels.blocksOf_nonempty. Sum first over a possible block $b\in Y$ and use LabelAct.entropy at $b$:
$$\sum_{y:\operatorname{blocksOf}(y)\subset Y}e^{-\kappa_0\mathrm{dl}(y)}\le |Y|K_c. \tag{3.5}$$
CubeSystem.card_le_dExt gives $|Y|\le c_1(d,L)(1+d_{\rm Ext}(Y))$. Since dExt_nonneg and $1+t\le e^t$ for $t\ge0$, one unit of exponential rate absorbs this factor. This proves (3.4). The final identification is exactly dExt_eq_toReal, not an implicit replacement by a different P5 size. $\square$

Fluctuation.marked_cubes_two requires the stronger smallness condition with $16$ replacing $8$ in (3.2). For two marks with bounds $F_0,F_1$, it gives a connected coefficient bounded by
$$C_{\rm PE2}F_0F_1e^{-\kappa_0(\mathrm{dl}(y_0)+\mathrm{dl}(y_1))}
e^{-\kappa'd_{\rm Ext}(Y)}, \tag{3.6}$$
zero unless both supports lie in $Y$. This is an available connected response estimate; it does not prove the model's mark bounds (3.1). MarkedCubesHolo.lean and MarkedCubesLocal.lean provide analytic and congruence tools once their hypotheses are established.

P6 Lemma 4.2, following (4.29)--(4.31), states a localized mark bound with $\epsilon=\mathrm{const.}\,\beta_k^{-m-2}$ and permits the weaker $\epsilon=\beta_k^{-m-3/2}$; its proof of P5 Proposition 3.2 uses the latter. That is the ordinary later-step mark of P5 (3.9), including the comparison displacement $\delta^{(k)}_0$. At $k=0$ the old $\delta\mathscr E_0,\delta\mathscr F_0,\delta\mathcal R^{(0)}$ terms are absent, but the hard-spin chart Jacobian, mixed normal term and covariance/background localization remain. Lemma 4.2 therefore does not supply (3.1) for the base mark by substitution alone.

**Corollary 3.2 (proved, half-budget arithmetic).** Suppose the actual first-step construction identifies its remainder coefficient with $R(Y)$ of (3.3) plus one determinant coefficient and satisfies (3.1)--(3.2) uniformly with
$$F_0=C_m\beta_0^{-m-3/2},\qquad
C_{\rm mark}=C_{\rm PE}K_cc_1(d,L)C_m+C_{\rm det}, \tag{3.7}$$
and the separately localized determinant coefficient is at most $C_{\rm det}\beta_0^{-m-3/2}e^{-\kappa_b d_{\rm Ext}(Y)}$ for every admissible $Y$. If
$$\beta_1/\beta_0\le B_L:=2L^{d-2},\qquad
\beta_0\ge(2C_{\rm mark}B_L^{m+1})^2, \tag{3.8}$$
then
$$|\mathcal R_m^{(1)}(Y)|\le\tfrac12\beta_1^{-m-1}e^{-\kappa_b d_{\rm Ext}(Y)}. \tag{3.9}$$
Indeed (3.4) gives $C_{\rm mark}\beta_0^{-m-3/2}$. The second inequality of (3.8) yields $C_{\rm mark}\beta_0^{-1/2}\le\frac12B_L^{-(m+1)}\le\frac12(\beta_0/\beta_1)^{m+1}$; multiply by $\beta_0^{-m-1}$. Thus the stronger $\beta_0^{-m-2}$ premise of BASE-KERNEL-2.md Lemma 3.2 is sufficient but not necessary for the arithmetic. The P6 exponent also suffices with the squared threshold (3.8).

To obtain Proposition II.7.9, the first chart integral still needs actual product reference measures $\mu_b$, labels and activities $A.H$, and marks $G_y$; measurability, DepOn support, entropy, (3.1), (3.2), and equality with the base P5 (3.9) marked expectation must be proved. The determinant needs a compatible local expansion and the whole-torus equality of P5 Proposition 3.2. The cube set $Y$ must be identified with the paper's localization domain, with the finite dOmega or modular-domain statement proved. The resolvent of §1 alone gives no LabelAct bound. The margin implication of §2 is needed before the fixed real fluctuation cutoff can be absorbed in the product measures.

## 4. Closure

Theorem 1.1 proves a base decoupled resolvent, principal matrix functions, decay and exact block-component locality under (1.4), for both mass regimes. Lemma 3.1 proves the marked-polymer resummation after its model inputs are supplied, and Corollary 3.2 proves the half-budget from a P6-strength localized base mark. The base record proves the $P_1$ witness factors do not read integrated spins. Proposition II.7.9 still requires verification of the chart multiplier and H7 domain for §1, conversion to the required cube localization, the record-wide margins on (2.2), and the first-step LabelAct, mark, determinant and I-7 estimates. Until then BASE-KERNEL.md remains conditional at the first small-field integral.
