# Round 37 — the high-mass heavy object

**PROVED (scope).** Fix $d\ge3$, $N\ge2$, $m=N-1$, $L\ge3$, $s=ML$, $\nu_*:=7/(8L^2)\le\nu\le1$, a unit vector $h$, and $\beta\ge1$. Write $r_\beta=A\log(\beta a)/\sqrt\beta$ with fixed $A>0,a>1$, $\delta_\beta=r_\beta/\sqrt\nu$, $K_\Lambda=-\Delta_\Lambda+\nu$, and $q=2d/(2d+\nu_*)<1$, $\eta=-\log q$. The physical good test is $\chi_Q=\mathbf1\{\max_{x\in Q}|\phi_x-h|<\delta_\beta\}$ on each $s$-block $Q$.

**OPEN (verdict).** Neither LF-BASE-KF0.md Parts B,F,G nor LF-BASE-KF0-H.md H.1–H.4 proves CompleteHeavyLocality. A physical-space decomposition gives a stronger boundary estimate and an exact common-product sector sum, but it has not been rewritten as gasXiOp with bounded, finite-DepOn heavy functions satisfying (K0.6). The one-scale theorem and KF0RootFPartial therefore remain conditional.

## 1. Physical-space boundary: what square completion proves

**PROVED (exact split).** For a bad block set $B$, let $D=D_B$ be its sites, $G=\Lambda\setminus D$, and $q=\phi_D$. The identity (K0.2) of KF0.md retains all crossing bonds. On $G$, $K_G=(2d+\nu)I_G-A_G$ is the principal Dirichlet matrix, and its diagonal crossing degree is $D_\partial(x,x)=d_\partial(x):=\#\{y\in D:y\sim x\}$; thus $K_G\ge D_\partial+\nu I$.

**PROVED (force and charge).** For a crossing edge $e=(x,y)$ with $x\in G,y\in D$, set $a_e=h-q_y$, $S(q)=\sum_e|a_e|^2$, and $J_q(x)=\sum_{e=(x,y)}P_{h^\perp}a_e$. Formula (K0.5) has tangent boundary energy $\frac12\langle v,K_Gv\rangle+\sqrt\beta\langle J_q,v\rangle+\frac\beta2S(q)$; its remaining boundary term is $\sqrt\beta\sum_e(a_e\cdot h)n_\beta(v_x)$, where $n_\beta(v)=\sqrt\beta(\sqrt{1-|v|^2/\beta}-1)$.

**PROVED (explicit Schur bound).** Let $E$ copy each good-site tangent vector to its crossing edges, so $E^*E=D_\partial$ and $J_q=E^*P_{h^\perp}a$. From $K_G\ge D_\partial+\nu I$,
$$\langle J_q,K_G^{-1}J_q\rangle\le\|E(D_\partial+\nu I)^{-1}E^*\|\,S(q)\le\theta S(q),\qquad
\theta:=\frac{2d}{2d+\nu_*}<1.\tag{H37.1}$$
**PROVED (why the constant works).** The nonzero eigenvalues of $E(D_\partial+\nu I)^{-1}E^*$ are $d_\partial(x)/(d_\partial(x)+\nu)$; $d_\partial(x)\le2d$ and $\nu\ge\nu_*$. Orthogonal projection cannot enlarge $S(q)$.

**PROVED (completed square).** The tangent expression is exactly $\frac12\langle v+\sqrt\beta K_G^{-1}J_q,K_G(v+\sqrt\beta K_G^{-1}J_q)\rangle+\frac\beta2(S(q)-\langle J_q,K_G^{-1}J_q\rangle)$. Its shifted physical tangent mean is $-K_G^{-1}J_q$ and the Gaussian factor left by the shift is at most $e^{-\beta(1-\theta)S(q)/2}$.

**PROVED (normal term on the actual good domain).** Unit length of $q_y$ gives $a_e\cdot h=|a_e|^2/2\ge0$. On $\chi_G=1$, $|v_x|\le\sqrt\beta\,\delta_\beta\le A\log(\beta a)/\sqrt{\nu_*}$ and $0\le-\sqrt\beta n_\beta(v_x)\le|v_x|^2$. Thus the normal boundary term can cost at most $A^2\log^2(\beta a)S(q)/(2\nu_*)$ in the exponent. If
$$\frac{A^2\log^2(\beta a)}{\nu_*}\le\frac{\beta(1-\theta)}2,\tag{H37.2}$$
the tangent and normal boundary factors together are bounded above by $e^{-\beta(1-\theta)S(q)/4}$ after square completion; the nonnegative normal quadratic energy only helps.

**PROVED (scope of H37.2).** For fixed $d,L,A,a$, (H37.2) holds for all sufficiently large $\beta$. This is an upper bound on the restricted real integrand. It neither replaces the crossing factor in the exact identity nor compares the restricted shifted Gaussian with an unshifted good-region partition function.

## 2. The collar is not fixed at one block

**PROVED (massive inward decay).** The killed-walk expansion $K_G^{-1}=a_\nu^{-1}\sum_{n\ge0}(A_G/a_\nu)^n$, $a_\nu=2d+\nu$, gives, for $t=\operatorname{dist}(x,\partial G)$,
$$|(K_G^{-1}J_q)(x)|\le\frac{\|J_q\|_\infty}{\nu}q^t\le\frac{2d\,u(q)}{\nu_*}q^t,\quad
u(q):=\max_{e\ {\rm crossing}}|h-q_{y(e)}|\le2.\tag{H37.3}$$
**PROVED (finite-walk locality).** Each summand in this formula and each truncated Dirichlet inverse uses only paths contained in $G$ of its stated length; the residual tail is bounded by $\nu_*^{-1}q^R$ in row sum. A fixed full covariance decay bound alone does not turn the cutoffs or Jacobians into finite-support factors.

**REFUTED (uniform one-block collar).** For one bad spin $q_y\ne h$ with nonzero tangential component, $J_q\ne0$, and positivity of the killed Green kernel gives a nonzero physical mean at a good site just outside any fixed finite collar on a sufficiently large torus. That mean is independent of $\beta$, while $\delta_\beta\to0$; hence no fixed number of $s$-blocks keeps the shifted mean inside the shrinking good chart for every $\beta$. Enlarging the fixed $M$ before $\beta_0$ cannot change this conclusion.

**PROVED (adaptive radius).** The sufficient site radius
$$R(q,\beta)=\left\lceil\eta^{-1}\log_+\!\left(\frac{4d\,u(q)}{\nu_*\delta_\beta}\right)\right\rceil\tag{H37.4}$$
makes the right side of (H37.3) at most $\delta_\beta/2$ outside that collar. At a threshold-sized bad spin, $u(q)=O(\delta_\beta)$, the radius is bounded after $L$ is fixed; at $u(q)\asymp1$ it grows as $\eta^{-1}\log\beta/2$.

**PROVED (numerical energy budget).** If $a_Q=\max_{y\in Q}|q_y-h|\ge\delta_\beta$ for each bad block, the core mass contributes at least $\frac{\beta\nu}2\sum_{Q\in B}a_Q^2$. A collar of radius $R_Q=\lceil\eta^{-1}\log_+(C_La_Q/\delta_\beta)\rceil$ uses at most $C_d(1+R_Q/s)^d$ blocks per $Q$. For fixed $L,M,d,C_L,C_d$ and $0<c<A^2\nu_*/4$, sufficiently large $\beta$ makes
$$\frac{\beta\nu_*}4a_Q^2\ \ge\ c\log\beta\,C_d(1+R_Q/s)^d+c\log^2(\beta a),\qquad a_Q\in[\delta_\beta,2].\tag{H37.5}$$
**PROVED (reason for H37.5).** Put $t=\sqrt\beta a_Q\ge A\log(\beta a)/\sqrt\nu\ge A\log(\beta a)$. The collar term is bounded by $C_{L,M,d}[1+\log_+^d(Ct/\log(\beta a))]$, and $\log_+^d u\le C'_d(1+u)$; $t^2$ dominates its product with $\log\beta$ uniformly for $t\ge A\log(\beta a)$. Thus a variable collar is not numerically ruled out by entropy or polynomial normalization losses.

**OPEN (collar proof).** H37.5 does not construct compatible heavy objects. One must integrate the good spins swallowed by each collar, prevent double use when collars overlap, retain every hard cutoff and Jacobian, and prove a local bound after that integration. No such theorem is in the cited notes or landed Lean files.

## 3. Exact common reference and the hole determinant

**PROVED (one fixed product space for sector sums).** Normalize sphere measure to probability $\sigma$, put $c_\beta=a_N^{-1}(2\pi/\beta)^{m/2}$ with $a_N=|\mathbb S^{N-1}|$, and let $\mu=\bigotimes_{Q}(\sigma^{Q}\otimes\gamma_m^{Q})$. For each $B$ use only $q_D$ and $\psi_G$; unused coordinates integrate to one. Set $v=K_G^{-1/2}\psi_G$, $\Phi_x^+(v)=h+\beta^{-1/2}(v_x+n_\beta(v_x)h)$, and $\mathcal J_G(v)=\prod_{x\in G}\mathbf1_{\{|v_x|^2<\beta\}}(1-|v_x|^2/\beta)^{-1/2}$.

**PROVED (exact fixed-reference sector identity).** With $G_S=c_\beta^{|S|}(\det K_S)^{-m/2}$, $G_\varnothing=1$, $N_0=G_\Lambda$, and $R_{\det}(B)=G_G/G_\Lambda$, the normalized-sphere partition function is
$$Z_\Lambda^{\rm prob}(g)=N_0\int d\mu\sum_{B\subset\mathcal Q_s}R_{\det}(B)\,
\prod_{Q\in B}(1-\chi_Q(q))\prod_{Q\notin B}\chi_Q(\Phi^+(v))\,\mathcal J_G(v)
\exp\!\left[-\beta H_B(q)-\beta H_G(\Phi^+(v)\mid q)+\tfrac12\langle\psi_G,\psi_G\rangle+
\langle g_D,q\rangle+\langle g_G,\Phi^+(v)\rangle\right].\tag{H37.6}$$
**PROVED (normalization check).** Multiplying (H37.6) by the product Gaussian density cancels its $+\frac12\langle\psi_G,\psi_G\rangle$ term; the chart change of variables supplies $G_G\mathcal J_G$. The factor $a_N^{-|G|}$ in $c_\beta$ is required for normalized sphere measure. All internal and crossing bonds are in $H_B+H_G$, every indicator appears once, and $N_0$ is source independent; the frozen unnormalized partition has an additional source-independent $a_N^{|\Lambda|}$.

**REFUTED (H37.6 as gasXiOp).** The measure $\mu$ is common, but the summand uses the $B$-dependent map $K_G^{-1/2}\psi_G$ and $R_{\det}(B)$. It is not a product of local heavy and ordinary weights, and the good-chart Jacobians are unbounded before suitable integration. A common reference measure alone does not supply gasOp_eq or the Bdd/DepOn hypotheses of gasOp_pe.

**PROVED (exact determinant walk formula).** For $a_\nu=2d+\nu$, adjacency $A_\Lambda$, and $A_G$ its principal restriction, let $\mathscr W_n(D)$ be the rooted closed nearest-neighbour walks of length $n$ on $\Lambda$ visiting $D$, with adjacency multiplicity. The absolutely convergent identity is
$$\log\frac{G_G}{G_\Lambda}=-|D|\log c_\beta+\frac m2\left[|D|\log a_\nu-
\sum_{n\ge1}\frac{|\mathscr W_n(D)|}{n\,a_\nu^n}\right].\tag{H37.7}$$
**PROVED (walk bound and lift).** Since $|\mathscr W_n(D)|\le n|D|(2d)^n$, the loop sum is at most $|D|q/(1-q)$, and its terms of length at least $R$ total at most $|D|q^R/(1-q)$. Each finite walk has exact path support and agrees under a nonwinding torus lift; a loop visiting two bad cores couples them and must be assigned to one connected activity, not independently to both cores.

**PROVED (determinant scale).** Jacobi's principal-minor identity also gives $\det K_G/\det K_\Lambda=\det(K_\Lambda^{-1})_{DD}$ and $R_{\det}(B)\le[c_\beta^{-1}(4d+\nu)^{m/2}]^{|D|}$. This costs $O(|D|\log\beta)$, which H37.5 can pay numerically, but it proves no local factorization of the restricted good integral.

## 4. Comparing the three routes and the literal GAS interface

**OPEN (route a: physical first).** The sector sum (H37.6), boundary bound (H37.1)–(H37.2), and loop formula (H37.7) are usable starts. The open step is an exact linked expansion of the $B$-dependent Dirichlet Gaussian, moving good indicators, integrated collar spins, Jacobians and loop interactions into finite-support functions with a support-size estimate. The ordinary finite-walk Taylor expansion (F.8) only treats the all-plus product-cutoff sector.

**REFUTED (route b: bare Gaussian shells).** LF-BASE-KF0-H.md H.3 yields $\int|K_R|\le e^{-h_\beta^*|D|}q^{R/4}$ for a bare marked kernel, but its ball support can contain order $(R/s)^d$ blocks. For fixed $\beta$ and growing torus no $e^{-h|S_R|}$ follows when $d\ge3$; the kernel omits exterior Jacobians and crossing bonds and so is not an exact factor of (F.4). The square-root cusp in H.4 also rules out a naive derivative-per-edge estimate.

**OPEN (route c: adaptive two-step collar).** A plausible next construction integrates physical bad cores and the adaptive collars of (H37.4), then expands the remaining shifted Dirichlet field by finite walks. H37.5 pays possible $O(\log\beta)$ losses per collar block, but exact overlap bookkeeping, conditional chart moments after collar integration, and a sparse-support rather than ball-support expansion remain unproved. No route currently closes (K0.6).

**PROVED CONDITIONAL ON CompleteHeavyLocality and HeavyGeometry (GAS entry).** For the connected block metric $d(X)=|X|$, connected supports give hzd with $c_2=1$, hG3 with $c=0$, hG1 with $c_1=1$, and hG3P with $c_P=0$. A single grouped heavy index per connected $v$-block support gives hcount with $K_{0h}=(2d)^2$; any retained decorations need a separately proved exponential count or must be summed into that function.

**PROVED CONDITIONAL ON CompleteHeavyLocality, HeavyGeometry and OrdinaryMayerInput (remaining GAS entry).** gasOp_pe additionally requires nonempty support, $\mathrm{core}_z\subset S_z$, exact DepOn and Measurable for both kinds of function, Bdd for each, pointwise $|\beta_y|\le B_0e^{-\kappa''|c_y|}$, and $\int|\tau_z|d\mu\le e^{-p-h|S_z|}$. If ordinary indices through a block with support size $v$ number at most $D_0^{v-1}$, hent follows with $K_{0g}=e^{-(\kappa''-\kappa_g)}/[1-D_0e^{-(\kappa''-\kappa_g)}]$ when $\kappa''-\kappa_g>\log D_0$; hG2P similarly holds with $K_{0P}=e^{-\kappa_{0P}}/[1-(2d)^2e^{-\kappa_{0P}}]$ when $\kappa_{0P}>2\log(2d)$.

**PROVED CONDITIONAL ON CompleteHeavyLocality, HeavyGeometry and OrdinaryMayerInput (numeric GAS entry).** With the preceding $c,c_1,c_2,c_P$, its literal numerical conditions reduce to $h\ge B_0e^{B_0}K_{0g}+\kappa_g+4+\log K_{0h}$, $\kappa'+\kappa_{0P}+1\le\kappa_g-2$, and $3e^{1-p}K_{0P}\le1$, besides positivity and $\kappa_g\le\kappa''$. The conditional estimates in H37.1–H37.7 do not supply the missing DepOn, Bdd, hτ, hent or exact gasXiOp identity.

## 5. Smallest useful replacement target and Lean order

**OPEN — DirectK0PolymerInput (replacement for CompleteHeavyLocality).** Instead of individual heavy functions, construct connected $s$-block activities $K_\Lambda(Y;g)$ and a source-independent $N_\Lambda$ such that $Z_\Lambda^{\rm prob}(g)=N_\Lambda e^{\langle g,h\rangle}\Xi_\Lambda(K_\Lambda(\cdot;g))$ exactly. Require $K_\Lambda(Y;\cdot)$ analytic on $\|g\|_1<1$, dependent only on $g|_Y$, identical on nonwinding torus lifts, and $|K_\Lambda(Y;g)|\le\epsilon_\beta e^{-\kappa_0|Y|}$ uniformly, with $\epsilon_\beta\to0$. This asks for the linked physical-space activity directly and drops the stronger per-object Bdd, DepOn, common-product GAS and support-size heavy norm.

**PROVED CONDITIONAL ON DirectK0PolymerInput (one-scale implication).** Choose $\kappa_0>\kappa'+2\log(2d)$, then for sufficiently small $\epsilon_\beta$ choose $\alpha_\beta=C\epsilon_\beta\to0$ so $q_{\rm PE}=(2d)^2e^{-(\kappa_0-\kappa'-\alpha_\beta)}<1$ and $\epsilon_\beta e^{-(\kappa_0-\kappa'-\alpha_\beta)}/(1-q_{\rm PE})\le\alpha_\beta$. FrozenTorus.pe_blockTorus_frozen gives $p_X=\mathrm{frozenPY}(K)_X$ with $|p_X|\le\alpha_\beta e^{-\kappa'|X|}$; Holomorphic.pe_PY_analyticOnNhd and BoxTransport.frozenPY_boxMap supply analytic and exact-lift transfer once their stated hypotheses are checked. Cancelling $N_\Lambda$ yields (K0.1), hence KF0.md's Cauchy argument gives the restricted Root-F clauses.

**OPEN (what the replacement does not solve).** DirectK0PolymerInput is weaker as an interface but remains a substantial model theorem: no cited source constructs its activities from (H37.6) or proves their uniform bound. A new tree-influence GAS theorem is another possible interface, but H.2's affine $L^1$ modulus alone does not establish the repeated-difference/tree norm such a theorem would need.

**PROVED (Lean package H37-1; after K2a).** In at most 300 new lines, formalize $K_G\ge D_\partial+\nu I$, the incidence-map proof of (H37.1), and the exact tangent square identity. Inputs: K2a's (K0.3)–(K0.5) and finite positive-matrix order; mathematical proof above, routine transport.

**PROVED (Lean package H37-2; after H37-1).** In at most 300 new lines, formalize $a_e\cdot h=|a_e|^2/2$, the normal-coordinate inequality, and (H37.2), retaining the real good indicator. Inputs: B2's normalCoord and K2a's chart formula; mathematical proof above, routine.

**PROVED (Lean package H37-3; after K1).** In separate at-most-300-line files prove the killed-walk inverse, (H37.3), exact path locality, and the determinant trace expansion (H37.7) with its tail and nonwinding lift. Inputs: K1 gap, adjacency walk algebra; mathematical proof above, new finite-matrix transport.

**PROVED (Lean package H37-4; after K2a and H37-3).** In at-most-300-line pieces formalize the common product $\mu$, exact sector identity (H37.6), Gaussian normalization including $a_N^{-1}$, and the principal-minor bound. Inputs: SphereChart.toSphere_eq_graph, K2a and finite Gaussian change of variables; mathematical identities above, new measure bookkeeping.

**OPEN (Lean package H37-5; after H37-1 through H37-4).** State adaptive-collar selection (H37.4) and budget (H37.5) in at-most-300-line lemmas; then prove an exact linked activity construction from (H37.6), including overlap resolution, integrated chart factors, connected sparse supports and exact lift. The numerical lemmas are routine; the linked construction is the new mathematical gap and must be split into bounded statements before assigning proof workers.

**PROVED CONDITIONAL ON DirectK0PolymerInput (Lean package H37-6).** In at-most-300-line modules, instantiate pe_blockTorus_frozen, pe_PY_analyticOnNhd, and frozenPY_boxMap, then KF0.md's Cauchy bridge to KF0RootFPartial. This is conditional assembly, not a proof of the full frozen logPartition_multiscale, whose low-mass branch is separate.
