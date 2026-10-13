# Round 38 — linked one-scale activities

**PROVED (scope).** Use the notation of KF0.md and KF0-HEAVY.md: $d\ge3$, $N\ge2$, $m=N-1$, $\nu_*:=7/(8L^2)\le\nu\le1$, $s=ML$, $q=2d/(2d+\nu_*)$, $\eta=-\log q$, and $\delta_\beta=A\log(\beta a)/\sqrt{\beta\nu}$. Sources satisfy $\|g\|_1<1$. All claims concern finite admissible tori; constants may depend on fixed $d,N,L,M,A,a,b$ but not on the torus, $\nu$, unit $h$, or $\beta$ after its threshold.

**OPEN (verdict).** The physical collars, determinant loops, and finite-walk formula below give exact identities and some sharp numerical bounds. They do not give a uniform bound on the connected activities when the hard-chart and Gaussian cutoffs are removed. DirectK0PolymerInput, and therefore the high-mass one-scale theorem, remains OPEN. The missing statement is an integrated linked hard-chart estimate, stated precisely in §5.

## 1. Corrected mean threshold and dressed components

**REFUTED (H37.4 as an expansion threshold).** H37.4 makes the physical mean outside a collar at most $\delta_\beta/2$, hence its tangent Gaussian coordinate can still be as large as $\sqrt\beta\delta_\beta/2=A\log(\beta a)/(2\sqrt\nu)$. This grows with $\beta$ and cannot be treated as a small insertion in the ordinary Taylor majorant (F.12).

**PROVED (per-core decomposition).** For each bad $s$-block $Q$, set $a_Q=\max_{y\in Q}|q_y-h|\in[\delta_\beta,2]$. Split the boundary source $J_q=\sum_{Q\in B}J_Q$, where $J_Q$ uses crossing edges whose bad endpoint is in $Q$, and let $m_Q=-K_G^{-1}J_Q$. The killed-walk row bound gives
$$|m_Q(x)|\le \frac{2d}{\nu_*q}\,a_Q\,q^{\operatorname{dist}(x,Q)}.\tag{L38.1}$$
**PROVED (why L38.1 holds).** Each $J_Q$ is supported at good sites adjacent to $Q$ and has sup norm at most $2d a_Q$. A walk from $x$ to that support takes at least $\operatorname{dist}(x,Q)-1$ steps, and its residual row sum is at most $\nu_*^{-1}q^{(\operatorname{dist}(x,Q)-1)_+}$.

**PROVED (uniform multi-core summation).** Define $D_{d,L}:=\sum_{r\ge0}(2r+1)^d q^{r/2}<\infty$ and $C_L:=4dD_{d,L}/(\nu_*q)$. For each bad block freeze the radius
$$R_Q:=\left\lceil\frac2\eta\log_+\!\bigl(C_L\sqrt\beta\,a_Q\log(\beta a)\bigr)\right\rceil.\tag{L38.2}$$
**PROVED (correct Gaussian-unit bound).** If $x$ lies outside the site-radius-$R_Q$ neighborhood of every bad block, then
$$\sqrt\beta\,\left|\sum_{Q\in B}m_Q(x)\right|\le \frac1{2\log(\beta a)}.\tag{L38.3}$$
**PROVED (proof of L38.3).** For $r=\operatorname{dist}(x,Q)\ge R_Q$, (L38.2) implies $\sqrt\beta a_Qq^{r/2}\le[C_L\log(\beta a)]^{-1}$. Split $q^r=q^{r/2}q^{r/2}$ in (L38.1). The number of distinct blocks whose distance from $x$ equals $r$ is at most the number of sites in the radius-$r$ ball, bounded by $(2r+1)^d$; summing gives $D_{d,L}$ and the factor $1/2$. Thus the estimate does not silently multiply a one-core error by $|B|$.

**PROVED (closure definition).** Let $C_Q$ be the set of $s$-blocks intersecting the site-radius-$R_Q$ neighborhood of $Q$. Form the finite graph on bad blocks with an edge when $C_Q$ and $C_{Q'}$ meet or touch by one block edge. A dressed component is a graph component $I$, with core $I$ and support $S_I=\bigcup_{Q\in I}C_Q$. This is the closure operation; the radii are frozen before merging.

**PROVED (termination and compatibility).** Finite graph components terminate without an iterative radius update. Each $S_I$ is connected, distinct supports neither meet nor touch, and $\sum_I|S_I|\le\sum_{Q\in B}|C_Q|$. There is a dimension constant $c_d$ such that $|C_Q|\le c_d(1+R_Q/s)^d$.

**PROVED (new collar budget).** For any fixed $C_{\rm loss}>0$ and $0<c<A^2\nu_*/4$, sufficiently large $\beta$ gives, uniformly for $a_Q\in[\delta_\beta,2]$,
$$\frac{\beta\nu_*}{4}a_Q^2\ge C_{\rm loss}\log(\beta a)\,c_d(1+R_Q/s)^d+c\log^2(\beta a).\tag{L38.4}$$
**PROVED (proof of L38.4).** Put $t=\sqrt\beta a_Q\ge A\log(\beta a)$. At the smallest $t$, (L38.2) gives $R_Q=O_{L,M}(\log\log\beta)$, so the collar cost is $O(\log\beta(\log\log\beta)^d)=o(\log^2\beta)$; the remaining left coefficient is at least $A^2\nu_*/4$. For larger $t$, $[1+\log^d(Ct\log\beta)]/t^2$ is eventually decreasing on $t\ge A\log\beta$, so the same ratio bound holds uniformly. The volume factor $s^d$ for any fixed per-site polynomial normalization loss can be absorbed into $C_{\rm loss}$.

**REFUTED (a polynomially small Gaussian mean from this budget).** Replacing $1/\log\beta$ in (L38.3) by $\beta^{-c_0}$ with fixed $c_0>0$ makes $R_Q\asymp(2c_0/\eta)\log\beta$ even for $a_Q\asymp\delta_\beta$. The collar then has order $(\log\beta)^d$ blocks, and an $O(\log\beta)$ loss per block is order $(\log\beta)^{d+1}$, larger than that core's $O(\log^2\beta)$ charge for $d\ge3$.

**OPEN (what L38.4 does not pay automatically).** A collar may contain good spins with a moving hard indicator and a square-root chart Jacobian. L38.4 pays a *specified polynomial normalization loss* after such an integrated bound is proved; it is not itself an estimate for that integral or for interactions between distinct dressed components.

## 2. Exact factor ledger for the physical sector identity

**PROVED (sector reindexing).** In (H37.6), each configuration has a unique bad set $B$ and, for fixed bad spins $q$, the closure above has a unique family $\{(I,S_I)\}$ of pairwise non-touching dressed components. Insert the corresponding closure indicator and sum over those families. This is an exact reindexing of (H37.6), including $B=\varnothing$; it does not factor the conditional good integral.

**PROVED (source ledger).** After factoring $e^{\langle g,h\rangle}$, assign $e^{\sum_{y\in D}g_y\cdot(q_y-h)}$ to bad-spin sites and $e^{\beta^{-1/2}\sum_{x\in G}g_x\cdot(v_x+n_\beta(v_x)h)}$ to good chart sites. These factors multiply to the source in (H37.6) exactly and are analytic on the full source ball.

**PROVED (energy and measure ledger).** $e^{-\beta H_B(q)}$ includes bad-site masses and bonds internal to $D$; (K0.5) includes every internal good bond and every crossing bond once. Each bad site uses normalized sphere measure, each good site uses the plus-chart Jacobian and good indicator, and $G_G/G_\Lambda$ contains the entire Gaussian normalization change. No bound such as $e^{-\beta|\phi_x-q_y|^2/2}\le1$ may replace a crossing factor in this identity.

**PROVED (determinant-loop assignment before exponentiation).** H37.7 writes $\log(G_G/G_\Lambda)$ as the local site term $-|D|\log c_\beta+(m/2)|D|\log(2d+\nu)$ plus one term $-\frac m{2n}(2d+\nu)^{-n}$ for every rooted length-$n$ closed walk meeting $D$. Assign each walk to its full visited path support; a walk meeting two cores is a link between those cores, not a factor of either individual heavy activity.

**PROVED (localization of the OR condition).** If $b_Q$ records whether $Q$ is bad and $\mathcal Q(w)$ are the blocks visited by a loop, then
$$\mathbf1_{\{w\cap D_B\ne\varnothing\}}=1-\prod_{Q\in\mathcal Q(w)}(1-b_Q)
=\sum_{\varnothing\ne I\subseteq\mathcal Q(w)}(-1)^{|I|+1}\prod_{Q\in I}b_Q.\tag{L38.5}$$
Each monomial in (L38.5) has finite path support and makes the loop's multi-core dependence explicit. The loop series is absolutely convergent for $\nu\ge\nu_*$, with tail $|D|q^R/(1-q)$ from H37.7.

**PROVED (hole inverse-square-root walk identity).** For $x,y\in G$, the Stieltjes walk series gives
$$K_G^{-1/2}(x,y)=K_\Lambda^{-1/2}(x,y)
-\sum_{\substack{w:x\to y\\w\ {\rm visits}\ D}}c_\nu(w),\qquad c_\nu(w)\ge0.\tag{L38.6}$$
**PROVED (scope of L38.6).** Each individual difference term has the support of its actual walk and is identical on a nonwinding lift. Its sum decays in walk length. The identity does not make a hard indicator or Jacobian analytic in the sum of those walks.

**OPEN (factorization step).** To obtain the requested product of activities, one must expand the good-region expectation into finite-support terms and show that the closure indicator, boundary force, all loops of (L38.5), all hole walks of (L38.6), and all chart factors can be grouped into connected families with a summable absolute norm. No cited result performs that operation on the integrated hard chart. Consequently there is no honest explicit finite-dimensional activity $K(Y;g)$ for the *unregularized* model to write down here.

## 3. Choice of interpolation and an exact regularized linked identity

**PROVED (choice).** Use finite Stieltjes walks, as in LF-BASE-KF0.md F.1 and LF-BASE-KF0-H.md H.1, for an exact finite-range algebraic expansion. For a fixed graph $G$, each truncated $C_{G,R}$ is positive, has spectrum in $[c_L,\nu_*^{-1/2}]$, and its coefficient paths stay inside $G$. The full-torus version $C_R$ is invertible for every $R$.

**PROVED (why direct BKAR is unavailable).** External/BKAR/Formula.lean:bkar_formula assumes BKARContDiff, namely global $C^\infty$ smoothness of the scalar interpolation function on the whole real edge-parameter space. A pointwise interpolation of $C_G^{1/2}\psi$ moves the hard indicator and the singular Jacobian; H.4 gives a square-root cusp after one marked-site integration, so this function has no proved BKARContDiff instance.

**OPEN (density-level BKAR alternative).** Interpolating a positive Gaussian covariance and differentiating its density could leave the indicator fixed inside a block. At the forest-min matrices positivity follows from the Schur product theorem and the mass gap, but a global smooth extension required by the landed BKAR theorem, uniform mixed-derivative bounds, and control of the $B$-dependent diagonal covariance have not been proved. The landed forest formula is an identity under smoothness, not a tree bound for these derivatives.

**PROVED (exact finite-walk change of variables).** On the full torus let $C_R$ be H.2's length-$R$ Stieltjes polynomial in adjacency, put $u_R=\beta^{-1/2}C_R\psi$, $Q_R=C_RK_\Lambda C_R-I$, and $N_R=c_\beta^{|\Lambda|}(\det C_R)^m$. Then for every finite $R$,
$$Z_\Lambda^{\rm prob}(g)=N_R\int d\gamma(\psi)\sum_{\sigma\in\{\pm1\}^\Lambda}
\prod_x\mathbf1_{\{|u_R(x)|<1\}}(1-|u_R(x)|^2)^{-1/2}
\exp\!\left[-\tfrac12\langle\psi,Q_R\psi\rangle-\beta V(u_R,\sigma)
+\sum_x g_x\cdot\Phi(u_R(x),\sigma_x)\right].\tag{L38.7}$$
**PROVED (proof of L38.7).** The map $u_R=\beta^{-1/2}C_R\psi$ is invertible. Its Jacobian gives $N_R$, while $\beta\langle u_R,K_\Lambda u_R\rangle/2=\langle\psi,C_RK_\Lambda C_R\psi\rangle/2$; the Gaussian reference supplies $-\langle\psi,\psi\rangle/2$, leaving exactly $-\langle\psi,Q_R\psi\rangle/2$. The two-sheet identity (F.3) supplies $V$ and every bond. Thus L38.7 is exact for each $R$, even though $C_R\ne K_\Lambda^{-1/2}$.

**PROVED (finite-range factor supports).** $C_R$ has walk range $R$, and $Q_R$ is a polynomial in adjacency of degree at most $2R+1$. Every site, bond, source and chart factor in L38.7 reads only a finite $R$-dependent neighborhood of its anchor; the optional identity $\prod_Q[\chi_Q+(1-\chi_Q)]=1$ has the same finite-range property and is used only when reindexing by physical bad blocks. The determinant $N_R$ is source independent and stays outside the activity. Declare a site's radius-$R$ ball, a bond's union of adjacent balls, and each quadratic correction walk's visited path as its connected support. Expanded individual walks lift exactly when their path supports do not wind.

**PROVED (bounded regulator).** For $T,J<\infty$, restrict each Gaussian variable to $|\psi_x|\le T$ using its conditioned product law and replace the chart factor $(1-|u|^2)^{-1/2}$ by its minimum with $J$. Keep the real chart indicator. Call the resulting integral $Z_{R,T,J}(g)$ and put its Gaussian-cutoff normalization into the source-independent $N_{R,T,J}$. Every elementary site, bond and quadratic-correction factor is then bounded, measurable, and has finite declared support.

**PROVED (explicit regularized connected integral).** Write the unpartitioned bounded regularized integrand, including sheet marks with a product mark law, as $\prod_{t\in\mathcal T_{R,T,J}}(1+U_t(\omega;g))$; site factors include the chart indicators, clipped Jacobians and source, bond factors include all normal and crossing energies, and quadratic factors are split into individual finite-walk terms of $Q_R$. For a nonempty connected union $Y$ of declared block supports set
$$K_{R,T,J}(Y;g):=
\sum_{\substack{\varnothing\ne F\subseteq\mathcal T_{R,T,J}\\
\text{contact-connected},\ \cup_{t\in F}S_t=Y}}
\int_{\Omega_Y}\prod_{t\in F}U_t(\omega;g)\,d\mu_Y(\omega).\tag{L38.8}$$
**PROVED (algebraic identity at fixed regulators).** Expanding the product over $F$, splitting each $F$ into contact components, and using product-measure factorization for disjoint supports proves
$$Z_{R,T,J}(g)=N_{R,T,J}\,\Xi_\Lambda(K_{R,T,J}(\cdot;g)).\tag{L38.9}$$
**PROVED (scope of L38.9).** Balaban.Polymer.decomposition is the landed combinatorial form of this step. L38.8 is an explicit finite-dimensional integral for the *regularized* activity; the choice of mark-law normalization is absorbed into its local site factors and $N_{R,T,J}$. This algebraic activity has not been shown to equal an activity built from the dressed components of §1.

**PROVED (regularized source and lift).** For fixed $R,T,J$, each $K_{R,T,J}(Y;g)$ is entire in the source coordinates anchored in $Y$ and is unchanged under a nonwinding lift of all its declared finite-walk supports. The source is bounded by $e^{\|g\|_1}$ on the real spin domain; finite sums and the bounded cutoff integral justify differentiation in $g$.

**PROVED (finite-volume regulator removal for the partition function).** At fixed $\Lambda,\beta,\nu,h,g$, $Z_{R,T,J}(g)\to Z_\Lambda^{\rm prob}(g)$ by first removing the chart and Gaussian cutoffs and then, if desired, letting $R\to\infty$; L38.7 itself already equals the exact partition for every $R$. For fixed $R$, undo the invertible $C_R$ change of variables: the clipped chart density and Gaussian cutoff are dominated in absolute value by the full physical spin integrand, whose source modulus is at most $e^{\|g\|_1}$. Dominated convergence proves the stated partition-function limit without a polymer bound.

**OPEN (limit of activities).** L38.9 cannot be passed termwise to a polymer gas for the full model without a weighted bound uniform in $R,T,J$ and the torus. The site factor still depends on every variable in its radius-$R$ ball and its sup norm grows with $J$; the exact equality at fixed regulators supplies no decay in the number of blocks of that ball.

## 4. Why the intended linked bound is not yet proved

**PROVED (ordinary restricted input).** On the all-plus product event $|\psi_x|\le p_\beta=b\log(\beta a)$, with $A>\sqrt2b/\sqrt{\nu_*}$, the physical good indicators are one. The F.8 path expansion gives the ordinary weighted bound
$$B_{\rm ord}(\beta)\le C\!\left[\frac{\log(\beta a)}{\sqrt\beta}
+\frac{\log^2(\beta a)}{\beta}+\frac{\log^4(\beta a)}{\beta}\right].\tag{L38.10}$$
**PROVED (hole restriction of ordinary walks).** Replacing the full Stieltjes paths in F.8 by paths staying in $G$ only reduces their nonnegative row majorant. Paths removed by a hole are exactly L38.6 and can be tagged as links to a bad core. This transfers the algebraic path support and the all-good Taylor majorant *away from integrated collar factors*; it does not bound the linked heavy activity.

**REFUTED (one block-crossing factor $e^{-\eta s}$).** A walk can move from one $s$-block to an adjacent block in one lattice step. The scalar walk tail $q^s$ applies to separation by $s$ sites, not to every new block of a connected support. F.10 uses a separate path-occupancy geometry bound; extending it to hole walks and heavy chart factors requires a new weighted summation estimate.

**REFUTED (H.3 shells as a uniform estimate for L38.8).** H.3 controls a bare marked kernel with a radius cost $q^{R/4}$, while a radius-$R$ support can have order $(R/s)^d$ blocks. It omits exterior Jacobians and crossing bonds, and its square-root cusp blocks the naive repeated-derivative tree estimate. It cannot bound all connected families in L38.8.

**OPEN (source-independent vacuum normalization).** A direct Mayer expansion of L38.7 around a uniform sheet-mark law has site factors of order one at $g=0$ even as $\beta\to\infty$. An activity bound with $\epsilon_\beta\to0$ requires a chosen plus-sheet/product-cutoff reference and a proof that every vacuum normalization and minus/bad complement is assigned to local linked objects. Moving an extensive constant into $N_{R,T,J}$ is legal, but a global normalization by $Z_\Lambda(0)$ alone does not prove locality.

**OPEN (tree bound).** Balaban.Polymer.card_animals_le counts connected block sets and mayer_activity_bound/pe_size propagate an already established local weight. External/BKAR/Formula.lean:bkar_formula supplies the forest identity under BKARContDiff. None supplies the mixed hard-chart influence estimate for the attached collar, so the forest sum cannot currently be bounded by a product of small edge factors.

**OPEN — LinkedHeavyInfluenceBound (precise missing lemma).** Construct a regulator-independent regrouping of L38.8 into source-local connected block functions $\widehat K_{R,T,J}(Y;g)$, with the full physical sector and closure ledger, preserving $\Xi(\widehat K_{R,T,J})=\Xi(K_{R,T,J})$, such that for prescribed $\kappa_0>0$
$$\sup_{\Lambda,\nu,h,Q,\|g\|_1<1}\sum_{Y\ni Q}
e^{\kappa_0|Y|}\bigl|\widehat K_{R,T,J}(Y;g)\bigr|
\le C_{d,N,L,M,\kappa_0}\left(B_{\rm ord}(\beta)+e^{-c\log^2(\beta a)}\right)\tag{L38.11}$$
uniformly in the regulators, with exact nonwinding equality and a termwise regulator limit. This is stronger than a pointwise bound and would imply DirectK0PolymerInput after choosing $\beta_0$; its proof must integrate every hard Jacobian inside connected marked objects and control repeated exterior influences along sparse paths.

**OPEN (candidate rate and constants).** If L38.11 holds, one may take $\epsilon_\beta=C[B_{\rm ord}(\beta)+e^{-c\log^2(\beta a)}]\to0$ and any fixed $\kappa_0$ below its weighted rate. The constant $c$ is the residual Peierls charge from L38.4 after all normalization losses. Neither this $\epsilon_\beta$ nor a numerical $\beta_0$ is currently proved for the full gas.

**PROVED (order of choices actually used).** Fix the requested target $\kappa_0$ and root parameters, then choose $L$ (or freeze $L=3$), choose $a,b,A$ with $A>\sqrt2b/\sqrt{\nu_*(L)}$, choose $M$ so $s=ML\ge8$ and $8\kappa_0 3^d/s<\eta$, and finally enlarge $\beta_0$ for chart, collar and numeric smallness. A choice of fixed $A$ before an arbitrary later $L$ cannot enforce $A>\sqrt2b/\sqrt{\nu_*(L)}$ uniformly as $L\to\infty$; the requested literal order needs $A$ specified as a function of $L$.

## 5. Conditional conclusion and bounded Lean packages

**PROVED CONDITIONAL ON LinkedHeavyInfluenceBound (exact linked limit).** Uniform weighted summability permits dominated termwise removal of $T,J$ and regrouping of the finite-walk indices, producing analytic, source-local activities $K_\Lambda(Y;g)$ with exact nonwinding lifts and $|K_\Lambda(Y;g)|\le\epsilon_\beta e^{-\kappa_0|Y|}$. The source-independent normalizers in L38.9 converge to a source-independent $N_\Lambda$, so the limit is exactly $Z_\Lambda^{\rm prob}(g)=N_\Lambda e^{\langle g,h\rangle}\Xi_\Lambda(K_\Lambda(\cdot;g))$ after extracting the source constant in each site factor.

**PROVED CONDITIONAL ON DirectK0PolymerInput (one-scale completion).** FrozenTorus.pe_blockTorus_frozen then gives analytic local $p_X$ with the required weighted bound; Holomorphic.pe_PY_analyticOnNhd and BoxTransport.frozenPY_boxMap transfer analyticity and already proved lift equality. KF0.md's Cauchy formula gives $T_1$ and the restricted $k_f=0$ Root-F clauses. This is conditional and says nothing about the low-mass branch.

**PROVED (Lean package L38-1, after H37-3; at most 300 new lines).** Define the per-core force and prove L38.1 and the uniform shell count $D_{d,L}<\infty$. The inputs are H37.3's killed-walk proof and finite torus distance counting; the mathematical estimate is complete above.

**PROVED (Lean package L38-2, after L38-1; at most 300 new lines).** Define L38.2, prove L38.3, and prove L38.4 by a separate elementary logarithmic-budget lemma. These are paper-level proved numeric statements; split the shell sum and calculus inequalities if needed.

**PROVED (Lean package L38-3, after L38-2; at most 300 new lines).** Define the finite graph on bad blocks, prove the component partition, pairwise non-touching supports, and $\sum_I|S_I|\le\sum_Q|C_Q|$. The graph partition is routine; do not recompute radii after merging.

**PROVED (Lean package L38-4, after H37-4; at most 300 new lines per module).** Prove L38.5 for loop occupancy, L38.6 from the Stieltjes paths, and the exact source/energy/measure ledger of (H37.6). Their individual identities are mathematical consequences above; the linked norm is not part of this package.

**PROVED (Lean package L38-5, after K1 and B2; separate modules of at most 300 new lines).** Prove positive invertibility of $C_R$, the finite-range statement for $Q_R$, and L38.7 by finite Gaussian change of variables. Then define the bounded regulators and prove L38.8–L38.9 using Balaban.Polymer.decomposition. This lands a real algebraic identity, with no claim of a uniform activity bound.

**OPEN (Lean package L38-6, after L38-1 through L38-5).** Prove LinkedHeavyInfluenceBound, including integrated chart moments for overlapping marked collars, sparse-path influence estimates for every exterior Jacobian and hole walk, connected-family entropy, and exact torus lift. These must be separate statements of at most 300 new lines each. The first missing mathematical estimate is the integrated repeated-influence bound, not an invocation of an existing forest or Mayer theorem.

**PROVED CONDITIONAL ON LinkedHeavyInfluenceBound (Lean package L38-7; at most 300 new lines per module).** Pass the regulator limit through the weighted connected sum, establish DirectK0PolymerInput, and invoke the already specified PE/holomorphic/box transport bridge to KF0RootFPartial. This is the next assembly only after L38-6 is proved.
