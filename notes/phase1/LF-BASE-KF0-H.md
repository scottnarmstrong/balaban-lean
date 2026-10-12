# The $k_f=0$ marked kernel: a finite-walk localization and its limit

This note answers `followup_h.txt` using the notation and proved estimates of [LF-BASE-KF0.md](LF-BASE-KF0.md), Parts F–G. All changes are confined to the present scratch directory. The exact result is Theorem H.3: the **bare integrated marked kernel** has a decomposition into bounded finite-support functions whose product-Gaussian $L^1$ norms decay exponentially in the walk radius. The coefficients can be chosen to agree exactly on non-winding torus lifts. The theorem does not localize the exterior chart Jacobians or give decay in the *number* of blocks in a coefficient's support. Neither `gasOp_pe` nor `gasOp_pe_hole` accepts the estimate obtained here. Thus the requested (B.5) and the all-clause $k_f=0$ Root-F proof remain open. The last section records the precise additional theorem that would finish them.

## H.1. Walk truncations with a uniform inverse

Fix $d\ge3$, $N\ge2$, $L\ge3$, $m=N-1$, and $\nu_*:=7/(8L^2)<\nu\le1$. On a periodic site torus $\Lambda$ write $K=-\Delta_\Lambda+\nu I=(2d+\nu)I-A$, where $A$ is the nearest-neighbour adjacency matrix, and $C=K^{-1/2}$. Put
$$q_L=\frac{2d}{2d+\nu_*}<1,\qquad a_L=\nu_*^{-1/2},\qquad c_L=\frac{1-q_L}{\sqrt{2d+1}},\qquad \Lambda_L=\frac{a_L}{c_L}.\tag{H.1}$$
For $R\ge0$ define the finite-walk matrix
$$C_R=\frac1\pi\int_0^\infty t^{-1/2}
 \sum_{n=0}^R\frac{A^n}{(2d+\nu+t)^{n+1}}\,dt.\tag{H.2}$$
The Stieltjes formula and the walk expansion in Part E.3 give $C_R\to C$ in operator norm. Every entry of $C_R$ is nonnegative, and its $(x,y)$ entry is a sum of walks of length at most $R$ from $x$ to $y$. Unlike a hard spatial truncation of $C$, this matrix has a uniform positive lower spectral bound.

**Lemma H.1.** For every $R$, torus, and $\nu\in(\nu_*,1]$,
$$c_L I\le C_R\le a_L I,\qquad
 \sup_x\sum_y(C_R-C_{R-1})(x,y)\le a_Lq_L^R\quad(R\ge1),\tag{H.3}$$
where $C_{-1}=0$. Every principal matrix $(C_R)_{DD}$ has spectrum in $[c_L,a_L]$. A coefficient of $C_R$ whose walks remain inside a lifted non-winding box is identical on any two tori with the same local graph there.

*Proof.* At fixed $t$, put $D_t=2d+\nu+t$ and $T_t=A/D_t$. The spectrum of $T_t$ is contained in $[-q_L,q_L]$. For $z\in[-q_L,q_L]$ the partial sum $\sum_{n=0}^Rz^n$ is at least $1-q_L$: for $z\ge0$ it is at least one; for $z<0$, pair the terms $(1+z)$, $(z^2+z^3)$, and so on, leaving a nonnegative final even power if necessary. Integrating the resulting operator inequality in (H.2) gives
$$C_R\ge(1-q_L)\frac1\pi\int_0^\infty\frac{t^{-1/2}}{2d+\nu+t}\,dt\ I
=(1-q_L)(2d+\nu)^{-1/2}I\ge c_LI.$$
The entries of the walk integrals are nonnegative, so the row sum of $C_R$ is at most that of $C$. By (F.5) the latter is $\nu^{-1/2}\le a_L$. Symmetry and the row-sum bound imply $C_R\le a_LI$. The $n=R$ walk row sum is at most $a_Lq_L^R$ by (E.2)/(F.9) with no length weight. Principal matrix bounds follow by extending a vector by zero. A walk of length at most $R$ uses only edges within distance $R$ of its start, and its coefficient in (H.2) depends only on $d,\nu,t$ and those edges; lifting it proves the last assertion. $\square$

The lower bound is needed: the conditional integration in Part G uses the inverse determinant of the internal linear map. Entrywise truncation of $C$ does not automatically preserve invertibility.

## H.2. Affine continuity of the integrated chart density

Let $I_{m,q}$ be (G.2), let $I_m=I_{m,1}$, and put $S_m=2\pi^{m/2}/\Gamma(m/2)$. For $\sigma\in\{+1,-1\}$, $\|g_x\|_1\le1$, and real $|u|<1$, set
$$f_{\sigma,g_x}(u)=\mathbf1_{\{|u|<1\}}(1-|u|^2)^{-1/2}
 \exp\left[-\frac{\beta\nu}{2}(\sigma\sqrt{1-|u|^2}-1)^2
             +g_x\cdot\Phi(u,\sigma)\right].\tag{H.4}$$
It is extended by zero off the unit ball. The source may be complex; $|f_{\sigma,g_x}(u)|\le e^{\|g_x\|_1}j(u)$, where $j(u)=\mathbf1_{\{|u|<1\}}(1-|u|^2)^{-1/2}$.

**Lemma H.2 (affine $L^1$ modulus).** Suppose $F_D(u_D)=\prod_{x\in D}f_{\sigma_x,g_x}(u_x)$, $\beta\ge1$, and $\sum_{x\in D}\|g_x\|_1<1$. Let $M$ be a real invertible site matrix, acting identically in each tangent coordinate, with $|\det M|^{-1}\le\Lambda_L^{|D|}$, and let $c$ be a tangent vector. Write
$$\epsilon=\|M-I\|_{\infty\to\infty}+\max_{x\in D}|c_x|.$$
One explicit coarse choice is
$$A_{m,L}=10^8(1+m)^2(1+I_m+S_m)^2(1+\Lambda_L)^{2m}.\tag{H.5}$$
Then
$$\int_{(\mathbb R^m)^D}|F_D(Mu+c)-F_D(u)|\,du
 \le [A_{m,L}(1+\beta)]^{|D|}\min\{1,\epsilon^{1/2}\}.\tag{H.6}$$

*Proof.* First consider one site. For $0<s=|a|\le1/100$, split the ball into the boundary layer $1-|u|\le4s$ and its complement. Radial integration gives
$$\int_{1-|u|\le4s}j(u)\,du\le4S_m\sqrt{s},\qquad
 \int_{|u|\le1-4s}|\nabla j(u)|\,du\le S_m s^{-1/2}.$$
The same estimates apply to the translated ball after changing variables. The mean-value theorem on the common interior yields
$$\|j(\cdot+a)-j\|_1\le16(S_m+I_m)s^{1/2};\tag{H.7}$$
for $s>1/100$ the bound follows from $2I_m\le20I_m\sqrt{s}$. On the common interior, $|t(u+a)-t(u)|\le\sqrt{3s}$ and $|\Phi(u+a,\sigma)-\Phi(u,\sigma)|\le(1+\sqrt3)\sqrt{s}$. The real mass exponent changes by at most $2\sqrt3\beta\sqrt{s}$, while the source exponent changes by at most $(1+\sqrt3)\|g_x\|_1\sqrt{s}$. Integrating the exponential along the straight segment between the exponents, whose real mass part is nonpositive, and using (H.7), gives a one-site $L^1$ modulus bounded by $100e^{\|g_x\|_1}(1+I_m+S_m)(1+\beta)\sqrt{s}$. Its $L^1$ norm is at most $e^{\|g_x\|_1}I_m$.

For an affine map close to the identity, take $\epsilon<1/100$. If either $F_D(u)$ or $F_D(Mu+c)$ is nonzero, every relevant coordinate of $u$ has norm at most $1+3\epsilon$, and $|Mu+c-u|_\infty\le3\epsilon$. On the union of the $4\epsilon$ boundary layers, the first radial estimate and a change of variables under $M$ bound both integrals by $[C_m(1+\beta)]^{|D|}|D|\sqrt\epsilon$. On the complementary region, the path $u+t(Mu+c-u)$ stays at least $\epsilon$ from every unit-sphere boundary. Apply the fundamental theorem of calculus along that path. The integral of $|\nabla j|$ is bounded by the second radial estimate; the derivative of the mass/source factor contributes at most $C_m(1+\beta)\epsilon^{-1/2}$ after integration against $j$. The path Jacobian is bounded by $(1-\epsilon)^{-m|D|}\le e^{2m|D|\epsilon}$. Multiplication by the path displacement $3\epsilon$, summation over $D$, and $|D|\le2^{|D|}$ give (H.6) with the much larger constant (H.5). If $\epsilon\ge1/100$, use $\|F_D\|_1\le eI_m^{|D|}$ and $\|F_D\circ(M\cdot+c)\|_1\le\Lambda_L^{m|D|}eI_m^{|D|}$; the factor $\sqrt\epsilon\ge1/10$ and (H.5) cover this case. $\square$

The exact decimal factor in (H.5) is deliberately loose; it is displayed so that the radius and temperature estimates below have stated dependencies. The exponent $1/2$ reflects the integrable square-root singularity at the chart equator. A pointwise Lipschitz bound on (H.4) is false.

## H.3. A torus-exact finite-support shell decomposition

Take a nonempty marked set $D=B\cup M\subset\Lambda$, with Gaussian-bad set $B$ and minus-sheet set $M$ as in (G.4), and keep the exact event $E_B$ there. For $R\ge0$ define
$$u_x^{[R]}=\beta^{-1/2}\sum_{y\in\Lambda}C_R(x,y)\psi_y,
\quad
\mathcal H^{[R]}_{D;B,M}(\psi_{D^c};g_D)
 =\int_{E_B}\prod_{x\in D}f_{\sigma_x,g_x}(u_x^{[R]})\,d\gamma_D(\psi_D).\tag{H.8}$$
Thus $\mathcal H^{[R]}$ is a conditional integral with an **approximate** tangent map. It is an auxiliary function, not an exact partition-function sector. Define $K_0=\mathcal H^{[0]}$ and $K_R=\mathcal H^{[R]}-\mathcal H^{[R-1]}$ for $R\ge1$. Set
$$\begin{aligned}
C_*&=\max\{1,(2\pi)^{-m/2}c_L^{-m}I_{m,3/2}\},\\
H_\beta^*&=\min\{p_\beta^2/12,\beta\nu_*/2\}
 -\frac m3\log\beta-\frac23\log C_*-\frac m6\log2-1,\\
D_L^*&=\Lambda_L+\sqrt m\,a_L(1+\Lambda_L),\\
B_\beta^*&=2(2\pi)^{-m/2}c_L^{-m}A_{m,L}
 \max\{1,D_L^*\}^{1/2}\beta^{m/2}(1+\beta),\\
h_\beta^*&=\tfrac12\bigl(H_\beta^*-\log(2B_\beta^*)\bigr).
\end{aligned}\tag{H.9}$$
For $p_\beta=b\log(\beta a)$ with fixed $a>1,b>0$, one has $h_\beta^*\to\infty$.

**Theorem H.3 (the available quasi-locality).** For all sufficiently large $\beta$, uniformly in $D,B,M$, $\nu$, $h$, and the torus:

1. Each $K_R$ is a bounded measurable function of the exterior Gaussian variables at graph distance at most $R$ from $D$. Its source dependence is entire in $g_D$.
2. The exact bare kernel of (G.4) satisfies $\mathcal H_{D;B,M}=\sum_{R\ge0}K_R$ pointwise in the exterior variables, and the series converges absolutely in $L^1(\gamma_{D^c})$.
3. For $R\ge1$,
   $$\int|K_R|\,d\gamma_{D^c}\le e^{-h_\beta^*|D|}q_L^{R/4},\qquad
   |K_0|\le e^{-H_\beta^*|D|}.\tag{H.10}$$
4. If the graph-radius-$R$ neighbourhood of $D$ lifts without winding into the same box on two admissible tori, the function $K_R$ is identical under that lift, with the same $\nu,\beta,h,g_D$ and local Gaussian coordinates.

*Proof.* Lemma H.1 gives $\det[(C_R)_{DD}]^{-1}\le c_L^{-|D|}$. Repeating the affine change of variables and Hölder calculation in G.1–G.2 with $C_R$ in place of $C$ gives
$$\sup_{\psi_{D^c}}|\mathcal H^{[R]}_{D;B,M}|\le e^{-H_\beta^*|D|}\qquad(R\ge0).\tag{H.11}$$
This is where the uniform lower spectral bound in H.1 is used. The formula in (H.8) is measurable by parameterized Fubini, and dominated differentiation on bounded source sets makes it entire.

For $R\ge1$ and fixed exterior variables, set $A_0=\beta^{-1/2}(C_{R-1})_{DD}$, $A_1=\beta^{-1/2}(C_R)_{DD}$, $b_i=\beta^{-1/2}(C_{R-1+i})_{D,D^c}\psi_{D^c}$, $M_0=A_1A_0^{-1}$, and $c_0=b_1-M_0b_0$. Change variables $u=A_0\psi_D+b_0$ in the absolute difference of the two integrands of (H.8); discard $\mathbf1_{E_B}\le1$ and bound the Gaussian density by $(2\pi)^{-m|D|/2}$. Lemma H.2 yields
$$|K_R|\le\left[(2\pi)^{-m/2}c_L^{-m}A_{m,L}(1+\beta)\beta^{m/2}\right]^{|D|}
 \min\{1,(\|M_0-I\|_{\infty\to\infty}+\|c_0\|_\infty)^{1/2}\}.\tag{H.12}$$
The determinant condition of H.2 holds because both principal matrices have spectra in $[c_L,a_L]$.

The row sum of $C_R-C_{R-1}$ is at most $a_Lq_L^R$ by (H.3). Also $\|(C_{R-1})_{DD}^{-1}\|_{\infty\to\infty}\le\sqrt{|D|}/c_L$, and the row sum of $(C_{R-1})_{D,D^c}$ is at most $a_L$. Consequently
$$\|M_0-I\|_{\infty\to\infty}\le\Lambda_L\sqrt{|D|}\,q_L^R,
\quad
\mathbb E_{\gamma_{D^c}}\|c_0\|_\infty
 \le\beta^{-1/2}\sqrt m\,a_L|D|(1+\Lambda_L\sqrt{|D|})q_L^R.\tag{H.13}$$
Here $\mathbb E|\psi_y|\le\sqrt m$, the triangle inequality and nonnegative walk coefficients suffice; independence beyond the product reference is not used. Jensen's inequality, $\beta\ge1$, and $|D|^{3/4}\le2^{|D|}$ turn (H.12)–(H.13) into
$$\int|K_R|\,d\gamma_{D^c}\le(B_\beta^*)^{|D|}q_L^{R/2}.\tag{H.14}$$
On the other hand (H.11) gives $\int|K_R|\le2e^{-H_\beta^*|D|}$. The geometric mean of these two bounds is (H.10). Since $H_\beta^*$ grows as a positive multiple of $\log^2\beta$ and $\log B_\beta^*=O(\log\beta)$, $h_\beta^*\to\infty$.

Every length-at-most-$R$ walk starting in $D$ stays in the radius-$R$ neighbourhood, so (H.8) reads only the Gaussian coordinates there after integrating $\psi_D$. This proves exact `DepOn` for $K_R$ with that declared support. The same walk statement proves clause 4, including the internal principal matrix $(C_R)_{DD}$. Finally $C_R\to C$ entrywise. For each fixed exterior configuration, $u_D^{[R]}\to u_D$ for almost every internal Gaussian configuration; the exceptional chart-boundary set has measure zero because $(C_R)_{DD}$ and $C_{DD}$ are invertible. The uniform $L^{3/2}$ moment from the first paragraph gives uniform integrability, so $\mathcal H^{[R]}\to\mathcal H$ by Vitali's theorem. Telescoping proves clause 2 pointwise, while (H.10) gives absolute $L^1$ convergence. $\square$

For a connected $D$ and $s=ML$, the declared block support $X_R$ is the set of $s$-blocks meeting its radius-$R$ neighbourhood. It is connected, and (H.10) can be written $e^{-h_\beta^*|D|}e^{-\eta_LR/4}$ with $\eta_L=-\log q_L$. This is the proved locality property: exponential in a charged core and in *radius*, in integrated norm. Since $R$ site steps represent approximately $R/s$ block steps, choosing $M$ after $L$ with $\eta_Ls/4>\kappa$ gives any prescribed decay in block radius; it still gives no decay proportional to the number of blocks in $X_R$. There is no uniform sup-norm decay in $R$ on the full Gaussian space. For a singleton $D=B=\{x\}$, $M=\varnothing$, $g=0$, and a site $y$ with $\operatorname{dist}(x,y)=R$, the finite-walk coefficient $C_{R-1}(x,y)$ vanishes while $C_R(x,y)>0$. Hold all other exterior variables at zero and let $|\psi_y|\to\infty$. Then $\mathcal H^{[R-1]}$ stays at its positive value at zero shift, while $\mathcal H^{[R]}\to0$ by the change-of-variables argument for (G.11). For $\beta$ so large that $2p_\beta a_L/\sqrt\beta<1/2$, the zero-shift value is at least $e^{-\beta/2}\gamma_m\{p_\beta<|\psi|<2p_\beta\}>0$, uniformly in $R$ and the torus. Thus $\|K_R\|_\infty$ has a positive lower bound independent of $R$ whenever the torus contains a site at that distance. The integrated norm in (H.10) is the meaningful decaying norm.

## H.4. Why the landed polymer theorems do not finish the argument

The exact statements of `Balaban.Polymer.gasOp_pe` in `Polymer/GasOperator.lean:336` and `Balaban.Polymer.gasOp_pe_hole` in `Polymer/HoleOperator.lean:434` both demand `DepOn` for each heavy function **and**
$$\int|\tau_z|\,d\mu\le\exp[-p-h|z_s|],\tag{H.15}$$
where $|z_s|$ is the number of blocks in its full support. The latter theorem additionally imposes hole closure and a Steiner-size estimate. `Polymer/Hole.lean:389` (`pe_hole`) starts from already bounded hole-polymer activities; it does not derive (H.15) from a radius estimate. The new $K_R$ satisfy exact support, but their established bound (H.10) charges $|D|$ and $R$, not $|X_R|$. For a singleton core in $d\ge3$, $|X_R|$ grows at least as a constant times $(R/s)^d$ until the torus diameter. No positive $h$ independent of $R$ and the torus follows from $e^{-h_\beta^*}e^{-\eta_LR/4}\le e^{-p-h|X_R|}$: the proposed conclusion has an exponent of order $R^d$, while the premise has an exponent of order $R$. Enlarging $\beta_0$ cannot repair this for all volumes, since $h_\beta^*$ is fixed once $\beta$ is fixed and $R$ can grow with the torus.

**Sparse-support transfer lemma.** There is a direct replacement for the numerical hypothesis (H.15) when the localized functions have sparse supports. Suppose a finite-index operator gas over a product probability measure satisfies every hypothesis of gasOp_pe except hτ. For each heavy index $z$, suppose it has a nonempty core $C_z$, an integer path length $r_z\ge0$, constants $A,B,h_c,\eta>0$ independent of the torus, and
$$|z_s|\le A|C_z|+Br_z,\qquad
\int|\tau_z|\,d\mu\le e^{-p-h_c|C_z|-\eta r_z}.\tag{H.16}$$
Set $h'=\min\{h_c/A,\eta/B\}$. If the explicit hh inequality of gasOp_pe holds with $h'$, all conclusions of that theorem hold with $h'$. *Proof.* The two inequalities in (H.16) imply $h_c|C_z|+\eta r_z\ge h'|z_s|$, hence exactly hτ with $h=h'$. Every other binder was assumed, so apply gasOp_pe. The same reduction applies to gasOp_pe_hole when its additional hole-closure and Steiner hypotheses are supplied. $\square$ The linear support growth is the missing content: a walk halo has such a bound by (E.9), but no decomposition of the **complete** marked integrand into walk-halo functions with the second bound of (H.16) has been proved. The radius shells (H.8) have ball supports of order $r_z^d$, so they fail the first bound for fixed $A,B$.

A second exactness gap remains even if a stronger sparse-support expansion of (G.4) were proved. Formula (F.4) contains $\prod_{x\notin D}j(u_x)$, and those factors depend on the integrated $\psi_D$. The real crossing-bond exponential is at most one for the inequality (G.8), but an upper bound cannot replace it in an **identity** for the partition function. Thus $\mathcal H_{D;B,M}$ is not an activity whose product with the ordinary factors reproduces the complementary sector. In particular, (H.8) does not yield the common-reference equality required by `GasOperator.gasOp_eq` in `Polymer/GasOperator.lean:116`. The radius shells alone cannot be inserted into `gasOp_pe`, and `MayerPE.mayer_pe` still needs bounded ordinary terms on the same reference space.

For a fixed finite torus, radii after the ball fills the torus can be grouped into one full-support tail, making a finite index type as Lean requires. Its available norm is $e^{-c\ell}$, while its support has order $\ell^d$ blocks, so this grouping does not restore (H.15) uniformly in volume. A valid replacement for `gasOp_pe` would have to accept a **tree-weighted influence norm** that charges every distant block along a sparse connecting graph, prove the corresponding connected-cumulant and Peierls bounds, and preserve source and torus locality. Neither the landed `GasOperator`, `HoleOperator`, `MayerPE`, nor `KP` declarations is such a theorem. The scalar radius estimate (H.10) is insufficient to prove that replacement theorem: repeated exterior differences of the integrated kernel have not been bounded by products of edge influences. The loss of differentiability is concrete. Take $m=1$, $D=B=\{x\}$, $M=\varnothing$, $g=0$, and write $\alpha=\beta^{-1/2}C(x,x)$, with $\alpha p_\beta<1/4$. In the positive-$\psi_x$ part of (G.11), set $b_c=1-\alpha p_\beta$. For $b<b_c$ near $b_c$, its integration interval is $p_\beta<\psi_x<(1-b)/\alpha$; for $b\ge b_c$ it is empty. Changing to $v=(1-b)/\alpha-\psi_x$ and using $1-(1-\alpha v)^2\sim2\alpha v$ and writing $\varphi(p)=(2\pi)^{-1/2}e^{-p^2/2}$ gives the one-sided asymptotic
$$\mathcal H_+(b)=\frac{\sqrt2\,\varphi(p_\beta)e^{-\beta\nu/2}}{\alpha}\sqrt{(b_c-b)_+}+o(\sqrt{|b-b_c|}).\tag{H.17}$$
The negative-$\psi_x$ contribution is smooth near $b_c$: its cutoff endpoint maps to $u=b-\alpha p_\beta<1$, away from the upper chart boundary, while the lower chart endpoint can be held fixed after changing to $u$. Thus the complete one-site kernel has a square-root cusp at $b_c$. Repeated exterior differences cannot be bounded by a product of one-variable derivatives using H.2.

The precise remaining model input is therefore an exact decomposition of the **complete** two-sheet integrand (F.4) into bounded local ordinary and heavy functions over one fixed product probability reference, with crossing bonds and every Jacobian allocated, or a new tree-influence polymer theorem applied directly to that complete integrand. It must give a summable bound exponential in the number of blocks of each completed support, prove the explicit geometry/entropy hypotheses of `gasOp_pe` or its replacement, and group non-winding walks into torus-identical activities. Only then may one invoke `gasOp_pe` or a proved replacement, `FrozenTorus.pe_blockTorus_frozen` (`Polymer/FrozenTorus.lean:56`), and `Holomorphic.pe_PY_analyticOnNhd` (`Polymer/Holomorphic.lean:79`). Part B.4–B.6 of LF-BASE-KF0.md then gives the analytic local $T_1$, the $c_9L^{-((d-2)/2+\delta)}e^{-\kappa|X|}$ estimate with $\delta=1/8$, the principal-log identity, and exact quarter-box torus agreement. This is a conditional assembly, not a completed proof of (B.5) or Root-F.

## H.5. Lean dependencies and status

| Order | Proposed declaration | Estimated new lines | Landed reuse and status |
|---|---|---:|---|
| H1 | `finiteWalk_sqrtInverse`, `finiteWalk_spectrum`, `finiteWalk_rowTail`, `finiteWalk_lift` | 800–1,600 | H.1; spectral calculus, `Green/OneScaleDecay` only for its compatible estimates, `Polymer/BoxTransport` for lift bookkeeping |
| H2 | `chartDensity_affineL1`, `markedKernel_truncated_bdd` | 1,200–2,200 | H.2 and (H.11); G.1–G.2 and chart normalization |
| H3 | `markedKernel_walkShell_depOn`, `markedKernel_walkShell_L1`, `markedKernel_walkShell_lift`, `markedKernel_walkShell_sum` | 1,600–3,000 | H.3; H1–H2, product Gaussian Fubini, walk support |
| H4 | `sparseSupport_integrated_to_gasOp` | 150–300 | Sparse-support transfer lemma; direct instantiation of `GasOperator.gasOp_pe` |
| H5 | `kf0_completeHeavy_localize`, `kf0_gasIdentity`, block-size heavy norm and GAS/Hole hypotheses | At least 6,000–12,000 | **Open**; required before `GasOperator.gasOp_pe` or `HoleOperator.gasOp_pe_hole` |
| H6 | `kf0_gasPe`, `kf0_to_rootF` | 2,000–4,000 | **Conditional** on H5; `MayerPE`, `FrozenTorus`, `Holomorphic`, Part B.6 |

Confidence is high in the finite-walk spectral estimate and the conditional chart moment. The affine modulus and shell constants are given with deliberately coarse margins and should be checked independently before Lean implementation. The radius decomposition is a theorem about the bare marked kernel only. The requested completed $k_f=0$ Root-F proof remains open at H5; claiming that `pe_hole` accepts (H.10) would misstate its hypotheses.
