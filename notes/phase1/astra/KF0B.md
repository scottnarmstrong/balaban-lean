# The one-scale high-field branch: a checked obstruction and the remaining gap

## Result and scope

Fix $d\ge3$, $N\ge2$, $L\ge3$, $s=ML$, and $\nu_* =7/(8L^2)$. The requested conclusion is the $k_f=0$, $j=1$ specialization of `Balaban/Frozen/Roots/LogPartitionMultiscale.lean:logPartition_multiscale`: for all $\nu\in(\nu_*,1]$, large enough $\beta$ independent of the torus, and $\|g\|_1<1$, its principal logarithm must have local analytic coefficients $T_1(x,X;g)$ supported on connected $s$-block polymers, bounded by $c_9L^{-((d-2)/2+\delta)}e^{-\kappa |X|/s^d}$ on $\|g\|_1\le1/2$, with exact quarter-box agreement on two tori. The quantifier order is $\exists\delta>0\;\forall\kappa,c_9>0\;\exists L,M,\beta_0\;\forall\beta\ge\beta_0\;\forall\nu\in(\nu_*,1]$.

**The requested conclusion is not proved in this note.** I found neither a complete finite-support decomposition of the opposite-hemisphere sector, nor an alternative convergent one-scale expansion, nor a counterexample to the frozen clause. The theorem proved below rules out one tempting alternative reference measure. It is an obstruction to that *method*, not to Root-F. This distinction matters: a positive external field and a massive spin-wave covariance are consistent with the frozen conclusion.

The source and landed inputs inspected were [LF-BASE-KF0.md](LF-BASE-KF0.md), Parts B and F–G; [LF-BASE-KF0-H.md](LF-BASE-KF0-H.md), Theorem H.3 and §H.4; `docs/BLOCKERS.md` §1; `notes/phase1/KF0.md`, `KF0-P7.md`, `KF0-HEAVY.md`, `KF0-INFL.md`, `KF0-LAST.md`, `KF0-LINK.md`, and `KF0-ONECORE.md`; and the declarations `gas_activity_bound` in `Balaban/Polymer/GasBound.lean:445`, `gas_activity_bound_core` in `Balaban/Polymer/GasCore.lean:57`, `gasOp_pe` in `Balaban/Polymer/GasOperator.lean:336`, and `gasOp_pe_hole` in `Balaban/Polymer/HoleOperator.lean:434`. These paths are relative to `/home/scott/Balaban/`; that repository was read only.

## The independent-spin reference is not a small-bond expansion

One might avoid the Gaussian integral by taking the external-field part of the action as a product reference and expanding the bond factors. The following exact low-temperature limit shows why the temperature does not make those factors small.

**Theorem B.1.** Let $m=N-1$, $|h|=1$, and let $\mu_{\beta,\nu}$ be the probability measure on $\mathbb S^{N-1}$ with density proportional to $\exp[-\beta\nu(1-h\cdot\phi)]$ relative to normalized surface measure. For independent $\phi,\phi'$ with this law, put

$$F_\beta(\phi,\phi')=\exp[-\tfrac\beta2|\phi-\phi'|^2]-1.$$

For every fixed $0<\nu_*\le1$, convergence is uniform for $\nu\in[\nu_*,1]$:

$$\lim_{\beta\to\infty}\int|F_\beta|\,d\mu_{\beta,\nu}^{\otimes2}=1-(1+2/\nu)^{-m/2}\ge1-3^{-1/2}>0.\tag{B.1}$$

Moreover $\|F_\beta\|_\infty=1-e^{-2\beta}$. Thus the nearest-neighbor Mayer activity about this product reference has neither pointwise nor integrated smallness as $\beta\to\infty$, even at $\nu=1$.

*Proof.* Identify $h^\perp$ with $\mathbb R^m$. Except for the equator, write a spin as $\phi=u+\sigma\sqrt{1-|u|^2}\,h$, where $|u|<1$ and $\sigma\in\{+1,-1\}$. The normalized sphere measure on either sheet is $a_N^{-1}(1-|u|^2)^{-1/2}du$, where $a_N$ is the area of $\mathbb S^{N-1}$; this is (F.1) of LF-BASE-KF0.md. Set $v=\sqrt\beta,u$. On the plus sheet the unnormalized density in $v$ is

$$a_N^{-1}\beta^{-m/2}\mathbf1_{|v|<\sqrt\beta}(1-|v|^2/\beta)^{-1/2}\exp\{-\beta\nu[1-\sqrt{1-|v|^2/\beta}]\}.\tag{B.2}$$

For $\beta\ge4$, integration over $|v|\le1$ gives the explicit lower bound $Z_1(\beta,\nu)\ge a_N^{-1}\beta^{-m/2}e^{-1}\operatorname{vol}(B_m(1))$ for the one-site normalizer: the Jacobian is at least one and $\beta\nu(1-\sqrt{1-|v|^2/\beta})\le\nu|v|^2\le1$. On $|v|\le\sqrt\beta/2$, the Jacobian is at most $2/\sqrt3$, while $\beta\nu(1-\sqrt{1-|v|^2/\beta})\ge\nu_*|v|^2/2$. The probability of the remaining part of the plus sheet is at most

$$\frac{a_Ne}{\operatorname{vol}(B_m(1))}\,\beta^{m/2}e^{-\beta\nu_*/8},\tag{B.3}$$

because $|u|\ge1/2$ implies $1-\sqrt{1-|u|^2}>1/8$. The entire minus sheet obeys the still smaller bound obtained by replacing $e^{-\beta\nu_*/8}$ by $e^{-\beta\nu_*}$. On each fixed $v$-ball, the factor in (B.2) after removal of $a_N^{-1}\beta^{-m/2}$ converges uniformly in $\nu\in[\nu_*,1]$ to $e^{-\nu|v|^2/2}$. The preceding Gaussian majorant and (B.3) allow dominated convergence, uniformly in $\nu$. Consequently $\sqrt\beta$ times the tangential projection of a $\mu_{\beta,\nu}$ spin converges in law, uniformly in $\nu$, to $V\sim N(0,\nu^{-1}I_m)$, and the minus-sheet probability tends to zero.

For two independent spins, the tangential part of $\beta|\phi-\phi'|^2$ is exactly $|v-v'|^2$. On bounded $v,v'$ sets the normal part tends uniformly to zero, since $\sqrt{1-|v|^2/\beta}-\sqrt{1-|v'|^2/\beta}=O(\beta^{-1})$. Tightness established above and $0\le e^{-\beta|\phi-\phi'|^2/2}\le1$ therefore give

$$\lim_{\beta\to\infty}\mathbb E_{\mu_{\beta,\nu}^{\otimes2}}e^{-\beta|\phi-\phi'|^2/2}=\mathbb E e^{-|V-V'|^2/2}=(1+2/\nu)^{-m/2}.$$

The last equality is the elementary Gaussian integral for $V-V'\sim N(0,2\nu^{-1}I_m)$. Since $F_\beta\le0$, (B.1) follows. Finally $0\le|\phi-\phi'|^2\le4$, with equality attainable for antipodal spins, so the asserted supremum is $1-e^{-2\beta}$. $\square$

There is also a literal failure of the landed ordinary Mayer hypothesis. If one takes the nearest-neighbor potential to be $H_{xy}(\phi)=-\beta|\phi_x-\phi_y|^2/2$, then $\sup|H_{xy}|=2\beta$. The `hH` premise of `Balaban/Polymer/MayerPE.lean:mayer_pe` (line 37) asks $|H_{xy}|\le H_0e^{-(\kappa_0+\kappa_1)d(c_{xy})}$, while its `hH0'` asks $H_0\le\log2$ and its rates and size are nonnegative. Thus these premises would imply $2\beta\le H_0\le\log2$, impossible for $\beta>\frac12\log2$. This theorem does not exclude a direct spin expansion that first resums the strong quadratic bonds. It shows that merely changing the reference to independent spins in the external field does not furnish the small ordinary interaction required by the landed Mayer theorem. The nonzero limit in (B.1) is a spin-wave effect, present entirely in the near-$h$ sector.

## What the existing finite-walk decomposition supplies

The exact common-Gaussian identity is (F.4) of LF-BASE-KF0.md. The all-plus product-cutoff sector has the finite-walk localization (F.8) and the ordinary amplitude (F.13). For the bare integrated marked kernel (G.4), Theorem H.3 of LF-BASE-KF0-H.md gives an exact sum of bounded finite-support shells $K_R$ and

$$\int|K_R|\,d\gamma_{D^c}\le e^{-h_\beta^*|D|}q_L^{R/4}\quad(R\ge1),\qquad q_L=\frac{2d}{2d+\nu_*}<1.\tag{B.4}$$

The support of $K_R$ is a radius-$R$ halo. For a singleton core on a large torus it meets order $(R/s)^d$ blocks. At fixed $\beta$, (B.4) cannot *imply* an estimate $e^{-p-h|\operatorname{supp}K_R|}$ with $h>0$ independent of $R$: its stated exponent is linear in $R$, while the requested exponent is of order $R^d$. This does not rule out a different, sparse decomposition. It records the exact limitation of H.3.

There is a separate identity gap. The marked kernel (G.4) has integrated the marked-site Jacobians and on-site field factors. The complete integrand (F.4) still contains the Jacobians and chart tests at unmarked sites, and the bond factors joining marked and unmarked sites. Those unmarked factors depend on the marked Gaussian coordinates through $u_x=\beta^{-1/2}\sum_yC(x,y)\psi_y$. Bounding a real crossing-bond factor by one preserves an inequality but not the partition-function identity. Thus no product of the $K_R$ and the ordinary factors has been shown to equal the opposite-hemisphere sector. The one-site nonlocality and the square-root boundary cusp are calculated in LF-BASE-KF0-H.md §H.4; neither is a counterexample to the frozen Root-F coefficient clause.

## Exact interface with the landed gas theorems

`Gas.lean:gas_eq` is an algebraic identity for *already supplied* scalar ordinary weights $\beta_y$ and heavy weights $\tau_z$. In `GasBound.lean:gas_activity_bound`, the quantitative inputs include

$$|\beta_y|\le B_0e^{-\kappa''d(c_y)},\qquad |\tau_z|\le e^{-p-h|z_s|},\tag{B.5}$$

plus nonempty heavy supports, $cr(z)\subseteq z_s$, support-size and connected-union bounds (`hzd`, `hG3`, `hG1`), ordinary entropy `hent`, heavy count `hcount`, and the explicit inequality

$$B_0e^{B_0}e^{\kappa'c}K_0'+\kappa'(c_2+c)+c_1+3+\log K_0''\le h.\tag{B.6}$$

Under these hypotheses its conclusion is $|K(X)|\le3c_1e^{-p}e^{-(\kappa'-2)d(X)}$. `GasCore.lean:gas_activity_bound_core` changes the charged supports to prescribed cores; it still assumes (B.5) for those charged supports and supplies no physical factorization.

For the common product-Gaussian measure, `GasOperator.lean:gasOp_pe` additionally requires exact `DepOn`, measurability and boundedness of each ordinary and heavy function (`hβd`, `hτd`, `hβm`, `hτm`, `hβb`, `hτb`). Its `hB` is pointwise and its heavy `hτ` is

$$\int|\tau_z(\psi;g)|\,d\mu(\psi)\le e^{-p-h|z_s|}.\tag{B.7}$$

It also assumes the geometry and entropy above and its PE inequalities `hG2P`, `hG3P`, `hκ`, and `hα`; see the literal theorem at line 336. `HoleOperator.lean:gasOp_pe_hole` retains `DepOn`, `Bdd`, and (B.7) on its charged support, and adds the hole-closure and Steiner conditions at line 434. The hole theorem therefore does not turn (B.4) into (B.7).

The current results supply an ordinary finite-support expansion only on the all-plus product cutoff and the integrated estimate (B.4) only for an incomplete marked kernel. They do **not** supply `hτd`, `hτb`, or `hτ` for completed heavy functions, nor the exact `gasXiOp` equality needed by `gasOp_eq` (`GasOperator.lean:116`). They also do not supply `hcount` for whatever decorations an exact sparse decomposition would introduce. Theorem B.1 supplies none of these GAS hypotheses; it diagnoses why the independent-spin reference is not an immediate replacement.

If completed activities on one common product reference were constructed with (B.7), exact support, and the remaining geometry and numerical premises, `gasOp_pe` would give a connected activity bound. `FrozenTorus.lean:pe_blockTorus_frozen` and `Holomorphic.lean:pe_PY_analyticOnNhd` could then give the analytic local logarithm once their own rate and lift hypotheses were verified. The Cauchy construction in `notes/phase1/KF0.md` §"The statement and frozen-root bridge" would define $T_1$ by integrating $\partial_{g_i(x)}p_X(tg)$ from $0$ to $1$. This is a conditional implication, not an invocation of those theorems here.

## A check on the frozen logarithm and final status

There is no elementary zero of the partition function on the prescribed source ball. Indeed, with $r=\sum_{x,i}|g_i(x)|<1$ and the positive normalized Gibbs measure at $g=0$, every spin configuration obeys $|\operatorname{Re}\langle g,\phi\rangle|,|\operatorname{Im}\langle g,\phi\rangle|\le r$. Therefore

$$\operatorname{Re}\frac{Z(g)}{Z(0)}=\mathbb E_0\left[e^{\operatorname{Re}\langle g,\phi\rangle}\cos(\operatorname{Im}\langle g,\phi\rangle)\right]\ge e^{-r}\cos r>0.\tag{B.8}$$

This proves analyticity of the *finite-volume principal logarithm* on $\|g\|_1<1$. It gives no spatial locality or volume-uniform polymer bound and hence does not establish the frozen theorem.

**Confidence.** High in Theorem B.1, (B.8), and the literal GAS hypothesis comparison. I have no justified confidence in a claim that options (a), (b), or (c) has been completed. The unresolved mathematical input is an exact linked expansion of the full opposite-hemisphere sector with a support-size weighted norm, or an independent proof of the same local logarithm estimates. No assertion in this note should be used as a completed $k_f=0$ Root-F proof.

## Follow-up: a block-covariance BKAR identity

The following construction answers the algebraic part of the proposed BKAR route. It keeps the complete two-sheet integrand, including the singular chart factor and every normal crossing bond. Its estimates below do not establish a volume-uniform polymer norm.

Let $\mathcal Q_s$ be the set of $s$-blocks of a finite admissible torus $\Lambda$. Put $K_\nu=-\Delta_\Lambda+\nu$, $G_\Lambda=K_\nu^{-1}$, $m=N-1$, and $v=\sqrt\beta,u$. In (F.2) of LF-BASE-KF0.md split the nonnegative normal remainder as $V=\sum_QV_Q+\sum_{\{Q,Q'\}}V_{QQ'}$: $V_Q$ contains the on-site mass and bonds internal to $Q$, while $V_{QQ'}$ contains normal-component bond squares crossing the two blocks. Non-neighboring blocks have $V_{QQ'}=0$. Write $J_x(v_x)=\mathbf1_{\{|v_x|<\sqrt\beta\}}(1-|v_x|^2/\beta)^{-1/2}$, $\Phi_x(v,\sigma)=v_x/\sqrt\beta+\sigma_x\sqrt{1-|v_x|^2/\beta}\,h$, and $\Delta_g(v,\sigma)=\sum_xg_x\cdot(\Phi_x-h)$.

For one real parameter $t_{QQ'}=t_{Q'Q}$ on every pair of distinct blocks, define the site covariance

$$C(t)_{xy}=\begin{cases}G_\Lambda(x,y),&Q(x)=Q(y),\\t_{Q(x)Q(y)}G_\Lambda(x,y),&Q(x)\ne Q(y),\end{cases}\tag{B.9}$$

and, wherever $C(t)$ is positive definite, define

$$F_\Lambda(t;g)=\mathbb E_{\gamma_{C(t)}^{\otimes m}}\sum_{\sigma\in\{\pm1\}^\Lambda}\Bigl(\prod_xJ_x(v_x)\Bigr)
\exp\!\left[-\beta\sum_QV_Q-\beta\sum_{\{Q,Q'\}}t_{QQ'}V_{QQ'}+\Delta_g(v,\sigma)\right].\tag{B.10}$$

The sum is understood to be zero outside the chart domain. The Gaussian normalization $G_\Lambda^{\rm norm}=a_N^{-|\Lambda|}(2\pi/\beta)^{m|\Lambda|/2}(\det K_\nu)^{-m/2}$ is source independent, and (F.4) gives the exact equality $Z_\Lambda^{\rm prob}(g)=G_\Lambda^{\rm norm}e^{\langle g,h\rangle}F_\Lambda(\mathbf1;g)$. The superscript distinguishes this scalar normalizer from the covariance $G_\Lambda$.

**Theorem B.2 (exact finite-volume forest decomposition).** For a forest $T$ on $\mathcal Q_s$ and $u_e\in[0,1]$ on its edges, set $w^T_{QQ}=1$ and, for distinct blocks, set $w^T_{QQ'}$ to the minimum $u_e$ along the unique $T$-path between them, or zero when they lie in different components. Then $C(w^T)$ is positive definite and

$$\frac1{4d+\nu}I\ \le\ C(w^T)\ \le\ \frac1\nu I.\tag{B.11}$$

The integral (B.10) is smooth in all $t$ near every such forest point. After a smooth extension away from these points, the landed scalar `BKAR.bkar_formula_forestIndex_cube_contributions` (`Balaban/External/BKAR/Formula.lean:363`, applied to real and imaginary parts) gives the exact finite-volume identity

$$F_\Lambda(\mathbf1;g)=\sum_{T\text{ forest on }\mathcal Q_s}\int_{[0,1]^{E(T)}}(\partial_{E(T)}F_\Lambda)(w^T(u);g)\,du.\tag{B.12}$$

Each summand in (B.12) factors over the components of $T$. More explicitly, let $F_S$ be (B.10) restricted to the blocks in a nonempty set $S$, using the principal covariance $(G_\Lambda)_{S,S}$, and set

$$A_S(g_S)=\sum_{T\text{ a tree on }S}\int_{[0,1]^{E(T)}}(\partial_{E(T)}F_S)(w^T(u);g_S)\,du,\tag{B.12a}$$

where the one-vertex tree contributes $A_{\{Q\}}=F_{\{Q\}}(0;g_Q)=:f_Q(g_Q)$. Then (B.12) is exactly $F_\Lambda(\mathbf1;g)=\sum_{\pi\text{ a partition of }\mathcal Q_s}\prod_{S\in\pi}A_S(g_S)$. Each $f_Q(g_Q)$ is nonzero when $\|g\|_1<1$: multiplying it by $e^{\langle g_Q,h\rangle}$ gives a positive-measure block integral with source $e^{\langle g_Q,\phi_Q\rangle}$, whose normalized real part is positive by the argument of (B.8). Therefore the exact optional-polymer form is

$$F_\Lambda(\mathbf1;g)=\Bigl(\prod_Qf_Q(g_Q)\Bigr)
\sum_{\substack{\Gamma\text{ pairwise disjoint}\\S\in\Gamma\Rightarrow |S|\ge2}}
\prod_{S\in\Gamma}\frac{A_S(g_S)}{\prod_{Q\in S}f_Q(g_Q)}.\tag{B.12b}$$

This is a finite-volume scalar overlap gas. A term indexed by $S$ depends on the source only through $g$ on the sites of $S$. No norm bound or spatial connectedness is asserted for its activities.

*Proof.* For $r\in[0,1]$, retain the edges of $T$ with $u_e\ge r$. Two blocks have $w^T_{QQ'}=\int_0^1\mathbf1\{Q,Q'\text{ belong to the same retained component at }r\}\,dr$. Hence, for every real site vector $z$,

$$z^TC(w^T)z=\int_0^1\sum_{A\text{ a retained component at }r}z_A^T(G_\Lambda)_{AA}z_A\,dr.\tag{B.13}$$

The spectrum of $K_\nu$ lies in $[\nu,4d+\nu]$, so $(4d+\nu)^{-1}I\le G_\Lambda\le\nu^{-1}I$. Applying these inequalities to each restricted vector $z_A$ proves (B.11). The same bounds hold in each tangent coordinate.

The set of all forest-minimum points is a finite union of compact cube images. By (B.11) it lies in the open set where $C(t)$ is positive definite. On a neighborhood of this compact set, differentiating the Gaussian *density* in $t$ produces a polynomial in $v$ times a smooth Gaussian density. At fixed finite volume and $\beta$, the chart domain $|v_x|<\sqrt\beta$ is bounded, the product of its square-root Jacobians is Lebesgue integrable by (F.1), and $|e^{\Delta_g}|\le e^{2\|g\|_1}$. Thus differentiation under the integral gives $C^\infty$ there without differentiating a hard indicator. A smooth cutoff equal to one near the compact forest-minimum set and supported in that positive-definite neighborhood extends the real and imaginary parts of $F_\Lambda$ to global $C^\infty$ functions, meeting the `BKARContDiff` premise in `Balaban/External/BKAR/Smoothness.lean:44`. The cutoff does not change the value or derivatives in (B.12), so the landed formula proves it.

At a forest point, $C(w^T)$ has no covariance between distinct components of $T$, and $w^T_{QQ'}=0$ removes their crossing $V_{QQ'}$. The integrand and Gaussian measure therefore factor over components. Differentiating only the forest edges preserves this factorization. Group the products of connected-tree contributions by their disjoint block sets; source locality follows directly from (B.10). $\square$

There is also an exact finite-volume observable ledger. Let $\Xi_\Lambda(g)$ denote the last sum in (B.12b). Equation (B.8), the nonvanishing of each $f_Q(g_Q)$, and (B.12b) show that $\Xi_\Lambda(g)\ne0$ for $\|g\|_1<1$. All these functions are holomorphic there: the source is bounded on the compact spin domain, and the $f_Q$ denominators do not vanish. The complex $\ell^1$ ball is convex, so each ratio below has a unique holomorphic logarithm equal to zero at $g=0$. Equality at zero and exponentiation then give

$$\operatorname{Log}\frac{Z_\Lambda^{\rm prob}(g)}{Z_\Lambda^{\rm prob}(0)}
=\langle g,h\rangle+\sum_Q\log\frac{f_Q(g_Q)}{f_Q(0)}
+\log\frac{\Xi_\Lambda(g)}{\Xi_\Lambda(0)}.\tag{B.12c}$$

The left side is the principal logarithm by (B.8). For each block term, the fundamental theorem of calculus gives $\log[f_Q(g_Q)/f_Q(0)]=\sum_{x\in Q}\int_0^1\langle g_x,\partial_{g_x}\log f_Q(tg_Q)\rangle\,dt$; the same radial derivative identity applies to $\Xi_\Lambda$. This supplies the requested linear-in-$g_x$ *form* at finite volume. Its coefficients have no established exponential polymer bound. The singleton terms use torus covariance entries, and their exact agreement between tori has not been proved.

The derivative in (B.12) contains more than a covariance link. If $e=\{Q,Q'\}$ and $\dot C_e$ is the matrix with entries $G_\Lambda(x,y)$ for $x\in Q,y\in Q'$ and the transposed entries, differentiation of the density gives the exact first-derivative insertion

$$-\beta V_{QQ'}+\frac12\sum_{i=1}^m(v^i)^TC(t)^{-1}\dot C_eC(t)^{-1}v^i-\frac m2\operatorname{tr}(C(t)^{-1}\dot C_e).\tag{B.14}$$

Repeated derivatives also hit the inverse covariance and determinant. Equation (B.14) is useful for estimating a tree, but Theorem B.2 asserts no absolute tree bound.

## Peierls estimates valid throughout the forest interpolation

The spectral bounds (B.11) allow the marked-site chart estimate of LF-BASE-KF0.md §G.1 to be used at every forest point. The following version makes the bad-spin gain explicit. Fix $A>0,a>1$, put $\ell_\beta=\log(\beta a)$ and $\delta_\beta=A\ell_\beta/\sqrt{\beta\nu}$, and assume $\beta\ge\max\{4,A^2\ell_\beta^2/\nu_*\}$ so that $\delta_\beta\le1$. (As usual, this is an eventual condition on $\beta$.) For a set $D=B\sqcup M$ of distinct witness sites, require a plus-sheet spin at every $x\in B$ to satisfy $|\Phi_x-h|\ge\delta_\beta$, and choose the minus sheet at every $x\in M$. Let $J_D=\prod_{x\in D}J_x$.

**Theorem B.3 (uniform marked-site estimate).** Under any forest-point Gaussian from Theorem B.2, with $k=|D|$, $C_{m,d}=(2\pi)^{-m/2}(4d+1)^{m/2}\pi^{m/2}\Gamma(1/4)/\Gamma((m+1/2)/2)$, and the indicated sheet marks,

$$\mathbb E\!\left[J_D\prod_{x\in B}\mathbf1_{\{|\Phi_x-h|\ge\delta_\beta\}}\prod_{x\in M}e^{-\frac{\beta\nu}{2}(1+\sqrt{1-|v_x|^2/\beta})^2}\right]
\le \bigl(C_{m,d}^{2/3}\beta^{m/3}2^{m/6}\bigr)^k
\exp\!\left[-\frac{A^2\ell_\beta^2}{24}|B|-\frac{\beta\nu}{2}|M|\right].\tag{B.15}$$

In particular, summing the two possible witness types independently at $k$ selected sites gives an upper bound $e^{-H_\beta k}$, where

$$H_\beta=\min\{A^2\ell_\beta^2/24,\,\beta\nu_*/2\}-\frac m3\log\beta-\frac23\log C_{m,d}-\frac m6\log2-\log2\ \longrightarrow\ +\infty.\tag{B.16}$$

*Proof.* Every principal covariance on $D$ has spectrum in $[(4d+1)^{-1},\nu^{-1}]$ by (B.11). Its $m k$-dimensional Gaussian density is at most $(2\pi)^{-mk/2}(4d+1)^{mk/2}$. Changing $v_D$ to $u_D=v_D/\sqrt\beta$ therefore gives, for $q=3/2$,

$$\mathbb E[J_D^q]\le(C_{m,d}\beta^{m/2})^k.\tag{B.17}$$

Indeed the one-site integral is $\int_{|u|<1}(1-|u|^2)^{-3/4}du=\pi^{m/2}\Gamma(1/4)/\Gamma(m/2+1/4)$, which is the constant in the theorem. If a plus spin is bad, $|\Phi_x-h|^2=2(1-\sqrt{1-|v_x|^2/\beta})\le2|v_x|^2/\beta$; hence $|v_x|^2\ge A^2\ell_\beta^2/(2\nu)$. The covariance upper bound in (B.11) gives

$$\mathbb E\exp\!\left(\frac\nu4\sum_{x\in B}|v_x|^2\right)\le2^{m|B|/2},\qquad
\mathbb P(\text{all plus witnesses bad})\le2^{m|B|/2}e^{-A^2\ell_\beta^2|B|/8}.\tag{B.18}$$

For a minus spin, $(1+\sqrt{1-|v_x|^2/\beta})^2\ge1$, giving $e^{-\beta\nu/2}$ pointwise. Hölder with exponents $3/2$ and $3$, applied to $J_D$ and the plus-witness event, combines (B.17) and (B.18) into (B.15). Replacing $2^{m|B|/6}$ by $2^{mk/6}$ makes its prefactor common to both types. Summing the $2^k$ choices and using $\nu\ge\nu_*$ proves (B.16). $\square$

Theorem B.3 is a valid real Peierls gain for selected distinct witness sites, hence for one witness chosen in each physically bad block. The $e^{-\beta\nu/2}$ factor belongs to a minus-sheet witness; a plus-sheet spin that only crosses the shrinking physical cutoff has the $e^{-A^2\ell_\beta^2/24}$ gain in (B.15), so an $e^{-c\beta\nu}$ charge cannot be assigned to every bad block. The estimate remains valid if multiplied by real normal-bond exponentials of modulus at most one, or by a source exponential of modulus at most $e^{\|g\|_1}$ after the source constant is restored. It is **not** the `hτ` estimate of `gasOp_pe`: the full integrand includes Jacobians at unmarked sites, and mixed derivatives (B.14) insert polynomials that have not been bounded by a product of per-edge and per-vertex factors.

For the literal opposite-hemisphere sector, take $B=\varnothing$ in (B.15). If $D=M$ has one minus-sheet witness in each of $k$ distinct blocks, its marked integral is at most $\exp[-k(\beta\nu_*/2-(m/3)\log\beta-(2/3)\log C_{m,d}-(m/6)\log2)]$. Whenever $\beta\nu_*/4\ge(m/3)\log\beta+(2/3)\log C_{m,d}+(m/6)\log2$, this is at most $e^{-\beta\nu_*k/4}$. Likewise, for any *fixed* chord radius $r\in(0,1)$, replacing the plus bad-spin condition by $|\Phi_x-h|\ge r$ replaces $A^2\ell_\beta^2/24$ in (B.15) by $\beta\nu r^2/24$: the proof of (B.18) uses $|v_x|^2\ge\beta r^2/2$. Thus genuine fixed-radius far spins have an $e^{-c\beta\nu}$ witness reserve. These bounds concern selected witnesses, not the normalized activity of their entire block cluster.

## Why the proposed tree norm and torus clause do not follow

Three precise steps remain after Theorems B.2–B.3.

First, the covariance decay alone does not pay the number of blocks of a tree. Adjacent $s$-blocks contain sites $x\sim y$ across their common face, and the positive walk series gives $G_\Lambda(x,y)\ge(2d+\nu)^{-2}\ge(2d+1)^{-2}$ from its one-step term, independent of $s$ and $\beta$. Across a full common face there are $s^{d-1}$ such pairs, so even $\sum_{x\in Q,y\in Q'}G_\Lambda(x,y)\ge s^{d-1}(2d+1)^{-2}$. A tree can add an adjacent block through an edge of length one. Thus increasing $s=ML$ makes well-separated block links inexpensive, but does not make every new block cost a covariance factor $e^{-c\sqrt\nu s}$. The required weighted sum for arbitrarily prescribed $\kappa$ must also use small ordinary vertices and the bad-site gain (B.16). The near-$h$ ordinary bound (F.13) was proved for whitened variables under a product cutoff; its transfer to the correlated block interpolation, its complement, and its repeated covariance derivatives are not controlled by B.3.

Second, a tree on a set $S$ of blocks need not make $S$ connected in the nearest-neighbor block graph: it may contain a single covariance edge between distant blocks. The raw activity of Theorem B.2 is source-local on $S$ but is not necessarily supported on an `IsPolymer` of the frozen theorem. One must add connecting block paths and pay their cardinality. Decay of $G_\Lambda(x,y)$ can pay the length of a distant path, but the nearby-link issue in the preceding paragraph persists. In particular, declaring the tree's touched blocks to be the connected polymer without this enlargement is false.

Third, the *raw* block-covariance construction does not establish exact two-torus agreement. Let $G_\infty(z)$ be the positive infinite-lattice Green function of $-\Delta+\nu$. The absolutely convergent walk expansions give, for a torus of side $\ell$,

$$G_\ell(0,0)=\sum_{n\in\mathbb Z^d}G_\infty(n\ell),\qquad
G_\ell(0,0)-G_{2\ell}(0,0)=\sum_{n\in\mathbb Z^d\setminus(2\mathbb Z)^d}G_\infty(n\ell)>0.\tag{B.19}$$

Every term is nonnegative and at least one is strictly positive, because a nearest-neighbor walk reaches every lattice point. To see the consequence without an unproved property of the physical integrand, insert the local test observable $f(v_0)=|v_0|^2$ in the one-vertex (empty-tree) block expectation. Its value is $mG_\ell(0,0)$, different from $mG_{2\ell}(0,0)$ even when that block lies well inside both quarter boxes. Thus the BKAR construction using the unlocalized torus covariance does not, by itself, give torus-identical one-block coefficients. Winding walks must be separated and assigned to supports large enough to record their winding before exact lift can be claimed. This is an obstruction to the *raw BKAR coefficient construction*, not a counterexample to Root-F.

There is also a cancellation in the derivative bound that cannot be discarded. For a centered two-variable Gaussian with variances $a,b>0$ and covariance $tc$, the derivative of $\mathbb E_t1$ is zero. At $t=0$ the density score is $cv_1v_2/(ab)$, whose absolute expectation is $2|c|/(\pi\sqrt{ab})>0$. Taking absolute values of the density insertion (B.14) before subtracting the Gaussian vacuum therefore loses the factor that should make an ordinary vertex small as $\beta\to\infty$. A proof of the requested weighted tree estimate must perform this centered cancellation at every derivative order and integrate the hard Jacobians uniformly. Neither `BKAR.bkar_formula` nor Theorem B.3 supplies that estimate.

The proposed massive decay itself is valid, with an explicit uniform lattice rate. On any torus of side at least three, let $\rho(x)=\operatorname{dist}_{\rm graph}(x,y)$, $W_{xx}=e^{a_\nu\rho(x)}$, and $a_\nu=\operatorname{arcosh}(1+\nu/(4d))$. Each nearest-neighbor edge changes $\rho$ by at most one. Taking the real part of the quadratic form of $WK_\nu W^{-1}$ edge by edge gives

$$\operatorname{Re}\langle f,WK_\nu W^{-1}f\rangle\ge[\nu-2d(\cosh a_\nu-1)]\|f\|_2^2=\frac\nu2\|f\|_2^2.\tag{B.20}$$

Indeed an edge $\{x,z\}$ contributes $|f_x|^2+|f_z|^2-2\cosh(a_\nu[\rho(x)-\rho(z)])\operatorname{Re}(\bar f_xf_z)$, which is at least $-(\cosh a_\nu-1)(|f_x|^2+|f_z|^2)$. The inverse of this accretive finite matrix has operator norm at most $2/\nu$. Since $\rho(y)=0$, its $(x,y)$ entry yields

$$0<G_\Lambda(x,y)\le\frac2\nu e^{-a_\nu\operatorname{dist}_{\rm graph}(x,y)},\qquad
a_\nu\ge\frac{\sqrt\nu}{2\sqrt d}\quad(0<\nu\le1).\tag{B.21}$$

The last inequality follows from $\cosh z\le1+z^2$ for $0\le z\le1$, applied to $z=\sqrt{\nu/(4d)}$. In particular, for distinct blocks and their minimum site distance $D(Q,Q')$, one has the explicit uniform bound $\sum_{x\in Q,y\in Q'}G_\Lambda(x,y)\le(2/\nu)s^{2d}e^{-a_\nu D(Q,Q')}$. Thus long covariance edges can pay a connecting block path when $s a_\nu>\kappa$; the one-step lower bound above shows why this decay is insufficient for adjacent edges. The estimate is compatible with the landed, differently parameterized `kf0_resolvent_decay` in `Balaban/Green/KF0Reference.lean:468`.

The exact overlap gas (B.12b) clarifies the GAS interface. One could use no ordinary indices (so `hB` is vacuous with $B_0=0$) and index heavy terms by $S$, with scalar weight $R_S(g)=A_S(g_S)/\prod_{Q\in S}f_Q(g_Q)$. A scalar weight regarded as a constant function of a product reference is automatically measurable, bounded, and `DepOn` every prescribed support; thus `gasOp_pe`'s `hτd` and `hτb` are *formally available for these already integrated scalar terms*. The real missing numerical premise is $|R_S(g)|\le e^{-p-h|z_s|}$, uniformly in volume, together with connected charged supports $z_s$, `hzd`/`hG3` geometry, and `hcount`. In particular, the requested weighted summability would require a volume-uniform estimate of the form $\sup_Q\sum_{z:Q\in z_s}e^{\kappa|z_s|}\sup_{\|g\|_1\le1/2}|\tau_z(g)|\le\epsilon_\beta$ with $\epsilon_\beta\to0$ for a torus-coherent connected-support refinement of the $R_S$. No such estimate follows from (B.11), (B.15), or (B.21). Taking $z_s=S$ gives exact source support but can be disconnected and has arbitrarily many size-$v$ choices through one block as the torus grows. Taking a connected hull requires a paid path decoration and torus-coherent assignment. The singleton factor $f_Q$ in (B.12c) needs its own uniform bound and exact-lift construction. For the *unintegrated* common-Gaussian representation (F.4), completed bounded `DepOn` heavy functions and the exact `gasXiOp` identity remain missing as stated earlier.

**Follow-up status.** The exact finite-volume BKAR identity, its source-local scalar overlap gas, and the uniform interpolated Peierls estimate are proved above. They do not supply the support-size weighted `hτ` bound, connected charged supports and their count, or exact nonwinding lift. Consequently the bounded local $T_1$ and the two-torus clause remain unproved. Confidence is high in (B.9)–(B.21) as finite-volume identities and inequalities; the quantitative cluster estimate that would complete the $k_f=0$ branch has not been established.

## Round 3: an exact positive finite-range decomposition

The cited finite-range papers establish positive *semidefinite* decompositions of lattice resolvents: Brydges–Guadagni–Mitter, [Theorem 1.1(1)–(2)](https://arxiv.org/pdf/math-ph/0303013), has range proportional to $L^j$ (its printed rescaled cutoff is $6L$), while Bauerschmidt, [Theorem 1.2, Example 1.3, and Remark 1.7](https://arxiv.org/pdf/1206.2212), gives finite-range positive forms for massive discrete elliptic operators and scale-kernel estimates. The precise range $L^j/2$ and the remainder estimate in the question are not literal statements of those cited theorems. For the present nearest-neighbor operator the following elementary decomposition is exact and has a local independent-noise representation, so no unproved transfer from either paper is needed.

Let $A_\Lambda$ be the nearest-neighbor adjacency matrix on a torus of side at least three, counting oriented steps with multiplicity, and set $a=2d+\nu$, $q=2d/a<1$, and $G_\Lambda=(aI-A_\Lambda)^{-1}$. For every integer $n\ge0$ define

$$\Gamma_n^\Lambda=a^{-2n-2}A_\Lambda^n(aI+A_\Lambda)A_\Lambda^n
=a^{-2n-1}A_\Lambda^{2n}+a^{-2n-2}A_\Lambda^{2n+1}.\tag{B.22}$$

**Theorem B.4 (walk finite-range decomposition).** Each $\Gamma_n^\Lambda$ is positive semidefinite, has graph range at most $2n+1$, and has nonnegative entries. Moreover

$$G_\Lambda=\sum_{n=0}^\infty\Gamma_n^\Lambda,\qquad
R_N^\Lambda:=\sum_{n=N}^\infty\Gamma_n^\Lambda
=a^{-2N}A_\Lambda^{2N}G_\Lambda,\qquad
\|R_N^\Lambda\|_{2\to2}=\frac{q^{2N}}{\nu},\qquad
\sum_yR_N^\Lambda(x,y)=\frac{q^{2N}}{\nu}.\tag{B.23}$$

There is an explicit product-Gaussian realization. For each $n$ take independent standard real Gaussians $\eta_{n,z}$ at sites and $\xi_{n,e}$ at unoriented nearest-neighbor edges, all independent across $n$. With $b_e=\mathbf1_{\{x\}}+\mathbf1_{\{y\}}$ for $e=\{x,y\}$, set

$$\zeta_n=a^{-n-1}A_\Lambda^n\left(\sqrt\nu\,\eta_n+\sum_e b_e\xi_{n,e}\right).\tag{B.24}$$

Then $\operatorname{Cov}(\zeta_n)=\Gamma_n^\Lambda$ and $\sum_n\zeta_n$ converges in $L^2$ and almost surely at every site to a field with covariance $G_\Lambda$. Each $\zeta_n(x)$ reads only site noises at graph distance at most $n$ from $x$ and edge noises with an endpoint at distance at most $n$.

*Proof.* Since the spectrum of $A_\Lambda$ lies in $[-2d,2d]$, $aI+A_\Lambda\ge\nu I$, so the first expression in (B.22) is positive semidefinite. Its second expression proves finite range and entrywise nonnegativity by the walk interpretation of $A_\Lambda^r$. The norm-convergent geometric series gives
$\sum_{n\ge0}a^{-2n-2}A^{2n}(aI+A)=(aI+A)(a^2I-A^2)^{-1}=(aI-A)^{-1}$, and shifting the series gives $R_N=a^{-2N}A^{2N}G$. On the constant vector, $A$ has eigenvalue $2d$ and $G$ has eigenvalue $\nu^{-1}$; positivity and the spectral bounds show this is the maximal eigenvalue of $R_N$, proving the norm equality and its row sum. On the $2d$-regular torus, $\sum_e b_eb_e^{\mathsf T}=2dI+A$, hence the covariance of the bracket in (B.24) is $\nu I+2dI+A=aI+A$. This proves its stated covariance and support. Independent centered Gaussian summands with summable variances converge in $L^2$ and almost surely at each of the finitely many sites; their covariance sum is $G$. $\square$

For $L\ge4$, put $N_0=0$, $N_j=\lfloor L^j/4\rfloor$ for $j\ge1$, and $\widehat\Gamma_j=\sum_{n=N_{j-1}}^{N_j-1}\Gamma_n$. Thus

$$G_\Lambda=\sum_{j=1}^{J}\widehat\Gamma_j+R_{N_J}^\Lambda,\qquad
\operatorname{range}(\widehat\Gamma_j)\le2N_j-1\le L^j/2,\qquad
\|R_{N_J}^\Lambda\|=\frac{q^{2N_J}}{\nu}
\le\frac1\nu\exp\!\left[-\frac{\nu_*}{2d+1}\left(\frac{L^J}{2}-2\right)\right].\tag{B.25}$$

All constants are uniform in the torus and $\nu\in(\nu_*,1]$. In particular $J=3$ is sufficient for the numerical estimate $\|R_{N_3}\|\le L^{-6}/\nu$ whenever $L$ is large enough that $\frac{\nu_*}{2d+1}(\frac{L^3}{2}-2)\ge6\log L$. This explicit condition is eventually true because $\nu_*=7/(8L^2)$. The grouping has only three scales, but its residual is small rather than zero. For fixed $L$, continuing the sum over all $j$ removes that residual exactly.

Positive semidefinite cannot silently be replaced by strictly positive definite here. If the torus side is divisible by four, the Fourier mode with every coordinate momentum $\pi/2$ has adjacency eigenvalue zero. Every $\widehat\Gamma_j$ with $j\ge2$ vanishes on this mode, because all its terms have $n\ge N_1\ge1$. Thus those pieces have no full-dimensional Gaussian density and the inverse-covariance score (B.14) cannot be applied to them separately. Formula (B.24) realizes their possibly degenerate laws on a product-noise space and avoids that particular difficulty, but does not supply a cluster estimate.

Strict positivity can also be imposed without changing the sum. Put $\epsilon=\nu/(2a^2)$, replace $\Gamma_0$ by $\Gamma'_0=\Gamma_0-\epsilon I$, and for $n\ge1$ put $\Gamma'_n=\Gamma_n+\epsilon2^{-n}I$. Then $\sum_n\Gamma'_n=G$, $\Gamma'_0\ge\epsilon I$, and $\Gamma'_n\ge\epsilon2^{-n}I$ for $n\ge1$; every range bound is unchanged, and the grouped $\widehat\Gamma'_j$ are strictly positive definite with the range in (B.25). The local-noise factor for $\Gamma'_0$ is (B.24) at $n=0$ with $\sqrt\nu$ replaced by $\sqrt{\nu/2}$, while $\Gamma'_n$ for $n\ge1$ adds an independent site noise of variance $\epsilon2^{-n}$. For $N\ge1$ the new tail is $R_N+\epsilon2^{1-N}I$, with norm $q^{2N}/\nu+\epsilon2^{1-N}$. Its off-diagonal entries and its two-torus difference (B.28) are exactly those of $R_N$. Thus the singularity can be repaired, but the nonlocal residual and hard chart remain.

### Connected walk footprints and an actual weighted covariance bound

The two terms in (B.22) can be expanded into nearest-neighbor walks $\omega$ rooted at $x$: a walk of length $2n$ has coefficient $a^{-2n-1}$ and a walk of length $2n+1$ has coefficient $a^{-2n-2}$. Give each walk the *full set of $s$-blocks visited by its vertices*, denoted $X(\omega)$, rather than only its endpoint blocks. Consecutive sites of the walk lie in the same or neighboring blocks, so $X(\omega)$ is connected in the nearest-neighbor block graph used by Balaban/Polymer/Lattice.lean:10,30. Partition a length-$r$ path into pieces of at most $s$ steps. Each piece stays in a radius-$s$ cube and meets at most $3^d$ blocks. Hence

$$|X(\omega)|\le3^d(1+r/s).\tag{B.26}$$

Put $q_*=2d/(2d+\nu_*)$ and $a_*=2d+\nu_*$. Summing the positive coefficients of all walks rooted at a site gives $\sum_y\Gamma_n^\Lambda(x,y)=(a+2d)a^{-2}q^{2n}$. Therefore, for every $\kappa\ge0$ and $s=ML$ satisfying $q_*^2e^{2\kappa3^d/s}<1$,

$$\sup_{\Lambda,\nu,x}\sum_{n\ge0}\ \sum_{\substack{\omega_0=x\\|\omega|\in\{2n,2n+1\}}}
e^{\kappa|X(\omega)|}\,w(\omega)
\le\frac{a_*+2d}{a_*^2}\,
\frac{\exp[\kappa3^d(1+1/s)]}{1-q_*^2\exp(2\kappa3^d/s)}<\infty.\tag{B.27}$$

Here $w(\omega)$ is the coefficient just specified, and the supremum is over admissible finite tori and $\nu\in(\nu_*,1]$. The condition is equivalent to $s>3^d\kappa/\log(1/q_*)$ and can be met by choosing $M$ after $L,\kappa$. For the physical tangent variable $u=\beta^{-1/2}\sum_n\zeta_n$, the covariance-walk bound (B.27) is multiplied by $\beta^{-1}$. This is a proved support-size weighted bound for *covariance atoms*. It is not a bound for the nonlinear spin activities.

Every coefficient $w(\omega)$ is a function only of $a,d,n$, and the sequence of nearest-neighbor steps. If the full visited path lies in a common non-winding lift of two tori, it has the same coefficient and block footprint on both; this proves exact termwise lift for the decorated covariance expansion. Merely knowing that a kernel has finite range would not give this statement: the range-zero kernels $c_\ell I$ with torus-dependent $c_\ell$ are an elementary counterexample to automatic lift. It would also not make endpoint blocks connected: in $d\ge2$ a two-step walk can join sites in blocks meeting only at a corner, while the intermediate site lies in a third block.

The finite-$J$ remainder is the first point where a proposed *few-scale exact* argument fails. For every $N$ and every $x,y$, $R_N^\Lambda(x,y)>0$: the term $A^{2N}(x,x)G_\Lambda(x,y)$ in (B.23) is strictly positive (with $A^0(x,x)=1$). Thus the residual Gaussian has covariance at arbitrary separation, however small its operator norm. If $R_N^\infty$ is defined on $\mathbb Z^d$ by the same absolutely convergent walk sum, periodization gives

$$R_N^\ell(0,0)-R_N^{2\ell}(0,0)
=\sum_{z\in\mathbb Z^d\setminus(2\mathbb Z)^d}R_N^\infty(z\ell)>0.\tag{B.28}$$

The positivity follows from $R_N^\infty(z)>0$ for every $z$. Dropping $R_{N_J}$ changes the partition function, and retaining it as one Gaussian piece restores the original nonlocality and torus dependence. An exact proof must either keep *all* scales and localize each term, or expand the remainder further into finite-footprint atoms. The small norm in (B.25) cannot replace an exact identity or exact quarter-box agreement.

### The centred good sector and the hard-chart obstruction

The product noise of (B.24) gives the exact law of the tangent Gaussian in (F.4), equivalently (B.10) at $t=\mathbf1$, if one takes an independent copy in each of the $m=N-1$ tangent directions and puts $v=\sum_{n\ge0}\zeta_n$. Consequently the marked-site Peierls estimate (B.15) remains valid under this realization. For a fixed site $x$, the local hard factor $J_x(v_x)$ nevertheless reads noises at arbitrarily distant sites: for every distant $z$, the coefficient of $\eta_{n,z}$ in $v_x$ is $\sqrt\nu\,a^{-n-1}A^n(x,z)>0$ when $n=\operatorname{dist}(x,z)$. Even on one fixed torus, the coefficients of $\eta_{2n,x}$ are positive for every $n$. Varying any one of these real noises changes the chart indicator or Jacobian. Thus the *full* factor is not DepOn any finite set of independent noise variables, even though every individual $\zeta_n(x)$ is local. This is the exact algebraic point where finite range of the covariance pieces stops short of finite support for a nonlinear factor.

On a controlled plus-sheet region there is real smallness. If $|v_x|,|v_y|\le p$ and $p^2/\beta\le1/4$, then $t_x=\sqrt{1-|v_x|^2/\beta}$ obeys $1-t_x\le |v_x|^2/\beta$, and direct calculus gives

$$0\le J_x-1\le\frac{p^2}{\beta},\qquad
\frac{\beta\nu}{2}(1-t_x)^2\le\frac{\nu p^4}{2\beta},\qquad
\frac{\beta}{2}(t_x-t_y)^2\le\frac{2p^4}{\beta}.\tag{B.29}$$

These are the small site and crossing-bond factors required for an ordinary expansion. For an $s$-block $Q$, let $F_Q^+$ be the product of its plus-sheet Jacobians and its on-site and internal-bond normal exponentials. Since $Q$ has $s^d$ sites and at most $ds^d$ internal bonds, (B.29) implies the explicit pointwise bound $|F_Q^+-1|\le\exp\{s^d[p^2+\nu p^4/2+2dp^4]/\beta\}-1$ on the cutoff. It tends to zero after $L,M,p$ are fixed and $\beta\to\infty$. A cutoff on $v_x=\sum_n\zeta_n(x)$ is itself nonlocal in the product noises. A possible next construction would cut off each independent noise level separately and expand the resulting analytic factors in finite walks. LF-BASE-KF0.md F.2 proves an analogous finite-walk majorant for its own product cutoff, but does not prove this infinite-level construction. Restoring the complement requires activities for the unbounded noise levels and the opposite spin sheets, with their complete neighboring factors.

The centred cancellation can be stated at *every tree order* for a factorized auxiliary model. Let $S$ be a finite set of blocks, let $C(t)$ be positive definite on the interpolation domain, with fixed within-block marginals and independent cross-block parameters, and let $R_Q(v_Q)$ be bounded local perturbations with no crossing interaction. For any tree $T$ on $S$ with $|S|\ge2$,

$$\partial_{E(T)}\mathbb E_{C(t)}\prod_{Q\in S}(1+R_Q)
=\partial_{E(T)}\mathbb E_{C(t)}\prod_{Q\in S}R_Q.\tag{B.30}$$

Indeed expand the product on the left over subsets $U\subseteq S$. For every proper $U$, choose $Q\in S\setminus U$ and an edge $e$ of $T$ incident to $Q$. The marginal law on $U$ is independent of $t_e$, so its mixed derivative vanishes. This proves (B.30) without taking absolute values of Gaussian density scores. In the physical two-sheet integral, the crossing normal factors $e^{-\beta V_{QQ'}}$ are present. Expanding each as $1+(e^{-\beta V_{QQ'}}-1)$ attaches a perturbation to both endpoint blocks; (B.29) bounds that perturbation in the controlled plus sector, and (B.15) gives a Peierls reserve for selected bad witnesses. Neither equation bounds the sum of all differentiated trees with their complete chart factors.

There is a sharp integrability barrier to the simplest Gaussian tree estimates. For any nondegenerate Gaussian one-site marginal, at every finite $\beta$,

$$\mathbb E[J_x(v_x)^2]
=\int_{|v|<\sqrt\beta}\frac{p_\beta(v)}{1-|v|^2/\beta}\,dv
=\infty,\tag{B.31}$$

because its density $p_\beta$ is continuous and strictly positive at the chart sphere, while the radial integral has a logarithmic divergence. The real normal-field and bond exponentials remain finite and positive at that sphere, so they do not remove this local $L^2$ obstruction. The $L^{3/2}$ estimate (B.17) survives, but an arbitrary-degree tree requires a uniform mixed-derivative or conditional-smoothing estimate that can distribute such $L^p$ moments, retain the centred cancellation, and pay for every bad block after all unmarked Jacobians are included. No such estimate is in the cited finite-range decomposition theorems or the landed gas theorems.

**Round-3 conclusion and GAS interface.** Equations (B.22)–(B.27) prove an exact positive finite-range Gaussian decomposition, an independent local-noise realization, connected walk footprints, and a volume-uniform $e^{\kappa|X|}$ *covariance-atom* norm. Full-path decorations give exact two-torus lift for these atoms. At any bounded number of scales, leaving the nonzero residual (B.28) as one piece defeats automatic exact support and lift; at infinitely many scales the hard-spin factors still read infinitely many noises. The controlled plus sector has the explicit $\beta^{-1}$ factors (B.29), and (B.30) performs the Gaussian vacuum cancellation at every tree order for block-local factors. What remains unproved is an exact decomposition of the *complete* bad-noise/opposite-sheet integrand into bounded, finite DepOn functions with the support-size weighted heavy-activity bound (B.7), connected-support geometry and counting of GasBound.lean:445 and GasOperator.lean:336. Moreover, GasOperator.lean:39 assumes a finite reference-index type, so the countably many noise levels in (B.24) would require a finite-regulator argument with a uniform weighted estimate before passing to the limit. The observable identity (B.12c) consequently has no proved bounded local $T_1$, and the physical quarter-box two-torus clause remains open. Confidence is high in the elementary identities (B.22)–(B.31) and in the stated failure of finite truncation; this is not a proof or counterexample for the frozen Root-F clause.

## Round 4 (17 October 2026): may the existential final index be one?

### Claim and units

**The numerical observation is correct, but it does not instantiate the landed RG step.** Fix $L\ge3$, $\nu_* =7/(8L^2)$ and $\nu\in(\nu_*,1]$. The frozen [Root-F statement, lines 40–78](/home/scott/Balaban/Balaban/Frozen/Roots/LogPartitionMultiscale.lean:40) asks only for *some* $k_f$ with $L^{k_f}\sqrt\nu\le L$ and $1/2\le L^{k_f+1}\sqrt\nu$. For $k_f=1$, the first inequality is $\sqrt\nu\le1$, and the second follows from $L^2\sqrt\nu>\sqrt{7/8}\,L\ge1/2$. This choice changes the required conclusion: the sum includes **both** $j=1$ and $j=2$, with coefficient bounds at each scale, and is asserted on tori divisible by $ML^2$. It cannot be implemented by merely renaming the $j=1$ last integral.

Write $m_0=\nu L^2$ for the block-unit mass needed by the first $0\to1$ step. If the conditional running relation of [RunningHyp](/home/scott/Balaban/Balaban/LargeField/Analytic/Constants.lean:60) holds, write $v_1=\nu L^2\delta_1$ for the mass of the proposed final integral. Since $|\log\delta_1|\le\epsilon\le1/20$, [StopIndex.nu_two_sided](/home/scott/Balaban/Balaban/Flow/StopIndex.lean:85) gives

$$\frac78 e^{-\epsilon}<v_1\le L^2e^\epsilon\le\frac{20}{19}L^2.\tag{B.32}$$

At the initial scale $\beta\nu>1$ for every sufficiently large $\beta$ uniformly in this interval, so [KZeroGenuine](/home/scott/Balaban/Balaban/LargeField/Analytic/Constants.lean:128) is false and $k_0=0$ is the conventional index. This is *not* by itself a general assumption of all steps: [Def6v2Regime](/home/scott/Balaban/Balaban/SmallField/Def6v2Regime.lean:29) distinguishes the physical mass of the small-field class from the zero large-field background mass at the conventional $k_0$. The small-field complete background of the proposed $0\to1$ step still has physical mass $\nu$, so its level-one mass product is $m_0$.

### Source and landed-premise inventory

The following are classifications of **hypotheses as they stand**, with repeated downstream wrappers grouped at their producer. Here (a) means the hypothesis holds, (b) means a displayed estimate has a bounded-mass replacement with the stated constant but the consumer still needs to be rebuilt, and (c) means the existing hypothesis fails for part or all of the requested interval. A (c) is an obstruction to *this proof interface*, not a counterexample to Root-F.

| Interface and exact source anchor | For $0\to1$ and then final $v_1$ | Classification / replacement |
| --- | --- | --- |
| [StopIndex.kStop](/home/scott/Balaban/Balaban/Flow/StopIndex.lean:165), `kStop_spec`, `kStop_min`, `massLe_of_lt_kStop` (lines 207–210); [FlowHorizon](/home/scott/Balaban/Balaban/LargeField/Counter/FlowHorizon.lean:13) | The paper/landed $k_f$ is the **first** index above $7/(8L^2)$. For exact initial running mass $n_0=\nu$, that index is $0$; there is no $0<kStop$ premise to produce an ordinary first step. | **(c)** for using the landed stop-index bridge. Root-F itself has no minimality condition, so a *new* bridge with a deliberately delayed stop is logically permitted. |
| [ScaleUniform.massLe_iff](/home/scott/Balaban/Balaban/Fluctuation/ScaleUniform.lean:50) and `not_massLe_of_gt` (107–110); [BgHyp.massLe](/home/scott/Balaban/Balaban/Background/ExistenceSetup.lean:41); [LevelStepSettingGeneral.bgHyp_lvG](/home/scott/Balaban/Balaban/Inhabited/LevelStepSettingGeneral.lean:157); [RayData.H](/home/scott/Balaban/Balaban/Fluctuation/StepRegBg.lean:48) | The complete background of the first step requires $\nu L^2\le1$. This holds only for $\nu\le L^{-2}$ and fails for $\nu>L^{-2}$. The 103 `Inhabited/` and 18 `Fluctuation/` files matching the literal general/specialized step premise $\nu L^{2(k+1)}\le1$ are consumers or wrappers of this same gate, including source and marked-activity producers. | **(a)** on the lower subinterval, **(c)** on $(L^{-2},1]$. More coercivity cannot supply a missing proof of `BgHyp`. |
| [Background.Data.InUnionDomainC](/home/scott/Balaban/Balaban/Background/Data.lean:306), [Theorem73](/home/scott/Balaban/Balaban/Background/Theorem73.lean:359), [XiMassResponse](/home/scott/Balaban/Balaban/SmallField/XiMassResponse.lean:120), [ClassOldBirthRun.hmargin](/home/scott/Balaban/Balaban/Fluctuation/ClassOldBirthRun.lean:206) | The complex chart itself is empty when $m_0>1$ (proof below). The mass-response step has the stronger margin $m_0(1+r)\le1$, $r>0$. At $m_0=1$ even an arbitrarily small positive mass variation exits the chart. | **(c), structural.** A massive chart must change the relation between its radii; replacing `massLe` by $m_0\le L^2$ leaves an empty domain. On $m_0<1$ a positive $r$ exists, but no fixed $r>0$ works uniformly as $m_0\uparrow1$. |
| [Multiscale.PointwisePotential.laplacian_bound](/home/scott/Balaban/Balaban/Multiscale/PointwisePotential.lean:143), [Background.Calculus.Rsc_bound](/home/scott/Balaban/Balaban/Background/Calculus.lean:163), [Background.Contraction](/home/scott/Balaban/Balaban/Background/Contraction.lean:622) | These estimate the **upper** mass contribution. The first already takes $\Lambda=\nu L^{2k}$ and gives $3+\Lambda$. The `Rsc_bound` proof splits $2d$ gradient terms, $6$ block terms and $1+\nu\ell^2$ mass/multiplier terms. | **(b)** algebraically: with $\nu\ell^2\le m_{\max}$, use $3+m_{\max}$ and $(2d+7+m_{\max})VW$ (vector version $N(2d+7+m_{\max})VW$), instead of $3+1$ and $N(2d+8)VW$. At the first step $m_{\max}=L^2$ is safe from $\nu\le1$. The contraction radius and downstream cut-resolvent bounds must be reproved; these displayed constants alone do not do that. |
| [Localization.Decoupled.DGSetting.massLe](/home/scott/Balaban/Balaban/Localization/Decoupled.lean:146), [Decoupled2.OpSetting.massLe](/home/scott/Balaban/Balaban/Localization/Decoupled2.lean:129), [NC3.laplacian_cut_bound](/home/scott/Balaban/Balaban/Localization/NC3.lean:219) | The decoupled first-step background and cut operators also require $\nu L^{2(k+1)}\le1$ through their level-$k+1$ settings. | **(c)** for $m_0>1$ as declarations. Their Laplacian upper-bound subestimate admits $3+m_{\max}$, but this does not construct new decoupled settings, inverses or complex charts. |
| [Fluctuation.InteractionEnergyScaled](/home/scott/Balaban/Balaban/Fluctuation/InteractionEnergyScaled.lean:88), `energyBdScaled` (117) | Its use of $\nu L^{2(k+1)}\le1$ bounds the quadratic mass density. | **(b)** for this algebraic term: replace $(1+\rho)/L^2$ in the scale-free block constant by $(m_{\max}+\rho)/L^2$. At $k=0$, $m_{\max}=L^2$ gives $d+1+\rho/L^2$ in its bracket. The localization and smallness thresholds that consume `energyBdScaled` need recalculation. |
| [Green.CoarseOperator.coarseOperator_form_of_nonneg](/home/scott/Balaban/Balaban/Green/CoarseOperator.lean:278), [coarseGreen_decay_of_nonneg](/home/scott/Balaban/Balaban/Green/CoarseOperator.lean:345) | The older `coarseOperator_form` and `coarseGreen_decay` wrappers carry $v\le2$, but these stronger landed declarations cover every $v\ge0$ with the same `trGamma d L` and `trRate d L`; the proof handles $v\ge2$ in [coarseOperator_form_large](/home/scott/Balaban/Balaban/Green/CoarseOperator.lean:236). The decay theorem still assumes a scale index $k\ge1$. | **(a)** for the mass bound of this coarse covariance at the proposed final scale $k=1$. Its decay theorem does not directly cover the first scale $k=0$, nor does it extend the first-step complex background domain or `FinalMassGreen`, which concerns a different final operator. |
| [nuIdeal](/home/scott/Balaban/Balaban/SmallField/Def6Terms.lean:71), [Def6v2Regime.physMass_nuIdeal](/home/scott/Balaban/Balaban/SmallField/Def6v2Regime.lean:106), [Def6AvgBridge.termwise_irrelevant_avg](/home/scott/Balaban/Balaban/SmallField/Def6AvgBridge.lean:83), [Def7Variants.SFFlat/D9Flat](/home/scott/Balaban/Balaban/LargeField/Def7Variants.lean:113) | Matching at $k=1$ gives `nuIdeal L 1 v₁ 1 = v₁` and at $j=0$ gives $v_1/L^2$; it is an identity, not a smallness proof. The displayed irrelevance theorem separately requires `nuIdeal ... j ≤ σ²`; the flat class and D9 require running mass $\le1$. | **(a)** for the identity; **(c)** for those conditional bounds if $v_1>1$ (or $v_1>\sigma^2$). The irrelevance theorem may be avoidable at the top level, but it cannot be invoked there as stated. A class with mass cap $V=(20/19)L^2$ and redone term bounds is needed. |
| [LargeField.PositiveMassFacts.fieldClose_of_flow](/home/scott/Balaban/Balaban/LargeField/R/PositiveMassFacts.lean:79), [History.EarlyMassRatio](/home/scott/Balaban/Balaban/LargeField/History/EarlyMassRatio.lean:19) | The early-field argument uses $\beta_k\nu_k\le e^{2\epsilon}$ (and genuine $k_0$) to infer $2\sqrt{\nu_k}<O(\delta_k)$ or $2\nu_k<\delta_k^2$. Here $\beta\nu\to\infty$ while $\delta_0\to0$. | **(c)** for this argument. Larger mass makes these *inequalities* worse. A new high-field localization using closeness of the actual minimizer to $h$, or a new bad-block Peierls argument, is required; `KZeroGenuine` should not be inserted falsely. |
| [Green.FinalHessian](/home/scott/Balaban/Balaban/Green/FinalHessian.lean:340), [FinalMassGreen](/home/scott/Balaban/Balaban/Green/FinalMassGreen.lean:16), [FinalMassSqrt](/home/scott/Balaban/Balaban/Green/FinalMassSqrt.lean:43), [FinalCutComplex](/home/scott/Balaban/Balaban/Green/FinalCutComplex.lean:392) | Their final mass argument is $v$, with $0\le v\le1$ and $7/(8L^2)<v$; $k\ge1$ is satisfied by $k_f=1$. Equation (B.32) supplies the lower threshold, but not $v\le1$. | **(a)** for $k\ge1$ and the lower mass bound; **(c)** for $v\le1$ on most of the interval. The replacement Gaussian inequality with explicit $V$ and gap is (B.34) below. Cut-parameter, square-root and physical interaction results still need to be rerun with it. |
| [Green.FinalTorusCloseUnif](/home/scott/Balaban/Balaban/Green/FinalTorusCloseUnif.lean:410), `X_sum_close` and the uniform theorems (890ff); [FinalConstants.cutoffInteraction_final_phys_comp](/home/scott/Balaban/Balaban/Green/FinalConstants.lean:87) | Several lift/close estimates additionally use $\sqrt v\le1$ (for example line 424), and the displayed physical final cutoff and coefficient theorems pass `hv1 : v≤1`. Exact two-torus agreement of coefficients is obtained after a cut/localization expansion, not by entrywise equality of raw Green kernels. | **(c)** as landed. One may cap the fine Green decay exponent by $\min(\sqrt v,1)$ and replace $\sqrt v\le1$ by $\sqrt v\le\sqrt V$, but the resulting numerical and torus-close statements are new proofs. The physical final theorem also takes analytic interaction and bound hypotheses; `FinalTailGas` explicitly leaves its heavy-activity bound as an input. |

The background and fluctuation rows include the smaller `hν` interfaces of `Background/WeightedProp51Basic.lean:392`, `Background/Existence.lean:68`, `Fluctuation/RenDom.lean:83,110`, and `SmallField/XiMassResponseBounds.lean:95`: their hypotheses are the same $\nu L^{2q}\le1$ at the relevant level, or a direct use of it. The `LargeField/Operators/StepData.lean` axiomatizes a step kernel satisfying (S0)–(S2); [BaseStep](/home/scott/Balaban/Balaban/Inhabited/BaseStep.lean:13) only inhabits this interface with a zero kernel. Neither is a physical high-mass $0\to1$ producer. [Flow.RGInfty](/home/scott/Balaban/Balaban/Flow/RGInfty.lean) is conditional coupling recursion, not such a density theorem. This is why changing the stop index does not bypass the open opposite-hemisphere activity of Rounds 1–3: it relocates it to the first-step large-field kernel.

### Two exact obstructions and a bounded-mass Gaussian replacement

**Empty-chart lemma.** Put $m=\nu L^{2q}$. By [InUnionDomainC](/home/scott/Balaban/Balaban/Background/Data.lean:308), membership requires $0<\delta\le\varepsilon$ and $m\varepsilon^2\le\delta^2$. Since $\varepsilon>0$, division by $\varepsilon^2$ gives $m\le(\delta/\varepsilon)^2\le1$. Thus for $q=1$ and $\nu>L^{-2}$ the complex domain is empty even at the perfectly aligned datum $\Psi=h$. For $m=1$ the radii must satisfy $\delta=\varepsilon$; the positive variation $m(1+t)$, $t>0$, has no such domain. This refutes the proposed repair “increase the constant in `BgHyp.massLe`” for the actual landed chart. The additional [D2(b) margin](/home/scott/Balaban/Balaban/Fluctuation/ClassOldBirthRun.lean:206) $m(1+r)\le1$ is equivalent to $r\le m^{-1}-1$. For example $r=1/16$ is allowed when $m\le16/17$, but no positive uniform $r$ covers $m\uparrow1$.

**Final Gaussian estimate available with new constants.** Let $U_v$ be the scalar final Schur-complement operator of [UnitLattice.unconstrainedUnitOperator_lower](/home/scott/Balaban/Balaban/Green/UnitLattice.lean:517). That landed inequality itself needs only $v\ge0$, $a>0$ and gives

$$\langle u,U_vu\rangle\ge {a\over a+4d+v}\bigl(E(u)+v\|u\|_2^2\bigr).\tag{B.33}$$

For $1/2\le a\le2$ and $0\le v\le V$, the fraction is at least $\gamma_V=(1+8d+2V)^{-1}$: it is increasing in $a$, decreasing in $v$, and its value at $(a,v)=(1/2,V)$ is exactly $\gamma_V$. The longitudinal part of the full Hessian is $aI$ ([FinalHessian.finalHessian_eq_split](/home/scott/Balaban/Balaban/Green/FinalHessian.lean:191)); the elementary lattice bound $E(u)\le4d\|u\|_2^2$ and $\gamma_V(4d+V)\le1/2\le a$ cover it. The same orthogonal split as `finalHessian_form_ge` therefore yields

$$\langle u,D_vu\rangle\ge\gamma_V\langle u,(-\Delta+v)u\rangle\ge\gamma_V v\|u\|_2^2.\tag{B.34}$$

For the ideal $v=\nu L^2\in(7/8,L^2]$, take $V=L^2$ and the explicit gap $g_{d,L}=7/[8(1+8d+2L^2)]$. For a running $v_1$ satisfying (B.32), take $V=20L^2/19$ and the safe gap $g'_{d,L}=133/[160(1+8d+40L^2/19)]$. These are mathematical consequences of the landed lower estimate and the displayed Hessian split, **not landed replacement declarations**. The entry-decay bound [CoarseOperator.unconstrainedUnitOperator_decay](/home/scott/Balaban/Balaban/Green/CoarseOperator.lean:89) assumes $v\ge0$ but no upper mass bound, so its constant $2+4\,\mathrm{blockDecayConst}(d,L)$ can be kept. A new Combes–Thomas application can use $g'_{d,L}$ in place of `finalGap d L` and hence use the explicit rate

$$\mathrm{ctRate}\bigl(2+4\,\mathrm{blockDecayConst}(d,L),\ \mathrm{blockDecayRate}(d),\ g'_{d,L},\ \mathrm{ballConst}(d,\mathrm{blockDecayRate}(d)/4)\bigr).\tag{B.35}$$

In this limited coercivity sense, extra mass does help. It does **not** preserve the old comparison constant $(8d+3)^{-1}$ against $(-\Delta+v)$ for arbitrary $v\le L^2$: on a constant longitudinal mode the Hessian is $aI$, whereas the requested lower bound would be $v/(8d+3)$; for sufficiently large $L$ and $v=L^2$ this exceeds $a$. Nor does stronger coercivity fix the empty complex domain or the real upper-mass terms in the first step. The final Gaussian replacement must be propagated through the complex cut family, torus-close estimates, analytic chart, source derivatives and final gas.

### What a $k_f=1$ proof would have to add

1. A **physical bare-to-scale-one theorem** for the normalized hard-spin partition function at every $\nu\in(7/(8L^2),1]$. It must construct the full first-step density, with the opposite-hemisphere sectors, crossing bonds, nonzero source, Peierls reserve and connected local activities; identify the exact integral before and after blocking; and produce the $j=1$ observable terms with their support, decay, analytic and two-torus properties. P5's conditional H1–H5/H7 propagation and the abstract `StepData` record do not supply this base theorem.
2. A **massive step replacement** valid with $m_0\le L^2$, including a *nonempty* complex domain with changed radii, massive background and decoupled Green estimates, composition, mass response with uniform complex margin, fluctuation coefficients and renormalization, and a large-field operator bound. The $\beta\nu\gg1$ case needs a direct high-field witness or a new test estimate, because the early $\beta\nu=O(1)$ argument does not apply. Constants may depend on fixed $d,L,N$ but the physical estimates and source ball must be uniform for the whole stated $\nu$ interval. The new chart and its proof, not just changed numbers in (B.33), are essential.
3. A **last-integral theorem** at $k=1$ for $v_1$ in (B.32), with (B.34)–(B.35) substituted through every `Final*` consumer, the complete inherited density and heavy operator (P7 §4, equations (4.1), (4.9)–(4.17), as indexed in [the P7 source review](/home/scott/Balaban/review/papers/P7-large-field-renormalization.md:130)). It must verify the actual heavy-activity hypothesis of `FinalTailGas` / `gas_activity_bound`, establish the normalized nonzero analytic partition function, and produce $j=2$ coefficients with the stronger $L^{-2((d-2)/2+\delta)}$ bound and exact nonwinding two-torus agreement. The present `Final*` Gaussian, cut and gas lemmas are conditional pieces rather than this physical theorem.

**Verdict.** Choosing $k_f=1$ is a valid *logical option in the frozen statement*, and there is no counterexample to Root-F here. It is **not a viable proof using the landed P1–P7 step and final-integral interfaces for all $\nu\in(7/(8L^2),1]$**: $m_0>1$ makes the step's complex domain empty, $m_0=1$ loses the D2(b) mass margin, and $v_1>1$ lies outside the landed final Green class. The required replacement first step includes the unresolved heavy-sector localization. On a fixed lower subinterval $m_0\le1-\eta$, the numerical mass gates can be met for suitable $r$ and large $\beta$, but a physical bare step and final bridge still have to be proved. Confidence is high in the negative instantiation verdict and (B.32)–(B.35); feasibility of the new massive first-step construction is open.

**Audit record and refutation pass.** Read-only source snapshot: tracked worktree clean at Git commit `f8f2579b21891ecfabd3f15367fb146e8dd91ee9`; SHA256 anchors: Root-F `21833bea3211257ac51d0879ef9f692acb0021fb04e792375cf5257104380e40`, `ScaleUniform.lean` `fc4aa72184c294f9bee577ed4c055eaa52495581b5f65b6ecbd7e77c170029f9`, `Background/Data.lean` `9fd2ab665e228cc29f62835c6f53d3db7e297e70841295981e4659b3ab017a10`, `FinalMassGreen.lean` `b535747adc3d5b08bb4f8987e6991fe8e68958075ba972bb5d2669751ceaa52f`. Three plausible refutations were checked: (i) use the large-field zero-mass convention at conventional $k_0=0$—this does not change the complete small-field mass (`sfBgMassAt`) or prove its high-field perturbation; (ii) use stronger ellipticity to keep the old step constants—this contradicts the empty-domain lemma and the longitudinal-mode example; (iii) infer a coarse Green obstruction from the older $v\le2$ wrapper—this is refuted by the landed all-mass `coarseGreen_decay_of_nonneg`, as recorded in the corrected table row. No Lean file was edited or built; this is a source and mathematical audit, not a new Lean theorem.

## Round 5 (17 October 2026): can larger one-scale blocks cure the high-mass branch?

### Quantifiers and the proposed small parameter

Fix $0<c\le1$ and consider $c/L^2\le\nu\le1$, with $s=ML$ chosen after $\kappa,c_9$ and before $\beta$. The intended application has $c=1-\eta$. If $c\ge1/4$, every mass in this interval meets the numerical $k_f=0$ condition $L\sqrt\nu\ge1/2$ in [Root-F](/home/scott/Balaban/Balaban/Frozen/Roots/LogPartitionMultiscale.lean:40); if $c<1/4$, its bottom part cannot use $k_f=0$ regardless of $M$. The theorem below concerns the proposed *block-covariance tree mechanism*, not existence of some other one-scale expansion.

Let $Q,Q'$ be neighboring $s$-blocks in a torus of side at least $2s$, and let $G_\Lambda=(-\Delta_\Lambda+\nu)^{-1}$. The valid long-distance estimate (B.21) has rate $a_\nu\ge\sqrt c/(2\sqrt d L)$. It is tempting to substitute a block separation of order $s$ into it. A tiling has neighboring sites across every shared face, so that substitution is false for the off-diagonal *block* covariance.

**Theorem B.5 (no block-size gain for an adjacent covariance link).** For each pair of sites $x\in Q$, $y\in Q'$ sharing a nearest-neighbor bond,

$$G_\Lambda(x,y)\ge(2d+\nu)^{-2}\ge(2d+1)^{-2},\qquad
\sum_{x\in Q,y\in Q'}G_\Lambda(x,y)\ge\frac{s^{d-1}}{(2d+1)^2}.\tag{B.36}$$

The obstruction persists in a bounded two-block Gaussian test after its independent expectation is subtracted. Take one tangent coordinate $v$, let $C(t)$ retain its two within-block marginals and multiply its between-block covariance by $t$, as in (B.9), and put $F_Q(v)=e^{i\sqrt\nu v_x}$, $F_{Q'}(v)=e^{i\sqrt\nu v_y}$. Both factors have modulus one. Their connected two-vertex BKAR contribution is

$$\begin{aligned}
|\mathbb E_{C(1)}F_QF_{Q'}-\mathbb E_{C(0)}F_QF_{Q'}|
&=e^{-\nu[G_\Lambda(x,x)+G_\Lambda(y,y)]/2}
  (1-e^{-\nu G_\Lambda(x,y)})\\
&\ge\frac{e^{-1}\nu}{2(2d+1)^2}
\ge\frac{e^{-1}c}{2L^2(2d+1)^2}.\tag{B.37}
\end{aligned}$$

The last number is independent of $s$; therefore no estimate $O(e^{-b s/L})$, with $b>0$ independent of $s$, holds for general bounded two-block factors. *Proof.* The nonnegative Neumann walk series $G_\Lambda=(2d+\nu)^{-1}\sum_{n\ge0}(A_\Lambda/(2d+\nu))^n$ gives the one-step lower bound; summing the $s^{d-1}$ face bonds gives (B.36). Gaussian characteristic functions give the equality in (B.37). The spectral bound $G_\Lambda\le\nu^{-1}I$ implies $\nu G_\Lambda(x,x),\nu G_\Lambda(y,y)\le1$ and $0\le\nu G_\Lambda(x,y)\le1$ by Cauchy–Schwarz. Apply $1-e^{-u}\ge u/2$ for $0\le u\le1$ and (B.36). $\square$

This test is diagnostic, not the physical hard-spin factor: physical good-sector factors become close to one as $\beta\to\infty$. It proves that **increasing $s$ alone supplies no small factor for every new block of a covariance tree**. A tree can traverse arbitrarily many neighboring blocks using these face links. The number of near-face pairs grows as $s^{d-1}$. One can separate *block interiors* by leaving corridors, but those corridors contain the original strong bonds and hard-spin factors and require their own linked expansion. Any per-block smallness must instead come from centered good-sector perturbations and Peierls-charged bad sectors, after their complete integrands have been linked.

### What the large block and Peierls estimates *do* give

For a link between non-neighboring blocks at site separation $D(Q,Q')$, (B.21) gives the legitimate estimate

$$\sum_{x\in Q,y\in Q'}G_\Lambda(x,y)
\le\frac{2s^{2d}}{\nu}e^{-\sqrt c\,D(Q,Q')/(2\sqrt d L)}.\tag{B.38}$$

Thus links spanning $R$ block steps have exponential length reserve once $s\sqrt c/(2\sqrt dL)>\kappa$, up to the displayed polynomial prefactor and the $O(d)$ boundary correction in $D\ge s(R-d)$. It says nothing small about adjacent links. The exact positive walk decomposition (B.22)–(B.27) offers a torus-coherent alternative at the *covariance-atom* level: with $q_c=2d/(2d+c/L^2)$, its support-weight condition at rate $\lambda$ is

$$q_c^2e^{2\lambda3^d/s}<1
\quad\Longleftrightarrow\quad
s>\frac{\lambda3^d}{\log(1+c/(2dL^2))}.\tag{B.39}$$

This particular sufficient condition requires $s>2d\lambda3^dL^2/c$, since $\log(1+t)\le t$. It is stronger than merely taking $s$ of order $L/\sqrt c$; the loss comes from charging every step of an unreduced random walk rather than using its sharp massive displacement decay. The frozen quantifier order permits such a large $M$, and then $\beta_0$ can depend on it. Equation (B.39) controls covariance walks, not derivatives of the physical two-sheet integral.

There is a genuine per-*selected-witness* block reserve. Let $m=N-1$, $C_{m,d}$ be the constant of (B.15), and $A_\beta=C_{m,d}^{2/3}\beta^{m/3}2^{m/6}$. If $k$ distinct blocks each contain a selected opposite-hemisphere spin, summing (B.15) over at most $s^d$ possible witness sites in each block yields

$$\sum_{\substack{x_Q\in Q\\Q\text{ among }k\text{ blocks}}}
\mathbb E\left[\prod_Q J_{x_Q}
e^{-\beta\nu(1+\sqrt{1-|v_{x_Q}|^2/\beta})^2/2}\right]
\le\left[s^dA_\beta e^{-\beta c/(2L^2)}\right]^k.\tag{B.40}$$

For any prescribed $p,h>0$, this is at most $e^{-p-hk}$ for $k\ge1$ when

$$\frac{\beta c}{2L^2}\ge p+h+d\log s+\frac m3\log\beta+\frac23\log C_{m,d}+\frac m6\log2.\tag{B.41}$$

The condition is feasible uniformly in $\nu\in[c/L^2,1]$ after $s$ is fixed. For plus-sheet failures of the shrinking good cutoff, (B.16) similarly gives $[s^d e^{-H_\beta}]^k\le e^{-p-hk}$ when $H_\beta\ge p+h+d\log s$; $H_\beta\to\infty$ at fixed $c,L,s$. These estimates may supply the size of the *Peierls reserve* required by [gas_activity_bound](/home/scott/Balaban/Balaban/Polymer/GasBound.lean:445), but (B.40) is only an integral of marked Jacobians and field factors, not its `hτ` bound for a completed activity. In particular, every unmarked Jacobian is $\ge1$ and cannot be dropped when estimating that activity from above; crossing bonds and tree derivative insertions remain.

On a controlled all-plus region one does obtain a second candidate small parameter. Put $p_\beta=A L\log(\beta a)/\sqrt c$ and assume $p_\beta^2/\beta\le1/4$. Equation (B.29) bounds the complete internal normal perturbation of an $s$-block by

$$|F_Q^+-1|\le
\exp\!\left\{\frac{s^d}{\beta}\left[p_\beta^2+(1/2+2d)p_\beta^4\right]\right\}-1,\qquad
|e^{-\beta V_{QQ'}}-1|\le\frac{2s^{d-1}p_\beta^4}{\beta}\tag{B.42}$$

for a shared face. Both tend to zero at fixed $s,L,c$ as $\beta\to\infty$. Thus (B.36) does **not** disprove a low-temperature cluster expansion: a centered tree estimate could charge each good block by (B.42) and each bad block by (B.40). Equation (B.30) proves that cancellation for an auxiliary product of block-local perturbations without crossing interactions. The physical cutoff $\mathbf1_{\{|v_x|\le p_\beta\}}$ depends on the full, nonlocal Gaussian field, and the complete two-sheet integral also contains crossing normal factors. Neither (B.30) nor (B.42) proves the required bound for its arbitrary-degree trees.

### Exact locality and the chart singularity remain separate tasks

Changing $s$ does not change the raw torus covariance. The strictly positive difference (B.19) between $G_\ell(0,0)$ and $G_{2\ell}(0,0)$ persists for every finite $\ell$ divisible by $s$, however small its numerical size becomes. Therefore the unlocalized singleton $f_Q$ in (B.12c) is not automatically identical on two tori. Exact quarter-box agreement needs termwise lift of **every** contributing path and assignment of winding paths to large supports. The full-path walk atoms of (B.22)–(B.27) have this property and connected footprints, but a finite-range truncation retains the strictly nonlocal residual (B.28); an infinite expansion of the nonlinear hard-spin factors in those atoms has not been bounded. The support-size bound, counting of decorations, and exact `DepOn` hypotheses of [gasOp_pe](/home/scott/Balaban/Balaban/Polymer/GasOperator.lean:336) are statements about the *completed factors*, not just their covariance entries.

The chart issue cannot be handled by a standard Cauchy–Schwarz estimate on tree factors. Equation (B.31) says $\mathbb E J_x^2=\infty$ at every $\beta$, and the real normal factors are positive at the chart boundary. A valid finite-volume procedure is to differentiate the **Gaussian density** as in (B.14), leaving exactly one copy of $J_x$ per site, and use the finite $L^{3/2}$ moment (B.17) on selected sites. At tree order $r$, however, the differentiated density contains polynomials of degree up to $2r$, traces and products of inverse covariances; taking absolute values before the vacuum cancellation loses the good-block factor. Multiplying separately bounded edge insertions can also put $J_x$ to power two or higher and is invalid. The missing analytic estimate must jointly control these density polynomials with *all* unmarked Jacobians, preserve the centered cancellation with crossing factors, and distribute one Peierls charge per bad block, uniformly in $r$, volume, $\nu$, and $\beta\ge\beta_0$ for each chosen $s$, with its $s$-dependence explicit. No estimate in (B.11), (B.15), (B.21), (B.27), or the landed gas theorems supplies it.

Concretely, the scalar BKAR gas (B.12b) would need a torus-coherent refinement $R_{S,\xi}^{\rm phys}(g)$, with connected charged support $X(S,\xi)$, satisfying a uniform bound strong enough to imply, for a fixed block $Q_0$,

$$\sup_{\Lambda,\nu,g}\ \sum_{(S,\xi):Q_0\in X(S,\xi)}
e^{(h+\kappa)|X(S,\xi)|}
|R_{S,\xi}^{\rm phys}(g)|\le\varepsilon_\beta,
\qquad \varepsilon_\beta\longrightarrow0,\tag{B.43}$$

where $\|g\|_1\le1/2$ and the supremum covers $c/L^2\le\nu\le1$. The geometry and entropy assumptions `hzd`, `hG3`, `hcount`, and the per-heavy bound `hτ : |τ_z|\le e^{-p-h|z_s|}` at [GasBound.lean:445](/home/scott/Balaban/Balaban/Polymer/GasBound.lean:445) must then be verified for this refinement; the pointwise, bounded, measurable finite-support factors and exact `gasXiOp` identity are additional obligations if one invokes `gasOp_pe` instead. Equation (B.43) is a **missing target estimate**, not an established lemma. It would also have to carry source analyticity and exact nonwinding lift to yield the frozen $T_1$ through the radial derivative construction described after (B.12c).

**Round-5 verdict and confidence.** A large freely chosen $s=ML$ makes long links and the selected-witness Peierls charge quantitatively manageable, and $\beta$ can be made large enough to control the pointwise good-sector perturbations. It does **not** make the covariance coupling of neighboring blocks exponentially small in $s/L$: (B.36)–(B.37) are a rigorous counterexample to that proposed per-block mechanism. Exact two-torus agreement and the complete hard-chart tree norm remain unproved; enlarging $s$ does not remove either issue. This is a precise obstruction to the suggested shortcut, **not** a counterexample to the frozen $k_f=0$ clause and not a proof that a more carefully centered high-field expansion is impossible. Confidence is high in (B.36)–(B.41) and in the distinction between covariance-atom control and full-activity control; (B.43) is explicitly conditional.
