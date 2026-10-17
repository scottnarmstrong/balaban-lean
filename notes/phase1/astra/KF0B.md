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
