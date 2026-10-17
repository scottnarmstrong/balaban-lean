# The first large-field step for hard O(N) spins

17 October 2026. This note addresses blocker 1, item 17(a),(c), using Plan B's first-step convention. **Verdict:** the test-free bare-density identity, the first decomposition, the real witness gains, and the numerical reserve are valid. They do **not** establish P5 (1.31) for the physical first-component operator: the required exact localized first integral and its operator majorant have not been constructed. Below is a counterexample to treating the current abstract Lean input as that physical construction, followed by the strongest unconditional first-sector estimate and the exact conditional implication to (1.31). The separate $k_f=0$ last integral is not settled here.

## 1. Sources and conventions

P5 is Bałaban, *A low temperature expansion for classical N-vector models. III. A complete inductive description, fluctuation integrals*, **Commun. Math. Phys. 196** (1998), 485–521, [DOI](https://doi.org/10.1007/s002200050433). The relevant places are the first-step description on p. 487; (H.1), (1.1) on p. 488; (1.18)–(1.20) on pp. 492–493; (H.5), (1.21)–(1.31) on pp. 493–496; (2.1)–(2.16) on pp. 501–504; and (2.42)–(2.47) on pp. 511–512. P6 is Bałaban, *Renormalization and localization expansions. II. Expectation values of the “fluctuation” measures*, **Commun. Math. Phys. 198** (1998), 1–45: §3, in particular (3.2) and (3.4)–(3.9), pp. 15–19. P7 is Bałaban, *The large field renormalization operation for classical N-vector models*, **Commun. Math. Phys. 198** (1998), 493–534, §4 beginning on p. 529. The pattern comparison is Bałaban, *Convergent renormalization expansions for lattice gauge theories*, **Commun. Math. Phys. 119** (1988), 243–285, [DOI](https://doi.org/10.1007/BF01217741), §1, pp. 246–248. The local PDF text layer of that Yang–Mills paper garbles several symbols in (1.2)–(1.11); the prose and the existence/order of its decompositions are legible. None of the O(N) formulas below is inferred from a garbled Yang–Mills display.

The model is a finite periodic fine lattice $\Lambda$, $d\ge3$, $N\ge2$, integer block sizes $L,M\ge1$, unit spins $\phi_x,h\in S^{N-1}$, $\beta>0$, $0<\nu\le1$, and

$$H_\Lambda(\phi)=\frac12\sum_{(x,x+e_\mu)}|\phi_{x+e_\mu}-\phi_x|^2+\frac\nu2\sum_x|\phi_x-h|^2,\qquad \rho_0(\phi;g)=e^{-\beta H_\Lambda(\phi)+\sum_xg_x\cdot\phi_x}.\tag{1}$$

Each positively oriented nearest-neighbour bond occurs once. The geometric sphere measure has mass $s_N=Nv_N$ per site; $v_N$ is the volume of the unit ball of $\mathbb R^N$. For the probability estimates below we use $d\widehat\sigma=s_N^{-1}d\sigma$. Replacing it by $d\sigma$ multiplies an integral over $D$ spins by exactly $s_N^{|D|}$; this factor belongs in the first-step vacuum/boundary normalization. It cannot silently be discarded from a P5 operator estimate. The source convention is $\sum_{x,i}|g_i(x)|<1$, so $|e^{\langle g,\phi\rangle}|\le e^{\|g\|_1}<e$ on real spins.

Use P5's $\delta_0=p_0(\beta)/\sqrt{a\beta}$, $p_0(\beta)=A_0\lambda^{p_0}$, $\lambda=\log(a\beta)$, with $a,A_0>0$. The exponent $p_0$ is an integer; $p_2(\beta_1)=A_2(\log\beta_1)^{p_2}$ and $H_1=H_0\log\beta_1$. In this note $p_0$ without an argument is the exponent, and $p_0(\beta)$ is the threshold amplitude. We require $\lambda\ge1$ and $\delta_0<2$ when making the counterexample. The campaign's stronger choice, $p_2=2d+3$ and $p_0$ the least even integer at least $d^2+7d+2$, satisfies every power inequality used below; P5 p. 495 permits $p_2=p_0-2d-2$ in another choice of constants.

## 2. Exact base representation and first-step records

The bare density is the **single test-free term** (1). In particular, it is not asserted to belong to P5's space $\mathcal R_0$ with its literal (H.1) characteristic function. The naive identity $\rho_0=\chi_0\rho_0$ is false: take neighbouring spins $h$ and $-h$ on a bond. Its length is $2>\delta_0$, so the required small-gradient test fails. This is the precise exception to (H.1) at the initial index. P5 p. 487 explicitly starts by applying $T^{(0)}$ and then splitting its integral into small and large field sectors; the Yang–Mills §1 uses the analogous order.

Insert the **normalized** block-spin Gaussian $T^{(0)}$ first. For an $L$-block $B_1(y)$ write $(Q\phi)_y=L^{-d}\sum_{x\in B_1(y)}\phi_x$, $\theta_y=z_1\psi_1(y)$, and $\gamma_G=\beta aL^{d-2}$. The density in $u_y=\theta_y-(Q\phi)_y$ is

$$t_0(u_y)=\left(\frac{\gamma_G}{2\pi}\right)^{N/2}e^{-\gamma_G|u_y|^2/2},\qquad \int_{\mathbb R^N}t_0(u_y)\,du_y=1.\tag{2}$$

In the $\psi_1$ variable the density includes the Jacobian $z_1^N$ (assuming $z_1>0$). This normalization gives $\int T^{(0)}\rho_0=\int\rho_0$ before any region choice.

Let $c$ range over P5's disjoint $\pi_1$ cubes, of side $M$ in scale-one blocks, hence side $LM$ fine sites. In the products below, $x\in c$ means that the fine site maps to $c$. Define the binary tests, for the real pair $(\phi,\theta)$,

$$A_c=\prod_{y\in c}\mathbf1\{|\theta_y-(Q\phi)_y|<2\delta_0\},\quad B_c=\prod_{b:\,b\text{ meets }c}\mathbf1\{|\partial\phi(b)|<\delta_0\}\prod_{x\in c}\mathbf1\{\nu|\phi_x-h|^2<\delta_0^2\}^{[k_0=0]},\quad C_c=A_cB_c.\tag{3}$$

The direction/site factor is absent in regime A ($k_0\ge1$) and present in regime B ($k_0=0$), exactly as in `chiBondB`; a bond meeting two cubes is tested twice but appears only once in (1). Formula (3) is the landed `chiPrimeZero` (`ChiBlockProp`, `ChiBondProp`, `ChiSiteProp`) in `LargeField/Base/BaseRecord.lean`. No factor called the *old* $\chi_0$ is inserted. This matters algebraically: putting a separate $B_c$ in front of $A_c(1-B_c)$ would make the bond-witness sector zero.

The first partition is the literal pointwise identity

$$1=\prod_{c\in\pi_1}[C_c+(1-C_c)]=\sum_{P\subset\pi_1}\prod_{c\in P}(1-C_c)\prod_{c\notin P}C_c.\tag{4}$$

It is `chiPrimeZero_decomposition` in `BaseRecord.lean` and specializes P5 (2.5)–(2.6), pp. 502–503, with $Z_0=U_0=U'_0=\varnothing$ and $\Omega'_1=\mathbb T_1$. Given $P=\mathsf P_1$, form $\Omega_1=\operatorname{Op}_1(P^{\sim3};\mathbb T_1)$. On $\Omega_1^{\sim3}$ insert the second partition $1=\prod_c[\chi'_1(c)+(1-\chi'_1(c))]$, and call the failed-cube set $Q=\mathsf Q_1$ (P5 (2.13)–(2.14), pp. 503–504). On $\Omega_1$ insert $1=\prod_c[\chi^{(0)}(c)+(1-\chi^{(0)}(c))]$, with $\chi^{(0)}(c)=\mathbf1\{\sup_{x\in c}|\psi'_0(x)|<p_1(\beta)\}$, and call the failed set $R=\mathsf R_1$ (P5 (2.42)–(2.43), p. 511). After the first integral P6 (3.2), pp. 15–16, inserts the $\chi_1$ partition and calls its failures $S=\mathsf S_1$. Each is a binary partition; equality of the complete density is the product of these identities **only when all factors, including the first integral, are retained**.

Set $r=\lfloor R_0\rfloor$ in the operative geometry. The landed `BaseRecord` has fields `.P`, `.Q`, `.R`, `.S` and defines $\Omega''_1=\operatorname{Op}_1(Q^{\sim(r+2)}\cup R^{\sim(2r+4)};\Omega_1)$ (`BaseRecord.Omega`, `.FDD`, `.OmegaDD`). Its `toStep` has old region empty; `RegionHistory.baseRecord`, `step_zero_Z`, `step_zero_OmegaPrime`, and `base_geometry` verify this. The new seeds are $\mathcal N_1=P\cup Q\cup R\cup S$ (`Region.newCubes`); the preliminary bad region $Z_1^{\rm pre}$ is the hull built from the complements of $\Omega''_1$ and the $S$ failures (`Region.FZ`, `Region.Z0`, `Region.Zpre`). Every component contains a new seed (`RegionHistory.base_newCube`), has no old part (`base_parts_empty`), and in regime A is not ripe (`base_noRipe`). For an admissible history `base_rem_one` proves no component is removed at scale one in either regime, and `base_Z_one` identifies the final $Z_1$ with $Z_1^{\rm pre}$. The first record is therefore a genuinely new component, not an inherited component with an unprovided old operator.

For a component $X$ of $Z_1^{\rm pre}$, write $\widehat X$ for its fine-site lift, and use fine-site lifts also for $\Omega_1,\Omega''_1$. Split its fine sites into $D_{\rm out}=\widehat X\cap\widehat\Omega_1^c$, $D_-=\widehat X\cap(\widehat\Omega_1\setminus\widehat\Omega''_1)$, and $D_+=\widehat X\cap\widehat\Omega''_1$. The raw sphere spins on $D_{\rm out}$ are retained as variables of the first component operator. The chart/fluctuation variables on $D_-$ are also retained; those on $D_+$ enter the first small-field expectation. Bonds crossing these sets retain their Boltzmann factors, with the actual spin on a retained endpoint. Thus “kept raw variables” means **not integrated in the first small-field expectation**; P5's later $T_1(X)$ integrates its retained inputs in the operator bound (1.31). This is the O(N) reading of P5 pp. 487, 493–494 and P6 (3.2).

One must split an old good factor $B_c=B_c^-B_c^+$ by whether its spin arguments meet $D_+$; a crossing-bond test belongs to $B_c^+$ when its integrated endpoint is in $D_+$. The bond energy itself is never removed. `baseCutoffTransfer` proves deletion of certain $B_c^+$ factors **under** `BaseCutoffMargins`; `baseMargin_counterexample` shows that the record's strict tests alone do not imply those margins. The normalization of the chart, its determinant and Jacobian, and the $D_+$ expectation are part of the physical first-step input, not consequences of (4).

## 3. An unconditional real first-sector theorem

This theorem isolates the reserve supplied by the level-zero threshold. It estimates the entire *first $P$ sector* after integrating both the coarse Gaussian and all sphere spins against product probability measure. It is deliberately not identified with P5's localized component operator, which also carries $Q,R,S$, backgrounds, chart factors, and a boundary exponent.

**Theorem 1 (bare $P$-sector bound).** Fix $P\subset\pi_1$ with $n=|P|\ge1$ and define $W_P(\phi,\theta)=\prod_{c\in P}(1-C_c)\prod_{c\notin P}C_c$. With $\|g\|_1<1$, put

$$q_A=M^d2^{N/2}e^{-L^{d-2}p_0(\beta)^2},\qquad q_B=(2d+1)(LM)^d e^{-p_0(\beta)^2/(4a)}.\tag{5}$$

Then, for the product Gaussian (2) and normalized sphere measure,

$$\left|\int W_P(\phi,\theta)e^{-\beta H_\Lambda(\phi)+\langle g,\phi\rangle}\,d\widehat\sigma_\Lambda(\phi)\prod_y t_0(\theta_y-(Q\phi)_y)d\theta_y\right|\le e^{\|g\|_1}(q_A+q_B)^n.\tag{6}$$

The same holds with any further **real** indicator factors bounded by one. It holds for either regime of (3). If the geometric surface measure is used, multiply the right side by $s_N^{|\Lambda|}$; a component normalization must allocate this volume factor locally.

*Proof, including the constants.* For one $N$-dimensional Gaussian $u$ of precision $\gamma_G$, exponential Markov with parameter $\gamma_G/4$ gives

$$\Pr(|u|\ge2\delta_0)\le e^{-\gamma_G\delta_0^2}\mathbb E e^{\gamma_G|u|^2/4}=2^{N/2}e^{-L^{d-2}p_0(\beta)^2},\tag{7}$$

because $\gamma_G\delta_0^2=\beta aL^{d-2}p_0(\beta)^2/(a\beta)=L^{d-2}p_0(\beta)^2$. If $A_c=0$, at least one of the $M^d$ distinct coarse blocks in $c$ violates its test. Therefore $\Pr(A_c=0\mid\phi)\le q_A$. For distinct cubes choose one witness block in each; all chosen Gaussian variables are distinct and independent. The union bound hence gives $q_A^{n_A}$ for any prescribed set of $n_A$ cubes whose $A$ tests fail, uniformly in $\phi$.

If $B_c=0$, choose a failed bond meeting $c$, or a failed site in $c$ in regime B. A cube contains $(LM)^d$ fine sites; at most $2d(LM)^d$ positively oriented bonds meet it (each site has at most $2d$ incident oriented bonds). There are at most $(LM)^d$ possible site witnesses. Thus there are at most $W_B=(2d+1)(LM)^d$ choices per cube. For a chosen failed bond, its term in $\beta H$ is $\beta|\partial\phi(b)|^2/2\ge\beta\delta_0^2/2$. For a chosen failed site it is $\beta\nu|\phi_x-h|^2/2\ge\beta\delta_0^2/2$. One physical bond can witness at most two $\pi_1$ cubes, and one site at most one. If $n_B$ cubes are assigned $B$ failures and one witness is chosen in each, summing the selected energy terms with multiplicity at most two yields

$$\beta H_\Lambda(\phi)\ge\frac12\sum_{\text{distinct selected energy terms}}\beta\delta_0^2\ge\frac{n_B\beta\delta_0^2}{4}=\frac{n_Bp_0(\beta)^2}{4a}.\tag{8}$$

All other energy terms are nonnegative. Product sphere probability has mass one and $|e^{\langle g,\phi\rangle}|\le e^{\|g\|_1}$. Thus the integral for one prescribed $A/B$ assignment is at most $e^{\|g\|_1}q_A^{n_A}q_B^{n_B}$. Finally $1-A_cB_c=(1-A_c)+A_c(1-B_c)\le(1-A_c)+(1-B_c)$; expanding over $P$ and dropping the good factors (at most one) gives

$$e^{\|g\|_1}\sum_{J\subset P}q_A^{|J|}q_B^{n-|J|}=e^{\|g\|_1}(q_A+q_B)^n.\tag{9}$$

This proves (6). The use of product probability and integration of **all** coarse variables is essential to (7); holding arbitrary coarse output variables fixed does not give $q_A$. $\square$

**Corollary 2 (explicit logarithmic reserve for this sector).** Suppose $p_0(\beta)=A_0\lambda^{p_0}$ and $p_0\ge d+1$, $2p_0>p_2$. Let a set $Z$ of first-scale cubes be covered by radius-$5r_0$ sup-norm balls about the $n$ cubes of $P$, where $r_0=\lceil R_{\rm base}\lambda^2\rceil$, $R_{\rm base}\ge0$. Put

$$B=10R_{\rm base}+11,\quad C=M^d2^{N/2}+(2d+1)(LM)^d,\quad c=\min\{L^{d-2},(4a)^{-1}\}.\tag{10}$$

Assume $\beta_1\ge1$, $\log\beta_1\le\lambda+C_\beta$ for a fixed $C_\beta\ge0$, and $\lambda\ge1$. A sufficient **fully numerical** threshold for any $\ell\in\{1,2\}$ is

$$\begin{split}
\lambda^{2p_0}&\ge\frac{4(1+\log C)}{cA_0^2},\\
\lambda^{2p_0-p_2}&\ge\frac{4\ell A_2(1+C_\beta)^{p_2}}{cA_0^2},\\
\lambda^{2p_0-2d-1}&\ge\frac{4H_0(1+C_\beta)B^d}{cA_0^2}.
\end{split}\tag{11}$$

Equivalently, let $\Lambda_*$ be the maximum of $1$ and the positive real powers of the three right sides of (11), with exponents $1/(2p_0)$, $1/(2p_0-p_2)$, and $1/(2p_0-2d-1)$ respectively. Then $\beta\ge a^{-1}e^{\Lambda_*}$ suffices, together with $\beta_1\ge1$ and the stated scale comparison. All denominators are positive by the theorem's exponent assumptions. This makes the threshold's dependence on $d,L,M,N,a,A_0,A_2,H_0,R_{\rm base},C_\beta$ explicit.

Under (11), the right side of (6) is at most $\exp[-\ell p_2(\beta_1)-H_1|Z|]$. Here $|Z|$ is the number of first-scale cubes; if P5's size $|Z|_1=M^d|Z|$ is used, replace $H_0$ in the third line of (11) by $M^dH_0$.

*Proof.* A sup-norm ball of radius $5r_0$ on a cube torus has at most $(10r_0+1)^d$ cubes, even if it wraps. Since $r_0\le R_{\rm base}\lambda^2+1$ and $\lambda\ge1$,

$$|Z|\le n(10r_0+1)^d\le nB^d\lambda^{2d}.\tag{12}$$

From (5), $q_A+q_B\le C e^{-cA_0^2\lambda^{2p_0}}$. Since $n\ge1$ and $\|g\|_1<1$, (6) is at most

$$\exp\{-n[cA_0^2\lambda^{2p_0}-\log C-1]\}.\tag{13}$$

The first inequality of (11) pays $1+\log C$ with at most a quarter of the charge. Because $\lambda+C_\beta\le(1+C_\beta)\lambda$, the second pays $\ell A_2(\log\beta_1)^{p_2}$ with at most a quarter. Equations (12) and the third inequality pay $H_0\log\beta_1|Z|$ with at most a quarter. The remaining quarter is nonnegative; hence (13) is no larger than the asserted factor. Every constant in (10)–(11) is independent of torus volume. $\square$

For P5's full base geometry the seed set is $P\cup Q\cup R\cup S$, not just $P$. `RegionHistory.baseRecord_seeds_new` gives a radius-$5r_0$ cover of the **raw** bad set $Z_1^{(0)}$ by all new seeds. Hull closure can add cubes beyond that radius; its box-cover cost is treated in Lemma 3 below. Corollary 2 does not charge a component with $P=\varnothing$. The $Q$ and $S$ gains require the energy/background estimate of P6 (3.7)–(3.8), and the $R$ gain requires its fluctuation Gaussian. This is why the corollary cannot be renamed P5 (1.31).

## 4. The exact conditional proof of P5 (1.31)

Here is the missing statement in P5's own operator variables. For every admissible localized first record $\mathfrak a$ and nonempty component $X\subset Z_1^{\rm pre}$, let $T_1(X,\mathfrak a)$ be the **physical** component kernel obtained from the exact transform of (1), with the factors of §2, and let $\chi_{\mathfrak a}$ restrict the retained variables as in P5 (1.24)–(1.25), p. 494. The desired one-component bound is

$$\sum_{\mathfrak a|X}\int d\psi_1|_X\,|T_1(X,\mathfrak a|X)F_{\mathfrak a}|\le e^{-\ell A_2(\log\beta_1)^{p_2}-H_0(\log\beta_1)|X|_1}\sup_{\mathfrak a,\text{retained variables}}\chi_{\mathfrak a}|F_{\mathfrak a}|,\quad \ell=1\text{ or }2.\tag{14}$$

The scale-one size is $|X|_1=M^d\#X$ in the landed budget convention. This is P5 (1.31), p. 495, at the first component. It is **not** an estimate of $\rho_0$ or of the scalar integral (6).

There is a complete deduction of (14) from three precise hypotheses, matching P5 (1.26)–(1.30):

1. **Physical identity and step majorant.** The actual first transform equals the sum over the records of §2, and each physical $T_1(X,\mathfrak a)$ has P5's factorization/support and an absolute kernel majorant. Its new-variable integral, including $e^{\operatorname{Re}b_0}$, is at most $e^{-\kappa_1(X,\mathfrak a)}\sup\chi_{\mathfrak a}|F_{\mathfrak a}|$. At step zero this is `BaseStepData.S2` with a **physical** `BaseSmallFieldInput`; the exact equality with the transformed (1) is an additional required premise. The $Q,R,S$ gains and the shell/Jacobian/boundary losses must all be in this estimate.
2. **Record counting.** Positive combinatorial factors $C_1(\mathfrak a|X)$ obey $\sum_{\mathfrak a|X}C_1(\mathfrak a|X)^{-1}\le1$, P5 (1.27), p. 494. The first-record cost is $\log C_1=(5/4)L^d\#X$, exactly `RegionHistory.base_exponents`. Multiplying each majorant by $C_1^{-1}C_1$ gives P5 (1.29) without an uncontrolled number of records.
3. **Numerical budget.** For every record, $\kappa_1-\log C_1-H_1|X|_1\ge\ell A_2(\log\beta_1)^{p_2}$. The following lemma verifies this implication of the high threshold under explicit scale comparisons; it is the only part of (14) that follows from choosing $p_0$ large.

**Lemma 3 (first-history budget arithmetic).** Let $n_X=|X\cap\mathcal N_1|_\#\ge1$ and $v_X=\#X$. Assume the landed `BudgetSetup`/`Setting.Ok` conditions of `RegionHistory.base_budget`, with $\lambda_0\ge1$, $\lambda_1\le2\lambda_0$, $r_j=\lceil R_{\rm base}\lambda_j^2\rceil$, and $\log\beta_1\le\lambda_0+C_\beta$, $C_\beta\ge0$. Put $c_0=S.c0$ (the fixed spine/critical-side integer) and

$$B_{\rm hull}=\max\{10R_{\rm base}+11,\;8c_0R_{\rm base}+2c_0+10\}.\tag{15a}$$

Assume $A_3,c_v,A_2>0$, $2p_0>p_2$, $2p_0>2d+1$, and

$$\lambda_0^{2p_0-2d-1}\ge\frac{8c_vB_{\rm hull}^d}{A_3},\qquad
\lambda_0^{2p_0-p_2}\ge\frac{4\ell A_2(1+C_\beta)^{p_2}}{A_3}.\tag{15}$$

Then $G_1^{\rm pre}(X)=\kappa_1^{\rm pre}(X)-\log C_1^{\rm pre}(X)-H_1|X|_1\ge\ell p_2(\beta_1)$.

*Proof.* `RegionHistory.base_exponents` gives **exactly**

$$\kappa_1^{\rm pre}=A_3(\log\beta_0)^{2p_0}n_X-(c_1\log\beta_0+c_2)M^dv_X,\quad \log C_1^{\rm pre}=\tfrac54L^dv_X.\tag{16}$$

`RegionHistory.base_budget`, whose numerical premises are `BudgetSetup`, combines (16) with the $H_1M^dv_X$ charge and yields the explicit lower bound

$$G_1^{\rm pre}(X)\ge g_0n_X-c_v\lambda_1v_X,\qquad g_0=\tfrac12 A_3\lambda_0^{2p_0}.\tag{17}$$

We need a cover after the hull rule, since `baseRecord_seeds_new` only applies to $Z_1^{(0)}$. At hull round zero, every cube of $Z_1^{(0)}$ lies within $5r_0$ of a new seed in its own component, so each component is covered by one box of side $10r_0+1$ per seed. If $k_0=0$, $Z_1^{\rm pre}=Z_1^{(0)}$ and this is the final cover. If $k_0\ge1$, `Region.Zpre` applies `hullClosure` with critical side $\mathrm{crit}_1=2c_0r_1+10$. At each hull round, replace the boxes assigned to a hulled component by its single hull box. That hull box has side at most $\mathrm{crit}_1$ by the definition of a hull round. Every such component already contains an original seed (`RegionStep.seedsIn_card_pos` and the hull-round component lemma), hence at least one assigned box, so replacing its boxes by one cannot increase the total number. When components merge, join their box lists; their seed lists are disjoint. Induction over the finite hull rounds leaves every final component covered by at most its number $n_X$ of new-seed boxes. This is the *base* specialization of the box-cover reasoning in `History/StepCover.lean` and `History/FlowInv.lean`; it is not the false claim that every hull-added cube remains within $5r_0$ of a seed.

Now $r_0\le R_{\rm base}\lambda_0^2+1$, $r_1\le4R_{\rm base}\lambda_0^2+1$, and $\lambda_0\ge1$. Thus both the initial side $10r_0+1$ and the replacement side $2c_0r_1+10$ are at most $B_{\rm hull}\lambda_0^2$. A box of side $s$ has at most $s^d$ torus cubes, even if it wraps. Hence

$$v_X\le n_XB_{\rm hull}^d\lambda_0^{2d}.\tag{18}$$

Insert (18) and $\lambda_1\le2\lambda_0$ in (17):

$$G_1^{\rm pre}(X)\ge\left(\tfrac12A_3\lambda_0^{2p_0}-2c_vB_{\rm hull}^d\lambda_0^{2d+1}\right)n_X\ge\tfrac14A_3\lambda_0^{2p_0}n_X.\tag{19}$$

The second inequality is the first condition in (15). Since $n_X\ge1$, $\log\beta_1\le(1+C_\beta)\lambda_0$, and the second condition in (15) holds, (19) is at least $\ell A_2(\log\beta_1)^{p_2}$. This is the stated inequality. There is no volume-dependent constant. $\square$

*Conditional derivation of (14).* Hypothesis 1 bounds each absolute integral by $e^{-\kappa_1}\sup\chi|F|$. By Lemma 3, $C_1e^{-\kappa_1}\le e^{-\ell p_2(\beta_1)-H_1|X|_1}$. Therefore

$$\begin{aligned}
\sum_{\mathfrak a|X}\int|T_1F_{\mathfrak a}|
&\le\sum_{\mathfrak a|X} C_1(\mathfrak a|X)^{-1}\bigl[C_1(\mathfrak a|X)e^{-\kappa_1(X,\mathfrak a)}\bigr]\sup\chi|F|\\
&\le e^{-\ell p_2(\beta_1)-H_1|X|_1}\sup\chi|F|\sum_{\mathfrak a|X}C_1(\mathfrak a|X)^{-1}\\
&\le e^{-\ell p_2(\beta_1)-H_1|X|_1}\sup\chi|F|.
\end{aligned}\tag{20}$$

This writes every inequality in the passage P5 (1.26) $\Rightarrow$ (1.31). It proves (14) **conditional on the physical operator majorant and counting**, and proves the numerical budget once `BudgetSetup` and the displayed scale comparisons are available. It does not upgrade the scalar sector theorem to an operator majorant. The $N$ dependence enters the latter through the Gaussian $2^{N/2}$ and sphere/chart volumes, hence through $C_b,c_1,c_2$ and the chosen $A_3,c_v$; (15) is uniform after these constants are fixed. The dependence on $L,M,a,R_{\rm base},c_0$ is explicit and unavoidable because the Gaussian precision, $\pi_1$ cubes, and hull use them. In the campaign $M$ also depends on the requested localization rate $\kappa$ (and its earlier constants); all these parameters must be fixed before the lower bound on $\beta$ is chosen.

### What a full physical majorant must pay

The landed `baseBlock_gain` proves the Gaussian factor $M^d2^{N/2}e^{-L^{d-2}p_0(\beta)^2}$ per block-type $P$ witness. `bond_gain_real` and `baseMainAction_bond_gain` give $e^{-p_0(\beta)^2/(8a)}$ when the actual retained bond has its full energy in `baseMainAction`; a bond used by two cubes spends two shares. `site_gain_real` and `baseMainAction_site_gain` give $e^{-p_0(\beta)^2/(9a)}$ in regime B under $\beta_0^{(1)}\ge\beta/2$ and $\mu\ge8\nu/9$. These are real inequalities with their hypotheses; they do not identify the physical kernel.

For the other first seeds, P6 (3.4), (3.7)–(3.8), pp. 16–18, gives the **raw per-cube** factors $e^{-8\gamma_0p_0(\beta_0)^2/[6^d(9K_1)^2]}$ for $Q$, $e^{-p_1(\beta_0)^2/4}$ for $R$, and $e^{-\gamma_0p_0(\beta_1)^2/[2\cdot6^dK_1^2]}$ for $S$; (3.4) also carries the displayed Gaussian counting costs. If half of the $Q,S$ exponents is spent elsewhere, their remaining coefficients are $4\gamma_0/[6^d(9K_1)^2]$ and $\gamma_0/[4\cdot6^dK_1^2]$ respectively. This allocation must be justified in the physical majorant. To obtain a uniform $A_3\lambda_0^{2p_0}$ per seed, the $R$ threshold must satisfy $p_1(\beta_0)\ge A_1\lambda_0^{p_0}$ and the $S$ threshold must satisfy $p_0(\beta_1)\ge A_0c_\lambda^{p_0}\lambda_0^{p_0}$ for some fixed $c_\lambda>0$. The bare assumption $p_1\le p_0$ about **exponents**, and the upper comparison $\lambda_1\le2\lambda_0$ in Lemma 3, do not imply these lower bounds. Subject to those comparisons and payment of all counting and volume losses, a possible gain coefficient is at most a fixed fraction of

$$\min\left\{A_0^2\min\left\{L^{d-2},\frac1{8a},\frac1{9a},\frac{8\gamma_0}{6^d(9K_1)^2},\frac{\gamma_0c_\lambda^{2p_0}}{2\cdot6^dK_1^2}\right\},\frac{A_1^2}{4}\right\}.\tag{21}$$

The witness choice count can be bounded by $(d+1)(2LM)^d$ per cube in the base construction; its logarithm and the $2^{N/2}$ factors must be taken from the witness gain. The residual sphere and chart factors cost at most $s_N$, $2$ and a variance-two Gaussian factor $2^{N/2}$ per retained fine site on the prescribed chart support. The boundary exponent must obey a source-independent $|b_0|\le C_{b,\mathrm{sf}}(\log\beta+1)|X|_1$; choosing $C_b\ge C_{b,\mathrm{sf}}+\max\{0,L^d\log(2^{N+1}s_N)\}$ absorbs these factors. These are the exact roles of `Prop279Phys.Csf`, `.b0_sf`, `.Cb_ge` in `LargeField/Base/Prop279.lean` and of $c_1,c_2$ in (16). The physical cutoff transfer, complex analytic continuation, localized covariance, nonzero first expectation and its determinant/vacuum allocation remain separate estimates.

## 5. Counterexamples and the Lean shape

There are two logically decisive counterexamples.

**(i) The bare H.1 counterexample.** The two neighbouring spins $h,-h$ violate a level-zero gradient test when $\delta_0<2$. Hence $\rho_0=\chi_0\rho_0$ cannot be the bare identity. Formula (4) is the nearest exact replacement, with all bad sectors retained. This does not contradict P5's positive-scale inductive statement: P5 p. 487 describes insertion of the tests *during* $T^{(0)}$.

**(ii) The abstract-input counterexample, already proved in Lean.** `zeroBaseSmallFieldInput` in `LargeField/Base/Prop279Counter.lean` sets every remainder kernel $\widetilde K_0^w$ to zero and every $b_0$ to zero while satisfying the fields of `BaseSmallFieldInput`. `zero_input_kernel_eq_zero` then makes `baseKernel_of_input` identically zero. The actual first Gaussian transform of the strictly positive bare weight is strictly positive (`positive_transform_pos`). Thus neither `baseSmallFieldInput_nonempty`, `baseStepData_of_input`, `prop279Input_nonempty`, nor `prop279_of_input` identifies a physical base kernel. An inequality for that zero kernel is vacuous. `baseMargin_counterexample` additionally shows that the strict record tests do not imply the margins required by `baseCutoffTransfer`. These are counterexamples to the proposed **deductions**, not to physical P5 (1.31).

The appropriate Lean statements, in dependency order, are:

| Lean statement | Exact hypotheses and conclusion | Current status |
|---|---|---|
| `chiPrimeZero_decomposition`, `baseF_decomposition` | Pointwise (4), then $1-AB=(1-A)+A(1-B)$ for the outside factors | Landed in `BaseRecord.lean`, `BaseWitness.lean` |
| `baseSector_P_integral_bound` (proposed) | Physical `rho_0`, normalized block kernel, product sphere probability, any fixed $P$: conclusion (6), with $q_A,q_B$ from (5) | Proof in §3; not a landed declaration |
| `baseSector_P_reserve` (proposed) | Previous bound, the radius cover, (10)–(11): $e^{-\ell p_2(\beta_1)-H_1|Z|_1}$ after using the $M^d$ version | Proof in Corollary 2; not a landed declaration |
| `baseHullCover` and `baseGpre_ge_p2` (proposed) | `RegionHistory.base_budget`, `base_newCube`, `baseRecord_seeds_new`, hull-round box replacement, the scale comparisons and (15): $G_1^{\rm pre}(X)\ge\ell A_2(\log\beta_1)^{p_2}$ | Mathematical proof in Lemma 3; the base box cover and arithmetic are not landed as one theorem |
| `physicalBaseKernel_eq_transform` (needed) | A **nonzero physical** `Prop279Phys`/`BaseSmallFieldInput` whose record sum is exactly the transform of (1), including cutoff transfer, chart measure and determinant | Open; `Prop279Conclusion` explicitly excludes this equality |
| `physicalBaseStep_S2` (needed) | `BaseStepData.S2` for that physical input, with `BaseW`/`baseF`, `GaussStepSpec` and $\kappa_1$ of (16) | Open; `Prop279Conclusion` explicitly excludes (S2) |
| `physicalBase_component_131` (conditional) | Previous two, record counting (1.27), Lemma 3: conclusion (14) for every nonempty component | Deduction (20); physical premises open |

The formal target uses `RegionHistory S n R k0 K`, `H.Comp 1`, `H.localHistory M K 1 X`, `BaseStepData K k0 geo cs N`, `BaseStepData.S2`, `GaussStepSpec`, `H.kappaPre P 0`, `H.logCPre 0`, `H.Gpre P κ logC 1 X`, `RegionHistory.base_budget`, `BaseRecord.toStep`, and `Prop279Phys`. The names `baseGpre_ge_p2` and `physicalBaseKernel_eq_transform` above are **proposed**, not citations to landed declarations. The latter must be stated against the actual first transform, not merely against a `Nonempty` input; `Prop279.lean` currently says that transform is not represented in its conclusion. `BaseS5` supplies the complex-parameter form in regime A only when its **physical** witness is proved; real bounds (6), (7), (8) do not prove it.

## 6. What the induction consumes, and the status of each input

P5 §1 needs, at scale one, an **exact** (H.1) sum over admissible $Z_1$; the small-field action/generating/remainder data on $Z_1^c$ ((H.2)–(H.4), pp. 488–492); the real positive, localizable component operator and its factorization (H.5), pp. 493–494; the retained-variable support (1.24)–(1.25); the component factor (1.31); and boundary terms (H.7). Formula (4) supplies only the first algebraic sector partition. `BaseRecord`, the region history and `baseF_decomposition` supply the record geometry and outside witness algebra. The physical first integral, its exact normalizers, small-field output, and the boundary terms still have to be proved. `Prop279Conclusion` explicitly leaves out the RG solution, (D7), (S2), and equality with $\rho_1$. Consequently the full (H.1) base output is not supplied yet.

P5 §2 applies $T^{(k)}$ to an **already valid** (H.1) density, then uses (2.6), (2.14), (2.43) and P6's later $S$ partition. At $k=0$ the two displayed *old* $\chi_k$ factors in P5 (2.15), (2.47) must be $1$, as §2 explains; they cannot be replaced by $B_c$. The generic scheme also needs the protected good domain, background, localized covariance, cutoff transfer and exact first fluctuation integral. The first three real $P$ witness gains are landed, and `baseCutoffTransfer` handles a stated margin premise, but the physical proof of those premises and the first localized expectation are not. So the common induction step can be **specified** from this base, but cannot yet be instantiated physically.

P5 §3 and P6 §2–§3 need the first integral's local action terms, vacuum constant, reduced-symmetry remainder at the next-scale half budget, the inside/crossing boundary split, $O(N)$ and Euclidean covariance, analytic/source locality, and the operator reserve that survives the record sum. `Prop279Input` packages cutoff, marked-remainder and physical-kernel hypotheses; `prop279_of_input` proves only its conditional conclusion. `RegionHistory.base_budget` and Lemma 3 provide the numerical reserve once `BaseStepData.S2` has been produced. The $Q,R,S$ factors are source estimates for that production, but a list of their rates is not a majorant for the actual first kernel. The source-strength distinction is concrete: `b0_bound_strictly_weaker` proves that `BaseSmallFieldInput.b0_bound` with $C_bB_0$ need not imply the $C_b$ bound used in the first witness accounting.

At scale one the combinatorial history has no old component (`base_parts_empty`). In regime A it also has no ripe component (`base_noRipe`); in regime B the ripe-window condition is not used at this index. Thus the inherited-operator and old-boundary parts of the induction have no base obligation. A genuine base output still needs a physical H.7 boundary family, which may be newly created by the first integral. P5 (1.31) is the **$ψ_1$-integrated component bound**; it neither proves those H.7 estimates nor the exact density identity. Finally, when $k_f=0$ there is no ordinary $0\to1$ step; P7 §4, p. 529, starts from a density already satisfying the inductive hypotheses. This base-step design therefore leaves the one-scale final integral of item 17(b) open, as `LF-BASE-KF0.md` Part G and `KF0-P7.md` explain.

**What this unblocks.** The mathematical base convention is fixed: no bare $\chi_0$, four first-step failure sets, retained raw spins on $D_{\rm out}$, and a threshold whose power pays the first-history numerical budget, including one or two $p_2$ factors. The next proof target is the physical `Prop279Phys` plus exact transform identity and `BaseStepData.S2`; only then can (20) close P5 (1.31) and feed the induction. **Confidence:** high for the algebra, Theorem 1, Corollary 2 and Lemma 3 under their stated hypotheses; high that the zero-input and margin counterexamples prohibit the current shortcut; no claim of a proved physical first-component (1.31) or $k_f=0$ last integral.
