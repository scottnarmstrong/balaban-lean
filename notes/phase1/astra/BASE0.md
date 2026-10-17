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

## Part 2. The localized first integral and the actual scope of the landed chart theorems

17 October 2026, round 2. **Result:** an exact *raw conditional* first integral and a boundary-uniform operator estimate for its $P$ witnesses are given below. The requested physical P5 (1.31) for **every** first component still does not follow: a proposed application of the landed chart normalization to a proper large-field sector has a false hypothesis, and P6's block-only $P$ estimate is false for the $AB$ test of (3). The corrected full-component theorem is stated precisely in §2.4, with its proof from the missing local majorant and the already established reserve. This identifies the remaining mathematical assertion, rather than treating a zero-kernel abstract input as its proof.

### 2.1 The exact physical first partition, and a conditional component integral

Write $\Lambda_0=\operatorname{Torus}_d(Ln)$ and $\Lambda_1=\operatorname{Torus}_d(n)$, and suppose $n=Mm$ so that the $\pi_1$ cubes have $M^d$ first blocks. For $\theta=z_1\psi_1$ put $G_\beta(\theta,\phi)=\prod_{y\in\Lambda_1}t_0(\theta_y-Q\phi_y)$ and $E(\phi;g)=\exp[-\beta H(\phi)+\langle g,\phi\rangle]$. These are exactly `baseKernel` and the spin exponential in `baseRho1` of `BasePhysicalDensity.lean`, with $a=a_{\rm Ker}$; `basePhysicalDensity` proves

$$Z_\Lambda(g)=\int d\psi_1\,z_1^{N|\Lambda_1|}\int d\sigma_{\Lambda_0}(\phi)\,G_\beta(z_1\psi_1,\phi)E(\phi;g).\tag{22}$$

At fixed $(\theta,\phi)$ define $W_P$ by (4), with $C_c=A_cB_c$ as in (3). Then the **pointwise, physical** identity is

$$\rho_1(\psi_1;g)=\sum_{P\subset\pi_1}\rho_{1,P}(\psi_1;g),\qquad
\rho_{1,P}=z_1^{N|\Lambda_1|}\int d\sigma_{\Lambda_0}(\phi)\,G_\beta(z_1\psi_1,\phi)E(\phi;g)W_P(\phi,z_1\psi_1).\tag{23}$$

This follows by multiplying (4) into the integrable density in `baseRho1` and interchanging a **finite** sum and integral. `chiPrimeZero_decomposition` proves the pointwise identity for arbitrary $M$; `spin_integrand_bound` and `baseRho1_integrable` supply the fixed-output and global physical integrability. `baseSector_selected_sector_weight` and `baseSector_physical_cut_selection` prove related pointwise selection and cut facts only for the specialized `baseSectorN L n`, whose cube parameter is **$M=1$**. Reblocking those facts to the actual $\pi_1$ with $M>1$ is an additional bridge, not an already landed equality.

Here is a literal local integral that keeps the raw variables. Fix one first component $X$, let $D_X$ be the fine sites mapping to cubes of $X$, and $Y_X$ the first blocks in $X$. Freeze the exterior spins $\tau$ and exterior coarse field. Let $H_X(\phi_{D_X};\tau)$ contain every bond energy whose bond meets $D_X$, once, and all field terms at sites of $D_X$. For separated components these bond sets are disjoint; bonds left over belong to the exterior action. Thus their exponentials multiply to the exact full Boltzmann factor. The failed-test footprints lie in $D_X$: a $P$ cube's block and site tests are in that cube, every bond-test endpoint is in its one-neighbourhood, and `baseRecord_good_region` places the entire three-neighbourhood of $P$ in $\Omega_1^c\subset Z_1^{\rm pre}$. The connecting one-neighbourhood path lies in the same component $X$. Let $J_X$ be *any* product of the remaining real record indicators, so $0\le J_X\le1$. With product **probability** sphere measure define

$$\begin{aligned}
(\mathcal K_{X,P,J}F)(\tau)
={}&\int_{\mathbb R^{NY_X}}\prod_{y\in Y_X}t_0(\theta_y-Q\phi_y)\,d\theta_y
\int_{(S^{N-1})^{D_X}}e^{-\beta H_X(\phi_{D_X};\tau)+\langle g_{D_X},\phi_{D_X}\rangle}\,
W_{P,X}(\phi,\theta)J_X(\phi,\theta)F(\phi,\theta;\tau)\,d\widehat\sigma_{D_X}(\phi).
\end{aligned}\tag{24}$$

$W_{P,X}$ is the product of $1-C_c$ on $P\cap X$ and $C_c$ on the other tested cubes of $X$. Indicators touching the frozen exterior read its actual spins; they are never replaced by a free boundary condition. Formula (24) is an exact finite-measure **conditional** integral for the raw $P$ sector. In the $\psi_1$ variable its integrand has $z_1^{N|Y_X|}$ and $d\psi_1$, which become $d\theta$ because $z_1>0$. In the geometric sphere convention multiply the right side by $s_N^{|D_X|}$. The first small-field expectation itself integrates only the chart variables on $D_+$; (24) integrates also the retained variables because it is an operator-norm test of the type in P5 (1.26). It is not yet P6's $T_1(X)$: peeling off the small-field action, its determinant, vacuum term and crossing-boundary activity is a further **identity to prove**.

**Theorem 4 (boundary-uniform physical $P$ operator bound).** With $n_P=|P\cap X|\ge1$, $\beta>0$, $a>0$, $L,M\ge1$, $0<\nu\le1$, and $\|F\|_\infty<\infty$, (24) obeys, for every exterior configuration $\tau$,

$$\bigl|\mathcal K_{X,P,J}F(\tau)\bigr|\le
e^{\|g_{D_X}\|_1}\|F\|_\infty
\left[M^d2^{N/2}e^{-L^{d-2}p_0(\beta)^2}+(2d+1)(LM)^de^{-p_0(\beta)^2/(4a)}\right]^{n_P}.\tag{25}$$

*Proof.* The full conditional Gaussian integral of a first block is one regardless of its spin block mean or the exterior configuration. Expand each $1-A_cB_c$ into $(1-A_c)+A_c(1-B_c)$ and drop all other indicators, which are at most one. For $n_A$ selected $A$ failures, choose one of $M^d$ blocks per cube. The selected Gaussian variables are disjoint, and (7) gives $q_A^{n_A}$. For $n_B$ selected $B$ failures choose one of at most $(2d+1)(LM)^d$ bonds/sites per cube. Every chosen bond lies in $H_X$ by the footprint hypothesis, even if it crosses the boundary of an individual $\pi_1$ cube; a bond is chosen at most twice. Each selected energy is at least $\delta_0^2/2$, so $\beta H_X\ge n_B\beta\delta_0^2/4=n_Bp_0(\beta)^2/(4a)$, exactly (8). The remaining energy is nonnegative, product sphere probability has mass one, and the source is bounded by $e^{\|g_{D_X}\|_1}$. Summing the $2^{n_P}$ assignments by the binomial theorem gives (25). All bounds are uniform in $\tau$. $\square$

This upgrades Theorem 1 from a torus integral to a conditional **operator** estimate for components with a $P$ witness. Corollary 2 and Lemma 3 turn (25) into a first-component reserve when the component's size is charged to these $P$ witnesses and all chart/boundary losses are separately bounded. They say nothing when $P\cap X=\varnothing$ and $Q$, $R$ or $S$ creates $X$.

### 2.2 Two false steps and explicit counterexamples

**False step A: using the landed all-good chart theorem for a proper bad sector.** `baseSectorCubeProduct` in `BaseSectorSupport.lean` is $\prod_c C_c$. The exact hypotheses of `baseSectorChartIntegral_eq_normalized` (`BaseChartComponentNormalization.lean`) and `baseRetainedChartIntegral_gaussian` (`BaseChartRetained.lean`) include

$$\texttt{hp}:\quad\prod_c C_c(\phi_0,\theta)\ne0.\tag{26}$$

For any $P\ne\varnothing$, $W_P(\phi,\theta)\ne0$ implies $C_c=0$ for some $c$, and therefore the left side of (26) is zero. The premise is **logically incompatible** with the proper large-field sector to be estimated. `baseSectorChartIntegral_eq_cut_gaussian` (`BaseChartCutFamily.lean`) has no explicit (26), but its integrand contains the same *global* cutoff $\prod_c C_c$, so it too represents only the all-good chart term. This is not a vacuous sector: take every spin equal to $h$, let every $\theta_y=h$ except one block $y_*$, and set $\theta_{y_*}=h+3\delta_0u$ for a unit vector $u$. All bond and site tests pass, precisely the cube containing $y_*$ fails its $A$ test, and an open neighbourhood of this configuration has positive physical measure. The all-good chart integral is zero there, while the $P$-sector integral is positive for $g=0$. `baseSector_physical_cut_selection` does supply a proper cut $U$ from the selected failed set, but its last conclusion explicitly says that under (26) $P=\varnothing$ and $U$ is the whole torus. Moreover `baseSectorCenter` in `BaseSectorSupport.lean` uses `GeneratingSet.single`, the full first torus, and falls back to $h$ when its global background-domain test fails; a proper-sector centre must instead use the good region and the actual raw collar. An arbitrary-$U$ Gaussian algebra theorem with (26) does not repair this support mismatch.

**False step B: applying P6 (3.4)'s Gaussian $P$ gain to $P=\{c:C_c=0\}$.** Choose a real spin configuration with one bond of length greater than $\delta_0$, and set $\theta_y=Q\phi_y$ on every first block. Then every $A_c=1$, while one or two adjacent $B_c$ fail. Thus $P\ne\varnothing$ but *no* Gaussian block tail occurs. P6 (3.4), p. 16, charges its $P$ set using the block test of P5 (2.5); it cannot be imported verbatim for the base convention (3). The corrected disjoint witness split is

$$1-A_cB_c=(1-A_c)+A_c(1-B_c),\tag{27}$$

with the first term paid by (7) and the second by bond/site energy (8) or by the appropriately shared `baseMainAction_bond_gain`/`baseMainAction_site_gain`. Equation (25) proves this correction after the retained variables are integrated. In a P6 majorant the energy share used for this $B$ witness must also be withheld from the shares used for $Q$ and $S$; multiplying three estimates that each spend the full action would be another invalid step.

### 2.3 The exact chart formula that a proper sector needs

The proper-sector replacement is mathematically unambiguous. Fix $P,Q,R,S$, their regions $\Omega_1,\Omega''_1,Z_1$, a component $X$, exterior raw spins, and the retained variables. Let $U= D_X\cap\widehat\Omega_1$. On $U$ choose a unit background $e_x$ determined by the coarse output and the fixed collar spins, **independent of the spins to be integrated**. Good tests $C_c=1$ for $c\subset\Omega_1$ give

$$|\theta_y-\phi_x|\le2\delta_0+d(L-1)\delta_0,\qquad
|\phi_x-e_x|\le C_{\rm hs}L\delta_0\le\tfrac14,quad
C_{\rm hs}=d+2+4dK_1.\tag{28}$$

The first inequality is the block test plus a path of at most $d(L-1)$ tested bonds within a block. The second is exactly the conclusion of `spins_near_background` when its `BaseSpinSupport` and `BgHyp` hypotheses are supplied. It implies $\phi_x\cdot e_x=1-|\phi_x-e_x|^2/2\ge31/32>0$, so each such spin has the unique tangent chart coordinate $v_x=\sqrt\beta[\phi_x-(\phi_x\cdot e_x)e_x]\in e_x^\perp$ and

$$\phi_x=e_x\sqrt{1-|v_x|^2/\beta}+v_x/\sqrt\beta,\quad |v_x|<\sqrt\beta,\qquad
d\sigma(\phi_x)=\beta^{-(N-1)/2}(1-|v_x|^2/\beta)^{-1/2}dv_x.\tag{29}$$

The last identity is the geometric surface-measure chart formula `toSphere_eq_graph`/`integral_sphere_pi_hemisphere_cutoff` in `SphereChart.lean`; `baseGoodIntegral_eq_baseChartIntegral` proves its finite-product form for any measurable cutoff **already known** to have this hemisphere support. The collar spins outside $U$ are kept raw. For $D_-=D_X\cap(\widehat\Omega_1\setminus\widehat\Omega''_1)$ the tangent coordinates are retained; for $D_+=D_X\cap\widehat\Omega''_1$ they are integrated in the first small-field expectation. At fixed collar and retained variables, the exact local integral is therefore the $D_+$ integral of the literal kernel, Boltzmann factor, source and selected tests after substitution (29), multiplied by $\prod_{x\in D_+}\beta^{-(N-1)/2}(1-|v_x|^2/\beta)^{-1/2}$. The $D_-$ Jacobians accompany their later retained-variable integration. Every bond touching a raw site still uses that raw spin; no crossing-bond energy can be deleted.

For clarity, let $W_{\mathfrak a}$ be the product of the four **ordered** selectors: $W_P$ of (4), the $Q$ selector from P5 (2.14), the $R$ selector from P5 (2.43), and the $S$ selector from P6 (3.2), each evaluated only on its eligible cube set. At fixed exterior data $\tau$ and fixed $\theta_X$, set $\Phi_x=\sigma_x$ on $D_{\rm out}$ and use (29) with $v_x$ on $D_-\sqcup D_+$. If $W_{\mathfrak a}$ vanishes off the hemispheres on $D_-\sqcup D_+$ and $e$ depends only on $(\theta_X,\sigma_{D_{\rm out}},\tau)$, finite-product change of variables gives the **exact selected local spin integral**

$$\begin{aligned}
&\int d\sigma_{D_X}(\phi)\,
 W_{\mathfrak a}(\phi,\theta)G_X(\theta,\phi)
 e^{-\beta H_X(\phi;\tau)+\langle g_{D_X},\phi\rangle}F(\phi,\theta)\\
&=\int d\sigma_{D_{\rm out}}(\sigma)
  \int_{|v_x|<\sqrt\beta,\ x\in D_-\sqcup D_+}
  \prod_{x\in D_-\sqcup D_+}
    \frac{\beta^{-(N-1)/2}\,dv_x}{\sqrt{1-|v_x|^2/\beta}}\;
 W_{\mathfrak a}(\Phi,\theta)G_X(\theta,\Phi)
 e^{-\beta H_X(\Phi;\tau)+\langle g_{D_X},\Phi\rangle}F(\Phi,\theta).
\end{aligned}\tag{29a}$$

Here $G_X=\prod_{y\in Y_X}t_0(\theta_y-Q\phi_y)$, and $d\sigma$ is the **geometric** sphere measure. The proof is Fubini over the finite site sets followed by (29) at each chart site; because the centre is independent of its integration variable, no derivative of $e$ enters the Jacobian. The $D_+$ integral on the second line, with $(\sigma,v_-)$ held fixed, is the precise first expectation that the P5/P6 operator must contain. Equation (29a) is not yet an equality with the *renormalized* P6 $T_1$: that equality additionally allocates its small-field action, determinant, vacuum and boundary terms. The local hemisphere premise and this allocation are the two assertions absent from the landed all-good chain.

For the Gaussian reference choose cut parameters $s_b=0$ on bonds crossing $U$ and $s_b=1$ otherwise. `baseSector_selected_cut` gives `IsFirstBlockUnion`, `CrossZero` and parameter membership. The exact identity is $q_1=q_s+(q_1-q_s)$; hence the *activity* contains $e^{-(q_1-q_s)}$ together with the chart Jacobian, cutoff, nonlinear normal-coordinate term, source and regime-A mass perturbation. `baseSector_cut_exponent_of_product_ne_zero` proves precisely this algebra, but again with the **global** product support (26). `baseRetainedChartIntegral_gaussian` proves the principal-submatrix Gaussian/determinant calculation for a cut $U$, but with the same support premise. Replacing (26) by the good-cube product on $U$ and supplying the collar data in (28) is the missing local theorem. Its exact statement must retain $(q_1-q_s)$; dropping it changes the physical density whenever a crossing bond has nonzero energy. `baseSector_component_logDet_factorization` can then split the determinant after this legitimate cut; it does not perform the support replacement.

The further $Q,R,S$ partitions are inserted **in order**: $Q$ on the eligible cubes of $\Omega_1^{\sim3}$ by P5 (2.13)–(2.14), pp. 503–504; $R$ on the eligible cubes of $\Omega_1$ by P5 (2.42)–(2.43), p. 511; $S$ on the eligible first-output cubes in P6 (3.2), pp. 15–16. On each stage the two characteristic functions sum to one pointwise in the variables available at that stage. The source operator is P5 (2.47), pp. 512–513, followed by P6 (3.2). At the test-free base, only factors of the *old density's* small-field $\chi_0$ and old component operator disappear; the **new** failed-test factor $\chi'^{(0)c}(P)$ remains and is replaced by $1-A_cB_c$ as in (27). A proof identifying this staged operator with (23), after the $D_+$ expectation and the good small-field action have been peeled off, is **not** among the landed theorems just cited. Formula (29) gives its necessary local measure, not that missing identification or a bound for its activity.

### 2.4 Corrected full-component majorant and deduction of (1.31)

Here is the exact remaining assertion. For each admissible record and $X$, let $\mathcal T^{\rm phys}_{1,X}$ be the operator from the staged construction of §2.3, with the $D_+$ chart expectation already evaluated and with its physical determinant, vacuum normalization, crossing-bond activity and P6 boundary term allocated. Split $P=P_A\sqcup P_B$ by (27), with $P_B$ carrying a chosen bond/site witness; write $(|P_A|+|P_B|+|Q|+|R|+|S|)_X$ for the sum of their cardinalities after intersection with $X$. A **physical local majorant** must prove, uniformly in retained boundary spins and in the source ball,

$$\int d\psi_1|_X\,|\mathcal T^{\rm phys}_{1,X}F|
\le\exp\{-A_3\lambda_0^{2p_0}(|P_A|+|P_B|+|Q|+|R|+|S|)_X
 +(c_1\lambda_0+c_2)|X|_1\}\sup\chi_X|F|.\tag{30}$$

The support $\chi_X$ must be P5 (1.24)–(1.25), p. 494. To make $A_3>0$ explicit, choose $p_1=p_0$ as P6 does in (3.9), require $p_0(\beta_1)\ge A_0c_\lambda^{p_0}\lambda_0^{p_0}$, and split the nonnegative main action into four shares: one for $P_B$, one for $Q$, one for $S$, and one residual share. Before witness-choice and volume costs, conservative available coefficients of $\lambda_0^{2p_0}$ per seed are

$$\begin{array}{c|ccccc}
\text{seed}&P_A&P_B&Q&R&S\\ \hline
\text{coefficient}&L^{d-2}A_0^2&A_0^2/(16a)&2\gamma_0A_0^2/[6^d(9K_1)^2]&A_1^2/4&\gamma_0 A_0^2c_\lambda^{2p_0}/[8\cdot6^dK_1^2].
\end{array}\tag{31}$$

The $P_A$ coefficient follows from (7); the $P_B$ coefficient follows from (8) with one quarter of the bare action; the $Q$ and $S$ coefficients are one quarter of P6 (3.7) and (3.8), p. 18; the $R$ coefficient is P6 (3.4), p. 16. These last three source rates apply **only after** their action and Gaussian measures have been identified with the physical local operator. The source's own (3.9), p. 18, sets $p_1=p_0$ and $A_3=\min\{8\gamma_0A_0^2/[6^d(9K_1)^2],A_1^2/8\}$ in its block-only convention; (31) is a conservative proposed modification for the $AB$ base test, not a claim that P6 proves it verbatim. Let $c_*$ be the minimum of the five positive coefficients in (31), and let $C_{\rm wit},C_{\rm loc}\ge0$. If a local activity proof bounds all witness-choice losses by $C_{\rm wit}n_X$ and all sphere, chart, determinant, localization and boundary losses by $C_{\rm loc}(\lambda_0+1)|X|_1$, then the **written inequalities**

$$C_{\rm wit}\le\tfrac12c_*\lambda_0^{2p_0},\qquad
A_3=\tfrac12c_*,\qquad c_1\lambda_0+c_2\ge C_{\rm loc}(\lambda_0+1)\tag{32}$$

turn the typewise factors into (30): $c_*\lambda_0^{2p_0}n_X-C_{\rm wit}n_X\ge A_3\lambda_0^{2p_0}n_X$, and the last inequality absorbs the volume loss. A sufficient explicit threshold for the first condition is $\lambda_0\ge(2C_{\rm wit}/c_*)^{1/(2p_0)}$, in addition to $\lambda_0\ge1$; $c_1,c_2\ge C_{\rm loc}$ suffice for the second. **No landed theorem supplies a physical, volume-uniform $C_{\rm loc}$ for this proper sector**, so (31)–(32) are a corrected proof target, not an unconditional verification of (30).

Once (30) and the exact density identity are proved, P6 (3.11), p. 19, supplies the record-counting target $\sum_{\mathfrak a|X}C_1(\mathfrak a|X)^{-1}\le1$. `RegionHistory.base_exponents` gives the base values of $\kappa_1$ and $\log C_1$; `RegionHistory.base_budget` and Lemma 3 give

$$\kappa_1-\log C_1-H_1|X|_1\ge\ell p_2(\beta_1),\qquad \ell\in\{1,2\},\tag{33}$$

under (15). Multiply each instance of (30) by $C_1^{-1}C_1$, take the supremum of $C_1e^{-\kappa_1}$ using (33), and sum the $C_1^{-1}$ weights. This is exactly (20), hence P5 (1.31). The derivation is complete **conditional on (30), physical identification and record counting**; the high-power threshold pays the reserve but cannot manufacture a missing component kernel estimate.

### 2.5 Lean correspondence and final verdict

| Step | Landed declaration and what it actually proves | Missing proper-sector statement |
|---|---|---|
| Starting density and first partition | `basePhysicalDensity`, `baseRho1_integrable` in `BasePhysicalDensity.lean`; `chiPrimeZero_decomposition` in `BaseRecord.lean` | Glue generic $M$ record tests to `baseRho1` as (23) |
| Retained $P$ footprint and witnesses | `baseRecord_good_region`, `baseF_decomposition`, `baseBlock_gain`, `baseMainAction_bond_gain`, `baseMainAction_site_gain` | Identify the witnesses with factors of the nonzero physical component; use shared action energy for $P_B,Q,S$ |
| Good spin chart | `spins_near_background` under `BaseSpinSupport`; `baseSectorSpinSupport_of_product_ne_zero` only on global all-good support | `baseRecord_localSpinSupport` from good cubes in $\Omega_1$ and raw collar spins; no all-good hypothesis |
| Exact chart measure and action | `toSphere_eq_graph`, `baseGoodIntegral_eq_baseChartIntegral`, `basePhysicalExponent_chart`, `baseSector_cut_exponent_of_product_ne_zero` | Conditional hemisphere chart of (29) on $\Omega_1$ for the selected $P,Q,R,S$ record, with crossing activity |
| Cut Gaussian and determinant | `baseSector_selected_cut`, `baseRetainedChartIntegral_gaussian`, `baseSector_component_logDet_factorization` | Replace their global `hp` by the local record support; split $D_+$ from retained $D_-$ and raw exterior |
| P6 majorant and closure | Source P6 (3.4)–(3.9); landed `RegionHistory.base_budget` and `base_exponents` | Prove (30) for the physical operator, with a nonzero exact transform identity and the count (1.27) |

**Verdict and confidence.** Equations (22)–(25), the incompatibility (26), the bond-only counterexample, and the chart change (28)–(29) under its stated local-support hypothesis are rigorous. The two counterexamples show why the present all-good chart chain and the unmodified P6 block gain cannot prove the requested full first-component bound. The corrected statement (30) has an explicit route to P5 (1.31) through (31)–(33), but its local physical activity estimate and exact staged identification are still open in the landed code and have not been proved in this note. Confidence is high in these negative and conditional conclusions; **P5 (1.31) for every first large-field component is not claimed proved.**

## Part 3. The proper-record chart and the limit of the present operator argument

**Update to Part 2.** Its table says that `baseRecord_localSpinSupport` is missing. The required statement is in fact already landed, under the name `baseSpinSupport_of_baseRecord` in `BaseSupport.lean`. The theorem below uses it. This repairs the first obstruction in that table, but does not remove the global all-good premise of the Gaussian and determinant theorems. Throughout this part the first density is the test-free `baseRho1` of `BasePhysicalDensity.lean`, with $M$ absorbed into the coarse torus side $M n_1$ when comparing its notation with `BaseRecord.lean`. A selected $P$ is **proper** when its first-sector weight is nonzero and $P\ne\varnothing$.

### 3.1 Local spin support: proved, without an all-good premise

**Proposition P3.1 (the landed local-support lemma).** Let $G:\texttt{GeneratingSet}\ d\ L\ (M n_1)\ 1\ \varrho$, $b:\texttt{BaseRecord}\ d\ L\ n_1\ R$, and suppose

$$x\in G.\Omega 1\quad\Longleftrightarrow\quad\operatorname{cubeMap}(x)\in b.\Omega.\tag{34}$$

Assume the scale relation $n_0=Ln_1$, $\delta_0>0$, unit spins $\phi$, a unit $h$, and background data $D$ equal to $\theta$ on the blocks of $G.\Omega1$, to the **raw** $\phi$ on $\operatorname{collar}G$, and to $h$ for the field on $G.\Omega1$. If

$$\chi'_0(c;\phi,\theta)=1\qquad(c\notin b.P),\tag{35}$$

then `BaseSpinSupport G (if regimeB then ν else 0) δ₀ φ h D` holds. The conclusion has no premise $\prod_c\chi'_0(c)\ne0$; (35) is exactly the good-cube factor of the selected $P$ term. In Lean this is the full statement of `baseSpinSupport_of_baseRecord` (`BaseSupport.lean`, lines 73–133), with (34) its `hΩ`, (35) its `hsupp`, and the three data equalities its `hDΨ`, `hDc`, `hDh`. `RegionHistory.baseSpinSupport` (same file, lines 143–159) supplies (34) for `histGen` when its stated no-removal and $L\ge2$ hypotheses hold.

*Proof.* If $x\in G.\Omega1\cup\operatorname{collar}G$, `exists_near_of_mem_dataSites` places its scale-one cube at index distance at most $3$ from a cube of $b.\Omega$. `BaseRecord.not_mem_P_of_near_Omega` says this cube is outside $b.P$. Unpacking (35) by `chiPrimeZero_eq_one_iff` therefore gives its block, bond and, in regime B, site tests. The block test is transported to `spinBlockAverage` by `spinAverage_eq_spinBlockAverage`. For a bond with either endpoint in the data sites, apply the bond test in that endpoint's cube. The site test holds on every data site; in regime A its coefficient is zero and $0<\delta_0^2$. The remaining `BaseSpinSupport` fields are exactly the unit and data hypotheses. This is the proof in `BaseSupport.lean`; every use of a good test is local to the $3$-neighbourhood of $\Omega_1$. $\square$

**Scope.** The theorem assumes the data equalities, the existence of $G$, and the background hypothesis in the next step. A bare `BaseRecord` alone does not construct $D$ or an admissible background. The record's $Q,R,S$ fields may be arbitrary subject to their geometry; they do not enter the proof of (35).

### 3.2 Conditional hemisphere chart on the selected record: proved

Fix $\theta$ and all raw spins $\sigma$ outside $E=G.\Omega1$, including $\Gamma=\operatorname{collar}G$. Construct $D=D(\theta,\sigma_\Gamma)$ as in Proposition P3.1, and set $e_x=\Re\,\texttt{bgField}\ G\ a\ \nu_*\ D(x)$ for $x\in E$, where $\nu_* =\nu$ in regime B and $0$ in regime A. Thus $e$ is **independent of every spin subsequently integrated on $E$**. Let $W_P=\prod_{c\in P}(1-C_c)\prod_{c\notin P}C_c$, and let $V_{QR}$ be any measurable pre-expectation $Q,R$ selector taking values in $[0,1]$. Then $W_PV_{QR}\ne0$ implies (35). A post-expectation $S$ selector may be included only when it is a measurable function of the variables fixed at this stage; otherwise multiply it after that expectation, as P6 (3.2), pp. 15–16, prescribes. This corrects the unqualified single-product reading of $W_{\mathfrak a}$ in (29a).

Explicitly, take $\Psi(x)=\theta_{j\operatorname{Block}(x)}$ on $E$, $\Psi(x)=\sigma_x$ on $\Gamma$, and zero elsewhere; take $\widetilde h=h$ on $E$ and zero elsewhere. The block lift is constant on every complete first block of $E$, while the collar values have no such requirement. Therefore these fields satisfy the layer-constancy hypotheses of `BgData.clip` (`Background/Data.lean`, lines 219–243), which constructs $D$ with the equalities used in Proposition P3.1. This construction uses the first-block-union property of $G.\Omega1$; it is not a consequence of arbitrary pointwise choices of $\Psi$.

**Proposition P3.2 (conditional record chart).** Assume `BgHyp d L 1 ϱ a ν_*` and

$$4dL\delta_0\le\texttt{bgC1}\ d\ L\ N,\qquad C_{\rm hs}L\delta_0\le\tfrac14,
\quad C_{\rm hs}=d+2+4d\,\texttt{bgK1}\ d\ L\ N.\tag{36}$$

On $W_PV_{QR}\ne0$, every $x\in E$ satisfies $|e_x|=1$, $|\phi_x-e_x|\le C_{\rm hs}L\delta_0$ and $e_x\cdot\phi_x>0$. Hence $v_x=\sqrt\beta(\phi_x-(e_x\cdot\phi_x)e_x)$ is unique, $v_x\in e_x^\perp$, $|v_x|\le\sqrt\beta C_{\rm hs}L\delta_0<\sqrt\beta$, and (29) recovers $\phi_x$. For every integrable selected physical integrand $F$ and fixed exterior $\sigma$, its conditional spin integral is **exactly**

$$\int_{(S^{N-1})^E}W_PV_{QR} F(\phi_E,\sigma)\,d\sigma_E
=\beta^{-m/2}\int_{\prod_{x\in E}\{|v_x|<\sqrt\beta\}}W_PV_{QR} F(\Phi_E(v),\sigma)
\prod_{x\in E}(1-|v_x|^2/\beta)^{-1/2}\,dv_E,
\qquad m=(N-1)|E|.\tag{37}$$

Here $d\sigma$ is geometric surface measure, as in `aprioriMeasure` (`Frozen/Model/AprioriMeasure.lean`); probability surface measure instead contributes $s_N^{-|E|}$ on the right. $F$ may contain the literal `baseKernel`, **all** bond factors touching $E$, the source, and any pre-expectation selector. No crossing bond is omitted.

*Proof.* Proposition P3.1 supplies `BaseSpinSupport`; `spins_near_background` (`SpinsNearBackground.lean`, lines 422–495) under (36) gives all three stated background assertions and the tangent bound, pointwise on $E$. Unit length gives $e_x\cdot\phi_x=\sqrt{1-|v_x|^2/\beta}>0$. The sphere graph Jacobian at each $x$ is $\beta^{-(N-1)/2}(1-|v_x|^2/\beta)^{-1/2}$. Multiply these identities over finite $E$ and apply Fubini. The conditional centre does not vary with $\phi_E$, because its block data are $\theta$ and its collar data are the fixed $\sigma_\Gamma$. `integral_sphere_pi_hemisphere_cutoff` and `baseGoodIntegral_eq_baseChartIntegral` (`BaseChartIdentity.lean`, lines 130–220) are the landed full-product form of this geometric change of variables when a cutoff has the proved hemisphere support. $\square$

The independence of the centre is essential. If one sets $e(\phi)=\phi$ for a single spin, the alleged tangent coordinate is identically zero while the sphere measure has positive mass on open sets; (37) would be false. The data construction above excludes this counterexample. Proposition P3.2 is an integral identity, not yet the P6 component operator or an activity estimate.

### 3.3 The cut Gaussian and determinant: the true local statement

Write $E=I\sqcup J$, where $I=D_+\cap E$ is the set integrated in the first expectation and $J=E\setminus I$ contains the retained chart sites. Assume $I$ is a union of complete first blocks and cut every Hessian bond from $I$ to $J$. The raw sites $E^c$ are **not** coordinates of this Hessian: they remain arguments of the physical crossing activity. Let $K_s$ be the real symmetric positive definite matrix of the cut tangent quadratic form on $E$, with blocks $K_I,K_J$, and set $q_s(v)=\frac12\langle v,K_sv\rangle$. Zero crossing entries give

$$K_s=K_I\oplus K_J,\quad q_s(v_I,v_J)=q_I(v_I)+q_J(v_J),\quad
\det K_s=(\det K_I)(\det K_J).\tag{38}$$

For fixed $v_J$ and raw $\sigma_{E^c}$, define the **literal activity** $A_s$ by the exact equality

$$\mathcal I_{\rm phys}(\Phi(v),\sigma;\theta,g)
=e^{-q_s(v)}A_s(v,\sigma;\theta,g).\tag{39}$$

To make (39) non-tautological, write the Gaussian kernel as $K(\theta,\Phi)=\kappa\exp[-B_{\rm block}(\Phi,\theta)]$ and define the **exact**, as yet unbounded, remainder by $R(v,\sigma)=\beta H(\Phi,\sigma)+B_{\rm block}(\Phi,\theta)-B(e,\sigma;\theta)-q_1(v)$. Here $B(e,\sigma;\theta)$ is any specified background constant, and $q_1$ is the local uncut Hessian quadratic allocated from that same exponent. Then, including the chart Jacobian $J_\beta$ in $\mathcal I_{\rm phys}$, its $A_s$ is exactly

$$\kappa e^{-B(e,\sigma;\theta)}e^{-R(v,\sigma)}e^{-[q_1(v)-q_s(v)]}
J_\beta(v)W_PV_{QR}e^{\langle g,\Phi\rangle}.\tag{40}$$

The physical boundary bonds with a raw endpoint are included in $R$ (or kept literally in $A_s$). They cannot be represented by a determinant on $E$. If $m_I=(N-1)|I|$, the exact first integral at fixed $(v_J,\sigma)$ is

$$\int_{\mathbb R^{m_I}}e^{-q_I(v_I)}A_s(v_I,v_J,\sigma)\,dv_I
=(2\pi)^{m_I/2}(\det K_I)^{-1/2}\,
\mathbb E_{\gamma_I}A_s(V_I,v_J,\sigma),\tag{41}$$

where $\gamma_I$ is the centred Gaussian with covariance $K_I^{-1}$; the chart-domain indicator is in $A_s$. The complete chart prefactor $\beta^{-m/2}$ from (37) is allocated between $I$ and $J$. Equations (38)–(41) follow by block-matrix multiplication, the real Gaussian integral, and the definition (39). They do **not** bound $A_s$. The algebraic cut identity $q_1=q_s+(q_1-q_s)$ is the content of `baseSector_cut_exponent_of_product_ne_zero` (`BaseChartCutFamily.lean`, pp. 1–3 of that file); `baseRetainedChartIntegral_gaussian` (`BaseChartRetained.lean`, line 819) and `baseSector_selected_cut_gaussian_factorization` (`BaseChartComponentGauss.lean`, line 269) prove a corresponding Gaussian/determinant result for their stated **single, globally all-good** centre. The generic matrix steps also appear as `cinner_hessian_add_of_cross_zero` (`BaseChartRetained.lean`) and `trace_logMat_eq_blocks` (`BaseComponentDeterminant.lean`). None of those sector theorems replaces its hypothesis `baseSectorCubeProduct ≠ 0` by (35), nor constructs $K_s$ from $D(\theta,\sigma_\Gamma)$ for a proper record. Thus (38)–(41) are proved as finite-dimensional identities **conditional on a positive local $K_s$ and the exact local quadratic allocation**; their proposed identification with the landed sector Gaussian is false.

For a concrete failure if one drops the crossing activity or factors the *uncut* determinant, take $K_1=\begin{pmatrix}1&t\\t&1\end{pmatrix}$, $0<|t|<1$, and cut to $K_s=I_2$. Then $q_1-q_s=t v_1v_2\ne0$ and $\det K_1=1-t^2\ne(\det K_I)(\det K_J)=1$. Both discrepancies persist on open sets. This is the local algebra behind the crossing term in P5 (2.47), pp. 512–513, and P6 (3.2), pp. 15–16.

### 3.4 Exact first transform, a nonzero sector, and the count

For fixed $\theta$ let $\mathcal K(\theta,\phi)$ denote the literal integrand of `baseRho1`: `baseKernel` times $e^{-\beta H+\langle g,\phi\rangle}$, including the $z_1^D$ Jacobian in the $\psi_1$ variable. The exact first identity, with no chart or Gaussian allocation, is

$$\rho_1(\psi_1;g)=z_1^D\sum_{P\subset\pi_1}\int W_P(\phi,z_1\psi_1)
\mathcal K(z_1\psi_1,\phi)\,d\sigma_\Lambda(\phi).\tag{42}$$

Its proof is (4), finite distributivity, and linearity of the integral; `basePhysicalDensity` and `chiPrimeZero_decomposition` supply exactly those ingredients. At the later stages, insert each $Q$, then $R$, then $S$ binary partition **on the variables then present**. Summing over all records restores (42), by repeated $\chi+(1-\chi)=1$ and finite Fubini. This is an exact identity for the staged *unrenormalized* pieces. It is not an identification of those pieces with P6's renormalized $T_1(X)$: that requires the local background action, (39), Gaussian normalizations, vacuum terms, and boundary allocation to match P5 (2.47)/P6 (3.2).

The identity is nonzero on a proper sector. Set all spins to $h$, choose one block $y_*$ and set $\theta_{y_*}=h+3\delta_0u$ for a unit $u$, with $\theta_y=h$ elsewhere. Then exactly its cube $c_*$ fails $A$, every $B$ passes, and $W_{\{c_*\}}=1$. For $g=0$, `baseKernel` and the Boltzmann factor are strictly positive. Strict inequalities persist on an open set of positive sphere and Lebesgue measure, so the $P=\{c_*\}$ term of (42) is strictly positive. The later partitions place each point in at least one $Q,R,S$ sector; therefore some proper complete record also has positive integral. This directly rules out using the zero all-good chart term as the physical proper-record operator.

There is an elementary **global** count: if the coarse torus has $V$ cubes, a record is determined by four subsets $P,Q,R,S$, so there are at most $2^{4V}$ records. With $C_{\rm glob}=2^{4V}$, $\sum_{\mathfrak a}C_{\rm glob}^{-1}\le1$. This volume-wide count cannot replace P5 (1.27), p. 494, for a single component: outside cubes can change $\Omega\cap X$.

**Proposition P3.3 (the P5 local count, using P6's local coding bound).** P6 §3, p. 19, immediately before (3.11), bounds the number of choices of the *new regions restricted to a fixed component* by $2^{6(LM)^{-d}|Z_0^c\cap X|_\eta}$; its separate old-region factor is $2^{M^{-d}|Z_0\cap X|_\eta}$. At $k=0$, $Z_0=\varnothing$, so in the landed base convention $|X|_\eta=(LM)^d\#X$ the number $r_X$ of admissible restricted first records satisfies

$$r_X\le2^{6\#X},\qquad
\log C_1(X)=\tfrac54 L^d\#X,\qquad
\sum_{\mathfrak a|X}C_1(X)^{-1}
\le\exp[(6\log2-\tfrac54L^d)\#X]\le1.\tag{43}$$

The middle equality is `RegionHistory.base_exponents` (`BaseHistory.lean`, lines 212–236), the base case of P6 (3.11), p. 19. For the last inequality $d\ge3,L\ge2$ imply $L^d\ge8$, hence $(5/4)L^d\ge10>6>6\log2$. This proves (1.27) mathematically **with P6's stated local coding estimate as input**. The landed base files verify the value of $C_1$ but contain no theorem formalizing that local coding estimate or the final sum inequality; a Lean closure still needs that count. The estimate applies to P6's admissible *localized restrictions*, not to arbitrary `BaseRecord` structures with no chosen component.

### 3.5 What can be proved about (30)

The exact hypotheses needed to turn (41) into (30) are now visible. In addition to Theorems 3–4, one must prove, for every proper admissible record and every component $X$:

1. A **physical identification** of the staged piece of (42) with P5 (2.47)/P6 (3.2) after the $I=D_+$ expectation, retaining the raw exterior and the factor $e^{-[q_1-q_s]}$ in (40).
2. A positive local $K_s$ and an activity inequality for the *actual* $A_s$, uniform in $(v_J,\sigma_{E^c})$, which allocates the bare bond/site action between $P_B,Q,S$, the Gaussian tails to $P_A,R$, and bounds chart, determinant, source, localization and boundary terms by $C_{\rm loc}(\lambda_0+1)|X|_1+C_{\rm wit}n_X$.
3. An identification of the admissible local record restrictions in the physical transform with those counted in P6's p. 19 estimate, so that Proposition P3.3 applies to precisely the operators in the sum.

Under these three quantitative hypotheses, (31)–(32) prove (30) with $A_3=c_*/2$, $c_1,c_2\ge C_{\rm loc}$ and $\lambda_0^{2p_0}\ge2C_{\rm wit}/c_*$. Indeed the five witness types contribute at least $c_*\lambda_0^{2p_0}n_X$; subtracting the witness-choice cost leaves $A_3\lambda_0^{2p_0}n_X$, and the remaining loss is at most $(c_1\lambda_0+c_2)|X|_1$. Proposition P3.3 and `RegionHistory.base_budget` then yield (33) and P5 (1.31) exactly as in §2.4. This is a **conditional theorem**, with its analytic and record-identification hypotheses displayed rather than hidden in the definition of $\mathcal T^{\rm phys}_{1,X}$.

The landed statements do not establish those hypotheses. `baseMargin_counterexample` (`Prop279Counter.lean`, lines 83–142) exhibits a nonzero proper $P$ term whose good bond test lies arbitrarily close to its threshold; thus the strict record tests alone cannot supply the margin needed by `baseCutoffTransfer`. The bond-only example in §2.2 shows that P6 (3.4)'s $P$ Gaussian rate cannot be applied to the base $A B$ test. The globally all-good hypotheses of `baseRetainedChartIntegral_gaussian` and `baseSector_selected_cut_gaussian_factorization` are incompatible with this same nonzero proper term. These are counterexamples to specific attempted implications, **not** counterexamples to the correctly formulated physical estimate (30). No bound of the form (30) for that physical operator is proved by the cited landed files or by (38)–(42). P5/P6 give the induction template and its rates, but their formulas do not themselves verify the test-free base identification and its local activity allocation.

**Lean shape and conclusion.** The first lemma is already `baseSpinSupport_of_baseRecord`, followed by `spins_near_background`. The next useful Lean declaration should take `G`, `br`, (34)–(36), fixed raw collar data, and `hsupp` as inputs and conclude a conditional chart identity of the form (37) for a measurable selected cutoff. A subsequent theorem must construct a local positive cut Hessian and prove (39)–(41) with the *record* centre; its majorant must expose $P_A/P_B$ and the $Q,R,S$ shares. A separate Lean local record-count theorem should formalize P6's p. 19 coding bound and conclude (43). Only then can `RegionHistory.base_budget` close (1.31). Confidence is high in Propositions P3.1–P3.2, the elementary cut identities, (42), the deduction (43) from P6's stated count, and the counterexamples; confidence in an unconditional (30) is **not warranted** by the present evidence. The local-support obstacle from Part 2 is removed. The physical activity and identification remain open; the source-level count is available but has no landed Lean proof.
