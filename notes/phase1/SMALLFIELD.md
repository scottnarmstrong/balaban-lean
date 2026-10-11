# SMALLFIELD: the small-field step at $\lambda=\infty$ (phase 1, document D-SF; roadmap I-6 … I-9)

Status: draft for review, 2026-10-11. Pure mathematics on paper; no Lean was written or run. Labels: **proved** (a complete argument is given here, possibly from named inputs), **cited** (a source or another phase-1 note proves it), **sketched** (plan with the key estimate), **UNCERTAIN:** (doubt). Page numbers are journal pages; P1 = CMP 167 (pdf page = journal $-102$), P4 = CMP 182 (pdf page = journal $-674$).

**What was read.** AGENTS.md, roadmap §3.3, §5.2, §8, §9; BIG §2.5, §7 item 13; the reviews P1, P4, P5, P6; `ERRATA.md`; `GREEN.md` (G-1…G-6 headings, C14, §4.4), `BACKGROUND.md` (§0, §1, §5, §6), `POLYMER.md` (PE, MY, PE-M), `CORRELATIONS.md` (§2, §5), `LF-ARCHITECTURE.md` (§1.4, §3.6); the landed `Balaban/Flow/RGEquations.lean` and `RunningCoefficients.lean`. **Page images read for this document:** P4 pp. 708–718 (pdf 34–44: equations (5.4)–(5.34), Proposition 5.1 and its remarks, Proposition 5.2). **P1 was not re-read**; its statements are taken from the review `review/papers/P1-LTE-I-RG-flow.md` and tagged [review].

Notation. $d\ge3$, $N\ge2$, $L\ge2$ the block factor, $M=L^m$, $\mathbb T$ a torus, $\Lambda_j=T^{(j)}_1$ the unit lattice of level $j$ (centres of $L^j$-blocks, rescaled to spacing 1), $\eta=L^{-k}$, $s=s_{jk}:=L^j\eta=L^{-(k-j)}$. Spins are $\mathbb R^N$-valued (complex in the analytic extensions); $u\cdot v=\sum_iu^iv^i$ is bilinear. $\lambda=\infty$ throughout: $1/\lambda_j=0$ for all $j$, the constraint is $|\phi|=1$ with a Lagrange multiplier $\alpha$.

---

## 0. Summary (the reply asked for by the brief)

**The four statements.**

- **I-6** (P1 Prop 3.10, Cor 3.11). If the localized terms $\mathcal E^{(j)}(y,X;\cdot)$ are analytic, $O(N)$- and Euclid-invariant, localized with $|\mathcal E^{(j)}(y,X)|\le E_0e^{-\kappa d_j(X)}$ and satisfy the renormalization conditions (H.5), then for configurations of the form $\psi^{(j)}_k$ one has $\mathcal E^{(j)}(y;\psi)=\mathcal V^{(j)}(\psi(y))+A_y(\psi)+\mathcal I^{(j)}(y;\psi)$ with $\sum_yA_y=0$ and $|\mathcal V|,|\mathcal I|\le CE_0(\varepsilon_k/\varepsilon_j)^2s^{3-\alpha_1}$, hence $|\mathcal E_k|\le C_6E_0|T^{(k)}_1|$ on $\Xi_k^c(1,\varepsilon_k)$ uniformly in $k$ (§2).
- **I-7** (P4 Prop 5.1, (5.31)–(5.33)). At $\lambda=\infty$ the renormalization conditions are a triangular system $A\xi+\tilde c(\xi)=\tilde f(\xi)$ for $\xi=(\zeta/\varepsilon_{k+1},e/\beta,b/\beta)\in\mathbb C^3$ with exactly one solution in a polydisc of radius $r_0$, real and analytic in the data, $|\xi^0|_\infty\le C_\xi\beta^{-1}L^{-2\gamma(k+1)}$; the choices $c=a_{k+1}b$ and $c=0$ (with $d=b$, vacuous at $\lambda=\infty$) give the same system up to second order; (H.6) holds with $\gamma_\infty,\delta_\infty$ and $|\gamma_\infty-1|,|\delta_\infty-1|\le C/\beta$ (§3).
- **I-8** (P4 Props 2.1, 2.2, 4.1, 4.2; P5 Props 3.1–3.4 on the whole lattice). The new contributions $\mathcal E^{(k+1)}_0,\mathcal M^{(k+1)}_0$ of the fluctuation integral and the renormalized $\mathcal E^{(k+1)},\mathcal M^{(k+1)}$ have localization expansions on $\Xi^c_{k+1}(\mathbb B_{k+1}(Y);1,\varepsilon_{k+1})$ with the (H.4)/(H.7) bounds and exponent $2\kappa-3-6\kappa_0$; proved from I-4, I-5, PE-L/MY/PE-M and P6 (4.11) (§4).
- **I-9** (P4 Thms 1–2). One step $\chi_{k+1}S^{(k)}T^{(k)}\chi^{(k)}$ maps $\mathbb R^{\rm sf}_k(\beta,a,\nu;B,\bar\nu)$ into $\mathbb R^{\rm sf}_{k+1}(\beta,a,\nu;BL^{d-2},\bar\nu L^2)$ for $\bar\nu\le\frac78L^{-2}$, with $\mathcal E^{(j)}_{k+1}=\mathcal E^{(j)}_k$ ($j\le k$) and the coefficient recursion (1.9)–(1.10) of P4; I-8's conclusions are produced inside its proof, not assumed (§5).

**Which proofs are complete.**
- *I-7*: complete from the landed `exists_rg_solution_triangular` once the analytic bounds (5.24)–(5.25) on the data are supplied (they come from I-8 and I-6's domain lemma); the triangular coefficients are bounded here at $\lambda=\infty$; the rate $|\gamma_\infty-1|\le C/\beta$ is proved (new, from P4 (5.31)); continuity in $\nu\downarrow0$ is reduced to one explicit clause on the data (Lemma 3.4, the stability lemma, is proved).
- *I-6*: complete as a proof of the decomposition and the bound, from the named inputs (I-1, I-2, the second-difference bound P1 (3.107), the elementary domain inequalities P1 Lemma 3.1, cited). The proof written here is not P1's: it uses a second-order Taylor expansion with third-order remainder and a short exact identity (the Ward identity (WI), §2.3 Step 5) that replaces P1 (3.67)–(3.125); it makes the role of (H.5) transparent. Constants are not tracked.
- *I-8*: statements and a step-by-step proof plan; sketched.
- *I-9*: statement and proof outline with every input named; sketched. The base case $\rho_1\in\mathbb R^{\rm sf}_1$ at $\lambda=\infty$ is not in the sources (ER-062, ER-063) and is left to LF-6.
- *Two-point/one-point parts*: the extra statements are listed (§6); not proved.

**Main risk.** I-8 (and, inside I-9, the identification of the constants chain with those of I-4/I-5): the localization expansions of the fluctuation integral are only "deferred" in P4, P5 and described in P6; their Lean cost and the loss of $\kappa$ per step ($\kappa\to2\kappa-3-6\kappa_0$) are the least controlled quantities. A second, smaller risk is the continuity clause in $\nu$ (§3.5).

**Size.** $\approx 270$k–470k Lean lines for I-6…I-9 and the one/two-point extension, on top of Green, Background, Localization and PE (table in §7.5); I-8 and I-9 are about 60% of it.

**Questions** (details in §7.6): (1) free flow $c=a_{k+1}b$ versus P5–P7's $c=0$ in Def-7 (D2); (2) the continuity-in-$\nu$ clause; (3) state the analyticity domains of $\mathcal E^{(j)}$ by $\tilde\Psi^c$ instead of $\Xi^c$; (4) $\gamma_0=\frac12$ versus $1$; (5) which of P1's and P4's numbering is frozen; (6) the form of the interface I-8.

---

## 1. The small-field class $\mathbb R^{\rm sf}_k$ at $\lambda=\infty$

### 1.1 Constants and scales

Constants, in the order of P4 §6 [review]: $d,N$; $L$; $\gamma\in(0,\frac12)$ (P4 requires $0<\gamma<\min\{\frac{d-2}2,\frac12\}$, which is $(0,\frac12)$ for $d\ge3$) and $\alpha:=\frac{d-2}2-\gamma$; $\alpha_1\in(0,1-2\gamma)$; $\kappa$ large, then $M=L^m\ge M(\kappa)$ (ER-025); $c_8$ (small), $c_9$; $A_0,p_0,A_1,p_1$ (small-field radii); then the analytic constants $\alpha_0$ (small), $E_0$, $B$.

For a step index $j\ge1$ put $\xi_j=L^{-j}$ and $\varepsilon_j=\alpha_{0,k}\,\xi_j^{\alpha}$ with $\alpha_{0,k}=\alpha_0(1+\sum_{n\ge k}n^{-2})$ (P4 (H.1), p. 676; P1's printed $\sum_{n=-k}^\infty$ is a misprint, ER-018). The ratio $\varepsilon_k/\varepsilon_j=(1+O(1/k))\,s_{jk}^{\alpha}$.

Running coefficients $\beta_k,a_k,\nu_k$ ($\lambda_k=\infty$): P4 (H.1)–(H.2), (H.6): $\beta_k>BL^{k(d-2)}$, $0<\nu_k\le\bar\nu$ with $\bar\nu\le\frac78L^{-2}$, $a_k\in[\frac12,\frac32)$, and for $j\le k$ the "ideal flow matched at step $k$" of P1 (2.9)–(2.11), P4 (H.2):
$$\nu_j=\nu_k\,s_{jk}^2,\qquad a_j=a_k\frac{1-L^{-2k}}{1-L^{-2j}},\qquad(\lambda_j=\infty).$$
These $a_j$, $\nu_j$ are the coefficients of the connecting problem (P1 (2.6)); they are defined from the $k$-th ones and do not coincide with the actual earlier coefficients of the flow. (H.6): $\beta_k=\beta L^{k(d-2)}\gamma_k$, $\nu_k=\nu L^{2k}\delta_k$, and $\gamma_k^{\pm1},\delta_k^{\pm1}<\exp\big(c_8\sum_{j\le k}L^{-2\gamma j}\big)$. For $a_k$ see §3.1.

### 1.2 Domains

The domains are those of P1 §2, in the form of `BACKGROUND.md` §1.3 at $\lambda=\infty$. Let $\phi_k(\psi;h,a_k,\nu_k)$, $\alpha_k$ be the small solution of (EL) of `BACKGROUND.md` (I-1; the unique minimiser over $(S^{N-1})^{T_\eta}$ for real data). For $(\sigma,\varepsilon)$:

- $\Phi_k(\sigma,\varepsilon)$ (P1 (2.15) at $\lambda=\infty$): $(\phi,h)$ with $|\partial^\eta\phi|<\sigma\varepsilon$, $|\Delta^\eta\phi|<\sigma^2\varepsilon$, $|\alpha|<\sigma^2\varepsilon$ ($\alpha$ the multiplier, not $\frac\lambda2(|\phi|^2-1)$), $|\phi-h|<\sigma\varepsilon/\sqrt{\nu}$, $\big||h|^2-1\big|<\sigma^2\varepsilon^2/\nu$.
- $\Xi_k(\sigma,\varepsilon)$ (P1 (2.20)): $(\psi,h)$ with $(\phi_k(\psi;h,a_k,\nu_k),h)\in\Phi_k(\sigma,\varepsilon)$ and $|\psi-Q_k\phi_k|<\sigma^2\varepsilon$; $\Xi_k^c(\sigma,\varepsilon)$ (P1 (2.21)): the complex analytic extension, defined through $\tilde\Psi^c$ of I-1; for localization terms the local version $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$ of P3 §4 (neighbourhood of $X$ only; P4 (H.4)).
- The $\psi$-level domains $\Psi_j(\sigma,\varepsilon)$, $\bar\Psi_j(\delta)$ and their complex versions (P1 (3.13)–(3.19)): these are the data domains $\tilde\Psi,\tilde\Psi^c$ of `BACKGROUND.md` §1.3 (R1–R4, C1–C3) with $\delta=\sigma\varepsilon$.

Two facts connect them (both elementary or cited): (D1) $\Xi_j(\sigma,\varepsilon)\subset\Psi_j(3\sigma,\varepsilon)$ and the same for $\Xi_j^c$ (P1 Lemma 3.1, (3.16); proved in P1 pp. 121–122 by (3.1)–(3.12) [review]; at $\lambda=\infty$ the estimate of $\phi\cdot\partial\phi$ in (2.17)–(2.19) becomes exact, $\phi(x)\cdot(\phi(x')-\phi(x))=-\frac12|\phi(x')-\phi(x)|^2$, and the condition $\lambda_j\xi^2>\frac56$ disappears); (D2) $\bar\Psi^c_j(\delta,\varepsilon)\subset\Xi^c_j(1,\bar\varepsilon)$ if $\varepsilon+K_1\delta\le\bar\varepsilon$ (P1 (3.21); this is I-1 Theorem 5.2(3) of `BACKGROUND.md`). The chain of P1 Lemma 3.2 for $\psi^{(j)}_k$ (P1 (3.22)) is, at $\lambda=\infty$, I-2 Theorem 6.1(iv) of `BACKGROUND.md` together with (D1), (D2).

### 1.3 The hypotheses (P4 numbering; P1's in brackets)

Let $\rho_k$ be a function of $\psi_k:\Lambda_k\to\mathbb R^N$ (and of $h\in S^{N-1}$, $g$ with $\|g\|_{\ell^1}<1$). $\rho_k\in\mathbb R^{\rm sf}_k$ means:

**(H.1)** [P1 (H.1)] $\rho_k=\chi_k\exp[\mathscr A_k+\mathscr F_k]$, $\mathscr A_k=-\beta_kA_k(\psi_k,\phi_k;h,a_k,\nu_k)+\mathscr E_k(\psi_k,h)-E_k|T_1^{(k)}|$, with $A_k=\frac{a}2\|\psi-Q_k\phi\|_1^2+\frac12\|\partial^\eta\phi\|^2+\frac\nu2\|\phi-h\|^2$ at $\phi=\phi_k$, $|\phi|=1$; $\chi_k$ the characteristic function of $\Xi_k(1,\beta_k^{-1/2}p(\beta_k))$ (P4 p. 679); $\mathscr E_k$ real analytic on $\Xi_k(1,\varepsilon_k)$, $\mathscr F_k$ on $\Xi_k(1,\varepsilon_k)\times\{\|g\|_{\ell^1}<1\}$.

**(H.2)** [P1 (H.2),(H.3)] $\mathscr E_k(\psi_k,h)=\sum_{j=1}^k\mathscr E^{(j)}(\psi_k^{(j)}(\psi_k,h),h)$, $\mathscr E^{(j)}(\psi_j,h)=\sum_{y\in\Lambda_j}\mathscr E^{(j)}(y;\psi_j,h)$, with $\mathscr E^{(j)}(y;\cdot)$ analytic on $\Xi_j^c(1,\varepsilon_j)$. Here $\psi^{(j)}_k$ is the minimiser of the connecting problem (P1 (2.6), formula (2.14)), i.e. $\psi^{(j)}_k=\texttt{composeField}$ of I-2.

**(H.3)** [P1 (H.4)] Invariance: $\mathscr E^{(j)}(y;R\psi,Rh)=\mathscr E^{(j)}(y;\psi,h)$ for $R\in O(N)$ (also on the complex extension, for $R\in SO(N,\mathbb C)$ where defined), and $\mathscr E^{(j)}(ry;r\psi,h)=\mathscr E^{(j)}(y;\psi,h)$ for lattice Euclidean transformations $r$ (translations, reflections, permutations of coordinates). Hence for constant $\psi$ the value is independent of $y$: $\mathscr V^{(j)}(\psi,h)$ (P1 (2.25)).

**(H.4)** [P1 (H.5)] Localization: $\mathscr E^{(j)}(y;\psi,h)=\sum_{X\in\mathcal D_j,X\ni y}\mathscr E^{(j)}(y,X;\psi,h)$, each term depending only on $(\psi|_X,h)$, analytic on $\Xi^c_j(\mathbb B_j(X);1,\varepsilon_j)$, $O(N)$- and Euclid-invariant termwise, and
$$|\mathscr E^{(j)}(y,X;\psi+\psi',h+h')|\le E_0\,e^{-\kappa d_j(X)}.$$
The terms are defined on finite subsets of $\mathbb Z^d$ and transported to tori (`LF` roadmap §3.5; torus independence for non-winding $X$ is then automatic, ER-010).

**(H.5)** [P1 (H.6),(H.7)] Renormalization conditions at $(e_1,e_1)$, $e_1=(1,0,\dots,0)$, with $\mathscr V^{(j)}(\psi,b):=\mathscr V^{(j)}(\psi,\nu_jh)$ written in the variable $b=\nu_jh$: for $j\le k$
$$\mathscr V^{(j)}(e_1,\nu_je_1)=0,\qquad \partial_b\mathscr V^{(j)}(e_1,\nu_je_1)\cdot e_1=0\ \ (\nu_j>0),\qquad \sum_{y'}\partial_{\psi(y')}\mathscr E^{(j)}(y;e_1,\nu_je_1)\cdot e_1=0,$$
$$\sum_{x\in\mathbb Z^d}\operatorname{tr}\Big[\lim_{T\to\mathbb Z^d}\Big(\tfrac{\partial^2}{\partial\psi(x)\partial\psi(0)}\mathscr E^{(j)}\Big)(e_1,\nu_je_1)\,(e_2\otimes e_2)\Big]\,|x|^2=0 .$$
P1's condition "$\partial_h\mathscr V\cdot e_1=0$" is $\nu_j\,\partial_b\mathscr V\cdot e_1=0$; it is void at $\nu_j=0$ (see §2.6 and §3.5). P4 states (H.5) for every $j\le k$ but imposes it only on the new term (p. 678); the older terms inherit it from the step at which they were created.

**(H.6)** [P1 (H.8)] The coefficient bounds of §1.1.

**(H.7)** [P1 (H.9)] $\mathscr F_k(\psi_k,h,g)=\langle g,\phi_k\rangle_1+\sum_{j=1}^k\mathscr F^{(j)}(\psi_k^{(j)}(\psi_k,h),h,g)$, $\mathscr F^{(j)}(\psi_j,h,g)=\langle g,\mathscr M^{(j)}(\cdot;\psi_j,h,g)\rangle_1$, $\mathscr M^{(j)}(x;\cdot)$ analytic on $\Xi_j^c(1,\varepsilon_j)\times\{\|g\|_{\ell^1}<1\}$, $O(N)$-equivariant ($\mathscr M(x;R\psi,Rh,Rg)=R\mathscr M$), Euclid-covariant, localized with $|\mathscr M^{(j)}(x,X;\cdot)|<c_9\,\xi_j^{\frac{d-2}2+\gamma-\alpha_1}e^{-\kappa d_j(X)}$. (P1 (H.9) writes $\beta_{j-1}^{-1/2}\mathscr F^{(j)}$ with $|\mathscr M|\le M_0\xi^{\gamma-2\alpha_1}$; the two normalizations are related by BIG §2.4, ER-011, ER-012.)

**Space.** $\mathbb R^{\rm sf}_k(\beta,a,\nu;B,\bar\nu;\mathsf c)$, $\mathsf c=(L,M,\kappa,\gamma,\alpha_1,\alpha_0,E_0,c_8,c_9,\ldots)$: the families over admissible tori satisfying (H.1)–(H.7) and $\beta_k>B L^{k(d-2)}$, $0<\nu_k\le\bar\nu$ (P4 (1.4)). It is a predicate on families indexed by tori; the localized terms are given on finite subsets of $\mathbb Z^d$.

### 1.4 What is not in the class

Large fields: the class is the whole-lattice small-field class. P5's $\mathbb R_k$ (Def-7) restricts to $Z_k^c$ and replaces (H.2)'s $\mathscr E^{(j)}$ by the form with the extra antisymmetric sum (P5 (1.8)); that sum is the term $A_y$ of §2 (the two coincide up to irrelevant terms, §2.5). P4 says explicitly that the generalization of its theorems to small-field subdomains is easy and deferred (pp. 675–676, 682); it is I-8's "general form" (P5 Props 3.1–3.4).

### 1.5 What changes at $\lambda=\infty$

1. $\alpha$ is the Lagrange multiplier of $|\phi|=1$; $\Phi_k$ has $|\alpha|<\sigma^2\varepsilon$ and $\lambda_k$ does not appear. The characteristic function $\chi_k$ of P1 (2.30) has no $\alpha$-condition other than this one; $\alpha_k$ is determined by $\phi_k$.
2. $\mathscr E^{(j)}$ with $\lambda=\infty$: in P1 (2.17)–(2.19) the bound for $\phi\cdot\partial\phi$ is exact.
3. The $\lambda$-equation of the renormalization system is vacuous: $d_{k+1}$ drops out of (5.10) (the term $\frac1{2\lambda}(2\beta^{-1}b-\beta^{-1}d)\|\alpha^{(1)}\|^2$ is multiplied by $\lambda^{-1}$), $a_{21}=0$, $a_{11}=a$ (§3).
4. In the one-point/two-point part (P9) the longitudinal main term vanishes exactly (`CORRELATIONS.md` §2.4).
5. The second-order expansion of $\phi_{k+1}(e_1+\psi',\nu e_1)$ used in P4 (5.6)–(5.10): I re-derived $\phi^{(1)},\alpha^{(1)}$ and $e_1\cdot\phi^{(2)}$ directly from (EL) at $\lambda=\infty$ in §3.3; they reproduce the quadratic form (5.11) with $1/\lambda=0$.
6. At $\lambda=\infty$ the first step $k=0\to1$ is a sphere-chart computation (P4 (2.42)–(2.50) is written for $\lambda_0$ uniform); it is LF-6, not repeated here (§5.5).

---

## 2. I-6: renormalization analysis (P1 §3, Prop 3.10, Cor 3.11)

### 2.1 What is claimed, and what it is used for

P1 shows that the localization bound alone gives only $|\mathscr E_k|\le(L^d-1)^{-1}E_0K_0|T_1|$, proportional to the volume of the *original* lattice (P1 p. 118), because each scale $j$ contributes $E_0K_0$ per site of $\Lambda_j$ and there are $L^{(k-j)d}|T_1^{(k)}|$ such sites. The renormalization conditions (H.5) make the contribution of scale $j$ evaluated on $\psi^{(j)}_k$ smaller by $s^{d+\alpha_3}$ per site, which sums to a bound by the *current* volume.

**Use.** (U1) LF-3/LF-4 (P5 Thm 1, P7 Thm 2): the main-action cancellation and the localized differences of $\mathscr E_k$ between small-field domains (P7 (3.24)–(3.25), via P1 (3.127)): this needs the per-site statement (a) of Theorem 2.1, not only the global bound. (U2) LF-8 and Root-F: the bound $|e^{\mathscr E_k}|\le e^{C_6E_0|T_1^{(k)}|}$ against the large-field gain $e^{-p_2|Z|}$. (U3) I-7: (H.5) is what Theorem 2.1 consumes, and I-7 is what produces (H.5) at each step. The one-step theorem I-9 itself does not consume Theorem 2.1 (its analytic bounds need only the domain chain, P4 (5.15)–(5.17)); the roadmap's single milestone SF therefore contains I-6 as a separate output, not as a step of I-9.

### 2.2 Statement

Fix $d,N,L,M,\kappa,\gamma\in(0,\frac12)$, $\alpha=\frac{d-2}2-\gamma$, $\alpha_1\in(0,1-2\gamma)$ and put
$$\alpha_2:=2(1-\gamma),\qquad \alpha_3:=1-2\gamma-\alpha_1>0 .$$
(P1's $\alpha_3=2(\gamma_0-\gamma)-\alpha_1$ with $\gamma_0=\frac12$, P1 pp. 145–147; $4+2\alpha=d+\alpha_2$ and $3-\alpha_1+2\alpha=d+\alpha_3$.) Let $0\le j\le k$, $s=s_{jk}$, and let $(\psi,h)$ be a complex configuration on $\Lambda_j$ with the following data, written $b:=\nu_jh$, $\sigma:=C_0s$ ($C_0\ge3$, P1 Lemma 3.2), $\varepsilon:=\varepsilon_k$, $R:=\varepsilon/\varepsilon_j\le1$:

- (Σ1) $(\psi,h)\in\Psi_j^c(\sigma,\varepsilon)$ (P1 (3.14));
- (Σ2) the second-difference bound $|\partial^2\psi(x)|\le K_\Sigma\,s^{2-\alpha_1}\varepsilon$ for all $x$ (P1 (3.107)).

**Theorem 2.1 (I-6, local form).** Assume (H.2)–(H.4) and the first three conditions of (H.5) and the fourth (second moment) for the terms of scale $j$, with constants $E_0,\kappa$. There are $s_*>0$ and $C$, depending only on $(d,N,L,M,\kappa,\gamma,\alpha_1,K_\Sigma)$, such that for $s\le s_*$, all $y\in\Lambda_j$ and all data as above:

(a) *(per-site decomposition)*
$$\mathscr E^{(j)}(y;\psi,h)=\mathscr V^{(j)}(\psi(y),b)+A_y(\psi)+\mathcal I^{(j)}(y;\psi,h),\qquad A_y(\psi):=\tfrac12\sum_{x}a^{(j)}(x-y)\big(\psi(x)\cdot\psi(x)-\psi(y)\cdot\psi(y)\big),$$
where $a^{(j)}(z):=\sum_{X\ni0,z}\partial_{\psi(z)}\mathscr E^{(j)}(0,X;e_1,\nu_je_1)\cdot e_1$ is even in $z$ and rapidly decaying, and
$$|\mathscr V^{(j)}(\psi(y),b)|\le CE_0\,\sigma^4R^2,\qquad |\mathcal I^{(j)}(y;\psi,h)|\le CE_0\,\sigma^{3-\alpha_1}R^2 .$$
(b) *(torus sum)* $\sum_{y\in\Lambda_j}A_y(\psi)=0$ on every torus, hence $|\mathscr E^{(j)}(\psi,h)|\le CE_0|\Lambda_j|\sigma^{3-\alpha_1}R^2$.

**Corollary 2.2 (I-6, global form; P1 Cor 3.11, (3.131)).** Assume in addition that $\psi=\psi^{(j)}_k(\psi_k,h)$ with $(\psi_k,h)\in\Xi_k^c(1,\varepsilon_k)$ and let $n_1$ be the smallest integer with $L^{-n_1}\le s_*$. Then (Σ1), (Σ2) hold for $k-j\ge n_1$ and
$$|\mathscr E_k(\psi_k,h)|\le C_6\,E_0\,|T^{(k)}_1|,\qquad C_6=C\Big(\frac{1}{1-L^{-\alpha_3}}+K_0L^{n_1d}\Big),$$
uniformly in $k$, $\beta$, $\nu$, and the torus.

The theorem is stated with premises that are genuine: (Σ1) is I-2 Theorem 6.1(iv) with (D1); (Σ2) is the Hölder bound I-1(e) with one fixed exponent (ER-016; `BACKGROUND.md` §5.2 item 3 and (e)); everything else is a hypothesis on $\mathscr E^{(j)}$ of the form of (H.2)–(H.5). No step of the proof is a hypothesis.

### 2.3 Proof

Throughout $C$ denotes constants depending only on the listed parameters.

**Step 0: geometry (cited).** For $X\in\mathcal D_j$ and $x\in X$ there is a lattice path $\Gamma_{y,x}\subset X$ of length $|\Gamma_{y,x}|\le 2dLM+dM\,d_j(X)$ (P1 (3.54) [review]); the number of sites is bounded by $|X|\le(3LM)^d(1+d_j(X))$ (P6 (4.11), proved pp. 25–26, ER-060), so $K_0':=\sup_y\sum_{X\ni y}(1+d_j(X))^6e^{-(\kappa-\kappa_0)d_j(X)}\cdot|X|^2<\infty$ for $\kappa\ge\kappa_0+7$ (PE-L (G2)). For $(\psi,h)$ as in (Σ1) and $x\in X$:
$$|\psi(x)-\psi(y)|\le|\Gamma_{y,x}|\,\sigma\varepsilon\le C(1+d_j(X))\,\sigma\varepsilon.\tag{2.1}$$

**Step 1: the tail $d_j(X)>d_*$ (proved).** Let $d_*:=c\,\min\{\varepsilon_j,\delta_0\}/(M\sigma\varepsilon)$ with $\delta_0=\sigma_1\varepsilon_{j+1}$ (P1 (3.59)); then $d_*\ge c'(\sigma R)^{-1}$. For $d_j(X)>d_*$ use the crude bound $|\mathscr E(y,X;\psi)-\mathscr E(y,X;\psi(y))|\le2E_0e^{-\kappa d_j(X)}$ (the analytic extension to constant configurations is inside the domain by (D2)); the part of $A_y$ coming from such $X$ is bounded by $CE_0\varepsilon_j^{-1}e^{-\kappa d_j(X)}$ times $|\psi(x)\cdot\psi(x)-\psi(y)\cdot\psi(y)|\le2\sigma^2\varepsilon$ (by (Σ1): $|\psi\cdot\psi-1|<\sigma^2\varepsilon$ at every site). Summed over $X\ni y$ with $d_j(X)>d_*$: $\le CE_0e^{-(\kappa-\kappa_0)d_*}\le CE_0e^{-c''/(\sigma R)}\le CE_0(\sigma R)^3\le CE_0\sigma^{3-\alpha_1}R^2$ (as $\sigma R\le1$ and $e^{-c/t}\le Ct^3$). From now on $d_j(X)\le d_*$ and every set $X$ is "small": the path bound (2.1) gives $|\psi(x)-\psi(y)|\le C(1+d_j(X))\,\sigma R\,\varepsilon_j\le c\,\varepsilon_j$, inside the analyticity radius.

**Step 2: the invariant reduction and the base point (proved).** Fix $y$ and $X\ni y$ with $d_j(X)\le d_*$. By (H.3) we may rotate: choose $R_y\in SO(N,\mathbb C)$ with $R_y\psi(y)=u_ye_1$, $u_y=\sqrt{\psi(y)\cdot\psi(y)}$ (analytic in $\psi(y)$ near the unit sphere; this is the content of $U,V,W^2$ in P1 (3.24)–(3.37)). Then $|u_y^2-1|<\sigma^2\varepsilon$, and $b':=R_yb$ satisfies, by (Σ1) ($|\nu_j(1-\psi_0\cdot h)|<\sigma^2\varepsilon^2$, $|\nu_j(h\cdot h-1)|<\sigma^2\varepsilon^2$) and $\nu_j=\nu_ks^2\le s^2\le\sigma^2$ (this is the assumption (3.41) of P1; here automatic):
$$|b'_1-\nu_j|\le C\sigma^2\varepsilon,\qquad |b'_\perp|\le C\sqrt{\nu_j}\,\sigma\varepsilon\le C\sigma^2\varepsilon,\tag{2.2}$$
($\perp$ = components $2,\dots,N$). So after the rotation the base point $(u_ye_1,b')$ is within $C\sigma^2\varepsilon$ of the *reference point* $P_0:=(e_1,\nu_je_1)$ in the variables $(u,b)$, and $\delta(x):=R_y(\psi(x)-\psi(y))$ has, by (Σ1) and (2.1), $|\delta(x)|\le C(1+d_j(X))\,\sigma R\,\varepsilon_j$, $\delta_1(x)=\tfrac12\big(\psi(x)\cdot\psi(x)-\psi(y)\cdot\psi(y)\big)-\tfrac12|\delta_\perp(x)|^2+O(\sigma^2\varepsilon\,|\delta_\perp|^2+|\delta_\perp|^4)$ (because $\psi\cdot\psi$ is rotation invariant and $\psi_1=\sqrt{\psi\cdot\psi-|\psi_\perp|^2}$).

**Step 3: the potential (proved; P1 Prop 3.4, Cor 3.5).** $\mathscr V^{(j)}(\psi(y),b)=\sum_{X\ni y}\mathscr E^{(j)}(y,X;\text{const }\psi(y),b)$ is, by (H.3) and the reduction of Step 2, a function $f(u,v,w)$ of the three invariants
$$u=\sqrt{\psi\cdot\psi},\qquad v=\frac{\psi\cdot b}{u},\qquad w=b\cdot b-v^2$$
(P1 (3.28), with $v=\nu\psi_0\cdot h$, $w=\nu^2(|h|^2-(\psi_0\cdot h)^2)$), analytic in the polydisc $\{|u-1|<\delta_0,\ |v-\nu_j|<\delta_0^2,\ |w|<\delta_0^2\}$ for $\delta_0=\sigma_1\varepsilon_{j+1}$ (P1 Lemma 3.3 [review]: $(U,V,W^2)$ map $\Psi_{\rm const}^c$ into it; domain (D2)), bounded there by $E_0K_0$ by (H.4) and $K_0=\sum_{X\ni y}e^{-\kappa d_j(X)}$. By (H.5) (first three conditions) $f(1,\nu_j,0)=\partial_uf=\partial_vf=0$ there ($\partial_vf=\partial_b\mathscr V\cdot e_1$). Hence, by Taylor in $(u-1,v-\nu_j,w)$ and the Cauchy estimates on the polydisc,
$$|f|\le CE_0K_0\Big[\Big(\tfrac{|u-1|}{\delta_0}\Big)^2+\Big(\tfrac{|v-\nu_j|}{\delta_0^2}\Big)^2+\tfrac{|w|}{\delta_0^2}\Big].$$
By (Σ1): $|u-1|\le C\sigma^2\varepsilon$, $|v-\nu_j|\le C\sigma^2\varepsilon^2$, $|w|\le C\sigma^4\varepsilon^2$; with $\delta_0\asymp\varepsilon_j$ this is $\le CE_0\sigma^4R^2$. This is (a) for $\mathscr V$.

**Step 4: second-order Taylor expansion with remainder (proved).** For $X$ small, consider $\tau\mapsto F_X(\tau):=\mathscr E(y,X;\psi(y)+\tau(\psi-\psi(y))|_X,b)$. By the local analyticity domain and (2.1) it is analytic for $|\tau|\le r_X:=c/((1+d_j(X))\sigma R)\ge2$ (the conditions defining $\tilde\Psi^c$ scale linearly in $\tau$ on the displacement, and the displacement is $\le C(1+d)\sigma R\varepsilon_j$), with $|F_X|\le E_0e^{-\kappa d_j(X)}$. Cauchy in $\tau$:
$$\Big|F_X(1)-F_X(0)-F_X'(0)-\tfrac12F_X''(0)\Big|\le CE_0e^{-\kappa d_j(X)}\big((1+d_j(X))\,\sigma R\big)^3 .$$
Summing over $X\ni y$ with the weights of Step 0, the total remainder is $\le CE_0\sigma^3R^3\le CE_0\sigma^{3-\alpha_1}R^2$. The terms $F_X'(0)$, $F''_X(0)$ are, in the rotated frame, with the tensors at the base point $(u_ye_1,b')$:
$$F_X'(0)=\sum_{x\in X}\partial_{\psi(x)}\mathscr E\cdot\delta(x),\qquad F_X''(0)=\sum_{x,x'}\delta(x)\cdot\partial^2_{\psi(x)\psi(x')}\mathscr E\cdot\delta(x').$$

**Step 5: tensors at the reference point, the identity (WI), and the vanishing of the marginal term (proved).** At $P_0=(e_1,\nu_je_1)$, with $\psi\equiv e_1$ on $X$, the stabilizer of $(e_1,\nu_je_1)$ in $O(N)$ is $O(N-1)$ (acting on $e_2,\dots,e_N$). By (H.3) (termwise invariance) the derivatives at $P_0$ have the form
$$\partial_{\psi(x)}\mathscr E=a_X(x)\,e_1,\qquad \partial_{\psi(x)}\partial_{\psi(x')}\mathscr E=A_X(x,x')\,e_1e_1^{\!\top}+B_X(x,x')\,(I-e_1e_1^{\!\top}),\qquad \partial_{\psi_i(x)}\partial_{b_{i'}}\mathscr E=m_X(x)\,\delta_{ii'}\ (i,i'\ge2)$$
(for $N=2$ the reflection $e_2\mapsto-e_2$ gives the same shapes). Write $a=\sum_Xa_X$, $B=\sum_XB_X$, $m=\sum_Xm_X$, all for the fixed centre $y$; $a(z)$ is even by the reflection through $y$.

*Perturbing the base point.* Replacing the base $(u_ye_1,b')$ by $P_0$ changes each tensor by a Cauchy remainder of relative size $|u_y-1|/\delta_0+|b'-\nu_je_1|/\delta_0^2\cdot\varepsilon\le C\sigma^2\varepsilon/\varepsilon_j=C\sigma^2R$. Applied to the first-order term (size $\varepsilon_j^{-1}E_0\cdot\sigma R\varepsilon_j$, with $\delta(x)\sim\sigma R\varepsilon_j$) it gives $CE_0\sigma^3R^2$; applied to $F_X''(0)$ (size $E_0(\sigma R)^2$) it gives $CE_0\sigma^4R^3$. The dependence on $b'_\perp$ of the first derivative (the vector $\partial_{\psi(x)}\mathscr E$ acquires a component $m_X(x)b'_\perp$) contributes $|m||b'_\perp||\delta_\perp|\le CE_0\varepsilon_j^{-2}\sigma^2\varepsilon\cdot\sigma\varepsilon=CE_0\sigma^3R^2$ by (2.2). All of this is irrelevant.

*First-order term.* By Step 2, $\sum_xa(x)\delta_1(x)=\frac12\sum_xa(x-y)(\psi\cdot\psi(x)-\psi\cdot\psi(y))-\frac12\sum_xa(x-y)|\delta_\perp(x)|^2+\text{(irrelevant)}$. The first sum is $A_y(\psi)$ (with the full sum over $X$ in $a^{(j)}$; the part of it from $d_j(X)>d_*$ was bounded in Step 1).

*Second-order term.* The $(1,1)$ and $(1,\perp)$ parts of $F''_X(0)$ involve $\delta_1$, which is $O(\sigma^2\varepsilon+|\delta_\perp|^2)$, hence are of order at least $\sigma^3R^3$ (cubic in the small displacement): irrelevant. What remains is
$$Q_y:=\tfrac12\sum_{x,x'}B(x,x')\,\delta_\perp(x)\cdot\delta_\perp(x')-\tfrac12\sum_xa(x-y)|\delta_\perp(x)|^2 .$$

*The identity (WI).* Let $\mathcal A$ be the generator of rotations in the $(e_1,e_2)$-plane, $\mathcal Ae_1=e_2$, $\mathcal Ae_2=-e_1$. Invariance of the single term $\mathscr E(y,X;\cdot)$ gives, for all $(\psi,b)$, $\sum_x\partial_{\psi(x)}\mathscr E\cdot\mathcal A\psi(x)+\partial_b\mathscr E\cdot\mathcal Ab=0$. Differentiate in the direction $\chi=\delta_{x'}e_2$ at $\psi\equiv e_1$, $b=\nu_je_1$ (so $\mathcal A\psi(x)=e_2$, $\mathcal Ab=\nu_je_2$, $\mathcal Ae_2=-e_1$):
$$\sum_xB_X(x',x)\;-\;a_X(x')\;+\;\nu_j\,m_X(x')=0\qquad\text{for every }x'\ \text{and every }X.\tag{WI}$$
Using $\delta_\perp(x)\cdot\delta_\perp(x')=\frac12\big(|\delta_\perp(x)|^2+|\delta_\perp(x')|^2-|\Theta(x)-\Theta(x')|^2\big)$ with $\Theta=\psi_\perp$ (in the rotated frame) and the symmetry $B(x,x')=B(x',x)$, then (WI):
$$Q_y=-\frac{\nu_j}2\sum_xm(x)|\delta_\perp(x)|^2-\frac14\sum_{x,x'}B(x,x')\,|\Theta(x)-\Theta(x')|^2 .\tag{2.3}$$
*First term of (2.3).* $|m|\le CE_0\varepsilon_j^{-2}$ (Cauchy in $(\psi,b)$, polydisc radii $\asymp\varepsilon_j$ in $\psi$ and $\asymp\delta_0^2/\varepsilon\asymp\varepsilon_j$ in $b$) and $|\delta_\perp|\le C\sigma R\varepsilon_j$, so it is $\le C\nu_jE_0\sigma^2R^2\le CE_0\sigma^4R^2$ because $\nu_j\le\sigma^2$.
*Second term of (2.3).* In the rotated frame $|\Theta(x)-\Theta(x')|^2=|\psi(x)-\psi(x')|^2-\big(\hat\psi(y)\cdot(\psi(x)-\psi(x'))\big)^2$ and the subtracted square is of fourth order ($\hat\psi(y)\cdot(\psi(x)-\psi(x'))=\frac12(\psi\cdot\psi(x)-\psi\cdot\psi(x'))+$ quadratic terms, size $\le C\sigma^2\varepsilon$ and $C(\sigma R\varepsilon_j)^2$): irrelevant. For the remaining $|\psi(x)-\psi(x')|^2$, expand along the path: with $z=x-x'$, $|\psi(x')-\psi(x)|^2=|z\cdot\nabla\psi(x)|^2+r$, where by (Σ2) $|r|\le C\big(|z|^3|\nabla\psi||\partial^2\psi|+|z|^4|\partial^2\psi|^2\big)\le C(1+d)^4\,\sigma\varepsilon\cdot s^{2-\alpha_1}\varepsilon$. With the weights $|B(x,x')|\le CE_0\varepsilon_j^{-2}e^{-\kappa d}$ this is $\le CE_0\sigma\,s^{2-\alpha_1}R^2\le CE_0\sigma^{3-\alpha_1}R^2$. The leading part is
$$-\frac14\sum_{x'}\sum_{z}B(x'+z,x')\,|z\cdot\nabla\psi(x')|^2 .$$
*This is where (H.5)(4) enters.* The tensor $\sum_{x'}B(x'+z,x')$ is, after summing over the centre, $G_{22}$ of (H.5)(4): by translation invariance $S^{(y)}_{\mu\nu}:=\sum_{x,x'}B(x,x')(x-x')_\mu(x-x')_\nu$ does not depend on $y$ and equals $\sum_zG_{22}(z)z_\mu z_\nu$ with $G_{22}(z)=\sum_{y}\partial^2\mathscr E(y)/\partial\psi_2(z)\partial\psi_2(0)$. The sum over $X\ni y$ of $\mathscr E(y,X)$ is invariant under the point group at $y$, so $S^{(y)}_{\mu\nu}=\frac1d\delta_{\mu\nu}\sum_zG_{22}(z)|z|^2=0$ by (H.5)(4). Therefore the leading part equals $-\frac14\sum_{x'}\sum_{\mu\nu}S_{\mu\nu}\partial_\mu\Theta\cdot\partial_\nu\Theta=0$ exactly (before the tail $d>d_*$, which is irrelevant by Step 1; all sums over $X$ are absolutely convergent).

Collecting Steps 1–5 gives (a). The potential bound is Step 3; the function $a^{(j)}$ is even and summable. For (b): on a torus $\sum_y\sum_xa(x-y)(\psi\cdot\psi(x)-\psi\cdot\psi(y))=0$ because $a(z)=a(-z)$ (interchange $x,y$). Hence $\mathscr E^{(j)}(\psi,h)=\sum_y\big[\mathscr V+\mathcal I\big]$ and $|\mathscr E^{(j)}|\le C E_0|\Lambda_j|(\sigma^4R^2+\sigma^{3-\alpha_1}R^2)$. $\square$

**Proof of Corollary 2.2.** By I-2 Theorem 6.1(iv) and (D1), (Σ1) holds for $\psi^{(j)}_k$ with $\sigma=C_0s_{jk}$; (Σ2) is I-1(e) and (2.14) of P1. For $n=k-j\ge n_1$, $s=L^{-n}$, $R=\varepsilon_k/\varepsilon_j\le Cs^\alpha$, $|\Lambda_j|=L^{nd}|T^{(k)}_1|$ and $\sigma^{3-\alpha_1}R^2\le CL^{-n(3-\alpha_1+2\alpha)}=CL^{-n(d+\alpha_3)}$. Hence $\sum_{j\le k-n_1}|\mathscr E^{(j)}|\le CE_0|T_1^{(k)}|\sum_{n\ge n_1}L^{-n\alpha_3}$. For $k-n_1<j\le k$ use the crude bound $|\mathscr E^{(j)}(\psi,h)|\le E_0K_0|\Lambda_j|$ (P1 (2.29)), $\sum_{n<n_1}L^{nd}$ times $|T^{(k)}_1|$. $\square$

### 2.4 What was used and what is only cited

Proved here: the potential bound (Step 3, from (H.5) and Cauchy), the Taylor remainder (Step 4), the identity (WI) and the exact vanishing of the leading gradient term (Step 5), the tails and the summation. Cited: Lemma 3.1 (D1), the path and volume bounds (Step 0), P1 Lemma 3.3 ($U,V,W^2$ into the polydisc), the rotation to $e_1$ for complex data (a complex orthogonal matrix exists when $\psi\cdot\psi\neq0$; the formulas in $U,V,W^2$ avoid choosing it), I-1(e), I-2. UNCERTAIN: Step 0's constant $K_0'$ needs $\kappa\ge\kappa_0+7$ in this formulation (P1 loses $e^{d}$ only); this is a harmless change of the lower bound on $\kappa$.

### 2.5 Relation to P1's proof and to P5 (1.8)

(i) P1 expands to fourth order and treats third order crudely (3.103); with a second-order expansion and a third-order remainder the same exponents result, because the third-order term carries $\sigma^3R^3\le\sigma^{3-\alpha_1}R^2$. (ii) P1's marginal coefficient is $\frac12(v_0-v_1+\nu v_2)^{(\infty)}$, killed through the Ward identity (3.122)–(3.125) [review] and (H.5)(4) (ER-023). In the present form the Ward identity is (WI), a one-line consequence of invariance; it gives the transverse gradient coefficient as $-\frac14\sum_zG_{22}(z)|z|^2/d$ up to the $\nu_j$-term in (2.3), so (H.5)(4) as stated (only the $e_2\otimes e_2$ component) suffices, and (H.5)(3) (radial first derivative) is needed only for the potential. (iii) $A_y$ is the combination of the $v_1$ and $v_2$ antisymmetric terms of P5 (1.8) at the reference point: there $\partial_{\psi(x)}\mathscr E=a(x)e_1$ and the two terms ($v_1\psi$ and $v_2b$ are both parallel to $e_1$) cannot be told apart, so $a=v_1+\nu_jv_2$ at that point. $A_y$ itself is of size $E_0\sigma^2R$, larger than the irrelevant bound; it must cancel in the sum. On a subdomain the sum of $A_y$ over $y$ does not vanish, which is the reason for P5's second sum in (1.8). (iv) The role of $\gamma_0=\frac12$: the third term $\sigma s^{2-\alpha_1}R^2$ in Step 5 has exponent $d+1-2\gamma-\alpha_1$, which is $d+\alpha_3$ exactly when the bound on $\partial^2\psi$ is $s^{2-\alpha_1}$; the improvement to $\gamma_0=1$ mentioned by P1 (p. 145) would need a symmetry analysis of the second-derivative term; not needed.

### 2.6 Remarks on the hypotheses

1. *$\nu_j=0$.* If $\nu_k=0$ the field $b$ is absent, the $b$-conditions are void and $\mathscr V$ depends on $u$ only; the proof is the same with $v,w$ dropped.
2. *Where the hypotheses on $\mathscr E^{(j)}$ come from.* (H.5) for $j\le k-1$ is inherited from earlier steps; I-7 produces it for the new term. (H.5)(4) is a limit along tori; its existence (ER-010) is part of the torus-independence of (H.4).
3. *Complex data.* All steps use only analytic functions of $U,V,W^2$ and Cauchy estimates; the real case is a special case.

---

## 3. I-7: the RG equations at $\lambda=\infty$ (P4 Prop 5.1, (5.31)–(5.33))

### 3.1 The step and the unknowns

Fix the data of step $k\to k+1$: $\beta=\beta_k$, $a_k$, $\nu_k$, the kernel constant $a$ (P4's $a\in(1,\frac32)$, optimal $a=(1-L^{-2})^{-1}$), and $\mathscr E_k^{(j)}$, $j\le k$. Unrenormalized coefficients (P4 (2.9), (3.1)):
$$\beta_{k+1,u}=\beta_kL^{d-2},\qquad a_{k+1,u}=\frac{a\,a_k}{a_k+aL^{-2}},\qquad \nu_{k+1,u}=\nu_kL^2 .$$
Five constants $\zeta,b,c,d,e$ (P4 (4.1)): $\theta=z_{k+1}\psi_{k+1}$ with $z=1+\zeta$,
$$\beta_{k+1,u}=\beta_{k+1}+b,\quad \beta_{k+1,u}a_{k+1,u}=\beta_{k+1}a_{k+1}+c,\quad \frac{\beta_{k+1,u}}{\lambda_{k+1,u}}=\frac{\beta_{k+1}}{\lambda_{k+1}}+\frac{d}{\lambda_{k+1}},\quad \beta_{k+1,u}\nu_{k+1,u}=\beta_{k+1}\nu_{k+1}+\nu_{k+1}e .$$
At $\lambda=\infty$ the third relation is $0=0$: $d$ does not occur anywhere (it multiplies $\lambda^{-1}$ in (5.10), the second term of $a_{11}$ etc.). Put $\xi_1=\zeta/\varepsilon_{k+1}$, $\xi_2=e/\beta$, $\xi_3=b/\beta$ (P4 (5.2), $\beta=\beta_{k+1}$), $\xi=(\xi_1,\xi_2,\xi_3)\in\mathbb C^3$ with the sup norm. Then (P4 (5.28))
$$\beta_{k+1}=\frac{\beta_kL^{d-2}}{1+\xi_3},\qquad \nu_{k+1}=\nu_kL^2\frac{1+\xi_3}{1+\xi_2}.$$

**The two supplementary choices.** (i) *Free flow* (P4 (5.20), the case proved in Prop 5.1): $c=a_{k+1}b$, equivalently $a_{k+1}=a_{k+1,u}$; $a_k=a\frac{1-L^{-2}}{1-L^{-2k}}$ exactly, a deterministic sequence in $(\frac12,\frac32)$ (decreasing to $a(1-L^{-2})$). (ii) *P5–P7's choice* $c=0$ (with $d=b$, i.e. also $\lambda_{k+1}=\lambda_kL^2$, vacuous here): from $\beta_{k+1,u}a_{k+1,u}=\beta_{k+1}a_{k+1}$,
$$a_{k+1}=(1+\xi_3)\,a_{k+1,u}\qquad(\text{P4 (5.34)}).$$
Write both as $a_{k+1}=(1+\xi_3)^{1-\theta_c}a_{k+1,u}$, $\theta_c\in\{1,0\}$. P4 p. 717 states that Proposition 5.1 holds for $c=0,d=0$ "without any changes" except (5.28)–(5.34), and that mixed choices (e.g. $c=0,d=b$) work; the statement of Prop 5.1 itself covers $c=ab$, $d=b$. For (ii), P5 Thm 1 and P6 Thm 1 quote (1.8)–(1.9) of P4 with $c_{k+1}=0$, $d_{k+1}=b_{k+1}$ (BIG §7 item 13, ER-067): since $d$ is vacuous at $\lambda=\infty$, this is the case $c=0$.

*The sequence $a_k$ under (ii).* Let $\varphi(x)=ax/(x+aL^{-2})$ and $a_k^f=a\frac{1-L^{-2}}{1-L^{-2k}}$ (so $a^f_{k+1}=\varphi(a^f_k)$). Put $r_k=a_k/a^f_k$. Since $\varphi(tx)/\varphi(x)=t\frac{x+aL^{-2}}{tx+aL^{-2}}$ lies between $\min(1,t)$ and $\max(1,t)$, $r_{k+1}=(1+\xi_3^{(k)})\varphi(r_ka_k^f)/\varphi(a^f_k)$ gives $|\log r_{k+1}|\le|\log r_k|+|\log(1+\xi_3^{(k)})|$, hence $|\log r_k|\le\sum_{i<k}|\log(1+\xi_3^{(i)})|$. Moreover the factor $\varphi(tx)/\varphi(x)$ has $t$-log-derivative $aL^{-2}/(x+aL^{-2})\le\theta_*:=\frac{aL^{-2}}{a^f_k+aL^{-2}}<\frac14$ near $t=1$, so $|\log r_{k+1}|\le\theta_*|\log r_k|+|\log(1+\xi^{(k)}_3)|$ and $r_k-1=O(c_8)\max(\theta_*,q)^k$ where $q=L^{-2\gamma}$ (compare P4's variant of (H.6): $a_k=a^f_k\gamma_k^{-1}$ up to such terms). In particular $a_k\in[\frac9{10},\frac32)$ for $\beta\ge\beta_*$ if $a$ is chosen with $a^f_k\in[1,\frac32-\frac1{10})$. **Recommendation:** use (i) in Def-6 and Def-7 (question 1, §7.6): it gives the exact sum rule needed by `CORRELATIONS.md` (G4); under (ii) the sum rule holds only up to terms of the type of P9 (4.18), which requires a perturbation statement for the Gaussian kernels in the sequence $(a_i)$ (Lipschitz dependence of $T_j$ on $a_i$, $i<j$, with decay in $j-i$) that no source states.

### 3.2 The system (5.5), (5.14) at $\lambda=\infty$ (checked on pp. 708–711 and 714)

The first renormalization condition is satisfied by the choice of the additive constant $E^{(k+1)}(z)$ (P4 p. 708). With $f_u$ the effective potential of the unrenormalized new term in the invariants $(u,v,w^2)$ of §2.3 Step 3, $c_2$ the second-order part of the counterterm, $v=\nu_{k+1}$, and using $a+\beta^{-1}c=(1+\xi_3)a_{k+1,u}$ (true for both choices), (5.4) and (5.5) at $1/\lambda=0$ read:
$$\partial_uf_u(1,v,0)-\beta(1+\xi_3)a_{k+1,u}(\zeta^2+\zeta)+\beta\,\partial_uc_2(1,v,0)=0,\tag{E1}$$
$$\tfrac1v\partial_vf_u(1,v,0)+\beta\xi_2+\tfrac\beta v\,\partial_vc_2(1,v,0)=0.\tag{E2}$$
The third equation is the vanishing of the transversal second moment, P4 (5.14) with the quadratic form (5.11), which I checked at $\lambda=\infty$ (the denominators $1+\frac{a+v}\lambda$ become $1$). Put $\xi_c:=\beta^{-1}c=\theta_c'\,a_{k+1}\xi_3$ ($\theta_c'=1$ for $c=a_{k+1}b$, $0$ for $c=0$). With $a:=a_{k+1}$ in the factors that come from the transversal operators ($H=aGQ^*$, $G$), $a_u=a_{k+1,u}$, and $a+\beta^{-1}c=(1+\xi_3)a_u$:
$$v_u^{(k+1,\infty)}-\beta\Big\{(1+\xi_3)a_u\zeta\,\frac{a}{(a+v)^2}\Big[1+\tfrac v{12}\tau-v^2c_1(v)\Big]+\xi_c\,\frac{av}{(a+v)^3}\Big[1+\tfrac v{12}\tau-v^2c_1\Big]+\big((1+\xi_3)a_u\zeta+v\xi_2\big)\frac{a^2}{(a+v)^3}\Big[-1+\tfrac{a-v}{24}\tau-avc_1+\tfrac12(a+v)v^2c_2\Big]+\xi_3\frac{a^2}{2(a+v)^2}\big[1+v^2c_1-v^3c_2\big]\Big\}+\beta v^\infty(C_2)=0,\tag{E3}$$
with $\tau\in[0,1]$ the factor printed as $1-L^{-2m}$ in (5.13) and as $1-L^{-2}\eta^2$ in (5.14), (5.21) (one of the two is a misprint; harmless for the bounds), and $c_1(v),c_2(v)$ the lattice sums of (5.13) with $0<c_i<\frac1{20}$, $0<c_1-vc_2<c_1$. This is (5.14) as printed (the $-v\beta^{-1}b$ of (5.11) is merged into the last bracket there, so it is not repeated).

**Hypotheses supplied by I-8 and §2.** (B1) $f_u,c_2$ and $v_u^{(k+1,\infty)}$, $v^\infty(C_2)$ are analytic functions of $\xi$ on the polydisc $\{|\xi|_\infty<c_{10}\}$ ($\xi_1=\zeta/\varepsilon_{k+1}$) and bounded: the localization expansions of $\mathscr E_u^{(k+1)}$, $C_2^{(k+1)}$ (I-8(c), P4 Prop 4.1) extended to the disc $\{\zeta:|\zeta|<\varepsilon_0+\delta_0,\ |\partial^1\zeta|<\delta_0,|\zeta|^2<\delta_0\}$ (P4 p. 712: by P1 Lemma 3.2 with $\varepsilon_0=\delta_0=\frac12K_1^{-1}\varepsilon_{k+1}$) give, by Cauchy,
$$|c_i(\xi)|\le K_5C_4\epsilon^2\ \ (|\xi|_\infty\le\epsilon\le c_{10}),\qquad |f_i(\xi)|\le B_6K_5\,\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}\tag{5.24, 5.25}$$
where $K_5=9K_0(16dK_1LM)^2(3LM)^d$, using P4 (5.15)–(5.19) and $|Y|\le(3LM)^d(1+d_{k+1}(Y))$ (P6 (4.11)); $B_6=NL^dB_4+2$, $C_4$ from P4 Prop 4.1. (B2) the second equation's data are uniform as $\nu\to0$ (§3.5).

### 3.3 The quadratic form at $\lambda=\infty$ (direct computation)

For ψ=e_1+ψ', h=e_1, the (EL) system at $\lambda=\infty$ is $(−\Delta+aQ^*Q+\nu+\alpha)\phi=aQ^*\psi+\nu h$, $\phi\cdot\phi=1$ (componentwise operators, $G=(-\Delta+aQ^*Q+\nu)^{-1}$). Base solution $\phi_0=e_1$, $\alpha_0=0$. At order one: $\phi^{(1)}=G(aQ^*\psi'-\alpha^{(1)}e_1)$, $e_1\cdot\phi^{(1)}=0$, hence $\alpha^{(1)}=aQ^*\psi_1'$ and $\phi^{(1)}=aGQ^*\psi'_\perp=H_{tr}\psi'$ (P4 (5.7), (5.8) at $1/\lambda=0$). At order two: $e_1\cdot\phi^{(2)}=-\frac12|\phi^{(1)}|^2$ and $\phi^{(2)}_\perp=-G(\alpha^{(1)}\phi^{(1)})$. The quadratic form (5.10) needs only $\phi^{(1)}$ and $e_1\cdot\phi^{(2)}$ (the terms $\langle\psi',\psi'-Q\phi^{(1)}\rangle$, $\langle e_1,Q\phi^{(2)}\rangle$, $\|\partial\phi^{(1)}\|^2$, $\|\phi^{(1)}\|^2$); the $\perp$ part of $\phi^{(2)}$ does not enter. The cross term of the rescaling $\theta=(1+\zeta)\psi$ is $(a+\beta^{-1}c)\zeta\langle\psi,\psi-Q\phi\rangle$; its second-order part contains $-(a+\beta^{-1}c)\zeta\langle e_1,\phi^{(2)}\rangle=+\frac12(a+\beta^{-1}c)\zeta\|H\theta\|^2$ with my $e_1\cdot\phi^{(2)}=-\frac12|\phi^{(1)}|^2$. P4 (5.10) writes $-\frac12(a+\beta^{-1}c)\zeta\langle e_1,\phi^{(2)}\rangle$ and (5.9) has $e_1\cdot\phi^{(2)}=-|H_{tr}\psi'|^2$ at $1/\lambda=0$, i.e. twice mine, so both bookkeepings give the first line of (5.11): $\frac12 a\zeta\|H\theta\|^2$. UNCERTAIN: P4's printed (5.9) differs from the direct computation by this factor 2 (compensated by the $\frac12$ in (5.10)) and by the placement of $G$ in the $\perp$ part (which does not enter); the final form (5.11) agrees with the direct computation, and (5.9) is not used elsewhere. Lean should re-derive (5.4), (5.10), (5.11) at $\lambda=\infty$ from the linear response of `BACKGROUND.md` Prop 5.4 and (EL) directly, not from a limit $\lambda\to\infty$.

### 3.4 The reduction to the landed theorem; the statement

Divide (E1) by $\beta\varepsilon_{k+1}$, (E2) by $\beta$, (E3) by $\beta$ (P4 p. 714). The system takes the form
$$A(\xi,p)\,\xi+\tilde c(\xi,p)=\tilde f(\xi,p)\tag{3.1}$$
with $A$ lower triangular (P4 (5.21) at $\lambda=\infty$):
$$a_{11}=a_{k+1},\ \ a_{21}=0,\ \ a_{22}=1,$$
$$a_{31}=\varepsilon_{k+1}\frac{a^2}{(a+v)^2}\Big[1+\tfrac v{12}\tau-v^2c_1\Big]+\varepsilon_{k+1}\frac{a^3}{(a+v)^3}\Big[-1+\tfrac{a-v}{24}\tau-avc_1+\tfrac12(a+v)v^2c_2\Big],$$
$$a_{32}=\frac{a^2v}{(a+v)^3}\Big[-1+\tfrac{a-v}{24}\tau-avc_1+\tfrac12(a+v)v^2c_2\Big],\qquad a_{33}=\frac12\frac{a^2}{(a+v)^2}[1+v^2c_1-v^3c_2]+\frac{a^2v}{(a+v)^3}\Big[1+\tfrac v{12}\tau-v^2c_1\Big],$$
$a=a_{k+1}$, $v=\nu_{k+1}$, and $\tilde c$ collects the explicitly second-order terms of (E1), (E3) (products $\xi_1\xi_3$, $\varepsilon\xi_1^2$, the second-order parts of $c_i$) and the $\xi$-dependence of $a,v$.

**Lemma 3.1 (coefficient bounds at $\lambda=\infty$; proved).** If $a_{k+1}\in[\frac9{10},\frac32]$ and $0<v\le\frac7{32}$ (note $\bar\nu\le\frac78L^{-2}\le\frac7{32}$ for $L\ge2$), $\tau\in[0,1]$, $0<c_i<\frac1{20}$, $0<c_1-vc_2<c_1$, then $|a_{11}|\ge\frac12$, $a_{22}=1$, $\frac14<a_{33}<1$, $|a_{31}|\le\frac52\varepsilon_{k+1}$ (indeed $\le2.1\varepsilon_{k+1}$), $|a_{32}|\le\frac32$ (indeed $\le0.3$). *Proof.* Put $\rho=a/(a+v)\in[\frac{1}{1+v},1]$. Then $a_{33}\ge\frac12\rho^2(1-v^3c_2)\ge\frac12\big(\tfrac{0.9}{0.9+0.219}\big)^2\cdot0.999>0.32$ and $a_{33}\le\frac12(1+v^2c_1)+\frac va\rho^3(1+\frac v{12})\le0.5013+0.245<1$. The bracket $[-1+\ldots]$ lies in $[-1.07,-0.9]$, so $|a_{32}|\le\frac{v}{a}\rho^2\cdot1.07\le0.27$ and $|a_{31}|\le\varepsilon_{k+1}(1.02+1.07)$ crudely (the two terms nearly cancel for small $v$). $\square$ (P4 (5.22) states these for $a\in(1,\frac32)$ and $\bar\nu\le\frac78L^{-2}$.)

These are exactly the hypotheses `TriangularBounds A ε` of `Balaban.Flow.exists_rg_solution_triangular` with $\varepsilon=\varepsilon_{k+1}$ at $\xi=0$. The $\xi$-dependence of $A$ (through $v=\nu_{k+1}(\xi)$, and through $a_{k+1}$ in case (ii)) is moved into $\tilde c$: $\tilde c(\xi)=c(\xi)+(A(\xi)-A(0))\xi$ with $|A(\xi)-A(0)|\le C|\xi|$ (the entries are rational in $(a,v)$ with $\partial_\xi v=O(v)$, $\partial_{\xi_3}a=O(a)$ in (ii)), so $\tilde c$ is of second order with constant $\tilde\kappa\le K_5C_4+C$, independent of $\beta$ and $k$. The landed theorem gives the following.

**Theorem 3.2 (I-7).** Assume (B1) and let $\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}\le\frac2{\alpha_0^2}\beta^{-1}$ (this is (5.29), from (H.6) and $\gamma_k<\frac32$). There are $C_\xi$ and $\beta_*$ (depending on $B_6,K_5,C_4,\alpha_0,c_{10},L,\gamma$) such that for $\beta\ge\beta_*$:

(a) *(existence, uniqueness, analyticity)* the system (3.1) has exactly one solution $\xi^0$ in the closed polydisc of radius $r_0=\min\{(16\cdot42\tilde\kappa)^{-1},\frac12c_{10}\}$; it is real for real data and analytic in the data (the parameter $p$ ranges over an open set; `exists_rg_solution_triangular`, conclusion `AnalyticOnNhd`); $|\xi^0|_\infty\le84\,\eta$ with $\eta=B_6K_5\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$, so
$$|\xi^{0}|_\infty\le C_\xi\,\beta^{-1}L^{-2\gamma(k+1)},\qquad C_\xi:=\frac{168\,B_6K_5}{\alpha_0^2}\tag{3.2}$$
(P4 (5.31) with explicit constants; the hypothesis of the landed theorem, `16·42η·max(2·42κ̃,1/c₁₀)≤1`, is P4 (5.27)/(5.30)).

(b) *(coefficients)* $b_{k+1}=\beta_{k+1}\xi_3^0$, $e_{k+1}=\beta_{k+1}\xi_2^0$, $\beta_{k+1},\nu_{k+1},a_{k+1}$ given by §3.1; with $q=L^{-2\gamma}$ and $c_8:=4C_\xi/\beta$ one has $|\xi^{(k)}|_\infty\le\frac{c_8}4q^{k+1}$ for all $k$ (inductively, since (H.6) at step $k$ is needed to bound $\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$), so (H.6) holds with $\gamma_k^{\pm1},\delta_k^{\pm1}\le\exp(c_8\sum_{j\le k}q^j)$ (landed `norm_gammaSeq_le`), and the bounds (1.10) of P4: $|\beta_{k+1}^{-1}b|,|\beta_{k+1}^{-1}e|\le\frac14c_8q^{k+1}$.

(c) *(limits and rate)* $\gamma_\infty=\lim\gamma_k$, $\delta_\infty=\lim\delta_k$ exist (landed `exists_gamma_infty`) and
$$|\gamma_\infty-1|,\ |\delta_\infty-1|\le\frac{c_8q}{2(1-q)}=\frac{2C_\xi\,q}{(1-q)}\,\beta^{-1},\qquad \beta_j^{-1}=(\beta\gamma_\infty)^{-1}L^{-j(d-2)}+O(\beta^{-2})L^{-j(d-2+2\gamma)}$$
(landed `exists_inv_betaSeq_asymptotics`, P9 (4.18)). This is the rate that `CORRELATIONS.md` (F1) needed and flagged as not proved (§5 item 5 there): it is proved here because P4's (5.31) bounds $|\xi^0|$ by $O(\beta^{-1})$ directly, with no need for "$c_8$ arbitrarily small"; $c_8=4C_\xi/\beta$ and $\beta\ge\beta_*$ ensure $c_8q\le1-q$.

*Proof.* (a) is the landed theorem applied to (3.1) with the hypotheses (B1) and Lemma 3.1. (b), (c) are P4 (5.28), (5.31)–(5.33) and the landed running-coefficient lemmas. For the $\beta^{-2}$ in the last display: $\beta_j^{-1}=L^{-j(d-2)}\beta^{-1}\gamma_j^{-1}$ and $|\gamma_j^{-1}-\gamma_\infty^{-1}|\le Cc_8q^j$. $\square$

### 3.5 Continuity in $\nu$ down to $\nu=0$ (CORRELATIONS (F1))

Two statements are needed by `CORRELATIONS.md` (F1): (i) the bound (3.2) for every $\nu\in[0,1]$ — **settled**: it holds for every $\nu\in(0,\bar\nu]$ with the same constants because nothing in (a)–(c) depends on $\nu$ beyond $v\le\bar\nu$ and the data bounds, which are uniform (the uniformity of (B1) in $\nu$ is a hypothesis on the class); (ii) for each $k$, $\lim_{\nu\downarrow0}\xi^{(k)}(\nu)$ exists (continuity at $0$ from the right) — **reduced to an explicit clause on the data**, by the following lemma.

**Lemma 3.3 (stability of the fixed point; proved).** Let $\Phi_p(\xi):=\tilde f(\xi,p)-\tilde c(\xi,p)$ (after applying $A^{-1}$), with $\Phi_p(B_{r_0})\subset B_{r_0}$ and $\mathrm{Lip}(\Phi_p)\le\frac12$ on $B_{r_0}$ for $p,p'$ in the parameter set. Then the fixed points satisfy $\|\xi_p-\xi_{p'}\|\le2\sup_{B_{r_0}}\|\Phi_p-\Phi_{p'}\|$. *Proof.* $\xi_p-\xi_{p'}=[\Phi_p(\xi_p)-\Phi_p(\xi_{p'})]+[\Phi_p(\xi_{p'})-\Phi_{p'}(\xi_{p'})]$ and the first bracket is $\le\frac12\|\xi_p-\xi_{p'}\|$. $\square$ (Lipschitz constant $\le\frac12$ is P4 (5.26); the landed `exists_rg_solution` proves it inside.) Since $\Phi_p$ are analytic and uniformly bounded on the polydisc, pointwise convergence on a set with an accumulation point suffices (Vitali), hence it suffices that the data converge at *one open set of $\xi$*.

**Clause (CONT).** For each fixed $k$ and each $j\le k+1$, as $\nu\downarrow0$ the localized terms $\mathscr E^{(j)}_\nu(y,X;\psi,b)$, $\mathscr M^{(j)}_\nu$ converge uniformly on a $\nu$-independent open set of $(\psi,b)$ [the domain in the variables $(\psi,b=\nu h)$ is $\nu$-independent: (C3) of `BACKGROUND.md` §1.3 bounds $|b'|<\delta^2/\varepsilon$ and $|(\psi_0\cdot b')|<\delta^2$], together with $\beta_k(\nu),a_k(\nu)$. Given (CONT) at step $k$ and the explicit formulas of P4 (2.52)–(2.60), (4.14)–(4.22), (CONT) at step $k+1$ follows by dominated convergence (Tannery: the series over $Y$ converge absolutely with $\nu$-independent bounds) and I-1's analytic dependence on the parameter $\mu=\nu_kL^{-2k}$: the operator $-\Delta+aQ_k^*Q_k+\mu+\alpha$ is coercive uniformly in $\mu\ge0$ (the block term gives the gap; `GREEN.md` G-1 at $\mu=0$), so the solution of (EL) is analytic in $\mu$ on a complex neighbourhood of $[0,L^{-2k}]$ uniformly in the torus. Then $\xi^{(k)}(\nu)\to\xi^{(k)}(0^+)$ by Lemma 3.3, inductively in $k$.

**On the factor $1/v$ in (E2).** UNCERTAIN: as printed, the data $f_2=-\beta^{-1}v^{-1}\partial_vf_u$ and the bound (5.25) contain $v^{-1}$. If $\partial_vf_u$ is the derivative in the variable $v'=\nu\,\psi_0\cdot h$ of $f(u,v',w')$ then Cauchy in the disc $|v'-\nu|<\delta_0^2$ gives only $|\partial_{v'}f|\le E_0K_0/\delta_0^2$ and $f_2\sim\beta^{-1}\varepsilon^{-2}/v$, which is not uniform as $v\to0$. The estimate (5.25) is uniform if "$\partial_v$" means the derivative in the variable $V=\psi_0\cdot h$: $g_\nu(u,V,W^2):=f(u,\nu V,\nu^2W^2)$ is analytic and bounded on $|V-1|<\delta_0^2/\nu$ (domain $\bar\Psi^c$, (C3)), so $|\partial_Vg_\nu|\le E_0K_0\nu/\delta_0^2$ and $v^{-1}\partial_Vg_\nu=O(\delta_0^{-2})$ uniformly. This is how P4's printed bound is to be read, and the Lean statement should define the second condition by the $b$-derivative, $\partial_b\mathscr V\cdot e_1=0$, with $b=\nu h$, whose polydisc radius ($\asymp\delta_0^2/\varepsilon$) does not depend on $\nu$. The existence of $\lim_{\nu\downarrow0}v^{-1}\partial_Vg_\nu(1,1,0)$ (a first-order response coefficient) is then the content of (CONT) for the $b$-dependence. This is the exact requirement; confidence that it holds: high (every object at fixed $k$ depends on $\nu$ analytically through $\mu$), but no source states it.

*What is not needed:* uniqueness of the $\nu=0$ state, or a separate construction of the flow at $\nu=0$ (Root-C asks only for the limits $\nu\downarrow0$).

### 3.6 What I-7 does not contain

The construction of $\mathscr E_u^{(k+1)}$, $C^{(k+1)}$ and the bounds (B1) (I-8, §4) and the verification (P4 Prop 5.2) that the renormalized terms satisfy (H.2)–(H.7), with $E_0\ge4C_4B_6K_0K_5$ (P4 (5.39)) and $c_9=\beta^{-1/4}$ (5.40); both are part of I-9 (§5).

---

## 4. I-8: the localization and cluster expansions of the fluctuation integrals

### 4.1 The objects (P4 §2, §4, whole lattice, $\lambda=\infty$)

Fix $\rho_k\in\mathbb R^{\rm sf}_k$ and the step $k\to k+1$.

1. *Gaussian composition (I-2; P4 (2.3)–(2.14)).* For $\theta$ on $\Lambda_{k+1}$ with $|\theta-Q\psi|<2\beta_k^{-1/2}p(\beta_k)$ the function $\psi\mapsto-\beta_k[\frac a2L^{-2}\|\theta-Q\psi\|^2+A_k(\psi,\phi_k(\psi))]$ has exactly one critical point $\psi^{(k)}(\theta)$ (a minimum), given by the linear formula (2.8): $\psi=Q_k\phi-\frac{aL^{-2}}{a_k+aL^{-2}}Q^*Q_{k+1}\phi+\frac{aL^{-2}}{a_k+aL^{-2}}Q^*\theta$; $a_{k+1,u}=aa_k/(a_k+aL^{-2})$; $\phi_k(\psi^{(k)}(\theta))=\phi_{k+1}(\theta)$, $\alpha_k=\alpha_{k+1}$ (I-2 Theorem 6.1(ii)).
2. *Expansion.* $\psi=\psi^{(k)}+\psi'$; the perturbed system with independent data (I-1, Prop 5.1 of `BACKGROUND.md`) gives $\delta\phi_k(\psi'),\delta\alpha_k(\psi')$, analytic, of norm $\le K_2|\psi'|$; the quadratic form is $\frac12\langle\psi',\Delta^{(k)}\psi'\rangle$ with the *constrained* $\Delta^{(k)}$ ($\Pi$ of `BACKGROUND.md` §5.5, `GREEN.md` (1.8$'$)), bounded below by $\frac12\gamma_0L^{-2}$ together with $\frac a2L^{-2}\|Q\psi'\|^2$ (G-1(b); P4 (2.24)–(2.25)), so $C^{(k)}=(aL^{-2}Q^*Q+\Delta^{(k)})^{-1}$ has exponentially decaying kernel (G-4(i) of `GREEN.md` §4.4); the interaction $V^{(k)}(\psi')=\sum_zV^{(k)}(z;\psi')$ (P4 (2.26)–(2.28)) is $O(|\psi'|^3)$, analytic.
3. *Rescaling.* $\psi'=\beta_k^{-1/2}C^{(k)1/2}\psi$; the Gaussian becomes $e^{-\frac12\|\psi\|^2}$, a product measure over the sites of $\Lambda_k$; the characteristic function $\chi^{(k)}$ restricted to the fluctuation variable is the pointwise condition $|\psi_x|<p_1(\beta_k)$ (P4 (2.39)–(2.40)). So the measure is $d\nu=\prod_x\chi(|\psi_x|<p_1)e^{-|\psi_x|^2/2}d\psi_x/\mathcal Z$. (The non-product obstruction noted for P9 (3.13) in `POLYMER.md` §4.1 does not arise here: it appears only after the P9 restriction to $\Omega''$ and $g\ne0$.)
4. *The interaction and the old terms.* $\delta\mathscr E_k(\psi')=\mathscr E_k(\psi^{(k)}+\psi')-\mathscr E_k(\psi^{(k)})=\sum_{j\le k}[\mathscr E^{(j)}(\psi_k^{(j)}(\psi^{(k)}+\psi'),h)-\mathscr E^{(j)}(\psi_k^{(j)}(\psi^{(k)}),h)]$ via the composition (P4 (2.32)–(2.35), I-2 formula (4.21)); similarly $\delta\mathscr F_k$.
5. *New contributions* (P4 (2.51)–(2.60)): with $d\mu_{s,t}$ the normalized measures with weights $\exp[-\beta_kV^{(k)}(\beta_k^{-1/2}C^{1/2}s\psi)+\delta\mathscr E_k(\beta_k^{-1/2}C^{1/2}t\psi)]$ relative to $d\nu$,
$$\mathscr E_0^{(k+1)}=\tfrac12\log\det C^{(k)}+\mathscr E_1^{(k+1)},\quad \mathscr E_1^{(k+1)}=\int_0^1\!ds\!\int d\mu_{s,0}\big(-\beta_k^{1/2}\langle V^{(k)\prime},C^{1/2}\psi\rangle+\beta_k^{-1/2}\langle\delta\mathscr E_k',C^{1/2}\psi\rangle\big),$$
$$\mathscr F_0^{(k+1)}(g)=\langle g,\beta_k^{-1/2}\mathscr M_0^{(k+1)}(g)\rangle=\int_0^1dt\int d\mu_{1,t}\,\tfrac d{dt}\delta\mathscr F_k(\beta_k^{-1/2}C^{1/2}t\psi),$$
with the localized forms (2.57) and $\tfrac12\log\det C^{(k)}=-\frac12\sum_y\operatorname{tr}\log(aL^{-2}Q^*Q+\Delta^{(k)})(y,y)$ (2.58)–(2.60).
6. *Renormalization* (P4 §4): $\theta=z_{k+1}\psi_{k+1}$, perturbed minimal configuration $\phi_{k+1}+\delta\phi_{k+1}$ with $(\delta\phi_{k+1},\delta\alpha_{k+1})$ the solution of (4.4)–(4.5) (I-1 Prop 5.1 again; bounds (4.7), (4.11)); $\beta_{k+1,u}A_{k+1,u}(\theta,\phi_{k+1,u})=\beta_{k+1}A_{k+1}(\psi_{k+1},\phi_{k+1})+\beta_{k+1}C^{(k+1)}+\frac12\nu e(|h|^2-1)|T_1|$ (4.12)–(4.13) with the counterterm $C^{(k+1)}=C_1-C_2$ (4.14), $C_1$ at least first and $C_2$ at least second order in the constants, both sums of local terms (4.15); $\mathscr E_u^{(k+1)}$ (4.17), $\mathscr M^{(k+1)}$ (4.18) with the localization by $\int d\tau\,\frac d{d\tau}$ at $(t+\tau\chi_\Delta(z))\psi_0$ (4.20), using that $\delta\phi,\delta\alpha,\delta\psi$ vanish at zero constants.

### 4.2 Statement

**Theorem 4.1 (I-8; whole-lattice, $\lambda=\infty$; P4 Props 2.1, 2.2, 4.1, 4.2).** Let $\rho_k\in\mathbb R^{\rm sf}_k(\ldots;B,\bar\nu)$ with the constants of I-9 and $\kappa\ge3+6\kappa_0$, $\beta\ge B$ large. For $z\in\Lambda_{k+1}$:

(a) $\mathscr E_0^{(k+1)}(z;\theta,h)=\sum_{Y\in\mathcal D_{k+1},Y\ni z}\mathscr E_0^{(k+1)}(z,Y;\theta,h)$, each term depending on $(\theta,h)|_Y$, analytic on $\Xi^c_{k+1}(\mathbb B_{k+1}(Y);1,\varepsilon_{k+1})$, invariant as in (H.3), with $|\mathscr E^{(k+1)}_0(z,Y)|\le(NL^dB_4+1)\,e^{-(2\kappa-3-6\kappa_0)d_{k+1}(Y)}$ (P4 Prop 2.1, p. 696).

(b) $\mathscr M_0^{(k+1)}(x;\theta,h,g)=\sum_{Y\ni x}\mathscr M_0^{(k+1)}(x,Y;\cdot)$, analytic on $\Xi^c_{k+1}(\ldots)\times\{\|g\|_{\ell^1}<1\}$, equivariant, with $|\mathscr M^{(k+1)}_0(x,Y)|\le C\beta^{-(\frac38+\alpha_1)}\xi_{k+1}^{\frac{d-2}2+\gamma-\alpha_1}e^{-(2\kappa-4-6\kappa_0)d_{k+1}(Y)}$, $C\beta^{-3/8-\alpha_1}\le\frac12\beta^{-1/4}$ (P4 Prop 2.2).

(c) For renormalization constants with $|\varepsilon_{k+1}^{-1}\zeta|,|\beta^{-1}b|,|\beta^{-1}c|,|\beta^{-1}e|<\epsilon\le\epsilon_0$ ($d$ absent at $\lambda=\infty$), $C_1^{(k+1)}(z)$, $C_2^{(k+1)}(z)$, $\mathscr E^{(k+1)}_u(z)$ have localization expansions with the properties of (a), analytic also in $\xi$ on the polydisc (4.8), with constants $C_4\varepsilon_{k+1}^2\epsilon$, $C_4\varepsilon_{k+1}^2\epsilon^2$, $NL^dB_4+1+C_5E_0\epsilon$ respectively and decay $\kappa$ (P4 Prop 4.1, p. 706).

(d) $\mathscr M^{(k+1)}(x;\ldots)$ of (4.18) has an expansion with $c_9$ replaced by $\frac12\beta^{-1/4}+C_6\epsilon L^{(k+1)(2\gamma-\alpha_1)}$ (P4 Prop 4.2).

Here $B_4$ is the constant of the localization of $(aL^{-2}Q^*Q+\Delta^{(k)})$ (P3 Sect. 3 = I-4(c)); $\kappa_0$ is absolute (P3); $K_0=\sup_z\sum_{Y\ni z}e^{-\kappa_0d_{k+1}(Y)}$.

On the form of the interface. P4 (Props 2.1, 2.2, 4.1, 4.2) and P5 (Props 3.1–3.4) state these for the whole lattice and, "in a more general form", for small-field subdomains with holes $\Omega^c$ (modular connectivity); I-9 needs only the whole-lattice form. I recommend freezing one statement for all four items (they are four coordinates of the same expansion), in the whole-lattice form, and leaving the modular form to LF-3 (question 6).

### 4.3 Proof plan (every input named)

**Inputs.** I-4 (P3 Props 2.1–2.3, 3.1): the decoupling extensions in $s_\square$, $|s_\square|\le e^{\kappa_1}$, of $\delta\phi_k,\delta\alpha_k$, of $\psi(\mathbb B_j,\mathbb B'_k)$ and of $C^{(k)1/2}=\frac1\pi\int_0^\infty x^{-1/2}C^{(k)}_xdx$ (`GREEN.md` C12, G-4(i)), with the localization property and bounds. I-5 (P3 Prop 4.3): the localization expansion of $\mathscr E(X;\psi^{(j)}_k(\psi^{(k)}(\theta)+\psi'))$ with bound $E_0e^{-\kappa_0d_j(X)-2\kappa\tilde d_{k+1}(Y)}$, including the "simple variations" of P3 p. 81. PE-L, MY, PE-M (`POLYMER.md` §§2.3–2.5). Geometry: P6 (4.11) $|Y|\le(3LM)^d(1+d_{k+1}(Y))$, (G2) $K_0<\infty$, (G3) subadditivity (P6 (4.43)–(4.45)). G-4/G-5 for $C^{(k)}$ and $H=aGQ^*$.

**Step 1: the determinant (a, first part).** $\frac12\log\det C^{(k)}=-\frac12\operatorname{tr}\log A$, $A=aL^{-2}Q^*Q+\Delta^{(k)}$, with kernel localized in the data $(\phi_{k+1},\alpha_{k+1})$ by I-4(c) (the locality of $C^{(k)}_x$, `GREEN.md` C17, G-4(c)); write $\operatorname{tr}\log A=\sum_y\operatorname{tr}\log(A)(y,y)$ and localize each diagonal entry by the same decoupling in $s_\square$ and a resolvent-type formula (P4 (2.58)–(2.60)): terms with bound $NL^dB_4e^{-(2\kappa-3-6\kappa_0)d(Y)}$ (P6 (4.54)–(4.56) [review]). Status: sketched.

**Step 2: the interaction (the potential $U$).** By I-4(a),(b) the functions $\delta\phi_k(\beta_k^{-1/2}C^{1/2}\psi)$, $\delta\alpha_k$ have decoupling extensions; $V^{(k)}(z;\cdot)$ is a polynomial/analytic function of them, so $\mathcal U^{(k)}_{t,u}(Z;\beta_k^{-1/2}\sigma,C^{1/2}\psi)=\sum_Y\mathcal U(Y;\psi)$ with terms analytic in $\psi,\sigma,t$, localized in $Y$, bounded by $\varepsilon e^{-(2\kappa-1)d_{k+1}(Y)}$, $\varepsilon=\beta^{-1/8}$ arbitrarily small for $\beta$ large (P6 Lemma 4.1, (4.24)–(4.28); the $\kappa$ is doubled because the potential is cubic and contributes two derivatives of the localized $\delta\phi$). The $\delta\mathscr E_k$ terms enter through I-5, with the same bound (the "$2\kappa\tilde d_{k+1}$" of I-5). Status: sketched (P6 p. 32).

**Step 3: decoupling.** Replace $\sum_Y\mathcal U(Y)$ by $\sum_Yt_Y\mathcal U(Y)$ and use the Taylor/Möbius identity $F(1)=\sum_{C}\int_{[0,1]^C}\partial^CF(t_C,0)$ (T0 of `POLYMER.md`), with Cauchy estimates in each $t_Y$ on circles $|\tau_Y|=r_Y=\varepsilon^{-1/2}e^{(2\kappa-1-5\kappa_0)d(Y)}$, giving $|\tau_Y\mathcal U(Y)|\le\varepsilon^{1/2}e^{-5\kappa_0d(Y)}$ (P6 (4.39)–(4.43)). The expectation factorizes over the connected components of $\bigcup Y$ because $\nu$ is a product measure: the numerator and the normalization cancel outside the component containing the marked point.

**Step 4: cluster expansion.** Apply MY (product measure, terms $H(Y)=t_Y\mathcal U(Y;\psi)$, $|H|\le\varepsilon^{1/2}$-type, $\kappa_h=5\kappa_0$) and PE-L: $\Xi=\exp L$, $P(Y)$ localized with $|P(Y)|\le\alpha e^{-\kappa'd(Y)}$, using (G1)–(G3) of §4.3 inputs; for the expectation of the marked function use PE-M with one marked function (the term $\mathcal U(z,Y_0)$), which gives (P6 (4.52)–(4.54))
$$|\mathscr E_1^{(k+1)}(z,Z,Y_0)|<C\varepsilon\,e^{-6\kappa_0d(Y_0)}e^{-(2\kappa-3-6\kappa_0)d(Z)}$$
after the loss of $\kappa_1-\frac32$ in MY and $\kappa'$ in PE-L; the printed exponent $2\kappa-3-6\kappa_0$ comes from the order of resummation (any exponent $\ge\frac12\kappa+O(1)$ suffices for (H.7), `POLYMER.md` §4.2; ER-100). Summing over $Y_0$ with (I-5's) $e^{-6\kappa_0d(Y_0)}$ gives (a).

**Step 5: $\mathscr M_0$ and $\mathscr F$.** The same with the marked function $\partial_t\delta\mathscr F_k$; here the extra analyticity in the Cauchy parameter $\sigma$ of the disc $\{\beta_k^{-1/8}\eta^{\gamma-\alpha_1}|\sigma|\le1\}$ is used: the terms vanish at $\sigma=0$ and the Cauchy bound gives the factor $2\beta^{-1/8}\eta^{\gamma-\alpha_1}$ (P6 p. 42, ER-100: "analyticity used for the first time"; a constant $\propto\beta^{-1/2}$ would need clearing out lower orders; not done in the source and not needed). Status: sketched.

**Step 6: renormalized terms (c), (d).** $C_1^{(k+1)},C_2^{(k+1)}$ are explicit polynomial expressions in $\delta\phi_{k+1}(\delta\psi),\delta\alpha_{k+1}(\delta\psi)$ with $\delta\psi=\chi_\Delta(z)\zeta\psi_{k+1}$ (4.14)–(4.15), localized to the block $\Delta_{k+1}(z)$ by I-4(a),(b) (decoupling of the perturbed system with parameters $(\zeta,b,c,e)$ in the polydisc); the $\mathscr E_u^{(k+1)}$ of (4.17) is the sum of the old terms at the new background plus the integral in $\tau$ of (4.20), and the bounds (c) are the corresponding estimates (P4 pp. 698–706), with $\epsilon$-dependence through the small parameters. (d) is the analogue for (4.18) with the bound $\frac12\beta^{-1/4}+C_6\epsilon L^{(k+1)(2\gamma-\alpha_1)}$. Status: sketched; P4 defers the proofs ("will be proved together with all other results on localization expansions", p. 706).

**Output to I-7.** The functions $f_i,c_i$ of §3 are obtained from (c) by the Cauchy estimates of P4 (5.15)–(5.19), (5.24)–(5.25), with the bound $|Y|\le(3LM)^d(1+d_{k+1}(Y))$ (P6 (4.11); P4 p. 712 cites it as "to be proved in the localization paper"; ER-060).

### 4.4 Requirements to verify in the instance, and gaps

1. The characteristic function factorizes over sites (§4.1 item 3; ER-101, settled in the whole-lattice case by the definition (2.39)–(2.40)).
2. $\mathcal U(Y;\psi)$ depends on $\psi$ only through $\psi|_Y$ and is holomorphic in $\tau_Y,\theta,h,\sigma$ on a common domain with the stated bound for all $\psi$ in the support of $\nu$ ($|\psi_x|<p_1$): the polynomial growth $p_1(\beta)^n\le C\beta^{\alpha}$ is what makes the Cauchy radii $r_Y$ admissible.
3. The exponents: $\kappa\to2\kappa-3-6\kappa_0\ge\kappa$ iff $\kappa\ge3+6\kappa_0$ (P4 p. 696 asserts the version of (H.4) at step $k+1$ with the *same* $\kappa$; the iteration is therefore consistent only for $\kappa\ge3+6\kappa_0$, ER-069). Order of constants: $\kappa$ first, then $M\ge M(\kappa)$ (ER-025), then $\alpha_0$, $E_0$, $\beta$.
4. P6's remark that $\mathscr E_0$ and the stronger Cauchy bound in $\sigma$ need "analyticity beyond P3 Lemma 4.1" (ER-100) is an additional interface statement for I-4.
5. P4's $B_4$, $\kappa_0$ are constants of I-4/I-5 and must be quantified in the same order in the frozen statements.

---

## 5. I-9: one small-field step (P4 Theorems 1, 2)

### 5.1 Statement

**Theorem 5.1 (I-9, Theorem 1 form).** Fix $d\ge3$, $N\ge2$, $L$, and constants $M,\kappa,\alpha_1,c_8,c_9,\gamma\in(0,\frac12)$ with $M,\kappa$ large (order of §1.1). There are $B,\alpha_0,E_0$ such that if $\bar\nu\le\frac78L^{-2}$, the map $\chi_{k+1}S^{(k)}T^{(k)}\chi^{(k)}$ maps
$$\mathbb R^{\rm sf}_k(\beta,a,\nu;B,\bar\nu;M,\kappa,\alpha_0,\alpha_1,\gamma,E_0,c_8,c_9)\ \longrightarrow\ \mathbb R^{\rm sf}_{k+1}(\beta,a,\nu;BL^{d-2},\bar\nu L^2;M,\kappa,\alpha_0,\alpha_1,\gamma,E_0,c_8,c_9).$$
**Theorem 5.2 (Theorem 2 form, the equations).** On the data $(\beta_k,a_k,\nu_k,(\mathscr E^{(j)}_k)_{j\le k},(\mathscr M^{(j)}_k)_{j\le k})$ the step is a (real analytic) map into the data of step $k+1$ with $\mathscr E^{(j)}_{k+1}=\mathscr E^{(j)}_k$, $\mathscr M^{(j)}_{k+1}=\mathscr M^{(j)}_k$ for $j\le k$ (P4 (1.8)), and, at $\lambda=\infty$,
$$\beta_{k+1}=\beta_kL^{d-2}-b_{k+1},\quad a_{k+1}=\frac{\beta_kL^{d-2}}{\beta_{k+1}}\frac{a\,a_k}{aL^{-2}+a_k}-\frac{c_{k+1}}{\beta_{k+1}},\quad \nu_{k+1}=\frac{\beta_{k+1}+b_{k+1}}{\beta_{k+1}+e_{k+1}}\nu_kL^2\tag{P4 (1.9)}$$
(and $\lambda_{k+1}=\infty$), with $b,c,e$ analytic in the data and $|\beta_{k+1}^{-1}b|,|\beta_{k+1}^{-1}c|,|\beta_{k+1}^{-1}e|<\frac14c_8L^{-2\gamma(k+1)}$ (P4 (1.10)); here $b,c,e$ are the solution of I-7 with the supplementary equations (i) or (ii) of §3.1 (and $|\beta^{-1}c|\le\frac32|\beta^{-1}b|$). The clause "$\mathscr E_{k+1}$" and the additive constants $E_k$ follow (4.21), not part of Theorem 2.

Remarks. P4 p. 681: "purely existential: the new coefficients are not defined by $T$ alone". Order: P4's list "there exist $B,\alpha_0,E_0$" (the review's ER-064: $\alpha_0$ is output, "small" belongs to (H.1)); $E_0\ge4C_4B_6K_0K_5$ (5.39), $c_9=\beta^{-1/4}$ (5.40), $\beta$ large by (5.30) and (5.41). The statement of Theorem 5.2 is what Root-C consumes (through I-7(c)); I recommend freezing Theorem 5.1 *together with* the recursion clause of Theorem 5.2 and the analyticity-in-data clause as in `BACKGROUND.md` (Def-5 style: a map defined by `∃!`), not Theorem 5.2's "analytic map" alone (ER-070: the paper's remark that Thms 1–2 imply P1 Thm 2.2 is only for small fields).

### 5.2 Proof outline (inputs named)

*Step 0. Data.* $\rho_k\in\mathbb R^{\rm sf}_k$; $\varepsilon_{k+1}=\alpha_{0,k+1}\xi_{k+1}^\alpha$ ($\varepsilon_{j,u}=\varepsilon_j+k^{-2}\alpha_0\xi^\alpha$, P4 §3).

*Step 1. The Gaussian step.* P4 (2.1)–(2.14): extract the Gaussian prefactor; restrict by $\chi^{(k)}$; composition and unique critical point $\psi^{(k)}(\theta)$ (I-2, I-1; $\theta\in\tilde\Psi(\delta_1)$, $\delta_1=4L\beta_k^{-1/2}p(\beta_k)$, P4 (2.3)). Complete modulo I-1, I-2 (algebra: `GREEN.md` G-6, `BACKGROUND.md` §6).

*Step 2. Expansion, quadratic form, covariance.* I-1 Prop 5.1 (perturbed system, $K_2$), G-1 (coercivity), G-4/G-5 and `GREEN.md` §4.4: $C^{(k)}$, $C^{(k)1/2}$ exponentially decaying and localized (I-4(c)); the lower bound (2.25) uniform in $k$. At $k=0$ see §5.5.

*Step 3. The fluctuation integral (2.41) and the new contributions.* Algebra: rescaling (2.38), $E''_k=E'_k+\frac N2\log\beta_k$; (2.52)–(2.60) as definitions. The localization expansions are I-8 (a), (b), proved inside this theorem from I-4, I-5, PE (§4.3), not assumed.

*Step 4. Scaling.* $S^{(k)}$: $\beta_{k+1,u}=\beta_kL^{d-2}$, $a_{k+1,u},\nu_{k+1,u}=\nu_kL^2$ (P4 §3, (3.1)–(3.2)); old terms keep (H.2)–(H.4), (H.7) with the unrenormalized $\psi^{(j)}_{k+1,u}$ and $\varepsilon_{j,u}$.

*Step 5. Renormalization.* (4.1)–(4.22): $\theta=z\psi_{k+1}$, perturbed background (I-1 Prop 5.1 with data $(\zeta,b,c,e)$, bounds (4.7)–(4.11)); $\mathscr E_u^{(k+1)},C^{(k+1)}$ and $\mathscr M^{(k+1)}$: I-8 (c), (d) provide the localization with the analyticity in $\xi$; the effective potential $f_u(u,v,w^2)$ with $U,V,W^2$ of P1 (3.37) is analytic on the polydisc and bounded by $B_6K_0$ on the disc $\delta_0=\frac12K_1^{-1}\varepsilon_{k+1}$ (the domain chain of §1.2 (D1), (D2) = P1 Lemma 3.2 at $\lambda=\infty$, i.e. I-2(iv)).

*Step 6. The equations (I-7).* §3: solution $\xi^0$, (H.6) at $k+1$ by P4 (5.28)–(5.33).

*Step 7. The new terms satisfy the hypotheses (P4 Prop 5.2).* Substituting $\xi^0$: $\mathscr E^{(k+1)}=\mathscr E_u^{(k+1)}-\beta_{k+1}C^{(k+1)}-E^{(k+1)}(z)$ (4.22) is analytic, invariant, localized with $|\mathscr E^{(k+1)}(z,Y)|<4C_4B_6K_0K_5e^{-\kappa d_{k+1}(Y)}$ (5.38); (H.5) holds for it by construction (the three conditions are the equations; the additive constant takes the first); $\mathscr M^{(k+1)}$ satisfies (H.7) with $c_9=\beta^{-1/4}$ (5.40). The strongest restriction on $\beta$ is (5.41): $16B_6^2C_4C_5K_0K_5^2\alpha_0^{-2}\beta^{-1}\le1$. $\chi_{k+1}\chi_{k+1,u}=\chi_{k+1}$ gives Theorem 1.

*Step 8. Constants.* Order (P4 §6, [review]): $d,N,L$; $\gamma,\alpha_1,\kappa,M,c_8,c_9,p_0,p_1,A_0,A_1,\gamma_0$; then $c_6,K_2$ (I-1), $B_4,\kappa_0$ (I-4), $K_0,K_1,c_{10},K_5$, $B_5$, $B_6=NL^dB_4+2$, $C_4,C_5,C_6$ (I-8); $\alpha_0$ small (conditions $7K_2\varepsilon_{k+1}\epsilon\le c_6$ etc.), $E_0\ge4C_4B_6K_0K_5$, $\epsilon=4B_6K_5\alpha_0^{-2}\beta^{-1}$; last $B$ (so $\beta$), with $c_8$-dependence $\beta\ge16B_6K_5/(\alpha_0^2c_8)$ (P4 §5 (5.31)); with my $C_\xi$ of Theorem 3.2 this is $\beta\ge4C_\xi/c_8$.

### 5.3 Inputs, listed

I-1 (existence/uniqueness/analyticity of $\phi_k$, perturbed system $K_2,c_6$, Hölder), I-2 (composition, formula (4.21), identities (4.39), complex data), I-4 (decoupling extensions, localization of $C^{(k)1/2}$), I-5 (expansion of $\mathscr E(X;\psi_k^{(j)}(\psi^{(k)}+\psi'))$), I-6 (only its domain lemma D1–D2; the bound Theorem 2.1 is a separate output), I-7 (§3), I-8 (§4), G-1, G-4, G-5, G-6 (coercivity, unit-lattice operators with decay, identities), PE-L/MY/PE-M/T0 (§4.3), P6 (4.11).

### 5.4 What I-9 may not assume

By the roadmap and AGENTS.md rule 4, I-9 may not take the conclusions of I-8 (the localization expansions of §4.2) as hypotheses; as arranged here it takes none: I-8 is Step 3 and 5 of its proof. If the Lean development sequences I-8 before I-9, I-9 *uses* I-8 as a proved theorem, which is permitted. The frozen surface should therefore contain I-9 and I-8 as two statements with I-9's proof importing I-8 once I-8 is sealed.

### 5.5 The base case and the last step

*Base case.* $\rho_1\in\mathbb R^{\rm sf}_1$ for the hard-spin $\rho_0$ (P4 (2.42)–(2.50), a one-page sketch for $\lambda_0$ uniform; ER-062, ER-063). At $\lambda=\infty$ the first-step quadratic form is $P^\perp G_1^{-1}P^\perp+P$ with $P=(\phi_1)_0\otimes(\phi_1)_0$ site-diagonal (`GREEN.md` §4.4(ii)), which has range $\le L$ and real part $\ge\frac14L^{-2}$, so $C^{(0)}$ decays exponentially without further work; what is missing is the sphere-chart change of variables (the radial variable $\chi$ with $2|\phi_1|\chi+\chi^2+|\phi''|^2=2|\phi_1|\chi'$, P4 (2.45)) written for the measure $\prod\sigma_N(d\phi_x)$ and the verification of (H.1)–(H.7) at $k=1$ including $\mathscr E^{(1)}$'s renormalization (H.5). This is LF-6; the SF milestone needs it as an input, not as part of I-9. I flag it because Theorem 5.1 alone does not start the induction.

*Last step.* P4 §6 (the step $k_1$ with $\nu_k>\frac78L^{-2}$ and the final integration with the restriction $|\psi_{k_1}-h|<(5L+3)\delta_{k_1}$) is LF-8, not SF.

### 5.6 Risks specific to I-9

(i) The composition of constants across I-1, I-4, I-5, I-8 (P4's order is not stated explicitly, ER-024). (ii) The iteration of $\kappa$ (§4.4 item 3). (iii) P4 Theorem 2's analyticity statement is "from explicit expressions"; the analytic dependence on the *data* $(\mathscr E_k^{(j)})_{j\le k}$ (an infinite family) needs a definition of the topology on data; I recommend dropping it from the frozen statement (the Lean statement keeps analyticity in the unknowns $\xi$, which is what Root-C and I-7 use). (iv) The torus-family form: the step maps families over tori to families over tori, with the clause that localized terms of non-winding $Y$ are the same on all tori (`POLYMER.md` §4.5); this is propagated, not proved, by the step.

---

## 6. The one-point and two-point parts for C-1a / C-1\* (`CORRELATIONS.md` §2.3)

### 6.1 Where they enter the small-field step

The generating functional $\mathscr F_k$ of (H.7) is analytic in $g$ on $\|g\|_{\ell^1}<1$; the one-point function is its first-order part, the two-point function the second-order part. P9 refines (H.7) to the form C-1a (`CORRELATIONS.md` §2.3), which I restate in the notation here ($\lambda=\infty$): at second order in $g$,
$$M_k(x;\psi,h)=m_k\,\phi_k(x;\psi,h)+\sum_{j=1}^k\beta_{j-1}^{-1/2}\mathscr M^{(j)}(x;\psi^{(j)}_k,h),\quad m_k=1-\sum_{j\le k}\beta_{j-1}^{-1/2}\mu_j,$$
$$G_k=C_k+R_k,\quad C_k=\sum_{j=1}^k\beta_{j-1}^{-1}m_kG^{(j)}m_k,\ G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*,\quad R_k=\sum_{i\le j\le k}\beta_{i-1}^{-1}R^{ij},$$
with $\mathscr M^{(j)}(x;h,h)=0$ (the constants $\mu_j(x)$ absorbed into $m_k$), $|\mu_j|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}$, $|\mathscr M^{(j)}(x,X)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\kappa d}$, $|R^{ij}(x,x';X)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\delta_0L^{-i}|x-x'|}e^{-\kappa d_j(X)}$.

In the step $k\to k+1$ they enter at three places:

1. **The Gaussian main term.** The coefficient of $\psi'$ in $\langle g,\phi_k(\psi^{(k)}+\psi')\rangle$ is $\langle g,H\psi'\rangle$ with $H=H_{tr}=aG_{k+1}Q^*(I-e_1\otimes e_1)$ at $\psi=h$ (§3.3, `BACKGROUND.md` Prop 5.4: $\dot\phi=(G-\Pi)\dot S$, and at $\psi=h$ constant, $\Pi=Ge_1[e_1\cdot Ge_1]^{-1}e_1\cdot G$, so $\dot\phi=aGQ^*(I-e_1\otimes e_1)\dot\psi$); averaging over the Gaussian $d\mu$ with covariance $\beta_k^{-1}C^{(k)}$ gives $\frac1{2\beta_k}\langle g,H C^{(k)}H^*g\rangle$, which is the new summand $\beta_k^{-1}G^{(k+1)}$ of $C_{k+1}$ (the index shift of `CORRELATIONS.md` §2.1).
2. **The new contributions $\mathscr M_0^{(k+1)},R^{k+1,j}$.** $\mathscr F_0^{(k+1)}$ of (2.52) at second order in $g$ is $\int_0^1dt\int d\mu_{1,t}\,\frac d{dt}\delta\mathscr F_k$ expanded in $g$; its connected two-point part is a truncated expectation of two marked functions $F_1,F_2$ (the $g$-linear terms) under $d\mu_{1,0}$, which is P9 Prop 3.1 (3.13), proved from PE-M with two marked functions (`POLYMER.md` §4.1, conditional on the product measure form, which holds here as in §4.1 item 3). The normalization step $\mu_{k+1}(x):=\mathscr M_0^{(k+1)}(x;h,h)$, $\mathscr M^{(k+1)}:=\mathscr M_0^{(k+1)}-\mu_{k+1}\phi_{k+1}$ puts $\mathscr M^{(k+1)}(h,h)=0$ and moves $\beta_k^{-1/2}\mu_{k+1}$ into $m_{k+1}$ (P9 (2.2)–(2.9)).
3. **The old terms.** At step $k+1$ the one-point terms $\mathscr M^{(j)}$, $j\le k$, and the kernels $R^{ij}$, $i\le j\le k$, are re-evaluated at $\psi^{(j)}_{k+1}$ with the renormalization shifts $\delta\psi^{(j)}_{k+1}$; this uses the irrelevance gap of §2: $|\mathscr M^{(j)}(x;\psi^{(j)}_k(\cdot))|$ for $\psi$ near $h$ is small by the factor $s_{jk}^{\ldots}$, which is what keeps the decay $L^{-j\rho_0}$ (P9 Lemma 2, (2.21)–(2.22), (3.21)–(3.23); `CORRELATIONS.md` §5 item 7).

### 6.2 Extra statements required beyond I-6…I-9

- **X1 (class).** Add to $\mathbb R^{\rm sf}_k$ the second-order components $(\mu_j,\mathscr M^{(j)},R^{ij})$ with the bounds and covariance above (P9 (H.1), (H.2)); the $O(N)$ covariance is $\mathscr M^{(j)}(x;R\psi,Rh,Rg)=R\mathscr M^{(j)}$ (already (H.7)) and, for $R^{ij}$, the tensor covariance of the kernel; at $\lambda=\infty$ the longitudinal component of $C_k$ vanishes exactly (`CORRELATIONS.md` §2.4).
- **X2 (preservation).** P9 Prop 3.1 with its truncated product (3.13) and the estimate (2.21)–(2.22) for the corrections to $\mathscr M^{(j)}$, $R^{ij}$, $j\le k$ — a new statement of I-8 type, using PE-M with two marked functions.
- **X3 (normalization and the scalar $\mu_{k+1}$).** $|\mu_{k+1}|\le\beta^{-1/2+\rho_1}L^{-(k+1)\rho_0}$ and its continuity in $\nu$; this is the analogue of Theorem 2.1(a) for the one-point function (the potential of $\mathscr M$ at the constant configuration $h$ is zero by normalization, so the smallness comes from the irrelevance gap). It is the only place where an exponent $\rho_0>0$ is created; $\rho_0\le\min\{2\gamma,d-2\}$-type restrictions of P9 p. 511 (`CORRELATIONS.md` §5 item 8).
- **X4 (exact Gaussian main term).** The explicit $H_j,G^{(j)}$ with the free sequence (`CORRELATIONS.md` §2.1, (2.2)): requires the free flow (i) of §3.1, or a perturbation statement for (ii).
- **X5 (the unit conventions)** $G_jQ_j^*$ versus the weighted adjoint: `CORRELATIONS.md` Question 3 (seaturtle2).
- **X6 (continuity in $\nu$)** of $\mu_j(\nu;x)$, $R^{ij}$ and of the remainder $r$: clause (CONT) of §3.5 extended to the second-order components.
- **X7 (torus independence)** of all second-order terms (`POLYMER.md` §4.5), propagated by the step.

None of X1–X7 changes the first-order theory of §§2–5; they are additions to the class and to the step. The last-step (P9 (4.7)–(4.9)) is C-1/LF-8.

---

## 7. Interfaces for freezing; changes at $\lambda=\infty$; errata; Lean plan; questions

### 7.1 Proposed frozen interfaces

Following the small-frozen-surface principle (freeze roots and major interfaces; the rest are editable targets), I propose for the SF milestone:

| Item | Statement | Freeze? |
|---|---|---|
| Def-6 | $\mathbb R^{\rm sf}_k$ of §1.3, as a predicate on families over tori, with (CONT) as a clause and (H.5) in the $b$-form | yes, after rulings 2, 3, 5 |
| I-6 | Theorem 2.1(a),(b) and Corollary 2.2, premises (Σ1), (Σ2), (H.2)–(H.5) | yes (a genuine-premise source lemma) |
| I-7 | Theorem 3.2 (a)–(c) with hypothesis (B1) written as the analytic bounds (5.24)–(5.25); plus the triangular-bound Lemma 3.1 as an editable lemma | yes |
| I-8 | one statement: Theorem 4.1 (a)–(d), whole-lattice form | yes |
| I-9 | Theorems 5.1 and 5.2 (recursion clause; no "analytic map") | yes |
| C-1\* | (F1)–(F3) of `CORRELATIONS.md` §2.2, derived from Def-6 + X1–X7 | separate (C-1) |
| Editable | Lemma 3.1, Lemma 3.3, the domain lemmas (D1), (D2), steps of §2.3, §4.3 | not frozen |

I-8 may not be assumed by I-9's proof if I-9 is stated before I-8 is sealed (§5.4).

### 7.2 What changes at $\lambda=\infty$ (collected)

(1) multiplier replaces $\frac\lambda2(|\phi|^2-1)$; (2) $\lambda$-equation and $d_{k+1}$ vacuous; $a_{11}=a_{k+1}$, $a_{21}=0$; the first two renormalization equations decouple (E1)–(E2); (3) $\phi\cdot\partial\phi$ bound exact; (4) quadratic form (5.11) with $1/\lambda=0$, longitudinal terms absent; (5) $C^{(k)}$ uses the constrained operator $\Pi$ (`GREEN.md` (1.8$'$)); (6) base case on the sphere (LF-6); (7) the constant branch $\phi\to-\phi$ of (EL) is excluded by $|\alpha|<c_0$ (`BACKGROUND.md` §1.2); (8) $\bar\nu\le\frac78L^{-2}$ gives $v\le\frac7{32}$ used in Lemma 3.1; (9) the term $\frac1{2\lambda}\ldots\|\alpha^{(1)}\|^2$ and the $3/\lambda^2$ term in $\phi^{(2)}$ vanish; (10) in P1 the condition $\lambda_j\xi^2>\frac56$ disappears.

### 7.3 Errata and unconfirmed points (relevant rows of `ERRATA.md` and new items)

Existing rows touched: ER-008 (numbering: §1.3 fixes P4's, with P1's in brackets), ER-011/012 ((H.7)/(H.9) normalization), ER-014–ER-024 (P1: Theorem 2.2, $\chi^{(j)}$, $\lambda=\infty$, $\gamma_0$, "similarly" steps: **Theorem 2.1 gives an independent proof**, which removes ER-020's suspected typos from the logical path), ER-023 ((H.7) via Ward identity: replaced by (WI)), ER-025 (order $\kappa$ then $M$), ER-058–ER-070 (P4), ER-060 (settled by P6 (4.11)), ER-061 (derivation of (5.9)–(5.14) condensed: **partly re-derived here, §3.3**), ER-062/063 (base case), ER-064, ER-066, ER-067 (the choice $c=0$: **written out, §3.1**), ER-068, ER-069, ER-095/096/100/101/102 (P6/I-8).

New items from this document:

- **SF-1** (P1 (3.122)–(3.125), (H.7)). The marginal coefficient is killed by (H.5)(4) alone, through the exact identity (WI); the $e_2\otimes e_2$ component suffices; (H.5)(3) is needed only for the potential (§2.5). Not an error in P1.
- **SF-2** (P4 p. 717; P5–P7 $c=0$). With $c=0$ versus $c=ab$ the system (E1)–(E3) is the same at $\xi=0$ (since $a+\beta^{-1}c=(1+\xi_3)a_{k+1,u}$ for both choices); the difference is second order in $\xi$. The coefficient $a_k$ differs by $r_k$ with $|r_k-1|=O(\beta^{-1})\max(L^{-2},L^{-2\gamma})^k$ (§3.1). For Root-C the free flow is preferable.
- **SF-3** (P4 (5.5)(2), (5.25)). The printed bound for $f_2$ is uniform in $\nu\to0$ only if $\partial_v$ is the derivative in the variable $V=\psi_0\cdot h$ (§3.5), equivalently the $b$-derivative; UNCERTAIN how P4 intends it; the $b$-form is recommended for the frozen (H.5).
- **SF-4** (P4 (5.9) as transcribed). Differs from my direct computation at $\lambda=\infty$ by a factor 2 in $e_1\cdot\phi^{(2)}$ and in the placement of $G$ in the $\perp$ part (§3.3); the final form (5.11) is consistent. UNCERTAIN until checked against the page image of p. 709 beyond what was read.
- **SF-5** (P4 (5.13) vs (5.14), (5.21)). The factor printed $1-L^{-2m}$ in (5.13) and $1-L^{-2}\eta^2$ in (5.14), (5.21); harmless for the bounds.
- **SF-6** (P4 (5.22)). P4 proves the bounds for $a\in(1,\frac32)$; Lemma 3.1 checks them at $\lambda=\infty$ for $a_{k+1}\in[\frac9{10},\frac32]$, $v\le\frac7{32}$ (needed under the choice (ii) where $a_k$ can dip below $1$).
- **SF-7** (P1 (3.41), $\nu_j\le\sigma^2$). Automatic here ($\nu_j=\nu_ks^2$, $\nu_k\le1$, $C_0\ge3$); it is the reason the $\nu_j m$-term of (2.3) and the $b'_\perp$ terms are irrelevant.
- **SF-8** (P1 pp. 125–147, Step 0 of §2.3). The loss $e^{d}$ per tree length in P1 versus the polynomial weights $(1+d)^6$ used here need $\kappa\ge\kappa_0+7$.
- **SF-9** (roadmap I-6 text: "$|\mathscr E_k|\le CE_0|T_1^{(k)}|$ on $\Xi_k^c(1,\varepsilon_k)$"). Holds with the proof of §2 only for $k-j\ge n_1$; the last $n_1$ scales are bounded crudely, constant $K_0L^{n_1d}$ (as in P1 (3.131)).

### 7.4 Lean plan

Modules (all new, in `Balaban/SmallField/`; nothing imports a root):

- `Class.lean` Def-6 (families over tori, $\mathscr E^{(j)}(y,X;\cdot)$ on finite subsets of $\mathbb Z^d$, domains via I-1/I-2's $\tilde\Psi^c$ rather than $\Xi^c$, (CONT), (H.5) in the $b$-form).
- `Domains.lean`: (D1), (D2), the chain via I-2(iv). Finite arithmetic with lattice paths.
- `Potential.lean`: reduction to $f(u,v,w)$, Cauchy on the polydisc, Taylor.
- `Gradient.lean`: Steps 0, 1, 4, 5 of §2.3, identity (WI), the isotropy argument.
- `Renormalization.lean`: Theorem 2.1, Corollary 2.2.
- `Flow/RGSystem.lean`: (E1)–(E3), Lemma 3.1, Theorem 3.2 (using the landed `exists_rg_solution_triangular`, `exists_gamma_infty`, `exists_inv_betaSeq_asymptotics`), Lemma 3.3.
- `Flow/Coefficients.lean`: the explicit Fourier sums $c_1(v),c_2(v)$, formulas (5.13)–(5.14), derived at $\lambda=\infty$.
- `Fluctuation/*.lean`: §4.1 objects, I-8 (Steps 1–6).
- `Step.lean`: I-9.
- `OnePoint.lean`, `TwoPoint.lean`: X1–X7.

### 7.5 Size estimate

Using the FS82 ratio (about 3k Lean lines per dense source page) discounted where the argument here is shorter than the source:

| Package | Source pages | Lean lines |
|---|---|---|
| I-6 (Theorem 2.1, Cor 2.2, domains) | P1 §3 ≈ 33 pp.; shorter proof here | 40k–70k |
| I-7 (landed 0.7k + system, coefficients (5.4)–(5.14), Lemma 3.1, 3.3, (CONT) bookkeeping) | P4 §5 ≈ 12 pp. | 25k–40k |
| I-8 | P4 §§2,4 ≈ 30 pp. localization + P6 §4 ≈ 15 pp.; uses I-4, I-5, PE as black boxes | 70k–120k |
| I-9 (assembly; Steps 1–8, composition of constants, torus families) | P4 §§2–5 ≈ 40 pp. | 90k–160k |
| One-/two-point extension (X1–X7) | P9 §§2–3 ≈ 15 pp. | 40k–80k |
| **Total** | | **265k–470k** |

This sits inside the roadmap's 0.5–1.0M for milestone SF (which also contains P2, P3 and the Green layer). Order of work: Domains, Potential, Gradient, Renormalization (I-6, no flow needed); in parallel Flow/RGSystem (W4); then I-8 (after I-4/I-5 and PE), then I-9; X1–X7 last. I-6 and I-7 can be done before Def-6 is frozen as a predicate on abstract data.

### 7.6 Questions

1. **(Author/orchestrator) Free flow or $c=0$.** Def-7 (D2) of `LF-ARCHITECTURE.md` §3.6 writes "RG equations with $c_j=0$, $d_j=b_j$"; `CORRELATIONS.md` needs the free flow $c_{k+1}=a_{k+1}b_{k+1}$ for the exact sum rule. §3.1 shows both are admissible for I-7 and differ at second order. Recommendation: use $c=a_{k+1}b$ everywhere (P4 Prop 5.1 proves exactly this case) provided nothing in LF uses $c=0$ except $0.5<a_k<1.5$. Does LF-ARCHITECTURE's author confirm?
2. **(Author) The continuity clause (CONT).** Is it acceptable to put "terms extend continuously to $\nu=0$ in the variables $(\psi,b=\nu h)$" into Def-6 (and Def-7), as a clause that I-9 and LF-3 propagate? No source states it (§3.5; `CORRELATIONS.md` Question 1, 4).
3. **(Orchestrator) Domains.** State the analyticity domains of $\mathscr E^{(j)}$ in Def-6 by the $\psi$-level data domain $\tilde\Psi^c(\delta_j,\varepsilon_j)$ (no $\phi$ in the definition; (D1), (D2), P1 Lemma 3.2 become I-2(iv)) instead of by $\Xi^c$ of P1 (2.20)–(2.21)? The two are comparable up to constants (D1, D2). The $\tilde\Psi^c$ form is simpler to formalize; the $\Xi^c$ form is closer to the source.
4. **(Author) $\gamma_0=\frac12$.** P1 pp. 145–147 uses $\gamma_0=\min\{\frac{d-2}2,\frac12\}$ and says an improvement to $\min\{\frac{d-2}2,1\}$ needs a lengthy symmetry analysis. Any $\gamma<\frac12$ suffices for Root-F and Root-C? (Roland's batch 2: constants may be anything that works.)
5. **(Orchestrator) Numbering.** Freeze P4's numbering (H.1)–(H.7) (as in §1.3) and cite P1's in brackets, as the concordance of BIG §2.4?
6. **(Orchestrator) Form of I-8.** One whole-lattice statement (Theorem 4.1), with the modular form (holes $\Omega^c$) left to LF-3, or both forms frozen now?
7. **(seaturtle2) Hypothesis (H.5)(4).** Is P1 (H.7) / P4 (H.5)(3rd line) meant with the limit along tori of the *sum over centres* $y$ (as I read it: $G_{22}(z)=\sum_y\partial^2\mathscr E(y)/\partial\psi_2(z)\partial\psi_2(0)$)? In Theorem 2.1 I used it per centre, which is equivalent by translation invariance.
