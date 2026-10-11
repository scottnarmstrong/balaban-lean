# POLYMER: the abstract polymer-expansion theorem PE (phase 1, document D-PE)

Status: paper document, not reviewed. Mathematics on paper only. Page numbers are journal pages as
printed. Labels: **proved** (the source proves it), **cited** (the source quotes a result),
**sketched** (the source argues in outline), **this note** (proved here). Doubts are marked
"UNCERTAIN:". Notation: $\mathfrak B$ a finite set of blocks, $S_0\subset\mathfrak B$ the hole,
$\mathcal P$ polymers, $K$ activities.

## 0. Summary

One theorem PE (Kotecký–Preiss form with test objects, a hole $S_0$, activities holomorphic in
parameters) covers every cluster/polymer use of the series. Its proof uses the BKAR forest formula
(the ported public file set `Balaban/External/BKAR/`, flagship
`BKAR.bkar_formula_forestIndex_cube_contributions`) for the Penrose tree bound and the sign of the
Ursell function, a tree recursion for absolute convergence, and the exponential formula for the
identification $\Xi=\exp L$. Three companions share the proof: a Mayer layer for product measures
(MY), a marked version giving truncated expectations (PE-M, which proves P9 Prop 3.1 (3.13)), and
an activity lemma for non-small boundary terms (GAS, P7 (3.26)–(4.14)).

Findings. (i) The hole enters in two different ways. In P6 (Props 3.1–3.4 of P5) and D2 Thm F.1
the hole is a region where nothing is integrated, so polymers are compatible when they overlap
only inside it ("$\Omega$-disjoint"). In P7 §3 the hole $\Omega_k^c\cap Y_k$ is the fixed part of an
old large-field region; P7 §4 has no hole. (ii) A size function that is only a block count fails
the entropy bound (G2) with holes; one needs a tree-length (Steiner) size, §3.6. (iii) P9's
argument for (3.13) ("terms with disconnected $Y$ cancel") is not enough as written; the correct
statement is $\langle F_1;F_2\rangle^T=\sum_Y\partial_{\lambda_1}\partial_{\lambda_2}P(Y)$, §4.1.
(iv) P7's "almost completely standard" activity bound for non-small boundary terms reduces to a
short lemma (GAS) in which the volume decay $e^{-H_k|Z|}$ absorbs a fixed constant; no
condition like $H_0>2B_0K_0M^{-d}$ beyond $\beta$ large is needed in this formulation.

## 1. Every use in the series

Conventions of the series. $\mathcal D_k$ = localization domains (connected unions of blocks of
$\pi_k$), $d_k(X)$ = tree length (P5 (1.34)); $\Omega_k$ = domain where the $k$th fluctuation
integral is performed, $\Omega_k^c\subset Z_k$ (inclusions (1.20) of P5, p. 492);
$\mathcal D_k(\mathrm{mod}\,\Omega^c)$ = domains containing or missing each component of $\Omega^c$
(P5 (1.33), p. 496); $d_k(X\,\mathrm{mod}\,\Omega^c)$ P5 (1.34); the bound
$\sum_{X\in\mathcal D_k(\mathrm{mod}\Omega^c),X\supset\square}e^{-d_k(X\,\mathrm{mod}\,\Omega^c)}<K_0$
is P5 (1.35), asserted (G2 mod hole; D2 Lemma E.3, p. 90, proves the analogue).

**U1. P3 Prop 4.3, (4.41)–(4.52) (pp. 77–81).** Interpolation $\mathcal E(s{=}1)=\sum_{\mathscr C}\prod_{\square\in\mathscr C}\int ds_\square\,\partial_{s_\square}\mathcal E|_{s(\mathscr C^c)=0}$ over families of cubes, Cauchy bounds on $|s_\square|=e^{\kappa_1}$, resummation to $Y\in\mathscr D(\mathbb B_{k+1})$, counting (4.50). No gas, no compatibility relation, ordinary connectivity. This is the decoupling identity T0 (not PE). Proved in outline (the printed (4.47) exponent is garbled in the review: UNCERTAIN).

**U2. P4.** No cluster expansion is carried out. Props 2.1, 2.2 (p. 696) and 4.1, 4.2 (p. 706) state localization expansions of $E_0^{(k+1)},F_0^{(k+1)},M^{(k+1)}$ with exponent $2\kappa-3-6\kappa_0$ and defer the proofs to the later localization paper, i.e. to P6 §4 (U4). P4 (H.4), p. 677, contains the torus-independence statement for non-winding terms that Root-F's agreement clause quotes. The final integral (Sect. 6, pp. 719–720) is a plain fluctuation integral. Status: deferred.

**U3. P5 §3, Props 3.1–3.4 (pp. 514–520).** Statements of localization expansions of the expectations (3.2) (boundary term $\mathcal B''$, Prop 3.1, over $Y\in\mathcal D_{k+1}(\mathrm{mod}\,\Omega^c_{k+1})$, $Y\cap\Omega^c\ne\emptyset\ne Y\cap\Omega$, bound (3.4) $\beta_k^{-1}e^{-\frac32\kappa d(Y\,\mathrm{mod})}$); (3.9) ($V^{(k)}$, Prop 3.2, bound with $\frac12\beta_k^{-m-1}$); (3.11) ($\mathcal R_n$, Prop 3.3); (3.14), (3.15) ($E'$, $M'$, Prop 3.4: $Y\ni z$, bound constant $(NL^dB_5+1)K_0$ resp. $\beta^{-5/8+\alpha_1}(L^{-1}\eta)^{\frac{d-2}2+\gamma-\alpha_1}$). Included: "if $Y\subset\Omega''_{k+1}$ the term equals the whole-torus term" (p. 520). The cluster expansion is described as "a very simple form" (p. 515); proofs are in P6. Status: stated.

**U4. P6 §4.4–4.5 (pp. 35–44).** What is expanded: $\mathbf E_1^{(k+1)}(z)=\int_0^1ds\int d\mu_{s,0}(\psi)\,\mathcal U^{(k)}_{s,0}(z;\psi)$ (4.35)–(4.36), where $\mu_{s,0}$ is the (rescaled) free Gaussian measure, a product over sites, times $\exp\sum_Y\mathcal U(Y;\psi)$, $\mathcal U(Y;\cdot)$ localized in $Y\in\mathcal D'=\mathcal D_{k+1}(\Omega'_{k+1})$ (Lemma 4.1, bounds (4.28), (4.43): $|\tau_Y\mathcal U(Y)|<\varepsilon^{1/2}e^{-5\kappa_0d_{k+1}(Y)}$ on $|\tau_Y|=r_Y$). Steps:
1. decoupling (4.39)–(4.42) with parameters $t_Y$; connected $Z=\bigcup Y\cup Y_0$ only (components cancel, p. 36) — this is a *marked* single-function expectation, $\partial_\lambda\log\Xi_\lambda$ in PE terms;
2. tree-length estimate $d_{k+1}(Z)\le\sum(d_{k+1}(Y)+2dL)+d_{k+1}(Y_0)$ (p. 37), the volume factor $\exp(K_0\varepsilon_0M^{-d}|Z|)$ (4.45), $|Z|\le(3LM)^d(1+d_k(Z))$ (4.11) (proved pp. 25–26);
3. the denominator $Z^{(k)}_{s,0}(Z,\tau)$: polymer gas (4.46)–(4.50) over sets of *disjoint* domains in $Z$, activities (4.49) $|U(Z')|<2\cdot3^deK_0L^d\varepsilon^{1/2}e^{-(4\kappa_0-1)d(Z')}$, exponentiation (4.50) with "$\rho^T$ of [7,9]", conclusion (4.51) $|(4.46)|>e^{-1}e^{-d(Z)}$ and (4.52), (4.54) $|\mathbf E_1(z,Z)|<e^2K_0\varepsilon e^{-(2\kappa-3-6\kappa_0)d(Z)}$. Status: the gas (4.48)–(4.49) is *asserted* ("simple explicit formulas", p. 38); the bound (4.49) and (4.51) are quoted.
4. complex $\sigma$, $M^{(k+1)}$ (4.58)–(4.67): Cauchy in $\sigma$, exponent $2\kappa-4-7\kappa_0$; ER-100.
5. Hole version (pp. 43–44): "two domains $Y_1,Y_2\in\mathcal D_{k+1}(\mathrm{mod}\,\Omega^c_{k+1})$ are connected if $Y_1\cap Y_2\cap\Omega_{k+1}\ne\emptyset$"; all formulas of (4.37)–(4.54) hold "with $d_{k+1}(\cdot\ \mathrm{mod}\,\Omega^c)$". Resummations (4.55)–(4.57). Status: one sentence.
Compatibility for the gas in step 3: disjoint (no hole, $\Lambda=Z$); for step 5: $\Omega$-disjoint. Smallness: $2K_0e^{4dL\kappa}(3L)^d\varepsilon^{1/2}\le1$ (p. 38).
P6 §2 and the rest of §4 (4.1)–(4.34) construct localization expansions of the potential by P3 Prop 4.3 (T0), not by a gas; p. 44 says remaining cluster expansions "are all covered by the constructions ... of Lemma 4.1".

**U5. P7 §3, (3.26)–(3.29) (pp. 527–529).** What is expanded: $R^{(k)}\rho_k$, (3.26): the brace $\{\sum_{n\ge0}\sum_{\{Z_1..Z_n\}}\sum_{\cup(\mathbb A''\cap Z_i)}\prod_i\mathbb T''_k(Z_i,\cdot)e^{E_k|Z_i|}\exp[\mathcal B''^{(k)}(Y_k\cup\bigcup Z_i,\mathbb A''_k)]\}$. Gas variables: the large-field components $Z_i$ (activity $\mathbb T''e^{E_k|Z_i|}$, operators, very small by $e^{-p_2(\beta_k)-H_k|Z|}$, P5 (1.26), (1.31)); coupling: boundary terms $\mathcal B''$ of size $B_0$ (not small) whose domains meet $\Omega_k^c\cap Z_i$. Mayer expansion of $e^{\mathcal B''}$; "cluster" $\{X_1..X_p\}$ of connected domains, polymer $X=\bigcup X_i\cup(\bigcup Z_{i_r}^{\approx2})^{\sim2}$, $X\in\mathcal D_k(\mathrm{mod}\,\Omega_k^c\cap Y_k)$. Result (3.27): $1+\sum_n\sum_{\{X_1..X_n\}}\prod\rho''_k(X_i)$, $X_i$ disjoint; activities bounded by (1.35) with $\frac32\kappa$, $\beta_k^{-m-1}$. Exponentiation (3.28) "applying results of [9,11,13–15]", terms $P^{(k)}(X;\psi,\psi',h,g)$ with the (H.4) properties and constant $\le\frac12\beta_k^{-m}$; locality: for $X\subset Y_k^c$ the term equals the whole-lattice term "as follows from the standard formula for a term in the cluster expansion" (p. 529), $R''^{(k)}_m=P^{(k)}(\mathbb T;\cdot)$ (3.29). Hole: $S_0=\Omega_k^c\cap Y_k$ is fixed (not summed), so overlaps in $S_0$ do not couple: compatibility is $\Omega$-disjointness for the Mayer clusters. Status: "A bound of this sum is almost completely standard" (p. 528); no activity bound written; no convergence theorem stated (ER-107).

**U6. P7 §4, (4.9)–(4.14) (pp. 531–533).** Same with $Y_k=\emptyset$, $\psi_k=h$: no hole, ordinary disjointness, arbitrarily large large-field regions. Activity bound (4.12): per component $\exp(-p_2(\beta_k)-H_k|Z|+E_{k+1,0}|Z|+\frac12\varepsilon^{-2}B_0K_0M^{-d}|Z|)$, per cluster element $\varepsilon\exp(-(\frac32\kappa-\kappa_0)d_{k+1}(X_i\,\mathrm{mod}\,\Omega_{k+1}^c))$, $\varepsilon^{-2}=3^dK_0e^{\frac32dL\kappa}$, $H_k=H_0\log\beta_k$, $H_0$ large; sum (4.13) $\le\varepsilon^{-2}e^{-p_2}e^{-(\frac32\kappa-2\kappa_0-1)d_{k+1}(X)}$ using $q\ge1$; exponentiation (4.14) $\exp\sum_{X\in\mathcal D_k}P^{(k+1)}(X;h,g)$, terms $\le\frac12\beta_k^{-m-1}e^{-\kappa d_{k+1}(X)}$. Status: sketched ("very briefly").

**U7. P9 §3, Prop 3.1 (pp. 502–504).** Localization expansion of $\langle F(X;\psi^{(j)}_k(\psi^{(k)}(\theta)+z\psi'),h)\rangle_{\beta_k^{-1/2}\sigma}$ over $Y\in\mathcal D_{k+1}$, $Y\supset X$, (3.11)–(3.12), bound $CF_0e^{-\kappa_0d_j(X)}e^{-2\kappa d_{k+1}(Y)}$, activity parameters $\sigma$ ($|\sigma|<r_1$) and $z$ ($|z|<r_0$, three cases p. 503). Truncated product (3.13): $Y\supset X_1\cup X_2$ (connected), bound $CF_1F_2e^{-\kappa_0d_i(X_1)}e^{-\kappa_0d_j(X_2)}e^{-2\kappa d_{k+1}(Y)}$. P9 states (3.11) follows from [5] (that is P6), and that (3.13) "has not been proved in [5]" and follows because "the terms corresponding to disconnected domains $Y$ are cancelled" (p. 504). Status: (3.11) cited, (3.13) argued in two sentences (ER-134). Used in (3.16)–(3.26), the $R_1,R_2,R_3$ terms (3.5)–(3.10), the 2-point function.

**U8. P9 §4, (4.2)–(4.6) (pp. 514–516).** As U6 for $\log Z(g)$ at the last step $k=k(v)$: polymer expansion "by expanding in the boundary terms" (footnote 1, p. 516: P6 §4 and P7 §3), activities "bounded by arbitrary powers of $\beta_k^{-1}$", exponentiation (4.4), $|P^{(k+1)}(Y;g)|<\beta_k^{-2}e^{-2\kappa d_{k+1}(Y)}$ (4.6) (printed with $2\kappa$), $g$-derivatives (4.8), (4.9). Parameter: $g$, $\|g\|_{\ell^1}<1$. Status: cited. This is what Root-F's large-field terms come from.

**U9. Not cluster expansions but related:** P1 (H.6)–(H.7) and the thermodynamic limit (ER-010) use "independence of the torus for localized terms" (PE locality gives it for the polymer terms, §3.8). E10 (1.90)–(1.101), E7 (1.9), (2.27): gauge precedents; D1 Thm 27 (p. 39, proved except Penrose); D2 Thm F.1 (p. 91, hole version, sketch, with the $\Omega$-connectivity above). E1 Thm 2 and E11 Thm 3.4 prove the no-hole logarithm with cardinality weights via Penrose and Cayley.

Summary table of structure:

| Use | gas variables | compatibility | hole $S_0$ | parameters | conclusion used |
|---|---|---|---|---|---|
| U4 step 3 | domains $Z'\subset Z$ | disjoint | $\emptyset$ | $\tau_Y$, $\theta,h$, $\sigma$ | (e) lower bound (4.51), (a) |
| U4 steps 1,4 | same, one marked function | disjoint | $\emptyset$ | $\sigma$, $\theta,h$ | marked (PE-M), bound (4.54) |
| U4 step 5, U3 Prop 3.1, 3.3 | domains mod $\Omega^c$ | $\Omega$-disjoint | $\Omega_{k+1}^c$ | same | (c) with mod-size |
| U5 | large components + Mayer clusters | $\Omega$-disjoint | $\Omega_k^c\cap Y_k$ | $\psi,\psi',h,g$ | (a),(c),(d) + locality |
| U6, U8 | same | disjoint | $\emptyset$ | $h,g$ | (a),(c),(d) |
| U7 | domains $\supset X_1\cup X_2$ | $\Omega$-disjoint if hole | $\emptyset$ or $\Omega^c_{k+1}$ | $\sigma,z$ | PE-M two-function |

## 2. The abstract theorem PE

### 2.1 Data

* $\mathfrak B$ finite set of blocks; $S_0\subset\mathfrak B$ (hole, possibly empty); $\mathcal T:=\mathfrak B\setminus S_0$ (test objects).
* $\mathcal P$ a finite set of polymers, each a nonempty $X\subset\mathfrak B$ with $X\not\subset S_0$. (Identify polymers with supports; a polymer system with several labels per support is obtained by summing activities.)
* Incompatibility: $X\not\sim Y$ iff $(X\cap Y)\setminus S_0\ne\emptyset$ (reflexive on $\mathcal P$, symmetric). For a test object $\square\in\mathcal T$: $\square\not\sim X$ iff $\square\in X$. With $S_0=\emptyset$ this is ordinary overlap.
* Parameter set $U$ (an open subset of $\mathbb C^m$ when analyticity is wanted); activities $K:\mathcal P\times U\to\mathbb C$; $k(X):=\sup_U|K(X,\cdot)|$.
* Weights $a:\mathcal P\cup\mathcal T\to[0,\infty)$, $b:\mathcal P\to[0,\infty)$.

For $\Lambda\subset\mathcal P$, $u\in U$: $\Xi_\Lambda(u)=\sum_{\Gamma\subset\Lambda\text{ pairwise compatible}}\prod_{X\in\Gamma}K(X,u)$ (empty $\Gamma$ gives 1).
A cluster is $\mathbf X=(X_1,\dots,X_n)\in\Lambda^n$; $G(\mathbf X)$ is the graph on $\{1..n\}$ with edge $ij$ iff $X_i\not\sim X_j$. Ursell function
$\varphi^T(\mathbf X)=\sum_{G'\subset G(\mathbf X)\text{ connected spanning}}(-1)^{|E(G')|}$ (zero if $G(\mathbf X)$ is disconnected), $w(\mathbf X,u)=\varphi^T(\mathbf X)\prod_iK(X_i,u)/n!$.
The cluster $\mathbf X$ has union $\bigcup\mathbf X=\bigcup_iX_i$.

**(KP)** For all $A\in\mathcal P\cup\mathcal T$: $\displaystyle\sum_{Y\in\mathcal P,\,Y\not\sim A}k(Y)\,e^{a(Y)+b(Y)}\le a(A)$.

### 2.2 Theorem PE (this note; proof §3)

Assume (KP). For every $\Lambda\subset\mathcal P$ and $u\in U$:

(a) $L_\Lambda(u):=\sum_{n\ge1}\sum_{\mathbf X\in\Lambda^n}w(\mathbf X,u)$ converges absolutely and $\Xi_\Lambda(u)=\exp L_\Lambda(u)$.

(b) For every $A\in\mathcal P\cup\mathcal T$: $\sum_{n\ge1}\frac1{n!}\sum_{\mathbf X\in\Lambda^n:\ \exists i,\,X_i\not\sim A}|\varphi^T(\mathbf X)|\prod_ik(X_i)e^{b(X_i)}\le a(A)$.

(c) Put $P_\Lambda(Y,u)=\sum_n\sum_{\mathbf X\in\Lambda^n,\ \bigcup\mathbf X=Y}w(\mathbf X,u)$. Then $L_\Lambda=\sum_{Y\subset\mathfrak B}P_\Lambda(Y)$; $P_\Lambda(Y)=P_{\Lambda_Y}(Y)$ with $\Lambda_Y=\{X\in\Lambda:X\subset Y\}$ (locality: $P(Y,u)$ depends only on the activities of polymers inside $Y$, and on $S_0$ only through $S_0\cap Y$); $P(Y)=0$ unless $Y$ is the union of a cluster with connected $G$.

(d) If $U\subset\mathbb C^m$ is open and each $K(X,\cdot)$ is holomorphic, then $L_\Lambda$, $P_\Lambda(Y,\cdot)$ are holomorphic on $U$, with $|P_\Lambda(Y,u)|\le\sum_{\mathbf X:\bigcup\mathbf X=Y}|w|$ bounded by (b) uniformly on $U$.

(e) $\exp\!\big(-\sum_{\square\in(\bigcup\Lambda)\setminus S_0}a(\square)\big)\le|\Xi_\Lambda(u)|\le\exp\!\big(\sum_{\square\in(\bigcup\Lambda)\setminus S_0}a(\square)\big)$.

(f) (transport) If $\iota:Y\to Y'$ is a bijection of blocks with $\iota(Y\cap S_0)=Y'\cap S_0'$, carrying $\Lambda_Y$ onto $\Lambda'_{Y'}$ and $K'(\iota X,u)=K(X,u)$, then $P'(\iota Y,u)=P(Y,u)$.

### 2.3 Lattice corollary PE-L

Let $d:2^{\mathfrak B}\to[0,\infty)$ be a size and $c_1,c\ge0$, $\kappa_0>0$, $K_0<\infty$ with
(G1) $|Y\setminus S_0|\le c_1(1+d(Y))$;
(G2) $\sum_{X\in\mathcal P:\,X\ni\square}e^{-\kappa_0d(X)}\le K_0$ for every $\square\in\mathcal T$;
(G3) if $X_1..X_n\in\mathcal P$ have connected $G$, then $d(\bigcup X_i)\le\sum d(X_i)+c(n-1)$.
Suppose $|K(X,u)|\le\varepsilon e^{-\kappa d(X)}$, $\kappa\ge\kappa'+\kappa_0+c_1$, and $\alpha:=\varepsilon K_0e^{c_1+\kappa'c}\le1$. Then (KP) holds with $a(A)=\alpha|A\setminus S_0|$, $a(\square)=\alpha$, $b(X)=\kappa'(d(X)+c)$, and for every $\square\in\mathcal T$
$$\sum_{Y\ni\square}|P_\Lambda(Y,u)|\,e^{\kappa'd(Y)}\le\alpha e^{-\kappa'c}\le\alpha,\qquad |L_\Lambda|\le\alpha\,|(\textstyle\bigcup\Lambda)\setminus S_0|.$$
In particular $|P(Y,u)|\le\alpha e^{-\kappa'd(Y)}$ for every $Y$ (take any $\square\in Y\setminus S_0$).
Proof: §3.6.

### 2.4 Mayer layer MY (product measures)

Data: $\nu=\bigotimes_{x\in\Sigma}\nu_x$, $\Sigma=\bigsqcup_{b\in\mathfrak B\setminus S_0}\Sigma_b$ (sites; no variable in hole blocks); a finite set $\mathcal D$ of terms $X\subset\mathfrak B$, $X\not\subset S_0$, and $H(X,u,\Phi)$ depending on $\Phi$ only through $\Phi|_{\Sigma_{X\setminus S_0}}$, holomorphic in $u$, with $|H(X,u,\Phi)|\le H_0e^{-\kappa_hd(X)}$ on the support of $\nu$, $H_0\le\ln2$.
Define $\mathcal P$ = unions of $\mathcal D$-families $D$ whose overlap graph modulo $S_0$ is connected, and
$K(Y,u)=\int\sum_{D\subset\mathcal D:\ \bigcup D=Y,\ D\text{ connected}}\prod_{X\in D}(e^{H(X,u,\Phi)}-1)\,d\nu$.
Then (i) $\int\exp\sum_{X\in\mathcal D}H(X,u,\Phi)\,d\nu=\Xi_{\mathcal P}(u)$ (with the data $(\mathfrak B,S_0,\mathcal P,K)$ above); (ii) $K(Y,u)$ is holomorphic in $u$; (iii) with (G1)–(G3) for $\mathcal D$ (G2 summed over $\mathcal D$) and $\kappa_h=\kappa_0+\kappa_1$, $q:=2H_0K_0e^{\kappa_1c}$, $qc_1\le\frac12$: $|K(Y,u)|\le2qc_1\,e^{-(\kappa_1-3/2)d(Y)}$.
Proof: §3.7.

### 2.5 Marked version PE-M and truncated expectations

Let $\lambda=(\lambda_1..\lambda_m)\in\Delta=\prod\{|\lambda_j|<r_j\}$ and let $K(X,u,\lambda)$ be holomorphic in $(u,\lambda)$ and satisfy (KP) uniformly on $U\times\Delta$. Let $S_1..S_m\subset\mathfrak B$ and assume $K(X,u,\lambda)$ does not depend on $\lambda_j$ unless $X\supset S_j$. Then for every multi-index $\alpha$ with support $J=\{j:\alpha_j>0\}$:
(M1) $\partial_\lambda^\alpha P_\Lambda(Y,u,0)=0$ unless $Y\supset\bigcup_{j\in J}S_j$ and $Y$ is the union of a connected cluster;
(M2) $|\partial_\lambda^\alpha P_\Lambda(Y,u,0)|\le\alpha!\prod r_j^{-\alpha_j}\sup_{\lambda}|P_\Lambda(Y,u,\lambda)|$, and so, in the setting of PE-L, $\sum_{Y\ni\square}|\partial^\alpha_\lambda P(Y)|e^{\kappa'd(Y)}\le\alpha!\prod r_j^{-\alpha_j}\,\alpha_{\rm PE}$.
(M3) $\partial_\lambda^\alpha\log\Xi_\Lambda(u,\lambda)|_{\lambda=0}=\sum_Y\partial^\alpha_\lambda P_\Lambda(Y,u,0)$ for $|\alpha|\ge1$ (any analytic branch).
Proof §3.8. Truncated expectations: §4.1.

### 2.6 Lemma GAS (non-small boundary terms)

Data: $S_0$, polymers as above; a finite set $\mathcal Z$ of heavy objects $Z\subset\mathfrak B$ with cores $c(Z)\subset Z$, weights $\tau(Z,u)$; a finite set $\mathcal Y$ of couplings $Y\subset\mathfrak B$ with $B(Y,u)$. Partition function
$\Xi=\sum_{\Gamma\subset\mathcal Z\text{ pairwise disjoint}}\prod_{Z\in\Gamma}\tau(Z)\exp\sum_{Y:\,Y\cap c(\Gamma)\ne\emptyset}B(Y)$, $c(\Gamma)=\bigcup_{Z\in\Gamma}c(Z)$, and $Z\cap S_0=\emptyset$. Polymers: pairs $(D,\Gamma_0)$, $D\subset\mathcal Y$, $\Gamma_0\subset\mathcal Z$ pairwise disjoint, every $Y\in D$ meeting $c(\Gamma_0)$, contact graph (Y–Y' if $(Y\cap Y')\setminus S_0\ne\emptyset$; Y–Z if $Y\cap Z\ne\emptyset$) connected; support $\bigcup D\cup\bigcup\Gamma_0$, activity $K=\prod\tau(Z)\prod(e^{B(Y)}-1)$. Hypotheses: $|B(Y,u)|\le B_0e^{-\kappa''d(Y)}$; $|\tau(Z,u)|\le e^{-p-h\,v(Z)}$ with $v(Z)=|Z|$ (blocks); (G1)–(G3) for $d$ with $d(Z)\le c_2v(Z)$ and $\sum_{Y\ni\square}e^{-(\kappa''-\kappa')d(Y)}\le K_0'$. Put $C=B_0e^{B_0}e^{\kappa'c}K_0'$. If $h\ge C+\kappa'c_2+c_1+2+\ln(K_0'')$ for the entropy constant $K_0''$ of heavy objects through a block, then $\Xi=\Xi_{\mathcal P}$ and $|K(X)|\le e^{-p}\,3c_1\,e^{-\kappa'd(X)}$. Proof §3.9. The extra entropy hypothesis (number of $Z\ni\square$ of volume $v$ is $\le K_0''^{\,v}$) holds by lattice animals.

## 3. Proof

### 3.1 Ursell function from BKAR (sign and Penrose bound)

Let $\zeta_{ij}=\mathbf 1[X_i\not\sim X_j]\in\{0,1\}$, $V=\{1..n\}$, and $\rho(s)=\prod_{i<j}(1-s_{ij}\zeta_{ij})$ on $\mathbb R^{\mathrm{Edge}\,V}$ (a polynomial, hence $C^\infty$). Used form of BKAR: `BKAR.bkar_formula_forestIndex_cube_contributions`, $\rho(\mathbf 1)=\sum_F\int_{[0,1]^{E(F)}}\partial_{E(F)}\rho(x^F(u))\,du$ over acyclic edge sets $F$ (empty $F$ gives $\rho(\mathbf 0)=1$), where $x^F(u)_e$ is the minimum of $u$ along the $F$-path (0 across components); `standardInterp_mem_Icc` gives $x^F_e\in[0,1]$. Since $\rho$ is affine in each coordinate, $\partial_{E(F)}\rho(x)=\prod_{e\in F}(-\zeta_e)\prod_{e\notin F}(1-x_e\zeta_e)$.

*Step 1.* Both sides factor over the components $B_1..B_r$ of $F$ (edges between components have $x_e=0$, factor 1; inside a component $x^F$ depends only on that component's parameters). Hence $\rho(\mathbf 1)=\sum_\pi\prod_{B\in\pi}t(B)$ over set partitions $\pi$ of $V$, with
$t(B)=\sum_{T\text{ spanning tree of }K_B}(-1)^{|B|-1}\prod_{e\in T}\zeta_e\int_{[0,1]^T}\prod_{e\notin T}(1-x^T_e(u)\zeta_e)\,du$ ($t(\{i\})=1$).
*Step 2.* Directly, $\rho(\mathbf 1)=\sum_{G'\subset G}(-1)^{|G'|}=\sum_\pi\prod_B\varphi^T(X_B)$ (split $G'$ into components).
*Step 3.* Induction on $|V|$ (both $t$ and $\varphi^T$ of a block use only $\zeta$ restricted to it) gives $t=\varphi^T$.
Consequences: $(-1)^{n-1}\varphi^T(\mathbf X)\ge0$ and $|\varphi^T(\mathbf X)|\le\tau(G(\mathbf X))$, the number of spanning trees of $G(\mathbf X)$ (each integrand lies in $[0,1]$). This is the step D1 Thm 27 leaves out (p. 42) and E1/E11 take from Penrose. It uses only the real-valued BKAR formula; activities are complex but $\varphi^T$ is real.

### 3.2 Exponential formula

With $\zeta_{ii}=1$ (reflexive), $\Xi_\Lambda(z)=\sum_n\frac1{n!}\sum_{\mathbf X\in\Lambda^n}\prod_{i<j}(1-\zeta_{ij})\prod z_{X_i}$, since repeated entries kill the term and each compatible set arises $n!$ times. Expanding as in §3.1 Step 2 and grouping by set partitions, as formal power series in the variables $z_X$: $\Xi_\Lambda=\exp\big(\sum_n\frac1{n!}\sum_{\mathbf X}\varphi^T(\mathbf X)\prod z_{X_i}\big)$ (exponential formula; not in Mathlib; proof by removing the block containing the element 1).

### 3.3 Tree recursion (absolute convergence, (b))

Put $\kappa(Y)=k(Y)e^{b(Y)}$. For a root $A\in\mathcal P\cup\mathcal T$ let $F^{(h)}(A)$ be the sum over $n\ge0$, $(Y_1..Y_n)\in\mathcal P^n$ and trees on $\{0..n\}$ of height $\le h$ rooted at $0$ ($Y_0=A$), every tree edge $ij$ having $Y_i\not\sim Y_j$, of $\frac1{n!}\prod_{i\ge1}\kappa(Y_i)$. Then $F^{(0)}=1$ and, decomposing at the root (children, each with its own planted subtree; labelled counting gives the exponential),
$$F^{(h+1)}(A)=\exp\Big(\sum_{Y\not\sim A}\kappa(Y)F^{(h)}(Y)\Big).$$
Induction with (KP): $F^{(h)}(Y)\le e^{a(Y)}$ for all $Y\in\mathcal P$, $h\ge0$ ($F^{(0)}=1\le e^{a}$; and $\sum_{Y\not\sim A}\kappa(Y)e^{a(Y)}\le a(A)$). The limit $F=\sup_hF^{(h)}\le e^a$ is the sum over all trees.
For (b): $\mathbf 1[\exists i\,X_i\not\sim A]\le\sum_i\mathbf 1[X_i\not\sim A]$, symmetry in the ordering, and $|\varphi^T|\le\tau(G)$ give
$\sum_n\frac1{n!}\sum_{\exists i}|\varphi^T|\prod\kappa(X_i)\le\sum_{X_1\not\sim A}\kappa(X_1)\sum_{n\ge1}\frac1{(n-1)!}\sum_{X_2..X_n}\tau(G(\mathbf X))\prod_{i\ge2}\kappa(X_i)=\sum_{X_1\not\sim A}\kappa(X_1)F(X_1)\le\sum_{Y\not\sim A}\kappa(Y)e^{a(Y)}\le a(A)$ (the spanning-tree count equals the count of trees rooted at 1).

### 3.4 Part (a)

Absolute convergence: every cluster has $X_1\not\subset S_0$, so it touches some $\square\in\mathcal T$, and $\sum|w|\le\sum_{\square\in\bigcup\Lambda\setminus S_0}\sum_{\text{clusters}\sim\square}|w|\le\sum_\square a(\square)<\infty$ by (b). Identification: replace $K$ by $sK$, $|s|\le1$ ((KP) is monotone in $k$). $L(s)=\sum_ns^nL_n$ converges absolutely for $|s|\le1$; $\Xi(sK)$ is a polynomial in $s$; §3.2 says $\exp(\sum s^nL_n)$ and $\Xi(sK)$ have the same formal coefficients, and for $|s|<1$ the Cauchy product of absolutely convergent series equals the composition. So equality on $|s|<1$; both sides are continuous on $|s|\le1$; take $s=1$. This avoids multi-variable identity theorems.

### 3.5 Parts (c)–(f)

(c): grouping by the union. Locality: a cluster with union $Y$ uses only polymers inside $Y$, and compatibility of such polymers depends only on $S_0\cap Y$. Vanishing: $\varphi^T=0$ unless $G$ connected. (d): each cluster term is a polynomial in the $K(X_i,u)$; partial sums over $n$ are holomorphic and converge uniformly on $U$ by (b) (Weierstrass; in Lean `differentiableOn_tsum_of_summable_norm`). (e): $|\Xi|=e^{\mathrm{Re}L}$, $|\mathrm{Re}\,L|\le|L|\le\sum_\square a(\square)$. (f): immediate from the definition of $P$.

### 3.6 Proof of PE-L, and the geometry (G1)–(G3)

Write $\sum_{Y\not\sim A}\le\sum_{\square\in A\setminus S_0}\sum_{Y\ni\square}$ (if $Y\not\sim A$ then $Y$ contains a block of $A\setminus S_0$). For $Y\ni\square$: $a(Y)\le\alpha c_1(1+d(Y))\le c_1(1+d(Y))$ by (G1), so $k(Y)e^{a(Y)+b(Y)}\le\varepsilon e^{c_1+\kappa'c}e^{(c_1+\kappa'-\kappa)d(Y)}\le\varepsilon e^{c_1+\kappa'c}e^{-\kappa_0d(Y)}$; sum with (G2): $\le\alpha$. Hence $\le\alpha|A\setminus S_0|=a(A)$; for $A=\square$ the bound is $\alpha=a(\square)$. For $Y\ni\square$ and a cluster with $\bigcup\mathbf X=Y$, some $X_i\ni\square$, and by (G3) $\sum b(X_i)=\kappa'(\sum d(X_i)+cn)\ge\kappa'(d(Y)+c)$, so (b) with $A=\square$ gives $\sum_{Y\ni\square}|P(Y)|e^{\kappa'(d(Y)+c)}\le\alpha$. $\square$

**Geometry (what must be checked for an instance).** Take $\mathfrak B$ the block torus of side $ML^j$ with nearest-neighbour adjacency (degree $\le2d$; this is the adjacency of `IsPolymer`: two sites adjacent in $\mathbb Z^d$ lie in the same or in face-adjacent blocks).

*No hole* ($S_0=\emptyset$, $\mathcal P$ = connected block sets). Size $d(X)=|X|$ (number of blocks, as in the frozen `IsPolymer` and Root-F's $e^{-\kappa|X|/(ML^j)^d}$). (G1) $c_1=1$ (with the $+1$ unused); (G3) $|\bigcup X_i|\le\sum|X_i|$, $c=0$; (G2) the animal bound $\#\{X\ni\square:|X|=n\}\le(2d)^{2(n-1)}$ (`card_animals_latticeGraph_le`, proved in the author's FroehlichSpencer development, reused as a public dependency; note it gives the bound for the lattice $\mathbb Z^d$, to be transferred to the block torus). So $K_0\le\sum_n(2d)^{2(n-1)}e^{-\kappa_0n}$, finite for $\kappa_0>2\ln(2d)$. Sources give decay in tree length; $|X|\le(3LM)^d(1+d_k(X))$ (P6 (4.11), proved) converts: decay in $d_k$ with rate $\kappa$ gives decay in $|X|$ at rate $\kappa/(3LM)^d$ (units: blocks of side $M$ here).

*Hole.* The block count fails (G2): if $\Omega^c$ has a huge component $C$ with $m$ adjacent blocks of $\Omega$, then $X=C\cup(\text{any subset of those blocks})$ is connected, giving $\binom mn$ polymers with $|X\setminus S_0|=n$. Take as size the Steiner size $d_{S_0}(X)=\mu(X\setminus S_0)$, $\mu(Y)=\min\{|W|:W\supset Y,\ W$ nn-connected in $\mathfrak B\}$. Then (G1) $|X\setminus S_0|\le\mu$, $c_1=1$; (G3): if $X_1,X_2$ share a block outside $S_0$ then $W_1\cap W_2\ne\emptyset$ and $W_1\cup W_2$ is connected, so $\mu\big((X_1\cup X_2)\setminus S_0\big)\le\mu_1+\mu_2$, $c=0$; (G2) (this is D2 Lemma E.3, p. 90, with this size): given $Y=X\setminus S_0$, $X=Y\cup\{\text{whole components of }S_0\text{ adjacent to }Y\}$ and $Y$ has at most $2d|Y|$ adjacent components (distinct components are not adjacent), so at most $2^{2d|Y|}$ polymers; the number of $Y\ni\square$ with $\mu(Y)=n$ is $\le(2d)^{2(n-1)}2^n$ (subsets of animals $W$). Sum: finite for $\kappa_0$ large. Comparison with Balaban's $d_k(X\,\mathrm{mod}\,\Omega^c)$ (tree inside $X$ meeting every cover cube meeting $X\cap\Omega$, P5 (1.34)): a tree inside $X$ plus, in each touched cover cube, connecting paths of $\le d(L^2M)$ blocks gives $\mu(X\setminus S_0)\le C(d,L,M)(1+d_k(X\,\mathrm{mod}\,\Omega^c))$. So bounds in $d_k(\cdot\ \mathrm{mod})$ with rate $\kappa$ give bounds in $\mu$ with rate $\kappa/C$. UNCERTAIN: the constants $C$ and whether the series fixes $\kappa$ large enough after $L,M$; the series says $\kappa$ is arbitrary large depending on $M$.

*P7 §4 with volume weights.* If holes carry the volume decay $e^{-H|Z|}$ one may take $S_0=\emptyset$ and the size $d'(X)=\mu(X\setminus S_0)+|X\cap S_0|$, for which (G1)–(G3) are immediate and (G2) holds as above.

### 3.7 Proof of MY

(i) $e^{\sum H}=\prod_X(1+f_X)=\sum_{D\subset\mathcal D}\prod_{X\in D}f_X$, $f_X=e^{H(X)}-1$ (a *set* $D$ of distinct terms). Split $D$ into components of the overlap-modulo-$S_0$ graph; the unions of different components are $S_0$-disjoint, and conversely any collection of pairwise compatible unions with their families recombines to a $D$ whose components are those families. This gives $\sum_{\Gamma}\prod_{Y\in\Gamma}K(Y,\Phi)$ with $K(Y,\Phi)=\sum_{D\text{ connected},\bigcup D=Y}\prod f_X$, depending on $\Phi$ only through $\Sigma_{Y\setminus S_0}$. Pairwise compatible $Y$'s have disjoint $Y\setminus S_0$, so the factors are functions of disjoint sets of independent variables and $\int\prod K=\prod\int K$. (D1 (300)–(311), D2 (639)–(645); in D1 there is no hole.)
(ii) dominated convergence/Morera. (iii) $|f_X|\le2|H|$ for $|H|\le\ln2$. Write $D$ as an ordered tuple ($n!$ orderings, dropping distinctness only enlarges): $|K(Y)|\le\sum_n\frac1{n!}\sum_{(X_i):\bigcup=Y,\text{conn}}\prod2H_0e^{-(\kappa_0+\kappa_1)d(X_i)}$. By (G3) $\prod e^{-\kappa_1d(X_i)}\le e^{-\kappa_1d(Y)}e^{\kappa_1c(n-1)}$; then drop the constraint to $X_i\subset Y$ and use (G2): $\sum_{X\subset Y}2H_0e^{-\kappa_0d(X)}\le2H_0K_0|Y\setminus S_0|$. So $|K(Y)|\le e^{-\kappa_1d(Y)}e^{-\kappa_1c}(e^{q|Y\setminus S_0|}-1)\le e^{-\kappa_1d(Y)}q|Y\setminus S_0|e^{q|Y\setminus S_0|}$ and by (G1) with $qc_1\le\frac12$: $\le qc_1(1+d)e^{(1+d)/2}e^{-\kappa_1d}\le2qc_1e^{-(\kappa_1-3/2)d(Y)}$. $\square$ (Compare D1 (306)–(307).)

### 3.8 Proof of PE-M

$K(X,u,\lambda)$ is a function of $\lambda_j$ only if $X\supset S_j$. A cluster term $w(\mathbf X,u,\lambda)$ has $\partial_{\lambda_j}w\ne0$ only if some $X_i\supset S_j$; so $\partial^\alpha_\lambda w=0$ unless the union contains all $S_j$, $j\in J$ (M1). (M2) is the Cauchy estimate in each $\lambda_j$ on circles of radius $r_j'<r_j$ ($r_j'\uparrow r_j$) applied to the holomorphic function $P(Y,u,\cdot)$, which is bounded by (d). (M3): $\Xi=e^{L}$ near $\lambda=0$ (§3.4), so $\log\Xi=L+$const and the derivatives of $L$ are those of $\sum_YP(Y)$; termwise differentiation is justified by the uniform bound and Cauchy.

### 3.9 Proof of GAS

Expand $\exp\sum_{Y\text{ active}}B=\prod_{Y:Y\cap c(\Gamma)\ne\emptyset}(1+f_Y)$, $f_Y=e^{B(Y)}-1$, $|f_Y|\le|B|e^{|B|}\le B_0e^{B_0}e^{-\kappa''d(Y)}$. Group $(D,\Gamma)$ by connected components of the contact graph; a $Y$ meeting $c(\Gamma)$ lies in the component of that heavy object. Different components have no contact, i.e. pairwise $S_0$-disjoint couplings and disjoint heavy objects, and no coupling of one meets a heavy object of another, which is the polymer compatibility. This is the identification $\Xi=\Xi_{\mathcal P}$. Activity bound: by (G3) on the contact graph, for $X=(D,\Gamma_0)$, $d(X)\le\sum_{Z}d(Z)+\sum_{Y}(d(Y)+c)$ (up to $c\cdot(\#Z)$ absorbed into $c_2$), so
$e^{\kappa'd(X)}|K(X)|\le\prod_Z|\tau(Z)|e^{\kappa'c_2v(Z)}\prod_{Y\in D}|f_Y|e^{\kappa'(d(Y)+c)}.$
Sum over $D$ for fixed $\Gamma_0$ (each $Y$ meets $c(\Gamma_0)$): $\le\exp\big(\sum_{\square\in c(\Gamma_0)}\sum_{Y\ni\square}|f_Y|e^{\kappa'(d(Y)+c)}\big)\le e^{C\,v(\Gamma_0)}$. Hence $e^{\kappa'd(X)}|K(X)|\le\sum_{\Gamma_0\subset X}\prod_Ze^{-p-(h-C-\kappa'c_2)v(Z)}$. Let $\eta:=\sum_{Z\ni\square}e^{-p-(h-C-\kappa'c_2)v(Z)}\le e^{-p}\sum_vK_0''^ve^{-(h-C-\kappa'c_2)v}\le e^{-p}e^{-c_1-2}$ by the choice of $h$. Since every polymer has at least one heavy object, $\sum_{\Gamma_0\ne\emptyset,\subset X}\le\eta|X\setminus S_0|e^{\eta|X\setminus S_0|}\le\eta c_1(1+d(X))e^{c_1\eta(1+d(X))}$; as $c_1\eta\le e^{-p-2}\le\frac1{7}$, this is $\le e^{-p}\cdot3c_1\,e^{d(X)\cdot\kappa'}\cdot e^{-\kappa'd(X)}$ after replacing $\kappa'$ by $\kappa'+2$ in the bookkeeping (the factors $(1+d)e^{d/7}\le e^{2d}$). This gives $|K(X)|\le3c_1e^{-p}e^{-\kappa'd(X)}$ with $\kappa'$ lowered by 2. $\square$ UNCERTAIN: the constant bookkeeping in the last line (the loss of 2 in the rate) should be redone when stated in Lean. The mechanism is the point: the fixed constant $C=B_0e^{B_0}e^{\kappa'c}K_0'$ is absorbed by $h=H_k\to\infty$ with $\beta$.

### 3.10 Proof route comparison

* BKAR/tree route (above). New Lean: $\sim$ Penrose and sign from BKAR, exponential formula, tree recursion, series identification. Gives (a)–(e) with the sharp absolute bound (b) directly, and uses real-valued BKAR only.
* Kotecký–Preiss/Dobrushin induction. One proves, by induction on $|\Lambda|$, $\Xi_\Lambda\ne0$ and $|\Xi_\Lambda/\Xi_{\Lambda\setminus\{X\}}|$ bounds from $|K(X)|\le c_X/\prod_{Y\not\sim X}(1+c_Y)$ (short, no trees). But (b), (c) require absolute convergence, which needs either Penrose (the sign property then identifies $\sum|w|e^b$ with $-\log\Xi_{-|K|e^b}$ and one uses the ratio bound) or complex analysis of $\log\Xi$ in a polydisc (Taylor coefficients, a multi-variable Cauchy theory that Mathlib supports poorly). Not shorter overall; it needs the BKAR sign anyway. Recommendation: tree route.

## 4. Corollaries

### 4.1 Truncated expectations: P9 Prop 3.1 (this note)

Setting: $\nu$ product measure, terms $H_0(Y)$ as in MY (the localization expansion of the potentials of P6 Lemma 4.1 / (4.24)), and functions $F_j(X_j;\cdot)$, $j=1,2$, each with a localization expansion $F_j=\sum_{Y_1\supset X_j}G_j(Y_1,\Phi)$, $|G_j(Y_1)|\le F_{0,j}e^{-\kappa_0d_j(X_j)}e^{-2\kappa d(Y_1)}$ (the form produced by P3 Prop 4.3). Let $\langle\cdot\rangle$ be the expectation for $e^{\sum H_0}d\nu/\Xi(0)$. Put $H_\lambda(Y_1)=H_0(Y_1)+\sum_j\lambda_jG_j(Y_1)$. Then $\Xi(\lambda)=\int e^{\sum H_\lambda}d\nu$ and
$$\langle F_1\rangle=\partial_{\lambda_1}\log\Xi|_0,\qquad\langle F_1;F_2\rangle^T=\partial_{\lambda_1}\partial_{\lambda_2}\log\Xi|_0 .$$
*One function ((3.11)).* Choose $r_1=\theta F_{0,1}^{-1}e^{\kappa_0d_j(X_1)}$ with $\theta$ small; then $|\lambda_1G_1(Y_1)|\le\theta e^{-2\kappa d(Y_1)}$, a potential of the same type as $H_0$, so MY and PE-L apply uniformly in $|\lambda_1|<r_1$ (the activity of a polymer depends on $\lambda_1$ only if it contains $X_1$). PE-M gives $\langle F_1\rangle=\sum_{Y\supset X_1}\partial_{\lambda_1}P(Y)$, $|\partial_{\lambda_1}P(Y)|\le\theta^{-1}F_{0,1}e^{-\kappa_0d_j(X_1)}\alpha e^{-\kappa'd(Y)}$. This reproduces (3.12) with $\kappa'\to2\kappa$ minus the losses of MY ($\kappa_1-\frac32$ and $\kappa'$), the constant $C$ depending on $d$ only through $c_1,K_0$.
*Two functions ((3.13)).* Same with $r_1,r_2$; (M1) says $\partial_{\lambda_1}\partial_{\lambda_2}P(Y)\ne0$ only if some cluster element contains $X_1$ and some contains $X_2$, hence $Y\supset X_1\cup X_2$ and $Y$ is a union of a connected cluster; (M2): $|\partial_1\partial_2P(Y)|\le r_1^{-1}r_2^{-1}\sup|P|\le CF_{0,1}F_{0,2}e^{-\kappa_0d_i(X_1)}e^{-\kappa_0d_j(X_2)}e^{-\kappa'd(Y)}$, the bound of (3.13). Parameters $\sigma$ ($|\sigma|<r_1$) and $z_1,z_2$ are carried as the parameter $u$ (all bounds uniform; a function holomorphic on a product of discs). Hole version: replace $\mathcal D$ by $\mathcal D(\mathrm{mod}\,\Omega^c)$, $d$ by $\mu$.
*Remark on P9's argument (p. 504).* For $\langle F_1F_2\rangle=\partial_1\partial_2\Xi/\Xi$ one has $\partial_1\partial_2e^{\Delta L}|_0=\partial_1\partial_2L+\partial_1L\,\partial_2L$; the product term has support $Y_1\cup Y_2$ with $Y_1,Y_2$ possibly overlapping, so connectedness of $Y$ alone does not separate the truncated part. The truncated expectation is exactly $\partial_1\partial_2L$. UNCERTAIN: whether P9 intends the expansion of $\langle F_1F_2\rangle$ organised so that overlapping terms are already counted as products; the statement proved here is not affected.

### 4.2 P6 (4.46)–(4.54)

(4.46)–(4.48) is MY with $S_0=\emptyset$, $\mathcal D=\mathcal D'$, $H(Y)=\tau_Y\mathcal U(Y;\psi)$, $H_0=\varepsilon^{1/2}$-type, $d=d_{k+1}$ or the block count, $\kappa_h=5\kappa_0$; (4.49) is MY (iii); (4.50)–(4.51) are PE (a), (e) with the volume bound from (G1) (P6 (4.11)). (4.35)–(4.42), (4.52)–(4.54): PE-M with one function $U(z,\cdot)$ (§4.1), the Cauchy radius $r=\varepsilon^{-1}$-type playing the role of P6's $\varepsilon$ in front. Differences from the printed constants (exponent $2\kappa-3-6\kappa_0$) come from the order of resummation; any exponent $\ge\frac12\kappa+O(1)$ suffices for (H.7). Requirements to verify in the instance: (1) the small-field characteristic function $\chi^{(k)}$ factorizes over sites (P6 review item 10, UNCERTAIN); (2) $\mathcal U(Y;\psi)$ depends on $\psi$ only in $Y\cap\Omega''^c$ and is holomorphic in $\tau,\theta,h,\sigma$ on a common domain with the stated bound for all $\psi$ in the support.

### 4.3 P7 (3.26)–(3.29), (4.11)–(4.14)

Apply GAS. Heavy objects $Z$ = large-field components (with halos $Z^{\approx2\sim2}$ in the supports), cores $\Omega_k^c\cap Z$, $\tau=\mathbb T''e^{E_k|Z|}$ evaluated pointwise in the external variables $u=(\psi,\psi',h,g)$ (operators acting on disjoint variable sets compose to products of activities; $|\mathbb T''(Z)F|\le e^{-p_2-H_k|Z|}\sup|F|$, P5 (1.31), (4.10)); couplings $Y$ = terms of $\mathcal B''$ with $|B(Y)|\le B_0e^{-\frac32\kappa d(Y\,\mathrm{mod})}$ (via (1.35) with $\frac32\kappa$). Output: activity $|K(X)|\le e^{-p_2}3c_1e^{-\kappa'd(X)}$ once $H_k=H_0\log\beta_k$ exceeds $C+\kappa'c_2+c_1+2+\ln K_0''$, which holds for $\beta$ large because $B_0,\kappa,K_0,L,M$ are fixed before $\beta$ (order of constants, roadmap §4.4). Then PE-L with $\varepsilon=3c_1e^{-p_2(\beta_k)}$ ($\alpha\le\frac12\beta_k^{-m-1}$ for large $\beta$ since $p_2$ grows like a power of $\log\beta_k$) gives (3.28): $\exp P^{(k)}$, $P^{(k)}(X;u)$ holomorphic, local in $u|_X$, bound $\frac12\beta_k^{-m-1}e^{-\kappa'd(X)}$, with $S_0=\Omega_k^c\cap Y_k$ in (3.27)–(3.28) and $S_0=\emptyset$ in (4.14). Locality for $X\subset Y_k^c$ equal to the whole-lattice term (p. 529) is PE (c) (locality) plus the instance fact that activities of polymers inside $Y_k^c$ do not depend on $Y_k$ (the cancellation stated at p. 527: terms of $\mathcal B''$ with domains disjoint from the cores drop out).
The printed hypothesis $H_0>2B_0K_0M^{-d}$ is not needed in GAS beyond $\beta$ large; P7's $\varepsilon$ is replaced by the explicit constants of GAS.

### 4.4 From $P$ to Root-F's $T_j(x,X;g)$

For $\|g\|_{\ell^1}<1$ let $P(X;g)$ be holomorphic with $|P|\le M_X$ on the open ball and $P(X;g)$ depending on $g|_X$ only. Then $P(X;g)-P(X;0)=\sum_{x\in X}\sum_ig_x^i\int_0^1\partial_{g_x^i}P(X;tg)\,dt$, and for $\|g\|\le\frac12$, Cauchy on the disc of radius $\frac12$ in the variable $g_x^i$ (contained in the ball) gives $|\partial_{g_x^i}P(X;g)|\le2M_X$. This gives analyticity on the open ball and the bound on $\|g\|\le\frac12$ asked for in Root-F, for the large-field and the $\mathcal R$-polymer terms (P9 (4.4)–(4.6): $M_X=\beta_k^{-2}e^{-2\kappa d(X)}$; the factor $L^{-j((d-2)/2+\delta)}$ follows from $\beta_k^{-2}\le L^{-2k(d-2)}\beta^{-2}$).

### 4.5 Torus independence (needed by Root-F's agreement clause)

From PE (f) (transport): a block set $Y$ contained in a box $\{|y_\mu|<\min(\ell,\ell')/4\}$ with $ML^{j}\mid\ell,\ell'$ is identified with the same set of blocks in both tori (block $=\lfloor y_\mu/s\rfloor$, consistent for negative $y$ since $s\mid\ell,\ell'$); polymers inside $Y$ and their incompatibility relation are the same (box side $<\ell/2$, so no wrap-around adjacency). If $K_\ell(X,u)=K_{\ell'}(X,u)$ for all polymers $X\subset Y$, then $P_\ell(Y,u)=P_{\ell'}(Y,u)$. The instance must supply the equality of activities of polymers in the box: this is the inductive hypothesis "terms independent of the torus for non-winding domains" (P4 (H.4) p. 677; ER-010), which must be carried in the inductive class (Def-7). PE does not prove it; it propagates it.

## 5. Instantiation table

| Use | PE data | Hypotheses and verification | Gap |
|---|---|---|---|
| U4 step 3 (P6 (4.46)–(4.51)) | MY + PE-L, $S_0=\emptyset$, $d=|\cdot|$ or $d_{k+1}$ | $|H|\le\varepsilon^{1/2}e^{-5\kappa_0d}$ given (4.47); (G1)–(G3) P6 (4.11), (4.45), (4.43) tree argument; smallness $2K_0e^{4dL\kappa}(3L)^d\varepsilon^{1/2}\le1$ | site-factorization of $\chi^{(k)}$ not stated (item 10); complex $\tau_Y$ handled as parameter |
| U4 steps 1,4 (P6 (4.35)–(4.54)) | PE-M one function | radius $r$; hypotheses as above; $\sigma$-analyticity from (d) | exponent differs (3.1.. see 4.2); $M$-part needs the extra Cauchy in $\sigma$ (ER-100) |
| U4 step 5, U3 Props 3.1, 3.3 | MY with hole $S_0=\Omega^c_{k+1}$, size $\mu$ | $\Omega$-connectivity (P6 p. 44); (G1)–(G3) §3.6 | comparison $\mu$ vs $d_k(\cdot\,\mathrm{mod})$ constants UNCERTAIN; (1.35) is cited by P5 |
| U3 Prop 3.2, 3.4 | MY, $S_0=\emptyset$ (3.4) | marked $z\in Y$ | as U4 |
| U5 (P7 (3.26)–(3.29)) | GAS with $S_0=\Omega_k^c\cap Y_k$, then PE-L | $\tau$ bound (P5 (1.31)), $B''$ bound; (G1)–(G3) mod hole | depends on the definition of $\mathbb T''$ and the large-field class (D-LF); $H_k$ vs constants order |
| U6 (P7 (4.11)–(4.14)) | GAS, $S_0=\emptyset$ | same; large components of arbitrary size need $v(Z)$ weights | same |
| U7 (P9 Prop 3.1) | PE-M, two functions | $F_j$ expansions (P3 Prop 4.3 in the form of §4.1), radii $r_j$ | need that P3 Prop 4.3 yields $G_j(Y_1)$ with the bound $e^{-\kappa_0d(X)}e^{-2\kappa d(Y_1)}$ and holomorphy in $z$ |
| U8 (P9 (4.2)–(4.6)) | GAS as U6 with $u=g$ | $\ell^1$ ball $<1$; $\mathbb T$ bound uniform in $g$ | uniformity in $g$ of boundary terms (ER-135) |
| U2 (P4 Props 2.1, 2.2, 4.1, 4.2) | via U4 | deferred to P6 | none new |
| U1 (P3 (4.41)) | not PE (T0) | $F(1)=\sum_{C}\int\partial^CF(s_C,0)$ is a Taylor/Möbius identity | separate lemma |

Exponent bookkeeping: every instance loses a bounded amount of $\kappa$ in MY ($\kappa_1-\frac32$) and in PE-L ($\kappa\ge\kappa'+\kappa_0+c_1$); all are absorbed because $\kappa$ is chosen large after $L,M$ (P5 (H.7) discussion; ER-100 records that the printed exponents are weaker than $2\kappa$).

Uses NOT covered by PE: U1 (needs T0, a different identity); the E10/gauge uses are outside the series. Everything else is covered, provided the instance hypotheses above are verified in the large-field reconstruction.

## 6. Lean plan

Order (module group `Balaban/Infra/Polymer/`):
1. `Cluster.Defs`: incompatibility graphs from a symmetric reflexive relation; Ursell function $\varphi^T$ over connected spanning edge sets; clusters; $w$. (about 300 lines)
2. `Cluster.ExpFormula`: set-partition exponential formula; $\Xi=\exp$ at the level of formal power series in finitely many variables or via the one-variable $s$-series. (500)
3. `Cluster.BKARApply`: mixed partial of $\prod_{i<j}(1-s_{ij}\zeta_{ij})$ along a forest (product of affine coordinates; induction over the edge list of `mixedPartialList`), factorization of the forest sum over components, induction giving $t=\varphi^T$, sign and Penrose bound. Uses `BKAR.bkar_formula_forestIndex_cube_contributions`, `standardInterp_mem_Icc` from `Balaban/External/BKAR/` (18,686 lines; toolchain port done by the orchestrator). (700)
4. `Cluster.TreeBound`: tree-count recursion by height, KP bound (b). (800)
5. `PE`: (a), (c)–(f); analytic identification via the $s$-series (Mathlib: `DifferentiableOn` for tsum). (500)
6. `PE.Lattice`: PE-L; geometry: nn block adjacency on the torus, `IsPolymer`-connectedness vs block adjacency, animals (G2) from `card_animals_latticeGraph_le` (the author's public FroehlichSpencer development; the transfer from $\mathbb Z^d$ to the block torus needs a covering argument), Steiner size $\mu$, (G1)–(G3) with hole, the $2^{2d|Y|}$ count. (700)
7. `PE.Mayer`: MY, with product-measure factorization (Mathlib `Measure.pi`, independence on disjoint coordinate sets). (600)
8. `PE.Marked`: PE-M by Cauchy (`Complex.norm_deriv_le_of_forall_mem_sphere_norm_le` style), the two-function corollary. (300)
9. `PE.Gas`: GAS. (400)
10. `PE.Torus`: transport lemma and the box identification. (200)
Total new: about 5,000 lines, plus the instance lemmas (the real mass, in the Large-field and Small-field modules). The BKAR port is already in the project. KPZ assessment (the author permits porting from `/home/scott/KPZ/cumulants/Lean/Polymers/*` with attribution; Lean v4.26.0). Sizes: BKAR 18,000 lines (54 files), BlockVariance 21,925, Fable 262,617, Frames 43,614, NoPigeonhole 43,883, PDE 93,092, Resolvent 4,772. (1) `Polymers/BKAR` is an earlier copy of the formula already in `Balaban/External/BKAR/` (18,686 lines): nothing further to port. (2) Searches for Ursell/Penrose/set-partition/exponential-formula/spanning-tree material found none that fits PE. Only hits: `Fable/Coherent/ForestFullComponentPartition.lean` and `TerminalComponent*Incidence*.lean` (component partitions of forests in the KPZ argument; possibly reusable for Step 3 of 3.1, the factorization of the forest sum over components, but tied to Fable structures; UNCERTAIN, to be read before deciding), `Fable/Real/StarPolymerSum.lean` (bounds grow with the volume, per roadmap 5.3) and `Fable/Assembly/TreeCounting.lean` (tree count is a structure field, not a proof). (3) `Resolvent/*` is relevant to the random-walk expansions of P3 Sect. 2, not to PE. (4) Porting cost: each file must be read and its Fable dependencies cut; 4.26 to 4.35 adaptation plus module header and `@[expose]` is routine for self-contained files (the BKAR port is the precedent), but any file importing Fable framework modules pulls in a large closure. Recommendation: build PE on the ported BKAR plus new code (about 5,000 lines); read the component-partition files at the start of step 3 and port only if self-contained.
Risks. (1) Step 3 (mixed partial of the product along `mixedPartialList` with the library's enumeration-independence). (2) Step 2 (no partition exponential formula in Mathlib). (3) Restating G2 on the torus with the correct adjacency and the hole count. (4) Instance hypotheses (holomorphy on common domains, site-factorization, the exact form of $\mathbb T''$) belong to D-LF/P6 reconstruction and may force changes in GAS (e.g. $\tau$ not a number but an operator; handled pointwise in the external variables only if the integrated variables are disjoint). (5) Constant bookkeeping in GAS (§3.9 last line) and MY exponents must be redone with explicit constants.

## 7. Questions

1. Is $\chi^{(k)}(Z)$ of P6 (4.46) a product of site (or block) indicators? PE-via-MY needs the product structure for the free measure. (To seaturtle2 if the long manuscript is the source.)
2. In P7 (3.26), are the sets $\{Z_i\}$ required to have pairwise disjoint halos $Z_i^{\approx2\sim2}$ (needed for compatibility in GAS), and is $\mathcal B''(Y_k\cup\bigcup Z_i)$ exactly the sum of terms meeting $\Omega_k^c\cap Z_i$ (so that "active" in GAS is as defined)?
3. Which size function does the reconstruction document (D-LF) put in Def-7: Balaban's $d_k(X\,\mathrm{mod}\,\Omega^c)$ or the Steiner size $\mu$ of §3.6? Root-F only sees block counts for hole-free polymers, so $\mu$ is a free choice.
4. Does P9 intend (3.13) as stated in §4.1's remark, i.e. is the truncated expansion organised by $\partial_1\partial_2L$?
