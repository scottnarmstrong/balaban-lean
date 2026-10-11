# CORRELATIONS: Root-C from the flow (phase 1, document D-C)

Status: draft for review, 2026-10-11. Pure mathematics on paper; no Lean was written or run. Labels: **proved** (complete argument given here), **cited** (a source or another phase-1 note proves it), **sketched** (plan with the key estimate), **UNCERTAIN:** (doubt). Page numbers are journal pages (P9 = CMP 199, pp. 493–520; PDF page = journal − 492).

Notation throughout. $d\ge3$, $N\ge2$, $\mathbb T_\ell=(\mathbb Z/\ell)^d$. For Root-F's output: $\theta:=\frac{d-2}2+\delta$, $s_j:=ML^j$, $J:=k_f+1$, and for a scale-$j$ polymer $X$ the block number $n(X):=|X|/s_j^d$. $|x|$ is the sup norm. $\langle\cdot\rangle_\ell$ is the Gibbs state of `gibbsExpectation`, $M_\ell(x)=\texttt{onePoint}$, $G_\ell(x,y)=\texttt{twoPointTruncated}$. $F_\ell(g):=\operatorname{Log}\big(Z_\ell(g)/Z_\ell(0)\big)$ with $Z_\ell=$ `partitionFunction`.

## 0. Summary

**Answer to the brief's closing request** (details in the sections named).

*What follows from Root-F alone* (§1, §4; all with complete proofs below):
- the identities $M_\ell(x)=h+\sum_{j,X}T_j(x,X;0)$ and $G_\ell(x,y)=\sum_{j,X}[\partial_{g(y)}T_j(x,X;0)+\partial_{g(x)}T_j(y,X;0)]$ on every admissible torus;
- the exact $O(N)$ and translation structure, $M=m\,h$, $G=G_{tr}(I-h\otimes h)+G_{lg}\,h\otimes h$, with $m,G_{tr},G_{lg}$ independent of $h$ (this uses only the symmetries of Def-1, not Root-F);
- $|m-1|\le 3c_9$ and $|G_{tr}|,|G_{lg}|\le C c_9(1+|x|)^{-\theta}e^{-c'\sqrt\nu|x|}$ with $\theta=\frac{d-2}2+\delta$, uniformly in $\nu$, the torus and $h$, for every $c_9$ (the constants $L,M,\beta_0$ then depend on $c_9$);
- **the whole thermodynamic limit of Root-C along the tori with side divisible by $q^n$, $q=ML$, with the identification of the limits, in all three quantities** (§4, complete proof, using the torus-independence clause);
- boundedness of $m(\nu),G(\nu,x)$ in $\nu\downarrow0$ (hence subsequential limits).

*What does not follow from Root-F alone*: the rate $|m-1|\le c\beta^{-1+\rho_1}$ (Root-F gives only $O(c_9)$ with $\beta_0=\beta_0(c_9)$ and no rate); the decay exponent $d-2$ (Root-F gives $\theta<d-2$ because $\delta<\frac{d-2}2$); the existence of the limits $\nu\downarrow0$ (the terms $T_j$ are chosen separately for every $\nu$, so Root-F contains no relation between different $\nu$); the Goldstone asymptotics with $\gamma_\infty$ and $G$; the decay $(1+|x|)^{-(d-2+\rho_0)}$ of $G_{lg}$ and of the remainder.

*Extra interfaces needed* (one line each; §2):
- **I-G** (Gaussian kernels, cited from `GREEN.md` G-5 plus two facts proved here): infinite-volume limits $t_j^\mu(x,y)$ of the $j$-th term of the exact decomposition of $(-\Delta+\mu)^{-1}$ (two arguments: the individual terms are only $L^j\mathbb Z^d$-periodic); uniform decay $|t_j^\mu(z)|\le C L^{-j(d-2)}e^{-\delta L^{-j}|z|}$; continuity in $\mu\in[0,1]$; bounded prolongation kernels.
- **I-F1** (running coefficients, observable form): $\xi^{(k)}(\nu)$, $\nu\in[0,1]$, with $|\xi^{(k)}|\le \frac{c_\xi}{4\beta}q^{k+1}$ and continuity in $\nu$, so that $\beta_j=\beta L^{j(d-2)}\gamma_j$, $\nu_j=\nu L^{2j}\delta_j$ are the sequences of `RunningCoefficients.lean`.
- **I-F2** (one-point): $m(\nu)=1-\sum_{j\le J}\beta_{j-1}^{-1/2}\mu_j(\nu)+e_m$, $|\mu_j|\le c\beta^{-1/2+\rho_1}L^{-j\rho_0}$, $\mu_j$ continuous at $\nu=0$, $|e_m|\le c\beta_J^{-2}$ (P9 (2.8)–(2.9), (4.8)).
- **I-F3** (two-point): $G_{tr}(\nu,x-y)=m_J^2\sum_{j<J}(\beta\gamma_j)^{-1}t_j^{\nu\delta_j}(x,y)+r_{tr}(\nu;x,y)$, $G_{lg}=r_{lg}$ (the longitudinal main term is exactly $0$ at $\lambda=\infty$), $|r|\le c(1+|x|)^{-(d-2+\rho_0)}e^{-c'\sqrt\nu|x|}$, and $r(\nu,x)$ converges as $\nu\downarrow0$ (P9 (2.10)–(2.20), (4.9)–(4.11); the convergence is **not** in P9).
- I-F1–F3 together form the candidate **C-1\*** (observable form); the inductive form C-1a (P9 (H.1)–(H.2), Prop 3.1) from which it is derived is stated in §2.3.

*What no source proves* (§5): the $\nu\downarrow0$ convergence of the remainder (P9 proves it for the main term only, and only for fixed $j$ by dominated convergence); the thermodynamic limit (P4 p. 720 remark only; proved here from Root-F); the exact Gaussian decomposition (4.17) (cited to Parisi, no proof; proved here from `laplacian_inv_eq_multiscale`); the identification of $G$ (never discussed); the rate $|\gamma_\infty-1|\le c/\beta$ (P4 (5.33) gives existence only).

*Questions*: §7 (four).

---

## 0.1 Standing facts about the model (Def-1) — proved

These use only the definitions `aprioriMeasure`, `energy`, `partitionFunction`, not Root-F.

**Lemma 0.1 (analyticity and cumulants).** For fixed $\ell,\beta,\nu,h$, $Z_\ell$ is an entire function of $g\in\mathbb C^{\mathbb T_\ell\times N}$ and $Z_\ell(0)>0$. With $\Phi=(\phi_i(x))$,
$$\partial_{g_i(x)}Z_\ell(0)/Z_\ell(0)=M_{\ell,i}(x),\qquad \partial_{g_i(x)}\partial_{g_k(y)}Z_\ell(0)/Z_\ell(0)=\langle\phi_i(x)\phi_k(y)\rangle_\ell .$$
Near $g=0$ one has $|Z_\ell(g)/Z_\ell(0)-1|<1$, so $F_\ell=\operatorname{Log}(Z_\ell/Z_\ell(0))$ is analytic there, and
$$\partial_{g_i(x)}F_\ell(0)=M_{\ell,i}(x),\qquad \partial_{g_i(x)}\partial_{g_k(y)}F_\ell(0)=G_{\ell,ik}(x,y).$$

*Proof.* The integrand $\exp(-\beta H(\phi)+\langle g,\phi\rangle)$ is entire in $g$ with $|\phi_i(x)|\le1$ on the sphere; the a priori measure is finite (a product of finite measures), so differentiation under the integral is justified by domination on bounded sets of $g$ (Mathlib: `hasFDerivAt_integral_of_dominated_of_fderiv_le`, twice). $Z_\ell(0)>0$ because the integrand is positive and the measure is nonzero. The logarithm: $(\operatorname{Log}u)'=u'/u$, $(\operatorname{Log}u)''=u''/u-(u'/u)^2$, evaluated at $u=Z/Z(0)=1$. $\square$

**Lemma 0.2 (symmetries).** (a) *Translations*: for $a\in\mathbb T_\ell$, $M_\ell(x+a)=M_\ell(x)$ and $G_\ell(x+a,y+a)=G_\ell(x,y)$.
(b) *Orthogonal covariance*: for $R\in O(N)$, $M_\ell(x;Rh)=R\,M_\ell(x;h)$ and $G_\ell(x,y;Rh)=R\,G_\ell(x,y;h)\,R^{\top}$.
(c) *Consequences.* For every unit $h$ there are reals $m_\ell,\ G_{tr,\ell}(z),\ G_{lg,\ell}(z)$ ($z\in\mathbb T_\ell$), **independent of $h$**, with
$$M_\ell(x)=m_\ell\,h,\qquad G_\ell(x,y)=G_{tr,\ell}(x-y)(I-h\otimes h)+G_{lg,\ell}(x-y)\,h\otimes h .$$
Explicitly $m_\ell=M_\ell(0;e_1)_1$, $G_{lg,\ell}(z)=G_\ell(0,z;e_1)_{11}$, $G_{tr,\ell}(z)=G_\ell(0,z;e_1)_{22}$.

*Proof.* (a) The map $\phi\mapsto\phi(\cdot+a)$ preserves the product measure (permutation of the factors, `MeasurePreserving.piCongrLeft`-type) and $H$ (the sums over $x$ and the bond differences are translation invariant). (b) $\phi\mapsto R\phi$ (sitewise) preserves the product of surface measures and maps $H(\cdot;h)$ to $H(\cdot;Rh)$ since $|R\phi-Rh|=|\phi-h|$ and bond differences rotate. The surface measure is $O(N)$-invariant (it is the cone measure of Lebesgue measure; this needs a Mathlib lemma, §6 item A). Then $\langle\phi_i(x)\rangle_{Rh}=\sum_jR_{ij}\langle\phi_j(x)\rangle_h$, and the same for the two-point function. (c) Let $S\subset O(N)$ be the stabilizer of $e_1$ (isomorphic to $O(N-1)$, which contains the sign changes and permutations of $e_2,\dots,e_N$). By (b) with $Rh=h=e_1$: $M(x;e_1)=RM(x;e_1)$ for all $R\in S$, so $M\in\mathbb Re_1$ (a vector fixed by all sign changes of $e_k$, $k\ge2$, has zero $k$-th component; $N\ge2$ is used here only to have $e_1$ and the sign changes). Similarly $G(e_1)=RG(e_1)R^\top$ forces $G_{1k}=G_{k1}=0$ for $k\ge2$, $G_{kk'}=0$ for $k\ne k'\ge2$ (sign changes), and $G_{kk}=G_{22}$ for $k\ge2$ (permutations). For general $h$ choose $R\in O(N)$ with $Re_1=h$ and apply (b). Independence of $h$ follows because $m_\ell=M(x;h)\cdot h=M(x;e_1)\cdot e_1$, and likewise for $G_{tr},G_{lg}$. Dependence on $x-y$ only is (a). Evenness: $G_{ik}(x,y)=G_{ki}(y,x)$ (symmetry of the covariance) and (a) give $G_{tr,\ell}(-w)=G_{tr,\ell}(w)$, $G_{lg,\ell}(-w)=G_{lg,\ell}(w)$, so that $G_\ell(x,y)$ may be written with $x-y$ as in Root-C. $\square$

(For $N=2$ the stabilizer is $\{\pm\}$-reflection of $e_2$ and the same argument applies.) These two lemmas are where Root-C's "$m,G_{tr},G_{lg}$ independent of $h$" (S0-Q07) is obtained.

**Remark 0.3 (Ward identity; consistency check only, not used).** Rotating all spins in the $(e_1,e_2)$-plane and differentiating at $0$ gives the exact identity $m_\ell=\beta\nu\sum_{x}G_{tr,\ell}(x)$ (the weight is $\exp(\beta\nu\sum_x h\cdot\phi_x)$ up to constants since $|\phi|=1$). In the Goldstone picture $G_{tr}\approx\frac{m^2}{\beta\gamma_\infty}G_{\nu_{\rm eff}}$ and this forces $\nu_{\rm eff}=\nu m/\gamma_\infty$, i.e. $\delta_\infty\approx m/\gamma_\infty$ at leading order; at leading order all three are $1$. I did not check whether $\delta_\infty=m/\gamma_\infty$ holds exactly in P4's flow.


---

## 1. What Root-F gives and what it does not

Fix $d,N$ and take Root-F's $\delta$. Fix $\kappa=\kappa_*:=2\log(8d^2)$ (any larger $\kappa$ also works), and $c_9>0$; Root-F then provides $L,M,\beta_0$. Fix $\beta\ge\beta_0$, $\nu\in(0,1]$, a unit $h$, and Root-F's $k_f$, $T$; put $J=k_f+1$. "Admissible" tori are those with $ML^{J}\mid\ell$.

### 1.1 Polymer counting and geometry — proved

**Lemma 1.1 (counting).** Let $\ell$ be admissible, $1\le j\le J$, $x\in\mathbb T_\ell$. The number of scale-$j$ polymers $X\ni x$ with $n(X)=n$ is at most $C_0^{\,n}$, $C_0=(2d)^2$. Consequently, since $C_0e^{-\kappa_*/2}\le\frac12$,
$$\sum_{X\ni x}e^{-\kappa_*n(X)/2}\le\sum_{n\ge1}2^{-n}= 1 ,\qquad \sum_{X\ni x,\ n(X)\ge n_0}e^{-\kappa_* n(X)}\le 2^{1-n_0}.$$

*Proof.* A polymer is a union of blocks of side $s_j$ (`IsPolymer`: closed under "same block"), so $X$ is determined by its set $\mathcal B(X)$ of blocks, a subset of $(\mathbb Z/(\ell/s_j))^d$ with $|\mathcal B(X)|=n(X)$. Connectedness of $X$ for nearest-neighbour steps inside $X$ implies that $\mathcal B(X)$ is connected for face-adjacency of blocks (a step $y\to y\pm e_\mu$ either stays in a block or passes to a face-adjacent block). The block graph has degree $\le 2d$. A connected set $\mathcal B$ of $n$ vertices containing a given vertex $b$ is the vertex set of a closed walk of length $2(n-1)$ from $b$ (depth-first traversal of a spanning tree), and there are at most $(2d)^{2(n-1)}$ such walks. $\square$

**Lemma 1.2 (diameter).** Let $\ell$ be admissible, $X$ a scale-$j$ polymer, $x,y\in X$. Then $n(X)\,s_j\ge d_\ell(x,y)+1$, where $d_\ell$ is the torus sup distance, $d_\ell(x,y)=\max_\mu|\mathrm{valMinAbs}(x_\mu-y_\mu)|$.

*Proof.* A path from $x$ to $y$ inside $X$ passes through a simple chain of $r+1\le n$ distinct, consecutively face-adjacent blocks. Two points of the same block differ by at most $s_j-1$ in each coordinate, two points of face-adjacent blocks by at most $2s_j-1$; along the chain the coordinate differences add (modulo $\ell$), so $d_\ell(x,y)\le(r+1)s_j-1\le n s_j-1$. $\square$

**Lemma 1.3 (summation, P9 Lemma 1 pp. 497–498 in the form needed) — proved.** For $\sigma>0$, $\delta>0$, $L\ge2$ there is $C=C(\sigma,\delta,L)$ with
$$\sum_{j\ge0}L^{-j\sigma}e^{-\delta L^{-j}r}\le C(1+r)^{-\sigma}\qquad(r\ge0).$$
*Proof.* For $r<1$ bound by $\sum_jL^{-j\sigma}=(1-L^{-\sigma})^{-1}$. For $r\ge1$ split at $L^j\le r$: with $u_j=rL^{-j}\ge1$ the term is $r^{-\sigma}u_j^{\sigma}e^{-\delta u_j}\le r^{-\sigma}C_1e^{-\delta u_j/2}$, and the numbers $u_j$ are $\ge L^m$, $m=0,1,2,\dots$ (distinct, geometric), so the sum is $\le r^{-\sigma}C_1\sum_me^{-\delta L^m/2}$. For $L^j>r$ the terms are $\le L^{-j\sigma}$, summing to $\le(1-L^{-\sigma})^{-1}L^{-j_1\sigma}\le(1-L^{-\sigma})^{-1}r^{-\sigma}$, $j_1$ the first such index. $\square$

(This is the "well-known bound" quoted after P9 (2.19); P9 proves Lemma 1 itself by "interchanging the sums". Lemma 1.3 is the same statement; with $\sigma=d-2+\varepsilon_0$ and the extra $L^{-i\gamma}$ factors of (2.19) the interchange of sums is a two-line computation, left to the Lean proof.)

### 1.2 The formulas for $M_\ell$ and $G_\ell$ — proved

**Proposition 1.4.** For admissible $\ell$, $x,y\in\mathbb T_\ell$, $i,k\le N$,
$$M_{\ell,i}(x)=h_i+\sum_{j=1}^{J}\sum_{X\ni x}T_j(x,X;0)_i,$$
$$G_{\ell,ik}(x,y)=\sum_{j=1}^{J}\sum_{X\ni x,y}\Big[D_{k,y}T_j(x,X;0)_i+D_{i,x}T_j(y,X;0)_k\Big],$$
where $D_{k,y}T(x,X;0)=\frac{d}{d\zeta}\big|_{\zeta=0}T(x,X;\zeta e_k\delta_y)$ (a complex derivative along the single coordinate $g_k(y)$). The sums are finite.

*Proof.* Both sides of the Root-F identity are analytic on $\{\sum|g|<1\}\ni0$; by Lemma 0.1 the derivatives of the left side at $0$ are $M$ and $G$. On the right, differentiate $\sum_{j,z,X}\sum_lg_l(z)T_j(z,X;g)_l$ once in $g_i(x)$: $\sum_{j,X}T_j(x,X;g)_i+\sum g_l(z)\partial_{g_i(x)}T_j(z,X;g)_l$; at $g=0$ the second sum vanishes. Differentiate again in $g_k(y)$ at $0$: $\sum_{j,X}\partial_{g_k(y)}T_j(x,X;0)_i+\sum_{j,X}\partial_{g_i(x)}T_j(y,X;0)_k$ (the terms with $g_l(z)$ in front vanish at $0$). By vanishing (outside polymers containing the first site argument) and locality ($T_j(x,X;\cdot)$ depends on $g|_X$ only) the first sum is over $X\ni x,y$, the second over $X\ni x,y$. For $x=y$ no change. $\square$

### 1.3 Estimates — proved

**Proposition 1.5.** With $\kappa=\kappa_*$ and $\ell$ admissible, uniformly in $\ell,\beta\ge\beta_0,\nu,h$:

(a) $\big|M_\ell(x)-h\big|_\infty\le 3c_9$, hence (taking $h=e_1$ and Lemma 0.2) $|m_\ell-1|\le3c_9$.

(b) For all $x,y$ and all $i,k$, with $r=1+d_\ell(x,y)$,
$$|G_{\ell,ik}(x,y)|\le C_*\,c_9\,r^{-\theta}\,e^{-c'\sqrt\nu\,(r-1)},\qquad \theta=\tfrac{d-2}2+\delta,\quad c'=\frac{\kappa_*}{4ML^2},$$
with $C_*=C_*(d,L,M,\delta)$. In particular $|G_{tr,\ell}(z)|,|G_{lg,\ell}(z)|$ obey the same bound.

*Proof.* (a) By Root-F, $\|T_j(x,X;0)\|\le c_9L^{-j\theta}e^{-\kappa_*n(X)}$. Summing over $X\ni x$ (Lemma 1.1) gives $\le c_9L^{-j\theta}$ for each $j$, and $\sum_{j\ge1}L^{-j\theta}\le(L^{1/2}-1)^{-1}\le 3$ since $\theta\ge\frac12$ and $L\ge2$.

(b) *Cauchy.* Fix $j,x,X,y,k,i$. The function $\zeta\mapsto T_j(x,X;\zeta e_k\delta_y)_i$ is analytic for $|\zeta|<1$ (here $\sum|g|=|\zeta|$) and bounded by $B=c_9L^{-j\theta}e^{-\kappa_*n(X)}$ for $|\zeta|\le\frac12$. The Cauchy estimate on the circle of radius $\frac12$ (in Lean: `norm_fderiv_line_le` of `Balaban/Analysis/Cauchy.lean` with $\rho\uparrow\frac12$) gives $|D_{k,y}T_j(x,X;0)_i|\le 2B$. By Proposition 1.4,
$$|G_{\ell,ik}(x,y)|\le 4c_9\sum_{j=1}^{J}L^{-j\theta}\sum_{X\ni x,y}e^{-\kappa_*n(X)}.$$
By Lemma 1.2, $n(X)\ge r/s_j$ for $X\ni x,y$. Write $e^{-\kappa_*n}=e^{-\kappa_*n/2}e^{-\kappa_*n/2}\le e^{-\kappa_*n/2}e^{-\kappa_*r/(2s_j)}$ and sum over $X$ by Lemma 1.1:
$$|G_{\ell,ik}(x,y)|\le4c_9\sum_{j=1}^JL^{-j\theta}e^{-\kappa_*r/(2ML^j)} .$$
Split $e^{-\kappa_*r/(2ML^j)}=e^{-\kappa_*r/(4ML^j)}\cdot e^{-\kappa_*r/(4ML^j)}$. By Lemma 1.3 ($\sigma=\theta$, $\delta=\kappa_*/(4M)$) the sum of the first factors over $j\ge0$ is $\le C r^{-\theta}$. For $j\le J=k_f+1$, $L^j\le L^{k_f+1}\le L^2/\sqrt\nu$ (Root-F: $L^{k_f}\sqrt\nu\le L$), so the second factor is $\le e^{-\kappa_*r\sqrt\nu/(4ML^2)}$. Finally $e^{-c'\sqrt\nu r}\le e^{-c'\sqrt\nu(r-1)}$. $\square$

**Corollary 1.6 (what Root-F gives about Root-C's second bullet).** For every $\epsilon>0$ there is $c_9=\epsilon/3$ and, from Root-F, $L,M,\beta_0$ such that for $\beta\ge\beta_0$ all $\nu\in(0,1]$ have $|m_\ell-1|\le\epsilon$ and $|G|\le C\epsilon(1+|x|)^{-\theta}e^{-c'\sqrt\nu|x|}$. Constants $c,c'$ depending only on $(d,N)$ and a **rate** $c\beta^{-1+\rho_1}$ are not obtained: with $c_9$ fixed, $\beta_0$ is fixed, and $\beta\mapsto$ the best $c_9$ is whatever the (unspecified) function $c_9\mapsto\beta_0(c_9)$ allows.

### 1.4 The thermodynamic limit

Using only the torus-independence clause, with $q:=ML$ (for the data of Root-F at $\kappa_*$ and $c_9=1$), the limits in the first bullet of Root-C exist along $q^{n}\mid\ell$, for $M,G_{tr},G_{lg}$, and the bounds of Proposition 1.5 pass to the limit. The proof is in §4 (it is item 4 of the brief, C-3).

### 1.5 Table: Root-C against Root-F

| Root-C clause | From Root-F + Def-1 symmetries? |
|---|---|
| limits $\ell\to\infty$ along $q^n\mid\ell$, form $m h$, $G_{tr}(I-hh)+G_{lg}hh$, independent of $h$ | **yes** (Lemma 0.2, §4); $q=ML$ |
| $\lvert m-1\rvert\le c\beta^{-1+\rho_1}$ | no (only $\le3c_9$ for $\beta\ge\beta_0(c_9)$) |
| $\lvert G_{tr}\rvert,\lvert G_{lg}\rvert\le c(1+\lvert x\rvert)^{-(d-2)}e^{-c'\sqrt\nu\lvert x\rvert}$ | partly: mass decay and exponent $\theta<d-2$ only |
| $\nu\downarrow0$ limits of $m,G_{tr},G_{lg}$ | no (nothing relates different $\nu$) |
| $-\Delta G=\delta_0$, $G\to0$ | no (Gaussian, §3.4); independent of Root-F |
| $G_{tr,0}-\frac{m_0^2}{\beta\gamma}G=O(\lvert x\rvert^{-(d-2+\rho_0)})$, $\lvert\gamma-1\rvert\le c/\beta$ | no |
| $\lvert G_{lg,0}\rvert\le c(1+\lvert x\rvert)^{-(d-2+\rho_0)}$ | no |

Why $\theta<d-2$ is sharp for the method: the Cauchy estimate for $\partial_gT$ on the $\ell^1$-ball of radius $\frac12$ gains nothing, while the true size of $T_j$'s dependence on a single $g_k(y)$ is $L^{-j(d-2)/2}$ times the size of $T_j$ (one more factor of the field scale), which is not part of Root-F's bound. In the source $\delta=\gamma-\alpha_1<\gamma<\gamma_0=\min(\frac{d-2}2,\frac12)$ (P9 p. 495; `surface-v1-for-approval.md` S0-Q05), so $\theta<d-2$. The frozen Root-F only asserts $\exists\delta>0$; a proof with $\delta\ge\frac{d-2}2$ would not be the source's and is not expected.


---

## 2. The extra outputs of the flow that Root-C needs

Three groups: the Gaussian kernels (explicit lattice operators; I-G), the running coefficients and scalar sequence (I-F1, I-F2), and the two-point decomposition (I-F3). Together I-F1–I-F3 are the observable form **C-1\*** of the candidate C-1. §2.3 states the inductive form (C-1a) from which C-1\* is derived.

### 2.1 Gaussian kernels, in the plain units of `Multiscale.lean` (I-G)

*Conventions.* Everything is on $\mathbb Z^d$ or $\mathbb T_\ell$ with plain sums; $Q$ is `blockAverageMatrix` ($(Qf)(u)=L^{-d}\sum_{x\in B_u}f(x)$, so $QQ^{\top}=L^{-d}I$); a weighted inner product (P1, P9) is absorbed into the scale parameters, as in `Multiscale.lean`'s header. Fix $L\ge2$, $a>0$ and the **free-flow sequence**
$$\alpha_i:=a\,L^{(i+1)(d-2)}\qquad(i\ge0),$$
to be used as the sequence `a` of `laplacian_inv_eq_multiscale`.

**Definition.** For $\mu>0$ and a torus $\mathbb T_\ell$ with $L^{j+1}\mid\ell$, let $A_0=$ `latticeLaplacian d ℓ μ`, $A_{i+1}=\Delta_i:=\alpha_i-\alpha_i^2QM_i^{-1}Q^\top$, $M_i=A_i+\alpha_iQ^\top Q$ (the effective operators `effOp`, `stepOp`), $H_i=\alpha_iM_i^{-1}Q^{\top}$ (`stepProlong`), $P_j=H_0H_1\cdots H_{j-1}$ ($P_0=I$), and
$$T_j^{\ell,\mu}:=P_j\,M_j^{-1}P_j^{\top}\qquad(j\text{-th summand of }\texttt{fluct}).$$
`laplacian_inv_eq_multiscale` is then, with $K\ge1$ steps on $\mathbb T_{L^Km}$,
$$(-\Delta+\mu)^{-1}=\sum_{j<K}T_j^{\ell,\mu}+P_K\,A_K^{-1}P_K^{\top}.\tag{2.1}$$

**Dictionary to P9 — derived here, UNCERTAIN only in the identification of P9's weighted units.** The effective operator after $j$ steps equals the one-shot operator $\Delta_{tr}^{(j)}=b_j-b_j^2Q_jG_jQ_j^\top$, $G_j=(-\Delta+\mu+b_jQ_j^\top Q_j)^{-1}$, $Q_j=$ composite block average over $L^j$-blocks, where
$$b_j^{-1}=\alpha_{j-1}^{-1}+L^{-d}b_{j-1}^{-1}\ (b_0^{-1}=0),\qquad b_j=L^{j(d-2)}\,a_j,\quad a_j=\frac{a(1-L^{-2})}{1-L^{-2j}} .$$
Proof of the closed form: the recursion for the *inverse* is $A_{i+1}^{-1}=\alpha_i^{-1}I+QA_i^{-1}Q^\top$ (Woodbury, the identity `hΔ` in the proof of `inv_eq_blockSpin_decomposition`); iterating and using $QQ^\top=L^{-d}I$ gives $A_j^{-1}=b_j^{-1}I+Q_jA_0^{-1}Q_j^\top$ with $b_j^{-1}=\sum_{i<j}\alpha_i^{-1}L^{-d(j-i-1)}=a^{-1}L^{-j(d-2)}\frac{1-L^{-2j}}{1-L^{-2}}$ (a geometric sum: exponent $-(i+1)(d-2)-d(j-i-1)=-dj+2(i+1)$). The same elimination applied to the pair of springs shows that two steps $(\alpha_1,\alpha_2)$ with $Q_2Q_2^\top=L^{-d}I$ are equivalent to one step with $Q=Q_2Q_1$ and $b^{-1}=\alpha_2^{-1}+L^{-d}\alpha_1^{-1}$ (minimise over the intermediate field and the fine field in either order; the minimiser of the fine field is $H_0H_1\psi_2$ in one order and $b\,M^{-1}Q^\top\psi_2$ in the other), so $P_j=b_jG_jQ_j^{\top}=H_j^{P9}$ and $M_j=L^{j(d-2)}\big(\Delta^{(j)P9}_{tr}+aL^{-2}Q^*Q\big)$ with $Q^*=L^dQ^\top$. Hence
$$T_j=L^{-j(d-2)}\,\big[a_j^2G_jQ_j^*C^{(j)}_{tr}Q_jG_j\big]=:L^{-j(d-2)}K_j ,\tag{2.2}$$
which is exactly the $j$-th summand of P9 (4.14), (4.16), (4.17) with the factor $L^{-j(d-2)}$ of (4.17); and $\beta_j^{-1}K_j=(\beta\gamma_j)^{-1}T_j$ (since $\beta_j=\beta L^{j(d-2)}\gamma_j$). This is the unit bookkeeping behind "$\beta_j^{-1}\le2L^{-j(d-2)}\beta^{-1}$" in P9 p. 518. Check at $j=1$: $b_1=\alpha_0=aL^{d-2}=L^{d-2}a_1$ and $\alpha_0Q^\top Q=aL^{d-2}Q^\top Q=aL^{-2}Q^*Q$ with $Q^*=L^dQ^\top$, which is P9's penalty $aL^{-2}Q^*Q$ in $C^{(j)}_{tr}$.

The **index shift in P9.** (2.13) defines $G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*$ for $j=1,\dots,k$ (step $j$ integrates the fluctuation at scale $j-1$ and produces the scale-$j$ contributions), (2.11) pairs it with $\beta_{j-1}^{-1}$. In (4.14)–(4.16) the symbol $G^{(j)}$ and the index $j=0,\dots,k-1$ are used for the summand $a_j^2G_jQ_j^*C^{(j)}_{tr}Q_jG_j=H_jC^{(j)}_{tr}H_j^*$, i.e. P9's $G^{(j+1)}$ of (2.13). So (4.14) is (2.11) with $j-1\to j$, and "$k$" in §4 is "$k+1$" of (4.7)–(4.9) ("for simplicity we replace the index $k+1$ by $k$", p. 517). In our notation: $T_j$, $j=0,\dots,J-1$, $J=$ P9's final $k$.

**The formula $a_j=a\frac{1-L^{-2}}{1-L^{-2j}}$ at $j=0$.** It gives $a_0=\infty$; this is the instruction "no penalty at the finest scale": $b_0^{-1}=0$ and $P_0=I$, $T_0=M_0^{-1}=(-\Delta+\mu+\alpha_0Q^\top Q)^{-1}$. In the closed form, $a_0^2G_0Q_0^*C^{(0)}Q_0G_0\to C^{(0)}=(-\Delta+\mu+aL^{-2}Q^*Q)^{-1}$ as $a_0\to\infty$ because $G_0\sim a_0^{-1}$. In the formalisation $a_0=\infty$ never occurs: $T_0$ is defined as `stepCov`, and $T_j$, $j\ge1$, with finite $\alpha_i$.

**Interface I-G** (cited: `GREEN.md` G-5(a),(b), C14; what is new is only (G4) below, proved in §3.4). Constants $C_G,\delta_G,C_P>0$ depending on $d,L,a$. *The individual terms $T_j$ are not translation invariant*: the blocks are aligned to $L\mathbb Z^d$, so $T_j(x,y)$ is invariant only under simultaneous shifts of $x,y$ by $L^j\mathbb Z^d$; only the sum over all $j$ (with the remainder) is. So the kernels carry two arguments.

- **(G1) infinite-volume limit.** For $\mu\in(0,1]$, $j\ge0$, $x,y\in\mathbb Z^d$ the limit $t_j^\mu(x,y):=\lim T_j^{\ell,\mu}(x\bmod\ell,y\bmod\ell)$ as $\ell\to\infty$ through multiples of $L^{j+1}$ exists.
- **(G2) decay, uniform in $\mu$ and $\ell$.** $|T_j^{\ell,\mu}(x,y)|,\ |t_j^\mu(x,y)|\le C_GL^{-j(d-2)}\exp(-\delta_GL^{-j}|x-y|)$.
- **(G3) continuity.** For each $j,x,y$, $\mu\mapsto t_j^\mu(x,y)$ is continuous on $(0,1]$ and has a limit $t_j^0(x,y)$ as $\mu\downarrow0$ (Lipschitz in the kernel norm of (G2), G-5(b)); (G2) holds for $\mu=0$.
- **(G5) prolongation kernels are bounded:** $|P_j^{\ell,\mu}(y,u)|\le C_P$ for all $j,\ell,\mu\in(0,1]$, $y\in\mathbb T_\ell$, $u$ on the level-$j$ torus (this is $|a_jG_jQ_j^*(x,y)|\le ce^{-\delta|x-y|}$ of G-5(a); in plain units $P_j=H_j$ is dimensionless, with row sums $1$ at $\mu=0$).

**(G4) sum rule** (proved in §3.4): $\mathcal G(x,y):=\sum_{j\ge0}t_j^0(x,y)$ converges absolutely, $\mathcal G(x,y)=G(x-y)$ with $-\Delta G=\delta_0$, and $G(z)\to0$ as $|z|\to\infty$.

### 2.2 The flow data and the observable statement C-1\*

*The running coefficients.* The sequences of `Balaban/Flow/RunningCoefficients.lean`: for $\xi:\mathbb N\to\mathrm{Fin}\,3\to\mathbb C$, `betaSeq` $\beta_{k+1}=\beta_kL^{d-2}/(1+\xi_k(2))$, `nuSeq` $\nu_{k+1}=\nu_kL^2(1+\xi_k(2))/(1+\xi_k(1))$, with $\beta_k=\beta L^{k(d-2)}\gamma_k$, $\nu_k=\nu L^{2k}\delta_k$ (P4 (H.6), (5.28)). For real $\xi$ they are real; the plain mass at scale $k$ is $\nu_kL^{-2k}=\nu\delta_k$.

**Interface C-1\* (observable form; $\lambda=\infty$).** For $d\ge3$, $N\ge2$ there are an integer $L\ge2$, $a\in(\frac12,\frac32)$, $\gamma_0\in(0,\frac12]$ (put $q=L^{-2\gamma_0}$), constants $c_*,c_\xi,c'>0$, $\rho_0>0$, $\rho_1\in(0,1)$, $\beta_*$, a function $J:(0,1]\to\mathbb N$ with $J(\nu)\to\infty$ as $\nu\downarrow0$ and $\frac12\le L^{J(\nu)}\sqrt\nu\le L^2$, such that for every $\beta\ge\beta_*$ there are
$$\xi:[0,1]\to(\mathbb N\to\mathrm{Fin}\,3\to\mathbb R),\qquad \mu_j:[0,1]\to\mathbb R\ (j\ge1),\qquad r_{tr},r_{lg}:(0,1]\times\mathbb Z^d\times\mathbb Z^d\to\mathbb R,\qquad e_m:(0,1]\to\mathbb R,$$
with (writing $\beta_j(\nu),\gamma_j(\nu),\delta_j(\nu)$ for the sequences generated by $\xi(\nu)$, $J=J(\nu)$, and $m,G_{tr},G_{lg}$ for the infinite-volume functions of §4):

- **(F1) running coefficients.** $\|\xi(\nu)_k\|_\infty\le\frac{c_\xi}{4\beta}q^{k+1}$ for all $\nu\in[0,1]$, $k\ge0$; for each $k$ the map $\nu\mapsto\xi(\nu)_k$ is continuous at $\nu=0$ (on $[0,1]$).
- **(F2) one-point.** $|\mu_j(\nu)|\le c_*\beta^{-1/2+\rho_1}L^{-j\rho_0}$, $\mu_j$ continuous at $0$ (right), and for $\nu\in(0,1]$
$$m(\nu)=m_J(\nu)+e_m(\nu),\qquad m_J(\nu):=1-\sum_{j=1}^{J}\beta_{j-1}(\nu)^{-1/2}\mu_j(\nu),\qquad|e_m(\nu)|\le c_*\beta_J(\nu)^{-2}.$$
- **(F3) two-point.** For $\nu\in(0,1]$ and all $x,y\in\mathbb Z^d$,
$$G_{tr}(\nu,x-y)=m_J(\nu)^2\sum_{j=0}^{J-1}\frac{1}{\beta\gamma_j(\nu)}\,t_j^{\nu\delta_j(\nu)}(x,y)+r_{tr}(\nu;x,y),\qquad G_{lg}(\nu,x-y)=r_{lg}(\nu;x,y),$$
$$|r_{tr}(\nu;x,y)|,\,|r_{lg}(\nu;x,y)|\le c_*\,(1+|x-y|)^{-(d-2+\rho_0)}\,e^{-c'\sqrt\nu|x-y|},$$
and for all $x,y$ the limits $r_{tr}(0;x,y):=\lim_{\nu\downarrow0}r_{tr}(\nu;x,y)$, $r_{lg}(0;x,y)$ exist.

(F1) is P4 Prop. 5.1 with $c_8=c_\xi/\beta$: P4 (5.25)–(5.31) bound $|\xi|$ by $O(\beta^{-1}\alpha_0^{-2})q^{k+1}$ and P4 (5.30) makes $c_8$ small only through that inequality; P9 states $|\gamma_\infty-1|<c\beta^{-1}$ (UNCERTAIN: the rate $\beta^{-1}$ is derived from P4 (5.25)–(5.30), not printed there). Continuity in $\nu$ up to $\nu=0$ is expected because $\xi^{(k)}$ is the fixed point of a contraction (P4 (5.23)–(5.27)) whose data depend analytically on $\nu_k$, itself a rational function of $\nu$ and $\xi^{(0)},\dots,\xi^{(k-1)}$; it is not printed (UNCERTAIN whether P4's estimates are uniform down to $v=0$; P2 allows $\nu=0$, `GREEN.md` §1). (F2) is P9 (2.8)–(2.9), (4.8), (4.10). (F3) is (4.9), (4.11), (2.10)–(2.12), (2.20), (4.14); the longitudinal main term is $0$ exactly at $\lambda=\infty$ (§2.4); the convergence of $r(\nu;x,y)$ is not in P9.

### 2.3 The inductive form C-1a (P9 (H.1)–(H.2), Prop 3.1, §4) and the derivation of C-1\*

**C-1a (stated schematically; the ambient class $\mathcal R_k$ is Def-7, not yet written).** For a density $\rho_k$ in the inductive class (P5 (H.1)–(H.7), λ=∞, with $h$ the unit external direction and $\nu\in[0,1]$), the second-order part of $F_k(\psi;h,g)=\langle g,M_k\rangle+\frac12\langle g,G_kg\rangle+O(g^3)$ (P9 (2.1)) has the form:

1. *(H.1)* $M_k(x;\psi,h)=m_k\varphi_k(x;\psi,h)+\sum_{j=1}^k\beta_{j-1}^{-1/2}M^{(j)}(x;\psi_k^{(j)}(\psi,h),h)$, with $M^{(j)}$ real analytic on $\Xi_j(1,\varepsilon_j)$, covariant ($M^{(j)}(R\psi,Rh)=RM^{(j)}(\psi,h)$, translation and lattice symmetries), localised $M^{(j)}=\sum_{X\in\mathcal D_j,X\ni x}M^{(j)}(x,X;\cdot)$ with $|M^{(j)}(x,X)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\kappa d_j(X)}$, normalised by $M^{(j)}(x;h,h)=0$; and $m_k=1-\sum_{j\le k}\beta_{j-1}^{-1/2}\mu_j$, $|\mu_j|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}$ (P9 (2.2)–(2.9)).
2. *(H.2)* $G_k=C_k+R_k$, $C_k=\sum_{j=1}^k\beta_{j-1}^{-1}m_kG^{(j)}m_k$, $G^{(j)}=H_{j-1}C^{(j-1)}H_{j-1}^*$ (explicit, P9 (2.13)–(2.14)), $R_k=\sum_{j\le k}\sum_{i\le j}\beta_{i-1}^{-1}R^{ij}$, with $R^{ij}$ analytic, covariant, localised, $|R^{ij}(x,x';X)|\le\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\delta_0L^{-i}|x-x'|}e^{-\kappa d_j(X)}$ (P9 (2.10)–(2.18)).
3. *(Preservation)* the next step $\rho_{k+1}=\mathcal T\rho_k$ again has these properties, with the new contributions given by P9 (3.1)–(3.10) and (3.44)–(3.49) (this includes P9 Prop 3.1, whose truncated-product part (3.13) is the subject of `POLYMER.md` PE-M, conditional on the product-measure form (3.11)).
4. *(Last step)* for $k=k(\nu)$ the final integration gives $\log Z(g)=F_{k+1}(h,g)+R^{(k+1)}(h,g)+P^{(k+1)}(g)$ (P9 (4.7)) with $|\partial_g R|,|\partial_gP|,|\partial_g^2R|,|\partial_g^2P|$ bounded as in P9 (4.8)–(4.9) (polymer activities $\beta_k^{-2}e^{-2\kappa d_{k+1}(Y)}$ by (4.6), (3.46)).

**Derivation of C-1\* from C-1a plus the translation to infinite volume (sketch).**
(i) By torus independence (P4 (H.4)) every object in 1–4 is the pushforward of a finite-set object; the infinite-volume versions exist and the bounds hold. (ii) At $\psi=h$ one has $\varphi_k(x;h,h)=h$ and $M^{(j)}(x;h,h)=0$, so $M_k(x;h,h)=m_kh$ (P9 (4.10)); with (4.8) this is (F2), $e_m$ being the sum of (4.8)'s last two terms ($\le3K_0\beta_k^{-2}$). (iii) $G=G_{k+1}(h,h)+\partial^2R+\partial^2P$ (4.9), $G_{k+1}(h,h)=C+R$ and the trace formulas (4.11) give $G_{tr}=\frac1{N-1}\mathrm{tr}[\cdot(I-h\otimes h)]$, $G_{lg}=\mathrm{tr}[\cdot\,h\otimes h]$. The transverse part of $C_J$ is $m_J^2\sum_{j<J}\beta_j^{-1}K_j=m_J^2\sum(\beta\gamma_j)^{-1}T_j$ by (2.2), the longitudinal part vanishes (§2.4). (iv) $r:=$ transverse/longitudinal part of $R_J(h,h)+\partial^2R+\partial^2P$. Bound: P9 (2.18) summed over $X\ni x,x'$ ($|R^{ij}(x,x')|\le K_0\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\delta_0L^{-i}|x-x'|}$), then
$$\sum_{i\le j\le J}\beta_{i-1}^{-1}L^{-j\rho_0}e^{-\delta_0L^{-i}|x|}\le2\beta^{-1}L^{d-2}\sum_{i}L^{-i(d-2)}e^{-\delta_0L^{-i}|x|}\frac{L^{-i\rho_0}}{1-L^{-\rho_0}}\le C\beta^{-1}(1+|x|)^{-(d-2+\rho_0)}$$
by Lemma 1.3 ($\sigma=d-2+\rho_0$), which is P9 (2.20) (with the factor $\beta^{-1/2+\rho_1}$ in front, $\beta^{-3/2+\rho_1}$ total). For the mass factor $e^{-c'\sqrt\nu|x|}$: the indices satisfy $i\le J$, $L^J\le L^2/\sqrt\nu$, so $e^{-\delta_0L^{-i}|x|}\le e^{-\delta_0\sqrt\nu|x|/L^2}$ and half of the exponent is used for Lemma 1.3. The last-step terms: $\beta_J^{-2}e^{-\kappa|x|/L^{J}}\le$ the same form. (v) *Convergence as $\nu\downarrow0$* (the new content, §5 item 1): for fixed $(i,j,x)$ the kernel $R^{ij}(x,x';h,h)$ is a continuous function of $\nu\in[0,1]$ at $0$ (the flow with its renormalization conditions, including the large-field parts that enter $R^{(k+1)},P^{(k+1)}$, is carried down to $\nu=0$ and depends continuously on $\nu$ through the contraction mappings; this needs to be a clause of Def-7), and the bound $|R^{ij}|\le K_0\beta^{-1/2+\rho_1}L^{-j\rho_0}e^{-\delta_0L^{-i}|x|}$ is summable over $(i,j)$; Tannery's theorem (dominated convergence for series, `tendsto_tsum_of_dominated_convergence`) gives the limit of $\sum_{i\le j\le J(\nu)}$; the last-step terms are $O(\beta_J^{-2})\to0$.

### 2.4 Notes on $\lambda=\infty$

- *Longitudinal main term.* P9 (4.12) at $\psi=h$ has $H_j=a_jG_jQ_j^*\big(I-a_jG_j(\lambda_j^{-1}+G_j)^{-1}\!\cdots(h\otimes h)\big)$ (the printed formula is garbled in the text layer); as $\lambda_j^{-1}=\lambda^{-1}L^{-2j}\to0$ this becomes $H_j=a_jG_jQ_j^*(I-h\otimes h)$ (`GREEN.md` C14), and P9 p. 519 bounds the $11$ component by $c\beta^{-1}\lambda^{-2}(1+|x-x'|)^{-(d+2)}$ for finite $\lambda$. For hard spins the same follows from $|\varphi|=1$, which forces $\partial_\psi\varphi(h)\,h=0$. Together with $H_{1a}=0$ for $a\ge2$ (symmetry) this gives $(H_jC^{(j)}H_j^*)_{11}=0$: the longitudinal function consists of remainders only, hence the claim $|G_{lg}(0,x)|\le c(1+|x|)^{-(d-2+\rho_0)}$.
- *Transverse part.* $(H_jC^{(j)}H_j^*)_{22}$ uses $H_j^{tr}=a_jG_jQ_j^*$ and $C_{tr}^{(j)}$ (P9 (4.13)): unconstrained, translation invariant, i.e. exactly (2.2).
- *Free flow.* The sum rule (4.17) is exact only for the free sequence $a_{k+1}^{-1}=a_k^{-1}+L^{-2k}a^{-1}$ (P4 (2.9), option (i) of the underdetermination in P4 §5: $c=ab$, $d=b$). With option (ii) of P4 (5.34), $a_{k+1}$ carries a factor $(1+\xi_3)$; then (2.2) changes by sequence perturbations of size $q^k$ and the sum rule gives $G$ only up to errors of the same type as (4.18). I use option (i); Question 2 in §7.

---

## 3. Derivation of Root-C from Root-F, C-1\*, I-G

**Theorem 3.1 (conditional).** Assume Root-F, the interface C-1\* of §2.2 (F1)–(F3) and I-G (G1)–(G3), (G5). Then Root-C holds with the following choice of constants. Let $L_F,M_F,\beta_0^F$ be Root-F's output for $\kappa=\kappa_*$, $c_9=1$, and put
$$q_{\rm C}:=M_FL_F\quad(\text{Root-C's }q),$$
$\rho_1$ as in C-1\*, $\rho_0^{\rm C}:=\min(\rho_0,2\gamma_0)$, $c'$ the minimum of C-1\*'s $c'$ and $\delta_G/(2L^2)$, $c$ large enough for the estimates below, $\beta_0:=\max(\beta_0^F,\beta_*,\beta_1)$, where $\beta_1$ makes $c_\xi q/(2(1-q)\beta_1)\le\frac12$ and $e^{c_\xi q/((1-q)\beta_1)}\le2$.

All constants depend on $(d,N)$ only: $\delta,L_F,M_F,\beta_0^F$ come from Root-F at fixed $\kappa_*,c_9=1$; the C-1\* data are chosen once, before $\beta$. Fix $\beta\ge\beta_0$. Steps A–E build the functions $m,G_{tr},G_{lg}$ and the objects $m_0,\gamma,G_{tr,0},G_{lg,0},G$ of Root-C.

### 3.1 Step A: the functions and the first bullet

Define, for $\nu\in(0,1]$ (and $=0$ otherwise), $m(\nu),G_{tr}(\nu,\cdot),G_{lg}(\nu,\cdot)$ as the limits of §4 (Theorem 4.1): $m(\nu)=\lim_n M_{q_{\rm C}^n}(0;e_1)_1$, $G_{lg}(\nu,z)=\lim_nG_{q_{\rm C}^n}(0,z;e_1)_{11}$, $G_{tr}(\nu,z)=\lim_nG_{q_{\rm C}^n}(0,z;e_1)_{22}$. These are chosen after $\beta$ and before $h$, and do not depend on $h$ (Lemma 0.2(c)). Theorem 4.1 gives the first bullet of Root-C: for all $\nu,h,x,y,\varepsilon$ there is $n_0$ with $|M_\ell(x)-m(\nu)h|<\varepsilon$ and $|G_{\ell,ik}(x,y)-(\dots)|<\varepsilon$ whenever $q_{\rm C}^{n_0}\mid\ell$.

The infinite-volume functions of C-1\* are these functions; the C-1\* decomposition is a statement about them.

### 3.2 Step B: bounds for $\nu>0$

Because $\|\xi(\nu)_k\|\le\frac{c_\xi}{4\beta}q^{k+1}$ and $\beta\ge\beta_1$, `norm_gammaSeq_le` gives $|\gamma_j^{\pm1}|,|\delta_j^{\pm1}|\le e^{c_\xi q/((1-q)\beta)}\le2$ (P4 (5.32)), so $\beta_j(\nu)\in\beta L^{j(d-2)}[\frac12,2]$ is real positive.

*One-point.* $|\mu_j|\le c_*\beta^{-1/2+\rho_1}L^{-j\rho_0}$ and $\beta_{j-1}^{-1/2}\le\sqrt2\,\beta^{-1/2}L^{-(j-1)(d-2)/2}$, so
$$|m_J(\nu)-1|\le\sqrt2c_*\beta^{-1+\rho_1}L^{(d-2)/2}\sum_{j\ge1}L^{-j((d-2)/2+\rho_0)}\le C\beta^{-1+\rho_1},$$
and $|e_m|\le c_*\beta_J^{-2}\le4c_*\beta^{-2}\le c_*\beta^{-1+\rho_1}$ (for $\beta\ge1$). Hence $|m(\nu)-1|\le c\beta^{-1+\rho_1}$ for all $\nu\in(0,1]$ and $\beta\ge\beta_0$, which is the second bullet's first claim; also $|m_J|\le2$ for $\beta$ large.

*Two-point.* By (G2), $|(\beta\gamma_j)^{-1}t_j^{\mu}(x,y)|\le2\beta^{-1}C_GL^{-j(d-2)}e^{-\delta_GL^{-j}|x-y|}$ for $j<J=J(\nu)$. For $j<J$, $L^{-j}\ge L^{-J}\ge\sqrt\nu/L^2$ (C-1\*: $L^J\sqrt\nu\le L^2$), so $e^{-\delta_GL^{-j}|z|}\le e^{-\delta_GL^{-j}|z|/2}e^{-\delta_G\sqrt\nu|z|/(2L^2)}$, and Lemma 1.3 ($\sigma=d-2$, $\delta=\delta_G/2$) bounds the sum over $j$. With $|r|\le c_*(1+|z|)^{-(d-2+\rho_0)}e^{-c'\sqrt\nu|z|}$ this gives, for $z=x-y$ (choose $y=0$),
$$|G_{tr}(\nu,z)|,\ |G_{lg}(\nu,z)|\le c(1+|z|)^{-(d-2)}e^{-c'\sqrt\nu|z|}$$
(after enlarging $c$; $G_{lg}=r_{lg}$ directly). This is the second bullet.

### 3.3 Step C: the limits $\nu\downarrow0$ (P9 (4.15) written out)

We use **Tannery's theorem**: if $a_j(\nu)\to a_j$ as $\nu\downarrow0$ for each $j$ and $|a_j(\nu)|\le b_j$ with $\sum b_j<\infty$, then $\sum_ja_j(\nu)\to\sum_ja_j$ (Mathlib `tendsto_tsum_of_dominated_convergence`). Continuity inputs: for each fixed $k$ the finite products $\gamma_k(\nu)=\prod_{i<k}(1+\xi_i(\nu)_2)^{-1}$, $\delta_k(\nu)$, $\beta_k(\nu)$ are continuous at $\nu=0$ by (F1) (the factors are $\ge\frac12$ in modulus since $|\xi|\le\frac14$). 

*Magnetization.* $m_{J(\nu)}(\nu)=1-\sum_{j\ge1}a_j(\nu)$ with $a_j(\nu)=\mathbf 1_{[j\le J(\nu)]}\beta_{j-1}(\nu)^{-1/2}\mu_j(\nu)$. For fixed $j$, $J(\nu)\ge j$ for small $\nu$ (since $J(\nu)\to\infty$), so $a_j(\nu)\to\beta_{j-1}(0)^{-1/2}\mu_j(0)$; the bound $b_j=\sqrt2c_*\beta^{-1+\rho_1}L^{-(j-1)(d-2)/2}L^{-j\rho_0}$ is summable. Also $|e_m(\nu)|\le4c_*\beta^{-2}L^{-2J(\nu)(d-2)}\to0$. Hence $m(\nu)\to m_0:=1-\sum_{j\ge1}\beta_{j-1}(0)^{-1/2}\mu_j(0)$, and $|m_0-1|\le c\beta^{-1+\rho_1}$.

*Transverse function.* Put $S_J(\nu;x,y):=\sum_{j<J(\nu)}(\beta\gamma_j(\nu))^{-1}t_j^{\nu\delta_j(\nu)}(x,y)$. The $j$-th term tends to $(\beta\gamma_j(0))^{-1}t_j^0(x,y)$: the first factor by continuity, the second because $\mu(\nu):=\nu\delta_j(\nu)\in(0,2\nu]$ tends to $0$ and $t_j^\mu(x,y)\to t_j^0(x,y)$ as $\mu\downarrow0$ (G3). The domination $2\beta^{-1}C_GL^{-j(d-2)}$ is summable. So $S_{J(\nu)}(\nu;x,y)\to S_\infty(x,y):=\sum_{j\ge0}(\beta\gamma_j(0))^{-1}t_j^0(x,y)$, and with (F3), the convergence of $m_J$ and of $r_{tr}$:
$$G_{tr}(\nu,x-y)\ \longrightarrow\ G_{tr,0}(x-y):=m_0^2S_\infty(x,y)+r_{tr}(0;x,y).$$
The right side depends on $(x,y)$ only through $x-y$ because the left side does (take $y=0$ to define $G_{tr,0}(z)$). Likewise $G_{lg}(\nu,z)\to G_{lg,0}(z):=r_{lg}(0;z,0)$. Passing to the limit in Step B gives $|G_{lg,0}(z)|\le c(1+|z|)^{-(d-2+\rho_0)}$ (the factor $e^{-c'\sqrt\nu|z|}\to1$).

In P9 (4.15) the limit is shown for the sum with fixed index structure after dropping the dependence of $\beta_j,\gamma_j,\delta_j$ on $\nu$ and the remainder; the two additions here are (F1)'s continuity and (F3)'s convergence of $r$.

### 3.4 Step D: the lattice Green's function $G$ (proof of (G4))

*Absolute convergence and decay.* By (G2) at $\mu=0$ and Lemma 1.3, $\sum_j|t_j^0(x,y)|\le C(1+|x-y|)^{-(d-2)}$. So $\mathcal G(x,y):=\sum_jt_j^0(x,y)$ converges absolutely and tends to $0$ as $|x-y|\to\infty$ (since $d\ge3$).

*Two exact identities for one step* ($A$ positive definite, $H=\alpha M^{-1}Q^\top$, $M=A+\alpha Q^\top Q$, $\Delta=\alpha-\alpha^2QM^{-1}Q^\top$):
$$A\,H=Q^\top\Delta .\tag{3.1}$$
Indeed $AH=\alpha(M-\alpha Q^\top Q)M^{-1}Q^\top=\alpha Q^\top-\alpha^2Q^\top QM^{-1}Q^\top=Q^\top\Delta$. Iterating along the recursion $A_{i+1}=\Delta_i$,
$$A_0P_J=Q_{(J)}^{\top}A_J,\qquad Q_{(J)}:=Q_{J-1}\cdots Q_0\ \ (\text{composite average over }L^J\text{-blocks}).\tag{3.2}$$

*The sum rule on the torus.* Fix $J\ge1$, $\mu\in(0,1]$, $\ell=L^Jm$. Apply $A_0=-\Delta+\mu$ to (2.1) with $K=J$:
$$\sum_{j<J}A_0T_j^{\ell,\mu}+A_0P_JA_J^{-1}P_J^\top=I,\qquad A_0P_JA_J^{-1}P_J^\top\overset{(3.2)}=Q_{(J)}^\top P_J^\top .$$
Its entries are $\big(Q_{(J)}^\top P_J^\top\big)(x,y)=\sum_uQ_{(J)}(u,x)P_J(y,u)=L^{-Jd}P_J(y,u_J(x))$, where $u_J(x)$ is the block containing $x$; by (G5) they are bounded by $C_PL^{-Jd}$, uniformly in $\ell,\mu$. Since $A_0$ involves only the $2d+1$ entries $x,x\pm e_\mu$, letting $\ell\to\infty$ through multiples of $L^J$ (G1), then $\mu\downarrow0$ (G3), gives for all $x,y\in\mathbb Z^d$
$$\Big|\big(-\Delta_x\textstyle\sum_{j<J}t_j^0\big)(x,y)-\delta_{xy}\Big|\le C_PL^{-Jd}.$$
Letting $J\to\infty$ and using absolute convergence at the finitely many points $x,x\pm e_\mu$: $-\Delta_x\mathcal G(x,y)=\delta_{xy}$.

*Translation invariance.* Put $G(z):=\mathcal G(z,0)$. For fixed $y$ the functions $x\mapsto\mathcal G(x,y)$ and $x\mapsto G(x-y)$ both solve $-\Delta u=\delta_y$ and tend to $0$ at infinity. Their difference is harmonic on $\mathbb Z^d$ and tends to $0$ at infinity, hence $0$ by the maximum principle: if it were not identically $0$, say with positive supremum, the supremum is attained at some point $x_0$ (it tends to $0$ at infinity), the mean-value property $u(x_0)=\frac1{2d}\sum_\mu(u(x_0+e_\mu)+u(x_0-e_\mu))$ forces $u$ to be constant on the neighbours, hence on $\mathbb Z^d$, contradicting decay. So $\mathcal G(x,y)=G(x-y)$.

*The properties of Root-C:* $\sum_\mu(2G(x)-G(x+e_\mu)-G(x-e_\mu))=\mathbf 1_{x=0}$ and $G\to0$ along the cofinite filter. $\square$

(The same maximum-principle argument shows that this $G$ is the unique solution; Root-C does not require uniqueness.)

### 3.5 Step E: the Goldstone asymptotics (P9 (4.16)–(4.18))

Let $\xi=\xi(0)$ (real), $\beta\ge\beta_1$, $c_8:=c_\xi/\beta$. `exists_inv_betaSeq_asymptotics` (with $\gamma:=\gamma_\infty$, $L$ real, $q<1$, $c_8q\le1-q$) gives $\gamma_\infty=\lim\gamma_j(0)$, $|\gamma_\infty-1|\le c_8q/(2(1-q))=c_\xi q/(2(1-q)\beta)\le c/\beta$, so $\gamma_\infty$ is real and $>0$, and for all $j$
$$\Big|\beta_j(0)^{-1}-(\beta\gamma_\infty)^{-1}L^{-j(d-2)}\Big|\le e^2\frac{c_8q}{2(1-q)}\beta^{-1}L^{-j(d-2)}q^j .$$
Since $\beta_j^{-1}=L^{-j(d-2)}(\beta\gamma_j)^{-1}$, the difference $E_j':=(\beta\gamma_j(0))^{-1}-(\beta\gamma_\infty)^{-1}$ satisfies $|E_j'|\le C\beta^{-2}q^j$ (one power of $\beta^{-1}$ more than P9 (4.18) because $c_8=O(\beta^{-1})$). Then
$$S_\infty(x,y)=(\beta\gamma_\infty)^{-1}\sum_jt_j^0(x,y)+\sum_jE_j't_j^0(x,y)=(\beta\gamma_\infty)^{-1}G(x-y)+\mathcal E(x,y),$$
using (G4), and by (G2) and Lemma 1.3 ($q^jL^{-j(d-2)}=L^{-j(d-2+2\gamma_0)}$, $\sigma=d-2+2\gamma_0$)
$$|\mathcal E(x,y)|\le C\beta^{-2}\sum_jL^{-j(d-2+2\gamma_0)}e^{-\delta_GL^{-j}|x-y|}\le C\beta^{-2}(1+|x-y|)^{-(d-2+2\gamma_0)} .$$
Put $\gamma:=\gamma_\infty$ in Root-C. With $y=0$ and Step C,
$$\Big|G_{tr,0}(z)-\frac{m_0^2}{\beta\gamma}G(z)\Big|\le m_0^2|\mathcal E(z,0)|+|r_{tr}(0;z,0)|\le c(1+|z|)^{-(d-2+\rho_0^{\rm C})},$$
since $m_0\le2$ and $(1+|z|)^{-(d-2+s)}$ decreases in $s$. This is the third bullet; with Steps A–D the proof of Theorem 3.1 is complete. $\square$

**What the proof used from C-1\*** (and so what C-1 must deliver): (F1) the rate $c_\xi/\beta$ and the continuity in $\nu$; (F2) with its $\beta^{-1+\rho_1}$ bound and the continuity of $\mu_j$; (F3) with the continuity of the remainder $r$; and the uniform kernels of I-G. The role of Root-F in Theorem 3.1 is only to produce the infinite-volume functions with the stated symmetries (Step A); the quantitative bounds come from C-1\*.

---

## 4. The thermodynamic limit (C-3), complete proofs

**Theorem 4.1.** Let $d\ge3$, $N\ge2$. Apply Root-F with $\kappa=\kappa_*$, $c_9=1$; call the output $\delta,L,M,\beta_0^F$ and put $q:=ML$. Let $\beta\ge\beta_0^F$, $\nu\in(0,1]$. Then:

1. For every $z\in\mathbb Z^d$ the three sequences $n\mapsto m_{q^n}$, $G_{tr,q^n}([z])$, $G_{lg,q^n}([z])$ (notation of Lemma 0.2, $[z]=z\bmod q^n$) converge. Call the limits $m(\nu)$, $G_{tr}(\nu,z)$, $G_{lg}(\nu,z)$ ($m$ does not depend on $z$).
2. For every $\varepsilon>0$ and $z$ there is $n_0$ such that $|m_\ell-m(\nu)|<\varepsilon$, $|G_{tr,\ell}([z])-G_{tr}(\nu,z)|<\varepsilon$, $|G_{lg,\ell}([z])-G_{lg}(\nu,z)|<\varepsilon$ for **every** $\ell$ with $q^{n_0}\mid\ell$. Consequently, for every unit $h$, all $x,y\in\mathbb Z^d$, $i,k\le N$: $|M_{\ell,i}([x])-m(\nu)h_i|<\varepsilon$ and $|G_{\ell,ik}([x],[y])-(G_{tr}(\nu,x-y)(\delta_{ik}-h_ih_k)+G_{lg}(\nu,x-y)h_ih_k)|<2\varepsilon$ for $q^{n_0}\mid\ell$ (with $n_0$ depending on $\nu,\beta,x-y,\varepsilon$ only, not on $h$ or $i,k$).
3. $|m(\nu)-1|\le3$ and $|G_{tr}(\nu,z)|,|G_{lg}(\nu,z)|\le C_*(1+|z|)^{-\theta}e^{-c'\sqrt\nu|z|}$ (Proposition 1.5 with $c_9=1$).

Items 1–2 are the first bullet of Root-C (with $q$ as stated and the functions independent of $h$); item 3 is the part of the second bullet that holds with the weaker constants.

*Proof.* Fix $h=e_1$ and let $k_f$, $T$ be Root-F's output for $(\beta,\nu,e_1)$; $J=k_f+1$. A torus $\mathbb T_\ell$ is admissible if $ML^J\mid\ell$; every $\ell$ with $q^n\mid\ell$, $n\ge J$ is admissible since $q^n=M^nL^n$ is a multiple of $ML^J$. By Lemma 0.2(c), the first assertion of 2 for general $h,x,y$ follows from the statements for the three scalars (with $|\delta_{ik}-h_ih_k|\le1$, $|h_ih_k|\le1$ and evenness of $G_{tr,\ell},G_{lg,\ell}$ to pass from $x-y$ to $y-x$ and from the pair $(x,y)$ to $(0,x-y)$ by translation invariance). Item 3 passes to the limit from Proposition 1.5 because $d_\ell(0,[z])=|z|$ for $\ell>2|z|$.

*Box notation.* For an integer $R\ge1$ put $B_R=\{w\in\mathbb Z^d:|w_\mu|<R\ \forall\mu\}$. If $\ell\ge4R$, the map $\iota_\ell:B_R\to\mathbb T_\ell$, $w\mapsto w\bmod\ell$ is injective, $\mathrm{valMinAbs}\circ\iota_\ell=\mathrm{id}$, and its image is $\{u\in\mathbb T_\ell:d_\ell(0,u)<R\}$. For a finite $A\subset B_R$ write $\iota_\ell A=A.\mathrm{image}$.

**Lemma 4.2 (comparison of two tori).** Let $R\ge1$, $z\in B_R$, and $\ell,\ell'\ge4R$ admissible. Put $\mathcal X^\ell_R=\{X\subset\mathbb T_\ell:X\subset\iota_\ell B_R\}$ and let $\Sigma^\ell_R(m)$, $\Sigma^\ell_R(G_{lg})$, $\Sigma^\ell_R(G_{tr})$ be the sums in Proposition 1.4 (for $h=e_1$, $x=0$, $y=[z]$, indices $(1,1)$ resp. $(2,2)$), restricted to $X\in\mathcal X^\ell_R$. Then
$$\Sigma^\ell_R(\cdot)=\Sigma^{\ell'}_R(\cdot),\qquad\Big|\text{(full sum)}-\Sigma^\ell_R(\cdot)\Big|\le24\cdot2^{-R/(ML^J)} .$$

*Proof.* *Equality.* The sum over $X\in\mathcal X^\ell_R$ equals the sum over $A\subset B_R$ (with $0\in A$, resp. $0,z\in A$; other $X$ give $0$ by the vanishing clause and locality) of $T^\ell_j(0,\iota_\ell A;0)_1$ (resp. of the $\zeta$-derivatives). By the third clause of Root-F with $a=0$ (resp. $a=z$ for the second term) and $A\subset B_R$ (so $4|y_\mu|<4R\le\ell,\ell'$ for $y\in A$), for **every** $g:\mathbb Z^d\to\mathbb C^N$
$$T^\ell_j([0],\iota_\ell A;g\circ\mathrm{valMinAbs})=T^{\ell'}_j([0],\iota_{\ell'}A;g\circ\mathrm{valMinAbs}).$$
Taking $g=0$ gives equality of the one-point terms. Taking $g=g_\zeta:=\zeta e_k\mathbf 1_{\{z\}}$ ($|\zeta|<1$) gives, since $g_\zeta\circ\mathrm{valMinAbs}=\zeta e_k\delta_{[z]_\ell}$ on $\mathbb T_\ell$ and $=\zeta e_k\delta_{[z]_{\ell'}}$ on $\mathbb T_{\ell'}$ (because $|z_\mu|<R\le\ell/4$), equality of the two functions of $\zeta$, hence of their derivatives at $0$. The second term of Proposition 1.4 is treated the same way with the roles of $0$ and $z$ exchanged. The correspondence $A\leftrightarrow\iota_\ell A$ between finite subsets of $B_R$ and subsets of $\iota_\ell B_R$ is a bijection, and polymer-ness need not be tracked: if $\iota_\ell A$ is a polymer but $\iota_{\ell'}A$ is not, both sides are $0$.

*Tail.* A polymer $X\ni0$ at scale $j$ not contained in $\iota_\ell B_R$ contains a point at torus distance $\ge R$ from $0$, so $n(X)\,s_j\ge R+1$ by Lemma 1.2, i.e. $n(X)\ge(R+1)/s_j\ge R/s_J$ ($s_j\le s_J=ML^J$). By Cauchy (as in Proposition 1.5) and Lemma 1.1 each of the sums in question is bounded, for $c_9=1$, by $4\sum_{j\le J}L^{-j\theta}\sum_{n(X)\ge R/s_J}e^{-\kappa_*n(X)}\le4\cdot3\cdot2^{1-R/s_J}$. $\square$

*End of proof of Theorem 4.1.* Let $\varepsilon>0$, $z\in\mathbb Z^d$. Choose $R>|z|$ with $24\cdot2^{-R/(ML^J)}<\varepsilon/4$, and $n_0\ge J$ with $q^{n_0}\ge4R$. For $\ell,\ell'$ multiples of $q^{n_0}$ both are admissible and $\ge4R$, so by Lemma 4.2 each scalar $Q\in\{m,G_{tr}([z]),G_{lg}([z])\}$ satisfies $|Q_\ell-Q_{\ell'}|\le|{\rm tail}_\ell|+|{\rm tail}_{\ell'}|<\varepsilon/2$. Taking $\ell=q^n$, $\ell'=q^{n'}$, $n,n'\ge n_0$: the sequence $Q_{q^n}$ is Cauchy, hence convergent, to $Q_\infty$, and $|Q_\ell-Q_\infty|\le\varepsilon/2$ for every multiple $\ell$ of $q^{n_0}$ (take $\ell'=q^{n}$, $n\to\infty$). $\square$

**Remarks.**
- The proof uses from Root-F only: the identity (Proposition 1.4), the bound on $\|g\|\le\frac12$ with Cauchy, the polymer geometry and the agreement clause. The analyticity of $T$ on the open ball and the identity on the open ball are used to differentiate at $g=0$.
- Torus independence is needed only for polymers of block number $\le R/s_J$; Root-F's clause is stated for the finite sets inside the box $\{|y_\mu|<\min(\ell,\ell')/4\}$, which is exactly what the box $B_R$, $4R\le\min(\ell,\ell')$ provides. The reduction to $x=0$ by translation invariance of the model (Lemma 0.2(a)) avoids needing translation covariance of the $T$'s, which Root-F does not assert (S0-Q04).
- Along all $\ell\to\infty$ (not divisible by $q^n$) nothing is claimed, and nothing follows: the identity of Proposition 1.4 holds only on admissible tori. This is the content of S0-Q02 (c).
- The limit functions $m(\nu),G_{tr}(\nu,\cdot),G_{lg}(\nu,\cdot)$ are independent of the choice of the data $(k_f,T)$ of Root-F (they are limits of model quantities), and of $q$: any $q'$ of the form $M'L'$ for another admissible choice yields the same limit on common multiples. Uniqueness of the state is not claimed.


---

## 5. What no source proves

Confidence = my estimate that the statement is true and provable by the indicated route.

1. **Convergence as $\nu\downarrow0$ of everything except the Gaussian main term at fixed $j$** (F1 continuity of $\xi(\nu)$, F2 continuity of $\mu_j$, F3 convergence of $r(\nu;x,y)$). P9 p. 518 proves only that $\sum_j\beta_j^{-1}[G^{(j)}(v_j)-G^{(j)}(0)]\to0$ with $\beta_j$ treated as $\nu$-independent; Theorem 1.1(b) then speaks of "the $v\downarrow0$ limiting expectations" as if they existed. The audit already recorded this (Audit C-3, D.8; roadmap C-3). *Route:* carry $\nu\in[0,1]$ through the inductive class (P2 already allows $\nu=0$, `GREEN.md` §1.2), observe that the data at scale $j$ depend on $\nu$ only through $\nu_0,\dots,\nu_j$ and the earlier $\xi$'s by contraction mappings with parameters, and use Tannery. *Confidence:* true 90%; routine once $\nu\in[0,1]$ is a parameter of Def-7, 75%. **UNCERTAIN:** whether the large-field regions, thresholds or the choice of the last scale $k_f$ (P7 §4, P9 (4.2)–(4.6)) enter the first $j<k_f$ steps; if they depend on $k_f(\nu)$ the scale-wise independence of $\nu$ fails and (F3) needs the argument "the terms at scale $j$ for $j\le J_0$ are the same for all small $\nu$" proved in the class.
2. **The thermodynamic limit.** P4 p. 720 (remarks at the end of §6) and P9 p. 494 ("$\langle\cdot\rangle=\lim\langle\cdot\rangle_T$") state it without proof or without the sequence of tori. §4 proves it from Root-F. What remains is the clause itself (torus independence of all terms for non-winding polymers, P4 (H.4) p. 677; ER-010), which must be a clause of the inductive class and be shown to survive each step and the polymer expansion (`POLYMER.md` §4.5). *Confidence* 85%.
3. **The exact decomposition (4.17).** P9 cites Parisi [10]; no proof. §2.1 and §3.4 prove it (as the sum rule (G4)) from `laplacian_inv_eq_multiscale` and kernel bounds. *Confidence* 95% for the argument; the kernel bounds (G1)–(G3), (G5) are G-5 of `GREEN.md`, whose pointwise parts the note itself marks as its main risk.
4. **The identification of $G$.** P9 writes $1^{-1}$ ($=(-\Delta)^{-1}$, "$1\equiv\partial^*\partial$") without saying in what sense; Root-C needs $-\Delta G=\delta_0$, $G\to0$. §3.4. *Confidence* 95%.
5. **$|\gamma_\infty-1|\le c/\beta$.** P4 (5.33) gives existence of $\gamma_\infty$ and (via (5.32)) $|\gamma_\infty-1|\le C c_8$ with $c_8$ "arbitrarily small"; the rate $\beta^{-1}$ is read off from (5.25)–(5.30) ($|f_i|\le B_6\beta_{k+1}^{-1}\varepsilon_{k+1}^{-2}$). *Confidence* 85% (the contraction gives $|\xi|\le2|f(0)|$).
6. **P9 (3.13), truncated expectation of a product.** P9 says it "has not been proved in [5]" and argues in two sentences. `POLYMER.md` §4.1: reduced to the product-measure form (3.11) under (H-MY); the reduction of P9's non-product Gaussian expectation goes through P6 (4.35)–(4.42), not redone. *Confidence* 75%.
7. **Lemma 2 (2.21)–(2.22)** and the use of the irrelevancy gap in (3.21)–(3.23): argued with citations to [1] (P1 Lemmas 2.3, 2.4, 2.7–2.9, (2.87)–(2.103)). It is what keeps the bound $L^{-j\rho_0}$ for the corrections added at scale $k+1$ to $M^{(j)}$, $j\le k$. *Confidence* 80%.
8. **The "similar" arguments of §3** ((3.38)–(3.41), (3.44)–(3.49)): sketches. Each estimate has the same structure as the one done in detail, but none is written. *Confidence* 85% that all are as claimed; the exponents $\rho_0,\rho_1,\rho_2,\gamma$ restrictions p. 511 are consistent.
9. **The last-step bounds (4.8)–(4.9).** Argued as "bounded as the terms defined by $R_0^{(k+1)}(g)$ in Sect. 3"; the printed bound in the second display on p. 517 is partly illegible in the text layer (**UNCERTAIN:** the exact power of $|x-x'|$; only the facts that it is $\le c\beta_J^{-2}$ times an exponentially decaying function of $L^{-J}|x-x'|$ and tends to $0$ with $\nu$ are used). *Confidence* 85%.
10. **Passage $\lambda<\infty\to\lambda=\infty$.** P9 treats $\lambda_0\le\lambda\le\infty$ in the statement but computes at finite large $\lambda$ (e.g. $|C_{lg}|\le c\beta^{-1}\lambda^{-2}$); at $\lambda=\infty$ one uses the constrained covariance (P3 (3.9), `GREEN.md` (1.8$'$)). The $G$-operators are the unconstrained ones for the transverse part (`GREEN.md` §1.3). *Confidence* 90%.
11. **Constants independent of $\beta$** ($c,c',\rho_0,\rho_1,q$; S0-Q07): the proof tracks $\beta$ explicitly, so the strong reading is the natural one, but P9 does not say so (open with Roland).

Items 1, 5, 9 are the only ones that need *new* mathematics beyond completing the printed arguments. Items 6–8 and 10 are sources' proofs with gaps of the kind "similarly".

---

## 6. Lean plan and size estimate

Mapping to the roadmap: **C-1** = I-F1–F3 (with C-1a as the inductive source); **C-2** = I-G (the Gaussian decomposition, with the new sum rule) and §3.4–3.5; **C-3** = §4 (done on paper) plus the $\nu\downarrow0$ part §3.3.

Dependency discipline (AGENTS.md rules 3–4, 8): the work below can be done as lemmas about an abstract predicate `RootFClauses` (a definition collecting the clauses of Root-F, in a non-frozen file) and an abstract record for C-1\*; nothing imports a root. The final theorem `lowTemperature_correlations` (inside its provider) combines `logPartition_multiscale`, the C-1 theorem and the lemmas, when both are sealed.

| Package | Content | Lines | Risk |
|---|---|---|---|
| A | Def-1 symmetries: translation invariance of `aprioriMeasure` (`MeasurePreserving.piCongrLeft`-type), $O(N)$ invariance of `Measure.toSphere volume` (cone measure; probably absent from Mathlib), energy/partition/Gibbs transformation, stabilizer argument (sign changes, permutations) giving Lemma 0.2 | 450 | medium: $O(N)$-invariance of `toSphere` |
| B | Lemma 0.1: $Z$ entire, $Z(0)>0$, first and second derivative formulas (`hasFDerivAt_integral_of_dominated_of_fderiv_le`), derivative of $\operatorname{Log}$; matching with Root-F's identity (uniqueness of derivatives on a neighbourhood), Prop 1.4 | 400 | low |
| C | Polymer counting and geometry: block map, block graph degree $\le2d$, connected-set bound $(2d)^{2n}$ (exploration walks), torus distance and Lemma 1.2 | 500 | medium: the animal bound |
| D | Prop 1.5 (Cauchy via `Balaban/Analysis/Cauchy.lean`), sums over $X$ | 300 | low |
| E | §4: box embedding $\iota_\ell$, bijection of finite subsets, use of the agreement clause for $g=0$ and $g=\zeta e_k\mathbf 1_z$, tail bounds, Cauchy $\Rightarrow$ limit, uniformity in $h$ | 600 | low–medium |
| F | Series lemmas: Lemma 1.3, Tannery (existing Mathlib lemma), geometric sums | 250 | low |
| G | Gaussian: one-step identity (3.1), iterate (3.2), "iterated = one-shot" (prolongation and effective-operator compositions, `blockSpinOperator_comp_inv` exists; the prolongation composition is new), sum rule, maximum principle on $\mathbb Z^d$, existence of $G$, the (4.18) step | 700 | low–medium |
| H | Assembly: constants and quantifier order of Root-C, Steps A–E | 500 | low |
| | **Total (excluding C-1\* and I-G)** | **~3,700** | |

Not counted: I-G (the Green package, phase-1 `GREEN.md`; G-5 only, for the single-scale translation-invariant operators on $\mathbb Z^d$ and tori); C-1 itself (inductive form C-1a with Prop 3.1 preserved, last-step conversion, continuity in $\nu$): in the range 5,000–8,000 lines on top of the large-field and polymer packages (rough: the two-point part of the inductive class plus the localisation of $G^{(j)}$ and $R^{ij}$; the $\nu$-continuity adds 1,000–2,000 lines if it must be proved from scratch for every contraction mapping, less if the contractions are written with a parameter from the start).

Order: A, B, C, D, E, F first (they need only the *statement* of Root-F and no flow) and give, alone, the thermodynamic limit and the symmetric structure for Root-C's first bullet. G can proceed in parallel with the Green package. H and the C-1 theorem are last.

---

## 7. Questions

1. **(Author/orchestrator) Form of C-1.** Recommendation: carry C-1a inside the inductive class (Def-7, P9 (H.1)–(H.2)) and state **C-1\*** (§2.2) as the theorem consumed by Root-C, with continuity in $\nu\in[0,1]$ as an explicit clause (F1)–(F3). No source states that clause, so freezing C-1\* means asking for a small addition to the flow (item 1 of §5). Is the observable form with the clause acceptable as the interface, or should the clause be proved separately from a version of C-1\* without it?
2. **(seaturtle2 / author) Free flow at $\lambda=\infty$.** The sum rule (G4) and the identification of $G$ require the free sequence $a_{k+1}^{-1}=a_k^{-1}+L^{-2k}a^{-1}$ for the scale parameter of the Gaussian terms (P4 option (i), $c=ab$, $d=b$; P4 §5 leaves this free). P4 (5.34) also writes option (ii). Please confirm that the reconstructed flow uses (i); under (ii) the argument survives only with additional perturbation estimates of the type (4.18).
3. **(seaturtle2) Units.** P9 (4.12)–(4.17): please confirm (i) that $G_j,Q_j^*$ are the weighted-inner-product operators of P1 with the weight ratio $L^d$ between consecutive lattices, so that $a_j^{\rm P9}L^{j(d-2)}$ is the penalty $b_j$ of §2.1 and the factor $L^{-j(d-2)}$ of (4.17) is the unit conversion; (ii) the exact form of the second bound of P9 p. 517 (powers of $|x-x'|$ and $L^{-(k+1)}$).
4. **(author) Does anything in the large-field part of the flow (the R operation, thresholds, the choice of the last scale) depend on $k_f(\nu)$ for the early scales $j\ll k_f$?** If so, the $\nu$-continuity for the remainder $r(\nu;x,y)$ must be shown through a "stability in the number of scales" statement rather than through continuity of the individual contraction mappings.
