# D1: Dimock, "The renormalization group according to Balaban I. Small fields"

Conventions for this review. Page numbers are those of the arXiv v2 PDF (21 Dec 2012), which has 52 pages and printed page numbers 1–52 equal to the PDF pages. I did not have the Rev. Math. Phys. pagination. Equation, Lemma and Theorem numbers are Dimock's (his numbering is one running sequence: Theorem 1, Lemma 2, ..., Theorem 27 ..., Lemma 35). All formulas were checked on the page images. Bundle keys: P1–P9 as in `SOURCES.md`. Dimock's bibliography maps as follows: [17]=P1, [18]=P2, [19]=P3, [20]=P4, [21]=P5, [22]=P6, [23]=P7, [25]=P9, [4]=E3 (CMP 89), [6]=E4, [7]=E5 (CMP 96), [12]=E6, [13]=E7, [14]=E8, [15]=E9, [16]=E10, [1]=E2, [29]=E11 (Brydges, Les Houches), [33]=E1 (Cammarota).

## 0. Identification

J. Dimock, "The renormalization group according to Balaban I. Small fields", Rev. Math. Phys. 25 (2013) 1330010, arXiv:1108.1335v2. Bundle key **D1**. 52 pages (text pp. 1–37, appendices A–E pp. 38–50, references pp. 51–52).

**What the paper does.** It is an expository, almost self-contained account of Balaban's RG method for the scalar $\phi^4$ model on the 3-torus: ultraviolet (UV) problem, lattice spacing $L^{-\mathsf N}\to0$ in a fixed torus of volume $L^{3\mathsf M}$ (p. 2). The goal (Theorem 1, p. 2) is the stability bound $e^{-c\,\mathrm{Vol}}\le Z/Z(0)\le e^{c\,\mathrm{Vol}}$ for a suitable choice of counterterms. The proof is in three papers. D1 treats a *modified* model, with characteristic functions that keep all fields small (eq. (172), p. 22); it proves one RG step (Theorem 14) and solves the RG flow (Theorem 24) for this modified model. Paper II (large fields, arXiv:1212.5562 = D2) and III (convergence, arXiv:1304.0705 = D3) are needed for Theorem 1 itself. Theorem 1 is not proved in D1 (p. 2: "whose proof comes in the final paper").

**Role relative to the bundle.** D1 post-dates all of P0–P9 and is cited by none of them. The cell "Cited by" for D1 in `SOURCES.md` is "—", and `grep -i dimock` over `papers/P*.md` finds only Brydges–Dimock–Hurd (P4 [4], P5 [7], P6 [8]), a different paper. So section 9 below is the reinterpretation requested in the task: which O(N)-series components D1 proves in a more complete or more standard way. D1 itself cites the O(N) series [17]–[23], [25] as the source of "improvements" (p. 1: "we also incorporate many of the improvements which can be found in [17]–[23]") and of the ingredient (122) (cited to [22] = P6, p. 16).

## 1. Setting and notation

**Lattices and torus (pp. 2–3).** $L$ is a fixed large odd integer. Torus $\mathbb T_{\mathsf M}=(\mathbb R/L^{\mathsf M}\mathbb Z)^3$, volume $L^{3\mathsf M}$. Lattice of spacing $L^{-\mathsf N}$: $\mathbb T^{-\mathsf N}_{\mathsf M}=(L^{-\mathsf N}\mathbb Z/L^{\mathsf M}\mathbb Z)^3$ (1). Inner product (3): $\langle u,v\rangle=L^{-3\mathsf N}\sum_x u(x)v(x)$. $\partial_\mu\phi(x)=(\phi(x+L^{-\mathsf N}e_\mu)-\phi(x))L^{\mathsf N}$ (4), $\Delta=-\partial^*\partial$. Warning on notation: sans-serif $\mathsf M,\mathsf N$ are the torus size and the number of scales; $M=L^m$ (italic) is the side of the large cubes ("$M$-cubes", p. 10: "Warning: $M$ is not the same as the volume parameter"). Distances $|x-y|=\sup_\mu|x_\mu-y_\mu|$.

**Model (2), (5), (6) (p. 2).** $\phi:\mathbb T^{-\mathsf N}_{\mathsf M}\to\mathbb R$,
$$\rho^{\mathsf N}(\phi)=\exp\Big(-\tfrac12\langle\phi,(-\Delta+\bar\mu)\phi\rangle-V^{\mathsf N}(\phi)\Big),\quad V^{\mathsf N}(\phi)=\varepsilon^{\mathsf N}\mathrm{Vol}(\mathbb T_{\mathsf M})+\tfrac12\mu^{\mathsf N}\!\!\int\!\phi^2+\tfrac14\lambda\!\!\int\!\phi^4,$$
with fixed $\bar\mu>0$, $\lambda>0$ and counterterms $\varepsilon^{\mathsf N},\mu^{\mathsf N}$ depending on the lattice spacing (the second form of (2) writes the quadratic part as $-\frac12\|\partial\phi\|^2-\frac12\bar\mu\|\phi\|^2$). Coupling $\lambda$ needs no renormalization (p. 2). $Z_{\mathsf M,\mathsf N}=\int\rho^{\mathsf N}d\phi$ (6).

**Scaled model (pp. 3–4, (8)–(14)).** The change of variables $\Phi_{L^{-\mathsf N}}(x)=L^{\mathsf N/2}\Phi(L^{\mathsf N}x)$ maps to the unit lattice $\mathbb T^0_{\mathsf M+\mathsf N}$ (volume $L^{3(\mathsf M+\mathsf N)}$). The field has scaling dimension $\tfrac12$. Couplings scale as $\bar\mu_0=L^{-2\mathsf N}\bar\mu$, $\lambda_0=L^{-\mathsf N}\lambda$, $\varepsilon_0=L^{-3\mathsf N}E^{\mathsf N}$, $\mu_0=L^{-2\mathsf N}\mu^{\mathsf N}$ (13), (14). Subscript-0 quantities are the RG starting point. This is how the UV problem becomes an infrared problem on a huge torus: all couplings start tiny.

**Block averaging (pp. 3–6).** $B(y)$ = cube of $L^3$ sites centred at $y$ (15)–(16). $(Qf)(y)=L^{-3}\sum_{x\in B(y)}f(x)$, $(Q^Tf)(x)=f(y)$ for $x\in B(y)$ (17); $QQ^T=I$, $Q^TQ$ is a projection. Iterated: $Q_k=Q^k$ (29), $(Q_kf)(y)=\int_{|x-y|<1/2}f$, mapping functions on $\mathbb T^{-k}_{\mathsf M+\mathsf N-k}$ to functions on the same lattice (piecewise constant on unit cubes). Transformation (18)–(28), with Gaussian kernel $\exp(-\frac a{2L^2}\|\Phi_1-Q\Phi_0\|^2)$, normalization $\mathcal N_{a,\Omega}=(2\pi/a)^{|\Omega|/2}$, then back-scaling $\Phi_{1,L}(x)=L^{-1/2}\Phi_1(x/L)$ (21), (22). The integral is preserved (20), (23), (28).

**Backgrounds and free flow (§2.2–2.3, pp. 7–10).** After $k$ steps the density lives on $\Phi_k:\mathbb T^0_{\mathsf M+\mathsf N-k}\to\mathbb R$ and the integration variable is a field $\phi$ on the fine lattice $\mathbb T^{-k}_{\mathsf M+\mathsf N-k}$. Free action
$$S_k(\Phi_k,\phi)=\tfrac{a_k}2\|\Phi_k-Q_k\phi\|^2+\tfrac12\langle\phi,(-\Delta+\bar\mu_k)\phi\rangle\ (46),\qquad \bar\mu_k=L^{2k}\bar\mu_0=L^{-2(\mathsf N-k)}\bar\mu\ (47),\qquad a_k=a\tfrac{1-L^{-2}}{1-L^{-2k}}\ (32),$$
$a_{k+1}=a_ka/(a_k+aL^{-2})$ (39). Minimizer (the "background field"): $\phi_k(\Phi_k)=a_kG_kQ_k^T\Phi_k$ (50) with $G_k=(-\Delta+\bar\mu_k+a_kQ_k^TQ_k)^{-1}$ (49). It is *linear* in $\Phi_k$. Reduced action (54): $S_k(\Phi_k,\phi_k)=\frac12\langle\Phi_k,\Delta_k\Phi_k\rangle$, $\Delta_k=a_k-a_k^2Q_kG_kQ_k^T$. The intermediate (connecting) minimizer $\Psi_k(\Phi_{k+1},\phi)$ is (35), (59); the key identity is $\phi^0_{k+1}(\Phi_{k+1})=\phi_k(\Psi_k)$ (60).

**Fluctuation covariance (Lemma 4, p. 9).** $C_k=(\Delta_k+\frac a{L^2}Q^TQ)^{-1}$ (67); $\frac12\langle Z,(\Delta_k+\frac a{L^2}Q^TQ)Z\rangle$ is the quadratic form (70). Square root by resolvent integral (192)–(193): $C_k^{1/2}=\frac1\pi\int_0^\infty r^{-1/2}C_{k,r}\,dr$, $C_{k,r}=(\Delta_k+\frac a{L^2}Q^TQ+r)^{-1}$, with explicit form (194)–(196) (Lemma 28, App. C): $C_{k,r}=A_{k,r}+a_k^2A_{k,r}Q_kG_{k,r}Q_k^TA_{k,r}$, $A_{k,r}=\frac1{a_k+r}(I-Q^TQ)+\frac1{a_k+aL^{-2}+r}Q^TQ$ (as printed), $G_{k,r}=(-\Delta+\bar\mu_k+a_kQ_k^TQ_k-a_k^2Q_k^TA_{k,r}Q_k)^{-1}$; alternative (196). $G_{k,r}$ interpolates between $G^0_{k+1}$ ($r=0$) and $G_k$ ($r=\infty$). The rescaled fluctuation variable is $W$ with identity covariance, $Z=C_k^{1/2}W$, and $\mathcal W_k=\phi_k(C_k^{1/2}W)=a_kG_kQ_k^TC_k^{1/2}W$ (191).

**Cubes, polymers, tree length (§2.4, §3.1, §3.3, App. A).** $M=L^m$; $\square_z$ = $M$-cubes (in the unit lattice $\mathbb T^m_{\mathsf M+\mathsf N-k}$ of centres, spacing $M$) partitioning the torus; $\tilde\square_z$ = union of the $3^3$ cubes touching $\square_z$ ("$3M$-cube"); $\Delta_y=B_k(y)$ unit cubes. An $M$-polymer $X$ is a connected union of $M$-cubes (connected = adjacent cubes share a 2-dim face, p. 14); $\mathcal D_k$ = set of all $M$-polymers (107). $d_M(X)$ = (length of shortest tree in the continuum torus joining the $M$-cubes of $X$)$/M$ (119); $|X|_M$ = number of $M$-cubes (121). Inequalities (122): $d_M(X)\le|X|_M\le3^d(1+d_M(X))$ (cited to [22] = P6; not proved in D1). Counting (Lemma 25): $\sum_{X\supset\square}e^{-a|X|_M}\le b$, $\sum_{X\supset\square}e^{-\kappa_0d_M(X)}\le K_0$ (290), constants depending only on dimension; Cor 26 (294): sums over $X\cap Y\neq\emptyset$ are $\le K_0|Y|_M$. $LM$-polymers $\mathcal D^0_{k+1}$ appear after reblocking.

**Small-field domains (§3.2, pp. 14–15).** $p_k=p(\lambda_k)=(-\log\lambda_k)^p$ (109), integer $p$; assume $\lambda_k<1$.
- $\mathcal S_k$ (Def. 1, (110)): all $\Phi_k$ with $|\Phi_k-Q_k\phi_k|\le p_k$, $|\partial\phi_k|\le p_k$, $|\phi_k|\le\lambda_k^{-1/4}p_k$ (pointwise, $\phi_k=a_kG_kQ_k^T\Phi_k$). If one fails the density gains $O(e^{-p_k})$.
- $\mathcal R_k$ (Def. 2, (111)), complex fields $\phi:\mathbb T^{-k}_{\mathsf M+\mathsf N-k}\to\mathbb C$ with $|\phi|<\lambda_k^{-1/4-3\epsilon}$, $|\partial\phi|<\lambda_k^{-1/4-2\epsilon}$, $|\delta_\alpha\partial\phi|<\lambda_k^{-1/4-\epsilon}$, where $\delta_\alpha f(x,x')=(f(x)-f(x'))/d(x,x')^\alpha$ is the Hölder quotient, $\frac12<\alpha<1$ (82), and $\epsilon>0$ is a fixed small number. Lemma 8: $\Phi_k\in\mathcal S_k\Rightarrow|\Phi_k|\le2p_k\lambda_k^{-1/4}$, $|\partial\Phi_k|\le3p_k$, and for $\lambda_k$ small $\phi_k\in\mathcal R_k$ (uses Cor 7 and $p_k\le\lambda_k^{-\epsilon}$).

**Analyticity and norms (§3.3, pp. 15–16).** $\mathcal K_k$ (Def. 3): functions $E:\mathcal D_k\times\mathcal R_k\to\mathbb C$, (a) $E(X,\phi)$ depends only on $\phi|_X$, (b) analytic and bounded in $\phi\in\mathcal R_k$, (c) even in $\phi$, (d) invariant under lattice symmetries. $\|E(X)\|_k=\sup_{\phi\in\mathcal R_k}|E(X,\phi)|$ (118); $\|E\|_{k,\kappa}=\sup_X\|E(X)\|_ke^{\kappa d_M(X)}$ (120), a Banach space for $\kappa>0$; $\mathrm{Re}(\mathcal K_k)$ = real subspace (117). Hence $\sum_{X\supset\square}|E(X,\phi)|\le K_0\|E\|_{k,\kappa}$ for $\kappa\ge\kappa_0$ (124). There is a single analyticity domain $\mathcal R_k$ per scale (no analogue of the P-series' two-tier domains $\Xi^c_j(\mathbb B_j(X))$).

**Normalization (§3.5, p. 18).** $E$ is *normalized* if $E(X,0)=0$, $E_2(X,0;1,1)=0$, $E_2(X,0;1,x_\mu)=0$ (135), where $E_n(X,\phi;f_1,\ldots,f_n)=\partial^n_{t_1\ldots t_n}E(X,\phi+\sum t_if_i)|_{t=0}$ (136). Required only for *small* polymers ($d_M(X)<L$); $\mathcal K^{norm}_k$ (137). The extraction map $\mathcal RE$ (158)–(159) and the extracted energy and mass constants (166)–(167).

**Density after $k$ steps (§4.1, (176)–(178), p. 23).** For $\Phi_k\in\mathcal S_k$:
$$\rho_k(\Phi_k)=Z_k\exp\big(-S_k(\Phi_k,\phi_k)-V_k(\phi_k)+E_k(\phi_k)\big),\ V_k(\phi)=\varepsilon_k\mathrm{Vol}+\tfrac12\mu_k\|\phi\|^2+\tfrac14\lambda_k\!\int\!\phi^4,$$
$E_k(\phi)=\sum_{X\in\mathcal D_k}E_k(X,\phi)$ with $E_k(X,\cdot)\in\mathrm{Re}(\mathcal K^{norm}_k)$. Running constants: $\lambda_k=L^k\lambda_0=L^{-(\mathsf N-k)}\lambda$ (106), a parameter, not a dynamical variable; $\varepsilon_k,\mu_k,E_k$ are dynamical.

**The modified RG map (172)–(175), p. 22.**
$$\tilde\rho_{k+1}(\Phi_{k+1})=\mathcal N^{-1}_{aL,\mathbb T^1}\!\int\!\exp\!\big(-\tfrac a{2L^2}\|\Phi_{k+1}-Q\Phi_k\|^2\big)\,\chi^w_k\big(C_k^{-1/2}(\Phi_k-\Psi_k)\big)\chi_k(\Phi_k)\rho_k(\Phi_k)d\Phi_k,$$
$\chi^w_k(W)=\chi(|W|\le p_{0,k})$, $p_{0,k}=(-\log\lambda_k)^{p_0}$, integer $p_0<p$; $\chi_k(\Phi_k)=\chi(\Phi_k\in\mathcal S_k)$; then back-scaling (173). Here $\Psi_k$ is the free minimizer (59) and $C_k^{-1/2}(\Phi_k-\Psi_k)$ is the whitened fluctuation. The first factor $\chi^w$ is the "small fluctuation" restriction; the second is the "small field" restriction (largely superfluous on the target set, p. 22).

### Glossary

| Symbol | Meaning | Where |
|---|---|---|
| $\mathsf M,\mathsf N$ | torus size $L^{\mathsf M}$; number of scales (spacing $L^{-\mathsf N}$) | (1), p. 2 |
| $L$ | block factor, large odd | p. 2, p. 4 |
| $M=L^m$ | large-cube side (in unit-lattice units) | p. 10 |
| $\square_z,\tilde\square_z,\Delta_y$ | $M$-cube, $3M$-cube, unit cube | p. 10 |
| $Q,Q^T,Q_k$ | block average, transpose, $k$-fold average | (15), (17), (29) |
| $a,a_k$ | kernel coefficient; free flow $a_k=a\frac{1-L^{-2}}{1-L^{-2k}}$ | (32), (39) |
| $\bar\mu,\bar\mu_k$ | fixed mass-squared; $L^{2k}\bar\mu_0$ | (47) |
| $\varepsilon_k,\mu_k,\lambda_k$ | running vacuum energy, mass counterterm, coupling | (177), (106) |
| $G_k$ | $(-\Delta+\bar\mu_k+a_kQ_k^TQ_k)^{-1}$ | (49) |
| $\phi_k(\Phi)$ | linear background field $a_kG_kQ_k^T\Phi$ | (50) |
| $\Psi_k,\phi^0_{k+1}$ | intermediate minimizer, next-scale background | (35), (59), (58) |
| $\Delta_k,C_k$ | reduced quadratic form; fluctuation covariance | (54), (67) |
| $C_{k,r},A_{k,r},G_{k,r}$ | resolvent family for $C_k^{1/2}$ | (193)–(196) |
| $\mathcal W_k$ | background induced by fluctuation: $a_kG_kQ_k^TC_k^{1/2}W$ | (191) |
| $\mathcal D_k$, $d_M(X)$, $|X|_M$ | $M$-polymers, tree length, size | (107), (119), (121) |
| $\mathcal S_k$, $\mathcal R_k$ | real small-field set; complex analyticity domain | (110), (111) |
| $p_k,p_{0,k}$ | small-field and fluctuation thresholds | (109), (175) |
| $\epsilon,\alpha$ | domain-gap parameter; Hölder exponent in $(\frac12,1)$ | (111), (82) |
| $\mathcal K_k,\mathcal K^{norm}_k$, $\|\cdot\|_{k,\kappa}$ | spaces and norms of localized functionals | (116)–(120), (137) |
| $\kappa,\kappa_0,K_0$ | decay rate; counting constants | (120), (123), (290) |
| $\mathcal B$, $(\cdot)_{L^{-1}}$ | reblocking and scaling-down | (127), (125) |
| $s_\square$, $G_k(s)$ | decoupling parameters; weakened Green's function | (102), (103) |
| $\beta$ (p. 33–34) | exponent in Theorem 24 ($0<\beta<\frac14-10\epsilon$); NOT inverse temperature | (263) |

## 2. Main results

**Theorem 1 (p. 2), stated, not proved here.** For $\lambda,\bar\mu>0$ there are a choice of counterterms $E^{\mathsf N},\mu^{\mathsf N}$ and a constant $c$ with
$$\exp\big(-c\,\mathrm{Vol}(\mathbb T_{\mathsf M})\big)\le Z_{\mathsf M,\mathsf N}/Z_{\mathsf M,\mathsf N}(0)\le\exp\big(c\,\mathrm{Vol}(\mathbb T_{\mathsf M})\big)\quad\text{for all }\mathsf M,\mathsf N.$$
Status: cited to D2, D3 (proof "comes in the final paper"). Upper bound due to Glimm–Jaffe [36]; Balaban [1]–[5]; Brydges–Dimock–Hurd [31] gave another RG proof.

**Lemma 2 (p. 5), proved (pp. 5–6).** $\rho_k(\Phi_k)=\mathcal N^{-1}_{a_k,\mathbb T^0}\int\exp(-\frac{a_k}2\|\Phi_k-Q_k\phi\|^2)\rho_0(\phi_{L^k})d^{(k)}\phi$, with $a_k$ as in (32). Proof by induction, completing the square in $\Phi_k$ (34)–(43).

**Lemmas 3, 4, 5 (pp. 8–10), proved.** Free flow: (Lemma 3) the joint minimizer of $J(\Phi_{k+1},\Phi_k,\phi)=\frac a{2L^2}\|\Phi_{k+1}-Q\Phi_k\|^2+\frac12a_k\|\Phi_k-Q_k\phi\|^2+\frac12\|\partial\phi\|^2+\frac12\bar\mu_k\|\phi\|^2$ is $(\Psi_k,\phi^0_{k+1})$ with $\phi^0_{k+1}=L^{-2}a_{k+1}G^0_{k+1}Q^T_{k+1}\Phi_{k+1}$, $G^0_{k+1}=(-\Delta+\bar\mu_k+a_{k+1}L^{-2}Q^T_{k+1}Q_{k+1})^{-1}$ (57), (58), and $\phi^0_{k+1}=\phi_k(\Psi_k)$ (60); (Lemma 4) $\tilde\rho_{k+1}=Z_k\mathcal N^{-1}(2\pi)^{|\mathbb T|/2}(\det C_k)^{1/2}\exp(-S^0_{k+1}(\Phi_{k+1},\phi^0_{k+1}))$ with $C_k$ as in (67); (Lemma 5) after scaling the result equals $Z_{k+1}\exp(-S_{k+1}(\Phi_{k+1},\phi_{k+1}))$, $Z_{k+1}=Z_k\mathcal N^{-1}(2\pi)^{|\mathbb T|/2}(\det C_k)^{1/2}$ (74), (78).

**Lemma 6 and Corollary 7 (pp. 11–13), proved modulo (80)–(82).** Statement: for $M$ sufficiently large (depending on $L$) the random-walk series $G_k=\sum_\omega G_{k,\omega}$ (84) converges for $G_k$, $\partial G_k$, $\delta_\alpha\partial G_k$ and gives, for $x,x'\in\Delta_y$ and $\mathrm{supp}f\subset\Delta_{y'}$, $|(G_kf)(x)|,|(\partial G_kf)(x)|,|(\delta_\alpha\partial G_kf)(x,x')|\le Ce^{-\frac12\gamma_0d(y,y')}\|f\|_\infty$ (85), with $\gamma_0=O(L^{-2})$. Corollary 7: $|G_kf|,|\partial G_kf|,|\delta_\alpha\partial G_kf|\le C\|f\|_\infty$ uniformly in $k,\mathsf M,\mathsf N$ (100).

**Theorem 14 (p. 23), the one-step theorem of D1.** Let $L,M$ be sufficiently large and $\lambda_k$ sufficiently small (depending on $L,M$). Suppose $\rho_k$ has the representation (176)–(178) for $\Phi_k\in\mathcal S_k$ and
$$|\mu_k|\le\lambda_k^{1/2},\qquad\|E_k\|_{k,\kappa}\le1\qquad(179).$$
Then $\rho_{k+1}(\Phi_{k+1})$ has a representation of the same form for $\Phi_{k+1}\in\mathcal S_{k+1}$, with
$$\varepsilon_{k+1}=L^3\varepsilon_k+\mathcal L_1E_k+\varepsilon^*_k,\quad\mu_{k+1}=L^2\mu_k+\mathcal L_2E_k+\mu^*_k,\quad\lambda_{k+1}=L\lambda_k,\quad E_{k+1}=\mathcal L_3E_k+E^*_k\qquad(180)$$
where the $\mathcal L_i$ are linear with $|\mathcal L_1E_k|\le O(1)L^{-\epsilon}\|E_k\|_{k,\kappa}$, $|\mathcal L_2E_k|\le O(1)L^{-\epsilon}\lambda_k^{1/2+6\epsilon}\|E_k\|_{k,\kappa}$, $\|\mathcal L_3E_k\|_{k+1,\kappa}\le O(1)L^{-\epsilon}\|E_k\|_{k,\kappa}$ (181), and the "starred" (fluctuation-integral) terms satisfy $|\varepsilon^*_k|\le O(1)L^3\lambda_k^{1/4-10\epsilon}$, $|\mu^*_k|\le O(1)L^3\lambda_k^{3/4-4\epsilon}$, $\|E^*_k\|_{k+1,\kappa}\le O(1)L^3\lambda_k^{1/4-10\epsilon}$ (182). The standing assumption $\kappa\ge10(\kappa_0+1)$ is imposed in the proof (p. 31, below (244)), not in the statement. The remark after the theorem says the unstarred terms are zeroth-order perturbation theory (scaling and rearrangement), the starred terms are the effect of the fluctuation integral and "are not necessarily smaller than the unstarred terms, although they do have bounds" (p. 23).

**Lemma 22 (p. 33), derivative bounds** in the region $|\mu_k|\le\frac12\lambda_k^{1/2}$, $\|E_k\|_k\le\frac12$: $|\partial\mu^*_k/\partial\mu_k|\le O(1)L^3\lambda_k^{1/4-4\epsilon}$, $\|\partial\mu^*_k/\partial E_k\|\le O(1)L^3\lambda_k^{3/4-4\epsilon}$, $|\partial E^*_k/\partial\mu_k|\le O(1)L^3\lambda_k^{-1/4-10\epsilon}$, $\|\partial E^*_k/\partial E_k\|\le O(1)L^3\lambda_k^{1/4-10\epsilon}$ (252), (253). Proved from analyticity in $(\mu_k,E_k)$ (the proof "works as well for $\mu_k\in\mathbb C$, $E_k\in\mathcal K^{norm}_k$ with exactly the same bounds", p. 32) plus Cauchy estimates (254)–(258). The analyticity of $\mu^*_k,E^*_k$ in $(\mu_k,E_k)$ is asserted ("one can show", p. 32), not demonstrated.

**Theorem 24 (p. 36), the flow theorem.** Fix $0<\beta<\frac14-10\epsilon$ (263). Let $\lambda_K=L^{-\Delta}\lambda$ be sufficiently small. Then for $\mathsf N\ge\Delta$, $K=\mathsf N-\Delta$, there is a unique sequence $\varepsilon_k,\mu_k,E_k$, $k=0,\ldots,K$, solving the RG equations (259),
$$\varepsilon_{k+1}=L^3\varepsilon_k+\mathcal L_1E_k+\varepsilon^*_k,\ \ \mu_{k+1}=L^2\mu_k+\mathcal L_2E_k+\mu^*_k,\ \ E_{k+1}=\mathcal L_3E_k+E^*_k,$$
with *final/initial* conditions $\varepsilon_K=0$, $\mu_K=0$, $E_0=0$ (260), satisfying $|\mu_k|\le\lambda_k^{1/2+\beta}$, $\|E_k\|_{k,\kappa}\le\lambda_k^\beta$ (283) and $|\varepsilon_k|\le O(1)\lambda_k^\beta$ (284). Proof: Banach space $\mathsf B$ of sequences $\underline\xi=(\xi_0,\ldots,\xi_K)$, $\xi_k=(\mu_k,E_k)$, norm $\sup_k\{\lambda_k^{-\frac12-\beta}|\mu_k|,\lambda_k^{-\beta}\|E_k\|_{k,\kappa}\}$ (264); subset $\mathsf B_1$ with $\mu_K=0$, $E_0=0$, $\|\underline\xi\|<1$; map $T$ (267) from the backward form (261) ($\mu_k=L^{-2}(\mu_{k+1}-\mathcal L_2E_k-\mu^*_k)$, $E_k=\mathcal L_3E_{k-1}+E^*_{k-1}$) maps $\mathsf B_1$ to itself and is a $\frac12$-contraction (Lemma 23, pp. 35–36, (270)–(282)); $\varepsilon_k$ is then solved backward (285)–(288). The paper's remarks (p. 37): "our method is efficient, but the estimates are not very sharp" ($\varepsilon_k=O(\lambda_k^\beta)$, $\mu_k=O(\lambda_k^{\frac12+\beta})$ rather than $O(\lambda_k)$). The initial values of $\varepsilon_0,\mu_0$ depend on $K$, hence on $\mathsf N$: this is "non-perturbative renormalization" (p. 34). At $k=K$ the lattice is $\mathbb T^0_{\mathsf M+\Delta}$ and the total mass is $\bar\mu_K$.

**Supporting theorem, Theorem 27 (cluster expansion, App. B, pp. 39–43), proved.** There is $c_0$ such that if $H(X,\Phi)$ (depending only on $\Phi|_X$) satisfies $|H(X,\Phi)|\le H_0e^{-\kappa d_M(X)}$ on the support of an ultralocal probability measure $\mu=\prod_xd\mu(\Phi(x))$ with $\kappa>3\kappa_0+3$ and $H_0\le c_0$, then $\Xi=\int\exp(\sum_XH(X,\Phi))d\mu=\exp(\sum_YH^\#(Y))$, $H^\#(Y)$ depends only on $H(X)$ with $X\subset Y$, $|H^\#(Y)|\le O(1)H_0e^{-(\kappa-3\kappa_0-3)d_M(Y)}$. (In the statement $c_0$ "depends only on the dimension"; see section 7.)

**Inductive hypotheses.** D1 has no separate list (H.1)–(H.n). The inductive hypothesis is the representation (176)–(178) together with (179). Four ingredients play the role of the P-series hypotheses: form (176)–(177) [P1–P4 (H.1), (H.2)]; localization with decay $e^{-\kappa d_M(X)}$, $\|E_k\|_{k,\kappa}\le1$ [(H.4) of P4 / (H.5) of P1]; analyticity in $\mathcal R_k$ and evenness/symmetry (116) [(H.3), (H.4) of P4]; normalization (135) [(H.5) of P4]. There is no analogue of the generating functional hypotheses (H.7) of P4 (no source $g$ in D1).

## 3. Proof architecture

**§1 (pp. 1–3).** Overview and model; scaling to the unit lattice (1.3).

**§2 The RG transformation (pp. 3–13).** Routine algebra of Gaussian integrals plus the one analytic piece (random walks).
- §2.1 (Lemma 2): composition of $k$ averaging steps gives one Gaussian kernel with $a_k$.
- §2.2: *free flow*: with $\rho_0$ Gaussian, $\rho_k=Z_ke^{-S_k(\Phi_k,\phi_k)}$, minimizer $\phi_k=a_kG_kQ_k^T\Phi_k$ and (54).
- §2.3 (Lemmas 3–5): the single-step version, producing $\Delta_k,C_k$ and the identity $\phi^0_{k+1}=\phi_k(\Psi_k)$. Dimock remarks that the proof "is maybe not the shortest, but it develops machinery we want to use later" (p. 5).
- §2.4: *random-walk expansion* of $G_k$ (Lemma 6, Cor 7). Mechanism: the cube Green's functions $G_k(\tilde\square)=[-\Delta+\bar\mu_k+a_kQ_k^TQ_k]^{-1}_{\tilde\square}$ with Neumann b.c. on the $3M$-cube $\tilde\square_z$ satisfy the exponential bounds (80)–(81); a quadratic partition of unity $1=\sum_zh_z^2$ (86)–(88) with $h_z=\prod_\mu h((x_\mu-z_\mu)/M)$, $h\in C_0^\infty(-\frac23,\frac23)$, $|\partial h|\le O(1)M^{-1}$, $|\partial\partial h|\le O(1)M^{-2}$ (89); parametrix $G_k^*=\sum_zh_zG_k(\tilde\square_z)h_z$ (90); then $(-\Delta+\bar\mu_k+a_kQ_k^TQ_k)G_k^*=I-K$, $K=\sum_zK_zG_k(\tilde\square_z)h_z$, $K_z=-[(-\Delta+a_kQ_k^TQ_k),h_z]$ (91)–(92). Solution $G_k=G_k^*\sum_nK^n$ (93), the random-walk form (94) over paths $\omega=(\omega_0,\ldots,\omega_n)$ of centres at mutual distance $\le M$. Key estimate (95)–(97): $|K_zf|\le O(1)M^{-1}(\|1_{\Delta_y}f\|_\infty+\|1_{\Delta_y}\partial f\|_\infty)$, because $[-\Delta,h_z]$ involves derivatives of $h_z$ and $[Q^TQ,h_z]$ is the integral operator (96); only interior derivatives of $G_k(\tilde\square)$ enter since $\mathrm{supp}\,h_z$ is well inside. Each factor in a path of length $n$ contributes $(CM)^{-1}e^{-\gamma_0d}$ (98), summation over paths costs $(3^d)^n$ (99), so the series converges for $M$ large. The potential term $\bar\mu_k$ cancels in the commutator. Cor 7 follows by summing $e^{-\frac12\gamma_0d(y,y')}$ over $y'$.
- §2.5 *decoupling*: attach $s_\square\in[0,1]$ to each $M$-cube, $s_\omega=\prod_{\square\subset X_\omega}s_\square$, $X_\omega=\bigcup_{j\ge1}\tilde\square_{\omega_j}$ (the starting cube $\tilde\square_{\omega_0}$ is omitted), $G_k(s)=\sum_\omega s_\omega G_{k,\omega}$ (103): $G_k(1)=G_k$, $G_k(0)=G_k^*$ (104). The same bounds hold for complex $|s_\square|\le M^{1/2}$ (replace $(CM^{-1})^n$ by $(CM^{-1/2})^n$).

**§3 Localized functionals (pp. 14–22).** Definitions (small fields, norms, polymers) and three operations on $E\in\mathcal K_k$, which implement the power counting:
- *Scaling* $F_{L^{-1}}(X,\phi)=F(LX,\phi_L)$ (125), Lemma 9: $\phi\in\mathcal R_{k+1}\Rightarrow\phi_L\in L^{-3/4-3\epsilon}\mathcal R_k$, and $\|F_{L^{-1}}(X)\|_{k+1}\le\|F(LX)\|_k$.
- *Reblocking* $(\mathcal BE)(Y,\phi)=\sum_{X:\bar X=Y}E(X,\phi)$ (127) where $\bar X$ = union of the $LM$-cubes meeting $X$; Lemma 10: $\|\mathcal BE\|_{k,\kappa'}\le9K_0L^3\|E\|_{k,\kappa}$ with $\kappa'=L(\kappa-\kappa_0-1)$ (129) (loses the factor $L^3$, gains decay $L\times$ because tree lengths measured in $LM$ units shrink by $L$).
- *Normalization* (§3.5): Lemma 11: for $E\in\mathcal K^{norm}_k$, $L$ large, $\lambda_k$ small: $\|(\mathcal BE)_{L^{-1}}\|_{k+1,\kappa}\le O(1)L^{-\epsilon}\|E\|_{k,\kappa}$ (138), i.e. normalization converts the $L^3$ growth into a gain $L^{-\epsilon}$. Proof: large polymers ($d_M(X)\ge L$) gain $e^{-L}$ from the decay (139), (140); small polymers: Taylor expand $E(X,\phi_L)$ in $\phi_L$ to second order with Cauchy-estimate remainder on the circle $|t|=\frac12L^{3/4+3\epsilon}$ (145) (gains $L^{-3-12\epsilon}$), and expand $E_2(X,0;\phi_L,\phi_L)$ around a base point $x_0\in X$ using $\phi_L(x)=\phi_L(x_0)+(x-x_0)\cdot\partial\phi_L(x_0)+\Delta_{\phi_L}(x,x_0)$ (146)–(147). The first two terms of (148) vanish by normalization; the remaining terms gain at least $L^{-3-\epsilon}$ (152); the weakest, the term $E_2(X,0;\phi_L(x_0),\Delta_{\phi_L})$, gains $L^{-5/2-\alpha-\epsilon}$, which needs the Hölder exponent $\alpha>\frac12$ (153)–(157). Lemma 12: $\|\mathcal RE(X)\|_k\le O(1)\|E(X)\|_k$ for the extraction $\mathcal R$ (160); Lemma 13: extracted energy and mass satisfy $|\varepsilon(E)|\le O(1)\|E\|_{k,\kappa}$, $|\mu(E)|\le O(1)\lambda_k^{1/2+6\epsilon}\|E\|_{k,\kappa}$ (169). The odd-derivative and $\phi\,\partial_\mu\phi$ terms vanish by evenness and reflection (168).

**§4 One RG step with small fields (pp. 22–33).** The proof of Theorem 14.
- §4.1: statement and the modified definition (172)–(175).
- §4.2: for $\Phi_{k+1}\in\mathcal S^0_{k+1}$ (183) (the scaled-down version of $\mathcal S_{k+1}$) expand around $\Psi_k$: $\Phi_k=\Psi_k+Z$, $\phi_k(\Psi_k+Z)=\phi^0_{k+1}+\mathcal Z_k$ with $\mathcal Z_k=a_kG_kQ_k^TZ$. Linear terms vanish, giving $S^0_{k+1}(\Phi_{k+1},\phi^0_{k+1})$, the Gaussian $d\mu_{C_k}(Z)$, and $E^+_k=E_k-V_k$ evaluated at $\phi^0_{k+1}+\mathcal Z_k$ ((184)–(190)). Both $V_k$ and $E_k$ are treated as the *interaction* for the fluctuation integral.
- §4.3 (Lemmas 15, 16): the restriction $\chi_k(\Psi_k+C_k^{1/2}W)=1$ is automatic for $|W|\le p_{0,k}$ because $p_{0,k}/p_k=(-\log\lambda_k)^{p_0-p}$ is as small as desired. Proof: $|C_k^{1/2}W|$, $|\mathcal W_k|$, $|\partial\mathcal W_k|$, $|\delta_\alpha\partial\mathcal W_k|\le Cp_{0,k}$ using (193)–(195), the kernel bound (203) for $D_{k,r}=Q_kG_{k,r}Q_k^T$ (which comes from App. E, an $L^2$ random walk expansion) and Cor 7. Also $\mathcal W_k\in\lambda_k^{1/4}\mathcal R_k$.
- §4.4 *fluctuation integral* $\Xi_k(\phi)=\int\exp(E^+_k(\phi+\mathcal W_k))\chi^w_k(W)d\mu_I(W)$ (206): normalize the product measure $\chi^w_k d\mu_I$ (the product over sites of a one-dimensional restricted Gaussian; normalization $e^{-\varepsilon^0_k\mathrm{Vol}}$ with $\varepsilon^0_k=O(e^{-p_{0,k}^2/2})$ (208)–(210)), split off $E^+_k(\phi)$, so $\Xi_k=\exp(-\varepsilon^0_k\mathrm{Vol}+E^+_k(\phi))\Xi'_k(\phi)$ with $\Xi'_k=\int\exp(\delta E^+_k(\phi,\mathcal W_k))d\mu^*_k$. Lemma 17: $|\delta E^+_k(X,\phi,\mathcal W_k)|\le O(1)\lambda_k^{1/4-10\epsilon}e^{-\kappa d_M(X)}$ for $\phi\in\frac12\mathcal R_k$, $|W|\le p_{0,k}$ (by explicit computation for the potential part, (214)–(216): the dominant term is $2\lambda_k\int\phi^3\mathcal W_k\sim\lambda_k^{1/4}$; Cauchy estimate in $t$ on $|t|=\lambda_k^{-1/4}/4$ for the $E_k$ part, (217)–(219)). The remark (220) reblocks to $LM$-polymers.
- §4.5 *localization*: the only non-locality is in $W$ through $\mathcal W_k$. Introduce $s=\{s_\square\}$ for $LM$-cubes (221), weakened covariance $C_k^{1/2}(s)=\frac1\pi\int r^{-1/2}C_{k,r}(s)dr$ with the RW expansion of $G_{k,r}$ based on $LM$-cubes (222)–(223), and $\mathcal W_k(s)=a_kG_k(s)Q_k^TC_k^{1/2}(s)W$ (224). Mayer-type identity $f(s_\square=1)=f(0)+\int_0^1ds\,\partial_sf$ iterated over the cubes outside $Y$ gives (226): $(\delta E^+_k)'(Y)=\sum_{Z\supset Y}\delta E^+_k(Y,Z)$ with $\delta E^+_k(Y,Z)=\int ds_{Z-Y}\partial_{s_{Z-Y}}[(\delta E^+_k)'(Y,\phi,\mathcal W_k(s))]|_{s_{Z^c}=0,s_Y=1}$; define $(\delta E^+_k)^{loc}(Z)=\sum_{Y\subset Z}\delta E^+_k(Y,Z)$ (228). Lemma 18: only connected $Z$ contribute and $(\delta E^+_k)^{loc}(Z)$ depends only on $\phi,W$ on $Z$ (proof: at $s_{Z^c}=0$, $G_k(s)$, $C^{1/2}_k(s)$ preserve functions supported on the components of $Z$, p. 29). Lemma 19: $|(\delta E^+_k)^{loc}(Z,\phi,W)|\le O(1)L^3\lambda_k^{1/4-10\epsilon}e^{-L(\kappa-2\kappa_0-2)d_{LM}(Z)}$ (229): analyticity in $|s_\square|\le M^{1/2}$ ($\kappa_1=\frac12\log M$), Cauchy bound (231), and Lemma 20 (tree length inequality $Md_M(Y)\le M|Y-X|_M+Md_M(X)$, with a full proof (234)).
- §4.6 *cluster expansion* (Lemma 21, p. 30): $\Xi'_k(\phi)=\exp(\sum_Y E^\#_k(Y,\phi))$ with $|E^\#_k(Y,\phi)|\le O(1)L^3\lambda_k^{1/4-10\epsilon}e^{-L(\kappa-5\kappa_0-5)d_{LM}(Y)}$ (237), by Theorem 27 applied with $LM$-cubes, valid when $O(1)L^3\lambda_k^{1/4-10\epsilon}\le c_0$. The measure $\mu^*_k$ is a product, as Theorem 27 requires.
- §4.7: scaling back: $E^\#_{k,L^{-1}}$ has norm $\le O(1)L^3\lambda_k^{1/4-10\epsilon}$ provided $\kappa\ge10(\kappa_0+1)$ ((243)–(244)); $\varepsilon^0_k$ and the quartic and mass terms scale canonically (240): $\frac12L^2\mu_k\|\phi_{k+1}\|^2$, $\frac14\lambda_{k+1}\int\phi^4_{k+1}$ with $\lambda_{k+1}=L\lambda_k$ (245).
- §4.8: neither $(\mathcal BE_k)_{L^{-1}}$ nor $E^\#_{k,L^{-1}}$ is normalized, so apply the extraction (166): $\mathcal L_1,\mathcal L_2,\mathcal L_3$ from $(\mathcal BE_k)_{L^{-1}}$ (246)–(247), and $\varepsilon^*_k=L^3\varepsilon^0_k+\varepsilon(E^\#)$, $\mu^*_k=\mu(E^\#)$, $E^*_k=\mathcal R(E^\#)$ (248)–(249). Footnote 5: normalizing all polymers rather than only small ones "presents other difficulties".
- §4.9: derivative bounds (Lemma 22).

**§5 The flow (pp. 33–37).** A discrete dynamical systems argument: contraction in the weighted sequence space (264) after rewriting the equations in a form where the dangerous (growing) directions are solved backward. The text says this section "is not particularly due to Balaban" and cites [32], [30] (Brydges–Dimock–Hurd; Brydges lectures) for similar methods in IR problems (footnote 6, p. 33). The genuinely hard estimates of D1 are the fluctuation-integral bounds (Lemmas 15–21) and the Green's function bounds (App. D). Routine: Lemmas 2–5, 8–10, 12–13, 22–24 (given the bounds of Theorem 14).

**Appendices.**
- A (pp. 38–39): counting of polymers, Lemma 25, Cor 26. Full proof by tree/path counting ($2^d$ choices per step, path length $2(n-1)$).
- B (pp. 39–43): cluster expansion, Theorem 27 (below).
- C (p. 44): identity (334)–(335), proved by Gaussian integration.
- D (pp. 45–48): Green's function bounds; Lemma 29 (mass lower bound), Lemma 30 ($L^2$ exponential decay), Lemma 31 (kernel of $\mathcal H_k=a_kG_k(\Omega)Q_k^T$, cited to [4], not proved), Lemma 32, Lemma 33. The text says "We sketch a proof" (p. 45).
- E (pp. 49–50): random-walk expansion for $G_{k,r}$ in $L^2$ (Lemmas 34–35).

**Theorem 27 proof (App. B, pp. 39–43), steps.**
1. Mayer expansion $\exp(\sum_XH)=\prod_X(e^{H(X)}-1+1)=\sum_{\{Y_j\}}\prod_jK(Y_j,\Phi)$ over collections of disjoint connected $Y_j$ with $K(Y,\Phi)=\sum_{\{X_i\}:\cup X_i=Y,\ \text{not splittable}}\prod_i(e^{H(X_i)}-1)$ (300)–(302). For $H_0\le\log2$: $|e^H-1|\le2H_0e^{-\kappa d_M}$ (303). Tree-length inequality (305): $Md_M(Y)\le\sum Md_M(X_i)+M(n-1)$. Result (307): $|K(Y,\Phi)|\le O(1)H_0e^{-(\kappa-\kappa_0-2)d_M(Y)}$ on the support of $\mu$; here $c_0$ is chosen so that $2c_0K_0\kappa_0e^{\kappa-\kappa_0}\le1$, so $c_0$ depends on $\kappa$ (p. 40).
2. Integrate $\prod K(Y_j)$ using independence of fields at different sites: $K^\#(Y)=\int K(Y,\Phi)d\mu$ (308)–(310).
3. Identify $\sum_{\{Y_i\}}\prod K^\#(Y_i)=\exp(\sum H^\#)$ with $H^\#(Y)=\sum_n\frac1{n!}\sum_{(Y_1..Y_n):\cup Y_i=Y}\rho^T(Y_1,\ldots,Y_n)\prod K^\#(Y_i)$ (311)–(322), via the standard Ursell/Penrose graph argument as a formal series.
4. Convergence: $|\rho^T|\le$ number of trees in the graph (323), cited as "one can show" (no proof); then tree sums with Cayley's formula and the counting bound (324)–(333) give $|H^\#(Y)|\le O(1)H_0e^{-(\kappa-3\kappa_0-3)d_M(Y)}$.

## 4. Ingredients and prerequisites

**4a. From the bundle (P0–P9).** None is used inside D1 as a logical input. D1 says it "incorporates many of the improvements found in [17]–[23]" (p. 1). The only specific use I could locate is (122), cited to [22] = P6 (p. 16). The method of D1 follows P3 (localization), P4 (one step) and P6 §4 (cluster expansion with product measure) in structure.

**4b. Outside the bundle (as cited by D1).**
- [4] = E3, CMP 89 (1983) 571, "Regularity and decay of lattice Green's functions": cited for the bounds (80)–(82) (p. 11), for Lemma 31 (proof in D: "[4]. First establish the result by Fourier series on the whole lattice. Then extend to $\Omega$ by multiple reflections"), and for identity (373) (also [34]). Essential for the pointwise bounds; D1 only sketches.
- [7] = E5, CMP 96 (1984) 223, and [19] = P3: cited for (80)–(82) (p. 11 "References are [4], [7], [19]"), and Appendix D says "The proof follows [4] with improvements suggested by [19]".
- [34] J. Dimock, "Quantum electrodynamics on the 3-torus I, II" (math-phys/0210020, 0407063): for (373).
- [33] = E1 (Cammarota), [29] = E11 (Brydges), [37] Glimm–Jaffe, [40] Seiler: general references for the cluster expansion (App. B). The proof is self-contained apart from (323).
- [28] Brydges–Yau and [32] Brydges–Dimock–Hurd: idea of normalizing only small polymers ("A similar distinction was first exploited in [28]", p. 18; "roughly follows [32]" for normalization, p. 18).
- [36] Glimm–Jaffe, [35] Feldman–Osterwalder, [31] Brydges–Dimock–Hurd: prior stability results (p. 2).
- [1]–[5] Balaban, (Higgs)$_{2,3}$ and $\phi^4_3$ ultraviolet stability: the original treatment (E2 = [1]).

**4c. Standard mathematics.** Gaussian integration and completing the square; discrete Laplacian with Neumann boundary conditions on cubes; Combes–Thomas conjugation by $e^{q\cdot x}$ (Lemma 30); Neumann series with a smooth quadratic partition of unity; Cauchy estimates for analytic functions in a ball of a sequence space; Mayer expansion, Ursell/Penrose tree-graph bound, Cayley's formula; Banach contraction principle; Fourier analysis on the lattice (only cited).

## 5. Dependency ledger

| Result | Uses (internal) | Other bundle | External | Status |
|---|---|---|---|---|
| Lemma 2 (composition of averagings) | (15)–(28) | analogue P1 (2.9)–(2.11), P4 (2.8) | none | proved |
| Lemmas 3–5 (free single step) | Lemma 2 | analogue P4 (2.8)–(2.25) | none | proved |
| Lemma 6, Cor 7 (RW expansion, bounds) | (80)–(82), (89), (95)–(99) | P3 §2 analogue | [4], [7], [19] for (80)–(82) | expansion proved; (80)–(82) sketched (App. D) |
| §2.5 decoupling | Lemma 6 | P3 Props 2.1–2.3 analogue | none | proved (one paragraph) |
| Lemma 8 (S to R) | Cor 7 | none | none | proved |
| Lemma 9 (scaling) | (126) | none | none | proved |
| Lemma 10 (reblocking) | (122), (123) | none | (122) cited to [22]=P6 | proved given (122) |
| Lemma 11 (normalization gain $L^{-\epsilon}$) | Lemmas 9, 10, (122) | P1 §3 analogue | none | proved |
| Lemmas 12–13 | Lemma 11 | none | none | proved |
| Theorem 14 | Lemmas 2–21, 27 | P4 Thms 1–2 analogue | none beyond Lemmas | proved (modulo sketched App. D, (122), analyticity in $(\mu,E)$) |
| Lemmas 15–16 (smallness of fluctuation background) | Cor 7, (193)–(196), (203) | none | App. E | proved |
| Lemma 17 (bounds on $\delta E^+$) | Lemma 16 | none | none | proved |
| Lemmas 18–20 (localization, tree geometry) | Lemma 6, §2.5 | P3 Prop 4.3 analogue | none | proved |
| Lemma 21 (cluster expansion) | Lemma 19, Thm 27 | P6 §4 analogue | none | proved |
| Theorem 27 | Lemma 25, (305) | none | (323) uncited standard fact | proved except (323) |
| Lemmas 22–23, Theorem 24 | Theorem 14, Lemma 22 | analogue P4 Prop 5.1 | none | proved (analyticity in $(\mu,E)$ asserted) |
| Lemmas 29–30 (decay of cube Green's functions) | none | none | none | proved |
| Lemma 31 (kernel of $\mathcal H_k$) | none | none | [4] | cited |
| Lemmas 32–33 (decay of $G_k(\Omega)$, sup norm) | Lemmas 29–31, (373) | none | [4], [34] for (373) | sketched |
| Lemmas 34–35 (RW for $G_{k,r}$, $L^2$) | Lemma 30 pattern | none | none | proved in outline ("follow") |
| Theorem 1 | none in D1 | none | D2, D3 | deferred |

## 6. Constants and parameters

Order of choice, as I reconstruct it (D1 never gives a global order; "constants depending on $L$" are written $C$, absolute constants $O(1)$, p. 10).
1. Dimension $d=3$ (the paper says "although not necessarily in dimension $d=3$" only in App. A). $a>0$ arbitrary (p. 4: "the positive constant $a$ is arbitrary"; but Lemma 29 and the bound $\gamma_0=O(L^{-2})$ have constants depending on $a$ implicitly). $\bar\mu>0$, $\lambda>0$ given.
2. $L$ large (odd) with the requirements: $L^{-\epsilon}$ small in Lemma 11, $e^{-L}9K_0L^3\le L^{-1}$ (p. 18), $L^{\beta-3/2}\le\frac14$ and $L^{-2}\lambda_k^{6\epsilon}\le\frac14$ in Lemma 23 (p. 35), $L\ge2$ for $\kappa\ge10(\kappa_0+1)$ (p. 31).
3. $\epsilon>0$ fixed small (domain gap, (111)), $\alpha\in(\frac12,1)$ (Hölder exponent), $\beta\in(0,\frac14-10\epsilon)$ (flow exponent, (263)).
4. $\kappa_0\ge1,K_0$ from Lemma 25 (dimension only, $\kappa_0\ge3^da$ with $a>2d\log2$); $\kappa\ge10(\kappa_0+1)$ for the scaling loss (p. 31); Theorem 27 needs $\kappa>3\kappa_0+3$ (applied at $L(\kappa-2\kappa_0-2)$).
5. $M=L^m$ large: the RW expansion needs $C(CM)^{-1}\cdot3^d\ldots<1$ (99), with $C$ depending on $L$; the decoupling radius $e^{\kappa_1}=M^{1/2}$ must satisfy $\kappa_1-1\ge\kappa'=L(\kappa-\kappa_0-1)$ (p. 29, "We can assume $\kappa_1-1\ge\kappa'$"), which forces $\log M\ge2(L(\kappa-\kappa_0-1)+1)$: $M$ is exponentially large in $L\kappa$. So $\kappa$ is chosen before $M$, the opposite of the P-series, where $M$ large and $\kappa$ "arbitrarily large depending on $M$" are claimed to be mutually compatible (see `BIG_PICTURE.md` §4).
6. Integers $p>p_0$ with $p_{k}=(-\log\lambda_k)^p$, $p_{0,k}=(-\log\lambda_k)^{p_0}$; no explicit lower bounds on $p_0$ are needed besides $p_0<p$ and the Gaussian tail estimate $e^{-p_{0,k}^2/2}\ll$ powers of $\lambda_k$ (needs $p_0\ge1$).
7. $\lambda_k\le\lambda_{max}(L,M)$ small: this is the single smallness condition, replaced at the start by taking $\lambda_K=L^{-\Delta}\lambda$ small ((268): choose $\lambda$ small with $\Delta=0$, or $\Delta$ large). The flow runs for $k\le K=\mathsf N-\Delta$ with $\lambda_k\le\lambda_K$.
8. Output of Theorem 24: unique solution with $|\mu_k|\le\lambda_k^{1/2+\beta}$, $\|E_k\|\le\lambda_k^\beta$; $c$ of Theorem 1 comes from D3.

Note the dimensional constant in $\mathcal R_k$: all of these use the same two scales $\lambda_k^{-1/4}$ (field) and $\lambda_k^{1/2}$ (mass), reflecting the $\phi^4$ potential $\lambda\phi^4+\mu\phi^2$.

## 7. Weak spots and open points

1. **Theorem 1 is not proved here.** D1 proves only the modified model. The remainder needs D2, D3, which treat large fields in the sense of this model (a different, easier large-field problem than the O(N) series, because the large-field penalty comes directly from $\exp(-\frac14\lambda\int\phi^4)$ and the fluctuation Gaussian).
2. **Green's function bounds (80)–(82) are only sketched** (App. D, "We sketch a proof", p. 45). What is actually proved: Lemma 29 (mass lower bound by $c_0(-\Delta+I)$ on unit cubes and unions of $M$ cubes with Neumann b.c.), Lemma 30 ($L^2$ off-diagonal exponential decay via Combes–Thomas conjugation, with $\delta_0=O(1)$). What is cited or compressed: Lemma 31 (decay of the kernel of $\mathcal H_k=a_kG_k(\Omega)Q_k^T$; proof cited to [4]), identity (373) (cited to [4] or [34]), and the passage from $L^2$ to the pointwise bounds on $G_k,\partial G_k,\delta_\alpha\partial G_k$ in Lemma 33 ("the other bounds are similar"). The Hölder estimate (81) is not derived anywhere in full. The mechanism of the bootstrapping through (364)–(365) (the lower-depth operator $G^0_{k+1}(\Omega)$ is $G_{k+1}$ at a coarser lattice after scaling) is an implicit induction on $k$ that is not written out. UNCERTAIN how much of Lemma 33 is a circular use of lower-$k$ bounds.
3. **Printed errors.** (i) p. 11, below (83): "$3^d=9$ neighbors"; $3^3=27$; (99) uses $(3d)^n$ instead of $(3^d)^n$. Harmless. (ii) Theorem 27 states "$c_0$ depending only on the dimension" and "$O(1)$ depending only on the dimension", but the proof (p. 40, after (306)) says "(So $c_0$ does depend on $\kappa$)". In the application $\kappa$ is fixed first, so the logic is fine, but the dependence must be recorded (compare 6.5 above). (iii) p. 24: "These conditions imply $\Phi_{k+1,L}\in\mathcal S_{k+1}$"; the needed direction is $\Phi_{k+1}\in\mathcal S_{k+1}\Rightarrow\Phi_{k+1,L}\in\mathcal S^0_{k+1}$, which does follow from (183) and the scaling, so the sentence appears to state the converse loosely. (iv) The title of Section 2.3 and the proof of Lemma 4 write $d\Phi_k$ after change of variable without the Jacobian; fine since volume factors are collected in $Z_k$. (v) p. 33, (259)–(260): $E_0=0$ is the initial condition, while $\varepsilon_K=\mu_K=0$ are terminal; the statement before (260) "we do not at first specify initial values for $\varepsilon_k,\mu_k$" is consistent. (vi) Theorem 14's statement does not list the assumption $\kappa\ge10(\kappa_0+1)$ and the condition $\kappa_1-1\ge\kappa'$ on $M$ versus $\kappa$.
4. **Inequality (122)** ($d_M(X)\le|X|_M\le3^d(1+d_M(X))$) is quoted from [22] = P6 and never proved in D1 (Lemma 25(2) uses $d(X)\ge3^{-d}|X|-1$ "quoted in (122)"). It is used in Lemma 10, Lemma 19 and Lemma 25.
5. **Estimate (323)** ($|\rho^T|\le$ number of trees in $g$, "one can show") is the standard Penrose tree-graph inequality; stated without proof or citation.
6. **Analyticity of $\mu^*_k,E^*_k$ in $(\mu_k,E_k)$** (p. 32) is asserted ("one can show"). The contraction argument (Lemma 23) uses only the Lipschitz bounds derived from this analyticity by Cauchy estimates.
7. **Lemma 11, constants.** The factor $L^{-\epsilon}$ (not $L^{-\text{large}}$) is a consequence of choosing the domain $\mathcal R_k$ so large that everything is absorbed in powers of $\lambda_k$ (see (153) "$(9M(L+1)\lambda_k^\epsilon)\le1$"). It would not survive in a setting where the analyticity radius is only a power of $L$ larger than the typical field (the O(N) setting).
8. **$p_{k+1}$ versus $p_k$.** (183)–(200) use $p_{k+1}\le p_k$ (true as $\lambda_{k+1}=L\lambda_k>\lambda_k$) and $|\phi^0_{k+1}|\le L^{-3/4}\lambda_k^{-1/4}p_k$; checked, no error found.
9. **Analyticity in $W$** is never needed (only analyticity in $\phi$ and in $s$); the support restriction $|W|\le p_{0,k}$ is used throughout instead.
10. Unreadable passages: none. All formulas were legible; one doubtful transcription: the second coefficient in $A_{k,r}$ (195), which on the page reads $\frac1{a_k+aL^{-2}+r}$; it agrees with (338) ("$(a_k+r+aL^{-2}Q^TQ)^{-1}=A_{k,r}$" on constants and orthogonal complement), so I take it as correct.

## 8. Preliminary formalization notes

Self-contained, formalizable early (for a Lean project on the O(N) series this is infrastructure, not the O(N) content itself):
- Gaussian free flow and composition of block averages (Lemmas 2–5): finite-dimensional linear algebra and Gaussian integrals; Mathlib has finite-dimensional Gaussian integrals ("integral_gaussian" in dimension one; multivariate requires work).
- Polymer counting (Lemma 25, Cor 26) and tree-length geometry (Lemma 20, (122)): finite combinatorics on $\mathbb Z^d$; needs a notion of minimal tree / connected union of cubes (not in Mathlib in this form).
- Cluster (Mayer) expansion (Theorem 27): a complete written proof exists for an ultralocal measure and polymers with tree-length decay; formalization is substantial (Penrose bound, Cayley's formula; Cayley's formula for labeled trees is partially in Mathlib (guess)). Alternative: a Kotecký–Preiss theorem.
- Contraction in a weighted sequence space (Theorem 24 / Lemma 23): Banach fixed point is in Mathlib; the work is in setting up the Banach spaces $\mathcal K_k$ (bounded analytic functions on a polydisc-like domain of a finite-dimensional complex space, sup norm).
- Cauchy estimates for analytic functions on products of discs: Mathlib has one-variable estimates; several variables must be assembled by iteration.

Hardest parts:
- Green's function pointwise and Hölder bounds (Lemmas 31–33, App. D–E), and the random-walk expansion with the multi-scale operator. This is the same difficulty as in the O(N) case (see section 10 for alternatives).
- The normalization estimate (Lemma 11) and the fluctuation integral (Lemmas 15–19): long but elementary; the main burden is bookkeeping of exponents of $\lambda_k$ and $L$.
- The whole scheme needs only real-analytic bounded functions of a lattice field with sup-norm domain conditions, so a first formalization could treat finite lattices (finite sums) throughout and state the Theorem 14 estimates uniformly in lattice size.

## 9. What the O(N) series uses from this paper (reinterpreted)

No paper of P0–P9 cites D1 (chronologically impossible: D1 is 2011/2013; the series is 1995–1999). I find no defective citation to D1 in the bundle. The task asks instead which O(N)-series components D1 proves more completely or in a more standard way. For each component: D1's exact item, its statement, and whether it applies to the O(N) setting.

### 9.1 Gaussian RG identities, free flow, composition of averages

D1: Lemma 2 (p. 5), (30), (32) $a_k=a\frac{1-L^{-2}}{1-L^{-2k}}$; Lemmas 3–5 (pp. 8–10). Statement of the identity used later: $\rho_k=Z_k\exp(-S_k(\Phi_k,\phi_k(\Phi_k)))$, $\phi_k=a_kG_kQ_k^T\Phi_k$, $S_k=\frac12\langle\Phi_k,\Delta_k\Phi_k\rangle$ with $\Delta_k=a_k-a_k^2Q_kG_kQ_k^T$; and the single-step form with covariance $C_k=(\Delta_k+\frac a{L^2}Q^TQ)^{-1}$.

O(N) counterparts: P1 (1.11)–(1.13) (the transformation), (2.8)–(2.11) (free flow, connecting problem), P2 (4.2)–(4.4), (4.39), P4 (2.8)–(2.14), (2.19)–(2.25), P5 (1.40)–(1.41), P9 (4.12)–(4.18) (the transverse Gaussian block $C_{k,tr}$ at $\psi=h$ with $G_j=(-\Delta^{L^{-j}}+a_jQ_j^*Q_j+\nu_j)^{-1}$).

Applicability: applies as stated to the *Gaussian part* of the O(N) problem (transverse modes at $\psi=h$, and the "spin-wave" propagator of P9 (4.17), cited by P9 to Parisi): replace $\bar\mu_k$ by $\nu_k$, and $\beta_k$ appears as an overall factor of the action. It does not apply to the nonlinear minimizers $\phi_k(\psi;\alpha)$ of P2 (those involve the multiplier field $\alpha$ and the constraint). D1's proof of the free-flow identity is one page and completely explicit, including normalization constants and scaling (Lemma 5), whereas the O(N) papers state these identities in the course of larger arguments. Adaptation: $N$ components, torus $\mathbb Z/ML^n\mathbb Z$, fields not rescaled (P-series scaling $\beta\to\beta L^{d-2}$ instead of $\Phi_L=L^{-1/2}\Phi(x/L)$ of D1; D1's scaling is the same up to the factor $L^{(d-2)/2}$ moved into $\beta$).

### 9.2 Fluctuation covariance and its square root

D1: Lemma 4 (67); (192)–(196), Lemma 28 (App. C, p. 44). Statements: $C_k^{1/2}=\frac1\pi\int_0^\infty r^{-1/2}C_{k,r}dr$ and $C_{k,r}=A_{k,r}+a_k^2A_{k,r}Q_kG_{k,r}Q_k^TA_{k,r}$ with $A_{k,r},G_{k,r}$ as in (195).

O(N) counterparts: P3 §3, (3.9) (explicit Gaussian formula for the resolvent, "12-type walk expansion", Prop 3.1), P4 (2.19)–(2.25).

Applicability: the same operator structure; in the O(N) case $G_{k}(\alpha)$ replaces $G_k$ and $Q$, $a$ are the generating-set operators of P2. Lemma 28's proof (Gaussian integration with an auxiliary field, (336)–(339)) is short and could be reused verbatim with $-\Delta+\bar\mu_k$ replaced by $-\Delta+\nu+\alpha$ (any symmetric positive operator in place of $-\Delta+\bar\mu_k$): only the identity $(a_k+r+aL^{-2}Q^TQ)^{-1}=A_{k,r}$ (using that $Q^TQ$ is a projection) and Gaussian algebra are used. Needs: $\alpha$-dependent operator, and positivity for the real range.

### 9.3 Random-walk expansion for $G=(-\Delta+Q^*aQ+\ldots)^{-1}$ and exponential decay

D1: Lemma 6 and Corollary 7 (pp. 11–13), (80)–(82), (86)–(99); local decay Lemma 29, Lemma 30 (pp. 45–47); Lemmas 34–35 (pp. 49–50).

O(N) counterparts: P2 §3 (uses CMP 96 (2.57) for $G(\alpha)=(-\Delta^D+Q^*aQ+\nu+\alpha)^{-1}$ in scale-weighted sup and Hölder norms), P3 §2 (random-walk expansion with decoupling parameters; local decay "from CMP 96 (2.33)"), P4 (2.25).

Does D1 prove them in full? **The expansion and its convergence: yes, in full** (partition of unity, parametrix, commutator $K_z$, path sum). **The input bound on the local (cube) Green's function with Neumann conditions: partly** ($L^2$ exponential decay in full by Combes–Thomas, Lemma 30; pointwise, derivative and Hölder bounds only sketched or cited to [4]). Method of proof: Neumann series $G=G^*(1-K)^{-1}$ with $\|K\|=O(M^{-1})$ in a weighted $\ell^\infty$ norm; local decay by Combes–Thomas conjugation $e^{-q\cdot x}De^{q\cdot x}$ with $|q|\le\delta_0$.

Applicability to the O(N) case, in order of difficulty:
- The commutator $K_z=-[(-\Delta+a_kQ_k^TQ_k),h_z]$ (92) is unaffected by adding a multiplication operator (mass, $\nu$ or $\alpha$): $[\alpha,h_z]=0$. So the argument carries over to $-\Delta+Q^*aQ+\nu+\alpha$ with $\alpha(x)$ nonconstant, provided the local Green's functions with $\alpha$ satisfy the same bounds; D1's Lemma 29/30 give these when $\alpha\ge-c$ with $c$ small relative to the $a_kQ_k^TQ_k$ mass, which is the situation of P2 ($|\alpha|<(L^j\eta)^{-2}c_0$). This is my assessment, not a statement in D1.
- Multi-scale operators $Q^*(\mathbb B_k)a(\mathbb B_k)Q(\mathbb B_k)$ with Dirichlet boundary conditions on generating sets $\Omega_1\supset\cdots\supset\Omega_k$ (P2 (1.1)–(1.3)): D1 treats only the global operator $a_kQ_k^TQ_k$ on the torus, with a single $a_k$ and Neumann conditions on cubes. The commutator $[Q^*aQ,h_z]$ is still given by an integral operator of the form (96) if $a$ is constant on unit cubes, but this is not in D1.
- Hölder norm (81): needed by P2/P3 (the Hölder derivative of $\alpha$-equations); in D1 only $\delta_\alpha\partial G_k$ with $\alpha\in(\frac12,1)$, and only sketched.
- Decay rate: D1 gets $\gamma_0=O(L^{-2})$ (Lemma 33), matching P4's $\gamma_0=O(L^{-2})$; in the O(N) case with $\nu>0$ one also wants the $\sqrt\nu$ rate (P9 Thm 1.1(a)), for which D1 gives no information ($\bar\mu_k$ is dropped in the bounds: "the parameter $\bar\mu_k$ is generally tiny and cannot help with this uniform bound", p. 45).

### 9.4 Localization expansion with decoupling parameters

D1: §2.5 (p. 13), §4.5 (pp. 28–29), Lemmas 18–20 (pp. 29–30).

O(N) counterparts: P3 Prop 2.1–2.3, Prop 3.1, Prop 4.3 (p. 81), P6 §4 (Lemma 4.1, "decoupling parameters $t_Y$"). Statements: $F(1)=\sum_{\mathscr C}\prod_{\square\in\mathscr C}\int_0^1ds_\square\partial_{s_\square}F|_{s(\mathscr C^c)=0}$ and the restriction to connected supports through the property that at $s_{Z^c}=0$ the operators preserve the components of $Z$.

Applicability: same idea and same resulting estimate form (decay $e^{-\kappa'd(Z)}$, with $\kappa$ degrading at each step, $\kappa\to L(\kappa-2\kappa_0-2)$, versus the "$2\kappa$ doubling" of P3 Prop 4.3 for $Y$). D1's version is much shorter because (i) the integrand is a function of the *single* field $\phi+\mathcal W_k(s)$, (ii) there is no composition of nonlinear backgrounds $\psi^{(j)}_k(\psi)$ (no need for P3's composition formula (4.16)), (iii) polymers are in $\mathbb R^3$ with only one scale of cubes. Adaptation to O(N): the dependence on $\psi'$ goes through nonlinear $\psi^{(j)}_k(\psi^{(k)}(\theta)+\psi')$, i.e. the functions $\delta\phi_k(s),\delta\alpha_k(s)$ of P3 Props 2.1–2.3; the nonlinear $\alpha$-equation needs the extra P3 (2.24)–(2.45) argument. D1's Lemma 18 argument (support on components of $Z$) is the model for P3 Prop 2.3.

### 9.5 Cluster (polymer) expansion for the fluctuation integral

D1: Lemma 21 (p. 30), Theorem 27 and its proof (App. B, pp. 39–43), preceded by Lemma 25, Cor 26.

O(N) counterparts: P6 (4.46)–(4.51) (the cluster expansion with product measure and connectivity modulo $\Omega^c$), P7 (3.27)–(3.28), (4.14), P9 (4.4)–(4.6); the external references Brydges Les Houches (E11), Cammarota (E1).

Applicability: D1's proof is the standard Mayer expansion for an ultralocal (product) measure, with the activities bounded by $e^{-\kappa d_M(X)}$; this is what P6 §4 does (after rescaling the Gaussian is a product measure and the covariance sits inside the interaction). Theorem 27 can be used directly for the *small-field* part of the O(N) fluctuation integral (with $\psi\in\mathbb R^N$ per site and the restriction $|\psi|<p_1(\beta_k)$ in $\chi^{(k)}$), provided only the support bound $|H|\le H_0e^{-\kappa d}$ is checked; not for the large-field remainders (P7) or the variant with connectivity modulo $\Omega^c$.

### 9.6 Normalization / power counting (renormalization conditions)

D1: §3.5 (pp. 18–22), Lemmas 11–13, (135)–(169).

O(N) counterparts: P1 §3 (renormalization conditions H.6–H.7, effective potential, gradient expansion, Ward identity, Prop 3.4, Cor 3.5, Prop 3.10, Cor 3.11), P4 §4.

Does D1 prove it more completely/standardly? D1 gives a complete, short version for a scalar even model. Statement: for $E\in\mathcal K^{norm}_k$, $\|(\mathcal BE)_{L^{-1}}\|_{k+1,\kappa}\le O(1)L^{-\epsilon}\|E\|_{k,\kappa}$. Applicability: *does not apply as stated*. Reasons: (i) no $O(N)$ symmetry and no stabilizer analysis ($E_2$ reduced by evenness and reflection only), (ii) no marginal direction (no analogue of P1's term $\frac12(v_0-v_1+\nu v_2)\|\partial\psi\|^2$ and its Ward identity), (iii) the huge analyticity domain $\mathcal R_k$ makes irrelevance trivial (see 7.7). What is reusable is the structure: Cauchy estimates on the polydisc, Taylor expansion about a base point of the polymer with remainder controlled by a Hölder bound on $\partial\phi$ (146)–(157), and the split of polymers into small ($d_M<L$) and large (gain $e^{-L}$). P1's lattice Taylor formula (3.97, from CMP 109) plays the role of (146)–(148).

### 9.7 RG equations (flow of running constants)

D1: §5, Lemma 23, Theorem 24 (pp. 33–37).

O(N) counterparts: P4 §5, Prop 5.1 (solution of the $3\times3$ system for $(\zeta,b,c,d,e)$ by contraction on a polydisc), P4 Thm 2, (1.9)–(1.10), (5.33).

Applicability: different structure (see section 10). D1 solves a global two-point boundary-value problem (tuning of bare counterterms for a UV problem); the O(N) series solves a local (one-step) fixed-point problem inside each step, with the flow of $(\beta_k,a_k,\lambda_k,\nu_k)$ forward and bounds $|\beta_{k+1}^{-1}b_{k+1}|<\frac14c_8L^{-2\gamma(k+1)}$ giving limits. Not reusable except for the generic weighted-sequence-space contraction (264)–(272).

### 9.8 Explicit mismatches to flag (items cited in the bundle but absent here)

Since the bundle does not cite D1, there are no missing cited items. Items that the O(N) series needs and D1 does not contain: nonlinear minimizer with constraint (P2 Props 1.1, 3.1, 4.1), O(N)-invariant effective potential and Ward identity (P1 §3), large-field operators and $R$ operation (P5–P7; D1 only mentions large fields as the subject of D2, p. 22 and p. 37), source terms $\mathcal F_k(g)$ and correlation functions (P9), a flow of $\beta_k$.

## 10. Relevance to the formalization

**Verdict.** Use D1 as a *blueprint for the linear/Gaussian skeleton and the generic analytic machinery*, not as a blueprint for the whole O(N) series. It is cleaner and more complete on: (a) the free flow and Gaussian identities, (b) the covariance square root, (c) the random-walk expansion mechanics, (d) decoupling-parameter localization in its simplest form, (e) the polymer expansion with a full proof, (f) the abstract Banach-space bookkeeping of $(\mathcal K_k,\|\cdot\|_{k,\kappa})$ with scaling/reblocking/normalization operators. It is not a blueprint for the nonlinear variational problems, the O(N)/Ward-identity renormalization, the flow of $\beta_k$, or large fields. For large fields D2 would need its own review; it is the only real candidate for a large-field blueprint and, because the $\phi^4$ large-field problem is easier (penalty directly from the potential), the transfer to the O(N) $R$-operation is uncertain.

**Essential differences from the O(N) series (my assessment, from the pages cited).**
1. *UV versus IR.* D1's model has a fixed torus and $\mathsf N\to\infty$ (spacing $L^{-\mathsf N}$); after scaling all couplings are tiny ($\lambda_0=L^{-\mathsf N}\lambda$, (13)) and the flow runs *toward* strong coupling; the only dangerous growth is $\varepsilon_k$ ($L^3$), $\mu_k$ ($L^2$), $\lambda_k$ ($L$); the problem is super-renormalizable, so it suffices to track mass and energy (relevant terms). In the O(N) series the effective temperature $\beta_k^{-1}\sim L^{-k(d-2)}\to0$ and the relevant parameters are $\lambda_k,\nu_k$ (growing) and the marginal ones $\beta_k,a_k$; irrelevant terms must be shown to contract with only a polynomial gap ($L^{j\gamma}$).
2. *Size of the analyticity domain.* D1: $\mathcal R_k$ has radius $\lambda_k^{-1/4-3\epsilon}$, huge compared with the fields ($p_k\le\lambda_k^{-\epsilon}$ times $\lambda_k^{-1/4}$ at most), so any fixed power of $L$ or $M$ is absorbed by smallness of $\lambda_k$ (e.g. (153)). In the O(N) series the radius is $\varepsilon_j=\alpha_0L^{-j\alpha}$, only a factor $L^{j\gamma}$ above the typical fluctuation $\beta_j^{-1/2}$; hence all the delicate bookkeeping of P1 §3 and the choice of $\gamma<\frac12$.
3. *Linear versus nonlinear background field.* D1's background $\phi_k=a_kG_kQ_k^T\Phi_k$ is the minimizer of the *quadratic* part only, linear in $\Phi_k$; the quartic term and $E_k$ enter the fluctuation integral as interaction. In the O(N) series the background is the minimizer of the full nonlinear action with the constraint, solved with the multiplier $\alpha$ (P2). D1 therefore has no counterpart of P2 (Props 1.1, 3.1, 4.1), nor of the delicate $\lambda\to\infty$ issue. For O(N) with hard spins ($\lambda=\infty$) the constraint is inherently nonlinear: spins live on the sphere, block averages are not on the sphere, and the relevant manifold of backgrounds is curved.
4. *Symmetry and renormalization conditions.* D1: evenness and lattice symmetries; three normalization conditions (135), the third vanishing by reflection (168). O(N): invariance under $O(N)$ broken to the stabilizer of $h$ by $\nu\neq0$; five conditions including the transverse second moment and the Ward identity relating it to the coefficient of $\|\partial\psi\|^2$.
5. *Running couplings.* D1: $\lambda$ scales canonically and is not renormalized, $a_k$ follows the free flow exactly, no field renormalization, $\mu_k,\varepsilon_k$ solved backward as a tuned boundary-value problem (non-perturbative renormalization). O(N): $\beta_k,a_k,\lambda_k,\nu_k$ get genuine corrections $b,c,d,e$ (P4 (1.9)), solved forward by contraction at each step; the series proves convergence of $\gamma_k,\delta_k$ (P4 (5.33)); there is no tuning of bare parameters.
6. *Large fields.* Absent from D1 (small fields only, with characteristic functions (172)); O(N) needs P5–P7. Roland identified large fields as essential (see `ROLAND_ANSWERS.md`), so D1 alone cannot be the blueprint.
7. *Source terms.* D1 has none; the O(N) final theorem needs $\mathcal F_k(g)$ and correlation functions (P9).

**Which D1 statements could become interfaces (if reused).**
- Free-flow identity (Lemma 2/Lemma 5): interface of the Gaussian RG: $\rho_k=Z_ke^{-S_k}$.
- Cube-Green's function decay bound (80) with $\gamma_0$, parametrized by the potential: interface used by (a) the random-walk expansion, (b) bounds on $C_k^{1/2}$.
- Abstract localization framework: a type of "polymer functionals" $E:\mathcal D\times\Omega\to\mathbb C$ with norm $\|E\|_{k,\kappa}$ and operations $\mathcal B$ (reblocking, Lemma 10), scaling (Lemma 9) and normalization (Lemma 11), with the statement of Lemma 10 as the interface. Needs generalization from scalar fields on $\mathbb R$ to $\mathbb R^N$-valued fields and two analyticity tiers.
- Cluster expansion Theorem 27: interface for the polymer expansion of a product measure; a modern statement (Kotecký–Preiss or the Fernández–Procacci criterion) could replace it.

**Reusable arguments.** The partition-of-unity parametrix and path-sum bound (Lemma 6); Combes–Thomas (Lemma 30); Lemma 20 (tree length of enlarged polymer) and Lemma 25 (polymer counting); decoupling by Mayer's identity with Cauchy bounds in $s$ (§4.5); the Taylor-with-Hölder-remainder argument of Lemma 11; the contraction set-up of Lemma 23 (as a template).

**Gauge/UV-specific or irrelevant.** The scaling of fields by $L^{-1/2}$ and the scaling dimensions $(1,2,3)$ of $(\lambda,\mu,\varepsilon)$ are specific to $\phi^4_3$; the choice of counterterms by terminal conditions (260); the specific exponents $\frac14-10\epsilon$ etc.; the stability bound itself.

**Suggestions on the Green's function estimates (suggestions, not claims).** Roland encouraged other proofs. Considering D1's text:
- The *local* decay is already a standard Combes–Thomas argument (Lemma 30, with $e_q=e^{q\cdot x}$, $|q|\le\delta_0$, and the lower bound (357)); this part could be formalized as written for any operator of the form $-\Delta+W$ with $W\ge0$ a multiplication operator plus $a\,Q^*Q$-type terms, with the explicit constant $\delta_0=\min\{\frac12c_1^{-1}c_0,1\}$.
- The *global* operator bound $|G_kf|,|\partial G_kf|\le C\|f\|_\infty$ (Cor 7) could alternatively be approached by a Neumann series on a weighted $\ell^\infty$ space of kernels $\|k\|_\gamma=\sup_x\sum_ye^{\gamma d(x,y)}|k(x,y)|$ (a Banach algebra), where $K=\sum_zK_zG_k(\tilde\square_z)h_z$ has small norm $O(M^{-1})$; this is exactly what (95)–(99) do, written without paths. Cleaner for Lean: one inequality $\|K\|_\gamma\le CM^{-1}$ and a geometric series replace the combinatorics of random walks.
- The uniform pointwise bounds could also come from discrete elliptic regularity for $\partial G$ and $\delta_\alpha\partial G$ (Schauder/Hölder estimates for $-\Delta$ with potential on lattices) and the $L^2\to L^\infty$ conversion by local Moser/Nash type bounds; D1's route (sum over scales (373) with the explicitly smooth kernel of $\mathcal H_k$ [Lemma 31], then Lemma 33) is more specific to the Gaussian RG and relies on the cited [4].
- For the O(N) problem the extra difficulty not treated by D1 is the multiplier $\alpha(x)$ and Dirichlet/generating-set structure; the above commutator remark (9.3) suggests the argument is stable under bounded perturbations of the potential, but this needs checking against the specific bounds P2 requires (scale-weighted sup and Hölder norms).

**Recommended usage.** (1) Read D1 §§2, 3.3–3.5 and App. B and C alongside P3, P4, P6 §4 when writing the Lean statements for the Gaussian skeleton and polymer framework, using D1's explicit proofs as the reference for those lemmas. (2) Treat D1 Lemmas 29–33, App. D as a proof sketch to be completed, not as an authority. (3) For the nonlinear variational problems, the Ward-identity renormalization and the RG equations, rely on P1, P2, P4. (4) Obtain and review D2 for the large-field decomposition and D3 for convergence before deciding whether any of the D-series large-field machinery can be transplanted to P5–P7.
