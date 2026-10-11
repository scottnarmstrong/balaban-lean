# P0: Survey, low temperature expansion and "spin wave picture"

Page convention: printed page numbers 201-218 (PDF page p = printed page - 200). Printed page 201 is the title page.

## 0. Identification

T. Balaban, "A Low Temperature Expansion and 'Spin Wave Picture' for Classical N-Vector Models", pp. 201-218 (18 pages), Rutgers University. Key P0. 18 PDF pages.

Venue: the page images carry no book title, running head or copyright line; the running heads are only author and chapter title. The ISBN in the file name (3-540-59190-7) is a Springer ISBN, and the chapter number "_30" and the page range 201-218 fit a proceedings volume. I could not confirm the volume from the images. The PDF metadata title is the chapter title only. UNCERTAIN: "Lecture Notes in Physics 446, Constructive Physics" is the guess in SOURCES.md; it is consistent with the page range but not verified here.

Summary. This is an expository overview with no proofs. It announces:
- Theorem 1 (the spin wave picture: a unique pure phase for $\nu>0$, one-point function near $h$, and exponentially decaying truncated correlations of mass $\sim\sqrt\nu$, with a $\nu\to0^+$ limit having power-law decay);
- Theorem 2 (the variational problem);
- Theorem 3 (bounds on effective actions satisfying renormalization conditions);
- Theorem 4 (the seven inductive hypotheses H.1-H.7 hold for the small-field densities);
- Theorem 5 (one-step stability of a class $\mathcal R_k$, with the recursion for the running constants);
- Theorem 6 (large-field version, stated only as "an idea of a theorem").

It describes the block-spin RG with averaging operator $Q$, Gaussian kernel $t$, scaling $S$, restrictions $\mathcal X$, minimizers $\phi_k$, localization expansions, and renormalization conditions. It cites [1] (= P1; "preprint, to appear in Commun. Math. Phys.") for proofs of Theorems 2-5 and [2] (Balaban-O'Carroll preprint 1994 = P8/P9) for Theorem 1. It sets the problem and the inductive scheme for the whole series.

## 1. Setting and notation

Model (p. 201-202). Spins $\phi(x)\in\mathbb R^N$, $x\in\mathbb Z^d$, $N\ge2$, $d\ge3$. Action (1):
$$A(\phi)=\tfrac12\sum_{\langle x,x'\rangle}|\phi(x')-\phi(x)|^2+\sum_x\Big(\tfrac\lambda8|\phi(x)|^4-\tfrac\mu2|\phi(x)|^2-h\cdot\phi(x)\Big),\quad\lambda>0,\ \mu>0,\ h\in\mathbb R^N.$$
Effective potential (2): $V(\phi)=\frac\lambda8|\phi|^4-\frac\mu2|\phi|^2-h\cdot\phi=\frac\lambda8(|\phi|^2-\frac{2\mu}\lambda)^2-\nu h_o\cdot\phi-\frac{\mu^2}{2\lambda}$, with $h=\nu h_o$, $\nu\ge0$, $|h_o|=1$. For $\nu=0$ the minima form the sphere $|\phi|^2=2\mu/\lambda$. For $\nu>0$ there is a unique minimum, proportional to $h_o$. After rescaling $\phi$ so that this minimum equals $h_o$ (p. 201-202), eq. (3):
$$V(\phi)=\tfrac\lambda8\big(|\phi|^2-1+\tfrac{2\nu}\lambda\big)^2-\nu h_o\cdot\phi-\tfrac\lambda8\big(1-\tfrac{2\nu}\lambda\big)^2=\tfrac\lambda8(|\phi|^2-1)^2+\tfrac\nu2|\phi-h_o|^2-\tfrac\lambda8\big(1+\tfrac{4\nu}\lambda\big).$$
UNCERTAIN: the exact constant term printed in the last expression of (3) is hard to read; it is irrelevant to the statements. (The same rescaling is meant to give (5).)

Finite volume (p. 202). Torus $T=\{x\in\mathbb Z^d:-L_\mu\le x_\mu<L_\mu\}$, periodic. Measure (4): $d\mu(\phi)=\rho(\phi)d\phi$, $\rho=\exp[-\beta A(\phi)-E]$, $\beta=1/kT$ (inverse temperature), $E=\log Z$. Action in the form (5):
$$A(\phi)=\tfrac12\|\partial\phi\|^2+\tfrac\lambda8\||\phi|^2-1\|^2+\tfrac\nu2\|\phi-h\|^2,$$
with $L^2(T)$ norms and $h\in S^{N-1}$ after rescaling ($\nu$ is the field strength). Parameter range: $\beta$ large, $\lambda\ge1$, $\nu>0$, $h$ in the unit sphere; the method is uniform in $\lambda\in[1,+\infty]$, and $\lambda=+\infty$ is the limit giving the classical Heisenberg (hard-spin) measure $\exp[-\beta(\frac12\|\partial\phi\|^2+\frac\nu2\|\phi-h\|^2)-E_\infty]\prod_x\delta(|\phi(x)|^2-1)$. Generating functional: add $\langle g,\phi\rangle$, $g:T\to\mathbb C^N$, to the exponent.

Symmetries (p. 202-203). $A(R\phi;Rh,\lambda,\nu)=A(\phi;h,\lambda,\nu)$ for $R\in O(N)$ (eq. before 6); $A(r\phi;h,\lambda,\nu)=A(\phi;h,\lambda,\nu)$ for lattice Euclidean transformations $r$ (6), $(r\phi)(x)=\phi(rx)$. The $\nu$-term breaks $O(N)$ down to the stabilizer of $h$.

RG transformation (p. 204, eq. 10-11). For a density $\rho(\phi;\beta)$:
$$(T\rho)(\psi)=\int d\phi\,t(\psi,\phi;\beta,a)\rho(\phi;\beta),\quad t=\prod_{y\in T_L^{(1)}}t(y;\psi,\phi;\beta,a),$$
$$t(y;\cdot)=\exp\Big[-\tfrac12\beta aL^{d-2}|\psi(y)-(Q\phi)(y)|^2+\tfrac N2\log\tfrac{\beta aL^{d-2}}{2\pi}\Big],\qquad (Q\phi)(y)=\sum_{x\in B(y)}L^{-d}\phi(x).$$
$L$ is a positive integer, $B(y)$ the $L$-block centred at $y\in T_L^{(1)}$ (new lattice of block centres), $a\approx1$ (e.g. $\frac12<a<\frac32$). Normalization (11): $\int d\psi\,(T\rho)(\psi)=\int d\phi\,\rho(\phi)$. Only linear averaging with Gaussian kernels is used.

Scaling (p. 205-206). Canonical scalings (12)-(13): with $T_\epsilon=\{\epsilon x:x\in T\}$, $\beta^\epsilon=\beta\epsilon^{2-d}$, $\lambda^\epsilon=\lambda\epsilon^{-2}$, $\nu^\epsilon=\nu\epsilon^{-2}$. The spin field is not rescaled ("trivial factor 1"), to keep the minimum at $|\phi|=1$ / $\phi=h$. After $n$ steps $\nu_n\approx\nu L^{2n}$; the procedure stops when $\nu L^{2n}\approx1$, so for $\nu\to0^+$ the number of steps $\to\infty$ (p. 206). $S$ = one-step scaling by $L^{-1}$; $ST$ = one RG step. Eq. (14): $\rho_k=S^{(k-1)}T^{(k-1)}\rho_{k-1}=\prod_j S^{(k-j)}T^{(k-j)}\rho_o=(ST)_k\rho_o$; $\rho_k$ lives on the unit lattice $T_1^{(k)}$ (block centres of $L^k$-blocks of $T_\eta$, $\eta=L^{-k}$) and depends on running parameters $\beta_k,\lambda_k,\nu_k,a_k$.

First fluctuation integral (15), p. 206: $(T^{(0)}\rho_o)(\psi)=\int d\phi\exp[-\beta_o\{\frac12aL^{-2}\|\psi-Q\phi\|_L^2+\frac12\|\partial\phi\|^2+\frac{\lambda_o}8\||\phi|^2-1\|^2+\frac{\nu_o}2\|\phi-h\|^2\}+\langle g,\phi\rangle-E_o']$. Its exponent is $A_1(\psi,\phi;h,aL^{-2},\lambda_o,\nu_o)$.

Large-field restrictions (p. 207, eq. 16): on blocks $y$, bonds $b$, points $x$:
$|\psi(y)-(Q\phi)(y)|<\beta_o^{-1/2}p(\beta_o)$, $|(\partial\phi)(b)|<\beta_o^{-1/2}p(\beta_o)$, $||\phi(x)|^2-1|<\lambda_o^{-1/2}\beta_o^{-1/2}p(\beta_o)$, $|\phi(x)-h|<\nu_o^{-1/2}\beta_o^{-1/2}p(\beta_o)$, with $p(\beta_o)=(A_o+\log\beta_o)^{p_o}$, $A_o$ large, $p_o$ an even integer. Decomposition $1=\sum_P\mathcal X_P\mathcal X^c_{P^c}$ over subsets $P$ of blocks/bonds/points. The part on $P^c$ (large field set $X$) is bounded by $\exp[-\frac1{8}\cdot]$-type factor $\exp(-\frac12p^2(\beta_o)|X|)$ (UNCERTAIN: constant prefactor in the exponent, p. 207, read as $\frac12 p^2$; the text also mentions a factor "$\frac18$" for the remaining estimate).

Small field spaces (p. 208-209). $A_k(\psi,\phi;h,a,\lambda,\nu)=\frac a2\|\psi-Q_k\phi\|_1^2+\frac12\|\partial^\eta\phi\|^2+\frac\lambda8\||\phi|^2-1\|^2+\frac\nu2\|\phi-h\|^2$ (18), norms on $T_\eta$ except the first on the unit lattice; variational problem (19) $\inf_\phi A_k$ with $\frac12<a<\frac32$, $\lambda\ge1$, $0<\nu\le1$. Small-field set (20):
$$\Phi_k(\epsilon;\lambda,\nu)=\{(\psi,\phi,h):|\psi-Q\phi|<\epsilon,\ |\partial^\eta\phi|<\epsilon,\ |\Delta^\eta\phi|<\epsilon,\ \tfrac\lambda2||\phi|^2-1|<\epsilon,\ |\phi-h|<\tfrac{\epsilon}{\sqrt\nu}\},\ h\in S^{N-1},$$
with complexification $\Phi_k^c$ (sums $(\psi+\psi',\phi+\phi',h+h')$ with the primed ones in $\mathbb C^N$ and the sum in the set). Reduced set (21): $\Psi_k(\delta;\nu)=\{(\psi,h):h\in S^{N-1},\ ||\psi|^2-1|<\delta,\ \nu(1-\hat\psi\cdot h)<\delta,\ \nu(1-\hat\psi\cdot h)<\delta^2,\ \hat\psi=\psi/|\psi|\}$ (UNCERTAIN: the printed condition on $\nu(1-\psi_o\cdot h)$ appears twice with $\delta$ and $\delta^2$; "$\psi_o$" is probably $\hat\psi$). $(\psi,\phi,h)\in\Phi_k(\epsilon;\lambda,\nu)\Rightarrow(\psi,h)\in\Psi_k(3\epsilon;\nu)$.

Glossary.

| symbol | meaning | where |
|---|---|---|
| $\phi,\psi$ | spin field on fine lattice / new block-spin field | p. 201, 204 |
| $\beta,\lambda,\mu,\nu,h,h_o$ | inverse temperature, quartic coupling, mass parameter, field strength, external field, direction | p. 201-202 |
| $T$, $T_\epsilon$, $T_L^{(1)}$, $T_1^{(k)}$ | torus; $\epsilon$-lattice; lattice of $L$-block centres; unit lattice of $L^k$-block centres | p. 202, 205, 204, 208 |
| $T$ (script) / $Q$ | RG transformation / block-averaging operator | p. 204 |
| $S$ | scaling by $L^{-1}$ | p. 206 |
| $a,a_k$ | Gaussian-kernel parameter, running version | p. 205, 210 |
| $\beta_k,\lambda_k,\nu_k$ | running constants | (14), (23), (H.6) |
| $A_k$ | $k$-th variational action | (18) |
| $\phi_k(\psi,h)$ | minimizer of (19) | p. 209 |
| $\psi_k^{(j)}$ | transformation of spin variables, $\phi_j(\psi_k^{(j)}(\psi))=\phi_k(\psi)$ | (22) |
| $\mathcal X_k$ | characteristic function of small-field domain | (H.1) |
| $\mathcal E_k,\mathcal E^{(j)}$ | effective action, its $j$-th scale pieces | (H.1), (H.2) |
| $\mathcal F_k,\mathcal M^{(j)}$ | generating functional of truncated correlations and its pieces | (H.1), (H.7) |
| $\mathcal D_j$, $d_j(X)$ | connected unions of $M$-cubes in $T_\xi$, linear size | (H.3) |
| $\Omega_k$ | large/small-field domain at step $k$ | (33) |
| $\Phi_k$, $\Psi_k$ | spaces (20), (21) | p. 208-209 |
| $\mathcal R_k$ | space of densities (27) | p. 213 |

## 2. Main results

All are stated without proof. Hypotheses on parameters are as in the model above.

**Theorem 1 (p. 203-204), the spin wave picture.** The model (4),(5) has exactly one thermodynamic limit if $\beta$ is large enough and $\nu>0$. Write $\langle\cdot\rangle_\nu$ for the expectation (depends also on $\beta,h,\lambda$). The one-point function satisfies (7):
$$\langle\phi(x)\rangle_\nu=m(\beta,\nu)h,\qquad |m(\beta,\nu)-1|<C\beta^{-1+\rho_1},$$
with $\rho_1>0$ arbitrarily small and $C$ independent of $\beta,\nu$. The truncated many-point functions decay exponentially at a rate proportional to $\sqrt\nu$; for the two-point function $\langle\phi(x)\phi(x')\rangle^T_\nu=\langle\phi(x)\phi(x')\rangle_\nu-\langle\phi(x)\rangle_\nu\langle\phi(x')\rangle_\nu$, (8):
$$\langle\phi(x)\phi(x')\rangle^T_\nu=G_{tr}(x-x';\beta,\nu)(I-h\otimes h)+G_{long}(x-x';\beta,\nu)\,h\otimes h,$$
$$|G_{tr}|,|G_{long}|\le C\frac1{|x-x'|^{d-2}}\exp(-c\sqrt\nu|x-x'|),$$
with an absolute positive $c$. The states have a limit as $\nu\to0^+$, $\langle\cdot\rangle=\lim\langle\cdot\rangle_\nu$, which is a pure state whose many-point truncated correlations have power-law decay. More precisely: the one-point function satisfies (7) with $\nu=0$; the two-point truncated function satisfies (8) with $\nu=0$, where (9)
$$G_{tr}(x-x';\beta,0)=\frac1{\beta\gamma_\infty(\beta)}m^2(\beta,0)\Delta^{-1}(x-x')+R(x-x';\beta),\quad|\gamma_\infty(\beta)-1|<C\beta^{-1},$$
$$|R(x-x';\beta)|,\ |G_{long}(x-x';\beta,0)|<C\frac1{|x-x'|^{d-2+\rho}}.$$
(UNCERTAIN: the sign convention of $\Delta^{-1}$ is as printed; $\rho>0$ is not quantified.) Status: "a consequence of the multi-scale expansion", proved in [2] (Balaban-O'Carroll, 1994 preprint, see section 4a). The author notes the decay (9) could be generalized to an expansion with remainders of arbitrarily large power-law rate; such a construction is "lengthy and cumbersome", not carried out.

The abstract's "continuum of phases parametrised by vectors of the unit sphere" is not a separate numbered theorem: it is the statement that for each $h_o\in S^{N-1}$ the limit $\nu\to0^+$ gives a pure state with $\langle\phi\rangle=m(\beta,0)h_o$, $m\approx1$. "Existence of Goldstone bosons" = free massless decay of truncated transverse two-point functions, $G_{tr}\sim\Delta^{-1}$, i.e. $|x|^{-(d-2)}$ (9). Note that (9) states only $G_{tr}$ asymptotics; $G_{long}$ is bounded by $|x|^{-(d-2+\rho)}$, i.e. faster decay than the transverse part. That the states for different $h_o$ are distinct and related by $O(N)$ is implicit and not stated as a theorem.

**Theorem 2 (p. 209), variational problem.** There exist positive $c_o,c_1,K_1$ with $K_1c_1\le c_o$ such that if $\epsilon\le c_1$ and $(\psi,h)\in\Psi_k(\epsilon;\nu)$, then (19) has a solution in $\Phi_k(K_1\epsilon;\lambda,\nu)$, unique in $\Phi_k(c_o;\lambda,\nu)$, and it is the only critical point of (18) in the latter space. The solution $\phi_k(\psi;h,a,\lambda,\nu)$ is analytic, extending to a complexification of $\Psi_k(c_1;\nu)$. Status: cited from [1] (this is the content of P2 ("The variational problems...") and of parts of P1; see 4a). Remark (p. 209): for $j,k,j\le k$ there is $\psi_k^{(j)}(\psi)$ on $T^{(k)}$ with values in spin configurations on $T^{(j)}$ with $\phi_j(\psi_k^{(j)}(\psi))=\phi_k(\psi)$ (22), where coefficients are linked by the scaling laws (13).

**Inductive hypotheses (H.1)-(H.7), p. 210-213.** The densities have the form below.

- (H.1) $\rho_k(\psi)=\mathcal X_k\exp[A_k+\mathcal F_k(\psi,h,g)]$, $A_k=-\beta_kA_k(\psi,\phi_k;h,a_k,\lambda_k,\nu_k)+\mathcal E_k(\psi,h)-E_k$, with $\phi_k$ the minimizer. Asymptotics (23): $\beta_k\approx\beta L^{k(d-2)}$, $a_k\approx a\frac{1-L^{-2}}{1-L^{-2k}}$, $\lambda_k\approx\lambda L^{2k}$, $\nu_k\approx\nu L^{2k}$. $\mathcal X_k$ is the characteristic function of $\{\psi:(\psi,\phi_k,h)\in\Phi_k(\beta_k^{-1/2}p(\beta_k);\lambda_k,\nu_k)\}$, which lies between two domains (21) with $\delta$ times constants; it is bounded by const.$\,\beta^{-1/2+\alpha}\eta^{\frac{d-2}2-\alpha}$, $\alpha$ arbitrarily small (p. 210).
- (H.2) $\mathcal E_k(\psi,h)=\sum_{j=1}^k\mathcal E^{(j)}(\psi_k^{(j)}(\psi,h),h)$, $\mathcal E^{(j)}(\psi_j,h)=\sum_{y\in T^{(j)}}\mathcal E^{(j)}(y;\psi_j,h)$. Each has an analytic extension to complex $(\psi,h)$ with $(\psi_j,\phi_j(\psi_j),h)\in\Phi_j^c(\epsilon_j;\lambda_j,\nu_j)$, $\epsilon_j=\epsilon_oL^{-j(\frac{d-2}2-\gamma)}$, $\epsilon_o$ small, $0<\gamma<\gamma_o=\min\{\frac{d-2}2,1\}$.
- (H.3) Localization expansion $\mathcal E^{(j)}(y;\psi_j,h)=\sum_{X\in\mathcal D_j;y\in X}\mathcal E^{(j)}(y,X;\psi_j,h)$, sums over connected unions of cubes of fixed size $M$ in $T_\xi$, $\xi=L^{-j}$, localized terms depending on $(\psi_j,h)|_X$, bounds $|\mathcal E^{(j)}(y,X;\psi_j,h)|<E_o\exp(-\kappa d_j(X))$, also on the analytic extension. $\kappa$ large so that $\sum_{X\in\mathcal D_j;y\in X}e^{-\kappa d_j(X)}\le K_o$ ($K_o$ depends only on $d$). Gives only the weak bound $|\mathcal E_k|<(L^d-1)^{-1}E_oK_o|T_1|$ (p. 211).
- (H.4) Symmetry: $\mathcal E^{(j)}(ry;r\psi_j,h)=\mathcal E^{(j)}(y;\psi_j,h)$ for lattice Euclidean $r$, and $\mathcal E^{(j)}(y;R\psi_j,Rh)=\mathcal E^{(j)}(y;\psi_j,h)$, $R\in O(N)$, also for localized terms. For constant $\psi_j$ this defines an effective potential $\mathcal V^{(j)}(\psi,h)=\mathcal E^{(j)}(y;\psi,h)$ (24).
- (H.5) Renormalization conditions (relevant and marginal terms), with $e_1=(1,0,\dots,0)$: $\mathcal V^{(j)}(e_1,e_1)=0$; $(\partial_h\mathcal V^{(j)})(e_1,e_1)\cdot e_1=0$; $(\partial_\psi\mathcal V^{(j)})(e_1,e_1)\cdot e_1=\sum_{y'}(\partial_{\psi(y')}\mathcal E^{(j)})(y;e_1,e_1)\cdot e_1=0$; and $\sum_{x\in\mathbb Z^d}\mathrm{tr}[\lim_{T^{(j)}\to\mathbb Z^d}(\partial^2\mathcal E^{(j)}/\partial\psi(x)\partial\psi_j(0))(e_1,e_1)\cdot(e_2\otimes e_2)]\,|x|^2=0$, for all $j\le k$. (UNCERTAIN: exact index placement in the last two conditions, p. 212, is partly illegible in details; the structure is: vanishing of value, first $h$- and $\psi$-derivatives, and a second-moment condition in the transverse direction.)
- (H.6) $\beta_k=\beta L^{k(d-2)}\gamma_k$, $a_k=a\frac{1-L^{-2}}{1-L^{-2k}}$, $\lambda_k=\lambda L^{2k}$, $\nu_k=\nu L^{2k}\delta_k$, with $\gamma_k,\delta_k$ arbitrarily close to 1 for $\beta$ large. Limits $\gamma_\infty,\delta_\infty$ exist but are said not to matter here.
- (H.7) $\mathcal F_k(\psi,h,g)=\langle g,\phi_k\rangle_1+\sum_{j=1}^k\beta_{j-1}^{-1/2}\mathcal F^{(j)}(\psi_k^{(j)}(\psi,h),h,g)$, $\mathcal F^{(j)}(\psi_j,h,g)=\langle g,\mathcal M^{(j)}(\cdot;\psi_j,h,g)\rangle_1$; $\mathcal M^{(j)}$ analytic in $(\psi,h)$ on the same domain as $\mathcal E^{(j)}$ and in $g$ on $\|g\|_{\ell^1}<1$ (UNCERTAIN: norm subscript), with symmetries as (H.4) and localization expansions as (H.3) with bounds $|\mathcal M^{(j)}(x,X;\psi_j,h,g)|<M_oL^{-j(\gamma-\alpha_1)}\exp(-\kappa d_j(X))$, $\alpha_1$ small. The sum over $j$ is then bounded by $4M_oK_o\beta^{-1/2}$.

**Theorem 3 (p. 212), bounds from renormalization conditions.** If $\mathcal E_k(\psi,h)$ satisfies (H.2)-(H.5) then there are positive $K_2,\alpha_2$ such that on the analyticity domain of (H.2):
$$|\mathcal E^{(j)}(\psi_k^{(j)}(\psi,h),h)|\le K_2(L^j\eta)^{d+\alpha_2}E_o|T_1^{(j)}|=K_2(L^j\eta)^{\alpha_2}E_o|T_1^{(k)}|\ (25),\qquad |\mathcal E_k(\psi,h)|\le\frac{1}{1-L^{-\alpha_2}}K_2E_o|T_1^{(k)}|\ (26)$$
(the middle equality in (25) is as printed; $(L^j\eta)=L^{j-k}$ so $(L^j\eta)^{d}|T_1^{(j)}|$ carries the volume factor. UNCERTAIN: exact printed form of the sum in (26), see page 212.) Mechanism: factor $(L^j\eta)^{d+\alpha_2}$ comes from renormalization conditions (relevant and marginal terms removed) and from the substitution $\psi_k^{(j)}$ which maps the analyticity domain into a smaller one with better regularity. Status: cited from [1] (proof "along the guidelines sketched above, given in [1]").

**Theorem 4 (p. 213), small-field densities satisfy (H.1)-(H.7).** Consider the model (4),(5) for $d\ge3$, $N\ge2$, $\beta\ge1$, $1\le\lambda\le+\infty$, $0<\nu\le1$ and define $\rho_k$ by applying the small-field renormalization transformations (17). For $\beta$ sufficiently large, $\eta\in(0,1)$, there exist constants $E_o,\kappa,\epsilon_o,M_o,\alpha_1$ and coefficients $\beta_k,a_k,\lambda_k,\nu_k$ such that $\rho_k$ satisfies (H.1)-(H.7) as long as $\nu_k\le1$. (UNCERTAIN: as printed "for $\beta$ sufficiently large, $\eta\in(0,1)$"; the role of $\eta$ here is unclear since $\eta=L^{-k}$ is determined by $k$.) Status: consequence of Theorem 5 (iteration) via [1]. Here (17) is $\rho_k=\mathcal X_kS^{(k-1)}T^{(k-1)}\mathcal X^{(k-1)}\cdots S^{(0)}T^{(0)}\mathcal X^{(0)}\rho_o$, with $\mathcal X^{(j)}$ restrictions of type (16) formulated more elaborately in [1].

**Theorem 5 (p. 214), one-step stability.** With
$$\mathcal R_k(E_o,\kappa,\epsilon_o,\gamma,M_o,\alpha_1,B_o)=\{\text{densities of form (H.1) with }\beta_k,a_k,\lambda_k,\nu_k\text{ as in (H.6), }\beta_k>B_o,\nu_k\le1,\ \mathcal E_k\text{ as (H.2)-(H.5)},\ \mathcal F_k\text{ as (H.7)}\}$$
(27), there exist $E_o,\kappa,\epsilon_o,M_o,\alpha_1,B_o$ independent of $k,\kappa$ (as printed; probably "independent of $k$"; $B_o$ sufficiently large; $\epsilon_o,\alpha_1$ sufficiently small) such that (28)
$$\mathcal X_{k+1}S^{(k)}T^{(k)}\mathcal X^{(k)}:\mathcal R_k(E_o,\kappa,\epsilon_o,\gamma,M_o,\alpha_1,B_o)\to\mathcal R_{k+1}(E_o,\kappa,\epsilon_o,\gamma,M_o,\alpha_1,B_o).$$
The new coefficients satisfy the RG equations (29):
$$\beta_{k+1}=\beta_kL^{d-2}-b_{k+1},\quad a_{k+1}=\frac{aa_k}{aL^{-2}+a_k},\quad\lambda_{k+1}=\lambda_kL^2,\quad \nu_{k+1}=\frac{\beta_kL^{d-2}}{\beta_{k+1}+c_{k+1}}\nu_kL^2=\frac{\beta_{k+1}+b_{k+1}}{\beta_{k+1}+c_{k+1}}\nu_kL^2,$$
where $b_{k+1},c_{k+1}$ are determined by $\beta_k,a_k,\lambda_k,\nu_k,\mathcal E_k$ and are small relative to $\beta_{k+1}$: $|\beta_{k+1}^{-1}b_{k+1}|,|\beta_{k+1}^{-1}c_{k+1}|<\alpha_3L^{-(k+1)2\gamma}$ with $\alpha_3$ arbitrarily small for $B_o$ large (p. 214). The transformation depends on $\beta_k$ through (H.1), hence is nonlinear. The statement is said to be a simplification: a more detailed version describes the dependence of the elements of $\rho_{k+1}$ on $\rho_k$. Status: cited from [1]. Proof sketch on p. 214-215 (see section 3).

**Theorem 6 (p. 217), large fields.** "The renormalization transformation $S^{(k)}T^{(k)}$ preserves the form and the bounds of the densities (33), with the same equations for the coefficients $\beta_{k+1},a_{k+1},\lambda_{k+1},\nu_{k+1}$, and similar restrictions on the remaining constants." The author says this is "actually only an idea of a theorem", the densities (33) not being described in sufficient detail. Status: sketched only, no reference given for the proof (presumably later papers, see section 7).

## 3. Proof architecture (what the survey says about the strategy)

1. p. 203: author's aim is not to reprove known results (infrared bounds, chessboard estimates, etc. cited via [5,6,7,11,12,17]) but to construct a convergent low-temperature expansion for this class, an analogue of the Peierls expansion for Ising and of [15] for $N=1$ ("$\lambda\phi^4-\frac\mu2\phi^2$"), which would then be robust enough for disordered, stochastic or quantum models. A multi-scale expansion is needed because of massless modes. Tools: RG ideas of [3,4,13] (Balaban gauge/scalar papers, Gawedzki-Kupiainen).
2. p. 203-204: Theorem 1 follows from the expansion and is proved in [2].
3. p. 204-206: block-spin RG with linear averaging and Gaussian kernels, canonical scalings, iteration count fixed by $\nu L^{2n}\approx1$. Key observation (p. 205-206): if $\nu\approx1$, a straightforward cluster expansion gives a unique phase with exponential decay, uniformly in $\beta,\lambda$; so the RG runs from small $\nu$ up to $\nu_k\approx1$, with $\beta_k$ growing like $L^{k(d-2)}$, and one ends with one last step integrating a density with $\nu_k\approx1$ and $a=0$.
4. p. 206-207, large field problem: the fluctuation integral (15) cannot be handled by a saddle point on the whole configuration space (singular critical sets). One imposes restrictions (16) on block variables, $\sum_P\mathcal X_P\mathcal X_{P^c}^c=1$; on large-field sets the density is bounded by $\exp(-\frac12p^2(\beta_o)|X|)$, which dominates the combinatorics for the first steps. This is called the easiest part of the large field problem.
5. p. 207-216, small-field problem (the core): not a perturbation series ("in fact it is difficult even to make contact with a standard spin wave series for most of the renormalization steps"; contact appears after the last step). Mechanism: on the small-field domain the exponent has exactly one critical point, a minimum $\phi_k$ of $A_k$ (Theorem 2). Then change variables $\psi=\psi_{k+1}^{(k)}(\theta,h)+\beta_k^{-1/2}\psi'$ (32), where $\psi_{k+1}^{(k)}$ solves the variational problem (31) $\inf_\psi\{\frac12aL^{-2}\|\theta-Q\psi\|_L^2+A_k(\psi,\phi_k;\dots)\}$; expand in $\psi'$ to get a fluctuation integral: leading term quadratic form bounded above and below uniformly in $k$ with exponential decay, other terms carry powers of $\beta_k^{-1/2}$ and exponential decay, so the integral is represented by a convergent cluster expansion (details "technically quite involved", only in [1]). The result is then rescaled by $S^{(k)}$, and the new effective action is re-expressed: the main part $A_{k+1}$ is rearranged via (29) with unknown parameters $b_{k+1},c_{k+1}$, and the discarded terms go into $\mathcal E_{k+1}$. One shows $b_{k+1},c_{k+1}$ can be chosen so that (H.5) holds (this is the genuine implicit-function-type step). Effects of the restriction $\mathcal X^{(k)}$: $|\psi'|<p_1(\beta_k)=(A_1+\log\beta_k)^{p_1}$.
6. Why $\mathcal E_k$ stays bounded (p. 211-212): (H.3) gives only $|\mathcal E_k|\lesssim|T_1|$ (very bad, a constant times volume of the unit lattice, while one expects a constant times $|T_\eta|$ scale gain); (H.5) removes relevant/marginal terms so that $\mathcal E^{(j)}$ contributes $(L^j\eta)^{d+\alpha_2}$ (Theorem 3), making $\mathcal E_k$ summable in $j$.
7. p. 216: last step. When $\nu_k\approx1$ one integrates $\rho_k$ directly with $a=0$, $\psi=h+\beta_k^{-1/2}\psi'$, obtaining $\mathcal F_{k+1}(h,h,g)$, a generating functional of truncated correlations that satisfies (H.7); this yields most of Theorem 1 for the small-field correlation functions, and all of it with a more precise inductive description of $\mathcal F_k$ (from [2]).
8. p. 216-217, large fields in general: decompose $1=\sum_P\mathcal X_P\mathcal X^c_{P^c}$, add a layer of large cubes of proper size to the large-field set to form $\Omega_1^c$; small-field domain $\Omega_1$; integrate over $\Omega_1$ with boundary conditions, with variational problem $A_1^{B.C.}(\Omega_1;\psi,\phi)$. Result (33): $\rho_k(\psi)=\sum_{\Omega_k}\rho_k(\Omega_k^c;\psi,h,g)\mathcal X_k(\Omega_k)\exp[-\beta_kA_k^{B.C.}(\Omega_k;\psi,\phi_k;\dots)+\mathcal E_k(\Omega_k;\psi,h)-E_k(\Omega_k)+\mathcal F_k(\Omega_k;\psi,h,g)]$, with localization expansions (H.3),(H.7) restricted to $X\subset\Omega_k$. The large-field factors $\rho_k(\Omega_k^c)$ are not localized to $\Omega_k^c$ but have small boundary terms that "creep into" $\Omega_k$ and are bounded by $\exp[-K|\Omega_{k}^c|_\eta]$, $K$ large. Because with each step the exponential bounds on large-field factors may worsen (a part is used to control sums), the bounds depend on the size of connected components of $\Omega_k^c$; one "exponentiates" a sum over components into new terms in the exponent added to the effective action (p. 217). The author calls this the second difficult technical point and says it is "quite universal and discussed before for other problems" ([3,4,8,9,10,13] cited in the discussion on p. 207).

## 4. Ingredients and prerequisites

4a. Bundle papers.
- [1] "A low temperature expansion in classical N-vector models, preprint, to appear in Commun. Math. Phys." = P1 (CMP 167 (1995)) at least for Theorems 3-5 and (H.1)-(H.7), the restrictions $\mathcal X^{(j)}$, the definition of $d_j(X)$ and "$\psi_k^{(j)}$ as solutions of variational problems". Theorem 2 (the variational problem) is also the topic of P2 ("The variational problems for classical N-vector models", CMP 175), but the reference as printed is only [1]; I did not open P1 to see which parts are in P1 versus P2 (the survey predates P2). Localization expansions (H.3) correspond to P3.
- [2] "Balaban, T., O'Carroll, M. preprint 1994" = P9 (CMP 199 (1999), "Low temperature properties for correlation functions...") by author list and subject; P8 (Ann. Phys. 1997) is a related short note. Not verified; the CMP 199 title and Theorem 1 match.
- Mapping to P1-P9 of the author's announced division: (i) one-step RG, small field: P1 (and P4: "II. Renormalization group equations"), (ii) variational problems: P2, (iii) localization expansions: P3 (and P6), (iv) complete inductive description incl. fluctuation integrals: P5, (v) large field operation: P7 (matches the sketch on p. 216-217; the survey says only that large fields are handled in "previous papers"), (vi) correlation functions: P8, P9. This mapping is from SOURCES.md titles only.

4b. External.
- [3] Balaban, T., Imbrie, J., Jaffe, A. Commun. Math. Phys. (a) 97 (1985) 299; (b) 114 (1988) 257. [4] Balaban, T. Commun. Math. Phys. (a) 85 (1982) 603; (b) 86 (1982) 555; (c) 89 (1983) 571; (d) 109 (1987) 249; (e) 116 (1988) 1. [8] Brydges, D., Yau, H. CMP 129 (1990) 351. [9] Brydges, Dimock, Hurd, "Weak Perturbations of Gaussian Measures", preprint (set of lectures). [10] Feldman, Magnen, Rivasseau, Seneor CMP 109 (1987) 437. [13] Gawedzki, K., Kupiainen, A. CMP 99 (1985) 197. These are the RG methods (scalar/gauge-field block-spin, large-field analysis, localization). [15] Glimm, Jaffe, Spencer, Ann. Phys. 101 (1976) 610, 631 (low temperature Peierls expansion for $\lambda\phi^4-\frac\mu2\phi^2$, $N=1$).
- [5] Bleher, Major CMP 125 (1989) 43; Ann. IHP 49 (1988) 1. [6] Bricmont, Fontaine, Lebowitz, Spencer, CMP 78 (1980) 281, 363. [7] Bricmont, Fontaine, Lebowitz, Lieb, Spencer, CMP 78 (1981) 595. [11] Frohlich, Simon, Spencer CMP 50 (1976) 79. [12] Frohlich, Pfister CMP 89 (1983) 30. [17] Schor, O'Carroll CMP 138 (1991) 487; J. Stat. Phys. 64 (1991) 163. These are mentioned as earlier rigorous results (infrared bounds, chessboard, existence of magnetization), not used. [14,16,18] Glimm-Jaffe, Negele-Orland, Zinn-Justin are in the bibliography but not cited in the text I read (UNCERTAIN: could be in the first page's omitted citations).
- Essential: the methods of [3,4,13] (the survey says the description of the block-spin approach "has been described already several times").

4c. Standard mathematics. Gaussian integration with kernel $t$; saddle-point/variational analysis of $A_k$ on a small-field set; implicit function theorem / contraction for the minimizer and for $b_{k+1},c_{k+1}$; analytic functions of many variables with Cauchy estimates (complex domains $\Phi^c_k$); cluster/polymer expansion with exponentially localized terms; discrete elliptic estimates for the Laplacian on $T_\eta$; $O(N)$ and sphere $S^{N-1}$ geometry.

## 5. Dependency ledger

| result | uses (internal) | uses (bundle) | uses (external) | status |
|---|---|---|---|---|
| Thm 1 (spin wave picture) | (H.1)-(H.7), last step p. 216 | [2] (P9; also P8) | block-spin RG [3,4,13] | cited, proof in [2]; correlation part at (H.7) |
| Thm 2 (variational problem) | (18)-(21) | [1] (cf. P2) | none stated | cited |
| Thm 3 (bound on $\mathcal E_k$) | (H.2)-(H.5) | [1] | none | cited; mechanism sketched p. 212 |
| Thm 4 (inductive hypotheses hold) | Thm 5 | [1] | RG methods | cited; "consequence" |
| Thm 5 (one-step stability and (29)) | (H.1)-(H.7), Thm 2, 3 | [1] | cluster expansion | sketched p. 214-215, proof in [1] |
| Thm 6 (large field step) | Thm 5 idea, (33) | none stated | [3,4,8-10,13] | idea only |
| Correlation expansion for generalized decay (remark after (9)) | (H.7) | none | none | declared possible, not carried out |

## 6. Constants and parameters

Order of choice, as far as the survey indicates:
- Model parameters: $d\ge3$, $N\ge2$, $\lambda\in[1,+\infty]$, $0<\nu\le1$ (Theorem 4), $\frac12<a<\frac32$. Integer $L$ is fixed (not quantified; chosen before $\beta$ is large, UNCERTAIN: the survey does not say how $L$ is chosen).
- $\gamma\in(0,\gamma_o)$, $\gamma_o=\min\{\frac{d-2}2,1\}$ (p. 210); for $d=3$, $\gamma$ may be arbitrarily close to $\frac{d-2}2=\frac12$.
- $E_o,\kappa$ (large, with $\sum_X e^{-\kappa d_j(X)}\le K_o(d)$), $\epsilon_o$ (small), $M_o$, $\alpha_1$ (small), $B_o$ (large), all independent of $k$ and of $\beta$ (Theorem 5); $\beta\ge B_o$ ("sufficiently large", i.e. $\beta_k>B_o$).
- $\alpha_2>0$ in Theorem 3 (from $d+\alpha_2$ scaling gain); $K_2$.
- Large-field parameters: $A_o$ large positive, $p_o$ even integer, $p(\beta_o)=(A_o+\log\beta_o)^{p_o}$ (16); $A_1,p_1$ for $\mathcal X^{(k)}$, $|\psi'|<(A_1+\log\beta_k)^{p_1}$ (p. 215). Constraints "some restrictions with respect to $A_o,p_o$": not specified.
- $\alpha$ arbitrarily small in $\beta^{-1/2+\alpha}\eta^{(d-2)/2-\alpha}$; $\rho_1$ arbitrarily small in (7), $\rho>0$ in (9).
- Running constants: $\beta_k,a_k,\lambda_k,\nu_k$ with (H.6), $\gamma_k,\delta_k$ within $\alpha_2$ of 1 (p. 214; the printed text writes $|\gamma_k-1|<\alpha_2,|\delta_k-1|<\alpha_2$ as an optional extra restriction), with $b_{k+1},c_{k+1}$ bounded by $\alpha_3L^{-(k+1)2\gamma}\beta_{k+1}$.
- Fixed parameter name clash: $\alpha_2$ is used both in Theorem 3 ($d+\alpha_2$ exponent) and in the optional restriction $|\gamma_k-1|<\alpha_2$ (p. 214); these are probably different constants (UNCERTAIN).

## 7. Weak spots and open points

- No proofs. Every theorem except Theorem 1 is attributed to [1]; Theorem 1 to [2]; Theorem 6 is explicitly only an idea.
- Typographical glitches in the text: Theorem 5 says constants are "independent of $k,\kappa$" (likely "$k$"); Theorem 4 mentions $\eta\in(0,1)$ ambiguously; (21) has a doubled condition and a symbol "$\psi_o$" probably meaning $\hat\psi$; (H.5) index details uncertain; (3)'s constant term hard to read.
- Theorem 1 as stated: the many-point exponential decay for $\nu>0$ is stated with rate $\sqrt\nu$ but for general $n$-point functions no explicit form is given beyond "for example the two-point function". The $\nu\to0^+$ claims (pure state, power-law decay of many-point truncated functions) are stated only for the two-point case in formulas. Uniformity in $\lambda\in[1,\infty]$ and the passage to $\lambda=\infty$ are asserted without discussion. The decay (9) for $G_{tr}$: the $\Delta^{-1}$ leading term with coefficient $m^2/(\beta\gamma_\infty)$ and remainder $|x|^{-(d-2+\rho)}$ ($\rho$ unquantified).
- The thermodynamic limit statement "exactly one thermodynamic limit" requires $\nu>0$ and large $\beta$; how uniqueness is deduced (periodic torus, limit of states) is not explained.
- The survey's claim that distinct directions $h_o$ yield a "continuum of phases" is not a numbered theorem; it is read off from the choice of $h_o$.
- To check in P1-P9 (announced here, no clear counterpart from titles/abstracts in SOURCES.md):
  1. Theorem 3 (bound on $\mathcal E_k$ from (H.5)): possibly inside P1 or P4/P5; "to check".
  2. Full large-field renormalization (Theorem 6, (33)): presumably P7 (and possibly P5), "to check" that it includes the exponentiation of large-field component sums and the boundary terms of $\rho_k(\Omega_k^c)$.
  3. The generalization of (9) to expansions of arbitrary power-law order: explicitly declared not carried out.
  4. The last step ($\nu_k\approx1$, $a=0$) giving $\mathcal F_{k+1}(h,h,g)$ and Theorem 1: P8/P9 ("to check" that the $\nu\to0^+$ limit and the Goldstone statement (9) with leading coefficient $m^2/(\beta\gamma_\infty)\Delta^{-1}$ appear with $\gamma_\infty$ as here).
  5. Statement for $\lambda=+\infty$ and for $d\ge3$ general, $N\ge2$ (the survey says uniform in $\lambda\in[1,+\infty]$): check that later papers keep $\lambda=\infty$ included.
  6. Existence of limits $\gamma_\infty,\delta_\infty$ (p. 213): said to follow from the RG equations; check where proved (P4/P5).
  7. Infinite-volume / thermodynamic limit procedure at $\nu>0$ via a "fairly straightforward cluster expansion" at $\nu\approx1$: "to check" that it is carried out in P5-P9 rather than only asserted.
- Restriction on $\nu$: Theorem 4 states $\nu\le1$ and the iteration stops when $\nu_k\approx1$; the final step is not formalized as a theorem here.

## 8. Preliminary formalization notes

- Nothing here is a self-contained proof; P0 is a guide to statement forms. The Lean-relevant content is the exact formulation of the setting (finite-volume torus measure (4)-(5), generating functional with $g$, symmetries (6)), the target Theorem 1, and the shape of the inductive scheme (H.1)-(H.7), (29).
- Early/formalizable: definitions of the action, the measure on the torus (a finite product of $\mathbb R^N$ or, for $\lambda=\infty$, spheres $(S^{N-1})^T$), the transformation $T$ (Gaussian kernel, normalization identity (11)), the scaling laws (13), the one-step recursion (29) as pure real sequences, the symmetries.
- Infrastructure needed (guess): Gaussian integrals on $\mathbb R^{N|T|}$ and Gaussian-kernel convolution identities; multivariable analyticity (complex Banach-valued, Cauchy bounds); variational problem and implicit-function theorem on finite-dimensional spaces; localization/polymer expansion bookkeeping; $O(N)$-equivariance. Mathlib has Gaussian measures in some form and the inverse function theorem, but uniform-in-volume discrete elliptic estimates and polymer expansions are likely absent (guess).
- Hardest: Theorem 5 and Theorem 6 (cluster expansion of the fluctuation integral with large-field restrictions, coupled with the construction of $b_{k+1},c_{k+1}$ to enforce (H.5)); the correlation-function part of Theorem 1 via (H.7).
