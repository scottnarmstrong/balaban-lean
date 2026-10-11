# P2: The variational problems for classical N-vector models

Page references: journal pages 607-642 as printed (PDF page = journal page - 606). All formulas were read from page images.

## 0. Identification

T. Balaban, "The variational problems for classical N-vector models", Commun. Math. Phys. 175 (1996) 607-642. Bundle key P2. 36 pages. Received 8 Nov 1994, revised 15 Mar 1995. The reference list has only two entries: [1] = P1 (CMP 167, 103-154) and [2] = Balaban's gauge-theory propagator papers (CMP 89, 571 (1983); CMP 96, 223 (1984)).

Summary. P1 introduces the renormalization group flow and the "background" variational problems (its (2.1), (2.2), (2.6), (2.7)). This paper proves that those problems are well posed: for boundary data $(\psi+\psi',h+h')$ in a small neighbourhood of the "unit sphere" configurations, the Euler-Lagrange system has a unique small-$\alpha$ solution $(\phi,\alpha)$. The solution is analytic in the data, and it has pointwise bounds that improve with the scale $L^j\eta$ (Prop. 1.1, p. 611). The method is the following.
- Solve the problem for constant configurations by algebra (Sect. 2).
- Patch the constant solutions with a partition of unity to get an approximate solution $(\phi_0,\alpha_0)$ with small residual $f_0$ (Sect. 3).
- Correct it with an inverse function theorem, with the linearized operator inverted by a Neumann series using the propagator bounds of [2(b)] (Sect. 3).
- Sect. 4 treats the "two generating sets" problem. It constructs the function $\psi(\mathbb B_j,\mathbb B_k')$, which is a block-spin field obtained by minimizing out the intermediate scales. It shows this function satisfies the properties needed in the inductive hypotheses of P1.

Role in the series. From P1 it takes the definitions of the actions, the domains $\tilde\Psi$, $\mathcal D_j$, $T_\eta$, the one-step transformation (1.11 of P1), and the inductive hypotheses (H.8), (H.5). It supplies P1's Corollary 1.1 (existence, uniqueness and analyticity of the solution of problem (2.2) of P1), which P1 "has used extensively" (p. 612). It also supplies the functions $\psi_k^{(j)}$ and the identity (4.39) (the composition rule) used in later localization papers (P3 and onward).

## 1. Setting and notation

Lattice and scales.
- $T_\eta$ is the unit torus with lattice spacing $\eta$ (also treated as a continuous torus $T$ in (3.1)-(3.2)).
- $\mathcal T^{(j)}_{L^j\eta}$ is the lattice of centres of $L^j\eta$-cubes.
- $\mathcal D_j$ is the class of localization domains of P1, Sects. 1-2.
- $\xi = L^{-j}$ rescales $T_\eta$ to the $\xi$-lattice (2.2).
- $L\ge3$ is an integer. $M$ is the block size for "big blocks" and is not necessarily $L$ ("one of adjustable parameters", p. 607). Also $L^m=M$ (p. 632).

Domains (pp. 607-608).
- A decreasing sequence $\Omega_1\supset\dots\supset\Omega_k$ with $\Omega_j\subset T_\eta$.
- The connected components of $\Omega_j^c$ belong to $\mathcal D_j$, and $(L^j\eta)^{-1}\mathrm{dist}(\Omega_j^c,\Omega_{j+1})>RM$ (1.1), with $R$ a positive integer "fixed later".
- Some $\Omega_j$ may equal $T_\eta$.
- $\Lambda_j=\Omega_j^{(j)}\setminus\Omega_{j+1}^{(j)}$ for $j<k$, $\Lambda_k=\Omega_k^{(k)}$, and $\Lambda_0=\Omega_1^c\cap\Omega_1^\sim$ (one layer of large blocks around $\Omega_1$; "$\sim$" adds one layer of large $L^{-1}$-scale cubes touching $\Omega_1$). Here $\Omega_j^{(i)}=\Omega_j\cap\mathcal T^{(i)}_{L^i\eta}$ are the centres of $i$-blocks.
- $\mathbb B_k=\bigcup_{j=1}^k\Lambda_j$ is the "generating set" (1.3). It is identified with the sequence $\{\Omega_j\}$.

Fields.
- $\phi:T_\eta\to\mathbb R^N$ (the background field, varied only on $\Omega_1$).
- $\psi$ is defined on $\mathbb B_k$ ($\psi=\psi_j$ on $\Lambda_j$).
- $\alpha:T_\eta\to\mathbb R$ is the auxiliary (Lagrange-multiplier-like) field for the spherical constraint.
- $h\in\mathbb R^N$, $|h|=1$ is the constant magnetic-field direction.
- Complex versions: $\psi+\psi'$, $h+h'$ with values in $\mathbb C^N$.

Averaging operator (1.4).
$$(Q(\mathbb B_k)\phi)(y)=(Q_j\phi)(y)=\sum_{x\in B_j(y)}L^{-jd}\phi(x),\qquad y\in\Lambda_j,$$
where $B_j(y)$ is the $j$-block with centre $y$. The multiplier is $a(\mathbb B_k)=a_j(L^j\eta)^{-2}$ on $\Lambda_j$, with
$$a_j=\frac{1-L^{-2k}}{1-L^{-2j}}a_k .$$

Action (1.4), with $\|\cdot\|$ norms at the indicated scale.
$$A(\mathbb B_k;\psi,\phi;h,a_k,\lambda_k,\nu_k)=\tfrac12\langle\psi-Q\phi,\,a(\psi-Q\phi)\rangle+\tfrac12\|\partial^\eta\phi\|^2+\tfrac{\lambda_k}{8}\||\phi|^2-1\|^2+\tfrac{\nu_k}{2}\|\phi-h\|^2 .$$
- The first term is $\sum_{j=1}^k a_j(L^j\eta)^{-2}\sum_{y\in\Lambda_j}(L^j\eta)^d|\psi_j(y)-(Q_j\phi)(y)|^2$ (1.5).
- The last three terms use the $\eta$-scale norms.
- $a_k,\lambda_k,\nu_k$ are arbitrary constants subject to P1 Thm 2.2: $\tfrac12<a<\tfrac32$, $\eta^2\lambda\ge1$ and $0<\nu\le1$. Here $\lambda=\lambda_k$ and so on. No change of $\beta$ is discussed.

Linearization by auxiliary field $\alpha$ (1.7)-(1.9).
$$J=\tfrac12\langle\psi-Q\phi,a(\psi-Q\phi)\rangle+\tfrac12\|\partial^\eta\phi\|^2+\tfrac12\langle\alpha,|\phi|^2-1\rangle-\tfrac1{2\lambda}\|\alpha\|^2+\tfrac\nu2\|\phi-h\|^2,$$
and $A=\sup_\alpha J$. The problem is $\inf_{\phi|\Omega_1}\sup_\alpha J$.

Euler-Lagrange system (1.10), where $\chi_{\partial\Omega_1}\Delta^\eta$ is the boundary coupling and $\phi=\psi_0$ on $\Omega_1^c$:
$$\big(-\Delta^{D,\eta}_{\Omega_1}+Q^*aQ+\alpha+\nu\big)\phi=Q^*a\psi+\nu h+\chi_{\partial\Omega_1}\Delta^\eta\chi_{\Omega_1^c}\phi,\qquad \tfrac12(|\phi|^2-1)-\tfrac1\lambda\alpha=0 .$$
Here $\Delta^{D,\eta}_\Omega=\chi_\Omega\Delta^\eta\chi_\Omega$ is the Dirichlet Laplacian, and $\partial\Omega=\{x\in\Omega:\exists$ bond $\langle x,x'\rangle$ with $x'\in\Omega^c\}$.

Configuration spaces (1.11), (1.12), p. 610.
- $\tilde\Psi(\mathbb B_k;\delta)$ is the set of real $(\psi,h)$ with $\psi$ on $\mathbb B_k\cup\Lambda_0$, $h\in\mathbb R^N$, such that:
  - $|\psi_j(b_+)-\psi_j(b_-)|<\delta$ for bonds $b$ in $\Lambda_j$;
  - $|\psi_j(b_+)-\psi_{j-1}(x)|<\delta$ for bonds across $\Lambda_{j-1},\Lambda_j$ (with $x\in B(b_-)$);
  - $\big||\psi_j(x)|^2-1\big|<\delta$ and $|\nu(1-(\psi_j(x))_0\cdot h)|<(L^j\eta)^{-2}\delta^2$ on $\Lambda_j$;
  - $\nu|h|^2-1<\delta^2$-type condition: the printed text reads $|\nu(|h|^2-1)|<\delta^2$;
  - $(\psi)_0=\psi/|\psi|$.
- $\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ is the complex space of $(\psi+\psi',h+h')$ with $(\psi,h)\in\tilde\Psi(\mathbb B_k;\delta)$. Here $|\psi'|<\varepsilon+\delta$, $|(\psi_j+\psi_j')^2-\psi_j^2|<\delta$, $|\nu h'|<(L^j\eta)^{-2}\delta^2/\varepsilon$ and $|\nu(\psi_j)_0\cdot h'|<(L^j\eta)^{-2}\delta^2$. The corresponding bond conditions on $\psi'$ hold with $\delta$.
- Constant-configuration versions are $\tilde\Psi^c_{\rm const}(\delta,\varepsilon)$ (P1 (3.18), (3.19)).

Norms (3.17), p. 621. With $|f|_\sigma=\max_j\sup_{x\in\Omega_j\setminus\Omega_{j+1}}(L^j\eta)^\sigma|f(x)|$ and
$$|f|_{(\alpha),\sigma}=\max_j\sup_{y\in\Lambda_j}\sup_{x,x'\in\bar\Lambda(y)}\frac{(L^j\eta)^\sigma}{|x-x'|^{1-\alpha}}|f(x)-f(x')|,$$
where $\bar\Lambda(y)$ is the union of the cubes touching $\Lambda(y)$ and $|x-x'|$ is the $\ell^1$ distance. $\Lambda(y)$ is the cube of side $L^j\eta$ centred at $y\in\Lambda_j$.

Invariants for constant configurations (2.6):
$$U=\sqrt{(\psi+\psi')^2},\qquad V=(\psi+\psi')_0\cdot(h+h'),\qquad W^2=(h+h')^2-V^2 .$$

Glossary.

| symbol | meaning | where |
|---|---|---|
| $\Omega_j,\Lambda_j,\mathbb B_k$ | small-field domains, layers, generating set | (1.1)-(1.3), p. 607-608 |
| $Q(\mathbb B_k)$, $a(\mathbb B_k)$ | multiscale averaging, multiplier | (1.4), p. 608 |
| $A$, $J$ | action, linearized action | (1.4), (1.7) |
| $\alpha$ | auxiliary scalar field, equals $\tfrac\lambda2(|\phi|^2-1)$ at the solution | (1.8), (1.10) |
| $\tilde\Psi,\tilde\Psi^c$ | admissible data (real, complex) | (1.11), (1.12), p. 610 |
| $K_1,c_0,c_1$ | constants of Prop. 1.1 | p. 611 |
| $\phi_0,\alpha_0,f_0$ | approximate solution and residual | (3.2), (3.3) |
| $|\cdot|_\sigma$, $|\cdot|_{(\alpha),\sigma}$ | scaled sup / Hölder norms | (3.17) |
| $G(\alpha)$ | resolvent $(-\Delta^{D,\eta}_{\Omega_1}+Q^*aQ+\nu+\alpha)^{-1}$ | (3.22) |
| $\delta_0,\delta_1,\gamma_1$ | smallness parameters for Sect. 3 | (3.21), (3.22) |
| $B_0,B_1$ | bounds on $G$, on $H_1,H_2$ | (2.57) of [2(b)], (3.44) |
| $\psi_k^{(j)}=\psi(\mathbb B_j,\mathbb B_k';\psi')$ | minimizing block-spin field | (4.21) |
| $T(\mathbb B_k',\mathbb B_j)$ | composition of RG steps | (4.11) |
| $a_r$ | RG multiplier sequence | (4.4) |

## 2. Main results

**Proposition 1.1 (p. 611).** Assume $\tfrac12<a<\tfrac32$, $1\le\eta^2\lambda\le+\infty$ and $0<\nu\le1$. There exist positive constants $c_0,c_1,K_1,K_1c_1\le c_0$, independent of the coefficients in these intervals, such that for $(\psi+\psi',h+h')\in\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ with $0<\delta\le\varepsilon\le c_0$, $\delta\le c_1$, $\nu\varepsilon^2\le\delta^2$, system (1.14) has a solution that is unique among $(\phi,\alpha)$ satisfying only the restriction $|\alpha|<(L^j\eta)^{-2}c_0$ on $\Omega_j$, $j=1,\dots,k$. (Here $|\alpha|$ is the scaled norm $|\cdot|_2$ in (3.17).) The system (1.14) is (1.10) with complexified data and $\Omega_1$-boundary data $\psi_0+\psi_0'$ extended by $0$.

The solution is analytic in $(\psi+\psi',h+h')$ and satisfies on $\Omega_j$ (1.15):
- $|\phi-Q^*(\psi+\psi')|<K_1(L^j\eta)^{-1}\delta$;
- $|\partial^\eta\phi|<K_1(L^j\eta)^{-1}\delta$;
- $\frac{1}{|x-x'|^{1-\alpha}}|(\partial^\eta_\mu\phi)(x)-(\partial^\eta_\mu\phi)(x')|<K_1C_\alpha(L^j\eta)^{-2+\alpha}\delta$ for $0<\alpha\le1$;
- $|\Delta^\eta\phi|<K_1(L^j\eta)^{-2}\delta$;
- $|\alpha|<K_1(L^j\eta)^{-2}\delta$;
- $|\delta\phi(\psi',h')|<\varepsilon+K_1\delta$, where $\delta\phi(\psi',h')=\phi(\psi+\psi',h+h')-\phi(\psi,h)$.

$C_\alpha$ is absolute depending on $\alpha$ only (it "can be taken as $O(1)\alpha^{-d-1}$", p. 611, citing [2(a)]). The last bound says that $\delta\phi$ is "almost a contraction" in $\psi'$.

Real part: for real $(\psi,h)\in\tilde\Psi(\mathbb B_k;\delta)$ the solution is real and is a minimum of (1.4), hence a solution of (1.6)/(1.9). Additionally (1.16):
$$|\phi-h|<K_1(L^j\eta)^{-1}\frac{\delta}{\sqrt\nu},\qquad |\nu\phi\cdot Q^*h'|<K_1(L^j\eta)^{-2}\delta^2$$
for all $h'$ satisfying the last two conditions in (1.12).

Remark (p. 611): bounds improve with $j$ (they can be stated on $B^j(\Lambda_j)=\Omega_j\setminus\Omega_{j+1}$).

**Corollary 1.1 (pp. 611-612).** Special case $\Omega_j=T_\eta$ ($L^j\eta=1$, $k=j$). If $(\psi,h)\in\tilde\Psi_k(\delta)$ and $\delta\le c_1$, then problem (2.2) of P1 has exactly one solution $\phi$ with $|\alpha|<c_0$, $\alpha=\tfrac\lambda2(|\phi|^2-1)$. It extends analytically to $\tilde\Psi_k^c(\delta,\varepsilon)$ for $\delta\le\varepsilon\le c_0$, $\nu\varepsilon^2\le\delta^2$, with the maps
$$(\phi_k(\psi+\psi',h+h'),h+h'):\tilde\Psi^c_k(\delta,\varepsilon)\to\Phi^c_k(1,\tilde\varepsilon;\lambda,\nu),\qquad \tilde\Psi^c_k(\delta,\varepsilon)\subset\Xi_k^c(1,\tilde\varepsilon)\quad(1.18)$$
if $\varepsilon+K_1\delta\le\tilde\varepsilon$, $2K_1\delta\le\tilde\varepsilon$. (Spaces $\Phi^c_k$ and $\Xi_k^c$ are P1 objects not redefined here.)

**Proposition 2.1 (p. 615), constant configurations.** There are $c_2,c_4,C_1$, independent of $a,\lambda,\nu$ in the stated intervals ($\tfrac12<a<\tfrac32$, $\lambda>0$, $0<\nu\le1$), such that for $0<\delta\le\varepsilon$, $\nu\varepsilon^2\le\delta^2$, $\delta\le c_4$ and $(\psi+\psi',h+h')\in\tilde\Psi^c_{\rm const}(\delta,\varepsilon)$, Eq. (2.4) has a unique solution with $|\alpha|<c_2$. It is analytic and satisfies (2.15)
$$|\phi-(\psi+\psi')_0|<C_1\delta,\ |\phi-(\psi+\psi')|<C_1\delta,\ |\alpha|<C_1\delta,\ |\delta\phi(\psi',h')|<\varepsilon+C_1\delta .$$
For real data, $|\phi-h|<C_1\delta/\sqrt\nu$ and $|\phi\cdot h'|<C_1\delta^2/\nu$ (2.16).

**Lemma 2.1 (p. 614).** The scalar cubic (2.9) for $\alpha$ as a function of $z=a(u-1)+\nu(v-1)$ and $\nu^2w^2$ has a unique solution in $|\alpha|<c_2$ for $(u,v,w^2)\in K(1,c_3)\times K(1,c_3/\nu)\times K(0,c_3^2/\nu^2)$. The solution is analytic and $|\alpha|\le2(|z|+|\nu^2w^2|)$ (2.10). Here $K(x,r)$ is a disc (UNCERTAIN: the printed definition of $K$ is not given in this paper; it is from P1).

**Proposition 2.2 (p. 616), effective potential.** For the effective potential $V_j(\psi,h)$ of (2.17), (2.18) (the action (1.4) at the constant solution, $|h|=1$, real data), there are $c_5\le c_4$, $\gamma_2,C_2>0$ such that on $\tilde\Psi_{\rm const}(c_5)$ and for $\lambda\ge1$:
$$\gamma_2\big[(|\psi|-1)^2+\nu(1-\psi_0\cdot h)\big]\le V_j(\psi,h)\le C_2\big[(|\psi|-1)^2+\nu(1-\psi_0\cdot h)\big].$$
The proof is omitted ("elementary though lengthy"). Lowest-order part: $\tfrac12\frac{a(\lambda+\nu)}{\lambda+a+\nu}(|\psi|-1)^2+\frac{a}{a+\nu}\nu(1-\psi_0\cdot h)$ (2.19). Assumption $\lambda\ge1$ comes from (H.8) of P1 ($\lambda_k=\lambda_0L^{2k}$, $\lambda_0\ge1$).

**Lemma 3.1 (p. 620).** The functions $\phi_0,\alpha_0,f_0$ defined by (3.2), (3.3) are analytic in $(\psi+\psi',h+h')$ on $\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ for $\delta,\varepsilon$ as in Prop. 2.1 and $\varepsilon$ small. There is $C_3=C_3(C_1,L,d)$ such that $\phi_0,\alpha_0$ satisfy (1.15), (1.16) with $K_1\to C_3$, and $|f_0|<C_3(L^j\eta)^{-2}\delta$ on $\Lambda(y)$, $y\in\Lambda_j$ (3.16).

**Lemma 3.2 (p. 626-627).** For $\delta_0,\delta_1$ small, if (3.43) $\delta\alpha+H_1\delta\alpha+H_2(\delta\alpha)=H_0$ has analytic terms on (3.21) with $|H_1\delta\alpha|_2\le B_1(\delta_0+\delta_1)|\delta\alpha|_2$, $|H_2(\delta\alpha)|_2\le B_1|\delta\alpha|_2^2$, $|H_0|_2<B_1\delta_1$, then for $\delta_0\le c_6$, $2B_1\delta_1\le c_6$ there is a unique solution in $\{|\delta\alpha|_2<c_6\}$, analytic, with $|\delta\alpha|_2\le2|H_0|_2<2B_1\delta_1$ (3.45).

**Proposition 3.1 (p. 627).** There are $c_6,K_2$ depending on $d,L$ only such that for $(\delta\psi,\phi_0,\alpha_0,f_1,\alpha_1)$ in the domain (3.21) with $\delta_0,K_2\delta_1\le c_6$, system (3.20) has a unique solution $(\delta\phi,\delta\alpha)$ with $|\delta\alpha|_2<c_6$. It is analytic in $\delta\psi,\phi_0,\alpha_0,f_1,\alpha_1$ with
$$|\delta\phi|<K_2\delta_1,\ |\partial^\eta\delta\phi|_1<K_2\delta_1,\ |\partial^\eta\delta\phi|_{(\alpha),2-\alpha}<C_\alpha K_2\delta_1,\ |\Delta^{D,\eta}_{\Omega_1}\delta\phi|_2<K_2\delta_1,\ |\delta\alpha|_2<K_2\delta_1 .$$
The domain (3.21): $|\delta\psi|<\delta_1$, $\tfrac12<|\phi_0|<\tfrac32$, $|\phi_0^2-1|<\delta_0$, $|\partial^\eta\phi_0|_1<\delta_0$, $|\Delta^{D,\eta}\phi_0|_2<\delta_0$, $|\alpha_0|_2<\delta_0$, $|f_1|_2<\delta_1$, $|\alpha_1|_2<\delta_1$.

The system (3.20) is
$$(-\Delta^{D,\eta}_{\Omega_1}+Q^*aQ+\nu+\alpha_0+\delta\alpha)\delta\phi=Q^*a\delta\psi-\delta\alpha\,\phi_0+f_1,\qquad \tfrac12(2\phi_0\cdot\delta\phi+(\delta\phi)^2)-\tfrac1\lambda\delta\alpha=-\tfrac1\lambda\alpha_1 .$$
The perturbation is $\phi=\phi_0+\delta\phi$, $\alpha=\alpha_0+\delta\alpha$, $\psi\to\psi+\psi'+\delta\psi$ (3.18), with $f_1$ replacing $-f_0$ (and $\alpha_1$ replacing $0$) as independent functional variables. The point of Prop. 3.1 is that $\delta\psi,\phi_0,\alpha_0,f_1,\alpha_1$ are all treated as independent variables, to be reused later (p. 627).

**Corollary 3.1 (p. 628).** Under Prop. 1.1, $\phi_k,\alpha_k$ are analytic in $(\psi+\psi',h+h')$ on $\tilde\Psi^c(\delta,\varepsilon)$ and in $\delta\psi$ on $\{|\delta\psi|<\delta_1\}$ with $K_2\delta_1\le c_6$. The corrections $\delta\phi_k,\delta\alpha_k$ defined by (3.49) solve (3.20) with $\phi_0=\phi_k$, $\alpha_0=\alpha_k$, $f_1=0$, $\alpha_1=0$, and satisfy (3.47).

**Lemma 4.1 (p. 633).** Gaussian kernel (4.12) of $T(\mathbb B_k',\mathbb B_j)$:
$$\mathrm{const}\cdot\exp\Big[-\tfrac12\beta L^{k(d-2)}\langle\psi'-Q(\mathbb B_k',\mathbb B_j)\psi,\ a(\mathbb B_k',\mathbb B_j)(\psi'-Q(\mathbb B_k',\mathbb B_j)\psi)\rangle\Big]$$
where $\psi$ on $\mathbb B_j\cup\Lambda_0$ and $\psi'$ on $\mathbb B_k'\cup\Lambda_0'$. The scalar product uses the $\eta$-scale and each $A_p'\cap\Omega_p^{(p)c}$ term carries the volume $(L^p\eta)^d$.

**Lemma 4.2 (p. 636).** If $(\psi',h)\in\tilde\Psi(\mathbb B_k';\delta)$, $\delta\le c_1$, the system (4.17) has a unique solution $(\psi,\phi,\alpha)$ with the restrictions (4.16) and $|\alpha|_2'<c_0$. $\phi,\alpha$ solve (1.10) for $\mathbb B_k'$, so $=\phi(\mathbb B_k';\psi'),\alpha(\mathbb B_k';\psi')$, and
$$\psi(\mathbb B_j,\mathbb B_k';\psi')=Q(\mathbb B_j)\phi(\mathbb B_k';\psi')+\frac{1}{a(\mathbb B_j)}Q^*(\mathbb B_k',\mathbb B_j)a(\mathbb B_k')\big(\psi'-Q(\mathbb B_k')\phi(\mathbb B_k';\psi')\big)\qquad(4.21)$$
on $\mathbb B_j\cup(\Omega_1^c\cap\Omega_1')$. These functions extend analytically to $\tilde\Psi^c(\mathbb B_k';\delta,\varepsilon)$ (assumptions of Prop. 1.1) and satisfy the analytically extended (4.17).

**Lemma 4.3 (p. 639).** If $\delta\le c_1$, $(\psi',h)\in\tilde\Psi(\mathbb B_k';\delta)$, $X\subset\Omega_1'\cap\Omega_j$, then $(\psi(\mathbb B_j,\mathbb B_k';\psi'),h)\in\tilde\Psi(\mathbb B_j;(d+2)K_1\delta)$ (4.29) and restricted to $X$ lies in $\Psi_j(X;3L^j\eta,K_1\delta)$ (4.30). Also $(L^n\xi)^2(L^j\eta)^2|\alpha_k(x)|\le K_1\delta\le K_1c_1\le c_0$ on $B_n(y)$ (4.31). Hence if $(d+2)K_1\delta\le c_1$, then (4.23) holds and $\phi_k=\phi(\mathbb B_j;\psi_k^{(j)})$, $\alpha_k=(L^j\eta)^{-2}\alpha(\mathbb B_j;\psi_k^{(j)})$ (4.32).

**Lemma 4.4 (p. 640).** For the complex data with $\delta,\varepsilon$ as in Prop. 1.1, $(\psi'+\delta\psi',h+h')\in\tilde\Psi^c(\mathbb B_k';\delta,\varepsilon)$ and $X\subset\Omega_1'\cap\Omega_j$:
$$(\psi(\mathbb B_j,\mathbb B_k';\psi'+\delta\psi'),\ h+Q^*(\mathbb B_k',\mathbb B_j)h')\in\tilde\Psi^c(\mathbb B_j;2(d+2)K_1\delta,\varepsilon)\quad(4.37),$$
$$(\psi(\mathbb B_j,\mathbb B_k';\psi'+\delta\psi'),\ h+Q^*_{k-j}h')|_X\in\Psi^c_j(X;3L^j\eta,K_1\delta)\quad(4.38).$$

**Proposition 4.1 (p. 641).** If $(\psi',h)\in\tilde\Psi(\mathbb B_k';\delta)$, $\delta\le c_1$, then the function (4.15) has a unique critical point in the domain of all $(\psi,\phi,\alpha)$ with restriction $|\alpha|_2'<c_0$. It is $\psi(\mathbb B_j,\mathbb B_k';\psi'),\phi(\mathbb B_k';\psi'),\alpha(\mathbb B_k';\psi')$. If $(d+2)K_1\delta\le c_1$, then $\psi(\mathbb B_j,\mathbb B_k';\psi')$ is a critical point of (4.14), a solution of the variational problem, and the unique critical point there in $\{\psi:(\psi,h)\in\tilde\Psi(\mathbb B_j;c_1),|(L^j\eta)^{-2}\alpha(\mathbb B_j;\psi)|'_2<c_0\}$. It has analytic extensions to $\tilde\Psi^c(\mathbb B_k';\delta,\varepsilon)$ satisfying (4.37). If $4dK_1\delta\le\varepsilon,4dK_1\delta\le c_0$ (or $4dK_1\delta\le c_1$), then the identities (4.39) hold:
$$\phi(\mathbb B_j;\psi(\mathbb B_j,\mathbb B_k';\psi'))=\phi(\mathbb B_k';\psi'),\qquad (L^j\eta)^{-2}\alpha(\mathbb B_j;\psi(\mathbb B_j,\mathbb B_k';\psi'))=\alpha(\mathbb B_k';\psi'),$$
with $\phi,\alpha$ extended off $\Omega_1$ by (4.40): $\phi(x)=\psi(x)$, $\alpha(x)=\tfrac{\lambda_j}2(\psi^2(x)-1)$ for $x\in\Omega_1^c$.

Last paragraphs (pp. 641-642), no numbered statement. The two-sided problem (4.41) for the data $(\delta\psi,\phi_0,\alpha_0,f_1,\alpha_1)$ of Sect. 3 has solution (4.42), $\delta\psi(\mathbb B_j,\mathbb B_k')=Q(\mathbb B_j)\delta\phi(\mathbb B_k';\dots)+\frac1{a(\mathbb B_j)}Q^*(\mathbb B_k',\mathbb B_j)a(\mathbb B_k')(\psi'-Q(\mathbb B_k')\delta\phi(\ldots))$, bounded by $(2K_2+1)\delta_1$. If $K_2(2K_2+1)\delta_1\le c_6$ and $\delta_0\le c_6$, then identities (4.43) hold. Stated without proof: "the proof is the same".

Inductive hypotheses. This paper states no new (H.n). It uses (H.8) of P1 ($\lambda_k=\lambda_0L^{2k}$, $\lambda_0\ge1$, via $\lambda\ge1$, p. 616), P1 Thm 2.2 for the coefficient ranges, and mentions (H.5) of P1 as an application of $\psi_k^{(j)}$ (p. 641).

## 3. Proof architecture

**Sect. 1 (pp. 607-612).** It sets up the generating-set geometry and the multiscale action, reformulates via $\alpha$, and states Prop. 1.1. The parenthetical remark on p. 609 is the strategy: the first Euler-Lagrange equation is linear in $\phi$ with a positive operator, so $\phi$ is a function of $\alpha$. Substituting into the second gives a local scalar equation for $\alpha$. One first builds an "almost ultra-local" approximate solution, then solves the exact one by contraction.

**Sect. 2 (pp. 612-616), constant solutions.**
- Localize to a subdomain with $\Omega_j=T_\eta$, rescale to the $\xi$-lattice (2.2)-(2.3).
- For constant $(\psi+\psi',h+h')$ the system (2.4) is algebraic: $(a+\alpha+\nu)\phi=a(\psi+\psi')+\nu(h+h')$, $\tfrac12(\phi^2-1)=\alpha/\lambda$.
- Solve $\phi$ in closed form (2.5) in the O(N)-invariants $U,V,W^2$ (2.6). Bounds (2.7), (2.8) for the invariants follow from P1 (3.39), (3.41), (3.43) with $\sigma\varepsilon$ replaced by $\delta$ (UNCERTAIN: P1 inequalities not opened here).
- Substituting gives the scalar equation (2.9) for $\alpha$. Lemma 2.1 solves it by the implicit function theorem. The coefficients of (2.9) are bounded uniformly in $a\in(\tfrac12,\tfrac32)$, $\nu\in(0,1]$, $\lambda>0$, so the constants are independent of them.
- Prop. 2.1 collects bounds (2.11)-(2.14); explicit numbers appear (e.g. $|\alpha|<8\delta$, $O(1)=80$, $78\delta<1$).
- Prop. 2.2 gives upper and lower bounds on the effective potential from the lowest-order terms. It is flagged as being used "in the last paper only" (probably P7, large field) (p. 616).

**Sect. 3 (pp. 616-629), proof of Prop. 1.1.** This is the core.
- Step 1, approximate solution (pp. 616-621).
  - Take a smooth partition of unity $\{h_y\}$ on the continuous torus subordinate to the cubes $\bar\Lambda(y)$, $y\in\mathbb B_k$ (3.1), with $|\partial h_y|<2(L^j\eta)^{-1}$ and $|\partial\partial h_y|<4(L^j\eta)^{-2}$.
  - Define $\phi_0=\rho_0\tilde\phi/\sqrt{\tilde\phi^2}$ with $\tilde\phi=\sum h_y\phi(y)$, $\phi(y)$ the constant solution at the data frozen at $y$, and $\rho_0=(\sum h_y\phi^2(y))^{1/2}$ (3.2). Then $\phi_0^2=\rho_0^2$, so $\alpha_0=\tfrac\lambda2(\phi_0^2-1)=\sum h_y\alpha(y)$ is automatically local (3.3), (3.4).
  - Bounds (3.5)-(3.14) are repeated Taylor/differencing estimates using the closeness of neighbouring data (the conditions in (1.11), (1.12)). The extra factor $L^2$ in (3.5) comes from neighbours in $\Lambda_{j-1}$.
  - The residual $f_0$ is estimated in (3.15)-(3.16) and is $O((L^j\eta)^{-2}\delta)$.
  - Lemma 3.1 summarizes. $\phi_0$ is the exact projection of a smooth interpolation onto the sphere, so one-point bounds hold with constants depending only on $C_1,L,d$.
- Step 2, exact solution by perturbation (pp. 621-628).
  - Write $\phi=\phi_0+\delta\phi$, $\alpha=\alpha_0+\delta\alpha$ with the extra data $\delta\psi,f_1,\alpha_1$ (3.20).
  - Linear operator: $G(\alpha)=(-\Delta^{D,\eta}_{\Omega_1}+Q^*aQ+\nu+\alpha)^{-1}$ is a Neumann series around $G=G(0)$ when $|\alpha|_2<\gamma_1$ (3.22). The needed bounds on $G(0)$ are quoted from (2.57) of [2(b)] (norms (3.17), with $B_0$ such that $B_0\ge 4$ is allowed). This is the principal input from outside.
  - Solve the first equation for $\delta\phi$ (3.23) and substitute into the second to get a nonlinear equation (3.24) for $\delta\alpha$. Expand $G(\alpha_0+\delta\alpha)$ (3.25) to get (3.26): $G_0\delta\alpha+F_2(\delta\alpha)=F_0$.
  - $F_2$ is at least quadratic in $\delta\alpha$ (bound (3.28), $\le20B_0^2|\delta\alpha|_2^2$), $F_0$ (3.29) is $O(\delta_1)$.
  - The difficulty is that $G_0=\phi_0\cdot G(\alpha_0)\phi_0+\tfrac1\lambda+R_1$ is not uniformly invertible as $k\to\infty$ (the leading part $\phi_0G\phi_0+\tfrac1\lambda$ is not bounded below uniformly if $\lambda$ is large, "or even 0 in the limit $\lambda=\infty$"). The remedy is to apply $G^{-1}(\alpha_0)$ (the Laplacian-containing operator) to the equation, and use the Leibniz rule for the Laplacian (3.31)-(3.33) to move derivatives onto $\phi_0$ (which is smooth by (3.21)): (3.34)-(3.38). The result is an equation (3.39) of the form $\delta\alpha+\tfrac1\lambda(-\Delta^D+Q^*aQ+\nu)\delta\alpha+(\text{small})=\ldots$. So the Laplacian is a leading term, not a perturbation.
  - The operator $1+\tfrac1\lambda(\ldots)=\tfrac1\lambda G^{-1}(\lambda)$ is inverted by $\lambda G(\lambda)$, and $|\lambda G(\lambda)f|_2\le O(1)|f|_2$ uniformly in $\lambda>0$ (3.41) is proved by a Neumann series under $\lambda\eta^2\ge8dL^2+2$ (proof via direct small-perturbation argument). Then the equation takes the form (3.43), which is a contraction.
  - Lemma 3.2 is the abstract contraction lemma, Prop. 3.1 the statement.
- Step 3, conclusion (pp. 627-628).
  - Apply Prop. 3.1 with $\delta\psi=0,f_1=-f_0,\alpha_1=0$, $\delta_0=\delta_1=C_3\delta$. Uniqueness of the full solution among $|\alpha|_2<c_6/2$ is by recentring: if $(\phi,\alpha)$ solves (1.14) then $(\phi-\phi_0,\alpha-\alpha_0)$ solves (3.20). Constants: $c_0=\tfrac12c_6$, $c_1=\min\{c_4,(2K_2+1)^{-1}C_3^{-1}c_6\}$ and $K_1=(2K_2+1)C_3$.
  - Minimum property: expand $A(\psi,\phi+\delta\phi)$ around $\phi$ with $\delta\phi=0$ on $\Omega_1^c$ (3.48); the quadratic form $\tfrac12\langle\delta\phi,(-\Delta^D+Q^*aQ+\nu+\alpha+\lambda\phi\otimes\phi)\delta\phi\rangle$ is positive definite. Hence $\phi$ is the only critical point in $\{\phi:|\tfrac\lambda2(|\phi|^2-1)|_2<c_0\}$.
- Corollary 3.1 records the analytic dependence on a further perturbation $\delta\psi$.

**Pp. 628-630, remark on general potentials.** Sketch of the same method for a generalized third term $\tfrac12\langle V(|\phi|^2-1),1\rangle$ (3.50) with $V$ analytic, $V(0)=V'(0)=0$ ($V''(0)>0$ possibly large): constant solutions, approximate solution, change of variables $\delta\phi=\phi_0\chi+\phi'$, $\phi_0\cdot\phi'=0$, with nonlinear substitution $\chi=(1+2\chi'-|\phi'|^2/|\phi_0|^2)^{1/2}-1=\chi'+h_2(\chi',|\phi'|^2)$, and rescaling $\chi'=\lambda^{-1/2}\chi$, $\lambda=2V''(0)$. Described as a sketch ("more technical details to work out"). Not used later in this paper.

**Sect. 4 (pp. 630-642), two generating sets.**
- Setting: two generating sets $\mathbb B_j\prec\mathbb B_k'$ ($\Omega_1\subset\Omega_1',\dots,\Omega_j\subset\Omega_j'$, $j\le k$). The generalization of problem (2.6) of P1 asks what field on the finer set $\mathbb B_j$ one gets when one first integrates the intermediate scales, i.e., composes the RG steps for $\mathbb B_j$ (steps up to $j$, "$T(\mathbb B_j)$") with extra steps to reach $\mathbb B_k'$.
- Gaussian composition formula (4.2): $\int d\psi\,\exp[-\tfrac12A|\theta-Q\psi|^2]\exp[-\tfrac12\sum B|\psi-f|^2]=\mathrm{const}\cdot\exp[-\tfrac12C|\theta-Qf|^2]$ with $C=A/(L^{-d}(Q\tfrac AB)+1)$ (the printed formula for $C$ is difficult to read exactly; UNCERTAIN in detail). Composing $r$ steps gives (4.3) with $a_{r+1}=\frac{aa_r}{L^{-2}a+a_r}$, i.e. $a_r=a\frac{1-L^{-2}}{1-L^{-2r}}$ as printed on p. 631 (the printed form is $a_r=a\frac{1-L^{-2}}{1-L^{-2r}}$; I read $\frac{1-L^{-2}}{1-L^{-2r}}$ but UNCERTAIN: the image gives $1-L^{-2}$ in the numerator, consistent with $a_1=a$ and $a_\infty=a(1-L^{-2})$). The sequence decreases to $a(1-L^{-2})$.
- General multiscale composition: (4.5)-(4.7) with averaging $Q(\Lambda_p(y),\mathbb B_j)$ and $1/a(\Lambda_p(y),\mathbb B_j)=\sum_{n<p}\sum_{x}\frac{|\Lambda_n(x)|}{|\Lambda_p(y)|}\frac1{a_{p-n}}$. Proved by induction on $p$ (pp. 631-633). The key facts are the bounds $a(1-L^2)\le a_p\le a(\Lambda_p(y),\mathbb B_j)\le a_1=a$ (4.8). (The printed interval is $[a(1-L^{2}),a]$ as written; correct reading is $[a(1-L^{-2}),a]$ by the text.)
- Lemma 4.1 gives the Gaussian kernel of $T(\mathbb B_k',\mathbb B_j)$ with $Q(\mathbb B_k',\mathbb B_j)$, $a(\mathbb B_k',\mathbb B_j)$ (4.9)-(4.10).
- Variational problem (4.14), (4.15): fixed $\psi'$ on $\mathbb B_k'\cup\Lambda_0'$, vary $\psi,\phi,\alpha$ with the restrictions (4.16). Euler-Lagrange (4.17).
- Solution of (4.17): the $\psi$-equation is a linear, diagonal-by-cube algebraic system solvable explicitly (formula (4.19)), using the identity (4.18) from the invariance of the kernel under composition. Then $\psi=Q\phi+\frac1{a}Q^*a'(\psi'-Q'\phi)$ (4.20). Substituting back, the remaining equations for $(\phi,\alpha)$ are exactly (1.10) for $\mathbb B_k'$ (Lemma 4.2). So existence and uniqueness reduce to Prop. 1.1 for $\mathbb B_k'$; this is routine given Prop. 1.1.
- Lemma 4.3: show that $\psi_k^{(j)}$ lies in the small-field domain $\tilde\Psi(\mathbb B_j;(d+2)K_1\delta)$. This uses (4.24)-(4.28), which are the "arguments of Lemma 3.1 of P1" repeated with scaling factors $L^nL^{-p}$; the constants worsen to $d+2$ (and improve to $3$ on subdomains $X$, with the generalized spaces $\Psi_j(X;\sigma,\varepsilon)$ of P1 (3.13)).
- Lemma 4.4 is the complex analogue, with $h'$ transported by $Q^*(\mathbb B_k',\mathbb B_j)$.
- Prop. 4.1 combines: uniqueness for the $\mathbb B_j$ problem (in $\tilde\Psi(\mathbb B_j;c_1)\cap\{|\alpha|<c_0\}$), the identities (4.39), which give the compatibility "minimize over $\mathbb B_j$ first then $\mathbb B_k'$ equals minimize in one step". These identities are what the RG needs when composing steps.
- Final paragraphs: (4.41)-(4.43) for the Sect. 3 setting with perturbation data. Only sketched.

Routine vs hard.
- Routine: the constant case (Sect. 2) is explicit algebra plus the implicit function theorem. Sect. 4 composition formulas are Gaussian algebra. The partition-of-unity estimates are tedious but elementary.
- Hard: the uniform-in-$\lambda$ treatment of the linearized operator in Sect. 3, pp. 623-626, and, behind it, the propagator bounds (2.57) of [2(b)], which are not reproved here. The uniformity of constants over $\lambda\in[1,\infty]$ and over the multiscale operator $Q^*aQ$ with $k$ arbitrarily large is the substantive content.

## 4. Ingredients and prerequisites

**4a. Bundle papers.**
- P1 (CMP 167). Used throughout:
  - Definitions: lattice classes $\mathcal D_j$ (Sects. 1-2 of P1), spaces $\tilde\Psi(\delta)$, $\tilde\Psi^c$, $\Psi_j(X;\sigma,\varepsilon)$ (P1 (3.13), (3.18), (3.19)), $\Phi_k^c$, $\Xi^c_k$.
  - Variational problems (2.1), (2.2), (2.6), (2.7); the one-step transformation (1.11); coefficient ranges (Thm 2.2); inductive hypotheses (H.8) (growth $\lambda_k=\lambda_0L^{2k}$, $\lambda_0\ge1$) and (H.5).
  - P1 (3.37)-(3.43) for the invariants $U,V,W^2$ and their bounds (2.7); Lemma 3.1 of P1, whose argument (3.1)-(3.6) is repeated in (4.24)-(4.27).
  - P1 (2.25), the formula for effective potentials; P1 (3.25), the symmetry argument that $V_j$ is a function of $|\psi|-1$ and $\nu(1-\psi_0\cdot h)$.
  - P1 (1.10), the scaling relations.
  - P1 (2.11): $a_j(L^j\eta)^{-2}$.
- Paper P2 supplies back to P1 (which cites it as [..]) Corollary 1.1.

**4b. External.**
- [2] as printed: "Balaban, T.: Commun. Math. Phys. **89**, 571 (1983); (b) **96**, 223 (1984)" (labelled (a), (b) in the text).
  - From memory (not verified against the bundle; UNCERTAIN): [2(a)] is "Regularity and decay of lattice Green's functions", CMP 89 (1983) 571-597; [2(b)] is "Propagators and renormalization transformations for lattice gauge theories. II", CMP 96 (1984) 223-250.
  - Uses: [2(b)] Sect. B, Prop. 2.1 and (2.57), is cited for the lattice operator $-\Delta^{D,\eta}_{\Omega}+Q^*aQ+\nu+\alpha$: positivity, bounds of the Green's function $G(\alpha)$ in the scaled norms (3.17), including Hölder (regularity) norms. It is also the source of the Neumann-series control for small $\alpha$ (p. 622). The Hölder-regularity constant $C_\alpha=O(1)\alpha^{-d-1}$ is attributed to [2(a)] (p. 611).
  - Essential: yes. Without these propagator/decay bounds Props. 1.1 and 3.1 cannot be proved. The bounds themselves rely on random-walk expansions (in the gauge-theory setting), which are not reproduced here and are not reviewed.
  - Notice the structure: the operator in [2(b)] there is $-\Delta+Q^*aQ$ with $Q$ the (multiscale) averaging; P2 only needs its scalar version with $\nu,\alpha$ added as small perturbations to the mass-like term $Q^*aQ+\nu+\alpha$.

**4c. Standard mathematics.**
- Analytic functions of several complex variables (or of Banach-space-valued variables): analytic implicit function theorem, analyticity of limits of uniformly convergent Neumann series of analytic operators, Cauchy estimates (not invoked explicitly but implicit in the use of analytic extensions to complex $\psi'$).
- Contraction mapping principle (Lemma 3.2).
- Discrete Laplacian calculus (Leibniz rule (3.31)-(3.33)), Dirichlet Laplacian on subsets of $T_\eta$, discrete Hölder norms.
- Smooth partitions of unity.
- Gaussian integration with linear forms (4.2).
- $O(N)$-invariant theory for two vectors ($U,V,W^2$).
- Elementary Taylor expansions around the sphere.

## 5. Dependency ledger

| result | internal | other bundle | external | status |
|---|---|---|---|---|
| Prop. 1.1 (main existence/uniqueness/analyticity/bounds) | Prop. 2.1, Lemma 3.1, Prop. 3.1, (3.48) | P1 defs, (H.8) | [2(a)], [2(b)] via Prop. 3.1 | proved modulo cited propagator bounds; some constants/steps sketched |
| Corollary 1.1 | Prop. 1.1 | P1 Sect. 2-3 | none | stated as special case; no separate proof |
| Lemma 2.1 | (2.9) | -- | -- | proved (existence of constants only, "obvious") |
| Prop. 2.1 | Lemma 2.1, (2.5)-(2.14) | P1 (3.37)-(3.43) | -- | proved (explicit) |
| Prop. 2.2 | (2.17)-(2.19) | P1 (2.25), (3.25), (H.8) | -- | details omitted ("We omit the details") |
| Lemma 3.1 | Prop. 2.1, (3.1)-(3.16) | P1 | -- | proved (long, routine estimates) |
| (3.41) uniform bound on $\lambda G(\lambda)$ | (3.40) | -- | [2(b)] (2.57)-type bounds not needed; direct Neumann series | proved for $\lambda\eta^2\ge8dL^2+2$; a "simple proof via localization" promised later |
| Lemma 3.2 | contraction | -- | -- | proved (standard, omitted details) |
| Prop. 3.1 | (3.20)-(3.46), Lemma 3.2 | -- | [2(b)] Prop. 2.1, (2.57); [2(a)] | proved modulo cited bounds; $F_2$ expansion described, not written out |
| Gen. potential sketch (3.50)-(p. 630) | Sect. 3 method | -- | -- | sketched only |
| Lemma 4.1 | (4.2)-(4.8) | P1 (1.11) | -- | proved by induction (formulas dense) |
| Lemma 4.2 | Lemma 4.1, Prop. 1.1 | P1 | -- | proved |
| Lemma 4.3, 4.4 | Prop. 1.1, (4.24)-(4.36) | P1 Lemma 3.1 | -- | argued ("repeated arguments") |
| Prop. 4.1 | Lemmas 4.2-4.4 | P1 (H.5) | -- | proved modulo the above; second-order check "omitted" |
| (4.41)-(4.43) | Prop. 3.1, Lemma 4.2 | -- | -- | stated; "same proof" |

## 6. Constants and parameters

Order of choice.
1. Data: $d\ge3$, $N$, $L\ge3$ (used as $L\ge3$ in (4.26)), $R$ (fixed later; unspecified here), $M=L^m$ (not fixed here; "connected with other conditions in following papers").
2. Coefficients: $\tfrac12<a<\tfrac32$, $1\le\eta^2\lambda\le\infty$ (so $\lambda\ge1$ at scale $L^j\eta=1$, since $\lambda=\lambda_0L^{2j}$ from (H.8) of P1 gives $\lambda\ge1$ after rescaling; (2.20) and Prop. 2.2 use $\lambda\ge1$), $0<\nu\le1$. Bounds are claimed uniform over this range.
3. Absolute constants from Sect. 2: $c_2,c_3,c_4,c_5$, $C_1,C_2$, $\gamma_2$ (independent of $a,\lambda,\nu$, of $L$, $d$ except through absolute numbers; $c_3$ from Lemma 2.1).
4. $C_3=C_3(C_1,L,d)$ from Lemma 3.1.
5. From Sect. 3: $B_0$ (propagator bound, from [2(b)], $B_0\ge4$ wlog), $\gamma_1$ (Neumann convergence radius), $B_1=B_1(B_0,d,L)$, then $c_6,K_2$ depending on $d,L$ only: $\delta_0\le c_6$, $2B_1\delta_1\le c_6$, $3B_0\delta_0\le1$, $B_0\gamma_1\le1$.
6. Prop. 1.1 constants: $c_0=\tfrac12c_6$, $c_1=\min\{c_4,(2K_2+1)^{-1}C_3^{-1}c_6\}$, $K_1=(2K_2+1)C_3$.
7. Sect. 4: $K_1$ reused; domain shrinkage factor $(d+2)K_1$ for $\delta$ (Lemma 4.3), $2(d+2)K_1$ for complex (Lemma 4.4); requirements $(d+2)K_1\delta\le c_1$, $4dK_1\delta\le\varepsilon$ etc.

Constraints.
- $\delta\le\varepsilon\le c_0$, $\delta\le c_1$, $\nu\varepsilon^2\le\delta^2$ (Prop. 1.1).
- $\lambda\eta^2\ge8dL^2+2$ for (3.41); this is implied by $\eta^2\lambda\ge1$ only for the explicit approach if $L$ is such; UNCERTAIN how the case $1\le\lambda\eta^2<8dL^2+2$ is handled (text defers to "a simple proof by localization" in the next paper, p. 626).
- $\delta_0,\delta_1$ small as in Lemma 3.2: $\delta_0\le c_6$, $2B_1\delta_1\le c_6$, $B_1(\delta_0+\delta_1+c)\le\tfrac12$.
- $R$, $M$: left to later papers.

## 7. Weak spots and open points

1. **Propagator bounds are quoted, not proved.** The key bounds (2.57) of [2(b)] are used for $G(\alpha)=(-\Delta^{D,\eta}_{\Omega_1}+Q^*aQ+\nu+\alpha)^{-1}$ in the scaled sup and Hölder norms, including the dependence on the multi-layer domain $\Omega_1\supset\Omega_2\supset\dots$ and on the weights $a_j(L^j\eta)^{-2}$. Whether the setting of [2(b)] (gauge theory, one-step averaging with block $L$) literally covers the multiscale operator $Q(\mathbb B_k)$ of (1.4) with variable multiplier $a(\mathbb B_k)$ and Dirichlet conditions is asserted, not demonstrated (p. 622).
2. **Uniform inverse in $\lambda$** (pp. 623-626). The statement "(3.41) with $O(1)$ independent of $\lambda>0$ ... we will prove it later in the next paper, together with its localization expansion" (p. 626) means the full uniformity in $\lambda\ge\eta^{-2}$ is not proved here; only the case $\lambda\eta^2\ge8dL^2+2$ is shown directly. This matches the later localization papers (P3).
3. **Prop. 2.2 proof omitted** ("We omit the details", p. 616). It is stated that this inequality is used only in the "last paper" (P7 presumably).
4. **Details of (3.26)-(3.29)** are described but not written: $F_2$ is "a sum of terms of one of the forms (3.28)". The list of bounds (3.34)-(3.38) is only sampled ("Inspecting the function $F_2$...").
5. **Constants in Lemma 2.1:** only existence ("It is easy to find explicitly...it is not important"). Numbers in (2.10)-(2.14) like 80, 78, 56, 22 do not all follow from (2.7)/(2.8) in an evident way.
6. **Arithmetic/typographical points to check against the image**:
   - (2.7) vs (2.8): $K(1,2\delta)\times K(1,22\delta^2/\nu)\times K(0,56\delta^4/(\nu^2\varepsilon^2))$ versus the simplified $8\delta$, $(8\delta)^2/\nu$, $(8\delta)^2/\nu^2$; the second is claimed from $\delta\le\varepsilon$.
   - (4.4) formula for $a_r$ and (4.8) interval: the text says "interval $[a(1-L^2),a]$" but $a_\infty=a(1-L^{-2})$; presumably a missing minus sign in the exponent.
   - Lemma 4.1 requires $L^m=M$, and the Gaussian constant $\beta L^{k(d-2)}$ means $\beta$ enters but the problem is $\beta$-independent after (4.13).
   - $\nu(|h|^2-1)$ condition in (1.11): printed as $|\nu(|h|^2-1)|<\delta^2$; the garbled reading "$\nu|h|^2-1$" above is mine; read the image.
7. **Dependency on the Hölder exponent.** $C_\alpha\sim\alpha^{-d-1}$ attributed to [2(a)] with "it follows from the analysis" (p. 611). The third bound in (3.47) quantifies $|\partial^\eta\delta\phi|_{(\alpha),2-\alpha}$ using the same $C_\alpha$; this is not derived here.
8. **Analyticity** is asserted from the Neumann series and the inverse function argument; no explicit statement of the topology (which Banach space) is given. In particular, analyticity in $\psi+\psi'$ over the complex domain $\tilde\Psi^c$ with infinitely many (finite but arbitrarily large) variables relies on uniform bounds, and is treated as evident.
9. **Complex extension of uniqueness.** The sentence on p. 640 ("the only change is that we consider the complex solutions of the extended system...") makes uniqueness in the complex case rely on re-running Prop. 1.1; the claim $(4.39)$ for complex data is then via analytic continuation of an identity valid for real data. Not written out.
10. **Final paragraph (4.41)-(4.43)** is a sketch ("same proof"), no statement is numbered; later papers use it as if it were a proposition.
11. **Section 3 remark on general potentials** (pp. 628-630) is sketched only; $V$ in (3.50) with large $V''(0)$ would need new work.
12. $R$ and $M$ are not fixed; "obtain conditions on $M$ connected with the variational problems" is stated in the Introduction but no condition on $M$ actually appears in the statements (the paper never uses $M$ other than $L^m=M$ and the separation (1.1)). UNCERTAIN how $RM$ in (1.1) enters the proofs: it is not visibly used in Sect. 3 (the bounds are local; the domain geometry enters only via $\Omega_1$ vs. $\Lambda_0$ and neighbour cubes touching).
13. The text layer of this scan was not consulted; all formulas were read from the images, but several (e.g. (3.28), (3.37), (4.2)) are dense and my transcriptions are partial.

## 8. Preliminary formalization notes

Self-contained early targets.
- **Sect. 2 (constant solutions)**: finite-dimensional algebra. The map $(\psi+\psi',h+h')\mapsto(\phi,\alpha)$ is an implicit function problem for a scalar cubic (2.9) in one variable, plus the explicit formula (2.5). Formalizable with the Mathlib analytic implicit function theorem (an existing theory for $C^k$ in Banach spaces, `HasStrictFDerivAt.toPartialHomeomorph`; analytic version less complete; GUESS). The invariants $U,V,W^2$ are elementary. The explicit constants ($c_2,c_3$) can be left existential.
- **Sect. 4 composition formulas (4.2)-(4.8) and Lemma 4.1**: finite-dimensional Gaussian algebra (completing the square), an induction on $p$, no analysis needed. Good early target after settling the data structure (generating sets, nested domains).
- **Sect. 3 abstract contraction (Lemma 3.2)**: reusable contraction/inverse function lemma in a Banach space of weighted functions on a finite lattice; the Neumann series for $G(\alpha)$ given the base-case bound on $G(0)$ is standard operator theory. Mathlib has the Neumann series for bounded operators, Banach fixed point.

What it needs from outside.
- The propagator estimates of [2(b)] in the weighted sup/Hölder norms (3.17) for the multiscale operator. These are the main external dependency, and need a separate formalization effort (random-walk expansions or other decay proof). Alternatively one could axiomatize the bound $|G(0)f|_2\le B_0|f|_2$ and the derivative bounds as a hypothesis (like "Green's function interface"), formalize everything in P2 relative to it, and treat it as a frozen statement to be proved separately. P2 is a good test of that interface.
- The bound (3.41) for $\lambda G(\lambda)$ uniform in $\lambda$ is promised elsewhere. If it were needed as input, it too has to come from a localization argument.
- Definitions from P1: $\tilde\Psi$, $\Psi_j(X;\sigma,\varepsilon)$ and the lattice classes $\mathcal D_j$ must be fixed first. Note that the definitions of the spaces in this paper are only partly self-contained (spaces $\Phi_k^c,\Xi_k^c$ are quoted).

Hardest parts.
- Setting up the multiscale norms (3.17) and the family of weighted domains and operators $Q^*aQ$ in a form that allows both the quoted propagator bound and the Leibniz-rule estimates (3.31)-(3.38).
- Bookkeeping of many constants ($K_1,K_2,C_3,B_0,B_1,c_i$): best done existentially with explicit dependency structure ($d,L$ only).
- Analyticity in infinitely many variables (really finitely many, but with uniform bounds) of the solution map: needs a clean formulation (analytic maps between Banach spaces of configurations, or holomorphic in each coordinate with uniform bound, plus Hartogs/Osgood).
- Lemmas 4.3-4.4: heavy case analysis over scales $p_1,p_2,n$ (4.24)-(4.28).

Assessment as an early target. Real-variable Sect. 2 and Sect. 4 algebra are self-contained and could be done early. The core existence theorem (Prop. 1.1) is formalizable if the Green's function bounds of [2(b)] are taken as a stated interface. Without it, Prop. 1.1 is not self-contained. The paper is short and its logic is clean (approximate solution + inverse function theorem + Laplacian-absorbing trick), so it is a reasonable second-stage target after the basic definitions of P1.
