# GREEN: the Green's function estimates of the Balaban series, as interfaces with proofs

Phase-1 document D-G. Author: analyst session, 2026-10-11. Source for freezing the interfaces
G-1 to G-6 and for writing their Lean proofs. Mathematics on paper only; no Lean was written or run.

Conventions of this document. "P2 p. 611" means the journal page of CMP 175; "(3.22)" without a
paper name is the equation of the paper under discussion. Page images of the scans P2, P3, P4 and of
E5 were read for every item marked "read"; P6, P7, P9, D1 were read from their text layers. Items
cited from the reviews only are marked "(review)". Doubts are marked UNCERTAIN. Everything in
Sections 4.1 to 4.5 is proved here (or reduced to a named elementary lemma whose proof is given); what
is cited is listed at the head of each subsection.

Reference to Lean infrastructure: the public repository `scottnarmstrong/Frohlich-Spencer`, commit
`b47bc3d` (local read-only clone `/home/scott/mining/Frohlich-Spencer`, same layout), file
`FroehlichSpencer/Infra/Green/CombesThomas.lean`. No other FroehlichSpencer path is cited.

---

## 1. Setting and definitions

### 1.1 Lattices, inner products, differences

$L\ge 3$ is an integer (P2 p. 607). $\eta=L^{-n}$ for an integer $n\ge k$. The *fine torus*
$T_\eta=(\eta\mathbb Z/\mathbb Z)^d$ has $\eta^{-d}$ points; the infinite-volume analogue is
$\eta\mathbb Z^d$. For $j\ge0$ put $\ell_j=L^j\eta$. The *scale-$j$ lattice* $T^{(j)}_{\ell_j}=(\ell_j\mathbb Z/\mathbb Z)^d$
is the set of centres of $j$-blocks; $B_j(y)$ is the cube of $L^{jd}$ points of $T_\eta$ with centre $y$
(P2 (1.2), p. 607: "$\Omega_j^{(i)}=\Omega_j\cap T^{(i)}_{L^i\eta}$ is the set of centres of $i$-blocks").
The *unit lattice of step $k$* is $T^{(k)}_1:=T^{(k)}_{\ell_k}$ with $\ell_k=L^k\eta=1$; its points are the
centres of the unit blocks. For $\ell_k=1$ one has $\eta=L^{-k}$. For fields on $T^{(k)}_1$ we write
$\Delta^1$ for the nearest-neighbour Laplacian of spacing 1 (P4 uses $\Delta$ for this).

Inner products. On $T_\eta$: $\langle f,g\rangle=\eta^d\sum_x\overline{f(x)}\,g(x)$ for $\mathbb C^N$-valued
(or $\mathbb C$-valued) $f,g$; $\|f\|^2=\langle f,f\rangle$. For real fields the bar is absent. On a lattice of
spacing $\ell_j$ the weight is $\ell_j^d$ (P2 (1.5)). For *analytic extensions* (complex $\alpha$, complex
$\phi_0$) Balaban keeps the *bilinear* expressions, e.g. $\phi_0\cdot G\phi_0$ with the dot product of $\mathbb C^N$
without conjugation; coercivity statements below are stated for the sesquilinear form and its real part.

Differences. For a bond $b=(b_-,b_+)=(x,x+\eta e_\mu)$ put $\partial^\eta f(b)=\eta^{-1}(f(b_+)-f(b_-))$,
$\|\partial^\eta f\|^2=\eta^d\sum_b|\partial^\eta f(b)|^2$ (sum over all bonds of the lattice under
consideration), and $\Delta^\eta=-\partial^{\eta*}\partial^\eta$, i.e.
$(\Delta^\eta f)(x)=\eta^{-2}\sum_{\mu}(f(x+\eta e_\mu)+f(x-\eta e_\mu)-2f(x))$. For $\Omega\subset T_\eta$,
$\chi_\Omega$ is the indicator, and the **Dirichlet Laplacian** is $\Delta^{D,\eta}_\Omega=\chi_\Omega\Delta^\eta\chi_\Omega$
(P2 p. 609, after (1.10)); for $u:\Omega\to\mathbb C$ extended by zero (written $\tilde u$),
$$\langle u,-\Delta^{D,\eta}_\Omega u\rangle=\|\partial^\eta\tilde u\|^2,$$
the sum running over *all* bonds of $T_\eta$ including those joining $\Omega$ to $\Omega^c$. We always
suppress the superscript $\eta$ when no confusion arises. The $\ell^1$-distance is $|x-x'|=\sum_\mu|x_\mu-x'_\mu|$ (P2 p. 611).

### 1.2 Domains, generating sets, multiscale averaging

Fix $k\ge1$ and a decreasing sequence $\Omega_1\supset\Omega_2\supset\dots\supset\Omega_k$ of subsets of $T_\eta$, each
$\Omega_j$ a union of $j$-blocks (P2 (1.2): $\Omega_j=B^j(\Omega^{(j)}_j)$), with the separation condition
(P2 (1.1), p. 607)
$$\ell_j^{-1}\,\mathrm{dist}(\Omega_j^c,\Omega_{j+1})>RM\qquad(1\le j<k),\tag{S}$$
$R$ a positive integer and $M=L^m$ ("fixed later", P2 p. 607; the product $RM$ is what is used; we write
$\varrho:=RM$). Put $\Omega_{k+1}=\emptyset$. The *layers* and block-centre sets are
$$\Lambda_j=\Omega_j^{(j)}\setminus\Omega_{j+1}^{(j)}\ (j<k),\quad\Lambda_k=\Omega_k^{(k)},\quad
\mathbb B_k=\bigcup_{j=1}^k\Lambda_j\tag{1.3}$$
(the *generating set*, P2 p. 608). The layer $j$ region is $\Omega_j\setminus\Omega_{j+1}=B^j(\Lambda_j)$; it is a
disjoint union of $j$-blocks. (P2 also uses $\Lambda_0=\Omega_1^c\cap\Omega_1^\sim$; it does not enter the operators below.)
Some $\Omega_j$ may equal $T_\eta$; then the layers $j'<j$ are empty. The case "all $\Omega_j=T_\eta$" is the
small-field case of P4: only $\Lambda_k=T^{(k)}_1$ is nonempty and $\mathbb B_k$ is the single unit lattice.

*Multiscale spacing.* $\ell(x):=\ell_j=L^j\eta$ for $x\in\Omega_j\setminus\Omega_{j+1}$. The block of $x$ is
$B(x)$, the $j$-block containing $x$; $\Delta(y)$ ($y\in\Lambda_j$) is the cube of side $\ell_j$ centred at $y$,
i.e. $B_j(y)$; $\tilde\Delta(y)$ the union of the blocks of $\Omega_1$ touching $\Delta(y)$ (P2 (3.17), "$\bar\Lambda(y)$").

*Averaging.* $(Q_jf)(y)=\sum_{x\in B_j(y)}L^{-jd}f(x)$ for $y\in T^{(j)}_{\ell_j}$ (P2 (1.4)). The adjoint
with respect to the weights $\ell_j^d$ and $\eta^d$ is $(Q_j^*\psi)(x)=\psi(y)$ for $x\in B_j(y)$. Hence
$Q_j^*Q_j=P_j$ is the orthogonal projection of $\ell^2(T_\eta)$ onto functions constant on $j$-blocks, and for a
block $B$ we write $P_B$ for the projection onto constants in $\ell^2(B,\eta^d)$. With
$Q(\mathbb B_k)f=Q_jf$ on $\Lambda_j$ and $a(\mathbb B_k)=a_j\ell_j^{-2}$ on $\Lambda_j$ (P2 (1.4)),
$$a_j=\frac{1-L^{-2k}}{1-L^{-2j}}\,a_k,\qquad
\langle u,Q^*aQu\rangle=\sum_{j=1}^k a_j\ell_j^{-2}\sum_{B\subset\text{layer }j}\|P_Bu\|^2,\tag{1.4}$$
where the last identity uses $\ell_j^d|Q_ju(y)|^2=\|P_{B_j(y)}u\|^2$. P2's standing assumptions
(P2 p. 609): $\tfrac12<a_k<\tfrac32$, $0\le\nu\le1$ (P2 states $0<\nu\le1$; the case $\nu=0$ is needed by
P7 (2.34) and P9, and all our bounds hold for it). Since $\frac{1-L^{-2k}}{1-L^{-2j}}\in[1,\frac98]$ for $j\le k$ and $L\ge3$,
$$a_j\in\big(\tfrac12,\tfrac{27}{16}\big)\subset[\tfrac12,2]\qquad(1\le j\le k).\tag{1.5}$$
All constants below hold under (1.5) only. In P3 the parameter is $a$ in $aL^{-2}Q^*Q$ (the $k{+}1$-st
step); the same range is assumed.

### 1.3 The operators

For $\alpha:\Omega_1\to\mathbb C$ with $|\alpha|_2<\gamma_1$ (norms in 1.5 below) and $D=\Omega_1$:
$$H_D(\alpha)=-\Delta^{D,\eta}_{\Omega_1}+Q^*(\mathbb B_k)a(\mathbb B_k)Q(\mathbb B_k)+\nu+\alpha,\qquad
G_D(\alpha)=H_D(\alpha)^{-1}\ \text{ on }\ell^2(\Omega_1)\tag{1.6}$$
(P2 (3.22): $G(\alpha)=(-\Delta^{D,\eta}_{\Omega_1}+Q^*aQ+\nu+\alpha)^{-1}$). $G=G(0)$. Here $\Omega_1=T_\eta$
(no boundary) is allowed; $\Delta^{D}_{T_\eta}=\Delta^\eta$ is the periodic Laplacian. Since $\Omega_1\subset T_\eta$ is
finite, $H_D(\alpha)$ is a finite matrix, and "invertible" is a statement to be proved (it follows from G-1).

*The domains $\mathcal D$ of the roadmap.* P3 (2.3) uses also the cubes $\square_z\cap\Omega_1$ of side $3M\ell_j$
with Neumann conditions on $\partial\square\cap\Omega_1$ for the walk expansion. We do not need them (Section 4.6);
if a localization expansion by walks is kept, their coercivity and $L^2$ bounds are the same
(only bonds are removed), and pointwise bounds near Neumann faces follow by even reflection.

*The $x$-variant (P3 (3.8), p. 62, read).* Let $Q_k$ be the $k$-block average $T_\eta\to T^{(k)}_1$, $Q$ the
$L$-block average $T^{(k)}_1\to T^{(k+1)}_L$ (so $Q_k^*Q^*QQ_k=P_{k+1}$), $a=a_{k+1}$-type constant in
$aL^{-2}$, and $x\ge0$. Then
$$G_{k,x}(\alpha_0)=\Big(-\Delta^{D,\eta}_{\Omega_1}+a_kQ_k^*\Big[\tfrac{x}{a_k+x}(I-Q^*Q)+\tfrac{aL^{-2}+x}{a_k+aL^{-2}+x}Q^*Q\Big]Q_k\big|_{\Omega_{k+1}}
+Q^*(\mathbb B_k)aQ(\mathbb B_k)\big|_{\Omega_{k+1}^c}+\nu_k+\alpha_0\Big)^{-1}\tag{1.7}$$
(the restrictions are to $\Omega_{k+1}$ and its complement in $\Omega_1$, with $\Omega_{k+1}$ here the $(k{+}1)$-st
domain of the extended generating set), and
$A_{k,x}=\frac1{a_k+x}(I-Q^*Q)+\frac1{a_k+aL^{-2}+x}Q^*Q$. In terms of the unit-lattice operator
$S_x:=\big(a_k^{-1}+(x+aL^{-2}Q^*Q)^{-1}\big)^{-1}=a_k-a_k^2A_{k,x}$ (see G-6(b)), the bracket in (1.7) is $S_x$.

*Unit-lattice operators.* For $\psi$ on $T^{(k)}_1$ (or on a subset, with zero extension):
$$\Delta^{(k)}(\mathbb B_k;\alpha)=a_k-a_k^2Q_kG_D(\alpha)Q_k^*\ \ (\text{P4 (2.23)}: \Delta^{(k)}=a_k-a_k^2Q_kG_k(\alpha_{k+1})Q_k^*),\tag{1.8}$$
with $G_k(\alpha)=(-\Delta^\eta+a_kQ_k^*Q_k+\nu_k+\alpha)^{-1}$ on $T_\eta$ in the small-field case of P4
(there $\mathbb B_k=T^{(k)}_1$ and $Q^*aQ=a_kQ_k^*Q_k$, so (1.8) agrees with (1.6)). In general the
multiscale $G_D$ contains the layer-$k$ term $a_kQ_k^*Q_k$ on $\Omega_k$; (1.8) is the object of P3 (3.1), P7 (2.36)
("operator $G_k(\alpha)$ given by (2.27) [5] for the generating set $\mathbb B_k(U_k)$"). The fluctuation covariance is
$C^{(k)}=(aL^{-2}Q^*Q+\Delta^{(k)})^{-1}$ and $C^{(k)}_x=(aL^{-2}Q^*Q+\Delta^{(k)}+x)^{-1}$ (P3 (3.6), (3.4)).
In P9, $G_j=(-\Delta+a_jQ_j^*Q_j+\nu_j)^{-1}$ on the translation-invariant lattice, $\Delta^{(j)}_{tr}=a_j-a_j^2Q_jG_jQ_j^*$,
$C^{(j)}_{tr}=(\Delta^{(j)}_{tr}+aL^{-2}Q^*Q)^{-1}$ (P9 (4.13)).

### 1.4 Distances

*Path metric* (used in all proofs; comparable to P3's). For a bond $b$ of $T_\eta$ with endpoints in layers
$j,j'$ let $\ell(b)=\max(\ell_j,\ell_{j'})$ and
$$d(x,x')=\inf_{\text{bond paths }x=z_0,\dots,z_m=x'}\ \sum_{i=1}^m\frac{\eta}{\ell(z_{i-1},z_i)},\tag{1.9}$$
the infimum over nearest-neighbour paths of $T_\eta$. It is a pseudo-metric, $d(x,x')\le \ell_j^{-1}|x-x'|$
if the straight lattice path stays in layer $j$, and **each step costs $\eta/\ell(b)\le1$**.
P3 (2.4) (p. 37, read) defines $d(y,y')=\inf_\Gamma\sum_j\ell_j^{-1}|\Gamma\cap\Omega_j\cap\Omega_{j+1}^c|$ over paths $\Gamma$ joining
$y,y'$; our (1.9) differs only in the treatment of bonds straddling two layers and in using $\eta$-bonds; both are
within a factor $2$ and an additive $2d$ of each other on block centres. (UNCERTAIN: P3 says paths are "unions of
bonds of this lattice $\Lambda_j$"; if it means bonds of the lattice $T^{(j)}_{\ell_j}$ the cost of a bond is 1 and
$d_{P3}\asymp d_{(1.9)}$ with constants depending on $d$ only. No bound consumed depends on the choice.)
For blocks, $d$ between two points of one $j$-block is $\le d$ (the dimension) since the $\ell^1$-diameter of a block is $<d\ell_j$ and all of its
points lie in layer $j$. For $Z\subset T_\eta$, $d(x,Z)=\min_{z\in Z}d(x,z)$. The $\ell(x)$-independent
bound $d(y,y')\ge\varrho(|j-j'|-1)_+$ for $y\in\Lambda_j,y'\in\Lambda_{j'}$ (separation) is proved in Lemma 4.3.

### 1.5 Norms

For $f:\Omega_1\to\mathbb C^N$ (P2 (3.17), p. 621, read):
$$|f|_\sigma=\max_j\sup_{x\in\Omega_j\setminus\Omega_{j+1}}\ell_j^{\sigma}|f(x)|,\qquad
|f|_{(\alpha),\sigma}=\max_j\sup_{y\in\Lambda_j}\sup_{x\in\Delta(y),\,x'\in\tilde\Delta(y)}\frac{\ell_j^\sigma}{|x-x'|^{1-\alpha}}|f(x)-f(x')|.$$
Hence the condition "$|\alpha|_2<\gamma_1$" means $|\alpha(x)|<\gamma_1\ell(x)^{-2}$. $|\partial f|_1$ is the maximum over bonds
$b$ of $\ell(b_-)|\partial^\eta f(b)|$ with $\ell(b_-)$ the spacing at the lower endpoint (P2 does not say which endpoint; we
take the maximum over both endpoints, which is at least as strong). The weighted $L^2$ norms are
$\|\ell^{\sigma}f\|$. $\|\cdot\|_\infty$ is the sup norm on the lattice.

### 1.6 Where Balaban's conventions differ from ours

1. P2/P3 write $\Delta^\eta$ for the *negative* semidefinite operator ($-\Delta^\eta\ge0$); we follow.
2. P2 (1.5) uses weights $(L^j\eta)^d$ on $\Lambda_j$ for the multiplier term; we keep it, so $Q^*aQ$ has the block form (1.4).
3. $\alpha$ is used for three things: the Lagrange multiplier field (P2), the Hölder exponent (P2 (3.17), E3), and a
   number $O(M^{-1})$ in E3 §5 (ER-150). Below, $\alpha$ is the multiplier field; the Hölder exponent is $\theta\in(0,1)$.
4. P3 (3.10) uses $\gamma_0=\frac1{5d}L^{-2}$, E5 uses $\delta_0$, P2 uses $\gamma_1$ for the smallness of $|\alpha|_2$.
   We use $\varepsilon_0$ for the Agmon rate and $\gamma_1=\frac14$ for the allowed size of $|\alpha|_2$.
5. Constants in Balaban's cube bounds (P3 (2.5)) carry $e^{-\gamma_0d}$ with distances measured as in 1.4;
   P2's separation (1.1) and E5's (2.59) are the same condition in the form $\varrho=RM\ge R_0$.
6. The unit lattice has spacing 1; P4 writes the unit-lattice mass as $\nu_k$ (the fine-lattice mass is
   $\nu_kL^{-2k}$ in lattice units: P4 p. 687 prints "$\tfrac12\langle\phi,(-\Delta+\nu_kL^{-2k})\phi\rangle$" for the Gaussian
   density and "$\tfrac12\gamma_0\langle\psi',(-\Delta+\nu_k)\psi'\rangle$" for the bound after $k$ renormalization steps; read).
   In P9, $\nu_j=\nu L^{2j}$ is the mass in scale-$j$ lattice units and $k(\nu)$ is the first index with $\nu_k>\frac78L^{-2}$ (P4 p. 719).

---

## 2. What is consumed, precisely

Verified against the PDFs: P2 pp. 607–611, 621–629 (read, images); P3 pp. 36–40, 59–67 (read, images);
P4 pp. 686–687, 693–694, 710–711, 719–720 (read, images; cropped at 200 dpi where noted); P6 pp. 16–18,
29–30 and P7 pp. 506–507 and P9 pp. 517–519 (text layer); E5 p. 234 (read, image); D1 §§ before Lemma 30
(text layer). Not re-read: P3 pp. 46–48 and 55–56 (the $\lambda$-dependent items; moot at $\lambda=\infty$),
E3 §§1–5 (review only), E4, E5 outside p. 234.

"Uniform in" means: the constants depend on $d$ and $L$ only (and on a fixed Hölder exponent where
stated) and not on $k$, $\eta$, the volume, $\varrho$ (once $\varrho\ge R_0(d,L)$), the domains
$\Omega_j$, $a_k\in(\frac12,\frac32)$, $\nu\in[0,1]$, $\alpha$, or $x\ge0$.

**C1. P2 (3.22)–(3.47), pp. 621–627 (read).** The operator is $G(\alpha)$ of (1.6). What is used:
(i) analyticity of $G(\alpha)$ in $\alpha$ on $\{|\alpha|_2<\gamma_1\}$ by the Neumann series (3.22), with
the bounds (2.57) of [2(b)] "multiplied by 2" (P2 p. 622); (ii) for $f$ with $|f|_2<\infty$:
$$|G(\alpha)f|_0,\ |\partial G(\alpha)f|_1,\ |\Delta^{D}G(\alpha)f|_2\le B_0|f|_2,\qquad
|\partial G(\alpha)f|_{(\theta),2-\theta}\le C_\theta B_0|f|_2$$
(P2 (3.23), (3.46), (3.47)); (iii) in the proof of Prop. 3.1, the *products* $\phi_0\cdot G(\alpha_0)f$ and
$G(\alpha_0)f\cdot G(\alpha_0)g$ under $G^{-1}(\alpha_0)$ via the Leibniz formula (3.31)–(3.33): this uses
$|\nabla G f|_1$ and $|Gf|_0$ pointwise, and gives (3.34)–(3.38) in $|\cdot|_2$. **Check of the roadmap:** the
Hölder bound is *not* used in the fixed-point argument of P2 §3 (pp. 623–627 use only $|\cdot|_0$, $|\partial\cdot|_1$,
$|\Delta\cdot|_2$); it appears only in the conclusions (3.46)–(3.47), (1.15). It is consumed downstream only
through P1 (3.107), $|\partial^2\psi^{(j)}_k|<K_1C_{\alpha_1}(L^j\eta)^{2-\alpha_1}\varepsilon_k$ for "any constant $\alpha_1$,
$0<\alpha_1\le1$" (P1 p. 147, read), in the combination $\alpha_3=2(\gamma_0-\gamma)-\alpha_1>0$ with
$\gamma_0=\frac12$ ($d\ge3$; P1 p. 147 and ER-019). Therefore *one fixed exponent* $\theta=\alpha_1<\frac12$ suffices, and
the $\alpha^{-d-1}$ dependence of $C_\alpha$ (P2 p. 611) is never used (ER-027, ER-041 resolved: only a fixed exponent is
used; UNCERTAIN until the P1 document confirms the normalization of $\partial^2$ in (3.107): a second difference of
the block-spin field on the lattice of spacing $\ell_j$ or $\eta$). (iv) The global form: $|f|_2$ is a sup over layers; the
global bound follows from the layer-wise decay bound G-2 by summation over $y'$ (Lemma 4.4). Parameters: $a\in(\frac12,\frac32)$,
$\nu\in[0,1]$, $\lambda=\infty$, complex $\alpha$ with $|\alpha|_2<\gamma_1$ ($\gamma_1$ may be fixed as $\frac14$),
$\varrho\ge R_0$. At $\lambda=\infty$: unchanged.

**C2. P2 (3.48), p. 628 (read).** Positivity for real $\alpha$, $|\alpha|_2<c$: the second variation
$\frac12\langle\delta\phi,(-\Delta^D+Q^*aQ+\nu+\alpha)\delta\phi\rangle$ is positive; the $\lambda$-terms in (3.48) are nonnegative.
This is G-1(a) with real $\alpha$. At $\lambda=\infty$ the minimization is over $|\phi|=1$ and the second variation is the
same form on tangent directions; unchanged.

**C3. P2 (3.40)–(3.41), P3 (2.31)–(2.34): $|\lambda G(\lambda)f|\le O(1)|f|$** (P2 p. 626, read). *Disappears* at $\lambda=\infty$:
at $\lambda=\infty$ the linear operator in (3.39) is $1+R_2$ with $R_2$ small by (3.38), and (3.40) does not occur.

**C4. P3 (2.5), p. 37 (read).** For $\square_z$ not meeting $\partial\Omega_1$ and $|\alpha|_2<\gamma_1$:
$\ell_j\|\chi_{\Delta(y)}\partial G(\square_z,\alpha)\chi_{\Delta(y')}f\|+\|\chi_{\Delta(y)}G(\square_z,\alpha)\chi_{\Delta(y')}f\|\le B_0e^{-\gamma_0d(y,y')}\ell_{j'}^2\|\chi_{\Delta(y')}f\|$
(P3 states the left side with sup norms in the paper's typesetting and cites "[2b] (2.33)" = E5 (2.43), ER-042).
This is the cube version of G-2. It is consumed only by the walk expansion (C5), so see 4.6.

**C5. P3 (2.6)–(2.23), (2.52)–(2.56), pp. 38–41 (2.6)–(2.12) read.** Convergence of the walk expansion (2.8) in the
norms $|\cdot|_0,|\partial\cdot|_1,|\partial\cdot|_{(\theta),2-\theta},|\Delta\cdot|_2$ (stated in the sentence after (2.8), p. 38),
constants $2^{d+2}B_0c_1(d,\frac14\gamma_0)$ in (2.11), conditions $8dB_0c_1(2L+1)^dM^{-1}\le1$ (p. 39, ER-050). Consumer:
the localization expansion of $\delta\phi_k$ (P3 Prop. 2.1–2.3, hypotheses (H.5)). No Green's function bound beyond C1, C4 is
consumed; see 4.6 for the decision.

**C6. P3 (3.8)–(3.20), pp. 61–66 (read).** (i) The form bound (3.10): for a cube $\square\subset\Omega_k$ of $(k{+}1)$-blocks,
$\mathrm{Re}\,e(q)^{-1}\big(-\Delta^{\eta,N}_\square+[\dots]\big)e(q)\ge\frac13(-\Delta^{\eta,N}_\square)+\frac16a_{k+1}L^{-2}\ldots$ on $L^2(\square)$ with
$e(q;x')=e^{q\cdot x'}$, $|q|_\infty\le\frac1{5d}L^{-2}$, $|\alpha_0|<\frac1{12}a_{k+1}L^{-2}$, uniformly in $x\ge0$; (ii) the $L^2$ block bound (3.11) with
$B_0=15L^2/a_{k+1}$, $\gamma_0=\frac1{5d}L^{-2}$; (iii) the expansion (3.12), (3.15)–(3.20) of $C_x^{(k)}$, with the representation (3.9).
(iv) The operator $\lambda_kG_{k,x}(\lambda_k)$ has Hilbert-space norm $\le1$ and appears in (3.15). At $\lambda_k=\infty$
$\lambda_kG_{k,x}(\lambda_k)\to I$ strongly, and the constraint terms $(\phi_0^2-1+\alpha_0/\lambda_k)$ reduce to $(\phi_0^2-1)$.
**Correction to the roadmap:** (3.10) is a statement for an operator on a *cube with Neumann conditions*, in the
weight $e^{q\cdot x}$ with a *linear* exponent (Dimock's Lemma 30 pattern), and it is $L^2$ only. The
constants $\gamma_0=\frac1{5d}L^{-2}$ in (3.11) are in units where the cube has side $\sim L$; our rate $\varepsilon_0$ is dimensionless in the metric (1.9).
Here the gap is $L^{-2}$ per unit block because the effective operator lives at scale $\ell_{k+1}=L$, which is the same as G-1(a$'$) below.

**C7. P4 (2.23)–(2.25), (2.21)–(2.22), pp. 686–687 (read).** (i) $\Delta^{(k)}\ge$ (2.24)
$\frac12\langle\psi,\Delta^{(k)}\psi\rangle\ge\frac12a_k\|\psi\|^2-\frac12a_k^2\langle\psi,Q_kG_kQ_k^*\psi\rangle-O(|\alpha_{k+1}|)\|\psi\|^2$, with the first two terms $\ge\frac12\gamma_0\langle\psi,(-\Delta+\nu_k)\psi\rangle$ "uniformly in $k$" ("[2c]" = P1's reference to E3 (1.22); ER-058);
(ii) (2.25): $\frac12aL^{-2}\|Q\psi\|^2+\frac12\langle\psi,\Delta^{(k)}\psi\rangle\ge\frac12\gamma_0L^{-2}\|\psi\|^2$;
(iii) "the operator of this form has an exponentially decaying matrix with decay rate uniform in $k$" and the inverse $C^{(k)}$ is
exponentially decaying "by Sect. 5 of [3]" (= E3 §5, ER-058); (iv) in (2.22) the term $\big[\frac1{\lambda_k}+\phi_{k+1}\cdot G_k(\alpha_{k+1})\phi_{k+1}\big]^{-1}$ and its kernel decay ("analyzed in detail in [2]"; P4 p. 686).
At $\lambda=\infty$: the term $[\phi\cdot G\phi]^{-1}$ survives and needs the *weighted* $L^2$ bounds of $G$, $\partial G$ of G-2(a)
(Section 4.5, statement G-2(v)). The unit-lattice kernel of $Q_kGQ_k^*$ needs only the $L^2$ decay (Lemma 4.5), not pointwise bounds.

**C8. P4 (2.48)–(2.50), p. 693 (read).** $G_1^{-1}(\alpha_1)=-\Delta+aL^{-2}Q^*Q+\nu_0+\alpha_1\ge\gamma_0$ on $T_1$ for small $\alpha_1$, and the quadratic form (2.49)
$\langle\phi',[I-(1-\lambda_0^{-1/2})(\phi_1)_0\otimes(\phi_1)_0]G_1^{-1}(\alpha_1)[\dots]\phi'\rangle+\langle\phi',(1+2\alpha_1/\lambda_0)(\phi_1)_0\otimes(\phi_1)_0\phi'\rangle$ is $\ge\gamma_0\langle\phi',\phi'\rangle$.
At $\lambda_0=\infty$ it reads $P^\perp G_1^{-1}P^\perp+P$ with $P=(\phi_1)_0\otimes(\phi_1)_0$ and the bound holds with $\gamma_0\wedge1$. Needs G-1(c) (Section 3) and no decay beyond G-4 (the "(5.17)" localization of the inverse).

**C9. P4 (6.5), p. 719 (read).** $\Delta^{(k_1)}\ge\frac78\gamma_0L^{-2}$: from $\frac12\langle\psi',\Delta^{(k_1)}\psi'\rangle\ge\frac12\gamma_0\langle\psi',(-\Delta+\nu_{k_1})\psi'\rangle\ge\frac12\gamma_0\langle\psi',(-\Delta+\frac78L^{-2})\psi'\rangle$ since $\nu_{k_1}>\frac78L^{-2}$ by the definition of $k_1$ and $\alpha_{k+1}=0$. This is G-1(b) with $\alpha=0$ and $\nu\ge\frac78L^{-2}$.

**C10. P4 (5.11)–(5.14), pp. 710–711 (read at 200 dpi).** The Woodbury-type identities (5.12)
$I-aQGQ^*=(I+aQ(-\Delta+\nu)^{-1}Q^*)^{-1}$, $QG^2Q^*=(Q(-\Delta+\nu)^{-2}Q^*)(I+aQ(-\Delta+\nu)^{-1}Q^*)^{-2}$,
$QG(-\Delta+\nu)GQ^*=(Q(-\Delta+\nu)^{-1}Q^*)(I+aQ(-\Delta+\nu)^{-1}Q^*)^{-2}$ (the third line is as printed; our derivation in
G-6(d) gives the same), the Fourier symbols $f,g,h$ on the unit lattice with $u_m(q)=\prod_\mu\frac{e^{iq_\mu}-1}{\partial_\mu(q)}$ and the Taylor data (5.13): $f(0)=\frac\nu{a+\nu}$, $f'(0)=0$, $f''(0)=\frac{2a}{(a+\nu)^2}\big(1+\frac1{12}(1-L^{-2m})\nu-\nu^2c_1(\nu)\big)$, $g(0)=1/\nu$, $g''(0)=\dots$, $h(0)=1/\nu^2$, with $0<c_i(\nu)<\frac1{20}$,
$c_i(\nu)=\sum_{l\ne0}\frac{1}{2L^{2m}(1-\cos L^{-m}l)}\frac1{[2L^{2m}(1-\cos L^{-m}l)+\nu]^i}$. At $\lambda=\infty$ the $\lambda$-factors become 1 (the displayed (5.11) contains $\frac{a+\nu}{\lambda}$). Pure algebra and calculus
(G-5, G-6).

**C11. P6 Prop. 3.1 (3.5)–(3.6), p. 17 (read).** Lower bounds for the main action $\beta_{k+1}A^*_{k+1}(X,\mathbb B_{k+1};\psi,\phi)$ by $\gamma_0\sum_j\beta_j\frac12\sum_b|\partial^1\psi_j(b)|^2+\sum_j\beta_{j+1}\frac12\sum_b|\psi_{j+1}(b_+)-(Q\psi_j)(b_-)|^2$ for *arbitrary* configurations, with $\gamma_0=\frac1{7d+4}$ "for example" ($\gamma_0=\frac13$ for two neighbouring cubes), proved "several times before in various places" (P6 p. 17). **This is not a Green's function bound** (it is an inequality for the action with no propagator); it belongs to LF-1 (ER-094). Its proof is of the same type as G-1(b) (block Poincaré and $\|\partial^\eta\phi\|\ge\|\partial^{(j)}Q_j\phi\|$, Lemma 3.1 of Section 4.1) and is *not* covered by G-1..G-6; we record Lemma 4.1 below because it is the main tool, and leave (3.5)–(3.6) to the large-field document.

**C12. P6 p. 29–30 and P3 Prop. 3.1 (read for P3).** The operator $C^{(k)1/2}(\phi_0,\alpha_0,s)=\frac1\pi\int_0^\infty x^{-1/2}C^{(k)}_x\,dx$ (P3 (3.4), (3.22)) has the localization property and the bound
(3.24); P6 uses it "unchanged" with bounds uniform in $\Omega_{k+1}$. Needs: G-4 for each $C_x$ with $\int_0^\infty x^{-1/2}(\gamma_0+x)^{-1}dx<\infty$ and the $x$-uniform rate (G-4(a)); at $\lambda=\infty$ with $\phi_0$: G-2(v).

**C13. P7 (2.36)–(2.38), pp. 506–507 (read, text layer).** The variational problem (2.34) on a box $Z_0$ with $\mathrm{diam}_k(Z_0)<15$ and *no* mass ($\nu_k=0$): $\langle\delta\psi,\Delta^{(k)}\delta\psi\rangle\ge\gamma_0\langle\delta\psi,(-\Delta^1)\delta\psi\rangle-O(\delta)\|\delta\psi\|^2$ (2.37) (the form of P4 (2.24) with the generating set $\mathbb B_k(U_k)$ from P5 (2.27)), with $\langle\delta\psi,(-\Delta^1)\delta\psi\rangle\ge\sum_{b\subset Z_0}|\delta\psi(b_+)-\delta\psi(b_-)|^2+\sum_{x\in\partial(Z_0\cap T^{(k)}_1)}|\delta\psi(x)|^2$ and the Poincaré inequality $\ge\frac1{36}\|\delta\psi\|^2$ (2.38) ($|\Gamma_{x,x'}|\le7$), hence $\ge\frac{\gamma_0}{72}\|\delta\psi\|^2$. G-1(b) with $\nu=0$ plus the restriction of the form to functions supported in $Z_0$ (zero extension). The "7" and "36" are the arithmetic of a path argument with $|\Gamma|\le7$: $(|\Gamma|+1)(|\Gamma|+2)/2=36$ for $|\Gamma|=7$; this checks.

**C14. P9 (4.12)–(4.17), pp. 517–519 (read, text layer).** (a) $|C^{(j)}_{tr}|$ bounds and $|G_jQ_j^*(x,y)|$: $|\mathcal C_{k,tr}|\le O(1)\beta^{-1}e^{-\delta\sqrt\nu|x-x'|}(1+|x-x'|)^{-(d-2)}$ from $\sum_{j<k}\beta_j^{-1}e^{-\delta(\sqrt\nu+L^{-j})|x-y'|}$ (4.14) and $\beta_j^{-1}\le2L^{-j(d-2)}\beta^{-1}$, which uses, for the scale-$j$ unit lattice, kernel decay of $a_j^2G_jQ_j^*C^{(j)}_{tr}Q_jG_j$ at rate $\delta(\sqrt\nu+L^{-j})$ in original lattice units, uniformly in $\nu_j\in(0,1]$ (P9 p. 518: "$\sup_{\nu_j\in(0,1]}|G^{(j)}(\nu_j)|\le\dots$"); (b) continuity as $\nu\downarrow0$ at fixed $j$ and (4.15); (c) the decomposition (4.17) (from "[10]"). **Check of the roadmap:** the rate $\delta(\sqrt\nu+L^{-j})$ is a consequence of unit-scale decay at rate $2\delta$: for $j<k(\nu)$ one has $\nu_j=\nu L^{2j}\le\frac78L^{-2}$, hence $\sqrt\nu\le L^{-j}$ (our normalization in 1.6), so $\delta(\sqrt\nu+L^{-j})\le2\delta L^{-j}$. At $\lambda=\infty$: $\Delta^{(j)}_{lg}=a_j$ exactly (P9 (4.13): $\Delta_{lg}=\Delta_{tr}+a_j^2Q_jG_j(\lambda_j^{-1}+G_j)^{-1}G_jQ_j^*\to a_j-a_j^2Q_jG_jQ_j^*+a_j^2Q_jG_jQ_j^*$), so $C_{lg}^{(j)}=(a_j+aL^{-2}Q^*Q)^{-1}$ is local and $H_{j,11}=0$ in the sense of P9 p. 519 ($H_j=a_jG_jQ_j^*(I-h\otimes h)$ at $\lambda=\infty$).

**Missing from the roadmap's table (additions).**

**C15. P3 (3.15)–(3.17), p. 64 (read): $[\phi_0\cdot G_{k,x}(\alpha_0)\phi_0]^{-1}=\big[\frac1{\lambda_k}G_{k,x}^{-1}(\alpha_0)+G^{-1}_{k,x}(\alpha_0)(\phi_0\cdot G_{k,x}\phi_0)\big]^{-1}$ rewritten with $K_x(\phi_0)=2\nabla\phi_0\cdot\nabla+\Delta\phi_0-[\dots,\phi_0]$.** At $\lambda=\infty$ this is the only place where the Green's function enters through its *gradient* in the weighted $L^2$ norm: the operator $K_x(\phi_0)\cdot G_{k,x}\phi_0$ is small ($O(\delta_0)$) in weighted $L^2$ and the inverse of $\phi_0^2-K_x(\phi_0)G_{k,x}\phi_0$ is a convergent Neumann series. Covered by G-2(v).

**C16. P2 (3.25)–(3.27), p. 622–623 (read):** the expansion $G(\alpha_0+\delta\alpha)=G(\alpha_0)-G(\alpha_0)\delta\alpha\,G(\alpha_0)+G(\alpha_0)\delta\alpha\,G(\alpha_0)\delta\alpha\,G(\alpha_0+\delta\alpha)$ and the second-order bounds, covered by C1 and G-6(c).

**C17. P3 (3.1), p. 59 and P4 (2.50)/(5.17): locality of $\Delta^{(k)},C^{(k)}$ in the domain.** The dependence of $C^{(k)}$ on $(\phi_{k+1},\alpha_{k+1})$ restricted to a unit-lattice subdomain (P3 Prop. 3.1 last sentence). Covered by G-4(c) and G-2(vi).

**Summary of corrections to the roadmap table.** (a) C1: Hölder bound not used inside P2 §3; only a fixed exponent downstream via P1 (3.107). (b) C3, C6 as stated. (c) C11 is not a Green's function bound. (d) C7's kernel decay of $Q_kGQ_k^*$ needs only $L^2$ decay; the pointwise bounds are needed only for the fixed point in P2. (e) C14's $\sqrt\nu$ rate is not a separate estimate (confirms G-5 remark). (f) (3.10) of P3 carries a linear exponential weight on a Neumann cube, not a multiscale weight: the multiscale path metric is new (this document). (g) C2 is G-1(a) with real $\alpha$. (h) New items C15–C17.

---

## 3. The interface statements G-1 to G-6

Standing assumptions (A): $L\ge3$ integer; $\eta=L^{-n}$; domains as in 1.2 with separation (S) and $\varrho=RM\ge R_0(d,L)$
(a constant fixed in Lemma 4.3 and in G-2); $a_j$ as in (1.5), $a_k\in(\frac12,\frac32)$; $\nu\in[0,1]$; $\alpha:\Omega_1\to\mathbb C$ with $|\alpha|_2\le\gamma_1:=\frac14$; $\Omega_1\subset T_\eta$ possibly equal to $T_\eta$.
Letters $c,C,B$ denote constants depending only on $d$ and $L$ (and where stated on $\theta$); they never depend on $k,\eta$,
the volume, $\varrho$, the $\Omega_j$, $a_k$, $\nu$, $\alpha$, $x$, or on the points $y,y'$.

**G-1 (coercivity).**

(a) *Multiscale coercivity.* For all $u:\Omega_1\to\mathbb C$,
$$\mathrm{Re}\langle u,H_D(\alpha)u\rangle\ \ge\ \tfrac12\|\partial^\eta\tilde u\|^2+\tfrac14\|\ell^{-1}u\|^2 .$$
In particular $H_D(\alpha)$ is invertible, $\|\ell^{-1}G_D(\alpha)f\|\le4\|\ell f\|$ and, for $u=G_D(\alpha)f$, $\|\partial^\eta\tilde u\|^2\le2\|\ell f\|\|\ell^{-1}u\|\le8\|\ell f\|^2$.
This holds with $\nu\ge0$ arbitrary; the same estimate holds for the Neumann-bracketed operators of P3 (2.3) (each term below is a sum over blocks and bonds are only dropped).

(a$'$) *The $x$-variant.* For $G_{k,x}(\alpha_0)$ of (1.7), $\nu_k\ge0$, $x\ge0$, $|\alpha_0|\le\frac1{12}a_{k+1}L^{-2}$ (this is the P3 hypothesis (3.10), read) on $\Omega_{k+1}$ and $|\alpha_0|_2\le\frac14$ on $\Omega_{k+1}^c$:
$\mathrm{Re}\langle u,H_{k,x}(\alpha_0)u\rangle\ge c_1'\big(\|\partial\tilde u\|^2+\|\ell^{-1}u\|^2\big)$, with $c_1'>0$ depending only on $d,L$ and a lower bound for $a_{k+1}$, **uniformly in $x\ge0$**.

(b) *Unit-lattice coercivity.* For $\psi:T^{(k)}_1\to\mathbb C$ and $|\alpha(x)|\le\theta_0$ on $\Omega_k$ (with $\theta_0\le\frac1{16}$) and $|\alpha|_2\le\frac1{16}$ elsewhere,
$$\mathrm{Re}\langle\psi,\Delta^{(k)}(\mathbb B_k;\alpha)\psi\rangle\ \ge\ \gamma_0\,\langle\psi,(-\Delta^1+\nu_k)\psi\rangle-4\theta_0\|\psi\|^2,\qquad\gamma_0=\frac1{2(8d+5)}\ ;$$
for real $\alpha$, $0\le\Delta^{(k)}\le a_k$, and for $\alpha=0$ in the single-scale case $\langle\psi,\Delta^{(k)}\psi\rangle\le C_d\langle\psi,(-\Delta^1+\nu_k)\psi\rangle$ (see 4.1). Consequently
$aL^{-2}Q^*Q+\Delta^{(k)}\ge\gamma_0'L^{-2}-4\theta_0$ (P4 (2.25), with $\gamma_0'=\gamma_0$),
$-\Delta^1+aL^{-2}Q^*Q+\nu_0+\alpha_1\ge\frac14L^{-2}$ for $|\alpha_1|\le\frac14L^{-2}$ (P4 (2.49)),
$\Delta^{(k)}\ge\gamma_0\nu_k-4\theta_0$ (C9 with $\nu_k\ge\frac78L^{-2}$), and, for $\nu_k=0$, $\theta_0=0$ and $\psi$ supported in a lattice box $Z_0$ of $\ell^1$-diameter $\le14$ (zero extension, Dirichlet outside), $\langle\psi,\Delta^{(k)}\psi\rangle\ge\frac{\gamma_0}{36}\|\psi\|^2$ (C13; Poincaré constant per P7 (2.38)).

(c) The consequences needed by P4 (C8): the three statements just listed.

*Constants.* $\gamma_0$ of (b): the explicit value $\frac1{2(8d+5)}$ is obtained in 4.1; Balaban's $\gamma_0$ is nonexplicit.

**G-2 (weighted Green's function bounds).** Under (A), let $y\in\Lambda_j$, $y'\in\Lambda_{j'}$ and $f:\Omega_1\to\mathbb C$ with $\operatorname{supp}f\subset\Delta(y')$, and $u=G_D(\alpha)f$. There are $\varepsilon_0=\varepsilon_0(d)>0$, $R_0(d,L)$, $B_0(d,L)$ and, for each $\theta\in(0,1)$, $B_\theta(d,L,\theta)$ such that, with $\gamma_0=\varepsilon_0/2$:

(i) ($L^2$ block bound, P3 (3.11).) 
$$\ell_j\|\chi_{\Delta(y)}\partial^\eta u\|+\|\chi_{\Delta(y)}u\|\le B_0e^{-\gamma_0d(y,y')}\ell_{j'}^{2}\,\|f\|\qquad(\text{the }L^2\text{ norms with weights }\eta^d\text{ throughout}).$$
(ii) (Pointwise, P3 (2.5) and E5 (2.67).) For $x\in\Delta(y)$:
$$|u(x)|+\ell_j\max_{b\ni x}|\partial^\eta u(b)|+\ell_j^2|(\Delta^{D,\eta}_{\Omega_1}u)(x)|\le B_0\,e^{-\gamma_0d(y,y')}\,\ell_{j'}^2\,\|f\|_\infty .$$
(iii) (Hölder, fixed exponent.) For $\theta\in(0,1)$, $x\in\Delta(y)$, $x'\in\tilde\Delta(y)$, $x\ne x'$ (and the bond differences taken as in 1.5):
$$\frac{\ell_j^{2-\theta}}{|x-x'|^{1-\theta}}\max_{b\ni x,\ b'\ni x'}|\partial^\eta u(b)-\partial^\eta u(b')|\le B_\theta e^{-\gamma_0d(y,y')}\ell_{j'}^2\|f\|_\infty,$$
with $b,b'$ bonds in the same direction $\mu$. (Only one fixed $\theta$ is consumed.)
(iv) (Global form, P2 (3.46), C1.) For $f$ with $|f|_2<\infty$ and every $\theta$:
$|Gf|_0+|\partial Gf|_1+B_\theta^{-1}|\partial Gf|_{(\theta),2-\theta}+|\Delta^DGf|_2\le B_1|f|_2$ with $B_1=B_1(d,L,\theta)$.
(v) (Constraint sandwich, needed at $\lambda=\infty$; C7(iv), C15.) Let $\phi_0:\Omega_1\to\mathbb C^N$ with $\frac12<|\phi_0|<\frac32$, $|\phi_0^2-1|<\delta_0$, $|\partial\phi_0|_1<\delta_0$, $|\Delta\phi_0|_2<\delta_0$ (P3 (3.2), P2 (3.21)) and $\delta_0\le\delta_*(d,L)$. Then $\phi_0\cdot G_D(\alpha)\phi_0$ is invertible on $\ell^2(\Omega_1;\mathbb C)$ and the operator
$$\Pi=G_D(\alpha)\,\phi_0\,[\phi_0\cdot G_D(\alpha)\phi_0]^{-1}\,\phi_0\cdot G_D(\alpha)$$
satisfies, for $f$ supported in $\Delta(y')$, $\|\chi_{\Delta(y)}\Pi f\|\le B_0'e^{-\gamma_0'd(y,y')}\ell_j\ell_{j'}\|f\|$ and $\ell_j\|\chi_{\Delta(y)}\partial\Pi f\|\le\dots$ (same right side). Moreover $\mathcal S:=(\phi_0\cdot G\phi_0)^{-1}$ equals $(\phi_0^2-K(\phi_0)G\phi_0)^{-1}G^{-1}(\alpha)$ with $K(\phi_0)=2\nabla\phi_0\cdot\nabla+\Delta\phi_0-[Q^*aQ,\phi_0]$ and $\|\ell\,e^{\gamma d(\cdot,y')}K(\phi_0)G\phi_0f\|\le c\delta_0\|\ell e^{\gamma d}f\|$. The same holds for $G_{k,x}$ in place of $G_D$, uniformly in $x\ge0$.
(vi) (Locality and analyticity in $\alpha$.) For $\alpha,\alpha'$ as in (A), $Z\subset\Omega_1$ with $\alpha=\alpha'$ off $Z$, and sets $Y,Y'$ of blocks:
$\|\chi_{\Delta(y)}(G(\alpha)-G(\alpha'))\chi_{\Delta(y')}\|_{L^2\to L^2}\le B_0\ell_j\ell_{j'}\,e^{-\gamma_0'(d(y,Z)+d(y',Z))}$. For fixed data, $\alpha\mapsto G_D(\alpha)$ is a rational function of the finitely many values of $\alpha$, analytic on the polydisc $\{|\alpha|_2<\frac14\}$, with the bounds (i)–(iv) uniform on it.
(vii) For the $x$-variant $G_{k,x}(\alpha_0)$ of (1.7): (i)–(iv) hold with constants uniform in $x\ge0$ (the multiscale structure being that of $\mathbb B_k$ on $\Omega_{k+1}^c$ and the two block structures $Q_k^*Q_k$, $P_{k+1}$ on $\Omega_{k+1}$).

*Remark on $B_0$ versus P2's constant.* Our $B_1$ is not P2's $B_0$ and $B_\theta$ is not $O(\theta^{-d-1})$; only existence with a fixed $\theta$ is claimed (see C1).

**G-3 (random-walk representation; decision).** We do not state G-3 as an interface: no consumer in C1–C14 needs it once G-2 is available (Section 4.6). What replaces it is G-2(vi), the resolvent identity of G-6(c), and the lemma "locality for domain-restricted data" of 4.6. If the localization document keeps the walk expansion of P3 (2.8)–(2.13), (3.12)–(3.20), then G-3 is the statement: with the cover $\{\square_z\}$ and partition of unity (P3 (2.2)), $G(\alpha)=\sum_\omega h_{\omega_0}G(\square_{\omega_0})hK\cdots$ converges absolutely in the norms of G-2 with the bound (P3 (2.11)); proof: G-2 for cubes (Neumann bracketing; no new idea) plus the discrete Leibniz rule (P3 (2.6)–(2.7)).

**G-4 (unit-lattice operators; E3 §5 as an interface).** Let $X$ be $T^{(k)}_1$, $\mathbb Z^d$ or a finite subset, $\mathbb C^N$-valued fields (the kernel may carry spin indices: $A(x,x')\in\mathrm{End}(\mathbb C^N)$, norms operator norms). Let $A$ be an operator on $\ell^2(X)$ with kernel $A(x,x')$ (not necessarily Hermitian) such that
$$\mathrm{Re}\langle u,Au\rangle\ge\gamma_0\|u\|^2,\qquad|A(x,x')|\le c_0e^{-\delta_0|x-x'|}\quad(\ell^1\text{ distance on the unit lattice}).$$
Then for all $\Lambda\subset X$, $x\ge0$, $x_1,x_2\in\Lambda$, with $A_\Lambda=\chi_\Lambda A\chi_\Lambda$:
(a) $|(A_\Lambda+x)^{-1}(x_1,x_2)|\le\frac{2}{\gamma_0+x}\,e^{-\mu|x_1-x_2|}$, $\mu=\mu(\gamma_0,c_0,\delta_0,d)>0$ independent of $x$ and $\Lambda$ (Combes–Thomas);
(b) (domain difference, E3 (5.8)) for $\Lambda'\subset\Lambda$ and $x_1,x_2\in\Lambda'$: $|(A_\Lambda+x)^{-1}(x_1,x_2)-(A_{\Lambda'}+x)^{-1}(x_1,x_2)|\le\frac{C}{\gamma_0+x}\,e^{-\mu'(d(x_1,\Lambda\setminus\Lambda')+d(x_2,\Lambda\setminus\Lambda'))}$;
(c) (perturbation, E3 (5.10); localization (5.17), used in P4 (2.50)) if $B$ is another operator with $\mathrm{Re}\langle u,(A+B)u\rangle\ge\gamma_0\|u\|^2$, $|B(x,x')|\le c_0e^{-\delta_0|x-x'|}$, supported in $X'\times X'$, then for $x_1,x_2\in\Lambda$: $|(A_\Lambda+B_\Lambda+x)^{-1}(x_1,x_2)-(A_\Lambda+x)^{-1}(x_1,x_2)|\le\frac C{(\gamma_0+x)^2}e^{-\mu'(d(x_1,X')+d(x_2,X'))}$.
The hypotheses are supplied by G-1(b) and the $L^2$ decay of Lemma 4.5: $A=\Delta^{(k)}+aL^{-2}Q^*Q$ has $\mathrm{Re}A\ge\frac12\gamma_0L^{-2}-4\theta_0$ and kernel decay with $c_0,\delta_0$ depending on $d,L$ only. The constants depend only on $\gamma_0,c_0,\delta_0,d$.

**G-5 (translation-invariant one-scale operators; P9, P4 §5).** On $T^{(j)}_{\ell_j}$ for tori of any volume and on $\mathbb Z^d$, with $G_j=(-\Delta^\eta+a_jQ_j^*Q_j+\nu_j)^{-1}$, $a_j\in(\frac12,\frac32)$, $\nu_j\in[0,1]$ (mass in unit-lattice units), $\Delta_{tr}^{(j)}=a_j-a_j^2Q_jG_jQ_j^*$, $C_{tr}^{(j)}=(\Delta_{tr}^{(j)}+aL^{-2}Q^*Q)^{-1}$:
(a) $|a_jG_jQ_j^*(x,y)|\le c\,e^{-\delta|x-y|}$ (unit-lattice distance from the block centre $y$), $|C_{tr}^{(j)}(y,y')|\le ce^{-\delta|y-y'|}$ uniformly in $j$, the volume, $\nu_j\in[0,1]$, with $c,\delta>0$ depending on $d,L$ only;
(b) $\nu_j\mapsto G_jQ_j^*$, $C^{(j)}_{tr}$ are Lipschitz on $[0,1]$ in the kernel norm of (a) (hence continuity as $\nu\to0$, P9 (4.15)); infinite-volume limits exist (strong limits of tori) and satisfy (a);
(c) the identities (5.12) of P4 and the symbol data (5.13): see G-6(d) and 4.4;
(d) consequently $\sum_{j<k(\nu)}\beta_j^{-1}|a_j^2G_jQ_j^*C^{(j)}_{tr}Q_jG_j(x,y)|$ obeys the bound of P9 (4.14), which is the content of P9's first-part computation; no separate estimate at rate $\sqrt\nu$ is needed (Section 2, C14).

**G-6 (exact identities).** (a) *Schur complement:* for $\alpha$ with $G_D(\alpha)$ defined, $\langle\psi,\Delta^{(k)}\psi\rangle=a_k\|\psi-Q_k\phi\|^2+\langle\phi,\tilde H\phi\rangle$ with $\phi=G_Da_kQ_k^*\psi$ and $\tilde H=H_D-a_kQ_k^*Q_k$, in particular (real symmetric case) $\langle\psi,\Delta^{(k)}\psi\rangle=\min_\phi[\dots]$.
(b) *The $x$-variant:* $G_{k,x}=(\tilde H+Q_k^*S_xQ_k)^{-1}$ with $S_x=a_k-a_k^2A_{k,x}$, and $C^{(k)}_x=A_{k,x}+a_k^2A_{k,x}Q_kG_{k,x}Q_k^*A_{k,x}$ (the unconstrained part of P3 (3.9); with the constraint the third term of (3.9) is $-a_k^2A_{k,x}Q_kG_{k,x}\phi_0[\phi_0G_{k,x}\phi_0]^{-1}\phi_0G_{k,x}Q_k^*A_{k,x}$).
(c) *Resolvent and domain identities:* $G(\alpha+\delta\alpha)=G(\alpha)-G(\alpha)\delta\alpha\,G(\alpha+\delta\alpha)$; for $\Lambda'\subset\Lambda$, $G_\Lambda-\iota G_{\Lambda'}\pi=-G_\Lambda(1-\chi_{\Lambda'})A\chi_{\Lambda'}G_{\Lambda'}$.
(d) *Woodbury:* P4 (5.12) (three lines) for translation-invariant $G=(A_0+aQ^*Q)^{-1}$, $A_0=-\Delta+\nu$, and the symbol formulas of P4 (5.13).
(e) *Leibniz and commutators:* $\Delta(fg)=f\Delta g+g\Delta f+\sum_{b\in st(x)}\partial f(b)\partial g(b)$ and $K(h)=2\nabla h\cdot\nabla+\Delta h-[Q^*aQ,h]$ (P2 (3.31)–(3.33), P3 (2.6), (3.13)).
(f) *Free flow:* $a_j(1-L^{-2j})$ is independent of $j\le k$ (from (1.4)); the Gaussian composition formula E3 (3.8) is not consumed by the Green's function interfaces and is left to the document on the free flow.

Items whose proof is given in Section 4: G-1, G-2(i)–(vii) except as noted, G-4, G-6. G-5(a),(b) are reduced to G-2(i), G-4 and the translation-invariant structure (4.4). Section 4.5 contains the detailed plan for the pointwise parts.


---

## 4. Proofs

Notation in this section: $d$ is the dimension; the path metric of 1.4 is written $d(\cdot,\cdot)$ with two arguments (no clash is
intended). $\varrho=RM$. All constants named $c,C$ depend on $d,L$ only.

### 4.1 G-1: coercivity

**Lemma 4.1 (block Poincaré).** Let $B$ be a cube of $n^d$ lattice points of spacing $\eta$, $\ell=n\eta$, and let $\partial u$ range over the bonds
inside $B$. Then $\|u-P_Bu\|_B^2\le\frac{\ell^2}8\|\partial u\|^2_B$, i.e. $\|\partial u\|_B^2\ge8\ell^{-2}\|u-P_Bu\|_B^2$.
*Proof.* One dimension: for $u_0,\dots,u_{n-1}$ with $g_m=u_{m+1}-u_m$,
$\sum_i|u_i-\bar u|^2=\frac1n\sum_{i<i'}|u_i-u_{i'}|^2$ and by Cauchy–Schwarz $|u_i-u_{i'}|^2\le(i'-i)\sum_{m=i}^{i'-1}|g_m|^2$. For fixed $m$, $\sum_{i\le m<i'}(i'-i)=\frac n2ab$ with
$a=m+1$, $b=n-a$ (the mean of $i'-i$ over the rectangle is $\frac{a+b}2=\frac n2$), and $ab\le n^2/4$. Hence $\sum_i|u_i-\bar u|^2\le\frac{n^2}8\sum_m|g_m|^2$. In $d$ dimensions, with $E_\mu$ the average over the $\mu$-th coordinate and
$u-P_Bu=\sum_\mu(E_{<\mu}u-E_{\le\mu}u)$ (orthogonal telescoping, where $E_{\le\mu}$ averages over the first $\mu$ coordinates), $\|u-P_Bu\|^2=\sum_\mu\|E_{<\mu}u-E_{\le\mu}u\|^2$, and each term is at most the one-dimensional
variance in direction $\mu$ of $E_{<\mu}u$, hence $\le\frac{n^2}8\|\partial_\mu E_{<\mu}u\|^2\le\frac{n^2}8\|\partial_\mu u\|^2$ (averaging does not increase the energy in an
untouched direction, by Jensen). Multiply by $\eta^2$. The sharp constant would be $\pi^2$; the roadmap's "$4$" (printed above P3 (3.10), "$c(-\Delta^N)+c'Q_j^*Q_j\ge\ell^{-2}\min\{4c,c'\}$") is implied. $\square$

**Lemma 4.2 (gradient of block averages).** For $\phi$ on $T_\eta$ (zero-extended, all bonds) and $Q_k:T_\eta\to T_1^{(k)}$, $\|\partial^1Q_k\phi\|^2\le\|\partial^\eta\phi\|^2$, and $\|Q_k\phi\|^2\le\|\phi\|^2$.
*Proof.* For $y$ and a unit direction $e_\mu$, $Q_k\phi(y+e_\mu)-Q_k\phi(y)=L^{-kd}\sum_{x\in B(y)}[\phi(x+e_\mu)-\phi(x)]$ and $\phi(x+e_\mu)-\phi(x)=\eta\sum_{m=0}^{L^k-1}\partial^\eta_\mu\phi(x+m\eta e_\mu)$. By Cauchy–Schwarz (the $L^k\eta=1$) $|\phi(x+e_\mu)-\phi(x)|^2\le L^{-k}\sum_m|\partial_\mu^\eta\phi(x+m\eta e_\mu)|^2$, and Jensen over $x\in B(y)$ gives
$|\partial^1_\mu Q_k\phi(y)|^2\le L^{-kd}\sum_{x\in B(y)}L^{-k}\sum_m|\partial^\eta_\mu\phi(x+m\eta e_\mu)|^2$. Summing over $y$ every point $x'=x+m\eta e_\mu$ is hit exactly $L^k$ times, so $\sum_y|\partial_\mu^1Q_k\phi|^2\le L^{-kd}\sum_{x'}|\partial_\mu^\eta\phi(x')|^2$, i.e. $\|\partial^1_\mu Q_k\phi\|^2\le\|\partial^\eta_\mu\phi\|^2$ (weight $1$ per site on the unit lattice, $\eta^d=L^{-kd}$ on $T_\eta$). The second claim is Jensen. $\square$

**Proof of G-1(a).** Let $u:\Omega_1\to\mathbb C$, $\tilde u$ its zero extension. The bonds of $T_\eta$ inside the blocks of the partition of $\Omega_1$ into layer blocks form a subset of all bonds, so $\|\partial\tilde u\|^2\ge\frac12\|\partial\tilde u\|^2+\frac12\sum_B\|\partial u\|^2_B$, and by Lemma 4.1 on a layer-$j$ block ($\ell=\ell_j$), $\frac12\|\partial u\|_B^2\ge4\ell_j^{-2}\|u-P_Bu\|_B^2$. With (1.4),
$$\mathrm{Re}\langle u,Hu\rangle\ge\tfrac12\|\partial\tilde u\|^2+\sum_B\ell_B^{-2}\big[4\|u-P_Bu\|_B^2+a_B\|P_Bu\|_B^2\big]+\nu\|u\|^2-\|\alpha\|_{\ell^2\text{-weight}},$$
the last term being $\le\gamma_1\|\ell^{-1}u\|^2$. Since $a_B\ge\frac12$ by (1.5), the bracket is $\ge\frac12\|u\|_B^2$. Thus $\mathrm{Re}\langle u,Hu\rangle\ge\frac12\|\partial\tilde u\|^2+(\frac12-\gamma_1)\|\ell^{-1}u\|^2$; with $\gamma_1=\frac14$ this is the claim. Invertibility: $H$ is a finite matrix and $\mathrm{Re}\langle u,Hu\rangle>0$ for $u\ne0$. If $Hu=f$: $\frac14\|\ell^{-1}u\|^2\le\mathrm{Re}\langle u,f\rangle\le\|\ell^{-1}u\|\|\ell f\|$, so $\|\ell^{-1}u\|\le4\|\ell f\|$ and $\|\partial\tilde u\|^2\le2\|\ell^{-1}u\|\|\ell f\|\le8\|\ell f\|^2$. $\square$

**G-1(a$'$).** $Q_k^*S_xQ_k=s_1P_k+(s_2-s_1)P_{k+1}$ with $s_1=\frac{a_kx}{a_k+x}$, $s_2-s_1=\frac{a_k^2aL^{-2}}{(a_k+x)(a_k+aL^{-2}+x)}\ge0$, $s_2=\frac{a_k(x+aL^{-2})}{a_k+x+aL^{-2}}$ ($P_{k+1}=Q_k^*Q^*QQ_k$ is the projection onto $L$-block constants, $P_{k+1}\le P_k$). For $0\le x\le a_k/8$: $S_x\ge s_2P_{k+1}$ and $s_2\ge\frac23aL^{-2}$; on blocks of side $L$ Lemma 4.1 gives
$\frac12\|\partial u\|_B^2+\frac23aL^{-2}\|P_Bu\|_B^2\ge cL^{-2}\|u\|_B^2$. For $x>a_k/8$: $S_x\ge\min(s_1,s_2)P_k\ge\frac{a_k}{12}P_k$ and the gap is at unit scale. In both cases the multiscale argument of G-1(a) gives
$\mathrm{Re}\langle u,H_{k,x}u\rangle\ge\frac12\|\partial\tilde u\|^2+c\,\|\ell^{-1}u\|^2-|\alpha_0|\text{-term}$, and $|\alpha_0|\le\frac1{12}a_{k+1}L^{-2}$ is absorbed. The constant depends on $d$ only through nothing and on $L$, $\underline a$. (For P3 (3.10) with a linear weight $e^{q\cdot x}$ this is an alternative proof.) $\square$

**Proof of G-1(b).** Let $\psi$ be supported in $\Lambda_k$ (zero extension to $T^{(k)}_1$) and $\phi=G_Da_kQ_k^*\psi$. By G-6(a) (proved in 4.7),
$\mathrm{Re}\langle\psi,\Delta^{(k)}\psi\rangle=a_k\|\psi-Q_k\phi\|^2_{\Lambda_k}+\mathrm{Re}\langle\phi,\tilde H\phi\rangle$ with $\tilde H=-\Delta^D+\sum_{j<k}(\text{layer }j\text{ block terms})+\nu+\alpha$. Allocate
$\|\partial\tilde\phi\|^2=\frac12\|\partial\tilde\phi\|^2+\frac12\|\partial\tilde\phi\|^2$. On blocks of layers $j<k$: $\frac12\|\partial\phi\|_B^2+a_j\ell_j^{-2}\|P_B\phi\|_B^2\ge\frac12\ell_j^{-2}\|\phi\|^2_B$ and $|\alpha|\le\frac1{16}\ell^{-2}$, so these blocks contribute $\ge\frac7{16}\ell_j^{-2}\|\phi\|_B^2\ge3\|\phi\|_B^2$ since $\ell_j\le L^{-1}$ ($j<k$, $\ell_k=1$). On $\Omega_k$ (unit blocks $B$, $\ell=1$): $\frac12\|\partial\phi\|_B^2\ge4\|\phi-P_B\phi\|^2$ and $\theta_0\|\phi\|_B^2\le2\theta_0\|\phi-P_B\phi\|^2+2\theta_0\|P_B\phi\|_B^2$, the first part is absorbed, the second is $2\theta_0\|Q_k\phi\|^2_{\Lambda_k}\le4\theta_0(\|\psi-Q_k\phi\|^2+\|\psi\|^2)$; since $4\theta_0\le\frac14\le\frac{a_k}2$:
$$\mathrm{Re}\langle\psi,\Delta^{(k)}\psi\rangle\ge\tfrac12a_k\|\psi-Q_k\phi\|^2_{\Lambda_k}+3\|\phi\|^2_{\Omega_1\setminus\Omega_k}+\tfrac12\|\partial\tilde\phi\|^2+\nu\|\phi\|^2-4\theta_0\|\psi\|^2.$$
Put $\bar\psi=Q_k\tilde\phi$ on the whole unit lattice $T^{(k)}_1$ (note $\Omega_k$ is a union of unit blocks, so unit blocks outside $\Lambda_k$ meet $\tilde\phi$ only in $\Omega_1\setminus\Omega_k$ or in the zero extension). Lemma 4.2 gives $\|\partial^1\bar\psi\|\le\|\partial\tilde\phi\|$, $\|\bar\psi\|\le\|\phi\|$ (blockwise, so also on the complement of $\Lambda_k$), and $\psi=0$ off $\Lambda_k$, so
$\frac12a_k\|\psi-Q_k\phi\|_{\Lambda_k}^2+3\|\phi\|^2_{\Omega_1\setminus\Omega_k}\ge\frac14\|\psi-\bar\psi\|^2_{T^{(k)}_1}$. Therefore
$$\mathrm{Re}\langle\psi,\Delta^{(k)}\psi\rangle+4\theta_0\|\psi\|^2\ge\min_{\bar\psi}\Big[\tfrac14\|\psi-\bar\psi\|^2+\langle\bar\psi,T\bar\psi\rangle\Big],\qquad T=\tfrac12(-\Delta^1)+\nu .$$
The minimum is $\langle\psi,T(1+4T)^{-1}\psi\rangle$; since $T\le2d+1$ (as $\|-\Delta^1\|\le4d$), $T(1+4T)^{-1}\ge T/(8d+5)$, and $\ge\frac1{2(8d+5)}(-\Delta^1+\nu)$. So $\gamma_0=\frac1{2(8d+5)}$ in G-1(b) (the statement of Section 3 is to be read with this value; Balaban's $\gamma_0$ is non-explicit). The subsidiary claims:
(1) $aL^{-2}Q^*Q+\Delta^{(k)}\ge\gamma_0'L^{-2}-4\theta_0$: on $L$-blocks of the unit lattice Lemma 4.1 with $\ell=L$, $\eta=1$ gives $\langle\psi,-\Delta^1\psi\rangle\ge8L^{-2}\|\psi-Q^*Q\psi\|^2$, so $\gamma_0\langle\psi,-\Delta^1\psi\rangle+aL^{-2}\|Q\psi\|^2\ge\min(8\gamma_0,a)L^{-2}\|\psi\|^2\ge\gamma_0L^{-2}\|\psi\|^2$ (since $8\gamma_0<\frac12<a$).
(2) $-\Delta^1+aL^{-2}Q^*Q+\nu_0+\alpha_1\ge\frac14L^{-2}$ for $|\alpha_1|\le\frac14L^{-2}$: with $a>\frac12$, $-\Delta^1+aL^{-2}P\ge\min(8,a)L^{-2}\ge\frac12L^{-2}$ (Lemma 4.1 on $L$-blocks).
(3) $\Delta^{(k)}\ge\gamma_0\nu_k-4\theta_0$: use $-\Delta^1\ge0$.
(4) For the Dirichlet box: apply the main inequality to $\psi$ supported in $Z_0$, with $\nu=0=\theta_0$: $\mathrm{Re}\langle\psi,\Delta^{(k)}\psi\rangle\ge\gamma_0\|\partial^1\psi\|^2_{\text{all bonds of }T_1^{(k)}}$ (zero extension) and the Poincaré inequality for a box with Dirichlet boundary values (path argument of P7 (2.38): $|\psi(x)|^2\le(|\Gamma|+1)\big(\sum_{b\in\Gamma}|\partial\psi|^2+|\psi(x')|^2\big)$ with $x'\in\partial$ and $|\Gamma|\le7$), giving $\ge\frac1{36}\|\psi\|^2$ as printed.
Upper bound for $\alpha=0$, single scale: with the multilinear interpolant $I$ from $T_1^{(k)}$ to $T_\eta$ one has $\|\partial^\eta I\psi\|^2\le C_d\|\partial^1\psi\|^2$, $\|I\psi\|^2\le C_d\|\psi\|^2$, $\|\psi-Q_kI\psi\|^2\le C_d\|\partial^1\psi\|^2$, so $\langle\psi,\Delta^{(k)}\psi\rangle\le C_d\langle\psi,(-\Delta^1+\nu_k)\psi\rangle$ by the variational formula; this gives the "matching upper bound" of the roadmap and is not consumed by any item of Section 2. $\square$

(The identification $\ge\gamma_0\langle\psi,(-\Delta+\nu_k)\psi\rangle$ for P4 (2.24) was claimed "from [2c]" = E3 (1.22); our proof does not use E3. It also removes the need for the Fourier-analytic Neumann Gaussian bound of E3 §4.)

### 4.2 G-2 step 1: $L^2$ decay by an Agmon argument with the multiscale metric

**Lemma 4.3 (geometry).** Let $y\in\Lambda_j,y'\in\Lambda_{j'}$ (or any points of layers $j,j'$) and $\varrho\ge2$. Then (a) $d(y,y')\ge(\varrho-1)(|j-j'|-1)_+$; (b) if $x,x'$ lie in one $j$-block, $d(x,x')\le d$ (dimension); (c) $|d(x,y')-d(x',y')|\le\eta/\ell(b)\le1$ for a bond $b=(x,x')$; (d) for $j\ge2$ every $x$ in layer $j$ has $\mathrm{dist}_{\ell^1}(x,\Omega_1^c)>\varrho\,\ell_{j-1}$ and the ball $\{z:|z-x|\le2\varrho'\ell_j/L\}$ lies in layers $j-1,j,j+1$ and inside $\Omega_1$ when $2\varrho'\le\varrho$.
*Proof.* (a) Say $j<j'$ and fix $i$ with $j<i<j'$. Then $y\in\Omega_{j+1}^c\subset\Omega_i^c$ and $y'\in\Omega_{j'}\subset\Omega_{i+1}$. On a bond path from $y$ to $y'$ let $z_a$ be the last point in $\Omega_i^c$ and $z_b$ the first later point in $\Omega_{i+1}$; the points strictly between lie in layer $i$. By (S) the path from $z_a$ to $z_b$ has $m$ bonds with $m\eta\ge\mathrm{dist}(\Omega_i^c,\Omega_{i+1})>\varrho\ell_i$; a bond with one endpoint in layer $i$ and the other in a layer $<i$ has $\ell(b)=\ell_i$, a bond between layers $i$ and $i+1$ has $\ell(b)=\ell_{i+1}$, and only the last bond of the segment can be of the latter type. So the segment costs at least $(m-1)\eta/\ell_i\ge\varrho-1$. Segments for distinct $i$ are disjoint, so $d(y,y')\ge(\varrho-1)(j'-j-1)$. (b) The straight path inside the block has $\ell^1$-length $<d\ell_j$ and all points in layer $j$. (c) The triangle inequality. (d) A path from $x\in$ layer $j$ to $\Omega_1^c$ must cross layer $j-1$ (from $\Omega_{j-1}^c$... the same argument), so its length exceeds $\varrho\ell_{j-1}$; the other statements follow likewise from (S). $\square$

The constant $R_0(d,L)$ is fixed in 4.3; all that is used is that $\varrho-1\ge R_0$ implies (4.1), (4.2) and the hypothesis of Lemma 4.4.

**Lemma 4.4 (counting).** Let $\gamma>0$ and $(\varrho-1)\ge R_1(d,L,\gamma)$. Then $\sup_{y}\sum_{y'\in\mathbb B_k}e^{-\gamma d(y,y')}\le C(d,L,\gamma)$.
*Proof.* Let $N(s)$ be the number of $y'$ with $d(y,y')\le s$. For such $y'$ take a path of cost $\le s$ and let $m^*$ be the deepest layer it visits. Layers visited form an interval (adjacent points lie in layers differing by at most one, because points of layers $i$ and $i+2$ are at distance $>\varrho\ell_{i+1}>\eta$), so by Lemma 4.3(a) applied twice, $m^*\le\max(j,j')+1+\frac s{2(\varrho-1)}$ if $m^*>\max(j,j')$. The $\ell^1$ length of the path is at most $s\ell_{m^*}$, hence $|y-y'|\le s\ell_{m^*}$ and the number of $j'$-block centres within that distance is at most $(2s\ell_{m^*}/\ell_{j'}+1)^d\le(2sL^{(m^*-j')}+1)^d$. Also $d(y,y')\ge(\varrho-1)(|j-j'|-1)_+$ bounds the number of layers $j'$ by $2+2s/(\varrho-1)$. Collecting, $N(s)\le(3+2s)^{d+1}L^{d(2+(\ldots)s/(\varrho-1))}$ with an explicit coefficient $\le3$; thus $N(s)\le C(1+s)^{d+1}e^{(3d\log L/(\varrho-1))s}$, and $\sum_{y'}e^{-\gamma d(y,y')}\le\sum_{m\ge0}N(m+1)e^{-\gamma m}<\infty$ as soon as $3d\log L/(\varrho-1)\le\gamma/2$. $\square$ (This is E5 Lemma 2.1 (2.61), p. 234, read: "$\sup_y\sum_{y'}e^{-\alpha\delta_0d(y,y')}\le c_1(\alpha)$", with (2.60) our 4.3(a).)

**Proposition 4.5 (Agmon estimate).** Let $\varepsilon_0=\frac1{184d}$, $0\le\varepsilon\le\varepsilon_0$, $y'\in\mathbb B_k$, $w(x)=e^{\varepsilon d(x,y')}$, $f$ arbitrary, $u=G_D(\alpha)f$. Then
$$\|\ell^{-1}wu\|\le8\|\ell wf\|,\qquad\|\partial\widetilde{wu}\|\le4\|\ell wf\|,\qquad\|w\,\partial u\|\le5\|\ell wf\|.$$
*Proof.* Put $v=wu$, $h=wf$, $H_w=wHw^{-1}$. Then $\langle v,H_wv\rangle=\langle wu,wf\rangle=\langle v,h\rangle$ (here $w$ is real). We compare $H_w$ with $H$ term by term. (1) Multiplications by $\nu+\alpha$ commute with $w$. (2) Laplacian. For a bond $b=(x,x')$ put $\rho_b=w(x)/w(x')$; $|\log\rho_b|\le\varepsilon\eta/\ell(b)$ by 4.3(c). A direct computation with $\tilde v$ gives
$\mathrm{Re}\langle v,w(-\Delta^D)w^{-1}v\rangle=\|\partial\tilde v\|^2-\sum_b\eta^{d-2}(\rho_b+\rho_b^{-1}-2)\mathrm{Re}(\overline{v(b_-)}v(b_+))$.
Since $2(\cosh t-1)\le1.55t^2$ for $|t|\le1$ and $\mathrm{Re}(\bar ab)\le\frac12(|a|^2+|b|^2)$, the error is at most $1.55\varepsilon^2\cdot\frac12\sum_x\eta^d|v(x)|^2\sum_{b\ni x}\ell(b)^{-2}\le2d\varepsilon^2\|\ell^{-1}v\|^2$ (there are $2d$ bonds at $x$, each with $\ell(b)\ge\ell(x)$). (3) Block terms: for a block $B$ of layer $j$, $\langle v,wP_B(w^{-1}v)\rangle_B=|B|\,\overline{\mathrm{avg}(w^{-1}\cdot)}\ldots$ precisely
$=|B|\,\mathrm{avg}_B(w\bar v)\,\mathrm{avg}_B(w^{-1}v)$. Write $c=\mathrm{avg}_Bv$, $\bar w=w(x_B)$ for a reference point, $\tau=e^{\varepsilon d}-1$ (so that $\bar w^{-1}w(x)\in[e^{-\varepsilon d},e^{\varepsilon d}]$ on $B$ by 4.3(b)); then $\mathrm{avg}(w)\mathrm{avg}(w^{-1})\ge1$ (Cauchy–Schwarz), $|\mathrm{avg}(w^{-1}(v-c))|\le\bar w^{-1}\tau\,\mathrm{avg}|v-c|$ and the same for $w$, so
$\mathrm{Re}\,|B|\,\mathrm{avg}(w\bar v)\mathrm{avg}(w^{-1}v)\ge\|P_Bv\|^2-6\tau\|v\|_B^2$ for $\varepsilon d\le1$. Summing with $a_B\ell_B^{-2}\le2\ell_B^{-2}$: error $\le12\tau\|\ell^{-1}v\|^2\le21\varepsilon d\|\ell^{-1}v\|^2$. Hence, with G-1(a) applied to $v$,
$$\mathrm{Re}\langle v,H_wv\rangle\ge\tfrac12\|\partial\tilde v\|^2+\big(\tfrac14-2d\varepsilon^2-21d\varepsilon\big)\|\ell^{-1}v\|^2\ge\tfrac12\|\partial\tilde v\|^2+\tfrac18\|\ell^{-1}v\|^2\quad(\varepsilon\le\varepsilon_0).$$
Since $\mathrm{Re}\langle v,h\rangle\le\|\ell^{-1}v\|\|\ell h\|$ we obtain $\|\ell^{-1}v\|\le8\|\ell h\|$ and $\|\partial\tilde v\|^2\le2\cdot8\|\ell h\|^2$. Finally $w\partial u(b)=\partial v(b)-v(b_+)\partial(w^{-1}...)$: $|w(b_-)\partial u(b)|\le|\partial v(b)|+\frac{e^{\varepsilon\eta/\ell(b)}-1}\eta|v(b_+)|$ and $\frac{e^{t}-1}{\eta}\le1.6\varepsilon/\ell(b)$; summing, $\|w\partial u\|\le4\|\ell h\|+2\cdot1.6\varepsilon_0\cdot8\|\ell h\|\le5\|\ell h\|$. $\square$

**Corollary 4.6 (G-2(i)).** If $\mathrm{supp}f\subset\Delta(y')$ then $\|\ell wf\|\le e^{\varepsilon d}\ell_{j'}\|f\|$ (by 4.3(b), $d(x,y')\le d$ on $\Delta(y')$), and for $x\in\Delta(y)$, $w(x)\ge e^{\varepsilon(d(y,y')-d)}$. So, for $\varepsilon=\varepsilon_0$,
$\|\chi_{\Delta(y)}u\|=\ell_j\|\ell^{-1}\chi u\|\le8e^{2d\varepsilon_0}\ell_j\ell_{j'}e^{-\varepsilon_0d(y,y')}\|f\|$, and likewise $\ell_j\|\chi_{\Delta(y)}\partial u\|\le5e^{2d\varepsilon_0}\ell_j\ell_{j'}e^{-\varepsilon_0d(y,y')}\|f\|$. Now $\ell_j\ell_{j'}\le L^{(j-j')_+}\ell_{j'}^2$ and, by Lemma 4.3(a), $L^{|j-j'|}e^{-\frac{\varepsilon_0}2d(y,y')}\le L\,e^{-\frac{\varepsilon_0}{2}(\varrho-1)(|j-j'|-1)_+}L^{|j-j'|-1}\le L$ provided
$$\tfrac{\varepsilon_0}2(\varrho-1)\ge\log L,\tag{4.1}$$
(i.e. $\varrho-1\ge368d\log L$). Hence G-2(i) holds with $B_0^{(2)}=9e^{2d\varepsilon_0}L\le 10L$ and $\gamma_0=\varepsilon_0/2$. (This replaces E5 (2.59), (2.64); it needs only $\varrho\ge R_0$ for the scale mismatch.) The same weighted estimate holds for $G_{k,x}$ with $x\ge0$ (G-2(vii), L² part), since by G-1(a$'$) the coercivity holds uniformly and the conjugation errors of the two block terms are estimated as in (3).

**Lemma 4.7 (unit-lattice kernels need only $L^2$ decay).** Let $\ell_j=1$ (so $Q_k\to$ unit lattice) and $M=Q_kG_DQ_k^*$ acting on the unit lattice with entries $M(y,y')=\langle1_{B(y)},G1_{B(y')}\rangle$ (unit blocks have $|B|=1$; precisely $M(y,y')=\ell_j^{-d}\langle1_{B(y)},G1_{B(y')}\rangle$). By 4.6, $|M(y,y')|\le B_0e^{-\gamma_0d(y,y')}$ for $y,y'\in\Lambda_k$; on the unit lattice $d(y,y')\ge|y-y'|_1$-comparable (the layer is of unit scale): $d(y,y')=|y-y'|_1$ if the segment lies in $\Omega_k$. Hence $\Delta^{(k)}(y,y')=-a_k^2M(y,y')$ ($y\ne y'$) satisfies $|\Delta^{(k)}(y,y')|\le c_0e^{-\delta_0|y-y'|}$ whenever $y,y'$ lie in one connected component of $\Omega_k$ at unit steps (in general one uses $d$; the constants depend on $d,L$ only). This supplies hypothesis (G-4) for $A=aL^{-2}Q^*Q+\Delta^{(k)}$ (the term $aL^{-2}Q^*Q$ has range $L$). No pointwise bound is used here.

### 4.3 G-2 step 2: the scale mismatch

Done in Corollary 4.6 via (4.1) and Lemma 4.3(a): the factor $\ell_j/\ell_{j'}\le L^{|j-j'|}$ is absorbed because $d(y,y')\ge(\varrho-1)(|j-j'|-1)_+$ and (4.1). The same absorption is used for $\|f\|_{L^2(\Delta(y'))}\le\ell_{j'}^{d/2}\|f\|_\infty$ in 4.5 (factors $(\ell_{j'}/\ell_j)^{d/2}\le L^{d|j-j'|/2}$), which requires
$$\tfrac{\varepsilon_0}4(\varrho-1)\ge\tfrac d2\log L+\log L\ \ (\Leftarrow\varrho-1\ge R_0:=\lceil1500\,d\log L\rceil).\tag{4.2}$$
We fix $R_0(d,L):=\max(1500\,d\log L,\ R_1(d,L,\varepsilon_0/2))+2$.

### 4.4 G-4: unit-lattice operators (operator-norm Combes–Thomas and the geometric resolvent identity)

*Cited:* the abstract scheme of FroehlichSpencer `combesThomas_core` (public repository `scottnarmstrong/Frohlich-Spencer`, commit `b47bc3d`, file `FroehlichSpencer/Infra/Green/CombesThomas.lean`). *Proved here:* the generalization and the three statements.

**What `combesThomas_core` proves** (read). For a kernel `a : X → X → ℂ` with `ha : a y x = star (a x y)` (Hermitian), `hK : ∑_{y∈s} ‖a x y‖ ≤ K` for every finset `s`, a pseudo-metric `d` with `hrange : a x y ≠ 0 → d x y ≤ 1`, a real potential `v`, a finite set $\Lambda$, a complex shift $z$ and a constant `c > 0` with `hlow : c‖u‖ ≤ ‖(H_Λ − z)u‖` for all $u$ (and `hdet`), the column of the resolvent satisfies $\|G_\Lambda(z;\cdot,y)\|(x)\le\frac2c\exp(-\log(1+\frac c{2(K+1)})\,d(x,y))$. The proof conjugates by $e^{\mu d(\cdot,y)}$; the perturbation $B_{uu'}=a_{uu'}(e^{\mu(d(u,y)-d(u',y))}-1)$ has $|B_{uu'}|\le|a_{uu'}|(e^\mu-1)$ by `hrange` and the triangle inequality (`norm_weightPerturbation_le`; here `ha` is used to pass from row to column sums), and Schur's test (`norm_toLp_mulVec_le`) gives $\|B\|\le K(e^\mu-1)\le c/2$; then `hlow` yields $\|e^{\mu d}g\|\le2/c$.

**Required generalization (to be made when porting, not in the public repository):**
1. Replace `hrange` and `hK` by *exponentially weighted row and column sums*: there are $\mu_0>0$ and $K_{\mu_0}$ with
$\sup_x\sum_{x'}|A(x,x')|e^{\mu_0d(x,x')}\le K_{\mu_0}$ and $\sup_{x'}\sum_x|A(x,x')|e^{\mu_0d(x,x')}\le K_{\mu_0}$. For $|A(x,x')|\le c_0e^{-\delta_0|x-x'|}$ on $\mathbb Z^d$ and $\mu_0=\delta_0/2$ this holds with $K_{\mu_0}=c_0\sum_ze^{-\delta_0|z|/2}$. The perturbation entries then satisfy
$|B_{uu'}|\le|A(u,u')|(e^{\mu d(u,u')}-1)$ and, for $\mu\le\mu_0$, $\sum_{u'}|B_{uu'}|\le\sum_{u'}|A(u,u')|\,\mu\,d(u,u')e^{\mu d(u,u')}\le\mu\,K'$ with $K'=c_0\sum_z|z|e^{-\delta_0|z|/2}$, by $e^t-1\le te^t$ (the same for columns). Choose $\mu=\min(\mu_0,c/(2K'))$.
2. Drop `ha` (the Hermitian hypothesis): it was used only to relate the column bound to the row bound (`norm_weightPerturbation_le` and `hcol`), which is now replaced by the hypothesis on column sums. The operator may be complex symmetric or have no symmetry.
3. Replace the potential `v` (real) and the shift $z$ by an arbitrary decomposition $H_\Lambda-z\to A_\Lambda+x$; the proof of the core needs only `hlow` and the conjugation identity `weight_identity`, whose algebra holds for any complex matrix (`restrictedOp a v Λ` is replaced by $\chi_\Lambda A\chi_\Lambda$, the diagonal being part of $A$; the diagonal entries commute with the weight).
4. For matrix-valued kernels ($\mathbb C^N$ fields) use operator norms of the blocks; Schur's test holds with $\|A(x,x')\|_{op}$.
5. **Lower bound `hlow` for $A_\Lambda+x$:** $\mathrm{Re}\langle u,(A_\Lambda+x)u\rangle=\mathrm{Re}\langle u_\Lambda,Au_\Lambda\rangle+x\|u\|^2\ge(\gamma_0+x)\|u\|^2$ (restriction of a form with $\mathrm{Re}A\ge\gamma_0$ to $\ell^2(\Lambda)$), hence $\|(A_\Lambda+x)u\|\ge(\gamma_0+x)\|u\|$ by Cauchy–Schwarz.
The core then yields (a) with $c=\gamma_0+x$ and $\mu=\min(\mu_0,(\gamma_0)/(2K'))$ independent of $x$: the condition $K'\mu\le c/2$ is monotone in $c$.

**Proof of (b) (domain difference, E3 (5.8)).** For $\Lambda'\subset\Lambda$ write $P=\chi_{\Lambda'}$, $G=(A_\Lambda+x)^{-1}$, $G'=(A_{\Lambda'}+x)^{-1}$ extended by zero. Since $(A_\Lambda+x)PG'=P+(1-P)APG'$ (for $G'$ extended by zero, $PG'P=G'$), we get the geometric resolvent identity
$$G-G'=-G(1-P)APG'.$$
Hence for $x_1,x_2\in\Lambda'$, $(G-G')(x_1,x_2)=-\sum_{z\in\Lambda\setminus\Lambda'}\sum_{w\in\Lambda'}G(x_1,z)A(z,w)G'(w,x_2)$. Using (a) for $G$ and $G'$ and the decay of $A$ with $\mu'=\min(\mu,\delta_0)/3$ and $|x_2-z|\le|x_2-w|+|w-z|$,
$|(G-G')(x_1,x_2)|\le\frac{4c_0}{(\gamma_0+x)^2}\sum_{z,w}e^{-\mu|x_1-z|}e^{-\delta_0|z-w|}e^{-\mu|w-x_2|}$ and $\le\frac C{\gamma_0+x}e^{-\mu'(|x_1-z|+|x_2-z|)}$ after summing over $w$ and using $e^{-\mu|x_1-z|}\le e^{-\mu|x_1-z|/2}e^{-\mu|x_1-z|/2}$; the sum over $z\in\Lambda\setminus\Lambda'$ with $|x_1-z|\ge D_1=d(x_1,\Lambda\setminus\Lambda')$ is bounded by $C e^{-\mu'(D_1+D_2)}$ (with $D_2$ for $x_2$; $|x_1-z|+|x_2-z|\ge D_1+D_2$). Two factors $2/(\gamma_0+x)$ give $4c_0/(\gamma_0+x)^2\le4c_0\gamma_0^{-1}(\gamma_0+x)^{-1}$, which is the stated form. (E3 (5.9) prints the signs of the distance terms apparently misplaced, ER-151; the sign is as here.) $\square$

**Proof of (c) (perturbation, E3 (5.10), (5.17)).** With $G_{A}=(A_\Lambda+x)^{-1}$, $G_{A+B}=(A_\Lambda+B_\Lambda+x)^{-1}$: $G_{A+B}-G_A=-G_{A}B_\Lambda G_{A+B}$, so for $x_1,x_2\in\Lambda$, $|(G_{A+B}-G_A)(x_1,x_2)|\le\sum_{z,w\in X'}|G_A(x_1,z)||B(z,w)||G_{A+B}(w,x_2)|$, bounded by $\frac{C}{(\gamma_0+x)^2}e^{-\mu'(d(x_1,X')+d(x_2,X'))}$ exactly as in (b) (both factors decay from the support $X'$ of $B$). The localization expansion (5.17) used in P4 (2.50): $G_{A}$ is a convergent series in the geometric resolvent identity, and every term is local in the sense of (b), (c); statement (c) with $B=A'-A$ for two operators that agree outside $X'$ is what is consumed (C8, C12, C17). $\square$

**G-4 applied to P4/P3.** (i) $A=aL^{-2}Q^*Q+\Delta^{(k)}$: $\mathrm{Re}A\ge\gamma_0'L^{-2}-4\theta_0\ge\frac12\gamma_0'L^{-2}$ by G-1(b) for $\theta_0\le\frac18\gamma_0'L^{-2}$; kernel decay by 4.7. Then $C^{(k)}_x=(A+x)^{-1}$ decays uniformly in $x\ge0$ with prefactor $2/(\gamma_0+x)$, so $C^{(k)1/2}=\frac1\pi\int_0^\infty x^{-1/2}C_x^{(k)}dx$ has a kernel bounded by $\frac2\pi\int_0^\infty x^{-1/2}(\gamma_0+x)^{-1}dx\,e^{-\mu|\cdot|}=\frac{2}{\sqrt{\gamma_0}}e^{-\mu|\cdot|}$ (C12; the rate is that of $x=0$, uniform in $x$). (ii) At $\lambda=\infty$ the form (2.49) is $P^\perp G_1^{-1}P^\perp+P$ with coefficient kernel decaying: the hypotheses of G-4 for the operator $[I-P]\,G_1^{-1}\,[I-P]+P$ follow from those of $G_1^{-1}=-\Delta^1+aL^{-2}Q^*Q+\nu_0+\alpha_1$ (finite range, $\mathrm{Re}\ge\frac14L^{-2}$ by G-1(b)(2)) and from the exponential decay of the entries of $P=(\phi_1)_0\otimes(\phi_1)_0$ (range zero: $P$ is a multiplication operator by a rank-one matrix at each site). Note $\mathrm{Re}(P^\perp G_1^{-1}P^\perp+P)\ge\min(\frac14L^{-2},1)\ge\frac14L^{-2}$ because $P^\perp\perp P$.

### 4.5 G-2 step 3: pointwise, gradient and Hölder bounds (detailed plan, with the proofs of the lemmas that are short)

What is consumed (Section 2, C1): sup, gradient and Laplacian bounds in the $|\cdot|_\sigma$ norms with $L^\infty$ data, with decay (C4, C5) and a Hölder bound for *one* fixed exponent $\theta$ (via P1 (3.107)). The cheapest route found is **potential theory on $\mathbb Z^d$ with local absorption**; the layers $j=1$ and the layers with $L^j$ bounded are handled by the inverse inequality. We list the lemmas in order.

**Lemma K (lattice Green's function on $\mathbb Z^d$, $d\ge3$).** Let $q_t(n)=\frac1{2\pi}\int_{-\pi}^\pi e^{in\vartheta-2t(1-\cos\vartheta)}d\vartheta$, $p_t(x)=\prod_\mu q_t(x_\mu)$, $C(x)=\int_0^\infty p_t(x)dt$. Then $C\ge0$, $-\Delta^1C=\delta_0$, and for all $x\in\mathbb Z^d$, with $\langle x\rangle=1+|x|$:
$C(x)\le c\langle x\rangle^{2-d}$, $|\partial_\mu C(x)|\le c\langle x\rangle^{1-d}$, $|\partial_\mu\partial_\nu C(x)|\le c\langle x\rangle^{-d}$ (forward differences; also for backward ones).
*Proof.* (1) $q_t\ge0$, $\sum_nq_t(n)=1$ (the Poisson-weighted random walk), and $\sum_{x}p_t=1$. $-\Delta^1p_t=-\partial_tp_t$ gives $-\Delta^1C=p_0=\delta_0$ after integrating (decay at $t\to\infty$ from $p_t\le ct^{-d/2}$). (2) One-dimensional bounds: for $t\ge1$ and $|n|\ge0$,
$q_t(n)\le c\,t^{-1/2}e^{-c'\min(n^2/t,|n|)}$, $|q_t(n+1)-q_t(n)|\le c\,t^{-1}e^{-c'\min(n^2/t,|n|)}$, $|\partial^2q_t(n)|\le c\,t^{-3/2}e^{-c'\min(n^2/t,|n|)}$; for $t\le1$, $q_t(n)\le c\,t^{|n|}$ and the differences are $\le2q_t(n)+2q_t(n+1)$. *Proof of (2):* shift the contour $\vartheta\to\vartheta+i\tau$: $|q_t(n)|\le e^{-n\tau+2t(\cosh\tau-1)}\frac1{2\pi}\int e^{-2t(1-\cos\vartheta)}d\vartheta\cdot$ (using $|e^{-2t(1-\cos(\vartheta+i\tau))}|=e^{-2t(1-\cos\vartheta\cosh\tau)}$), and $\frac1{2\pi}\int e^{-2t(1-\cos\vartheta)}d\vartheta\le ct^{-1/2}$ since $1-\cos\vartheta\ge2\vartheta^2/\pi^2$; choose $\tau=\min(n/(2t),1)$: for $n\le2t$ the exponent is $\le-n^2/(2t)+0.55\,n^2/(2t)\cdot\frac12\cdot2=-0.225\,n^2/t$ and for $n\ge2t$ it is $\le-n+1.09t\le-0.45n$. For differences insert the factors $(e^{i\vartheta}-1)$, resp. $(e^{i\vartheta}-1)^2$, which are bounded by $|\vartheta|+\tau$ and handled by $\int|\vartheta|^me^{-ct\vartheta^2}d\vartheta\le ct^{-(m+1)/2}$ and $\tau t^{-1/2}\le nt^{-3/2}$, then absorb $n\,t^{-1}e^{-0.225n^2/t}\le ct^{-1/2}e^{-0.1n^2/t}$. (3) Integrate in $t$: with $r=\langle x\rangle$, $\int_{r}^\infty t^{-d/2}dt\sim r^{2-d}$ and, using $\min(x_\mu^2/t,|x_\mu|)$, the region $t\le r$ contributes $\le c\,e^{-c'r}$-type terms (at least one coordinate has $|x_\mu|\ge r/d$); the same with $t^{-(d+1)/2}$, $t^{-(d+2)/2}$ for the differences; the part $t\le1$ contributes $O(e^{-c|x|})$ for $|x|\ge2$ and $O(1)$ otherwise. $\square$
Scaling: on the lattice $\eta\mathbb Z^d$ with weight $\eta^d$ the Green's function of $-\Delta^\eta$ is $K_\eta(x)=\eta^{2-d}C(x/\eta)$ and $(-\Delta^\eta)^{-1}g(x)=\sum_z\eta^dK_\eta(x-z)g(z)$ for finitely supported $g$; $K_\eta(x)\le c|x|^{2-d}$, $|\partial K_\eta|\le c|x|^{1-d}$, $|\partial\partial K_\eta|\le c|x|^{-d}$ for $|x|\ge\eta$ and $K_\eta\le c\eta^{2-d}$, $|\partial^\eta K_\eta|\le c\eta^{1-d}$ near $0$. (On the torus, a function supported in a ball of radius $<\frac14$ is regarded as a function on $\eta\mathbb Z^d$.) Existence/definition of $C$ in Lean: through the Fourier integral $C(x)=(2\pi)^{-d}\int_{[-\pi,\pi]^d}e^{ix\cdot p}(\sum_\mu(2-2\cos p_\mu))^{-1}dp$ equals $\int_0^\infty p_t(x)dt$ by Fubini; the Fourier template is `FroehlichSpencer/FS82/Infinite/FourierGreen.lean` (public repository, same commit; it treats $\mathbb Z^4$, with `chordSq`, `intervalGreenMajorant`; to be generalized to $d$).

**Lemma Loc (interior estimate for the discrete Poisson equation).** Let $x_0\in\eta\mathbb Z^d$, $\rho\ge8\eta$, $B_{2\rho}=\{|z-x_0|\le2\rho\}$, $u:B_{2\rho}\to\mathbb C$ and $g$ with $-\Delta^\eta u=g$ on $B_{2\rho}$ (interior points). For $x\in B_{\rho/2}$:
(a) $|u(x)|\le C\rho^{-d/2}\|u\|_{L^2(B_{2\rho})}+\sum_{z\in B_{2\rho}}\eta^d|K_\eta(x-z)||g(z)|$;
(b) $|\partial_\mu^\eta u(x)|\le C\rho^{-1-d/2}\|u\|_{L^2(B_{2\rho})}+\sum_z\eta^d|\partial_\mu K_\eta(x-z)||g(z)|$;
(c) for bonds $b,b'$ in direction $\mu$ at $x,x'\in B_{\rho/2}$, $r=|x-x'|\le\rho/4$: $|\partial u(b)-\partial u(b')|\le C\rho^{-1-d/2}\frac r\rho\|u\|_{L^2}+\sum_z\eta^d|\partial K_\eta(x-z)-\partial K_\eta(x'-z)||g(z)|$, and for $|g|\le G_\infty$ on $B_{2\rho}$ the last sum is $\le C G_\infty\,r\,(1+\log_+(\rho/r))$ (hence $\le C_\theta G_\infty r^\theta\rho^{1-\theta}$ for each $\theta<1$).
*Proof.* Let $\chi$ be a cutoff with $\chi=1$ on $B_\rho$, supported in $B_{7\rho/4}$, with $|\partial\chi|\le c\rho^{-1}$, $|\partial\partial\chi|\le c\rho^{-2}$ (a product of one-dimensional smooth cutoffs sampled on the lattice; this is where $\rho\ge8\eta$ is used). Then $v=\chi u$ is finitely supported and $v=(-\Delta^\eta)^{-1}(-\Delta^\eta v)$ with the discrete Leibniz formula (G-6(e)):
$-\Delta v=\chi g-u\Delta\chi-\sum_{b\in st}\partial\chi(b)\partial u(b)$. The first term gives the $g$-sum (note $\chi\le1$). In the last term, after the exchange of the two orientations of each bond and a summation by parts in $\partial u$, its contribution to $v(x)$, $x\in B_{\rho/2}$, is $\sum_\mu\sum_z\eta^d\,u(z)\,\partial_\mu^{*}\big[(K_\eta(x-z)+K_\eta(x-z-\eta e_\mu))\partial_\mu\chi(z)\big]$, which is supported where $\partial\chi\ne0$, i.e. $|z-x_0|\ge\rho$, hence $|x-z|\ge\rho/2$, and bounded by $c\rho^{-d}\sum_{z\in B_{2\rho}}\eta^d|u(z)|\le c\rho^{-d}(\rho^d)^{1/2}\|u\|_{L^2}$ using $|K_\eta|\le c\rho^{2-d}$, $|\partial K_\eta|\le c\rho^{1-d}$ there. The term $u\Delta\chi$ is bounded in the same way. This proves (a); (b), (c) use the same representation with $\partial K_\eta$, $\partial\partial K_\eta$, whose bounds are $|x-z|^{1-d}$, $|x-z|^{-d}$; for (c) the $g$-sum is split at $|x-z|=2r$ (near part $\le CG_\infty r$ since $\sum_{|z-x|\le2r}\eta^d|x-z|^{1-d}\le cr$; far part $\le C G_\infty r\int_{2r}^{\rho}s^{-d}s^{d-1}ds=CG_\infty r\log(\rho/2r)$, using $|\partial K(x-z)-\partial K(x'-z)|\le cr|x-z|^{-d}$ for $|x-z|\ge2r$ by Lemma K for second differences). $\square$

**Lemma P (pointwise estimate for $u=G_D(\alpha)f$, $\mathrm{supp}f\subset\Delta(y')$).** There are $c_0=c_0(d,L)\in(0,\frac14)$, $J_0(d,L)$ and $K_1$ such that for every $x$:
$$U(x):=|u(x)|+\ell(x)\max_{b\ni x}|\partial u(b)|\le K_1e^{-\frac{\varepsilon_0}2d(x,y')}\ell_{j'}^2\|f\|_\infty+\theta_1\sup_{d(z,x)\le3d}U(z),\qquad\theta_1<\tfrac12e^{-3d\varepsilon_0}.\tag{4.3}$$
*Plan of proof, in the order of the cases.* Write $j=j(x)$, $g=f-(Q^*aQ+\nu+\alpha)u$ so that $-\Delta^\eta u=g$ at interior points; by (1.5), $\nu\le1\le\ell^{-2}$ and $|\alpha|\le\ell^{-2}/4$,
$$|g(z)|\le|f(z)|+4\ell(z)^{-2}\max_{z'\in N(z)}|u(z')|,\qquad N(z)=B(z)\cup\{z\}.\tag{4.4}$$
*Case 1 (layer $j=1$, or $L^{j}\le J_0$).* Inverse inequality: $|u(x)|\le\eta^{-d/2}\|u\|_{L^2(\Delta(y))}$ and $\ell(x)|\partial u(b)|\le2\ell(x)\eta^{-1}\max(|u(x)|,|u(x')|)\le2L^j\max(|u(x)|,|u(x')|)$ with $x'$ a neighbour (its own bound is the same type, since $x'$ lies in a layer $j$ or $j\pm1$, and the factor is at most $L^{J_0}$ or $L$). By 4.6, $\|u\|_{L^2(\Delta(y))}\le B\ell_j\ell_{j'}e^{-\varepsilon_0d(y,y')}\ell_{j'}^{d/2}\|f\|_\infty$, and $\eta^{-d/2}\ell_j\ell_{j'}\ell_{j'}^{d/2}=(\ell_j/\eta)^{d/2}(\ell_{j'}/\ell_j)^{d/2}\ell_j\ell_{j'}$ with $(\ell_j/\eta)^{d/2}=L^{jd/2}\le L^{J_0d/2}$ (for $j=1$: $L^{d/2}$) and $(\ell_{j'}/\ell_j)^{d/2}\ell_j\ell_{j'}\le L^{(d/2+1)|j-j'|}\ell_{j'}^2$, which is absorbed by (4.2). So $U(x)\le K_1e^{-\frac{\varepsilon_0}2d(x,y')}\ell_{j'}^2\|f\|_\infty$ with no recursion term. (This is the only place where $L$ enters through powers, as announced in the roadmap.)
*Case 2 ($j\ge2$, $L^j>J_0$).* Put $\rho=c_0\ell_j/L$ and apply Lemma Loc at $x_0=x$ (note $\rho\ge8\eta$ when $c_0L^{j-1}\ge8$, which fixes $J_0=8L/c_0$). By Lemma 4.3(d) the ball $B_{2\rho}(x)$ lies in $\Omega_1$, in layers $j-1,j,j+1$ (so $\ell(z)\ge\ell_j/L$ and every block meeting it has diameter $\le dL\ell_j$), hence $-\Delta u=g$ throughout and $N(z)\subset\{z':d(z',x)\le3d\}$. Lemma Loc gives, with (4.4):
(1) the $L^2$ term: $\rho^{-d/2}\|u\|_{L^2(B_{2\rho})}\le C(L/c_0)^{d/2}\ell_j^{-d/2}\sum_{\text{blocks}\,B'\cap B_{2\rho}\ne\emptyset}\|u\|_{L^2(B')}\le C'\,\ell_j^{-d/2}\ell_j\ell_{j'}e^{-\varepsilon_0d(x,y')}\ell_{j'}^{d/2}\|f\|_\infty\cdot e^{\varepsilon_0\cdot3d}$ (at most $3^dL^d$ blocks meet the ball; their centres have $d(\cdot,x)\le3d$), which is $\le K_1'e^{-\frac{\varepsilon_0}2d(x,y')}\ell_{j'}^2\|f\|_\infty$ by (4.2) as in Case 1 ($(\ell_{j'}/\ell_j)^{d/2}\ell_j\ell_{j'}$ again);
(2) the $f$ part of the $g$-sum: $\sum_z\eta^d|K_\eta(x-z)||f(z)|\le\|f\|_\infty\sum_{z\in\Delta(y')}\eta^dK_\eta(x-z)\le C\|f\|_\infty\ell_{j'}^2$ (rearrangement: the integral of $|z|^{2-d}$ over a set of volume $V$ is at most that over a ball of volume $V$, $\le CV^{2/d}$), and the sum is empty unless $B_{2\rho}(x)\cap\Delta(y')\ne\emptyset$, in which case $d(x,y')\le5d$ and $e^{-\frac{\varepsilon_0}2d(x,y')}\ge c$; for the gradient, $\ell_j\sum\eta^d|\partial K||f|\le C\ell_j\|f\|_\infty\ell_{j'}\cdot\min(\ell_{j'},\ldots)^{1}$: the integral of $|z|^{1-d}$ over a set of volume $V$ is $\le CV^{1/d}$, so $\le C\ell_j\ell_{j'}\|f\|_\infty\le CL^{(j-j')_+}\ell_{j'}^2\|f\|_\infty$ and for $j>j'$ the ball meets $\Delta(y')$ only if $|j-j'|\le1$ (separation), so the factor is at most $L$;
(3) the potential part: $\sum_z\eta^dK_\eta(x-z)4\ell(z)^{-2}\max_{N(z)}|u|\le4(L/\ell_j)^2\sup_{d(z',x)\le3d}|u(z')|\cdot\sum_{z\in B_{2\rho}}\eta^dK_\eta(x-z)\le C\rho^2(L/\ell_j)^2\sup|u|=Cc_0^2\sup_{N}|u|$, and for the gradient $\ell_j\sum\eta^d|\partial K||g_u|\le C\ell_j\rho(L/\ell_j)^2\sup|u|=Cc_0L\sup|u|$; choose $c_0$ so small that $Cc_0^2+Cc_0L\le\theta_1$.
Combining (1)–(3) gives (4.3). $\square$

**Proposition 4.8 (G-2(ii), pointwise).** $U(x)\le K_2e^{-\gamma_0d(x,y')}\ell_{j'}^2\|f\|_\infty$ with $\gamma_0=\varepsilon_0/2$.
*Proof.* The lattice is finite, so $A(t):=\sup\{U(x):d(x,y')\ge t\}<\infty$. From (4.3), $A(t)\le K_1e^{-\frac{\varepsilon_0}2t}F+\theta_1A(t-3d)$ with $F=\ell_{j'}^2\|f\|_\infty$ and $A(s)=A(0)$ for $s\le0$. For $t=0$: $A(0)\le K_1F+\theta_1A(0)$, so $A(0)\le2K_1F$. Iterating $n=\lceil t/3d\rceil$ times: $A(t)\le K_1F\sum_{m<n}\theta_1^me^{-\frac{\varepsilon_0}2(t-3dm)}+\theta_1^nA(0)$, and since $\theta_1e^{\frac32d\varepsilon_0}\le e^{-\frac32d\varepsilon_0}\cdot\frac12$ this is $\le4K_1Fe^{-\frac{\varepsilon_0}2t}\cdot$ (geometric sum $\le2$) $+2K_1F\,\theta_1^{t/3d}$ with $\theta_1^{t/3d}\le e^{-\varepsilon_0 t}$. Hence $A(t)\le6K_1Fe^{-\frac{\varepsilon_0}2t}$. Evaluating at $x\in\Delta(y)$ ($d(x,y')\ge d(y,y')-d$) gives (ii) for $u$ and its gradient. For the Laplacian: $\ell(x)^2\Delta^Du(x)=\ell(x)^2[(Q^*aQ+\nu+\alpha)u-f](x)$, so $\ell^2|\Delta^Du|\le4\max_{N(x)}|u|+\ell^2|f|$, and $\ell_j^2|f(x)|\le\ell_{j'}^2\|f\|_\infty$ times $L^{2(j-j')_+}$, where $f(x)\ne0$ forces $x\in\Delta(y')$ and $j=j'$ or adjacent: the factor is $\le L^2$. $\square$

**Proposition 4.9 (G-2(iii), Hölder with fixed $\theta$).** For $x,x'$ with $|x-x'|\le\rho/4$ Lemma Loc(c) gives, as in Case 2, $|\partial u(b)-\partial u(b')|\le C_\theta r^\theta\ell_j^{\theta-2}[\ldots]$ with the same right-hand side as (4.3) (the $L^2$ term carries the additional factor $r/\rho\le(r/\rho)^\theta$; the $g$-sum is $\le CG_\infty r^\theta\rho^{1-\theta}$ with $G_\infty\le\|f\|_\infty+4(L/\ell_j)^2\sup|u|$ and $\rho^{1-\theta}\le\ell_j^{1-\theta}$, so the potential part is $\le C c_0^{1-\theta}\ell_j^{-1}\ell_j^{-1+\theta}\cdots$ absorbed by the same recursion). For $|x-x'|>\rho/4$ use $|\partial u(b)-\partial u(b')|\le2\max U/\ell_j$ and $|x-x'|^{1-\theta}\ge(\rho/4)^{1-\theta}=c(c_0/L)^{1-\theta}\ell_j^{1-\theta}$. In layer 1 or $L^j\le J_0$, $|x-x'|\ge\eta$ and $\ell_j^{2-\theta}\eta^{\theta-1}|\partial u(b)-\partial u(b')|\le2\ell_j^{2-\theta}\eta^{\theta-1}\ell_j^{-1}\max U=2(\ell_j/\eta)^{1-\theta}\max U\le2L^{J_0}\max U$. The constant is $B_\theta=C(d,L)\,(1-\theta)^{-1}$ from the logarithm in Lemma Loc(c). Only one exponent $\theta<\frac12$ is consumed; one may fix $\theta=\frac14$. $\square$

*Remark (cheaper variants considered and rejected).* (i) Moser iteration plus Campanato iteration needs the lattice Sobolev inequality, Caccioppoli, Moser's local maximum bound, Campanato's lemma and a decay lemma for discrete harmonic functions: each of these is longer than Lemma K plus Lemma Loc, and none of them gives the gradient bound from a bounded right-hand side without the extra Campanato step. (ii) E3's multiscale Fourier decomposition (2.34) is not used (E3 p. 586 states the $j$-uniform analytic strip without proof, ER-148). (iii) A maximum-principle argument for $Q^*aQ$ is impossible: $Q^*aQ$ has positive off-diagonal entries, $H$ is not an M-matrix, and treating $Q^*aQ$ as a perturbation of $K=-\Delta^D+\ell^{-2}$ gives a Neumann series with ratio of size $2$.

**Proof of G-2(iv) (global form).** Let $f$ with $|f|_2<\infty$, $f=\sum_{y'}f_{y'}$ with $f_{y'}=f\chi_{\Delta(y')}$, $\|f_{y'}\|_\infty\le\ell_{j'}^{-2}|f|_2$. By 4.8, $|u(x)|\le\sum_{y'}K_2e^{-\gamma_0d(y,y')}|f|_2\le K_2C(d,L,\gamma_0)|f|_2$ by Lemma 4.4 (with $\varrho-1\ge R_0\ge R_1(d,L,\gamma_0)$), and likewise for $U$, for the Laplacian and, by 4.9, for the Hölder seminorm; the Hölder norm of P2 (3.17) for $x\in\Delta(y)$, $x'\in\tilde\Delta(y)$ involves points of neighbouring blocks, handled by the same estimate with the ball enlarged by a factor 3. $\square$

### 4.6 G-3: is the random-walk representation needed?

*Decision: no interface G-3.* The consumers of the Green's function bounds are C1–C14. Among them only C5 (P3 (2.6)–(2.23), (3.12)–(3.20)) uses the walk expansion, and C5's use is the *localization expansion* of $\delta\phi_k$ and $C^{(k)}$ (P3 Props. 2.1–2.3, 3.1; hypothesis (H.5)), i.e. a statement about the dependence of $G(\alpha)$, $\phi_k$, $C^{(k)}$ on data in domains, not a Green's function bound. Given G-2, G-4 and the identities of G-6, that dependence is available directly:
(1) *Locality in $\alpha$* (G-2(vi)): proof. $G(\alpha)-G(\alpha')=-G(\alpha)(\alpha-\alpha')G(\alpha')$ (G-6(c)); for blocks $\Delta(y),\Delta(y')$,
$\|\chi_{\Delta(y)}(G(\alpha)-G(\alpha'))\chi_{\Delta(y')}\|\le\sum_{z\in\text{blocks meeting }Z}\|\chi_yG\chi_z\|\,\|(\alpha-\alpha')\chi_z\|\,\|\chi_zG'\chi_{y'}\|$, and by 4.6 (with operator-norm form: apply 4.5 to $\chi_{\Delta(z)}$ data, $L^2\to L^2$) $\|\chi_yG\chi_z\|\le10L\ell_y\ell_ze^{-\gamma_0d(y,z)}$, $\|(\alpha-\alpha')\chi_z\|\le\frac12\ell_z^{-2}$. Thus the sum is $\le C\ell_y\ell_{y'}\sum_{z}e^{-\gamma_0(d(y,z)+d(z,y'))}$ and, since $d(y,z)+d(z,y')\ge\frac12(d(y,z)+d(z,y'))+\frac12d(y,y')$ and $z$ ranges over blocks within $Z$, Lemma 4.4 bounds the sum by $Ce^{-\frac{\gamma_0}2(d(y,Z)+d(y',Z))}$ (each term has $d(y,z)\ge d(y,Z)$, $d(z,y')\ge d(y',Z)$, and the remaining $e^{-\frac{\gamma_0}2(\cdots)}$ is summed by 4.4). 
(2) *Analyticity.* For finite $\Omega_1$, $G_D(\alpha)$ is a rational function of the values of $\alpha$ with no poles on $\{|\alpha|_2<\frac14\}$ (G-1(a)); the bounds of G-2 are uniform on this polydisc, so Cauchy's estimates give uniform bounds for the derivatives in the interpolation parameters of P3 (the $s$ of (2.16)–(2.23)).
(3) *Localization by inclusion–exclusion.* P3's expansion expresses $\phi_k$ as a sum over domains $X$ of terms depending on the data in $X$ only, with decay $e^{-\kappa d(X)}$. With (1) and (2) the same decomposition is obtained from the telescoping $F=\sum_X\sum_{Y\subset X}(-1)^{|X\setminus Y|}F[\text{data}|_Y]$ and the bound of (1) for each added block (an iteration of (1) over a tree of blocks gives the factor $e^{-\gamma d(X)}$ via the minimal tree of $X$). UNCERTAIN: whether the exact form of (H.5) (spaces $\Xi^c_j$ with exponent $\kappa-1$, P3 p. 74, ER-053) is reproduced by this route; this is a question for the localization-expansion document and does not affect the Green's function interface.
If the localization document insists on the walk expansion of P3, G-3 is the statement of Section 3 and its proof is: the algebra (G-6(e)), the cube versions of G-1, G-2 (Neumann faces: even reflection; the cube $\square_z\cap\Omega_1$ meets $\partial\Omega_1$ only in layer 1 where the bounds are trivial) and a Neumann series in the Banach algebra of kernels with norm $\sup_x\sum_ye^{\gamma d(x,y)}|k(x,y)|$ (D1 Lemma 6 and Corollary 7); size: about one third of G-2 step 1 plus the bookkeeping of the 12-type walk (3.17), for which P3 states no index restrictions (ER-046).

### 4.7 G-5, G-6: proofs

**G-6(a)** is proved in 4.1 (identity checked there). **(b)** *Reduction of $G_{k,x}$.* Let $T:=a_k+x+aL^{-2}Q^*Q$ (unit lattice). Then $T$ is invertible, $T^{-1}=A_{k,x}$ and $a_k-a_k^2T^{-1}=\ldots$: $a_k-a_k^2A_{k,x}=a_k\frac{x+aL^{-2}Q^*Q}{a_k+x+aL^{-2}Q^*Q}=S_x$ (functional calculus on the two eigenspaces of the projection $Q^*Q$: on $I-Q^*Q$: $a_k-\frac{a_k^2}{a_k+x}=\frac{a_kx}{a_k+x}$; on $Q^*Q$: $\frac{a_k(x+aL^{-2})}{a_k+x+aL^{-2}}$), which are the two coefficients in (1.7). The Woodbury formula for $(T-a_k^2Q_kGQ_k^*)^{-1}$ (with $G=\tilde H^{-1}$... i.e. $G_D=(\tilde H+a_kQ_k^*Q_k)^{-1}$): $(T-a_k^2Q_kG_DQ_k^*)^{-1}=T^{-1}+a_k^2T^{-1}Q_k\big(G_D^{-1}-a_k^2Q_k^*T^{-1}Q_k\big)^{-1}Q_k^*T^{-1}$ and $G_D^{-1}-a_k^2Q_k^*T^{-1}Q_k=\tilde H+Q_k^*(a_k-a_k^2T^{-1})Q_k=\tilde H+Q_k^*S_xQ_k=G_{k,x}^{-1}$. Since $aL^{-2}Q^*Q+\Delta^{(k)}+x=T-a_k^2Q_kG_DQ_k^*$, this is $C_x^{(k)}=A_{k,x}+a_k^2A_{k,x}Q_kG_{k,x}Q_k^*A_{k,x}$, the first and second terms of P3 (3.9). The constraint term follows by the same block-matrix algebra from the Gaussian integral over $(\psi,\phi,\alpha)$ in P3 (3.7) at $\lambda=\infty$ (restriction of $\phi'$ to $\phi_0\cdot\phi'=0$; the Schur complement w.r.t. the constraint gives the third term with $[\phi_0G_{k,x}\phi_0]^{-1}$). The statement for the constrained term is the part of P3's "elementary Gaussian integrations" that is not shown (ER-046); at $\lambda=\infty$ it is a finite-dimensional Schur complement: $\mathrm{Cov}(\psi\,|\,\phi_0\cdot\phi=0)$.
**(c)** $G(\alpha)-G(\alpha')=G(\alpha)[H(\alpha')-H(\alpha)]G(\alpha')=-G(\alpha)(\alpha-\alpha')G(\alpha')$ ; the geometric resolvent identity is in 4.4.
**(d)** The three Woodbury lines are verified: with $A_0=-\Delta+\nu$, $S=QA_0^{-1}Q^*$ and $G=(A_0+aQ^*Q)^{-1}=A_0^{-1}-aA_0^{-1}Q^*(I+aS)^{-1}QA_0^{-1}$ one has $QG=(I+aS)^{-1}QA_0^{-1}$ and $GQ^*=A_0^{-1}Q^*(I+aS)^{-1}$, so $I-aQGQ^*=I-a(I+aS)^{-1}S=(I+aS)^{-1}$, $QG^2Q^*=(I+aS)^{-1}QA_0^{-2}Q^*(I+aS)^{-1}$ and $QGA_0GQ^*=(I+aS)^{-1}S(I+aS)^{-1}$; all three operators are translation invariant, hence commute (P4 p. 710, read: the printed third line agrees with ours). The Fourier symbols: $\widehat{QA_0^{-1}Q^*}(p)=\sum_l\frac{|u_m(p+l)|^2}{\Delta(p+l)+\nu}$ is the aliasing (Poisson summation) formula for the block average, and its Taylor data at $p=0$ (P4 (5.13)) are one-variable calculus with the quantities $c_i(\nu)$; the bounds $0<c_i(\nu)<\frac1{20}$ and $0<c_1-\nu c_2<\frac1{20}$ are elementary estimates of $\sum_{l\ne0}$ (C10; not re-derived here, to be done in the document on the renormalization equations, since only $f'(0)=0$, $f(0)$, $f''(0)$ are consumed).
**(e)** Leibniz: summation of $f(x\pm\eta e)g(x\pm\eta e)-2fg$; and for $K(h)$ the commutator of $H$ with multiplication by $h$.
**G-5(a),(b).** On a torus or $\mathbb Z^d$ the multiscale structure is a single layer $j$ with $\ell_j=1$, $\Omega_1=T_\eta$: G-2 applies with $\varrho$ irrelevant (one layer) and gives, for $y,y'$ unit-lattice points and $f=1_{B(y')}$ (so $\|f\|_\infty=1$): $|G_jQ_j^*(x,y')|\le B_0e^{-\gamma_0d(x,y')}$ for all $x$, i.e. $|a_jG_jQ_j^*(x,y)|\le ce^{-\delta|x-y|}$ with unit-lattice distance and $\delta=\gamma_0$ (the single-layer proof of 4.8 has no layers $j\ne1$ and uses Case 2 with $\rho=c_0$ throughout, so no $L$-dependence enters at all; uniform in the volume because only local estimates and $L^2$ decay are used). Taking the matrix elements of $a_jG_jQ_j^*$ against $Q_jG_jQ_j^*$ gives, by 4.7, the kernel decay of $\Delta^{(j)}_{tr}$ with $c_0,\delta_0$; then G-4 gives $|C_{tr}^{(j)}|\le ce^{-\delta|y-y'|}$ with $\mathrm{Re}(\Delta_{tr}^{(j)}+aL^{-2}Q^*Q)\ge\frac12\gamma_0'L^{-2}$ from G-1(b) with $\theta_0=0$. For (b): $\partial_\nu G=-G^2$ and $\|\partial_{\nu}(G_jQ_j^*)\|$ is bounded in the weighted $\ell^2$-norms by 4.5 (with $\|\ell^{-1}\|=1$) and pointwise by the argument of 4.8 applied to $G(\cdot)f$; hence Lipschitz in $\nu_j$ in the kernel norm after the weighted sum; $C^{(j)}_{tr}$ is Lipschitz by the resolvent identity of G-6(c) and G-4(a). Infinite-volume limits: tori $T_L\uparrow\mathbb Z^d$: the kernels converge along subsequences by the uniform bounds; uniqueness of the limit follows from G-4(b) (domain difference), which shows the kernels at a fixed point form a Cauchy family in the volume. UNCERTAIN: the symbol-based statements of P4 §5 (analyticity of $f,g,h$ in a strip) are not derived here; they follow from the decay in (a) by Fourier series with an exponentially decaying kernel (a strip of width $\delta$).
(d) The bound of P9 (4.14) is a computation with the kernel bounds of (a): by P9 p. 518 the sum $\sum_{j<k}\beta_j^{-1}e^{-\delta(\sqrt\nu+L^{-j})|x-y'|}$ uses the rate $\delta(\sqrt\nu+L^{-j})\le2\delta L^{-j}$ ($j<k(\nu)$, $\nu_j=\nu L^{2j}\le\frac78L^{-2}$) in original lattice units, which is rate $2\delta$ in scale-$j$ lattice units: one estimate (a), no separate $\sqrt\nu$ estimate. (This agrees with the roadmap's remark; BIG §2.9 and the E5 review item N7 should be read accordingly.)

### 4.8 What is proved, what is cited (summary)

Proved here in full: G-1(a), (a$'$), (b), (c); Lemmas 4.1–4.4; Proposition 4.5 and G-2(i), (vii, $L^2$ part); G-4(a)–(c) given the generalization of `combesThomas_core`; G-6(a)–(e); G-2(vi). Proved with short remaining routine steps (written out as lemmas and proofs but with some estimates only indicated, named in 5): Lemma K (one-dimensional heat kernel bounds), Lemma Loc, Lemma P and Propositions 4.8, 4.9 (G-2(ii)–(iv)); G-2(v) (Section 4.5a below); G-5. Cited: the Fourier-symbol data of P4 (5.13) (C10, not re-derived); the structure of $G_{k,x}$ and (3.9), (3.16)–(3.20) of P3 (their *use* is not proved: it belongs to I-4); E5 (2.60), (2.61) (we re-prove them); D1 Lemma 30 (re-proved in the multiscale form).

### 4.5a G-2(v), the constraint sandwich (proof)

Let $u=G f$ for $f\in\ell^2(\Omega_1;\mathbb C^N)$ and $Y_w=L^2(\Omega_1;\ell^2e^{2\gamma d(\cdot,y')})$, $\gamma\le\varepsilon_0$. Write $H=H_D(\alpha)$. For scalar $s$: $H(\phi_0s)=\phi_0Hs-K(\phi_0)s$ with $K(\phi_0)s=2\nabla\phi_0\cdot\nabla s+(\Delta\phi_0)s-[Q^*aQ,\phi_0]s$ (G-6(e), signs: $-\Delta(\phi s)=-\phi\Delta s-s\Delta\phi-2\nabla\phi\cdot\nabla s$ and $Q^*aQ(\phi s)-\phi Q^*aQs=[Q^*aQ,\phi]s$). Hence for $f\in\ell^2(\Omega_1;\mathbb C)$:
$H(\phi_0\cdot G\phi_0f)=\phi_0\cdot\phi_0f-K(\phi_0)\cdot G\phi_0f$, i.e. $\phi_0\cdot G\phi_0=G\,M$ with $M=\phi_0^2-K(\phi_0)\cdot G\phi_0$.
*Smallness of $K\!G\phi_0$ on $Y_w$.* By 4.5 with data $\phi_0f$: $\|w\partial G\phi_0f\|\le5\|\ell w\phi_0f\|\le8\|\ell wf\|$, $\|\ell^{-1}wG\phi_0f\|\le12\|\ell wf\|$. The three terms of $K$: $\|\ell w\,2\nabla\phi_0\cdot\nabla u\|\le2\delta_0\|w\partial u\|\le16\delta_0\|\ell wf\|$ (using $|\partial\phi_0|_1<\delta_0$, i.e. $\ell|\partial\phi_0|\le\delta_0$); $\|\ell w\,\Delta\phi_0\,u\|\le\delta_0\|\ell^{-1}wu\|\le12\delta_0\|\ell wf\|$ ($|\Delta\phi_0|_2<\delta_0$); the commutator: on a block $B$, $([Q^*aQ,\phi_0]s)=a_B\ell_B^{-2}(P_B(\phi_0s)-\phi_0P_Bs)$, $|P_B(\phi_0s)-\phi_0P_Bs|(x)\le\mathrm{osc}_B\phi_0\cdot\mathrm{avg}_B|s|\le d\delta_0\,\mathrm{avg}_B|s|$ ($\mathrm{osc}_B\phi_0\le d\ell_B\cdot\delta_0\ell_B^{-1}$ along a path in the block), so $\|\ell w[Q^*aQ,\phi_0]u\|\le2d\delta_0e^{\varepsilon d}\|\ell^{-1}wu\|\le cd\delta_0\|\ell wf\|$. Therefore $\|K(\phi_0)\cdot G\phi_0\|_{Y_w\to Y_w}\le c_*\delta_0$, $c_*=c_*(d)$, uniformly in $y'$, and $\|\phi_0^2-1\|_{Y_w\to Y_w}<\delta_0$. For $\delta_0\le\delta_*=(2(1+c_*))^{-1}$, $M=1+(\phi_0^2-1)-K G\phi_0$ is invertible on $Y_w$ with $\|M^{-1}\|\le2$ (Neumann series). Since $G$ is invertible (G-1(a)) we get $[\phi_0\cdot G\phi_0]^{-1}=M^{-1}H$ and
$$\Pi f=G\phi_0\,M^{-1}\,\big(\phi_0\cdot f-K(\phi_0)\cdot Gf\big)\qquad(f\in\ell^2(\Omega_1;\mathbb C^N)),$$
because $H(\phi_0\cdot Gf)=\phi_0\cdot f-K(\phi_0)\cdot Gf$ (the same identity applied componentwise). The factors: $f\mapsto\phi_0\cdot f-K(\phi_0)\cdot Gf$ is bounded on $Y_w$ (the second term by the same estimates, with $\|\ell wK(\phi_0)Gf\|\le c\delta_0\|\ell wf\|$), $M^{-1}$ is bounded on $Y_w$, and $G\phi_0:Y_w\to\{v:\|\ell^{-1}wv\|\le12\|\ell w\cdot\|\}$ by 4.5. So $\|\ell^{-1}w\,\Pi f\|\le C\|\ell wf\|$ and $\|w\partial\Pi f\|\le C\|\ell wf\|$, uniformly in $y'$; with $f$ supported in $\Delta(y')$ and $w=e^{\gamma d(\cdot,y')}$ this is the stated block bound (as in 4.6). The same proof for $G_{k,x}$ gives uniformity in $x\ge0$ because 4.5 does (G-1(a$'$)). *Consumption.* $\Pi$ is the operator in the third term of P3 (3.9) (up to the factors $A_{k,x}$, $Q_k$, $Q_k^*$) and in P4 (2.22)–(2.23); its unit-lattice kernel $Q_k\Pi Q_k^*$ decays by the same argument as 4.7. (This needs $\phi_0$ complex-valued with the bilinear dot product; all steps are algebraic.)

---

## 5. Size estimate and risks

Line counts are estimates for the Lean development in the style of the repositories in `review/FORMALIZATION_ROADMAP.md` §7; they include statements, but not the lattice, torus and block infrastructure of §7.3 item 1 of the roadmap, which G-1 and G-2 share (about 1,200 lines: tori, blocks, $Q_j,Q_j^*$, generating sets, the metric (1.9), zero extension, Dirichlet form).

| Piece | Content | Lean lines | Risk |
|---|---|---|---|
| G-1(a), (a$'$) | Lemma 4.1 (Poincaré by tensorized variance), Lemma 4.2, block bookkeeping, coercivity, invertibility | 1,200–1,800 | low; Lemma 4.1 in dimension $d$ is the longest part (Efron–Stein on a product lattice) |
| G-1(b) | Schur identity, minimization formula, $T(1+4T)^{-1}$ bound, subsidiary inequalities, Poincaré for Dirichlet box | 700–1,000 | low |
| G-2(i), (vii-$L^2$) | Proposition 4.5 (conjugation errors: Laplacian, block term), Lemma 4.3 (metric, separation), Lemma 4.4 (counting) | 2,500–3,500 | medium; the metric and counting lemma are fiddly, the Agmon algebra is routine |
| G-2(ii)–(iv) | Lemma K (heat kernel bounds, Fourier), Lemma Loc, Lemma P, 4.8, 4.9 | 6,000–10,000 (Lemma K alone 2,500–4,000) | **high**; Lemma K is the single largest item |
| G-2(v) | Section 4.5a | 800–1,200 | low once G-2(i) is available |
| G-2(vi) | locality and analyticity | 500–800 | low |
| G-4 | generalization of `combesThomas_core` (about 320 lines in the public file), (b), (c), application to $C^{(k)1/2}$ | 900–1,400 | low |
| G-5 | reduction to G-2 single layer, Lipschitz in $\nu$, limits | 800–1,200 | low to medium (infinite-volume limits) |
| G-6 | identities | 600–900 | low |
| G-3 (if kept) | cubes, Neumann reflection, Neumann series in kernels, 12-type walk | 3,000–5,000 | medium (index restrictions of (3.17)) |

Total without G-3: roughly 14,000–22,000 lines; the pointwise block (G-2(ii)–(iv)) is about half of it.

**Main risk.** The pointwise bounds of G-2 (Lemma K and Lemma Loc: discrete elliptic regularity uniform as $\eta\to0$): no discrete Caccioppoli, Moser, Schauder or Hölder estimate exists in the repositories surveyed in the roadmap (the closest are the continuum Moser/Caccioppoli files of `EllipticRegularity`, e.g. `DGNMAnchors/MoserLocalMax.lean`, `EllipticRegularity/Energy/CaccioppoliBall.lean`, the continuum Agmon template under `/home/scott/Superdiffusion/Algsuperdiff/StochasticProcess/Common/DivergenceForm/Decay/` (`ExponentialWeight`, `LocalizedInteriorPointwise`, `PointwiseDecay`), and the difference-quotient algebra in `/home/scott/CoarseGraining/Homogenization/Sobolev/Foundations/DifferenceQuotient.lean`, which can supply the discrete Leibniz/summation-by-parts lemmas of Lemma Loc). With the author's permission to reuse his repositories these are to be ported, not imported (they are continuum statements). A secondary risk: the interplay of the cutoff $\chi$ with the lattice (discrete derivatives of $\chi$ at scale $\rho\ge8\eta$); this is why Case 1 handles all layers with $L^j\le J_0$ by the inverse inequality.

**Other risks.**
1. The conjugation algebra of Proposition 4.5(3) (block term) and the choice of the metric (1.9) on straddling bonds: if the formalization changes (1.9), 4.3(a) and 4.5(2) must be redone together. The cost per bond $\eta/\ell(b)$ with $\ell(b)=\max$ was chosen so that 4.5(2) holds with $\ell(b)\ge\ell(x)$ at both endpoints.
2. Constants: $R_0(d,L)\sim1500\,d\log L$ is a bound, not an optimum; Balaban's $R$ is "fixed later" and is not an input to anything else here beyond $\varrho\ge R_0$. If the large-field document wants a smaller separation, 4.5 can be run with a smaller $\varepsilon$.
3. The Hölder part (4.9) is optional for the root as far as this document can see (one exponent, consumed only through P1 (3.107)); if the P1 document shows that (3.107) can be derived from the gradient bound, drop Lemma K's second-difference bound and 4.9 (saves 800–1,200 lines).
4. G-3 is not frozen; if I-4 needs the walk expansion the extra size is in the table.
5. Translation from the paper's $\lambda=\infty$ system: the statement (v) uses the bilinear dot product for complex $\phi_0$; the interface must state it explicitly.

---

## 6. Questions

1. (P1 document) Normalization of $\partial^2$ in P1 (3.107) and the exact use of $C_{\alpha_1}$: is $\partial^2\psi^{(j)}_k$ a second difference on the lattice of spacing $L^j\eta$ divided by the squared spacing? If it can be replaced by a bound that follows from $|\partial\phi_k|_1$ alone, the Hölder statement G-2(iii) and Lemma K's second difference bound can be dropped. (Asked of the P1 reader, not of Roland.)
2. (Localization document I-4) Is P3's (H.5) with exponent $\kappa-1$ reproduced by inclusion–exclusion plus G-2(vi) (Section 4.6 (3)), or must the walk expansion of P3 (2.12)–(2.23) be kept (G-3)? Decision needed before freezing; G-3 is not part of the proposed interface.
3. (Statement-level) For P4 (2.24): P4 states the bound "$-O(|\alpha_{k+1}|)\|\psi\|^2$" without saying whether $|\alpha_{k+1}|$ means $\sup|\alpha|$ on $\Omega_k$ or the scaled norm $|\alpha|_2$; our G-1(b) states it with $\theta_0=\sup_{\Omega_k}|\alpha|$ (unit scale), which for $\Omega_j=T_\eta$ ($j\le k+1$) equals $|\alpha_{k+1}|_2L^{-2}$-type quantities. If the large-field work needs the version with $\alpha$ of size $\ell^{-2}$ on layers $j<k$ it is the case of G-1(b) as written (layers $j<k$ allow $|\alpha|\le\frac1{16}\ell^{-2}$).
4. (Roland, optional) None required. His ruling (our own proofs) is used.

Open doubts marked UNCERTAIN in this document: (1) the relation of $d$ in (1.9) to P3 (2.4); (2) the normalization of $\partial^2$ in P1 (3.107); (3) reproduction of (H.5) by Section 4.6(3); (4) the symbol-analyticity statements of P4 §5; (5) the precise definition of $\Omega_{k+1}$ in (1.7) (P3 uses the generating set $\mathbb B_{k+1}$ with its $(k{+}1)$-st domain).
