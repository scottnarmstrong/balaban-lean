# I-6 on the anisotropic small-field domain

This is a mathematical specification for replacing the isotropic `Tube` proof of I-6. It uses the centred, Reynolds-averaged family and the infinite-volume stabilization specified in `CLASS-RULINGS.md`, Q-A and Q-C. All page numbers below are the printed page numbers of Balaban, *A low temperature expansion for classical N-vector models. I* (P1, CMP **167** (1995)); the formulas cited here were checked on the images of `/home/scott/Balaban/sources/BF02099355.pdf`. The definitions of `XiC` are those of `Balaban/SmallField/Xi.lean`; the inclusion theorem used below is `XiD2.psiTildeC_subset_xiC`. No change to `XiCBounds.hDot` is proposed.

## 1. Parameters, domains, and the source's three distinct radii

Write $e=e_{i_0}$, let $i_1\ne i_0$, and denote the effective level-$j$ mass by $v=\nu_j=\texttt{nuIdeal}\,L\,k\,\nu_k\,j>0$. The background mass in `Def6.XiDom` is $\mu=\texttt{bgMass}\,L\,k\,\beta_k\,\nu_k$: $\mu L^{2j}=v$ in the massive branch and $\mu=0$ in the other branch. In either case $\mu L^{2\ell}\leq v$ for $\ell\leq j$. In `RenormDefs` the parameter named `ν` is $v$. The term is a function of $b=vh$, with reference $(\psi,b)=(e,ve)$. Put $r_j=\varepsilon_j$. The class analyticity domain of a polymer $X$ is

$$
\Omega_{j,X}=\{\operatorname{pack}_X(\psi,b):\text{the level-$j$ block-constant lift of }(\psi,b/v)
\text{ belongs to }\operatorname{XiDom}(\mathrm{gs}_j(X),a,\mu,j,r_j)\}.
\tag{1.1}
$$

Here `gs_j(X)` means **`Tm.gs j X`**, with `IsSF.gs_spec`: $X\subset\Omega_1(\mathrm{gs}_j(X))$ and every layer above $j$ empty. For the infinite-volume family, (1.1) means the eventually stable local cylinder set for a fixed finite non-winding $X$; for an averaged term it is the finite intersection of the transported cylinder sets of its nonzero summands. The class's `localE` makes the choice of extension outside $X$ immaterial for the value of a term, although the extension is needed to prove domain membership. The open-set and common-germ arguments for this definition must be included in the lift proof.

P1 p. 123, (3.13)–(3.15), distinguishes $\sigma\varepsilon$ for spin gradients, $\sigma^2\varepsilon$ for the spin norm and $vh'$, and $\sigma^2\varepsilon^2$ for the component of $vh'$ along the reference spin. P1 p. 124, (3.18)–(3.21), gives the intermediate complex domain $\widetilde\Psi^c(\delta,\varepsilon_0)$ with $|vh'|<\delta^2/\varepsilon_0$ and $|v\psi_0\cdot h'|<\delta^2$, and states its inclusion in the class domain if $\varepsilon_0+K_1\delta\leq r_j$. The **landed** inclusion `psiTildeC_subset_xiC` uses the following stronger sufficient conditions:

$$0<\delta\leq\varepsilon_0,\qquad
\varepsilon_0+(2K_1+1)\delta\leq r_j,\qquad
\varepsilon_0\leq c_0,\qquad \delta\leq c_1,\qquad
\mu L^{2k}\varepsilon_0^2\leq\delta^2.
\tag{1.2}$$

The last condition is the background union-domain condition. For $\varepsilon_0=\delta$ it follows from `BgHyp.massLe`. The factor $2K_1+1$ is the **landed sufficient constant**, not a quotation of P1's $K_1$. One must not apply this theorem with P1's auxiliary choice $\delta_0=\sigma_1\varepsilon_{j+1}$, $\varepsilon_0=\varepsilon_{j+1}$ without checking $\mu L^{2k}\leq\sigma_1^2$: `BgHyp.massLe` only says $\mu L^{2k}\leq1$. The proof below instead applies the landed theorem with equal parameters $\delta_*=\varepsilon_*=r_j/B$, for which its mass condition is automatic.

### 1.1 A rectangular probe, including all three requested slices

Let $B=2K_1+2$ and $\delta_*=r_j/B$. Assume $0<\delta_*\leq\min(c_0,c_1,1/16)$ and `BgHyp.massLe`. Extend a level-$j$ spin configuration by $e$ outside $X$. The following **single product inclusion** is the useful Lean lemma:

$$
\begin{split}
&\sup_{x,i}|\psi_i(x)-e_i|<\frac{\delta_*}{8N},\\
&|b_{i_0}-v|<\frac{\delta_*^2}{8},\qquad
\sup_{i\ne i_0}|b_i|<\frac{\delta_*}{8N}
\quad\Longrightarrow\quad \operatorname{pack}_X(\psi,b)\in\Omega_{j,X}.
\end{split}\tag{1.3}
$$

In particular, fixing $b=ve$ gives a spin polydisc of radius $c_s r_j$, where $c_s=(8NB)^{-1}$; fixing $\psi=e$ and $b_\perp=0$ gives a longitudinal disc of radius $c_\parallel r_j^2$, where $c_\parallel=(8B^2)^{-1}$; fixing $\psi=e$ and $b_{i_0}=v$ gives a transverse polydisc of radius $c_\perp r_j$, where $c_\perp=(8NB)^{-1}$. These are radii for **$b=vh$**. The corresponding radii for $h$ are divided by $v$. The constants are conservative and independent of $j,k,X$ and the torus side. In the branch $\mu=0$, `XiCBounds.hAbs/hDot` are vacuous; the same discs are valid sufficient subsets of the larger class domain, while the source $\Sigma$ conditions still control the effective $b$ at evaluation.

**Proof of (1.3).** Use the real witness $(\Psi_0,h_0)=(e,e)$ and complex displacements $\Psi''=\psi-e$, $h''=b/v-e$, constant on each $j$ block; on the other data sites extend $\Psi''$ by zero. `IsSF.gs_spec` and `Def6BridgeDomain.isLayerConstant_of_jBlock` give the required layer constancy. In `InPsiTildeC G μ δ_* δ_*`, the real fields satisfy `r1`–`r4` strictly at $(e,e)$. A neighbour difference of $\Psi''$ is at most $2\sqrt N\delta_*/(8N)<\delta_*$ (`c1`), its Euclidean norm is less than $\delta_*/8<2\delta_*$ (`c2a`), and

$$| (e+\Psi'')^2-e^2|\leq 2|\Psi''_{i_0}|+\sum_i|\Psi''_i|^2
<\frac{\delta_*}{4N}+\frac{\delta_*^2}{64N}<\delta_*$$

(`c2b`). At every $x\in\Omega_1$, $\mu L^{2\ell(x)}\leq v$, so the mass-weighted norm of $h''$ is bounded by $|b_{i_0}-v|+\sum_{i\ne i_0}|b_i|<\delta_*$ (`c3a`, since $\delta_*^2/\delta_*=\delta_*$), while its component along $e$ is less than $\delta_*^2/8<\delta_*^2$ (`c3b`). Thus the datum is in `InPsiTildeC G μ δ_* δ_*`. Apply `psiTildeC_subset_xiC` using $\delta_*+(2K_1+1)\delta_*=r_j$, change its level to $j$ by `Def6BridgeDomain.xiC_level_irrel`, and package the four witnesses of `Def6.XiDom`. This is a direct strengthening of `Def6BridgeDomain.inPsiTildeC_of_close`: its common condition $N\rho<\delta_*^2$ is replaced by the two separate bounds in (1.3). No estimate of the complex background solution has been assumed beyond the cited landed inclusion theorem.

The spin slice actually used for Cauchy differentiation is centred at a constant configuration $(p,b)$ arising from the input data, in the analytic frame in which $p$ points along $e$. Its elementary version is: if a fixed lift $(p,b)$ lies in the *half-sized* box of (1.3), every spin perturbation $z$ with $\sup_{x,i}|z_i(x)|<\delta_* /(16N)$, with $b$ fixed, remains in (1.3). The proof is the triangle inequality; the half-box hypothesis must be proved from the source $\Sigma$ conditions and the scale-separation inequalities, not inferred merely from `DataHyp.mem_const`.

For interpolation $p+t(\psi-p)$ one needs a moving-centre version. P1 p. 133, Lemma 3.6, and p. 134, (3.58)–(3.59), give a real/complex extension of the restriction to $X$; its spin-square change is $<\delta_0/2$ and its real cone constraints have parameter $\delta_0/2$. **The Lean domain bridge must sharpen this extension at the actual data**: keep its real witness, use $\varepsilon=\varepsilon_k\ll\delta_*$ for the complex displacement, and allow a Cauchy increment of size $\delta_0/(6n)$, $1\leq n\leq4$. With $\delta_0<\delta_*$, $\varepsilon_k\leq\delta_*/8$, $\sigma\varepsilon_k\leq\delta_0/8$, and P1's (3.57), the triangle estimates in the proof of Lemma 3.6 give `c1`, `c2a`, `c2b` with parameters $(\delta_*,\delta_*)$; P1 (3.14) gives `c3a` from $\sigma^2\varepsilon_k<\delta_*$ and `c3b` from $\sigma^2\varepsilon_k^2<\delta_*^2$. The real `r1`–`r4` bounds with parameter $\delta_0/2$ also hold with $\delta_*$. Hence `psiTildeC_subset_xiC` applies at $(\delta_*,\delta_*)$, and (3.58) transports the resulting packed membership to the local term. This is the specific `moving_spin_slice` lemma to formalize. The inequalities involving $\varepsilon_k$ are obtained by increasing the fixed separation $n_1$; they are properties of the RG input scale, not new fields of Def-6. Transport through the complex frame needs equality of analytic germs on the overlap of the original and rotated packed domains; `Def6.IsSF.rotE` supplies the equality once both memberships are proved. The printed inclusion of the entire $\widetilde\Psi^c(\delta_0,\varepsilon_0)$ is not needed, so the extra mass condition that blocks a direct use of landed `XiD2` at those parameters is avoided.

### 1.2 The *printed* invariant-coordinate polydiscs

Choose $0<\delta_0\leq\varepsilon_0\leq 1/2$ and $\delta_0<\delta_*$. For a constant spin and field write $\psi=u e$, $h=z e+w e_{i_1}$. (The letter $z$ here is P1's variable $v$; $v$ in this note denotes the mass.) P1 p. 127, (3.29), gives the larger disc

$$|u-1|<\delta_0/3,\qquad |z-1|<\delta_0^2/v,\qquad
|w|<\delta_0^2/(\sqrt2\,v\varepsilon_0).\tag{1.4}$$

P1 p. 127, (3.31), gives the smaller disc

$$|u-1|<\delta_0/6,\qquad |z-1|<\delta_0^2/(2v),\qquad
|w|<\delta_0^2/(2v\varepsilon_0).\tag{1.5}$$

The last radii have denominators $\sqrt2\,v\varepsilon_0$ and $2v\varepsilon_0$, respectively. In $b$ coordinates they are $\delta_0^2/(\sqrt2\varepsilon_0)$ and $\delta_0^2/(2\varepsilon_0)$ for $b_{i_1}$. The function is even in $w$ and is hence expressed as $f_X(u,vz,v^2w^2)$.

**Invariant-disc inclusion lemma.** Every point of (1.4) lifts to `XiDom (Tm.gs j X) ... j r_j`, hence the restriction of a term to it is analytic and bounded by $M_X=E_0e^{-\kappa d_j(X)}$, provided $\delta_0<\delta_*$ and $\delta_0=\sigma_1\varepsilon_0$ with $\sigma_1\leq1$. Use the real witness $(e,e)$ and apply the landed inclusion at $(\delta_*,\delta_*)$. The spin-square displacement is at most $2\delta_0/3+\delta_0^2/9<\delta_*$; $v|z-1|<\delta_0^2<\delta_*^2$; and

$$v\bigl\|(z-1)e+w e_{i_1}\bigr\|_2
<\delta_0^2\sqrt{1+(2\varepsilon_0^2)^{-1}}
=\delta_0\sigma_1\sqrt{\varepsilon_0^2+1/2}<\delta_*$$

for $\varepsilon_0\leq1/2$. Since $\mu L^{2\ell}\leq v$, the mass-weighted $h''$ bound is no larger than the displayed bound. All neighbour differences vanish. Thus `InPsiTildeC G μ δ_* δ_*` holds; (1.2) at this **equal** parameter pair and `psiTildeC_subset_xiC` finish the proof. The inequality $\delta_0<\delta_*$ is a concrete numeric gap: with P1's $\sigma_1=\alpha/K_1$ and the class sequence $r_j/\varepsilon_{j+1}>L^\alpha$, it follows from $L^\alpha>(2+2/K_1)\alpha$. For $L\geq3$, $\alpha>0$, and the explicit landed $K_1\geq3$, the latter follows from $L^\alpha/\alpha\geq e\log L\geq e\log3>8/3$. This direct argument uses `BgHyp.massLe` only at $(\delta_*,\delta_*)$. The smaller disc (1.5) follows by containment.

For derivative coefficients of a localized term P1 further uses p. 138, (3.75):

$$|u-1|<\delta_0/6,\quad |z-1|<\delta_0^2/(4v),\quad
|w^2|<\frac1{32}\left(\frac{\delta_0^2}{v\varepsilon_0}\right)^2.\tag{1.6}$$

P1 pp. 142–143, (3.90), maps the constant-data domain into (1.6) when $\varepsilon\leq\varepsilon_0$ and $10\sigma\varepsilon_0\leq\delta_0$. Its bound for $W^2$ is proportional to $\sigma^4\varepsilon^2/v^2$, **not** $\sigma^4\varepsilon^4/v^2$; this exponent is visible on the p. 129 image in (3.43)–(3.44). It is essential for the final ratio $(\varepsilon/r_j)^2$.

## 2. Anisotropic analytic estimate for one term

Assume the P1 source data (3.13)–(3.15) at $(y,X)$, with $\varepsilon=\varepsilon_k$, $\sigma=C_0L^j\eta$, and the usual scale separation $j\leq k-n_1$. The `Σ1, Σ2` interface for Lean must record, or derive from a source-domain witness, all of the following: the spin-square and nearest-neighbour bounds already in `DataHyp`; $v|1-\widehat\psi(y)\cdot h|\lesssim\sigma^2\varepsilon^2$ and $v|h^2-1|\lesssim\sigma^2\varepsilon^2$ from (3.13); $|vh'|\lesssim\sigma^2\varepsilon$ and $|v\widehat\psi(y)\cdot h'|\lesssim\sigma^2\varepsilon^2$ from (3.14); the interpolation-domain condition of Lemma 3.6; and

$$\|\partial^2\psi\|_X\leq K_2\leq K_\alpha\sigma^{2-\alpha_1}\varepsilon,\qquad 0<\alpha_1<1.\tag{2.1}$$

P1 p. 147, (3.107), supplies (2.1) for the block field. `RenormDefs.DataHyp.b_close`, which says only $\|b-v\psi(y)\|\leq\sigma^2\varepsilon$, does not imply the $\sigma^2\varepsilon^2$ longitudinal bound. Membership in the *large* class domain `Dom` only gives an $r_j^2$ bound there. Therefore retaining exactly the old `DataHyp` while replacing `ρ` cannot justify the source proof. The replacement `DataHypAniso` should carry a witness of P1 (3.13)–(3.15), or the resulting three invariant bounds below, and the moving-centre inclusion.

Set $U=\sqrt{\psi(y)^2}$ (branch near 1), $V=\widehat\psi(y)\cdot(h+h')$, and $W^2=(h+h')^2-V^2$. P1 p. 128, (3.37)–(3.40), and p. 129, (3.41)–(3.44), prove

$$|U-1|<2\sigma^2\varepsilon,\qquad
|v(V-1)|<22\sigma^2\varepsilon^2,\qquad
|v^2W^2|<56\sigma^4\varepsilon^2.\tag{2.2}$$

The hypotheses include $v\leq\sigma^2$ and small $\varepsilon$. The third inequality follows from the exact identity (3.42); its first term is $|h^2-1|$, so it cannot in general have $\varepsilon^4$ in place of $\varepsilon^2$. P1 Lemma 3.3 then maps these invariants into (1.5) if $\varepsilon\leq\varepsilon_0$ and $7\sigma\varepsilon_0\leq\delta_0$. These are explicit fields or derived lemmas of `DataHypAniso`; they must be checked after the physical lift and Reynolds transport.

### 2.1 Constant-field potential of a single term

For $X$, define $F_X(p,b)=T.\mathrm{term}(X)(\operatorname{pack}_X(\mathrm{const}\,p,b))$. By its local $O(N)$ invariance, (1.4), and the identity theorem, it factors near $(e,ve)$ as $f_X(u,vz,q)$, $q=v^2w^2$, with $\|f_X\|\leq M_X$ there. The factorization needs $N\geq2$ and the real reflection changing $w$ to $-w$; it is a statement about the analytic germ. P1 p. 126, (3.25)–(3.28), proves the real invariant representation, and p. 127, (3.29)–(3.32), gives its analytic extension. On (1.5) the three-variable Cauchy estimate is, for $a,b,c\in\mathbb N$,

$$
\left|\partial_u^a\partial_{(vz)}^b\partial_q^c f_X\right|
\leq 8a!b!c!6^a2^b4^c M_X
\frac{\varepsilon_0^{2c}}{\delta_0^{a+2b+4c}}.
\tag{2.3}
$$

This is P1 (3.30) with $E_0K_0$ replaced by the single-term bound $M_X$; the factor $K_0$ in P1 comes from summing the polymers of the potential, not from Cauchy's theorem. Taylor's formula (3.32)–(3.33) gives a remainder bounded by

$$8M_X\left[\left(\frac{6|U-1|}{\delta_0}\right)^2+
\frac{6|U-1|}{\delta_0}\frac{2|v(V-1)|}{\delta_0^2}+
\left(\frac{2|v(V-1)|}{\delta_0^2}\right)^2+
\frac{4\varepsilon_0^2|v^2W^2|}{\delta_0^4}\right].\tag{2.4}$$

Insert (2.2), $\delta_0=\sigma_1\varepsilon_0$, and $\varepsilon\leq\varepsilon_0$. Each bracketed term is at most a constant depending on $\sigma_1$ times $\sigma^4(\varepsilon/\varepsilon_0)^2$. This proves, **termwise**, the potential remainder after subtracting the value and the two linear invariant coefficients of the landed `Ttw`. It does not set those coefficients to zero termwise. P1 p. 128, (3.34)–(3.36), sets their **sums** to zero using (H.6), the predecessor of the class's renormalization conditions.

### 2.2 Spatial Taylor expansion and the local remainder

The moving-centre inclusion above gives the spin-direction Cauchy bound of P1 p. 137, (3.67)–(3.68): for $1\leq n\leq4$ and $n$ spin increments supported in $X$,

$$\left|D_\psi^n E_X[\zeta_1,\ldots,\zeta_n]\right|
\leq (6n/\delta_0)^n M_X\prod_{a=1}^n\|\zeta_a\|_X.\tag{2.5}$$

The proof is one-variable Cauchy on the disc $|t|<\delta_0/(6n\|\zeta\|_X)$ in (3.67). The estimate differentiates only spin variables; it never charges a longitudinal $b$ derivative at a fictitious radius $r_j$. The fourth-order Taylor remainder of P1 pp. 134–135, (3.60)–(3.61), is bounded by $(24dLM)^4(\delta/\delta_0)^4M_Xe^{d_j(X)}$ after the path estimate (3.54)–(3.55). The coefficient functions in the first and second derivatives are controlled by the invariant discs and (2.3): P1 pp. 137–140, (3.69)–(3.81). Their remaining terms are estimated on pp. 141–146, (3.82)–(3.103).

More precisely, if $d_j(X)$ satisfies P1 (3.59), Lemma 3.8 on p. 146 gives the decomposition (3.104) for **one** $E(y,X)$ and the bound

$$
|E_{\mathrm{irrel},X}|
\leq C_{\mathrm{loc}} M_Xe^{d_j(X)}
\left[\sigma^3\left(\frac{\varepsilon}{\varepsilon_0}\right)^2+
\frac{\sigma\varepsilon}{\varepsilon_0^2}\|\partial^2\psi\|_X\right],
\quad C_{\mathrm{loc}}=\frac{K_1}{\alpha}\left(\frac{20dK_1LM^{1/\alpha}}{\alpha}\right)^4.
\tag{2.6}
$$

This is (3.105), with $M_Xe^{d_j(X)}=E_0e^{-(\kappa-1)d_j(X)}$. P1 p. 147, (3.107)–(3.108), inserts (2.1). Since $0<\sigma\leq1$ and $\alpha_1<1$, $\sigma^3\leq\sigma^{3-\alpha_1}$. Also $\varepsilon_0=\varepsilon_{j+1}$ is comparable to $r_j=\varepsilon_j$ by the explicit `Consts.eps` sequence; the comparison factor depends on the fixed $L,\alpha$ and is absorbed in $C$.

The landed `Itw` is $E_X-T_X-A_X-\Phi_X$, with `Ttw`, `Ax`, and `Phitw` in `RenormTermwiseDefs.lean`. Let $H_X$ be the sum of the first four displayed terms on the right of P1 (3.104), so $E_X=F_X+H_X+E_{\mathrm{irrel},X}$ exactly. The replacement algebra lemma to prove is

$$I_X=(F_X-T_X)+E_{\mathrm{irrel},X}+Q_X,\qquad
Q_X:=H_X-A_X-\Phi_X,\qquad
|Q_X|\leq C_QM_Xe^{d_j(X)}
\left[\sigma^3(\varepsilon/\varepsilon_0)^2+
\frac{\sigma\varepsilon}{\varepsilon_0^2}\|\partial^2\psi\|_X\right].\tag{2.6a}$$

Here is the coefficient calculation behind this lemma. Differentiate the **single-term** $O(N)$ identity as in P1 p. 151, (3.122)–(3.124), or invoke the already formalized `RenormExpand.ward_algebra`. For each $x$, $\sum_{x'}B_X(x,x')-a_X(x)+v m_X(x)=0$. Symmetry of $B_X$ then gives, for every pair of coordinate indices $\mu,\nu$,

$$\frac12\sum_{x,x'}B_X(x,x')r_{x,\mu}r_{x',\nu}
-\frac12\sum_x(a_X(x)-v m_X(x))r_{x,\mu}r_{x,\nu}
=-\frac14\sum_{x,x'}B_X(x,x')(r_x-r_{x'})_\mu(r_x-r_{x'})_\nu,\tag{2.6b}$$

where $r_x=x-y$. This is the frozen quadratic coefficient of $\Phi_X$ **without summing over polymers or invoking point-group isotropy**. The first-order longitudinal spin term of $H_X$ is $A_X$. For its $m_X$ term use P1 (3.83): $b\cdot\widehat\psi(x)-b\cdot\widehat\psi(y)$ equals its quadratic tangent part plus a remainder $Z_2$; (3.88), (3.91) bound $Z_2$ at order $\sigma^2\varepsilon^2(1+d_j(X))^2$. Insert the first-order coefficient bounds (3.77), the Hessian bounds (3.80)–(3.81), and the path remainders (3.98)–(3.103). These are the terms in $Q_X$, and each has the right side of (2.6a), by the same estimates used to prove (3.105). The terms proportional to $v\|\partial\psi\|^2$ are estimated with $v\leq\sigma^2$ as in the last term of `RenormLocal.TermOK.local_bound`. This proves (2.6a). The Euclidean cancellation used later is a separate sum-level step.

For $d_j(X)$ above the (3.59) threshold, P1 p. 136, (3.66), and p. 149, (3.116), use the direct bound on $E_X$ and the subtracted coefficients; P1 p. 149 explicitly bounds this large-polymer expression by the right side of (3.105). For the landed `Itw`, the same proof uses $|E_X|\leq M_X$, $|T_X|\leq C M_X[1+\sigma^2\varepsilon/r_j+\sigma^2\varepsilon^2/r_j^2]$, and the spin Cauchy bounds on $A_X,\Phi_X$. The threshold gives $1+d_j(X)\gtrsim r_j/(\sigma\varepsilon)$; use $e^{-d_j(X)}(1+d_j(X))^m\leq C_{m,q}(\sigma\varepsilon/r_j)^q$ with $q\geq3$ to absorb their polynomial factors. This is the exact large-polymer analogue of `RenormTermwiseCtx.CtxTw.tail_case`; it avoids trying to continue a long interpolation through one small domain.

Combining the two cases, (2.1), (2.4), (2.6), and the ratio comparison yields the requested termwise theorem, for the source range $0<\sigma\leq\sigma_2$ and $j\leq k-n_1$:

$$
|I(y,X;\psi,b)|\leq C E_0\,\sigma^{3-\alpha_1}
\left(\frac{\varepsilon_k}{\varepsilon_j}\right)^2
e^{-(\kappa-1)d_j(X)}.\tag{2.7}
$$

$C$ depends on fixed dimension, spin dimension, $L,M,K_1,\alpha,\alpha_1,C_0$ and the fixed scale comparison, not on $j,k,y,X$ or torus side. The proof uses only boundedness and $O(N)$ invariance of the **one** localized term, its packed-domain analytic germ, geometry, and the input data. It uses no termwise renormalization condition. For $\sigma>\sigma_2$, (2.7) is not asserted by P1 Lemma 3.8; the application of I-6 has $\sigma=C_0L^j\eta\leq\sigma_2$ after the prescribed separation $n_1$.

## 3. Ward identity, sum conditions, and the global I-6 statement

P1 p. 151, (3.122)–(3.124), applies to each $E_X$ as an identity of analytic germs. At $(e,ve)$ with the generator in the $(i_0,i_1)$ plane it reads

$$\sum_{x'}B_X(x,x')-a_X(x)+v,m_X(x)=0,\tag{3.1}$$

where $a_X$ is the longitudinal spin derivative and $m_X$ is the transverse mixed $h$–spin derivative (in the $b$ convention its coefficient is adjusted by $v$). It is the same relation used by `RenormExpand.ward_algebra`; the convention change must be checked when moving between `h` and `b`. P1 p. 152 applies (3.1) to the thermodynamic-limit density and obtains (3.125): after translation invariance, the remaining gradient coefficient equals $-\frac1{2d}\sum_z B_{\rm dens}(z,0)|z|^2$, hence vanishes by (H.7). The second-moment condition is on the **density summed over all centres**, as ruled in `CLASS-RULINGS.md`, Q-B. It is not an identity for each $X$.

For the Reynolds-averaged $T^\infty$ family, its centre sum is the same covariant density by Q-A, and its winding tail has disappeared by the stabilization of Q-C. Its point-group action makes the period-summed second-moment tensor scalar. The four `SumConds` therefore hold exactly for this infinite family. Sum (2.7) with `PremisesTerm.count_summable/count_le`, and use `SumConds` to cancel the summed `Ttw` and `Phitw` terms. The summed `Ax` is the explicitly retained local counterterm: `energy - Aterm = ∑' Itw` in the landed notation. This proves the local form of P1 Proposition 3.10, p. 152, (3.126)–(3.127). For the final RG data, (3.107) gives (2.1), and $\varepsilon_k/r_j\lesssim s_{jk}^{(d-2)/2-\gamma}$ with $\sigma=C_0s_{jk}$ gives

$$\sigma^{3-\alpha_1}(\varepsilon_k/r_j)^2
\lesssim s_{jk}^{d+1-2\gamma-\alpha_1}.
\tag{3.2}$$

This is P1 Corollary 3.11, pp. 152–153, (3.128)–(3.129), with $\alpha_3=1-2\gamma-\alpha_1$. The summation over scales in (3.130)–(3.131) is a geometric series because $\alpha_3>0$; it supplies the uniform effective-action bound. The finite-torus class provides the analytic estimates and uniform bounds; the exact cancellations are asserted only after passage to $T^\infty$.

## 4. Lean interface and exact replacement obligations

The following is specification syntax; it is **not** claimed to elaborate without the indicated domain and germ definitions. The types and field names make the intended change precise.

```lean
-- Is a stable, local, packed image of Def6.XiDom for gs j X, with b = νj • h.
-- For the averaged family, this is the finite intersection of transported images.
def XiPacked (T : TermFamily d N) (j : ℕ)
    (bridge : InfiniteXiBridge T j) (X : Finset (Site d)) :
    Set (Cfg d N X) := ...

structure PremisesTermAniso
    (T : TermFamily d N) (j : ℕ) (bridge : InfiniteXiBridge T j)
    (i₀ i₁ : Fin N) (νj rj E₀ κ A K₀ : ℝ)
    (Dom : Set ((Site d → Spin N) × Spin N)) : Prop where
  ne            : i₀ ≠ i₁
  zero_mem      : ∀ X ∈ T.polys, (0 : Site d) ∈ X
  dist_nonneg   : ∀ X ∈ T.polys, 0 ≤ T.dist X
  diam          : ∀ X ∈ T.polys, ∀ x ∈ X,
                    ((∑ μ, |x μ| : ℤ) : ℝ) ≤ A * (1 + T.dist X)
  count_summable : Summable fun X : T.polys => wt κ X.1 (T.dist X.1)
  count_le      : ∑' X : T.polys, wt κ X.1 (T.dist X.1) ≤ K₀
  radius_pos    : 0 < rj
  mass_pos      : 0 < νj
  analyticXi    : ∀ X ∈ T.polys, AnalyticOnNhd ℂ (T.term X) (XiPacked T j bridge X)
  boundXi       : ∀ X ∈ T.polys, ∀ c ∈ XiPacked T j bridge X,
                    ‖T.term X c‖ ≤ E₀ * Real.exp (-κ * T.dist X)
  boundDom      : ∀ X ∈ T.polys, ∀ p ∈ Dom,
                    ‖T.term X (pack X p.1 p.2)‖ ≤
                      E₀ * Real.exp (-κ * T.dist X)
  rotXi         : ∀ X ∈ T.polys, ∀ c ∈ XiPacked T j bridge X, ∀ R,
                    IsOrth R → EntryBd N R →
                    rotCfgL R X c ∈ XiPacked T j bridge X →
                    T.term X (rotCfgL R X c) = T.term X c
  sym_mem       : ∀ r, IsLatGen r → ∀ X ∈ T.polys, X.image r ∈ T.polys
  sym_inv       : ∀ r, IsLatGen r → ∀ X ∈ T.polys, ∀ ψ b,
                    T.term (X.image r) (pack (X.image r) (fun x => ψ (r x)) b) =
                      T.term X (pack X ψ b)

structure DataHypAniso (T : TermFamily d N) (j : ℕ)
    (bridge : InfiniteXiBridge T j)
    (Dom : Set ((Site d → Spin N) × Spin N))
    (νj σ ε K₂ : ℝ) (ψ : Site d → Spin N) (b : Spin N) : Prop where
  -- retain sq, bdd0, adj, sec, mem, mem_const, K2_nonneg of DataHyp
  basic          : DataHyp Dom νj σ ε K₂ ψ b
  -- P1 (3.13)–(3.15), with real (ψ₀,h₀) and complex (ψ',h') witnesses
  sourceSigma    : SourceSigma νj σ ε ψ b
  -- equivalently derive (2.2) and P1 Lemma 3.6 from sourceSigma
  invariantBound : InvariantBounds νj σ ε ψ b
  interpXi       : MovingSpinSlice bridge νj rj σ ε ψ b
```

`SourceSigma` must state the real/complex decomposition and the five inequalities of P1 (3.13)–(3.15), with the centre $y=0$ after translation; `InvariantBounds` is (2.2); `MovingSpinSlice` is the extension and Cauchy-disc assertion of Lemma 3.6. These last two should be **theorems from** `SourceSigma`, geometry and `XiPacked`, rather than extra Def-6 class fields. They are shown as fields only to locate the interfaces consumed by the proof. `InfiniteXiBridge` carries `gs_spec`, background hypotheses, the positive mass and scale identity, cylinder stabilization, and the transported domain used in Q-A. A mere arbitrary set `Ω X` with `Tube ⊆ Ω X` as in `PremisesTerm.ofDomain` is insufficient.

`RenormDefs.Premises` changes analogously: replace index `ρ` by $r_j$, its `analytic`, `bdd_tube`, `rot_inv` by `analyticXi`, `boundXi`, `rotXi`, and retain `bdd_dom` as `boundDom`; retain the six geometry/count fields and `sym_mem/sym_inv` for the averaged family. Keep `ren_val`, `ren_b`, `ren_psi`, `moment` **unchanged in formula** but apply them to $T^\infty$ and the density second moment, as in Q-B/C. `RenormTermwiseDefs.PremisesTerm` gets the same replacement but has no renormalization fields; `SumConds` and `Premises{,.Term}.toTerm/toPremises` only change their premise type. `RenormDefs.DataHyp` must be strengthened as above. The class-facing analytic fields of `Def6.IsSF` remain on `XiDom`; no `Tube` is added to Def-6. The old `ρ` field and ratio `ε/ρ` disappear from `Ctx`, `CtxTw`, and the I-6 theorem statements. The new ratio is $\varepsilon_k/r_j$.

The replacement theorem is:

```lean
theorem termwise_irrelevant_aniso
    (hP : PremisesTermAniso T j bridge i₀ i₁ νj rj E₀ κ A K₀ Dom)
    (hd : DataHypAniso T j bridge Dom νj σ ε K₂ ψ b) (hX : X ∈ T.polys)
    (hScale : SourceScale j k rj ε σ K₂) :
    ‖Itw T i₀ i₁ νj X ψ b‖ ≤
      C * E₀ * σ ^ (3 - α₁) * (ε / rj) ^ 2 *
        Real.exp (-(κ - 1) * T.dist X)
```

`SourceScale` includes (1.2) at the **equal** pair $(\delta_*,\delta_*)$, $\delta_*=r_j/(2K_1+2)$, the auxiliary choices $\varepsilon_0=\varepsilon_{j+1}$ and $\delta_0=\sigma_1\varepsilon_0$, the numeric gaps $\delta_0<\delta_*$, $\varepsilon_k\leq\delta_*/8$ and $\sigma\varepsilon_k\leq\delta_0/8$, the $\sigma\leq\sigma_2$ and $v\leq\sigma^2$ bounds, (2.1), and fixed scale comparison $\varepsilon_0\asymp r_j$. The scaled corollary replaces only $\varepsilon/\rho$ by $\varepsilon/r_j$ and invokes the unchanged real-power algebra. This states the source application range; a theorem for arbitrary `DataHyp` or all $\sigma\leq1$ would require additional work. The current `Def6.Consts.Admissible` gives only `α₀_pos`, so it does **not** supply the needed smallness of $r_j$. Since `bgK1` depends on the spin dimension $N$, add to `Def6.IsSFFamily` the fields `eps_one_small : P.eps d L 1 ≤ 1/2` and `eps_one_bg : P.eps d L 1 / (2 * bgK1 d L N + 2) ≤ min (bgC0 d L N) (bgC1 d L N)` (with $c_0\leq1/16$ by its definition). Monotonicity of `epsSeq` then gives these bounds at every $j\geq1$. This is P1's choice of sufficiently small $\varepsilon$ and P4's small $\alpha_0$, expressed as a class constant condition. The two remaining numeric gaps follow from $r_j/\varepsilon_{j+1}>L^\alpha$ and from increasing the fixed step separation $n_1$; they are theorem scale facts rather than Def-6 class fields.

### Landed lemma audit

| Lean declaration | Status and replacement |
|---|---|
| `RenormDefs.Tube`, `ball_subset_tube`, `TermOK.analytic_ball`, `TermOK.taylor_diff`, `TermOK.norm_tensA_le`, `TermOK.norm_D2_basis_le` | Their general Cauchy mathematics remains available. Replace each use of the isotropic membership by `xiPacked_spin_slice`, `xiPacked_invariant_disc`, or `moving_spin_slice`; the derivative conclusions have $c_s r_j$ for spin derivatives and the separate invariant radii (1.4)–(1.6). Do not derive a `TermOK i₀ ν ρ` with $ρ\asymp r_j$. |
| `RenormShape` algebraic invariance/derivative identities and `RenormExpand.ward_algebra`, `tensB_symm` | Algebra survives unchanged. Their `TermOK` wrappers need a new `TermOKXi`/germ hypothesis and an open neighbourhood for differentiation. The $b=vh$ convention in the mixed derivative is checked once in `ward_algebra_b`. |
| `RenormIso.lineQ_cov`, `tensB_cov`, `Sx_cov`, `moment_tensor`, `Lx_tsum_zero` | Proofs after the premises projection are unchanged; their hypotheses are the averaged $T^\infty$ family and `SumConds T∞`. The norm estimates inside `Sx_le` replace $M_X/ρ^2$ by $C M_X/r_j^2$ from the spin slice. |
| `RenormCtx.Ctx.zc_le`, `CtxTw.zc_le`, `term_rot`, `small_case`; `RenormLocal.TermOK.local_bound` | Replace the scalar bound on `zcfg` and isotropic ball by the longitudinal/transverse bounds and the moving spin slice. `local_bound_aniso` states (2.6) after the termwise Ward rewriting. The elementary `l1_le`, `rotDiff_le`, `ga_le`, `long_bounds`, `dotT_diff_bound` remain as proved. |
| `RenormPot.Ctx.potential_term`, `CtxTw.rem_bound` | Replace by `constant_potential_aniso`, namely (2.4) with (2.2), concluding $C M_X\sigma^4(\varepsilon/r_j)^2$. The old proof's $\rho^{-2}$ on all constant coordinates is invalid for longitudinal $b$. |
| `RenormSmall.smallBnd`, `Ctx.small_case`; `RenormTermwiseCtx.CtxTw.small_case`, `tail_case` | Replace the numeric small bound by (2.6) and the large-polymer estimate of §2.2. The case split, geometry and exponential-weight absorption remain valid after changing the threshold from $\rho/(\sigma\varepsilon)$ to $r_j/(\sigma\varepsilon)$. |
| `RenormTermwiseBound.CtxTw.itw_eq`, `ttw_eq`, `alpha_eq`, `beta_eq`; `RenormTermwiseDefs.Ttw`, `Phitw`, `Itw` | Algebraic definitions and equalities survive; the bound lemmas are replaced by `itw_bound_raw_aniso` from (2.4), (2.6) and the tail case. |
| `RenormTermwiseIrrel.termwise_irrelevant`, `_scaled`; `RenormTheorem.renormalization_local` | Replace statements by `termwise_irrelevant_aniso` above, its ratio-scaled corollary, and a local theorem summing the new `Itw`. Existing count summation and real-power arithmetic survive. |
| `RenormTermwiseSum.Ttw_tsum_zero`, `Phitw_tsum_zero`, `energy_sub_Aterm_eq_tsum_Itw` | Algebra and summability arguments survive after spin-Cauchy derivative bounds and the $T^\infty$ `SumConds` are supplied. `Phitw_tsum_zero` needs the averaged point-group action for isotropy; no symmetry of the original fixed-paving polymer family is asserted. |

The first files to prove are therefore the packed-domain product lemma (1.3), invariant-disc inclusion (1.4), moving spin slice, source-data invariant bounds (2.2), and the spin/invariant Cauchy estimates. Only after those lemmas are available should the old `ρ` be removed from theorem signatures. These are proof obligations, not additional axioms of the class.
