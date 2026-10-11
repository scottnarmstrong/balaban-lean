# BACKGROUND: the background fields of Balaban's variational problems at $\lambda=\infty$

Phase-1 document D-V. Author: analyst session (Sonnet), 2026-10-11. Mathematics on paper only; no Lean was
written or run. Source for freezing the interfaces I-1, I-2 and the definitions Def-5, and for writing
their Lean proofs. Not yet independently reviewed.

Sources read for this document: P2 (CMP 175, `sources/BF02099510.pdf`; page images read for pp. 610, 611, 630–636,
641–642, i.e. PDF pages 4, 5, 24–31, 35, 36; the rest of §3 via `review/papers/P2-variational-problems.md`),
`notes/phase1/GREEN.md` (Rev. 2), `notes/ERRATA.md` (P2 rows ER-026 to ER-041), roadmap §3.3 and Def-5, and the landed Lean
in `Balaban/Background`, `Balaban/Multiscale`, `Balaban/Analysis`.

**Status key.** *proved* = every step is written here and uses only landed Lean, GREEN.md statements marked ready, or
standard facts; *cited* = taken from a named statement elsewhere; *sketched* = the estimates are listed but the proof is
not written out; UNCERTAIN: marks a doubt.

---

## 0. Summary of results

All statements are at $\lambda=\infty$ (hard spins, $|\phi(x)|=1$), in the units of the landed Lean (§1.1).

* **I-1** (P2 Prop 1.1, Cor 1.1, Prop 3.1). There are $c_0,c_1,K_1,c_6,K_2>0$ depending only on $(d,L,N)$ such that for every
  generating set $\mathbb B_k$ with separation $\varrho\ge R_0$, admissible weights, mass $0\le\mu\le L^{-2k}$ and data in
  $\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ with $0<\delta\le\varepsilon\le c_0$, $\delta\le c_1$, $\mu L^{2k}\varepsilon^2\le\delta^2$, the
  system $H_D(\alpha)\phi=S$, $\phi\cdot\phi=1$ has exactly one solution with $|\alpha|_2<c_0$; it is analytic in the data, obeys
  P2 (1.15)–(1.16) (Theorem 5.2), and for real data it is the unique global minimiser of the hard-spin action. The
  perturbed system with independent data (P2 Prop 3.1) is Proposition 5.1: unique solution with $|\delta\alpha|_2<c_6$,
  analytic, with all norms $\le K_2\delta_1$. *Status: Prop 5.1 proved (complete contraction proof from G-2(iv)); the
  approximate solution (Lemma 5.3) sketched with all estimates listed; Theorem 5.2 proved from them.*
* **I-2** (P2 Prop 4.1). For $\mathbb B_j\prec\mathbb B'_k$ and $(\psi',h)\in\tilde\Psi(\mathbb B'_k;\delta)$ the field
  $\psi(\mathbb B_j,\mathbb B'_k;\psi')$ given by (6.2) (P2 (4.21)) lies in $\tilde\Psi(\mathbb B_j;C_4K_1\delta)$, is the unique
  critical point of the composed action, and $\phi(\mathbb B_j;\psi(\mathbb B_j,\mathbb B'_k;\psi'))=\phi(\mathbb B'_k;\psi')$,
  $\alpha(\mathbb B_j;\cdot)=\alpha(\mathbb B'_k;\psi')$ on $\Omega_1$, also for complex data and for the perturbed system (4.41)–(4.43).
  *Status: the formula and the composition identities are proved (a pointwise algebraic identity, valid for any
  weights and complex data, no analytic continuation); the domain-membership Lemmas 4.3/4.4 are sketched with every
  estimate listed.*
* **Def-5.** $\phi(\mathbb B_k;\psi,h)$ := the unique minimiser of $A$ over the product of spheres, defined (with proof argument)
  where the minimiser is unique; $\alpha(\mathbb B_k;\psi,h)$ := its Lagrange multiplier; complex extensions
  $\phi^c,\alpha^c$ := the unique solution with $|\alpha|_2<c_0$ on $\tilde\Psi^c(\mathbb B_k;c_1,c_0)$;
  $\psi(\mathbb B_j,\mathbb B'_k;\psi')$ := formula (6.2). Characterization theorems in §7.
* **Main risk.** The approximate solution $(\phi_0,\alpha_0,f_0)$ (Lemma 5.3) on the multiscale lattice: a partition of unity
  across layer interfaces and about twenty first/second-difference estimates; this is $\approx 40\%$ of the Lean work.
  The Green's function input is only $|G(\alpha)f|_0+|\partial G(\alpha)f|_1\le B_1|f|_2$ uniformly on the polydisc,
  i.e. G-2(iv) (W16, in progress); nothing else of G-2 is used by I-1.
* **Findings that change the plan.** (a) The fixed-point step does not need the inverse of $\phi_0\cdot G\phi_0$: the Leibniz
  identity turns the constraint into $\delta\alpha=\mathcal N(\delta\alpha)$ with a small Lipschitz constant (§5.1); the
  constrained operator $\Pi$ enters only the linear response (§5.5). (b) For real data the minimiser property is an exact
  identity (§5.4), so P2 (3.48) and any second-variation argument disappear. (c) P2's review prints (1.15) with an extra
  factor $(L^j\eta)^{-1}$ on the first line; the page image (p. 611) shows $|\phi-Q^*(\psi+\psi')|<K_1\delta$. (d) P2 Prop 2.2
  (ER-030) has an exact formula and a short complete proof at $\lambda=\infty$ (§4.3).

---

## 1. The problems at $\lambda=\infty$

### 1.1 Setting and units

We use the units of the landed Lean (`Balaban/Multiscale/GeneratingSet.lean`): lattice spacing $\eta=1$, so P2's $L^j\eta$ is
$\ell_j=L^j$, the fine torus is $\mathbb T=(\mathbb Z/S\mathbb Z)^d$ with $S=N_0L^k$ (`Torus d (N₀ * L ^ k)`), $d\ge3$, $L\ge3$,
spins in $\mathbb R^N$ (or $\mathbb C^N$), $N\ge2$.

*Generating set* $G=\mathbb B_k$ (P2 (1.1)–(1.3), Lean `GeneratingSet d L N₀ k ϱ`): $\Omega_1\supseteq\dots\supseteq\Omega_k$,
$\Omega_{k+1}=\emptyset$, $\Omega_j$ a union of $j$-blocks (side $L^j$), separation $\mathrm{dist}(\Omega_j^c,\Omega_{j+1})>\varrho L^j$,
$\varrho=RM$. Layers $\Lambda_n=\Omega_n\setminus\Omega_{n+1}$ (a disjoint union of $n$-blocks); the layer index $n(x)$ and the spacing
$\ell(x)=L^{n(x)}$ for $x\in\Omega_1$ (`spacing`). *Collar* $C=C(\Omega_1)=\{x'\notin\Omega_1:x'\sim x\text{ for some }x\in\Omega_1\}$.
Because $\mathrm{dist}(\Omega_1^c,\Omega_2)>\varrho L\ge1$, every $x\in\Omega_1$ with a neighbour in $C$ lies in layer 1 (**wall sites are in layer 1**).
The collar plays the role of P2's $\Lambda_0$ ((1.2), (1.13): "one layer of big blocks surrounding $\Omega_1$"; UNCERTAIN whether P2's
$\Lambda_0$ is exactly this one-site collar or a thicker collar of blocks; only the values on $C$ enter the equations, and the conditions
on a thicker collar would be implied, see §1.3).

*Weights* $a:\mathbb N\to\mathbb R$, $a_n\in[\frac12,2]$ (Lean `IsAdmissibleWeights`); P2's $a_j=\frac{1-L^{-2k}}{1-L^{-2j}}a_k$ with
$\frac12<a_k<\frac32$ gives $a_j\in(\frac12,\frac{27}{16})$ (GREEN (1.5)). *Mass* $\mu\ge0$ in fine units; the unit-scale mass of P2 is
$\nu_*=\mu L^{2k}$ and P2's hypothesis $0<\nu\le1$ is $0\le\mu\le L^{-2k}$ (P2's $\nu\eta^2$; the lower bound $\nu>0$ is not needed,
the $\mu=0$ case being needed by P7 and P9, GREEN §1.2). At scale $n$ the local scaled mass is $\nu_n=\mu L^{2n}\le1$.

*Operators* (Lean `dirichletOperator G a μ α`, GREEN (1.6)). For $u:\Omega_1\to\mathbb C$ with zero extension $\tilde u$:
$$H_D(\alpha)=-\Delta^D_{\Omega_1}+Q^*aQ+\mu+\alpha,\quad (Q^*aQ\,u)(x)=a_nL^{-2n}(P_{B_n(x)}u)(x),\quad G(\alpha)=H_D(\alpha)^{-1}$$
acting on each of the $N$ components ($P_B$ = block average). Here $-\Delta^D_{\Omega_1}u(x)=(-\Delta\tilde u)(x)$ for $x\in\Omega_1$.

*Norms* (GREEN §1.5; P2 (3.17); the Hölder norm is not used in the fixed-point step). For $f$ on $\Omega_1$:
$|f|_\sigma=\sup_{x\in\Omega_1}\ell(x)^\sigma|f(x)|$; $|\partial u|_1=\sup_b\bar\ell(b)\,|\partial\tilde u(b)|$ over bonds $b$ with at least one endpoint in
$\Omega_1$, $\bar\ell(b)$ the larger spacing of its endpoints in $\Omega_1$ (Lean `bondCost`); $\|u\|_*:=|u|_0+|\partial u|_1$. Vector values use
the Euclidean norm of $\mathbb C^N$ (constants then depend on $N$; P2 states dependence on $d,L$ only). Write $u\cdot v=\sum_iu^iv^i$
(**bilinear**, no conjugation).

### 1.2 The variational problem and its Euler–Lagrange system

*Data.* A *lifted block-spin field* $\Psi:\mathbb T\to\mathbb C^N$ that is constant on every $n$-block of layer $n$, $1\le n\le k$
($\Psi|_{\text{block }y}=\psi_n(y)$, so $\Psi|_{\Omega_1}=Q^*\psi$ in P2's notation), with arbitrary values $\psi_0=\Psi|_C$; a field
$\tilde h$ on $\Omega_1$, constant on blocks (for real data $\tilde h\equiv h\in\mathbb R^N$). Source
$$S(\Psi,\tilde h)(x)=a_nL^{-2n}\Psi(x)+\mu\tilde h(x)+\sum_{x'\in C,\,x'\sim x}\Psi(x')\qquad(x\in\Omega_1,\ n=n(x)).\tag{1.1}$$

*Real problem.* For real $(\Psi,h)$ minimise over $\phi\in(S^{N-1})^{\Omega_1}$ (i.e. $|\phi(x)|=1$)
$$A(\phi)=\tfrac12\sum_{n=1}^k\sum_{y\in\Lambda_n}a_nL^{-2n}L^{nd}\,|\psi_n(y)-(Q_n\phi)(y)|^2+\tfrac12\sum_b|\partial\bar\phi(b)|^2+\tfrac\mu2\sum_{x\in\Omega_1}|\phi(x)-h|^2,\tag{1.2}$$
$\bar\phi=\phi$ on $\Omega_1$, $\bar\phi=\Psi$ on $C$, sum over bonds with an endpoint in $\Omega_1$. This is P2 (1.4) with $\lambda_k=\infty$ in fine units: P2's
three terms carry the common factor $\eta^{d-2}$ after rescaling and the mass becomes $\nu\eta^2=\mu$ (checked against the Lean
`avgMatrix`: $\sum_n\frac{a_n}{L^{2n}}\mathbb 1_{\Lambda_n}P_n\mathbb 1_{\Lambda_n}$). The generating-set problem of P2 (1.10)–(1.12) is this one. A minimiser
exists (compactness).

*Euler–Lagrange system (EL).* Differentiating (1.2) with the constraint $\frac12(|\phi(x)|^2-1)=0$ and multiplier $\alpha(x)$ (P2 (1.7)–(1.9), (1.10) at
$\lambda=\infty$; $\frac1\lambda\alpha\to0$):
$$H_D(\alpha)\phi=S(\Psi,\tilde h)\ \text{ on }\Omega_1,\qquad \phi\cdot\phi=1\ \text{ on }\Omega_1.\tag{EL}$$
Indeed $\partial A/\partial\phi(x)=(-\Delta\bar\phi)(x)+a_nL^{-2n}(Q_n\phi(y)-\psi_n(y))+\mu(\phi-h)(x)$ and $-\Delta\bar\phi=-\Delta^D\phi-\sum_{x'\in C}\Psi(x')$. For real
data every minimiser satisfies (EL) with the real multiplier $\alpha(x)=-\phi(x)\cdot(H_D(0)\phi-S)(x)$ (the constraint gradient $2\phi(x)\ne0$;
constraint qualification holds pointwise). The constant case is the landed `Balaban/Background/ConstantConfig*.lean`: for $\Omega_1$ a single block of
scale $n$ with constant data it reads $(a_n+\nu_n+\hat\alpha)\phi=a_n\Psi+\nu_nH$, $\phi\cdot\phi=1$, $\hat\alpha=L^{2n}\alpha$.

*What "solution" means for complex data.* For complex $(\Psi,\tilde h)$ a *solution* is a pair $(\phi,\alpha)$, $\phi:\Omega_1\to\mathbb C^N$,
$\alpha:\Omega_1\to\mathbb C$, satisfying (EL) with the **bilinear** constraint $\phi\cdot\phi=1$ and the size restriction $|\alpha|_2<c_0$. It is
a critical point, in general not a minimiser of anything. The restriction $|\alpha|_2<c_0$ is what selects it: the constant case has the
second branch $\phi\to-\phi$, $\hat\alpha=-\sqrt{w\cdot w}-a-\nu$ (Lean `eq_of_isCEL`: uniqueness under $\|\alpha\|<a+\nu$ with no assumption on the data).
The data of (EL) enter affinely through (1.1), so the solution map is a map between finite-dimensional complex vector spaces; "analytic" is the
usual notion on the open domain of §1.3, and no infinite-dimensional topology is involved (this settles ER-036: uniformity is in the bounds, not in the
analyticity).

### 1.3 The data domains $\tilde\Psi$ and $\tilde\Psi^c$ at $\lambda=\infty$

Translation of P2 (1.11), (1.12) (page 610, read) into fine units. Call two blocks *adjacent* if some sites of them are neighbours; each collar site
counts as a block of layer 0 (side 1). Write $(\psi)_0=\psi/|\psi|$. A pair $(\Psi,h)$ with $\Psi$ and $h\in\mathbb R^N$ real belongs to $\tilde\Psi(\mathbb B_k;\delta)$ if

* (R1) $|\psi_n(y)-\psi_{n'}(y')|<\delta$ for adjacent blocks $y$ (layer $n$), $y'$ (layer $n'$) with $n'=n$ or $n'=n-1$ ($n\ge0$; this contains the collar
  bonds and the interface bonds P2 prints as $|\psi_j(b_+)-\psi_{j-1}(x)|<\delta$, $x\in B(b_-)$);
* (R2) $\big||\psi_n(y)|^2-1\big|<\delta$, $0\le n\le k$;
* (R3) $\mu L^{2n}\,|1-(\psi_n(y))_0\cdot h|<\delta^2$, $0\le n\le k$ (P2: $|\nu(1-(\psi_j(x))_0\cdot h)|<(L^j\eta)^{-2}\delta^2$);
* (R4) $\mu L^{2k}\,|h\cdot h-1|<\delta^2$ (P2 prints $|\nu(|h|^2-1)|<\delta^2$, confirmed on the image; for $|h|=1$ void).

A complex pair $(\Psi+\Psi',\ h+h')$ belongs to $\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ if $(\Psi,h)\in\tilde\Psi(\mathbb B_k;\delta)$ and the fields $\Psi'$ (layers $0..k$) and $h'$ (layers $1..k$, block-constant) satisfy

* (C1) $|\psi'_n(y)-\psi'_{n'}(y')|<\delta$ for the adjacent pairs of (R1);
* (C2) $|\psi'_n|<\varepsilon+\delta$ and $|(\psi_n+\psi'_n)\cdot(\psi_n+\psi'_n)-\psi_n\cdot\psi_n|<\delta$;
* (C3) $\mu L^{2n}|h'_n|<\delta^2/\varepsilon$ and $\mu L^{2n}|(\psi_n)_0\cdot h'_n|<\delta^2$.

Both sets are open (finitely many strict inequalities). UNCERTAIN: P2 does not say whether $h'$ lives on $\Lambda_0\cup\mathbb B_k$ as a field or is constant
($(1.16)$ writes $Q^*h'$, which suggests a field on $\mathbb B_k$); we take a block-constant field, which contains the constant case. Condition (R3) at
$n=0$ and the conditions on $\psi_0$ beyond (R1), (R2) are not used by the proofs below (the collar enters only through (R1), (R2) at layers $0,1$).
The parameter $\varepsilon$ appears only through (C2), (C3), and the hypothesis $\mu L^{2k}\varepsilon^2\le\delta^2$ (P2: $\nu\varepsilon^2\le\delta^2$) is what makes
$\nu_n\varepsilon\le\sqrt{\nu_n}\,\delta\le\delta$ in §4.1.

---

## 2. Inputs used

| Input | Statement used | Where | Status |
|---|---|---|---|
| G-1 coercivity | $\mathrm{Re}\langle u,H_D(\alpha)u\rangle\ge\frac14(\|\partial\tilde u\|^2+\|\ell^{-1}u\|^2)$ for $|\alpha|\le\frac1{8}\ell^{-2}$; $H_D(\alpha)$ invertible; real $\alpha$: $H_D(\alpha)$ positive definite | `multiscale_coercive_sharp`, `dirichletOperator_isUnit_sharp` (CoercivitySharp) | landed |
| G-2(iv) | **(G)**: there is $B_1(d,L,N)$ with $\|G(\alpha)f\|_*=|G(\alpha)f|_0+|\partial G(\alpha)f|_1\le B_1|f|_2$ for all complex $\alpha$ with $|\alpha|_2\le\gamma_1:=\frac18$ and all $f$ (any $\varrho\ge R_0$, $\mu\le L^{-2k}$) | W16 (from landed `prop48`, `sum_siteWeight_decay_le`) | **in progress**; the only quantitative Green input of I-1 |
| Analyticity of $G$ | entries of $G(\alpha)$ analytic in $\alpha$ on the polydisc | `analyticOnNhd_green_apply` | landed |
| Constant configurations | $\phi=w/\sqrt{w\cdot w}$, $\hat\alpha=\sqrt{w\cdot w}-a-\nu$, uniqueness, analyticity, norm bounds, polydisc | `cMinimizer`, `cMultiplier`, `eq_of_isCEL`, `analyticOnNhd_cMinimizer`, `cNorm_cMinimizer_sub_le`, `mem_cDomain_of_near`; real: `constMinimizer`, `constMinimizer_le`, `constObjective_eq` | landed |
| Analytic contraction | unique fixed point of a $\theta$-contraction analytic in parameters is analytic, $\|\xi^*\|\le\|T(0,p)\|/(1-\theta)$ | `Balaban.Analysis.exists_analytic_fixedPoint` | landed |
| Constrained operator | $\Pi=\mathrm{constrainedOp}$, $\phi\cdot G\phi$ invertible, $M=\phi_0^2-K\,G\phi_0$ sandwich, weighted and block decay, $\Pi\succeq0$ for real data | `constraintForm_isUnit`, `constrainedOp_eq`, `constrained_weighted_bounds`, `constrained_G2v`, `constrainedOp_dirichlet_posSemidef`, `IsSmoothField` | landed (used only in §5.5) |
| Smooth fields | `IsSmoothField G δ φ`: $|\phi(x\pm e)-\phi(x)|\le\delta/\ell(x)$, $|\Delta\phi(x)|\le\delta/\ell(x)^2$ at $x\in\Omega_1$ | ConstraintField | landed |

Not used: the O(N) reduction `Balaban/Symmetry` (the constant solution is dimension-free and explicit), the Hölder bound G-2(iii) (only for the
last line of Theorem 5.2), the global-in-$\lambda$ bound C3 (it disappears, §8).

---

## 3. Calculus on the multiscale lattice (all proved)

Throughout, $\phi_0:\mathbb T\to\mathbb C^N$ is a field with `IsSmoothField G δ₀ φ₀` (so $|\partial\phi_0|_1\le\delta_0$, $|\Delta\phi_0|_2\le\delta_0$ at points of $\Omega_1$,
neighbours in the collar included), $\alpha_0:\Omega_1\to\mathbb C$ with $|\alpha_0|_2\le\delta_0$, $\delta_0\le\gamma_1$, and $H_0:=H_D(\alpha_0)$. Let $\Delta_e f(x)=f(x+e)-f(x)$ for the $2d$ unit
vectors $e$; $\Delta f(x)=\sum_e\Delta_ef(x)$. The exact discrete Leibniz rule is
$$\Delta(uv)=u\Delta v+v\Delta u+\sum_e\Delta_eu\,\Delta_ev,\tag{3.1}$$
since $u(x+e)v(x+e)-uv=u\Delta_ev+v\Delta_eu+\Delta_eu\Delta_ev$. For $x\in\Omega_1$ the bond bound gives $|\Delta_eu(x)|\le\|u\|_*\,/\ell(x)$ for every neighbour (zero extension, so
wall bonds are included), because $\bar\ell(b)\ge\ell(x)$.

**Lemma 3.1 (commutator).** For $v:\Omega_1\to\mathbb C^N$ put $Kv:=\phi_0\cdot H_0v-H_0(\phi_0\cdot v)$. Then $|Kv|_2\le(1+2d)\,\delta_0\,\|v\|_*$.

*Proof.* The terms $\mu,\alpha_0$ commute with multiplication. By (3.1), $-\phi_0^i\Delta v^i+\Delta(\phi_0^iv^i)=v^i\Delta\phi_0^i+\sum_e\Delta_e\phi_0^i\Delta_ev^i$, so
$$Kv=\sum_i\Big[v^i\Delta\bar\phi_0^i+\sum_e\Delta_e\bar\phi_0^i\Delta_e\tilde v^i\Big]-\sum_i[Q^*aQ,\phi_0^i]v^i .$$
Multiply by $\ell(x)^2$: the first term is $\le\delta_0|v|_0$ (Cauchy–Schwarz for the bilinear sum, $|\Delta\phi_0|_2\le\delta_0$); the second is $\le2d\,(\delta_0/\ell)(\|v\|_*/\ell)\,\ell^2$. For the commutator,
on a block $B$ of layer $n$ (all of whose sites have spacing $L^n$, and $B\subset\Omega_1$ because the layers are unions of blocks), $[Q^*aQ,\phi_0^i]v^i(x)=a_nL^{-2n}\,\mathrm{avg}_{y\in B}(\phi_0^i(y)-\phi_0^i(x))v^i(y)$; the $\ell^1$
diameter of $B$ is less than $dL^n$ and each step has $|\Delta_e\phi_0|\le\delta_0L^{-n}$, so $|\phi_0(y)-\phi_0(x)|\le d\delta_0$ and the term is $\le2d\delta_0|v|_0\,\ell^{-2}$. Sum: $\delta_0(1+2d)|v|_0+2d\delta_0|\partial v|_1$. $\square$

**Lemma 3.2 (quadratic remainder).** For $v:\Omega_1\to\mathbb C^N$ put $R(v):=H_0(v\cdot v)-2v\cdot H_0v$. Then $R$ is a quadratic form and $|R(v)|_2\le(8+2d)\|v\|_*^2$; hence
$|R(v)-R(v')|_2\le(8+2d)\,\|v-v'\|_*(\|v\|_*+\|v'\|_*)$.

*Proof.* With $w=v^i$: $H_0(w^2)-2wH_0w=-\sum_e(\Delta_ew)^2+[Q^*aQ(w^2)-2wQ^*aQw]-(\mu+\alpha_0)w^2$ by (3.1). Times $\ell^2$: the first is $\le2d\|\partial w\|^2$ (as above), the
second $\le 2\cdot3|w|_0^2$ ($a_n\le2$, $|\mathrm{avg}\,w^2|+2|w||\mathrm{avg}\,w|\le3|w|_0^2$), the third $\le(\mu\ell^2+\delta_0)|w|_0^2\le2|w|_0^2$, using $\mu\ell^2\le\mu L^{2k}\le1$. Sum over $i$ with
Cauchy–Schwarz. The Lipschitz bound is polarisation of the bilinear form. $\square$

**Lemma 3.3 (resolvent differences).** Assume (G). For $|\alpha|_2,|\alpha'|_2\le\gamma_1$: $G(\alpha)-G(\alpha')=-G(\alpha)(\alpha-\alpha')G(\alpha')$ and
$\|(G(\alpha)-G(\alpha'))f\|_*\le B_1^2\,|\alpha-\alpha'|_2\,|f|_2$.

*Proof.* The identity is $H(\alpha')-H(\alpha)=\alpha'-\alpha$. Then $|(\alpha-\alpha')G(\alpha')f|_2\le|\alpha-\alpha'|_2|G(\alpha')f|_0\le B_1|\alpha-\alpha'|_2|f|_2$ and apply (G) once more. $\square$

---

## 4. Constant solutions at $\lambda=\infty$ (P2 §2)

### 4.1 Proposition 4.1 (P2 Prop 2.1 at $\lambda=\infty$; proved)

Local data at a block of layer $n$: $a=a_n\in[\frac12,2]$, $\nu=\nu_n=\mu L^{2n}\in[0,1]$, $\nu_*=\mu L^{2k}\ge\nu$, $\Psi=\psi+\psi'$, $H=h+h'$ in $\mathbb C^N$, with the pointwise forms of (R2), (R3), (R4), (C2), (C3)
of §1.3 for parameters $\delta\le\varepsilon$, $\nu_*\varepsilon^2\le\delta^2$. Invariants as in P2 (2.6): $U=\sqrt{\Psi\cdot\Psi}$ (principal root), $V=\Psi\cdot H/U$, $W^2=H\cdot H-V^2$, $Z=a(U-1)+\nu(V-1)$
(Lean `invU`, `invV`, `invW2`, `invZ`; $w\cdot w=(a+\nu+Z)^2+\nu^2W^2$, `cBlend_dot_eq`).

**Lemma 4.1.** There are absolute $c_4,C_0$ with $|U-1|\le2\delta$, $\nu|V-1|\le C_0\delta$, $|\nu^2W^2|\le C_0\delta^2$ for $\delta\le c_4$.

*Proof.* $|\Psi\cdot\Psi-1|\le|\psi\cdot\psi-1|+|(\psi+\psi')^2-\psi^2|<2\delta$; the principal root has $\mathrm{Re}\,U\ge0$, so $|U+1|\ge1$ and $|U-1|\le|U^2-1|\le2\delta$.
For $\nu(V-1)=\nu(\Psi\cdot H-U)/U$ ($|U|\ge\frac12$) write
$\nu(\Psi\cdot H-U)=\nu(\psi\cdot h-|\psi|)+\nu\psi'\cdot h+\nu\Psi\cdot h'-\nu(U-|\psi|)$. First term: $|\psi|\,\nu|\psi_0\cdot h-1|<(1+\delta)\delta^2$ by (R3). Second: $\nu|\psi'|\le2\nu\varepsilon$ and
$\nu\varepsilon\le\sqrt\nu\sqrt{\nu_*}\,\varepsilon\le\delta$ since $\nu_*\varepsilon^2\le\delta^2$, $\nu\le1$ (here $\nu\le\nu_*$). Third: $\nu|\psi\cdot h'|\le|\psi|\delta^2$ by (C3) and $\nu|\psi'\cdot h'|\le(\varepsilon+\delta)\delta^2/\varepsilon\le2\delta^2$.
Fourth: $\le\nu(|U-1|+||\psi|-1|)\le3\delta$.
For $W^2$ use $\Psi_0=\Psi/U$, $\Psi_0\cdot\Psi_0=1$, $V=\Psi_0\cdot H$: then $W^2=(H-V\Psi_0)\cdot(H-V\Psi_0)$, hence $|\nu^2W^2|\le|\nu(H-V\Psi_0)|^2$, and
$$H-V\Psi_0=(h-\psi_0)+h'+(\psi_0-\Psi_0)+(1-V)\Psi_0 .$$
Times $\nu$: $\nu|h-\psi_0|\le\sqrt\nu\,(\nu|h-\psi_0|^2)^{1/2}$ with $\nu|h-\psi_0|^2=\nu(h\cdot h-2\psi_0\cdot h+1)\le\nu|h\cdot h-1|+2\nu|1-\psi_0\cdot h|\le3\delta^2$ by (R3), (R4);
$\nu|h'|<\delta^2/\varepsilon\le\delta$; $\nu|\psi_0-\Psi_0|\le\nu(|\psi'|+4\delta)\le6\delta$ (as above, $\nu\varepsilon\le\delta$); $\nu|1-V|\le C\delta$. So $|\nu(H-V\Psi_0)|\le C\delta$ and $|\nu^2W^2|\le C^2\delta^2$. $\square$

This is the estimate behind P2 (2.7), (2.8) (the discs $K(1,2\delta)\times K(1,22\delta^2/\nu)\times K(0,56\delta^4/\nu^2\varepsilon^2)$); only the existence of absolute constants is used, so the explicit numbers
80, 78, 56, 22 of ER-032, ER-033 are not needed.

**Proposition 4.1.** For $\delta\le c_4$, the local system $(a+\nu+\hat\alpha)\phi=a\Psi+\nu H$, $\phi\cdot\phi=1$ has exactly one solution with $|\hat\alpha|<a+\nu$ (Lean `eq_of_isCEL`), namely $\phi=\texttt{cMinimizer}$, $\hat\alpha=\texttt{cMultiplier}$;
it is analytic on the open set $\mathrm{Re}(w\cdot w)>0$ (`analyticOnNhd_cMinimizer`), which contains the data domain (`mem_cDomain_of_near` applied at the real point $(\psi,h)$), and:

* (a) $|\hat\alpha|\le C_1\delta$ (`norm_cMultiplier_le`, using $|Z|+4|\nu^2W^2|\le C\delta$ from Lemma 4.1);
* (b) $|\phi-\Psi|\le C_1\delta$ and $|\phi-\Psi_0|\le C_1\delta$ (`cNorm_cMinimizer_sub_le`: $|\phi-\Psi|\le4(\nu|H-\Psi|+(|Z|+4|\nu^2W^2|)|\Psi|)$, and $\nu|H-\Psi|\le\nu|h-\psi|+\nu|h'|+\nu|\psi'|\le\sqrt\nu\,(\nu|h-\psi|^2)^{1/2}+3\delta\le C\delta$ by (R3));
* (c) for real data $|\phi-h|\le C_1\delta/\sqrt\nu$ and, for every $h'$ with (C3), $\nu|\phi\cdot h'|\le C_1\delta^2$ (use $\nu|\psi_0\cdot h'|<\delta^2$ and $\nu|h'||\phi-\psi_0|\le(\delta^2/\varepsilon)\,C\delta\le C\delta^2$);
* (d) $|\phi(\Psi+\Psi',H)-\phi(\Psi,h)|\le\varepsilon+(2C_1+1)\delta$ (triangle inequality through (b) for both data, $|\psi'|<\varepsilon+\delta$).

*Status: proved.* The new pieces are Lemma 4.1 and the passage from the invariants to (a)–(d), written above. **Two hypotheses of the landed lemmas must be re-run:** `mem_cDomain_of_near` is stated for $a\le\frac32$
(P2's weights $a_n<\frac{27}{16}$ and Lean's `IsAdmissibleWeights` allow up to 2; change $\frac32\to2$ and $m/10\to m/12$), and `norm_cMultiplier_le` assumes $a+\nu>\frac12$ while `IsAdmissibleWeights` allows $a_n=\frac12$
(run it with $|Z|\le\frac18$, giving $\mathrm{Re}\,s\ge\frac38$). Only numerical constants change.

### 4.2 Closeness of neighbouring constant solutions

For a block $y$ of layer $n$ write $\phi^y,\hat\alpha^y$ for the local solution at the data $(\Psi_n(y),\tilde h_n(y))$ and $\alpha^y:=L^{-2n}\hat\alpha^y$ (the block equation
$a_nL^{-2n}(\Psi-\phi^y)+\mu(\tilde h-\phi^y)-\alpha^y\phi^y=0$ is the constant case of (EL) divided by $L^{-2n}$).

**Lemma 4.2 (proved).** For adjacent blocks $y,y'$ (layers $n,n'$, $|n-n'|\le1$): $|\phi^y-\phi^{y'}|\le C\delta$. For every pair of blocks $y,y'$ whose centres are at $\ell^1$-distance $\le rL^{\max(n,n')}$: $|\phi^y-\phi^{y'}|\le C(r,L,d)\delta$ (a chain of at most $C(r,L,d)$ adjacent blocks).

*Proof.* By Prop. 4.1(b), $|\phi^y-\Psi_0(y)|\le C_1\delta$ and $\Psi_0=\Psi/\sqrt{\Psi\cdot\Psi}$. By (R1), (C1) neighbours have $|\Psi(y)-\Psi(y')|<2\delta$, and $\Psi\mapsto\Psi/\sqrt{\Psi\cdot\Psi}$ is Lipschitz with constant $\le4$ near $|\Psi|=1$. The fact that the masses $\nu_n,\nu_{n'}$ and weights $a_n,a_{n'}$ differ by $O(1)$ between layers
does not matter: it is built into (b), which compares $\phi^y$ with the data direction and not with $h$. $\square$

### 4.3 Effective potential at $\lambda=\infty$ (P2 Prop 2.2, ER-030; proved, not needed for I-1)

For real constant data $(\psi,h)$, $|h|=1$, $U=|\psi|$, $V_\psi=\psi_0\cdot h$, local $a,\nu$: $V(\psi,h):=\min_{|\phi|=1}[\frac a2|\psi-\phi|^2+\frac\nu2|\phi-h|^2]$. By `constObjective_eq` and `constMinimizer_le`,
$V=\frac a2(U^2+1)+\nu-|w|$ with $w=a\psi+\nu h$, and $|w|^2=s^2-e$, $s=aU+\nu$, $e=2a\nu U(1-V_\psi)$. Then $\frac a2(U^2+1)=\frac a2(U-1)^2+aU$, so exactly
$$V(\psi,h)=\tfrac a2(U-1)^2+\frac{e}{s+|w|}.$$
For $U\in[\frac12,\frac32]$, $a\in[\frac12,2]$, $\nu\le1$: $s\ge\frac14$, $|w|\le s$, so $\frac e{s+|w|}\in[\frac e{2s},\frac es]$ and $\frac es=2\nu(1-V_\psi)\frac{aU}{aU+\nu}\in[\frac25\nu(1-V_\psi),2\nu(1-V_\psi)]$. Hence
$$\tfrac15\big[(U-1)^2+\nu(1-V_\psi)\big]\le V(\psi,h)\le2\big[(U-1)^2+\nu(1-V_\psi)\big],$$
which is P2's Prop 2.2 at $\lambda=\infty$ with $\gamma_2=\frac15$, $C_2=2$ (and $c_5=\frac12$). This settles the first half of ER-030; the second half (P6 Prop 3.1, the global action lower bounds) is a large-field statement not treated here.

---

## 5. I-1: existence, uniqueness, analyticity and bounds

### 5.1 Proposition 5.1 (P2 Lemma 3.2 and Prop 3.1 at $\lambda=\infty$; proved from (G))

*The perturbed system with independent data.* Fix $G$, weights, $\mu\le L^{-2k}$, and assume (G). The data are

* (P1) a lifted block-spin field $\delta\Psi$ (constant on blocks of each layer; arbitrary on the collar), $|\delta\Psi|\le\delta_1$ on $\Omega_1\cup C$;
* (P2) $\phi_0:\mathbb T\to\mathbb C^N$ with `IsSmoothField G δ₀ φ₀` and $|\phi_0|\le\frac32$ on $\Omega_1$;
* (P3) $\alpha_0:\Omega_1\to\mathbb C$, $|\alpha_0|_2\le\delta_0$; $f_1:\Omega_1\to\mathbb C^N$, $|f_1|_2\le\delta_1$;
* (P4) $g:=\phi_0\cdot\phi_0-1$ on $\Omega_1$ and its zero extension $\tilde g$ satisfy $|g|_0+|\Delta\tilde g|_2\le\delta_1$ (e.g. $g\equiv0$).

The system for $(\delta\phi,\delta\alpha)$, $\delta\phi:\Omega_1\to\mathbb C^N$, $\delta\alpha:\Omega_1\to\mathbb C$, is
$$(H_D(\alpha_0)+\delta\alpha)\,\delta\phi=F_s-\delta\alpha\,\phi_0,\qquad F_s:=Q^*a\,\delta\Psi+\mathfrak b(\delta\Psi)+f_1,\tag{P-1}$$
$$(\phi_0+\delta\phi)\cdot(\phi_0+\delta\phi)=1\ \text{ on }\Omega_1,\tag{P-2}$$
$(Q^*a\delta\Psi)(x)=a_nL^{-2n}\delta\Psi(x)$, $\mathfrak b(\delta\Psi)(x)=\sum_{x'\in C,x'\sim x}\delta\Psi(x')$. This is P2 (3.20) at $\lambda=\infty$ ($\alpha_1$ drops out because it enters as $\alpha_1/\lambda$); the boundary term $\mathfrak b$ is explicit here, whereas P2's (3.20) has
$\delta\phi=0$ off $\Omega_1$ and leaves the collar data implicit.

**Proposition 5.1.** There are $c_6\in(0,\gamma_1/4]$, $K_2$ and $\delta_*\in(0,\gamma_1/4]$, depending only on $(d,L,N)$ (through $B_1$), such that if $\delta_0\le\delta_*$ and $\delta_1\le\delta_*$ with $C_N\delta_1\le c_6/2$ ($C_N$ below), then
(P-1), (P-2) have exactly one solution with $|\delta\alpha|_2<c_6$. It is analytic in $(\delta\Psi,\phi_0,\alpha_0,f_1)$ on the open set of data satisfying (P1)–(P4) with strict inequalities, and
$$|\delta\phi|_0+|\partial\delta\phi|_1+|\Delta^D\delta\phi|_2+|\delta\alpha|_2\le K_2\,\delta_1.$$

*Proof (complete).* Put $\mathcal C_F=3+2dL^2$. Since wall sites lie in layer 1, $|\mathfrak b(\delta\Psi)|_2\le2dL^2\delta_1$; $|Q^*a\delta\Psi|_2\le2\delta_1$; so $|F_s|_2\le\mathcal C_F\delta_1$.
Let $\rho=c_6$ and $B=B_1$ be as in (G). Fix the following order of choice: $c_6\le\gamma_1/4$ and $2B(\tfrac32c_6)\le\frac1{16}$; then $\delta_*\le\gamma_1/4$ with $B(\mathcal C_F\delta_*+\frac32c_6)\le\frac12$ and the Lipschitz estimate (iii) below $\le\frac12$.

*(i) Solving the linear equation.* For $|\delta\alpha|_2\le\rho$ put $A=\alpha_0+\delta\alpha$, $|A|_2\le\gamma_1/2$, $F(\delta\alpha)=F_s-\delta\alpha\,\phi_0$, $|F|_2\le\mathcal C_F\delta_1+\frac32|\delta\alpha|_2$, and
$$\delta\phi(\delta\alpha):=G(A)F(\delta\alpha).$$
(P-1) holds iff $\delta\phi=\delta\phi(\delta\alpha)$, because $H_D(A)=H_D(\alpha_0)+\delta\alpha$ is invertible (G-1). By (G) and Lemma 3.3, $\|\delta\phi\|_*\le B(\mathcal C_F\delta_1+\frac32|\delta\alpha|_2)\le\frac12$ and
$$\|\delta\phi(\delta\alpha)-\delta\phi(\delta\alpha')\|_*\le\tfrac32B|\delta\alpha-\delta\alpha'|_2+B^2|\delta\alpha-\delta\alpha'|_2(\mathcal C_F\delta_1+\tfrac32\rho)\le2B|\delta\alpha-\delta\alpha'|_2.\tag{5.1}$$

*(ii) Reduction of the constraint to a fixed-point equation.* Let $H_0=H_D(\alpha_0)$, $K$ and $R$ as in Lemmas 3.1, 3.2, and $u:=2\phi_0\cdot\delta\phi+\delta\phi\cdot\delta\phi+g$ on $\Omega_1$ (zero extension $\tilde u$). Then (P-2) is $u=0$, since $(\phi_0+\delta\phi)^2=1+g+(u-g)=1+u$.
By the definitions of $K$ and $R$,
$$H_0u=2\phi_0\cdot H_0\delta\phi-2K\delta\phi+2\delta\phi\cdot H_0\delta\phi+R(\delta\phi)+H_0\tilde g.$$
From $\delta\phi=\delta\phi(\delta\alpha)$ we have $H_0\delta\phi=F_s-\delta\alpha(\phi_0+\delta\phi)$, and $(\phi_0+\delta\phi)^2=1+u$, so
$$H_0u=-2\delta\alpha(1+u)+2(\phi_0+\delta\phi)\cdot F_s-2K\delta\phi+R(\delta\phi)+H_0\tilde g ,$$
that is, with
$$\mathcal N(\delta\alpha):=(\phi_0+\delta\phi)\cdot F_s-K\delta\phi+\tfrac12R(\delta\phi)+\tfrac12H_0\tilde g,\qquad (H_0+2\delta\alpha)\,u=2\big(\mathcal N(\delta\alpha)-\delta\alpha\big).\tag{5.2}$$
Since $|\alpha_0+2\delta\alpha|_2\le\delta_*+2\rho\le\frac34\gamma_1$, $H_D(\alpha_0+2\delta\alpha)$ is invertible (G-1), so **$u=0$ iff $\mathcal N(\delta\alpha)=\delta\alpha$.** Thus solutions of (P-1), (P-2) with $|\delta\alpha|_2\le\rho$ are exactly the fixed points of $\mathcal N$ in the closed ball of radius $\rho$ of $(\mathbb C^{\Omega_1},|\cdot|_2)$.
The inverse of $\phi_0\cdot G\phi_0$ never appears: the linear dependence of $\delta\phi$ on $\delta\alpha$ produces the term $-K\delta\phi$, whose coefficient is $\delta_0$ by Lemma 3.1.

*(iii) Estimates.* By Lemmas 3.1, 3.2, $|H_0\tilde g|_2\le|\Delta\tilde g|_2+(2+1+\delta_0)|g|_0\le4\delta_1$ ($\mu\ell^2\le1$, $a_n\le2$):
$$|\mathcal N(0)|_2\le(\tfrac32+\tfrac12)\mathcal C_F\delta_1+(1+2d)\delta_0B\mathcal C_F\delta_1+(4+d)B^2\mathcal C_F^2\delta_1^2+2\delta_1\le C_N\delta_1,$$
$C_N:=3\mathcal C_F+2+(1+2d)B\mathcal C_F+(4+d)B^2\mathcal C_F^2$ (using $\delta_0,\delta_1\le1$). For the Lipschitz constant on the ball, by (5.1) and Lemmas 3.1, 3.2:
$$|\mathcal N(\delta\alpha)-\mathcal N(\delta\alpha')|_2\le\Big[2B\,\mathcal C_F\delta_1+2B(1+2d)\delta_0+4(4+d)B^2(\mathcal C_F\delta_1+\tfrac32\rho)\Big]|\delta\alpha-\delta\alpha'|_2\le\tfrac12|\delta\alpha-\delta\alpha'|_2$$
once $\delta_*$ and $c_6$ are small (in the order fixed above). Self-map: $|\mathcal N(\delta\alpha)|\le C_N\delta_1+\frac12\rho\le\rho$ if $C_N\delta_1\le\rho/2$.

*(iv) Conclusion.* Banach: a unique fixed point in the ball, with $|\delta\alpha|_2\le2|\mathcal N(0)|_2\le2C_N\delta_1$. Then $|F|_2\le(\mathcal C_F+3C_N)\delta_1$, so $|\delta\phi|_0+|\partial\delta\phi|_1\le B(\mathcal C_F+3C_N)\delta_1$, and from (P-1),
$-\Delta^D\delta\phi=F-(Q^*aQ+\mu+\alpha_0+\delta\alpha)\delta\phi$ gives $|\Delta^D\delta\phi|_2\le|F|_2+5|\delta\phi|_0\le(1+5B)(\mathcal C_F+3C_N)\delta_1$. Hence the claimed bound holds with $K_2:=2C_N+(\mathcal C_F+3C_N)(2+6B)$.
Uniqueness holds among all solutions of (P-1), (P-2) with $|\delta\alpha|_2<\rho$ by (i), (ii). Analyticity: the map $T(\xi,p)=\mathcal N_p(\xi)$ is analytic on $\overline B(0,\rho)\times P$ ($P$ the open set of data), because the entries of $G(\alpha_0+\xi)$ are analytic (`analyticOnNhd_green_apply`) and $K$, $R$, products are polynomial in $(p,\delta\phi)$;
`Balaban.Analysis.exists_analytic_fixedPoint` gives analyticity of the fixed point $\xi^*(p)$ and then $\delta\phi=G(\alpha_0+\xi^*)F$ is analytic. $\square$

*Remarks.* (1) Only $\|G(\alpha)f\|_*\le B_1|f|_2$ is used from G-2: neither the Laplacian part of G-2(iv) nor the Hölder bound nor any Neumann series (P2 (3.22)): (G) holds uniformly on the whole polydisc, so $G(\alpha_0+\delta\alpha)$ is treated directly and Lemma 3.3 replaces P2's expansion (3.25). (2) The hypothesis (P4) is the defect version; for $g\equiv0$ it is empty. It does *not* restrict to subdomains (the wall of a smaller $\Omega_1$ is a jump of $\tilde g$), which is why §6 uses only $g\equiv0$.
(3) This answers ER-031 ($F_2$ "sampled"): the nonlinear terms are the explicit $K$, $R$ of Lemmas 3.1, 3.2.

### 5.2 Theorem 5.2 (I-1; P2 Prop 1.1, Cor 1.1 at $\lambda=\infty$)

There are $c_0,c_1,K_1>0$, $K_1c_1\le c_0$, depending only on $(d,L,N)$, and $R_0(d,L)\ge3L$ such that the following holds for every generating set $G=\mathbb B_k$ on $(\mathbb Z/N_0L^k)^d$ with $\varrho\ge R_0$, weights $a_n\in(\frac12,2]$, mass $0\le\mu\le L^{-2k}$, and all data $(\Psi+\Psi',\tilde h)\in\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ with
$0<\delta\le\varepsilon\le c_0$, $\delta\le c_1$, $\mu L^{2k}\varepsilon^2\le\delta^2$:

1. **(Existence and uniqueness.)** (EL) has a solution $(\phi,\alpha)$ with $|\alpha|_2<c_0$ (i.e. $|\alpha(x)|<c_0\ell(x)^{-2}$), and it is the only one with this restriction.
2. **(Analyticity.)** $(\phi,\alpha)$ is an analytic function of the data on the open set $\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$ (for fixed $\delta,\varepsilon$; the functions for different $(\delta,\varepsilon)$ agree on overlaps by uniqueness).
3. **(Bounds, P2 (1.15).)** With $\bar\phi$ the extension by $\Psi+\Psi'$ on the collar: $|\phi-Q^*(\psi+\psi')|_0\le K_1\delta$, $|\partial\bar\phi|_1\le K_1\delta$, $|\Delta\bar\phi|_2\le K_1\delta$, $|\alpha|_2\le K_1\delta$, and $|\delta\phi(\psi',h')|_0\le\varepsilon+K_1\delta$ where $\delta\phi(\psi',h')=\phi(\psi+\psi',h+h')-\phi(\psi,h)$. Moreover, if G-2(iii) is available, $|\partial\phi|_{(\theta),2-\theta}\le C_\theta K_1\delta$ for a fixed $\theta\in(0,1)$.
4. **(Real data, ∃! form.)** For real $(\Psi,h)\in\tilde\Psi(\mathbb B_k;\delta)$, $\delta\le c_1$, the solution is real, $\phi$ is the **unique global minimiser** of (1.2) over $(S^{N-1})^{\Omega_1}$ (no condition on $\alpha$ is needed for this characterization), and (P2 (1.16)) $\sqrt\mu\,|\phi-h|(x)\le K_1\delta/\ell(x)$, $\mu|\phi\cdot h'|\le K_1\ell^{-2}\delta^2$ for every $h'$ with (C3).
5. **(Single scale, P2 Cor 1.1.)** For $\Omega_1=\dots=\Omega_k=\mathbb T$ (only layer $k$ nonempty, no collar, $Q^*aQ=a_kL^{-2k}P_k$) items 1–4 hold with $\ell\equiv L^k$.
6. **(Perturbations, P2 Cor 3.1.)** If also $(\Psi+\Psi'+\delta\Psi,\tilde h)\in\tilde\Psi^c(\mathbb B_k;\delta',\varepsilon')$ with $\delta'\le c_1$, $|\delta\Psi|\le\delta_1$, $K_2\delta_1+K_1\delta\le c_0/2$ and the smallness of Prop 5.1 for $(\delta_0,\delta_1)=(K_1\delta,\delta_1)$, then the solution for the perturbed data is $(\phi+\delta\phi,\alpha+\delta\alpha)$ with $(\delta\phi,\delta\alpha)$ the solution of Prop. 5.1 for $(\delta\Psi,\phi,\alpha,f_1=0,g=0)$.

Item 3's first line corrects the transcription in `review/papers/P2-variational-problems.md`, which prints $K_1(L^j\eta)^{-1}\delta$; page 611 reads $|\phi-Q^*(\psi+\psi')|<K_1\delta$ and $|\partial^\eta\phi|<K_1(L^j\eta)^{-1}\delta$, consistent with Prop 3.1's $|\delta\phi|<K_2\delta_1$.

### 5.3 Lemma 5.3 (P2 Lemma 3.1 analogue: the approximate solution; sketched)

For each block $y$ of layers $0,\dots,k$ (collar sites are layer-0 blocks with $\phi^y=\Psi(y)/\sqrt{\Psi(y)\cdot\Psi(y)}$, the case $a_0=\infty$ of Prop 4.1) let $(\phi^y,\alpha^y)$ be the local solution of §4.2. **Partition of unity.** Let $\beta$ be the quadratic B-spline (a $C^1$ bump of width 3 with piecewise-constant second derivative,
$\sum_m\beta(t-m)=1$, $\beta>0$ on $[-\frac12,\frac12]$) and $\tilde h_y(x)=\prod_\mu\beta((x_\mu-c_\mu(y))/L^{n(y)})$, $h_y=\tilde h_y/\sum_{y'}\tilde h_{y'}$. Facts used (for $\varrho\ge R_0:=3L$):

* (h1) $h_y\ge0$, $\sum_yh_y=1$ on $\Omega_1\cup C$; the denominator lies in $[2^{-d},3^{d+1}]$ (a site lies within $L^n/2$ of the centre of its own $n$-block, where the bump is $\ge2^{-d}$ because $\beta\ge\frac12$ on $[-\frac12,\frac12]$);
* (h2) $h_y(x)\neq0$ only if $|n(y)-n(x)|\le1$ and $\|x-c(y)\|_\infty<\frac32L^{n(y)}$ (by separation: $\mathrm{dist}>\varrho L^{n+1}>2L^{n+2}$ between a layer-$n$ site and $\Omega_{n+2}$, and a layer-$(n+2)$ bump reaches at most $2L^{n+2}$ from the centre-to-edge of its block; layers two below are farther still relative to their own scale);
* (h3) at most $3^{d+1}$ indices $y$ with $h_y(x)\ne0$;
* (h4) $|\Delta_eh_y(x)|\le C\ell(x)^{-1}$ and $|\Delta h_y(x)|\le C\ell(x)^{-2}$, $C=C(d,L)$ (second differences of a $C^{1,1}$ function are bounded by its second derivative; a hat function would give only $\ell^{-1}$ here, so the bump must be $C^{1,1}$; this is P2's "smooth partition of unity", p. 617).

Define $\tilde\phi=\sum_yh_y\phi^y$, $\phi_0=\tilde\phi/\sqrt{\tilde\phi\cdot\tilde\phi}$ on $\Omega_1\cup C$, $\alpha_0=\sum_{y:\,1\le n(y)\le k}h_y\alpha^y$ on $\Omega_1$, and the residual $f_0:=S(\Psi,\tilde h)-H_D(\alpha_0)\phi_0$.

**Lemma 5.3.** There are $\delta_{**},C_3$ depending on $(d,L,N)$ such that for data in $\tilde\Psi^c(\mathbb B_k;\delta,\varepsilon)$, $\delta\le\delta_{**}$ (hypotheses of Thm 5.2): (a) $\phi_0\cdot\phi_0=1$ on $\Omega_1\cup C$ and $|\phi_0-\Psi|\le C_3\delta$ on $\Omega_1\cup C$; (b) `IsSmoothField G (C₃δ) φ₀` and $|\alpha_0|_2\le C_3\delta$; (c) $|f_0|_2\le C_3\delta$;
(d) $(\phi_0,\alpha_0,f_0)$ are analytic in the data on the open domain; real for real data; (e) $|\phi_0(\Psi+\Psi',\tilde h)-\phi_0(\Psi,h)|_0\le\varepsilon+C_3\delta$; (f) for real data, $\sqrt\mu|\phi_0-h|\le C_3\delta/\ell$.

*Proof (sketched; every estimate listed).*
* *(A1) Closeness.* Lemma 4.2: $|\phi^y-\phi^{y'}|\le C\delta$ for the at most $3^{d+1}$ blocks active at one site, and for the two active blocks of two adjacent sites (chains of bounded length, $r=C(d)L$).
* *(A2) Norm of $\tilde\phi$.* $\tilde\phi\cdot\tilde\phi=\sum h_y\phi^y\cdot\phi^y-\frac12\sum_{y,y'}h_yh_{y'}(\phi^y-\phi^{y'})\cdot(\phi^y-\phi^{y'})=1-O(\delta^2)$ since $\phi^y\cdot\phi^y=1$; so $\mathrm{Re}\,\tilde\phi\cdot\tilde\phi\ge\frac12$ and the principal root is analytic. This gives the first claim of (a).
* *(A3) Differences.* From $\sum_y\Delta_eh_y=0$: $\Delta_e\tilde\phi(x)=\sum_y\Delta_eh_y(x)(\phi^y-\phi^{y_x})$, so $|\Delta_e\tilde\phi|\le C\delta/\ell(x)$ by (h3), (h4), (A1); likewise $|\Delta\tilde\phi|\le C\delta/\ell^2$. For $\phi_0=\tilde\phi\,(\tilde\phi\cdot\tilde\phi)^{-1/2}$: $|\Delta_e\phi_0|\le C|\Delta_e\tilde\phi|$, $|\Delta\phi_0|\le C(|\Delta\tilde\phi|+|\partial\tilde\phi|^2)\le C\delta\ell^{-2}$. Bonds to the collar are included because the formula defines $\phi_0$ there. This is (b), first part. For $\alpha_0$: $|\alpha^y|=L^{-2n(y)}|\hat\alpha^y|\le C_1\delta L^{-2n(y)}\le C_1L^2\delta\,\ell(x)^{-2}$ since $n(y)\ge n(x)-1$.
* *(A4) Closeness to the data.* $|\phi_0(x)-\phi^{y_x}|\le C\delta$ by (A1), so $|\phi_0-\Psi|\le|\phi_0-\phi^{y}|+|\phi^y-\Psi(y)|\le C\delta$ by Prop 4.1(b) (and for collar sites by (R2)).
* *(A5) Residual.* For $x\in\Omega_1$ in the block $y$ of layer $n$, write $H_D(\alpha_0)\phi_0=-\Delta\bar\phi_0+\mathfrak b(\phi_0)+a_nL^{-2n}Q_n\phi_0+\mu\phi_0+\alpha_0\phi_0$ and subtract the block equation $a_nL^{-2n}(\Psi-\phi^y)+\mu(\tilde h-\phi^y)-\alpha^y\phi^y=0$:
$$f_0(x)=a_nL^{-2n}\big(\phi^y-Q_n\phi_0(y)\big)+\mu\big(\phi^y-\phi_0(x)\big)+\big(\alpha^y\phi^y-\alpha_0\phi_0\big)(x)+\Delta\bar\phi_0(x)+\mathfrak b(\Psi-\phi_0)(x).$$
Times $\ell^2$: the first is $\le2C\delta$ ($a_n\le2$, (A4)); the second $\le C\delta$ because $\mu\ell^2\le1$; the third $\le C\delta$ (both multipliers are $O(\delta\ell^{-2})$; the exactness of the constant solution has cancelled the $O(1)$ parts); the fourth $\le C\delta$ by (A3); the fifth is supported on wall sites, which lie in layer 1 ($\ell^2=L^2$), and is $\le2dL^2C\delta$ by (A4) on the collar. This is (c).
* *(A6)* (d): cMinimizer is analytic on the domain (Prop 4.1), $h_y$ are constants, the root is analytic where $\mathrm{Re}>0$. (e): $|\tilde\phi-\tilde\phi^{\rm real}|\le\sum_yh_y|\phi^y-\phi^{y,\rm real}|\le\varepsilon+C\delta$ by Prop 4.1(d), the normalisation changes this by $O(\delta^2)$. (f): Prop 4.1(c), for $y$ of layer $n'\ge n-1$: $\sqrt\mu|\phi^y-h|\le C\delta L^{-n'}\le C L\delta/\ell$.

*Where the geometry is hard.* (h1)–(h4) across layer interfaces and the chain lengths in (A1) depend on the separation $\varrho\ge3L$ and on (R1) between layers $n$ and $n-1$; the discrete second differences of the normalised bumps are about 600 lines of Lean on their own (see §9). $\square$

### 5.4 Proof of Theorem 5.2

*Constants.* Let $c_6,K_2,\delta_*$ be those of Prop 5.1, $C_3$ those of Lemma 5.3. Put $c_0=\frac12c_6$, $K_1=(1+K_2)C_3$, $c_1=\min\{\delta_{**},\ \delta_*/C_3,\ c_6/(2K_1)\ (\text{so }K_1c_1\le c_0),\ c_6/(2C_3),\ c_6/(2C_NC_3)\}$, the last for the hypothesis $C_N\delta_1\le c_6/2$ of Prop 5.1 with $\delta_1=C_3\delta$.

*Existence, bounds.* Apply Prop 5.1 with $\delta\Psi=0$, $\phi_0,\alpha_0$ of Lemma 5.3, $f_1=f_0$, $g=0$, $\delta_0=\delta_1=C_3\delta$: this is legitimate by (a)–(c). Since
$H_D(\alpha_0+\delta\alpha)(\phi_0+\delta\phi)=S\iff(H_D(\alpha_0)+\delta\alpha)\delta\phi=f_0-\delta\alpha\phi_0$ (definition of $f_0$), $(\phi,\alpha):=(\phi_0+\delta\phi,\alpha_0+\delta\alpha)$ solves (EL), with $|\alpha|_2\le C_3\delta+K_2C_3\delta<c_0$.
The bounds: $|\phi-\Psi|\le C_3\delta+K_2C_3\delta$, $|\partial\bar\phi|_1\le|\partial\bar\phi_0|_1+|\partial\delta\phi|_1$ (the collar values of $\bar\phi$ and $\bar\phi_0$ coincide up to the data: $\bar\phi=\Psi$ on $C$ versus $\bar\phi_0$ on $C$ differ by $\le C_3\delta$; one more term $\le C_3\delta$ per wall bond, again in layer 1; absorb in $K_1$), $|\Delta\bar\phi|_2\le|\Delta\bar\phi_0|_2+|\Delta^D\delta\phi|_2+C\delta$, $|\alpha|_2\le(1+K_2)C_3\delta$.
Item 3's last line: $|\phi(\Psi+\Psi',h+h')-\phi(\Psi,h)|\le|\phi_0^{c}-\phi_0^{r}|+2K_2C_3\delta\le\varepsilon+C_3\delta+2K_2C_3\delta\le\varepsilon+K_1'\delta$.

*Uniqueness.* If $(\phi,\alpha)$ solves (EL) with $|\alpha|_2<c_0$, then $\delta\alpha=\alpha-\alpha_0$ has $|\delta\alpha|_2<c_0+C_3\delta\le c_6$ and $(\phi-\phi_0,\delta\alpha)$ solves (P-1), (P-2) (recentring), so equals the solution above by Prop 5.1.

*Analyticity.* Lemma 5.3(d) and Prop 5.1 (all of $\phi_0,\alpha_0,f_0$ are analytic functions of the data; Prop 5.1 is analytic in $f_1,\phi_0,\alpha_0$).

*Real data (item 4).* The conjugate of a solution for real data is a solution ($H_D(0)$ is a real matrix, $\bar\phi\cdot\bar\phi=1$, $|\bar\alpha|_2=|\alpha|_2$), so by uniqueness $\phi,\alpha$ are real. Write $A(\phi)=\frac12\langle\phi,H_D(0)\phi\rangle-\langle\phi,S\rangle+c$ (expand (1.2); $S$ as in (1.1); $c$ independent of $\phi$). Let $\phi_*$ be the solution, $\alpha_*$ real with $|\alpha_*|_2<c_0\le\frac18$, so $H_*:=H_D(\alpha_*)$ is real symmetric positive definite (`multiscale_coercive_sharp`). For every $\sigma\in(S^{N-1})^{\Omega_1}$, $\langle\sigma,\mathrm{diag}(\alpha_*)\sigma\rangle=\sum\alpha_*=\langle\phi_*,\mathrm{diag}(\alpha_*)\phi_*\rangle$ since $|\sigma|=|\phi_*|=1$, hence with $H_*\phi_*=S$:
$$A(\sigma)-A(\phi_*)=\tfrac12\langle\sigma,H_*\sigma\rangle-\langle\sigma,H_*\phi_*\rangle+\tfrac12\langle\phi_*,H_*\phi_*\rangle=\tfrac12\langle\sigma-\phi_*,H_*(\sigma-\phi_*)\rangle>0\quad(\sigma\ne\phi_*).\tag{5.3}$$
So $\phi_*$ is the unique global minimiser, and the characterization needs only that a solution with small real $\alpha$ exists. (P2 (3.48) argued with the second variation and proved only that $\phi$ is the unique critical point in the class $|\alpha|_2<c_0$; (5.3) is stronger and exact at $\lambda=\infty$.) The bounds (1.16): $\sqrt\mu|\phi-h|\le\sqrt\mu|\phi_0-h|+\sqrt\mu|\delta\phi|\le C_3\delta/\ell+K_2C_3\delta\sqrt\mu\le K_1\delta/\ell$ ($\sqrt\mu\,\ell\le1$); $\mu|\phi\cdot h'|\le\mu|\psi_0\cdot h'|+\mu|h'||\phi-\psi_0|\le\ell^{-2}\delta^2+C\ell^{-2}\delta^3/\varepsilon$ by (C3), (a).

*Items 5, 6.* Item 5 is the case of Theorem 5.2 for the generating set with only $\Omega_k=\Omega_{k-1}=\dots=\mathbb T$, which is a legitimate `GeneratingSet` (the separation condition is vacuous). Item 6: $(\phi+\delta\phi,\alpha+\delta\alpha)$ solves (EL) for the perturbed data, $|\alpha+\delta\alpha|_2\le K_1\delta+K_2\delta_1<c_0$, so equals the solution by uniqueness. $\square$

### 5.5 The linear response and the constrained operator $\Pi$ (consumed by I-4, P3 (3.9), P4 (2.23))

This is where the constrained operator of GREEN (1.8$'$) enters. Let $(\phi,\alpha)$ be the solution, $G=G_D(\alpha)$, $\Pi=\texttt{constrainedOp}\,G\,\phi=G\phi\,[\phi\cdot G\phi]^{-1}\,\phi\cdot G$ (bilinear dot, on $\Omega_1\times[N]$).

**Proposition 5.4 (proved).** Let $\dot S$ be a tangent vector of the data ($\dot S=Q^*a\dot\Psi+\mathfrak b(\dot\Psi)+\mu\dot{\tilde h}$, the data enter (EL) affinely). The derivatives $\dot\phi,\dot\alpha$ of the solution (analytic by Theorem 5.2) are
$$\dot\alpha=[\phi\cdot G\phi]^{-1}\,\phi\cdot G\dot S,\qquad\dot\phi=(G-\Pi)\dot S .$$
Moreover (a) $\phi\cdot G\phi$ is invertible (landed `constraintForm_isUnit`, which needs only `IsSmoothField` with $\delta\le(300d^2)^{-1}$, true by Theorem 5.2(3) after shrinking $c_1$); (b) for real data $G-\Pi\succeq0$.

*Proof.* Differentiate $H_D(\alpha)\phi=S$, $\phi\cdot\phi=1$: $H\dot\phi+\dot\alpha\phi=\dot S$, $\phi\cdot\dot\phi=0$. Then $\dot\phi=G(\dot S-\dot\alpha\phi)$ and $0=\phi\cdot G\dot S-\dot\alpha\,\phi\cdot G\phi$. (b): for real $\phi$, $G$ real symmetric positive definite, with $T=\texttt{fieldMul}\,\phi$, $G-\Pi=G^{1/2}(1-P)G^{1/2}$, $P$ the orthogonal projection onto the range of $G^{1/2}T$, so $G-\Pi\succeq0$ (and $\Pi\succeq0$ is the landed `constrainedOp_dirichlet_posSemidef`). $\square$

Kernel decay of $(G-\Pi)Q^*a$ follows from G-2(i) for $G$ and the landed `constrained_G2v`, `constrained_weighted_bounds` for $\Pi$ (with $\phi$ of Theorem 5.2(3) as the smooth field), which is the input of I-4. The proof of Prop 5.1 does not use $\Pi$: it controls the same object, $M=\phi_0^2-K\,G\phi_0$ of GREEN 4.5a, by a Banach iteration (the term $-K\delta\phi$ in (5.2)) instead of inverting it.

---

## 6. I-2: two generating sets, the function $\psi(\mathbb B_j,\mathbb B'_k;\psi')$ and the composition identities

### 6.1 Setting

$\mathbb B_j\prec\mathbb B'_k$ (P2 (4.1)): two generating sets on the same torus, $\Omega_i\subseteq\Omega'_i$ for $i\le j$. In the Lean model both are `GeneratingSet d L N₀ k ϱ` with the same $k$ (the torus is $(\mathbb Z/N_0L^k)^d$), $\mathbb B_j$ having $\Omega_i=\emptyset$ for $i>j$
(the separation condition is then vacuous above $j$ and `avgMatrix` has empty layers). The *same* weights and mass $\mu$ are used in both problems (P2 (4.14), (4.17): the third and fourth equations of (4.17) are (1.10) for $\mathbb B_j$ rescaled). For $x\in\Omega_1$ let $n=n(x)\le j$ and $p=p(x)\le k$ be the layers
in $\mathbb B_j$ and $\mathbb B'_k$; $\Omega_n\subseteq\Omega'_n$ gives $n\le p$, the $n$-block $y$ of $x$ lies in its $p$-block $y'$.

**Weights.** For the composition formulas the weights must be the sequence of P2 (4.4): with $u_r=1/a_r$,
$$u_{r+1}=u_1+L^{-2}u_r,\ u_0=0,\qquad a_r=a_1\frac{1-L^{-2}}{1-L^{-2r}}\quad(\text{P2 (4.4), page 631: }a_1=a,\ a_r\searrow a(1-L^{-2})),\tag{6.1}$$
equivalently P2 (1.4) $a_j=\frac{1-L^{-2k}}{1-L^{-2j}}a_k$. Then $a_r$ is decreasing, $a_p/a_n\le1$ for $p\ge n$, and (this is the whole content of P2 (4.18))
$$L^{2(n-p)}u_n=u_p-u_{p-n}\qquad(0\le n\le p),\tag{C1}$$
because $u_r=c(1-L^{-2r})$ with $c=u_1/(1-L^{-2})$: $L^{2(n-p)}u_n=c(L^{2(n-p)}-L^{-2p})=c(1-L^{-2p})-c(1-L^{-2(p-n)})$. Condition (6.1) is *not* needed for I-1, and it is not needed for the identities (6.4) below; it is needed for the variational characterization (iii) of Theorem 6.1. The printed "(4.8): $[a(1-L^2),a]$" (ER-034) is a misprint for $[a(1-L^{-2}),a]$; page 631–632 confirms $a_\infty=a(1-L^{-2})$.

### 6.2 The formula

Let $(\Psi',h)$ be data for $\mathbb B'_k$ (real, or complex as in §1.3), $(\phi',\alpha')=(\phi,\alpha)(\mathbb B'_k;\Psi')$ the solution of Theorem 5.2 and $\bar\phi'$ its extension by $\Psi'$ to $C(\Omega'_1)$. Define $\Psi=\psi(\mathbb B_j,\mathbb B'_k;\Psi')$ on $\Omega_1\cup C(\Omega_1)$ by
$$\Psi(x)=(Q_n\phi')(y)+\frac{a_p}{a_n}L^{2(n-p)}\big[\psi'_p(y')-(Q_p\phi')(y')\big]\quad(x\in\Omega_1;\ y\ni x\ \text{an }n\text{-block},\ y'\ni x\ \text{a }p\text{-block}),\qquad\Psi(x)=\bar\phi'(x)\quad(x\notin\Omega_1).\tag{6.2}$$
The right side is constant on each $n$-block, so $\Psi$ is a lifted block-spin field of $\mathbb B_j$; off $\Omega_1$ it is $\phi'$ on the gap $\Omega'_1\setminus\Omega_1$ and $\Psi'$ outside $\Omega'_1$ (P2 (4.16), (4.20) with $a_0=\infty$). Only the values on $C(\Omega_1)$ enter the $\mathbb B_j$ problem; a point of $C(\Omega_1)$ is in $\Omega'_1$ or in $C(\Omega'_1)$ (it is adjacent to $\Omega_1\subseteq\Omega'_1$). This is P2 (4.19)–(4.21), $\psi=Q(\mathbb B_j)\phi+\frac1{a(\mathbb B_j)}Q^*(\mathbb B'_k,\mathbb B_j)a(\mathbb B'_k)(\psi'-Q(\mathbb B'_k)\phi)$ on
$\mathbb B_j\cup(\Omega_1^c\cap\Omega'_1)$ (with $a_0=\infty$, so that on the collar $\psi_0=\phi$, and $\psi_0=\psi'_0$ outside $\Omega'_1$): $a(\mathbb B_j)=a_nL^{-2n}$ on layer $n$, $a(\mathbb B'_k)=a_pL^{-2p}$, and $Q^*(\mathbb B'_k,\mathbb B_j)$ lifts a function on the $p$-blocks of $\mathbb B'_k$ to the $n$-blocks inside.
On $\Lambda_p\cap\Lambda'_p$ ($n=p$) the formula gives $\Psi=\psi'_p$, the compatibility $\psi=\psi'$ of P2 (4.16).

### 6.3 Theorem 6.1 (I-2; P2 Lemmas 4.2–4.4, Prop 4.1 at $\lambda=\infty$)

Let $\mathbb B_j\prec\mathbb B'_k$, constants $c_0,c_1,K_1$ of Theorem 5.2 (for both generating sets), $C_4=C_4(d)$. If $(\Psi',h)\in\tilde\Psi(\mathbb B'_k;\delta)$ with $C_4K_1\delta\le c_1$ (and $K_1\delta\le c_0$):

* **(i) Domain.** $(\Psi,h)\in\tilde\Psi(\mathbb B_j;C_4K_1\delta)$ (P2 (4.29): $(d+2)K_1\delta$; Lemma 6.2 below gives $C_4=d+2$ for (R1), (R2) and a larger numerical value for (R3); only existence of a $C_4(d)$ is used).
* **(ii) Composition identities (P2 (4.39)).** $\phi(\mathbb B_j;\Psi)=\phi(\mathbb B'_k;\Psi')|_{\Omega_1}$ and $\alpha(\mathbb B_j;\Psi)=\alpha(\mathbb B'_k;\Psi')|_{\Omega_1}$ (in fine units no rescaling $(L^j\eta)^{-2}$ is needed; P2's $\phi,\alpha$ extended off $\Omega_1$ by (4.40) are not needed at $\lambda=\infty$: only $\phi$ on $\Omega_1\cup C(\Omega_1)$, where $\bar\phi'$ is the extension).
* **(iii) Variational characterization** (for weights (6.1)). The composed Lagrangian of P2 (4.15) at $\lambda=\infty$ has the unknowns: a lifted field $\psi$ on the layers $1..j$ of $\mathbb B_j$ with $\psi=\psi'$ on $\Lambda_p\cap\Lambda'_p$; $\phi$ on $\Omega'_1$ with $|\phi|=1$ (on $\Omega_1$ the variable of the $\mathbb B_j$ problem; on the gap $\Omega'_1\setminus\Omega_1$ it is P2's $\psi_0$, which is constrained at $\lambda=\infty$ since P2's fourth line of (4.17) reads $\frac12(|\psi_0|^2-1)-\frac1\lambda\alpha=0$ there); multipliers $\alpha$ on $\Omega'_1$; the datum $\psi'$ and $\psi_0=\psi'_0$ outside $\Omega'_1$ fixed. Its coupling term is $\frac12\langle\psi'-Q(\mathbb B'_k,\mathbb B_j)\psi,\,a(\mathbb B'_k,\mathbb B_j)(\psi'-Q(\mathbb B'_k,\mathbb B_j)\psi)\rangle$ with $Q(\mathbb B'_k,\mathbb B_j)$, $a(\mathbb B'_k,\mathbb B_j)$ of P2 (4.5)–(4.10) (volume averages (4.6); $1/a=$ volume average of $1/a_{p-n}$, (4.7)). **Claim:** the critical-point system (4.17) (whose $\psi$-equations are (6.3) below) has exactly one solution with $|\alpha|'_2<c_0$, namely $(\Psi,\phi',\alpha')$ (P2 Lemma 4.2); and, if $C_4K_1\delta\le c_1$, $\Psi$ is the unique critical point of the reduced function $\mathcal A(\psi)$ (P2 (4.14): eliminate $\phi,\alpha$ by solving the $\mathbb B_j$ problem) in the class $\{\psi:(\psi,h)\in\tilde\Psi(\mathbb B_j;c_1),\ |\alpha(\mathbb B_j;\psi)|'_2<c_0\}$ (P2 Prop 4.1; the restriction on $\alpha$ is, as in P2 (4.23), in the **primed** norm), and the minimal value is the quadratic form of P2 (4.12) (composition (4.11)).
* **(iv) Complex data.** For $(\Psi'+\Psi'',h+h')\in\tilde\Psi^c(\mathbb B'_k;\delta,\varepsilon)$, $\delta,\varepsilon$ as in Theorem 5.2 and $4dK_1\delta\le\varepsilon$ (or $4dK_1\delta\le c_0$), formula (6.2) with the complex solution defines $\Psi$, which lies in $\tilde\Psi^c(\mathbb B_j;2C_4K_1\delta,\varepsilon)$ (P2 (4.37)) and the identities of (ii) hold. No analytic continuation of an identity from real data is used (this removes ER-037).

### 6.4 Proof of (ii) and (iv)-identities (complete)

By (EL) for $\mathbb B'_k$ at $x\in\Omega_1\subseteq\Omega'_1$ (rewrite $H_D\phi'=S'$ with $-\Delta\bar\phi'=-\Delta^D\phi'-\mathfrak b'(\Psi')$):
$$-\Delta\bar\phi'(x)+a_pL^{-2p}\big((Q_p\phi')(y')-\psi'_p(y')\big)+\mu\big(\phi'(x)-\tilde h(x)\big)+\alpha'(x)\phi'(x)=0 .\tag{6.3'}$$
From (6.2): $a_nL^{-2n}\big((Q_n\phi')(y)-\Psi(x)\big)=a_nL^{-2n}\frac{a_p}{a_n}L^{2(n-p)}\big((Q_p\phi')(y')-\psi_p'(y')\big)=a_pL^{-2p}\big((Q_p\phi')(y')-\psi'_p(y')\big)$. Hence
$$-\Delta\bar\phi'(x)+a_nL^{-2n}\big((Q_n\phi')(y)-\Psi(x)\big)+\mu(\phi'-\tilde h)(x)+\alpha'(x)\phi'(x)=0\qquad(x\in\Omega_1).\tag{6.4}$$
For $\mathbb B_j$, the extension of $\phi'|_{\Omega_1}$ to $C(\Omega_1)$ by the datum $\Psi$ *is* $\bar\phi'$ (by the second line of (6.2)), so $-\Delta\bar\phi'(x)$ is the lattice Laplacian of the $\mathbb B_j$-extended field and (6.4) is exactly (EL) for $(\mathbb B_j;\Psi,\tilde h)$ with $(\phi,\alpha)=(\phi',\alpha')|_{\Omega_1}$; also $\phi'\cdot\phi'=1$. The block-constant field $\tilde h$ of $\mathbb B'_k$ is constant on the finer blocks of $\mathbb B_j$. This is a pointwise algebraic identity: it holds for any weights $a_n\ne0$, any mass, and complex data (the bilinear structure is never used).

*Uniqueness class.* $\ell_{\mathbb B_j}(x)^2|\alpha'(x)|=L^{2n}|\alpha'(x)|\le L^{2n}K_1\delta L^{-2p}\le K_1\delta\le c_0$ since $p\ge n$; so $(\phi',\alpha')|_{\Omega_1}$ is a solution of (EL) for $\mathbb B_j$ in the class $|\alpha|_2^{\mathbb B_j}<c_0$ (this is P2 (4.31)). If $(\Psi,\tilde h)$ is in the domain of Theorem 5.2 for $\mathbb B_j$ (part (i), resp. its complex analogue Lemma 6.3), uniqueness there gives the identities of (ii). $\square$

### 6.5 Proof of (iii) (complete, using (C1))

Let $y'\in\Lambda'_p\setminus\Lambda_p$, $B=y'$ its $p$-block; $B$ is partitioned into the sub-blocks $x$ of $\mathbb B_j$ of layers $n_x\in\{0,\dots,p-1\}$ (layer 0: single collar or exterior sites), with volume fractions $w_x=L^{(n_x-p)d}$ and $\mathcal Q_B\psi:=\sum_xw_x\psi(x)=Q(\Lambda_p(y'),\mathbb B_j)\psi$ (P2 (4.6)), $u^{(p)}:=1/a^{(p)}=\sum_xw_xu_{p-n_x}$ (P2 (4.7)). The composed action contributes $\frac12a^{(p)}L^{-2p}L^{pd}|\psi'_p(y')-\mathcal Q_B\psi|^2$ and $A(\mathbb B_j)$ the term $\frac12a_nL^{-2n}L^{n d}|\psi_n(x)-Q_n\phi(x)|^2$; the derivative in $\psi_{n}(x)$ is
$$a^{(p)}L^{-2p}\big(\mathcal Q_B\psi-\psi'_p(y')\big)+a_nL^{-2n}\big(\psi_n(x)-(Q_n\phi)(x)\big)=0.\tag{6.3}$$
(For $n_x=0$ the second term is absent: $a_0=\infty$ is read as $u_0=0$, i.e. $\psi_0=\phi$; at $\lambda=\infty$ it is the identity "(4.20) holds on $\Omega_1^c\cap\Omega'_1$".) Solve: $\psi_n(x)=Q_n\phi(x)-\frac{a^{(p)}}{a_n}L^{2(n-p)}t$ with $t:=\mathcal Q_B\psi-\psi'_p$. Averaging with weights $w_x$, using $\sum_xw_xQ_n\phi(x)=Q_p\phi(y')$ (block averages of nested blocks) and (C1) in the form $\frac{L^{2(n-p)}}{a_n}=u_p-u_{p-n}$:
$$t=Q_p\phi-\psi'_p-t\,a^{(p)}\sum_xw_x(u_p-u_{p-n_x})=Q_p\phi-\psi'_p-t\,a^{(p)}(u_p-u^{(p)}),\quad\text{so}\quad t\,\frac{a^{(p)}}{a_p}=Q_p\phi-\psi'_p ,$$
because $a^{(p)}u^{(p)}=1$ and $a^{(p)}u_p=a^{(p)}/a_p>0$. So $t=-\frac{a_p}{a^{(p)}}(\psi'_p-Q_p\phi)$ is uniquely determined and
$$\psi_n(x)=Q_n\phi(x)+\frac{a_p}{a_n}L^{2(n-p)}\big(\psi'_p(y')-Q_p\phi(y')\big),$$
which is (6.2) (P2 (4.19) — page 636). Thus for every $\phi$ the linear system (6.3) has the unique solution (6.2) (this is P2's "very simple system of linear equations", p. 635; for the gap rows $n_x=0$, $\psi_0=\phi$ is the case $u_0=0$).
Substituting into the remaining equations: for $x\in\Omega_1$ the $\phi$-equation of the composed system is (EL) for $\mathbb B_j$ with $\Psi$, which after (6.2) is (6.3'), i.e. (EL) for $\mathbb B'_k$ at $x$ (§6.4 read backwards); for a gap site $x\in\Omega'_1\setminus\Omega_1$ (layer $p$ of $\mathbb B'_k$), the derivative of the coupling term in $\psi_0(x)=\phi(x)$ is $a^{(p)}L^{-2p}t=-a_pL^{-2p}(\psi'_p-Q_p\phi)$, so the gap equation is again (6.3') at $x$. Hence the system (4.17) is equivalent to (EL) for $\mathbb B'_k$ plus the explicit (6.2), and by Theorem 5.2 for $\mathbb B'_k$ it has the unique solution with $|\alpha|'_2<c_0$ (P2 Lemma 4.2).
For the reduced function: if $\psi$ is a critical point of $\mathcal A$, put $\phi=\phi(\mathbb B_j;\psi)$, $\alpha=\alpha(\mathbb B_j;\psi)$; since $\partial_\phi\mathcal J=\partial_\alpha\mathcal J=0$ there, $(\psi,\phi,\alpha)$ solves (4.17), and if $|\alpha|'_2<c_0$ it equals $(\Psi,\phi',\alpha')$ by the first claim. Conversely $\Psi$ is in the class: $(\Psi,h)\in\tilde\Psi(\mathbb B_j;c_1)$ by (i), and $|\alpha'|'_2\le K_1\delta<c_0$. UNCERTAIN: the class in P2 Prop 4.1 mixes the $\mathbb B_j$-domain condition with the primed bound on $\alpha$; I read it as printed. $\square$

### 6.6 Lemma 6.2 (P2 Lemma 4.3; sketched with every estimate)

Let $(\Psi',h)\in\tilde\Psi(\mathbb B'_k;\delta)$ real, $\phi'$ as in Theorem 5.2, $r':=\psi'_p-Q_p\phi'$ and $\kappa:=\frac{a_p}{a_n}L^{2(n-p)}\in[0,1]$. Theorem 5.2(3) gives $|r'|\le|\phi'-Q^*\psi'|_0\le K_1\delta$ ($Q_p(Q^*\psi')=\psi'_p$) and $|\partial\bar\phi'|(b)\le K_1\delta/\ell'(b)$ with $\ell'\ge L^n$ on $\Omega_n$ (as $p\ge n$).

* (E1) $|\Psi-Q_n\phi'|\le\kappa|r'|\le K_1\delta$.
* (E2) For two sites $x_1,x_2$ of an $n$-block $y$: $|\phi'(x_1)-\phi'(x_2)|\le d(L^n-1)\cdot K_1\delta L^{-n}\le dK_1\delta$ (a monotone lattice path inside the block, all bonds in layers $\ge n$ of $\mathbb B'_k$). For $x_1\in y_1$, $x_2\in y_2$ in adjacent $n$-blocks, $|\phi'(x_1)-\phi'(x_2)|\le(d+1)K_1\delta$, whence $|Q_n\phi'(y_1)-Q_n\phi'(y_2)|\le K_1\delta$ for adjacent same-layer blocks (centres $L^n$ apart: a chain of $L^n$ bonds each $\le K_1\delta L^{-n}$; P2 (4.24) gets $3K_1\delta$ for $\Psi$ in total, which is $K_1\delta+2\kappa K_1\delta$).
* (R1) same layer: $|\Psi(y_1)-\Psi(y_2)|\le K_1\delta+2K_1\delta=3K_1\delta$ (P2 (4.24) has $3K_1\delta$). Layers $n$, $n-1$ (and collar–layer 1): the two blocks lie in a common $n$-cell, of $\ell^1$-diameter $<dL^n\cdot2$, and the bond bound along a path is $K_1\delta/\ell'$ with $\ell'\ge L^{n-1}$ (sites of layer $n-1$ of $\mathbb B_j$ may be in layer $n-1$ of $\mathbb B'_k$), so the crude estimate is $|Q_n\phi'(y_1)-Q_{n-1}\phi'(y_2)|\le2dL\,K_1\delta$. P2 (4.24)–(4.28) states $(d+2)K_1\delta$ ("$|(Q_{n-1}\phi_k)(x)-(Q_n\phi_k)(x)|$ can be bounded by $dK_1\delta$"), which needs $\ell'\ge L^n$ on the whole $n$-block; I do not see why this holds when part of the block lies in layer $n-1$ of $\mathbb B'_k$. So $C_4=C_4(d,L)$ here; this costs nothing downstream (see below).
* (R2) $\phi'\cdot\phi'=1$ gives $Q_n\phi'\cdot Q_n\phi'-1=-\frac12\mathrm{avg}_{x_1,x_2\in y}|\phi'(x_1)-\phi'(x_2)|^2\ge-\frac12d^2K_1^2\delta^2$ (this is the point where $\lambda=\infty$ simplifies P2 (4.25): no term $\frac2\lambda Q_n|\alpha|$). With (E1): $|\Psi\cdot\Psi-1|\le\frac12d^2K_1^2\delta^2+2K_1\delta+K_1^2\delta^2\le(d+2)K_1\delta$ for $K_1\delta\le\frac{d}{d^2+2}$.
* (R3) $|\phi'-h|(x)\le K_1\delta/(\ell'(x)\sqrt\mu)\le K_1\delta L^{-n}/\sqrt\mu$, so $\sqrt\mu L^n|Q_n\phi'-h|\le K_1\delta$, and $\sqrt\mu L^n\le1$: $\sqrt\mu L^n|\Psi-h|\le2K_1\delta$; with $|\Psi_0-\Psi|=||\Psi|-1|\le(d+2)K_1\delta$ and $\mu L^{2n}\le1$: $\mu L^{2n}|1-\Psi_0\cdot h|=\frac12\mu L^{2n}|\Psi_0-h|^2\le8(d+2)^2K_1^2\delta^2$.
* (R4) is the hypothesis (unchanged $\mu$, $h$). Collar: on $C(\Omega_1)\cap\Omega'_1$, $\Psi=\phi'$ with $|\phi'|=1$ exactly; on $C(\Omega_1)\setminus\Omega'_1$, $\Psi=\Psi'$ satisfies (R2) with $\delta$. (R1) between the collar and layer 1: $|Q_1\phi'(y)-\bar\phi'(x')|\le(d+1)K_1\delta$ (chain of $\le(d+1)L$ bonds, $\ell'\ge L$).

*(E3) α in the primed norm:* $\ell_{\mathbb B_j}^2|\alpha'|\le K_1\delta$ as in §6.4.

So $(\Psi,h)\in\tilde\Psi(\mathbb B_j;C_4K_1\delta)$ with $C_4=C_4(d,L)$; P2 claims $(d+2)K_1\delta$ for all of (R1)–(R3). UNCERTAIN: whether the $L$-dependence in the cross-layer step can be removed as P2 asserts; I could not reproduce P2 (4.26)–(4.28) from page 637 alone. An $L$-dependent $C_4$ suffices for everything downstream: $K_1$ itself depends on $L$, and the constants of Theorem 5.2 for $\mathbb B_j$ are then used at the larger $\delta$, i.e. $c_1'=c_1/(C_4K_1)$. *Status: sketched.* $\square$

**Lemma 6.3 (P2 Lemma 4.4, complex data; sketched).** For $(\Psi'+\Psi'',h+h')\in\tilde\Psi^c(\mathbb B'_k;\delta,\varepsilon)$ apply (E1)–(R4) to $\Psi^c-\Psi^r$ in each condition: the differences of the formula (6.2) for complex and real data are $Q_n(\phi'^c-\phi'^r)+\kappa(\Psi''-Q_p(\phi'^c-\phi'^r))$ with $|\phi'^c-\phi'^r|_0\le\varepsilon+K_1\delta$ (Theorem 5.2(3), last line), giving (C2) with $2(\varepsilon+\dots)$ — this is where the condition $4dK_1\delta\le\varepsilon$ enters — and the bond differences (C1) by (E2) applied to $\phi'^c-\phi'^r$ (whose gradient is $\le2K_1\delta/\ell'$). $h'$ is restricted unchanged ((C3) at layer $n\le p$ follows from (C3) at layer $p$ because $\mu L^{2n}\le\mu L^{2p}$).

### 6.7 Proposition 6.4 (P2 (4.41)–(4.43), the perturbed composition; proved for $g\equiv0$)

Let $(\delta\Psi',\phi_0,\alpha_0,f_1)$ be data for $\mathbb B'_k$ as in Prop 5.1 with $g\equiv0$ on $\Omega'_1$, and $(\delta\phi',\delta\alpha')$ its solution. Define $\delta\Psi$ by (6.2) with $\phi'\to\delta\phi'$, $\psi'_p\to\delta\Psi'_p$ (no $h$) and $\delta\Psi=\overline{\delta\phi'}$ on $C(\Omega_1)$, where $\overline{\delta\phi'}$ is $\delta\phi'$ on $\Omega'_1$ and $\delta\Psi'$ on $C(\Omega'_1)$. Then (P2 (4.42)):
$$\delta\psi(\mathbb B_j,\mathbb B'_k;\delta\Psi',\phi_0,\alpha_0,f_1)=Q(\mathbb B_j)\delta\phi'+\frac1{a(\mathbb B_j)}Q^*(\mathbb B'_k,\mathbb B_j)a(\mathbb B'_k)\big(\delta\Psi'-Q(\mathbb B'_k)\delta\phi'\big)$$
(in P2 the printed (4.42) writes $\psi'$ for the perturbation $\delta\psi'$), $|\delta\Psi|\le(2K_2+1)\delta_1$ (because $\kappa\le1$), and if $K_2(2K_2+1)\delta_1\le c_6$ then $(\delta\phi',\delta\alpha')|_{\Omega_1}$ is the solution of Prop 5.1 for $\mathbb B_j$ with the data $(\delta\Psi,\phi_0|,\alpha_0|,f_1|)$: P2 (4.43).

*Proof.* The data hypotheses restrict to $\mathbb B_j$: $\ell_{\mathbb B_j}\le\ell'$ on $\Omega_1$ makes `IsSmoothField`, $|\alpha_0|_2$, $|f_1|_2$ weaker conditions; $g\equiv0$ restricts (this is the reason for $g\equiv0$: a nonzero defect has a jump at the wall of the smaller $\Omega_1$); $\delta\Psi$ is block-constant for $\mathbb B_j$ by (6.2), and $|\delta\Psi|\le|Q_n\delta\phi'|+\kappa|\delta\Psi'-Q_p\delta\phi'|\le K_2\delta_1+(1+K_2)\delta_1$ on $\Omega_1$, and on the collar $|\overline{\delta\phi'}|\le\max(K_2\delta_1,\delta_1)$.
The equations: (P-1) for $\mathbb B'_k$ at $x\in\Omega_1$, rewritten with $-\Delta^{D'}\delta\phi'-\mathfrak b'(\delta\Psi')=-\Delta\overline{\delta\phi'}$, is
$-\Delta\overline{\delta\phi'}+a_pL^{-2p}(Q_p\delta\phi'-\delta\Psi'_p)+(\mu+\alpha_0+\delta\alpha')\delta\phi'+\delta\alpha'\phi_0-f_1=0$; the identity $a_nL^{-2n}(Q_n\delta\phi'-\delta\Psi)=a_pL^{-2p}(Q_p\delta\phi'-\delta\Psi'_p)$ from (6.2) turns it into (P-1) for $\mathbb B_j$ (the $\mathbb B_j$-extension of $\delta\phi'$ off $\Omega_1$ is the datum $\delta\Psi=\overline{\delta\phi'}$ on $C(\Omega_1)$). (P-2) restricts. $|\delta\alpha'|_2^{\mathbb B_j}\le|\delta\alpha'|'_2<c_6$. Uniqueness in Prop 5.1 gives the claim. $\square$

The identity (4.43) in the form "$\delta\alpha(\mathbb B_j;\dots)=(L^j\eta)^{2}\delta\alpha(\mathbb B'_k;\dots)$" has in fine units no rescaling factor. Combined with Theorem 5.2(6) it gives (4.39) for complex data once more, independently of Lemma 6.3.

---

## 7. Def-5: the background fields and their characterization theorems (stated for freezing)

Rule 4 of AGENTS.md: an object defined as "the unique ..." is defined only after its $\exists!$ theorem is proved, and lands with a characterization theorem. The `∃!` theorems are Theorem 5.2(4) (real minimiser), Theorem 5.2(1) (complex solution) and Theorem 6.1. Proposed Lean shape (all fields lifted as in §1.2; `G : GeneratingSet d L N₀ k ϱ`, `a`, `μ`, data as `BgData G`):

**Def-5(a) real background field.** `IsMinimizer G a μ h Ψ φ` := $\phi\in(S^{N-1})^{\Omega_1}$ and $A(\phi)\le A(\sigma)$ for all $\sigma\in(S^{N-1})^{\Omega_1}$ (with $A$ of (1.2)). Define, for a proof `hΨ : ∃! φ, IsMinimizer G a μ h Ψ φ`,
$$\phi(\mathbb B_k;\Psi,h)\ :=\ \texttt{hΨ.choose},\qquad \alpha(\mathbb B_k;\Psi,h)(x)\ :=\ -\phi(x)\cdot\big(H_D(0)\phi-S(\Psi,h)\big)(x).$$
*Characterization theorem 7.1* (from Thm 5.2(4)): for $(\Psi,h)\in\tilde\Psi(\mathbb B_k;c_1)$ the hypothesis `hΨ` holds; $(\phi,\alpha)$ satisfies (EL) with $|\alpha|_2<c_0$ and the bounds of Thm 5.2(3); it is the only solution of (EL) with $|\alpha|_2<c_0$; and for every $\sigma$, $A(\sigma)-A(\phi)=\frac12\langle\sigma-\phi,H_D(\alpha)(\sigma-\phi)\rangle$.
Remark: the domain of definition is "wherever the minimiser is unique" (constant-free); $c_1$ enters only through the theorem. The multiplier is defined by the explicit formula, not by "the" multiplier, so Def-5(a) needs no further uniqueness.

**Def-5(b) complex background field.** Fix once and for all the constants $(c_0,c_1,K_1)$ of Theorem 5.2 as `Classical.choose` of its statement (the "constant package"). For $(\Psi^c,\tilde h)\in\tilde\Psi^c(\mathbb B_k;c_1,c_0)$ ($\delta=c_1$, $\varepsilon=c_0$ — P2: "defined certainly on $\tilde\Psi^c(\mathbb B_k;c_1,c_0)$", (1.17)), let $(\phi^c,\alpha^c)$ be the unique solution of (EL) with $|\alpha|_2<c_0$. *Characterization theorem 7.2:* it is analytic on that open set, agrees with Def-5(a) on real data, satisfies Thm 5.2(3), and satisfies the linear response of Prop 5.4. (If $\mu L^{2k}c_0^2>c_1^2$ the domain is empty by the hypothesis $\nu\varepsilon^2\le\delta^2$; P2 has the same restriction and the extension to $\nu$ large is not needed since the roots use $\nu\to0$ along the flow.)

**Def-5(c) block-spin fields of a pair of generating sets.** $\psi(\mathbb B_j,\mathbb B'_k;\Psi')$ := (6.2), with $\phi'$ from Def-5(a) (real) or Def-5(b) (complex); $\psi^{(j)}_k(\psi):=\psi(\mathbb B_j,\mathbb B'_k;\Psi')$ for the pair used in P1–P7. *Characterization theorem 7.3* (Theorem 6.1(i)–(iv)): it lies in the data domain of $\mathbb B_j$, solves the composed system (4.17), is the unique critical point in the stated class, and obeys the identities of Theorem 6.1(ii): $\phi(\mathbb B_j;\Psi)=\phi(\mathbb B'_k;\Psi')|_{\Omega_1}$, $\alpha(\mathbb B_j;\Psi)=\alpha(\mathbb B'_k;\Psi')|_{\Omega_1}$.
Since (6.2) is an explicit formula, no `∃!` is needed to define it; the theorem is needed for the *meaning* (it is the object of P2 Prop 4.1) and for the domain.

**Def-5(d) increments.** $\delta\phi_k,\delta\alpha_k$ := the solution of Prop 5.1 with $\phi_0=\phi_k$, $\alpha_0=\alpha_k$, $f_1=0$, $g=0$, defined after Prop 5.1 and characterized by Theorem 5.2(6): $\phi(\Psi+\delta\Psi)=\phi_k+\delta\phi_k$.

**Frozen statements proposed** (size: about 14 statements; all with explicit $\exists$ constants):
I-1(a) existence, uniqueness, bounds (Thm 5.2(1),(3)); I-1(b) analyticity (2); I-1(c) minimiser (4); I-1(d) Prop 5.1; I-2(a) Thm 6.1(i),(ii); I-2(b) (iv); I-2(c) Prop 6.4; Def-5(a)–(d) with Theorems 7.1–7.3.
Recommended order: freeze the data-domain predicate $\tilde\Psi^c$ **first** (it is a definition and carries the faithfulness risk, §10 Q1), then Def-5(a) with I-1.

---

## 8. What changes at $\lambda=\infty$, and the status of P2's errata rows

**8.1 Which bounds disappear.**
* C3 of GREEN §2 (P2 (3.40)–(3.41), P3 (2.31)–(2.34): $|\lambda G(\lambda)f|\le O(1)|f|$ uniformly in $\lambda$) does not occur: $\frac1\lambda=0$, and the Banach iteration of §5.1 replaces the Neumann series in $\delta\alpha$ with the operator $1+\frac1\lambda(-\Delta+Q^*aQ+\nu)$ of P2 (3.39). ER-029 is moot for I-1.
* The hypothesis $\eta^2\lambda\ge1$ and the case distinction $\lambda\eta^2\ge8dL^2+2$ (P2 p. 626) disappear; $\lambda\ge1$ in P2 Prop 2.2 disappears (§4.3 is exact).
* The $\lambda$-dependence of $\alpha_0$: P2 (3.3) sets $\alpha_0=\frac\lambda2(\phi_0^2-1)$, so that $\alpha_0$ is determined by $\phi_0$; at $\lambda=\infty$ one takes $\phi_0\cdot\phi_0=1$ exactly and $\alpha_0=\sum h_y\alpha^y$ as an independent smooth field. The datum $\alpha_1$ of Prop 3.1 ($\alpha_1/\lambda$ in the second equation) disappears; the sphere defect is $g=\phi_0\cdot\phi_0-1$, which is zero in all applications of P2 (Lemma 3.1, Cor 3.1, P3 line "$f_1=0,\alpha_1=0$").
* P2 (3.48) (second variation to conclude "minimum") is replaced by the exact identity (5.3).
* P2 (4.40) ($\alpha=\frac{\lambda_j}2(\psi^2-1)$ off $\Omega_1$) has no meaning at $\lambda=\infty$; at $\lambda=\infty$ the exterior field is data (outside $\Omega_1$ the values are $\Psi$, no constraint is imposed there except on the gap $\Omega'_1\setminus\Omega_1$, where they are values of $\phi'$).

**8.2 New constraint terms.** (a) The commutator $K(\phi_0)$ and the quadratic remainder $R(\delta\phi)$ (Lemmas 3.1, 3.2): P2's (3.31)–(3.38) written in full, in the discrete Leibniz form (3.1). (b) The constrained operator $\Pi=G\phi[\phi\cdot G\phi]^{-1}\phi\cdot G$ in the linear response (Prop 5.4), the tangent-space Green's function $G-\Pi$; it carries the $\lambda=\infty$ form of P4 (2.23) and P3 (3.9). It is not needed to *prove* I-1, only to *use* it (I-4, P4 §2). (c) The bilinear (not sesquilinear) constraint $\phi\cdot\phi=1$ for complex data.

**8.3 Errata rows of P2 (`notes/ERRATA.md`).**

| Row | Status here |
|---|---|
| ER-026 (Green's function bounds with Dirichlet, $\nu$, complex $\alpha$, variable $a$, multiscale $Q$) | replaced: (G) is G-2(iv), proved by our own route (landed Agmon, `prop48`; W16). Only (G) is used |
| ER-027 ($C_\alpha\sim\alpha^{-d-1}$) | not used: the contraction needs no Hölder norm; a fixed $\theta$ only for Thm 5.2(3), last line, via G-2(iii) |
| ER-028 (wrong citation $[2(b)]$) | moot |
| ER-029 ($\lambda G(\lambda)$ uniformity) | moot at $\lambda=\infty$ (§8.1) |
| ER-030 (Prop 2.2 omitted) | proved at $\lambda=\infty$ (§4.3), exact formula; the P6 half of the row is outside this document |
| ER-031 ($F_2$ only sampled) | replaced by Lemmas 3.1, 3.2 with explicit constants |
| ER-032, ER-033 (constants 80, 78, 56, 22) | not needed; Lemma 4.1 gives absolute constants |
| ER-034 (misprint $a(1-L^2)$) | confirmed on the page image (p. 632, (4.8)); (4.4) $a_r=a\frac{1-L^{-2}}{1-L^{-2r}}$ confirmed (p. 631); (6.1) |
| ER-035 ($\nu(|h|^2-1)$) | confirmed on the page image (p. 610, (1.11)): $|\nu(|h|^2-1)|<\delta^2$, (R4) |
| ER-036 (topology of analyticity) | settled: finite-dimensional data spaces; Prop 5.1 uses `exists_analytic_fixedPoint` |
| ER-037 (complex (4.39)) | settled: the identity (6.4) is algebraic and holds verbatim for complex data; uniqueness in Thm 5.2 replaces analytic continuation |
| ER-038 ((4.41)–(4.43) sketch) | stated and proved as Prop 6.4 (for $g\equiv0$); note P2 (4.42) writes $\psi'$ for $\delta\psi'$ |
| ER-039 (general potentials) | not needed |
| ER-040 (role of $M$, $RM$ in (1.1)) | $\varrho=RM$ enters only through $\varrho\ge R_0(d,L)$ in G-2 (decay across layers), the wall-in-layer-1 observation (§1.1) and (h1)–(h4); no condition on $M$ arises from the variational problems at $\lambda=\infty$ |
| ER-041 (Hölder exponent) | one fixed $\theta$ suffices (GREEN C1) |
| ER-016 (P1 (3.107) cited from P2) | supplied by Thm 5.2 (the bound on $\partial^2\psi^{(j)}_k$ follows from Thm 5.2(3) and (6.2) with the Hölder part) |

New candidate errata (not in the ledger; none affects results): (i) `review/papers/P2-variational-problems.md` §2 prints (1.15) with $K_1(L^j\eta)^{-1}\delta$ on the first line; the page reads $K_1\delta$ (error of the review, not of P2). (ii) P2 (4.24)–(4.28): the cross-layer bond estimate $(d+2)K_1\delta$ is not clear (§6.6). (iii) P2 (4.42) prints $\psi'$ for the perturbation.

---

## 9. Lean plan and size estimate

All files under `Balaban/Background/` (new) unless noted; imports on the landed modules of §2. Line counts are estimates in the style of GREEN §5 (statements included).

| Module | Content | Lines | Risk |
|---|---|---|---|
| `Data.lean` | lifted fields, collar, `BgData`, the predicates $\tilde\Psi$, $\tilde\Psi^c$ (R1)–(R4), (C1)–(C3), source $S$ (1.1), action (1.2), (EL) | 700–1,000 | medium (faithfulness) |
| `Calculus.lean` | norms $|\cdot|_\sigma$, $|\partial\cdot|_1$ on $\Omega_1$ with zero extension, Leibniz (3.1), Lemmas 3.1, 3.2, 3.3; wall-in-layer-1 lemma | 900–1,400 | medium (zero extension, bond cost across layers; reuse `IsSmoothField`, `commK`, `bondCost`) |
| `ConstantLocal.lean` | Lemma 4.1, Prop 4.1 (a)–(d), Lemma 4.2 (needs the landed `ConstantConfig*` re-run for $a\le2$, $a+\nu\ge\frac12$), §4.3 | 600–900 | low |
| `Contraction.lean` | Prop 5.1: $\delta\phi(\delta\alpha)$, identity (5.2), $\mathcal N$, estimates, fixed point, analyticity, uniqueness | 800–1,200 | low once (G) and Calculus exist |
| `Interpolation.lean` | B-spline partition of unity on the multiscale lattice (h1)–(h4) | 1,200–1,800 | **high**: $C^{1,1}$ bumps at several scales, second differences |
| `Approximate.lean` | Lemma 5.3: (A1)–(A6), residual $f_0$ | 1,800–2,800 | **high** |
| `Existence.lean` | Thm 5.2 items 1–6 from 5.1 and 5.3: constants, uniqueness, analyticity, (5.3) minimiser, (1.16) | 800–1,200 | low |
| `LinearResponse.lean` | Prop 5.4 on top of `constraintForm_isUnit`, `constrainedOp_eq`; $G-\Pi\succeq0$ | 400–700 | low |
| `Composition.lean` | (6.1), (C1), (6.2), identities (6.4), (iii) of Thm 6.1, Prop 6.4 | 800–1,200 | low |
| `CompositionDomain.lean` | Lemma 6.2, 6.3: (E1)–(R4) | 1,500–2,500 | medium–high (case analysis over layers) |
| `Def5.lean` | Def-5(a)–(d) and Theorems 7.1–7.3 | 400–600 | low |

Total about **10,000–15,000 lines**; the two high-risk modules (`Interpolation`, `Approximate`) are 3,000–4,600 of them. Landed reusable: `Constrained.lean`, `Constraint*.lean` (≈3,500 lines, for §5.5), `ConstantConfig*` (686), `Contraction.lean` (163), `Analyticity.lean` (92), `GeneratingSet.lean`, `Operator.lean`, `Coercivity*.lean`.
Order of work: `Data`, `Calculus`, `ConstantLocal` (parallel); `Contraction` as soon as W16 lands; `Interpolation` can start immediately (it needs only `GeneratingSet`); `Composition` needs `Existence`.
Alternative to reduce risk: a *non-smooth* approximate solution does not work (a block-constant $\phi_0$ has $|\partial\phi_0|_1\sim\ell\delta$, not $\delta$); a $C^{1,1}$ interpolant is necessary. A cheaper choice than normalised B-splines would be the multilinear interpolation on the lattice of spacing $L^n$ plus a correction at layer interfaces; I have not checked that its second differences stay $O(\delta\ell^{-2})$ across interfaces.

---

## 10. Questions

1. **(Data domain, freezing.)** Is the translation (R1)–(R4), (C1)–(C3) of P2 (1.11), (1.12) acceptable as the definition of $\tilde\Psi$, $\tilde\Psi^c$? Points where I read P2 narrowly: the collar $\Lambda_0$ is the one-site collar $C(\Omega_1)$ (P2: "one layer of big blocks", p. 610; a thicker collar would only add conditions); $h'$ is a block-constant field; (R3), (C3) are imposed on all layers including the collar though only layers $1..k$ are used. The question for the author/seaturtle2: is a thicker collar of blocks needed by P3–P7 (e.g. for the localization domains $\tilde\Omega^{\sim}$)?
2. **(Defect version.)** Do P3–P7 (I-4, I-5) use Prop 3.1 with $\phi_0\cdot\phi_0\ne1$? I treated $g=\phi_0\cdot\phi_0-1\ne0$ in Prop 5.1 (hypothesis (P4), includes the wall) but I-2' (Prop 6.4) only for $g\equiv0$. P3's text (review, line "φ_0 = φ(B_{k+1}; θ, s) has |φ_0²−1|<") suggests the decoupled fields may have $g\ne0$ for finite $\lambda$; at $\lambda=\infty$ the analytic extension in $s$ of an exact solution has $g=0$. This needs a check against the I-4 design.
3. **(Hölder.)** Is the Hölder bound of Thm 5.2(3) needed anywhere beyond P1 (3.107) (one fixed exponent)? If so G-2(iii) (W12b) is on the critical path of I-1(a); otherwise drop it from the frozen statement.
4. **(Weights.)** P2's weights are $a_j=\frac{1-L^{-2k}}{1-L^{-2j}}a_k$ (one geometric sequence $a_r$, (6.1)); I-1 holds for any weights in $(\frac12,2]$, but I-2(iii) and the identity (C1) need (6.1). Should the frozen I-1 be stated for general admissible weights (as the landed `IsAdmissibleWeights`) and I-2 for (6.1) only? (Recommended.)
5. **(Constants depend on $N$.)** Because $G$ acts componentwise and bounds are in the Euclidean norm of $\mathbb C^N$, $B_1$, $K_i$ depend on $N$; P2 says $d,L$ only. Harmless for Roland's statement ($N$ fixed), but the interface should say "depending on $d,L,N$".
6. **(Mass range.)** $0\le\mu\le L^{-2k}$ (P2's $0<\nu\le1$ at the top scale). Is the $\nu>0$ strictness needed anywhere? Not by I-1; the data conditions (R3), (C3) are vacuous at $\mu=0$, so the massless background fields (P9 at $\nu\to0$) are covered.
