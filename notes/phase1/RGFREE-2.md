# Mass-free fluctuation data and the switch: follow-up

This note follows [RGFREE.md](RGFREE.md). Put $u=k+1$, $\varepsilon=\varepsilon_u$, $\beta_u=\beta_kL^{d-2}$, $z=1+\varepsilon\xi_1$, and $\beta(\xi)^{-1}=(1+\xi_3)\beta_u^{-1}$. On $\|\xi\|_\infty\le c_{10}$ let
$$
\widehat\beta^{-1}:=(1+c_{10})\beta_u^{-1},\qquad q=L^{-2\gamma}.
\tag{0.1}
$$
Every analytic bound below is meant on an open neighbourhood of the stated closed polydisc, as required by the landed Lean theorem.

## 1. The mass-free bound

### 1.1 Source statements and logical status

The current FLUCTUATION.md is **v2**, SHA-256 b8f27884637f48b3815b624e3175611b80816bcebf21a370f5d6fbff7d9c38c1. Its Lemma 3.5(i)–(iii) is a **proved algebraic** renormalization identity and background response formula. In the mass-free convention its $C_3$ is
$\nu(1+\xi_2)[\langle\delta\phi,\phi-h\rangle+\|\delta\phi\|^2/2]$; (3.10) defines the unrenormalized effective term from the fluctuation term and all old-action differences. Its Theorem 3.1(g) asserts local joint analyticity and bounds $C_4'\varepsilon^2r$, $C_4'\varepsilon^2r^2$, $(NL^dB_{\mathbb L}+1+C_5E_0r)K_0$ for $C_1,C_2,\mathscr E_u$ on $\|\xi\|_\infty<r\le\epsilon_R$. Theorem 3.1(h) gives the ordinary observable estimate.

The status paragraph immediately following Theorem 3.1 marks (g) and (h) **conditional on OPEN assertions**: the actual RG-to-termwise premises, auxiliary cover and NC, and fluctuation I-5. The modular variant is additionally needed in subdomains; Theorem 3.1(f), for old-action transport there, is conditional on OPEN P6 Propositions 2.1–2.2 transfer. Thus neither (g) nor (h) is presently a proved physical estimate. Lemma 5.7 calls its Cauchy computation of (B1) “proved,” but its proof invokes (g); it is an algebraic/analytic implication conditional on those open premises.

Theorem 3.1(h) does not supply an RG forcing bound. It is used only for the observable after the ordinary step. The RG forcing comes from (g), Lemma 3.5, and the constant-field and second-moment Cauchy estimates of P4 (5.15)–(5.17), printed p. 712.

### 1.2 A precise sufficient estimate

**OPEN FREE-LOC.** Choose $0<c_{10}\le\min\{1/16,\epsilon_R\}$. The mass-free $\mathscr E_u$ of Lemma 3.5(iii) has the local expansion of Theorem 3.1(g), uniformly on a common neighbourhood of
$$
\|\xi\|_\infty\le c_{10},\quad
|U-1|\le r_\psi,\quad |V-m|\le r_b,\quad |W|\le r_b,
\quad r_\psi=\varepsilon/(4K_1),\quad r_b=r_\psi^2,
\tag{1.1}
$$
in SMALLFIELD.md §2.3 Step 3's invariant constant-field coordinates, with $b=mh$, independent of $m\downarrow0$. The local terms retain their decay after every old-action composition in Lemma 3.5(iii), have the torus-independent thermodynamic limit and weighted $x_1^2$ moment sum of P4 (5.15)–(5.17), and commute with conjugation. The mass-free $C_3$ is included in the counterterm identity. This assertion includes the actual termwise, cover, and fluctuation I-5 premises that v2 Theorem 3.1(g) leaves open. In particular, mere analyticity in $h$ on a mass-dependent slice does not imply the uniform $b$-radius in (1.1).

**Proposition 1 (conditional on OPEN FREE-LOC).** Let
$$
B_E:=K_0(NL^dB_{\mathbb L}+1+C_5E_0c_{10}),\quad
K_5:=9K_0(16dK_1LM)^2((2L+3)M)^d,\quad
B_{\rm free}:=10(1+B_E)K_5.
\tag{1.2}
$$
Then the actual mass-free divided datum $\widetilde f$ of RGFREE.md (1.12), including the transverse moment (1.12b), is jointly analytic on a neighbourhood of $\overline{\mathcal P}_{c_{10}}\times P$, conjugation equivariant, and
$$
\sup_{p\in P,\ \|\xi\|_\infty\le c_{10}}
\|\widetilde f(\xi,p)\|_\infty
\le B_{\rm free}\widehat\beta^{-1}\varepsilon^{-2}.
\tag{1.3}
$$

*Proof.* At trial radius $c_{10}$, Theorem 3.1(g)'s proposed local bound gives $|\mathscr E_u(z,Y)|\le B_Ee^{-\kappa_a d^{\rm cov}(Y)}$ after absorbing its local-sum convention into $B_E$. The termwise sum converges normally. Cauchy on the strict smaller polydisc (1.1) gives $|\partial_U f_u|\le4K_1B_E\varepsilon^{-1}$ and $|\partial_bf_u\cdot e_1|\le16K_1^2B_E\varepsilon^{-2}$. Divide these by $\beta(\xi)\varepsilon$ and $\beta(\xi)$, respectively, as in RGFREE.md (1.8)–(1.9), and use (0.1).

For the third component apply two transverse Cauchy derivatives to each local kernel, multiply by $|x_1|^2$, and use P4 (5.15)'s moment normalization. The covering-tree bounds FLUCTUATION.md Lemma 1.2 (G1),(G5) give $|x-z|\le M(d^{\rm cov}(Y)+2\sqrt dL)$ and $|Y|\le((2L+3)M)^d(1+d^{\rm cov}(Y))$. P4 (5.16)–(5.17)'s entropy sum converges when $\kappa_a-3\ge\kappa_0$, which follows from FLUCTUATION.md (IC). The Cauchy cost and these geometric factors are bounded by the displayed $K_5$, with its spare numerical factor $9$. Thus $|v_u|\le2B_EK_5\varepsilon^{-2}$, in the normalization of RGFREE.md (1.12b). Division by $\beta(\xi)$ gives the third entry of (1.3). The factor $10$ in $B_{\rm free}$ safely dominates all three displayed constants and local normalization factors. Normal convergence on the larger neighbourhood gives holomorphy; it also allows differentiation under the thermodynamic limit. Conjugation passes termwise through the derivatives and sums. $\square$

This proves the implication from FREE-LOC, not FREE-LOC itself. A further constant issue matters: Lemma 5.7's $B_6K_5$ bound on the entire fixed $c_{10}$ ball uses $C_5E_0c_{10}\le1$. When $E_0$ is fixed after $c_{10}$ and may be arbitrarily large, this need not hold. Keeping $C_5E_0c_{10}$ in $B_E$, as in (1.2), is sufficient because the last $\beta$ threshold may depend on $E_0$.

### 1.3 The exact scale factor and Lean premises

Set $\eta_{\rm free}=B_{\rm free}\widehat\beta^{-1}\varepsilon^{-2}$. Inductive (H.6), $c_{10}\le1/4$, and $\varepsilon_u\ge\alpha_0L^{-u((d-2)/2-\gamma)}$ give
$$
\widehat\beta^{-1}\varepsilon^{-2}
\le (1+c_{10})\tfrac32\alpha_0^{-2}
\beta_{\rm initial}^{-1}L^{-2\gamma u}
\le(2/\alpha_0^2)\beta_{\rm initial}^{-1}q^u .
\tag{1.4}
$$
This is P4 (5.29) in the *fixed-$\eta$* form of the Lean hypothesis hηbd. In particular, the $\beta_u^{-1}\varepsilon^{-2}$ factor was not discarded before the scale comparison.

For Balaban.Flow.rg_step_infty in Flow/RGInfty.lean take $k=u-1$, $A=\operatorname{matrixFree}(a,m,\tau,\varrho_{31},\varepsilon)$, $c=\widetilde c$, $f=\widetilde f$, $\kappa=\bar\kappa_{\rm free}$, $B=B_{\rm free}$, and $\eta=\eta_{\rm free}$:

| Lean hypothesis | Verification and status |
|---|---|
| hP, hAan | Choose an open conjugation-stable complex parameter neighbourhood. The landed matrixFree_analyticOnNhd handles the rational matrix after an analytic physical data map is supplied. The latter common neighbourhood is part of OPEN FREE-LOC. |
| hA, hε0, hε1 | RGFREE.md (1.7), (1.13) and landed triangularBounds_matrixFree give the real matrix; $0\le\varepsilon\le1$. To obtain hA on open complex $P$, shrink around the compact physical range using the strict numerical matrix slack, or define $P$ by those strict norm inequalities. |
| hκ, hc₁₀, hc, hcb | RGFREE.md (1.11)–(1.14) proves $N_3(0)=DN_3(0)=0$ and $\|c(\xi,p)\|\le\bar\kappa_{\rm free}r^2$ on every $\|\xi\|\le r\le c_{10}$, on the cited common Green disc. |
| hη, hf, hfb | $\eta_{\rm free}\ge0$, holomorphy and (1.3); physical verification is conditional on OPEN FREE-LOC. |
| hcond | Require $16\cdot42\eta_{\rm free}\max\{84\bar\kappa_{\rm free},1/c_{10}\}\le1$, a last-$\beta_{\rm initial}$ condition after all displayed constants are fixed. |
| hηbd | Equation (1.4), under inductive (H.6). |
| hσP, hAσ, hcσ, hfσ | Conjugation-stable $P$, landed matrixFree_conj, real algebraic $c$, and the conjugation clause of OPEN FREE-LOC. |

The theorem then yields $\|\xi^{(k)}\|_\infty\le168B_{\rm free}\alpha_0^{-2}\beta_{\rm initial}^{-1}q^u$, **conditional on OPEN FREE-LOC**. The abstract Lean theorem does not establish the physical local expansion.

## 2. Joint switch at $k_0$

### 2.1 Exact correction and available bounds

Use RGFREE.md (2.2) for the full switched action correction $\mathscr D(\psi,h,\xi)$, with $\Theta=(1+\varepsilon\xi_1)\psi$, $\mu=\nu_{u,u}$, $D=\phi^0(\Theta)-\phi^\mu(\Theta,h)$. FLUCTUATION.md Lemma 2.9(a), the sphere chord identity, and BG Proposition 5.1 give
$$
A_u^\star(\Theta,\phi^0)-A_u^\mu(\Theta,\phi^\mu)
=\tfrac12\langle D,(H^\mu+\alpha^\mu)D\rangle .
\tag{2.1}
$$
On the real unit-field slice, $\|D\|_*\le2K_2\mu$; $\beta_u\mu\le e^{2c_{10}}L^d$ then gives the accepted $O(\beta_u^{-1})$ scalar cost per block. On the complete complex domain, $\sqrt\mu\|\phi^\mu-h\|\lesssim\varepsilon$ only gives, subject to joint domain inclusion,
$$
\|D\|_*\le CK_2\sqrt\mu\,\varepsilon,\qquad
|\mathscr D_{\rm chord}|\le C\beta_u\mu\varepsilon^2.
\tag{2.2}
$$
The real bound cannot be used as a Cauchy majorant.

Although FLUCTUATION.md Lemma 2.9(b) displays a localized switch bound, its heading and v2 status table say only the scalar identity and real cost are proved; its proof of localization invokes the fluctuation/old-action machinery that Theorem 3.1 marks OPEN. Part (c) explicitly leaves the joint RG assertion open. Thus (b) is not an independently proved joint complex estimate.

**OPEN SWITCH-LOC.** There are fixed $t\in(0,1)$, $R_\psi\ge c\varepsilon$, $R_b\ge c\varepsilon^2$, and a complete-convention open polydisc $\mathcal U^+$ in $(\psi,b,\xi)$, with $\|\xi\|_\infty<c_{10}+tc_{10}$, such that $(\psi,b,\xi)\mapsto((1+\varepsilon\xi_1)\psi,b)$ lies in the domains of *both* backgrounds and every old term. The full correction $\mathscr D$, including the old-action differences, has a translation-covariant local expansion $\sum_YD_Y$, analytic on $\mathcal U^+$, and
$$
\sup_{z_0}\sum_{Y\ni z_0}e^{\kappa_a d^{\rm cov}(Y)}
\sup_{\mathcal U^+}|D_Y|
\le C_{\rm sw}(\beta_u\mu\varepsilon^2+E_0\sqrt\mu).
\tag{2.3}
$$
It has the P4 (5.16)–(5.17) weighted $x_1^2$ moment bound after two transverse field derivatives, uniformly in torus and $\xi$, with a common strict margin.

The $E_0\sqrt\mu$ size is a sufficient target for old terms: (2.2), Lemma 3.5(iii)'s affine composition, and a first old-term Cauchy derivative suggest $E_0\|D\|/\varepsilon_j\le CE_0\sqrt\mu$. The actual sum over $j$, rate, support enlargement, and complete joint domain remain unproved. FLUCTUATION.md Lemma 5.6 proves a domain inclusion at the *actual solution* radius $O(\beta_{\rm initial}^{-1}q^u)$; it does not establish the fixed-$c_{10}$ neighbourhood in (2.3).

**Proposition 2 (conditional on OPEN SWITCH-LOC).** On the smaller polydisc, for all $j,\ell,n\ge0$,
$$
|\partial_\psi^j\partial_b^\ell\partial_\xi^nD_Y|
\le j!\ell!n!\,\sup_{\mathcal U^+}|D_Y|
(tR_\psi)^{-j}(tR_b)^{-\ell}(tc_{10})^{-n}.
\tag{2.4}
$$
The switched forcing in the three divided RG conditions satisfies
$$
\|f_{\rm sw}(\xi,p)\|_\infty
\le C_{\rm mom}C_{\rm sw}
(\beta_u\mu\varepsilon^2+E_0\sqrt\mu)
\widehat\beta^{-1}\varepsilon^{-2},
\tag{2.5}
$$
where $C_{\rm mom}$ depends only on the Cauchy margins, $K_5$, and the entropy sum.

*Proof.* Apply multivariable Cauchy termwise on the common larger domain. The three conditions use respectively $(j,\ell)=(1,0),(0,1),(2,0)$, with $\sum_xx_1^2$ in the last; (2.3) allows interchange of sums and derivatives. The first condition divides by $\beta(\xi)\varepsilon$, the second by $\beta(\xi)$, the third by $\beta(\xi)$. Since $R_\psi\gtrsim\varepsilon$ and $R_b\gtrsim\varepsilon^2$, all are bounded by (2.5). Every $n\ge1$ is covered by the same joint Cauchy formula, including differentiation of $\Theta=(1+\varepsilon\xi_1)\psi$. $\square$

Since $\beta_u\mu\le e^{2c_{10}}L^d$, $\varepsilon\le1$, and $\sqrt\mu\le1$, set
$$
B_{\rm sw}:=C_{\rm mom}C_{\rm sw}(e^{2c_{10}}L^d+E_0),\qquad
\eta_{\rm sw}:=B_{\rm sw}\widehat\beta^{-1}\varepsilon^{-2}.
\tag{2.6}
$$
This fixed $\eta_{\rm sw}$ bounds (2.5) and, by (1.4), satisfies
$\eta_{\rm sw}\le B_{\rm sw}(2/\alpha_0^2)\beta_{\rm initial}^{-1}q^{k_0+1}$.
This is the literal scale-sensitive hηbd premise, **conditional on OPEN SWITCH-LOC**.

### 2.2 Complete-matrix theorem application

The switched term, including its linear $\xi$ dependence, goes into $f_{\rm sw}$. The counterterm matrix is the complete-convention
$$
A_{\rm sw}=\operatorname{matrixInfty}
(a,\mu,\tau,c_1(\mu),c_2(\mu),\varepsilon)
=\begin{pmatrix}a&0&0\\0&1&0\\A_{31}&A_{32}&A_{33}\end{pmatrix}.
\tag{2.7}
$$
The entries $A_{31},A_{32},A_{33}$ are explicitly RGFREE.md (2.7a), equal to the landed Balaban.Flow.matrixInfty entries. For $9/10\le a\le3/2$, $0<\mu\le7/32$, $0\le\tau\le1$, $0<c_i(\mu)<1/20$, and $0<c_1(\mu)-\mu c_2(\mu)<c_1(\mu)$, P4 p. 711 supplies the landed InftyRange fields and triangularBounds_matrixInfty proves the real TriangularBounds. Use its strict numerical slack to choose a conjugation-stable open complex neighbourhood where the inequalities continue to hold and $a+\mu\ne0$.

Take $B=B_{\rm base}+B_{\rm sw}$, $\eta=B\widehat\beta^{-1}\varepsilon^{-2}$, and $\kappa_{\rm inf}>0$ bounding the complete quadratic counterterm on every smaller $\xi$-ball. The exact Balaban.Flow.rg_step_infty premises at $k=k_0$ are:

| Lean hypothesis | Instantiation and status |
|---|---|
| hP, hAan, hA | The open complex parameter neighbourhood; rational analyticity of matrixInfty for $a+\mu\ne0$; triangularBounds_matrixInfty plus strict-slack extension. The physical analytic parameter map needs OPEN SWITCH-LOC and base I-8. |
| hε0, hε1, hκ, hc₁₀, hη | $0\le\varepsilon\le1$, $\kappa_{\rm inf}>0$, $c_{10}>0$, $\eta\ge0$. |
| hc, hcb | The standard complete counterterm $c_{\rm inf}$, analytic and $\|c_{\rm inf}(\xi,p)\|\le\kappa_{\rm inf}r^2$ for $\|\xi\|\le r\le c_{10}$, from SMALLFIELD.md §§3.3–3.4 on a common parameter/Green disc. The switched term is in $f$. |
| hf, hfb | $f=f_{\rm base}+f_{\rm sw}$, with base I-8 and OPEN SWITCH-LOC providing holomorphy and the $\eta$ bound. Theorem 3.1(g) is not a proved physical instance. |
| hcond | $16\cdot42\eta\max\{84\kappa_{\rm inf},1/c_{10}\}\le1$, imposed by the final $\beta_{\rm initial}$ choice. |
| hηbd | Equation (1.4) with $B=B_{\rm base}+B_{\rm sw}$, under inductive (H.6). |
| hσP, hAσ, hcσ, hfσ | Stable $P$; landed matrixInfty_conj; real counterterm algebra; termwise conjugation of base and switch forcing, conditional on the named OPEN localization inputs. |

If the premises hold, the landed theorem gives a unique analytic, real solution with
$\|\xi^{(k_0)}\|_\infty\le168B\alpha_0^{-2}\beta_{\rm initial}^{-1}q^{k_0+1}$.
This is a **conditional application**; the verified matrix does not prove the physical forcing premise.

## 3. Observable re-expression

RGFREE.md (2.3) gives the exact difference
$$
\mathscr D_F=\langle g,D\rangle+
\sum_{j\le k_0}
\{\mathscr F^{(j)}(J_j^0((1+\varepsilon\xi_1)\psi),h,g)
-\mathscr F^{(j)}(J_j^\mu((1+\varepsilon\xi_1)\psi,h),h,g)\}.
\tag{3.1}
$$
It depends on $\xi_1$. Theorem 3.1(h) estimates the ordinary new observable of FLUCTUATION.md (3.11), not the extra two-background difference (3.1).

For the leading $\langle g,D\rangle$, (2.2) gives $CK_2\sqrt\mu\,\varepsilon$. Let $s=(d-2)/2+\gamma-\alpha_1$ and $c_9=\beta_{\rm initial}^{-1/4}$. Using $\mu\le CL^d\beta_{\rm initial}^{-1}L^{-u(d-2)}$ and $\varepsilon_u\le C_\varepsilon\alpha_0L^{-u((d-2)/2-\gamma)}$, the ratio to the H7 allowance $c_9L^{-us}$ is bounded by
$$
C'K_2\alpha_0L^{d/2}\beta_{\rm initial}^{-1/4}
L^{-u((d-2)/2-2\gamma+\alpha_1)}.
\tag{3.2}
$$
Therefore the leading *size* fits one eighth of the allowance by a late $\beta_{\rm initial}$ choice uniformly in $u$ if $(d-2)/2-2\gamma+\alpha_1\ge0$. The FLUCTUATION.md range $0<\gamma<1/2$ alone does not imply this in $d=3$. Without this early exponent restriction, a sharper complex response bound is needed. Equation (3.2) supplies no localization rate.

**OPEN SWITCH-H7.** On a common open H7 polydisc containing $(1+\varepsilon\xi_1)\psi$, the two-background difference (3.1) has a covariant, conjugation-equivariant, analytic local expansion $\sum_{Y\ni x}M_{\rm sw}(x,Y)$ such that its leading $D$ terms and old-observable terms each consume at most one eighth of $c_9L^{-us}$ in the norm
$$
\sup_x\sum_{Y\ni x}e^{(3\kappa/2)d^{\rm cov}(Y)}
\sup_{\mathcal U^+}|M_{\rm sw}(x,Y)|.
\tag{3.3}
$$
Precisely, write $\Delta M_{j,u}(x,Y)$ for the new-scale local coefficients of the $j$th difference in (3.1), obtained by integrating its first variation along $J_j^\mu+t(J_j^0-J_j^\mu)$ and then localizing as in FLUCTUATION.md (3.11). The missing old-term bound is
$$
\sup_x\sum_{j\le k_0}\sum_{Y\ni x}
e^{(3\kappa/2)d^{\rm cov}(Y)}
\sup_{\mathcal U^+}|\Delta M_{j,u}(x,Y)|
\le\tfrac18c_9L^{-us},
\tag{3.4}
$$
with absolute convergence. The old (H.7) estimate and Cauchy give the pre-localization factor $c_9L^{-js}\|J_j^0-J_j^\mu\|/\varepsilon_j$; the required $j$-sum, support enlargement, and new-scale decay in (3.4) have not been proved.

*Conditional H7 conclusion.* Theorem 3.1(h) gives an ordinary coefficient $\tfrac12c_9+C_6\epsilon_{\rm RG}L^{u(2\gamma-\alpha_1)}$, where $\epsilon_{\rm RG}$ is the actual solution radius. By the conditional RG bound, $\epsilon_{\rm RG}\le C_\xi\beta_{\rm initial}^{-1}q^u$, so at the final $\beta$ threshold the second term is at most $\tfrac14c_9$ uniformly in $u$. If SWITCH-H7 holds, add its two one-eighth shares; the total is at most $c_9L^{-us}$ with rate at least $3\kappa/2$. Normal convergence gives analyticity and covariance. This proves the implication, **conditional on OPEN SWITCH-H7 and on the OPEN localization premises of Theorem 3.1(h)**. The scalar switch cost and rg_step_infty do not supply (3.3)–(3.4). $\square$

## 4. Constants and closure status

Fix $d,N,\gamma,\alpha_1,L$, with the extra inequality of §3 if using (3.2); then background and Green constants, $\kappa_0,K_0,\kappa,\kappa_1,M_1,M,K_1,K_2,K_5,C_4',C_5$, and Cauchy margins. Next fix $c_{10}$, $\bar\kappa_{\rm free},\kappa_{\rm inf}$, and $C_{\rm sw},C_{\rm mom}$ **if** their OPEN estimates are proved. Fix $\alpha_0$ and $E_0$ in FLUCTUATION.md §1.5's order; then (1.2) and (2.6) fix $B_{\rm free},B_{\rm sw},B$. Finally choose $\beta_{\rm initial}\ge\beta_*(\alpha_0,E_0)$ for the small mass, (H.6), hcond, localization thresholds, and (3.2). No uniform threshold over arbitrarily small $\alpha_0$ or arbitrarily large $E_0$ is asserted.

| Item | Status |
|---|---|
| Lemma 3.5 algebra, switch chord identity, real scalar cost | **Proved**, with the cited proved BG response and chord identity. |
| Cauchy/moment deduction (1.3) and scale factor (1.4) | **Proved conditional on OPEN FREE-LOC** and inductive (H.6); the scale arithmetic itself is proved. |
| Joint derivatives (2.4), forcing (2.5)–(2.6), complete-matrix theorem application | **Proved conditional on OPEN SWITCH-LOC** and base I-8. The matrix and abstract Lean theorem are proved; the physical forcing is open. |
| Leading observable size (3.2) | **Proved conditional on the cited BG response, OPEN joint domain inclusion, and explicit exponent restriction**; localized H7 is open. |
| Full switched H7 (3.3)–(3.4) | **Conditional on OPEN SWITCH-H7** and Theorem 3.1(h)'s OPEN localization inputs. |

The exact missing estimates are FREE-LOC (joint $\xi$, field and $b$ analyticity with $m$-uniform Cauchy radii and $x_1^2$-summable locality), SWITCH-LOC (fixed-$c_{10}$ joint inclusion, localized action difference, old-term scale sum, weighted moment), and SWITCH-H7 (the separate marked expansion (3.3)–(3.4)). The v2 FLUCTUATION status leaves fluctuation I-5, cover/NC, and actual termwise RG premises OPEN. No unconditional physical RG or switched H7 conclusion follows from the available statements.

**Confidence.** High for the displayed algebra, Cauchy losses, scale exponent in (1.4), and literal Lean hypothesis list. Moderate for the sufficiency of the proposed local bounds (1.1), (2.3), and (3.3), since a complete construction could require stronger margins or decay. No confidence claim is made that the three OPEN assertions follow from the present source package.

**Sources.** P4, *A low temperature expansion for classical N-vector models. II*, printed pp. 710–714, (5.15)–(5.17), (5.21), (5.24)–(5.29); its scanned formulas were checked against PDF images in the preceding RGFREE.md work. P6, *Renormalization and localization expansions. II*, printed p. 11, (2.22)–(2.24) and the two-stage switch paragraph. Local notes: FLUCTUATION.md v2 §§2.8, 3.1, 3.6, 5.2; SMALLFIELD.md §§2.3, 3.4–3.7; RGFREE.md §§1.3–2.3. Landed read-only Lean declarations inspected: Balaban.Flow.matrixInfty, triangularBounds_matrixInfty, matrixInfty_conj, matrixFree_analyticOnNhd, matrixFree_conj, and rg_step_infty. No Lean source was changed or built.
