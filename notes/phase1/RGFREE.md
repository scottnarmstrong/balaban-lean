# The mass-free RG equations and the switch at $k_0$

“Mass-free” here describes the background equation. The term $m|\phi-h|^2/2$ remains in the action and the fluctuation integral. We use the free flow $c=ab$, so $a=a_{k+1}=a_{k+1,u}$. Set $\epsilon=\varepsilon_{k+1}$, $\beta=\beta_{k+1}$, $\beta_u=\beta(1+\xi_3)$, $z=1+\epsilon\xi_1$, and

$$m=m(\xi)=m_u\frac{1+\xi_3}{1+\xi_2},\qquad m_u=\nu_kL^2,\qquad \xi_2=e/\beta,\quad\xi_3=b/\beta.$$

The data $a,m_u$ are frozen before solving the step. Since $\beta=\beta_u/(1+\xi_3)$ varies with $\xi$, use the fixed disc bound $\widehat\beta^{-1}:=(1+c_{10})\beta_u^{-1}$ whenever a theorem premise requires one constant; on $\|\xi\|_\infty\le c_{10}$, $|\beta(\xi)^{-1}|\le\widehat\beta^{-1}$. The matrix below is the explicit linear part of the *counterterm*. It is not the derivative of the whole RG equation: the fluctuation data depend on $\xi$, as P4 states after (5.33). The physical conclusions of this note are limited by the open localization inputs identified below.

## 1. The mass-free divided equations

### 1.1 Transverse quadratic form

Let $Q$ be the scale-$(k+1)$ block average; scalar products on complex fields are bilinear. At constant incoming field $ze_1$, the mass-free minimizer is $e_1$ and its multiplier is $a(z-1)$. For $\psi=e_1+\vartheta e_2$, linearizing the Euler–Lagrange equation gives

$$\phi^{(1)}=azG_zQ^*\vartheta\,e_2,\qquad G_z=(-\Delta+aQ^*Q+a(z-1))^{-1}.$$

The sphere constraint gives $e_1\cdot\phi^{(2)}=-|\phi^{(1)}|^2/2$. Substitution into the minimized mass-free action and the explicit mass energy gives the quadratic kernels

$$K_z=I-aQG_zQ^*,\qquad B_z=a^2z^2QG_z^2Q^*,\qquad
\frac12az^2\langle\vartheta,K_z\vartheta\rangle+\frac12m\langle\vartheta,B_z\vartheta\rangle.$$

The mass term contributes $mB_z$ although the background equation has no mass. Retaining $a(z-1)$ in $G_z^{-1}$ is essential. P4's complete-background calculation instead uses $(-\Delta+aQ^*Q+m)^{-1}$; see P4 (5.7)–(5.14), images of printed pp. 709–711.

P4 (5.14), (5.21) uses the moment functional $\mathcal V(T)=\frac14\partial_{p_1}^2\widehat T(0)$ for these quadratic kernels. Define

$$q(z)=\frac a4\partial_{p_1}^2\widehat{z^2K_z}(0),\qquad
r(z)=\frac14\partial_{p_1}^2\widehat B_z(0). \tag{1.1}$$

The exact third counterterm moment is

$$T_3(\xi)=(1+\xi_3)q(z)-q(1)+m(\xi)\bigl[(1+\xi_2)r(z)-r(1)\bigr]. \tag{1.2}$$

This compares the minimized actions at $z\psi$ and $\psi$ and also their explicit mass energies. Hence (1.2) includes the $C_3$ term of FLUCTUATION Lemma 3.5; that term must not be added again.

### 1.2 Evaluation of $\varrho_{31}$

The formulas in this paragraph were checked against the **PDF image** of P4 p. 711, (5.12)–(5.13). Put $v=a(z-1)$; let $f_v=(1+ag_v)^{-1}$ and $h_v$ be P4's Fourier functions. Then $\widehat K_z=f_v$ and $\widehat B_z=a^2z^2f_v^2h_v$. With $\tau=1-L^{-2m_{\rm block}}\in[0,1]$ and P4's lattice sums $c_1(v),c_2(v)$, the printed $p_1$ derivatives at zero are

$$f_v(0)=\frac v{a+v},\quad f_v''(0)=\frac{2a}{(a+v)^2}
\left(1+\frac{v\tau}{12}-v^2c_1(v)\right),\quad h_v(0)=v^{-2},$$

$$h_v''(0)=-\frac2{v^3}\left(2+\frac{v\tau}{12}-v^3c_2(v)\right). \tag{1.3}$$

First $p_1$ derivatives vanish. The product rule therefore yields

$$\left(f_v^2h_v\right)''(0)=
-\frac{2}{v(a+v)^2}\left(2+\frac{v\tau}{12}-v^3c_2(v)\right)
+\frac{4a}{v(a+v)^3}\left(1+\frac{v\tau}{12}-v^2c_1(v)\right). \tag{1.4}$$

The apparent pole cancels. Expanding the rational factors, using continuity of the lattice sums at zero, gives

$$\left(f_v^2h_v\right)''(0)=
-\frac4{a^3}+\frac{\tau}{6a^2}
+v\left(\frac{12}{a^4}-\frac{2\tau}{3a^3}-\frac{4c_1(0)}{a^2}\right)+O(v^2). \tag{1.5}$$

Insert $v=a(z-1)$, differentiate the factor $z^2$, and use (1.1). This proves

$$q(1)=\frac12,\qquad q'(1)=\frac{a\tau}{24},\qquad
r(1)=-\frac1a+\frac\tau{24},\qquad
r'(1)=\frac1a-\frac\tau{12}-a c_1(0). \tag{1.6}$$

Consequently the coefficient left uncomputed in SMALLFIELD §3.7 is

$$\boxed{\varrho_{31}(a,\tau)=a^{-1}-\tau/12-a c_1(0).} \tag{1.7}$$

It is independent of the running mass. The calculation uses the P4 moment convention but no limit of P4's complete-background equation. Two checks fix its normalization: at $m=0$ the matrix below agrees with P4 (5.21) at $v=0$; and the $b$ coefficient is $q(1)=1/2$, exactly the printed $a_{33}$.

A further check is available without identifying the two conventions: differentiating P4 (5.21)'s *complete* $a_{31}/\epsilon$ at $v=0$ gives $1/a-\tau/12-a c_1(0)$; its $a_{32}$ has first-order term $(v/a)(-1+a\tau/24)$ and its $a_{33}$ has zero first derivative. Thus (1.10) agrees with the complete matrix through first order in the mass. This is a check of the algebra, not a substitution of one convention for the other.

### 1.3 All three divided equations

Let $F_u(\xi;\psi,h)$ be the unrenormalized new effective action from the fluctuation integral and old-action re-expression. Denote its constant-field potential by $f_u(\xi;u,b)$, $b=mh$, and its transverse second moment in P4 (5.15) by $v_u(\xi)$. The density normalization in P4 (4.13) matters: the field-only factor $\nu e(|h|^2-1)/2$ is outside the counterterm. P4 (4.14) consequently has a term linear in $h$ whose $e_1$ derivative is $-e$. Dropping that factor and retaining only $\nu\xi_2|\phi-h|^2/2$ would incorrectly make the $e$ coefficient zero. At constant longitudinal fields both mass-free minimizers equal $e_1$, so the first two conditions divide exactly to

$$a\xi_1+a\xi_1\xi_3+a\epsilon(1+\xi_3)\xi_1^2
=\frac1{\beta\epsilon}\partial_u f_u(\xi;1,me_1), \tag{1.8}$$

$$\xi_2=-\beta^{-1}\partial_b f_u(\xi;e_1,me_1)\cdot e_1. \tag{1.9}$$

The derivative in $b$ is taken at fixed $m>0$. A continuous $m\downarrow0$ family requires a separate premise. Put $m_0=m_u$ and define the frozen matrix

$$A_{\rm free}=
\begin{pmatrix}
a&0&0\\
0&1&0\\
\epsilon\bigl(a\tau/24+m_0\varrho_{31}\bigr)&
(m_0/a)(-1+a\tau/24)&1/2
\end{pmatrix}. \tag{1.10}$$

Define the entire nonlinear third component by exact subtraction:

$$N_3(\xi)=T_3(\xi)
-\epsilon\bigl(q'(1)+m_0r'(1)\bigr)\xi_1
-m_0r(1)\xi_2-\tfrac12\xi_3. \tag{1.11}$$

Then the actual divided equations, with every component specified, are $A_{\rm free}\xi+\widetilde c(\xi)=\widetilde f(\xi)$, where

$$\widetilde c(\xi)=
\begin{pmatrix}
a\xi_1\xi_3+a\epsilon(1+\xi_3)\xi_1^2\\0\\N_3(\xi)
\end{pmatrix},\qquad
\widetilde f(\xi)=
\begin{pmatrix}
(\beta\epsilon)^{-1}\partial_u f_u\\
-\beta^{-1}\partial_b f_u\cdot e_1\\
\beta^{-1}v_u(\xi)
\end{pmatrix}. \tag{1.12}$$

The first two arguments are those in (1.8)–(1.9). The sign of the third entry follows from $v_u-\beta T_3=0$. Formula (1.11) retains every $\xi$ power, including those from $m(\xi)$, and (1.6) gives $N_3(0)=DN_3(0)=0$. Thus it is an explicit analytic specification of the formerly missing $\widetilde c_3$; $\widetilde f_3$ is the *mass-free* fluctuation moment, not the complete-background one.

Equivalently, with $t=\epsilon\xi_1$, $R_q=q(1+t)-q(1)-q'(1)t$ and $R_r=r(1+t)-r(1)-r'(1)t$, direct expansion of (1.11) gives

$$N_3=\xi_3q'(1)t+(1+\xi_3)R_q+
[m(\xi)-m_0]\,[r(1)\xi_2+r'(1)t]
+m(\xi)\xi_2r'(1)t+m(\xi)(1+\xi_2)R_r. \tag{1.11a}$$

Each displayed summand has order at least two in $\xi$; this identity proves the quadratic vanishing without assigning any part of the $m(\xi)$ dependence to the matrix.

For clarity, $\widetilde f_3$ can be written without the shorthand $v_u$. Let $\mathscr E^{(k+1)}_0$ be exactly the mass-free fluctuation integral of FLUCTUATION §2.3 item 5, namely its determinant term plus its integral in $s$ against $d\mu_{s,0}$. Let

$$\mathscr U_{\rm free}(\xi;\psi,h)=
\mathscr E^{(k+1)}_0(z\psi,h)
+\sum_{j\le k}\left[
\mathscr E^{(j)}(J_j^u(\xi;z\psi),h)
-\mathscr E^{(j)}(J_j^r(\xi;\psi),h)
\right], \tag{1.12a}$$

where $J_j^u,J_j^r$ are respectively the unrenormalized and renormalized mass-free compositions of FLUCTUATION (3.10), including their distinct backgrounds. With the torus-independent thermodynamic limit of P4 (5.15),

$$\widetilde f_3(\xi)=
-\frac1{2\beta}\sum_{x\in\mathbb Z^d}x_1^2
\left.\frac{\partial^2\mathscr U_{\rm free}(\xi;\psi,h)}
{\partial\psi_2(x)\,\partial\psi_2(0)}\right|_{\psi=h=e_1}. \tag{1.12b}$$

This is an exact integral-and-old-terms formula, not a numerical constant. It includes the $\xi$ dependence of the covariance, the fluctuation measure, the compositions, and $\beta^{-1}$. P4 (5.15) has precisely this second-moment normalization. Absolute convergence and the bound for (1.12b) are the unresolved FREE-B1 assertion below.

**Normalization caveat.** FLUCTUATION Lemma 3.5 displays $\nu|\phi-h|^2/2$ but omits P4 (4.13)'s separate field-only factor. Equations (1.8)–(1.12) use P4's density normalization. Any other normalization requires a fresh derivation of (1.9).

### 1.4 Bounds and Lean interface

P4 p. 711 proves $0<c_1(0)<1/20$. If $9/10\le a\le3/2$, $0\le\tau\le1$, and $0\le m_0\le7/32$, then

$$|\varrho_{31}|\le\frac{10}{9}+\frac1{12}+\frac3{40}
=\frac{457}{360}<\frac43,\qquad m_0\frac43\le\frac7{24}<\frac{12}{5}. \tag{1.13}$$

These verify the exact eight range premises of the landed Balaban.Flow.triangularBounds_matrixFree with $r=\varrho_{31}$ and $C=4/3$; $0\le\epsilon$ supplies its final premise. Its conclusion is TriangularBounds for the complexification of Balaban.Flow.matrixFree applied to (1.10). This verifies the *counterterm matrix*, not the physical fluctuation data.

For a quantitative quadratic bound, choose a complex radius $d_z>0$ on which $q,r$ are analytic and set $M_q=\sup_{|z-1|\le d_z}|q(z)|$, $M_r=\sup_{|z-1|\le d_z}|r(z)|$. Choose $c_{10}\le1/4$ and $\epsilon c_{10}\le d_z/2$. For $s=\|\xi\|_\infty\le c_{10}$, Cauchy's series estimate bounds each Taylor remainder by $2M|z-1|^2/d_z^2$. Together with $|m(\xi)|\le5m_0/3$ and $|m(\xi)-m_0|\le8m_0s/3$, it gives

$$|N_3(\xi)|\le\kappa_3s^2,\quad
\kappa_3=\frac{5M_q\epsilon^2}{2d_z^2}+|q'(1)|\epsilon
+\frac{8m_0}{3}\bigl(|r(1)|+|r'(1)|\epsilon\bigr)
+\frac{5m_0}{3}|r'(1)|\epsilon
+\frac{25m_0M_r\epsilon^2}{6d_z^2}. \tag{1.14}$$

Hence $\|\widetilde c(\xi)\|_\infty\le\kappa_{\rm free}s^2$ with $\kappa_{\rm free}=\max\{a[1+\epsilon(1+c_{10})],\kappa_3\}$. For the order of constants below, replace this by any fixed upper bound $\bar\kappa_{\rm free}$ obtained in (1.14) using $\epsilon\le1$ and $m_0\le7/32$. A common $d_z,M_q,M_r$ over the allowed $a$ interval follows from the uniform gap in GREEN G-1/G-4; this is a **proved cited input**, not a statement of the Lean matrix theorem.

The needed bound on $\widetilde f$ is separate. P4 (5.3), (5.15)–(5.17), (5.25) proves a complete-background version, with $K_5=9K_0(16dK_1LM)^2((2L+3)M)^d$ as in FLUCTUATION §1.5. The exact mass-free input still required is:

> **OPEN FREE-B1.** The mass-free fluctuation integral and old-action re-expression are jointly analytic in $\xi$ on $\|\xi\|_\infty<c_{10}$, uniformly on the admissible parameter set $P$, and the three functions in (1.12) satisfy $\|\widetilde f(\xi,p)\|_\infty\le B_{\rm free}\widehat\beta^{-1}\epsilon^{-2}$ there, with $B_{\rm free}$ fixed before the final $\beta$. They have the required conjugation symmetry. Family continuity in $m\downarrow0$, if asserted, is also part of the family data.

The elementary Cauchy losses are $\epsilon^{-1}$ per constant-field derivative and $\epsilon^{-2}$ for the second moment, followed by the geometric factor $K_5$. They do not prove the required local expansion. FLUCTUATION Theorem 3.1(g) proposes it, but FL-A01 and FL-A02 of the cited audit leave its termwise locality and modular localization open. P4 Proposition 4.1 treats complete backgrounds. FREE-B1 is therefore **open**.

For the literal Balaban.Flow.rg_step_infty, take a complex Banach parameter space $G$ and open $P\subset G$, set $A(p)$ to (1.10), $c=\widetilde c$, $f=\widetilde f$, $\kappa=\bar\kappa_{\rm free}$, and the fixed $\eta=B_{\rm free}\widehat\beta^{-1}\epsilon^{-2}$. Its premises are accounted for as follows.

| Lean premise | Instantiation and status |
|---|---|
| hP, hAan | $P$ open by definition; matrix entries analytic because $a\ne0$ and (1.7) is rational in $a$. The analytic data map must be supplied. Balaban.Flow.matrixFree_analyticOnNhd gives entrywise analyticity after that map. |
| hA, hε0, hε1 | (1.13) and triangularBounds_matrixFree; choose $0\le\epsilon\le1$. Proved for the explicit matrix. |
| hκ, hc₁₀, hc, hcb | Take positive $\bar\kappa_{\rm free},c_{10}$; (1.11), (1.14) prove the analytic quadratic bound on every smaller ball, given the cited uniform Green disc. |
| hη, hf, hfb | Take the above $\eta$ and $f$; **conditional on OPEN FREE-B1**. |
| hcond | Require $16\cdot42\eta\max\{84\bar\kappa_{\rm free},1/c_{10}\}\le1$; a late $\beta$ threshold, **conditional on FREE-B1**. |
| hηbd | The uniform form of P4 (5.29) gives $\widehat\beta^{-1}\epsilon^{-2}\le(2/\alpha_0^2)\beta_{\rm initial}^{-1}q^{k+1}$, $q=L^{-2\gamma}$, from (H.6). Explicitly, its running-coefficient estimate $\beta_k^{-1}\le(3/2)\beta_{\rm initial}^{-1}L^{-k(d-2)}$ and $c_{10}\le1/4$ give $(1+c_{10})(3/2)<2$. Use $B=B_{\rm free}$. |
| hσP, hAσ, hcσ, hfσ | Conjugation stability of $P$, matrixFree_conj, the real coefficients in (1.11), and the conjugation clause of **OPEN FREE-B1**, respectively. |

Conditional on FREE-B1 and (H.6), rg_step_infty gives existence, uniqueness, analyticity, and $\|\xi^0\|\le168B_{\rm free}\alpha_0^{-2}\beta_{\rm initial}^{-1}q^{k+1}$. The theorem itself does not establish FREE-B1 or identify the physical counterterm. Choose constants in this order: $d,N,\gamma,\alpha_1,L$; background and Green constants; $\kappa_0,K_0,\kappa,\kappa_1,M_1,M,K_5$; $d_z,M_q,M_r,c_{10},\bar\kappa_{\rm free},B_{\rm free}$; $\alpha_0,E_0$; and finally $\beta$ for $m_u\le7/32$, $\epsilon\le1$, (H.6), hcond and localization thresholds. For example, if (H.6) gives $\beta_k\ge\beta_{\rm initial}/2$ and $\beta_k\nu_k\le e^{2c_{10}}$ before the switch, then $\beta_{\rm initial}\ge(64/7)e^{2c_{10}}L^2$ ensures $m_u\le7/32$. There is no finite $\beta_*$ uniform over arbitrarily small $\alpha_0$ or unbounded $E_0$ (audit FL-A10).

## 2. The step $k_0\longrightarrow k_0+1$

### 2.1 Exact switch and its dependence on $\xi$

Put $\mu=\nu_{k+1,u}$, $\Theta=(1+\epsilon\xi_1)\psi$. Let $\phi^0(\Theta)$ and $\phi^\mu(\Theta,h)$ be the mass-free and complete backgrounds for the **same** unrenormalized parameters. The chord identity, FLUCTUATION Lemma 2.9(a) and P6 (2.22)–(2.24), gives

$$A^\star_u(\Theta,\phi^0)-A^\mu_u(\Theta,\phi^\mu)
=\frac12\langle D,(H^\mu+\alpha^\mu)D\rangle,\qquad D=\phi^0-\phi^\mu. \tag{2.1}$$

Subtracting the Euler–Lagrange systems gives BG Proposition 5.1 with source $\mu(\phi^\mu-h)$ and hence $\|D\|_*\le K_2\mu\|\phi^\mu-h\|$ on its joint analytic domain. On real unit-field data, $\|\phi^\mu-h\|\le2$. Since $\beta_u\mu\le e^{2c_{10}}L^d$, the block cost is bounded by $C K_2^2L^{2d}\beta_u^{-1}$. This is the accepted real scalar estimate, **proved conditional on the cited BG response and chord identity**.

The switched density must be expanded as a function of both $\psi$ and $\xi$. Let $J_j^0(\Theta)$ and $J_j^\mu(\Theta,h)$ be the composed scale-$j$ fields. Before complete-convention renormalization its correction is

$$\mathscr D(\psi,h,\xi)=
-\frac{\beta_u}{2}\langle D,(H^\mu+\alpha^\mu)D\rangle
+\sum_{j\le k_0}\{\mathscr E^{(j)}(J_j^0(\Theta),h)
-\mathscr E^{(j)}(J_j^\mu(\Theta,h),h)\}. \tag{2.2}$$

The corresponding observable correction, with the sign chosen for the replacement $\phi^0\mapsto\phi^\mu$, is

$$\mathscr D_F(\psi,h,g,\xi)=
\langle g,D\rangle+
\sum_{j\le k_0}\{\mathscr F^{(j)}(J_j^0(\Theta),h,g)
-\mathscr F^{(j)}(J_j^\mu(\Theta,h),h,g)\}. \tag{2.3}$$

Reversing which side of the density identity contains (2.3) reverses its overall sign without changing its estimates. Equations (2.2)–(2.3) show that both corrections depend on $\xi_1$ through $\Theta$. Thus the assertion in FLUCTUATION Lemma 2.9(c) that the added terms do not depend on $\xi$ is false. Their $\xi$ derivatives may enter the three RG conditions and must be bounded.

### 2.2 Joint complex estimates and the precise missing input

Let $\mathcal U^+$ be a complete-convention complex polydisc with strict margins in $(\psi,b,\xi)$, $\xi$ radius $c_{10}$, field radius $R_\psi\asymp\epsilon$, and $b$ radius $R_b\asymp\epsilon^2$ in P4 p. 707's effective-potential coordinates. On the complete $\Xi^c$ domain, $\sqrt\mu\,\|\phi^\mu-h\|\lesssim\epsilon$. Therefore BG Proposition 5.1 and (2.1) imply, wherever the joint domain inclusion for $\Theta$ is valid,

$$\|D\|_*\le C K_2\sqrt\mu\,\epsilon,\qquad
|\mathscr D_{\rm main}|\le C\beta_u\mu\epsilon^2. \tag{2.4}$$

These are **complex-domain** bounds. The real $O(\beta_u^{-1})$ estimate is stronger on the real slice but cannot be substituted into Cauchy's formula. If a localized summand $D_Y$ is jointly analytic on $\mathcal U^+$ and bounded there by $M_Y$, the multivariable Cauchy formula on a smaller polydisc with margin fraction $t\in(0,1)$ gives

$$|\partial_\psi^j\partial_b^\ell\partial_\xi^nD_Y|
\le j!\ell!n!\,M_Y(tR_\psi)^{-j}(tR_b)^{-\ell}(tc_{10})^{-n}. \tag{2.5}$$

The three RG conditions use the constant-field $j=1$ derivative, the $\ell=1$ derivative, and the transverse $j=2$ derivative followed by P4 (5.15)'s $|x_1|^2$ moment sum. Taking $n\ge1$ in (2.5) controls all their $\xi$ derivatives, including those missed in Lemma 2.9(c). The moment sum pays P4 (5.16)–(5.17)'s geometry factor $K_5$ **if** the $D_Y$ have the required localized decay.

What (2.4) does not establish is a bound $M_Y$ for **every** term of (2.2), uniform in the torus, on a common joint domain. The old-action difference needs margins for each interpolation between $J_j^0$ and $J_j^\mu$ and a genuinely local first-variation estimate. FLUCTUATION Lemma 3.2 does not provide that estimate: the audit's FL-A01 exhibits a termwise counterterm that reads a site outside its stated support. The modular localization needed in the large-field version remains open by FL-A02. We isolate the missing assertion:

> **OPEN SW-JOINT.** Formula (2.2) has a termwise local expansion $\sum_Y D_Y$, analytic jointly on $\mathcal U^+$ with a common strict margin, such that per unit block $\sum_Y e^{\kappa d(Y)}\sup_{\mathcal U^+}|D_Y|\le C_{\rm sw}[\beta_u\mu\epsilon^2+E_0\sqrt\mu]$. The derivative and moment sums obtained from (2.5) hold on the smaller complete-convention polydisc. All support enlargement and covering or modular losses are included in $\kappa,C_{\rm sw}$.

The proposed $E_0\sqrt\mu$ term is a sufficient target for the old-action re-expression: $D=O(\sqrt\mu\,\epsilon)$ by BG, P2 (6.2)'s composition is affine in $D$, Cauchy differentiation of an old term costs $\epsilon_j^{-1}$, and $\epsilon/\epsilon_j\le1$ for $j\le k_0$. This does **not** prove the scale and support sums in SW-JOINT. They are the substantive open step.

Assuming SW-JOINT, (2.5) and the moment sum give a finite constant $C_{\rm mom}$, chosen after the Cauchy margins and $K_5$. Set

$$B_{\rm sw}=C_{\rm mom}C_{\rm sw}
\bigl(\beta_u\mu\epsilon^2+E_0\sqrt\mu\bigr),\qquad
\eta_{\rm sw}=B_{\rm sw}\widehat\beta^{-1}\epsilon^{-2}. \tag{2.6}$$

Because $\beta_u\mu\le e^{2c_{10}}L^d$, $\epsilon\le1$, and $\sqrt\mu\le1$, $B_{\rm sw}$ has a bound fixed before the final $\beta$. Most importantly, (2.6) **retains** the uniform version of $\beta_{k+1}^{-1}\epsilon^{-2}$. P4 (5.29), verified uniformly on the disc, then gives $\eta_{\rm sw}\le B_{\rm sw}(2/\alpha_0^2)\beta_{\rm initial}^{-1}q^{k_0+1}$. This is the scale factor in the literal hηbd premise of rg_step_infty. The estimate is **conditional on OPEN SW-JOINT**. The real scalar bound alone does not prove it.

### 2.3 Complete matrix, theorem application and observable

Under SW-JOINT, put **all** of the switched correction, with its $\xi$ dependence, in the analytic datum $f$. The explicit counterterm matrix remains

$$A_{\rm inf}=\operatorname{matrixInfty}(a,m_u,\tau,c_1(m_u),c_2(m_u),\epsilon). \tag{2.7}$$

Explicitly, $A_{\rm inf}$ has rows $(a,0,0)$, $(0,1,0)$, $(A_{31},A_{32},A_{33})$. Writing $v=m_u$ and $C_i=c_i(v)$, its entries, exactly P4 (5.21) at $\lambda=\infty$, are

$$A_{31}=\epsilon\frac{a^2}{(a+v)^2}
\left(1+\frac{v\tau}{12}-v^2C_1\right)
+\epsilon\frac{a^3}{(a+v)^3}
\left(-1+\frac{a-v}{24}\tau-avC_1+\frac12(a+v)v^2C_2\right),$$

$$A_{32}=\frac{a^2v}{(a+v)^3}
\left(-1+\frac{a-v}{24}\tau-avC_1+\frac12(a+v)v^2C_2\right),$$

$$A_{33}=\frac12\frac{a^2}{(a+v)^2}(1+v^2C_1-v^3C_2)
+\frac{a^2v}{(a+v)^3}\left(1+\frac{v\tau}{12}-v^2C_1\right). \tag{2.7a}$$

This is a splitting of $A\xi+c=f$, not a claim that the switched datum has zero derivative. For $m_u>0$, $m_u\le7/32$, $9/10\le a\le3/2$, and $0\le\tau\le1$, P4 p. 711 supplies $0<c_i(m_u)<1/20$ and $0<c_1-m_uc_2<c_1$. These are the fields of the landed Balaban.Flow.InftyRange; triangularBounds_matrixInfty gives hA. The rational entries of matrixInfty are analytic on $a+m_u\ne0$, providing hAan after the parameter map is shown analytic; matrixInfty_conj gives hAσ. The other premises of rg_step_infty are the ones listed in §1.4, now with the complete quadratic constant $\kappa_{\rm inf}$ and

$$B=B_{\rm base}+B_{\rm sw},\quad
\eta=B\widehat\beta^{-1}\epsilon^{-2},\quad
16\cdot42\eta\max\{84\kappa_{\rm inf},1/c_{10}\}\le1. \tag{2.8}$$

The base analytic $f$ bound, the switched $f$ bound, joint analyticity, reality and conjugation symmetry are **conditional** on the corresponding I-8 localization input and OPEN SW-JOINT. The hηbd premise is (2.6) plus P4 (5.29). The last inequality in (2.8) is imposed by increasing the initial $\beta$ **after** $B,\kappa_{\rm inf},c_{10},\alpha_0,E_0$ are fixed. This is an exact *conditional* use of the landed theorem; it does not establish (H.5) for the physical switched density without those analytic inputs.

The observable (2.3) requires its **own** H7 estimate on the complex domain. BG directly gives only $C K_2\sqrt\mu\,\epsilon$ for its leading term. The new-scale H7 allowance is $c_9L^{-(k_0+1)s}$, where $c_9=\beta_{\rm initial}^{-1/4}$ and $s=(d-2)/2+\gamma-\alpha_1$. Since $\mu\le C L^d\beta_{\rm initial}^{-1}L^{-(k_0+1)(d-2)}$, a sufficient inequality for that leading term to use one quarter of the allowance is

$$C K_2\alpha_0 L^{d/2}\beta_{\rm initial}^{-1/4}
L^{-(k_0+1)((d-2)/2-2\gamma+\alpha_1)}
\le\tfrac14. \tag{2.9}$$

For arbitrarily large $k_0$, a late $\beta$ choice establishes (2.9) if $(d-2)/2-2\gamma+\alpha_1\ge0$; the simple early choice $0<\gamma<\min\{1/2,(d-2)/4\}$ suffices. Without such a restriction, a sharper complex response bound is needed. The remaining old-observable differences in (2.3) require the following separate assertion:

> **OPEN SW-H7.** On the same H7 complex domain, (2.3) has an analytic localized expansion with rate at least $3\kappa/2$ and total new-scale coefficient at most $c_9L^{-(k_0+1)s}$, allowing at most one quarter for its leading BG term. This includes every old-observable first variation, composition margin, support enlargement and scale sum.

Neither P6's two-stage suggestion on printed p. 11 nor FLUCTUATION Lemma 2.9's real scalar estimate proves SW-H7.

## 3. Status, open items and source record

| Claim | Status |
|---|---|
| The mass-free transverse form, (1.6), $\varrho_{31}$, and $\widetilde f_3,\widetilde c_3$ in (1.11)–(1.12) | **Proved algebraically** from the displayed background equation, P4's printed Fourier identities and moment convention. Confidence high in the algebra; moderate in transport of P4's normalization to this mass-free density. |
| (1.13) and triangularBounds_matrixFree for the displayed matrix | **Proved**, conditional on P4's proved lattice-sum bounds and the stated parameter range. Confidence high. |
| (1.14) | **Proved conditional on the proved cited Green gap** for a common holomorphic disc. Confidence high. |
| Actual mass-free rg_step_infty instance | **Conditional on OPEN FREE-B1** and inductive (H.6). No unconditional physical RG step is claimed. |
| Scalar switch identity and real $O(\beta_u^{-1})$ block cost | **Proved conditional on the cited BG Proposition 5.1 and chord identity**. Confidence high. |
| Joint switch derivative and scale bounds (2.5)–(2.6), complete-matrix step (2.7)–(2.8) | The Cauchy and theorem calculations are **proved conditional on OPEN SW-JOINT**; the physical step remains **open**. Confidence high in the dependency and scaling, moderate in the proposed sufficient local bound. |
| Observable re-expression on H7 | **OPEN SW-H7**; (2.9) is sufficient for its leading BG term under the stated exponent choice. Confidence moderate. |

The remaining source-level work is precise: repair termwise support in FLUCTUATION Lemma 3.2 (audit FL-A01); prove the required modular localization and margins (FL-A02); establish FREE-B1, including its $b$ derivative; prove SW-JOINT on the complete complex domain with $\Theta=z\psi$; and prove SW-H7 for all old-observable terms. Family continuity at $m\downarrow0$ needs a common-family (CONT) premise (FL-A09). These are open assertions, not consequences of the landed Lean matrix or step theorems.

**Sources and frozen inputs.** P4: T. Balaban, *A low temperature expansion for classical N-vector models. II. Renormalization group equations*, Commun. Math. Phys. **182** (1996), 675–721; in particular printed pp. 702–703, 707–708, 710–714, 717–718, (4.13)–(4.14), (5.11)–(5.17), (5.21), (5.29), (5.39)–(5.41). The decisive formulas were checked on PDF images, rather than P4 OCR. P5: Balaban, *A low temperature expansion for classical N-vector models. III*, Commun. Math. Phys. **196** (1998), (1.9). P6: Balaban, *Renormalization and localization expansions. II*, Commun. Math. Phys. **198** (1998), printed p. 11, (2.22)–(2.24) and its two-stage switch paragraph. SMALLFIELD.md SHA-256 ab12f8746dec9b3de784aa3a28a4e4aad477c32191656ad1133f3952654f5fce; FLUCTUATION.md SHA-256 860d4b39e44d96a21d26d9dad4ef008bfd6ac9281b18537f5b2565b19763fb2a; audit FLUCT-AUDIT-astra.md. Landed Lean sources inspected: MatrixFree.lean SHA-256 3ecce7ed0e41da02a47e605d97824b12af1ff2be6a6d4781802d8da5a9706f93; MatrixInfty.lean SHA-256 a3554f15ad4ec960f76a1cc69d9efe3a318f05fed17c86ff1a32a2eca5dd837d; RGInfty.lean SHA-256 50d055254c0c28a6fc22813f23aca1cde75929d485c993493fcec6d0d8ef5bc2. No Lean build was run; no declaration is claimed to identify the physical mass-free fluctuation data.
