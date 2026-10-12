# A source-adapted repair of the mass-free class and switch

This note answers [followup3.txt](followup3.txt). The counterexamples in [RGFREE-3.md](RGFREE-3.md) are accepted inputs: a full complex transverse $b$ disc of radius $c\varepsilon_u^2$ cannot carry the proposed switch H4 or H7 bounds. The repair below replaces that disc by a source-adapted tube and uses the three *reference slices* actually needed by the renormalization conditions. It specifies changes to the draft Lean Def-6 and to FLUCTUATION.md, without editing either read-only source. Statements labelled **proved** are proved here or follow from the named proved algebraic result. Statements labelled **conditional on OPEN** name the physical localization or domain input still missing.

Write $m>0$ for the physical mass in unit-scale variables, $\mu_{\rm bg}\in\{0,m\}$ for the background mass, $\varepsilon=\varepsilon_u$, $\beta_u=\beta_kL^{d-2}$, and $b=mh$. At level $j$, the same symbols mean $m_j=\nu_kL^{-2(k-j)}$ and $b_j=m_jh$; at the switch output $m=m_u$. Assume the switch range $\beta_um\le C_L$, $m\le1$, and the late relation $m/\varepsilon^2\le c_*$. All complex scalar products are bilinear; all absolute-value bounds use the Hermitian norm. Put $s=(d-2)/2+\gamma-\alpha_1$, $c_9=\beta_{\rm initial}^{-1/4}$, and $q=L^{-2\gamma}$.

## 1. Repaired mass-free factorization and domain

### 1.1 Exact factorization

**Proposition 1 (proved).** For a sphere field $\phi^0$ solving the background equation with $\mu_{\rm bg}=0$, the correct physical main action is
$$
A_m^\star(\psi,h)=A_0(\psi,\phi^0)
  \frac m2\sum_x(\phi^0(x)-h(x))\cdot(\phi^0(x)-h(x)).
\tag{1.1}
$$
The physical mass is $m$ in this action, even though the background solver, composed backgrounds and covariance use zero mass. For any other sphere field $\phi=\phi^0+w$, set
$$
v_x=\phi^0(x)\cdot b(x),\qquad
t_x=b(x)-v_x\phi^0(x),\qquad \phi^0(x)\cdot t_x=0.
\tag{1.2}
$$
Then the mass variation is exactly
$$
\frac m2\bigl[(\phi-h)^2-(\phi^0-h)^2\bigr]
=-t_x\cdot w+\frac{v_x}{2}\,w\cdot w
\quad\text{at each }x.
\tag{1.3}
$$

*Proof.* Equation (1.1) is the landed actionC_mass_split of Balaban/Fluctuation/ExpansionNuFree.lean applied at $\phi^0$. Since both fields lie on the complex bilinear sphere, $(\phi^0+w)^2=(\phi^0)^2=1$ gives $\phi^0\cdot w=-w^2/2$. The difference of mass energies is $-b\cdot w=-t\cdot w-v\phi^0\cdot w$, which is (1.3). This also agrees with the landed massVar and expansion_nuFree after imposing the sphere equation. $\square$

For a constant external field, (1.1) contains the field-only term $\sum_x b^2/(2m)$ of RGFREE-3 (1.1). It must remain in the physical density or be displayed as a separate known factor. Define the reduced density $\rho^\flat=\exp\{\beta\sum_x b^2/(2m)\}\rho$ for $m>0$ when discussing a limit in independent $b$. This normalization is **exact**, but an analytic family across $m=0$ requires a separate continuation assertion: the function $b^2/m$ itself has no joint holomorphic extension at $(m,b)=(0,0)$. Along the physical path $b=mh$ it is $m h^2$ and poses no such algebraic problem. Form the RG renormalization conditions from the *full* density, restoring this known factor exactly; RGFREE.md §1 explains its contribution to the mass-free second equation using P4 (4.13)–(4.14).

### 1.2 Source-adapted tube

For a level-$j$ generating set $G$, let $\phi_{\rm bg}^c(\Psi,h)$ be its complex background of mass $\mu_{\rm bg}$. The **repaired scalar domain** $\mathcal T_{j,m}^{\mu_{\rm bg}}(G;r_v,r_t)$ consists of points of the landed $\Xi_j^c(G;\mu_{\rm bg},1,\varepsilon_j)$ satisfying, at every interior site,
$$
|\,\phi_{\rm bg}^c\cdot b-m\,|<r_v\varepsilon_j^2,
\qquad
\|b-(\phi_{\rm bg}^c\cdot b)\phi_{\rm bg}^c\|
  <r_t\sqrt m\,\varepsilon_j.
\tag{1.4}
$$
Here $r_v,r_t>0$ are fixed after the background constants and before $\alpha_0,E_0,\beta_{\rm initial}$. In the fine-lattice Lean coordinates, use the fine physical mass $\nu_kL^{-2k}$ and the site spacing $\ell(x)$: the unit-scale quantities in (1.4) are $m_x=(\nu_kL^{-2k})\ell(x)^2$ and $b_x=m_xh(x)$. At a level-$j$ site, $\ell(x)=L^j$ and $m_x=m_j$. The inequalities are strict, hence define an open domain wherever the landed background is analytic. At $m=0$ set $b=0$ and use the mass-zero background domain; the mass perturbation (1.3) then vanishes. The tube is invariant under real orthogonal rotations. The existing Def-6 complex rotation clauses can retain their form, asserting equality whenever both rotated arguments lie in the tube; Hermitian norms are not invariant under all complex orthogonal rotations.

**Real-domain inclusion (proved conditional on the proved background sphere property).** If $h_0\in S^{N-1}$ and $\phi_{\rm bg}$ is a real sphere field, then $|v_x-m|\le2m$ and $\|t_x\|\le2m$. Thus the original real cutoff data belong to (1.4) whenever
$$
2m<r_v\varepsilon_j^2,\qquad 2\sqrt m<r_t\varepsilon_j.
\tag{1.5}
$$
Both follow from the inductive (H.6) scale bounds after the final $\beta_{\rm initial}$ choice, uniformly in the mass-free range: $m/\varepsilon_j^2\le C\alpha_0^{-2}\beta_{\rm initial}^{-1}L^{-2\gamma j}$. The factor 2 is valid without assuming $h_0$ points near $\phi_{\rm bg}$. For complex data the tube is an additional condition; XiC alone does not imply it.

Equation (1.3) gives an explicit bare activity estimate on this tube:
$$
|V_m(w)|\le r_t\sqrt m\,\varepsilon_j\sum_x\|w(x)\|
  +\frac{m+r_v\varepsilon_j^2}{2}\sum_x\|w(x)\|^2.
\tag{1.5a}
$$
This is **proved** by the triangle inequality and $|v_x|\le m+r_v\varepsilon_j^2$. Multiplication by $\beta$ and integration still require Gaussian completion, cutoff control and a physical activity construction; (1.5a) by itself is not a polymer estimate.

At constant $\phi^0=e_1$, write $b=Ve_1+t$, $e_1\cdot t=0$. The domain permits $|V-m|<r_v\varepsilon^2$ but only $\|t\|<r_t\sqrt m\,\varepsilon$. The RGFREE-3 counterexample has $t=i\lambda\varepsilon^2e_2$, so it is excluded once $m<(\lambda/r_t)^2\varepsilon^2$. This is **proved** and remains true in $N\ge3$ for complex null vectors $t\cdot t=0$: (1.4) controls the Hermitian norm of $t$, not merely the invariant $t\cdot t$. A restriction only on SMALLFIELD.md §2.3's invariant $W=t\cdot t$ would not control such null vectors or the H7 background difference.

**One-block test (proved).** In the constant-field Gaussian model with tangent fluctuation $w\in\mathbb R^{N-1}$ and quadratic coefficient $a+v$,
$$
\frac{\int e^{-\beta(a+v)|w|^2/2+\beta t\cdot w}\,dw}
{\int e^{-\beta a|w|^2/2}\,dw}
=\left(\frac a{a+v}\right)^{(N-1)/2}
 \exp\!\left\{\frac{\beta\,t\cdot t}{2(a+v)}\right\}.
\tag{1.6}
$$
The identity extends holomorphically near $a>0,v=0$. On (1.4), its logarithm is bounded by $C(|v|+\beta m\varepsilon^2)$, uniformly as $m\downarrow0$ when $\beta m\le C_L$. On the old full disc $t=i\lambda\varepsilon^2e_2$, the last logarithm has modulus of order $\beta\varepsilon^4$. Thus the transverse restriction is necessary already for this Gaussian part. Formula (1.6) does **not** prove the physical polymer activity estimate: cutoffs, nonlinear sphere charts, determinants and old terms remain.

### 1.3 Exact draft Def-6 changes

In Balaban/SmallField/Def6Terms.lean retain bgMass for the solver and compositions, and add a physical fine mass
$$
\operatorname{physMass}(L,k,\nu_k)=\nu_kL^{-2k}
\tag{1.7}
$$
in the conventions of its current bgMass definition. In Balaban/SmallField/Def6.lean change the density equation to evaluate the main action at physMass and the background field at bgMass:
$$
\operatorname{action}(G,a,\operatorname{physMass},D,
          \operatorname{bgField}(G,a,\operatorname{bgMass},D)).
\tag{1.8}
$$
Keep Ecomp and Fcomp composed through bgMass. If field-only normalization is extracted, add its factor explicitly to the density field; do not hide it in a bounded local E. For mass-free terms and the switch output, replace XiDom by the mass-adapted tube (1.4) in analyticE, analyticM, boundE, boundM and the corresponding rotation/Euclidean domain premises. Give each term a domain tag recording its birth convention and physical mass: a later complete term may have the ordinary complete XiC domain, while an inherited thin-tube term keeps its transported tube. The domain on which the total density is controlled is the intersection of its term domains. This tag is necessary because (1.5) is guaranteed in the mass-free/switch range, not at arbitrarily late complete scales with larger $m_j$. Restrict the real density equation to the physical unit sphere $h_0\cdot h_0=1$ (for instance, add this condition to its indicator); prove (1.5) so that these real data enter the new analytic domain at their birth scale. Add the physical mass as a parameter to these domain fields. At $m=0$ require the local terms to be independent of $h$ on the unrestricted zero-mass domain, which is the content of Proposition 1 of RGFREE-3 rather than an inconsistency.

The current Def-6 is a draft read-only Lean class. These are proposed declaration changes, **not landed theorems**. Its locality, symmetry, torus-family and renormalization-condition fields remain necessary. The corresponding Def-7 subdomain class must carry the same physical/background mass split and domain tags. Showing that later background composition maps complete real data into every inherited thin tube is **OPEN TUBE-FLOW**; a switch-step repair alone does not prove the full iteration.

### 1.4 Repaired FREE-ACT and its present proof boundary

The original FREE-LOC in RGFREE-2 (1.1) demanded a full $m$-uniform transverse $b$ disc. Replace it by **FREE-ACT-TUBE**: the actual mass-free fluctuation integral and old-action re-expression have a covariant, conjugation-equivariant local expansion on a common open neighbourhood of the $c_{10}$ $\xi$ ball and the tube (1.4), with
$$
\sup_{z_0}\sum_{Y\ni z_0}e^{\kappa_a d(Y)}
\sup_{\mathcal T^+}|E_Y|\le B_E,
\tag{1.9}
$$
and a torus-independent limit and the P4 (5.15)–(5.17) $x_1^2$ moment bound. The enlarged tube $\mathcal T^+$ has fixed strict *relative* margins in the two inequalities of (1.4). It contains these three reference slices, uniformly for $\|\xi\|_\infty\le c_{10}$:

1. $U$ slice: constant $\Psi=Ue_1$, $b=m(\xi)e_1$, $|U-1|<r_U\varepsilon$;
2. $V$ slice: constant $\Psi=e_1$, $b=Ve_1$, $|V-m(\xi)|<r_V\varepsilon^2$;
3. transverse field slice: $b=m(\xi)e_1$, $\Psi=e_1+\vartheta_\perp$, $\|\vartheta_\perp\|_{\rm sf}<r_\perp\varepsilon$.

For the first two, $\phi^0=e_1$, so $t=0$ and (1.4) holds with a fixed margin when $r_U,r_V$ are small. For the third, the sphere identity gives $|v-m|\le C m\|\phi^0-e_1\|^2$, $\|t\|\le C m\|\phi^0-e_1\|$; therefore (1.4) follows from a background response estimate $\|\phi^0-e_1\|_{\rm sf}\le C r_\perp\varepsilon$ and late $m/\varepsilon^2\ll1$. The constant-field inclusion is **proved** directly; the uniform spatial-profile inclusion on the actual mixed cover is **conditional on OPEN PROFILE-DOM**, which must instantiate the background response and XiC margins for all $\xi$.

On the three slices, Cauchy gives the first two divided RG jets with losses $r_U^{-1}\varepsilon^{-1}$ and $r_V^{-1}\varepsilon^{-2}$, and the transverse second derivative with loss $2r_\perp^{-2}\varepsilon^{-2}$. The P4 moment sum then yields the same numerical form
$$
\|\widetilde f_{\rm free}(\xi,p)\|_\infty
\le B_{\rm free}\widehat\beta^{-1}\varepsilon^{-2},
\qquad
\widehat\beta^{-1}=(1+c_{10})\beta_u^{-1},
\tag{1.10}
$$
**conditional on OPEN FREE-ACT-TUBE and PROFILE-DOM**. RGFREE-2 (1.4) proves $\widehat\beta^{-1}\varepsilon^{-2}\le2\alpha_0^{-2}\beta_{\rm initial}^{-1}q^u$ under (H.6). Thus this repaired datum fits the landed rg_step_infty hfb and hηbd hypotheses with the algebraic matrixFree of RGFREE.md, if the actual physical activity bound is established. A single product disc in all raw field variables is unnecessary for these three jets; holomorphy in $\xi$ is still needed on one fixed neighbourhood.

From the permitted landed results, (1.1)–(1.3), the one-block bound (1.6), and this Cauchy implication are **proved**. expansion_bounds, interaction_block_bound and interactionV_rot in Balaban/Fluctuation control specified pointwise interactions under their complex background hypotheses; Covariance lemma24_*, Measure*, and SizeMod* control their stated objects. The landed marked_cubes and marked_cubes_two require an already bounded physical LabelAct and marks; Pst_Gst_differentiableOn requires their holomorphy. Localization/Decoupled2 supplies abstract mixed-cover estimates, while i5_background omits the fluctuation variable. SmallField/RenormTermwise* requires physical PremisesTerm and SumConds. No permitted declaration constructs the activity, mixed cover, fluctuation I-5 or old-term transfer on (1.4). FREE-ACT-TUBE and PROFILE-DOM therefore remain **OPEN**, not proved by (1.6).

## 2. Repaired switch domain and RG conditions

### 2.1 Exact domain and one-block check

Let $\phi^0(\Theta)$ and $\phi^m(\Theta,h)$ be the two backgrounds and $D=\phi^0-\phi^m$. Define $\|D\|_{\rm sf}$ as the supremum of the field difference and its appropriately spaced first and second differences and multiplier response, in the norm of FLUCTUATION.md Lemma 2.9(a). The **switch tube** $\mathcal S_{u,m}(r_D)$ is the open set on which:

- the data lie in the mass-free tube (1.4) and the corresponding complete tube, and in both landed XiC/background domains;
- every old composed argument and its interpolation has a common strict analytic margin in its repaired old-level tube;
- $\|D\|_{\rm sf}<r_D\sqrt m\,\varepsilon$.

The last two conditions are mathematical conditions of the proposed domain, not conclusions from the landed class. The first can be checked algebraically on the reference slices; the second is **OPEN OLD-TUBE-COMPOSE** for physical old terms. Analyticity of the two backgrounds on their landed domains makes the strict $D$ condition open.

**Proposition 2 (proved scalar bound).** On $\mathcal S_{u,m}(r_D)$, the chord contribution to the action per output block is at most $C_H r_D^2\beta_um\varepsilon^2$, where $C_H$ is fixed by the local operator and spacing bounds. 

*Proof.* FLUCTUATION.md Lemma 2.9(a) gives $\mathscr S=-\beta_u\langle D,(H^m+\alpha^m)D\rangle/2$. Here $H^m=-\Delta+aQ^*Q+m$. Each site enters at most $2d$ Laplacian bonds and a fixed number of block averages; $a\le3/2$, $m\le1$, and the complete XiC multiplier is uniformly bounded. Hence the absolute value of each site contribution is at most $C_H\|D\|_{\rm sf}^2$, with $C_H$ depending only on $d,L$ and the admitted multiplier bound. Sum over one output block and apply $\|D\|_{\rm sf}<r_D\sqrt m\,\varepsilon$. This proves the scalar estimate, not a localized polymer bound. $\square$

In the one-block example write $b=Ve_1+t$, $e_1\cdot t=0$, $A=a+V$, $R=\sqrt{A^2+t\cdot t}$. For $|V-m|<r_v\varepsilon^2$ and $\|t\|<r_t\sqrt m\,\varepsilon$, the exact formulas are
$$
\phi^m=(Ae_1+t)/R,\qquad
|R-A|\le C\|t\|^2\le Cr_t^2m\varepsilon^2,\qquad
\|\phi^m-e_1\|\le C\|t\|.
\tag{2.1}
$$
The proof is $R-A=(t\cdot t)/(R+A)$ and $|t\cdot t|\le\|t\|^2$, on the branch where $|R+A|\ge c_a>0$. The RGFREE-3 source $t=i\lambda\varepsilon^2e_2$ fails the tube when $m\ll\varepsilon^2$; its $\beta_u\varepsilon^4$ cost is therefore outside the repaired claim. This is **proved**.

### 2.2 The three RG reference slices

For each $\xi$ in the fixed trial ball, let $m(\xi)$ and $a(\xi)$ be the physical parameters. On the aligned constant-field slice $\Theta=Ue_1$, $b=Ve_1$, both backgrounds equal $e_1$ as long as $aU+V$ stays in its analytic branch. Thus $D=0$ and every old composition agrees:
$$
\mathscr D(Ue_1,Ve_1,\xi)=0
\quad\text{for }|U-1|<r_U\varepsilon,\quad
|V-m(\xi)|<r_V\varepsilon^2.
\tag{2.2}
$$
This is **proved** from the critical-point equation and the affine composition in FLUCTUATION.md Lemma 3.5(iii). At an old level $j$, the same constant external field gives $b_j=(m_j/m_u)Ve_1$ and hence $|b_j-m_j e_1|=(m_j/m_u)|V-m_u|\le r_V\varepsilon_u^2\le r_V\varepsilon_j^2$; its transverse source is zero. Thus the source-tube part of old-level inclusion holds on this slice. The full XiC/composition margin is still a separate domain condition. The switch contribution to the *radial* and *longitudinal-field* renormalization conditions is identically zero for every $\xi$; no transverse $b$ Cauchy disc is needed for those two conditions. The identity remains valid when $m(\xi)$ varies with $\xi$ because the two backgrounds coincide at each parameter value.

For the transverse second-moment condition, keep $b=m(\xi)e_1$ and vary $\Theta=e_1+\vartheta_\perp$ on a spatial profile disc $\|\vartheta_\perp\|_{\rm sf}<r_\perp\varepsilon$. If the proved background response of FLUCTUATION.md Lemma 2.9(a) is instantiated uniformly on this disc, then $\|\phi^m-e_1\|_{\rm sf}\le C r_\perp\varepsilon$ and its source $m(\phi^m-h)$ has norm at most $Cmr_\perp\varepsilon$. Its response satisfies
$$
\|D\|_{\rm sf}\le C K_2m r_\perp\varepsilon
  <r_D\sqrt m\,\varepsilon
\tag{2.3}
$$
after the late $m$ choice. This gives the strict $D$ margin needed for transverse field Cauchy, **conditional on OPEN PROFILE-DOM** for the actual generating sets and $\xi$ neighbourhood. It does not establish OLD-TUBE-COMPOSE.

**Repaired SWITCH-JOINT (OPEN physical localization input).** On a common enlargement of the switch tube containing the three slices above, the full correction of RGFREE.md (2.2) has a covariant, conjugation-equivariant local expansion $\sum_YD_Y$, with absolute old-scale convergence, and
$$
\sup_{z_0}\sum_{Y\ni z_0}e^{\kappa_a d(Y)}
\sup_{\mathcal S^+}|D_Y|
\le C_{\rm sw}\bigl(\beta_um\varepsilon^2+E_0\sqrt m\bigr),
\tag{2.4}
$$
plus the weighted $x_1^2$ moment after two transverse field derivatives. The source and $D$ bounds prove the *scalar chord* part of (2.4). For an individual old term, if its interpolation stays a fixed distance $c\varepsilon_j$ from its analytic boundary and $|J_j^0-J_j^m|\le C_{j,u}\|D\|_{\rm sf}$, the fundamental theorem of calculus and Cauchy give the **proved conditional estimate**
$$
|E_j(J_j^0)-E_j(J_j^m)|
\le C E_0e^{-\kappa d_j(X)}
     C_{j,u}\,\frac{\sqrt m\,\varepsilon}{\varepsilon_j}.
\tag{2.5}
$$
The required common interpolation, physical mixed-cover support, fluctuation I-5, star-crossing allocation, $j$ sum and new-scale moment are **OPEN OLD-TUBE-COMPOSE / OPEN SWITCH-JOINT**. The landed RenormTermwise, Decoupled2 and i5_background declarations do not discharge them without their physical hypotheses.

Assuming (2.4), use (2.2) for the first two divided switch forcing components. Apply two field Cauchy derivatives on the transverse profile disc and the weighted moment bound for the third. Its norm satisfies
$$
\|f_{\rm sw}(\xi,p)\|_\infty
\le C_{\rm mom}C_{\rm sw}
  (\beta_um\varepsilon^2+E_0\sqrt m)
  \widehat\beta^{-1}\varepsilon^{-2}
\le B_{\rm sw}\widehat\beta^{-1}\varepsilon^{-2},
\tag{2.6}
$$
where $B_{\rm sw}=C_{\rm mom}C_{\rm sw}(C_L+E_0)$ is fixed before the final inverse-temperature threshold. This is a **proved Cauchy implication conditional on OPEN SWITCH-JOINT and PROFILE-DOM**. Set $\eta_{\rm sw}=B_{\rm sw}\widehat\beta^{-1}\varepsilon^{-2}$. RGFREE-2 (1.4) yields
$$
\eta_{\rm sw}\le
B_{\rm sw}(2/\alpha_0^2)\beta_{\rm initial}^{-1}q^u,
\tag{2.7}
$$
the literal scale-sensitive hηbd bound of the landed Balaban.Flow.rg_step_infty. The switch correction, including all its $\xi$ dependence, belongs in $f$, not in the complete counterterm matrix.

The matrix remains Balaban.Flow.matrixInfty$(a,m,\tau,c_1(m),c_2(m),\varepsilon)$ with the explicit entries in RGFREE.md (2.7a). For the stated InftyRange, the landed triangularBounds_matrixInfty proves the real TriangularBounds hypothesis, and matrixInfty_conj gives conjugation. The landed rg_step_infty still additionally requires: an open complex parameter set $P$ and analytic physical parameter map (hP,hAan); analytic quadratic counterterm $c$ with the $r^2$ bound (hc,hcb); actual total forcing holomorphy and bound (hf,hfb), now conditional on FREE-ACT-TUBE and SWITCH-JOINT; the smallness inequality $16(42\eta)\max\{84\kappa,1/c_{10}\}\le1$ (hcond); (2.7) (hηbd); and the conjugation conditions (hσP,hAσ,hcσ,hfσ). No changed domain alone proves hf or hfb. For each positive real $m_0$ one may choose $P$ with $|m-m_0|<c m_0$, so the square-root tube radius is a fixed real bound on that $P$. A *single* open $P$ crossing $m=0$ is not obtained; continuity at zero remains OPEN CONT.

## 3. Repaired H7 domain

Define the **switch H7 tube** $\mathcal H_{u,m}$ by the same joint-background and old-composition conditions as $\mathcal S_{u,m}$ and the stricter response bound
$$
\|D\|_{\rm sf}<
\rho_H:=r_H\min\{\sqrt m\,\varepsilon,\ c_9L^{-us}\},
\qquad 0<r_H\le1/16.
\tag{3.1}
$$
On this domain the leading observable term satisfies $|\langle g,D\rangle|\le r_Hc_9L^{-us}$ for $\|g\|_1<1$, **proved**. The RGFREE-3 counterexample has $\|D\|\asymp\varepsilon^2$ independent of $m$ and lies outside (3.1) for small $m$. This pointwise estimate does not give the H7 localization rate. Name **OPEN H7-TUBE-DLOC** the additional claim that $D(x)$ has jointly analytic local coefficients $D(x,Y)$ with $\sup_x\sum_{Y\ni x}e^{(3\kappa/2)d_u(Y)}\sup_{\mathcal H^+}\|D(x,Y)\|\le\frac18c_9L^{-us}$. An actual local response/decoupling instance with its physical cover is required; the scalar response alone does not prove it.

The H7 tube still contains the physical real unit-field slice after the late $\beta_{\rm initial}$ choice. FLUCTUATION.md Lemma 2.9(a)'s proved real response gives $\|D\|_{\rm sf}\le2K_2m$. From (H.6) and $\varepsilon_u\ge\alpha_0L^{-u((d-2)/2-\gamma)}$,
$$
\frac{2K_2m}{\sqrt m\,\varepsilon_u}
\le C\alpha_0^{-1}\beta_{\rm initial}^{-1/2}L^{-\gamma u},
\qquad
\frac{2K_2m}{c_9L^{-us}}
\le C\beta_{\rm initial}^{-3/4}
 L^{-u((d-2)/2-\gamma+\alpha_1)}.
\tag{3.2}
$$
Both are uniformly small for $d\ge3$, $0<\gamma<1/2$, $\alpha_1>0$. Thus (3.1) does **not** discard the real switch data, and no extra restriction $(d-2)/2-2\gamma+\alpha_1\ge0$ is needed for this real inclusion. The claim concerns the real physical slice. A common open $\xi$ neighbourhood of the full fixed $c_{10}$ trial ball in this narrower tube is **OPEN H7-JOINT-DOM**; preservation of the tube through later RG steps is **OPEN H7-TUBE-PRESERVE**.

The old observable difference still requires a physical marked expansion. Under a common old-term Cauchy radius $c\varepsilon_j$ and an interpolation difference $|J_j^0-J_j^m|\le C_{j,u}\rho_H$, a single old mark obeys the **proved conditional estimate** $C c_9L^{-js}e^{-\kappa d_j(X)}C_{j,u}\rho_H/\varepsilon_j$. Turning this into a new-scale $3\kappa/2$ local expansion with total old contribution at most $\frac18c_9L^{-us}$ requires the actual marked activity, mixed-cover localization and old-scale sum. Name this missing physical assertion **OPEN H7-TUBE-MARK**. The landed marked_cubes and marked_cubes_two prove the abstract cluster estimates once their mark hypotheses hold; Pst_Gst_differentiableOn adds holomorphy once its input holomorphy holds. They do not prove H7-TUBE-MARK or H7-TUBE-DLOC. The separate H7 claim of RGFREE-2 (3.3)–(3.4) must be replaced by the present tube statement and these two named open localized assertions.

## 4. Changes to FLUCTUATION.md and closure status

In FLUCTUATION.md Definition 2.1 and §2.3, state two independent masses, physical $m$ in the action and $\mu_{\rm bg}$ in critical points, covariance and compositions; use (1.1) when $\mu_{\rm bg}=0$. In §2.8 Lemma 2.9 replace its complex localization claim (b) by Proposition 2 on $\mathcal S_{u,m}$ and OPEN SWITCH-JOINT (2.4), and replace its joint RG claim (c) by the three-slice argument (2.2)–(2.7), explicitly conditional on PROFILE-DOM and SWITCH-JOINT. State that the first two switch reference jets vanish identically. In Theorem 3.1(g),(h) and §3.6 replace the full XiC analytic-bound target at the switch with the source tube (1.4), switch tube $\mathcal S_{u,m}$ and H7 tube (3.1); record FREE-ACT-TUBE, OLD-TUBE-COMPOSE, SWITCH-JOINT, H7-JOINT-DOM, H7-TUBE-DLOC, H7-TUBE-MARK, H7-TUBE-PRESERVE and TUBE-FLOW as OPEN. Any I-8/I-9 closure claim must show these tubes are carried by the actual background compositions and fluctuation step; the existing i5_background and abstract mixed-cover declarations do not establish this.

Fix constants in this order: $d,N,L,\gamma,\alpha_1$, background/Green and cover constants, the rate and entropy margins, then $c_{10}$ and the fixed tube numbers $r_v,r_t,r_D,r_H,r_U,r_V,r_\perp$. Establish any geometric localization constants $C_{\rm sw},C_{\rm mom}$ independent of $E_0$, then fix $\alpha_0$ and $E_0$ in FLUCTUATION.md §1.5's order; $B_E,B_{\rm free},B_{\rm sw}$ and $B=B_{\rm free}+B_{\rm sw}$ are then fixed. Finally choose $\beta_{\rm initial}\ge\beta_*(\alpha_0,E_0)$ to enforce (1.5), (2.3), (3.2), inductive (H.6), the landed hcond, and the source/response margins. The source notes' precise order for other geometric constants remains the one in FLUCTUATION.md §1.5. No uniform threshold as $\alpha_0\downarrow0$ or $E_0\uparrow\infty$ is claimed.

| Result | Status |
|---|---|
| Physical/background mass split (1.1), exact source identity (1.3), one-block estimates (1.6),(2.1), exclusion of RGFREE-3 counterexamples | **Proved.** |
| Real unit-field inclusion in the source and H7 tubes, (1.5),(3.2) | **Proved conditional on the cited proved background sphere and real response results and inductive (H.6).** |
| Three-slice RG geometry (2.2), Cauchy implication (1.10),(2.6), scale factor (2.7) | Constant-field identity and scale arithmetic **proved**; transverse profile inclusion **conditional on OPEN PROFILE-DOM**; physical forcing **conditional on OPEN FREE-ACT-TUBE and SWITCH-JOINT**. |
| Physical FREE-ACT-TUBE, OLD-TUBE-COMPOSE, SWITCH-JOINT, H7-JOINT-DOM, H7-TUBE-DLOC, H7-TUBE-MARK, H7-TUBE-PRESERVE, TUBE-FLOW, CONT | **OPEN.** The permitted landed interfaces do not instantiate them for this repaired class. |

**Confidence.** High for the algebraic factorization, exact one-block repair, counterexample exclusion, reference-jet identity, and scale arithmetic. Moderate for the sufficiency of the proposed tube under future domain-preservation proofs; no physical localization or full RG step is claimed proved.

**Sources.** FLUCTUATION.md v2.1 §§1.5, 2.3, 2.8, 3.6 and Lemmas 2.9, 3.5; SMALLFIELD.md v3 §§1.6–1.7, 2.3, 3.4–3.7; [RGFREE.md](RGFREE.md) §§1–2, [RGFREE-2.md](RGFREE-2.md) §§1–3, [RGFREE-3.md](RGFREE-3.md) §§1–3. The algebraic mass-free split is the landed Balaban/Fluctuation/ExpansionNuFree.lean actionC_mass_split, massVar, expansion_nuFree. The other Lean declaration names in this note were checked in Balaban/Flow/MatrixInfty.lean and RGInfty.lean, Balaban/Fluctuation/ExpansionBounds.lean and ExpansionLocal.lean, Balaban/Polymer/MarkedCubes*.lean, Balaban/SmallField/Def6.lean and Def6Terms.lean, and Balaban/Localization/Decoupled2*.lean and I5.lean. No file under /home/scott/Balaban was edited.
