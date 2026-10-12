# The base small-field proposition: two failed deductions and a precise closure statement

**Status, 12 October 2026.** The landed hard-spin chart and base-action files prove the real chart identity and the first three witness gains. They do not prove the cutoff transfer or the localized first-step integral of LF-RECONSTRUCTION Proposition II.7.9. This note gives two precise counterexamples to deductions that would otherwise hide those gaps, proves the correct support-local cutoff implication, and states a conditional version of Proposition II.7.9 with the exact analytic and numerical inputs its consumers need. It does **not** claim the original proposition is proved. No theorem in the sources supplies the missing model-specific estimates for every base record.

Sources: LF-RECONSTRUCTION v1.3, Definition II.7.1, Lemmas II.7.2, II.7.7--II.7.8, Proposition II.7.9 and Theorem II.7.10; LF-BASE-KF0 Part A; FLUCTUATION §§3.4, 5.4--5.5; BASE-KERNEL.md and BASE-KERNEL-2/3.md; P5 Lemma 2.1, (2.39)--(2.47), (3.9), Proposition 3.2; P6 (2.2), (4.29)--(4.31), Lemma 4.2. Paper keys are those of review/SOURCES.md. Lean declarations cited below are read-only under /home/scott/Balaban.

## 1. What is already proved

The following source-to-Lean map fixes the boundary of this audit.

| Mathematical fact | Landed declaration | Exact extent |
|---|---|---|
| The $P_1,Q_1,R_1,S_1$ geometry and old cutoff decomposition | LargeField.BaseRecord, chiPrimeZero_decomposition; BaseHistory.base_P_nbhd_compl, base_bond_comp | Set geometry and the real algebra $1-AB=(1-A)+A(1-B)$ |
| Old small-field support on $\Omega_1$ and its collar | BaseSupport.baseSpinSupport_of_baseRecord | Strict old tests, with threshold $\delta_0$ |
| Spins in the base hemisphere | SpinsNearBackground.spins_near_background | $|\phi_x-e_x|\le C_{\rm hs}L\delta_0\le1/4$, $C_{\rm hs}=d+2+4dK_1$ |
| Chord quadratic identity and exact real chart measure | ChordQuadratic.action_sub_eq_chord_quadratic; ChartIntegral.lintegral_sphere_pi_eq_gaussian_sqrt | Exact real integrals, including Jacobian, mixed normal term and determinant |
| Base main action and $P_1$ witness gains | BaseMainAction.baseMainAction; BaseWitnessGain.baseBlock_gain, baseMainAction_bond_gain, baseMainAction_site_gain | The bond, site and block gains displayed in Lemma II.7.8 |
| Abstract base kernel from an input | BaseSmallField.baseKernel_of_input, baseStepData_of_input | The encoded clauses of (S0), (S1), (S4) from BaseSmallFieldInput; no physical integral is identified |
| Rotation form (S5) | BaseS5.BaseS5 | A target predicate; no proof that the physical base kernel satisfies it |

The landed base gains are $2^{N/2}e^{-L^{d-2}p_0^2}$ for a block witness, $e^{-p_0^2/(8a)}$ for a bond witness, and $e^{-p_0^2/(9a)}$ for a site witness in regime (B), under the explicit premises of BaseWitnessGain. The one-layer cut resolvent of BASE-KERNEL-3.md Theorem 1.1 has a gap $1/(4L^2)$ under $|\alpha_x|\le1/(8L^2)$ for real cut parameters and a small complex neighbourhood. It is a mathematical construction in that note, not a landed theorem for the actual H7 cube-polydisc. Dec2.FootLocal and its footprint lemmas concern a scalar Green operator; Dec2.XFootLocal still requires $k\ge1$. The landed principal-function estimates for the later step have not been instantiated at $k=0$.

## 2. Cutoff margins: counterexample to the record-only assertion

For a base record let $D_+=\Omega''_1\cap Z'$ be the integrated sites of one component and let $A_cB_c=$ chiPrimeZero for a scale-one cube $c$. For a good cube $c\notin P_1$, define its *full test footprint* $F(c)$ to contain every fine site in each block average used by $A_c$, both endpoints of each bond used by $B_c$, and every site in its regime-(B) test. Set
$$\mathcal J_+(Z')=\{c\notin P_1:F(c)\cap D_+\ne\varnothing\}. \tag{2.1}$$
In particular, a bond with one endpoint in $D_+$ puts its tested cube in $\mathcal J_+$ even if the cube itself is outside $D_+$. BaseHistory.base_P_nbhd_compl and base_bond_comp ensure that a failed $P_1$ factor reads only retained spins in $\Omega_1^c\cap Z'$; these failed factors remain in the kernel.

**Counterexample 2.1 (strict old tests have no uniform margin).** Let $N\ge2$, $0<\delta_0<1/4$, and $0<r<\delta_0/4$. On a sufficiently large torus choose a record with $P_1=\{p\}$ and $Q_1=R_1=S_1=\varnothing$. Choose a good cube $c$ at cube distance two from $p$. Lemma II.7.2(d) gives $P_1^{\sim3}\subset\Omega_1^c$; thus $c$ and every cube touching one of its bonds lie outside $\Omega_1$, so $F(c)\cap D_+=\varnothing$. Choose a fine site $x$ in $c$, let
$$t=\delta_0-r/2,\qquad u=(1,0,\ldots,0),\qquad
v=(1-t^2/2,\ t\sqrt{1-t^2/4},0,\ldots,0). \tag{2.2}$$
Both $u,v$ are unit and $|u-v|=t$. Put $\phi_x=v$ and $\phi_z=u$ at all other sites. Every nearest-neighbour bond difference is either $0$ or $t<\delta_0$. For every block outside $p$, choose $\theta_y=(Q\phi)_y$, so all its $A$ tests hold. On one block in $p$, choose $\theta_y$ at distance more than $2\delta_0$ from $(Q\phi)_y$, so $A_p=0$ and the prescribed $P_1$ failure holds. In regime (A) all good $B$ tests hold. In regime (B), choose $h=u$ and $0<\nu\le1$; then $\nu|\phi_z-h|^2\le t^2<\delta_0^2$, so the site tests also hold. Hence the old product of Definition II.7.1 is nonzero for this record, while a tested bond at $x$ has
$$|\partial\phi|=\delta_0-r/2>\delta_0-2r. \tag{2.3}$$
Thus neither BaseRecord nor chiPrimeZero $=1$ off $P_1$ implies a margin of size $2r$ on **every** good cube. The example lies outside $\mathcal J_+$, so it does not refute a margin theorem restricted to the tests actually read by the small-field integral. It shows why a record-wide half-threshold assertion is the wrong statement.

**Lemma 2.2 (proved, support-local transfer).** Let $e$ be the real unit background on $\Omega_1$, extended by the retained spin $\phi$ on $\Omega_1^c$. Suppose $|\phi_z-e_z|\le r$ on $\bigcup_{c\in\mathcal J_+}F(c)$ and, on all tests appearing in those footprints,
$$|\theta_y-(Qe)_y|<2\delta_0-r,\quad
|e_z-e_w|<\delta_0-2r,\quad
\sqrt\nu\,|e_z-h|<\delta_0-\sqrt\nu\,r \quad\text{in regime (B)}. \tag{2.4}$$
Then $A_cB_c=1$ for every $c\in\mathcal J_+$. Deleting exactly those factors from
$$\prod_{c\in P_1}(1-A_cB_c)\prod_{c\notin P_1}A_cB_c \tag{2.5}$$
is an identity on this real domain, and the remaining old factor is independent of all spins in $D_+$.

*Proof.* Block averaging contracts the supremum norm, so the block test is at most $|\theta_y-(Qe)_y|+r<2\delta_0$. The tested bond is at most $|e_z-e_w|+2r<\delta_0$. In regime (B) its site test is at most $\sqrt\nu|e_z-h|+\sqrt\nu r<\delta_0$. Thus each good factor indexed by $\mathcal J_+$ equals one. Every old factor not indexed there reads no integrated site by the definition of the full footprint, and no failed $P_1$ factor reads one by Lemma II.7.2(d). $\square$

A convenient sufficient version of (2.4) is
$$|\theta_y-(Qe)_y|<\tfrac32\delta_0,\quad
|e_z-e_w|<\tfrac12\delta_0,\quad
\sqrt\nu|e_z-h|<\tfrac12\delta_0,\quad
r\le\delta_0/4,\quad \sqrt\nu\,r\le\delta_0/4. \tag{2.6}$$
The last inequality is automatic from $r\le\delta_0/4$ when $\nu\le1$; for a larger mass it must be checked separately. In the source normalization of BaseWitnessGain.tailQ_two_delta,
$$\delta_0^2a\beta_0=p_0(\beta_0)^2. \tag{2.7}$$
If the localized chart estimate gives $|\xi_z|\le B_5\beta_0^{-1/2}p_1(\beta_0)$ and $|\xi_z|\le1/4$, the sphere chord has $|\phi_z-e_z|\le2|\xi_z|$. Thus one may take $r=2B_5\beta_0^{-1/2}p_1(\beta_0)$, and
$$\frac r{\delta_0}
=2B_5\sqrt a\,\frac{p_1(\beta_0)}{p_0(\beta_0)}
\le 2B_5\sqrt a\,\frac{A_1}{A_0}
=\frac{\sqrt a}{2K_2}, \tag{2.8}$$
using row 9, $A_0=4K_2B_5A_1$, and $p_1/p_0\le A_1/A_0$ for $\beta_0\ge e$. The explicit sufficient choice is $K_2\ge2\sqrt a$ (and $K_2\ge2\sqrt{a\nu}$ if $\nu>1$). This corrects the missing $\sqrt a$ in the convenient normalization discussed in BASE-KERNEL-2.md. The **background** inequalities in (2.6), including every bond across $\partial\Omega''_1$, do not follow from the landed SpinsNearBackground.spins_near_background: that theorem only gives $|\phi-e|\le(d+2+4dK_1)L\delta_0$, which is much larger than $\delta_0/4$ before the fluctuation cutoff is imposed. P5 Lemma 2.1 states an indicator removal in its later-step setting; LF-RECONSTRUCTION Lemma III.7.1 proves a window version from its own retained factors. Neither landed theorem identifies the full first-step family (2.1) and establishes (2.6) for it. This is the remaining local margin lemma.

## 3. The first-step estimate: counterexample to using the abstract input

BaseSmallField.BaseSmallFieldInput contains functions $Kt$ and $b_0$ and fields asserting nonnegativity, measurability, support, covariance, analyticity in $g$, and a volume bound. Its docstring explicitly says that the physical remainder, cutoff transfer and first expectation are open. The theorem BaseSmallField.baseSmallFieldInput_nonempty constructs an instance with
$$Kt(a,w,o,x,h)=0,\qquad b_0(a,o,x,h,g)=0 \quad\text{for every argument}. \tag{3.1}$$
Therefore BaseSmallField.baseKernel_of_input gives $K_0=0$ on every history. This is a valid instance of that Lean structure and even makes any upper kernel bound trivial.

**Counterexample 3.1 (the zero input is not the first transformation).** Take $g=0$, $\beta_0>0$, $a>0$, $z_1>0$, a nonempty finite torus, and $N\ge2$. The physical initial density $\rho_0(\phi)=e^{-\beta_0H(\phi)}$ is strictly positive on every spin configuration. The first Gaussian kernel $t_0(\theta,Q\phi)$ is strictly positive for every real $\theta,\phi$. The product sphere measure has positive total mass. Hence the exact transform of LF-RECONSTRUCTION (II.7.1) satisfies
$$\rho_1(\psi_1)=z_1^{N|T^{(1)}|}
\int\prod_y t_0(z_1\psi_1(y),(Q\phi)(y))\,e^{-\beta_0H(\phi)}
\,d\sigma^{\otimes}(\phi)>0 \tag{3.2}$$
for every real $\psi_1$. The sum of kernels built from (3.1) is identically zero, so it cannot equal (3.2). Thus an inhabited BaseSmallFieldInput, together with BaseMainAction, BaseWitnessGain, BaseS5, the chart identity or the landed marked-cubes theorem, does not prove the **model-specific** first-step estimate or even the physical representation. This is a counterexample to that proposed deduction, not to the physical Proposition II.7.9.

There is also a source-strength mismatch in the input: BaseSmallFieldInput.b0_bound permits
$|b_0|\le C_b(\log\beta_0+B_0)|X|_1$, whereas LF-RECONSTRUCTION Lemma II.7.7(b) and BASE-KERNEL.md §3 require $C_b(\log\beta_0+1)|X|_1$ with the same $C_b$. For $B_0>1$ the former does not imply the latter. The input also records dependence on $g|_V$ but has no separate field asserting that $b_0$ reads output $\psi_1$ only on $\Omega_1\cap V$. Both source-strength clauses must be proved for the physical $b_0$ in addition to inhabiting the Lean structure.

The analytic gap is more specific than an unspecified application of a cluster theorem. ChartIntegral.lintegral_sphere_pi_eq_gaussian_sqrt gives the exact real Jacobian and determinant but no complex H7 bound. The edge-parameter resolvent of BASE-KERNEL-3.md has a neighbourhood of width $O(L^{-2})$ about $[0,1]$; the needed cube-decoupling discs have radius $e^{\kappa_1}$ and require comparison, exact core equality and torus lift. Fluctuation.marked_cubes_explicit and marked_cubes_two accept a product probability measure, LabelAct with measurable local activities and an entropy bound, and one or two marks with pointwise decay. They do not construct these objects from the sphere chart. P6 Lemma 4.2 proves a later-step mark of order $\beta_k^{-m-3/2}$ after its comparison displacement estimate (4.31); the base hard-spin Jacobian, mixed normal term and first covariance localization need a new argument. FLUCTUATION §5.5 likewise leaves the base I-9 step to LF-6. In regime (A), the $\nu$-free RG matrix of SMALLFIELD §3.7 must be supplied; in regime (B), the complete-background system of §3.4 applies. No first-step Lean theorem solves either system for the actual chart integral.

## 4. Corrected conditional Proposition II.7.9

The physical statement is not weakened: Theorem II.7.10 consumes exact equality with $\rho_1$, the scale-one Def-6 or D2-flat data, D7 boundary terms, the first RG coefficients, and the half-budget on every localized domain, including those equal to whole-torus terms. A corrected proposition therefore makes the missing hypotheses visible rather than replacing them with the inhabited abstract BaseSmallFieldInput.

**Proposition 4.1 (conditional, sufficient for the LF Def-7 base case and the $k=0$ flow step).** Fix a base record and all constants of rows 0--16 of LF-RECONSTRUCTION, including the regime choice, the torus, and the component history. Assume:

1. **(CT)** The real chart and retained output restrictions imply (2.6) for every full footprint in $\mathcal J_+(Z')$, uniformly in every component and torus. In particular the cross-boundary bonds are included. The chart cutoff gives $r$ as in (2.8), with $K_2\ge2\sqrt a$ and, when needed, $K_2\ge2\sqrt{a\nu}$.
2. **(LC)** The first-step operator $A_e=P_e^\perp G_\alpha^{-1}P_e^\perp+P_e$ has a cube-decoupled resolvent on the actual H7 background domain and parameter discs $|s_Q|<e^{\kappa_1}$. Its principal square root and logarithm equal the physical ones at $s=\mathbf1$, obey uniform weighted response and determinant bounds, agree exactly when the data agree on the prescribed cores, and obey the torus-lift equality. The resulting chart contour has $|\beta_0^{-1}v_z\cdot v_z|\le1/4$ and a uniform analytic majorant.
3. **(PE)** After CT and LC, the exact chart integral of ChartIntegral.lintegral_sphere_pi_eq_gaussian_sqrt, including the mixed normal term, the determinant, the hard-spin Jacobian, the regime-(A) $\nu$ term and the source, has a cutoff fixed in the real $\psi$ coordinates and independent of complex background parameters, as required by LF-BASE-KF0 (A.2). It equals a product-reference polymer integral with the LabelAct, entropy, measurability, DepOn and numerical hypotheses (3.1)--(3.2) of BASE-KERNEL-3.md. Use the stronger version of (3.2), with $16$ in place of $8$, whenever two-mark response coefficients are invoked. Its base P5 (3.9) marks and determinant coefficients have the uniform local bounds
   $$F_0=C_m\beta_0^{-m-3/2},\qquad
   |\mathcal D(Y)|\le C_{\rm det}\beta_0^{-m-3/2}
          e^{-\kappa_b d^{\rm cov}_1(Y\bmod\Omega_1^c)}, \tag{4.1}$$
   including every domain with whole-torus equality, for constants $C_m>0$ and $C_{\rm det}\ge0$. Take $\kappa'=\kappa_b+1\ge1$ and $\kappa_G\ge\kappa_H$. The coefficient identification with P5 (3.9) and the modular-size bridge are part of this hypothesis.
4. **(RG)** The localized first integral has the exact scale-one D1 form with $\chi_1(Z_1^c)$, vacuum, source and interaction expansions, and the P6 (2.32)--(2.33) inside/crossing split and boundary coefficient $B_{\rm st}$ at $\kappa_+=3\kappa/2$. Define $\mathcal R_n^{(1)}=0$ for $n<m$. The actual regime-(A) $\nu$-free, respectively regime-(B) complete-background, I-7 system has a solution $(\beta_1,\nu_1,z_1,E_1)$ satisfying Def-6, respectively D2-flat, H5 and the required source bounds. These objects are jointly analytic on H7, real on real data, covariant, and coherent under torus lift and $\nu\downarrow0$ where that family clause is used.
5. **(PHYS)** Define $Kt$ and $b_0$ by the *physical* retained-factor and chart-integral formulas of BASE-KERNEL.md §§1--3, with the exact determinant allocation, and prove that the sum over base records and their component kernels reconstructs (II.7.1). Their restrictions to each localized history satisfy the fields of BaseSmallFieldInput and the regime-(A) BaseS5 predicate. In addition, $b_0$ reads $\psi_1$ only on $\Omega_1\cap V$ and obeys $|b_0|\le C_{b,\rm sf}(\log\beta_0+1)|X|_1$ on H7, where the row-11 constant is chosen so that
   $$C_b\ge C_{b,\rm sf}+\max\{0,L^d\log(2^{N+1}Nv_N)\}. \tag{4.1b}$$
   In particular the source-strength bound of Lemma II.7.7(b) holds with $C_b$. This excludes the zero instance (3.1) and closes the two weaker-field gaps just noted.
6. **(WG)** Each retained $Q_1,R_1,S_1$ failure factor is bounded by the sum of its violated tests. For each complete witness choice $w$, there is a Borel pointwise majorant $S^w_0\ge Kt^w e^{{\rm Re}\,b_0}$ obtained by splitting $e^{-\mathcal A_1}$ into equal halves: one half pays the bond and site witnesses, and the other pays the $Q_1,S_1$ witnesses by LF-1. The block witness is charged to $m^w_0$ and the $R_1$ witness to one half of its site Gaussian. The $P_1$ factors are the three landed BaseWitnessGain factors stated in §1. The other one-cube gains are at most
   $$\exp\!\left[-\frac{4\gamma_0}{6^d(9K_1)^2}p_0^2\right],\quad
   \exp[-p_1^2/4],\quad
   \exp\!\left[-\frac{\gamma_0}{4\cdot6^dK_1^2}p_0^2\right] \tag{4.2a}$$
   for $Q_1,R_1,S_1$, respectively, with $\gamma_0=1/(28d)$. Charge each bond witness to at most two cubes. With
   $$A_3=\tfrac14\min\!\left\{\frac{8\gamma_0A_0^2}{6^d(9K_1)^2},\frac{A_1^2}{8}\right\}, \tag{4.2b}$$
   the witness-choice count $(d+1)(2LM)^d$, the Gaussian factors and the remaining volume factor $\exp[L^d\log(2^{N+1}Nv_N)|Z'|_1]$ satisfy (Λ27) and (Λ17′). Assume (Λ26), $c_1\ge C_b$, $c_2\ge C_b$, and the base action and boundary coefficient inequalities used in Lemma II.7.8. No integrated witness bound is assumed.

Put $C_{\rm mark}=C_{\rm PE}K_cc_1(d,L)C_m+C_{\rm det}$ and $B_L=2L^{d-2}$. If
$$\frac{\beta_1}{\beta_0}\le B_L,\qquad
\beta_0\ge\max\big\{1,\big(2C_{\rm mark}B_L^{m+1}\big)^2\big\},\qquad
\kappa_b\ge\tfrac32\kappa, \tag{4.2}$$
then the conclusion of Proposition II.7.9 holds, including
$$|\mathcal R_m^{(1)}(Y)|
\le\tfrac12\beta_1^{-m-1}
e^{-\kappa_b d^{\rm cov}_1(Y\bmod\Omega_1^c)}
\quad\text{for every allowed }Y, \tag{4.3}$$
and the base data are admissible for the LF Def-7 base case and the $k=0$ flow step.

*Proof.* CT and Lemma 2.2 delete exactly the old factors that read integrated spins. PE supplies a fluctuation cutoff fixed in the real integration coordinates; LC and the corrected fixed-contour argument of LF-BASE-KF0 (A.2) then give its holomorphic chart integral on H7. The landed chord identity and chart-integral identity give the exact real transformed integrand with its vacuum factor; PHYS asserts the needed matching of the localized version to (II.7.1). Apply the landed marked_cubes_explicit to PE. BASE-KERNEL-3.md Lemma 3.1 sums over marks, uses LabelAct.entropy, and loses one unit from $\kappa'$ to $\kappa_b$. Its two-mark version supplies the connected response where PE invokes it. The determinant bound in (4.1) gives the combined coefficient $C_{\rm mark}\beta_0^{-m-3/2}e^{-\kappa_b d^{\rm cov}}$. The arithmetic of BASE-KERNEL-3.md Corollary 3.2 and (4.2) yield (4.3). RG supplies the ordinary and boundary coefficients with the required analytic class bounds and assigns inside domains to $b_0$ and crossing domains to $\mathcal B^{(1)}$. PHYS and the landed BaseSmallField.baseStepData_of_input give the encoded parts of (S0), (S1), (S4), while PHYS supplies the source-strength support and bound. For (S2), multiply the $P_1$ gains of BaseWitnessGain with the $Q_1,R_1,S_1$ gains of WG. With $A_3$ in (4.2b), charging a bond witness twice still leaves at least $2A_3(\log\beta_0)^{2p_0}$ per new cube. Sum the witness choices and integrate the remaining Gaussian, spin and output measures: (Λ17′) bounds the new-output shell by one, and (Λ27) bounds the choice count and polynomial prefactors by $e^{A_3(\log\beta_0)^{2p_0}}$ per cube. By (4.1b), the remaining volume factor and $e^{{\rm Re}\,b_0}$ cost at most $e^{C_b(\log\beta_0+1)|Z'|_1}$ for $\beta_0\ge1$; $c_1,c_2\ge C_b$ give exactly (II.7.5) with exponent $-\kappa^{(0)}(Z')$. The BaseS5 field of PHYS gives (S5); no invocation of the bare BaseS5 predicate proves it. The physical equality and these clauses are exactly the data consumed by Theorem II.7.10 and the $k=0$ instance of I-7. $\square$

The proof is an **assembly under explicit hypotheses**. In particular PE, RG and PHYS contain model-specific facts not established by the cited Lean files. The zero-input counterexample shows why PHYS is necessary. Neither this proposition nor BASE-KERNEL-3.md provides an unconditional replacement for LF-RECONSTRUCTION Proposition II.7.9.

## 5. Lean lemma list in dependency order

The names below are suggested declarations, not assertions that they exist.

| Order | Declaration | Input and conclusion | Status |
|---|---|---|---|
| 1 | baseTestFootprint, baseJPlus | Define $F(c)$ and $\mathcal J_+$ with both bond endpoints and all block sites | New definitions |
| 2 | basePFactor_disjoint_integrated | BaseHistory.base_P_nbhd_compl/base_bond_comp imply every failed $P_1$ factor reads retained sites | Geometry proof from landed results |
| 3 | baseCutoffMargin_on_JPlus | Actual output $\chi_1$, fluctuation cutoff and background imply (2.6) on all $F(c)$, including $\partial\Omega''_1$ | **Open**; no landed provider |
| 4 | baseCutoffTransfer | Apply chiPrimeZero_eq_one_iff and Lemma 2.2 to remove exactly $\mathcal J_+$ | Follows from 1--3 |
| 5 | baseOneLayerCutAligned, baseCutCoercive | Link the base record's $D$ and potential to Multiscale.cutOperator_isCoercive_min_sharp with (1.4) of BASE-KERNEL-3.md | New bridge; multiplier hypothesis open |
| 6 | baseDecCov_resolvent, baseDecCovSqrt_log | Nondegenerate base family; H7 discs, weighted comparison, exact core and torus lift | **Open** beyond BASE-KERNEL-3.md's narrow edge family |
| 7 | baseChartIntegral_real | Instantiate ChordQuadratic and ChartIntegral.lintegral_sphere_pi_eq_gaussian_sqrt on the full chart domain, then condition on $D_+$ without duplicating its determinant | Real identities landed; conditioning bridge new |
| 8 | baseActivity_LabelAct, baseMark_bound | Construct the actual product measure, activities and mark with (3.1)--(3.2) of BASE-KERNEL-3.md and (4.1) here | **Open** |
| 9 | baseMarkedCoeff_bound | Apply marked_cubes_explicit/marked_cubes_two and BASE-KERNEL-3.md Lemma 3.1; use (4.2) for the half-budget | Conditional combinatorics and arithmetic proved |
| 10 | baseRG_free, baseRG_complete | Solve the actual I-7 equations and H5 in the two regimes, with H7 and family bounds | **Open** |
| 11 | basePhysicalInput | Define $Kt,b_0$ from the real chart integral and prove equality with $\rho_1$ and the fields of BaseSmallFieldInput; prove BaseS5 in regime (A) | **Open**; BaseSmallFieldInput_nonempty is not a substitute |
| 12 | baseWitness_QRS, baseStep_bound | Supply WG, the $Q_1,R_1,S_1$ gains and the integrated (S2) estimate | **Open** for the physical $Kt$ |
| 13 | basePropII79 | Assemble 3--12 into Proposition II.7.9 and then the LF Def-7 base case | Conditional until the preceding open rows are filled |

The dependency order prevents a proof of the target from passing through BaseSmallFieldInput_nonempty: the physical equality is checked at row 11 before any representation or flow claim is made.
