# RAY-DOMAIN: the old-term domain on the fluctuation ray

**Status.** The unrestricted assertion requested in COMPLETE-STEP.md (1.5) is **OPEN** for the actual complete-background family. The corrected proposition below proves a mass-uniform, quantitative domain inclusion **conditional on two named physical bridges**: COMPLEX-RAY-CHART and LOCAL-PAIR-AGREEMENT. The proof after those inputs is a deduction from the displayed, landed domain theorems and elementary monotonicity. Neither P1 Lemma 3.2 nor P1 Lemma 3.6 supplies either bridge. All Lean paths below are under the read-only tree /home/scott/Balaban/Balaban. No Lean declaration named RayInDomain was found or added.

## 1. The source statement and the domain that must be used

Let the step be from level $k$ to $K=k+1$, with $k\geq1$. Write $\mu>0$ for the common fine-lattice **complete** mass, $m_K=\mu L^{2K}\leq1$, $\epsilon_+=\epsilon_K$, and $G_k=\mathrm{stepG}\ d\,L\,N_1\,m_1\,k\,\varrho$. For an old term born at $1\leq j\leq k$ on $X$, its generating set is $G_{j,X}=\mathrm{Tm.gs}\ j\ X$, and the domain in the landed Def-6 class is exactly

$$
\operatorname{XiDom}(G_{j,X},a,\mu,j,\epsilon_j;\Psi,h)
\quad\text{(SmallField/Def6Terms.lean:86--92).} \tag{1.1}
$$

The same $\mu$ occurs at every $j$ during this step: the ideal running mass in scale-$j$ units is $m_j=\mu L^{2j}$. This is the matching-mass convention stated in Def6Terms.lean:74--79, after Scheme A removes its current zero-mass branch. The $\Xi^c$ bound at birth level $j$ has a level-$j$ real-source norm clause, while its background union-domain witness remains at ambient top $K$ (Xi.lean:75--109,160--168). These are separate requirements.

The page image of P1, printed p. 124, Lemma 3.2 (3.22), gives the chain
$\Xi^c_K(1,\epsilon_K)\to\Xi^c_j(C_0L^{j-K},\epsilon_K)\subset\Psi^c_j(\sigma,\epsilon_K)\subset\widetilde\Psi^c_j(\delta,\epsilon_K)\subset\widetilde\Psi^c_j(\delta_0,\epsilon_0)\subset\Xi^c_j(1,\epsilon_j)$.
Its displayed conditions include the mass constraint $m_j\leq(\delta/\epsilon_K)^2$, $C_0L^{j-K}\leq\sigma$, $\epsilon_K\leq\delta\leq\delta_0$, $\epsilon_K\leq\epsilon_0$, $\delta/\epsilon_K\leq\delta_0/\epsilon_0$, and $\epsilon_0+K_1\delta_0\leq\epsilon_j$. This is an **unperturbed composition and radius budget**. The landed field-level version is xiC_compose_at/xiC_compose (SmallField/XiComposeField.lean:500--599), with $C_0=8d+12$, the mass-uniform $C_{\Xi1}=(4d+8)(2d+1)$, and explicit Precedes, ScaleGap and collar hypotheses. P1 printed pp. 132--133, (3.54)--(3.58) and Lemma 3.6, instead bound a **truncated slice extended by constants outside $X$**. The landed inPsiTildeC_slice and xiDom_slice (SmallField/PsiGeomSlice.lean:164,576) require a top-layer block union, constant $h'$, path diameter $Q$, and $(1+2|t|)Q\leq\delta_0/32$. A covariance square-root fluctuation is not that slice. The slice theorem can be used later for locality and Cauchy estimates of a term already evaluated on the ray.

There is also a level issue. The proved D1-j theorem xiC_subset_psiTildeCLevel (SmallField/XiLevelC.lean:111) concludes InPsiTildeCLevel with real norm clause $m_j|h_0^2-1|<\delta^2$; it does not conclude the top-$K$ InPsiTildeC required by the existing xiDom_of_psiTildeC (PsiGeomSlice.lean:440). Applying the latter to an arbitrary old $j<K$ datum silently changes the mass in that clause. The corrected proof below bypasses this invalid application: it retains the upper datum's stronger top-$K$ norm witness until after the perturbation. A fixed unit real witness $h_0$ is a simpler special case (Def6BridgeDomain.lean:40--49, xiC_level_irrel), but the corrected proposition does not require it.

## 2. Quantitative corrected ray proposition

Use the landed constants $C_0=\mathrm{scaledC0}\ d=8d+12$, $C_1=\mathrm{xiC1}\ d=(4d+8)(2d+1)$, $K'_2=\mathrm{xiK2}\ d\,L\,N=1+L+2dL^2+(N+1)\mathrm{cK2}\ d\,L\,N$, $K_1=\mathrm{bgK1}\ d\,L\,N$, $c_i=\mathrm{bgC}i\ d\,L\,N$, and $\delta_*=\mathrm{deltaStar}\ d\,L\,N$. Set $A_d=(4d+6)(2d+1)$. Assume $L\geq C_0$, $\beta_U>0$, $p_1>0$, $B_{\rm ray}>0$, $\epsilon_+<\epsilon_k\leq\epsilon_j$ for all $j\leq k$, and put

$$
\tau_k=\frac{\epsilon_k-\epsilon_+}{2}>0,\qquad
t=B_{\rm ray}\,\beta_U^{-1/2}p_1,\qquad D=2t,\qquad
\epsilon_*=\epsilon_+ + K'_2D. \tag{2.1}
$$

Here $\beta_U$ is StepSetting.betaU (StepObjects.lean:286--291). For the landed real StepSetting one may use $B_{\rm ray}=B_5$ from Lemma 2.5, because its proof bounds the lifted shift by $B_5\beta_U^{-1/2}p_1$ (Lemma25.lean:498--529). For a complex step chart, a sufficient choice is $B_{\rm ray}=\sqrt N\,\mathrm{covSupConstC}(d,L,N,a_k,0)$, provided the actual complex covariance datum lies in the DecDom of decCovSqrt_supNorm (CovSqrtSupComplexDec.lean:32--47). In either case the **needed assertion** is a bound on the *actual* layer-constant shift $V(\widehat\psi)$:
$\sup_{z\in\mathrm{dataSites}(G_k)}\operatorname{vn}V(\widehat\psi)(z)\leq t$ for every $\|\widehat\psi\|_\infty<p_1$, uniformly over the allowed upper data. At complex $s$ with $|s|<2$, its increment is bounded by $D$.

Assume the following strict numerical reserve, fixed before the small-mass family is varied:

$$
\begin{gathered}
A_d\epsilon_+\leq1,\quad C_1\epsilon_+\leq\mathrm{thm73C1},\quad
K_1C_1\epsilon_+\leq\delta_*,\\
0<D\leq1,\quad D\leq\delta_*,\quad
C_1\epsilon_++5D\leq c_1,\quad
K_1C_1\epsilon_+ +(\mathrm{cK2})D<c_0,\\
K'_2D\leq\tau_k,\quad A_d\epsilon_*\leq1,\quad
C_1\epsilon_*\leq\mathrm{thm73C1}.
\end{gathered} \tag{2.2}
$$

A useful uniform choice is $D$ less than the minimum of the positive differences in (2.2), divided by their displayed coefficients. All quantities in that minimum depend on $d,L,N,a_k,\epsilon_+,\epsilon_k$ and fixed background margins, **not on a positive lower bound for $\mu$**. The sequence GapE (SmallField/Xi.lean:174--180), when chosen with $q=L^{-\alpha}<1$, gives $\epsilon_+\leq q\epsilon_k$ and hence $\tau_k\geq(1-q)\epsilon_k/2$. The strict positivity of the other differences in (2.2) remains a numerical class choice and must be checked.

For every old support $X$, assume that $G_{j,X}$ and $G_k$ have BgHyp at ambient top $K$ with the same $\mu$ and one coefficient sequence $a$ that agrees exactly with the sequence in the old term's XiDom (in the ideal flow, both are the same compWeight sequence); $G_{j,X}\prec G_k$, ScaleGap at $\theta_j=L^{j-k}$, and the collar hypothesis of xiC_compose_at hold. Assume also the corresponding hypotheses for $G_k\prec G'$ at $\theta_0=L^{-1}$. These are the **GEOM-RAY** hypotheses. The landed Def-6 gs_spec (Def6.lean:205--207) gives $X\subset\Omega_1(G_{j,X})$ and no active layer above $j$, but by itself does not state every Precedes, ScaleGap, collar or BgHyp clause.

Let the complex upper data have a witness
$\Xi^c_K(G';1,\epsilon_+)$, with its top-$K$ real-source norm bound. For $|s|<2$, put $D_k(s)=D_k(0)+sV(\widehat\psi)$ in the **spin coordinate**, keeping the source fixed, and let $P_{j,X}(s)$ be the pair obtained by composing its complex BG solution from $G_k$ to $G_{j,X}$. The conclusion, in exact landed carriers, is

$$
P_{j,X}(s)\in
\operatorname{XiDom}(G_{j,X},a,\mu,j,\epsilon_j-\tau_k)
\subset \operatorname{XiDom}(G_{j,X},a,\mu,j,\epsilon_j),
\quad 1\leq j\leq k,\quad |s|<2. \tag{2.3}
$$

For $j=k$, take the level-$k$ datum directly and omit the second composition. Since $C_0L^{j-k}\leq C_0/L\leq1$ only for $j\leq k-1$, using the second composition at $j=k$ would consume a false factor $C_0$. Formula (2.3) has the **explicit mass-independent radius reserve** $\tau_k$; the radius is a fixed fraction of $\epsilon_k$ when GapE holds. It is a statement about the *local representative* $P_{j,X}$. To apply it to the actual terms in EcompAt/McompAt, LOCAL-PAIR-AGREEMENT below is required.

### Proof of the corrected proposition under its stated hypotheses

1. Apply xiC_compose_at to the upper $\Xi^c_K(G';1,\epsilon_+)$ witness and $G_k\prec G'$. It gives $\Xi^c_k(G_k;\sigma_0,\epsilon_+)$ with $\sigma_0=C_0/L\leq1$, the composed real and complex data, their BG union-domain witnesses, and restriction identities for their background fields and multipliers. Enlarge $\sigma_0$ to $1$ in XiBounds and XiCBounds. Each gradient and collar bound grows with $\sigma$, each Laplacian, multiplier, closeness, source and real norm bound grows with $\sigma^2$, while the complex field-value bound is independent of $\sigma$. This gives $\Xi^c_k(G_k;1,\epsilon_+)$.

2. The previous datum must be viewed at ambient level $K$ to use the *landed* xiC_perturb, whose conclusion is $\Xi^c_K$. The only XiC field involving the level argument is XiBounds.hnorm (Xi.lean:75--94). Replace the weaker level-$k$ hnorm field of the composed witness by the **upper input's** level-$K$ hnorm field, which is $m_K|h_0^2-1|<\epsilon_+^2$. Composition preserves the same constant real $h_0$. All other fields and the BG union-domain witness are unchanged. Thus $\Xi^c_K(G_k;1,\epsilon_+)$ follows even for nonunit $h_0$. This is the new elementary lemma xiC_compose_keep_top_hnorm. It is stronger than the invalid inference $\Xi^c_k\Rightarrow\Xi^c_K$.

3. The shift is layer constant on $G_k$: for the real landed path this follows from fluctPsi_layerConst (Lemma25Real.lean:269--288); for a complex covariance matrix the same conclusion follows from lifting its block variable to unit blocks, after COMPLEX-RAY-CHART identifies that lift. For every $|s|<2$, the data-site norm of $sV$ is at most $D$. Apply the **proved** xiC_perturb (SmallField/XiPerturb.lean:216--224) with $\epsilon'=\epsilon_+$, $\delta_3=D$, ambient index $K$, and precisely the first two lines of (2.2). Its conclusion is $\Xi^c_K(G_k;1,\epsilon_*)$, including the complex BG union-domain witness. In particular no division by $\mu$ appears. Prop33CloseDomain.lean:43,140 and Prop33CloseReal.lean:43 supply a separate perturbation-to-InUnionDomainC check on a complex disc; they do not replace the XiCBounds conclusion of xiC_perturb.

4. Since $j\leq k<K$, positivity of $\mu$ implies $m_j\leq m_K$. Thus the level-$K$ hnorm bound also gives the level-$k$ one; all other fields are identical, so $\Xi^c_k(G_k;1,\epsilon_*)$. The exact gap calculation is $\epsilon_*+\tau_k=\epsilon_++K'_2D+\tau_k\leq\epsilon_++2\tau_k=\epsilon_k\leq\epsilon_j$. If $j=k$, enlarge its radius from $\epsilon_*$ to $\epsilon_k-\tau_k$ to obtain (2.3). If $j<k$, apply xiC_compose_at again with $G_{j,X}\prec G_k$, $\theta_j=L^{j-k}$, and the last line of (2.2). It gives $\Xi^c_j(G_{j,X};C_0\theta_j,\epsilon_*)$. Because $C_0\theta_j\leq1$, enlarge the scale parameter to $1$, then the radius to $\epsilon_j-\tau_k$. The required monotonicity is a field-by-field comparison of XiBounds and XiCBounds; XiBounds_mono (XiPerturb.lean:125) proves its real-radius part, while the complex part and the scale-parameter part are new short lemmas. The BG union-domain witnesses are unchanged under this enlargement. Packaging the real/complex witnesses gives (2.3) by the definition of XiDom. The inclusions use only $0<\mu$ and $m_K\leq1$, never $1/\mu$.

The proof has a fixed complex $s$-disc. A Cauchy circle of radius $1/2$ about every $s\in[0,1]$ is inside $|s|<2$, so an old term bounded by $M_X$ throughout (2.3) has $|\partial_s E_{j,X}|\leq2M_X$; the same holds for the observable term with $\|g\|_1<1$. This is the needed **ray** regularity once LOCAL-PAIR-AGREEMENT identifies the evaluation, for source tests with $\|g\|_1<1$. The landed ClassRegular structure is parameterized by an arbitrary $g$; Def-6 alone gives no such conclusion outside its source ball. Block-direction regularity requires the same estimate with $V$ replaced by $V+u$, $\|u\|_\infty$ small enough to preserve $D$; that is a separate multivariate chart check for ClassRegularLoc. The strict inclusion in (2.3) alone does not prove a uniform open source neighbourhood for $h$.

## 3. The physical bridges still open

**COMPLEX-RAY-CHART.** The landed StepSetting (Fluctuation/StepObjects.lean:237--253,294--305) has a real datum $D'$, a real constant $h_0$, and a real-linear covariance map $K$ made from the real part of its square root. Lemma25_field (Lemma25Real.lean:289) proves the **real endpoint** cutoff identity under $\chi_{k+1,u}=1$, $p_1/(\sqrt{\beta_U}\delta)\leq(3B_5K_2)^{-1}$, and $B_5\beta_U^{-1/2}p_1\leq\mathrm{fluctRadius}$. Its proof extends along real $s\in[0,1]$ by chiFl_smul (StepIdentity.lean:1072), but it does not provide a complex upper-data chart or a complex $s$-disc. The theorem decCovSqrt_supNorm supplies $B_{\rm ray}$ **if** the actual upper complex background/multiplier/decoupling tuple lies in its DecDom on one open neighbourhood and its square-root map agrees with the physical complex continuation of $K$. One must verify that membership, the covariance branch and its analyticity, and the common data-site bound $t$ for all allowed complex data. The required bound is quantitative and independent of a positive lower mass; none of the cited declarations maps every Def-6 datum into this covariance DecDom.

**LOCAL-PAIR-AGREEMENT.** EcompAt and McompAt (StepObjects.lean:60--96) evaluate a term at composedPairAt from the **whole-level** set levelGS $j$; the class analyticity hypothesis instead uses $G_{j,X}=\mathrm{Tm.gs}\ j\ X$ (Def6.lean:208--216). The direct output of xiC_compose_at on $G_{j,X}$ is zero outside that local set, whereas the whole-level field need not be. The right proposition is agreement **on $X$** of the two composed spin/source pairs, followed by Terms.localE/localM (Def6.lean:255--263), not a global equality of their raw fields. Its proof has to show on $X$ that the local and whole-level layer indices and block means in composeField (Background/Composition.lean:171--181) agree, and that the two BG solutions restrict to the same local solution on the common collar. Theorem 7.3's restriction identities appear in xiC_compose_at, but the actual $G_{j,X}$-to-levelGS $j$ agreement and the needed common-collar geometry are not fields of gs_spec. The insufficiency of gs_spec is literal: when $j=2$, choosing $G_{2,X}=\mathrm{levelGS}(1)$ for a nonempty level-2 polymer $X$ satisfies its two displayed fields ($X\subset\Omega_1$ and no layers above 2), yet on $X$ the local composeField uses the level-1 block mean while composedPairAt uses the level-2 block mean. For a nonconstant background these need not agree. Thus one needs an additional layer/block identification or a different local set. For $j=k$, the same issue is restriction of the level-$k$ field to $G_{k,X}$. If these agreements fail at a boundary, enlarge the local generating set to a cube/halo containing every site read on $X$, prove the agreement there, and pay its covering cost before applying localE/localM. Do not assert (2.3) for the unmodified global pair merely from the local XiC theorem.

**RADIUS-AND-GEOMETRY.** P4 H1 gives a decreasing $\epsilon_j$, and the positive reserve in (2.1) follows from a strict GapE. It does not alone establish every inequality in (2.2), nor the common BgHyp/Precedes/ScaleGap/collar family GEOM-RAY for every $X$. Those fixed choices are the exact numerical/geometric inputs to prove once for the physical class. If $L<C_0$, the second composition at $j=k-1$ has $C_0/L>1$, and the simple enlargement argument fails. The corrected hypothesis is either $L\geq C_0$ or a direct XiC bound at $j=k-1$ with a larger radius budget $\max(\sigma,\sigma^2)\epsilon_*\leq\epsilon_{k-1}-\tau_k$, including its unchanged value bound. If $\epsilon_+\geq\epsilon_k$, the top $j=k$ case has no positive radius reserve from this argument.

Consequently the full RayInDomain for the actual wide complex class remains **OPEN** at COMPLEX-RAY-CHART and LOCAL-PAIR-AGREEMENT, with RADIUS-AND-GEOMETRY to be checked. The corrected proposition (2.3) is **PROVED CONDITIONAL ON THOSE NAMED INPUTS**. Its output is sufficient for the ray part of ClassRegular on the Def-6 source ball; it does not by itself close ClassRegular for arbitrary $g$, ClassRegularLoc, or ClassRegularObs.

## 4. Lean lemma list in dependency order

These are **new targets**, not claims that the named declarations exist.

1. xiC_mono_sigma_epsilon: if $0<\sigma\leq\sigma'$, $0<\epsilon\leq\epsilon'$, and the existing witnesses give XiC at $(\sigma,\epsilon)$, then they give XiC at $(\sigma',\epsilon')$; prove the hAbs comparison $\sigma^2\epsilon\leq{\sigma'}^2\epsilon'$ and the hDot comparison $(\sigma\epsilon)^2\leq(\sigma'\epsilon')^2$ explicitly.
2. xiC_level_down: for $\mu\geq0$, $j\leq n$, a XiC witness at level $n$ gives one at level $j$ with the **same** radius; only XiBounds.hnorm changes.
3. xiC_compose_keep_top_hnorm: use xiC_compose_at for $G_k\prec G'$, xiC_mono_sigma_epsilon with $C_0/L\leq1$, and the upper XiBounds.hnorm to produce $\Xi^c_K(G_k;1,\epsilon_+)$. Do not use xiC_level_irrel unless $h_0$ is unit.
4. ray_shift_bound_complex: construct the actual complex covariance chart and prove layer constancy and $\operatorname{vn}V\leq B_{\rm ray}\beta_U^{-1/2}p_1$ on dataSites $G_k$, using decCovSqrt_supNorm after its DecDom hypotheses. The landed real specialization uses Lemma25/Lemma25Real.
5. ray_lower_xiC: apply xiC_perturb to the datum of item 3 for $|s|<2$, under (2.2), and obtain $\Xi^c_K(G_k;1,\epsilon_*)$.
6. ray_old_local_xiDom: use xiC_level_down, xiC_compose_at for each $G_{j,X}\prec G_k$ when $j<k$, and xiC_mono_sigma_epsilon to produce (2.3). Check GEOM-RAY and the $j=k$ branch separately.
7. ray_local_pair_agreement: prove the equality on $X$ between the local pair of item 6 and composedPairAt, with its collar/halo hypothesis; then apply localE/localM. This is the exact term-facing RayInDomain statement.
8. ray_class_regular: compose the class's AnalyticOnNhd and bounds with the item-7 map, use the $|s|<2$ Cauchy circle, and sum the finite old terms. For ClassRegularLoc and ClassRegularObs, add a block-direction tube and componentwise observable Cauchy bounds.

The first proof task for the physical family is item 4 together with GEOM-RAY; the term-facing task is item 7. P1 Lemma 3.6 and the landed xiDom_slice belong to later local slicing and do not discharge either task.

