# RAY-CHART: the complex covariance chart and the interpolation disc

**Status.** The covariance chart below is **PROVED CONDITIONAL ON EXPLICIT LANDED INPUTS**: the complete-background `FlCore` hypotheses, the strict margins (2.1), and the covariance smallness hypotheses (2.2). The real restriction and the mass-uniform sup bound are then deductions from landed theorems. The full assertion that *every* datum of the physical Def-6 class meets those numerical hypotheses is **OPEN**; Def-6 `IsSF` does not contain `FlCore` or the covariance margins. The complex ray in the old-term domain is **PROVED CONDITIONAL ON** the numerical and geometric assumptions in §4 and, for the actual old term, **LOCAL-PAIR-AGREEMENT**. The latter is being handled separately. No new Lean theorem is claimed here. All cited Lean files are in the read-only `/home/scott/Balaban/Balaban` tree.

Let $K=k+1$, $k\ge1$, $N\ge1$, $G'=\mathfrak B_{K}$, and $G_k=\mathrm{stepG}\,d\,L\,N_1\,m_1\,k\,\varrho$. The mass is the **complete** mass $\mu>0$, with $m_K=\mu L^{2K}\le1$. Use Scheme A, so the same $\mu$ and $a=\mathrm{compWeight}\,L\,a_1$ occur in the upper datum, the lower background, and the covariance. Write $\epsilon_+=\epsilon_K$. The shorthand $D\in\Xi^c_K(G';1,\epsilon_+)$ means the exact landed proposition `XiCData G' a μ K 1 ε+ D` (`Localization/I5Chain.lean:73–80`). The covariance decoupling parameter will be denoted $\lambda$; the independent interpolation variable of the fluctuation ray will be $z$. This prevents the two occurrences of $s$ in the source notes from being conflated.

## 1. The actual chart, and the result already landed

The landed `DecDom G' N κ δc` is an **open** subset of `DecData G' N` consisting of triples $e=(\lambda,\phi_0,\alpha_0)$ satisfying, strictly,

$$
 |\lambda_P|<e^\kappa\quad(P\in\mathrm{cubeIdx}(G')),\qquad
 \operatorname{IsConstraintFieldStrict}(G',\delta_c,\phi_0),\qquad
 |\alpha_0(w)|<\frac{\operatorname{coerciveConst}(d)}{2\ell(w)^2}\quad(w\in\Omega_1(G')). \tag{1.1}
$$

These are precisely `DecoupledCovAnalyticFull.lean:42–62,105–141`, including `isOpen_decDom`. The field in this chart is **not** merely the interior solution $\phi$: it is $\bar\phi=\mathrm{barField}\,G'\,D.\Psi\,\phi$, equal to the solution on $\Omega_1(G')$ and to the datum outside. The latter distinction is needed for the strict gradient and Laplacian inequalities.

For every $D\in\Xi^c_K(G';1,\epsilon_+)$, let $(\phi_D(\lambda),\alpha_D(\lambda))$ be the unique `IsDecBg` solution of I-4b at $\lambda$. Its existence and uniqueness follow from `DecoupledBackground.lean:i4b_exists_unique`, **provided** the hypotheses of `FlCore` hold. Define

$$
 e_D(\lambda)=\bigl(\lambda,\bar\phi_D(\lambda),\alpha_D(\lambda)\bigr),\qquad
 \mathcal K_D(\lambda)=\operatorname{decCovSqrt}
 (G',a,a_1,\mu,\alpha_D(\lambda),\operatorname{extS}(\lambda),
 \bar\phi_D(\lambda),\operatorname{unitQ}(G'),\operatorname{unitP}(G')). \tag{1.2}
$$

Here `extS G' λ` is the full parameter field that equals $\lambda$ on the parameter cubes and $1$ elsewhere. In particular, `extS G' (fun _ => 1)` is identically $1$. The matrix in (1.2) is the **same integral definition** `DecoupledSqrt.lean:216–224`; no choice of a new matrix square-root branch is made.

Fix $c,BG,\kappa,K_c,C_x,c_2,BG_2,\delta_1$ for which

$$
 \operatorname{FlCore}(N,G',H_m,a_1,\mu,c,BG,\kappa,\epsilon_+,K_c,C_x,c_2,BG_2,\delta_1)
 \tag{2.0}
$$

holds (`InteractionEngine.lean:45–70`). This includes the upper `BgHyp` and $m_K\le1$, the `DGSetting`, $0<\kappa$, the I-4b decay-volume inequality, $0<\epsilon_+$, $(4d+6)(2d+1)\epsilon_+\le1$, $\mathrm{xiC1}(d)\epsilon_+\le c_7$, and the fluctuation-engine hypotheses. The covariance result needs the following additional **strict** choices:

$$
 \operatorname{decDomMargin}(d,L,N,BG,\kappa,\mathrm{xiC1}(d)\epsilon_+)<\delta_c,
 \qquad
 K_4(d,L,N,BG,\kappa)\,\mathrm{xiC1}(d)\epsilon_+
 <\tfrac12\operatorname{coerciveConst}(d). \tag{2.1}
$$

For analyticity and the uniform covariance estimate also require

$$
 0\le\delta_c,\qquad
 \delta_c^2\operatorname{smallConstX}(d,L,\kappa)\le\tfrac14,
 \qquad
 \operatorname{cstarX}(d,L)e^{\operatorname{N0}(d,L)\kappa}\le L^{m_1}.
 \tag{2.2}
$$

Here is an explicit sufficient fixed-margin choice. Put $S_X=\operatorname{smallConstX}(d,L,\kappa)>0$, $C=K_4(d,L,N,BG,\kappa)>0$, $C_1=\operatorname{xiC1}(d)>0$, and $\gamma_c=\operatorname{coerciveConst}(d)>0$. Choose $\delta_c=1/(4\sqrt{S_X})$, so $\delta_c^2S_X=1/16<1/4$. The definition `HatEngineDom.lean:33–36` gives, with $u=C_1\epsilon_+$,

$$\operatorname{decDomMargin}(d,L,N,BG,\kappa,u)
=(3C+2)u+(C^2+6C)u^2.
\tag{2.4}$$

Consequently the explicit inequalities

$$0<u\le1,\qquad (C^2+9C+2)u<\delta_c,\qquad Cu<\gamma_c/2 \tag{2.5}$$

imply both strict margins (2.1): the quadratic term in (2.4) is at most $(C^2+6C)u$, so the first inequality follows, and the last inequality is exactly the multiplier margin. These choices are independent of a positive lower bound on $\mu$. The class still has to meet (2.5), the separate volume inequality in (2.2), and the `FlCore` hypotheses. The `FlCore.hM` bound uses its own constant $c$; the last inequality in (2.2) is a distinct covariance hypothesis.

**Proposition (complex upper-data chart, conditional on (2.0)–(2.2)).** For every complex $D\in\Xi^c_K(G';1,\epsilon_+)$ and every $\lambda$ with 

$$|\lambda_P|<e^\kappa\quad\text{for all parameter cubes }P, \tag{2.3}$$

the point $e_D(\lambda)$ lies in `DecDom G' N κ δc`. Every entry of $\mathcal K_D(\lambda)$ is analytic on a neighbourhood of the pair $(\lambda,\operatorname{rawOf}D)$. Thus the chart holds **for all** complex upper data in the displayed $\Xi^c$ domain, with the *same* margins $\delta_c,\kappa$.

**Proof.** `I5Chain.lean:137–145`, `xiCData_inDomainC`, puts $D$ in `InDomainC G' μ (xiC1 d * ε+) (xiC1 d * ε+)`, using `FlCore.small1` and `FlCore.HBp`. `i4b_exists_unique` supplies `IsDecBg` for (2.3); `HatEngineDom.lean:137–165`, `decDom_of_isDecBg`, then gives exactly $e_D(\lambda)\in\mathrm{DecDom}$ from (2.1). Its proof first obtains the bound `BgBounds ... (K4 * xiC1 * ε+)` and then verifies each inequality in (1.1); it also uses $m_K\le1$ to meet I-4b's mass condition. `HatEngineDom.lean:170–179`, `xSetting_of_flCore`, gives `XSetting G' a a1 μ` because $k\ge1$. With (2.2), `DecoupledCovAnalyticFull.lean:252–292`, `analyticOnNhd_decCovSqrt_entry`, applies to every matrix entry on the open `DecDom`.

For analyticity **in the upper data**, `DecoupledBackground.lean:473–535`, `i4b_analytic`, provides one analytic map $F(\lambda,\operatorname{rawOf}D)=(\phi_D(\lambda),\alpha_D(\lambda))$ on a neighbourhood of each allowed point. Its domain is the I-4b union domain with $c_1=c_7$, and the preceding `xiCData_inDomainC` plus `FlCore.c7le` place all our points there. The map $(\lambda,D)\mapsto e_D(\lambda)$ is analytic at each such point: coordinatewise, `barField` combines the linear raw-data coordinate $D.\Psi$ with the analytic interior field $F_1$, and the multiplier is $F_2$. Since `DecDom` is open and contains that point, continuity gives a neighbourhood on which the composite is in `DecDom`; composition with `analyticOnNhd_decCovSqrt_entry` proves the claim. The neighbourhood may depend on $D$, as is appropriate for `AnalyticOnNhd`. A **single uniform open tube** around the entire $\Xi^c$ set does not follow from pointwise strictness and is not asserted. ∎

## 2. Real restriction and mass-uniform norm

Suppose $D'=S.D'$ is a real upper datum for a `StepSetting S` with $S.G'=G'$, $S.a_1=a_1$, $S.\nu=\mu$, and $D'\in\Xi^c_K(G';1,\epsilon_+)$. For the real comparison also assume $D'\in\operatorname{InUnionDomainR}(G',\operatorname{bgC1},\mu)$, as in the landed real step. Put $\lambda\equiv1$. Since $\kappa>0$, (2.3) holds. `DecoupledBackground.lean:i4b_one` identifies $(\phi_{D'}(1),\alpha_{D'}(1))$ with $(\operatorname{bgFieldC}D',\operatorname{bgMultC}D')$. `Background/Def5.lean:253–271`, `theorem72_real`, identifies the latter pair with $(\operatorname{bgField}D',\operatorname{bgMult}D')$. On $\Omega_1(G')$, `barField G' D'.Ψ φ` equals $\phi$; therefore `restrictField G' (barField ...)` equals `restrictField G' (svec G' φ)`. The covariance formula reads the field through `restrictField G'` (`DecoupledCovariance.lean:57–69`), so this equality and `extS G' 1=1` give, **by the same integral formula**,

$$\mathcal K_{D'}(1)=S.\operatorname{covSqrt}. \tag{3.1}$$

The right side is defined in `StepObjects.lean:289–292`. Under the real step's positivity hypotheses `StepIdentity.lean:315`, `covSqrt_isReal` says its entries are real. For a real fluctuation $\widehat\psi$, `HatEngineLift.lean:104–120`, `liftC_hatField_covSqrt`, then gives

$$\operatorname{liftC}\bigl(\beta_U^{-1/2}\mathcal K_{D'}(1)\widehat\psi\bigr)
=\bigl(\operatorname{liftU}(S.\operatorname{shiftU}\widehat\psi)\bigr)_{\mathbb C}. \tag{3.2}$$

Thus (1.2) is an analytic continuation of the **actual** real `StepSetting.K` substitution. The real-linear `K` itself is `covSqrt.map Complex.re` (`StepObjects.lean:300–304`); applying `Complex.re` at complex data would destroy analyticity. Equation (3.1), followed by the real-entry result and (3.2), is the correct comparison.

For every complex chart point and every $v:S.U\times[N]\to\mathbb C$ with $|v(q,i)|\le p_1$, `Fluctuation/CovSqrtSupComplexDec.lean:32–47`, `decCovSqrt_supNorm`, applied with `xSetting_of_flCore`, (2.2), and $c=p_1\ge0$, gives

$$ |(\mathcal K_D(\lambda)v)(q,i)|\le M_Cp_1,
 \qquad M_C=\operatorname{covSupConstC}(d,L,N,a(k),\kappa). \tag{3.3}$$

By the finite-dimensional Euclidean inequality $\operatorname{vn}(w)\le\sqrt N\max_i|w_i|$, the complex fluctuation field

$$ V_D(\widehat\psi)=\operatorname{liftC}\bigl(\beta_U^{-1/2}\mathcal K_D(1)\widehat\psi\bigr) \tag{3.4}$$

satisfies on **every** site, hence on `dataSites Gk`, 

$$\operatorname{vn}V_D(\widehat\psi)(x)\le t,
\qquad t=B_{\rm ray}\beta_U^{-1/2}p_1,
\qquad B_{\rm ray}=\sqrt N\,M_C, \tag{3.5}$$

provided $\beta_U>0$ and $\max_{q,i}|\widehat\psi(q,i)|<p_1$. `liftC` is constant on each unit block (`HatEngineLift.lean:63–76`), so this is the layer-constant shift required by `xiC_perturb`. The bound is uniform for $0<\mu L^{2K}\le1$: its displayed constant depends on $d,L,N,a(k),\kappa$, while the mass occurs only among the hypotheses establishing membership and `XSetting`. Uniformity requires those hypotheses to hold with the **same** chosen margins for the family. It says nothing about the limiting zero-mass covariance unless a separate limit theorem is used.

## 3. The complex interpolation disc

Fix an upper complex datum $D$ and $\widehat\psi$ as above. The covariance chart is constant in $z$; define the *old-spin* ray on $G_k$ by `perturbData Gk Dk(0) (z • V_D ψ̂) hconst`, where `hconst` is the `IsLayerConstant` witness from `isLayerConstant_liftC`. On `dataSites Gk` its fields satisfy

$$D_k(z).\Psi=D_k(0).\Psi+zV_D(\widehat\psi),\qquad D_k(z).h=D_k(0).h,
\qquad |z|<R,\quad R>1. \tag{4.1}$$

For the useful choice $R=2$, set $D_{\rm ray}=2t$. Then (3.5) gives $\|zV_D\|_{\mathrm{dataSites}(G_k)}\le D_{\rm ray}$ on $|z|<2$. This is a polynomial, hence analytic, map of $z$; the upper-data dependence is analytic by §1. **For a real upper datum and real $0\le z\le1$**, its spin coordinates agree with `S.psiAt z` by (3.2). `Lemma25Real.lean:289–324`, `lemma25_field`, and `StepIdentity.lean:1072–1080`, `chiFl_smul`, cover only the real ray and the real cutoff; the complex assertion follows from the chart plus `xiC_perturb`, as follows.

Assume the level-$k$ base datum $D_k(0)$ has `XiCData Gk a μ K 1 εbase`, including the **top-$K$** real-source norm witness, and the numerical hypotheses of `SmallField/XiPerturb.lean:216–224`, `xiC_perturb`, hold with input radius $\epsilon_{\rm base}$ and shift bound $D_{\rm ray}$. In particular the fixed smallness bounds on $D_{\rm ray}$, $\mathrm{xiC1}(d)\epsilon_{\rm base}+5D_{\rm ray}$, and $\mathrm{bgK1}\,\mathrm{xiC1}(d)\epsilon_{\rm base}+\mathrm{cK2}D_{\rm ray}$ must be checked (the full list is in `RAY-DOMAIN.md` (2.2), with $\epsilon_+$ replaced by $\epsilon_{\rm base}$). Then the landed perturbation theorem gives

$$ D_k(z)\in\Xi^c_K(G_k;1,\epsilon_{\rm ray}),\qquad
\epsilon_{\rm ray}=\epsilon_{\rm base}+\operatorname{xiK2}(d,L,N)D_{\rm ray},
\quad |z|<2. \tag{4.2}$$

The proof is pointwise in $z$: layer constancy comes from `liftC`, the norm is strictly below $D_{\rm ray}$, and all perturbation hypotheses are uniform in $z$. The same argument works for $R>1$ with $D_{\rm ray}=Rt$. Every Cauchy circle $|z-z_0|=1/2$, $z_0\in[0,1]$, is contained in $|z|<2$. This supplies a common complex disc for differentiating old terms after the local-domain inclusion of §4. No holomorphic continuation of the characteristic function $\chi_{\rm fl}$ is needed or claimed.

For the actual complete-background step, the base hypothesis of (4.2) is obtained from the upper $\Xi^c_K(G';1,\epsilon_+)$ witness by `xiC_compose_at`, enlargement of its scale parameter, and preservation of the **upper top-(K) hnorm witness**; that last preservation is an elementary new lemma, as explained in `RAY-DOMAIN.md` §2, steps 1–2. Its radius is subject to the correction in §4 below. The same correction must be made before invoking the numerical list of `RAY-DOMAIN.md`.

## 4. Corrected radius and geometry budget

Put $C_0=\operatorname{scaledC0}(d)=8d+12$. The first application of `SmallField/XiComposeField.lean:500`, `xiC_compose_at`, from $G'$ at level $K$ to $G_k$ at level $k$, has scale parameter $\sigma_0=C_0/L$. For $\sigma_0\le1$, elementary monotonicity gives a radius $\epsilon_{\rm base}=\epsilon_+$ at scale parameter $1$. For $\sigma_0\ge1$, the **landed** `Localization/I5Xi.lean:83`, `xiC_scale`, gives radius $\sigma_0^2\epsilon_+$ at scale parameter $1$. Thus a common formula is

$$ r_0=\max\{1,(C_0/L)^2\},\qquad
\epsilon_{\rm base}=r_0\epsilon_+,\qquad
\epsilon_{\rm ray}=r_0\epsilon_++\operatorname{xiK2}(d,L,N)D_{\rm ray}. \tag{5.1}$$

The hnorm witness at level $K$ must be retained from the upper input before `xiC_perturb`; no implication $\Xi^c_k\Rightarrow\Xi^c_K$ is available for a nonunit $h_0$. The first composition additionally needs its exact `BgHyp`, `Precedes`, `ScaleGap`, and collar hypotheses. These are geometric inputs, not consequences of `IsSF.gs_spec` as currently landed.

For a local term born at $j<k$, the second composition $G_k\to G_{j,X}$ has $\sigma_j=C_0L^{j-k}$. Apply `xiC_scale` when $\sigma_j\ge1$, or enlarge $\sigma_j$ to $1$ when $\sigma_j\le1$. Its scale-one radius is

$$r_j\epsilon_{\rm ray},\qquad r_j=\max\{1,(C_0L^{j-k})^2\}. \tag{5.2}$$

At $j=k$ there is **no second composition**, so set $r_k=1$. For a fixed positive Cauchy reserve $\tau_j$, the exact sufficient budget for the old-term domain is

$$r_j\bigl(r_0\epsilon_++\operatorname{xiK2}(d,L,N)D_{\rm ray}\bigr)
 +\tau_j\le\epsilon_j,\qquad 1\le j\le k. \tag{5.3}$$

The simple choice $\tau_j=\tau_k=(\epsilon_k-\epsilon_+)/2$ of `RAY-DOMAIN.md` works when $L\ge C_0$ and its other inequalities hold. For $L<C_0$, it must be checked against (5.3); the old uncorrected inequality $\epsilon_++K_2'D_{\rm ray}+\tau_k\le\epsilon_k$ misses the factor $r_0$. All `xiC_perturb` smallness inequalities must likewise use $r_0\epsilon_+$ in place of $\epsilon_+$.

**Answer to RADIUS-AND-GEOMETRY.** $L\ge C_0$ is a sufficient condition for this two-composition proof. The direct `XiC` scaling theorem does **not** prove the needed radius inclusion for every $L\ge3$. At $j=k-1$, $r_{k-1}=r_0=\max\{1,(C_0/L)^2\}$; (5.3) becomes

$$ r_0\bigl(r_0\epsilon_++K_2'D_{\rm ray}\bigr)+\tau_{k-1}\le\epsilon_{k-1}. \tag{5.4}$$

For a concrete failure of the *deduction from P4 (H.1)*, take $d=3,L=3$, so $C_0=36$ and $r_0=144$. With $\alpha=(d-2)/2-\gamma\in(0,1/2)$, P4's $\epsilon_j=\alpha_0\operatorname{epsTail}(j)L^{-j\alpha}$ gives

$$\frac{\epsilon_{k-1}}{\epsilon_{k+1}}
=3^{2\alpha}\frac{\operatorname{epsTail}(k-1)}{\operatorname{epsTail}(k+1)}
\longrightarrow 3^{2\alpha}<3. \tag{5.5}$$

The zero-fluctuation part of (5.4) alone demands $r_0^2\epsilon_+=20736\epsilon_+\le\epsilon_{k-1}$, which (5.5) violates for all sufficiently large $k$. Even a hypothetical *single direct* `xiC_compose_at` from $G'$ to $G_{k-1,X}$, before any fluctuation, has parameter $C_0/L^2=4$ and demands a scale-one radius $16\epsilon_+$; this too exceeds (5.5). Thus the advertised all-$L\ge3$ conclusion is unavailable from the landed general XiC bound and H1. A sharper special theorem for whole-level geometry, or a stronger radius sequence, could still treat particular $L<C_0$. This calculation does not assert the existence of a physical datum saturating the general theorem's bound.

Once (5.3), the perturbation smallness conditions, and the two `xiC_compose_at` geometry families hold, (4.2) followed by the second composition proves the **local representative** lies in $\Xi^c_j(G_{j,X};1,\epsilon_j-\tau_j)$ throughout $|z|<2$. Identifying that representative with the actual `composedPairAt` on $X$ requires LOCAL-PAIR-AGREEMENT; it is **OPEN here**. The requested strengthening of `Def6.gs_spec` to the minimal generating set with common collar is the appropriate input. No global equality of the two raw fields is needed.

## 5. Lean targets, in dependency order

The following names are proposed targets, **not** claims that declarations by these names exist.

1. `ray_upper_dec_bg`: from `FlCore`, upper `XiCData`, and $\lambda$ in (2.3), obtain the unique `IsDecBg` using **landed** `xiCData_inDomainC` and `i4b_exists_unique`.
2. `ray_upper_dec_dom`: combine item 1 with **landed** `decDom_of_isDecBg`; keep both strict margins (2.1) in the statement.
3. `ray_upper_cov_analytic`: combine **landed** `i4b_analytic`, `isOpen_decDom`, `xSetting_of_flCore`, and `analyticOnNhd_decCovSqrt_entry`, under the separate covariance inequalities (2.2), to obtain an analytic matrix-valued chart at each upper complex datum.
4. `ray_cov_real`: at $\lambda=1$, use **landed** `i4b_one`, `theorem72_real`, and equality of the two restricted fields to rewrite (1.2) as `StepSetting.covSqrt`; then use **landed** `StepSetting.covSqrt_isReal` and `liftC_hatField_covSqrt` for the real substitution.
5. `ray_cov_sup`: apply **landed** `decCovSqrt_supNorm` componentwise and the finite-dimensional $\sqrt N$ estimate to obtain (3.5), including the `liftC` layer-constancy lemma.
6. `xiC_compose_scale_one`: package **landed** `xiC_compose_at` and `xiC_scale`, plus the elementary $\sigma\le1$ monotonicity, with radius $\max\{1,\sigma^2\}\epsilon$. Keep the upper top-level hnorm witness separately.
7. `ray_xiC_disc`: use item 5, the top-level witness from item 6, and **landed** `xiC_perturb` to prove (4.2) on $|z|<2$, with the corrected $r_0\epsilon_+$ in every numerical premise.
8. `ray_old_local_disc`: apply item 6 for $G_k\to G_{j,X}$, use (5.3), and treat $j=k$ without a second composition; prove the local $\Xi^c_j$ inclusion on the whole disc.
9. `ray_old_term_disc`: apply LOCAL-PAIR-AGREEMENT on (X), then `Terms.localE`/`localM`, to identify the actual old-term evaluation with item 8. This is the remaining term-facing bridge and is **not** discharged by item 8 alone.

The numerical check that (2.0)–(2.2), the `xiC_perturb` inequalities at radius (5.1), and (5.3) hold for the chosen physical class is a separate obligation. Under those checked premises, items 1–8 provide the requested mass-uniform complex chart and ray disc; item 9 finishes the application to the class terms.
