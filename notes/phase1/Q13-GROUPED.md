# Q13 round 22: the grouped regional correction

## Summary

**A-VIABLE as a sharply reduced estimate, not yet a proved interface.** For the actual P5 (1.8) thickening, the $v_1$ correction cancels every crossing pair inside the halo. The surviving $v_1$ pairs reach outside a halo whose radius is at the **current** scale $q$, so their inherited-scale polymer size grows at least like $L^{q-j}$. Exponential polymer decay can pay any required power of $s_j=L^{-(q-j)}$. The surviving $v_2\nu_jh$ term is near the boundary, but the I6 source-alignment and spin bounds give it an $s_j^3(\varepsilon_q/\varepsilon_j)^2$ factor, stronger than the required $s_j^{d+\alpha_3}$. These conclusions have explicit constants below, conditional on one quantitative halo/cover lemma and the coefficient and common-domain identifications named there.

The omitted-polymer tail has the same large halo, so it is small by H4 polymer decay; it cannot be bounded by invoking D7 directly. The landed real mass-response theorem gives an $O(\nu_j)$ estimate for the difference of two regional expressions **after** a response bound for their composed fields is supplied. For the real partition identity, a real-variable comparison is enough. The inductive analytic class and its localized derivatives still need `regionalCommonTube`. The exact physical region assignment `regionalEnergyIdentity` remains open. Thus this round removes the suggested marginal-flux obstruction to A but does not prove the complete A switch.

## 1. Exact algebra and the coefficient identity

Fix $j<q$, $R=Y\cap T^{(j)}$, $B=Y^\approx\cap T^{(j)}$, $R\subset B$. Set $s_x=\psi(x)\cdot\psi(x)$, $u_x=\operatorname{unitDirC}(\psi(x))$, $b=\nu_jh$, $a_{yx}=a_j(x-y)$. `Def7v2Form.lean:EresJ2` uses exactly this pair of regions and `Def7v2Corr.lean:corrPair`/`corrSum` gives

$$\operatorname{Corr}(R,B)=\sum_{y\in R,x\in B}\left\{\tfrac12v_{1,yx}(s_x-s_y)+v_{2,yx}b\cdot(u_x-u_y)\right\}.\tag{1}$$

P1 p. 146 (3.104), (3.106), read from the page image, defines $v_1$ as the radial spin derivative at $(e_1,\nu_je_1)$ and $v_2$ as the mixed transverse spin/source derivative. `SmallField/RenormDefs.lean:aCoefX` and `Def7v2Corr.lean:v1Loc` are that **same radial derivative of the same term**. Thus $a_{yx}=v_{1,yx}$ for a common finite source-term family by unfolding the definitions and summing absolutely. Passing this equality between `Def6v2Renorm`'s averaged infinite family and `Def7v2.lean:D1Corr.v1_lim` is the named `regionalRadialCoefficient` bridge: **PROVED conditionally on identical averaging/limit families and absolute convergence; a landed cross-module theorem is OPEN**. `PIN-I6.md` and `PIN-JET.md` do not supply that bridge. The phrase “$a=v_1+\nu_jv_2$” in SMALLFIELD.md §2.5(iii) cannot be used simultaneously with these displayed derivative definitions for one family; P1 (3.106) identifies $v_1$ alone with the radial derivative.

Assume the averaged coefficients are symmetric and $a$ is even. `R/RegionalFlux.lean:regional_marginal_flux_finset` cancels the $R\times R$ part of $A$, and `Def7v2Corr.lean:corrSum_self_eq_zero` cancels that part of the correction. Splitting $R^c=(B\setminus R)\sqcup B^c$ and using $a=v_1$ gives the exact finite identity

$$\boxed{\mathcal B_j(\psi)=\frac12\sum_{y\in R,x\notin B}a_{yx}(s_x-s_y)
-\sum_{y\in R,x\in B\setminus R}v_{2,yx}\,b\cdot(u_x-u_y).}\tag{2}$$

Thus the $v_1$ near crossings cancel, the $v_1$ far crossings survive, the $v_2$ near crossings survive, and every interior pair cancels by exchange. If the coefficient bridge is not assumed, add $\frac12\sum_{R\times(B\setminus R)}(a-v_1)(s_x-s_y)$ to (2). `RegionalFlux.lean:corr_minus_flux` proves the unsplit starting identity; the displayed split follows by finite additivity. All these algebraic statements are **PROVED CONDITIONAL ON `regionalRadialCoefficient`** at the actual coefficient family.

## 2. The one geometric inequality and the explicit bound

The key point missed by a fixed-distance flux model is `Def7SmallField.lean:thickY` (lines 209–211): $Y^\approx$ is `thick ⌊R(q-1)⌋ Y` at the **current level $q$**. Define $H_{j,q}$ to be the smallest inherited-$j$ polymer covering size of any polymer $P$ with $y\in R_j$, $P\not\subset B_j$, or of any coefficient polymer connecting $y\in R_j$ to $x\notin B_j$. The sharply stated missing geometry lemma is

$$\texttt{regionalHaloDistance}:\qquad H_{j,q}\ge c_hR(q-1)L^{q-j}=c_hR(q-1)/s_j\quad(c_h>0),\tag{3}$$

with the stated convention for the normalized `Def6Terms.lean:sizeJ`/`treeLenCovOne` and a torus nonwinding condition. A proof should unfold `thickY`, `SFCtx.alignedIn`, and `SFCtx.sset`; a point outside the current-level halo is at least $R(q-1)$ current blocks from $Y$. A connected polymer from an inherited centre to that point needs at least a fixed fraction of $L^{q-j}R(q-1)$ inherited covering steps. The conversion factor $c_h$ includes the $M=L^{m_0+m_1}$ cover-block size. **(3) is OPEN as a landed theorem**; its scale dependence is fixed by the definitions. The argument must also handle periodic wraparound and histories near the torus seam, using the nonwinding clause of D8.

Here are explicit constants under (3). Suppose `PinJet.germ` or the full `PremisesTermAniso` gives each radial and mixed coefficient at polymer $P$ the respective bounds $E_0e^{-\kappa_E d_j(P)}/r_j$ and $4E_0e^{-\kappa_E d_j(P)}/r_j^2$, where $r_j=\varepsilon_j/K_r$. Suppose the number of size-$n$ contributing polymers and sites at a fixed centre, including the moment weight $(D_{yx}^2+D_{yx})$, is at most $K_{\rm cnt}e^{\kappa_{\rm cnt}n}$; set $\rho=\kappa_E-\kappa_{\rm cnt}>0$, $K_a=K_{\rm cnt}/(1-e^{-\rho})$, and $M_2=4K_{\rm cnt}/(1-e^{-\rho})$ after the indicated moment has been included. Then the coefficient estimates are

$$\sup_y\sum_{x:\,x\notin B}|a_{yx}|\le (K_aE_0/r_j)e^{-\rho H_{j,q}},\qquad
\sup_y\sum_x|v_{2,yx}|(D_{yx}^2+D_{yx})\le M_2E_0/r_j^2.\tag{4}$$

These are **PROVED CONDITIONAL ON** the specified polymer count, coefficient bounds and (3): group by the least size $n$, sum $\sum_{n\ge H}e^{-\rho n}\le e^{-\rho H}/(1-e^{-\rho})$. A real or complex small-field datum satisfying the translated `DataHypAniso` inequalities has $|s_x-1|\le\sigma^2\varepsilon$, $|\psi_x-\psi_y|\le D_{yx}\sigma\varepsilon$, $|b-\nu_j\psi_y|\le\sigma^2\varepsilon$, and $0\le\nu_j\le\sigma^2\le1$. On the branch $|\psi|\ge1/2$, $|u_x-u_y|\le4D_{yx}\sigma\varepsilon$ and $|b-\nu_ju_y|\le2\sigma^2\varepsilon$. Since $u_y\cdot(u_x-u_y)=-\frac12(u_x-u_y)\cdot(u_x-u_y)$, bilinear Cauchy and the norm triangle inequality give

$$|b\cdot(u_x-u_y)|\le8(D_{yx}^2+D_{yx})\sigma^3\varepsilon^2.\tag{5}$$

Let $\sigma=C_0s_j$, $\varepsilon=\varepsilon_q$, $\varepsilon_q/\varepsilon_j\le K_Rs_j^{\alpha}$, $\alpha=(d-2)/2-\gamma$, and $\alpha_3=1-2\gamma-\alpha_1>0$. The far $v_1$ term in (2), using $|s_x-s_y|\le2\sigma^2\varepsilon_q$, is at most $K_aE_0C_0^2K_rK_Rs_j^{2+\alpha}e^{-\rho c_hR(q-1)/s_j}$ per $y$. Put $p=d+\alpha_3-2-\alpha=d/2-\gamma-\alpha_1>0$, $R_*:=\inf_{q\le k_0+1}R(q-1)>0$. The elementary inequality $e^{-t}\le(p/e)^pt^{-p}$ yields

$$|\mathcal B_j^{v_1,\rm far}|/|R|\le C_1E_0s_j^{d+\alpha_3},\quad
C_1=K_aC_0^2K_rK_R\left(\frac{p}{e\rho c_hR_*}\right)^p.\tag{6}$$

For $v_2$, (4)–(5) give $8M_2E_0C_0^3K_r^2K_R^2s_j^{3+2\alpha}$ per crossing $y$. Since $3+2\alpha=d+1-2\gamma=d+\alpha_3+\alpha_1$, $0<s_j\le1$ implies

$$|\mathcal B_j^{v_2,\rm near}|/|R|\le C_2E_0s_j^{d+\alpha_3},\quad C_2=8M_2C_0^3K_r^2K_R^2.\tag{7}$$

Equations (6)–(7) prove $|\mathcal B_j|\le(C_1+C_2)E_0s_j^{d+\alpha_3}|R|$ **CONDITIONAL ON** (3)–(5), the coefficient bridge, translated `DataHypAniso`, and the coefficient count. If the actual cube assignment has at most $\Gamma_Es_j^{-d}$ relevant inherited centres per new cube, its charge is at most $\Gamma_E(C_1+C_2)E_0s_j^{\alpha_3}$ per new cube, and $\sum_{q-j\ge n_1}s_j^{\alpha_3}\le L^{-n_1\alpha_3}/(1-L^{-\alpha_3})$. This is the desired summable constant. The full analytic version remains conditional on `regionalCommonTube` placing both fields and every localization interpolation in these bounds.

## 3. Omitted polymers and D7

The omitted tail $T_j^Y=-\sum_{y\in R,P\not\subset B}E_j(y,P)$ is an H4 energy-polymer sum, not a D7 boundary activity. Under (3), H4 and the same count give

$$|T_j^Y(\psi)|/|R|\le K_aE_0e^{-\rho c_hR(q-1)/s_j}.\tag{8}$$

Using $p_T=d+\alpha_3>0$ in the same exponential inequality, its explicit irrelevant constant is $C_T=K_a[p_T/(e\rho c_hR_*)]^{p_T}$: $|T_j^Y|\le C_TE_0s_j^{d+\alpha_3}|R|$. On a **common** H4 domain, $|\Delta T_j^Y|\le2C_TE_0s_j^{d+\alpha_3}|R|$ without differentiating. These are **PROVED CONDITIONAL ON** (3), the H4 polymer count and common-domain membership. The factor $2$ is sufficient for summability but gives no small factor $\nu_j$.

For a literal D7 label $U$, one further needs `regionalTailAssignment`: omitted polymers assigned to $U$ have $d_j(P)\ge H_{j,q}+c_Dd_q^{\rm cov}(U\bmod\Omega_q^c)$ and the assigned incidence obeys the same $K_{\rm cnt}$ bound. Then the same sum yields

$$|T_{j,U}^Y|\le K_aE_0e^{-\rho H_{j,q}}e^{-\rho c_Dd_q^{\rm cov}(U\bmod\Omega_q^c)}.\tag{9}$$

This has D7 rate $\kappa_D=\rho c_D$ if $\rho c_D\ge\kappa$ (or the pre-class $\frac32\kappa$ when that stronger rate is required). **`regionalTailAssignment` is OPEN.** D7 (LF-RECONSTRUCTION Definition II.6.1, P5 (1.38)–(1.39)) is a condition on already localized boundary terms; it does not itself prove (9). The omitted tail must remain in the exact `regionalEnergyIdentity`, even though (8) bounds it separately.

## 4. The complete/free difference and the complex tube

Assume the two composed fields come from the **same** full datum and `R/MassResponseHyp.lean:massChange_sameData_response_unit` is transported to them with $U_j=2\sqrt N K_w\nu_j$, $|\psi^m-\psi^0|\le U_j$, $|\psi^0|\le B_\psi$, and both fields stay on the branch $|\psi|\ge1/2$. That composed-field transfer is **OPEN**; the landed theorem is for background solutions under its Green, Euler–Lagrange, domain and bound premises. `RegionalFlux.lean:sq_diff_le` gives $|\Delta s_z|\le S_j:=(2B_\psi+U_j)U_j$. The elementary unit-direction estimate gives $|u(\psi^m_z)-u(\psi^0_z)|\le4U_j$. Subtracting (2) proves the real estimate

$$|\Delta\mathcal B_j|\le S_j\sum_{y\in R,x\notin B}|a_{yx}|+8\nu_jU_j\sum_{y\in R,x\in B\setminus R}|v_{2,yx}|,\tag{10}$$

with an extra $S_j\sum_{R\times(B\setminus R)}|a-v_1|$ if the coefficient bridge is absent. This is **PROVED CONDITIONAL ON** the stated real field transfer and coefficient identity. It is $O(\nu_j)$ in the far part and $O(\nu_j^2)$ in the $v_2$ part. Combining (4), (8) and (10) with $\nu_j\le s_j^2$ gives a real summable far charge because of the halo exponential; the near $v_2$ term must still use (5) or a corresponding difference estimate to retain the full I6 scale power. The landed `regional_flux_diff_le` alone gives only $S_jK_a|R|$ and misses both the P5 correction and halo.

The **real partition identity** and a pointwise real (S2) comparison can use (10) and the real I6/tail bounds without complex interpolation. The inductive H4/H7 bounds, locality after decoupling, coupling derivatives and the next fluctuation step require analytic terms on a common complex tube with a uniform Cauchy margin. `regionalCommonTube` is **OPEN** and is needed there; real mass response cannot establish it. The sharp indicator remains on the real contour.

## Verdict and bounded Lean packages (13 lines)

**A-VIABLE, conditional reduction:** (2), (5)–(8) give the grouped regional rate $s_j^{d+\alpha_3}$ with the explicit constant $\Gamma_E(C_1+C_2+2C_T)L^{-n_1\alpha_3}/(1-L^{-\alpha_3})$, **PROVED CONDITIONAL ON** `regionalRadialCoefficient`, `regionalHaloDistance`, PinJet or full anisotropic tube coefficient bounds, translated I6 data, polymer/cube counts, and common-domain membership. No admissible order-one boundary counterexample to this statement was found. A fixed-distance flux model is outside the actual far-pair geometry.

**OPEN:** `regionalEnergyIdentity`, `regionalCommonTube`, `regionalTailAssignment`, and composed-field response transfer. Thus the full scheme-A interface is not proved; the author's recorded A choice is unchanged, and the hybrid remains pending `hybrid_sf_factorization`.

Lean packages of at most about 300 lines each: `regionalRadialCoefficient` (unfold `aCoefX`/`v1Loc`, then D1 limits); `regionalCrossSplit` (2), from `corr_minus_flux` and `corrSum_self_eq_zero`; `regionalHaloDistance` (3), from `thickY`, `alignedIn`, `sizeJ`, nonwinding geometry; `regionalCoeffTail` (4) and `regionalOmittedTail` (8), from H4/PinJet and polymer counts; `regionalV2Bound` (5),(7), from `DataHypAniso` and unit-direction lemmas; `regionalBoundScaleSum` (6)–(9), elementary exponential/geometric sums; `regionalRealDifference` (10), from the composed response. The physical identity and common tube require separate analytic packages, not deductions from these bounds.

The hybrid evaluates inherited $E$ in the complete background on both sides of its proposed factorization, so a **complete-to-massless** $\Delta\mathcal B_j$ is absent **conditional on `hybrid_sf_factorization`**. It still carries P5's restricted correction and its ordinary boundary localization.
