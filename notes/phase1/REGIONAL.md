# Q13 follow-up: the regional scheme-A interface

## Summary

The same-datum mass change has a regional chord and a crossing-bond term with explicit new-volume bounds, as in `MASS-RESPONSE.md` §§1–2. P5 (1.8) also gives the right *form* of the inherited regional energy: its restricted antisymmetric sum must be compared together with the polymer sum. The whole-torus I-6 estimate cannot simply be restricted to $X_{Z'}$. The needed regional cancellation, the complex segment for the two composed fields, and a decoupled local response have not been proved for the actual $X_{Z'}$ and P5 correction. Consequently no numerical $C_E^{\rm loc}$ or $C_F^{\rm loc}$ follows from the landed theorems. Below are exact regional identities and explicit constants *conditional on named local estimates*, with the unproved premises isolated.

The reference measure and the $R$ denominator can be kept literally common, at zero comparison cost. The cutoff cannot be changed by a multiplicative estimate: a shifted sharp indicator has an infinite ratio on its symmetric difference. A common cutoff is therefore a definition of the step representation that still needs an exact support and density identity for the physical construction. At the mass step, both solvers use the **same physical datum**, so $q_{\rm data}=0$. The later P7 physical-to-reference conversion belongs to the window $R$ identity and its refund; its cost is not a new-cube charge. Thus the full one-step (S2) interface remains **open**. This note does not turn conditional local constants into an unconditional operator bound.

## 1. The actual regional energy and its marginal flux

Write $q=k+1$, $X=X_{Z'}=Z_k^c\cap Z'$, $m=\nu_q$, and let $D^{\rm ph}$ be `COLLAR-FIX.md` (1.1)–(1.2). **Regime-index check:** at the literal transition $q=k_0+1$, `Def6v2Regime.lean:Regime.lfBgMass_eq_sfBgMass_of_lt` says that the LF and SF solver masses at level $q$ already agree. The massless level-$q$ field used in `MASS-RESPONSE.md` is therefore an *auxiliary* reference, not the LF solver prescribed by the landed regime. The actual discrepancy is in the inherited factors from levels $k\le k_0$. An identity transporting those factors through the $q$ step to this auxiliary comparison is part of `regionalEnergyIdentity`; without it, (5.2) is not an estimate for `StepData.ker`. At each inherited level $j$, put $R_j=Y\cap T^{(j)}$, $B_j=Y^\approx\cap T^{(j)}$, where $Y$ is the small-field region read by the *actual* step factor. Use the same $D^{\rm ph}$ to construct the complete and field-free composed fields $\psi_j^m,\psi_j^0$. In the notation of `LargeField/Def7v2Form.lean:EresJ2` and `Def7v2Corr.lean:corrSum`, define

$$E_j^Y(\psi)=\sum_{y\in R_j}\sum_{P\ni y,\,P\subset B_j}\mathscr E^{(j)}(y,P;\psi,h)-\operatorname{Corr}_j(R_j,B_j;\psi,h),\qquad \Delta E_Y=\sum_j\big(E_j^Y(\psi_j^m)-E_j^Y(\psi_j^0)\big).\tag{1.1}$$

This is an exact definition, including P5's second sum. It is *not* `Def7v2Interface.deltaE`, which is a whole-torus `Ecomp` difference. The exact local algebra is obtained by applying the I-6 decomposition to the unrestricted polymer sum at each $y$. Let $I_j(y;\psi,b)=\mathscr E_j(y;\psi,b)-A_j(y;\psi)$ be its remainder and let $T_j^Y$ be minus the excluded polymers $P\not\subset B_j$. Then

$$\Delta E_Y=\sum_j\left\{\sum_{y\in R_j}\Delta I_j(y)+\Delta\mathcal B_j(R_j,B_j)+\Delta T_j^Y\right\},\qquad
\mathcal B_j:=\sum_{y\in R_j}A_j(y)-\operatorname{Corr}_j(R_j,B_j).\tag{1.2}$$

Here $\Delta f=f(\psi^m)-f(\psi^0)$, with the same source $b_j=\nu_jh$. Equation (1.2) is finite-sum subtraction plus the I-6 identity; absolute convergence of the polymer sums permits rearrangement. `SmallField/Def6v2Renorm.lean:IsSFFamily2.renormalization_aniso` proves the averaged I-6 identity, an irrelevant bound for $I_j$, and $\sum_y A_j(y)=0$ on a torus. `SmallField/Def6v2Bridge.lean:polyAniso_subset_xiDom_sf` and `...toLanded` supply the complete-mass domain reduction; they do **not** establish that the interpolation between the two *regional composed fields* remains in a common analytic tube. `LargeField/Def7v2Corr.lean:corrSum_self_eq_zero` proves the correction vanishes when its two summation sets agree; `Def7v2Form.lean:EresJ2` and `EresJ2_eq` place the actual correction in the restricted factor. None identifies $\mathcal B_j$ with a bounded local remainder for this mass comparison.

For clarity, if $A_j(y)=\frac12\sum_x a_j(x-y)(s_x-s_y)$, $s_x=\psi(x)\cdot\psi(x)$, and $a_j$ is even, finite-set antisymmetry gives the **exact marginal flux**

$$\sum_{y\in R_j}A_j(y)=\frac12\sum_{y\in R_j}\sum_{x\notin R_j}a_j(x-y)(s_x-s_y).\tag{1.3}$$

The inner $R_j\times R_j$ sum cancels; the displayed crossing sum generally does not. P5 (1.8) subtracts `corrPair` for $y\in R_j$, $x\in B_j$, with both $v_1$ and $v_2\nu_jh\cdot(\psi_0(x)-\psi_0(y))$. Hence $\mathcal B_j$ is the crossing flux (1.3) minus that *full* correction. One must retain the $v_2$ term and the branch of the unit direction; replacing it by $\psi$ or by zero is not an identity. P5 p. 489 (1.8), p. 490 after (1.9), and P1 (3.106), (3.110) are the source references. The local I-6 form and the importance of this boundary term are also stated in `SMALLFIELD.md` §2.2, Theorem 2.1 and §2.5.

There is a direct finite bound on the *uncancelled* flux. If $\|\psi^0(z)\|\le B_\psi$, $\|\psi^m(z)-\psi^0(z)\|\le U_j$, and $K_{a,j}:=\sup_y\sum_x|a_j(x-y)|$, then $|\Delta s_z|\le(2B_\psi+U_j)U_j$ and (1.3) gives

$$|\Delta A_j(R_j)|\le\tfrac12(2B_\psi+U_j)U_jK_{a,j}|R_j|.\tag{1.3a}$$

For a union of $q$ cubes with $|R_j|\le\Gamma_E L^{d(q-j)}|X|_q$ and $U_j=C_{\rm cmp}L^{-(q-j)}m$, this is an explicit per-new-cube bound, but its factor $L^{(d-1)(q-j)}K_{a,j}$ need not be summable over inherited levels. A similar crude Cauchy bound on `corrSum` does not cure this. The requested uniform $C_E^{\rm loc}$ therefore needs the grouped cancellation and irrelevance estimate below; (1.3a) alone does not supply it.

Here is an explicit **conditional** constant rather than an undefined $C_E^{\rm loc}$. Let $s_j=L^{-(q-j)}$, $n_1=\min\{n:L^{-n}\le s_*\}$, $\alpha_3=1-2\gamma-\alpha_1>0$. Assume:

* `regionalEnergyIdentity`: the difference of inherited terms in the physical step is exactly (1.1), with a support assignment to $X$ and no old/exterior residue;
* `regionalCommonTube`: for every $j$, every interpolation $t\psi_j^m+(1-t)\psi_j^0$, and every decoupling parameter used to localize it, the relevant fields and the source lie in a complex tube with Cauchy radius at least $r\varepsilon_q/(C_{\rm cmp}m)$ in the interpolation parameter, $r>0$; the composed-field difference is at most $C_{\rm cmp}s_jm$ in the normalized field norm;
* `regionalMarginalRemainder`: on that tube, the three grouped quantities $\sum_{y\in R_j}I_j(y)$, $\mathcal B_j$, and $T_j^Y$, *after localization to one $q$ cube*, have respective absolute bounds $C_I E_0s_j^{d+\alpha_3}$, $C_B E_0s_j^{d+\alpha_3}$, $C_T E_0s_j^{d+\alpha_3}$ per relevant $j$ site for $q-j\ge n_1$; at the remaining levels their combined bound is $K_{\rm near}E_0$ per site. The bound for $\mathcal B_j$ includes its $v_2$ part. Finally, the localization/covering multiplicity of sites and pairs is at most $\Gamma_E$ times $s_j^{-d}$ per $q$ volume unit.

Cauchy's estimate applied to (1.2), then the geometric sum, yields

$$|\Delta E_X|\le C_E^{\rm loc}E_0\frac m{\varepsilon_q}|X|_q,\qquad
C_E^{\rm loc}:=\frac{\Gamma_E C_{\rm cmp}}r\left[\frac{(C_I+C_B+C_T)L^{-n_1\alpha_3}}{1-L^{-\alpha_3}}+K_{\rm near}\sum_{n=0}^{n_1-1}L^{nd}\right].\tag{1.4}$$

All constants in (1.4) are specified inputs, independent of $q,\beta,m,Y$. This is a proof **conditional on** the three displayed premises, not a value derived from Def-6. The potentially large crossing flux (1.3) is why $C_B$ cannot be set to zero using `Aterm_torus_sum` or a whole-torus Corollary 3.11. The `HatEngineDom.lean:decDom_of_bgBounds`, `HatEngineFan.lean:analyticAt_hatPsi_of_decDom`, `HatEngineLocal.lean:hatSqrtF_local`, and `HatEngineLocalEngine.lean:expansion_of_AE_hat` provide domain, analyticity and expansion consequences under their own hypotheses; they do not construct `regionalCommonTube` or `regionalMarginalRemainder` for these two backgrounds. Likewise `Fluctuation/Theorem42.lean:theorem42_of_input` consumes a supplied decoupled cube response. If one is supplied with cube bound $E_b$, rate $\kappa\ge3$, and $a_{\rm Multi}(d,L)+2\le2\kappa-\kappa'$, its trace bound is the one recorded in `INTERFACE-A.md` (2.3a); it cannot be invoked with $E_b=C_E^{\rm loc}E_0m/\varepsilon_q$ until that input is proved.

## 2. The inherited observable

Use the restricted P5 (H.7) observable at exactly the same region and data as (1.1), and include the leading source term $\langle g,\phi_q\rangle$. This gives an exact difference $\Delta F_X(g)$ by subtraction. It is analytic in $g$ on $\|g\|_1<1$ if each inherited term has the (H.7) analyticity and the regional sum is absolutely convergent. The $h$ in the large-field kernel is a fixed real unit vector; no mass-uniform transverse complex $h$ ball is required of that kernel. The small-field termwise I-6 still uses the complete-mass source chart $b_j=\nu_jh$ on its stated wide domain (`Def6v2Bridge.lean` §§mass/domain); this does not supply a common tube for *two composed fields*.

Assume `regionalObservableIdentity` (restriction and assignment to $X$), `decoupledMassResponse` (the complete/free composed-field difference and its coupling derivatives obey $C_{\rm cmp}s_jm$ times a summable off-diagonal kernel), and `regionalObservableTube` (the same fixed $r\varepsilon_j$ Cauchy margin for both fields and every coupling value). Let $K_{0,1}^{\rm loc}$ be the explicit supremum of the local polymer/decoupling load, including the $g$ incidence, divided by $|X|_q$; it must be bounded uniformly for the actual geometry. Since H.7 gives $c_9\xi_j^{\rho_F}$ and $1+\alpha-\rho_F=1-2\gamma+\alpha_1>0$, the Cauchy series proves

$$|\Delta F_X(g)|\le\left[C_F^{\rm loc}c_9\xi_q^{\rho_F}\frac m{\varepsilon_q}+K_mB_hm\right]\|g\|_1|X|_q,\quad
C_F^{\rm loc}:=\frac{C_{\rm cmp}K_{0,1}^{\rm loc}}{r(1-L^{-(1-2\gamma+\alpha_1)})}.\tag{2.1}$$

The second term follows from the same-data mass response for the leading $\langle g,\phi_q\rangle$; a factor for the actual $g$ incidence is included in $K_{0,1}^{\rm loc}$ or must be displayed separately. This is **PROVED CONDITIONAL ON** the three named hypotheses. The global version with $K_{0,1}$ is `INTERFACE-A.md` (2.4); it does not imply the regional incidence or decoupled response. The landed `SFtoLFInterface.dF_bound` instead uses $E_0m/\varepsilon_k$ and omits the H.7 coefficient $c_9\xi_q^{\rho_F}$; it cannot express (2.1).

## 3. Cutoff, measure, and denominator

The comparison must be against the *actual* `Operators/StepData.lean:StepData.ker` and `GaussStepSpec`, whose kernel includes `Operators/Quiet.lean:quietKernel` on quiet steps and the corresponding nonquiet kernel. The quiet kernel is a product of `gaussProd`, four `cubeProd` factors, `chiNew`, the `InUnionDomainR` indicator at `cs.mu (k+1)`, and $e^{-\mathrm{mainActionLoc}}$ (`Quiet.lean` lines 153–198). The `R/PsiZeroFinal.lean:psiZero`, `R/PsiZeroWindowBox.lean:Zzero_eq_box`, and `R/SmallFactorOne.lean:smallFactor_one` concern the later ripe-window decomposition and its small factors. They do not compare complete and field-free step cutoffs. The following are the exact lemmas needed.

**`massChange_cutoff_reference_glue` (OPEN).** For every localized history, output, internal variable and real $h$ on the original step support, the physical complete-background density factor and the proposed field-free LF factor must have the *same* product of characteristic functions, or there must be an exact partition into a common-support factor and separately bounded boundary-shell factors. In the common-support version require $\chi^{\rm orig}=\chi^{\rm ref}=:\chi$ and $\chi=1\Rightarrow D^{\rm ph}$ lies in both real background domains. Then the cutoff cost is exactly $0$, and `sfToLF_identity` can be used pointwise there. The implication is not a field of `StepData`, `SFCtx`, or `SFtoLFInterface`. A direct inequality $\chi^{\rm orig}\le e^{C|X|_q}\chi^{\rm ref}$ fails for any finite $C$ if the cutoffs differ: for $\chi_0(x)=\mathbf1_{|x|<\delta}$ and $\chi_m(x)=\mathbf1_{|x+m|<\delta}$, $x=\delta-m/2$ and $m>0$ give $\chi_0=1$, $\chi_m=0$. Small $m$ does not repair this. Defining a common cutoff is legitimate only after proving that its complement is represented by the other large-field branches with their own estimates; silently replacing an indicator changes the density.

**`massChange_measure_compare` (PROVED at the level of definitions).** With the *same* localized history and variable types, the reference measure is literally `Operators/Variables.lean:refMeasure N a q = Measure.pi (varMeasure N ∘ isSpin)` in both descriptions, independent of solver mass, $h$, and the background. `outMeasure` and `subMeasure` are likewise independent of that mass. Thus the identity change of variables has Radon–Nikodym factor $1$ and per-new-cube cost $0$. The `gaussProd` density is part of the kernel (`Quiet.lean:gaussProd`), not of `refMeasure`; with the same running coefficients its factor is common. A later translation of Lebesgue window variables or rotation of spin variables requires the appropriate measure-preservation lemma; it is not this equality.

**`massChange_denominator_common` (PROVED as an algebraic choice for the mass step; OPEN if two $R$ references are compared).** A step kernel has no $R$ denominator. Define both descriptions before $R$, or apply the *same* $R$ map with its field-free reference density $\rho_{k,0}(Z)$ and the same positive denominator $D_0(Z)=\int\rho_{k,0}(Z)\,d\psi_k|_{Z_0}$ of LF-RECONSTRUCTION Definition III.8.1–III.8.3. Then $D_0/D_0=1$: cost $0$, conditional on positivity from Lemma III.8.2. The proof is cancellation, not a comparison of two partition functions. If one instead uses a complete-mass $D_m$, a new bound for $|\log(D_m/D_0)|$ is required; P7 (3.3)–(3.5) bounds one denominator and supplies no such ratio. Its $Z_0$ volume is a ripe-component cost and need not be proportional to the current $|X|_q$. `R/GasIdentity.lean` and the `SmallFactor*` estimates do not turn it into a one-step new-cube cost.

## 4. The physical-to-reference collar datum and its charge

For the mass comparison set $D=D^{\rm ph}$ **on both sides**. Therefore the datum-conversion term in (3.2) of `MASS-RESPONSE.md` is exactly

$$q_{\rm data}^{\rm mass}=0.\tag{4.1}$$

The P7 window comparison is a different edge. `COLLAR-FIX.md` (1.2) defines the physical collar as the trace of the inherited parent multiscale field. Under `ParentRefines` and `inner_collar_in_regular_T`, its outer face equals the composed reference exactly, and on the inner face

$$|D^{\rm ph}.\Psi(c)-D^0.\Psi(c)|\le C_\partial\widehat W_k\delta_{k_1},\qquad C_\partial=3dL+3,\tag{4.2}$$

with the full interior profile $C_*\widehat W_k\delta_{\max(k_1,\min(n,k))}$, $C_*=3dL+3$. The order is: establish actual minimal-set incidence and the retained cutoff path, impose the strengthened (Λ21), (Λ22), then apply `WeightedProp51S` to the **full** data-site difference. The two incidence assertions are not landed. Formula (4.2) is an amplitude estimate, not an action or log-integral estimate. In particular it cannot be multiplied by $\beta$ and called a bounded $q_{\rm data}|X|_q$.

The available source-level accounting for this conversion is P7 (2.53)–(2.58), LF-RECONSTRUCTION Lemma III.6.3: the full action and composed Gaussian yield a nonnegative quadratic term, a surface term, and $C^\natural=C^\natural_0+C^\natural_1$ with $|C^\natural_0|\le1$ on the real domain, $\le C_\natural\widehat\lambda_k^{2d+1}$ on the complex domain, and $|C^\natural_1|\le\frac38$ of the Gaussian quadratic form. The coefficient-conversion cost $C_{15}\sum_{j=k_1}^{k-1}|X_j|_{j+1}$ and the remaining window cost are paid in LF-RECONSTRUCTION Lemma III.8.7 by the quiet-step refund and $C_R\widehat\lambda_k^{2d+1}$, not by the current new region alone. The denominator's $Z_0$ ball contributes the explicit factors in LF-RECONSTRUCTION (III.8.4), including $Np_0\log\lambda_k+C_{\rm vol}$ per $Z_0$ block. A standalone per-new-cube number for the physical-to-reference R conversion is therefore **not available**, and is not needed for the same-datum mass comparison.

## 5. Complete conditional one-step clause and order of choices

Let the common cutoff, same measure and common denominator of §3 be verified for the *actual* step, and assume the named hypotheses of §§1–2 and the mass-response/domain incidence of `MASS-RESPONSE.md` §§1–2. Set $B_h=2$ for real unit $h$ (or the stated $5/2+r_h$ on a pinned complex chart), $K_m=\sqrt N K_w$, $G_\nabla=3dLK_1$, and

$$C_D=(d+2)M^dL^2K_m^2B_h^2,\qquad C_W=2dM^{d-1}L^2K_mB_hG_\nabla.\tag{5.1}$$

The regional chord and wall bounds are $C_D\beta_qm^2|X|_q$ and $C_W\beta_qm\delta_k|X|_q$. The exact exponent identity on the common support is the subtraction of the regional actions and inherited terms, with P5's correction included. By triangle inequality, (1.4), (2.1), and (4.1), its real part obeys

$$|\operatorname{Re}J_{q,Z'}(g)|\le q_A|X|_q,\quad
q_A=C_D\beta_qm^2+C_W\beta_qm\delta_k+C_E^{\rm loc}E_0\frac m{\varepsilon_q}
+\left(C_F^{\rm loc}c_9\xi_q^{\rho_F}\frac m{\varepsilon_q}+K_mB_hm\right)\|g\|_1,\qquad \|g\|_1<1.\tag{5.2}$$

This is **PROVED CONDITIONAL ON** `regionalEnergyIdentity` (including the regime-index transport noted in §1), `regionalCommonTube`, `regionalMarginalRemainder`, `regionalObservableIdentity`, `decoupledMassResponse`, `regionalObservableTube`, uniform $\Gamma_E,K_{0,1}^{\rm loc}$, `massChange_cutoff_reference_glue`, and the actual response and spacing premises of `MASS-RESPONSE.md`. The measure and common-denominator terms are exactly zero under §3's chosen representation. At $q=k_0+1$, $\beta_qm\le e^{2\epsilon}L^d$ (LF-RECONSTRUCTION Theorem IV.2.2); hence the first two terms are at most $C_D(e^{2\epsilon}L^d)^2/\beta_q+C_We^{2\epsilon}L^d\delta_k$. Uniform finiteness of the inherited terms requires the cited local hypotheses and the flow bounds on $E_0,\varepsilon_q,\xi_q$; it is not a consequence of $\beta_qm\le e^{2\epsilon}L^d$ alone. At the actual $q$-level regime masses the direct `Def7v2Interface` correction is zero; the nonzero expression (5.2) applies only after the stated auxiliary-reference transport has been justified.

The admissible constant order is LF-RECONSTRUCTION §I.1.3: geometry and $L$ (rows 0–7), $M$ (row 6), fluctuation and localization constants (rows 5–11), $E_0,\alpha_0$ (row 11), $B_0$ (row 12), $H_0$ (row 13), then $c_1,c_2$ (row 14), $C_R$ (row 15), and $\lambda_*,\beta$ (row 16). All of $C_D,C_W,C_E^{\rm loc},C_F^{\rm loc}$ and a uniform $q_*\ge\sup q_A$ must be fixed from earlier-row data **before row 14**. Increase $c_2$ by $q_*$ in Definition II.5.11; increase $c_1$ only if a proved cost is proportional to $\log\beta$ per new cube. The (S2) exponent decreases by $q_*|X|_q$, then Lemma II.5.12 propagates the budget. A local polymer decay rate for (S4)/(S5) is a separate decoupled expansion and is not implied by (5.2).

### Lean clause and a nonzero example

`LargeField/Def7v2Interface.lean:SFtoLFInterface` has whole-torus polymer sums, a pure $C_D\beta m^2$ chord bound, an $E_0$-based observable bound, and an old budget. It has no regional $X$, half-bond wall, P5 correction, common-support identity, reference measure, or common denominator. Its `sfToLFInterface_witness` has $k>k_0$ and zero corrections; `LargeField/Def7v2Class.lean:IsRep2WithInterface` requires the clause for a representation whose (D9) has $k\le k_0$, so that witness does not inhabit the needed case. A corrected `RegionalSFtoLFInterface` should have: (i) actual `LocalHistory`, $Z'$, $X$, and `physicalWindowData`; (ii) common-support and overlap fields; (iii) an equality of the original complete expression with the field-free `StepData.ker` times $e^J$, including `EresJ2` and the $g$ observable; (iv) same `refMeasure`, `gaussProd`, and optional common $R$ denominator; (v) chord **and** wall bounds, (1.4), (2.1), analytic $g$ field, and (5.2); (vi) support, covariance, (S0), (S2), (S4), (S5) transfer to the actual operator. `IsRep2WithInterface.iface` should quantify this regional structure for every admissible localized history and output, not merely for every Def-6 torus. It should require $h$ real unit (or the stated real overlap), with complex $b$ only where Def-6 I-6 consumes it.

More precisely, a Lean record of *inputs* (as distinct from its derived cost theorem) should have fields of the following form, with `cfg` ranging over the output and new internal variables of `StepData.ker` and `g ∈ l1Ball`:

```text
structure RegionalSchemeAInput (H : RegionHistory ...) (Z' : H.Comp q) : Prop where
  physical_datum : ∀ cfg, BgData (localGen H Z') N
  same_data : ∀ cfg, datumFree cfg = physical_datum cfg ∧
                        datumComplete cfg = physical_datum cfg
  cutoff_glue : ∀ cfg h, IsUnitReal h → chiOriginal cfg h = chiReference cfg h
  cutoff_overlap : ∀ cfg h, chiOriginal cfg h = 1 →
                     RealDomain 0 (physical_datum cfg) ∧
                     RealDomain (physMass q) (physical_datum cfg)
  regional_exponent_identity : ∀ cfg h g, chiOriginal cfg h = 1 →
      expoOriginal cfg h g = expoReference cfg h g +
        chordStar cfg h + deltaERegional cfg h + deltaFRegional cfg h g
  chord_wall_bound : ∀ cfg h, IsUnitReal h →
      |chordStar cfg h| ≤ (CD * beta q * m^2 + CW * beta q * m * delta k) * volScale X q
  energy_bound : ∀ cfg h, IsUnitReal h →
      ‖deltaERegional cfg h‖ ≤ CE_loc * E0 * m / eps q * volScale X q
  observable_analytic : ∀ cfg h, IsUnitReal h →
      AnalyticOnNhd ℂ (deltaFRegional cfg h) (l1Ball gIndex)
  observable_bound : ∀ cfg h g, IsUnitReal h → g ∈ l1Ball gIndex →
      ‖deltaFRegional cfg h g‖ ≤
        (CF_loc * c9 * xi q ^ rhoF * m / eps q + Km * Bh * m) *
          l1 g * volScale X q
  reference_measure_eq : measureOriginal = refMeasure N (localHistory H Z') q
  denominator_eq : denominatorOriginal = denominatorReference
```

Here `regional_exponent_identity` must include the transport from the old $k\le k_0$ factors to the auxiliary free level-$q$ reference; the record must **not** prove it by `sfToLF_identity` at $q$, where the landed regime masses coincide. The theorem derived from this record is (5.2), followed by a separate `GaussStepSpec` majorant transfer. The equality of cutoff values alone does not prove the original-density representation; `regional_exponent_identity` carries that obligation. The positive denominator field can be omitted for a pre-$R$ step and supplied only by an $R$-specific input.

The clause is mathematically nonzero even with zero inherited terms. In a one-spin finite model on $S^1$, take $h=e_1$, $q=(\cos\theta,\sin\theta)$ with $0<\theta<\pi/4$, $0<m<1/4$, and $A_m(s)=\frac12|s-q|^2+\frac m2|s-h|^2$. The free minimizer is $s_0=q$, the complete minimizer is $s_m=(q+mh)/\sqrt{1+2m\cos\theta+m^2}$, and with one new cube

$$J=\beta[A_m(s_0)-A_m(s_m)]=\beta\frac{m^2\sin^2\theta}{\sqrt{1+2m\cos\theta+m^2}+1+m\cos\theta},\qquad 0<J\le\tfrac12\beta m^2.\tag{5.3}$$

Take cutoff $1$, a one-point reference measure, denominator $1$, and observable $g\cdot s$; its difference is entire in $g$ and bounded by $2m\|g\|$. This is an explicit nondegenerate witness for the **finite-model regional clause** (one cube, $E=0$, no wall), with $h$ fixed real unit. It is *not* a witness for `IsRep2WithInterface` on all actual histories; claiming that would assume the open geometry and local analytic inputs. The one-site **half-bond** example in `LargeField/R/MassChangeOneSite.lean` and `INTERFACE-A.md` (1.4) instead has $J/\beta=cm+O(m^2)$ and confirms why (5.1) needs the wall term. Neither example involves a transverse complex $h$ disc, so the RGFREE-3/RGFREE-6 counterexamples do not apply to this restricted clause; they still rule out the earlier mass-uniform transverse-source bound.

## 6. Bounded Lean work list and status

Each item is intended as a self-contained worker unit of at most roughly 300 lines; the mathematical derivation to formalize is indicated. `PROVED` means proved in this note by algebra or definitions, **not** that the named new Lean declaration has landed.

1. **PROVED:** `regional_marginal_flux_finset`. For even $a$, swap $x,y$ in the $R_j\times R_j$ finite sum to obtain zero; split the full $x$ sum into $R_j$ and its complement to get (1.3). `corrSum_self_eq_zero` is the analogous landed statement for the complete P5 pair.
2. **PROVED CONDITIONAL ON `regionalEnergyIdentity`:** `regional_energy_decompose`. Unfold `EresJ2`, add and subtract the full polymer sum, then apply the I-6 `energy-Aterm` identity centre by centre; obtain (1.2) with the explicitly defined omitted-polymer tail. The missing work is the exact identification of the physical step's $Y$ and $X$ support.
3. **OPEN:** `regional_common_tube_mass` and `regional_corr_matches_marginal`. Prove, for both regional composed fields and every decoupling parameter, the shared Cauchy tube, the branch of `unitDirC`, and a per-site irrelevant estimate for the *grouped* flux minus P5's $v_1,v_2$ correction plus the polymer truncation. `Def6v2Renorm` gives the full-torus I-6 decomposition, not this restricted statement.
4. **PROVED CONDITIONAL ON item 3 and a uniform $\Gamma_E$:** `regional_inherited_energy_bound`. Apply one-variable Cauchy to the grouped terms and sum $\sum_{n\ge n_1}L^{-n\alpha_3}$; the result is exactly (1.4). Prove $\Gamma_E$ for the actual step cube assignment in a separate short geometry file.
5. **OPEN:** `regional_observable_response_tube`. Establish the coupling-derivative response with exponential locality, common $r\varepsilon_j$ tube and a uniform load $K_{0,1}^{\rm loc}$ for the physical collar. `HatEngine*` and `Theorem42` use such inputs; they do not give this one.
6. **PROVED CONDITIONAL ON item 5:** `regional_inherited_observable_bound`. Use H.7 and Cauchy, then sum $\sum_{n\ge0}L^{-n(1-2\gamma+\alpha_1)}$; add the leading source response. This is (2.1).
7. **OPEN:** `massChange_cutoff_reference_glue`. For the actual `StepData.ker`, prove a common sharp cutoff and overlap identity or construct and bound the symmetric-difference branches. No finite multiplicative comparison of unequal indicators is possible.
8. **PROVED:** `massChange_measure_compare`. Unfold `refMeasure`, `outMeasure`, `subMeasure`, and `gaussProd`; at fixed history and coefficients both sides use identical objects, so the comparison cost is zero.
9. **PROVED CONDITIONAL ON positivity of the chosen $R$ reference denominator:** `massChange_denominator_common`. Use the same $D_0$ on both sides and cancel it algebraically. A theorem comparing $D_m$ to $D_0$ is a different, open statement.
10. **PROVED:** `massChange_same_physical_data`. The two solvers are applied to one `BgData`, so $q_{\rm data}^{\rm mass}=0$. **OPEN:** `window_parent_refines` and `inner_collar_in_regular_T`, then `window_physical_reference_response` for (4.2) and the full-data weighted response; these are the separate P7 window branch.
11. **PROVED CONDITIONAL ON items 2–7 and the mass-response incidence:** `regional_sf_lf_exponent_bound`. Combine the regional action identity of `MassChangeChord/Wall`, (1.4), (2.1), and common factors to obtain (5.2) by the triangle inequality.
12. **OPEN:** `regional_sf_lf_step_bound` and the actual `IsRep2WithRegionalInterface`. Transfer (5.2) to `GaussStepSpec` and the nonquiet step with uniform majorants, support, rotation covariance and localized decay; instantiate the row-14 $c_2$ budget only after all preceding inputs are established.

No file under `/home/scott/Balaban` was changed.
