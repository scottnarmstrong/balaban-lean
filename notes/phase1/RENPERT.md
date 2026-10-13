# RENPERT: the shifted perturbation in renormalization localization

**Scope.** This is the second and third `RenormExpInput` fields in `Fluctuation/RenormExpG.lean`: `locC2` and `locDφ`, at the physical full-level generating set $G=\mathrm{lvTop}$ and the proper covers of `levelLocalCover`. Paths below are relative
to `/home/scott/Balaban/Balaban`. **PROVED** cites a landed statement or an explicit algebraic deduction; **PROVED CONDITIONAL ON** refers to a proved cited result with hypotheses stated; **OPEN** names a missing assertion, including a consequence conditional on it. No proper-cover `locC2` or `locDφ`
theorem is landed.

## 1. Equations and the appropriate decoupled solver

Put $\delta=\mathrm{xiC1}(d)\varepsilon$, $\ell=G.\mathrm{spacing}$, $\nu_u=\mathrm{renMassU}(\nu,\xi)=\nu(1+\xi_1)/(1+\xi_2)$, $\zeta=\mathrm{renZeta}(\varepsilon,\xi)=\varepsilon\xi_0$, $\Delta\nu=\nu_u-\nu$, and $r=\|\xi\|<r_0\le1/16$; the Lean
indices are `ξ 0`, `ξ 1`, `ξ 2` in this order (`Fluctuation/RenormExpLemma35.lean`).
Let $(\phi_s,\alpha_s)$ be the `i4b_analytic` background for raw datum $D=(\Psi,h)$ and cut parameters $s$, with $\bar\phi_s=\mathrm{barField}(G,\Psi,\phi_s)$.
The exact data for the original, top-level I-4a are
$$\phi_{0,s}=\bar\phi_s,\quad \alpha_{0,s}=\alpha_s+\Delta\nu,\quad \delta\Psi=\zeta\Psi,\quad f_{1,s}(x)=\Delta\nu\,[h(x)-\phi_s(x)],\quad F_s=\mathrm{pertSource}(G,a,\delta\Psi,f_{1,s}).$$
**PROVED:** `Background/Prop51Mass.lean:isPerturbedM_iff` says that the desired `IsPerturbedM G a νu α_s φ0,s Fs δφ δα` is exactly `IsPerturbed G a ν α0,s φ0,s Fs δφ δα`.
The latter means $(H_D^\nu(\alpha_{0,s})+\delta\alpha)\delta\phi=F_s-\delta\alpha\phi_{0,s}$ and $(\phi_{0,s}+\delta\phi)^2=1$ on $\Omega_1$ (`Background/Contraction.lean:IsPerturbed`).

**REFUTED:** extending this unit-constraint equation to every complex cut $s$ and using I-4a mode U with an $O(r)$ output. The cut background need not have $\phi_{0,s}^2=1$; mode U's `Nmap` has the extra $\frac12H_0\mathrm{gdef}(\phi_{0,s})$ even
when $\xi=0$ (`Background/ContractionCore.lean:Nmap`). Its `DecHyp` also asks for two defect bounds of size $\delta_1=O(r)$, unavailable at $r=0$. `notes/phase1/LOCALIZATION.md` §3.2, especially pp. corresponding to lines 248–259, specifies mode P
for a cut family and explains the zero-source conclusion.
Use **mode P (`ιU=false`) for every $s$**. Its underlying constraint is $(\phi_{0,s}+\delta\phi_s)^2=\phi_{0,s}^2$; away from $s=1$ the decoupled fixed-point equation is the definition of the continued field, so this sentence does not assert that the continued field solves the original Euler–Lagrange equation. The zero-source clause of `Localization/DecoupledSolve.lean:i4a_exists_unique` gives $(\delta\phi_s,\delta\alpha_s)=0$ at $\xi=0$.
At $s=1$, `Localization/DecoupledBackground.lean:i4b_one` identifies $(\phi_1,\alpha_1)$ with `(bgFieldC,bgMultC)` and gives `IsSmallSolution`; its `IsEL` clause makes $\mathrm{gdef}(\phi_{0,1})=0$ on $\Omega_1$ (`Background/Data.lean:IsEL`,
`IsSmallSolution`). Thus the P and U fixed-point maps agree at $s=1$; there, and only there, the mode-P family solves the unit-constraint system after the endpoint conversion below.

The fluctuation step is an instance of the same **abstract I-4a construction**, not of these same data: `Fluctuation/InteractionSymm.lean:i5_functional_evTerm` invokes `Dec2.i4a_analytic` in mode P, with `flEdat` from `Localization/I5FluctData.lean`
(background from $G_p$, source $\psi'$, $f_1=0$) on the lower operator $H_m$; `Fluctuation/InteractionEngine.lean:FlCore.SM` supplies its `Dec2.FootLocal` setting and `flEdat_strict` supplies strict data.
`Fluctuation/SharpVF.lean:fsite_expansion_hat_dir` consumes that family. For renormalization use the **original** `Localization/DecoupledSolveAnalytic.lean:i4a_analytic` and `Localization/RowsBg.lean:i4a_local_rows` on top $G$ with `FlCore.hS.fam`,
`hS.an`, `Sp`, `HBp`, `hκ`, `hM`; no new Green family is called for.

`Localization/DecoupledSolve.lean:DecHyp` requires `GreenSetting`, $0\le\delta_0\le1$, $\delta_1\ge0$, smooth $\phi_0$ at radius $\delta_0$, $\|\phi_0\|\le3/2$, $\ell^2|\alpha_0|\le\delta_0$, $\ell^2|f_1|\le\delta_1$, and $\|\delta\Psi\|\le\delta_1$
on `dataSites`; its `g0`, `gl` implications vanish in mode P.
`Localization/DecoupledSolveAnalytic.lean:StrictDataM false` uses the **strict** versions of these data inequalities (P1–P3), and `i4a_analytic` additionally requires the parameter disc $\|s_P\|<e^\kappa$ and
$\delta_0,\delta_1\le\mathrm{deltaStar'}(d,L,N,\mathrm{famConst}(d,L,BG,\kappa),\mathrm{gamma1}(d)/8)$.
**OPEN, conditional on OPEN-REN-STRICT:** `FlCore.Sp` gives Green/DG; `FlCore.hS`, `hκ`, `hM` give family and analytic specifications and scale inequality; `i4b_exists_unique` gives `BgBounds` at $K_4\delta$; `FlCore.phi_lt` gives
$\|\phi_{0,s}\|<3/2$; the remaining shifted strict bounds and numeric margins are below. `FlCore.B_le` concerns the lower fluctuation solver and does **not** pay these top-level shifted margins.

## 2. Uniform constants, analyticity, class, and endpoint

Write $K_4=K4(d,L,N,BG,\kappa)$ and $K_1=\mathrm{bgK1}(d,L,N)$. `Fluctuation/RenormExpLemma35.lean:XiCOne.mass_le` gives $\nu\ell^2\|h-\phi_1\|\le3\varepsilon$; `i4b_one` and both `BgBounds.val` estimates give $\|\phi_s-\phi_1\|\le(K_4+K_1)\delta$.
Since $\nu\ell^2\le1$, set $m_*=3+(K_4+K_1)\mathrm{xiC1}(d)$; then $\nu\ell^2\|h-\phi_s\|\le m_*\varepsilon$ uniformly in complex $s$.
**PROVED:** `renMassU_sub_norm_le` gives $|\Delta\nu|\le(32/15)\nu r$. With the strict datum bound $\|\Psi\|<3/2$ on `dataSites`, set $b_*=3/2+(32/15)m_*$. Then $\ell^2|f_{1,s}|\le(32/15)m_*\varepsilon r$ and $\|\delta\Psi\|<(3/2)\varepsilon r$, so
one may take $\delta_1(r)=b_*\varepsilon r$.
For one fixed analytic domain take $D_1=b_*\varepsilon r_0$ and $D_0=2K_4\delta+3r_0$. The $3r_0$ absorbs $\ell^2|\Delta\nu|\le(32/15)r_0$ in $\alpha_{0,s}$; the $2K_4\delta$ leaves strict room for the background gradient, Laplacian, and multiplier
bounds.
**OPEN-REN-STRICT:** prove `StrictDataM G N false D0 D1 Eren` for every admitted $(D,\xi,s)$ and `DecHyp` with $D_0,\delta_1(r)$ pointwise, together with $D_0,D_1\le\mathrm{deltaStar'}(\cdots)$ and $D_0\le1$. The positive $D_1$ also covers $r=0$.
Choose constants before $\varepsilon,r_0$; the current `FlCore` record by itself states none of these shifted inequalities.

Define the proposed `Edat` map (using Lean's nested tuple order) by
$$E_{\rm ren}(D,\xi,s)=(\bar\phi_s,\ \alpha_s+(\nu_u-\nu),\ \varepsilon\xi_0\Psi,\ (\nu_u-\nu)(h-\phi_s)).$$
**OPEN, conditional on OPEN-REN-STRICT and the chart/parameter leaves of `RENINPUTS.md`:** `i4b_analytic`, `renMassU`'s nonzero denominator for $r_0\le1/16$ (`one_add_ne_zero_of_norm`), and `i4a_analytic ... false D0 D1` give one family
$(\delta\phi_s,\delta\alpha_s)$ jointly ambient analytic in raw $D$, $\xi$, and the cut parameters. `Fluctuation/RenormExpLemma35.lean:analyticAt_renRaw` is a landed model for the rational composition. `XiCOneReal` need not be open: `HasLocPrinciple`
asks for `AnalyticOnNhd` at its points.
The analytic theorem's fixed $D_1$ yields only an $O(r_0)$ bound. Apply `i4a_exists_unique` **again at each $\xi$**, with $\delta_1(r)$ and the same $D_0$; its uniqueness clause in the $c6'$ ball identifies this solution with the analytic family.
Therefore
$$\mathrm{Small}(G,\delta\alpha_s,K'_2b_*\varepsilon r),\qquad \mathrm{SupBounds}(G,\delta\phi_s,K'_2b_*\varepsilon r),$$
where $K'_2=\mathrm{cK2'}(d,L,N,\mathrm{famConst}(d,L,BG,\kappa))$. At $r=0$ this also proves exact vanishing. This two-radius argument is **OPEN as a Lean wrapper**, but uses only the landed existence, analytic, and uniqueness clauses.

`Fluctuation/RenormExpBounds.lean:pertClass` asks for `SupBounds` at $V$ and $\ell^2|\alpha_u+\nu_u|\le A$, with $\alpha_u=\alpha_s+\delta\alpha_s$. In `locC2`, exactly
$$V=c_K\,\mathrm{cK2}(d,L,N)\,B r,\qquad A=K_1\delta+c_K\,\mathrm{cK2}(d,L,N)\,B r_0+2.$$
**OPEN, conditional on OPEN-REN-STRICT and OPEN-REN-CLASS:** choose $c_K\mathrm{cK2}B\ge K'_2b_*\varepsilon$ (for `exists_isRenSol`, $B=8\varepsilon$, so $c_K\ge K'_2b_*/(8\mathrm{cK2})$). The sharp $O(r)$ bound gives the first clause and the
$\delta\alpha_s$ part of the second. `BgBounds` gives $\ell^2|\alpha_s|\le K_4\delta<1/2$ by `FlCore.phi_lt`; mass gives $\ell^2|\nu_u|\le1+(32/15)r_0\le17/15$. Their sum is $<2$ before the nonnegative $K_1\delta+c_K\mathrm{cK2}B r_0$ allowance. `OPEN-REN-CLASS`
is the elementary pointwise packaging for all complex $s$; `renSol_mem_pertClass` only covers $s=1$.
`norm_renC2On_le_of_mem` then gives the optional numeric bound $(17/32)N(3+A)V^2\,\mathrm{blockWeight}(G,B_z)$. The localization principle must also transfer **every** admissible $M$; this one numeric bound cannot replace that universal clause.

**OPEN-UNIQUENESS-MARGIN:** require $K'_2b_*\varepsilon r_0\le\min(\mathrm{rho4}(d,L,N,BG,\kappa),\mathrm{c6}(d,L,N))$ and $r_0\le r_F$, the radius of `IsRenSol`. At $s=1$, `i4b_one` makes $\mathrm{gdef}(\phi_{0,1})=0$; hence P's `DecFixed` equals
U's `DecFixed`. The zero defect supplies U's `DecHyp.g0/gl`, and `Localization/DecoupledBackground.lean:isPerturbed_of_decFixed_one` converts the fixed point (with the `rho4` margin) into `IsPerturbed` at real $\nu$. Then `isPerturbedM_iff` gives the
exact complex-mass equation. `Fluctuation/RenormExpLemma35.lean:IsRenSol.unique` identifies this endpoint with $F$ using the `c6` margin. There is no cited inequality $c6'\le c6$; the sharp $O(r)$ bound pays for the comparison. The endpoint
mode-change and arithmetic are **OPEN** as a wrapper, while every named theorem in this chain is landed.

## 3. Locality and bounded Lean leaves

**PROVED:** `Localization/RowsBg.lean:i4a_local_rows` is the usable I-4a locality statement. For a component $Y$ and $S_Y=\mathrm{SY}(G,X_1,\mathcal C,Y)$ it assumes two `DecHyp`s, both small fixed points, equal external cut parameters, zeros outside
$\mathcal C$, agreement on relevant cubes, and `DataAgreeRows` on $S_Y$. Its conclusion is $\delta\alpha=\delta\alpha'$ on $S_Y$ and $\delta\phi=\delta\phi'$ on $Y$.
`DataAgreeRows` asks for $\alpha_0,\delta\Psi,f_1$ on $S_Y$, $\phi_0$ on `RowSite G a ν α0 SY`, and $\delta\Psi$ on collar neighbours. Plain `i4a_local` asks for all data on all $Y$ and is too strong: `i4b_local_rows` only gives background multiplier
equality on $S_Y$.
**OPEN, conditional on OPEN-REN-ROW-BRIDGE:** `i4b_local_rows` gives $\alpha_s=\alpha'_s$ on $S_Y$ and $\phi_s=\phi'_s$ on `RowSite G a ν 0 SY` under raw agreement on `RowsDep(SY)`. `FootprintMargin.lean:biUnion_resDep_subset`,
`biUnion_approxDep_rowSites_subset` and `RowsBg.lean:rowSite_subset` control the read region. For the same $\xi$, $\Delta\nu$ and $\zeta$ agree. The needed short new fact is that replacing the zero potential by $\alpha_s+\Delta\nu$ does not enlarge
the off-diagonal `RowSite`, since this shift changes only the diagonal; together with root read containment, this supplies `DataAgreeRows` from `RawAgree (Ysites \mathcal C)`. At full level the collar condition is empty. This is
**OPEN-REN-ROW-BRIDGE**, not a new Green estimate.
For `locDφ`, the point $p$ lies in $X_1\subseteq Y$, so equality of $\delta\phi$ on $Y$ suffices. For `locC2`, `renC2Site` reads $\delta\phi$ at each root site and at every nonzero row of `dirichletOperator G a 0 (α_u+ν_u)` from it, and $\alpha_u$ at
the root. `RENINPUTS.md`'s proposed `rootBlock_subset_SY` puts roots in $S_Y$; `rowSite_subset` puts their row reads in $Y$. Prove equality of these rows via diagonal mass-shift and `i4a_local_rows`; then `renC2On` agrees termwise. `levelLocalCover`,
`RenormLocFibre.lean:renLoc_fin_domains` supply the same proper cover and `renLoc_localization_expansion_fin` supplies the same fibre sum and rate as `locC1`.

The following are **proposed** declarations, not landed citations. Each leaf is bounded by 300 lines; a dependency on an open leaf remains explicit.

| Order | Statement in landed vocabulary and dependency | Size, assignment, start |
|---|---|---|
| 1 | `renMass_strict_data`: for `XiCOneReal`, cuts from `extParams`, $r<r_0$, prove `StrictDataM G N false D0 D1 Eren`, and `DecHyp` at $\delta_1(r)$, with the displayed `deltaStar'` margins. Reuse `renXiCOneReal_inUnionC7`, `renExtParams`, `i4b_exists_unique`, `XiCOne.mass_le`, `renMassU_sub_norm_le`. | 220–290; strong; start now with explicit margins. |
| 2 | `renDec_analytic`: define $E_{\rm ren}$ and compose `i4b_analytic` with `i4a_analytic ... false`; prove `AnalyticOnNhd` on the exact `expDom` and strict cut disc. | 160–250; strong; after 1 and `RENINPUTS` chart leaves. |
| 3 | `renDec_sharp`: use `i4a_exists_unique` at $\delta_1(r)$ plus analytic solver uniqueness at $D_1$; prove the two $K'_2b_*\varepsilon r$ bounds and zero at $\xi=0$. | 130–220; Sonnet; after 1–2. |
| 4 | `renDec_pertClass`: package $(\delta\phi_s,\alpha_s+\delta\alpha_s)\in\mathrm{pertClass}(G,V,A,\nu_u)$ and `SupBounds G δφ_s V`; retain the exact $+2$ in $A$. | 110–190; Sonnet; after 3; start now with bound premises. |
| 5 | `renDec_one_unique`: from `i4b_one`, P/U equality at zero defect, `isPerturbed_of_decFixed_one`, `isPerturbedM_iff`, and the `rho4`, `c6`, $r_F$ margins, show endpoint pair equals the `IsRenSol` pair. | 170–260; strong; after 3; start now with margins as hypotheses. |
| 6 | `renDec_row_agree`: from `RawAgree (Ysites 𝒞)` show `DataAgreeRows` for two shifted families; prove the row-site diagonal-shift and `RowsDep(SY)` containment. Reuse `i4b_local_rows`, `FootprintMargin`, and `RENINPUTS` root-read leaf. | 180–280; strong; start now in geometric subleaves if needed. |
| 7 | `renC2_local_cut` / `renDphi_local_cut`: apply `i4a_local_rows` to get equality on the exact `renC2On` rows / at $p$, with `rootBlock_subset_SY` for $C_2$. | 130–220 each; strong; after 5–6. |
| 8 | `locC2_zero` / `locDphi_zero`: state exactly `RenormExpInput.locC2` / `locDφ` at $K_{\rm loc}=1$, class radii $V,A$ above, all $M$, and rates $\kappa_a,\kappa_b\le2\kappa_{\rm dec}$; use `renLoc_localization_expansion_fin`, joint analyticity, endpoint equality, and locality. | 130–230 each; Sonnet; after 1–7 and the common `RENINPUTS` leaves. |

**Assessment.** These fields are harder than `locC1` because the shifted multiplier consumes a new $D_0$ margin, the source must be bounded twice (fixed analytic radius and sharp $O(r)$ radius), mode P must be converted to the physical equation at
$s=1$, and the functional reads Green-operator rows. The current landed abstract solver covers all inverse and analytic estimates. The remaining **OPEN** work is the stated numeric/data wrappers, the endpoint conversion, and the `RawAgree` to
row-read bridge; no new analytic inverse estimate is identified. Confidence: high in the mode and solver choice and exact class/uniqueness interfaces; medium in the proposed strict margins until reconciled with the physical tower; medium-low in
`OPEN-REN-ROW-BRIDGE` until every root row and raw footprint is checked in Lean.
