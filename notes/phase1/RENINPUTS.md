# RENINPUTS: physical inputs to renormalization localization

**Scope and status.** This audits `RenormExpInput.locC1`, then `locC2` and `locDφ`, against the current read-only Lean tree. `PROVED` means a landed declaration or the indicated immediate deduction; `PROVED CONDITIONAL ON` names a proved result whose hypotheses still need supply; `OPEN` names a missing bridge.
Paths below are relative to `Balaban/` in `/home/scott/Balaban`. The earlier reduction in `notes/phase1/LOCREN-2.md` predates `Fluctuation/RenormLocFibre.lean` and describes some now-landed work as open.

## 1. Input ledger for `locC1`

Fix $d=L=3$, $N=2$, $K=k+1$, $a=\mathrm{compWeight}(3,1)$, the full-level $G=\mathrm{lvTop}(N_1,m_1,k,\rho_{\rm sep}(m_1))$, and lower-level $H=\mathrm{lvLow}$.

| Input | Status and exact source | Remaining distinction |
|---|---|---|
| `OPEN-COVER-PARAM` | **PROVED** geometry: `Fluctuation/LevelLocalCover.lean:levelLocalCover` supplies `CovSetup`, $X_{1,z}=\mathrm{nbhdF}(1,\mathrm{blockSite}(k,z))$, an attaining tree, $\Delta=0$, block inclusion and `BlockMargin`. `Fluctuation/RenormLocFibre.lean:renLoc_fin_domains` supplies `RenLabel`, `renCube`, `renYs`, `renDY`, legal/injective labels, and disjoint patches. `Localization/I5Glue.lean:ParIdx`, `extParams`, `extParams_par`, `extParams_one` are the landed physical parameter model. | `RenLabel G X₁` and `ParIdx G X₁` are nested subtypes with the same predicate, requiring a small equivalence/transport; the explicit `extParams` composition for `renC1On` is **OPEN**. |
| Physical hypotheses | **PROVED** at general scale: `Fluctuation/InteractionEngine.lean:FlCore` has `hS : DecSpecs`, `Sp : DGSetting`, `HBp : BgHyp`, `hκ`, `hM`, smallness and $c_7$ margin. `Inhabited/StepActivityDirectPhysicalRates.lean:tower_core_rates` chooses these constants; `Inhabited/LevelRayTower.lean:flCore_level_transfer` transfers them; `Inhabited/LevelStepSetting.lean:dgSetting_lv`, `bgHyp_lv`, `hatConn_lvTop` supply the physical instances. `Inhabited/SourceActivityScale.lean:sourceActivityC_scale` shows the every-scale quantifier pattern. | `HatConn` is separate from `FlCore`. Its level theorem is landed. `FlCore.SM` is `FootLocal (coverOf G) H` for the *lower* fluctuation operator, not the renormalization background class. |
| `OPEN-NC-PHYSICAL` | **REFUTED** as a claim that NC is a field of `FlCore` or an unproved physical self-cover hypothesis. `Localization/NC3.lean:pointwise_cut_cube`, `laplacian_cut_cube`, `holder_pair_cut_cube` prove the cut-cube estimates; `Localization/DecoupledCube.lean:cubeBlockBounds_exists` and `Localization/Decoupled2Self.lean:coverBase_self`, `coverLocal_self` package the required NC field for `coverOf G` from `DGSetting`. Original `Localization/DecoupledBackground.lean:i4b_exists_unique`, `i4b_analytic` already work from `DecSpecs`, `DGSetting`, `BgHyp` and numeric margins. | NC would be new only for a genuinely different auxiliary `DecCover`; `locC1` can use the physical `coverOf G`. `CoverBase.nc` is the selected block estimate, while NC3 also has the Hölder theorem. |
| `OPEN-BG-INPUT` | **PROVED CONDITIONAL ON** the strict datum inclusion and a new class-bound wrapper: original `i4b_exists_unique`, `i4b_analytic`, `i4b_one` give the physical analytic decoupled background, its bounds, and $s=1$. | Uniform `bgClass G ν (c_K ε) D` for *complex* $s$ is **OPEN** as a stated Lean lemma; its elementary proof and constant are in §3. |
| `OPEN-AGREE-BRIDGE` | **OPEN**, a different functional/read set. `Localization/I5.lean` proves locality for the interaction under agreement on `thickSet G (Ysites ...)`, whereas `HasLocPrinciple` requires `RawAgree Y` for `renC1On`. | Need a targeted proof for the block average, block sites, and bond neighbours from `RawAgree (renYs ...)`; §4 states the exact gap. |
| `OPEN-CHART` | **PROVED** inclusion into the unshifted data domain; **OPEN** only the short analytic composition from `extParams` and the global `i4b_analytic` family to the exact `renC1On` map. | No ambient openness of `XiCOneReal` is required. §2 gives the inclusion and explains `AnalyticOnNhd`. |
| `OPEN-TRANSPORT` | **PROVED** by `RenormLocFibre.lean:finOf`, `coe_finOf`, `mem_renYs`, `renLoc_fin_domains`, `renLoc_fibre`, `renAgg_norm_le`, `renLoc_localization_expansion_fin`. | No new finite-set conversion or fibre inequality is needed. |

The general-scale fluctuation theorems show that the physical decoupling infrastructure is available. They do **not** prove `locC1`: their functional is the interaction or source term at its own datum, while `locC1` is the $C_1$ density on every `XiCOneReal` datum with a universal class bound.
`sourceActivityC_scale` itself is at the central real datum, not a chart family.

## 2. The fixed-$h$ chart and analyticity

`Fluctuation/RenormExpBounds.lean:XiCOneReal` says there exist a real $\Psi_0$, a real constant vector $h_0$ and a complex $\Psi''$ such that $\Xi^c_G(a,\nu;K,1,\varepsilon)(\Psi_0,h_0,\Psi'',0)$ is realized by $D$. The real $h_0$ varies with $D$.

**PROVED**, by unpacking the definitions: for the full-level $G$ and $n=K$, $\Xi\mathrm{COneReal}(G,a,\nu,\varepsilon,D)\Rightarrow\Xi\mathrm{CData}(G,a,\nu,K,1,\varepsilon,D)$, using the same witnesses and $h''=0$. No loss in $\varepsilon$ or in $t=1$ occurs.
`Localization/I5Chain.lean:xiCData_inDomainC` then gives $\mathrm{InDomainC}(G,\nu,\delta,\delta,D)$ with $\delta=\mathrm{xiC1}(3)\varepsilon$ from `FlCore.small1`.
`inUnionDomainC_of_inDomainC` gives $\mathrm{InUnionDomainC}(G,\mathrm{bgC0},c_7,\nu,D)$ using `FlCore.c7le`, $\delta>0$, $c_7\le\mathrm{bgC0}$ and `HBp.massLe`.
This last arithmetic transport should be exposed as a named short lemma; it is not a new field estimate.

`Fluctuation/RenormExpCauchy.lean:expDom` consists of pairs $q=((D.\Psi,D.h),\xi)$ with $D$ in the stated domain and $\|\xi\|<r_0$.
`Fluctuation/RenormExpG.lean:HasLocPrinciple` requires `AnalyticOnNhd ℂ (term Y) (expDom ...)`: each term must be ambient analytic **at each point of that set**. The set need not itself be open.
`Fluctuation/RenormExpG.lean:renormExpInput_witness` proves this for whole-torus terms by composing `theorem72_analytic` with projection onto raw data and `IsRenSol.analytic` with projection onto $\xi$; it does not silently freeze $h_0$.

For a proper cover use `i4b_analytic`, whose function is defined on all `DecParams G × RawData` and analytic at every strict cut parameter and every raw datum in the union domain at $c_7$.
Composition with `extParams`, projection of $q$, and `Fluctuation/RenormExpG.lean:an_renC1On` gives the required ambient analyticity, then `Localization/I5Param.lean:analyticOnNhd_coef_of_analyticOnNhd` passes it to coefficients without openness of the chart.
**OPEN-CHART** is this Lean composition and the named strict inclusion, not a new chart or a restriction to one constant $h_0$.

## 3. The complex-$s$ background class

`Fluctuation/RenormExpBounds.lean:bgClass G ν c D` has three clauses, for each $x\in\Omega_1$: $\|\Psi(x)-Q\phi(x)\|\le c$; both forward and backward differences of $\bar\phi$ in each direction have norm at most $c/\ell(x)$; and $\nu\ell(x)^2\|\phi(x)-h(x)\|^2\le c^2$.
Here $Q$ is `blockAvg`, $\bar\phi$ is `barField`, and $\ell(x)=G.spacing(x)$.

**PROVED CONDITIONAL ON** `i4b_exists_unique` at $\delta=\mathrm{xiC1}(3)\varepsilon$: it yields `BgBounds G D φ_s α_s (K4 3 3 2 BG κ · δ)` and `SupBounds` of $\phi_s-\mathrm{approxField}$ with constant $cK2'\,\mathrm{lemma53Const}\,\delta$.
The `BgBounds` value and gradient clauses alone do not literally state `bgClass` because its first clause contains $Q$ and its third compares to $h$.

`XiCOneReal.factors` gives $\Psi-Q\phi_1<2\varepsilon$, bond gradients $<2\varepsilon/\ell$, and $\nu\ell^2\|\phi_1-h\|^2\le4\varepsilon^2$ for $\phi_1=\mathrm{bgFieldC}$. `i4b_one` identifies $\phi_{s=1}=\phi_1$.
The two `BgBounds.val` estimates give $\|\phi_s-\phi_1\|\le(K_4+\mathrm{bgK1})\delta$ sitewise.
`SmallField/FinalCutoff.lean:blockAvg_sub_const_le` gives the same bound for the difference of block averages; `BgBounds.grad` directly bounds the two bond differences of $\phi_s$.
Since $\nu\ell^2\le1$, the triangle inequality and the square bound for $\phi_1-h$ give $\sqrt{\nu}\ell\|\phi_s-h\|\le[2+(K_4+\mathrm{bgK1})\mathrm{xiC1}(3)]\varepsilon$.

Thus a sufficient constant fixed **before** $k,N_1$ is $c_K=2+(K_4(3,3,2,BG,\kappa)+\mathrm{bgK1}(3,3,2))\mathrm{xiC1}(3)$ (or any larger constant). The value and gradient estimates then fit $c_K\varepsilon$ as well.
Positivity and the square of the last inequality finish `bgClass`.
**OPEN** is the Lean wrapper carrying the pointwise vector norms, averaging, and square arithmetic for all strict complex $s$.
The tower gives uniform $BG,\kappa,\varepsilon=t$; no scale-dependent $c_K$ is allowed.
A request for additional smallness of $c_Kt$ must be paid by a stronger tower choice, not assumed from `tower_core_rates` without checking its inequalities.

## 4. Root reads and locality

`renC1On G a ν ε (blockSites ... z)` reads $\Psi,h$ at block sites; $Q\phi$ reads the entire $G$ block of each site; `bondSite` reads $\bar\phi$ at $x$ and $x+e_\mu$ (including collar values of $\Psi$).
At full level, all sites of the root block have the same $G$ block.
`levelLocalCover` proves `blockSites ⊆ nbhdF` and `BlockMargin` for that block; `Fluctuation/PhysicalReadsV.lean:multiplier_reads_subset_X1` turns this margin into $\mathrm{resDep}_G(x)\subseteq X_1$ for every multiplier site in the root block.
**PROVED as a direct geometric deduction (proposed Lean wrapper `rootBlock_subset_SY`):** for every cut family $C$ and its component $Y=\mathrm{compY}(C)$, the root block lies in `SY G X₁ C Y`. Indeed, `BlockMargin` gives, for each root site $x$, a centre $q$ with $x\in\mathrm{intBox}(q)$, $Qset(q)\cap\mathrm{parCubes}(X_1)=\varnothing$, and $\mathrm{hatBox}(q)\subseteq X_1\subseteq Y$; hence $q\in\mathrm{ZY}(G,X_1,C,Y)$ by the landed definition and $x\in\mathrm{SY}$.
`levelLocalCover` also proves `readSites H k z ⊆ nbhdF`, but those are the **interaction** reads, not by definition all `renC1On` reads.

`Localization/PolymerGeometry.lean:subset_compY`, `compY_subset_Ysites` give $X_1\subseteq\mathrm{compY}(C)\subseteq Ysites(C)$.
`Localization/FootprintMargin.lean:footprint_subset_component`, `biUnion_resDep_subset`, `biUnion_approxDep_rowSites_subset` put residual and row footprints of sites in `SY` inside the component.
`Localization/RowsBg.lean:i4b_local_rows` can compare the background at row sites under this narrower footprint agreement.
A concrete **OPEN-AGREE-BRIDGE** must prove the root block, its $Q$ sites, and bond neighbours lie in the comparison region where that theorem gives field equality, and that their raw/collar reads lie in $Ysites(C)$.

There is no landed lemma asserting `RawAgree (finOf (Ysites C)) ⇒ agreeOn (thickSet G (compY C))`.
The generic I-5 proof instead assumes agreement on `thickSet G (Ysites C)` (`Localization/I5.lean`); `thickSet` explicitly adjoins every `resDep` of every site in its argument (`Localization/I5Local.lean:thickSet`).
`RawAgree Ysites` cannot be replaced by that stronger premise in the `HasLocPrinciple` field.
`i4b_local` similarly asks for `resDep` agreement for **all** sites of the component.
The targeted row/root argument above is the cheapest plausible route; if it fails, the output domains or their counting theorem must change.
This is a genuine **OPEN** geometry/locality assertion, not supplied by `sourceActivityC_scale`.

## 5. Exact every-scale target and proof chain

**OPEN — proposed `locC1_zero` statement.** Fix $\kappa_0=\mathrm{aEnt}(3,3)+1$ and $\kappa_{\rm dec}$ satisfying the hypotheses of `tower_core_rates 2`; choose any $0\le\kappa_a\le2\kappa_{\rm dec}$.
There exist $m_1\ge4$, $c,BG,\kappa,t,c_K,r_0,\beta_0$ with $t>0$, $0<r_0\le1/16$, $\beta_0\ge2$, the `FlCore` and rate margins of `tower_core_rates`, and the displayed uniform $c_K$, such that **for every** $k\ge1$, $N_1$ with `[NeZero N₁]`, $3\mid N_1$, $N_1>5$, every $\nu>0$ with $\nu3^{2(k+1)}\le1$, every $\beta\ge\beta_0$, and every block root $z$, `RenormExpInput.locC1` holds at `hatStepK` with $G=\mathrm{lvTop}$, $\varepsilon=t$, $B_z=\mathrm{blockSites}(k,z)$, $X_{1,z}=\mathrm{nbhdF}(1,\mathrm{blockSite}(k,z))$, $\iota_z=\mathrm{RenLabel}(G,X_{1,z})$, $Y_z=\mathrm{renYs}(\mathrm{renCube},G,1,X_{1,z})$, $d_Y=\mathrm{renDY}(G,1,Y)$, $K_{\rm loc}=1$, domain `XiCOneReal G a ν t`, radius $r_0$, class `bgClass G ν (c_K t)`, and output rate $\kappa_a$.
The $\beta$ quantifier matches `sourceActivityC_scale` but the $C_1$ producer does not use $\beta$.

In particular the principle transfers **every** $M$ satisfying $\|\mathrm{renC1On}(D,v,\xi)\|\le M$ for all admitted $D$ and $v\in\mathrm{bgClass}(D)$ at fixed $\|\xi\|<r_0$; it cannot be proved merely for the convenient numeric $M$.
That numeric choice follows from `RenormExpBounds.lean:norm_renC1On_le_of_mem` after the principle.
The terms must be analytic at all points of `expDom`, local under `RawAgree Y`, and sum to the true $C_1$ at the uncut background.

**PROVED CONDITIONAL ON OPEN-BG-CLASS, OPEN-AGREE-BRIDGE and the short parameter/chart leaves:** `tower_core_rates` and `flCore_level_transfer` give `FlCore`; `dgSetting_lv`, `bgHyp_lv`, `hatConn_lvTop` identify the physical pair; `renLoc_fin_domains` gives root geometry; `XiCOneReal → XiCData → InDomainC → InUnionDomainC` supplies strict data; `i4b_exists_unique`, `i4b_analytic`, `i4b_one` give $(\phi_s,\alpha_s)$; the class wrapper supplies the universal bound; `extParams_one` gives the value at $s=1$; `an_renC1On` gives joint analyticity; the agreement bridge gives `LocalityAEOn`; `renLoc_localization_expansion_fin` gives the finite expansion, locality, analyticity and $K_{\rm loc}=1$ bound.
Its rate premises are those stated in `tower_core_rates`: $\kappa_{\rm dec}\ge3\kappa_0+3$, $\kappa\ge4d(2L+1)^d\kappa_{\rm dec}$, $1\le(\kappa/2-1)/2$, and $\log((2L+1)^d(L^{m_0})^d)\le(\kappa/2-1)/2$ with $m_0=1$ and $d=L=3$.
There is no new fibre factor.

Lean leaves, in dependency order (each intended at most 300 lines; `start now` means its stated hypotheses can be formalized immediately):

| Order | New declaration target (proposed name; not a landed citation) | Size / assignment |
|---|---|---|
| 1 | `renXiCOneReal_inUnionC7`: the two definitional inclusions and strict union-domain arithmetic from `FlCore`. | 50–100 lines; Sonnet; start now. |
| 2 | `renExtParams`: equivalence `RenLabel ≃ ParIdx`, `extParams` at one/cut vectors, and physical `parCubes` zero/one laws using `CovSetup.polySetup` and `I5Glue.Pset_subset_of_not_disjoint`; `I5Local.lean:fan_local` contains the proof pattern. | 100–180 lines; Sonnet; start now. |
| 3 | `renBgClass_dec`: from `i4b_exists_unique`, `i4b_one`, `XiCOneReal.factors`, `BgBounds` and the explicit $c_K$, prove every complex-$s$ class membership. | 150–250 lines; strong; start now. |
| 4 | `renC1_analytic_cut`: compose `i4b_analytic`, `extParams` and `an_renC1On` on `expDom × polydisc`. | 100–180 lines; Sonnet; start now after 1–2. |
| 5 | `renC1_root_reads` and `renC1_local_cut`: prove exact root read containment and `LocalityAEOn` from `RawAgree Ysites`, using `i4b_local_rows` and `FootprintMargin`; split if either exceeds 300 lines. | Two leaves, 180–280 lines each; strong; start now with explicit read-containment premise, then discharge it. |
| 6 | `locC1_zero`: instantiate `renLoc_localization_expansion_fin`, carrying the universal $M$ quantifier, `extParams_one`, analytic terms and $K_{\rm loc}=1$. | 120–220 lines; Sonnet; after 1–5. |

## 6. Additional `locC2` and `locDφ` inputs

**PROVED** infrastructure: the same cover, parameter transport, chart embedding into the *unshifted* background domain, `renLoc_fibre` and `renLoc_localization_expansion_fin` apply.
`Fluctuation/RenormExpLemma35.lean:renMassU_sub_norm_le` gives $|\nu_u-\nu|\le(32/15)\nu\|\xi\|$ for $\|\xi\|\le1/16$.
`Background/Prop51Mass.lean:isPerturbedM_iff` identifies the complex-mass equation with the real-$\nu$ equation at base multiplier $\alpha_s+(\nu_u-\nu)$, including the mass times $\delta\phi$ term.
These are the right algebraic inputs, not a proof of the shifted solver hypotheses.

**OPEN-REN-DEC-FAMILY** is a genuinely different object from `FlCore.SM`: it needs mode-U `Localization/Decoupled2SolveAnalytic.lean:i4a_analytic` and `Localization/Decoupled2FieldLocal.lean:i4a_local` on the physical top-level field with shifted source $f_{1,s}=(\nu_u-\nu)(h-\phi_s)$ and $\zeta\Psi$, plus strict `DecHyp`/`StrictDataM` margins for every $D\in\Xi\mathrm{COneReal}$, complex $s$, and $\|\xi\|<r_0$.
The landed lower-level fluctuation mode in `FlCore.SM` has source $\psi'$ and operator on $H$, so it does not supply this family.
Proposed leaf `renMass_dec_data` (200–300 lines, strong, start now) proves the shifted data and numeric margins; `renDec_pert_family` (split into analytic and local subleaves, each ≤300 lines, strong) then applies I-4a.

**OPEN-UNIQUENESS-MARGIN:** at $s=1$, the new fixed point must satisfy `Small G δα (c6 3 3 2)` to invoke the `unique` field of `Fluctuation/RenormExpLemma35.lean:IsRenSol`; `isPerturbedM_iff` identifies its equation, but this strict smallness requires the radius and tower arithmetic.
Proposed `renDec_one_unique` (100–180 lines, Sonnet; start with explicit margin).

**OPEN-REN-CLASS:** `Fluctuation/RenormExpBounds.lean:renSol_mem_pertClass` proves class membership only for the genuine solution at $s=1$.
For arbitrary complex $s$, the new family must satisfy `SupBounds G δφ_s (c_K cK2(3,3,2)B\|\xi\|)` and $(\delta\phi_s,\alpha_s+\delta\alpha_s)\in\mathrm{pertClass}(G,c_K cK2 B\|\xi\|,\mathrm{bgK1}\,\mathrm{xiC1}\,t+c_K cK2 B r_0+2,\nu_u)$.
Proposed `renDec_pertClass` (150–250 lines, strong; after the family).
The `$+2$` belongs to the exact record class radius; it cannot be dropped.

**PROVED CONDITIONAL ON** those three open inputs, the `locC1` agreement bridge extended to the $C_2$ and point-evaluation reads, and the same analytic composition: apply `Fluctuation/RenormExpG.lean:an_renC2On` and evaluation to the shifted family, use uniqueness at one, then `renLoc_localization_expansion_fin` twice.
Proposed `locC2_locDphi_zero` (two leaves, each 120–220 lines, Sonnet; after the family) gives the two universal `HasLocPrinciple` fields at $K_{\rm loc}=1$ and rates $\kappa_a,\kappa_b\le2\kappa_{\rm dec}$.
`RenormInputZero.lean:renormExpInput_zero_of_fields` only assembles fields once these genuine producers exist; its zero/whole-torus witnesses do not establish proper-cover locality.

**Confidence.** High for the NC, parameter, chart and fibre status because the cited declarations and hypotheses were checked.
Medium for the proposed $c_K$ wrapper until its vector-norm arithmetic is formalized.
Lower for the targeted root agreement bridge: the existing I-5 locality theorem uses a strictly stronger stated agreement set, and no exact `RawAgree Ysites` theorem was found.
`locC1`, `locC2`, and `locDφ` remain **OPEN** in the physical proper-cover form.
