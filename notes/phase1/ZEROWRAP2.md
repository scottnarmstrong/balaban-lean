# ZEROWRAP2 — exact-site zero-class fibre step

**PROVED (source snapshot).** Read-only `/home/scott/Balaban` main `a45f885052266f196a68cd4bb8dcc0f369d8855e`, integration branch `w596-output-consts-k0` at `73e4103eb431941ca0554bfce632b5418e36a449` (13 October 2026). All declaration claims below refer to that branch. This is a proof plan; no Lean build was run.

## T1. Energy coefficient

**PROVED (generic interface).** `Balaban/Fluctuation/ParamCarrierLocal.lean:138`, `paramMarked_analytic_local_bound`, takes a single projection $\pi:E\to P$. Its `hA` asks equality of label activities for real $s\in[0,1]$ when each label's `ysite` lies in `Yhat Ω (sitesOf C)`; its `hG` asks the corresponding equality of rooted marks. It then returns analyticity, $\pi$-locality, and the CPE bound for the same `gsumCoeff`.

**PROVED (exact mark supplier).** `Balaban/Inhabited/E1CoeffFamily.lean:327`, `e1CoeffFamily_value_fromTower`, already chooses $F_1$, `Sol`, labels, $A_0$ and one $c_z(\theta,C)$ with analytic, thick-local, bounded, supported, all-fibre value clauses. With these *same* witnesses and $\pi_C\theta=\operatorname{physRestrict}(\operatorname{sitesOf}C)(\operatorname{physIncl}\,2\,S\,\theta)$, `Balaban/Inhabited/E1CoeffFamily.lean:242`, `e1Mark_hG_rawY_fromTower`, supplies `hG`. Its underlying `markedOutDec_decMarkCorrTerm_hG_rawY` is in `E1ParamRawLocal.lean:589`; `physRestrict_physIncl_eq_iff` gives raw agreement on the rooted output's own sites and `Yhat_univ` reduces the enclosing set to `sitesOf C`.

**REFUTED (the requested old-lemma call).** `E1ParamRawLocal.lean:336`, `commonAct_zeroSourceAct_hA`, has an `hπ` requiring $\operatorname{agreeOn}(\operatorname{thickSet}_{G'}Y)$ for every $Y\subseteq\operatorname{Yhat}(\operatorname{sitesOf}C)$. Exact $\pi_C$ equality gives agreement on `sitesOf C`, not on its thickening. No W592 lemma discharges *that* `hπ`; invoking it with $\pi_C$ would be a false proof step.

**PROVED (W592 ingredient); OPEN (two short helpers).** `ObsSourceLocal.lean:87`, `labelActFamilyOn_local_scaled_rawY`, states, for **every complex** $u$, that two parameters of `V` whose raw data and sources agree on a label's own set have equal label activity. `E1ParamRawLocal.lean:61`, `zeroSource_mem_physVq`, puts the zero-source versions in `V`. Prove `commonAct_zeroSourceAct_H_local_rawY` by the `inl`/`inr` split of `commonAct_zeroSourceAct_H_local_raw` at line 85, replacing its thick activity call by `labelActFamilyOn_local_scaled_rawY`; the `inr` activity is zero. Then prove `commonAct_zeroSourceAct_hA_rawY`: split $\pi_C\theta=\pi_C\theta'$ with `physRestrict_physIncl_eq_iff`, apply `Yhat_univ`, restrict raw agreement to each `inl` label, and call the new complex-$u$ helper at $u=s$. This gives precisely `paramMarked_analytic_local_bound.hA` for the exact $\pi_C$.

**OPEN (in-place edit).** Append to the existing `∀ C` block of `e1CoeffFamily_value_fromTower`, after its thick-local clause, the following conjunct for the *same* $c$:

```lean
∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
  physRestrict (sitesOf C) (physIncl 2 S θ) =
    physRestrict (sitesOf C) (physIncl 2 S θ') → c θ C = c θ' C
```

**OPEN (proof).** Keep the old `hmain C` for its analytic/bound/thick clauses. Invoke `paramMarked_analytic_local_bound` a second time with $\pi_C$, `commonAct_zeroSourceAct_hA_rawY` for `hA`, and `e1Mark_hG_rawY_fromTower` for `hG`; project only its locality component. The carrier, root, mark and value witnesses remain unchanged. If the exact mark theorem's preconditions do not match the existing `hP` fields definitionally, bridge them locally without choosing a new mark family. The estimated proof change is below 200 lines.

**OPEN (threading).** `E0CoeffFamily.lean:187`, `e0CoeffFamily_value_fromTower`, copies the nested $c$ block; append the exact conjunct there and project it from the strengthened E1 theorem. `StepIdentityFibreFamilies.lean:87`, `stepIdentity_zeroClass_fibre_fromTower`, copies that nested block; append and project it again, preserving its single choices of $F_1$, `Sol`, $A_0$, $c_z$, `dz`, $e_0$, and the identity. `StepIdentityFibre.lean:337`, `stepIdentity_zeroClass_fibre_of_values_fromTower`, only needs value identities and does not need a locality edit.

**REFUTED (determinant shortcut).** Do not append exact locality to `dz` or $e_0=dz+c_z$. Their landed statements use `thickSet (Yhat (sitesOf C))`; the determinant enters the site record through its separately grouped collar term. Exact locality here is for the marked $c_z$ alone.

## T2. Observable coefficient

**PROVED (generic exact result).** `ObsCoeffExactSites.lean:168`, `obsCoeffParam_local_of_Ev_physRestrict`, yields exact $\operatorname{physRestrict}(\operatorname{sitesOf}C)$ locality for the same `obsCoeffParam` and `Ev`. It needs `hd`, sharp raw-site locality of `Ev`, and `hAloc`: for *every complex* $u$ and a label supported in $Z$, equality of activities both at $(e.1,0)$ and at $e$ when raw data and sources agree on $Z$. `ObsCoeffAnalytic.lean:264`, `obsEv_fromTower_rawY`, supplies `hd` for the `Ev` chosen in `ObsFamilyJoint.lean:46`, `obsFamily_full_fromTower`; the latter currently exposes only thick locality.

**REFUTED (real interpolation shortcut).** `ParamActivityPhysical.lean:409`, `physical_labelActFamily_local_rawY`, only gives real $s\in[0,1]$ and cannot supply `hAloc`'s complex $u$ quantifier. `ObsSourceLocal.labelActFamilyOn_local_scaled_rawY` *does* have every complex $u$, but the tower theorem still needs to expose that property for its chosen `A`.

**OPEN (missing tower export, about 80 lines).** `ObsTiltLabels.lean:282`, `obsTiltLabels_local_fromTower`, chooses the base activity `A` and exposes thick locality for it; its proof at lines 460–479 substitutes `hAeq` and calls `labelActFamilyOn_local` twice, once at zero source and once at $e$. Append a second, exact raw-site locality conjunct to this theorem and repeat that short proof with `labelActFamilyOn_local_scaled_rawY`, restricting `agreeOn Z` and source equality to the chosen label's `ysite`. Membership of $(e.1,0)$ follows from its existing `hsub` and $q>0$. This gives W600's **all-complex** `hAloc` directly for the same `A`; W600 itself transports the base activity through `physAct`, `physActObs`, and `tiltActObs` using `ObsSourceLocal.lean:129,145,165`. No separate `physAct_H_local_of_family_rawY` is needed. No tower theorem exposing this exact `hAloc` is landed on the branch.

**OPEN (in-place edit).** Pass the new exact `hAloc` through `obsFamily_full_fromTower` and add exact `physRestrict(sitesOf C)` locality as a second locality conjunct in its *same* `∀ T'` block, using `obsCoeffParam_local_of_Ev_physRestrict` with the chosen `Ev`; keep its thick clause, analytic/bound/support clauses and all-fibre value. Carry the conjunct through `StepIdentityFibreObs.lean:56`, `obsFamily_pair_fibre_fromTower`, and `ObsFamilyPrefactor.lean:153`, `obsFamily_prefactor_fromTower`, where those conclusions quote the family locality. The prefactor theorem supplies $C\,\operatorname{obsPrefactor}(p,s,\beta3^k)e^{-(3/2)\kappa_{dec}d_{Ext}(C)}$ with scale-independent $C$; `ObsPrefactorScale.lean` gives subsequent birth-scale comparisons, not the family locality. `RootTermFamily.lean:36`, `rootTermFamily_of_cubeFamily`, can regroup the resulting source-local cube family to site sets; its stronger entropy/rate assumptions must be checked separately if its conclusion is used.

## T3. Physical record and final wrapper

**PROVED (record interface).** `RenormPhysicalRecord.lean:50`, `renormPhysicalZero_onFibre_half_of_families`, takes $R:\operatorname{StepTowerTheta}(\kappa_{min})$, $\operatorname{renDetFibreMin}\le\kappa_{min}$, $k\ge1$, $3\mid N_1$, $N_1>5$, $0\le\nu$, $\nu3^{2(k+1)}\le1$, $\beta>0$, $p_1$, `Xcut`, $g$, $q\le1$, $\|g\|_1<q$, and two cube families $c_E,c_M$. It takes ten family hypotheses: analytic `hanE`, exact-site `hlocE`, bound `hbdE`, polymer support `hsuppE`, all-fibre `E1locC` value `hvalE`; and the analogous `hanM`, `hlocM`, `hbdM`, `hsuppM`, all-fibre $M0C=\sqrt{\beta_U}\sum c_M$ value `hvalM`. It returns one `F`, one `Fcut`, `IsRenSol`, cutoff analyticity/agreement, and a `RenormExpInputOn` on the constant-$h_0$ fibre. `renormPhysicalZero_onFibre_half_consequences` at line 190 projects the four `IsLocExp` clauses.

**OPEN (hypothesis suppliers once T1/T2 land).** Set $S=R.\mathrm{toStepTower}.\mathrm{step}$, $q=1$, $\kappa=\kappa_M=R.\kappa'=\tfrac32R.\kappa_{dec}$, $B=K_0(3,3,R.\kappa_0)$, and $B_M=C\operatorname{obsPrefactor}(p,s,\beta3^k)$ from the strengthened `obsFamily_prefactor_fromTower`. `hanE,hlocE,hbdE,hsuppE,hvalE` are respectively E1's analytic, new exact, bound restricted to polymer supports, support, value clauses; `hanM,hlocM,hbdM,hsuppM,hvalM` are the corresponding observable clauses at $q=1$ (restrict `physVq` to `physV` for W599). $B,B_M\ge0$ follow from the landed positivity bounds. `stepHullMin_le_renDetFibreMin` (`RenormDetFibreTower.lean:135`) supplies the energy threshold from $R$'s threshold. W599 itself joins the determinant in its site record; passing the old `dz` as `cE` would be wrong.

**PROVED (exact W599 output budgets).** Its common rate is $\min(\tfrac32R.\kappa_{dec},\min(\kappa,\kappa_M))=\tfrac32R.\kappa_{dec}$ at these choices. The energy budget is $B_{det}^{site}+B$, where $B_{det}^{site}=\operatorname{hullConst}(3,3,\operatorname{towerDetRate}R.\kappa,\operatorname{towerDetConst}R.\kappa)\,e^{c_1(3,3)\log2}\,e^{\operatorname{hullRate}(3,3,\operatorname{towerDetRate}R.\kappa)}$; the observable budget is $B_M$; both old budgets are zero. The cover is `renYs ∪ Ssite`, with `Ssite = Finset.univ.image (sitesOf ·)` rendered as finite site sets; the distance is `renDY`. For $0\le\varepsilon_R\le R.r_0$, the three root terms have respectively budgets $9(c_K e)^2W(B_z)\varepsilon_R$, $\frac{17}{32}\,2(3+A)(c_KK_2B_R)^2W(B_z)\varepsilon_R^2$, and $B_{det}^{site}+B$, where $e=R.t/2$, $B_R=8e$, and $A$ is exactly the `bgK1/xiC1` plus $c_KcK_2B_RR.r_0+2$ expression at `RenormPhysicalRecord.lean:257`. The observable plus first component of $F$ has budget $B_M+c_KcK_2B_R\varepsilon_R$. The fourth projected clause requires only $\varepsilon_R\le R.r_0$ in Lean; restrict it to $\varepsilon_R\ge0$ in the wrapper.

**OPEN (exact final wrapper target, explicit witness order).** Let $R:\operatorname{StepTowerTheta}(\kappa_{min})$, $\operatorname{renDetFibreMin}\le\kappa_{min}$, $A_1,C_R>0$, $p\in\mathbb N$, $0<s<1/2$. There exist $\beta_*\ge3$ and scale-independent $C_E,C_M\ge0$ such that, for *every* $k\ge1$, $3\mid N_1$, $N_1>5$, $0<\nu$, $\nu3^{2(k+1)}\le1$, $\beta\ge\beta_*$, $0<p_1\le pLog(A_1,p,\beta3^k)$ and `Dsc : StepScaleData R.toStepTower …`, there exist **before $D'$ and $g$** one common energy witness list $(F_1,\mathrm{Sol},L_E,A_E,c_E,d_z,e_0)$ and one observable witness list $(L_M,A_M,Ev_{y,i},c_M)$ and one renormalization solution $F$; for all constant-$h_0$ chart data $D'$ and all $\|g\|_1<1$, the following conjunction holds simultaneously:

```text
(a) E0locC(z;D') = ΣY e_z(D',Y), Y rooted IsDj,
    |e_z(D',Y)| ≤ (Bdet_site + K0 3 3 R.κ0) exp(-κout sizeJ(Y));
    the marked summand cE has exact physRestrict(sitesOf C) locality.
(b) M0C(g,y,i;D') = sqrt(βU) ΣY m_{y,i}(D',g,Y), Y rooted IsDj,
    |m_{y,i}(D',g,Y)| ≤ CM obsPrefactor(p,s,β·3^k) exp(-κout sizeJ(Y));
    cM has exact physRestrict(sitesOf C) locality.
(g) IsLocExp for C1, C2, Eu on Dom = XiCOneReal(..., R.t/2) ∩ {h=h₀},
    over renYs ∪ Ssite, renDY, κout, 0 ≤ εR ≤ R.r₀, with W599 budgets.
(h) IsLocExp for βU^(-1/2) M0C(g)+F₁ on the same Dom/cover/rate/radius,
    with W599 budget BM+cK K₂ (8·R.t/2) εR.
identity: TstepC_zeroClass(D',g) = exp(-β AnewC(D') - Eppp(D') nU(D')
    + FcompAtC_zeroClass(D',g) + Σz ΣC e0 z (rawOf D',0) C
    + Σy,i g(y,i) ΣC cM y i (rawOf D',g) C).
```

**OPEN (proof of wrapper).** Use the strengthened `stepIdentity_zeroClass_fibre_fromTower` at $q=1$ for the *same* $c_E,c_M$ and its exponential identity; use the site grouping `markFibre_sitesOf`/`Thm31SiteDomains` and the W599 record and consequences for (a),(b),(g),(h). Thresholds are combined by `max`. The identity retains `-Eppp·nU`, the bare `FcompAtC` pairing, and the physical determinant already inside $e_0$; there is no logarithm selection. W599's theorem quantifies $g$ **before** its existential $F$, so merely applying it separately does **not** prove the displayed shared-$F$ prefix. Its proof first calls `renLoc_fields_union_scale_of_tower_at` independently of $g$ (`RenJoinClassWitness.lean:101`) and then builds the physical record; factor this chosen $F$ into a short uniform-g variant of W599, or prove a compatible uniqueness theorem. Until then, the weaker $\forall g\,\exists F_g$ wrapper is available conditionally on T1/T2, while the requested shared-$F$ theorem is OPEN.

**REFUTED (stronger interpretation).** This statement fixes $d=L=3,N=2$, the zero class, and the fibre $h=h_0$; it uses cube coefficients regrouped by `sitesOf`, the unit $\ell^1$ source ball, rate $\kappa_{out}=3\kappa_{dec}/2$, and the union site cover. It does not assert the paper's local chart, $\sqrt2$ rotation radius, paper $\kappa_a,\kappa_b$ or prefactors, reality, symmetries, or nonzero old/boundary channels. `RootTermFamily_of_cubeFamily` can produce source-local site coefficients, but its extra decay assumption must be verified before substituting its stronger field for the regrouped one.

## T4. Owned leaves and confidence

| Order/status | File owner and bounded leaf | Dependency / concurrency |
|---|---|---|
| **OPEN 1** | `E1ParamRawLocal.lean`: `commonAct_zeroSourceAct_H_local_rawY`, `commonAct_zeroSourceAct_hA_rawY`; about 70 lines. | W592 landed; energy owner alone. Parallel with leaf 3. |
| **OPEN 2** | `E1CoeffFamily.lean`: exact $\pi_C$ call and added $c$ conjunct; `E0CoeffFamily.lean`: nested projection; about 180 + 35 lines. | After 1; energy owner. Parallel with 3. |
| **OPEN 3** | `ObsTiltLabels.lean`: append exact all-complex `hAloc` for its chosen base `A` using W592's raw-site lemma; about 80 lines. | W592/W600 landed; observable owner alone. Parallel with 1–2. |
| **OPEN 4** | `ObsFamilyJoint.lean`: pass `hAloc` and add the same-`Ev` exact conjunct; `StepIdentityFibreObs.lean` and `ObsFamilyPrefactor.lean`: projections; about 150 + 35 + 35 lines. | After 3; observable owner. Parallel with energy owner. |
| **OPEN 5** | `RenormPhysicalRecord.lean` or new `RenormPhysicalUniform.lean`: factor W599's $g$-independent `F` choice into a uniform-g record; about 180 lines. | W599 landed; renorm owner can start alongside 1 and 3. At most these three owners at once. |
| **OPEN 6** | `StepIdentityFibreFamilies.lean`: thread exact $c_E,c_M$ clauses through existing existential order; about 100 lines. | After 2 and 4; one integration owner. |
| **OPEN 7** | New `PhysicalZeroJoin.lean`: one threshold, site grouping, W599's ten suppliers, four projections and identity; split into two declarations if 300 lines is insufficient, each at most 300. | After 2,4,5,6; one integration owner. |

**PROVED (confidence in inspection).** High for cited declaration types, quantifier mismatch, and the false `hπ` shortcut; medium for the helper sizes and the same-witness threading; low for final elaboration until leaves 1–7 build. **OPEN (verification).** No source file was edited and no build was run for this note.
