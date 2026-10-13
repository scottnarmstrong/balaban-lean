# RENJOIN: physical zero-class renormalization input at the half-radius fibre

**PROVED (snapshot).** The read-only Lean tree is `/home/scott/Balaban` at commit `eb85ad1d4f44f26238987cabcab4070ea9b79f4a`. All declaration names below occur there. `RENJOIN` is a proposed join, not a landed theorem.

## T1. The record, field by field

**PROVED (signature).** In `Balaban/Fluctuation/RenormExpInputOn.lean`, `RenormExpInputOn G a ν ε r₀ cK B F blk Ys YsM dY κa κb Kloc BE0 Bold BM0 BoldM E0θ oldE M0θ oldM Dom` has these eight fields. `Ys` and `YsM` are parameters supplied to the record; its type does not fix them to `renYs`.

| Status | Field and exact requirement | Physical zero-class supplier |
|---|---|---|
| **PROVED** | `sub`: $D\in Dom\Rightarrow D\in\Xi^c_1(G,a,\nu,\varepsilon)$. Mentions `Dom`, not $r_0,Y,d_Y,\kappa$. | Fibre predicate projection, as in `renormDetOnlyZeroM_onFibre_half`. |
| **PROVED** | `locC1(z)`: `HasLocPrinciple` on the **full** `XiCOneReal`, radius $r_0$, family `Ys z`, size $d_Y$, rate $\kappa_a$, budget $K_{loc}$; class `bgClass G ν (cK*ε) D`, functional `renC1On` on `blk z`, endpoint `bgFieldC`. | `renLoc_fields_scale_of_tower_at` supplies it on `renYs`; enlargement needs `HasLocPrinciple.extend`. |
| **PROVED** | `locC2(z)`: same full domain, radius, `Ys z`, $d_Y,\kappa_a,K_{loc}$; class `pertClass G (cK*cK2*B*‖ξ‖) (bgK1*xiC1*ε+cK*cK2*B*r₀+2) (renMassU ν ξ)`, functional `renC2On`, endpoint $(F_1,\mathrm{bgMultC}+F_2)$. | Same landed tower supplier and enlargement. |
| **OPEN** | `expE0(z)`: `IsLocExp` on `Dom`, radius $r_0$, `Ys z`, $d_Y,\kappa_a$, budget $B_{E0}$, for the physical $E_{0\theta}(z)$ at `renThetaDatum`. | Determinant part: `renE0_fibre_det_at`; marked part: W580 running, exact site locality still required. |
| **PROVED** | `expOld(z)`: same expansion data with budget $B_{old}$, plus each term zero at $(\operatorname{rawOf}D,0)$. | At zero class set `oldE=0`, $B_{old}=0$; `renormExpInputOn_zero_of_fields` uses `isLocExp_zero_cover`. |
| **PROVED** | `locDφ(p)`: full domain, radius $r_0$, `YsM p`, $d_Y,\kappa_b,K_{loc}$; class $\{v:\mathrm{SupBounds}(G,v,c_KK_2B\|\xi\|)\}$, evaluation $v(p)$, endpoint $F_1(p)$. | `renLoc_fields_scale_of_tower_at` on `renYs`, then enlarge. |
| **OPEN** | `expM0(p)`: `IsLocExp` on `Dom`, radius $r_0$, `YsM p`, $d_Y,\kappa_b$, budget $B_{M0}$, for $M_{0\theta}(p)$ at `renThetaDatum`. | `obsFamily_full_fromTower` supplies an analytic, bounded, thick-local family and all-fibre value; exact site locality and packaging remain. |
| **PROVED** | `expOldM(p)`: same expansion data with $B_{oldM}$ and zero terms at $\xi=0$. | At zero class set `oldM=0`, $B_{oldM}=0$ by `renormExpInputOn_zero_of_fields`. |

**PROVED (shared solution and numbers).** `renLoc_fields_scale_of_tower_at` gives one $F$ with `IsRenSol … ν e e r₀ (8e) F` and its three full-domain localization fields; `renormDetOnlyZeroM_onFibre_half` also gives an analytic cut map with endpoint $F$. Take $e=t/2$, $B=8e$, $c_K=\mathrm{renCK}(3,3,2,BG,\kappa)$, $K_{loc}=1$, $\kappa_a=\kappa_b=\kappa_{out}=3\kappa_{dec}/2$, $d_Y=\mathrm{renDY}(G,1)$, $B_{old}=B_{oldM}=0$. `renCK_ge` gives $c_K\ge1$; `cK2 3 3 2` is the $K_2$ in the record. The tower gives $r_0>0$, $r_0\le1/16$, and the smallness hypotheses used by the consumers. Take $0\le\varepsilon_R\le r_0$ for all four conclusions.

**OPEN (budgets).** With the split determinant/marks construction, $B_{E0}=B_{det}+B_{mark}$, where `renE0_fibre_det_at` supplies $B_{det}=\mathrm{hullConst}(3,3,\mathrm{towerDetRate},\mathrm{towerDetConst})e^{c_1\log2}e^{\mathrm{hullRate}}$ and the marked-family bound gives $B_{mark}=K_0(3,3,\kappa_0)$ after rate reduction. For the rescaled observable, the budget $B_{M0}$ is the coefficient-family prefactor in `obsFamily_full_fromTower` (its two summands), subject to exact locality and the source-domain alignment below. These are proposed record budgets, not yet a physical record.

## T2. One fibre, radius, domain family, size and rate

**PROVED.** `renormDetOnlyZeroM_onFibre_half` uses $Dom(D):=\Xi^c_1(G,a,\nu,e;D)\land(\forall x,i,\ D.h(x,i)=h_0(i))$ on the full-level $G=\mathrm{lvTop}$. `RenDom` uses $\Xi^c_1\land(\forall x\in G.\Omega_1,i,\ D.h(x,i)=h_0(i))$; `renDom_iff_of_forall_mem` identifies them here. `RenFibreDatum.exists_xiCOneReal_fibre_step` exhibits the step datum in this fibre, and `StepTowerTheta.renDatum_half_mem_xiCData` places its renormalized datum in the chart of radius $t$.

**OPEN (join definition).** For each root $z$ and observable site $p$, set $Y_E(z)=\mathrm{renYs}_E(z)\cup Y_{site}$ and $Y_M(p)=\mathrm{renYs}_M(p)\cup Y_{site}$, where $Y_{site}$ is the finite image of all `sitesOf T` at level $m_0=1$. Use the **same** $Dom,r_0,d_Y=\mathrm{renDY}(G,1),\kappa_{out}$ for every field; `Ys` and `YsM` are these union families. `renDY_eq_sizeJ_sitesOf` and `renDY_eq_dExt_of_isPolyDom` align a site coefficient's $d_{Ext}$ with this size; `IsLocExp.congr_dY_eq` transfers exact equality, and `.congr_dY` permits a weaker size. No relabeling of a site coefficient as a `renYs` term is asserted.

**PROVED (available transport).** `IsLocExp.mono_dom` restricts full-domain determinant or packaged site expansions to the fibre; `.mono_radius` restricts $r_0$ to $\varepsilon_R$; `.mono_rate` lowers a proved coefficient rate to $\kappa_{out}$ when the size and budget are nonnegative; `.extend` and `.add_union` give the union family and sum of budgets. `HasLocPrinciple.extend` enlarges the three principles at unchanged $K_{loc}=1$ only after a member of each class is exhibited at every full-domain $D$ and $\|\xi\|<r_0$.

**PROVED (class witnesses, conditional on the tower hypotheses).** For `bgClass`, `XiCOneReal.mem_bgClass` exhibits `bgFieldC` at $2e$ and `RenormSharedClass.bgClass_mono` together with `renCK_ge` enlarges to $c_Ke$. For `pertClass`, `renSol_mem_pertClass` exhibits $(F_1,\mathrm{bgMultC}+F_2)$ using the same tower $F$; `IsRenSol.sup` exhibits $F_1$ in the `SupBounds` class after $c_K\ge1$. Thus the mathematical nonemptiness needed by `HasLocPrinciple.extend` holds on the **full** domain; three short Lean wrappers applying these witnesses are still to be written. The zero vector need not belong to `pertClass`.

## T3. Observable source and normalization

**PROVED (signature).** `RenormExpInputOn` has `M0θ oldM : (G.Ω 1 × Fin 2) → BgData G 2 → (Fin 3 → ℂ) → ℂ`: it indexes the site $p=(y,i)$ but has no source binder.

**OPEN (physical definition).** For each fixed source $g$ with $\sum_{y,i}\|g(y,i)\|<q\le1$, define $M_{0\theta,g}(p,D,\xi)$ as the sum of the **same selected** `obsCoeffParam` family evaluated at $(\operatorname{rawOf}(\operatorname{renThetaDatum}(D,\xi)),g)$. Choose the family before $g$ and before $D$; then produce a record for each such $g$.

**PROVED (landed value).** `obsFamily_full_fromTower` states for every fibre chart datum $D'$ and allowed $g$ that $M_{0}^{(k+1)}(g;y,i;D')=\sqrt{\beta_U}\sum_{T'}\mathrm{obsCoeffParam}((\operatorname{rawOf}D',g),T')$. Hence the record's $M_{0\theta,g}$ equals $\beta_U^{-1/2}M_0^{(k+1)}$ on the whole renormalized fibre chart, since $\beta_U>0$. A value at the base datum alone would not identify the function of $(D,\xi)$ required by `thm31h_on`.

**OPEN (source packaging).** `isLocExp_of_coeffFamily_renTheta_tower` packages a family on `physV` for $g\in\mathrm{l1Ball}$; the observable theorem supplies `physVq`. Use $q=1$ (or prove the explicit `physVq` to `physV` restriction) and establish exact raw-data locality on `sitesOf T'`, retaining source agreement there. Then the generic package yields $B_{M0}$ for the **rescaled** observable; inserting an extra $\sqrt{\beta_U}$ into that budget would count the factor twice. `thm31h_on` adds $F_1(p)$ and at zero class gives $B_{M0}+c_KK_2B\varepsilon_R$, with $K_{loc}=1$.

## T4. Energy conclusion and paper constants

**PROVED.** `thm31g_Eu_zero_of_fields_on` assumes a zero-old-term `RenormExpInputOn`, $r_0>0$, $\varepsilon_R\le r_0$, and a root $z$; it returns `IsLocExp` on `Dom` at radius $\varepsilon_R$ with **budget $B_{E0}$** for $E_{0\theta}(z,D,\xi)$. In Lean, $E_u=E_{0\theta}+oldE$ (`thm31g_Eu_on`), not $E_{0\theta}(\xi)-E_{0\theta}(0)$. `.cauchy` applies only to the old terms because their component functions vanish at $\xi=0$; `expE0` is merely restricted in radius. At zero class $oldE=0$, so no source-variation term arises.

**OPEN (paper comparison).** The target paper energy budget at the same paper rate is $(2\cdot27\cdot BL+1)K_0$, with an old-action source-variation addition $C_5E_0\varepsilon_R$ outside the zero class (after matching its $K_0$ convention). `e0CoeffFamily_value_fromTower` proves this coefficient-scale bound and all-fibre value for $e_0=dz+c$, but gives thickened locality for $dz$ and $e_0$. It cannot alone supply `expE0` on exact site domains. The landed collar-grouped determinant budget plus a marked budget can supply a physical Lean record conditionally, but an inequality reducing their sum to the paper's $(54BL+1)K_0$ is not landed; the zero-class record cannot yield $C_5E_0\varepsilon_R$.

## T5. Ordered Lean leaves, each at most 300 lines

1. **OPEN (executable now; 80–160 lines).** `RenJoinClassWitness`: from `renLoc_fields_scale_of_tower_at`, `XiCOneReal.mem_bgClass`, `renSol_mem_pertClass`, `IsRenSol.sup`, and `renCK_ge`, prove the three full-domain nonemptiness premises, enlarge `locC1/locC2/locDφ` with `HasLocPrinciple.extend`. No exact locality input.
2. **OPEN (executable now under a named exact-locality hypothesis; 100–220 lines).** `RenJoinMarkedGivenExact`: take W580's selected marked-energy family $c$ from `e0CoeffFamily_value_fromTower`, its analytic/bound/support/all-fibre-value clauses and `ExactMarkSites`; apply `isLocExp_of_coeffFamily_renTheta_tower` at source $0$, `renDY_eq_dExt_of_isPolyDom`, `mono_dom`, `mono_rate`. Return marked `IsLocExp` on the fibre with budget $K_0$ and identify its physical value for every $(D,\xi)$. W580 is working on the first packaging/alignment; `ExactMarkSites` remains open.
3. **OPEN (executable now without exact locality; 100–220 lines).** `RenJoinDetValueAllFibre`: align the witness $E$ in `renE0_fibre_det_at` with the determinant coefficient $dz$ in `e0CoeffFamily_value_fromTower`; use `DetExpansionLocC.sum_eq` and `renE0θ_det_eq_sum_collar` to prove $\mathrm{renE0\theta}_{det}(e,E,z,D,\xi)=\sum_C dz(\operatorname{rawOf}(\operatorname{renThetaDatum}(D,\xi)),0;C)$ for **every** fibre $D$ and $\|\xi\|<r_0$. The landed `renE0_fibre_det_at` itself states its displayed energy value only at the step datum and $\xi=0$.
4. **OPEN (executable now under a named exact-locality hypothesis; 130–260 lines).** `RenJoinObservableGivenExact`: select the common `obsFamily_full_fromTower` family before $g,D$, use `obsFamilyRate_eq_tower`, establish the $q=1$ `physVq`/`physV` alignment and the generic package under `ExactObsSites`; obtain `expM0` for every allowed fixed $g$, with its $\beta_U^{-1/2}M_0$ all-fibre value and coefficient prefactor. `ExactObsSites` remains open.
5. **OPEN (executable now conditional on leaves 2–4; 100–200 lines).** `RenJoinPhysicalInputHalf`: reuse $F$ and the three principles from `renormDetOnlyZeroM_onFibre_half` or `renLoc_fields_scale_of_tower_at`; combine determinant `renE0_fibre_det_at` and leaf 2 with `IsLocExp.add_union`, identify the result using leaf 3, then add leaf 4 and leaf 1. Apply `renormExpInputOn_zero_of_fields` to obtain one physical fibre record with $B_{old}=B_{oldM}=0$. This leaf must use the **same** $F$, $Dom,r_0,Y_E,Y_M,d_Y,\kappa_{out}$ throughout.
6. **OPEN (executable now conditional on leaf 5; 60–130 lines).** `RenJoinPhysicalConclusionsHalf`: use `thm31g_C1_on`, `thm31g_C2_on`, `thm31g_Eu_zero_of_fields_on`, `thm31h_zero_of_fields_on` at $0\le\varepsilon_R\le r_0$. The respective bounds are $9(c_Ke)^2W(B_z)\varepsilon_R$, $\frac{17}{32}\,2(3+A)(c_KK_2B)^2W(B_z)\varepsilon_R^2$ with $A=K_1C_1e+c_KK_2Br_0+2$, $B_{E0}$, and $B_{M0}+c_KK_2B\varepsilon_R$.

## T6. Five-line deviation docstring

**OPEN.** The record yields rate $\kappa_{out}=3\kappa_{dec}/2$; equality with the paper's $\kappa_a,\kappa_b$ is not proved.
**OPEN.** The record uses `XiCOneReal` and a fibre predicate; the paper's local chart $\mathfrak B(Y)$ has not been identified with each component domain.
**OPEN.** The record budgets above have not been reduced to the paper's $C'_4\varepsilon_K^2\varepsilon_R$, $C'_4\varepsilon_K^2\varepsilon_R^2$, $(54BL+1)K_0$, or observable prefactor.
**OPEN.** Reality, $O(2)$ symmetry and lattice covariance for the assembled physical families have not been transported to this record.
**PROVED.** The proved fibre theorem runs at class radius $t/2$, chart radius $t$, and perturbation radius $r_0$; the physical join must keep these three radii distinct.

**OPEN (confidence).** High confidence in the record signature, landed suppliers, all-fibre value normalization and zero-class consumer bounds; medium confidence in the estimated leaf sizes and the $q=1$ alignment until elaborated; low confidence in equality with the paper's constants and charts without further estimates.
