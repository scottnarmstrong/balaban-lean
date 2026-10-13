# EXACTJOIN — exact-site zero-class fibre join

**PROVED (snapshot).** Read-only main `/home/scott/Balaban` at `74cea1e805af188cd508c54c936428fa469a787a` (13 October 2026); inspected finished branches `w585-obs-ev-raw-y` at `df5799a9fd98cd761224647ae86103175206c756`, `w586-obs-family-prefactor` at `9a961a2ad5afcc863ff1cf90f0975b474b14876d`, `w587-pair-spec-export` at `87003dbd08ea52b35c428c77fa7255ca20b9e660`, and `w591-eterm-expansion-raw-y` at `1442181f8db5b20d38b9fe75ba54e64ecc0d93ab`. No build was run; no Balaban source was edited.

**OPEN (dependency).** `w592-phys-ag-exact` was still in progress at inspection: its `physAgΘ` still used `thickSet` and `labelActFamilyOn_local_scaled_rawY` was absent. Every proposed exact coefficient theorem below depends on that direct-terms result and must be checked after the branch lands.

## T1. Energy coefficient

**OPEN (precise added conjunct).** In the existing `∀ z, … ∃ c, … ∀ C, …` of `e1CoeffFamily_value_fromTower`, with `S := T.step k hk N₁ ν β p₁`, insert alongside the analytic, bound, support, and value clauses:
```lean
∀ θ ∈ physV S S.a₁ S.ν T.t, ∀ θ' ∈ physV S S.a₁ S.ν T.t,
  physRestrict (sitesOf C) (physIncl 2 S θ) =
    physRestrict (sitesOf C) (physIncl 2 S θ') → c θ C = c θ' C
```
**PROVED (proof interface).** `paramMarked_analytic_local_bound` in `ParamCarrierLocal.lean:138` takes the projection `π` as a parameter and consumes the corresponding activity hypothesis `hA` and mark hypothesis `hG`; its conclusion is equality on equal `π`. Take `π θ := physRestrict (sitesOf C) (physIncl 2 S θ)`. A relation-generic variant of that theorem is unnecessary.

**PROVED (mark supplier); OPEN (activity supplier).** W587's `e1Mark_hG_rawY_fromTower` supplies `hG` from equality of raw data on the mark's own sites. W592's planned `labelActFamilyOn_local_scaled_rawY`, passed through `commonAct_zeroSourceAct_hA` with this `π`, must supply `hA` for labels supported in `Yhat Set.univ (sitesOf C)`. Reuse the same `c`, `F₁`, `Sol`, labels, and activity witnesses; change the existing `hmain` invocation and retain its thick locality by restricting exact agreement from the thick region to `sitesOf C`.

**REFUTED (full-energy shortcut).** The same exact-site clause does not hold for the determinant coefficient `dz`, hence cannot be asserted for `e0 = dz + c` on each cube. In `e0CoeffFamily_value_fromTower` add the exact clause only inside its nested mark-family `c` block; preserve the thick clauses for `dz` and `e0`. Determinant locality is exact only at its collar-grouped `renYs` level. Its physical `E0locC` value remains the determinant plus the same marked sum.

**OPEN (W571 threading).** `stepIdentity_zeroClass_fibre_fromTower` in W571's `StepIdentityFibreFamilies.lean` quotes the energy family block verbatim. Add precisely the new conjunct inside its `∀ C` mark-family block and pass the extra projection from `e1CoeffFamily_value_fromTower`/`e0CoeffFamily_value_fromTower`; leave the `e0`/`dz` thick statements and the identity value untouched. `stepIdentity_zeroClass_fibre_of_values_fromTower` in `StepIdentityFibre.lean` consumes the value identities and needs no strengthened locality premise.

## T2. Observable coefficient

**OPEN (precise added conjunct).** For each `T'` in the `∀ T'` block of `obsFamily_full_fromTower`, with its *chosen* `Ev`, `A`, and `obsCoeffParam` expression (call that expression `cObs θ T'`), insert:
```lean
∀ θ ∈ physVq S S.a₁ S.ν T.t q, ∀ θ' ∈ physVq S S.a₁ S.ν T.t q,
  physRestrict (sitesOf T') (physIncl 2 S θ) =
    physRestrict (sitesOf T') (physIncl 2 S θ') →
      cObs θ T' = cObs θ' T'
```
**PROVED (generic route).** `obsCoeffParam_congr_of_local` in W585's `ObsCoeffLocal.lean` asks for exactly three coefficient-level premises: kernel `hk` on each subcluster, label activity `hA` along the interpolation, and remainder mark `hG` along the interpolation. W585's `obsHker_hatCoeff_local_rawY` supplies `hk`, and `obsGrFam_local_rawY` supplies `hG`, from raw agreement on `sitesOf T'` through its chosen sharp `Ev`. W592's activity lemma, through `tiltActObs_H_local_of_labels`, must supply `hA`. Add a sharp wrapper `obsCoeffParam_local_of_Ev_rawY` using these three premises; call it on the same `Ev` chosen by `obsFamily_full_fromTower`.

**PROVED (remaining thick use).** W585's `obsRemainder_of_sharpHat` call still takes thick `hd`. That premise certifies the remainder's mark assembly, analyticity, and value; it is not a locality premise that survives as a thick restriction in the final coefficient. The coefficient's remainder term is `obsGrFam`, for which W585 supplies sharp raw-site congruence. Retain `hd` for assembly and use the sharp `Ev` property separately for congruence.

**OPEN (exports).** `obsFamily_pair_fibre_fromTower` (W571) and `obsFamily_prefactor_fromTower` (W586) quote the full family locality clause and must copy the new conjunct, projecting it from the *same* full-family witness. `obsFamily_joint_fromTower` currently drops locality altogether: its conclusion has analytic, bound, support, and value clauses, so it needs no edit unless it is deliberately promoted to an exact-locality API. W585 and W586 live on distinct finished branches; their estimates alone do not establish a shared existential witness until integrated.

## T3. Physical record and four consumers

**PROVED (carrier alignment).** `physVq_one` in `SourceFamilyRelative.lean:86` states `physVq … 1 = physV`; set `q = 1` for the observable record. The observable family chooses its label/activity/`Ev` before `(y,i)`, datum `D'`, and source `g`. Its per-`(y,i)` coefficient is then chosen before `D'` and `g`. The required `hdj : ∀ Y ∈ obsDomains …, IsDj 1 (k+1) Y` follows from `Dsc.covers.2 (y,i)` and `obsDomains_isDj`, as used in `StepIdentityFibreObs.lean:165–169` on W585.

**OPEN (energy instantiation).** For `renE0_siteRecord_of_family` (`RenormE1SiteRecord.lean:124`), take the *same* tower mark `c` from T1, `κ := R.κ' = 3 R.κdec/2`, `B := K0 3 3 R.κ0`. Its `han` is T1 analyticity; `hloc` is the new exact-site conjunct; `hbd` follows from T1's bound for **all** cube sets by restricting to `IsPolyDom`; `hsupp` is T1 support; `hval` is T1's all-fibre `E1locC` sum at `(rawOf D',0)`. The record itself joins a separate determinant witness by `renE0θ_det_eq_logAC`; identifying an arbitrary `dz` with that witness is unnecessary and unsupported.

**PROVED (energy record conclusion, conditional on inputs).** With `Dom(D) := XiCOneReal G a ν (R.t/2) D ∧ D.h=h₀`, radius `R.r₀`, `Ssite := Finset.univ.image (fun T => Finset.univ.filter (· ∈ sitesOf T))`, the record expands the physical `E0locC` at the renormalized datum on `renYs_E(z) ∪ Ssite`, rate `κout := 3 R.κdec/2`, budget
`BE0 := hullConst 3 3 (towerDetRate R.κ) (towerDetConst R.κ) * exp (c1 3 3 * log 2) * exp (hullRate 3 3 (towerDetRate R.κ)) + K0 3 3 R.κ0`.

**OPEN (observable instantiation).** For W585's `renM0_siteRecord_union_of_family`, use the **same** T2 coefficient for each `(y,i)`, `q=1`, `κ=κout`, `B=BM0 := C * obsPrefactor p s (β*3^k)` from W586; obtain its nonnegativity from the prefactor hypotheses. `han`, `hloc`, `hsupp`, and `hval` come from the full/fibre observable clauses, with `M0C = √βU ∑ cObs`; `hbd` is the prefactor bound restricted to polymer sets. For each fixed `g` with `‖g‖₁<1`, this returns an expansion of `βU⁻¹/² M0C` on `renYs_M(y) ∪ Ssite` with radius `R.r₀`, rate `κout`, budget `BM0`. The coefficient family itself must already be fixed before `g`.

**PROVED (union type).** W588's `renLoc_fields_union_scale_of_tower_at` accepts `S : Finset (Finset (Torus 3 (N₁*3^R.m₁*3^(k+1))))`. `CTorus 3 3 N₁ R.m₁ (k+1)` abbreviates precisely that torus, so `S := Ssite` is type-compatible. Set `e:=R.t/2`, `B:=8e`, `cK:=renCK 3 3 2 R.BG R.κ`, `κa=κb=κout≤2R.κdec`, and `Kloc=1`; W588 supplies `F` and the three localization principles on the same unions over `XiCOneReal`. The `sub` argument of `renormExpInputOn_zero_of_fields` restricts their consumer to `Dom`.

**OPEN (proposed exact `renormPhysicalZero_onFibre_half` statement).** Assume the tower/scale hypotheses of the two family theorems, `R : StepTowerTheta κmin`, `renDetFibreMin≤κmin`, `0<β`, and `g` in the unit source ball. With `e, Dom, Ssite, κout, BE0, BM0, F` as above, conclude one
`I : RenormExpInputOn G a ν e R.r₀ cK (8e) F blk YsE YsM renDY κout κout 1 BE0 0 BM0 0 E0θ 0 M0θ 0 Dom`, where `E0θ` and `M0θ` are exactly the physical `E0locC` and `βU⁻¹/² M0C` functions returned by the records (including their constant-`h₀` guards), and `YsE/YsM := renYs_E/renYs_M ∪ Ssite`. Quantify the common families before `g`; the record `I` may be constructed for each `g`. Require `0≤εR≤R.r₀` to project all four estimates.

**PROVED (four consumer formulas, conditional on `I`).** `thm31g_C1_on` gives rate `κout`, radius `εR`, bound `9(cK e)^2 blockWeight(blk z) εR`. `thm31g_C2_on` gives `(17/32)*2*(3+bgK1 3 3 2*xiC1 3*e+cK*cK2 3 3 2*(8e)*R.r₀+2)*(cK*cK2 3 3 2*(8e))²*blockWeight(blk z)*εR²`. `thm31g_Eu_zero_of_fields_on` gives `BE0`; `thm31h_zero_of_fields_on` gives `BM0+cK*cK2 3 3 2*(8e)*εR`. The first two need their stated smallness/size hypotheses from `RenormExpInputOn.lean:166,187`; they do not follow from `I` alone.

## T4. Final wrapper

**OPEN (exact target shape).** Propose `zeroClassSiteStep_fromTower`: fix `R,hR,A₁,p,CR,s` with `A₁,CR>0` and `0<s<1/2`; choose one threshold and scale-independent positive constants before `k,N₁,ν,β,p₁,Dsc`; assume the existing tower admissibility and consumer smallness conditions. At each scale choose the common energy mark family, determinant family, observable label/activity/`Ev` and coefficient families before any `D'` or `g`, and choose the union-principle solution `F` once. Its conjunction asserts (a) the physical `E0locC` site expansion from its determinant collar record plus the exact-site mark `c`, (b) the physical `βU⁻¹/² M0C` site expansion from exact-site `cObs` at `q=1`, (g),(h) the four bounds of T3 on `Dom` and common site unions for every `g` with `‖g‖₁<1`, and the W571 all-fibre step identity using precisely these coefficients. For every admissible `D'` with `h=h₀` the identity is an equality of complex exponentials: the exponent contains `-β AnewC`, the surviving bare source pairing `FcompAtC`, `∑z E0locC(z)`, and `βU⁻¹/² ∑y,i g(y,i) M0C(g,y,i)`; the last two are replaced by sums of the *chosen* coefficient families through `stepIdentity_zeroClass_fibre_of_values_fromTower`.

**REFUTED (stronger readings).** This target does not give source radius `√2` or rotation (`q≤1`), a full chart, the paper's `B(Y)` domain, paper rates `κa,κb`, paper exact prefactors, reality, `O(2)`/lattice covariance, or a logarithmic effective-action identity. The determinant is grouped on `renYs`, while each marked coefficient is exact on its own `sitesOf`; the record cover is the union with the full `Ssite`. Paper clauses (a′),(c),(d),(e),(f) need their separate empty-channel identifications. State these deviations in the theorem docstring.

**OPEN (declaration design).** Use a small number of genuine theorems with a shared existential witness prefix: first an exact-site family/identity theorem, then a conditional physical-record theorem taking those chosen witnesses, then a final theorem that chooses once and projects the four estimates and identity. Do not replace the first theorem with `def MarkFamilyBlock : Prop`: the project architecture rule permits literal source predicates but bars theorem-shaped result bundles/assumption packages even when they abbreviate landed clauses. A private local `let` for repeated expressions inside a theorem statement is acceptable if it introduces no new theorem-shaped public interface.

## T5. Ordered leaves and ownership

**OPEN 1 (W592 owner; ≤300 lines).** Finish `physAgΘ` exact agreement and `labelActFamilyOn_local_scaled_rawY` in W592's direct-term/activity files. No other worker edits those files until landing.

**OPEN 2 (energy owner; ≤300 lines).** After W587 and W592 land, edit `E1CoeffFamily.lean` to instantiate `paramMarked_analytic_local_bound` with exact `π` and expose the added `c` clause; edit `E0CoeffFamily.lean` only to pass that nested clause. An independent conditional helper using W587's `hG` can be drafted before W592 in a new `E1CoeffExactSites.lean` file, without changing those owned files.

**OPEN 3 (observable owner; ≤300 lines).** After W585 lands, add `ObsCoeffExactSites.lean` with the three-premise sharp wrapper; it can be proved conditionally on exact activity before W592. After W592, one owner edits `ObsFamilyJoint.lean` to add the exact full-family clause and preserve `Ev`. A separate owner, after that export stabilizes, edits `ObsFamilyPrefactor.lean` and `StepIdentityFibreObs.lean` to project the same clause; do not edit W586's branch file concurrently.

**OPEN 4 (record owner; ≤300 lines).** In a new `RenJoinPhysicalInputHalf.lean`, first prove the conditional `renormPhysicalZero_onFibre_half` from supplied exact family clauses using the two site-record theorems and W588 union principles. This can start after W585 lands and before W592, since exact `hloc` is an explicit premise. Include the `physVq_one`, `hdj`, budget, and common-cover conversions.

**OPEN 5 (identity owner; ≤300 lines).** After leaves 2–3, edit `StepIdentityFibreFamilies.lean` to thread exact `c`/`cObs` conjuncts, preserving its witness order. Keep ownership separate from the observable corollary file.

**OPEN 6 (wrapper owner; ≤300 lines).** After 2–5 and the W586 prefactor integration, add `PhysicalZeroJoin.lean` with the one-threshold shared-witness theorem, four consumer projections, and docstring deviations. Verify with narrow Lean builds then project build before claiming closure; none was run for this report.

**PROVED (confidence).** High for the exact clause shapes, locality interfaces, record types, carrier equality, and consumer formulas; medium for the proposed cross-branch witness assembly and leaf lengths; low for a final executable theorem until W592 lands and the combined sources elaborate.
