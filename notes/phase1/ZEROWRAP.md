# ZEROWRAP — target zero-class Theorem 3.1

**PROVED (snapshot).** Read-only source snapshot `/home/scott/Balaban` at `19250ed8828e2d0f1c25df9a663cc905b083ff78` (13 October 2026). This file specifies a target, not a landed theorem. Here $d=L=3$, $N=2$, $K=k+1$, $\Omega=\Omega''=\mathbb T$, $Z_k=\varnothing$, and `C = zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)`.

## T1. One target statement

**OPEN (target quantifiers).** Fix a tower `T : StepTower κmin` with the required lower bound on `κmin`, and positive fixed $A_1,C_R$, $p\in\mathbb N$, $0<s<1/2$. Choose the class thresholds $\alpha_0,E_0$ and source radius $\rho$ (ultimately $\sqrt2$ for rotation) **before** $\beta_*$. Then there exist one $\beta_*$ and scale-independent positive energy/observable/renormalization constants. For every $k\ge1$, $3\mid N_1$, $N_1>5$, $0<\nu$ with $\nu3^{2K}\le1$, $\beta\ge\beta_*$, and $0<p_1\le pLog(A_1,p,\beta3^k)$, take `Dsc : StepScaleData T k …`, `S=T.step …`. Choose common coefficient/activity/renormalization families for this scale **before** the root $z$ or site $(y,i)$, before any chart datum $D'$ and before any source $g$. Their clauses hold simultaneously for every $D'$ with `XiCData … D'` and $D'.h=h_0$ and every $\sum_{y,i}|g(y,i)|<\rho$. Constants and the family must not be selected anew for each $g$ or $D'$.

**OPEN (common output domain).** The ideal paper form uses the local chart $\Xi^c_K(\mathbb B_K(Y);1,\varepsilon_K)$ for each $Y$, joint analyticity in datum/source on an open neighbourhood, dependence on restrictions to $Y$, reality and $O(2)$/lattice covariance. The immediately achievable Lean form uses `physVq`/`XiCRaw` on the fibre $h=h_0$, an explicit $\ell^1$ source ball, `IsDj 1 K Y`, `sizeJ 1 K Y`, and rate $\kappa_{out}=3\kappa_{dec}/2$. The paper's stronger $\kappa_a=2\kappa-5/2-3\kappa_0-c_1$ for (a),(g), $\kappa_b=\kappa_a-\kappa_0-1$ for (b),(h), exact chart $\mathbb B(Y)$, paper prefactors, reality and symmetries remain deviations to record in the final docstring; no current theorem implies them.

| Clause | Target Lean object, index, value and estimate |
|---|---|
| **OPEN (a)** | One family $e_z(D',Y)$, $Y=\operatorname{sitesOf}T'$ a rooted `IsDj 1 K` site domain, with $\sum_Y e_z=(S.withDatum\ D').E0locC\ C\ z$; `E0locC` includes the local $-\tfrac12\operatorname{tr}\log A_C$ and `E1locC`. Bound $|e_z|\le K_E e^{-\kappa_{out}\operatorname{sizeJ}(Y)}$ on an open fibre neighbourhood; $K_E$ can initially be the landed cube bound $(54B_{\mathbb L}+1)K_0$, $B_{\mathbb L}=\operatorname{covBLogMax}/(1-z_{det})$, after the same-family determinant join. Paper requests this constant with $\kappa_a$ and the local chart. |
| **OPEN (b)** | One $m_{y,i}(D',g,Y)$ with $Y$ rooted at `rootCube (blockIndex y)`, `IsDj`, $\sum_Y m_{y,i}=\beta_U^{-1/2}(S.withDatum\ D').M0C\ C\ g\ y\ i$; bound $K_M\,\mathrm{obsPrefactor}(p,s,\beta3^k)e^{-\kappa_{out}\operatorname{sizeJ}(Y)}$. Landed `obsCoeffFamily_fromTower` has cube coefficient `obsCoeffParam`, rate $\lambda=\min(\min(2\kappa_{dec},\kappa')-\kappa_0-1,\kappa')=\kappa_{out}$ by `StepTower.κ'_eq`, and constant $B_1+B_2$ on `physVq` for $q\le1$; its same-family value, prefactor comparison and extension to $\rho$ are still joins. Paper requests $\tfrac12\beta^{-1/4}(3^{-1}\eta)^{(d-2)/2+\gamma-\alpha_1}$ and $\kappa_b$. |
| **OPEN (g)** | One *physical* renormalization record on the fibre, not the determinant-only record: `renC1On`, `renC2On`, and $E_u$ as `IsLocExp` over a fixed union of `renYs` and the direct marked site domains, all measured by `sizeJ` at $\kappa_{out}$ and radius $0<\epsilon_R\le t/2$ initially. `thm31g_Eu_zero_of_fields` is a consumer of such fields; `renormDetOnlyZeroM_onFibre_half_C12` supplies only the determinant $C_1,C_2$ half-radius part. Paper asks $C'_4\varepsilon_K^2\epsilon$, $C'_4\varepsilon_K^2\epsilon^2$, $(54B_{\mathbb L}+1+C_5E_0\epsilon)K_0$ at $\kappa_a$. |
| **OPEN (h)** | The *same* record with the physical `M0C` family in its observable field yields `thm31h_zero_of_fields_on`/`thm31h_zero_of_fields`, an `IsLocExp` of $M^{(K)}$ over the same site/renormalization union and `sizeJ`, rate $\kappa_{out}$, $0<\epsilon_R\le t/2$ initially. Its abstract bound is $B_{M0}+K_{loc}c_KK_2B\epsilon_R$; comparison with the paper's $c_9\mapsto\tfrac12\beta^{-1/4}+C_6\epsilon3^{K(2\gamma-\alpha_1)}$ remains open. |
| **OPEN (degenerate rendering; algebraic reductions PROVED)** | (a′),(c): crossing-index sets are empty because $\Omega^c=\varnothing$; (d),(e): inherited `zeroTerms.E` and `.M` are zero; (f): old-term index sets in $\Omega^c$ or meeting $Z_K$ are empty. The proposed zero coefficients have any nonnegative bound and decay rate; identification of the paper's named boundary/defect objects with these absent Lean channels remains a wrapper obligation. The *bare source coupling* in `FcompAtC` survives and belongs in the principal source term. |

**PROVED (current scope).** `thm31a_zeroClass_supp_fromTower` gives a canonical fixed-datum cube sum, support and the stated $K_E$ at rate $\kappa'$; `thm31a_zeroClass_sites_fromTower` now gives its site-domain `sizeJ` version. `e1CoeffFamily_fromTower` gives one `E1locC` parameter coefficient family analytic/local on `physV`, but its value on all fibre data is W547. `obsCoeffFamily_fromTower` gives one analytic/bounded/supported cube family and `obsCoeff_fibreValue_fromTower` gives an all-fibre value for a separately quantified family; W556 must identify a single choice. `thm31b_zeroClass_sites_fromTower` gives a separate, source-by-source base-datum site-domain sum at $\kappa_{out}$. `markFibre_sitesOf` proves singleton fibres and $dExt(T')=sizeJ(sitesOf T')$ on polymer supports, with no rate loss. These declarations are in `Balaban/Inhabited/{Thm31aFromTower,Thm31SiteDomains,E1CoeffFamily,ObsCoeffFamily,ObsCoeffFibreValue}.lean` and `Balaban/Fluctuation/MarkFibreSitesOf.lean`.

## T2. Empty-channel statements for a worker

**PROVED (inventory).** `StepClass` has only `m₀,Tm,Ek`; `zeroClass` sets `m₀=0,Tm=zeroTerms,Ek=0`. `StepComplexOut` defines `E0locC,E0C,F0C,M0C`, but no boundary $E'_1$, $\mathcal B''$, $R'_m$ or inherited $R_n$ field. `Thm31cde.thm31c/d/e_of_input` and `StepComplexThm31.thm31cC_of_input` are arbitrary-mark consumers, not physical empty-channel identifications. The following are short wrapper propositions; `boundaryCoeff`, `defectCoeff`, and `oldCoeff` denote zero functions introduced by the worker, not existing Lean identifiers.

**OPEN (a′ wrapper; definitional after choosing the empty family).**
```lean
let cross : Finset Y := ∅
let boundaryCoeff : Y → ℂ := fun _ => 0
show ∑ Y' ∈ cross, boundaryCoeff Y' = 0
```
**PROVED (reason).** $\Omega^c=\varnothing$ makes every crossing support impossible; `Finset.sum_empty` discharges the display.

**OPEN (c wrapper; definitional).**
```lean
let cross : Finset Y := ∅
let boundaryMark : Y → ℂ := fun _ => 0
show (∀ Y', boundaryMark Y' = 0) ∧ ∑ Y' ∈ cross, boundaryMark Y' = 0
```
**PROVED (reason).** There is no `StepClass` boundary-mark field to identify; both claims reduce to `rfl` and `Finset.sum_empty`.

**OPEN (d wrapper; old term zero is already landed).**
```lean
let defectCoeff : Y → ℂ := fun _ => 0
show (∀ Y', defectCoeff Y' = 0) ∧
  EcompAtC 0 (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D = 0
```
**PROVED (reason).** First conjunct is definitional; second is `EcompAtC_zero` in `StepComplexNonvanish.lean`. Identifying the paper's $R'-\delta D$ with this absent old channel is a paper-to-Lean bridge, not definitional.

**OPEN (e wrapper; inherited terms are definitionally zero).**
```lean
let oldCoeff : ℕ → Y → ℂ := fun _ _ => 0
show ∀ n Y', oldCoeff n Y' = 0
```
**PROVED (reason).** This is `rfl`; `zeroTerms` has zero E/M fields, and a nonempty $X\subset\Omega^c$ cannot occur. No separate $R_n$ field exists.

**OPEN (f wrapper; empty old correction, not empty source).**
```lean
let oldBoundaryCoeff : Y → ℂ := fun _ => 0
show (∀ Y', oldBoundaryCoeff Y' = 0) ∧
  EcompAtC 0 (zeroTerms d L N₁ m₁ K N ϱ) a ν hj D = 0
```
**PROVED (reason).** The first part is definitional, the second `EcompAtC_zero`; `FcompAtC_zero_eq` instead identifies a generally nonzero $\sum_{y,i}g(y,i)svec(bgFieldC(D))(y,i)$.

## T3. Identity and its missing uniform form

**PROVED.** `StepComplexSource.prop26C_zeroClass` (or `_of_activity`) states, at each complex block datum and source under `StepNonvanishingC` (or `StepActivityBoundC`),
$$TstepC(g)=\exp[-\beta AnewC+EcompAtC(psiKdC)-Ek\,nU+FcompAtC(psiKdC,g)+E0C+F0C(g)].$$
For `zeroClass`, `EcompAtC=Ek=0`, while `FcompAtC_zero_eq` is the bare source pairing. `StepComplexSource.sum_E0locC_zeroClass` gives $E0C=\sum_z E0locC(z)$; `F0C_eq_pair_zeroClass` gives $F0C(g)=\beta_U^{-1/2}\sum_{y,i}g(y,i)M0C(g,y,i)$. The determinant is already in `E0C`/`E0locC` through `halfLogDetCC`/local $-\frac12\operatorname{tr}\log AC$; it is not an extra summand. `StepPiecesJoint.stepPieces_joint` packages scale pieces and `StepComplexOutWitness.exists_complexStep_cert_of_xiCData` gives a pointwise chart witness at fixed $N_1=6,k=1$, not the uniform tower coefficient theorem.

**OPEN (one useful new identity).** Under a single source activity/nonvanishing witness for every fibre datum, combine those three landed equalities into
$$TstepC_{S[D']}(g)=\exp\{ -\beta AnewC_{S[D']}+FcompAtC_{S[D']}(psiKdC,g)+\sum_z\sum_Y e_z(D',Y)+\beta_U^{-1/2}\sum_{y,i}g(y,i)\,\sqrt{\beta_U}\sum_Y m_{y,i}(D',g,Y)\}.$$
Here $e_z,m_{y,i}$ must be the **same** families as T1, and $D'$ ranges over the whole fibre $h=h_0$ with $\|g\|_1<\rho$. Pointwise algebra is proved conditional on their still-open family value identities and common activity witness. A globally defined analytic logarithm or equality of logarithmic effective actions is not asserted by `prop26C_zeroClass`; the exponential identity is the precise target.

## T4. Ordered bounded joins

| Order | Leaf, input → output; each planned at at most 300 lines | Dependencies and start |
|---|---|---|
| **OPEN 1** | W547 `e1CoeffFamily_fromTower` + physical corrected-mark identity → same-family `E1locC` value at every fibre datum. | Starts on landed energy family; W547 running. No HATY2/generator/radius dependency. |
| **OPEN 2** | W556 `obsCoeffFamily_fromTower` + `obsCoeff_fibreValue_fromTower` → one `Ev`, one tilt activity and one `obsCoeffParam` with value, holomorphy, support, bound. | Start now; W556 running. Current radius $q\le1$. |
| **OPEN 3** | W562 determinant parameter term + leaf 1 → one full `E0locC` family with correct determinant and mark sum at every fibre datum. | Start after W547/W562 land; no generator ruling. |
| **OPEN 4 (base form PROVED)** | `Thm31SiteDomains.sitesOf_regroup_analytic`/`sitesOf_regroup_eq` + leaves 2–3 → site-domain `IsDj`/`sizeJ` **parameter families**, retaining constants and singleton-fibre identity. | Base-datum forms `thm31a_zeroClass_sites_fromTower` and `thm31b_zeroClass_sites_fromTower` landed as W558; family form starts after 2–3. Does not itself fix exact read locality. |
| **OPEN 5** | `PhysicalFootprintRows` + `FootprintMargin` → eligible physical row reads lie in $Y=sitesOf T'$ for energy, determinant and observable inputs. | HATY2 physical locality; start independently of the generator ruling. |
| **OPEN 6** | `PhysicalCoeffYLocal` + leaves 3–5 → `RawAgree Y` and source agreement on $Y$ for every coefficient, on a common open fibre neighbourhood. | HATY2; source radius $\rho$ if used. The landed `thickSet Y` clauses are insufficient. |
| **OPEN 7 (W559 PROVED)** | `ObsUnconditional.obsMarks_zeroClass_family_ksupp_rho`, `SourceWitnessJoint.obsRayActivity_fromTower_of_witness_rho` (W559), W560–W561 radius-$\rho$ source witness/activity, and leaf 2 → one observable family and identity on $\|g\|_1<\rho$, with $\rho$ chosen before $\beta_*$. | Start as W560–W561 land; source-radius dependent, no generator ruling. |
| **OPEN 8** | `PaperGeneratorCoeff` + leaves 5–7 → replacement by coefficient on $\Xi^c_K(\mathbb B_K(Y))$, with local complex analyticity and strict circles. | HATY2 and generator ruling; may be postponed in an honestly labelled fibre theorem. |
| **OPEN 9** | `LocExpUnion` + `Prop33Level` (`renDY=sizeJ`) + `RenormDetFibre*` + leaves 3,6,7 → one fixed site/renormalization cover, zero extensions, common $\kappa_{out}$ and radius. | Start after physical families/locality; no generator ruling for the fibre version. |
| **OPEN 10** | `RenormCommonInput` + leaf 9 + `thm31g_Eu_zero_of_fields_on`, `thm31h_zero_of_fields_on` → physical $C_1,C_2,E_u,M^{(K)}$ on one record, including all-fibre value and constant comparisons. | Start after 9; exact local-chart form also needs 8. |
| **OPEN 11** | Empty-channel wrappers T2 + leaves 3,7,10 + `prop26C_zeroClass`, `sum_E0locC_zeroClass`, `F0C_eq_pair_zeroClass` → one threshold and uniform exponential identity. | Empty wrappers start now; final wrapper after joins. Symmetry/reality and paper prefactors require separate evidence. |

**REFUTED (shortcut).** Replacing $Y$ by a generic collar $Y^+$ does not preserve an additive `sizeJ` bound for zero-surplus observable terms (`HATY2.md`); `thickSet Y\subseteq Y` is false. `PhysicalFootprintRows` must prove the narrower read claim.

## T5. Beyond the zero class

**OPEN 1.** The target fixes $d=L=3,N=2$ and $h=h_0$; Root-F needs general $d,L,N$, chosen $L$, and admissible unit $h$.
**OPEN 2.** `StepTowerG` and its general endpoint field list await this specialization; the present tower cannot be quantified over all dimensions.
**OPEN 3.** A running nonzero class needs physical boundary/defect/inherited-term marks and their modular domains, not the empty T2 wrappers.
**OPEN 4.** The output must satisfy the next class's exact `IsSF.localE/localM` and generator agreement at every scale; fibre `thickSet` locality does not suffice.
**OPEN 5.** Class-to-class rate closure, large-field sectors, stopping/final integral, torus coherence and infinite-volume limits remain outside this statement.

**PROVED (confidence in audit).** High for the named declaration boundaries, empty channels and the pointwise identity; medium for the proposed theorem field list and leaf sizes; low for paper-rate, prefactor, symmetry and local-chart closure until their open physical estimates are proved. No Lean build was run and no file in `/home/scott/Balaban` was edited.
