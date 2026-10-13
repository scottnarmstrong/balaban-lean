# AUDIT-8 — headline statement and definition audit

Snapshot: `/home/scott/Balaban` commit `0372774c67cf745ea3ec36b736ee3008cb22e577` (2026-10-13), compared with `ed348d4`. Read-only inspection of statements, definitions and the cited proof applications; no Lean build. Source comparison is `notes/phase1/FLUCTUATION.md:393–410`. “Faithful” below means faithful to the stated limited target, not closure of all clauses of paper Theorem 3.1.

Frozen file SHA-256 (relative to the snapshot):

| File under `Balaban/` | SHA-256 |
|---|---|
| `Inhabited/Thm31aFromTower.lean` | `f9b1aa5e8c5886abcfb6d4e51b0b47155451323209902a2fe08c23fd6b522a89` |
| `Inhabited/E1CoeffFamily.lean` | `36c12120a696bfbb51ff676d0da3c3b71fc8201225705be819594c86905909a2` |
| `Inhabited/Thm31bKernelSupport.lean` | `b7398ba7ae21dc939f9e4e9824af75e736017e95505131c09108c98e3af42c5e` |
| `Inhabited/ObsCoeffFamily.lean` | `b594e5e6f3474620837f9a11d4d0c145f5507fcdbd2b33f0e3a315fa9e12dc2e` |
| `Inhabited/SourceExponentFamily.lean` | `f8d9cd8714b8553729a501500252c798fb6278e7b44a75b89784a8e1fef4eea2` |
| `Fluctuation/WoneChartIdentity.lean` | `5ba3cfab8a1809be5bf4f06dfb1e1df67dc0fea5379cae49a77070b95fe2e2eb` |
| `Inhabited/SourceActivityFromTower.lean` | `63c6042758f8c00edadcea253f823c7f72e772affd934165b508b560c80bd90c` |
| `Inhabited/TowerCoreRatesVariantsGeneral.lean` | `e0ab7292c5f481d83a42f4a6ba70d2a56c229f3ba90520d4371ec4859187f617` |

## H1. `thm31a_zeroClass_supp_fromTower` — WEAKER THAN CLAIMED as paper 3.1(a)

The witness is one `e`: the value, bound and support clauses share the same existential at `Inhabited/Thm31aFromTower.lean:42–58`; its proof takes all three from `thm31aC_coeff_supp` at lines 95–99. `S.E0locC zeroClass z` is the **zero-class, whole-lattice, complex base-datum** version of $\mathscr E''_0(z)=-D^{(k)}(z)/2+\mathscr E'_1(z)$: by `Fluctuation/StepComplexOut.lean:178–185`, it is $-\frac12\sum_{y\in B(z),i}\mathbb L(y,i;y,i)+E'_{1}(z)$, with $E'_1$ the $s$-integral of the masked derivative of $\Phi_1$. Here $\mathbb L=\log\mathcal A$ at `S.D'`, where `covAC` uses the complex background and `logAC` uses `decLog` at coupling one (`StepComplexOut.lean:52–70`). Its full block sum is the actual holomorphic $\frac12\log\det C^{(k)}$, by `halfLogDetCC` and `sum_trace_E0locC` (`StepComplexOut.lean:72–82,187–205`); the trace is no stand-in for the determinant.

The constant has the paper's $(2L^d B_{\mathbb L}+1)K_0$ shape at $N=2,L=3$: choose $B_{\mathbb L}=BL=\operatorname{covBLogMax}(3,3,\kappa)/(1-z_{\rm det})$, $z_{\rm det}=(\operatorname{detDeg}(3,3)+1)^2 2e^{-\kappa}<1$. `covBLogMax` is a valid uniform weight bound (`Fluctuation/DetPrefactor.lean:84–102`); lines 74–95 of `Thm31aFromTower.lean` use $K_0\ge1$ to absorb the determinant constant $27BL$ into $2\cdot27BL K_0$. This identifies an admissible $B_{\mathbb L}$, not an equality with a separately fixed paper constant.

The claimed decay is $\kappa'=\frac32\kappa_{\rm dec}+\kappa_0+1$ (`Inhabited/StepTower.lean:35–38`), whereas source 3.1(a) has $\kappa_a=2\kappa_{\rm dec}-\frac52-3\kappa_0-c_1$ (`FLUCTUATION.md:399,406–407`). The tower gives $\kappa'\le\kappa_a$ (`Inhabited/SourceActivityFromTower.lean:346–347`), with strict gap for its specified $\kappa_{\rm dec}=100(\kappa_0+c_1+10)$; hence the landed bound is weaker. It uses `dExt` on all level-one blocks, not the general $d^{\rm cov}(\bmod\Omega^c)$ and $Y\subset\Omega''$ clause. It states no parameter-family analyticity, locality or real/symmetry properties.

The hypotheses are nonvacuous: `exists_stepTower κmin` holds for every $\kappa_{\min}$ (`Inhabited/StepTower.lean:81–82`), so take $\kappa_{\min}=\operatorname{stepHullMin}$; `StepTower.scale` supplies `StepScaleData` at every admissible scale after one threshold (`Inhabited/StepTowerScale.lean:112–118`). The theorem itself is conditional on an individual `StepScaleData` and evaluates only its `S.D'` (`Thm31aFromTower.lean:47–52`).

## H2. `e1CoeffFamily_fromTower` — WEAKER THAN CLAIMED as a full energy expansion

The quantifier order is correct **after fixing base scale datum `D`**: `F₁`, `Sol`, label type and labels, $\varepsilon_H$, and `A₀` are chosen before the root `z` and all varying `D'` (`Inhabited/E1CoeffFamily.lean:229–260`). Clause (α) says `withDatum D'` has the physical `WoneC zeroClass` exponent almost everywhere (`E1CoeffFamily.lean:250–259`). `withDatum` changes `D'` and its complex covariance square root while retaining the fixed product measure $\nu_{p_1}$ (`Fluctuation/ParamDatumFamily.lean:78–108,124–139`; `Fluctuation/StepObjects.lean:403–404`). Background dependence of the Gaussian substitution enters `WoneC` through `covSqrtC`, `shiftUC`, `psiAtC` (`Fluctuation/StepComplex.lean:273–295,331–356`). Thus the measure is correctly datum-independent after the paper's change of variables.

The analytic and bound clauses hold on `physV`; locality requires equality of `physRestrict` on `thickSet (Yhat univ (sitesOf C))` (`E1CoeffFamily.lean:289–305`). `physRestrict (physIncl θ)` contains both components of the raw datum **and the source $g$** (`Fluctuation/ParamActivityPhysical.lean:356–361`; `Fluctuation/ParamActivitySubspace.lean:240–248`); the theorem alone does not state source-free locality. The support implication is indeed quantified for every $\theta$ (`E1CoeffFamily.lean:305–306`), obtained from the root and active-set combinatorics at lines 430–438. `e1MarkGParam` is set to zero outside its chart (`Inhabited/E1MarkParamCommon.lean:48–68`), so the universal support is harmless there. The `c` definition is `gsumCoeff` (`E1CoeffFamily.lean:278–288`), but **this file has no identity $E'_{1}(z)=\sum_C c(z,\theta,C)$**; the base-datum value is a separate record target (`Inhabited/E1RecordFromTower.lean:160`, `Inhabited/E1RecordOfSum.lean:249`). Neither that separate identity nor source independence follows merely from this family statement.

## H3. Observable — WEAKER THAN CLAIMED as paper 3.1(b); new family FAITHFUL to its stated bound

The `_ksupp` route begins at `Fluctuation/ObsMarksAssembly.lean:364` and `Inhabited/ObsMarksFromTower.lean:613`, then branches to `Inhabited/ObsUnconditional.lean:268` and `Inhabited/ObsOnCommonWitness.lean:42`; the latter feeds `Inhabited/Thm31bKernelSupport.lean:40,141`. In the one-scale proof, `E := obsCoeff I` at `Thm31bKernelSupport.lean:107–110` is exactly the coefficient in the sum, root clause and bound (`:92–98`); the polymer implication uses `I.obsCoeff_eq_zero_of_not_isPolyDom_of_kernel_supp` (`:129–130`). The common-witness theorem invokes this same one-scale statement (`:421–443`). No detached support witness was substituted.

The observable coefficient bound still uses `obsPrefactor p s (β 3^k)` (`Thm31bKernelSupport.lean:97,429`), defined as $(\log b)^{4p}b^{-1/2-s}+(\log b)^{2p}/b$ (`Inhabited/Thm31bFromTower.lean:37–39`); the paper asks $\frac12\beta^{-1/4}(3^{-1}\eta)^{(d-2)/2+\gamma-\alpha_1}$ and rate $\kappa_b$ (`FLUCTUATION.md:399,409`). The new support clause changes neither the prefactor nor the $\frac32\kappa_{\rm dec}$ rate. This is the earlier AUDIT-OBS limitation, not a new match to the paper.

`obsCoeffFamily_fromTower` discharges its displayed $\Theta$ budget: $K_{\rm obs}=2(K_0+1)+2K_0$ occurs in `stepTheta`, all `tiltActObs` terms and `CPE` (`Inhabited/ObsCoeffFamily.lean:399–403,428–505`); the proof obtains `hεΘ` for that same choice, and uses the same `obsRg CR s p (β3^k)` throughout (`:525–547`). Its $\lambda=\min(\min(2\kappa_{\rm dec},\kappa')-\kappa_0-1,\kappa')$ (`:505`) equals $\frac32\kappa_{\rm dec}$ by `StepTower.lean:37–38` and `stepTower_outRate_eq` (`Inhabited/Thm31bFromTower.lean:41–49`). The theorem supplies parameterized analyticity, bound and support; the physical fibre identification is separate (`Inhabited/ObsCoeffFibreValue.lean:15–27`).

## H4. Radius $\rho$ — FAITHFUL radius carriers; “only new constraint” is false for the scale wrapper

`sourceExponentFamily_fromTower_rho` assumes $\rho>0$, $\beta\ge\max(1,\rho)$ and quantifies the source over `l1BallRho ρ` with `physFibreRho ρ`; its activity amplitude uses $\rho/\beta$ (`Inhabited/SourceExponentFamily.lean:109–141`). `wone_chartIdentity_fromTower_rho` has a source-free first clause and a second clause quantified over **each** $\rho$ with `physVRho ρ` (`Fluctuation/WoneChartIdentity.lean:401–452`). Neither leaves a hidden unit-ball carrier; `l1BallRho` and `physVRho` are defined in `Fluctuation/SourceRadiusCarriers.lean:41–44,89–105`.

For `sourceActivityC_scale_fromTower_rho`, $C_E,C_F$ precede $\rho$, but $\beta_0$ is chosen **after** $\rho$, at least $\max(2,\rho)$ (`Inhabited/SourceActivityFromTower.lean:303–310`). It also must exceed the $\rho$-dependent `daThreshold((C_E+ρ C_F)/4)` (`:350–361`). Thus $\beta\ge\max(1,\rho)$ is the only *new displayed premise of the direct exponent theorem*, not the only restriction for the large-$\beta$ activity theorem. Its source-bearing conclusion uses `l1BallRho ρ` and explicitly bounds $\varepsilon_H$ by $C_E(\log b)^{3p}/\sqrt b+\rho C_F(\log b)^p/\sqrt b$ (`:313–325`, $b=\beta3^k$).

## H5. General core variants — FAITHFUL as conditional statement, with concrete inhabitation

`tower_core_rates_two_general_of_pair` requires `hpair` for the chosen `Gp,Hm`; it does not assert the result for every pair (`Inhabited/TowerCoreRatesVariantsGeneral.lean:35–46`). This condition is satisfiable for each $d\ge3,L\ge3$: `hpair_lvG` supplies the pair at $N_1=9,K=2,a_1=1$, $0\le\nu L^4\le1$ (`Inhabited/LevelPairGeneral.lean:138–149`), and `tower_core_rates_two_general` applies it for arbitrary fixed $N$ (`TowerCoreRatesVariantsGeneral.lean:272–304`). Choose $\kappa_0,\kappa_{\rm dec}$ above the displayed lower bounds. Both `FlCore` assertions use the **same** `Gp m₁,Hm m₁,c,BG,κ,c₂,BG₂`; only $t$ becomes $2t$ (`:47–50,65–71`).

## H6. Docstring corrections and statement drift

1. `Inhabited/Thm31aFromTower.lean:16–27,39–41`: append: “This is the whole-lattice zero-class value at one base datum, with decay $\kappa'$; it does not supply paper rate $\kappa_a$, boundary-cover clauses or a varying-datum coefficient family.”
2. `Inhabited/E1CoeffFamily.lean:18–33`: replace “locality in the raw datum” with: “Locality is under agreement of the raw datum **and source** on the thickened $\widehat Y$; the identity of the coefficient sum with $E'_1(z)$ is a separate theorem.”

Against `git show ed348d4`, the complete theorem header through `:=` is textually unchanged for `obsMarks_zeroClass_at_of_ray` (`Inhabited/ObsMarksFromTower.lean:694`) and for `obsMarks_onCommonWitness_fromTower` and `thm31b_onCommonWitness_fromTower` (`Inhabited/ObsOnCommonWitness.lean:364,675`). A header comparison of common named `theorem`/`lemma`/`def`/`structure`/`class`/`abbrev` declarations across changed Lean files found no changed existing statement; newly added declarations and removed files were excluded. This is a textual check, not elaboration or proof audit.

## Refutation ledger

| Candidate counterexample | Check and disposition |
|---|---|
| H1 determinant is a surrogate, or its hypotheses are empty | Refuted by `StepComplexOut.lean:52–82,182–205` and `StepTower.lean:81–82` plus `StepTowerScale.lean:112–118`. |
| H1 paper rate and domain already proved | Sustained: $\kappa'<\kappa_a$ at this tower, and `dExt` with `Set.univ` is narrower (`Thm31aFromTower.lean:50–58`; `FLUCTUATION.md:399,405–407`). |
| H2 frozen Gaussian measure loses background dependence | Refuted: `withDatum` changes covariance inside the exponent (`ParamDatumFamily.lean:106–139`; `StepComplex.lean:273–295,352–356`). |
| H2 raw-only locality and full physical $E'_1$ identity follow from the family theorem | Sustained as overreadings: `physRestrict` includes $g$ and no such sum identity occurs in `E1CoeffFamily.lean:229–306`. |
| H3 polymer support uses a different coefficient; `_ksupp` changed old statement | Refuted by `Thm31bKernelSupport.lean:107–130` and the three header spot checks above. Prefactor and paper-rate objections remain. |
| H3 new family carries an unmet $h\varepsilon$ or mismatched $K_{\rm obs},R_g$ | Refuted by `ObsCoeffFamily.lean:399–403,525–547`; $\lambda=\frac32\kappa_{\rm dec}$. |
| H4 hidden unit ball; $\beta\ge\rho$ alone suffices for final activity theorem | First refuted by radius carriers; second sustained by the $\rho$-dependent threshold (`SourceActivityFromTower.lean:350–361`). |
| H5 pair premise makes theorem vacuous, or doubled radius changes pair | Refuted by `LevelPairGeneral.lean:138–149` and `TowerCoreRatesVariantsGeneral.lean:47–71,272–304`. |
