# LOCREN-2: the three renormalization localization principles

**Scope.** This is a paper proof of the localization and aggregation steps under exact named inputs, and an audit of the physical inputs still absent. `PROVED` denotes a landed theorem or a deduction from its stated hypotheses;
`PROVED CONDITIONAL ON` names an additional premise; `OPEN` denotes a missing theorem. All Lean paths below are relative to the read-only `Balaban/` tree. The target is the zero class of `Fluctuation/RenormInputZero.lean`; its five-field
constructor does not produce any of the three principles.

## 1. A common output cover and size

Fix `K=k+1`, `N₀=N₁ L^m₁`, the whole-level generating set `G`, and `m₀≥1` with `L^m₀∣N₁`. Let `T=CTorus d L N₁ m₁ K`. For a block root `z`, set `x_z=blockSite k z`, `X_z=LocalCover.cube m₀ k x_z`, `X₁,z=LocalCover.nbhd m₀ x_z`. For a source root
`p`, use `x_p=p.1` in the same formulas. **PROVED:** `Fluctuation/LevelLocalCover.lean:levelLocalCover` gives `CovSetup` and an attaining tree for both roots, `treeLenCovOne m₀ k X=0`, and the block read-site and margin assertions; its
hypotheses include `DGSetting`, `IsLevel`, and the stated divisibility. It does not give an analytic physical field family.

Take the parameter labels to be the **finite type** `ι_z={q : ℕ×T // q∈cubeIdx G ∧ Disjoint (Pset m₁ q) X₁,z}` (similarly `ι_p`), and let `c:ι→ℕ×T` be the inclusion. Then `c` is injective, every label is a legal cube, and its patch misses `X₁`.
This is the exact index type required by `Localization/I5Expansion.lean:localization_expansion`; a chosen `DecCover` must identify its free parameters with these labels and set all other coordinates to one. **OPEN-COVER-PARAM** is that
identification for the physical step, together with its `CoverBase`/`CoverLocal`, `HatConn`, `DecSpecs`, `FamSpec`, and `AnSpec` hypotheses.

For `C:Finset ι`, write `Y(C)=Ysites G m₀ c X₁ C=X₁∪⋃_{i∈C}Dsites G m₀(c i)` (`Localization/PolymerGeometry.lean:Ysites`). Its component region for `LocalityAEOn` is `compY c X₁ C`, not `Y(C)`. Define `Ys z` and `YsM p` by taking
`polymerDomains c G m₀ X₁` (`I5Expansion.lean`), then converting each set of the finite type `T` to `Finset T` by `Finset.univ.filter (·∈Y)`. Conversion back to `Set T` is equality by finiteness. This is one finite family of finite site sets per
root. **OPEN-TRANSPORT** is the elementary but unlanded Lean conversion of `polymerDomains`, `evTerm`, and agreement across these two types.

Use the single total function `dY(Y:Finset T)=treeLenCov G m₀ (↑Y)` for both covers; `TreeLengthCov.lean:treeLenCov_nonneg` gives nonnegativity for every `Y`, including empty or disconnected sets. It is the size in
`I5Expansion.localization_expansion`, so no comparison with `dExt` is needed. `CubeB` and `sitesOf` belong to the *other*, cube-indexed output formalism (`Polymer/MarkedCubes.lean`); `levelLocalCover` produces `X`, `X₁`, and a singleton chosen
cube family, while I-5 already produces site domains. Using `sitesOf` here would insert an unproved cube-paving conversion. If downstream output requires `CubeB`, that conversion is a separate **OPEN-PAVING** leaf.

`NC` means the interior Neumann-cut Green bound of `notes/phase1/LOCALIZATION.md` §3.1: coercivity and Agmon decay for the cut-bond operator, plus interior sup, gradient, Laplacian and Hölder bounds on the core of each cut cube, uniformly in the
cut and scale. It is the analytic input behind the decoupled Green family and the common cover. The abstract `localization_expansion` and the `levelLocalCover` theorem do **not** assert NC. **OPEN-NC-PHYSICAL** is its verification for this
auxiliary cover and generating set; avoid treating `NC` as a counting estimate.

## 2. Leaf 10a: exact fibre inequality

**PROVED (`Localization/I5Param.lean:abstract_expansion_on`).** For finite `ι`, data set `S`, patches `P_i`, component `Yc(C)`, relation `Ag C`, and `F(u,s)`, assume `κ₁≥1`, analyticity and bound `|F(u,s)|≤M` on the open polydisc `|s_i|<e^{κ₁}`,
`LocalityAEOn (e^{κ₁}) S P Yc Ag F`, and reflexivity of `Ag`. Here `LocalityAEOn` compares `u,u'∈S` and `s,s'∈supN C e^{κ₁}` whenever `s_i=s'_i` for every `i∈C` whose patch lies in `Yc(C)`, and `Ag C u u'`. It concludes
`F(u,1)=Σ_{C connected} coef(Fu,C)`, zero coefficients off connected families, equality of coefficients under `Ag C`, and `|coef(Fu,C)|≤M e^{-(κ₁-1)|C|}`. The data set may include `(D,ξ)`; for a fixed-ξ universal transfer, keep ξ fixed in the
bound while Cauchy is taken only in `s`.

Put `A=(2L+1)^d (L^m₀)^d`, choose `κ₀≥0`, `κ≥3κ₀+3`, `κ₁≥4d(2L+1)^d κ`, `1≤(κ₁/2-1)/2`, and `log A≤(κ₁/2-1)/2`, as in `I5Expansion.localization_expansion`. For the root cubes above `Δ=treeLenCovOne m₀ k X=0`. **PROVED CONDITIONAL ON** the I-5
`CovSetup`, legal/injective labels, disjoint patches, and attained-tree premises: `PolymerCount.lean:gm4` gives, for every connected `C`,
\[
(κ₁-1)|C|\ge(κ₁/2-1)|C|+2κ\,dY(Y(C)).\tag{2.1}
\]
`I5Expansion.lean:gm3_fam` gives `Σ_{C connected:Y(C)=Y}e^{-(κ₁/2-1)|C|}≤1` under the last two rate inequalities. Its G2-type entropy is the `A` above: `PolymerGeometry.lean:gm1` bounds layer cubes, and `Peierls.lean:peierls_count_layers` sums the choices. Multiplying (2.1) by the exponential and summing the fibre proves, **with no unspecified factor**,
\[
\sup_{Y\in Ys}e^{2κdY(Y)}\sum_{C\,connected:Y(C)=Y}e^{-(κ₁-1)|C|}\le1.\tag{2.2}
\]
Thus any requested output rate `κa,κb≤2κ` has `Kloc=1` because `dY≥0`; the bound is uniform in `k,N₁` once the displayed hypotheses hold uniformly. The stronger `I5Expansion.localization_expansion` states directly
`|evTerm(Y,u)|≤M e^{-κ₀Δ-2κdY(Y)}` and joint analyticity. Its proof is exactly `abstract_expansion_on` + `gm4` + `gm3_fam`. `Polymer/Animals.lean:card_animals_le` is a general rooted connected-set count but is not needed for this specific fibre;
`MarkedRootGeometry.lean:bridge_isDj_and_le` and `fibre_weighted_le` concern an **additional root bridge**, not `C↦Y(C)`. If that bridge is inserted, the latter gives the separate factor `nFibre d L · exp(a cBr d L)` at rate `a`, under its
`IsDj` and divisibility hypotheses; do not multiply it into (2.2) for the present cover.

**PROVED CONDITIONAL ON OPEN-AGREE-BRIDGE.** Define `Ag C (D,ξ) (D',ξ')` to require `ξ=ξ'` and equality of raw data on all `resDep` read sites of the component `compY C` (plus the chosen cut/parameter agreement). If `RawAgree (fin(Y(C)))`
implies this `Ag C`, `abstract_expansion_on` gives equal coefficients, hence equal fibre sums. This implication is **OPEN-AGREE-BRIDGE**: `RawAgree Y` means equality of both `Ψ,h` at each site of `Y` (`RenormExpCauchy.lean:RawAgree`);
`i4b_local` and `i4a_local` ask for dependency-site and source agreement, and their `Y` must be thick enough to contain every read site. The block term includes bond neighbours and block averages, so `Y(C)` must also contain those reads;
`LevelLocalCover` gives the root block inclusion in `X₁`, but the full component-to-output inclusion remains to prove.

## 3. Leaves 10b–10c: `locC1`

Let `S=expDom G (XiCOneReal G a ν ε) r₀` and, for each admissible `(D,ξ,s)`, let `(φ_s,α_s)` be `Localization/Decoupled2Background.lean:decBgField/decBgMult` at the chosen cover and radius `rho4`. **PROVED CONDITIONAL ON** `DecSpecs`,
`CoverBase`, `BgHyp`, `c e^{N0 κ₁}≤L^{m₁}`, and membership of `D` in `InUnionDomainC`: `i4b_exists_unique` gives existence and bounds for each `|s_P|≤e^{κ₁}`; `i4b_analytic` gives one analytic `(s,raw D)` map on the strict polydisc; `i4b_one`
identifies its value at `s=1` with `(bgFieldC,bgMultC)`. None of these alone identifies `XiCOneReal` with the needed union domain at a strict margin. `i4b_local` supplies a comparison theorem under its explicit `IsNnComp`, zero/off-family,
parameter, `resDep` and data hypotheses. **OPEN-BG-INPUT** is the uniform physical instantiation of these hypotheses and the class inclusion `φ_s∈bgClass G ν (cK ε) D` for every complex `s`, every admitted `D`, with `cK` fixed before `k,N₁`.

Define `A₁((D,ξ),s)=renC1On G a ν ε (blk z) D.Ψ D.h φ_s ξ`. **PROVED CONDITIONAL ON OPEN-BG-INPUT:** `RenormExpG.lean:an_renC1On` and `i4b_analytic` give joint analyticity in `(raw D,ξ,s)`; the identity at `s=1` follows from `i4b_one`. At fixed
ξ, any `M` bounding `renC1On` for **all** `D∈XiCOneReal` and **all** `v∈bgClass G ν(cK ε)D` bounds `|A₁(D,ξ;s)|` throughout the polydisc by class inclusion. Apply `abstract_expansion_on` with this particular `M` and then (2.2). Because the
argument works for every `M`, it proves the universal transfer clause of `HasLocPrinciple`; the pointwise numeric choice `M=(d+6)(cK ε)^2‖ξ‖ blockWeight G (blk z)` follows separately from `RenormExpBounds.lean:norm_renC1On_le_of_mem`, under its
admissible-weight, datum-size, mass, radius and `ε≤cKε` hypotheses. Fibre sums are jointly analytic by finite summation of AE coefficients on an **open** data/ξ neighbourhood, as in `I5Expansion.localization_expansion`. **OPEN-LOCC1** consists
precisely of OPEN-COVER-PARAM, OPEN-NC-PHYSICAL, OPEN-BG-INPUT, OPEN-AGREE-BRIDGE, the strict domain inclusion, and the finite-set transport.

`XiCOneReal` (`RenormExpBounds.lean:XiCOneReal`) allows a real centre `Ψ₀`, a real vector `h₀`, a complex displacement `Ψ″`, and fixes the complex displacement of `h` to **zero**; it does not fix one physical value of `h₀` across different data.
`HasLocPrinciple` demands `AnalyticOnNhd` on the resulting `expDom`. The needed common open neighbourhood of each such raw datum and ξ is **OPEN-CHART**, unless a relative-chart theorem supplies it. A constant-`h` slice changes the quantified
data domain and would not prove the present field type.

## 4. Leaf 11a: `locC2` and `locDφ`

Set `νu=renMassU ν ξ`, `ζ=renZeta ε ξ`, `f₁,s=renF1 ν ξ D.h φ_s=(νu−ν)(h−φ_s)`, and `φ₀,s=barField G D.Ψ φ_s`. Choose the **real-base-mass route**. `Background/Prop51Mass.lean:isPerturbedM_iff` proves exactly
`IsPerturbedM G a νu α_s φ₀,s Fs δφ δα ↔ IsPerturbed G a ν (α_s+fun _=>νu−ν) φ₀,s Fs δφ δα`. Thus the decoupled mode-U solver may run at the real ν with base multiplier `α₀,s=α_s+(νu−ν)` and source `pertSource G a (ζ Ψ) f₁,s`. This is an
algebraic reformulation, **not** a theorem that its `DecHyp` holds. `RenormExpLemma35.lean:renMassU_sub_norm_le` gives `|νu−ν|≤(32/15)ν‖ξ‖` for `ν≥0`, `‖ξ‖≤1/16`; it pays the multiplier and source margins. Do not treat the mass shift as only an
additive source: it also multiplies `δφ` and must enter `α₀,s`.

**OPEN-REN-DEC-FAMILY, exact needed statement.** Under the physical `CoverLocal`, strict `XiCOneReal`-to-`StrictDataM` embedding, the rate hypotheses of §2, `0<r₀<r≤1/16`, `IsRenSol G a ν ε ε r B F`, and uniform smallness for the shifted data,
there exists `(δφ_s,δα_s)` jointly analytic on an open neighbourhood of `S×{|s_i|<e^{κ₁}}`, satisfying the `DecFixed` equation at ν for `(α₀,s,φ₀,s,ζΨ,f₁,s)` and its `dphi` identity; for all admitted triples it has
`SupBounds G δφ_s (cK cK2 B‖ξ‖)` and `(δφ_s,α_s+δα_s)∈pertClass G (cK cK2 B‖ξ‖) (bgK1 xiC1 ε+cK cK2 B r₀+2) νu`; at `s=1` it equals `F((D.Ψ,D.h),ξ)`; and for two truncated parameters and data satisfying `RawAgree Y(C)` it has the `i4a_local`
agreement on every `renC2On` read site and at the source root. Constants here abbreviate the exact `d,L,N` arguments in `RenormExpInput.locC2`.

**Proof route, conditional.** `Decoupled2SolveAnalytic.lean:i4a_analytic` gives a jointly analytic solution of `DecFixed` in the strict `StrictDataM` domain, given `FamSpec`, `AnSpec`, `CoverBase`, numeric `δ₀,δ₁≤deltaStar'`, and the analytic
map from `(D,ξ,s)` to shifted `Edat`. `Decoupled2FieldLocal.lean:i4a_local` compares two solutions under its `CoverLocal`, `HatConn`, `DecHyp`, `IsNnComp`, parameter and `DataAgree` hypotheses. Supply those by the background family,
multiplier-shift estimate, and the geometric dependency bridge. At `s=1`, `decG_one` within the landed I-4a route and `isPerturbedM_iff` identify the fixed equation with `IsRenSol.solves`; the decoupled small bound must imply
`Small G δα_s (c6 d L N)` so that `IsRenSol.unique` identifies both components. This small-radius implication is an explicit **OPEN-UNIQUENESS-MARGIN** check. The displayed class bounds are **OPEN-REN-CLASS**, since the landed
`RenormExpBounds.lean:renSol_mem_pertClass` applies only to the true `s=1` field.

Given OPEN-REN-DEC-FAMILY, let `A₂((D,ξ),s)=renC2On G a (blk z) ξ νu (α_s+δα_s) δφ_s` and `A_p((D,ξ),s)=δφ_s(p)`. `RenormExpG.lean:an_renC2On` gives joint analyticity of `A₂`; evaluation gives that of `A_p`. Their value at one is exactly the
`locC2` and `locDφ` target by the uniqueness step. For any `M` bounding `renC2On` on its entire `pertClass`, respectively evaluation on every field satisfying the `SupBounds` class, the decoupled class memberships bound `A₂`, respectively `A_p`,
for all complex `s`. Apply `abstract_expansion_on`, the agreement bridge, and (2.2); finite fibre summation yields both `HasLocPrinciple` fields with `Kloc=1` and rates `κa,κb≤2κ`. The numeric `M` for `A₂` comes from `norm_renC2On_le_of_mem`;
the numeric `M` for `A_p` is `cK cK2 B‖ξ‖`. These are **PROVED CONDITIONAL ON OPEN-REN-DEC-FAMILY**, OPEN-COVER-PARAM, OPEN-AGREE-BRIDGE, OPEN-TRANSPORT and OPEN-CHART, not unconditional physical results.

## 5. Nonvacuity and build order

**PROVED:** `RenormInputZero.lean:isLocExp_zero_cover` gives zero old terms on every cover; `HasLocPrinciple.of_single` and `renormExpInput_zero_pair_cover` extend the whole-torus witness to a cover containing a proper set, but all its extra
terms vanish. This establishes type-level inhabitation only. `Fluctuation/LevelLocalCover.lean:levelLocalCover` is the smallest landed *general-scale geometric setting* for each of `locC1`, `locC2`, and `locDφ`: one block or one site root with a
proper `X₁` whenever the torus has enough cells; no fixed minimum admissible `N₁` is asserted by that theorem. `Inhabited/RootActiveSizeWitness.lean:T01_nonempty` and `T01_ne_univ` concern a different cube-indexed size example and supply no
renormalization principle. A **genuine** proper-cover instance for `locC1` needs the background family and one nonzero proper coefficient; `locC2` and `locDφ` need OPEN-REN-DEC-FAMILY and nonzero proper coefficients. No such instance is
currently landed. The first nonvacuity test should exhibit two admissible data agreeing on one proper output set and varying outside, with the same local term, together with a nonzero term on that set.

Proposed Lean leaves below are **NEW**, not citations. Each has one main theorem, ≤300 lines; split helper calculations into earlier leaves if needed. “Start now” means prove the conditional interface without claiming its physical hypotheses.
“Strong” and “Sonnet” indicate suggested assignment strength only.

| Order | Exact target conclusion and hypothesis boundary | Status / assignment |
|---|---|---|
| 10a.1 | `renLoc_fin_domains`: with the finite label subtype above and `levelLocalCover` hypotheses, define `Ys` and `dY` and prove `↑(fin Y)=Y`, `dY≥0`, root `CovSetup`, attained tree and `Δ=0`. | **OPEN-TRANSPORT**; Sonnet; start now. |
| 10a.2 | `renLoc_fibre`: assuming the exact `localization_expansion` rate, cover, label and disjointness hypotheses, prove (2.2), and for `κout≤2κ` the `Kloc=1` inequality on `Ys`. | **PROVED** mathematically by `gm4`+`gm3_fam`; Sonnet; start now. |
| 10a.3 | `renLoc_raw_agree`: under an explicit `resDep`/read-site containment premise, prove `RawAgree(fin(Y(C)))→Ag C` and coefficient congruence, including the block bonds and source root. | **OPEN-AGREE-BRIDGE** geometry; strong; start now with explicit premise. |
| 10b.1 | `renBg_dec_family`: under `XiCOneReal→InUnionDomainC`, `DecSpecs`, `CoverLocal`, strict margins and cover identification, construct analytic `(φ_s,α_s)`, prove `s=1`, `bgClass` membership and `i4b_local` agreement. | **OPEN-BG-INPUT**; strong; start now conditionally. **CHART-SENSITIVE.** |
| 10c | `locC1_zero`: from 10a.1–3 and 10b.1, prove exactly `RenormExpInput.locC1`, with universal `M`, `Kloc=1`, and analytic terms on `expDom`. | **OPEN-LOCC1**; Sonnet; start after 10b.1. **CHART-SENSITIVE.** |
| 11a.1 | `renMass_dec_data`: for `‖ξ‖<r₀≤1/16`, prove the `isPerturbedM_iff` shifted `Edat` identity, `DecHyp`/`StrictDataM` inclusions with numeric margins, and joint analytic dependence. | **OPEN** shifted-data bounds; strong; start now. **CHART-SENSITIVE.** |
| 11a.2 | `renDec_pert_family`: under 11a.1 and 10b.1, construct OPEN-REN-DEC-FAMILY, prove the displayed `pertClass` and `SupBounds`, `s=1` equality by `IsRenSol.unique`, and `i4a_local` agreement. | **OPEN-REN-CLASS/UNIQUENESS-MARGIN**; strong; start after 11a.1. **CHART-SENSITIVE.** |
| 11a.3 | `locC2_locDphi_zero`: from 10a.1–3 and 11a.2, produce exactly both `HasLocPrinciple` fields, same `dY,Kloc=1`, rates `κa,κb≤2κ`; prove universal transfer separately for the product class and `SupBounds`. | **OPEN** physical producer; Sonnet; start with 11a.2 as hypothesis. **CHART-SENSITIVE.** |

The chart decision changes the **statements** of 10b.1, 10c, 11a.1, 11a.2 and 11a.3 if it replaces `XiCOneReal` by a constant-`h` slice or an ambient extension. It does not change the geometric 10a leaves. `XiCOneReal` fixes only the *complex
displacement* `h″=0`; a theorem on one fixed `h₀` is insufficient for the current record. `Fluctuation/RenormInputZero.lean:renormExpInput_zero_of_fields` then assembles the five fields, and its consumer bounds use no further cover facts. The
two remaining physical fields `expE0` and `expM0` are independent open inputs.
