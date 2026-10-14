# SF3TYPE: the separation index and a local successor class

**DECISION (2026-10-13; the author deferred to the orchestrator).** Option (a) of T1/T4: the ambient `StepClass` stays at `rhoSep m₁`; the local successor terms use the existing class structures at a separate index `ϱloc` with `bgR0 d L ≤ ϱloc ≤ 5L·L^{m₁}`; ambient and local coefficients are related by an explicit equality on common physical data. No core structure is changed now; the `LocalSuccessor` wrapper of T4 waits until a physical local term exists.

**PROVED (source inventory).** Read-only main commit `74cea1e805af188cd508c54c936428fa469a787a`; read-only worker branch `w597-local-generator` at `c8f6b1c41cd2c1d7a3d4d162a41f3a86b8314193`. No build was run. `LocalGeneratorSource.lean` exists on that branch, not on main.

## T1. What the type parameter permits

**PROVED.** `Multiscale/GeneratingSet.lean:60–75` declares `GeneratingSet d L N₀ k ϱ` with `separation : ∀ j, 1 ≤ j → j < k → ∀ x, x ∉ Ω j → ∀ y ∈ Ω (j+1), ϱ * L^j < torusDist x y`. Thus `ϱ` certifies a *lower* gap. `GeneratingSet.weakenSep` (`Multiscale/WeakenSep.lean:57–65`) changes a certificate from `ϱ'` to `ϱ ≤ ϱ'` without changing `Ω`; its layer, spacing, data-site and `GsSpecStrong` invariance lemmas are at lines 67–103 and 200–215.

**PROVED.** Numerical theorems nevertheless read the *declared* index: `BgHyp.hϱ : bgR0 d L ≤ ϱ` (`Background/ExistenceSetup.lean:35–44`); `DGSetting.cover_sep : 4d L L^{m₁} ≤ ϱ` (`Localization/Decoupled.lean:137–149`); `I5Fan.BgSetting.hr : r₀L^{m₁} ≤ ϱ-1` with `hr₀ : 4dL³ ≤ r₀` (`Localization/I5Fan.lean:62–86`). Weakening an ambient set to a smaller class index preserves its geometry but makes these premises unavailable at that new index.

**PROVED.** `Def6.Terms.gs` has type `ℕ → Set CTorus → GeneratingSet d L (N₁*L^{m₁}) k ϱ` (`SmallField/Def6.lean:89–95`). `Def6v2Domain.FieldDom.dom` takes a generator at the *same* `ϱ` (`:66–70`). The worker's `localB j hj X hsep` has that type only under `hsep : ϱ ≤ minSep L (L^{m₁}) = 5L L^{m₁}` (`LocalGeneratorSource.lean:41–47`, branch above). `I5Inhabited.rhoSep` at :216–217 equals `bgR0 3 3 + 360·3^{m₁} + 1 + tail`, with nonnegative terms (`rhoSep_tail_nonneg`, `bgR0_nonneg_aux`); hence `rhoSep m₁ > 5·3·3^{m₁}`. **REFUTED:** `localB` can be inserted directly into `zeroClass … (rhoSep m₁)` or into an `IsSF3` retaining that single tower index.

**PROVED.** Option (a) chooses `ϱloc` with `bgR0 d L ≤ ϱloc ≤ 5L L^{m₁}`; the interval exists exactly when that inequality holds, and for fixed `d,L ≥ 3` it exists for sufficiently large `m₁`. At the fixed tower `d=L=3`, `bgR0 3 3 ≥ 36` while `5L=15`, so `polyGS` at `5L` cannot satisfy `BgHyp`; `localB` at `ϱloc=bgR0 3 3` is typeable once `5·3^{m₁+1} ≥ bgR0 3 3`. The class's `eucEloc/Mloc` premises explicitly use `levelGS (ϱ := ϱloc)` (`Def6.lean:233–257`), and `FieldDom.dom j (levelGS …)` uses that same index. Keep the ambient `GA : GeneratingSet … (rhoSep m₁)` for `DGSetting`/`BgSetting`, and transport only fields or class-facing statements through `GA.weakenSep` when required; do not apply the high-gap theorems to its weakened copy.

**OPEN (formal transport).** `xiFieldDom.dom j G := XiDom G …` (`Def6v2Domain.lean:92–97`), so `FieldDom.dom` has no independent numerical use of `ϱ`. `XiDom` unfolds to `XiC` (`Def6Terms.lean:86–93`), whose witnesses and solution bounds use `G`'s domains and spacing (`SmallField/Xi.lean:106–169`). `WeakenSep.lean` proves invariance of the raw real/complex union domains and data carriers, but no landed `XiDom (G.weakenSep h) ↔ XiDom G` lemma was found. Its full proof must transport the canonical real and complex background solutions and every `XiBounds`/`XiCBounds` field, rather than cite only `inUnionDomainC_weaken`.

**PROVED (type-change count).** Option (a) changes **zero core structure declarations**: instantiate existing `Terms`, `FieldDom`, `SFTermClauses`, `IsSF2` at `ϱloc`; it needs a new family/member and comparison lemmas. Option (b), if made a replacement interface, changes at least **seven** named core structures in **three** files: `Terms`, `IsSF`, `IsSFFamily` (`Def6.lean`); `FieldDom` (`Def6v2Domain.lean`); `SFTermClauses`, `IsSF2`, `IsSFFamily2` (`Def6v2.lean`). A direct textual search for `Terms d L N₁ m₁ k N ϱ` or `FieldDom d L N₁ m₁ k N ϱ` hits **68 Lean files**, including **38 SmallField files**; this is a scope indicator, not an independent theorem count. Option (c), replacing `Terms.gs` by `Σ ϱ', GeneratingSet … ϱ'`, changes that field and every use of `Tm.gs` in the class clauses, in particular `FieldDom.dom` applications and `GsSpecStrong`; it also needs an ambient/local index selector. It has no smaller proved migration than (a).

**PROVED / OPEN.** `Fluctuation/StepIdentityInhabited.lean:34–39` defines `zeroClass … ϱ` with `Tm := Def6.zeroTerms … ϱ` and `Def6Inhabited.lean:48–55` gives whole-level `gs`. At `ϱloc` one may instantiate a *new* zero term family; its coefficients and `Ek` are still zero. **OPEN:** a class equivalence from the fixed `zeroClass … (rhoSep m₁)` to a local-generator member requires the local `pavingGS` and domain clauses and, for any nonzero output, coefficient identity on common data. Changing `ϱ` alone does not transport the fixed `StepClass` type.

## T2. What the landed `polyGS` class proves

**PROVED.** `SmallField/GsSpecPoly.lean:150–182` defines `polyGS hj X` using `minimalGenSet` with `M1=1`, `N₁'=N₁L^{m₁}`, `q=k`; its index is `minSep L 1=5L`, and `gsSpecCore_polyGS`/`gsSpecStrong_polyGS` cover `IsPolyDom` polymers. `GsSpecPolyEqv.lean` supplies `CubeIso`/`plAux_equiv`; `GsSpecPolyClass.lean:27–48` proves `pavingGS_polyGS`.

**PROVED.** `GsSpecPolyClass.localTerms` (:52–58) has `E=M=0`, `gs=polyGS` for `j≤k`, and `topGS` for `j>k`. `sfTermClausesStrong_localTerms` (:77–120) proves `SFTermClausesStrong P Dom localTerms` for **every** `FieldDom … (5L)` under its stated positivity assumptions: `gs_spec`, analyticE/M by `analyticOnNhd_const`, rotation/Euclidean covariance, localE/M, bounds, `pavingGS`, and `gsStrong`. `sfTermClausesStrong_localTerms_nonempty` (:124–130) gives an inhabitant at `witnessConsts`. A repository search found consumers only in `GsSpecPoly.lean`, `GsSpecPolyEqv.lean`, `GsSpecPolyClass.lean`; it is not the fixed tower's `zeroClass` or a physical output theorem.

**PROVED.** The two actual constructors differ: `polyGS` thickens in cubes of side `L^n`, whereas branch `localB` uses `M₁L^n=L^{m₁+n}` (`LocalGeneratorSource.lean:41–47`). The `polyGS` comments call it P3's minimal set, but that wording cannot make these differently scaled Lean objects equal. `localB_Ω_top_eq`, `gsSpecStrong_localB` and `localB_dataSites_range` (:104–168) establish the physical `M₁` geometry when `X` is a union of its cubes. **REFUTED:** the existing `polyGS` class by itself solves the P3 `M₁=L^{m₁}` local-generator requirement or supports `BgHyp` at `d=L=3`, since `bgR0 3 3≥36>15`.

**PROVED / OPEN.** The landed `polyGS` class proves analyticity on `Dom.dom j (polyGS …)` only for its identically zero `E,M`. **OPEN:** no landed theorem found proving `AnalyticOnNhd` on `XiDom (polyGS …)` for a physical nonzero term; the landed clause cannot be substituted for this result.

## T3. One-cell trace reachability

**PROVED.** In the one-top-cell case `Y`, the branch theorem `localB_Ω_top_eq` makes `Y` the top layer (under its cube-union hypothesis), so the trace of a local raw datum on `Y` is top-block-constant. Its lower-layer fine variation outside `Y` is invisible to the trace. A whole-level ambient generator admits top-block-constant data; therefore that outer variation alone does **not** refute the trace-space inclusion in (TR) of `LOCALENGINE.md:21–29`.

**PROVED (raw extension); OPEN (chart extension).** For a real `p∈XiAt B_Y`, regard its top-block trace on `Y` as a function on the finite graph of top blocks. Each real component has a finite Lipschitz constant; the McShane formula extends that scalar component to all top blocks with the same constant and unchanged trace. This gives ambient block-constant raw values, but does not preserve the vector norm, the *same* ambient chart radius, the real union-domain constraints, alignment with the constant `h₀`, or the ambient canonical `bgField/bgMult` inequalities in `XiBounds`. `XiAt` includes those solution bounds (`SmallField/Xi.lean:106–115`). `xiDom_of_close` (`Def6BridgeDomain.lean:218–247`) covers a small ball around a fixed unit vector with a radius tied to `δ²`, not every `p∈XiDom B_Y`. Thus one-cell (TR) is **OPEN**, neither refuted by fine variation nor proved by raw interpolation.

**OPEN (exact missing estimate).** Supply, uniformly for each local chart point, an ambient top-block-constant raw extension preserving the trace on `Y`, lying in the ambient `InUnionDomainR/C` at the required parameters, and proving all ambient `XiBounds/XiCBounds` for its *canonical* solutions at the class radius. The real case is already needed; the complex version and a local holomorphic right inverse are needed for analytic descent. `WeakenSep` cannot provide this: it changes the index of one fixed `Ω`, whereas (TR) changes the generating set and its solution problem.

## T4. Recommendation to the author

**PROVED (recommended interface shape); OPEN (its inhabitance and output).** Retain the high-gap tower object and attach a separate low-index local term family. A narrow source-facing declaration is a wrapper, schematically:

```lean
structure LocalSuccessor (ϱhi ϱloc : ℝ) where
  ambient : StepClass d L N₁ m₁ k N ϱhi
  terms : Terms d L N₁ m₁ (k+1) N ϱloc
  dom : FieldDom d L N₁ m₁ (k+1) N ϱloc
  hloc : ϱloc ≤ minSep L (L^m₁)
  hbg : bgR0 d L ≤ ϱloc
  clauses : SFTermClausesStrong P dom terms
  -- plus explicit coefficient identity on physical/common data
```

**OPEN.** This is interface text, not elaborated Lean. The branch `localB` can fill `terms.gs` at `ϱloc` once `hsep` and polymer cube-union bridges are supplied; its covariance under the class paving group and the physical output's local analyticity still require proofs. Keep `ambient` at `rhoSep m₁` for `DGSetting`/`I5Fan`; establish a separate explicit equality between ambient and local coefficients on common physical data. The `polyGS` zero-term inhabitant demonstrates the *shape* of a local `SFTermClausesStrong` witness but does not give the `M₁` witness or nonzero successor terms.

**PROVED (workflow); OPEN (successor claim).** Postpone replacing the established `StepClass`/`Terms` type until the general-class successor step is implemented. The present fixed-tower zero input is already used at `rhoSep` by many source and activity declarations (for example `Inhabited/ZeroSourceActivityCommon.lean` and `Inhabited/E1RecordFromTower.lean`); no current `polyGS` consumer supplies the local-domain output. For the *output of the zero input*, first prove the physical coefficient on `XiDom (localB …)` by local recomputation or by (TR) plus exact trace locality and physical equality, then package the low-index `SFTermClausesStrong` member. Do not infer this analytic clause from zero analyticity of the input terms. Tell the author explicitly that the high-index `zeroClass` remains valid as an ambient step object while the P3 local successor class is a separate open theorem.

**PROVED (confidence in source/type inventory); OPEN (analytic geometry).** High confidence in the numerical type obstruction and landed `polyGS` clauses; moderate confidence in the scope estimate (it is textual); no asserted proof or counterexample for (TR) or the physical local-domain analyticity.

## NEXT (W715)

1. At `ϱloc = bgR0 d L`, with `hsep : bgR0 d L ≤ minSep L (L ^ m₁)`, prove
   `localB_xiDom_of_xiCData`: `XiCData (localB j hj X hsep) A μ j (scaledC0 d) ε D`
   and `scaledC0 d ^ 2 * ε ≤ ε'` imply
   `XiDom (localB j hj X hsep) A μ j ε' D.Ψ D.h`.
   Also prove `localB_xiFieldDom_of_xiCData`, the same conclusion as
   `(xiFieldDom A μ εseq).dom j (localB j hj X hsep) D.Ψ D.h` when `ε' = εseq j`.
   These are same-generator chart realizations; `StepActivityClassChart.xiDom_of_xiCData`
   transports the real and complex witnesses and the `XiBounds`/`XiCBounds` radius estimates.
2. For the domain inclusion needed by a local successor class, the target is an
   explicit `FieldDom.Sub` or pointwise `hsub` from the actual ambient step chart
   to `xiFieldDom` at `localB j hj X hsep`, with the physical composed pair as input.
   `GeneralClassMatch.rayInDomain_dom_of_xiCData` shows its proof shape: construct
   a local `XiCData` witness for that pair at the class radius and apply item 1.
   `WeakenSep` invariance transports a fixed generator's raw data and domains;
   it does not compare an ambient generator with `localB`, whose domains and
   canonical solutions differ. The remaining input is the local solution estimate
   of `Xi.lean` for the physical composed pair (P3 (4.46)–(4.47), printed pp. 78–79).

**W715 status.** The conditional `XiCData → XiDom → FieldDom.dom` part of item 1 is proved
in `SmallField/LocalGeneratorClassDomain.lean`, including a specified raw field pair.
The physical realization part of item 1 and item 2 remain open: the present ambient
high-index step supplies neither a local `XiCData` witness for its composed pair nor
the comparison of its canonical background solutions with those on `localB`.

## NEXT (W717)

**REFUTED (physical full-raw-field witness on a proper local generator).** For an
ambient chart datum `Damb = composedDataAtC A μ … Dtop` at `levelGS j`, the requested
statement is `∃ Dloc : BgData (localB j hj X hsep) N, Dloc.Ψ = Damb.Ψ ∧
Dloc.h = Damb.h ∧ XiCData (localB j hj X hsep) A μ j (scaledC0 d) εloc Dloc`.
For any `x ∉ dataSites (localB j hj X hsep)`, `Dloc.Ψ x = 0` by `BgData.Ψ_zero`.
If `Damb` lies in the ambient `XiCData` chart, its complex union-domain condition gives
`|∑ᵢ Damb.Ψ(x,i)^2| > 7/8`: P2 (R2) and (C2) give a difference from `1` less than
`2δ ≤ 2 bgC1 ≤ 2 bgC0 ≤ 1/8`. Thus the full raw-field equality is impossible;
the squared-spin discrepancy exceeds `7/8`, independently of `εloc` or any radius loss.
`no_localB_xiCData_of_ambient_xiCData` proves the obstruction in Lean whenever
the local data sites are a proper subset of the torus.

**PROVED geometry.** `localB_precedes_levelGS_of_le` puts every local `Ω_i` inside an
ambient whole-level `Ω_i`; `localB_dataSites_subset_levelGS_omega_one` puts the local
union domain in its `Ω₁`.
**Bound inventory.** Ambient `XiCBounds.hAbs` has a potentially usable layer-index
inequality after restricting `h''`. Ambient `grad`, `lap`, `mult`, `val`, `close`, and
`hDot` concern the ambient canonical background, while their local versions concern
`bgFieldC/bgMultC` on `localB`; `collarBond` tests new local collar bonds absent from
the whole-level collar. The real `XiBounds` have the same background mismatch.
No finite radius constant transfers these fields. P3 pp. 78–79 (4.44)–(4.47)
recomputes locally; a true theorem must restrict raw fields to local sites and recompute the background and term.

## NEXT (W720)

**PROVED.** `LocalGeneratorRestriction.lean` clips an ambient `BgData` to the data sites of
`localB` and proves equality on those sites and on its `Ω₁`. Every local interface pair is
an ambient whole-level interface pair; the local layer mass weight is at most the ambient
one. Thus `localB_smallField_restrict` carries the complex union data domain to the local
generator, including its new collar bonds. This assumes the source mass condition `0 ≤ μ`.

**PROVED with radius loss.** `localB_xiCData_restrict` recomputes the local backgrounds through
`psiTildeC_subset_xiC` and obtains `XiCData` at radius
`ε + (2 bgK1 d L N + 1) δ` from an ambient data-domain witness `(δ, ε)`.
`localB_fieldDom_hsub` gives pointwise `hsub` for the *full ambient raw pair*,
because `XiDom` may adjust its displacement off the local sites. Its sufficient class-radius
condition is `bgC0 d L N + (2 bgK1 d L N + 1) bgC1 d L N ≤ εseq j`.

**OPEN.** This coarse radius condition is not established for the physical class sequence;
a sharper estimate from the ambient chart radius is needed. `OldXiDomOpenC` still needs an
open set of physical shifts and a class term family whose generator is `localB` at the low
index; its current `StepClass`, `FieldDom`, and `Terms` parameters share one separation index.

## NEXT (W723)

The physical class uses `εseq j = P.eps d L j` (`Def6.Consts.eps`, P4 (H.1)); its
`xiFieldDom` chart is `XiDom … j (P.eps d L j)` with `σ=1`. P3 (4.46)–(4.47),
printed pp. 78–79, recomputes a local term on `𝔹(Y)` and applies Lemma 4.2 on
that local chart; the formula is a local `Ξ^c` radius, not a fixed `bgC0` radius.
For zero background mass, P3 (Ξ1) gives data radius
`δ=ε=xiC1 d * εamb`; (D2) then gives local chart radius
`K * εamb`, `K=(2*bgK1 d L N+2)*xiC1 d`. The smallness requirements are
`(4d+6)(2d+1) εamb ≤ 1` and `xiC1 d * εamb ≤ min(bgC0,bgC1)`.
This estimate certifies a local chart at the *same* physical radius only with
`K*εamb ≤ P.eps d L j`; that budget fails when `εamb=P.eps d L j` and `K>1`.
At `d=3`, `xiC1=140`, so `K=280*(bgK1 3 L N+1)>280`.
For positive mass and `j<k`, landed (D1-j) controls only the level-`j` mass
norm; landed (D2) consumes the full scale-`k` data norm. A level-`j` (D2)
is needed to obtain this linear estimate without a zero-mass assumption.

## NEXT (W758) — the radius of the local class (D1)

**PROVED (P3 pp. 74–79, page text).** P3 has one radius sequence and no inclusion of an ambient chart in a local one. Production: (4.46) is analyticity on Ξ_{k+1}(𝔹_{k+1}(Y); 1, ε'), ε' ≤ ε_{k+1}, from Lemma 4.2 applied to the term *recomputed* with 𝔹_{k+1}(Y) (p. 79); its radius condition is (4.37) ε' + (K₂+1)δ₃ ≤ ε_k, the same as with 𝔹_{k+1}. Consumption: Lemma 4.1 (4.29) keeps ε' under composition (weight a(𝔹_j,𝔹_k) ≤ 1), then (4.39) Ξ^c(𝔹_j(X); a, ε_k) ⊂ Ξ(𝔹_j(X); 1, ε_j).

**DECISION (proposed).** The local class uses the class sequence itself, ε^loc_j = `P.eps d L j`, with step chart radius ε_{k+1} at level k+1. W723's K enters nowhere.

**PROVED (Lean, W758).** Consumption of a class at R₀ with gs = `localB` costs the test of `levelGS`: `classOldDecLocal_expansion_index` (class at its own index), `classOldDecLocal_expansion_localB`, `xiCRaw_localB_sub_xiFieldDom`, `bgSetting_localB_termGen` (a step setting with 𝔹_k = `stepG` holds with term generator `localB` at R₀). Whole-level composed pairs (`Ecomp`, `OldXiDomC`) need only the local pair in the domain: `SFTermClauses.analyticAt_E_of_agreeOn`/`analyticAt_M_of_agreeOn`, `SFTermClausesStrong.analyticAt_E_composedPairAt` (localE + `localPairAt_agree`); W720/W723's hsub is off the critical path. D3: `isSF2_localBZeroTerms`, `sfTermClausesStrong_localBZeroTerms(_nonempty)` (`SmallField/LocalZeroClass.lean`): a class member at R₀ with gs = `localB` (zero terms; the M₁ witness missing in T2/T4).

**REFUTED (a) K on the successor only.** Over an input at `P.eps`, (4.37) with ε' = Kε_{k+1} fails: `not_localLoss_eps_succ_le` (ε_k ≤ 2L^α ε_{k+1}, `epsSeq_le_two_rpow_mul_succ`; K = (2K₁+2)C₁ ≥ 2000·L²·C₁ > 2L^α for α ≤ 2, `two_rpow_lt_localLoss`; at d = L = 3 by a factor > 7·10⁵). A uniform ε^loc = K·`P.eps` (ambient chart at ε/K) is consistent in (4.37) but needs hsub, proved only at μ = 0 (W723), and gains nothing.

**REFUTED (b) "step chart at ε/K" as a production route.** hsub maps the ambient chart into the local one; analyticity on `XiDom (localB …)` needs the converse, (TR) of LOCALENGINE. For N = 2, (TR) fails (sketch, not in Lean): a polymer Y containing a loop of top blocks that bounds a disc outside the data sites of 𝔹(Y) carries a winding-one real configuration with small differences in the local chart, while an ambient chart point has small differences on all top-block pairs, hence discrete winding 0 around that loop.

**REFUTED (c) — with the landed constants no radius choice is consistent for any class with old terms, whole-level or local.** The chart test of the expansions, C₀²(C₀²ε + K₂δ₃ + K₂δ_fl) ≤ ε_k (`point_facts`/`eTerm_chain` then `xiDom_of_xiCData`, C₀ = `scaledC0 d` = 8d+12), with chart radius ε ≥ ε_{k+1} (the successor domain must lie in the chart of the new terms) is false: `not_chartTest_eps_succ`, `not_chartTest_newest` — it needs C₀⁴ ≤ ε_k/ε_{k+1} ≤ 2L^α; at d = L = 3, 36⁴ ≈ 1.7·10⁶ against < 3.5 (factor > 4.8·10⁵). m₁ does not enter; L would have to exceed (C₀⁴/2)^{1/α} > 7·10¹¹ at d = 3. So GENERAL-XI-RESCALE (GENERAL.md §1) is false as stated, not a choice of α₀; the step chart radius must also be ε_{k+1} itself, not 2ε_{k+1} as in the zero-class tower (ε_k/ε_{k+1} = L^α(1 + k^{-2}/T_{k+1}) < √3(1 + k^{-2}) < 2 for k ≥ 3 at d = L = 3; remark, not in Lean). **Fix (OPEN, next leaf):** the θ-sharp chain of (4.29). `xiBounds_compose`/`xiCBounds_compose`/`xiC_compose` use of C₀ only `1 < C₀`; with a constant c ∈ (1, L] in its place, σ_j = cL^{j−K} ≤ 1 for j < K, and with a σ-monotonicity lemma for `XiC` the composed datum lies in Ξ^c_j(𝔹_j; 1, ε) at the *same* ε. Generalize these three in place (landed statements as corollaries at c = C₀), rerun `point_facts` at σ = 1: the test becomes ε + K₂(δ₃+δ_fl) ≤ ε_j, i.e. (4.37).

**OPEN — exact obstruction of D2 (engine, not radius).** The successor terms recomputed on 𝔹_{k+1}(Y) cannot be produced by the landed engine: `not_bgSetting_localB` (`BgSetting.index_ge`: ϱ ≥ 4dL³M₁ + 1; `DGSetting.false_of_le_minSep`: 4dLM₁ ≤ ϱ ≤ 5LM₁ impossible) and `not_isLevel_localB` (fan/hat/fluctuation theorems need `IsLevel Gp (k+1)`) (`Fluctuation/LocalSuccessorEngine.lean`). The ratios 4d/5 and 4dL²/5 do not involve m₁ and grow with L, so neither helps. Needed: WIDEGEN route A/C (sharp X₀ distance at 5LM₁ and a local hat lift) or route B (widened generator, a source change for the author). D3 for physical successor terms waits on this.
