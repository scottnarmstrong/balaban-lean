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
