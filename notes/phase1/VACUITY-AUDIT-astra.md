# Balaban hypothesis vacuity audit

**Verdict.** The global large-field history defect is confirmed. `FlowSteps` and every `RegionHistory` are empty; `RegionSeq` is empty when `L ≥ 2`. This also makes the `RipeWindow` and `HistIso` bundles empty because their parameters include a `RegionHistory`. I found no second unconditional contradiction in the other landed bundles in the mechanical inventory below. Several research-level bundles remain **SUSPICIOUS** because no independent inhabitation witness was found; this is a limit of this audit, not an emptiness claim.

## Frozen input and method

Audit date: 2026-10-12 UTC. The source scan is tied to the SHA-256 values of all 729 `Balaban/**/*.lean` files in `SOURCE-HASHES.txt`. The repository was clean at the final freeze, commit `087ed81c6e4b678d074dee5e87c79bd062db46e8`. It advanced from `3d5c93c0d01d10348b7205741f46562bedd2f0c1` while this audit was running; the intervening commit changed `AGENTS.md`, not the Lean source anchors cited here. No file under `/home/scott/Balaban` was edited by this audit.

I enumerated 178 actual `structure`/`class` declarations (119 syntactically `Prop` valued), then scanned named `Prop` bundles and the requested theorem names. I checked field combinations for unbounded natural-number descent, inconsistent bounds, empty carriers, and pointwise equalities. `THEOREM-HITS.txt` is the exact `rg` output for the requested theorem-name families. `AFFECTED-HITS.txt` records every direct source occurrence of `FlowSteps`, `RegionHistory`, or `RegionSeq` (257 lines); `RECURRENCE-HITS.txt` records 33 separately written all-scale `hnn` hypotheses. Section-variable binders also affect later declarations without repeating the type name, so the affected-theorem lists below use those source contexts as well as direct hits. Verdicts below are about *logical inhabitation for at least one admissible parameter choice*. They do not certify that the intended nonempty geometric or physical instance has been constructed. The inventory gives a paper witness sketch or an explicit unresolved reason; the four emptiness mechanisms were checked in Lean.

## Confirmed emptiness and affected theorems

| Bundle and exact source | Verdict and proof | Affected landed theorems | Minimal repair |
| --- | --- | --- | --- |
| `FlowSteps`, `Balaban/LargeField/History/FlowSteps.lean:100` (`ok.two_le_L` and `hnn : ∀ k, n k = S.L * n (k+1)`) | **EMPTY** for every `S,n,R,k0`; `VacuityCore.lean:17`. Iteration gives `n 0 = L^m n m`, contradicting `0 < n m` at `m = n 0`. | Every theorem taking `F : FlowSteps`, and every theorem taking a `RegionHistory`. Direct downstream examples: `flow_counter` (`LargeField/Counter/InstantiationFlow.lean:27`), `lemmaB` and `lemmaB_recursive` (`LargeField/Budget/LemmaB.lean:158,254`), `quietKernel_bound` (`LargeField/Operators/QuietBound.lean:43`), `preOp_pkgBound` (`LargeField/Operators/CompBound.lean:1389`), `locOp_pkgBound` (`LargeField/Operators/LocOpBound.lean:36`), and `locOp_level`, `locOp_kept`, `locOp_domain`, `locOp_b_supp`, `locOp_support`, `locOp_factor`, `locOp_commute` (`LargeField/Operators/LocOp.lean:322,328,336,390,429,446,464`). | Put the recurrence on `k < K` for a fixed finite horizon (or index sides by `Fin (K+1)`), then thread the horizon through the history APIs and prove a positive finite-horizon side sequence exists. |
| `RegionHistory`, `Balaban/LargeField/History/RegionHistory.lean:29` (`F : FlowSteps …`) | **EMPTY**, inherited; `VacuityCore.lean:28`. | All the `RegionHistory`-dependent results in the preceding row, plus `locOp_rot_invariant`, `locOp_euclid_invariant` (`LargeField/Operators/Invariance.lean:126,385`) and the `RegionHistory` methods across `LargeField/History`, `LargeField/Budget`, and `LargeField/Operators`. `StepData`/`KeptData` themselves are not shown empty, but their `∀ H : RegionHistory, …` fields at `LargeField/Operators/StepData.lean:173-191,250` currently quantify over an empty type. | Repair `FlowSteps` first; then construct one `RegionHistory` with the corrected finite horizon and nonempty components for the intended use. |
| `RegionSeq`, `Balaban/LargeField/Region/Generating.lean:70` (`hnn` at every `i`) | **EMPTY when `2 ≤ L`**, `VacuityCore.lean:22`. The declaration alone has no `2 ≤ L` field; the proof does not rule out `L = 1`. | Every theorem or construction taking `S : RegionSeq` under `L≥2`, including `OmegaAt_compl_subset_Z`, `mem_flowOmega`, `RegionSeq.nesting`, and `flowGeneratingSet` (`Generating.lean:97,160,173,183`), plus `RegionSeq.Z_grow` (`Region/Overwrite.lean:147`). The standalone `fine_eq`, `cubeMap_eq_comp`, and `cubeMap_succ` (`Generating.lean:130,136,143`) take the same all-scale `hnn` and positive `nn`; they too have empty premises once `L≥2` is added. The earlier `nn_eq_pow` and `nn_eq_pow'` (`:103,111`) lack the positive-side hypothesis and can be instantiated with `nn≡0`, so they are not empty. | Bound the recurrence to a finite horizon and carry that horizon in `RegionSeq` and the standalone cube-map lemmas; retain `L ≥ 2` explicitly where mathematically intended. |
| Unbundled all-scale `hnn : ∀ i, n i = L * n (i+1)` together with `[∀ i, NeZero (n i)]`, e.g. `Balaban/LargeField/Budget/Fine.lean:31` and `Operators/CompBound.lean:61` | **EMPTY when `2≤L`**, by the same `VacuityCore.lean:6` lemma. This is a hypothesis combination, not a separately empty named structure: at `L=1` it can be inhabited. | Direct grep index: `RECURRENCE-HITS.txt` (33 occurrences). The affected conditional statements include `card_fineSet`, `cubeMap_surjective`, `fineSet_injective` (`Budget/Fine.lean:31,47,61`), `card_blocks_cube`, `mWit_baseF_le` (`Base/BaseWitnessGauss.lean:87,102`), `exists_near_of_mem_dataSites`, `baseSpinSupport_of_baseRecord` (`Base/BaseSupport.lean:50,73`), `histScale_eq` (`Characteristic/Analytic.lean:43`), and `blockCube_eq_cubeMap`, `blockSub_fineSet_succ_iff` (`Operators/CompBound.lean:61,69`). The grep index also includes two purely algebraic `nn_eq_pow` lemmas with no positivity assumption; those are **not** empty. | Replace the unbounded `hnn` argument with `∀ i < K, …` where only levels through `K` are used, or obtain a finite-horizon recurrence from the repaired history. |
| `RipeWindow`, `Balaban/LargeField/History/RipeWindow.lean:37`; `HistIso`, `Balaban/LargeField/Operators/Invariance.lean:176` | **EMPTY**, inherited from their `H : RegionHistory` parameters; `VacuityCore.lean:28` supplies the contradiction. | Results taking either bundle, including the history-ripeness and Euclidean-invariance results in those files; `locOp_euclid_invariant` is explicit at `Invariance.lean:385`. | Repair and witness `RegionHistory`; no local field weakening fixes the parent type. |
| `InUnionDomainC`, `Balaban/Background/Data.lean:308`, and `ApproxSetting`, `Balaban/Background/ApproxLocal.lean:67` | **EMPTY only when `1 < ν * (L^k)^2`**; `DomainEmpty.lean:15,23`. Their `0 < δ ≤ ε` and `ν L^{2k} ε² ≤ δ²` force the mass factor `≤ 1`. | Any theorem invoked with those bundles in the supercritical mass regime. The main `theorem52_*`, `theorem71/72/73_*` statements carry `BgHyp.massLe` (`Background/ExistenceSetup.lean:47`), so this boundary does **not** by itself vacate their intended regime. Direct `InUnionDomainC` consumers occur in `Background/Def5.lean:204,219`, `LargeField/Characteristic/Reg.lean:93-94`, and `Fluctuation/Expansion*.lean` (see source grep). | Make `ν L^{2k} ≤ 1` explicit at direct consumers that intend nonempty domains; retain the existing `BgHyp.massLe` elsewhere. |
| `RegC`, `Balaban/LargeField/Characteristic/Reg.lean:93` | **EMPTY when `1 < μ * (L^q)^2`**, by its `InUnionDomainC` conjunct at `:94` and `DomainEmpty.lean:15`. | `RegC`-domain results in `LargeField/Characteristic/Analytic.lean:66` and its symmetry transport in `LargeField/Characteristic/RegSymm.lean:206`; the latter equivalence remains true but relates empty predicates in this regime. | Carry `μ (L^q)^2 ≤ 1` at a direct `RegC` entry point, normally via `BgHyp.massLe`. |
| `IsEscPath` at `d = 0`, `Balaban/LargeField/Geometry/Escape.lean:45` | **EMPTY only in dimension zero**; `DegenerateEmpty.lean:6`. A nearest-neighbour step would require an element of `Fin 0`. | `IsEscPath.tail`, `JoinedToInf.shift`, `JoinedToInf.conn_path` (`Geometry/Escape.lean:97,130,139`) and `path_meets_boundary` (`Geometry/LemmaS.lean:118`) have empty path antecedents at `d=0`. The intended geometric results use positive dimension (notably `Escape.lean:86` takes `i : Fin d`). | State `0 < d` at any entry point claiming an escape path. |
| `InPsiTilde` / `InPsiTildeC` at `N = 0`, `Balaban/Background/Data.lean:262,280` | **EMPTY when `dataSites G` is nonempty and `δ ≤ 1`**; `DegenerateEmpty.lean:14,26`. The squared norm is zero, so (R2) requires `1 < δ`. | Direct consumers include `psiTilde_subset_xiAt`, `psiTildeC_subset_xiC` (`SmallField/XiD2.lean:116,166`), `perturb_inPsiTildeC` (`SmallField/XiPerturb.lean:37`), and `bg_mass_bound` (`Background/Mass116.lean:46`). These instances are vacuous in the stated regime. Root statements use `N ≥ 2`. | Require `0 < N` (normally `2 ≤ N`) where the domain is meant to contain data. |

The conditional rows are ordinary parameter boundaries, not a new globally empty declaration. In particular, the small-mass condition already appears in `BgHyp` and `DGSetting`.

## Requested main-theorem surface

| Family and source anchor | Audit verdict | Evidence or witness sketch |
| --- | --- | --- |
| `flow_counter`, `lemmaB*`, `quietKernel_bound`, `preOp_pkgBound`, `locOp_*` | **EMPTY premise** | Each needs a `RegionHistory` directly or through a section variable; anchors are in the first finding. `S.Good`, `BudgetSetup`, kernels, and labels cannot repair that parent contradiction. |
| `i5_stage1`, `i5_stage2` (`Localization/I5Chain.lean:156,243`) | **INHABITED on paper at an empty-geometry boundary** | Take `d=L=3`, `N₁=6`, `K=0`, `N≥2`, `ν=0`, empty `Gp,Gk,Gj` positive layers and `X₀=X₁f=∅`. `decSpecs_exists` supplies `c,BG≥0`; take `κ>0`, then large `m₁` for `hM`, `r₀≥4dL³`, and `ϱ` large enough for `hr`, `BgHyp.hϱ`, and both separation conditions in `DGSetting`. Use constant unit real data to satisfy the small `XiCData` domain at scale zero. In `ChainNum`, `composedCloseBound` is a fixed nonnegative multiple of `eps` (`I5Close.lean:38`, `DecoupledFieldClose.lean:973`); set `δ₃` equal to that bound and shrink `eps>0` until all upper bounds hold. Positivity of `c7`, `bgC0`, `bgC1`, and `deltaStar` is proved at `DecoupledBackground.lean:101`, `Background/ExistenceSetup.lean:119`, `DecoupledBackground.lean:79`, and `Background/Contraction.lean:404`. This is a paper witness, not a compiled constructor. |
| `i5_background` (`Localization/I5.lean:41`) | **SUSPICIOUS** | Its `CovSetup.hjK` requires `j+1≤K` (`TreeLengthCov.lean:133,138`), and `hopt` requires a nonempty connected `W₀⊆X` (`I5.lean:44-47`); thus the zero-scale and empty-polymer sketches above cannot witness the whole theorem. A positive-scale compatible cover, `BgSetting`, and the additional large-`κ` inequalities have no joint witness in this audit. No contradiction was proved. |
| `i4a_*`, `i4b_*`, `i4c`/`decCov*` (`Localization/Decoupled2Solve.lean:60`; `Decoupled2Background.lean:94`; `DecoupledCovPrincipal.lean:1232,1381`) | **INHABITED in a degenerate geometry; nonempty geometry unresolved** | Take `G.Ω j = ∅`, `C.cubeIdx = ∅`, `ν = 0`, constant admissible weights, and large separation. Every cover condition over a cube or site is then vacuous; `DecSpecs` has explicit existential theorems at `Localization/DecoupledBackground.lean:51` and `Decoupled2Background.lean:43`. This does not witness a nonempty cover. |
| `lemma24_*` (`Fluctuation/Covariance.lean:52-241`) | **INHABITED in a degenerate geometry** | `hfam : ∀ x ≥ 0, XData … x …` adds only `0 ≤ x` to the `x`-independent setting fields (`Localization/DecoupledXGreen.lean:35-42`); use the empty generating set, `ν=0`, `κ=0`, `s=1`, and sufficiently large `m₁`. |
| `marked_cubes*` (`Polymer/MarkedCubes.lean:372,498`; `MarkedCubesTwo.lean:185`; `MarkedCubesLocal.lean:132`) | **INHABITED at the empty-label boundary** | `CubeLabels` (`Polymer/MarkedCubes.lean:68`) and `LabelAct` (`:169`) allow `Lb = Empty`; dependent conditions and sums over labels then vanish. A nonempty-label witness was not checked. |
| `termwise_irrelevant*` (`SmallField/RenormTermwiseIrrel.lean:105,147`; `RenormTermwiseCrude.lean:420`) | **INHABITED for `N ≥ 2`** | `PremisesTerm` needs distinct `i₀,i₁`; take `N=2`, a singleton polymer containing zero, zero analytic term, nonnegative counting constants, and a constant unit-spin datum with small positive `σ,ε`. The source premises at `SmallField/RenormTermwiseDefs.lean:42` do not require a conflicting sign. |
| `IsSFFamily.bridgeInf` (`SmallField/Def6BridgeInfMoment.lean:282`) | **SUSPICIOUS** | `MomNum` (`SmallField/Def6InfTail.lean:394`) has compatible-looking finite-scale inequalities. `IsSFFamily` has a zero-scale witness sketch below, but `bridgeInf` assumes `1≤j≤k`; no compatible positive-scale joint witness was checked. No contradiction was derived from its fields. |
| `theorem52_*`, `theorem71/72/73_*` (`Background/Theorem52.lean:44,57`; `Def5.lean:171,218`; `Theorem73.lean:246,306`) | **INHABITED parameter/domain regime** | Take `ν=0`, `δ=ε>0` below `bgC0,bgC1`, `N≥1`, a constant real unit vector for `Ψ,h`, zero complex perturbations, and an empty or compatible generating set. Then the mass inequality holds. The actual theorems use `BgHyp.massLe` (`ExistenceSetup.lean:47`). |
| `rootC_of_rootFAndC1Star` (`Correlations/RootCFromFlow.lean:21`) | **SUSPICIOUS** | The `RootFAndC1Star` antecedent (`Correlations/C1Star.lean:156`) includes `Nonempty C1Star` and all `RootFClauses`; this is the substantial unproved flow interface, not a found syntactic contradiction. Its kernel side has an explicit witness theorem `Balaban.kernelHyp_and_large_holds` (`Correlations/KernelLargeAssembly.lean:22`). |
| `LF2` (`LargeField/Counter/LF2.lean:150`) | **INHABITED abstract premise** | `LF2Hyp.n_succ` is bounded by `k < K` (`Counter/LF2.lean:52-54`). For `K=0`, take `n k=1`, `Zp k=∅`, and all component-indexed functions and conditions on the empty type. The same empty-component construction witnesses `CounterHist` (`Counter/Hist.lean:26`); hence these abstract statements do not share the all-scale contradiction. |

## Inventory verdict key

The full declaration table follows. **INHABITED** is a paper witness for *some* admissible parameters, with one of these sketches: `Z` = empty sets/supports and zero fields or kernels, together with nonnegative bounds; `N` = choose numerical constants in the stated open intervals, enlarge upper-bound constants or scales, and use constant sequences; `F` = finite-horizon side lengths and empty components; `E` = a landed existential theorem cited above; `D` = direct constructor using empty or constant data; `K0` = take the terminal scale `k=0`, so all `1≤j≤k` clauses disappear, and set all localized terms to zero. **SUSPICIOUS** means no complete witness was obtained for the stated joint interface. Conditional empty rows state their exact parameter restriction. A `Z` or `K0` witness is deliberately degenerate and does not establish a populated geometric or positive-scale model.

| Declaration (`Balaban/…:line`) | Verdict | Witness or reason |
| --- | --- | --- |
| `Background/AbstractGreen.lean:136` `GreenFamily` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/ApproxLocal.lean:67` `ApproxSetting` | **EMPTY if mass factor > 1** | `DomainEmpty.lean:23`; otherwise `ν=0`, `δ=ε>0` |
| `Background/ApproxLocal.lean:82` `DataWit` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Background/Calculus.lean:277` `StarBound` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/Calculus.lean:426` `GreenSetting` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/CompositionDomain.lean:820` `Hyp63` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/CompositionEstimates.lean:243` `FieldBounds` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/CompositionEstimates.lean:314` `CompHyp` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/CompositionSystem.lean:116` `IsComposedSystem` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/Contraction.lean:656` `Prop51Hyp` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/ContractionCore.lean:95` `Setup` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/ContractionCore.lean:301` `CoreHyp` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Background/Data.lean:111` `BgData` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Background/Data.lean:262` `InPsiTilde` | **EMPTY if `N=0`, sites nonempty, `δ≤1`** | `DegenerateEmpty.lean:14,26`; for `N≥1`, constant unit data, `ν=0` |
| `Background/Data.lean:280` `InPsiTildeC` | **EMPTY if `N=0`, sites nonempty, `δ≤1`** | `DegenerateEmpty.lean:14,26`; for `N≥1`, constant unit data, `ν=0` |
| `Background/EquivarianceLat.lean:95` `NbrSymm` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/EquivarianceLat.lean:117` `TorusSymm` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/EquivarianceLat.lean:129` `LatSymm` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/ExistenceBounds.lean:35` `BgBounds` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/ExistenceSetup.lean:41` `BgHyp` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Background/ScaledComposition.lean:96` `ScaledPsiC` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Background/ScaledComposition.lean:120` `HypS` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Correlations/C1Star.lean:124` `C1Star` | **SUSPICIOUS** | U: no independent witness for the joint analytic/renormalization interface |
| `Correlations/GreenIdentification.lean:73` `KernelHyp` | **INHABITED** | E: landed existential theorem at compatible parameters |
| `Correlations/MainTerm.lean:52` `KernelHypLarge` | **INHABITED** | E: landed existential theorem at compatible parameters |
| `Correlations/RealSequences.lean:64` `SeqHyp` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `External/BKAR/Forest.lean:292` `AcyclicEdgeSetData` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/Forest.lean:434` `ForestIndex` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/Forest.lean:473` `Forest` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/Forest.lean:730` `EdgeExtension` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/OrderedExpansion.lean:177` `ActiveExtension` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/OrderedForest.lean:44` `ConsData` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/OrderedRemainder.lean:37` `ActiveBranchData` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/OrderedTerminalGrowth.lean:37` `TerminalGrowth` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `External/BKAR/OrderedTerminalGrowth.lean:329` `ActiveTerminalBranchData` | **INHABITED** | D: empty forest/edge set or a single legal extension |
| `Flow/MatrixInfty.lean:95` `InftyRange` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Flow/RGEquations.lean:196` `TriangularBounds` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Fluctuation/MeasureInterp.lean:49` `IsC1Family` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `Fluctuation/MeasureInterp.lean:279` `IsC1FamilyR` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `Green/Lattice/LocCutoff.lean:76` `CutoffProfile` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `LargeField/Analytic/Constants.lean:60` `RunningHyp` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Analytic/Constants.lean:433` `AnalyticConsts` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Analytic/Constants.lean:454` `AnalyticLamAt` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Background/Factorization.lean:36` `PieceDecomp` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Background/StepGenSets.lean:158` `BoundaryHyp` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Base/BaseRecord.lean:197` `BaseRecord` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Base/SpinsNearBackground.lean:64` `BaseSpinSupport` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Budget/Exponents.lean:35` `BudgetConsts` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Budget/LemmaB.lean:37` `BudgetSetup` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Characteristic/Measurable.lean:236` `RealFamily` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Counter/Conditions.lean:18` `LamStarConditions` | **INHABITED** | E: landed existential theorem at compatible parameters |
| `LargeField/Counter/Conditions.lean:62` `FlowLamConditions` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Counter/FlowHorizon.lean:30` `FlowSeq` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Counter/FlowHorizon.lean:556` `Matches` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Counter/Hist.lean:26` `CounterHist` | **INHABITED** | F: take an empty component family; for `LF2Hyp`, `K=0`, `n≡1` |
| `LargeField/Counter/LF2.lean:52` `LF2Hyp` | **INHABITED** | F: take an empty component family; for `LF2Hyp`, `K=0`, `n≡1` |
| `LargeField/Counter/Main.lean:20` `CounterConclusion` | **INHABITED** | F: take an empty component family; for `LF2Hyp`, `K=0`, `n≡1` |
| `LargeField/Counter/Params.lean:32` `Typing` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Counter/Params.lean:75` `Setting` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Counter/Params.lean:219` `Typing.Ok` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Counter/Params.lean:249` `Setting.Ok` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Geometry/DomainsMod.lean:102` `Seg` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Geometry/Escape.lean:45` `IsEscPath` | **EMPTY if `d=0`** | `DegenerateEmpty.lean:6`; for `d≥1`, a coordinate ray (`Escape.lean:86`) |
| `LargeField/History/FlowSteps.lean:100` `FlowSteps` | **EMPTY** | inherited all-scale `FlowSteps` contradiction; `VacuityCore.lean` |
| `LargeField/History/LocalHistory.lean:36` `LocalHistory` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/History/RegionHistory.lean:29` `RegionHistory` | **EMPTY** | inherited all-scale `FlowSteps` contradiction; `VacuityCore.lean` |
| `LargeField/History/RipeWindow.lean:37` `RipeWindow` | **EMPTY** | inherited all-scale `FlowSteps` contradiction; `VacuityCore.lean` |
| `LargeField/History/Scale.lean:24` `Setting.Good` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/History/Scale.lean:71` `BookInv` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/History/Spine.lean:44` `Spine` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/History/StepCover.lean:33` `OldCover` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/History/StepMerge.lean:17` `T4Facts` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/History/StepSeeds.lean:41` `StepGeom` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/History/StepSpine.lean:107` `SpineNum` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/History/WState.lean:32` `Book` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/History/WState.lean:164` `BookRule` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Operators/Invariance.lean:176` `HistIso` | **EMPTY** | inherited all-scale `FlowSteps` contradiction; `VacuityCore.lean` |
| `LargeField/Operators/Kernel.lean:29` `LFKernel` | **INHABITED** | Z: zero kernel/boundary factor; empty Gaussian witness index where needed |
| `LargeField/Operators/LocOp.lean:51` `OpPkg` | **INHABITED** | Z: zero kernel/boundary factor; empty Gaussian witness index where needed |
| `LargeField/Operators/Setup.lean:33` `Geo` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Operators/Setup.lean:50` `OpConsts` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Operators/StepData.lean:94` `GaussWit` | **INHABITED** | Z: zero kernel/boundary factor; empty Gaussian witness index where needed |
| `LargeField/Operators/StepData.lean:145` `StepData` | **INHABITED** | Z: zero kernel/boundary factor; empty Gaussian witness index where needed |
| `LargeField/Operators/StepData.lean:206` `KeptDatum` | **INHABITED** | Z: zero kernel/boundary factor; empty Gaussian witness index where needed |
| `LargeField/Operators/StepData.lean:217` `KeptData` | **INHABITED** | Z: zero kernel/boundary factor; empty Gaussian witness index where needed |
| `LargeField/Operators/Symm.lean:28` `TorusSym` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/Operators/Symm.lean:74` `HistImage` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `LargeField/R/ChainSeq.lean:27` `IsAdmDelta` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Region/Generating.lean:70` `RegionSeq` | **EMPTY if `2 ≤ L`** | all-scale side recurrence; `VacuityCore.lean:22` |
| `LargeField/Region/Seeds.lean:27` `StepRadii` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Region/Step.lean:110` `RadiusHyp` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `LargeField/Region/Step.lean:180` `RegionStep` | **INHABITED** | D: direct finite data/empty component or constant functions at compatible parameters |
| `Localization/CubeAligned.lean:128` `CubeAligned` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/CubeRegimes.lean:112` `AlignedCube` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecCover.lean:48` `DecCover` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/Decoupled.lean:137` `DGSetting` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Localization/Decoupled2.lean:116` `OpSetting` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Localization/Decoupled2.lean:131` `CoverGeom` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/Decoupled2.lean:146` `CoverBase` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/Decoupled2Background.lean:36` `DecSpecs` | **INHABITED** | E: landed existential theorem at compatible parameters |
| `Localization/Decoupled2Background.lean:53` `IsDecBg` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/Decoupled2Geometry.lean:48` `CoverLocalGeom` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/Decoupled2Geometry.lean:59` `CoverLocal` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/Decoupled2X.lean:64` `XCover` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/Decoupled2XGreen.lean:28` `XData` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/DecoupledBackground.lean:44` `DecSpecs` | **INHABITED** | E: landed existential theorem at compatible parameters |
| `Localization/DecoupledBackground.lean:191` `IsDecBg` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledBounds.lean:171` `StarBd` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledCovAnalyticFull.lean:45` `IsConstraintFieldStrict` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledCovBound.lean:167` `IsUnitLattice` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/DecoupledCovLocal.lean:293` `LocHyp` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledCube.lean:90` `CubeBlockBounds` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledCubeHolder.lean:88` `CubeBlockHolder` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledFieldClose.lean:539` `WSup` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledFieldLocal.lean:454` `DataAgree` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledGs.lean:90` `SupBdW` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledIdent.lean:121` `IsUnitLatticeB` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/DecoupledSolve.lean:195` `DecHyp` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/DecoupledSqrt.lean:135` `CovStanding` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/DecoupledX.lean:83` `XSetting` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Localization/DecoupledXGreen.lean:35` `XData` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Localization/DecoupledXGreen.lean:45` `XWeight` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/I5Chain.lean:117` `ChainNum` | **INHABITED on paper** | Choose `d=L=3`, `N≥2`, `BG≥0`, `κ>0`; set `δ₃` to its `close` lower bound, which is linear in `eps`, then choose `eps>0` sufficiently small for every positive upper threshold. |
| `Localization/I5Fan.lean:62` `BgSetting` | **INHABITED on paper** | The preceding `ChainNum` witness, empty generating-set layers, `N₁=6`, `K=j=0`, `X₀=X₁f=∅`, `ν=0`, large `m₁,r₀,ϱ`, and `decSpecs_exists` supply its fields. |
| `Localization/ReflectedGeneratingSet.lean:54` `FoldSetting` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/TreeLength.lean:555` `PolySetup` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Localization/TreeLengthCov.lean:133` `CovSetup` | **INHABITED** | Take `K=1`, `j=0`, `m₀=0`, `X=𝒦X=∅`, an empty-layer `G`, and `N₁>5`; `j+1≤K` holds and `ChosenOne`/`LayerUnion` quantify over empty sets. This does not witness the additional nonempty `hopt` of `i5_background`. |
| `Multiscale/AgmonCore.lean:262` `IsAgmonWeight` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintField.lean:86` `IsSmoothField` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintField.lean:97` `IsConstraintField` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintLocality.lean:328` `LocData` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintLocality.lean:825` `BaseDec` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintPerturb.lean:215` `Close` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintPerturb.lean:350` `PertData` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintSandwich.lean:165` `Standing` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/ConstraintSup.lean:176` `SupBounds` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/GeneratingSet.lean:60` `GeneratingSet` | **INHABITED** | Z: empty generating set/cover, zero fields, compatible numeric parameters |
| `Multiscale/KernelBase.lean:334` `GreenData` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/PointwiseAgmon.lean:39` `PtSetting` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Multiscale/XVariantIdentities.lean:210` `IsKernelEmbedding` | **INHABITED** | Z: empty support/zero field or kernel with compatible nonnegative bounds |
| `Observables/LayerConstants.lean:30` `ExponentConstraints` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Observables/LayerDef.lean:60` `ObsConsts` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `Observables/LayerDef.lean:66` `ObsConsts.Admissible` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `Observables/LayerDef.lean:75` `ObsTerms` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `Observables/LayerDef.lean:172` `IsObs` | **INHABITED on paper** | K0: set `Ot.μ`, `Ot.M`, `Ot.R`, and `Gker` to zero; `Mobs`, `Robs`, and the sums in `Fcomp` have no positive scale, while `topGS` has `Ω₁=∅`. The remaining `ident` derivatives are zero. |
| `Observables/LayerDef.lean:278` `IsSFObs` | **INHABITED on paper** | K0: combine the `IsSF` and `IsObs` zero-scale witnesses with their common zero `Terms`. |
| `Observables/LayerStructure.lean:62` `IsBgAt` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `Polymer/Expansion.lean:94` `KPCond` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `Polymer/MarkedCubes.lean:68` `CubeLabels` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `Polymer/MarkedCubes.lean:169` `LabelAct` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `Polymer/Ursell.lean:357` `Tgt` | **INHABITED** | D: direct finite/constant constructor at compatible parameters |
| `SmallField/Def6.lean:44` `Consts` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Def6.lean:62` `Consts.Admissible` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `SmallField/Def6.lean:87` `Terms` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Def6.lean:187` `IsSF` | **INHABITED on paper** | K0: `topGS` has `Ω₁=∅` (`Def6Terms.lean:51`), so the action and `Fcomp` vanish; `Ecomp` sums over `Icc 1 0=∅`. Take `Ek=0`, zero terms, and `ρ` the real indicator of the displayed `Xi` condition. |
| `SmallField/Def6.lean:329` `TorusIndep` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Def6.lean:431` `RenormCond` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Def6.lean:448` `RenormCondTorus` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Def6.lean:466` `CoeffBounds` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `SmallField/Def6.lean:486` `IsSFFamily` | **INHABITED on paper** | K0: use the preceding zero-term `IsSF` uniformly in `N₁`; torus-independence and renormalization clauses require `1≤j≤0`. Choose `d=L=3`, `ξ=0`, small `c₈,ν₀>0`, large `β₀`, and `a₀=5/4` for `CoeffBounds`. |
| `SmallField/Def6.lean:506` `ContAtZero` | **INHABITED on paper** | K0: choose `β(ν),a(ν)` constant in `ν`; their limits exist, and `termsE`/`termsM` require `1≤j≤0`. |
| `SmallField/Def6BridgeLift.lean:467` `LiftCtx` | **SUSPICIOUS** | U: no independent witness for the joint analytic/renormalization interface |
| `SmallField/Def6BridgeLift.lean:715` `PremisesCore` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/Def6InfPaving.lean:39` `GoodMap` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Def6InfTail.lean:394` `MomNum` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `SmallField/RenormCtx.lean:28` `Ctx` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormData.lean:74` `Frame` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormDefs.lean:104` `TermFamily` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/RenormDefs.lean:134` `Premises` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormDefs.lean:176` `DataHyp` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormNumeric.lean:21` `SigPow` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `SmallField/RenormNumeric.lean:70` `NumCtx` | **INHABITED** | N: compatible numeric parameters/constant sequence; see key and main surface |
| `SmallField/RenormShape.lean:202` `TermOK` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormTermwiseCtx.lean:30` `CtxTw` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormTermwiseDefs.lean:42` `PremisesTerm` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/RenormTermwiseDefs.lean:69` `SumConds` | **INHABITED** | Z: `N≥2`, zero terms on singleton/empty polymer family, constant unit datum |
| `SmallField/Xi.lean:75` `XiBounds` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |
| `SmallField/Xi.lean:126` `XiCBounds` | **INHABITED** | Z: zero terms/bounds and constant unit data at compatible parameters |

## Named `Prop` definitions used as bundles

| Definition (`Balaban/…:line`) | Verdict | Witness or obstruction |
| --- | --- | --- |
| `Multiscale/Operator.lean:39` `IsAdmissibleWeights` | **INHABITED** | Constant weights `a j=1` satisfy every interval, including positive horizons. |
| `Background/Composition.lean:83` `Precedes` | **INHABITED** | Reflexivity for any generating set, or inclusion between empty layers. |
| `Multiscale/ConstraintSup.lean:201` `GreenSupSpec` | **INHABITED** | `exists_green_sup` at `:212` supplies a constant for `d,L≥3`. |
| `Correlations/C1Star.lean:156` `RootFAndC1Star` | **SUSPICIOUS** | Requires the unproved joint Root-F and C-1* construction; no field contradiction found. |
| `Background/Data.lean:294,300` `InDomainR`, `InDomainC` | **INHABITED** for `N≥1` | Constant real unit data, zero perturbation, `ν=0`, `δ=ε>0`. Empty for `N=0`, nonempty data sites and `δ≤1` by `DegenerateEmpty.lean:14,26`. |
| `Background/Data.lean:308` `InUnionDomainC` | **EMPTY if mass factor > 1** | `DomainEmpty.lean:15`; nonempty at mass zero with positive radius constants and constant unit data. |
| `Background/Data.lean:313` `InUnionDomainR` | **INHABITED** for `N≥1`, `c₁>0` | Constant unit data, `ν=0`, choose `0<δ≤c₁`. |
| `Background/Data.lean:124,186,194,200,206` `BgData.IsReal`, `IsRealUnitField`, `IsEL`, `IsSmallSolution`, `IsMinimizer` | **INHABITED** in empty geometry | Empty `Ω₁`, constant unit exterior data and zero multiplier make site-indexed equations vacuous; no witness of a populated geometry claimed. |
| `Background/ContractionAnalytic.lean:66` `StrictData` | **INHABITED** in empty geometry | Zero perturbation and empty support. |
| `Localization/Decoupled2One.lean:29`, `DecoupledOne.lean:30` `OneSpec` | **INHABITED** | `oneSpec_exists` in the corresponding files (`Decoupled2One.lean:42`; `DecoupledOne.lean:43`). |
| `Localization/Decoupled2SolveAnalytic.lean:30`, `DecoupledSolveAnalytic.lean:101` `AnSpec` | **INHABITED** | `anSpec_exists` in the corresponding files. |
| `Localization/Decoupled2Field.lean:191`, `DecoupledField.lean:355` `FamSpec` | **INHABITED** | `decGreenFamily` (`Decoupled2Field.lean:232`; `DecoupledField.lean:408`). |
| `Localization/Decoupled2FieldClose.lean:31,60`, `DecoupledFieldClose.lean:732,761` `Dg2Spec`, `CloseSpec` | **INHABITED** | `dg2Spec_exists` and `closeSpec_exists` in those modules. |
| `Localization/DecoupledFieldHolder.lean:35` `HolSpec` | **INHABITED** | `holSpec_exists` at `:59`. |
| `Localization/Decoupled2Geometry.lean:90` `HatConn` | **INHABITED** in empty geometry | Take `C.cubeIdx=∅` and `H.Ω₁=∅`; the required connectivity statements quantify over no cover cubes. |
| `Localization/DecoupledGeometry.lean:210` `HatConn` | **INHABITED** in empty geometry | With `G.Ω₁=∅`, the cube index is empty, so all connectedness clauses are vacuous. |
| `Localization/TreeLengthCov.lean:44` `ChosenOne` | **INHABITED** | Take `X=𝒦=∅`; both directions of the cover condition have empty antecedents. |
| `Localization/I5Chain.lean:73` `XiCData` | **INHABITED** for `N≥1` | Constant unit real data, zero complex perturbation, `ν=0`, and small positive `eps`. |
| `LargeField/Operators/KerBound.lean:85` `KerBound` | **INHABITED** | The zero `LFKernel` has integral zero, bounded by `exp(-κ)` for any real `κ`. |
| `LargeField/Operators/StepData.lean:116` `GaussStepSpec` | **INHABITED** | Zero step kernel and an empty finite witness index `W` make the Gaussian sum zero; choose the zero dominating function. |
| `LargeField/Characteristic/Reg.lean:88,93` `Reg`, `RegC` | **INHABITED** in the small-mass domain | `RegC` contains `InUnionDomainC` at `:94`, so it is conditionally empty above the mass threshold; choose empty regions and constant unit data at `ν=0` for the compatible case. |
| `LargeField/History/StepCover.lean:41,53` `AllGood`, `CoverClaim` | **INHABITED** | Empty old-component family and empty cover; any positive cap needed by `OldCover.pos` is then vacuous. |
| `LargeField/History/FlowCover.lean:35` `CoveredBy` | **INHABITED** | Take `c=∅`, `B=∅`, and any `N`; the empty set is covered. |
| `LargeField/History/Step.lean:21` `RestartFacts`; `History/StepKinds.lean:34` `Setting.RecInv` | **INHABITED** | Choose pre-window bookkeeping and a direct membership witness in the finite merge set where required. |
| `Localization/TreeLength.lean:119` `Covers` | **INHABITED** at the empty-set boundary | Take `R=univ`, `A=∅`, `W={x}` for any torus site `x`, `E=∅`, and `c≥0`. `ConnStruct` requires the singleton `W` to be nonempty (`TreeLength.lean:42,92`); its cost is zero. |
| `Localization/DecoupledSolveAnalytic.lean:37,53` `StrictDataP`, `StrictDataM` | **INHABITED** in empty geometry | With `G.Ω₁=∅` and `dataSites G=∅`, every strict field inequality is over an empty index, for either mode. |
| `LargeField/Budget/Exponents.lean:88` `IsKeptEvent`; `History/GainClock.lean:52` `GainKept`; `Operators/LocOp.lean:299` `IsKept` | **EMPTY as full instantiated history claims** | Each takes or inherits a `RegionHistory`; repair the parent history first. |

No landed `IsRep*` declaration was found by `rg` in `Balaban/**/*.lean`. `StepData` and `KeptData` are structures, so their inventory rows are above. `KerBound` and `GaussStepSpec` are the named `Prop` definitions requested in the prompt.

## Refutation attempts and remaining limits

- The all-scale recurrence was checked adversarially against the finite-horizon counter. `LF2Hyp.n_succ` is restricted to `k < K` (`LargeField/Counter/LF2.lean:54`), and an empty-component `K=0` instance satisfies that requirement. The contradiction therefore belongs to `FlowSteps`/`RegionSeq`, not to the abstract LF-2 theorem.
- The mass-domain warning was checked against the point of use. `BgHyp.massLe` and `DGSetting.massLe` already supply `ν L^{2k}≤1` (`Background/ExistenceSetup.lean:47`; `Localization/Decoupled.lean:147`). A supercritical instantiation is empty, but the main background and localization hypotheses do not force one.
- Empty covers and empty generating sets show consistency of several localization bundles but can themselves make geometric conclusions weak. This audit did not prove a **nonempty** `CoverLocal` or `XCoverLocal` witness satisfying the cut-operator bounds.
- The `SUSPICIOUS` rows (`C1Star`, Root-F/C-1*, and `LiftCtx`) and the positive-scale `bridgeInf` and `i5_background` hypothesis combinations need explicit compatible witnesses or a separate theorem-driven non-vacuity check. The zero-scale small-field witnesses and empty-geometry I-5 stage witnesses do not address these positive-scale interfaces. No emptiness theorem was found for them.
- This was a hypothesis-consistency audit. It did not check mathematical source correspondence, proofs of theorems once instantiated, or construction of the physical large-field trajectory.

## Verification

The following commands returned exit code 0, one Lean process at a time, from `/home/scott/Balaban`:

```text
lake env lean /home/scott/Balaban-scratch/astra-vacuity/VacuityCore.lean
lake env lean /home/scott/Balaban-scratch/astra-vacuity/DomainEmpty.lean
lake env lean /home/scott/Balaban-scratch/astra-vacuity/DegenerateEmpty.lean
```

The proof files contain no `sorry`, `admit`, or custom axiom. No full Lake build was run, and the active worker's fixes were not inspected or modified. Audit closeout: the mechanical declaration inventory is complete for this frozen scan; all proven-empty findings have Lean certificates; the explicitly `SUSPICIOUS` bundles remain open non-vacuity checks.
