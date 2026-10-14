# TORUSCOH3: analytic core of the two-torus cut comparison

**PROVED (source state).** Main `/home/scott/Balaban` was read at commit `8a1bdf723d2e424cfea29662e2c1f7b1b1847cab`; finished `w589-two-torus-thick-sets` at `85a3b0f4146e5441481f63ecc1f700becbdc6521`; present `w593-two-torus-data` at `beb413e06042ee53077a41a795e98c369566c634`. The latter is a branch snapshot, not a main-tree landing. No build was run and the Balaban tree was not edited.

## T1. The actual background system

**PROVED.** On one torus, `Localization/DecoupledBackground.lean:191–200` defines `IsDecBg G a ν ρ s D φ α` as three clauses: `Small G α ρ`; `DecFixed G a ν s true 0 φ₀ f₀ α`, where `φ₀ = approxField G a ν D.Ψ D.h` and `f₀ = residual G a ν D φ₀`; and `φ = φ₀ + dphi G (decG G a ν s) 0 φ₀ f₀ α`. `DecFixed` is `Nmap … (dphi … α) = α` (`DecoupledSolve.lean:53–58`); `decG` uses `Gs = Gstar · (1-Kcal)⁻¹` (`Decoupled.lean:80–95`). The pair's exported `hF₁` identifies `F₁(s,rawOf D)` with every qualifying `IsDecBg` solution (`Localization/I5FluctFacts.lean:140–146`), so selected pair values can be replaced by this system.

**PROVED.** `Fluctuation/PhysicalVRawY.lean:73–111`, `compY_geometry`, gives `IsNnComp`, `s=1` off `parCubes`, `s=0` on unselected parameter cubes and agreement on selected cubes inside the component. For `Y` and `B=SY G X₁ 𝒞 Y`, `Localization/RowsBg.lean:347–391` defines `RowsDep G a ν B` as the union of `resDep x` for `x∈B∩Ω₁` and `approxDep y` for `RowSite G a ν 0 B y`. `i4b_local_rows` says two qualified same-torus solutions with equal raw data on this set have equal multipliers on `B` and equal corrections `φ−φ₀` on `Y`; it also gives field equality at the specified read rows. `FootprintFl.i4b_local_of_agree_on_component` is a wider-data corollary (`Localization/FootprintFl.lean:63ff`). **REFUTED:** same-torus locality is itself a comparison of different torus carriers.

**PROVED (two-sided linear block fact).** The cut Green operator has more than a one-sided row theorem. `DecoupledLocal.lean:241–269`, `blk_conditions`, proves *both* `P M_q=M_q=M_q P` for an active cube inside `Y`, and `P M_q=0=M_q P` for an active cube outside, for each `M_q` with row support in `intBox q` and right support through `cD q`. `sum_block_facts` (:223–239) gives `P Kcal=Kcal P` and `P Gstar=Gstar P` when applied to their cube sums; `Gs_local` (:281–376) uses exactly these identities and `block_locality` (:32–77). The component cut geometry required by `dg5'_inner` (`DecoupledFieldLocal.lean:169–279`) proves the active-cube dichotomy. Thus rows outside `Y` cannot linearly read columns inside `Y` through `Gstar`, `Kcal`, or their invertible cut resolvent. This is a landed same-torus algebraic mechanism, though its two-torus conjugacy is **OPEN**.

**OPEN (closed component formulation).** A useful *new* definition is `BgFixedOn B s D α := ∀ x∈B∩Ω₁, (Nmap G (dirichletOperator G a ν 0) true φ₀ f₀ (dphi G (decG G a ν s) 0 φ₀ f₀ α)) x = α x`, with the exact `DecFixed` arguments substituted from its definition. It is meaningful without inventing a restricted operator, but it still mentions whole-torus `dphi`; prove that its value on `B` depends only on `α|B` and `D|RowsDep(B)` by the cut block identities plus the row-local `Nmap` argument in `RowsBg.local_step_rows` (:102–158). This is a finite-dimensional component system only after that dependence theorem. Calling the displayed restriction itself `IsDecBgOn` without that theorem would hide the main issue.

## T2. Component uniqueness and transplantation

**PROVED.** `i4b_local_rows` already supplies the required same-torus uniqueness *on `B`* for two genuine `IsDecBg` solutions with data agreeing on `RowsDep(B)`. Whole-torus `i4b_exists_unique` (`DecoupledBackground.lean:232–246`) gives uniqueness of the entire pair on one fixed carrier and a pointwise `Small G α (rho4 …)` condition. It cannot be applied across carrier types.

**OPEN (two-torus transplant).** Let `b` be W589's `boxMap`, `Y'=bY`, `B'=bB`, and take data agreeing under W593 `RawBoxAgree` on a box containing both read sets. The desired proof transports the *restricted* solution from the first torus to the second and compares it with the second solution. The algebraic outside-to-inside and inside-to-outside separation of `Gstar/Kcal` is available as above; what is not landed is conjugacy of their **inner finite matrices** under `b`, including `cubeG=(cubeH)⁻¹ cD`, and closure of the nonlinear fixed-point rows under the chosen gluing region.

**OPEN (gluing caution).** Patching `α` on `B=SY` and taking `α'` outside `B` is not justified by `Gs_local`: `Nmap` contains the Dirichlet row of `dphi`, and a row just outside `B` may read a changed correction at a neighbouring site in `B`. One must either glue on a larger row-closed component (naturally `Y`, with the hat-box buffer) and prove `Nmap`'s outside rows are unaffected, or compare the restricted Picard maps directly. The pointwise `Small` bound of a *valid* patch follows by taking the maximum of the two bounds; it is not the missing ingredient. No landed theorem named `decBg_glue_isDecBg` or two-torus `IsDecBg` transport was found.

**OPEN (component uniqueness statement).** After proving restriction independence and conjugacy of the restricted Picard maps, the intended theorem is the following. `BgFixedOn` means the `DecFixed` equation at `B` for a whole-carrier representative; the conclusion is independent of that representative by `local_step_rows`. The common `ρ` is the landed `rho4`, and `Small` must be required on both full representatives so that the contraction applies.

```lean
theorem decBg_component_unique (C : TwoTorusCut G G' a ν s s')
    (hD : C.RawAgree D D')
    {α : G.Ω 1 → ℂ} {α' : G'.Ω 1 → ℂ}
    (hfix : C.BgFixedOn D α) (hfix' : C.BgFixedOn' D' α')
    (hsmall : Small G α ρ) (hsmall' : Small G' α' ρ) :
    ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.B →
      α x = α' (C.bΩ x)
```

**OPEN (exact block lemma to add).** For `P=indY G Y` and each admissible potential `α`, establish `P Kcal=Kcal P`, `P Gstar=Gstar P` and `P Gs=Gs P` as exported lemmas under `compY_geometry`; the first two are already constructed inside `Gs_local`, and the third follows by commutation with `(1-Kcal)⁻¹`. On the proposed gluing region `Z`, additionally prove for all bounded candidate multipliers `ξ,η` that `ξ=η` outside `Z` and equal outside data imply `Smap(ξ)=Smap(η)` outside `Z`. This last **nonlinear outside-row** statement, not `dg5'_inner` alone, validates a whole-torus glued fixed point.

## T3. The fluctuation fixed point

**PROVED.** `Localization/RowsFl.lean:101–110` gives `DataAgreeRows` on `B_F=SYF C H a ν X₁ 𝒞 Y` and `R_F=RowF H a ν B_F`: base potential on `B_F`, base field on `R_F`, perturbation and source on `B_F`; its theorem adds adjacent-collar agreement of `δΨ`. `i4a_local_fpS_rows` (:230–259) compares two *same-carrier* `DecFixed` solutions in the landed `c6' d L N (famConst d L BG κ) (gamma1 d / 8)` ball, yielding multiplier equality on `B_F` and `dphi` equality on `Y`. `Dec2.i4a_exists_unique` (`Decoupled2Solve.lean:60–87`) gives whole-carrier uniqueness in that ball. The pair's `hSol` includes the field equation, `DecFixed`, both smallness bounds, `SupBounds`, and uniqueness (`I5FluctFacts.lean:149–168`).

**OPEN.** Transport must carry `SYF`, `RowF`, collar adjacency, `DataAgreeRows`, the `pertSource` rows, and the paired-cover cut matrix. W589's `compY_image` and `resDep_levelGS_image` concern `levelGS`; they do not by themselves transport the paired `Hm`/`DecCover` fluctuation carrier. The paired proof uses `Dec2.dg5'_inner` (`Decoupled2FieldLocal.lean:105ff`) and `RowsFl.local_step_fpS_rows` (:157–211). As for background, a two-sided cut Green block identity does not alone establish the outside rows of the nonlinear `Smap`; either prove their gluing closure or use conjugate restricted Picard iterations.

## T4. Proposed Lean interfaces

**OPEN (new common context).** The following signatures are *proposed*, not elaborated declarations. `TwoTorusCut` is to carry two level generating sets and, for Sol, both `CoverLocal` carriers; `b` is the W589 box map; `bΩ` and `bHm` are its maps on selected `Ω₁` subtypes; `Y,B,BF` and their primed versions are `Finset`s with image equalities; `s,s'` are cuts satisfying `compY_geometry` on each side and corresponding on inner cubes; `hmargin` keeps all read, cube and hat supports in the box. Its data field is W593 `RawBoxAgree {z | RowsDep G a ν B z} (rawOf D) (rawOf D')`, extended as needed to `approxDep` at `Y`; the Sol field also carries `SrcBoxAgree` on `B_F` and collar reads. The record must *not* assume equality of solutions, Green rows, or fixed-point maps.

**OPEN (worker BG-1, 150–250 lines after geometry).** The first theorem is the cut resolvent conjugacy on a component. It needs `cubeH` row correspondence, finite inverse conjugacy for `cubeG`, re-indexing of `Gstar` and `Kcal` through W589 `cubeIdx_filter_image`, and W589's `active_levelGS_image`/`resDep_levelGS_image` for the data-dependent rows. `approxField` and `residual` are finite local formulas (`DecoupledBackgroundLocal.lean:36–115`); `cubeG` and `(1-Kcal)⁻¹` are inverses, not finite local formulas merely by unfolding. The output is deliberately restricted to rows in `Y` and sources in `B`:

```lean
-- Proposed; C carries the geometric and parameter hypotheses described above.
theorem decBg_green_rows_transport (C : TwoTorusCut G G' a ν s s')
    {α : G.Ω 1 → ℂ} {α' : G'.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.B →
      α x = α' (C.bΩ x)) (hsmall : C.Adm α α')
    {f : G.Ω 1 → ℂ} {f' : G'.Ω 1 → ℂ}
    (hf : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.B → f x = f' (C.bΩ x)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ C.Y →
      (Gs G a ν α (extS G s) *ᵥ f) y =
        (Gs G' a ν α' (extS G' s') *ᵥ f') (C.bΩ y)
```

**OPEN (worker BG-2, 80–140 lines after BG-1).** `decBg_rows_transport` says that candidate multipliers corresponding on `B` have corresponding `Nmap` rows on `B`, and corresponding corrections on `Y`, under W593 read-set data agreement. The operative statement is `C.BgRow D α x = C.BgRow' D' α' (C.bΩ x)` for `x∈B` and `C.BgCorr D α y i = C.BgCorr' D' α' (C.bΩ y) i` for `y∈Y`; `BgRow` and `BgCorr` are **new abbreviations** for the exact `Nmap` and `dphi` expressions in `IsDecBg.fixed/field`, with no new mathematical operator. Its proof uses BG-1, `approxField_congr`, `residual_congr`, finite `dirichletOperator` rows, and `RowsBg.local_step_rows` as same-torus template.

```lean
theorem decBg_rows_transport (C : TwoTorusCut G G' a ν s s')
    (hD : C.RawAgree D D')
    {α : G.Ω 1 → ℂ} {α' : G'.Ω 1 → ℂ}
    (hα : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.B →
      α x = α' (C.bΩ x)) (hsmall : C.Adm α α') :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.B →
      C.BgRow D α x = C.BgRow' D' α' (C.bΩ x)) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ C.Y → ∀ i : Fin N,
      C.BgCorr D α y i = C.BgCorr' D' α' (C.bΩ y) i)
```

**OPEN (worker BG-3, 120–220 lines).** The gluing theorem must expose, rather than bury, its outside-row premise:

```lean
-- Proposed: glue the correction and multiplier on a row-closed Z, not only SY.
theorem decBg_glue_isDecBg (C : TwoTorusCut G G' a ν s s')
    (hrows : C.BgRowsTransport D D')
    (hout : C.BgOutsideRowsClosed D')
    (hsol : IsDecBg G a ν ρ s D φ α)
    (hsol' : IsDecBg G' a ν ρ s' D' φ' α') :
    IsDecBg G' a ν ρ s' D' (C.glueField φ φ') (C.glueMult α α')
```

**OPEN.** Here `BgOutsideRowsClosed` must be proved from a hat-box buffer and the exact `Nmap` row support; it is not a license to assume that a patched pair is a solution. If this fails for `Z=Y`, use the component Picard map and prove uniqueness there from the landed contraction. A gluing proof invokes whole-torus `i4b_exists_unique` only *after* `IsDecBg` and `Small` are established.

**OPEN (worker BG-4, 30–60 lines after BG-3).** With `hF₁,hF₁'` from the W587 pair, the final theorem has this value-level target, where `φ₀,φ₀'` are the respective `approxField`s:

```lean
theorem decBg_value_twoTorus (C : TwoTorusCut G G' a ν s s')
    (hD : C.RawAgree D D') (hpair : C.PairBg F₁ F₁') :
    (∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.B →
      (F₁' (s', rawOf D')).2 (C.bΩ x) = (F₁ (s, rawOf D)).2 x) ∧
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ C.Y → ∀ i : Fin N,
      (F₁' (s', rawOf D')).1 (C.bΩ y, i) - C.φ₀' (C.bΩ y) i =
      (F₁ (s, rawOf D)).1 (y, i) - C.φ₀ y i)
```

**OPEN (workers FL-1–FL-4, analogous sizes).** Replace `BgRow/BgCorr` by the landed `Dec2.DecFixed`/`dphi` expressions, `B` by `B_F=SYF`, and `RowsDep` by `RowsFl.DataAgreeRows` plus the collar condition. State `decSol_green_rows_transport` on `Y`, `decSol_rows_transport` on `B_F`, `decSol_glue_DecFixed` with an explicit `FlOutsideRowsClosed`, and `decSol_value_twoTorus`: equality of `(Sol p).2` on `B_F` and `(Sol p).1` on `Y` after `bHm`. `hSol` supplies the `c6'` smallness and field identity; `Dec2.i4a_exists_unique` supplies uniqueness *after* a genuine primed fixed point is built. The new mathematics is cut inverse conjugacy and outside-row closure; mapping W589/W593 sets and finite source rows is re-indexing.

```lean
theorem decSol_rows_transport (C : TwoTorusCut G G' a ν s s')
    (hp : C.FlAgree p p')
    {δα : Hm.Ω 1 → ℂ} {δα' : Hm'.Ω 1 → ℂ}
    (hα : ∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.BF →
      δα x = δα' (C.bHm x)) (hsmall : C.FlSmall δα δα') :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.BF →
      C.FlRow p δα x = C.FlRow' p' δα' (C.bHm x)) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ C.Y → ∀ i : Fin N,
      C.FlCorr p δα y i = C.FlCorr' p' δα' (C.bHm y) i)

theorem decSol_value_twoTorus (C : TwoTorusCut G G' a ν s s')
    (hp : C.FlAgree p p') (hpair : C.PairSol Sol Sol') :
    (∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.BF →
      (Sol' p').2 (C.bHm x) = (Sol p).2 x) ∧
    (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ K) ∈ C.Y → ∀ i : Fin N,
      (Sol' p').1 (C.bHm y, i) = (Sol p).1 (y, i))
```

**OPEN (fluctuation component uniqueness).** The `c6'` ball and `FlAgree` include the collar condition; the proof should conjugate the restricted `Smap` and iterate from zero, just as for background:

```lean
theorem decSol_component_unique (C : TwoTorusCut G G' a ν s s')
    (hp : C.FlAgree p p')
    {δα : Hm.Ω 1 → ℂ} {δα' : Hm'.Ω 1 → ℂ}
    (hfix : C.FlFixedOn p δα) (hfix' : C.FlFixedOn' p' δα')
    (hsmall : Small Hm δα (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)))
    (hsmall' : Small Hm' δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))) :
    ∀ x : Hm.Ω 1, (x : CTorus d L N₁ m₁ K) ∈ C.BF →
      δα x = δα' (C.bHm x)
```

## T5. Hardest step and fallback

**OPEN (hardest step).** Prove the two-torus component identity for `cubeG` and the cut resolvent `(1-Kcal)⁻¹` with no wraparound. W589 transports active sets and dependencies with margin `2ρ+7L^K`, and `compY_image` uses the stronger box margin involving `5L·cellSide` on both tori; those do not transport the inverse automatically. `cubeH` is a finite matrix on the full carrier, so one must show its inner block and its inverse agree under the box bijection. The same-torus two-sided block proof supplies the algebraic factorization, but the conjugation of finite entries and the potential on every site of each inner cube remain to be established.

**OPEN (fallback without nonlinear glue).** Define the Picard map on `α|B` (and `δα|B_F`) by extending a candidate arbitrarily within the small ball, evaluating the full `Smap`, then restricting. `local_step_rows`/`local_step_fpS_rows` show independence of that extension on the same torus. Prove the two component maps conjugate by `b` using BG-1/FL-1 and finite row transport, then compare their iterations from zero. The landed contraction proofs (`RowsBg.i4b_local_rows`, `RowsFl.i4a_local_fpS_rows`) already use this style; it avoids the outside-row condition required for a whole-torus glue. A second fallback is a termwise Neumann expansion of `Gstar(1-Kcal)⁻¹` under the `Kcal` bound used by `neumann_isUnit` (`DecoupledMain.lean:66–76`, `DecoupledGs.lean:32–66`); every walk stays in its cut component by the two-sided block identities. **OPEN:** no landed `Gs` walk-series identity was found; `Green/KF0WalkTorus.lean` concerns a different free kernel and cannot be cited for this cut inverse.

**PROVED (confidence in landed identities); OPEN (completion).** High confidence in the exact one-torus clauses, two-sided cut block proof and W589/W593 declarations inspected; moderate confidence in the proposed sizes and the feasibility of row-closed gluing. No two-torus `decBg_value_twoTorus` or `decSol_value_twoTorus` theorem is claimed proved.

## W819 status (2026-10-14)

BG-1..BG-4 above are already landed (the OPEN marks in T4 are stale): `Polymer/TwoTorusGreenRows.lean` `decBg_green_rows_transport` (BG-1; W589/W593 box map, cubeG via `inv_block_transport`); `Polymer/TwoTorusDecBg.lean` `decBg_rows_transport` (BG-2), `decBg_picard_rows_transport`, `decBg_component_unique`, `decBg_value_twoTorus`, `decBg_value_twoTorus_of_box` (BG-4); fluctuation analogues `decSol_*` in `TwoTorusDecSol.lean`, `decCov*` in `TwoTorusDecCov.lean` (W627, W632, W626).
BG-3 (whole-torus gluing, `decBg_glue_isDecBg`) is not needed: component uniqueness is proved by comparing restricted Picard iterations (`fixed_agree_of_step_transport`, `smap_fixed_iterates`), so no outside-row premise arises. No new Lean file was written.
