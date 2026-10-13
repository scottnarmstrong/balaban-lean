# SCOPE — specializations outside the zero-class step

**PROVED. Snapshot and method.** Read-only inspection of `/home/scott/Balaban` at commit `9803c303bcf66cc996d7ae1d1d9db1c9101fbbda` (2026-10-13 UTC). I read both frozen root
declarations, checked the named Lean declarations by `rg`, and compared the roadmap and phase-1 notes. “General” below means the cited *interface or theorem* has variable `d,L,N`;
it does not assert an inhabited physical flow for every parameter.  
Names of the form `File.declaration` identify a source file and a declaration found there. Leaf names in the final table are proposed tasks, not existing Lean declarations.  
**REFUTED. Four equal gaps.** The four items in STEPSTATEMENT §4 have different logical status: general `d,N` and torus-coherent physical coefficients are open extensions;
root-uniform scalar constants are already present in many local theorems; the small-mass cutoff is the intended ordinary-step stopping condition, with separate final and `k_f=0`
branches still open.

## 1. Frozen target and dimensions

**PROVED. Root-F quantifiers.** `logPartition_multiscale` starts `(d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N)`, then `∃ δ>0`, then `∀ κ>0, ∀ c₉>0, ∃ L M : ℕ, 2 ≤ L ∧ 1 ≤ M ∧ ∃ β₀`, then `∀
β≥β₀, ∀ 0<ν≤1, ∀ ‖h‖=1`. Thus `L` is **chosen**, and may depend on `d,N,κ,c₉`; no theorem for every `L≥2` is required. A proof needs one admissible `L` for each such input, with
every lane using that same `L`.  
**PROVED. Root-C quantifiers.** `lowTemperature_correlations` starts the same `d,N` bounds, then chooses `β₀,c,c',ρ₀,ρ₁,q` before `β`; it quantifies all `0<ν≤1` and all unit `h`,
takes limits along tori with side divisible by `q^n`, and requires the stated one/two-point and `ν↓0` bounds. It does not follow from a three-dimensional spin-two step even if
Root-F eventually closes.  
**OPEN. Choosing `L`.** The source program often asks for a sufficiently large block scale; the frozen theorem allows that choice. Replacing the `3` in current numerical
certificates with an unspecified `L` is therefore not the exact task: prove or choose a single admissible `L≥L₀(d,N,κ,c₉)` and retain the needed inequalities. If a construction
works at `L=3` for every `d,N`, the root also permits that, but the present `L=3` proofs do not show it.

| Directory | Audited generality | Exact examples and boundary |
|---|---|---|
| `Background` | General interface | `BgHyp`, complex background domains and solver inputs carry `d,L,N`; their use at the step still needs an inhabited `FlCore` for the selected parameters. |
| `Green` | General except fixed examples | `finalMass_at_stop`, `finalMass_sqrt_decay`, `FinalCutFamily.finalOpCut_resOK` have variable `d,L`; `finalMass_instance` fixes `d=L=3,k=1` only for non-vacuity. These are matrix statements, not physical final-density identities. |
| `Localization` | General except level-pair instances | `DecEquivRot.decFixed_rot_iff`, `decBg_rot`, localization/decoupling carriers use variable `d,L,N`; `I5Inhabited` and `LevelPair` witnesses select the `3,3,2` geometry used by the tower. `detDeg_three` is a fixed numeric evaluation. |
| `Polymer` | General | `pe_blockTorus`, `pe_blockTorus_frozen` and `FrozenTorus` use variable dimension and block side; their premises require an actual physical activity and do not assert torus agreement of that activity. |
| `SmallField` | General interfaces; some examples specialized | Def-6 class carriers and source/energy terms are parameterized by `d,L,N`; `V2Energy.torusIndep_eTerms` is a synthetic family supported only on a whole torus at `N₁=1`, so it does not instantiate the physical step family. |
| `Fluctuation` | General abstract theorems, specialized physical scale | `StepComplexProp26.prop26C_step`, `StepComplexThm31.thm31bC_of_input_M0` and `DetRotation.rootTrace_rot` are variable-parameter conditional theorems. `StepRegWitness.exists_witness_params`, `SourceSliceScaled` and `hatStepK` routes use `d=L=3,N=2`; `DetCollarHullSymm.detCollarHull_cubeAct_genSymm` assumes `L=3`. |
| `Inhabited` | Specialized physical tower | `StepTowerRenSol`, `StepTower.scale`, `stepPieces_fromTower`, `detPackage_fromTower`, `markedRootAssembly_zero_fromTower` fix `d=L=3,N=2`; they vary `k,N₁,β,ν` only under their displayed premises. The rate precursor `tower_core_rates_at_least` keeps `N` variable but fixes `d=L=3`. |
| `LargeField` | General machinery, incomplete physical base/final use | Geometry, history, region and gas operators generally carry `d,L,N`; `KF0AllPlusGas.allPlus_gas` is an all-plus all-small sector, while its numeric instance fixes `d=3,N=2,s=64800`. A full large-field Root-F producer is open. |
| `Correlations` | General criteria, no root proof | `C1StarLimits.c1Star_remainder_limit_criterion` and its truncated analogue are parameterized convergence criteria; the physical summands/majorants and the Root-C conclusion are not landed. |
| `Flow` | General stopped-flow algebra | `StopIndex.kStop`, `massLe_of_lt_kStop`, `kStop_rootF_scale` use variable `d,L` and a `RunningHyp`; no theorem here constructs the whole physical running class. |

**PROVED. Numerical facts actually used by the `3,3,2` tower.** `StepRegWitness.exists_witness_params` chooses `m₁,δ,δ',T` with `cstarX 3 3≤3^m₁`, `fluctRadius 3 3 2>0`, `thm73C3 3
3 2>0` and small-domain inequalities. For general parameters this is a positivity/large-`m₁` and small-radius selection, not a finite computation at one point.  
**PROVED. Rate tuple.** `tower_core_rates`, `tower_core_rates_at_least`, `tower_core_rates_at_least_ren`, and `tower_core_rates_at_least_renSol` select `κ`, `t`, backgrounds, and
margins with the concrete entropy term `4·3·(2·3+1)^3`, `κ₀=aEnt 3 3+2`, and `κdec=100(κ₀+c1 3 3+10)`. A general theorem would replace these by the `d,L,N` expressions and choose
`κ,t` after the requested rate; it is a symbolic inequality and existence proof once general solver hypotheses are available.  
**PROVED. Finite numeric evaluations.** `c1_three`, `cG_three`, `aEnt_three_le`, `detDeg_three`, `detDeg_three_succ`, `collarB_three`, `log_three_lt_two` and
`fluctRadius_pos_three` certify fixed values or signs. Their direct analogues at a *chosen fixed* `(d,L,N)` are finite calculations; a uniform-in-`d,N` theorem should instead use
formulae, positivity, and logarithmic bounds, avoiding a separate giant numeral for each input.  
**PROVED. Determinant inequality.** `detDeg_three_rate` shows `(detDeg 3 3+1)^2·2/e^κ<1` for `κ≥57`; `log_detDeg_three_lt` makes its logarithmic cost `<57`. A general replacement
takes `κ>log 2+2log(detDeg d L+1)` with slack. This is a symbolic large-`κ` choice, not a new determinant identity or a fixed finite enumeration.  
**PROVED. Hull inequality.** `detHullThreshold`, `hullRate_ge_of_le`, `towerDetHullRate_ge`, `StepTower.kout_le_hullRate` use `c1 3 3=3375` and `collarB 3 3=60750`, hence the
factor `60751`. For general `d,L`, define a threshold using `collarB d L`, `c1 d L`, `detDeg d L`, then choose `κmin` above it. This is a symbolic threshold; proving finite
collar-fibre combinatorics in general is the separate geometric leaf.  
**OPEN. Geometry at other `L`.** `detCollarHull_cubeAct_genSymm` visibly assumes `L=3`; translations/permutations have more general lemmas, but reflection of the collar hull and
its grouped symmetry must be reproved for the chosen `L`. This is geometry, not arithmetic. The root only needs that chosen `L`, so a general reflection theorem is optional if one
can prove a selected-`L` instance.  
**OPEN. Unit field transport.** `LevelStepSetting.hatStepK` sets `h₀=unitVec hN2`, and `StepTower.scale` uses that step: the physical tower is at the constant coordinate unit
vector. `DecEquivRot.decFixed_rot_iff`, `decBg_rot` and `DetRotation.rootTrace_rot` provide general algebra; `exists_detExpansionLocC_rot_real` preserves the determinant chart for
real orthogonal rotations. One must still choose `Q∈O(N)` with `Qe₀=h`, transport the step measure, cutoff, source `g`, class/mark activities and the partition function under the
same `Q`, then identify the resulting coefficients. The determinant clauses alone do not yield Root-F's `∀h`.

## 2. Mass range and the stopping rule

**PROVED. Why the ordinary-step premise appears.** `LevelStepSetting.massLe_lv` converts `ν·3^{2(k+1)}≤1` to the `BgHyp.massLe` power form; `bgHyp_lv` and `opSetting_lv` consume it
to instantiate the background and lower operator. In the general flow, `ScaleUniform.sfBgMassAt_mul_sq` says the physical mass `sfBgMassAt L k (n k)` times `L^{2(k+1)}` is `L² n
k`; `massLe_iff` makes the condition exactly `n k≤L⁻²`.  
**PROVED. Stop before this fails.** `StopIndex.kStop` is the first index with `7/(8L²)<n k`. For every `k<kStop`, `massLe_of_lt_kStop` proves the *physical running mass* satisfies
the ordinary-step premise. `kStop_spec` supplies the lower stop-window bound, and `n_kStop_lt_one` supplies `n(kStop)<1` when `kStop>0`. No ordinary step is requested beyond this
index.  
**PROVED. Frozen scale interval.** `kStop_rootF_scale` proves exactly `L^{kStop}√ν≤L` and `1/2≤L^{kStop+1}√ν` under `RunningHyp` and `ν≤1`; this matches Root-F's existential `kf`
inequalities. It does not itself give the final coefficient family or the logarithm identity.  
**PROVED. Positive-stop matrix estimate.** `finalMass_at_stop` applies when `0<kStop` and proves unit resolvent, inverse and principal inverse-square-root decay with `finalGap d L`
and `finalRate d L`, uniformly in the torus. `FinalCutFamily.finalOpCut_resOK`, `finalOpCut_inverse_decay`, and `finalOpCut_sqrt_decay` treat cut scalar operators under the same
high-mass window.  
**OPEN. Positive-stop physical integral.** FINALMAP P1–P5 still require identification of the actual scale-`kStop` Hessian, physical cutoff coverage, complex chart/cut family,
localized all-small final expansion, and the nonempty large-field sectors. `finalMass_at_stop` is a matrix input, not that integral. The final output must also obey Root-F support,
source analyticity, decay and torus agreement.  
**OPEN. `kStop=0`.** `finalMass_at_stop` explicitly assumes `0<kStop`; it does not handle the bare one-scale case. Roland item 17 and LF-BASE-KF0 record an open extended base/final
theorem for `ν≳L⁻²`, including the heavy/minus-sheet gas and torus-exact localization. The all-plus all-small `allPlus_gas` and KF0 walk estimates cover only a sector.  
**REFUTED. “Mass interval” as an ordinary-step generalization.** Root-F's `0<ν≤1` does not demand a low-mass ordinary step at every scale. The correct route is ordinary steps for
`k<kStop`, a different last integral at positive stop, and a separate `kStop=0` base branch. The *handoff* from a running class to the tower step, including identification of its
mass parameter and constants, remains open; `massLe_of_lt_kStop` is not that handoff.

## 3. Torus coherence

**PROVED. Exact frozen clause.** After one family `T` has been chosen, Root-F requires the following equality for every pair of admissible sides. It does **not** assume `ℓ∣ℓ'` or
`N₁∣N₁'`:

```lean
∀ (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'],
  M * L ^ (kf + 1) ∣ ℓ → M * L ^ (kf + 1) ∣ ℓ' →
  ∀ (j : ℕ) (a : Fin d → ℤ) (A : Finset (Fin d → ℤ))
    (g : (Fin d → ℤ) → Fin N → ℂ),
    a ∈ A →
    (∀ y ∈ A, ∀ μ, 4 * |y μ| < (ℓ : ℤ) ∧ 4 * |y μ| < (ℓ' : ℤ)) →
    T ℓ j (fun μ => (a μ : ZMod ℓ))
      (A.image fun y μ => (y μ : ZMod ℓ))
      (fun z => g fun μ => ZMod.valMinAbs (n := ℓ) (z μ)) =
    T ℓ' j (fun μ => (a μ : ZMod ℓ'))
      (A.image fun y μ => (y μ : ZMod ℓ'))
      (fun z => g fun μ => ZMod.valMinAbs (n := ℓ') (z μ))
```

**PROVED. Uniform constants are weaker.** `StepTower.scale`, `stepPieces_fromTower`, `detPackage_fromTower` and `markedRootAssembly_zero_fromTower` quantify `N₁` after their tower
constants. This establishes bounds uniform in `N₁` in their stated range; each conclusion may still choose different coefficients on different tori. The frozen clause demands the
*same value* on every common nonwinding support for compatible source lifts.  
**PROVED. Landed transport ingredients.** `pe_blockTorus` and `pe_blockTorus_frozen` are torus-generic polymer expansions conditional on an activity; `Polymer/FrozenTorus` aligns
their polymer carrier with the frozen `IsPolymer`. `kf0Adj_pow_torus_eq` and `kf0CR_torus_eq` prove exact agreement of finite walks and truncated kernels when their radius fits
both tori; `abs_kf0C_sub_le` bounds the residual difference. `aCoef_liftTF_eq_v1T_of_nonwinding` is a conditional large-field lift theorem. None states coherence of the physical
step output.  
**REFUTED. Synthetic example as physical coherence.** `V2Energy.torusIndep_eTerms` proves `TorusIndep` for a constructed family with a nonzero whole-torus term only at `N₁=1`; it
tests the interface but is not the `e⁺_z` of STEPSTATEMENT. No landed theorem compares `hatStepK` at two torus sizes. The closest current facts are `hatStepK_betaU` and
`hatStepK_one_nine` (same torus/parameter identities), `kf0CR_torus_eq` (bare finite-range kernel), and the conditional `TorusIndep` example.  
**OPEN. Exact step statement needed.** For two admissible `N₁,N₁'` and a polymer `X` whose lifts lie inside both quarter-boxes, the marked and determinant coefficient functions
after lifting the same source must agree: `e⁺_{z,N₁}(X;g)=e⁺_{z',N₁'}(X';g')`. Prove the analogous equality for observable coefficients, then for the assembled Root-F `T`. The
condition is nonwinding support plus corresponding roots and sources; divisibility between the two torus sizes is unnecessary.  
**OPEN. One localization-engine insertion.** Establish equality of finite-range Green/covariance truncations and cut resolvents under the two lifts, then show the local analytic
expansion is a deterministic function of those kernels and the identical local data. The first insertion belongs at the finite-range truncation/cut-kernel layer of `Localization`;
it must feed determinant and marked/source coefficient constructions before `Polymer/FrozenTorus` sums them. Exponential tail bounds alone cannot yield exact equality.

## 4. Uniform roots and cost table

**PROVED. Root-independent local constants.** `detPackage_fromTower` chooses `E z` for every root with one `towerDetRate T.κ` and `towerDetConst T.κ`; its hull bound, root anchor,
lattice covariance and rotation clauses are uniform in `z`. `markedRootAssembly_zero_fromTower` likewise quantifies roots with shared tower constants, but its conclusion is a
rooted analytic/count family, not a completed physical `E1MarksC` or lattice-covariant energy output.  
**OPEN. Covariance and restriction.** A full `e⁺_z` family needs `e⁺_{σz}(σX;σD)=e⁺_z(X;D)` for generated lattice symmetries, and spin rotation transport for every unit `h`; marks
and source activities have no matching all-root covariance theorem. Restricting the same coefficients to a large-field region requires support and boundary agreement of the
*physical* generator; that is generator-dependent and outside this scope audit.

| Specialization | Frozen-root requirement | Landed generality | Smallest leaves; kind and size |
|---|---|---|---|
| `d=L=3,N=2` tower | Root-F: `∀d≥3,N≥2; ∃L≥2` after `κ,c₉` | General abstract BG/Green/Polymer/Fluctuation interfaces; physical `StepTowerRenSol` at `3,3,2` | `witness_params_general` (M, strong), `tower_rates_general` (M, strong), `det_rate_hull_general` (M, Sonnet): numeric re-instantiation with symbolic constants; `collar_symm_chosenL` (M, strong): new geometry. |
| Constant coordinate `h₀` | Root-F: `∀h, ‖h‖=1`; Root-C same | `unitVec` tower; general `DecEquivRot` and determinant rotation | `orthogonal_to_unitVec` (S, Sonnet); `rotate_physical_step` (L, strong): new measure/class/mark/source covariance, then Root-F transport. |
| Ordinary mass cutoff | Root-F: `∀0<ν≤1` and a stopped `kf` | `massLe_of_lt_kStop` general in `d,L`; `finalMass_at_stop` for positive stop | `running_mass_to_step` (M, strong): new physical handoff; `FINALMAP` P1–P5 (L, strong): new final mathematics; `KF0_full_base` (L, strong): new `kf=0` branch. No high-mass ordinary-step leaf. |
| Torus-uniform constants | Root-F picks one `T` before `∀ℓ` | Tower thresholds before `N₁`; conditional polymer kernels | `step_uniform_wrapper` (S, Sonnet): pure quantifier assembly after physical terms exist. |
| Exact torus coefficient equality | Root-F quarter-box equation above, any admissible `ℓ,ℓ'` | KF0 finite walks and conditional torus lifts; no `hatStepK` comparison or physical `e⁺` equality | `local_kernel_lift` (M, strong), `step_coeff_lift` (L, strong), `root_coeff_lift` (M, strong): new exact-locality work. |
| Every root and subregion | Root-F `∀x,X` locality/covariance and final LF sectors | Determinant `∀z` and symmetry; marked rooted family lacks full covariance | `mark_activity_symm` (M, strong): new physical covariance; `large_region_restrict` (L, strong): generator-dependent. |

**OPEN. Closeout.** The frozen roots remain draft proofs. The stopping algebra removes the false demand for ordinary steps beyond their mass range, while physical positive-stop and
bare-base integration remain substantive open work. General `d,N`, arbitrary unit `h`, and exact torus-coherent physical coefficients require their own proofs even if the
specialized zero-class step closes.
