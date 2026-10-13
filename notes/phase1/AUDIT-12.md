# AUDIT-12 — step fibre, raw-Y locality, and two-torus geometry

Read-only statement/definition audit, 2026-10-13. No Lean build or source edits. Verdicts assess the stated scope, not the full paper's later H7 output.

## Frozen sources

`/home/scott/Balaban` main HEAD `4f45447a64870d794b0a7a586b55709e37b51dd1`; W571 branch `w571-step-identity-fibre` at `f57058f69b476a4af976e4fbd6f7bdd470cb5806`. W583's raw-Y declarations are on main (branch `w583-fnu-expansion-direct-raw-y` at `44ac5e7728c0b6f317d791cdd96a325c238f4a28`); W578 geometry is on main, introduced at `5185b739c883a72baf14c95c83891ba8321d36ed`. Paths below are relative to `/home/scott/Balaban`; W571 paths refer to the branch, all others to main.

SHA-256 manifest (full hashes, first three from `git show`):

| File | SHA-256 |
|---|---|
| `Balaban/Inhabited/StepIdentityFibre.lean` | `7ea54c7dab275c0d133abc1c393daf5906549f8a9c03e084276639402f3d234a` |
| `Balaban/Inhabited/StepIdentityFibreObs.lean` | `a5f30987c5290e9010afecb8fcf99a8eb31f4640b4a5e5bb3ca39fbdafba694f` |
| `Balaban/Inhabited/StepIdentityFibreFamilies.lean` | `89a463701c7b88a0228ce0f0187878c84b5bca08680622274c0ed32d7f1fb7be` |
| `Balaban/Fluctuation/SharpVF.lean` | `ea0cb63b85e5d70cba6839358c28252b9363e6c0016a595b0393708edd5866dc` |
| `Balaban/Fluctuation/SharpENu.lean` | `abdaccca17374b50b0fff4d830f6e4b4a7217cba193fbe4aaab9c4f4a6c46b3e` |
| `Balaban/Fluctuation/SharpAssemblyScaled.lean` | `59e0582ba91037f9991ff5eb91f8e9050cd0b2d2c150b50ec1083e9b1c258206` |
| `Balaban/Fluctuation/PhysicalVRawY.lean` | `1c17b9249f5c2765ed29158c6ba679321158d0f6422b18cc5ff86b0df36712e1` |
| `Balaban/Polymer/TwoTorusStepGeometry.lean` | `721e6e51eba86d6a92791989d9b35af01d59f0e2be7913bc772c1b47b90ca5bf` |
| `notes/phase1/TSTEPID.md` | `773cd1101426ce6270e10fc6b55d991990588270001dc45fbdb5e1a1f3f9adab` |
| `notes/phase1/STEPSTATEMENT3.md` | `eddbc381a023c3ce935e6819566e82587c5068fb6d8ce17a7500cfde9c3e33c5` |
| `Balaban/Inhabited/StepTower.lean` | `015b9f8321e12a9bd8ce016439ca178ba42b8edc8b55315ee2176e985e25f6ef` |
| `Balaban/Inhabited/StepTowerScale.lean` | `6124b14f4687e3d7c4454a55f0020994017fcbd9847293801e26d91b2ecfebb4` |
| `Balaban/Inhabited/LevelStepSetting.lean` | `5083a37a1998b551440be1501ca98d16c33d0fda2cfc0872eae835c94aa0a174` |
| `Balaban/Inhabited/DAPhysicalCutoff.lean` | `d74e6c2d2ea73ae6c5d3ce42eec707b403aae05d2347696f194910ad2a55fb6d` |
| `Balaban/Fluctuation/StepComplexOut.lean` | `df16d2de12afbbf7594f28e103b48a1df7171dc46e306a0486cc98223925463c` |
| `Balaban/Fluctuation/StepComplexProp26Agree.lean` | `a522f1718335a75fd248479c079aeb90f8c448c217915102ba4cedcc61e175ca` |
| `Balaban/Fluctuation/StepComplexSource.lean` | `6542aad34ec84347a9c1e23ad87d3d2393bb7aab402bfa83e780a0edc4a85ef1` |
| `Balaban/Fluctuation/RootActiveSize.lean` | `31fbb89533c5fa48097e154ae068dce3d605d384a0aedfe7e3c3fde25b88d3bb` |
| `Balaban/Fluctuation/SharpAE.lean` | `758c441198ce0358434d78f896947f6b249620cd589b09c9c09a51fda80b47e8` |
| `Balaban/Fluctuation/SharpEngine.lean` | `de6b92e4ddf9bbc96c4e635f672e3f306a562c8a45406932ef6d1cee97528ba2` |
| `Balaban/Fluctuation/SharpAssemblyEta.lean` | `e611710236490e30d304add2ffd57896e81aa382d8e8c597d907881656eeaa99` |
| `Balaban/Localization/I5Expansion.lean` | `b07394309f7c0c72f77486c597a7db3141a6ce68d9a9f55fabf3df72159927a9` |

## Verdicts and evidence

**L1 — FAITHFUL to TSTEPID T2, within its explicit fibre/zero-class scope.** The headline binds `β₀, CE, CF` before all scales, then `q` and `D : StepScaleData` before `F₁, Sol, Lab₀, A₀, e0, Labo, Ao, mObs`, and only then `∀ D' … ∀ g` (`StepIdentityFibreFamilies.lean:87-125,346-367`). This matches `TSTEPID.md:23-30`. Families may depend on the *scale datum* `D` and fixed radius `q`, exactly as the target allows. The nested root/site existentials (`StepIdentityFibreFamilies.lean:135-155,255-266`) are chosen before `D',g` in the proof (`:379-388`; `StepIdentityFibreObs.lean:159-176`); no hidden post-fibre coefficient choice remains. The headline proof rewrites the local step identity with the observable pair and energy value for the same selected families (`StepIdentityFibreFamilies.lean:388-391`).

**L1 exponent — FAITHFUL.** The displayed exponent contains `−β AnewC − Eppp·nU + FcompAtC(g)`, the root energy family at `(rawOf D',0)`, and `g` times the site family at `(rawOf D',g)` (`StepIdentityFibreFamilies.lean:350-367`), precisely the target in `TSTEPID.md:25-29`. `Eppp` is retained, as required by `TSTEPID.md:21`; the old energy is proved zero, rather than silently dropped (`StepIdentityFibre.lean:255-269`). `E0C := halfLogDetCC + E1C C` has no source argument (`StepComplexOut.lean:133-142`); the energy family's zero-source value is an asserted fibre theorem (`StepIdentityFibreFamilies.lean:247-252`), not a free assumption. The observable theorem states `M0C = β_U^(1/2) Σ mObs` and its paired cancellation (`StepIdentityFibreObs.lean:145-157`); the proof uses `β_U>0` and `rpow_neg_half_mul_sum_pair` (`:170-201`; `StepIdentityFibre.lean:315-325`).

**L1 non-vacuity — FAITHFUL, with a quantifier distinction.** `exists_stepTower κmin` works for every lower bound (`StepTower.lean:81-82`), so one may take `κmin ≥ stepHullMin`. `StepTower.scale` inhabits `StepScaleData` beyond its own threshold for positive `p₁≤pLog` (`StepTowerScale.lean:112-146`), and `pLog_pos` supplies such a `p₁` when `β3^k>1` (`DAPhysicalCutoff.lean:29-41`). Take, for example, `k=1`, `N₁=6`, positive sufficiently small `ν`, and `β` above both thresholds. The scale record's `xi` inhabits the base chart (`StepTowerScale.lean:91-105,131-142`), while `hatStepK` defines its base `D'` with constant `h₀` (`LevelStepSetting.lean:73-83`); hence the later fibre universal has a member. `g=0` lies in every `q>0` source ball. The convenience `scale_instance` has `ν=0` (`StepTowerScale.lean:156-164`) and therefore is *not itself* an instance of the headline's `0<ν`; use `scale` instead.

**L1 scope — WEAKER THAN CLAIMED if read as the full paper step output.** `TstepC` is the complex fluctuation integral with `β_U^{-N|U|/2} det(covSqrtC)`, `chiFl`, `tKernelC`, and `rhoExpC` (`StepComplexOut.lean:116-129`); under the separate real-slice hypotheses, `TstepC_eq` identifies it with the landed real `Tstep` (`StepComplexProp26Agree.lean:199-216`). The theorem asserts equality of exponentials, not a chosen logarithm (`StepIdentityFibreFamilies.lean:74-82`), and only for the zero class, constant-`h₀` fibre, `q≤1`, with thickened raw-data locality (`:84-86,342-350`). `STEPSTATEMENT3.md:5,12-19` records further H7, symmetry, paper-rate and full-renormalization obligations. The headline docstring states these limitations; this is not a defect in its stated T2 target.

**L1 activity/conditional leaves — FAITHFUL.** `stepActivityBoundC_fibre_fromTower` first gets a single joint `Aseg`, transports `W1/W2` to `WoneC/WtwoC` a.e. (`StepIdentityFibre.lean:117-144`), then constructs `B` with that `Aseg`, block split, labels and numeric fields; every `HEq` is `HEq.rfl` (`:163-171`). Thus the heterogeneous equalities witness actual definitional identity and are useful to downstream consumers; nonvanishing applies `stepNonvanishingC_of_activityBoundC B` (`:178-197`; `StepComplexNonvanish.lean:124-142`). `stepIdentity_zeroClass_fibre_local_fromTower` is the local-sum identity (`StepIdentityFibre.lean:282-311`). `stepIdentity_zeroClass_fibre_of_values_fromTower` is a conditional rewrite given equality to arbitrary `E,M`, not a source of coefficient families (`:337-370`); its hypotheses are satisfiable with the actual values.

**L2 — FAITHFUL for expansion-level exact locality.** V, F, ν and scaled V each state one `Ev`, a sum over `polymerDomains` (ν uses `polyDom`), and the requested `agreeOn Y` plus unit-point hat agreement on the chart (`SharpVF.lean:119-138,304-322`; `SharpENu.lean:580-601`; `SharpAssemblyScaled.lean:97-116`). Their proofs obtain a single `Ev` from `i5_functional_hat_rawY_of_fan` (`SharpVF.lean:153-164,328-339`; `SharpENu.lean:617-627`; `SharpAssemblyScaled.lean:131-144`). The thick corollaries reuse that same `Ev` via `agreeOn_mono` (`SharpVF.lean:212-214,382-384`; `SharpENu.lean:682-686`; `SharpAssemblyScaled.lean:191-193`); no second witness is selected in these chains.

**L2 off-domain and source — FAITHFUL with a precise caveat.** The theorem statements quantify locality, bounds and analyticity over *all* `Y`, but their expansion sums only use the stated domain family. In fact, the chosen `Ev` is `evTerm`, a sum over connected families whose `Ysites` equals `Y` (`SharpAE.lean:154-161`; `I5Expansion.lean:43-68`); if `Y` is absent from `polymerDomains`, that index is empty and `Ev Y=0`. This is a consequence of the definitions, not a separate support clause in the four theorem statements. F's expanded `siteFun` has source amplitude `1` (`SharpVF.lean:303-310,328-335`); assembly inserts `g(y,i)` as `LocIntDm.wsum`'s amplitude and imposes source agreement on `Y`, using `y∈Y` (`SharpAssemblyEta.lean:127-142`). The raw-Y F clause alone does not assert locality of a source-weighted sum.

**L3 — FAITHFUL for box-restricted two-torus transport.** The header and each cited theorem require `X⊆InBox d r` and both inequalities `2r+L·cellSide < side`, together with `L^m₀∣N₁`, `L^m₀∣N₁'` and `j≤K`; they never assume `N₁∣N₁'` (`TwoTorusStepGeometry.lean:21-35,377-385,427-433,479-490`). For `treeLenCovOne`, a competitor has `W⊆X` (`:391-405`); for `dcovModE`, admissibility gives the same containment (`:439-463`). Hence every competitor lies inside the box, and inverse transport gives the reverse infimum inclusion (`:419-425,470-473`). The `SiteConnected` branch is reflected by paths staying in `X` (`:318-327,350-356,487-492`). This establishes equality of the *same* competitor class, including the `⊤` case for `dOmega`.

**L3 finite `dExt` — FAITHFUL, explicitly conditional.** `dExt_image_cubeMap` requires `dOmega … (sitesOf T) ≠ ⊤` (`TwoTorusStepGeometry.lean:609-619`); when it is `⊤`, both values are the torus-dependent respective `Mbig`, so equality is not asserted (`:621-629`). The hypothesis is automatic if `sitesOf T` is `IsPolyDom`, by `dOmega_ne_top_of_isPolyDom` (`RootActiveSize.lean:109-116`). It can fail inside the box, for example for `T=∅` (`RootActiveSize.lean:147`).

## Refutation ledger

| Attempt | Evidence / result |
|---|---|
| Hide a post-`D',g` energy or observable witness | Refuted by `choose` before `intro D' … g` in `StepIdentityFibreFamilies.lean:379-390` and `StepIdentityFibreObs.lean:175-201`. |
| Delete `Eppp`, lose `FcompAtC`, or retain an extra `β_U` factor | Refuted by `StepIdentityFibreFamilies.lean:353-366`, `StepIdentityFibre.lean:315-325`, `StepIdentityFibreObs.lean:145-157`. |
| Make the headline vacuous using `StepScaleData`, constant `h₀`, or the source ball | Refuted by `StepTower.lean:81-82`, `StepTowerScale.lean:112-146`, `LevelStepSetting.lean:73-83`, and `g=0`; note `scale_instance` itself uses inadmissible `ν=0`. |
| Smuggle a type mismatch through `HEq` | Refuted by direct construction and `HEq.rfl` in `StepIdentityFibre.lean:163-171`. |
| Use a second thick-corollary witness or an unconstrained off-domain term in the sum | Refuted by `SharpVF.lean:212-214,382-384`, `SharpENu.lean:682-686`, `SharpAssemblyScaled.lean:191-193`, and `I5Expansion.lean:43-68`. |
| Let a cover/tree competitor leave the box; claim unqualified `dExt` equality | Refuted by `TwoTorusStepGeometry.lean:391-405,439-463,609-629`; `dExt` does need finiteness. |

## Four docstring edits suggested, without source changes

1. `StepIdentityFibreFamilies.lean:67-72`: “The energy coefficient is evaluated at zero source because `E0C` is source-independent; the fibre value theorem identifies its sum there. The observable coefficient is evaluated at the actual source `g`.”
2. `SharpVF.lean:93-96`: “The thick corollary uses the same `Ev` selected here. The sum includes only polymer domains; the raw-Y locality clause is stated for every `Y` on the chart.”
3. `SharpENu.lean:552-555`: “The thick corollary uses the same `Ev` selected here. The raw-Y clause concerns the block expansion, before source-weighted assembly.”
4. `TwoTorusStepGeometry.lean:30-35`: “These equalities concern sets inside the centred box on both tori. Equality of `dExt` additionally requires finite `dOmega`; at `⊤`, its value is the respective torus-dependent `Mbig`.”

**Closeout.** No wrong-object or vacuous headline found. The only weaker-than-full-paper conclusion is the expressly scoped fibre exponential identity; no build was run, so this report does not certify elaboration of the unlanded W571 branch.
