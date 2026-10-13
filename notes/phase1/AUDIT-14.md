# AUDIT-14 — batch 3 and two-torus statement audit

Read-only, statement-and-definition audit; no Lean build. Main `/home/scott/Balaban` HEAD: `8a1bdf723d2e424cfea29662e2c1f7b1b1847cab`. Branch references below denote `git show <branch>:<path>`; line numbers are those of the listed commits. Auxiliary W592 comparison uses `w592-phys-ag-exact` at `a8be66393d4fa6e25bdcb38c7f6a586f5e332c89`.

| Branch | Audited commit | File |
|---|---|---|
| W594 `w594-step-tower-g` | `fc4d347767d4e160d1981390787ad60af5bcd290` | `Balaban/Inhabited/StepTowerG.lean`, `StepTowerGBridge.lean` |
| W596 `w596-output-consts-k0` | `6876fbdad1f31264992901cff0b335283d02391d` | `Balaban/Inhabited/StepOutputConsts.lean` |
| W595 `w595-root-support-bridge` | `7f087f1ca0620d2b84ad56878870ba0eae365145` | `Balaban/Fluctuation/RootSupportBridge.lean` |
| W599 `w599-ren-physical-record` | `9a87b5a505ac2838cda83a94af9ed223ac1cd64d` | `Balaban/Inhabited/RenormPhysicalRecord.lean` |
| W600 `w600-obs-coeff-exact-sites` | `f5ae094515334882968a925d1ccba650014ba853` | `Balaban/Inhabited/ObsCoeffExactSites.lean` |
| W593 `w593-two-torus-data` | `beb413e06042ee53077a41a795e98c369566c634` | `Balaban/Polymer/TwoTorusData.lean` |
| W589 `w589-two-torus-thick-sets` | `85a3b0f4146e5441481f63ecc1f700becbdc6521` | `Balaban/Polymer/TwoTorusThickSets.lean` |

## Verdicts

1. **W595 — FAITHFUL, conditional root geometry and rate.** `RootSupportBridge.lean:37-57,63-80` gives nonemptiness, quotient closure, and nearest-neighbor connectivity exactly as `Balaban/Frozen/Geometry/IsPolymer.lean:24-30` requires. The quotient by `s=L^(m₁+1) L^K` is the cell coordinate: `Balaban/Fluctuation/CubeSystem.lean:36-48` makes `CubeB` an aligned base and `sitesOf` a union of its side-`s` boxes; `Balaban/Localization/PolymerGeometry.lean:59,119-136` supplies the quotient base and adjacency. `RootSupportBridge.lean:115-167` gives `B exp(λ)` times the root exponential from `λ≥c₁κ`; with `M=L^(m₁+1), j=K`, `((L^(m₁+1)*L^K:ℕ):ℝ)^d=((M:ℝ)*(L:ℝ)^j)^d` by casts. The prefactor still needs absorption in a root constant. `:182-187` proves admissibility exactly equivalent to `L∣N₁`. These are lemmas for `m₀=1`, `hN` and `IsPolyDom`, not an instantiated full root theorem.

2. **W599 — FAITHFUL as a conditional zero-class, fixed-source physical record; WEAKER THAN CLAIMED if called an instantiated physical step.** `RenormPhysicalRecord.lean:50-94` assumes analytic, exact-local, bounded, supported families `cE,cM` and value identities for every constant-`h` chart datum; in particular `hvalM` fixes the sum to the *physical* `M0C` at the supplied `g`. The record at `:113-142` uses the same `F`, rate `min (3/2 κdec) (min κ κM)`, energy budget `Bdet+B`, observable budget `BM`, and physical `E0locC` and `betaU^(-1/2) M0C` evaluated at `renThetaDatum` on the stated fibre. Only the old-class fields are zero. The construction at `:149-179` supplies the field record with those two family lemmas. The four consumers at `:250-309,320-325` receive the stated C1, C2, energy and observable budgets, including `BM + renCK*cK2*8e*εR`; no physical field is replaced by a determinant-only placeholder. The theorem does **not** construct either family. A zero observable family meets `hvalM` only when this physical `M0C` vanishes; a constant-family trick does not establish exact locality of the physical observable.

3. **W600 — FAITHFUL conditional exact-site implication; WEAKER THAN CLAIMED as a supplied physical-locality bridge.** `ObsCoeffExactSites.lean:57-76` assumes activity equality for every `Z`, every complex `u`, labels with `ysite⊆Z`, and both zero-source and actual-source parameter pairs. The two clauses match the two activity values used in `tiltActObs`; `:128-161` uses sharp `Ev` locality on `Y`, raw-site kernel locality, and mark locality, with no thick agreement premise. `:168-217` converts `physRestrict` equality to raw and source agreement. However W592 `Balaban/Fluctuation/ParamActivityPhysical.lean:409-427` states its `physical_labelActFamily_local_rawY` only for real `s∈[0,1]` and a cube-derived region, so it does not *literally* discharge W600's all-`Z`, all-complex-`u`, two-parameter `hAloc`. Its underlying `labelActFamily_local` at `:279-297` is all-complex and generic-`Z`, so an additional specialization/zero-source admissibility argument may close this; W600 itself supplies neither. Sharp `hd` is also an explicit premise.

4. **W594 — FAITHFUL bridge from the fixed tower; WEAKER THAN CLAIMED as a general-scale witness.** `StepTowerG.lean:35-83` generalizes the fixed numerical fields (`κ0≥aEnt+2`, `κdec`, `κ′`, entropy/log and rate inequalities), and `StepTowerGBridge.lean:46-102` maps each fixed field with `m₀=1`, transporting the same `FlCore` witness via `:27-43`. But the new `m₀` affects `κ_log` at `StepTowerG.lean:43-56` while `core` is fixed at `GpG/HmG ... 9 m₁ 1`, cover index `1`, and `νref L` (`:49-50`). Thus an inhabitant with `m₀>1` does not certify a core at that cover scale. `StepTowerGBridge.lean:125-127` proves inhabitance only at `(d,L,N)=(3,3,2)` via `toG`; no producer beyond this image is present.

5. **W596 — FAITHFUL arithmetic existence; WEAKER THAN CLAIMED if treated as a physical output theorem.** `StepOutputConsts.lean:193-209` quantifies `κroot`, `entropyLoss`, `κmin` *before* the existential `C`, then concludes `κmin≤C.kapp`, the exact `κdec` equation and `entropyLoss+c₁κroot≤3/2 C.kdec`. The floor is a conclusion, obtained by choosing `C.k0` at least the input threshold (`:200-204`), not an assumed inequality. This record has no `FlCore` or physical step witness linking it to W594.

6. **W593 — FAITHFUL two-torus datum and source transport.** `TwoTorusData.lean:48-65` defines raw/source agreement through `boxMap` and `pushSrc` by inverse map on the image, zero elsewhere. `:121-154` proves source agreement and exact support norm under the target margin and source-box premise, then the full-norm bound. `:164-171` uses literally `g (fun μ => ZMod.valMinAbs (z μ))`, the root pullback. `:194-226` gives equal step constants and raw agreement of the two `D'` for every `R` without a margin because both `unitBg` fields are constant on the full `lvTop` data sites; it says nothing about arbitrary flowed data.

7. **W589 — FAITHFUL under its two-torus margin.** `TwoTorusThickSets.lean:512-534` commutes `thickSet (levelGS j)` with `boxMap` when `Y` is in the radius-`ρ` box and *both* lengths exceed `2ρ+7L^K`. `:916-938` specializes to `lvTop=levelGS(k+1)` and `lvLow=stepG=levelGS k` on the same torus type with `K=k+1` and `k≥1` (`Balaban/Inhabited/LevelStepSetting.lean:50-55`). An application must establish the displayed margins; the statement does not derive them from a generic root box hypothesis.

No audited exact statement is **VACUOUS** or a **WRONG OBJECT** on the inspected definitions. The weaker verdicts identify missing instantiations or scale linkage, not false implications.

## Refutation ledger

| Attempt | Result and decisive anchor |
|---|---|
| Choose an `IsPolyDom` domain with a partial side-`s` cell because `ChosenOne` uses larger boxes. | **Refuted:** W595's set is `sitesOf T`, a union of aligned side-`s` cells (`CubeSystem.lean:36-48`; `RootSupportBridge.lean:43-57`), independently of the `ChosenOne` witness. |
| Find a different root decay denominator after casting. | **Refuted:** `cellSide_one_eq` and `rootRate_of_dExt` (`RootSupportBridge.lean:37-39,152-167`) give `s^d=(M L^K)^d`. |
| Produce W599's observable by zero coefficients despite nonzero physical `M0C`. | **Refuted:** `hvalM` (`RenormPhysicalRecord.lean:87-94`) forces the physical value; family existence remains open. |
| Derive W600 `hAloc` directly from W592's named raw-site lemma. | **Survives as a gap:** W592 `ParamActivityPhysical.lean:409-427` is restricted to real `[0,1]` and cube-derived regions, while W600 `ObsCoeffExactSites.lean:58-64` requires all complex `u` and all `Z`. The underlying W592 lemma `:279-297` suggests a route, but no bridge is in W600. |
| Claim W594's `m₀` changes the core cover index. | **Survives:** `StepTowerG.lean:43-50` leaves the core at literal `1`; `StepTowerGBridge.lean:56-70` populates only `m₀=1`. |
| Reverse W596's quantifier order or treat its floor as an assumption. | **Refuted:** `StepOutputConsts.lean:195-204` has the stated binder and existential order. |
| Require a margin for W593's constant base data, or use different torus types for W589's low level. | **Refuted:** `TwoTorusData.lean:210-226`; `TwoTorusThickSets.lean:928-938` and `LevelStepSetting.lean:50-55`. |

## Docstrings needing a caveat (at most five)

1. `StepTowerG.lean:32-34`: general numerical tower has an `m₀` parameter, but its `FlCore` is at cover index `1`; currently inhabited only at `3,3,2`.
2. `RenormPhysicalRecord.lean:40-49`: “physical” record is conditional on exact physical coefficient families, on the constant-`h` fibre and a fixed source `g`.
3. `ObsCoeffExactSites.lean:48-56`: exact locality follows from the all-complex, all-site activity premise; W592's named theorem has narrower quantifiers.
4. `TwoTorusData.lean:206-209`: margin-free `rawBoxAgree_step_D'` concerns constant zero-class base data, not arbitrary flowed data.
5. `TwoTorusThickSets.lean:915-938`: both step-level specializations require the displayed two-torus margins.
