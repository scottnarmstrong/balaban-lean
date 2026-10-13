# STOWERG2 — amended general tower

**PROVED (snapshot).** Read-only source inspection of `/home/scott/Balaban` at commit `4f45447a64870d794b0a7a586b55709e37b51dd1`; no build or elaboration. I read `ROOTBOUND.md` in full. The author's approved baseline is `notes/phase1/STOWERG.md` and mechanism B′ of `GENLAYER.md`.

**PROVED (rate obstruction).** The frozen root chooses its requested `κ` before `L,M,β₀`. `ROOTBOUND.md` shows the landed output has rate `3κdec/2` in `sizeJ`, while `SizeModG1.G1_card` costs `c1 d L` plus an additive constant. Pinned `κ0=aEnt d L+2` and `κdec=100(κ0+c1 d L+10)` therefore cannot certify arbitrary root rate, even by increasing interpolation `κ`, `m₁`, or `L`.

## T1. Equality uses and large-rate audit

**PROVED.** Direct rewrites of `T.κ0_eq` occur only at `DetPackageFromTower.lean:161` and `RenormDetFibreTower.lean:150`: each turns `3κdec/2` into the *fixed* numeral expression inside `detHullThreshold` or `renDetFibreMin`. Those theorems remain fixed `3,3,2` wrappers with the old `StepTower`; a general theorem needs a threshold depending on the chosen `κ0,κdec` (or the output ledger's hull margin). `StepTower.lean:147` uses the equality only to prove `κ0_two : aEnt 3 3+2≤κ0`, which becomes direct projection `κ0_ge`.

**PROVED.** `StepTower.lean:129`, `StepTowerRen.lean:96`, `StepTowerRenSol.lean:89`, and `StepTowerTheta.lean:149` construct fixed records with `κ0_eq := rfl`; these constructors stay fixed. `StepOutputConsts.lean:105–185` chooses the pinned value internally and its fixed `:187–194` corollary preserves that header; the *general* producer must instead accept a selectable `κ0`. These are equality choices, not a general upper bound on `κ0`.

**PROVED.** The other cited tower uses require lower bounds or symbolic values: `StepOutputPhysical.lean:66` and `MarksNumericsFromTower.lean:43–47` use `κ0_two`; `ZeroSourceActivityCommon.lean:247,344–383`, `CommonWitnessJoint.lean:234`, `ObsOnCommonWitness.lean:296`, and `E1CoeffFamily.lean:408` pass the same lower bound to root-union/zero-source arguments. `K0 3 3 T.κ0` in `StepOutputPhysical.lean:61–68,117` and `ObsCoeffLocal.lean:264–351` is evaluated at the actual `κ0`, with no substitution by `aEnt+2`.

**PROVED.** `ObsFamilyJoint.lean:465–471` proves `obsFamilyRate_eq_tower` from `κ'_eq`, `κdec_lower`, and `κ0_nonneg`; it never uses `κ0_eq`. `StepOutputPhysical.lean:69–80`, `Thm31bFromTower.lean:45–52`, and `MarksNumericsFromTower.lean:57–92` similarly use the preserved rate equality/lower fields. Thus their algebra survives variable `κ0` when all three rates are chosen together.

**PROVED.** No inspected tower field requires `κ0≤constant` or `κdec≤constant`. Occurrences of `κdec≤κout=3κdec/2` and `3κdec/2≤2κdec` use positivity; larger `κdec` helps. The determinant hull target `3κdec/2` grows, however, so a *fixed* `κmin` threshold does not suffice for arbitrary enlarged `κ0`; this is why `detHullThreshold`, `stepHullMin`, and `renDetFibreMin` remain fixed-wrapper certificates. The new producer must choose determinant interpolation `κ` after `κ0,κdec`.

**PROVED / OPEN.** `stepTheta` (`StepOutputConsts.lean:35–37`), `K0`, and `CPE` (`StepNonvanishCluster.lean:43–47,101–106`; `ParamCarrierLocal.lean:152–163`) may become very large/small at large rates, but are finite, and `StepOutputConsts.theta_pos` plus `exists_beta0_stepOutput` chooses a later `β₀` for each fixed ledger. **OPEN:** a uniform root-level `β₀` through every scale, inherited observable and final contribution has not been proved by that one-step lemma.

**REFUTED.** A bare arbitrary `T : StepTowerG …` with only `det_rate : κ'≤detRateG` already has the determinant *hull* rate `3κdec/2`. Dividing a merely `κ'`-sized determinant rate by `1+collarB` loses much more than this record certifies. A general hull theorem must take the ledger margin or a dynamic threshold as an additional premise; the fixed wrapper obtains it from its pinned-rate threshold.

## T2. Paste-ready proposed declaration

**PROVED (bounds).** `LevelPairGeneral.lean:140–185`, `TowerCoreRatesGeneral.lean:43–79`, and `LevelStepSettingGeneral.lean:75–102` use `d,L≥3`, and the general step uses `N≥2`. The centred determinant collar requires odd `L` only when it is attached; it is not a base-tower field. `νref=L⁻⁴` satisfies the reference pair's `ν L⁴≤1` at `N₁=9,k=1`.

**OPEN (exact Lean proposal, unelaborated by instruction).** This is the complete new module text. `κout_le` is deliberately a conclusion of the producer below, not a field: a field depending on arbitrary requested `κroot` would make `StepTower.toG` impossible for a fixed-rate old tower.

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelPairGeneral
public import Balaban.Fluctuation.StepRegWitnessGeneral
public import Balaban.Fluctuation.DetCauchyGraph

/-! # The general numerical tower for one witness step -/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 LevelStep

noncomputable def νref (L : ℕ) : ℝ := 1 / (L : ℝ) ^ 4

structure StepTowerG (d L N : ℕ) [NeZero L] (κmin : ℝ) where
  hd : 3 ≤ d
  hL : 3 ≤ L
  hN : 2 ≤ N
  (κ0 κdec κ' : ℝ)
  κ0_ge : aEnt d L + 2 ≤ κ0
  κdec_eq : κdec = 100 * (κ0 + c1 d L + 10)
  κ'_eq : κ' = 3 / 2 * κdec + κ0 + 1
  m₁ : ℕ
  (c BG κ t c₂ BG₂ δc δ δ' : ℝ)
  m₁_four : 4 ≤ m₁
  t_pos : 0 < t
  core : Nonempty (FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1)
    1 (νref L) c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t)
  κ0_nonneg : 0 ≤ κ0
  κdec_lower : 3 * κ0 + 3 ≤ κdec
  κ_lower : 4 * (d : ℝ) * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ
  κ_one : 1 ≤ (κ / 2 - 1) / 2
  κ_log : Real.log (((((2 * L + 1) ^ d : ℕ) : ℝ)) *
    ((((L ^ 1) ^ d : ℕ) : ℝ))) ≤ (κ / 2 - 1) / 2
  c7_cap : c7 d L N BG κ ≤ thm73C3 d L N
  large_block : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  dom_margin : decDomMargin d L N BG κ (xiC1 d * t) < δc
  coer_margin : K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2
  δc_small : δc ^ 2 * smallConstX d L κ ≤ 1 / 4
  t_cap : 2 * t ≤ deltaStar d L N
  bg0_cap : cK2 d L N * (2 * t) < bgC0 d L N / 2
  cK2_cap : cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  cK2'_cap : cK2' d L N (famConst d L BG₂ κ) * t ≤
    c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  bg1_cap : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * t))) + 5 * (2 * t) ≤ bgC1 d L N
  κ0_ent : aEnt d L + 1 ≤ κ0
  rate_rel : 0 + 3 * κ0 + c1 d L + 3 / 2 ≤ 2 * κdec - 1
  fam_nonneg : 0 ≤ famConst d L BG₂ κ
  κmin_le : κmin ≤ κ
  δ_pos : 0 < δ
  δ_small : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4
  δ'_pos : 0 < δ'
  δ'_cap : δ' ≤ thm73C3 d L N / 2
  δ'_step : bgK1 d L N * δ' ≤ δ / 4
  δ'_coer : bgK1 d L N * δ' ≤ coerciveConst d / 4
  block_base : cstarX d L ≤ (L : ℝ) ^ m₁
  xi_small : xiC1 d * t ≤ 1
  rho_nonneg : 0 ≤ rho4 d L N BG κ
  det_z : ((detDeg d L + 1 : ℕ) : ℝ) ^ 2 * (2 / Real.exp κ) < 1
  det_rate : κ' ≤ (κ - Real.log 2 -
    2 * Real.log ((detDeg d L + 1 : ℕ) : ℝ)) / (2 * (d : ℝ) * (L : ℝ))

end Balaban.Inhabited
```

**PROVED (field comparison).** The following rows cover the 49 old fields in order; `→` gives the general field type. `[N]` marks a nonmechanical change. Scalar names retain type `ℝ`; only their surrounding record parameters change.

| Old `StepTower` field/type (`StepTower.lean:34–80`) | General `StepTowerG` field/type |
| --- | --- |
| `κ0 : ℝ` | `κ0 : ℝ` |
| `κdec : ℝ` | `κdec : ℝ` |
| `κ' : ℝ` | `κ' : ℝ` |
| `κ0_eq : κ0=aEnt 3 3+2` | `[N] κ0_ge : aEnt d L+2≤κ0` |
| `κdec_eq : κdec=100(κ0+c1 3 3+10)` | `κdec=100(κ0+c1 d L+10)` |
| `κ'_eq : κ'=3κdec/2+κ0+1` | same |
| `m₁ : ℕ` | same |
| `c : ℝ` | same |
| `BG : ℝ` | same |
| `κ : ℝ` | same |
| `t : ℝ` | same |
| `c₂ : ℝ` | same |
| `BG₂ : ℝ` | same |
| `δc : ℝ` | same |
| `δ : ℝ` | same |
| `δ' : ℝ` | same |
| `m₁_four : 4≤m₁` | same |
| `t_pos : 0<t` | same |
| `core : Nonempty (FlCore 2 (Gp m₁ (rhoSep m₁)) (Hm m₁ (rhoSep m₁)) 1 nuW c BG κ t (levelKc 3 3) (Cchi 3 3) c₂ BG₂ t)` | `[N] FlCore N (GpG d L 9 m₁ 1) (HmG d L 9 m₁ 1) 1 (νref L) c BG κ t (levelKc d L) (Cchi d L) c₂ BG₂ t` |
| `κ0_nonneg : 0≤κ0` | same |
| `κdec_lower : 3κ0+3≤κdec` | same |
| `κ_lower : 4·3·7³ κdec≤κ` | `4d(2L+1)^d κdec≤κ` |
| `κ_one : 1≤(κ/2−1)/2` | same |
| `κ_log : log(7³·3³)≤(κ/2−1)/2` | `log((2L+1)^d·(L^1)^d)≤(κ/2−1)/2` |
| `c7_cap : c7 3 3 2 BG κ≤thm73C3 3 3 2` | `c7 d L N BG κ≤thm73C3 d L N` |
| `large_block : cstarX 3 3·exp(N0 3 3 κ)≤3^m₁` | `cstarX d L·exp(N0 d L κ)≤L^m₁` |
| `dom_margin : decDomMargin 3 3 2 BG κ (xiC1 3 t)<δc` | `decDomMargin d L N BG κ (xiC1 d t)<δc` |
| `coer_margin : K4 3 3 2 BG κ·xiC1 3 t<coerciveConst 3/2` | `K4 d L N BG κ·xiC1 d t<coerciveConst d/2` |
| `δc_small : δc² smallConstX 3 3 κ≤1/4` | `δc² smallConstX d L κ≤1/4` |
| `t_cap : 2t≤deltaStar 3 3 2` | `2t≤deltaStar d L N` |
| `bg0_cap : cK2 3 3 2·2t<bgC0 3 3 2/2` | `cK2 d L N·2t<bgC0 d L N/2` |
| `cK2_cap : cK2 3 3 2·t≤c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3/8)` | `cK2 d L N·t≤c6' d L N (famConst d L BG₂ κ) (gamma1 d/8)` |
| `cK2'_cap : cK2' 3 3 2 (famConst 3 3 BG₂ κ)·t≤c6' 3 3 2 (famConst 3 3 BG₂ κ) (gamma1 3/8)` | corresponding `d,L,N` expression in code |
| `bg1_cap : 2(compC4 3·bgK1 3 3 2·xiC1 3 t)+5·2t≤bgC1 3 3 2` | corresponding `d,L,N` expression in code |
| `κ0_ent : aEnt 3 3+1≤κ0` | `aEnt d L+1≤κ0` |
| `rate_rel : 3κ0+c1 3 3+3/2≤2κdec−1` | `3κ0+c1 d L+3/2≤2κdec−1` |
| `fam_nonneg : 0≤famConst 3 3 BG₂ κ` | `0≤famConst d L BG₂ κ` |
| `κmin_le : κmin≤κ` | same |
| `δ_pos : 0<δ` | same |
| `δ_small : δ² smallConstX 3 3 0≤1/4` | `δ² smallConstX d L 0≤1/4` |
| `δ'_pos : 0<δ'` | same |
| `δ'_cap : δ'≤thm73C3 3 3 2/2` | `δ'≤thm73C3 d L N/2` |
| `δ'_step : bgK1 3 3 2·δ'≤δ/4` | `bgK1 d L N·δ'≤δ/4` |
| `δ'_coer : bgK1 3 3 2·δ'≤coerciveConst 3/4` | `bgK1 d L N·δ'≤coerciveConst d/4` |
| `block_base : cstarX 3 3≤3^m₁` | `cstarX d L≤L^m₁` |
| `xi_small : xiC1 3·t≤1` | `xiC1 d·t≤1` |
| `rho_nonneg : 0≤rho4 3 3 2 BG κ` | `0≤rho4 d L N BG κ` |
| `det_z : (detDeg 3 3+1)²·2/exp κ<1` | `(detDeg d L+1)²·2/exp κ<1` |
| `det_rate : κ'≤(κ−log2−2log(detDeg 3 3+1))/18` | `κ'≤(κ−log2−2log(detDeg d L+1))/(2dL)` |

**PROVED (boundary).** The three new fields `hd,hL,hN` have no old counterpart. Besides `κ0_ge` and the core's pair/mass transport, the other changes substitute `d,L,N` into already general constants. `Odd L` belongs to the later centred-collar endpoint.

## T3. Producer and fixed bridge

**OPEN (exact producer target).** Put this theorem in `StepTowerGProducer.lean`, with `κroot` quantified before the chosen `L`. The requested floor is a **conclusion**, so `toG` remains total. `entropyLoss` is the later, explicitly budgeted loss in `sizeJ` units; `ROOTBOUND.md` has not supplied a uniform numerical value for it.

```lean
theorem exists_stepTowerG (d N : ℕ) (κroot : ℝ) (L : ℕ) [NeZero L]
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N)
    (κmin entropyLoss : ℝ) :
    ∃ T : StepTowerG d L N κmin,
      entropyLoss + c1 d L * κroot ≤ 3 / 2 * T.κdec
```

**PROVED / OPEN (producer route).** Choose `κ0≥max (aEnt d L+2) ((entropyLoss+c1 d L·κroot)/150)` and set `κdec=100(κ0+c1 d L+10)`, `κ'=3κdec/2+κ0+1`; the floor then follows by arithmetic. `tower_core_rates_general` (`LevelPairGeneral.lean:159–185`) already accepts arbitrary `κ0` satisfying `aEnt+1≤κ0` and `κdec≥3κ0+c1+5`; `exists_witness_params_general` supplies witness radii. **OPEN:** `stepOutput_consts_exists_ge_general` (`StepOutputConsts.lean:105–185`) pins `κ0`, so it needs `stepOutput_consts_exists_ge_general_atK0`: given `aEnt d L+2≤k0` and `κmin`, return `C : StepOutputConsts d L` with `κmin≤C.kapp`, `C.k0=k0`, `C.kdec=100(C.k0+c1 d L+10)`. Replace the old general proof by the variable-rate proof and make its old pinned statement a same-landing corollary; then transport its determinant margins to the core's larger `κ` via `detRateG_mono` and the exponential inequality. This retains one proof body.

**OPEN (exact bridge target).** Put in `StepTowerGBridge.lean` after `νref_three`, `rhoSepG_three`, and the dependent `GpG/HmG` transport:

```lean
noncomputable def StepTower.toG {κmin : ℝ} (T : StepTower κmin) :
    StepTowerG 3 3 2 κmin
```

**PROVED / OPEN (bridge meaning).** `κ0_ge` is `T.κ0_two`; the scalar projections preserve `T.κ0,T.κdec,T.κ',T.κ`. The core needs propositional rewriting by `rhoSepG_three` and `νref_three`; it is not definitional before that rewrite. After a general theorem is proved, the *old* fixed theorem is replaced by a corollary applying it to `T.toG` in the same landing. For example a general `StepTowerG.obsFamilyRate_eq_tower` with the formula of `ObsFamilyJoint.lean:465–471` specializes to the old header using only scalar projection equalities; no geometry transport is needed for that endpoint. By contrast a step-setting or determinant endpoint needs the pair transport, `detRateG_three`, and sometimes a dynamic rate-margin lemma. `stepOutput_consts_exists_ge` is already the general theorem's fixed specialization and is not an instance of `StepTower.toG`.

## T4. First ten amended tasks

| # | Status | ≤300 changed lines per leaf; file and deliverable | Dependency / fixed file |
| --- | --- | --- | --- |
| 1 | **OPEN** | `Inhabited/StepTowerG.lean`: paste the record and `νref`; no output-floor field. | New file; import cone starts here. |
| 2 | **OPEN** | `Inhabited/StepTowerGBridge.lean`: `νref_three`, separation and core-index transport. | After 1; new file. |
| 3 | **OPEN** | Same bridge: `StepTower.toG` and scalar projection lemmas. | After 2; new file; no fixed edit. |
| 4 | **OPEN** | `Fluctuation/StepOutputConsts.lean`: variable-`k0` general producer; shorten pinned general theorem to a corollary. Split numerical helpers to a new file if the diff exceeds 300. | Touches landed file; isolate its landing; no permanent duplicate proof. |
| 5 | **OPEN** | `Inhabited/StepTowerGScalar.lean`: variable ledger to core-`κ` determinant/exponential transports and output-floor arithmetic. | After 4; new file. |
| 6 | **OPEN** | `Inhabited/StepTowerGProducer.lean`: assemble `exists_stepTowerG` from 1,4,5, `tower_core_rates_general`, `exists_witness_params_general`. | New file; `κ0` chosen after `κroot`. |
| 7 | **OPEN** | `Inhabited/LevelCoversG.lean`: general cover proposition and provider from `levelLocalCover`. | Independent of 2–6 after interfaces; new file. |
| 8 | **OPEN** | `Inhabited/StepScaleDataG.lean`: general step and nine-field scale record using 1,7. | New file. |
| 9 | **OPEN** | `Inhabited/StepScaleCoreG.lean`, then `StepScaleDataGProducer.lean`: core/chart helper, then `StepTowerG.scale` from general ray and covers; split into two ≤300-line landings. | After 6–8; new files. |
| 10 | **OPEN** | `Inhabited/StepScaleDataGBridge.lean`, then `StepTowerScale.lean`: transport `StepScaleDataG` to fixed and replace `StepTower.scale` body with the general specialization while retaining its header. Split bridge and fixed swap. | Touches landed `StepTowerScale.lean`; atomic general-provider/corollary landing. |

**OPEN (parallelism and rebuild).** Tasks 2–3 are serial; task 4 and task 7 can run in parallel with them in disjoint files, but task 4's same-file proof replacement has one owner. Tasks 5–6 depend on 4; task 8 depends on 7; task 9 joins both lanes; task 10 is serial after 9. Editing `StepOutputConsts.lean` or `StepTowerScale.lean` rebuilds their broad `Balaban/Inhabited` reverse-import cones; each new-file task rebuilds its dependants after import, and every landing still needs its prescribed full-tree check.

## T5. Decision and limit

**OPEN (text for author).** “Please approve changing only the general tower's `κ0_eq` to `κ0_ge : aEnt d L + 2 ≤ κ0`, keeping `κdec_eq` and `κ'_eq`, and placing each requested root-rate floor in the producer's conclusion so the approved fixed `StepTower` still maps to `StepTowerG 3 3 2`.”

**PROVED (audit limit).** An inhabitant of `StepTowerG` certifies a one-step numerical/core package, not any frozen root clause: the site-count conversion, `IsDj` to root-polymer support, arbitrary source direction, all-torus compatibility, and accumulated multi-scale prefactor are separate open proofs. The root's witness and quantifier order must be audited independently.

**OPEN (confidence).** High on the source-level equality inventory and rate obstruction; moderate on the proposed Lean text and producer architecture because no elaboration or build was permitted.
