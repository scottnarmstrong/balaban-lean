# AUDIT-6 — general level pair and source radius

**Scope and verdict.** Focused, refute-first source audit of the declarations named in `followup_audit6.txt`. The general pair, numerical core, centred hull, and radius-indexed direct/relative families are **FAITHFUL** to their displayed claims. The new polymer observable is **WEAKER THAN CLAIMED** if read as the paper's localized Theorem 3.1(b): its remainder is one scalar, and its displayed hull rate is negative at the present tower. A contradictory docstring sentence needs correction. No declaration inspected here was vacuous or a wrong object. This is a statement-and-definition audit, not a proof-term or clean-build audit.

**Permission and frozen input.** `/home/scott/Balaban` read only; only this report may be written in `/home/scott/Balaban-scratch/astra-fluctfix`; no commit, push, build, or delegation. Input `frozen-v1`: commit `7eefe0d4552ff7df57ed665239557d19b5f9e9cb`, 2026-10-13 UTC. SHA256 below; all `file:line` anchors in this report refer to that commit. Paths are relative to `/home/scott/Balaban/`.

| Frozen file | SHA256 |
|---|---|
| `Balaban/Inhabited/LevelPairGeneral.lean` | `c4ec163ad5b5dbfa81e1cb2768ccf0d4cb9bfcfac27f47f3014b983f9ff9e83c` |
| `Balaban/Inhabited/TowerCoreRatesGeneral.lean` | `68fb615c70ce26973db39e9417a1aa63dbec6b80d6927ac159f306b1d806095f` |
| `Balaban/Inhabited/LevelStepSettingGeneral.lean` | `d652de343e581d6cea1b16fd6e447c9e7bcbf8886122d58ce2b59f83255` |
| `Balaban/Inhabited/LevelLemmasGeneral.lean` | `840608200dda773cb7aac4668814c6b7121f7c59923a562ea3e1f7d1fe676544` |
| `Balaban/Fluctuation/StepRegWitnessGeneral.lean` | `bd1634c3604ecdc42c89ddace132e93f81d2fbfe21534419622f16358ce2e66b` |
| `Balaban/Fluctuation/DetRateGeneral.lean` | `9998b4db1fdcaaf099757a3a81c3191cd0f66b4d02c0e0f13984aaf3265b33d2` |
| `Balaban/Fluctuation/DetCollarCentered.lean` | `4e446b8926ea153d2676956037b00240ff55577efd92c9c361bc713e5a71269d` |
| `Balaban/Fluctuation/DetCollarCenteredFibre.lean` | `34d2f4ff8a2f1b57df9285d1164dee534c2d320105457dbb2946e8926d7570fd` |
| `Balaban/Fluctuation/SourceRadius.lean` | `3bf339ab0033044bb4cd5d4d1015ae59fd3ad3b1d0d82e8dc3e5aeb55fe6e43d` |
| `Balaban/Fluctuation/SourceDirectTermsScale.lean` | `f997815bc568b6918f56b2d1dcf30459ba1c5a205d974bf4eb6210bc16d08338` |
| `Balaban/Inhabited/SourceDirectTermsFromTower.lean` | `e55377f9a72e2d5cb2aba6d0957f9e9a5020b271ce34f1e4ea43873095203bcc` |
| `Balaban/Inhabited/ObsUnconditional.lean` | `8523b811659bad7744e0db0f739eeb15ff6764c3be62501f41902e4d4674d619` |
| `Balaban/Fluctuation/SourceFamilyRelativeRadius.lean` | `8f8fa388cadd4e1a170c1520a215fc947eb6c5779cdb6044ee9d6aae090c1709` |
| `Balaban/Inhabited/SourceFamilyRelativeRadiusFromTower.lean` | `2962af9dd2de9a1ac35630e01ea3d5cd33041aa1e9dac27a2722b42ae4c25a8a` |
| `Balaban/Inhabited/Thm31bPolymer.lean` | `99ea71c3abe817a9fe6f1d4159a06408ac30e91d7fb4ef6a34bb9f319322c2e7` |
| `Balaban/Inhabited/StepActivityDirectPhysicalRates.lean` | `21c24a7a3af0c0de830a0f7aff50db11a60dd8246af05b7456bd916e9f661e7f` |
| `Balaban/Inhabited/TowerCoreRatesAtLeast.lean` | `633072180be93ebfdfb6dd30dd7399f584d74dc2786dd485106864076594fde7` |
| `Balaban/Inhabited/StepTower.lean` | `015b9f8321e12a9bd8ce016439ca178ba42b8edc8b55315ee2176e985e25f6ef` |
| `Balaban/Fluctuation/CubeSystem.lean` | `b7e3cc2a0458562b2f65344975df9b70d6af3561ba86b708ec9b27b93531d37a` |
| `Balaban/Fluctuation/DARateNumerics.lean` | `95d4d94fb0e35a3ca3ce21db0e21527512de76af35b6a03e54d2b901980fa1f2` |
| `Balaban/Fluctuation/DetCollarHullSymm.lean` | `df099573f28cde79429caf7e9465260de2e5ae0ed82904f41fd5e4e68f91bfb1` |
| `/home/scott/Balaban-scratch/astra-lfr3/P6.txt` | `d1d5405f76d0ace0a36b5ae2ce28dd47624f33c0cd885c966b103e3b0739e823` |

**Post-freeze remap (`frozen-v2`).** Main advanced to `800817ef61715481ef76928a818a0130a7ad24c2` while this audit was being written. Rechecking all listed hashes found only three changed paths: `SourceRadius.lean` was shortened, and `SourceFamilyRelativeRadius.lean` and `SourceFamilyRelativeRadiusFromTower.lean` were removed. Their definitions/statements were moved into the following v2 files; the G4 verdict below was rechecked at these new anchors. All other v1 hashes still match live main. This is a source remap, not a semantic change found by the audit.

| Frozen-v2 file | SHA256 | Rechecked anchors |
|---|---|---|
| `Balaban/Fluctuation/SourceRadius.lean` | `b2c6e4394dc682c68adbdce798e9c8371d517bcee9613b611d69f2beeb4228ab` | `sourceSlice_mem_restricted_rho:39–44`, `physVqRho_one:46–48`, `physFibreRho_one:49–51` |
| `Balaban/Fluctuation/SourceRadiusCarriers.lean` | `b76ecb0815b3145328f467ba0df0d375f6b1f2b4afec9ab50fcef41f90644098` | `l1BallRho:42–46`, `physSΛRho/physVRho/physVqRho:90–100` |
| `Balaban/Fluctuation/SourceFamilyRelative.lean` | `c41534a4b3fd46e28751588a6fcc2581f7dfdd4b7372b6cbd9dc0fcfe9ca76ce` | `physInclScaled_image_subset_rho:116`, `directTermsFamilyOn_scaled_rho:144`, `sourceFamilyRelative_scale_rho:192–244`, unit corollary `:289` |
| `Balaban/Inhabited/SourceFamilyRelativeFromTower.lean` | `427d9ee7f9f06c60e9853b90a53c2f58ab50e722a6021d404e2cc0c174fe6e27` | `sourceFamilyRelative_scale_fromTower_rho:43–100`, unit corollary `:197` |
| `Balaban/Inhabited/UniformChartRelative.lean` | `e47485ef0dcc9d2c57d1c1651171a6cca759ef26918dcb23e228661c0c372919` | `hatStepK_physVRho:77`, unit corollary `hatStepK_physV:98` |

## G1. General pair and 21 numerical clauses

**FAITHFUL — inhabited binder prefix.** `LevelPairGeneral.lean:159–183` actually concludes a `FlCore N` for *every* natural `N`, with one pair `GpG d L 9 m₁ 1`, `HmG d L 9 m₁ 1`, `K=2`, `a₁=1`, `0≤ν`, and `ν L⁴≤1`. These hypotheses are consistent for every `d≥3,L≥3,N` (take `ν=0`, any sufficiently large `κ0,κdec`; the theorem itself proves the conclusion). For the physical positive-mass case one may choose `0<ν≤L⁻⁴`. This is an **existence of numerical core and one pair** statement, not a general-dimension one-step RG theorem for all `k,N₁`.

**FAITHFUL — same torus and mass.** `LevelStepSettingGeneral.lean:43–48` unfolds `lvTopG` to `levelGS` of level `k+1` and `lvLowG` to `stepG` of level `k`, both with ambient side `N₁ L^{m₁}` and level parameter `k+1`; `LevelPairGeneral.lean:98–105` instantiates both on that same torus. `dgSetting_lvG` and `opSetting_lvG` require the very same `ν L^{2(k+1)}≤1` (`:108–136`), and `hpair_lvG` specializes to `k=1`, `N₁=9`, `n=1` (`:140–149`). The pair supplies `BgHyp d L 2 ...` at the same mass; there is no separate hidden mass witness.

**FAITHFUL — clause correspondence.** The conclusion of `TowerCoreRatesGeneral.lean:54–71` is the clause list of `StepActivityDirectPhysicalRates.lean:57–74` after substituting `(3,3)↦(d,L)` in dimension/block arguments and replacing the old pair by `(Gp,Hm)`; it also appends `κmin≤κ`, as does `TowerCoreRatesAtLeast.lean:35–52`. Five high-risk spot checks are literal: `4 d (2L+1)^d κdec≤κ` (`:59`), `log((2L+1)^d L^d)≤(κ/2−1)/2` (`:60`), block cap `cstarX(d,L)e^{N0(d,L)κ}≤L^{m₁}` (`:62`), `FlCore N (Gp m₁) (Hm m₁) a₁ ν ... (levelKc d L) (Cchi d L) ...` (`:56`), and `3κ0+c1(d,L)+3/2≤2κdec−1`, `κmin≤κ` (`:71`). The proof chooses `κ` before `m₁` and `t` (`:91–118,140–163`), avoiding a reversed quantifier. `tower_core_rates_at_least_of_general` returns the old pair and identical conclusions at `d=L=3` (`:167–190`). `rhoSepG` unfolds to the explicit sum in `LevelPairGeneral.lean:35–37`, and `rhoSepG_three` proves equality with `rhoSep m₁` by unfolding both and `ring` (`:86–89`), not just comparable separation bounds.

## G2. General step, witness constants, determinant rate

**FAITHFUL.** `LevelStepSettingGeneral.lean:98–111` unfolds `StepSetting.betaU` as `β ((L^k)^d)/((L^k)^2)` and proves the exact `β L^{k(d−2)}` for `d≥2,L>0`. This is the canonical `β_k` scaling; P6 text layer, printed p. 1 (near the description of `R_{k+1}`), likewise changes the coupling by `L^{d−2}` per step. `hatStepKG_three` is `rfl` for the actual `hatStepK` at `(3,3,2,rhoSep)` (`:93–96`), and `lvTopG_three`/`lvLowG_three` are `rfl` for the tower's generating sets (`:50–54`). `bgHyp_lvG` has the same mass condition and weights `compWeight L 1` (`:152–165`). `LevelLemmasGeneral.lean:64–99` proves row/cover/foot and `FlCore` for those exact `lvTopG,lvLowG`; its `d=L=3` examples elaborate at the landed objects (`:109–137`). `StepRegWitnessGeneral.lean:30–39` defines `witB5G,witK2G` with the same formulas and proves `rfl` equality at `(3,3,2)`; `exists_witness_params_of_general` uses those equalities (`:95–103`). `DetRateGeneral.lean:53–73` defines `(κ−log2−2log(detDeg+1))/(2dL)` and proves `detRateG 3 3 κ = towerDetRate κ` by unfolding, not an unrelated rate. **Caveat:** these are exact specializations of constants/objects and a numerical witness; no general-dimension physical output record is claimed by these files.

## G3. Centred determinant collar

**FAITHFUL.** `DetCollarCentered.lean:49–59` sets base `b−q a(1,…,1)` and hull `sitesOf T ∪ ⋃_{b∈T} box(base,L a)`, with `a=cellSide L m₀ m₁ K`. `detCollarHullC_one` identifies the entire hull with the landed `detCollarHull` after `collarBasesC_one` (`:71–83`); `detCollarHullC_three` uses `(L−1)/2=1` at `L=3` (`:86–89`). `DetCollarCenteredFibre.lean:49–59` separately identifies the fibre and grouped terms at `q=1`. For odd `L=2q+1`, reflection, translation, coordinate permutation and composition are handled in `DetCollarCentered.lean:233–344`; the terminal theorem quantifies over every `GenSymm L N₁ m₁ K K m₀ σ`, exactly the binder used by landed `DetCollarHullSymm.lean:351–361` and `DetCollarCenteredFibre.lean:159–195` for covariance. This is full generated-group covariance, not reflection alone. The only adjacency lemma requiring `1≤q` and `q+2≤L` is `DetCollarCentered.lean:126–167`; for `L=3,q=1` both are equalities. The hull bound needs only `q+1≤L` (`:176–211`, `DetCollarCenteredFibre.lean:102–107`), and the symmetry theorem does not add either inequality. **Refuted suspicion:** the `q+2` condition excludes the landed `L=3` specialization.

## G4. Radius `ρ` source statements

**FAITHFUL — radius and order.** `SourceRadius.lean:42–46,102–128` defines `l1BallRho` by `∑‖g‖<ρ` and the physical carriers using that ball; the four `ρ=1` carrier equalities are definitional (`rfl`). `SourceDirectTermsScale.lean:487–527`, `SourceFamilyRelativeRadius.lean:129–178`, and `SourceFamilyRelativeRadiusFromTower.lean:36–92` choose `m₁,t,δ,β₀,...` or `β₀,CE,CF` **before** `∀ρ`; they require `max 1 ρ≤β`, `0<q≤ρ`. `SourceDirectTermsFromTower.lean:102–148,296–339` and `ObsUnconditional.lean:35–81` take arbitrary `ρ` and `q` at a fixed tower step. Their conclusions use `physSΛEta ... (q/β)` and quantify over every `g` with `∑‖g‖<q`; the relative family uses `physVqRho ... ρ q` (`SourceFamilyRelativeRadiusFromTower.lean:59–65,73–92`). Setting `q=ρ>0` gives the entire strict radius-`ρ` ball. The visible carrier and instance clauses in these `_rho` statements do not substitute `l1Ball` or `physV` at radius 1. **Refuted suspicion:** a hidden unit ball survives in the displayed `_rho` conclusions.

**FAITHFUL at `ρ=1`.** `SourceRadius.lean:46,119–128` gives literal carrier equalities; `SourceDirectTermsFromTower.lean:238–285,349–390` and `ObsUnconditional.lean:161–208` obtain their old statements by invoking `_rho` at `1`; `SourceFamilyRelativeRadius.lean:215–269` and `SourceFamilyRelativeRadiusFromTower.lean:187–248` do likewise. `SourceDirectTermsScale.lean:638–692` has the same reduction. The theorem types preserve the landed `q≤1` form; the `_rho` variants do not add a `ρ`-dependent threshold.

**WEAKER THAN CLAIMED if interpreted as a full radius-`ρ` observable theorem.** What is now proved: a common direct-term domain/term family on the scaled slice `q/β`, a full-ray clause for `‖ψ̂‖≤p₁` (`ObsUnconditional.lean:76–81`), and an analytic relative activity family on the open `physVqRho ... ρ q × ball 0 2`, with amplitude bound `CE(log β_k)^{3p}/√β_k + q CF(log β_k)^p/√β_k` (`SourceFamilyRelativeRadiusFromTower.lean:66–92`). `SourceDirectTermsScale.lean:401–428` also gives a **pointwise** `StepActivityBound` at `g` under its full numerical hypotheses and central real datum. These are not a tower-level activity package for all radius-`ρ` sources with one uniform small bound independent of `ρ`; the estimate explicitly grows with `q`. No radius-`ρ` `obsMarks_zeroClass_family`, observable `thm31b_zeroClass_fromTower`, or complete witness has been found in the named files: `ObsUnconditional.lean:213–373` reverts to the unit-ball statements. This is a bounded-scope conclusion, not a claim that such results are impossible.

## G5. Polymer regrouping and remainder

**FAITHFUL as a finite algebraic regrouping; WEAKER THAN CLAIMED as Theorem 3.1(b).** `Thm31bPolymer.lean:97–125` defines the remainder in the proof as `R=∑_{T:¬IsPolyDom(sitesOf T)}e T` (`:125`); it is one complex scalar, selected after `g,y,i` in `thm31b_zeroClass_polymer_fromTower` (`:220–232`). It has no domain index and no stated locality or analyticity. For each nonpolymer nonzero coefficient the root anchor makes `T` nonempty, so `dOmega=⊤` (`:140–146`) and `dExt T=Mbig=n²+1` by `CubeSystem.lean:103–110`. Summing at most `2^n` cube subsets and using `λ≥log 2` gives `‖R‖≤c e^{-λ}` (`Thm31bPolymer.lean:148–177`), precisely `C·obsPrefactor·e^{-(3/2)κdec}` in the tower theorem (`:228,241–247`). Thus the bound is correct, but does not localize `R`.

**WEAKER THAN CLAIMED — nondecaying bound at the current tower.** `hullRate_three_pos_iff` says `hullRate 3 3 λ>0` iff `60751·3375·log 2<λ` (`Thm31bPolymer.lean:181–195`). Here `λ=3T.κdec/2`. From `StepTower.lean:36–37` and `DARateNumerics.lean:214,242`, `κdec=100(aEnt(3,3)+2+3375+10)≤30,338,700`; hence `λ≤45,508,050`, whereas `60751·3375·log 2>60751·3375/2>102,000,000`. The output `hullRate` is therefore **negative** for this tower, so the displayed exponential bound grows with `sizeJ`. The theorem states this rate without asserting it is positive, and its docstring `:204–206` gives the exact positivity criterion. However the same docstring says `:210` that “the remainder `R`” is still lacking, despite the explicit `R` and estimate at `:223–228`. That sentence should say that a *localized or class-compatible treatment* of `R` is lacking. The lack of datum/source locality, source analyticity, reality, and symmetry is correctly admitted at `:208–210`.

## Refutation ledger, limitations, and G6

| Candidate defect tested | Countercheck | Disposition |
|---|---|---|
| General-pair hypotheses empty for arbitrary `d,L,N` | `ν=0` meets `0≤ν`, `νL⁴≤1`; `hpair_lvG` supplies concrete pair | **REFUTED** as a defect; `LevelPairGeneral.lean:140–183` |
| Different tori or an extra mass range in `FlCore` | Both sets have side `N₁L^{m₁}`; `hpair_lvG` passes one `ν` | **REFUTED**; `LevelStepSettingGeneral.lean:43–48`, `LevelPairGeneral.lean:143–149` |
| Odd-collar lemma silently excludes `L=3` | `q=1`, `q+2=L=3`; group theorem only needs oddness | **REFUTED**; `DetCollarCentered.lean:126–167,338–344` |
| `_rho` theorem still has a unit-ball carrier | Expanded carriers are `l1BallRho`/`physVqRho`; relative family keeps `q≤ρ` | **REFUTED** for named conclusions; `SourceRadius.lean:102–117`, `SourceFamilyRelativeRadiusFromTower.lean:59–92` |
| Polymer result establishes a positive localization rate | Numerical tower bound forces the displayed hull rate below zero | **SURVIVED**; `Thm31bPolymer.lean:181–206,231–232` |
| Remainder absent | Explicit scalar `R` and bound exist, but docstring says it is missing | **SURVIVED** as wording error; `Thm31bPolymer.lean:210,223–228` |

**G6 — two statements requiring the clearest caveat.** First, `tower_core_rates_general` (`LevelPairGeneral.lean:159–183`) is a genuine general-`d,L,N` numerical core at one pair (`k=1,N₁=9`), not a construction of the entire general-parameter RG step. Second, `thm31b_zeroClass_polymer_fromTower` (`Thm31bPolymer.lean:211–232`) is an exact regrouping with a bounded *scalar* remainder, but the present tower gives a negative hull rate and no locality for that remainder; correct the contradictory `:210` docstring before describing this as polymer localization in the paper's sense.

**Verification and closeout.** Evidence collected by `git rev-parse HEAD`, `sha256sum` of the listed frozen inputs, a post-freeze hash comparison, and line-numbered reads of declarations and unfolded definitions, including `CubeSystem.dExt`, `StepSetting.betaU`, `rhoSepG`, and `detCollarHullC`. No files in the read-only repository were changed. No Lean build, axiom census, or full proof dependency audit was run; verdicts are confined to statement faithfulness and the explicit numerical deduction above. The two survived findings are documented; no other reportable defect survived the checks listed here.
