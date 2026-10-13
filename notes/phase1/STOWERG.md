# STOWERG — signatures for the general tower

**PROVED snapshot.** Main `/home/scott/Balaban` was read at commit `8221cb751b998b9bef2b7c982725b5b48d0ade01` (2026-10-13); it was not edited. This is a source-level design, not an elaborated Lean file. Names with suffix `G` below are **OPEN proposed declarations** unless an existing declaration is explicitly cited.

## T1. Base record and producer

**OPEN proposed signature.** Use `open Balaban ... LevelStep LevelPair` as in `StepTower.lean`; `νref` is a new definition. The instance `[NeZero L]` is needed by the existing generating-set and constant definitions; `hd,hL,hN` are fields, so no numerical hypothesis is silently assumed. `Odd L` is absent: the base core, covers and ray work for every $L\ge3$; the centred determinant package will add oddness.

```lean
noncomputable def νref (L : ℕ) : ℝ := 1 / (L : ℝ) ^ 4
structure StepTowerG (d L N : ℕ) [NeZero L] (κmin : ℝ) where
  hd : 3 ≤ d
  hL : 3 ≤ L
  hN : 2 ≤ N
  (κ0 κdec κ' : ℝ)
  κ0_eq : κ0 = aEnt d L + 2
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
  κ_lower : 4 * (d : ℝ) * ((((2 * L + 1) ^ d : ℕ) : ℝ)) * κdec ≤ κ
  κ_one : 1 ≤ (κ / 2 - 1) / 2
  κ_log : Real.log (((((2 * L + 1) ^ d : ℕ) : ℝ)) * ((((L ^ 1) ^ d : ℕ) : ℝ))) ≤ (κ / 2 - 1) / 2
  c7_cap : c7 d L N BG κ ≤ thm73C3 d L N
  large_block : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  dom_margin : decDomMargin d L N BG κ (xiC1 d * t) < δc
  coer_margin : K4 d L N BG κ * (xiC1 d * t) < coerciveConst d / 2
  δc_small : δc ^ 2 * smallConstX d L κ ≤ 1 / 4
  t_cap : 2 * t ≤ deltaStar d L N
  bg0_cap : cK2 d L N * (2 * t) < bgC0 d L N / 2
  cK2_cap : cK2 d L N * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
  cK2'_cap : cK2' d L N (famConst d L BG₂ κ) * t ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)
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
  det_z : (((detDeg d L + 1 : ℕ) : ℝ)) ^ 2 * (2 / Real.exp κ) < 1
  det_rate : κ' ≤ (κ - Real.log 2 - 2 * Real.log (((detDeg d L + 1 : ℕ) : ℝ))) /
    (2 * (d : ℝ) * (L : ℝ))
```

**PROVED source alignment.** These are all 49 old fields, in their old order, after the three new hypothesis fields (`StepTower.lean:34–80`): 37 individually named fields and 12 names in the two grouped declarations. The core uses `GpG,HmG` on the $N_1=9$, $k=1$ reference torus (`LevelPairGeneral.lean:97–105,140–149`); $\nu_{\rm ref}=L^{-4}$ satisfies its mass bound. The factors $4d(2L+1)^d$, $(2L+1)^dL^d$, $L^{m_1}$ and $2dL$ replace $4116$, $9261$, $3^{m_1}$ and $18$ respectively (`TowerCoreRatesGeneral.lean:43–79`; `DetRateGeneral.lean:37–55`). The step constants $1/4$, $3/2$, $100$ remain fixed.

**PROVED reason to retain equalities.** `κ0_eq` supplies `κ0_two` and is rewritten in `DetPackageFromTower.lean:161`; `κdec_eq` is rewritten in `RenormDetFibreTower.lean:150`, `CommonWitnessJoint.lean:552` and others; `κ'_eq` is rewritten in `StepOutputPhysical.lean:69–78`, `Thm31bFromTower.lean:45` and others. Replacing them by bounds loses exact old endpoint statements and adds reverse inequalities. **OPEN recommendation:** keep all three pinned equations, using $c_1(d,L)$ and $a_{\rm Ent}(d,L)$, and strengthen $\kappa$ through `κmin` when needed.

**OPEN proposed producer.** `exists_stepTowerG (d L N : ℕ) [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) (hN : 2 ≤ N) (κmin : ℝ) : Nonempty (StepTowerG d L N κmin)`. First take `C` from the now **PROVED** `stepOutput_consts_exists_ge_general d L hd hL κmin` (`StepOutputConsts.lean:105–185`), so $C.\kappa\ge\kappa_{\min}$ and its $\kappa_0,\kappa_{\rm dec},\kappa'$ have exactly the pinned equations. Apply `tower_core_rates_general` with lower bound `C.kapp`, mass `νref L`, and rates `C.k0,C.kdec,C.k'`; the `hpair_lvG` input is built into that theorem (`LevelPairGeneral.lean:140–185`). `exists_witness_params_general` supplies $\delta,\delta'$ (`StepRegWitnessGeneral.lean:56–96`). Since the core returns $\kappa\ge C.\kappa$, `C.z_lt` transfers to `det_z` by monotonicity of $e^{-\kappa}$, and `C.kdet_ge`, `C.kdet_eq` and `detRateG_mono` give `det_rate` after normalizing the cast of $\operatorname{detDeg}+1$ (`DetRateGeneral.lean:50–70`). The core gives its 21 rate conjuncts; `large_block`, `xi_small` and `rho_nonneg` follow as in old `exists_stepTower` from the general `cstarX` bound, `c7_le_bgC1` with `bgC1_le_small`, and positive `rho4` (`StepTower.lean:105–127`; `RenormEndpointSharp.lean:50`). **OPEN:** the arithmetic transport, assembly and a checked Lean proof; no further new analytic theorem is identified for this *base* producer. The output ledger's $\kappa$ need not equal the core's $\kappa$.

## T2. Fixed-parameter bridge

**OPEN proposed bridge.** State `StepTower.toG {κmin : ℝ} (T : StepTower κmin) : StepTowerG 3 3 2 κmin`. First prove `νref_three : νref 3 = nuW` by `norm_num [νref, nuW]`. For `core`, rewrite **the index itself** by `rhoSepG_three T.m₁` (`LevelPairGeneral.lean:86–89`), then unfold `GpG,HmG,lvTopG,lvLowG,stepG,Gp,Hm`; at equal $\varrho$ these are the same `levelGS`, and proof arguments are irrelevant. In Lean use `simpa only [rhoSepG_three, νref_three, GpG, HmG, lvTopG_three, lvLowG_three, Gp, Hm, stepG] using T.core`, adjusting the simp list after elaboration. **REFUTED:** this field is `rfl` before rewriting $\varrho$; its type is indexed by two non-definitionally equal real expressions. The numeric fields are direct projections after specializing $d,L,N$; `det_rate` needs arithmetic normalization of $2\cdot3\cdot3=18$, and `νref` is not safely assumed definitionally equal to `nuW`. No `Gp_congr` is required: rewrite the index in the expected type, so Lean transports dependent arguments automatically. **REFUTED:** adding an arbitrary $\varrho$ field reduces work here, since landed `scale_C_items_general` has the step fixed at `rhoSepG` (`LevelRayDataGeneral.lean:139–157`).

**OPEN proposed step transport.** For an old `T`, prove a dependent identity `(rhoSepG_three T.m₁) ▸ (T.toG.step k hk N₁ ν β p₁) = T.step k hk N₁ ν β p₁`; this makes the two `StepSetting` indices comparable. After transport use `hatStepKG_three` (`LevelStepSettingGeneral.lean:94–96`). Do not write an uncast equality: its two sides have different indexed types.

**OPEN corollary shapes.** Once `StepTowerG.scale` and `StepScaleDataG.toFixed` are proved, the old `StepTower.scale T hA p` is `let G := T.toG; obtain ⟨β₀,hβ,h⟩ := G.scale hA p; exact ⟨β₀,hβ,fun k hk N₁ hdiv hN ν hν hmass β hβ p₁ hp hpLog => (h k hk N₁ hdiv hN ν hν hmass β hβ p₁ hp (by simpa [Nat.mul_sub_right_distrib] using hpLog)).map (StepScaleDataG.toFixed T)⟩`; the displayed normalization is schematic and must be checked. Once a **new** `detExpansionLocC_scale_fromTowerG` is proved, old `detExpansionLocC_scale_fromTower T ...` applies it to `T.toG` and rewrites `rhoSepG_three`, the transported step, `detRateG_three` and $L^dN/2=27$; it is **not yet** a corollary of landed `detExpansionLocC_scale_of_tower`, which is fixed at $(3,3,2)$ (`DetOutputTermsWitness.lean:194–230`).

## T3. Scale record and cover

**OPEN proposed signatures.** Define `T.step k hk N₁ ν β p₁ : StepSetting d L N₁ T.m₁ k N (rhoSepG d L T.m₁) := hatStepKG T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ`. Define `LevelCoversG d L N N₁ m₁ k ϱ ϱm Gp Hm m₀ : Prop` by the *exact two-conjunct conclusion* of `LocalCover.levelLocalCover` (`LevelLocalCover.lean:696–724`), with arbitrary top/lower generating sets of those indexed types. Its block conjunct has seven fields: `CovSetup`, `↑nbhdF = X1`, optimal `W₀,E₀` with `ConnStruct`, cube containment, `MeetsOne` and exact `bondCost = treeLenCovOne`, zero tree length, `readSites` inclusion, `BlockMargin`, block-site inclusion. Its source conjunct has five fields: `CovSetup`, the same neighbourhood equality, optimal structure, zero tree length, site membership. Set $m_0=1$, $\varrho=\varrho_m=\rho_{\rm SepG}$, $Gp=lvTopG$, $Hm=lvLowG$.

```lean
structure StepScaleDataG {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁]
    (ν β p₁ : ℝ) : Prop where
  core : FlCore N (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
    (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1 ν T.c T.BG T.κ T.t
    (levelKc d L) (Cchi d L) T.c₂ T.BG₂ T.t
  xi : XiCData (T.step k hk N₁ ν β p₁).G' (compWeight L 1) ν (k + 1) 1 T.t
    (T.step k hk N₁ ν β p₁).D'
  ray : Nonempty ((T.step k hk N₁ ν β p₁).RayData (2 * p₁))
  cψ_pos : 0 < lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))
  r_pos : 0 < lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁
  fl_radius : Real.sqrt (N : ℝ) *
    (‖(((T.step k hk N₁ ν β p₁).betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)‖ *
      (covSupConstC d L N (compWeight L (1 : ℝ) k) T.κ *
        lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))))) < T.t
  ray_margin : (4 + lvRG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2))) p₁) * p₁ <
    lvCpsiG d L N T.κ T.t (β * (L : ℝ) ^ (k * (d - 2)))
  p_lt : p₁ < 2 * p₁
  covers : LevelCoversG d L N N₁ T.m₁ k (rhoSepG d L T.m₁) (rhoSepG d L T.m₁)
    (lvTopG d L N₁ T.m₁ k (rhoSepG d L T.m₁))
    (lvLowG d L N₁ T.m₁ k (rhoSepG d L T.m₁)) 1
```

**OPEN producer statement.** `StepTowerG.scale (T) {A₁} (hA : 0 < A₁) (p : ℕ) : ∃ βray, 2 ≤ βray ∧ ∀ k (hk : 1 ≤ k) N₁ [NeZero N₁], L ∣ N₁ → 5 < N₁ → ∀ ν, 0 ≤ ν → ν * (L : ℝ) ^ (2*(k+1)) ≤ 1 → ∀ β, βray ≤ β → ∀ p₁, 0 < p₁ → p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k*(d-2))) → Nonempty (StepScaleDataG T k hk N₁ ν β p₁)`. `scale_C_items_general` gives positivity, radius, ray margin and ray data (`LevelRayDataGeneral.lean:139–210`); `hatStepKG_betaU` turns its explicit $b$ radius into the `betaU` field (`LevelStepSettingGeneral.lean:99–102`). `flCore_level_transfer` gives `core` from `T.core` using `dgSetting_lvG`, `opSetting_lvG`, both level lemmas and `bgHyp_lvG` (`LevelRayTower.lean:62–78`; `LevelPairGeneral.lean:108–149`). `exists_xiC` plus the unit datum gives `xi`, as in old `StepTower.scale` (`StepTowerScale.lean:124–143`). `LocalCover.levelLocalCover` gives `covers` from $L^1\mid N_1$ (`LevelLocalCover.lean:696–724`). **OPEN:** this package assembly and its Lean specialization bridge; no missing general analytic lemma for these nine fields was found.

## T4. First ten bounded tasks

**OPEN plan.** Each task changes at most 300 lines; a task whose proof grows beyond that splits before landing. Each landing builds the affected module and the whole tree. “Shared” means useful also for mechanism (a); fixed endpoint files are untouched until task 10.

| # | File, inputs → output | Fixed swap | Shared? |
|---:|---|---|---|
| 1 | `Inhabited/StepTowerG.lean`: old `StepTower`, `LevelPairGeneral` → `νref`, `StepTowerG` exact fields | none | yes |
| 2 | `Inhabited/StepTowerGBridge.lean`: `rhoSepG_three`, `nuW` → `νref_three`, pair/core transport lemmas | none | yes |
| 3 | same bridge: old projections → `StepTower.toG`, with tests of each field transport | none | no |
| 4 | `Inhabited/StepTowerGScalar.lean`: `stepOutput_consts_exists_ge_general`, `detRateG_mono` → transport `C.z_lt` and `C.kdet_ge` from `C.kapp` to core $\kappa$; add `xi_small` lemma | none | yes |
| 5 | `Inhabited/StepTowerGProducer.lean`: `tower_core_rates_general`, output ledger, witness parameters, task 4 → `exists_stepTowerG` | none | yes |
| 6 | `Inhabited/LevelCoversG.lean`: `levelLocalCover` → `LevelCoversG` and its level-pair provider | none | yes |
| 7 | `Inhabited/StepScaleDataG.lean`: `hatStepKG`, tasks 1 and 6 → `T.step`, nine-field scale record | none | yes |
| 8 | `Inhabited/StepScaleCoreG.lean`: general pair, `flCore_level_transfer`, `exists_xiC` → `core`/`xi` helper | none | yes |
| 9 | `Inhabited/StepScaleDataGProducer.lean`: tasks 6–8, `scale_C_items_general` → `StepTowerG.scale` | none | yes |
| 10 | `Inhabited/StepScaleDataGBridge.lean`, then `Inhabited/StepTowerScale.lean`: task 9 → `StepScaleDataG.toFixed`; replace old `StepTower.scale` body by corollary, retain header and `scale_instance` | `StepTower.scale` only | no |

**OPEN sequencing qualification.** Task 3 depends on task 1–2, task 5 on task 4, and task 10 briefly freezes `StepTowerScale.lean`; tasks 4, 6 and 8 can be drafted independently once the signatures are approved. The general determinant wrapper and its fixed corollary are subsequent tasks; the centred-collar expansion is not smuggled into the base tower.

## T5. Author decision

**OPEN proposed decision text.** Approve a general `StepTowerG d L N κmin` with the exact old field order, three dimension hypotheses, pinned definitions of $\kappa_0,\kappa_{\rm dec},\kappa'$, and a reference core on the general level pair at $\rho_{\rm SepG}$ and mass $L^{-4}$. The main design choice is the separation index: keeping `rhoSepG` matches the already proved ray theorem and makes the $3,3,2$ bridge one explicit dependent rewrite; a free $\varrho$ would require refactoring that theorem. Approval commits the general records and explicit specialization bridge while preserving each old endpoint header until its general proof can replace the body.

**Confidence: moderate.** **PROVED:** old field inventory and cited landed signatures at the snapshot. **OPEN:** elaboration of these proposed structures and transports, the new producer and scale assembly, line estimates, and the later general determinant endpoint.
