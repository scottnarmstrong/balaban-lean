# LF4K plan: the kept outcomes of Theorem III.8.9 (a), (b) against the landed Lean (W949, 2026-10-17)

Statuses LANDED / PARTIAL / MISSING (names checked in the worktree). Inventory only, no Lean. Sources: P7 (3.6)–(3.10) (`sources/s002200050486.pdf`), LFR Lemma III.8.7, Def. III.8.8, Thm. III.8.9 (a), (b) (`notes/phase1/LF-RECONSTRUCTION.md` l. 3582–3640; `review/papers/E9-*.md`, `E10-*.md`).
Scope: the five kept outcomes ϰ₁..ϰ₅ of a ripe component; the removed lane is LF4R-PLAN. What the consumers need: `KeptData.bound` (`Operators/StepData.lean`): for ripe kept `Z` of an admissible history, the support clause (`K = 0` off `ChiDomAt`) and `KerBound (localHistory) k (datum k a ϰ).ker (κ_k − C_R λ̂_k^{2d+1} + γ_k(ϰ))`; it enters `rg_ripe_of_kappaK` (`hκ`, via `Rep.keptExp`, `D4Pin`) and `locOp_pkgBound_kappa`.

## 0. What is already settled
1. (b) is arithmetic once (a) holds: `Rep.rg_ripe` (`Def7Basic.lean`) from `KeptData.gam_ge` and `D4Pin`; `rg_ripe_of_kappaK`, `hcount_of_flow`, `hrip_of_flow` (`R/RRemovedFinalRg.lean`) for the region-history budget. Nothing to add for (b).
2. `KeptData.bound` is a FIELD (an assumption); no theorem produces a `KeptData`. `keptOp`/`KeptDatum` exist (`Operators/LocOp.lean`, `StepData.lean`), `Rep.κK` is free.
3. `C_dec ≡ 5`: `cDec`, `sum_inv_cDec` (`Outcome.lean`); γ-inequality (III.5.1): `smallFactor_ge` (`R/SmallFactorGe.lean`) is stated for `SmallFactorPar` (`P.A3`, `P.lamHat`, `2·A3·λ̂^{pR}`), the consumer has `S.A3'`, `S.lam`: bridge MISSING (identify `P.A3 = S.A3'`, `P.lamHat = S.lam k`).

## 1. Ingredients of (a): (III.8.5) for o = ϰ₁..ϰ₅ with γ(ϰ_i) = γ_i
| Ingredient | Status | Evidence |
|---|---|---|
| Decomposition of unity, outcome kernels `K^{(ϰ_i)}` as `K^pre · indicators` (Def. III.5.2) | LANDED (abstract) | `Outcome.lean` `weight`, `weight_sum`, `outcomeKernel`, `outcomeKernel_sum`, `IsKept` |
| Small-factor indicators `χ̃_k, χ_S, χ⁰, χ''` and their read sets | LANDED | `R/SmallFactorChi.lean`, `RRemovedLocality*.lean` (`chiTilde_congr`, `chiDD_congr`, …) |
| Lemma III.5.3 (a)–(e): `e^{-𝒢^♮−𝒜_win} ≤ e^{C_{k₁,k}−γ_i}` per outcome | PARTIAL | `R/SmallFactorAction.lean`, `SmallFactorOne.lean`, `SmallFactorTilde.lean`; `HgeoDischarge.lean` `smallFactor_{one,two,five}_ripe`; ϰ₃, ϰ₄ geometry not instantiated for histories |
| (III.5.1) `γ_i − log C_dec ≥ 2A₃'λ̂^{pR}` | PARTIAL | `smallFactor_ge`; bridge to `S.A3'`/`S.lam` (0.3) |
| Window action/exponent bounds `(S0)`, (2.15′) | LANDED | `quietKernel_bound`, `absW_quiet_le`, `window_conversion`, `ActionConvWindow.lean` |
| Quiet window kernel as Gaussian chain × bounded rest; Gaussian node integral | LANDED | `absW_quiet_le_action`, `gauss_forest_trees`, `lintegral_gauss_coords_eq`, `window_node_integral_eq_of_history` (Gaussian part only, see §3) |
| Regrouping `Θ`, shells, tree/zero groups volumes | LANDED | `exists_regroup_shell`, `exists_window_hid` (`hid`,`hsupp`), `zero_group_vol_le`, `tree_group_vol_le`, `window_hvol_of_groups` |
| Core (D5) at `k₁` | LANDED | `hcore_of_anc`, `locOp_pkgBound_kappa` |
| ϰ₁–ϰ₃: integrate `𝒥` (Lemma III.1.6) and `ψ_k↾Z₀` by (2.8); `∫ const^♮ e^{-½𝒢^♮} = 2^{N/2}` per block | MISSING | no `∫` over `ψ_k↾Z₀` of the composed Gaussian with the `ϰ` indicators; `integral_window_comp` (block-tree level) landed |
| ϰ₄, ϰ₅: (2.58′) and Lemma III.6.4, `e^{-βA*_k+1+3+|C^♮_0|+C_{k₁,k}}` | PARTIAL | `removed_quotient_le_of_history` (quotient form), `cancellation_identity`; `hquot` of `exists_window_hid` still open (LF4R §8) |
| ϰ₅ kernel `χ^dom ρ_{k,0} K^{(3.7)}(1−χ_{Z''})` in the ORIGINAL variables (translation `ψ'' = ψ̃−ψ⁰` undone), `I'' = I∖𝒥` | MISSING | `removedKernel` (`R/RRemovedKernel.lean`) divides by `remDen`; no `keptKernel5` |
| `ρ_{k,0}(Z) ≤ e^{-γ₅}` on `1−χ_{Z''}` (Lemma III.5.3 (e)) | PARTIAL | `RhoZero`, `RhoZeroRestricted` (`rhoZeroRestricted_eq_mul`), `smallFactor_five_ripe` |
| Window volumes ≤ 1, `ψ_k` on `Z^c_0∩Ω^c_k` spanning tree (`3δ_k` balls) | LANDED | `outPartMeasure_chiTilde_le`, `tree_block_factor_le`, `volume_zeroCutoff_le` |
| (S3) structure: `K'' ≥ 0` Borel, `g`-free, `b''` real/analytic/local/covariant, support in `χ^dom`, (S5) | MISSING for K1/K2 | `KeptData` fields `b_supp, rot_K, rot_b, euclid_*` are assumptions; no `KeptDatum` built from `K^{(ϰ)}`, `b^{pre}` |
| Assembly `KerBound … (κ^pre − C_R λ̂^{2d+1} + γ)` incl. `L_res ≤ C_R λ^{2d+1}` | PARTIAL | `RRemovedLres.lean` `lres_at_scale`, `CR_le_A2_pow_of_lam0` |

## 2. Reused from the removed lane unchanged
`absW_quiet_le_action`; `exists_regroup_shell`, `exists_window_hid`; `lintegral_gauss_coords_eq`, `window_node_integral_eq_of_history`; `removedKernel_kerBound_of_window` (steps (1)–(4): Fubini order, volumes, core, exponent arithmetic `removed_exponent_le`) for ϰ₄, ϰ₅ with `γ` in place of `0`; `removed_quotient_le_of_history` for ϰ₄, ϰ₅; `lres_at_scale`; `hcore_of_anc`; `lf4R_removed_of_flow(_hist)` is the removed-lane consumer, not needed.
Differs: ϰ₁–ϰ₃ do not divide by `∫ρ_{k,0}` (no (2.58′), no `remDen`); ϰ₁ uses `½𝒢^♮` for a Gaussian normalization; ϰ₂, ϰ₃ drop `𝒢^♮` (`𝒜_win ≥ 0`, i.e. `quietRest_le_exp` suffices); ϰ₅ keeps `ρ_{k,0}` in the numerator and the original variables; the output differs by the smallness `e^{-γ_i}` and the labels `(ϰ, C_dec=5, γ)`.

## 3. Design caveat (from W944)
`window_node_integral_eq_of_history` integrates `gaussProd` only; `𝒜_win` depends on the node variables. For ϰ₂, ϰ₃ the action is only bounded (`≥ 0`), so the Gaussian-only integral suffices there; ϰ₁ likewise (`e^{-𝒜}≤1`). For ϰ₄, ϰ₅ (and rem) the per-configuration identity is needed (LF4R §8.5).

## 4. New statements in dependency order (Lean signatures as comments)
1. `-- theorem smallFactor_ge_setting (P : SmallFactorPar) (hP : P.A3 = S.A3' ∧ P.lamHat = S.lam k) (i) : 2*S.A3'*S.lam k^S.pR ≤ P.gamma i - Real.log (cDec i)`  (0.3).
2. `-- theorem windowKernel_le_gauss_gamma (i : Fin 4) … : ∫ over J, ψ_k↾Z₀ of K^{(ϰ_i)} e^{Re b} ≤ exp(…−γ_i)`  for ϰ₁..ϰ₃ (Lemma III.5.3 (a)–(c) + `window_node_integral_eq_of_history` + (2.8)).
3. `-- theorem keptKernel_{one..four}_kerBound (…) : KerBound (localHistory) k ker (κ^pre − C_R λ^{2d+1} + γ_i)`  assembling 2, `removedKernel_kerBound_of_window` steps, `lres_at_scale`.
4. `-- theorem keptKernel_five_kerBound`  as 3 with `ρ_{k,0}` kept (Lemma III.5.3 (e), `rhoZeroRestricted_eq_mul`), needs `hquot`.
5. `-- def/theorem keptDatum (k a ϰ) : KeptDatum N R a k` with `Ikeep ⊇ IsMsFluctVar` and the (S3) structure clauses; `-- theorem keptData_of_outcomes : KeptData k0 geo cs N κ lamHat` with `bound` from 3–4 and `gam_ge` from 1.
6. `-- theorem lf4K (hκ-pin : D4Pin …) : ∀ ripe kept Z, KeptData.bound`, then `rg_ripe_of_kappaK` closes (b).
Order of risk: 5 (new definitions: ask for approval), 4 (needs `hquot`), 2 (new integrals), 1, 3.

Status W950: item 1 LANDED (`smallFactor_ge_setting`, `R/KeptOutcomeGamma.lean`); shared core `window_lintegral_le_exp` factored out of `removedKernel_kerBound_of_window` (`R/RRemovedWindow.lean`, with the gain `γ`).
Item 3 for ϰ₁–ϰ₃ LANDED as `keptKernel_{one,two,three}_kerBound` (`R/KeptOutcomeWindow.lean`, kernel = `outcomeKernel`), with the window inputs `Θ, hid, hsupp, hbw, hfrac(Fr+γ), hcore, hvol` still NAMED (as in the removed lane).
Item 2 open: `hid`/`hsupp`/`hfrac` for `F = K^pre·weight` with the `e^{-γ_i}` gain (`exists_window_hid` is specific to `remDen`/`hquot`; the kept instance needs its own Gaussian-chain instance and Lemma III.5.3 (a)–(c)).
