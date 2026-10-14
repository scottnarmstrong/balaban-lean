# ROOTASM2 — top-level skeleton of Root-F and the status of each node (W777, reading task, 2026-10-14)

**PROVED (scope).** Worktree `w777-rootf-assembly-plan` from main `697b2048`. Read: the frozen root `Frozen/Roots/LogPartitionMultiscale.lean`, ROOTASM, SMALLTORUS, UNITH, FINALPHYS, BASEPLAN (to W774), GENCLASS, `docs/BLOCKERS.md`, `docs/PROGRESS.md`, `LF-ARCHITECTURE.md` §1.2, §3.7 (LF-3..LF-8), and the landed files named below. No Lean was edited or built. Status words: LANDED = a declaration exists on main (name given); CONDITIONAL = declaration exists with open hypotheses (named); OPEN = no declaration; BLOCKED n = needs blocker n of `docs/BLOCKERS.md`. Sizes are the sizes of the cited notes unless marked (mine).

## 1. The skeleton (Lean-like; names are proposals)

Notation: `Cl(T,ℓ,R)` = the five single-torus clauses of the root (support, locality, analyticity on `‖g‖₁<R`, bound on `‖g‖₁≤R/2`, log identity on `‖g‖₁<R`), as in `Correlations/Clauses.lean:RootFTorusClauses` (R = 1 there).

* **A0 `rootF_of_e0` (reduction to `h=e₀`).** `Cl(T⁰,ℓ,√N)` at `h=e₀`, for all `ℓ` divisible by `M L^{kf+1}`, plus agreement ⇒ the root at every unit `h`. Used: `rootF_clauses_unitField`, `rootF_clauses_transfer` (`Inhabited/RootRotation.lean`; the bound constant becomes `√N c₉`, so run the e₀ chain with `c₉/√N`).
* **A1 `rootParams` (constants).** `δ` from `d` only; for `κ,c₉`: `L≥6` (so `5<N₁=qL`, `L∣N₁`), `M=L^{m₁+1}`, `β₀`, tower decay `λ≥c₁(d,L)κ`, amplitude `B e^λ ≤ c₉ L^{-j((d-2)/2+δ)}`. Alternative with `L=3`: `m₀=2`, `N₁=qL²` (SMALLTORUS T1).
* **A2 `rootTorus` (torus arithmetic).** `ℓ=q M L^{kf+1}` is `CTorus d L N₁ m₁ K` with `N₁=q L^{kf+2-K}` at each output `K≤kf+1`; divisibilities and `5<N₁`.
* **A3 `baseStep` (scale 1).** For every admissible torus (smallest included), `Z(g)=∫ρ₁`, `ρ₁` in the scale-1 small-field and large-field classes (`IsSFFamily2`, `IsRep2` at `k=1`), data `(β₁,ν₁,z₁,E₁,𝓔¹,𝓜¹)` (BASEPLAN OUT-1). Regime `kf=0` is A7.
* **A4 `classStep` (scale k→k+1, whole torus, general class).** `ρ_k∈ℛ_k`(small field `IsSFFamily2` + large field `IsRep2`) ⇒ `ρ_{k+1}=R S T ρ_k∈ℛ_{k+1}`, `∫ρ_{k+1}=c ∫ρ_k`, with the new scale-`k+1` terms `E0,M0` (zero-class step) plus transported old terms. Split: A4a small-field step with inherited terms (GENCLASS T3); A4b large-field step LF-3/LF-4/LF-5 (flip of the ν-free to complete backgrounds at `k₀`).
* **A5 `flow` (induction).** `∀ k ≤ kf: ρ_k∈ℛ_k` by A3 and A4, constants from one global RG solution (P4 Prop 5.1, `Flow/RG*.lean`); `kf=kStop` with the scale clause.
* **A6 `lastIntegral` (scale kf+1).** For `ρ_{kf}`: `∫ρ_{kf}=exp[-E|𝕋|+ℱ_{kf+1}(h,g)+𝓡^{kf+1}(h,g)+𝓟^{kf+1}(g)]`, `ℱ=⟨g,h⟩+Σ_{j≤kf}⟨g,ℳ^{(j)}⟩+Σ_n⟨g,ℳ_n^{(kf+1)}⟩`, all terms localized, analytic on `‖g‖₁<R`, with the `𝓟` bound `β^{-2}e^{-2κd}` (P7 §4, P9 (4.4)–(4.6)).
* **A7 `lastIntegral_kf0`.** The same for `ρ₀` directly (`ν>7/(8L²)`): sector decomposition, polymer gas.
* **A8 `logIdentity` (F3, conversion).** `log(Z(g)/Z(0))=⟨g,h⟩+Σ_j Σ_x Σ_X ⟨g(x),T_j(x,X;g)⟩` on `‖g‖₁<R`: with `f(X;g)-f(X;0)=Σ_{x∈X}⟨g(x),∫₀¹∂_{g(x)}f(X;tg)dt⟩`, `T_j(x,X;g)=Σ_{T′:sitesOf T′=X}…` for `j≤kf` (from A4 terms) and the `ℳ_n^{(kf+1)}`, `𝓡,𝓟` increments at `j=kf+1`; principal branch fixed by the exponential identity and `Z(g)/Z(0)→1`.
* **A9 `bounds` (rate and amplitude).** `‖T_j‖≤c₉L^{-j((d-2)/2+δ)}e^{-κ|X|/(ML^j)^d}` on `‖g‖₁≤R/2`: tree length → site count (`rootRate_of_sizeJ`), Cauchy in one source variable (radius 1/2), amplitude per scale from the class bound H7, `𝓟` arithmetic `β_{kf}^{-2}≤c₉L^{-(kf+1)((d-2)/2+δ)}`.
* **A10 `support_locality_analytic`.** Support (`x∈X`, `IsPolymer` of side `ML^j`, `j∈[1,kf+1]`); locality on `g|_X` for all `g,g′` (restriction extension, ROOTASM T3 (C)); analyticity on the open ball (chart inclusion at `q=1`).
* **A11 `twoTorus`.** `T^ℓ=T^{ℓ′}` on images of `A` in the box `|y_μ|<min(ℓ,ℓ′)/4`: each ingredient of A3–A6 transported between two tori, then the nonwinding neighbourhood of `A` of size `M L^j` inside the box (blocker 7 on the reading).
* **A12 `rootF`.** `logPartition_multiscale` from A0–A2 at `h=e₀` and A5–A11.

## 2. Status of each node

| Node | Status | Landed theorems / open hypotheses / blocker |
|---|---|---|
| A0 reduction | LANDED | `rootF_clauses_unitField`, `rootF_clauses_transfer`, `partitionFunction_rot`, `sum_norm_rotSource_le`. The e₀ chain must supply analyticity and the log identity on radius `√N`, the bound on `√N/2` (UNITH route A: no change in the step; the step evaluates at `g/β`). |
| A1 constants | OPEN | Needs the tower with free `κ` and `L≥6`: `StepTowerThetaG d L N κmin`, `stepPieces_jointG` (landed, `R.m₀=1`, odd `L`); the selectable-decay budget and the choice `L≥6` against the numerical bounds of the general tower are not packaged (SMALLTORUS T3 OPEN 3; status of the general numerics not re-checked here). |
| A2 torus arithmetic | OPEN | `rootTorusParameters` (≤100). Landed: `CTorus` equalities `Localization/Cover.lean`, `torusSide_ge`, `dgSetting_lv(G)`. |
| A3 base step | BLOCKED 1, 2, 6 | Landed pieces (`LargeField/Base/`): `baseRetained_disintegrate` (S1), `baseRecord_good_region` (S2), `baseChartIntegral_retained` (S3), `baseCutoffTransfer` (T2, needs `BaseCutoffMargins`), `baseFootprint_margin_of_cutoff_of_bondCross` (T1, CONDITIONAL on `bondCross`), G2 pointwise part, `baseDGSetting_exists`, `baseConstrainedCov_analytic/_one`, `BasePhysicalDensity` (`∫ρ₁=partitionFunction`). OPEN: G1 full H7 discs (obstruction `|t_Q|<e^{κ₁}`), G3, G4 (blocker 6), G5, R1, R2 (blocker 2), R3, L1–L4 (blocker 1 for `P₁≠∅`). BASEPLAN: ~7k lines beyond landed. |
| A4a small-field step | CONDITIONAL / OPEN | Landed: `prop26C_class(_of_activity)`, `exists_analyticAt_TstepC_of_analyticAt_class`, `thm31g_Eu_on`, `thm31h_on`, `physical_directTerms_eta(_scaled)`, `eterm_locInt`; zero class at the tower: `stepIdentity_zeroClass_fibre_fromTower` (now landed in `Inhabited/StepIdentityFibreFamilies.lean`; ROOTASM's REFUTED note is out of date), `stepPieces_joint(G)`. OPEN: GENCLASS T4 leaves 1–9 (12–24k lines); needs local generators (BLOCKED 6), reality/symmetry/H5, uniform bounds in `k`. |
| A4b large-field step | BLOCKED 2, 3, 4 | Large-field machinery 45% (`LargeField/`, `Def7v2Class`, R operation); LF-3 (blocker 2 at `k₀`, blocker 3 for inherited boundary terms), LF-4, LF-5 gas (blocker 4). No theorem of the step itself. |
| A5 flow | OPEN | Landed: `kStop`, `kStop_spec/_min`, `massLe_of_lt_kStop`, scale clause (`Flow/StopIndex.lean`), RG equations (`Flow/RG*`); induction itself is OPEN (needs A3, A4). |
| A6 last integral | BLOCKED 5 (+1) | Landed (`Green/Final*`): `taggedGfin_final`, `taggedCfin_analyticOnNhd`, `abstract_expansion_taggedCfin_final`, `taggedCfin_isUnit_near_one`, `taggedCfin_sq_mul_final_near_one`, connected support `coef_taggedCfin_final_eq_zero_of_separated`. REFUTED: invertibility of `taggedCfin` on polydiscs about 0. OPEN: FINALPHYS L1 (250), L3 localized determinant (another parametrization), L4 (2×290), L5 (250), L7 (2×290), L8 physical joins (Hessian, cutoff coverage, complex chart, nonempty large-field region); item 18 of the author. |
| A7 `kf=0` | BLOCKED 1 | CONDITIONAL: `rootF_kf0_partial_of_oneScaleInput` (`Correlations/KF0RootFPartial.lean`, hypothesis `KF0OneScaleInput`: local analytic `p_ℓ(X;g)` on blocks of side `ML`, exponential identity); `KF0AllGoodGas`, `KF0AllPlusGas`; sector with reversed spins OPEN. |
| A8 logarithm | OPEN (generic part LANDED) | Landed: `log_partition_eq_of_exp` and `KF0Cauchy` lemmas (`∫₀¹∂f(tg)dt`, model independent), `re_partitionFunction_div_pos`. OPEN: identity of `Z(g)/Z(0)` with the exponential from A5/A6 (`F0C_eq_pair_zeroClass`, `-Eppp nU`, `FcompAtC`, subtraction of the zero-source exponent), principal branch on the ball. |
| A9 bounds | PARTLY LANDED | `rootRate_of_sizeJ`, `rootRate_of_dExt` (`Fluctuation/RootSupportBridge.lean`); `rootTermFamily_obs_prefactor_fromTowerG(_rho)` and `rootTermFamily_obs_birthScale_fromTowerG` (new terms of one step at their birth scale, 3,3,2 and general `d,L,N`). OPEN: amplitude of old terms at later scales (the class bound at scale `j` equals the birth bound), constant matching `B e^λ≤c₉L^{…}`, `𝓟` arithmetic, final-scale terms (A6). |
| A10 support, locality, analyticity | PARTLY LANDED | Landed: `sitesOf_isPolymer`, `mem_sitesOf_of_rootCube_blockIndex`, `markFibre_sitesOf`, `rootTermFamily_of_cubeFamily(_rho)`, `obsFamily_full_fromTower`, `isLocExp_of_coeffFamily_renTheta_tower`, sharp (raw-Y) locality `vblock_expansion_hat_rawY`, `evDec_local_rawY`. OPEN: the restriction-based global locality (ROOTASM leaf 4, ≤280), chart inclusion at `q=1` for the packaged families across all `(x,i)`, cross-step transport of the site sets (fine `CTorus` types), analyticity of the final-scale and large-field terms. |
| A11 two tori | PARTLY LANDED; blocker 7 | Landed per ingredient: `obsCoeffParam_twoTorus_fromTowerG(_source)`, `e0Coeff_twoTorus_fromTowerG`, `gsumCoeff_e1_twoTorus_fromTowerG(_large)`, `detTerm_twoTorus_fromTowerG`, `evDec_rootBlock_twoTorus`, `markedOutDec_twoTorus`, `kf0CR_torus_eq`. OPEN: cut comparison of the background (`decBg_component_unique`, TORUSCOH3), TORUSCOH2 transport across steps, final-scale L7, the nonwinding neighbourhood versus the box `min(ℓ,ℓ′)/4` (BLOCKED 7, interpretation). |
| A12 `rootF` | OPEN | Consumer already landed: `rootC_of_rootFAndC1Star` (`Correlations/RootCFromFlow.lean`) takes the clauses in the form `RootFClauses`. |

Counts (14 rows, A4 split into A4a, A4b; each row by its first state): LANDED 1 (A0); PARTLY LANDED 3 (A9, A10, A11); CONDITIONAL 2 (A4a, A7); BLOCKED 3 (A3, A4b, A6); OPEN 5 (A1, A2, A5, A8, A12). Blockers touched: 1 (A3, A7), 2 (A3, A4b), 3, 4 (A4b), 5 (A6), 6 (A3, A4a), 7 (A11).

## 3. Critical path

**OPEN (my reading).** `A3 base` (blockers 1, 2, 6; ~7k lines) → `A4 classStep` (A4a blocker 6; A4b blockers 2, 3, 4; 12–24k lines for A4a alone) → `A5 flow` → `A6 lastIntegral` (blocker 5, then physical joins) → `A8 logIdentity` → `A9, A10, A11` → `A12`. A7 is a parallel branch (blocker 1) that does not enter the main flow. The two nodes that no amount of Lean work removes are blocker 1 (A3, A7) and blockers 3, 4 (A4b): author answers (items 17, 14, 16). Blocker 5 (item 18) fixes the cover for A6. Blocker 2 enters twice (A3 regime A, A4b at `k₀`). The longest unblocked chain is A4a (blocker 6 has a working workaround), then A8 and A9.

## 4. Nodes that can be done now (no blocker)

1. `rootTorusParameters` (A2, ≤100) and the `m₀=2` cover generalization (≤180, SMALLTORUS OPEN 1–2).
2. Definition-free fixed-torus regrouping `U(x,X,g)` from a cube family, restriction extension, rate `B e^λ e^{-κ|X|/a^d}` (ROOTASM OPEN 4, ≤280); packaging of the observable families across all `(x,i)` with chart inclusion at `q=1` (ROOTASM T4, ~250, mine).
3. GENCLASS leaves 1–3: `StepOldTermSplit` (150–220), `StepClassPath` (180–260), `StepPhysicalActivityBridge` (220–290).
4. BASEPLAN: T1 statement, G2 remainder (non-local α part waits for G4), base cut family S+T stages (done to T2); G1 disc obstruction (proof or sharper statement).
5. FINALPHYS: L1 (250, only if E is absorbed), the near-1 invertibility consequences (`taggedCfin_isUnit_near_one` landed), part (i) of L4 `gaussian_change_cut` (~290), L3 after another parametrization (centre at `s=1`, ~280).
6. A8 generic part: principal-log lemma on the source ball from an exponential identity with `Z(0)` normalization, in a model-free form (~150, mine); A9 arithmetic of `𝓟` against `c₉L^{-(kf+1)((d-2)/2+δ)}` (~100, mine).
7. General `L≥6` tower consumers (`ObsFamilyJoint`, `StepTowerScale` moves to general `d,L,N` with 3,3,2 corollaries; several leaves of ≤260).

## 5. Root-F conditional on blockers 1–4 (planning device only)

**OPEN (not a frozen statement).** With answers to items 17, 13, 14, 16 the following would be hypotheses of `rootF_of_blockers_1_4`, each a proposition about the objects of the class, never a step of its proof inside the frozen statement:
* `hBase`: A3 for all tori and both regimes (blockers 1, 2): `∃ ρ₁ ∈ ℛ₁` with `∫ρ₁=Z(g)` and OUT-1 (a)–(d). Also `hBase0`: A7 for `ν>7/(8L²)` (blocker 1).
* `hLF`: A4b: the large-field class is preserved by one step for `1≤k<kf`, with `R` on covered windows and the switch at `k₀` (blockers 2, 3, 4), including the nonempty boundary and crossing terms of Theorem 3.1.
* Still to be proved after 1–4, not hypotheses: A4a (blocker 6, workaround in progress), A6 (blocker 5, item 18), A11 (blocker 7). So even the conditional theorem has `hLast` for A6 and, until blocker 6 closes, `hLocalGen` for A4a. The conditional theorem would then be: `hBase ∧ hStep(a,b) ∧ hLast ∧ hTwoTorus → ∃ T, Cl(T,ℓ,1) ∧ agreement` with `kf=kStop`, exactly the shape of `RootFClauses` in `Correlations/Clauses.lean`. Each hypothesis needs a `Nonempty` witness (rule 10), which the present conditional files (`KF0OneScaleInput`) do not yet carry.

**Orchestrator correction (2026-10-14).** Some "do now" items above are already landed: `rootTorusParameters`
(A2; `Fluctuation/RootTorusParameters.lean`, e28ef20b), GENCLASS leaves 1–3 (`StepOldTermSplit`, `StepClassPath`,
`StepPhysicalActivityBridge`, W608), last-integral L1 (W759, `*_of_coercive`, `*_finalPert`), the regrouping
(`rootTermFamily_of_cubeFamily`, `pairing_of_regroup`), and the general-L towers (W709–W732). Since this note was
written: blocker 6's composition is lossless (W763, W772, W775) and its background engine runs on `localB` (W771);
the first step has the parametrix on the full discs (W773, W774). Open "do now" items: the principal logarithm
on the source ball (A8), the large-field bound arithmetic (A9), L3 with the cut family centred at s = 1 (A6).

## W786 status (A9 arithmetic, 2026-10-14)
`Balaban/Inhabited/RootBoundsArith.lean`, all PROVED. (1) `rootBound_of_perTerm` (+ `amplitude_le`): per-term bound `C(C' L^e β^{-q})L^{-je}e^λ E` gives `c₉ L^{-je} E` once `β ≥ (C C' e^λ L^e/c₉)^{1/q}` (`e=(d-2)/2+δ`, `q=e/(d-2)`, as in `rootTermFamily_obs_birthScale_fromTowerG_rho`).
(2) `betaK_inv_sq_le`: `(β_k²)⁻¹ ≤ c₉ L^{-(k+1)((d-2)/2+δ)}` for every `k` if `0≤δ≤(d-2)/2` and `L^{(d-2)/2+δ} ≤ c₉β₀²`; the stopping condition on `k_f` is not used.
(3) `norm_kf0Deriv_le_two`: Cauchy in one source variable at radius 1/2: bound `B` on the unit ball gives `2B` for `∫₀¹∂F(tg)dt` (landed `norm_kf0Deriv_le` has 4B).

## W797 status (A1 rootParams, 2026-10-14)
`Balaban/Inhabited/RootParams.lean`: `exists_rootParams` (Root-F order: δ, κ, c₉, L M, tower T, β₀, ν h, kf), `exists_tower_blockSize`, `exists_kf_scale`. PROVED, no hypotheses beyond 3 ≤ d, 2 ≤ N.
Constraints: δ=(d-2)/8 (δ ≤ (d-2)/2 for `betaK_inv_sq_le`; δ < s(d-2), s=1/4, for the birth-scale bound); L=7 (odd, ≥ 6, 5 < L^{m₀}, m₀=1); decay c₁κ ≤ (3/2)κ_dec; M=L^{m₁+1} with hMB, hMκ of W787 at max κ 1, obtained from `large_block` by raising κ_min; β₀ for `rootBound_of_perTerm`, `cutConst_mul_lt_of_large`, `betaK_inv_sq_le` (L^e ≤ c₉β₀²); kf from ν.
UNVERIFIED: the amplitude and cut constants C, C', B, p, R are quantified (positive), not read off the landed tower bounds; the window `StepTowerG.bgR0_le_minSep` holds for any T; γ ≤ 1/4 (chart test) is independent of δ (α = (d-2)/2 - γ), not linked; kf here is any valid index, not `kStop`.
