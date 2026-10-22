# Balaban — agent instructions

Formalization in Lean 4 + Mathlib of T. Balaban's renormalization-group analysis of the
low-temperature classical `O(N)` model on `ℤ^d` (hard spins, `d ≥ 3`, `N ≥ 2`; the 3d classical
Heisenberg model is `N = d = 3`), from the series P1–P9 (1995–1999). Requested by Roland
Bauerschmidt; author and approver: Scott Armstrong. The orchestrator is a Claude session; workers
receive bounded briefs in `orchestration/briefs/`.

## Layout

- `sources/` — the papers (keys and DOIs in `review/SOURCES.md`).
- `review/` — the review phase: per-paper reviews `review/papers/`, `BIG_PICTURE.md`,
  `FORMALIZATION_ROADMAP.md` (v2, the plan), `LIBRARY.md`, `QC_LOG.md`, `ROLAND_ANSWERS.md`.
- `notes/` — campaign notes: `ERRATA.md` (errata ledger), `phase0/` (surface drafts, audits,
  approval packets), questions for Roland.
- `Balaban/` — Lean sources. `Balaban/Frozen/` holds frozen declarations only (one public
  declaration per file, each owned by exactly one entry of `frozen/manifest.json`).
- `frozen/` — `manifest.json`, `APPROVALS.md` (author approvals and rulings, with dates).
- `scripts/` — `check_frozen_anchors.py`, `anchor_abi.py`, `check_lean_modules.py`,
  `use_local_cache.py`.
- `orchestration/` — `LEDGER.md`, `briefs/`, `logs/`.

## Current phase

**Phase 0 (roadmap §8): complete on 2026-10-11.** Surface v1 approved by the author ("approve all
defaults", `frozen/APPROVALS.md#surface-v1`) and frozen: eight definitions `SEALED` (Def-1 model,
Def-2 `IsPolymer`) and two roots `DRAFT_SORRY`:
- Root-F `Balaban.logPartition_multiscale` (`Balaban/Frozen/Roots/LogPartitionMultiscale.lean`);
- Root-C `Balaban.lowTemperature_correlations` (`Balaban/Frozen/Roots/LowTemperatureCorrelations.lean`).
Their providers `Balaban/Provider/*.lean` are quarantined: nothing but the frozen root may import a
provider, and nothing may import a root, until the root is sealed.

**Next: phase 1** — the source dependency graph from the frozen roots; Lean work packages W1–W6
(roadmap §8); the large-field reconstruction document on paper (roadmap §4.5).

## Author rulings

- **surface-v1 (2026-10-11):** decisions S0-Q01 to S0-Q10 and m1–m4 of
  `notes/phase0/surface-v1-for-approval.md` at their recommended defaults (`frozen/APPROVALS.md`).
- **LF rulings 1–2 (2026-10-11, approved):** (1) the reconstructed large-field bookkeeping (A′) of
  `notes/phase1/LF-ARCHITECTURE.md` v4 §7 replaces P5–P7's H6, counter K, κ_{k,n} and admissibility
  by the budget invariant (H6′) with spines, clocks and three-way window states (pre-window /
  pending / active); the trigger K = 0 of R by ripeness of an active covered window with merge strips;
  R is generalized to windows of up to ν_max ≍ λ^{p₂} merged pieces; components are classes of
  "distance < ω_k cubes" — approved for Def-7, LF-2 and LF-4. (2) Def-7 design: a predicate `IsRep_k`
  on representations (𝓡_k = densities that have one), deterministic bookkeeping on the a-priori
  sequence λ̂, (D5) required at every scale j ≤ k, LF-4 in existential form — approved.
- **Q13 background convention (2026-10-12, Scott):** "rule out fully massive; hybrid pending
  factorization." (1) The fully massive variant A0 is ruled out: no mass in the sharp large-field
  characteristic functions and none in the reference of the R operation (both stay massless below
  k₀, as in P5–P7); the landed massless reference code stands. (2) Scheme A (approved 2026-10-13:
  complete backgrounds for the small-field class at every scale, field-free backgrounds inside the
  large-field operators below k₀, an SF→LF interface) remains the recorded scheme. (3) The hybrid
  A0′ (as A, but the main action and the inherited small-field terms of a new large-field region
  are evaluated at the complete background, with no interface) replaces A if and when the exact
  factorization `hybrid_sf_factorization` is proved (`notes/phase1/Q13-HYBRID.md`,
  `Q13-FACTOR.md`). Until then: write nothing specific to A's interface and nothing specific to
  the hybrid (in particular no split of `OpConsts.mu`); everything else proceeds.

- **Rulings R2, R4, R5, R6 (2026-10-17, Scott: "go with your recs").** Plan B rulings that change or add
  landed definitions, approved as recommended in `notes/phase1/PLAN-B.md`:
  (R2) route R-YM′ for blocker 2 (`notes/phase1/Q13-YM.md` §5 leaves 1, 4, 5, 6; `notes/phase1/astra/RADIUS.md`;
  W973 handoff item 3): three masses in `OpConsts` (action, background, cutoff) — this supersedes the clause
  "no split of `OpConsts.mu`" of the Q13 ruling, whose points (1) (no mass in the sharp large-field
  characteristic functions or in the reference of R below k₀) stand; the extended direction stencil
  (`Characteristic/Reg.lean`, `Stencil.lean`, `chiY`); a direction clause in `ChiDomProp`/`ChiDomAt` for
  k > k₀; a complex-source kernel interface (`KerBound`) and a holomorphic physical-action factor.
  (R4) the representation of R's output as a gas, W968 proposal (`notes/phase1/LF4R-PLAN.md`, W968 lines):
  heavy objects are the removed clusters; couplings decorated by the removed members they meet,
  b_X(S) = ℬ(X,𝔸′∪S) − ℬ̂(X;𝔸′) + ℬ′_X(S); operator form over the internal variables with the reference
  measures of (H-op); the pointwise bound (3.10″) replaces `hwin`/`hτ`; new definitions: complex R on
  ℂ-densities, ρ(𝔸,σ) on the Def-7 carrier, ℬ′ of P7 (3.22)–(3.25), the (H-op) measures.
  (R5) the clause `StepData.b_vac`: b_k = b⁰_k − (E_k|Z′∖Z_k∖Ω_{k+1}|_k + E″_k|Ω_{k+1}∖Ω″_{k+1}|_k +
  E‴_k|Ω″_{k+1}∩Z_{k+1}|_k), with b⁰_k bounded by constants free of E (LF4R-PLAN, W968 vacuum).
  (R6) the inherited levels of the small-field class live on domains frozen at their birth mass
  (the W868 design), replacing the current-mass `completeXiDom` in the induction; the v2-to-I6 bridge
  is re-proved for the new carrier (`notes/phase1/astra/SFFAM.md` Part 3).
  Every new or changed definition lands with an independent audit against its source.

- **Rulings R8, CRotE, R7, R5′ (2026-10-18, Scott: "go with your recs on R8 and the others").** Approved as
  recommended in `notes/phase1/PLAN-B.md`:
  (R8) the step's mark, determinant and activity objects (`decMarkG`, `decMarkCorr`, `decMarkCorrTerm`,
  `e1MarkGParamG`, `DetExpansionLocC`, `DirectTerms`, `physParam`/`physV`) are made generic in an explicit
  background generating set, the current objects being the instance `S.G'`, so that the new level's terms are
  computed with the local generating set of each polymer (P3 pp. 78–79, (4.44)–(4.47); P6 §4.1–4.4).
  (CRotE) the defect of `Def6v2.CRotE` (`notes/phase1/AUDIT-DEFS-1018.md`) is repaired now as in
  `notes/phase1/CROTE.md` §4: the four complex-rotation call sites use the real clause `rotE` with a Cayley
  path for bounded-entry matrices (`rotE_of_near`, `exists_cay_path_near`, `rotE_of_cay_path`), and every
  `hCR`/`CRotE` hypothesis is removed; `CRotE` is then deleted if nothing uses it.
  (R7) the physical base carrier of `BaseSmallFieldInput` is specialized to M = K = 1 with
  `a := H.localHistory 1 1 1 Z'` and a primary field `Kphys` on the history, component, base record, raw
  collar spins, complex source and local variables (W1009 handoff, "Exact carrier change"), with an
  extensionality field for the raw sites read; the source-free real factor and the per-witness complex
  factorization become theorems on their nonvanishing domain, the source reindexing an explicit lemma, and the
  carrier's exact definition receives the independent source audit before it is populated.
  (R5′) the first region of `StepData.b_vac` is that of P6 (3.2): E_k|Z_k^c ∖ Ω_{k+1}|_k (replacing
  E_k|Z′∖Z_k∖Ω_{k+1}|_k); the other two regions are unchanged (W1062: `stepVacuumVolume`).
- **Rulings R7′, R9, R-N₁, R10, R11 (2026-10-19, Scott: "Yes on all five decisions").** Approved as recommended in
  `notes/phase1/PLAN-B.md`:
  (R7′) the physical base carrier `BaseSmallFieldInput` (R7, `Kphys`) is stated at the class's general block
  constant M and torus horizon K (content of the corrected `Kphys` unchanged; only the geometry parameters freed),
  so that `BasePreStepInput`/`BaseFlatStepInput` can be populated from it.
  (R9) `sides L K nK j := if j ≤ K then nK * L^(K-j) else 1` (`LargeField/Def7.lean`): above the torus horizon the
  torus is a point, as in the source; `hsub` weakened to `K < j → n j = 1` in `ImageHist`, `ImageHistBook`,
  `QuietImage`; the fine torus is unchanged.
  (R-N₁) the small-field clauses of `D2SF2` and `SFFlat2` are required only on the Def-6 tori the class family reads,
  N₁ ∈ L^{m₀}ℕ₊ (`sfIdx`), instead of every N₁ ≥ 1.
  (R10) the first vacuum region of `stepVacuumTerm` is localized to the component: (Z_{k+1} ∖ Z_k) ∖ Ω_{k+1}
  (P6 (3.2) on the component; the object of R5′ on the component).
  (R11) a valid boundary-term domain (`FineValidAt`, `LargeField/Def7FineSize.lean`) is `Fluctuation.DjModFin` on the
  fine sets: nonempty, connected, containing or missing every hole, of finite modular size — π′-cubes are required
  only at its small-field sites, not at the hole sites; size, covers, `loc_hist`, the H7 domain and the bounds are
  unchanged, and every domain valid before stays valid.
- **Ruling R12 (2026-10-21, Scott: "yes, approve R12").** In the post-`R` form of the class (`D1Form2`,
  `LargeField/Def7v2Form.lean`), the term `postTerm2` of a history is zero whenever the history has a removal
  record `Rem_j ≠ ∅` at some scale `j ≤ k`; the history set and `IsComplete` are unchanged. Removed components
  are accounted for in `ℬ′` and `ℛ″` (P7 (3.26)–(3.29)); without the change the all-small-field term is counted
  n₀ ≥ 2 times (W1151 `two_le_card_empty_region`, audit `notes/phase1/REMOVAL-HIST.md`). This is the reading of
  LFR D-III.8 ("terms with zero operator are harmless").
- **Ruling R13 (2026-10-21, Scott: "approve R13"; amended form).** In the small-field class (`IsSF2`,
  `SFTermClausesStrong`, the generating-set clause of `SFNewLevelInput`) the generating set `Tm.gs j X` of a
  level-`j` term on the polymer `X` is the local set `𝔹_j(X⁺)`, where `X⁺` is `X` together with the `𝒞_j`-cubes of
  the neighbours `y + L^j e_μ` (`y ∈ X` aligned) that the irrelevant part reads; the step chain composes each
  inherited term on that set, and its cover set grows from `X ∪ □(y)` to `X⁺ ∪ □(y)`. The class domain reads the
  fields with the step's weights and background mass (`Def6.bgMass`). Source: P3 (4.4)–(4.6), P5 (2.10)–(2.11).
  Without it the class's own bound says nothing at the composed data and blocker 6's (A1)–(A5) cannot be
  derived (W1146, `notes/phase1/PLAN-B.md` "Ruling R13", `Fluctuation/OldTermClassDomain.lean`).
- **Ruling R13, implementation (2026-10-21, Scott: "approve all").** Two details of W1146s's implementation of R13
  are approved: the local set is `X̂ = hatSet m₀ j X`, `X` thickened by `⌊L/2⌋` cells of `𝒟_j` (it contains `X⁺`, is a
  union of cells and is invariant under the paving symmetries, which `X⁺` is not for even `L`); and the class term
  domain stays the birth-mass domain `birthXiDom` of ruling R6, the step's charts being put into it by the mass
  response, in place of the step's background mass (`notes/phase1/SPINE.md` "L5 R13 (W1146s)").
- **Ruling R14 (2026-10-21, Scott: "approve all").** The complex H7 cube domains `DeltaC`, `DeltaPrimeC`
  (`LargeField/Characteristic/Analytic.lean`) ask the lifted datum in `Ψ̃^c(ε, ε)` (`InDomainC G μ ε ε`) in place of
  the background theorem's union domain. As landed, the old-term datum input was false: a complex rotation of size
  `≥ 2ε` lies in the union domain (W1154b, `LFOldH7Refute`); the reader `deltaC_inUnionDomainC` is kept through
  `Ψ̃^c(ε, ε) ⊆ D` for `0 < ε ≤ c₁`, `μ L^{2q} ≤ 1`.
- **Ruling R15 (2026-10-21, Scott: "approve all").** At the cell `X = □(y)`, `irrelTorus` renormalizes only the
  polymers inside the box `B(y)` of radius `r_k = ⌊L^{m₀+m₁+k}/8⌋` fine sites around `y`:
  `ℰ_irrel(y,X) = ℰ(y,X) − A_{y,X} − 1[X ⊆ B(y)](T_X + Φ_{y,X}) + 1[X = □(y)] Σ_{X'∋y, X'⊆B(y)} (T_{X'} + Φ_{y,X'})`.
  Polymers in `B(y)` do not wind on any torus of the family, so the cell term agrees exactly between two tori; larger
  polymers keep their relevant parts and are small by size. The identity `Σ ℰ_irrel = ℰ`, the class and the
  infinite-volume renormalization conditions are unchanged (ORCH-A; `notes/phase1/PLAN-B.md` "Ruling R15 asked").
- **Ruling R16 (2026-10-21, Scott: "approve all").** In `D7Bdry2`, `D7Bdry2Post` the clauses `analytic` and `bound`
  of the large-field boundary terms are asked at the physical external field only (`hSetB hv`, as in the first
  version), not on the pinned ball `‖h' − h‖ < r_h`; the other (D7) clauses and the small-field domains (which keep
  the ball) are unchanged. Every reader uses (D7) at the physical field, and the whole build without the ball passes
  (ORCH-A, branch `orchA-r16`). `D7BdryBall` and `LFBdrySrcInput` are deleted; `lfStepInput_of_parts` loses `hBs`.
- **Ruling R17 (2026-10-21, Scott: "approve R17").** In the pre-`R` boundary-term records `D7Bdry`, `D7Bdry2`
  (clauses `analytic`, `bound`) the H7 domain is taken at `globalLHPre A.H M k`: the global history with the pre-`R`
  region `Z^pre_k` in place of `Z_k` at the top scale. At the top scale the cube tests' holes become `(𝕋_k ∖ Ω_k)^{∼3}`,
  the complement printed in P5 (1.36) (`Z^pre_k ⊇ Ω^c_k`: `Omega_compl_subset_Z0`, `Z0_subset_Zpre`); lower scales,
  `omegaCNb`, the post-`R` records and every localized-history user are unchanged, and with no removal at scale `k`
  the records coincide. Without it, at a history whose component of `Z^pre_{k+1}` is removed by `R^{(k+1)}`, no test reads
  `ψ_k` in the band outside the holes and `H7MixedDatumLoc2` is false (W1154d, `not_h7MixedDatumLoc2_of_site`). The
  transport across `R` (`d7Post_bound_of_avoid_of_gas`, `analytic_of_avoid`) splits off the labels within 3 cubes of
  a removed component, which go to the gas bound.
- **Ruling R18 (2026-10-21, Scott: "approve R18").** Ruling R-N₁ extended to the first version of the small-field
  class: in `Def6.IsSFFamily` the torus clause is asked only on the Def-6 tori the family reads, `L^{m₀} ∣ N₁`, and
  the renormalization conditions along those tori (`RenormCondAlong … torusSeq`), as `D2SF2`/`SFFlat2` already do.
  Without it the second version's read-tori family cannot be converted to the first version (`toLanded`), which the
  filed estimates of the cell label (`norm_filed_le_power`, the R15 label bounds) consume (ORCH-A, A1).
- **Ruling R19 (2026-10-21, Scott: "approve R19 and R20").** `irrelTorus` also subtracts the first-order variation of
  the external field, P1 Lemma 3.8 (3.104)'s second term `⟨v₂, ν(h·ψ₀)(x) − ν(h·ψ₀)(y)⟩`, which `aTermTorus` had merged
  into `a = v₁ + νv₂` (valid only for constant `h`): `A^h_{y,X} = Σ_{x ∈ X aligned} c_X(x) [(h·Ψ̂)(x) − (h·Ψ̂)(y)]`,
  `c_X(x) = ∂_h ℰ(y,X)(e,e)[blockDir x i₀]`. Its sum over the labels of the torus is zero, so `sum_irrelTorus_eq_Edens`
  and its consumers are unchanged; at constant `h` it is an irrelevant term `O(E₀σ³(ε/r)²)`. Without it the class
  chart's block-varying `h` (P3 (4.26)) leaves a first-order remainder that breaks P1 (3.128) (ORCH-A, A1; W1146u).
- **Ruling R20 (2026-10-21, Scott: "approve R19 and R20").** The torus independence of the small-field class
  (`Def6.TorusIndep`) is asked for pairs of read tori (`L^{m₀} ∣ N₁`, as R-N₁/R18), for polymers whose
  `c·L^{k+1+m₁'}`-thickening does not wind (the new terms read that thickening), and at fields in the class domain only
  (off it the step's choices are torus dependent). Root-F's quarter-box two-torus clause still follows under a constant
  condition recorded with the joint ties (ORCH-A, A1).
- **Ruling R21 (2026-10-21, Scott: "approve R21, R22 and R23").** The large-field boundary terms read the rescaled
  fluctuation, the field displacement `(β_j a)^{-1/2} ψ′`, not the raw Gaussian variable: P5 (1.25) bounds the raw
  variable on the kernels' support by `C_ψ p₀(β_j) ≫ 1`, while the analyticity domain (1.37) is `ε_{1,j} ≪ 1`, so read
  literally on the same variable the support leaves the domain where (D7) bounds the terms. With the rescaling the
  support gives `C_ψ δ_j`, and `C_ψ δ_j < ε_{1,j}` is a condition on the constants (ORCH-B, B3).
- **Ruling R22 (2026-10-21, Scott: "approve R21, R22 and R23").** In the pre-`R` records `D7Bdry`, `D7Bdry2` the
  top-scale `loc_hist` clause compares the pre-`R` objects, consistent with R17: agreement of `Z^pre_k ∩ X` and of the
  localized histories of all components of `Z^pre_k` meeting `X` (not only the post-`R` components). Without it a
  component removed by `R^{(k+1)}` can differ next to a label while every listed premise holds (W1154e, W1162).
- **Ruling R23 (2026-10-21, Scott: "approve R21, R22 and R23").** The first family of the support tests P5 (1.24)
  (`ChiDomProp`, `ChiNewProp`) includes the collar sites and collar bonds from `j = 0`, as P2's `Ψ̃` and `InPsiTilde`
  do; the Lean transcription had lost the collar, so the first step's mixed test (1.36) read the unit-lattice field
  on collar sites that no support clause constrained (exact counterexample by ORCH-B, B3).

Roland's answers (`review/ROLAND_ANSWERS.md`), binding on scope:
- (2026-10-11, batch 1) large fields are essential; hard spins with general `d ≥ 3`, `N ≥ 2`;
  finite volume on tori with bounds uniform in the volume, infinite volume only in the final
  correlation theorem; our own proofs of the Green's function estimates are encouraged.
- (2026-10-11, batch 2) λ large is needed (hard spins satisfy it); **any large-field mechanism that
  works is acceptable** (the bookkeeping of P5–P7, including the R operation, may be redefined);
  the repair of P6 Thm 4 (threshold frozen at `p₂(β_{k₀})`) is agreed; the step counter must be
  reconstructed; limits along tori suffice (no uniqueness); the forms of Root-F and Root-C are
  accepted; no known errata. Open: whether P9's constants may depend on `β` (Root-C assumes not).

## Hard rules

1. Every `.lean` file except `lakefile.lean` is a Lean module (`module` header, `public import`
   for the interface, `@[expose]` on source-facing definitions). No file over 10,000 lines
   (`scripts/check_lean_modules.py`).
2. No `axiom`, no unregistered `sorry`/`admit`, no `set_option maxHeartbeats` or other heartbeat
   overrides, no placeholder definitions, zero warnings in landed code.
3. Frozen files are read-only. A frozen declaration that looks wrong is reported to the
   orchestrator; it is never edited, and no premise is added to work around it.
4. Theorem hypotheses contain only source premises and typing data; a step of the proof is
   never a hypothesis. Definitions mean the source object on their whole carrier; an object
   defined as "the unique ..." is defined only after its `∃!` theorem is proved, and lands with
   a characterization theorem.
5. Candidate or probe `.lean` files never sit in the repository; use
   `/home/scott/Balaban-scratch/`.
6. **Machine limits (lemma.farm, shared).** The repository uses the `ocreg-throttled` toolchain
   (`elan override`), which caps simultaneous Lean compiles machine-wide. Run at most one
   `lake build` per worker, build only the modules you changed, never bypass the wrapper by
   calling a Lean binary directly, and never start extra sessions to go faster.
7. Commit only checked work; stage explicit paths; never rewrite history on `main`.
8. Before handoff, merge the current `main` into your branch and build the whole default target
   (`lake build`, not only your modules); declaration names must not clash with existing ones
   (search before naming). The orchestrator lands branches only with `scripts/land.sh`.
9. Never kill, stop or signal a process you did not start yourself: no `pkill`/`killall` by
   pattern, no `kill` of another PID. The machine is shared with other campaigns.
10. Every new structure, class or bundled `Prop` used as a theorem hypothesis lands together with a
   theorem proving it is inhabited (`Nonempty …`) for an admissible choice of parameters, unless the
   orchestrator records an exemption in the ledger. (A structure with contradictory fields makes every
   theorem about it vacuous.)

## Building

`python3 -I scripts/use_local_cache.py /home/scott/FroehlichSpencer` points Lake at an
already built Mathlib with the same pin (only Mathlib and its dependencies are taken from that
checkout's `.lake/packages`) (v4.35.0-rc2, Mathlib `065356127b1d`); elsewhere use
`lake exe cache get`. Then `lake build <Module>`.

## Reuse (survey before building infrastructure)

Public repositories by the author, usable as Lake dependencies or as sources to port:
- `scottnarmstrong/Frohlich-Spencer` (v4.35.0-rc2, modules, same Mathlib pin): Combes–Thomas
  resolvent bounds, lattice animals, Gaussian toolkit, Fourier on tori. Public clone
  `/home/scott/mining/Frohlich-Spencer` (commit `b47bc3d`); `/home/scott/FroehlichSpencer` is the
  author's private development mirror with the same layout.
- `scottnarmstrong/DOZZ` (v4.35.0-rc2, modules, same Mathlib pin): library `GaussianFields`.
- `scottnarmstrong/BKARForestFormula`: ported into this project as `Balaban/External/BKAR/`.
- **Private repositories may be copied too** (author, 2026-10-11: "I am very happy to expose all my
  private code"): e.g. `/home/scott/AVAnomalousRegularization-dev` (polydisc Cauchy estimates,
  `AVRegularity/External/`), `/home/scott/KPZ` (BKAR-based polymer expansions,
  `cumulants/Lean/Polymers/`), `/home/scott/EllipticRegularity`. **No attribution is required**
  (author: "it's all my code"). Do not add Lake dependencies on these repositories; copy.
Other local repositories with relevant material are listed in roadmap §7.2.
