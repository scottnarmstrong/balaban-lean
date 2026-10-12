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
