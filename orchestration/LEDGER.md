# Orchestration ledger

| Date | Item | Status | Notes |
|---|---|---|---|
| 2026-10-11 | Phase 0 scaffold | done | toolchain v4.35.0-rc2, Mathlib 065356127b1d, checkers from FroehlichSpencer adapted to the `Balaban` namespace |
| 2026-10-11 | Draft Def-1, Def-2, Root-F, Root-C | superseded by freeze below | package `notes/phase0/surface-v1-for-approval.md` v1.2 (audit FAIL on v1.0 → fixed; re-audit: statements approved as written); code in `/home/scott/Balaban-scratch/p0/tree` |
| 2026-10-11 | Questions for Roland, batch 1 | ready to send | `notes/QUESTIONS-ROLAND-1.md` (roadmap 5–10, new 11–12) |
| 2026-10-11 | Errata ledger | done | `notes/ERRATA.md`, 231 rows (16 orchestrator-verified) |
| 2026-10-11 | Freeze surface v1 | done | approved "all defaults"; 8 definitions SEALED, Root-F and Root-C DRAFT_SORRY; guard, ABI, statement closure, module checks pass |
| 2026-10-11 | Roland answers 5–12 | recorded | `review/ROLAND_ANSWERS.md` batch 2; open: β-dependence of P9 constants |
| 2026-10-11 | Phase 1 start | in progress | `notes/phase1/PLAN.md`; documents D-LF, D-G, D-PE being written; briefs W1, W3a |
| 2026-10-11 | Agent cap | rule | author: at most 4 Sonnet + 1 Opus subagents, no sub-subagents |
| 2026-10-11 | W3a BKAR port | landed | `975347f` (55 files, modules, v4.35.0-rc2; proof-only repairs `dif_pos/dif_neg → dite_eq_left/right`, `if_pos/if_neg → ite_eq_left/right`, one trailing `rfl`; statements unchanged, checked by diff against `a07f44a`); axioms standard |
| 2026-10-11 | W2a Combes–Thomas | running | Sonnet, worktree W2a |
| 2026-10-11 | W2a Combes–Thomas | landed | non-Hermitian coercive kernels with exponential decay: `combesThomas`, `combesThomas_restrict`, `perturbation_decay`, `greenFn_resolvent_identity` (`Balaban/Green/`, 724 lines); axioms standard |
| 2026-10-11 | W1 lattice/Gaussian | landed | `99dc252`: blocks, block averaging (Q, Q*, projection), Gaussian integral with determinant (complex source), Gaussian measure and moments, Schur/Woodbury, block-spin identity with minimizer, composition, weighted form (1,103 lines); axioms standard; target 6 open → W1b |
| 2026-10-11 | D-PE polymer document | draft, in review | `notes/phase1/POLYMER.md` (Sonnet); review → `POLYMER-review.md` |
| 2026-10-11 | W1b multiscale | landed | torus Laplacian matrix, one-step splitting `A⁻¹ = M⁻¹ + HΔ⁻¹Hᵀ`, exact k-step decomposition `laplacian_inv_eq_multiscale`, positivity (≈410 lines); axioms standard |
| 2026-10-11 | D-PE polymer document | revised | review R1–R12 addressed (`## Review dispositions`); ready for PE interface drafting and W3b |
