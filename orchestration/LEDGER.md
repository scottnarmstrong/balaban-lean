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
