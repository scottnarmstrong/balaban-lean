# Brief: roadmap v2 (with Roland's answers and the external library)

## Context

Read `SYNTHESIS_BRIEF.md` first: it gives the project context, the conventions
(Scott's campaign method: small frozen surface of ~20 author-approved anchors,
source dependency graph, definitions by their mathematics, `∃!` before
uniqueness-defined objects, every file a module) and the writing rules (plain
mathematical prose, exact references, no marketing words, avoid "calibration",
"robust", "leverage", "crucially"). Those rules apply here.

Since the first synthesis (`BIG_PICTURE.md`, `FORMALIZATION_ROADMAP.md` v1,
commit 2f3ba12):

1. **Roland answered** the roadmap's questions: `ROLAND_ANSWERS.md`. In short:
   large fields are essential ("the crux of the matter"); hard spins (λ = ∞) with
   general d ≥ 3, N ≥ 2 are fine; finite volume on tori with bounds uniform in the
   volume, infinite volume only in the final correlation theorem, is fine;
   different proofs of the Green's function estimates are fine and encouraged.
   Questions 5 (errata, copies) and 6 (constants in P9 Thm 1.1; why λ ≥ λ0) are
   open.
2. **The library grew**: external sources E1–E11 (Balaban's earlier Higgs and
   gauge-theory papers, including the large-field papers E8–E10 = CMP 119 (1988)
   243, CMP 122 (1989) 175 and 355; Cammarota; Brydges' Les Houches lectures)
   and Dimock's exposition D1–D3 were obtained and reviewed (`SOURCES.md`,
   `papers/E*.md`, `papers/D*.md`).

## Inputs

Read in full: `SOURCES.md`, `ROLAND_ANSWERS.md`, `QC_LOG.md`, `BIG_PICTURE.md`,
`FORMALIZATION_ROADMAP.md` (v1), and every review in `papers/` (P0–P9, E1–E7,
E11, D1–D3). Check load-bearing claims against the PDFs in `../sources/` (Read
tool with `pages`, at most 20 pages per call; the scans P0–P4, E1–E7, E11 need
page images). You may grep Scott's repositories under `/home/scott` again
(read-only) where the infrastructure section needs it.

## Deliverables

1. **`FORMALIZATION_ROADMAP.md` — rewrite in place (v2).** Start with a short
   "Changes from v1" section. Then the same overall structure as v1, revised:
   - §1 What Roland wants — now answered. Large fields are the crux, so the
     committed campaign must include the full large-field flow. Decide and
     justify the committed headline: the full RG flow with large fields
     (P7 Thm 5, in method and/or observable form) and/or the correlation
     theorem P9 Thm 1.1. Say what the small-field flow becomes (an internal
     milestone, not a deliverable).
   - §2 Scope: rewrite the tiers accordingly; record the fixed model choices
     (hard spins, general d, N, tori with uniform bounds).
   - §3 Frozen surface: revise roots and interfaces. The Green's function
     interface (old I-3) should now be stated as exactly the bounds the series
     consumes (use the E3, E5 reviews for what P2/P3 actually use), to be proved
     by our own methods; propose concrete proof routes (Combes–Thomas, block
     Neumann series, discrete elliptic regularity, etc.), flagged as proposals.
   - Large-field calculus: for each component (regions and their nesting,
     characteristic functions, the step counter K / admissibility, the R
     operation, polymer exponentiation, base case, last step), say whether we
     follow P5–P7, Dimock D2/D3, Balaban's gauge papers E8–E10, or a
     reconstruction, and what each of these sources supplies that the others
     lack. Use D3 for the global order of constants if it provides one.
   - Cluster expansions: state the single abstract polymer-expansion theorem to
     prove once (use the E7, E11 reviews), and its relation to Scott's KPZ BKAR
     formalization.
   - Phasing, size, risks, missing sources, and remaining questions for Roland
     (keep 5 and 6; add any new ones the library raised) — all updated.
2. **`BIG_PICTURE.md` — targeted edits, not a rewrite.** Update §5
   (prerequisites outside the bundle) with what the external papers actually
   contain and what the bundle uses from each, and update §7 where the library
   settles an item (e.g. P4's reference "[3]", "[2c]", P1's "[2d]", the CMP 96
   items, the step counter). Mark each changed item "(updated 2026-10-11 from
   E*/D*)".
3. **`LIBRARY.md` — new.** An annotated index of the whole library: one entry
   per source (P0–P9, E1–E11, D1–D3), in reading order by topic, each with
   citation, file, review link, status (obtained / missing), a three-to-five
   sentence annotation (what it is, what the O(N) formalization takes from it),
   and a reading priority (essential / important / background). End with a
   short "suggested reading path" for a new collaborator.

## Rules

Write only these three files. Do not modify the per-paper reviews, sources, or
other repositories; do not run Lean or builds. When done, reply with: the
committed headline(s) in one line each, the three biggest changes from v1, the
main remaining gaps in the sources (things no source in the library proves),
and the updated questions for Roland.
