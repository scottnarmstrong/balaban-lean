# Brief D-LF-v4 — version 4 of `notes/phase1/LF-ARCHITECTURE.md`

You are the author of the large-field architecture document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model (hard spins, $d\ge3$). Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Input
- `notes/phase1/LF-ARCHITECTURE.md` v3 (commit 9c37838; keep a copy of v3 in your scratch dir).
- `notes/phase1/LF-ARCHITECTURE-review.md`, section "Third review (v3)": R3-01 … R3-14 and its
  agreement with the counting audit.
- `notes/phase1/LF-V3-COUNTING-astra.md` (counting audit C-01 … C-05) and
  `notes/phase1/LF-V4-REPAIRS-astra.md` (paste-ready repair text: B pending-core state, transitions,
  activation, budget calculation replacing §4.5; C lattice path lemma for (3.11)′; D restated LF-2).
- Sources as before (`sources/`, `review/SOURCES.md`; P5–P7 text layers in
  `/home/scott/Balaban-scratch/astra-lemmaH/P*.txt`).

## Task
Write version 4, in place:
1. **Counting closure.** Adopt the pending-core state (three-way window state: pre-window / pending /
   active), C-01's last-box-entry split of Lemma C(e)–(f), (H-λ) and $Z_0=\varnothing$ in the §4
   theorem (C-04, C-05), deterministic bookkeeping (R3-12). Check the astra text before pasting:
   you are responsible for its correctness; state where you changed it.
2. **Adjacency (R3-01).** Components by distance $< w_k$ cubes so that the neighbourhoods $U^{\sim}$ of
   distinct components are disjoint (P5 (1.22)); propagate the constant changes; then (3.11)′ by the
   component-wide path (R3-02 and astra C.1), including the localization with the exact P7 (3.11)
   characteristic functions (journal p. 522) — prove it or mark it as the open item.
3. **Tori (R3-05).** State LF-2 and the region calculus on the torus; handle winding pre-window
   components and the hull on small tori for $k>k_0$.
4. **Def-7/LF-4 design decisions (R3-06 … R3-11), not their full definitions.** Decide and record:
   causality (a-priori sequence $\hat\lambda_j$ or whole-sequence parametrization plus a causality
   lemma); (D5) as P5 (1.26)–(1.27) for the localized operator with the domain (1.24)–(1.25); the
   operators and exponents of kept components and the generating set after removals (R3-08); the list
   of objects Def-7 needs, each with its ∃!/definition status (R3-09); Def-7 as a predicate on
   representations and LF-4 in existential form (R3-10); the explicit quantifier prefix of §5
   (R3-11). The full definitions belong to the reconstruction document (next deliverable); here give
   the decisions and the outline of that document (sections, objects, order, sizes).
5. R3-03, R3-04, R3-13, R3-14: fix or record.
6. Update §6 (new/unproved statements with confidence), §7 (questions), §8 (interfaces: what
   becomes freezable when), and append "Third-review dispositions (v3 → v4)" listing R3-xx and C-xx
   with accepted/declined and why.

Standards: exact page/equation references; distinguish proved / cited / sketched; mark doubts
"UNCERTAIN:". Plain mathematical prose; avoid "calibration", "robust", "leverage", "crucially".
Write only `notes/phase1/LF-ARCHITECTURE.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/lf4/ allowed); do not commit; do not run Lean.
Reply with: what closed, what is still open (with confidence), the Def-7/LF-4 design decisions (one
line each), and the outline of the reconstruction document.
