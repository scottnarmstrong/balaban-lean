# Brief D-SF-review — refute-first review of `notes/phase1/SMALLFIELD.md`

You are an independent referee for the small-field document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model (hard spins, λ = ∞). Repository /home/scott/Balaban
(read AGENTS.md first). You write a review; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Material
`notes/phase1/SMALLFIELD.md` (brief `orchestration/briefs/D-SF-small-field.md`); sources P1
(`sources/BF02099355.pdf`, scan), P4 (`sources/Balaban.pdf`, scan; read page images), P5, P6
(`sources/s002200050470.pdf`); `review/SOURCES.md`; reviews `review/papers/P1-*.md`, `P4-*.md`,
`P6-*.md`; `notes/ERRATA.md`; `notes/phase1/CORRELATIONS.md` (C-1*, C-1a, F1), `BACKGROUND.md` v2,
`POLYMER.md`, `LF-ARCHITECTURE.md` v4 (§1.4, Def-7 (D2)); landed Lean `Balaban/Flow/*`
(`exists_rg_solution_triangular`, `exists_gamma_infty`, running coefficients) and
`Balaban/Correlations/C1Star.lean` (statements only).

## What to check (try to refute)
1. **I-7**: the triangular system at λ = ∞ (P4 (5.5)–(5.34)), its reduction to the landed
   `exists_rg_solution_triangular` (do the hypotheses match exactly?), the rate |γ_∞ − 1| ≤ C/β from
   P4 (5.31), the continuity-in-ν stability lemma and its clause (CONT); the claims about P4 (5.9)
   (factor 2) and the 1/v factor in (5.5)/(5.25).
2. **I-6**: the new proof (second-order Taylor expansion, the O(N) identity that removes the marginal
   gradient term via (H.5)(4)); is every input named, does the bound hold uniformly in k?
3. **I-8 / I-9**: are the statements precise enough to freeze or to be internal lemmas; is the loss
   κ → 2κ − 3 − 6κ₀ right; is anything taken as a hypothesis that is a proof step (I-9 may not take
   I-8's conclusions as hypotheses); the base case (ER-062, ER-063).
4. **Consistency** with CORRELATIONS C-1* (what Root-C needs from the flow: (F1)–(F3)), with
   LF-ARCHITECTURE v4 (the small-field interface inside Def-7; flow choice c = 0 vs c = a_{k+1}b), and
   with BACKGROUND.md (I-1(e), Prop 5.1).
5. The size estimate (265k–470k Lean lines): is it plausible, and where could it shrink?
6. The questions of §7.6: give your answer to each where the sources decide it.

## Deliverable
Write `notes/phase1/SMALLFIELD-review.md`: findings S-01, … with severity (BLOCKER / MAJOR /
MINOR), location, argument, proposed fix; answers to §7.6; overall verdict (APPROVE /
APPROVE-WITH-CHANGES / CHANGES-REQUIRED). Plain mathematical prose; exact page/equation
references; avoid "calibration", "robust", "leverage", "crucially". Write only that file (scratch
under /tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/sfr/ allowed); do not commit; do not run Lean. Reply with the verdict and
the findings (one line each).
