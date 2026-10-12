# Brief D-LFR-IV — reconstruction document, Part IV (the flow and the end) and §II.7 (LF-6)

You are the author of the large-field reconstruction document (Lean formalization of Balaban's RG
analysis of the low-temperature O(N) model, hard spins, $d\ge3$). Repository /home/scott/Balaban
(read AGENTS.md first). You write mathematics; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Input
`notes/phase1/LF-RECONSTRUCTION.md` Parts I–III (commit d9e499e; your text). An independent audit of
Part III (astra) runs in parallel; its findings will be sent to you; fix Parts I–III in place when
they arrive. `LF-ARCHITECTURE.md` v4 §3.7 (LF-3, LF-5, LF-6, LF-7, LF-8), §9 outline Part IV, §II.7
(LF-6, base case). `SMALLFIELD.md` v2 (Def-6, I-9 one small-field step, Theorem 5.3 with the (F1)
clause) and its new check `notes/phase1/CHECKS1-astra.md` §2 (R-ν: the transversal RG equation and
entries change for ν-free backgrounds — LF-3 for k < k₀ uses P5's ν-free backgrounds);
`OBSERVABLES.md` (C-1a; the last step; observables through R and the frozen regime; (L4) to be
replaced per your P2-04 convention); `CORRELATIONS.md` §2 (C-1*), the Lean `C1Star`/`RootFAndC1Star`
(`Balaban/Correlations/C1Star.lean`, corrected by W34) — the flow must deliver `RootFAndC1Star`, and
Root-F's frozen statement (`Balaban/Frozen/Roots/LogPartitionMultiscale.lean`).

## Task
Write **§II.7 (LF-6, the base case at k = 0/1, O-6)** and **Part IV**: LF-3 (one full step for
k < k₀ with the obligations O-III-1: κ₊ = 3/2 κ, B_st independent of B₀, H₀, c₁, c₂, (S5) for kernels,
preservation of IsRepFam, C_b and C₁₅ as outputs, R_m ≤ ½β^{−m−1}; P5 Lemma 2.1 is now Lemma III.7.1),
LF-5 (the frozen regime k ≥ k₀ and the step k₀ → k₀+1 including the switch from ν-free to complete
backgrounds), LF-7 (ν-continuity, IsRepFam), LF-8 (the last step: (a) the final integration and the
identity for log Z, (b) k_f = 0; P9 (4.7)–(4.9) with the massive final covariance including the tail —
`OBSERVABLES-review.md`), and **the final assembly**: from LF-1…LF-8, I-1…I-9 and the polymer theorems
to (i) Root-F exactly as frozen and (ii) `RootFAndC1Star` exactly as in Lean — state precisely which
theorem of which document supplies each clause, and list every remaining cited input. Same standard
as Parts I–III; Lean declaration list and updated open items at the end; write section by section.

Standards: exact page/equation references; plain mathematical prose; avoid "calibration",
"robust", "leverage", "crucially". Write only `notes/phase1/LF-RECONSTRUCTION.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/lfr4/ allowed); do not commit; do not run Lean. Reply with: the list of
definitions and lemmas (one line each, with status), the assembly table (clause → source theorem),
changes to Parts I–III, and open items.
