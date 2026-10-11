# Brief D-TP — the one- and two-point functions through the flow (`notes/phase1/OBSERVABLES.md`; C-1a)

You are a mathematical analyst writing a phase-1 document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model, **hard spins (λ = ∞)**. Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics on paper; you do not write or run
Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context
P9 = Balaban, O'Carroll, CMP 199 (1999) 493–520 (`sources/s002200050510.pdf`; review
`review/papers/P9-*.md`) carries the observables (external field g, the generating function
F_k(ψ; h, g) = ⟨g, M_k⟩ + ½⟨g, G_k g⟩ + O(g³)) through Balaban's flow: (H.1), (H.2) (P9 (2.1)–(2.18)),
Prop 3.1 (the truncated-product part, `POLYMER.md` PE-M), the step (3.1)–(3.10), (3.44)–(3.49), and
the last step (4.7)–(4.9). The interface Root-C needs is C-1* (`notes/phase1/CORRELATIONS.md` §2.2,
formalized as `Balaban.Correlations.C1Star` and `RootFAndC1Star` in
`Balaban/Correlations/C1Star.lean`; Root-C follows in Lean from `RootFAndC1Star` alone:
`rootC_of_rootFAndC1Star`). The inductive form C-1a is sketched in CORRELATIONS §2.3 with the
derivation of C-1* from it; the small-field document `notes/phase1/SMALLFIELD.md` v2 §6 lists the
additions X1–X7 to the small-field class and step (estimated 40k–80k Lean lines). Large fields:
`LF-ARCHITECTURE.md` v4 (§1.4: which properties of ρ_k Root-C uses; Def-7) and the reconstruction
document `LF-RECONSTRUCTION.md` (Part I; Part II in progress) — the observables must also pass
through R (large-field regions) and the frozen regime k ≥ k₀.

## Task: write `/home/scott/Balaban/notes/phase1/OBSERVABLES.md`
1. **C-1a precisely**: the second-order components (μ_j, 𝓜^{(j)}, R^{ij}) with their analyticity,
   covariance, localization and bounds at λ = ∞, as additions to Def-6/Def-7; the exact form of
   (H.1), (H.2) at λ = ∞ (the longitudinal part of C_k vanishes, CORRELATIONS §2.4).
2. **Preservation under one small-field step** (X1–X7 made into statements and proofs or proof
   plans; P9 §3, Prop 3.1 with PE-M).
3. **Preservation under R and in the frozen regime** (what P9 assumes about large fields; what the
   reconstruction must add to LF-4 so that the second-order terms survive R; whether P9's argument
   needs anything beyond Def-7's polymer bounds).
4. **The last step** (P9 (4.7)–(4.9)) and the derivation of C-1* exactly in the form of the Lean
   structure `C1Star` (fields `C1StarF1`–`F3`, the additions W19 made: limits of r^ℓ along tori,
   their ν ↓ 0 limits, 2|x−y| < ℓ; the extension convention for `C1StarF1` of SMALLFIELD v2 §3.5),
   including continuity in ν (the clause (CONT)).
5. **The β-dependence question** (open with Roland): may P9's constants depend on β? Show exactly
   where Root-C's statement (constants chosen before β) needs uniformity, and whether the flow gives
   it.
6. Interfaces for freezing, errata (P9 rows of `notes/ERRATA.md`), Lean plan and size, questions.

Standards: exact page/equation references; proved / cited / sketched; "UNCERTAIN:" for doubts. Plain
mathematical prose; avoid "calibration", "robust", "leverage", "crucially". LaTeX in $...$. Expect
8,000–12,000 words; write the file section by section as you go.

Rules: write only `/home/scott/Balaban/notes/phase1/OBSERVABLES.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/obs/ allowed). Do not edit any other file, do not commit, do not
run Lean or lake. When done, reply with: C-1a in one paragraph, which proofs are complete, what LF-4
must add, the answer to item 5, the main risk, the size estimate and questions.
