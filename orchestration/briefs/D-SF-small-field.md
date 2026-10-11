# Brief D-SF — the small-field step at λ = ∞ (`notes/phase1/SMALLFIELD.md`; roadmap I-6 … I-9)

You are a mathematical analyst writing a phase-1 document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model, **hard spins (λ = ∞)**. Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics on paper; you do not write or run
Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context
Roadmap `review/FORMALIZATION_ROADMAP.md` §3.3: **I-6** (P1 Prop 3.10 / Cor 3.11: renormalization
analysis, `|𝓔_k| ≤ C E₀ |T^{(k)}_1|` on `Ξ^c_k(1,ε_k)` from analyticity, symmetry, localization and
renormalization hypotheses), **I-7** (P4 Prop 5.1, (5.31)–(5.33): RG equations; at λ = ∞ the
λ-equation is vacuous; the choice `c = 0`, `d = b` used by P5–P7 must be written out, BIG_PICTURE §7
item 13), **I-8** (P6 §4 = P4 Props 2.1, 2.2, 4.1, 4.2 and P5 Props 3.1–3.4: localization and
cluster expansions of the fluctuation integrals, from I-5, PE and P6 (4.11)), **I-9** (P4 Thms 1–2,
internal milestone SF: one small-field step `ℛ^{sf}_k → ℛ^{sf}_{k+1}` with the RG equations
(1.9)–(1.10); it may not take I-8's conclusions as hypotheses).
Sources: P1 = CMP 167 (1995) 103 (`sources/BF02099355.pdf`, scan), P4 = CMP 182 (1996) 675
(`sources/Balaban.pdf`, scan), P5, P6 = CMP 198 (1998) 1 (`sources/s002200050470.pdf`); map
`review/SOURCES.md`; reviews `review/papers/P1-*.md`, `P4-*.md`, `P5-*.md`, `P6-*.md`;
`review/BIG_PICTURE.md`; `notes/ERRATA.md`. For scans, read page images and say which pages.
Phase-1 documents you build on: `notes/phase1/GREEN.md`, `POLYMER.md`, `BACKGROUND.md` (v2),
`CORRELATIONS.md` (C-1*, C-1a: what the flow must deliver for Root-C — now formalized as the Lean
structure `Balaban.Correlations.C1Star` and `RootFAndC1Star`, `Balaban/Correlations/C1Star.lean`),
`LF-ARCHITECTURE.md` (§1.4 "which properties of ρ_k are used where", the small-field interface
P4 (H.1)–(H.7) at λ = ∞ that Def-7 contains). The localization document (I-4, I-5) is being written
in parallel (`notes/phase1/LOCALIZATION.md`, not yet available): cite I-4/I-5 by their roadmap
statements. Landed Lean: `Balaban/Flow/*` (`exists_rg_solution`, `exists_rg_solution_triangular`,
`exists_gamma_infty`, running coefficients), `Balaban/Polymer/*`, `Balaban/Gaussian/*`.

## Task: write `/home/scott/Balaban/notes/phase1/SMALLFIELD.md`
1. **The small-field class** `ℛ^{sf}_k` at λ = ∞: P4 (H.1)–(H.7) (and P1's hypotheses), stated
   precisely (domains `Ξ_k`, `Ξ^c_k`, the effective action decomposition, the polymer functions
   with their analyticity, symmetry, localization and normalization conditions).
2. **I-6** with a complete proof at λ = ∞ (P1 §3, Prop 3.10, Cor 3.11), and how it is used.
3. **I-7**: the RG equations at λ = ∞, the reduction to the landed `exists_rg_solution`, the choice
   `c = 0`, `d = b` written out, (H.6) with `γ_∞, δ_∞`, the rate `|γ_∞ − 1| ≤ c/β` (CORRELATIONS
   (F1)), and continuity in ν down to ν = 0 (CORRELATIONS F1, UNCERTAIN there): settle it or state
   exactly what is needed.
4. **I-8**: the expansions of the fluctuation integrals, statements and proof plan from I-5, PE
   (`POLYMER.md`), P6 (4.11).
5. **I-9**: one small-field step, statement and proof outline, with every analytic input named
   (I-1, I-2, I-4, I-5, I-6, I-7, I-8, G-*, PE).
6. **The two-point/one-point parts** that C-1a/C-1* need (CORRELATIONS §2.3: M^{(j)}, R^{ij}, the last
   step): where they enter the small-field step and what extra statements are required.
7. **Interfaces for freezing**, what changes at λ = ∞, errata, Lean plan and size estimate,
   questions.

Standards: exact page/equation references; distinguish proved / cited / sketched; mark doubts
"UNCERTAIN:". Plain mathematical prose; avoid "calibration", "robust", "leverage", "crucially".
LaTeX in $...$. Expect 8,000–14,000 words; write the file section by section as you go.

Rules: write only `/home/scott/Balaban/notes/phase1/SMALLFIELD.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/sf/ allowed). Do not edit any other file, do not commit, do not
run Lean or lake. When done, reply with: the statements of I-6 … I-9 (one line each), which proofs
are complete, the main risk, the size estimate and any questions.
