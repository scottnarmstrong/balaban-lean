# Brief D-FLUCT — the small-field step in full at λ = ∞ (`notes/phase1/FLUCTUATION.md`; I-8, I-9; P5 §§2–3, P6 §§2–4)

You are the author of the document that reconstructs the largest remaining cited block of the Root-F
proof: the analysis of one renormalization step on the small-field region, i.e. the fluctuation
integrals, their localization and cluster expansions, and the renormalization of the effective action,
at λ = ∞. Repository /home/scott/Balaban (read AGENTS.md first). You write mathematics; you do not
write Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context
- `notes/phase1/LF-RECONSTRUCTION.md` (complete: Parts I–IV) cites this block in LF-3 (Thm IV.1.1),
  LF-5 (Thm IV.2.2), LF-6 (Prop II.7.9) and the assembly list IV.5.6 item 4 ("SF I-6, I-7, I-8, I-9,
  (CONT); P5 Props 3.1–3.4; P6 Props 2.1–2.4 and §4"); also O-2′ (Lemma IV.1.3, the analytic half of
  Lemma F: expanding the background change into localized terms).
- `notes/phase1/SMALLFIELD.md` v3: I-6, I-7 (both RG systems, the switch), I-8 and I-9 stated but
  **sketched** (§4, §5), Def-6, the analyticity spaces Ξ, Ξ^c (landed in Lean).
- `notes/phase1/LOCALIZATION.md` v3 (I-4a/b/c, I-5, covering size functional `treeLenCov`),
  `BACKGROUND.md` v2 (I-1, I-2 — landed), `POLYMER.md` (PE, PE-M, GAS, hole — landed in scalar form),
  `GREEN.md`, `OBSERVABLES.md` (the observable layer X1–X7 rides on this step).
- Sources: P4 = CMP 182 (1996) 675 (`sources/Balaban.pdf`, scan; read page images), P5 = CMP 196 (1998)
  485, P6 = CMP 198 (1998) 1 (`sources/s002200050470.pdf`), P1, P3; `review/SOURCES.md`; reviews
  `review/papers/P4-*`, `P5-*`, `P6-*`; `notes/ERRATA.md`.
- Landed Lean you can cite by name: `Balaban/Background/*`, `Balaban/Localization/*` (incl. `Decoupled*`,
  `abstract_expansion`, `gm2`, `gm4`), `Balaban/SmallField/*` (Ξ, Ξ^c, (Ξ1)–(Ξ4)), `Balaban/Polymer/*`,
  `Balaban/Flow/*` (RG equations: `rg_step_infty`, `matrixInfty`, `matrixFree`, `matrixSel`).

## Task: write `notes/phase1/FLUCTUATION.md`
1. **The step at λ = ∞ precisely:** the integral operator of one step on Ω_{k+1} (the change of variables
   ψ_{k+1} ↦ fluctuation field, the Gaussian measure with covariance C^{(k)} (constrained at λ = ∞,
   GREEN 4.5b/C12, landed `constrainedOp`), the main action, the interaction U^{(k)}), in both background
   conventions (ν-free for k < k₀, complete for k ≥ k₀).
2. **I-8 in full:** the localization and cluster expansions of the fluctuation integrals (P4 Props 2.1,
   2.2, 4.1, 4.2; P5 Props 3.1–3.4; P6 Props 2.1–2.4 and §4, incl. P6 (4.11)), with complete proofs from
   I-4, I-5, PE/GAS/PE-M, with explicit exponents (the iteration condition κ ≥ 8 + 14κ₀ of SMALLFIELD v3)
   and constants; state everything with the covering size functional.
3. **O-2′:** the analytic half of Lemma F (LF-RECONSTRUCTION Lemma IV.1.3) — prove it.
4. **I-9:** one small-field step from I-1, I-2, I-4, I-5, I-6, I-7, I-8 — complete proof, including the
   (F1) clause of SMALLFIELD Thm 5.3 and (CONT).
5. Interfaces, errata, Lean plan (dependency order, sizes), open items, questions.

This is a long document (expect 15,000–25,000 words); write it section by section as you go so nothing is
lost; if you run out of budget, stop at a section boundary and say where.

Standards: exact page/equation references (scans: say which pages you read as images); proved /
cited / sketched; "UNCERTAIN:" for doubts; plain mathematical prose; avoid "calibration", "robust",
"leverage", "crucially". Write only `notes/phase1/FLUCTUATION.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/fluct/ allowed); do not commit; do not run Lean. Reply with: the statements
(one line each) with status, the main risk, the size estimate, and open items.
