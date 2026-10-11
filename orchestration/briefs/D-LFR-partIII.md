# Brief D-LFR-III — reconstruction document, Part III (R on covered windows; LF-4)

You are the author of the large-field reconstruction document (Lean formalization of Balaban's RG
analysis of the low-temperature O(N) model, hard spins, $d\ge3$). Repository /home/scott/Balaban
(read AGENTS.md first; note the approved LF rulings 1–2). You write mathematics; you do not write
Lean. **Do not launch subagents (no Agent tool); work directly.**

## Input
- `notes/phase1/LF-RECONSTRUCTION.md` Parts I (v1.1) and II (commit after 28afe92); your own text.
  An independent audit of Part I v1.1 fixes and Part II (astra) is running in parallel; its
  findings will be sent to you; fix Parts I–II in place when they arrive and list the fixes.
- `LF-ARCHITECTURE.md` v4 §3.8 (LF-4 in detail: Steps 0–6, (2.15)′ … (3.19)′, Lemma CH, Lemma L),
  §9 outline of Part III: III.1 core and composition; III.2 renormalized actions; III.3 late scales;
  III.4 Lemma CH in full; III.5 decompositions and K1; III.6 cancellation; III.7 Lemma 2.5;
  III.8 normalization, refund, K2, κ″, LF-4R; III.9 Lemma L, analytic extension, coset average;
  III.10 polymer expansion, B^♯, R″_m.
- Audits: `LF-V4-AUDIT-astra.md` (V4-01: (3.11)′ must be stated on the localized support of the ripe
  lineage), `LF-ARCHITECTURE-review.md` (third review, R3-03 Lemma CH outline items).
- Open items to close: O-3 (Lemma L(c) localized), O-8′ (carry the actual free-flow composed weights
  through the cancellation P7 p. 499, (2.7)–(2.9), (2.55), (2.57)), O-II-5 (P7's kept operators have
  the kept-data form (S3)), OBSERVABLES requirement 2 (coset average on the full integrand: joint
  O(N) covariance in (ψ, h, g)), the B₀/H₀ question (§5 row 12).
- Landed Lean you may cite by name: `Balaban/LargeField/Geometry/*` (Timár, Lemma S),
  `Balaban/Background/*` (I-1, Def-5 `bgField`/`bgFieldC` with `theorem71`, `theorem72`;
  composition `composeField`, `lemma62`), `Balaban/Polymer/*` (incl. `pe_hole`, `mayer_marked`),
  `Balaban/Localization/*`.

## Task
Write **Part III** appended to `notes/phase1/LF-RECONSTRUCTION.md`, at the standard of Parts I–II:
closed definitions, complete proofs or explicitly marked citations, explicit constants, every
UNCERTAIN marked; LF-4 stated exactly (existential form, hypothesis IsRep^pre_k and β_kν_k ≤ 1) with
its proof, and the internal lemma LF-4R ((Rg)). End with the Lean declaration list for Part III and
the updated open-items list. This is the longest part (≈50 pp in the outline): write section by
section as you go so nothing is lost; if you run out of budget, stop at a section boundary and say
where.

Standards: exact page/equation references (P5–P7, E9/E10); plain mathematical prose; avoid
"calibration", "robust", "leverage", "crucially". Write only `notes/phase1/LF-RECONSTRUCTION.md`
(scratch under /tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/lfr3p/ allowed); do not commit; do not run Lean. Reply with: the
list of Part III definitions and lemmas (one line each, with status), changes to Parts I–II or v4,
and open items.
