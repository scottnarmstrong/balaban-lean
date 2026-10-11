# Brief D-LFR-I — reconstruction document, Part I (geometry and counting, model-free)

You are the author of the large-field reconstruction document of the Lean formalization of
Balaban's RG analysis of the low-temperature O(N) model (hard spins, $d\ge3$). Repository
/home/scott/Balaban (read AGENTS.md first). You write mathematics; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Input
`notes/phase1/LF-ARCHITECTURE.md` v4 (commit 44141ef): §3.1–3.5, §3.7 Lemmas G, S, P, L, F (geometric
part), §4 (LF-2), §5.1 (prefix), §8.1, §9 (outline of the reconstruction document, Part I).
Reviews: `LF-ARCHITECTURE-review.md`, `LF-V3-COUNTING-astra.md`, `LF-V4-REPAIRS-astra.md`. An
independent audit of v4's counting (astra) is running in parallel; its findings will be fed to you if
they arrive while you write.

## Task
Write `notes/phase1/LF-RECONSTRUCTION.md`, **Part I only** (≈30 pp in the §9 outline): I.1 constants
and the explicit quantifier prefix; I.2 tori, cubes, components ("distance < ω_k cubes"); I.3 the
region calculus as explicit set functions (Z_k, Z^pre_k, hulls, spines, thickenings, U^∼), with
Lemmas G, S, P and the geometric part of F; I.4 histories, deterministic bookkeeping, the three-way
window state and transitions (T1)–(T7), Lemmas C4 and C; I.5 LF-2 on tori with its complete proof.

The standard is **closed definitions and complete proofs that a Lean worker can formalize line by
line**: every object defined as a function of explicitly typed data (state the Lean-facing types:
`Finset (Fin d → ZMod n)` or similar), every lemma with all hypotheses, every inequality written
out, constants as explicit functions. No forward references to Parts II–IV except through the
abstract axioms (G1), (G2), (B), (Rg), (K), (H-λ), (H-T) of LF-2, which must be stated as explicit
hypotheses of an internal lemma (they are never frozen). Include at the end: the list of Lean
declarations (definitions and lemmas, in dependency order) that Part I asks for, with estimated
sizes.

Standards: exact page/equation references to P5–P7, E9/E10; distinguish proved / cited / sketched;
mark doubts "UNCERTAIN:". Plain mathematical prose; avoid "calibration", "robust", "leverage",
"crucially". Write only `notes/phase1/LF-RECONSTRUCTION.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/lfr/ allowed); do not commit; do not run Lean.
Reply with: the list of definitions and lemmas of Part I (one line each) with status, anything in v4
you had to change, and open items.
