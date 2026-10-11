# Brief D-PE — the polymer-expansion document (`notes/phase1/POLYMER.md`)

You are a mathematical physicist writing a phase-1 document of a Lean 4 formalization of
Balaban's renormalization-group analysis of the low-temperature classical O(N) model (hard spins,
d ≥ 3, N ≥ 2). Repository: /home/scott/Balaban (read AGENTS.md first). You write mathematics on
paper; you do not write or run Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context

The series uses cluster/polymer expansions in many places (localization expansions of
fluctuation integrals P4/P6 §4, the large-field polymer expansions P7 (3.26)–(3.29) and §4
(4.11)–(4.14), P9 Prop 3.1 for truncated expectations), always citing general theorems ([9,11,13–15]
of P7; Brydges' Les Houches lectures E11; Balaban's gauge papers E7) rather than proving them;
some uses need "connectivity modulo Ω^c" (polymers connected modulo a hole set), which no source
in the library proves. The plan (`review/FORMALIZATION_ROADMAP.md` §5) is to prove one abstract
theorem PE once, with a marked corollary for truncated expectations that proves P9 Prop 3.1
(which P9 only sketches). A complete machine-checked BKAR forest interpolation formula exists:
`/home/scott/mining/BKARForestFormula` (read its README and `BKAR/Formula.lean`; flagship theorem
`BKAR.bkar_formula_forestIndex_cube_contributions`: ρ(1,…,1) = Σ_F ∫_{[0,1]^{E(F)}} ∂_{E(F)} ρ(x^F(u)) du
for C^∞ ρ on edge couplings); it is being ported into the project. Scott's KPZ repository has a
BKAR-based polymer development (`/home/scott/KPZ/cumulants/Lean/Polymers/BKAR/*`, read-only).

Read: `review/FORMALIZATION_ROADMAP.md` §5 and §6; `review/BIG_PICTURE.md` (cluster-expansion
uses); the reviews `review/papers/E7-*.md`, `E11-*.md`, `P5-*.md`, `P6-*.md`, `P7-*.md`, `P9-*.md`,
`D2-*.md`, `D3-*.md`; the ERRATA rows on polymer expansions and P9 Prop 3.1 (`notes/ERRATA.md`).
Check uses against the PDFs in `sources/` (map `review/SOURCES.md`; Read tool with `pages`, ≤ 20
pages per call; E7, E11 are scans — read page images; P5–P9 have text layers; text extractions
already exist in /tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/pe/). Also read the frozen roots
`Balaban/Frozen/Roots/*.lean` and `Balaban/Frozen/Geometry/IsPolymer.lean` (polymers =
nearest-neighbour connected unions of blocks of side M L^j; size = number of blocks).

## Task: write `/home/scott/Balaban/notes/phase1/POLYMER.md`

1. **Every use in the series.** For each place the O(N) series uses a cluster or polymer
   expansion (P4, P5, P6 §§2–4, P7 §3 and §4, P9 §§3–4): what is expanded, the activities, the
   compatibility relation, the hole set if any ("mod Ω^c"), the smallness condition, the
   conclusion used, with pages and equations.
2. **The abstract theorem PE.** One theorem (or a small family sharing one proof) covering every
   use: the polymer space (finite subsets of a lattice of blocks, connectivity possibly modulo a
   hole set), activities analytic in parameters, the smallness condition with an exponential size
   weight, and conclusions: (i) the logarithm of the polymer partition function is a sum over
   connected clusters of local terms; (ii) each term is analytic and bounded with decay in its
   support size (blocks, matching the frozen `IsPolymer` size); (iii) the marked/rooted version for
   truncated expectations (P9 Prop 3.1 (3.13)). Include locality and torus-independence for
   non-winding clusters (needed by Root-F's agreement clause).
3. **Proof.** A complete proof, paper style, via the BKAR forest formula as formalized (state
   which form and which ρ), the tree-graph bound, and lattice-animal counting; or, if a
   Kotecký–Preiss/inductive proof is shorter to formalize, give that and compare. Treat the hole
   set carefully.
4. **Corollaries**: the truncated-expectation corollary and the proof of P9 Prop 3.1 (one- and
   two-function forms); the exponentiation used in P7 (3.26)–(3.29) and (4.11)–(4.14).
5. **Instantiation table**: for each use in §1, the parameters of PE and the verification of its
   hypotheses (or the precise gap).
6. **Lean plan**: definitions and lemmas in order, which parts come from the BKAR port and from
   KPZ, a size estimate, risks.
7. **Questions**, if any.

Standards: exact page/equation references; distinguish proved / cited / sketched; mark doubts
"UNCERTAIN:". Plain mathematical prose; no marketing words; avoid "calibration", "robust",
"leverage", "crucially". LaTeX in $...$. Expect 6,000–12,000 words; write the file section by
section as you go.

Rules: write only `/home/scott/Balaban/notes/phase1/POLYMER.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/pe/ allowed). Read other repositories read-only. Do not edit any
other file, do not commit, do not run Lean or lake. When done, reply with: the statement of PE in
a few lines, the uses it does not cover (if any), and any questions.
