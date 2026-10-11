# Phase 1 plan (started 2026-10-11)

Roadmap §8, phase 1, adjusted to Roland's answers of 2026-10-11 (batch 2: any large-field
mechanism that works is acceptable; the P6 Thm 4 repair is agreed; the step counter is
reconstructed; limits along tori suffice).

## Order of work

The order is: anchors frozen → reviewed source → source dependency graph → Lean on the
dependency-ready frontier.
- **The source.** For three components the source the Lean proof follows is not Balaban's text
  but a document we write and review:
  - the large-field calculus (Roland: "anything that works");
  - the Green's function bounds (Roland: our own proofs are encouraged);
  - the polymer expansion (one abstract theorem replaces scattered citations).
- **The graph** for each component is extracted from its reviewed document, together with the
  parts of P1–P9 it serves, after the component's interface statements are approved and frozen
  (`build-proof-dependency-graph`).
- **Lean work before the graph.** Phase 1 Lean work is infrastructure that every route needs.
  This is off-frontier work with a recorded reason, per the orchestrator rules:
  - lattice tori with block hierarchies and block averaging;
  - Gaussian block-spin identities;
  - the BKAR port;
  - the contraction and implicit-function tools.

## Paper deliverables (no compiles)

| ID | Document | Content | Feeds |
|---|---|---|---|
| D-LF | `notes/phase1/LF-ARCHITECTURE.md`, then the reconstruction document | Choice of large-field architecture; definitions of regions, histories, characteristic functions, integral operators, the step counter and admissibility; the inductive class (Def-7); LF-1 to LF-8 restated; base case; last step; the constant chain (roadmap §4.4) | Def-7, LF-*, Root-F |
| D-G | `notes/phase1/GREEN.md` | Precise statements of G-1 to G-6 for the operators the series uses (hard spins); proofs of G-1 and of G-2 steps 1–2; a detailed plan for G-2 step 3 (discrete elliptic regularity); G-4 by Combes–Thomas (FroehlichSpencer port); G-5, G-6 | G-* interfaces (frozen in phase 1) |
| D-PE | `notes/phase1/POLYMER.md` | The abstract polymer-expansion theorem PE with holes ("connected modulo Ω^c"), its proof from the BKAR forest formula, the corollary for truncated expectations (P9 Prop 3.1), and the instantiation at each use in P5–P7, P9 | PE interface (frozen in phase 1) |

Each document gets an independent refute-first review before its interfaces are drafted in Lean
for approval.

## Lean work packages (compile-limited; machine-wide throttle)

| ID | Package | Status |
|---|---|---|
| W1 | Tori with block hierarchies; `Q`, `Q*`; Gaussian block-spin identities; free flow; Schur complement and Woodbury identities; the exact multiscale decomposition of `(−Δ+ν)^{-1}` on tori (G-6) | first wave |
| W3a | Port of `BKARForestFormula` (v4.33.0, not modules) to v4.35.0-rc2 and the module system, under `Balaban/External/BKAR/` | first wave |
| W2 | G-1 coercivity; `L²` Agmon decay; G-4 from FroehlichSpencer's Combes–Thomas | after D-G review |
| W3b | PE with holes, from the ported BKAR | after D-PE review |
| W4 | RG equations: contraction on a polydisc, existence of `γ_∞` (P4 §5) | second wave |
| W5 | Constant-configuration variational problem (P2 §2, Prop 2.1); `O(N)` reductions (P1 (3.24)–(3.28)) | second wave |
| W6 | Model-free large-field lemmas (normalization identity of R, P7 (1.7)) | after D-LF |

Milestone M1: W1–W6 landed and audited; D-LF reviewed and approved; Def-7, LF-1, LF-2, LF-6
drafted for approval; G-* and PE frozen.
