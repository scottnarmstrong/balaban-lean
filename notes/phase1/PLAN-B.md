# Plan B: closing the blockers without the author's answers (2026-10-17)

The two main theorems are statements about the O(N) model, not about Bałaban's construction. Any
construction that proves them is acceptable. Where the papers are ambiguous we therefore choose a
reading, record it as a design decision, and prove everything that reading needs. Answers from the
author, if they come, become a check, not a dependency. Decisions that change a landed definition
(rather than add proofs) are marked RULING: they need Scott's approval, as for every change of an
approved declaration.

## Blocker 1: base case and the case with no renormalization step (item 17)
- Base case k = 0: adopt the Yang–Mills pattern (YMACCOUNT.md; CMP 119 §1, pp. 246–248). The bare
  density is one term with no tests; the first step inserts the small-field tests through its own
  decompositions of unity; inside a bad region the raw variables are kept; the reserve for the first
  large-field components comes from the choice of the level-0 threshold (a high power of log β).
  Work: a design note against the landed base files (`LargeField/Base/*`), then the bound P5 (1.31)
  for the first components from the threshold (Opus).
- No step (k_f = 0, ν > 7/(8L²)): astra session `astra-kf0b` (running) is asked for a finite-range
  decomposition of the opposite-hemisphere activity, or a direct one-scale argument for large ν, or
  a counterexample. Builds on `LF-BASE-KF0.md`, `LF-BASE-KF0-H.md` (Theorem H.3).

## Blocker 2: switching backgrounds (item 13)
- Route R-YM (Q13-YM.md §5): large-field tests free of the external field up to the switching scale,
  the field carried in the weight, direction tests extended over the collar. Leaves 2, 3, 7 landed.
- The open estimate (activity bound on a transverse source radius of order β^{-1/2}): astra session
  `astra-radius` (running).
- RULING R2: leaves 1, 4, 5, 6 change landed definitions (three masses in `OpConsts`; the extended
  direction stencil in `Characteristic/Reg.lean`, `Stencil.lean`; a direction clause in
  `ChiDomProp`/`ChiDomAt` for k > k₀). About 120 files use `OpConsts`, 8 use `ChiDomProp`.

## Blocker 3: old boundary terms across a long hole (item 14)
- The cause is proved (VMOD-44 §§8–9): P5 (2.3)–(2.4) open the new region with L-blocks at every
  offset, so the face of a new hole cuts the π′ cubes and the completion spills active cells along a
  long face; nothing in (H.7) pays for that length.
- WITHDRAWN (astra-aligned, notes/phase1/astra/ALIGNED.md): R3 does not close blocker 3 — a fixed grid breaks the
  Euclidean covariance required by P5 (H.5), (H.7), and a completed hole still has positive tree length between two
  active attachments. Also, P5's π′_k allows blocks at every offset, so the long-face spill is narrower than VMOD-36
  suggested. Round 2 studies what pays the length between two attachments.
- (Former proposal) RULING R3: open the new region with L-blocks at aligned corners. Then every hole is a
  union of aligned boxes (`compl_isAlignedBoxUnion`, landed), the completion is spill-free and
  d(Y) ≤ d(X) (`HoleCompletionSize`, landed), and the length through a hole is never charged.
  Cost: the radii of the opening change by at most L cubes; the separation and ripeness lemmas of the
  region step must be re-checked with the new constants. About 20 files use the opening (`Region/Step.lean`,
  `SymmStep.lean`, `Inclusions.lean`, `Def7Hist.lean`, `History/Inhabited*.lean`, `R/StepGlue.lean`, …).
  Work: an Opus analysis of the blast radius before the change, then the change itself.
- Fallback: route B of VMOD-44 (plain domains, completion only for removed components), a change of the
  approved domain class Def7 (also a ruling).

## Blocker 4: the large-field gas (item 16)
- No author input needed: the clusters-on-core reading is our construction and its gas bound is
  proved. Remaining work is ours: the window bound (W964), the representation of R's output as this
  gas (design, Opus), the kept components (LF4K-PLAN.md), the vacuum energy (W965).

- Vacuum energy (W965, LF4R-PLAN §7.5′): the bound |E_k| ≤ C′(λ_k + 1) asserted on P7 p. 520 is false for the
  forward flow from a fixed E_0 and holds for the backward normalization (E_0 chosen so that E_K = 0).
  Decision (orchestrator, no landed definition changes): use the backward normalization; the constant
  cancels in log Z(g)/Z(0). To check: the large-field operators carry the same normalization (W968).

## Blocker 5: the last integral (item 18)
- Adopt our reading as the construction: the decoupling expansion is applied on the complement of the
  large-field blocks Z only; the field on Z enters the small-field terms through a background that
  depends on Z; the boundary terms B″ of P7 (4.11) are the only coupling. To prove: the boundary
  couplings across Z (FINALPHYS3.md §7, leaf L4). Queued for an astra session when one frees.

## Blocker 6: the general class (no author question pending)
- The open analytic input (the shifted data in the anisotropic domain, P1 Lemma 3.2, (3.107)):
  astra session `astra-xidom` (running). Then the torus defect at the cube of each centre
  (P1 (H.6), torus form), queued.

## Blocker 7: two tori (item 24)
- Our reading is proved (no floor needed below the last scales; the induction over the gap scales).
  Remaining work is engineering: tie the abstract terms to the tower's step terms.

## The step-to-step backbone (no author question; one ruling)
- The old terms are transported to the next scale's torus (W985: `oldTorusEquiv`, `liftOldTerms`).
- RULING R6 (Scott): the domain of the inherited levels. The landed `completeXiDom` uses the current
  scale's mass for every old level, and its inclusion across one step fails at admissible constants
  (`notes/phase1/astra/SFFAM.md` Part 3: a constant field with a small transverse source lies in the
  new domain but not in the old one, since `XiCBounds.hAbs` is strict with no margin). Options:
  (a) domains frozen at each level's birth mass (the W868 design; mass response already proved);
  (b) a step-dependent radius margin, as P4 (4.19), p. 704. Recommended: (a). Until then the clause
  transport on the pulled-back old domain proceeds (astra-sffam, W999).

## Minor confirmations (items 15, 19, 20, 22)
- We already use our readings; they need no change.

## Order
1. Rulings R2, R4, R5, R6 APPROVED by Scott (2026-10-17, "go with your recs"; AGENTS.md); R3 withdrawn.
2. Astra: `astra-xidom`, `astra-radius`, `astra-kf0b` (running); then blocker 5 (L4), blocker 6 (torus
   defect), blocker 3 (if R3 is declined, route B).
3. Opus: blocker 3 blast radius (if R3), blocker 1 base case design, the representation of R's output.
