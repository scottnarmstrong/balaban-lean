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

## Blocker 6: the general class (one ruling)
- Done since: the per-label bounds at the composed data, the filed torus defect, the chain at towers
  for every scale with one β₀ (W1040–W1069).
- RULING R8 (Scott, APPROVED 2026-10-18 as option (a)): the new level's terms on local generating sets. P3 pp. 78–79, (4.44)–(4.47)
  computes each term of the new level with the local generating set 𝔹_{k+1}(Y); mapping a local-chart
  point to the step chart is impossible in general (W1081: a local field can wind around a hole of the
  polymer). The step's mark, determinant and activity objects (`decMarkG`, `decMarkCorr`,
  `decMarkCorrTerm`, `e1MarkGParamG`, `DetExpansionLocC`, `DirectTerms`, `physParam`/`physV`) are typed
  by the step's whole-level set `S.G'`. Options: (a) generic versions with an explicit background
  generating set, the current objects being the instance `S.G'` (definition change); (b) no new
  definitions, refactor the cores to accept background maps glued from the local set (longer, more
  awkward). Recommended: (a). Meanwhile the parts that need no ruling proceed (W1084: the determinant
  on local sets without `HatConn`, P6 Lemma 4.1 on the local set).

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

## Rulings of 2026-10-18 (approved: "go with your recs on R8 and the others")
- R8: option (a), generic objects with an explicit background generating set (Blocker 6 above).
- CRotE: repaired now as in `CROTE.md` §4 (real clause + Cayley path; every `hCR` removed).
- R7: the base carrier `Kphys` of the W1009 handoff (Blocker 1); W1015 resumes on it.
- R5′: the first vacuum region of `StepData.b_vac` is Z_k^c ∖ Ω_{k+1} (P6 (3.2)).

## Ruling R7′ asked (2026-10-18)
- R7 specialized the physical base carrier `BaseSmallFieldInput` to M = K = 1 (`Geo S n R 1`,
  `RegionHistory S n R k0 1`, W1009 proposal). The spine's classes at the prefix constants have M = c·M₁
  with c ≥ 14 and torus horizon K = k̂_f + 1 ≥ 2, and no landed map connects the M = K = 1 carrier to
  them (W1110, `notes/phase1/SPINE.md`, BaseStepInput sub-inputs). Proposal: state the carrier at the
  class's general M and K (the corrected `Kphys` of W1101 unchanged in content; only the geometry
  parameters freed), so that `BasePreStepInput`/`BaseFlatStepInput` can be populated from it.
  Recommended: yes.

## Ruling R9 asked (2026-10-19)
- `sides L K nK j = nK * L^(K-j)` (`LargeField/Def7.lean:72`) uses truncated subtraction, so above the torus
  horizon (j > K) the torus keeps the size nK instead of being a point, as in the source (the torus of side
  ℓ/L^j is one point beyond the last scale). Above K the localized histories then evolve by `blockMap` on a
  torus of size nK, which does not commute with translations by level-K cubes; `QuietStepInput'.real_euclid`
  fails for nK ≥ 2 (W1124, explicit translation counterexample), so the quiet step data, and with them the
  class witnesses at the configurations the flow uses (K ≥ 2), cannot be built.
- Proposal: `sides L K nK j := if j ≤ K then nK * L^(K-j) else 1`; weaken `hsub` to `K < j → n j = 1` in
  `ImageHist`, `ImageHistBook`, `QuietImage`. The fine torus is unchanged. Cost: `sides` appears in 148 files
  (full rebuild; some `rfl` proofs may need repair). Alternative without a definition change: extend the quiet
  kernel along `HistImage` orbits (a rewrite of `QuietStepData`/`QuietLocalInput`, ~1,200 lines).
  Recommended: the definition fix.

## Ruling R-N₁ proposed (2026-10-19, W1127)
- `D2SF2` and `SFFlat2` require their small-field clauses on every Def-6 torus N₁ ≥ 1, but the class family
  only ever reads N₁ = L^{m₀} n_k (`sfIdx`), exactly the tori where the chain's conditions (3 ∣ N₁, 5 < N₁,
  3^{m₀} ∣ N₁) hold. Proposal: restrict those two clauses to the tori that are read (11 files); this removes
  a ≈ 600-line obligation (the step on every torus). Recommended: yes.
