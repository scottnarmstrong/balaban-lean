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
- W1140 (2026-10-19): the obstruction is the π′-shape required of the hole part of every domain (the new holes
  have seams, ALIGNED (23)–(26)); it also hits the new terms at Ŷ(S). Routes (i) (a property of the P6
  construction) and (ii) (a stronger H.7) are refuted, route B removes the spill but breaks the entropy (G2) of the
  domains; the minimal closure is ruling request R11 below (cover cubes only at small-field sites), under which
  the transfer of every domain across any new hole is proved (`Spine/LFBdryHole.lean`).

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

## Ruling R7′ asked (2026-10-18) — APPROVED 2026-10-19
- R7 specialized the physical base carrier `BaseSmallFieldInput` to M = K = 1 (`Geo S n R 1`,
  `RegionHistory S n R k0 1`, W1009 proposal). The spine's classes at the prefix constants have M = c·M₁
  with c ≥ 14 and torus horizon K = k̂_f + 1 ≥ 2, and no landed map connects the M = K = 1 carrier to
  them (W1110, `notes/phase1/SPINE.md`, BaseStepInput sub-inputs). Proposal: state the carrier at the
  class's general M and K (the corrected `Kphys` of W1101 unchanged in content; only the geometry
  parameters freed), so that `BasePreStepInput`/`BaseFlatStepInput` can be populated from it.
  Recommended: yes.

## Ruling R9 asked (2026-10-19) — APPROVED 2026-10-19
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

## Ruling R-N₁ proposed (2026-10-19, W1127) — APPROVED 2026-10-19
- `D2SF2` and `SFFlat2` require their small-field clauses on every Def-6 torus N₁ ≥ 1, but the class family
  only ever reads N₁ = L^{m₀} n_k (`sfIdx`), exactly the tori where the chain's conditions (3 ∣ N₁, 5 < N₁,
  3^{m₀} ∣ N₁) hold. Proposal: restrict those two clauses to the tori that are read (11 files); this removes
  a ≈ 600-line obligation (the step on every torus). Recommended: yes.

## Ruling R10 asked (2026-10-19, W1134) — APPROVED 2026-10-19
- `stepVacuumTerm` (`LargeField/Operators/StepData.lean`, region 1 set by ruling R5′) takes the first vacuum region
  as `(Z_k)ᶜ ∖ Ω_{k+1}` with the complement in the whole fine torus, while the local history of a component
  `Z'` has `Z_j`, `Ω`, `Ω″` inside `fineSet Z'` and `Z_{k+1} = fineSet Z'` (`locRH_Z`). So region 1 contains
  the whole torus outside `Z'` (`compl_fineSet_subset_vacuumRegion`, `Spine/RVacuumB0Defect.lean`), the term
  `E_k·|region 1|` grows with the torus, and the bound of `b⁰_k` by `(C_b log β_k + C_b B₀)|Z_{k+1} ∖ Z_k|`
  (`RVacuumB0Input`, A4-2v) fails for every flow with `E_k ≠ 0` (`norm_vacuumTerm_le_of_b0Bound`).
- Proposal: localize region 1 to the component, `(Z_{k+1} ∖ Z_k) ∖ Ω_{k+1}` (P6 (3.2) restricted to `Z'`;
  the same object as R5′ on the component). Files: `StepData.lean` (`stepVacuumTerm`), `StepVacuumR5`,
  `StepVacuumVolume` and the users repaired by `simp [stepVacuumTerm]` in W1092. Then the first excess of
  `stepVacuumVolume_eq_add_excess` is empty; the other two need the geometric bound
  `|Ω_{k+1} ∩ Z_k| ≲ |Z_{k+1} ∖ Z_k|` from the definition of `Ω`. Recommended: yes.

## Ruling R11 asked (2026-10-19, W1140) — APPROVED 2026-10-19: blocker 3 — boundary-term domains need cover cubes only at their small-field sites
- **What changes.** One clause of the valid domains (labels) of the boundary terms, `FineValidAt` in
  `LargeField/Def7FineSize.lean`. Today a valid domain must be a nonempty connected union of π′-cubes of its
  scale, contain or miss every large-field hole (component of Ω^c), and have finite size. R11 drops "union of
  π′-cubes" at the sites of the holes: a valid domain is nonempty, connected, contains or misses every hole, and
  has finite modular size. The finite size already puts every small-field site of the domain in a π′-cube inside
  the domain (`DjModFin.exists_box`), so the size `d7SizeAt`, its covers and trees, the history clause
  `loc_hist`, the H7 domain and the bounds are unchanged; every domain valid today stays valid
  (`FineValidAt.fineValidFinAt`). The new clause, elaborated (landed as `Def7.FineValidFinAt` in
  `Spine/LFBdryHole.lean`):
  ```
  def FineValidAt (F : FineSizeFrame S n M K m₀ m₁) (k : ℕ) (Om : Set (Torus S.d (n k)))
      (X : Finset (Torus S.d (n k))) : Prop :=
    Fluctuation.DjModFin m₀ k (d7Pull F k Om) (d7Pull F k (X : Set (Torus S.d (n k))))
  -- DjModFin m₀ j Ω X := X.Nonempty ∧ SiteConnected X ∧
  --   (∀ z ∈ Ωᶜ, OmegaComp Ω z ⊆ X ∨ Disjoint (OmegaComp Ω z) X) ∧ dcovModE m₀ j Ω X ≠ ⊤
  ```
- **Why the source needs it.** A boundary term depends on the history of every hole it meets (P5 p. 493), so its
  domain contains whole holes (P5 (1.33)). In the step, an old term whose domain meets Ω_{k+1} is carried to a
  domain of scale k+1 (P6 p. 34), which must contain every new hole it meets. The new holes of P5 (2.3)–(2.8) are
  not unions of π′_{k+1}-cubes: where two thick inherited pieces meet diagonally, every π′-cube through a site of
  the seam contains small-field sites (`notes/phase1/astra/ALIGNED.md` (23)–(26), at the level of the region
  step). A domain that must be a union of π′-cubes then contains small-field sites along the whole seam
  (`spill_of_defect`), its size grows linearly with the seam (`G1_cellCount`), and a coefficient constant in the
  fields, which (H.7) allows, has no decay to pay it (ALIGNED (33), `LFROOT3.md`). The same happens to the new
  terms: FLUCTUATION Theorem 4.2 and the marked expansion give terms on the domains Ŷ(S) (a small-field set with
  the holes next to it) of finite modular size; these are R11 domains (`djModFin_Yhat`) but not π′-unions at a
  seam, and the present `support` clause would force them to vanish. P5's size (1.34) and norms (1.36)–(1.37)
  use the cover cubes only through X ∩ Ω; nothing in P5–P7 uses the π′-shape of the hole part of a domain.
- **What it gives (proved, `Spine/LFBdryHole.lean`).** `Def7.exists_transfer_fineValidFinAt`: every valid domain
  X of scale k has a transfer Y ⊇ X of scale k+1 (with every new hole it meets) that is valid under R11, with
  d_{k+1}(Y) ≤ L⁻¹ d_k(X), for any shape of the new holes; with mark patches rooted at small-field sites the cost
  is 2dL per patch (`transfer_patches`). This is the blocker-3 piece of row (g2) (`LFBdryOldInput`). In the
  present class the same transfer holds only when the new holes are π′-unions
  (`Def7.exists_transfer_fineValidAt_of_open`). R11 domains keep (G1) and (G3) with the same constants
  (`DjModFin.cellCount_le`, `djModFin_union`).
- **The three routes of the brief, checked.** (i) *A property of the actual P6 construction*: refuted for the class.
  The step must work for every record of ℛ_k, and ℛ_k contains coefficients constant in the fields whose
  re-expansion is the coefficient itself: no vanishing, no crossing factor (ALIGNED (33)). (ii) *A stronger (H.7)*:
  no clause on the old coefficients helps, since the spill is created by the shape of the new hole at the next
  scale and also hits the new terms at Ŷ(S); a factor in the hole length is not produced by the construction
  (`LFH7PRIME.md`, `LFH7PRIME2.md`). (iii) *Route B (plain domains)*: it removes the spill too (a plain domain need
  not contain the seam, and its hole sites lie in the thickened inherited set, a union of π′-cubes when
  2(⌊R_k⌋ + 4) + 1 ≥ L, ALIGNED (22)), but it breaks the
  entropy bound (G2) of the domains used by the fluctuation integral and by the gas (`G2_X`,
  `D7GasRootEntropy`): with whole holes no longer required and hole sites not charged by the size, the domains
  with a given small-field part and bounded size are not finitely many uniformly in the hole (any union of
  π′-cubes of the hole may be added), so ∑_{X ∋ □} e^{−κ d(X)} grows with the hole volume. Charging the hole
  sites instead (the plain size of P1 (2.27)) changes the size, re-indexes the landed fluctuation outputs Ŷ(S)
  and the gas cores (`dExt_core_eq_d7SizeAt`), and asks a stronger (H.7) that is not known to be produced. R11 is
  the part of route B that is needed and nothing more: whole holes stay (so a domain is determined by its
  small-field cells and the holes next to them, and (G2) keeps its constant), only their π′-shape is freed.
- **Cost (landed files touched).** `LargeField/Def7FineSize.lean` (the definition; `fineValidAt_iff`;
  `fineValidAt_mono` holds only for domains whose newly small-field sites lie in π′-cubes of the domain, so
  `bdryDomsAt_mono`, `fineValid_of_fineValidPre`, `bdryDomsPre_subset_bdryDomsPost` are restated for domains
  avoiding the removed set or for removed components that are unions of π′-cubes, ~80 lines);
  `R/D7AvoidGeometry.lean`, `R/D7BoundTransport.lean` (validity across R for domains avoiding the removed set,
  ~60); `R/RExtraSize.lean` (`d7Size_le_d7SizePre_add_of_fineValid` through a cell-union core of
  `Fluctuation.modAdmissible_extend`, ~100); `R/D7GasRootEntropy.lean` with `Fluctuation/SizeModStruct`,
  `SizeModEntropy`, `SizeModHoleRoot` ((G2) over R11 domains: `X_eq_recon`, `G4_subset`, `G2_X`,
  `sum_exp_le_of_roots` as cores over `DjModFin`, the landed theorems their instances, same constant K₀, ~150);
  `Localization/P6ActiveSeed.lean` ((G1) through `DjModFin.cellCount_le`, ~10); witnesses unchanged
  (`fineValidAt_of_djMod` still holds). About 400–450 lines in 10 files. Untouched: `Def7.lean` (the records
  read `FineValidAt` through `bdryDomsPre`/`bdryDomsPost`), the history clauses, the H7 domain, the halos of R
  (`isDj_d7Pull_halo`), `RGasCore*`. The R11 side is landed (`Spine/LFBdryHole.lean`).
- **Recommendation: approve.**

## Ruling R12 asked (2026-10-21, W1151, audit W1148) — APPROVED 2026-10-21: removal histories contribute nothing to the post-R sum
- **What changes.** `postTerm2` (`LargeField/Def7v2Form.lean`) is zero for a history with `Rem_j ≠ ∅` at some `j ≤ k`;
  its 7 direct users are adjusted. The history set and its completeness are unchanged.
- **Why.** `IsComplete k (k+1)` keeps one history per pattern of removals; a history whose removed components lie
  away from every kept component has the same term as the history without them, so the post-R sum counted the
  all-small-field term n₀ ≥ 2 times (`two_le_card_empty_region`, `postTerm2_eq_of_region_empty`). The source
  (P7 (3.26)–(3.29)) has one term, with the removed components in `ℬ′` and `ℛ″`; LFR D-III.8 intended these terms
  to vanish. Evidence and options: `notes/phase1/REMOVAL-HIST.md`.

## Ruling R13 asked (2026-10-21, W1146) — the generating set of an inherited class term is the local set 𝔹_j(X)
- **What changes.** In the small-field class (`IsSF2`, `SFTermClausesStrong`, and the generating-set clause of `SFNewLevelInput`) the generating set `Tm.gs j X` attached to a level-`j` polymer `X` must be the local set `𝔹_j(X)` itself, not merely a set having `X` in its top layer `j` (which the present clause `GsSpecStrong` allows: the whole-level set satisfies it). The chain then composes the fields of each inherited term on that set. The class domain must also read the fields with the step's weights and background mass (they agree when the step's kernel coefficient is the class's `a_ker`, and, level by level, along the ideal flow of `ν_j`; otherwise the class domain is to use the step's background mass, as `Def6.bgMass` does).
- **Why the source has it.** P3 (4.4)–(4.6) and P5 (2.10)–(2.11): the term `E_j(X)` is a function of the fields composed on `𝔹_j(X)`, a set within a bounded distance of `X`, and its domain `Ξ_j(𝔹_j(X); ε_j)` only tests fields near `X`.
- **What breaks without it.** The bound of an inherited term (P1 (3.128)) holds on the class domain over `Tm.gs j X`. If that set is the whole torus, every field in the domain is nonzero at every site, while the composed fields of the step and of the local set of a polymer vanish away from the polymer. So the class's own bound says nothing at the data where the new level evaluates the term: the chain's chart premise is unsatisfiable for such classes, and the clauses (A1)–(A5) of the new level (blocker 6) cannot be derived. The locality of `E_j(X)` does not repair this: it would need to extend the field off `X`, which fails for `N = 2` around a hole of `X`.
- **Checked in Lean (W1146).** The sites `y + L^j e_μ` read by the irrelevant part are data sites of `𝔹_j(X)` (`stPlus_mem_dataSites`); the chain's settings hold with each term composed on `𝔹_j(X)` (`settings_family_castLocalB_spec_gen`); with matching weights and mass and the room `ε′ + K₂(δ₃ + δ_fl) ≤ ε_j`, the composed data of the step and of `Gb(T′)` lie in the class domain (`d2raw_mem_birthXiDom_of_top`).
- **Cost.** Three definitions, seven construction sites of the class, the composition-set clause of 16 chain files and the chart premise of 35 (10 on the formula path).
- **Recommendation (coordinator): approve (a).**
- **Amendment (W1146, 2026-10-21): the set must contain the sites read by the irrelevant part.** The inherited term of a label `(j, y, X)` is the irrelevant part `irrelTorus`, which reads the field on `X` and at the neighbours `y + L^j e_μ` of `y` (`irrelTorus_congr`); these may lie outside `X`. The chain identifies the term at the composed field with the class term at the whole-level composed field only on the top layer `j` of the composition set (`composeData_agree_on_X`, used through the chain's clause `GsSpecStrong j (XL τ) (Gj τ)`, `XL τ = X ∪ □(y)`). On `𝔹_j(X)` the neighbours outside `X` lie in a lower layer (or the collar, `j = 1`), where the composed field is a different object, so composing on `𝔹_j(X)` itself breaks that identification. The set to require is `𝔹_j(X⁺)`, `X⁺` the union of `X` and the `𝒞_j`-cubes of the neighbours `y + L^j e_μ` (`y ∈ X` aligned): the chain then composes on `Tm.gs j X` (top layer `X⁺ ⊇ X ∪ st₊(y)`), the inclusion of the composed data in the class domain is the room lemma (`d2raw_mem_birthXiDom_of_top`), and the settings construction takes `X_j = X⁺` with the cover set `XL τ ⊇ X⁺` (`settings_family_castLocalB_spec_gen`). The R13 definition change is held until this is settled.
