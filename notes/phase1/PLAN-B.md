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

## Ruling R13 asked (2026-10-21, W1146) — APPROVED 2026-10-21 in the amended form (𝔹_j(X⁺); the chain's cover set X⁺ ∪ □(y); the class domain with the step's weights and background mass): the generating set of an inherited class term is a local set
- **What changes.** In the small-field class (`IsSF2`, `SFTermClausesStrong`, and the generating-set clause of `SFNewLevelInput`) the generating set `Tm.gs j X` attached to a level-`j` polymer `X` must be the local set `𝔹_j(X)` itself, not merely a set having `X` in its top layer `j` (which the present clause `GsSpecStrong` allows: the whole-level set satisfies it). The chain then composes the fields of each inherited term on that set. The class domain must also read the fields with the step's weights and background mass (they agree when the step's kernel coefficient is the class's `a_ker`, and, level by level, along the ideal flow of `ν_j`; otherwise the class domain is to use the step's background mass, as `Def6.bgMass` does).
- **Why the source has it.** P3 (4.4)–(4.6) and P5 (2.10)–(2.11): the term `E_j(X)` is a function of the fields composed on `𝔹_j(X)`, a set within a bounded distance of `X`, and its domain `Ξ_j(𝔹_j(X); ε_j)` only tests fields near `X`.
- **What breaks without it.** The bound of an inherited term (P1 (3.128)) holds on the class domain over `Tm.gs j X`. If that set is the whole torus, every field in the domain is nonzero at every site, while the composed fields of the step and of the local set of a polymer vanish away from the polymer. So the class's own bound says nothing at the data where the new level evaluates the term: the chain's chart premise is unsatisfiable for such classes, and the clauses (A1)–(A5) of the new level (blocker 6) cannot be derived. The locality of `E_j(X)` does not repair this: it would need to extend the field off `X`, which fails for `N = 2` around a hole of `X`.
- **Checked in Lean (W1146).** The sites `y + L^j e_μ` read by the irrelevant part are data sites of `𝔹_j(X)` (`stPlus_mem_dataSites`); the chain's settings hold with each term composed on `𝔹_j(X)` (`settings_family_castLocalB_spec_gen`); with matching weights and mass and the room `ε′ + K₂(δ₃ + δ_fl) ≤ ε_j`, the composed data of the step and of `Gb(T′)` lie in the class domain (`d2raw_mem_birthXiDom_of_top`).
- **Cost.** Three definitions, seven construction sites of the class, the composition-set clause of 16 chain files and the chart premise of 35 (10 on the formula path).
- **Recommendation (coordinator): approve (a).**
- **Amendment (W1146, 2026-10-21): the set must contain the sites read by the irrelevant part.** The inherited term of a label `(j, y, X)` is the irrelevant part `irrelTorus`, which reads the field on `X` and at the neighbours `y + L^j e_μ` of `y` (`irrelTorus_congr`); these may lie outside `X`. The chain identifies the term at the composed field with the class term at the whole-level composed field only on the top layer `j` of the composition set (`composeData_agree_on_X`, used through the chain's clause `GsSpecStrong j (XL τ) (Gj τ)`, `XL τ = X ∪ □(y)`). On `𝔹_j(X)` the neighbours outside `X` lie in a lower layer (or the collar, `j = 1`), where the composed field is a different object, so composing on `𝔹_j(X)` itself breaks that identification. The set to require is `𝔹_j(X⁺)`, `X⁺` the union of `X` and the `𝒞_j`-cubes of the neighbours `y + L^j e_μ` (`y ∈ X` aligned): the chain then composes on `Tm.gs j X` (top layer `X⁺ ⊇ X ∪ st₊(y)`), the inclusion of the composed data in the class domain is the room lemma (`d2raw_mem_birthXiDom_of_top`), and the settings construction takes `X_j = X⁺` with the cover set `XL τ ⊇ X⁺` (`settings_family_castLocalB_spec_gen`). The R13 definition change is held until this is settled.

## Ruling R15 asked (2026-10-21, ORCH-A): the cell term of `irrelTorus` — renormalize only polymers inside a fixed box
- **Problem.** At the cell `X = □(y)`, `irrelTorus` adds `Σ_{X'∋y}(T_{X'} + Φ_{y,X'})` over every polymer through `y`,
  wrapping ones included. The flow's couplings are common to all tori, so the renormalization conditions hold only in
  infinite volume (`RenormCondAlong`), not on each torus (P1 (H.6)); the sum is a small nonzero defect that differs
  between two tori, and the exact two-torus agreement at the cell (`CellTermsAgree`, blocker 7's step clause) is false.
- **Proposal.** With `B(y)` the box of radius `r_k = ⌊L^{m₀+m₁+k}/8⌋` fine sites around `y` (1/8 of the side of the
  smallest torus with `L^{m₀} ∣ N₁`; polymers in it do not wind on any torus of the family):
  `ℰ_irrel(y,X) = ℰ(y,X) − A_{y,X} − 1[X ⊆ B(y)](T_X + Φ_{y,X}) + 1[X = □(y)] Σ_{X'∋y, X'⊆B(y)} (T_{X'} + Φ_{y,X'})`.
  Larger polymers keep their relevant parts and are small by size (`d_j(X) ≳ L^{k−j}`). Only the body of `irrelTorus`
  changes; the torus identity `Σ ℰ_irrel = ℰ`, the class and the infinite-volume conditions are unchanged; the top one or
  two levels get no extraction (the chain treats the top `n₁` levels separately).
- **Blocker 6 (the bound at the cell label).** No torus form of the conditions is needed, under either definition: the
  landed `norm_filed_le_power` (W980) bounds the full torus filed sum by `C E₀ L^{−(k−j)(d+α₃)}` on every torus with
  `L^{m₀} ∣ N₁`; under R15 the large shapes add a tail of the same order.
- **Work (ORCH-A, worker A1, branch `orchA-cellterm`).** The core `irrelTorusOn` (the landed `irrelTorus` its instance),
  its identity, bounds and two-torus agreement at the box instance; after approval, the body switch.
- **Implemented (A1, 9ca0652e, branch `orchA-r15`; approved by Scott 2026-10-21).** `irrelTorus := irrelTorusOn (relBox m₀)`;
  the identity and congr/analytic/rot unchanged; the non-cell bounds take `relBox P.m₀ y X` (M1 form kept); the large
  labels `norm_E_sub_aTermTorus_le_of_not_relBox`; every label `irrelTorus_label_bound_of_class(_birth_cap)`; the cell
  agreement `irrelTorus_cell_boxAgree`, `CellTermsAgree` by `cellTermsAgree_of_class`, the step clause with `hcell`
  discharged `newLevel_coeff_twoTorus_of_class_cells_R15`.

## Readings proposed 2026-10-21 (W1154, plan B; no landed definition changes): the step on a region and the old terms (blocker 3)
- **Reading HS-1, the step on a region** (P5 (2.16)–(2.48), (3.1)–(3.2); `Fluctuation/HoleStep*.lean`, `Spine/LFHoleStep*.lean`).
  Sets: G = 𝔹_k(W_k) (`p6OldC`) ≺ G′ = (𝔹_k(W_k) ∩ Ω^c_{k+1}) ∪ Λ_{k+1} of (2.17) (`p6TopC`), datum ψ_k off Ω_{k+1}
  and θ = z ψ_{k+1} on it (`liftMixed`). (2.17) is the composed background of G′; (2.18) and C^{(k)1/2}_loc (2.35) are
  the decoupled background and covariance root of (C, G′), C = `coverOf` G′, at the vector equal to s on the cover cubes
  inside R_{k+1}(□′) and 0 outside (`slocOf`), R_{k+1}(□′) = cubes of 𝕋_{k+1} within ⌊R_k⌋ of □′ (`locDomC`). The exponent
  of (2.48)/(3.2) is the log of the integrand of (2.16) (kernel at z ψ_{k+1}, 𝒜_k + ℱ_k + ℛ^{(k)} on Z^c_k, holomorphic)
  at the composed field (2.39), plus ½|ψ̂|² + u ℬ''^{(k)}; χ_k is carried by T′^{(k)} and dμ′ ((2.44)–(2.47)); by (2.38)
  this is P5's exponent up to a constant. The pre-localized terms that (3.1) moves into ℬ'' stay in it (kind (i)).
- **Reading HS-1′ (approved 2026-10-21), the coefficient on the local pair** (P5 (2.18)–(2.20), p. 505: the approximate
  background "depends only on R_{k+1}(□′)"; P3 Prop. 2.3; P6 p. 33). What: the coefficient T(X, J) of an old term, its
  average and `oldB` are computed on the local pair (C_V, G′_V), the restriction of (`coverOf` G′, G′) to V(X, J) = the
  r-collar of A_X ∪ ⋃J (datum, decoupled background and covariance root of the local pair); new definitions beside those of
  HS-1, tied by the comparison lemma (local = global when the global datum is in the I-4b domain). Why: under HS-1 the
  composite is `Dec2.decBgField` of the global pair, a choice needing the whole datum on G′ in Ψ̃^c(G′), while (D7) quantifies
  over all fields with H7(Y) constraining only the cubes of Y; so `loc_field` fails and `analytic` fails on H7(Y), and the
  extension of local good data to global good data fails for N = 2 around a hole (R13).
- **OPEN-P6-X1-INSTANTIATION.** P6 p. 34: "we consider this term as localized in X ∩ Ω_{k+1}, we introduce the same
  localization extension as before … the domains Y₁ may have several components, each of them containing at least one
  component of X ∩ Ω_{k+1}". Reading: X₀ = A_X = X ∩ Ω_{k+1}, and the uncut core X₁ = the sites within r of A_X
  (`collarCoreC`), the pair condition X₀^{∼r₀} ⊂ X₁ of P3 (2.14) that P5 (2.18) uses for (□′, R_{k+1}(□′)) (without a
  collar the read sites at the edge of A_X are cut points of the decoupled problem); the parameters are the cover cubes
  not inside X₁ (`parCubes`), set to 1 inside X₁; at □′ ⊂ Ω_{k+1} the vector is that of reading HS-1 (0 outside R_{k+1}(□′)).
  Output domains by (4.44)[3] through the optimal covers of X (`assignOut`, `assignWt`). Needs: the cell count of X₁ by
  d_k(X) (`P6ActiveSeed`, times the collar factor), and the H7 validity of the extension (OPEN-H7-MIXED).
- **OPEN-P6-ACTIVE-COMPOSITE-LOC.** Under reading HS-1 the "old operator" of the substitution is the operator of the one set G′
  (its layers off Ω_{k+1} are those of 𝔹_k(W_k)), with the one cover C = `coverOf` G′: background, covariance and
  covariance root at the vector s all belong to (C, G′), and the composition with G is a block average. Reading: the
  statement to prove is the AE locality (AE2) of s ↦ ℬ^{(k)}(X)(composed field) on the incidence component of X₁ ∪ J
  for the decoupled objects of the single pair (C, G′) — the same-set decoupling locality (`Decoupled2FpLocal`,
  `Dec2Covariance.decCovSqrt_BD_of_GsxBD`, `DecSqrtCutFactor.CovStanding.decCovSqrt_agree`), plus the spectator part
  (old spins on X ∩ Ω^c_{k+1}, h, g fixed: P5 (2.35), (2.39); proved by `composedMulti_out`, `composedMulti_of_lt`).
  Status (W1154, 2026-10-21): PROVED under reading HS-1 (`Fluctuation/HoleStepOldLocal.lean`: `oldInterp_localityAEOn`,
  `oldCoef_eq_zero_of_not_reached`, `oldCoef_congr_of_agreeReach`), given the standing analytic conditions of the pair at
  the localization vectors (domain of I-4b, `AdmPot`, units of `1 - 𝒦_x`, `M_x`: part of OPEN-H7-MIXED) and two geometric
  conditions on the localization domains (each read point covered by a centre with footprint in the core and in its
  domain; domains deep in Ω₁(G′), P3 (2.14) X₁ ⊂ Ω₁ with the collar of the cross lemmas). History instance PROVED
  (`Spine/LFOldLocal.lean`, `oldCoefLF_eq_zero_of_not_reached`): both geometric conditions hold for the domains
  R_{k+1}(□′) ∩ (deep part of Ω₁(G′)) and the 6-cell collar of A_X; the standing conditions follow from the datum in the
  chart Ξ^c(G′; 1, ε) (`standing_of_xiCData`); (coverOf G′, G′) has `CoverBase`/`XCover` (`p6TopC_coverBase`). Remaining
  input: the datum in the chart (OPEN-H7-MIXED) and the (D7) field locality of the record's term.
- **OPEN-H7-MIXED.** Reading: the image lemma for the composite of reading HS-1: for (θ, h, g) in the target H7 domain of
  scale k+1 (P5 (1.36)–(1.37) at Ω_{k+1}), |ψ̂| < p₁(β_k) and |s_P| ≤ e^{κ₁}, the multiscale field `composedMulti` (the
  composed field on the unit points of Ω_{k+1}, the record's fields elsewhere) lies in the source H7 domain of scale k
  on which the record's ℬ^{(k)}(X) is analytic with its bound ((D7) `analytic`, `bound`). It is one statement about the
  single pair (C, G′) (the background and covariance-root bounds of the decoupled objects, `Decoupled2XBounds`,
  `CovSqrtSupComplexDec`), not two mixed generating sets.

## Obstruction (W1154b, 2026-10-21): OPEN-H7-MIXED for the local pair — the named inputs are false as stated; ruling request
- **Proved false** (`Balaban/Spine/LFOldH7Refute.lean`, axioms `propext, Classical.choice, Quot.sound`):
  `not_h7MixedDatumLoc` — at zero sharp masses (`μ_j = 0`, the scales below `k₀`), for every set `V` whose local set
  `G′_V` (`locG'`) has a data site and every `Y_f` containing the fine images of its data sites on which the mixed cube
  tests are void (e.g. `V` one `𝒞_1`-cube of the old operator set and `Y_f` the image of the data sites of `G′_V`, which
  contains no cube of `𝕋_{i+1}`), `H7MixedDatumLoc` fails whenever `2 δ_b ≤ min(1, |z|) sinh t` and `2 sinh t ≤ c₀`;
  `not_h7MixedDatumLoc_of_le_c7` — the instance at the constants of its use (`δ_b ≤ c₇`, `0 ≤ BG`, `|z| ≥ 1/2`;
  `c7_le_bgC0_div_eight`: `c₇ ≤ c₀/8`). Consequence: the hypothesis `hDat` of `norm_oldCoefLoc_le_of_inputs`,
  `analyticOnNhd_oldCoefLoc_fluct`, `norm_oldMarkLF_le`, `measurable_oldMarkLF`, `oldClusterLF_spec`, `norm_oldClusterSite_le`,
  `norm_oldBAt_le`, `norm_oldB_le` cannot be met at zero sharp mass: these theorems say nothing there.
- **Mechanism.** The cube tests `Δ^c_q(□; 1, ε)` of the H7 domain (Definition II.3.5 (a); `DeltaC` = `RegC` with the
  domain conjunct `InUnionDomainC G c₀ c₁ μ` of BG Theorem 5.2) admit lifted data whose complex part has modulus up to
  `c₀ + c₁`, and at zero mass no inequality of `RegIneq` bounds a complex rotation of a constant field: the boost
  `w = cosh t e_{i₀} - i sinh t e_{i₁}` (`boostMat`, `Rᵀ R = 1`) has background `w` (`bgFieldC_rot`), multiplier `0`, and
  passes every cube test for every `ε > 0` (`deltaC_rotConst`, `h7Domain_rotConst`). The chain of the local pair (Theorems
  I-4b, I-4c as used in `analyticOnNhd_oldInterp`, `decDom_of_bgBounds`) needs the datum in `Ψ̃^c(δ_b, δ_b)`, complex part
  `< 2 δ_b ≤ 2 c₇ ≤ c₀/4` (`not_inDomainC_of_im`). Generalizing that chain to `Ψ̃^c(δ, ε)` (`δ ≤ c₇`, `ε ≤ c₀`; I-4b
  `i4b_exists_unique` already allows it, `DecDom` allows `|φ| < 3/2`) leaves the complex parts in `(c₀ + c₇, c₀ + c₁)`
  uncovered when `c₇ < c₁`, and gives no room across the step: the target and the source H7 domains have the same complex
  radius, while the composite adds `O(β_k^{-1/2} r_ψ)` and the change of background to the complex part.
- **Three further defects of reading HS-1′ and of the two named inputs** (independent of the ruling below):
  (D1) *the set `Y_f`*: the named inputs quantify over every `Y_f ⊇` data sites of `G′_V` (and `X`); the H7 domain at
  `Y_f` tests only the cubes contained in `Y_f`, so for a small `Y_f` the field is free. Repair: `Y_f` contains the cubes
  of `𝕋_k`, `𝕋_{k+1}` within 3 cubes of those sites (in the application `Y_f` is the fine set of the output label, which
  contains the `π′_{k+1}`-cubes of the mark site).
  (D2) *the stencil* (`H7MixedInnerLoc`): the source H7 domain at `X` reads the composed field on the cubes within 3
  cubes of the cubes of `X` (`deltaC_stencil`); the sites of `Ω_{k+1}` there need not lie within `r + r′` of
  `A_X = X ∩ Ω_{k+1}` (`X` may meet `Ω_{k+1}` far from a place where it only touches it), and at those sites the composed
  multiscale field is `ψ_k`, which the H7 domain of scale `k + 1` does not constrain on `Ω_{k+1}`. Repair: the core of
  `V(X, J)` is the `r`-collar of `Ω_{k+1} ∩ X^{∼3}` (the sites of `Ω_{k+1}` in the cubes of `𝕋_k` within 3 cubes of `X`);
  the cell count of `OldResumSite` changes by a factor depending on `d` only.
  (D3) *the datum of the local pair* (`holeStepLoc`): it is the mixed lift with `Ω` = the top layer of `G′_V`; at the
  sites of `Ω_{k+1}` in the lower layers of `G′_V` (where `V` cuts a `𝒞_{k+1}`-cube of `Ω_{k+1}`) and in its collar it reads
  `ψ_k`, which is not a variable of the density of scale `k + 1` (it is integrated). So `T(X, J)` depends on `ψ_k` on
  `Ω_{k+1}`, the identity with the old part of the step fails, and no domain condition on the target field controls the
  datum there. **Reading HS-2 (proposed):** the datum of the local pair is the restriction of the global mixed lift
  (`Ω` = the blocks of `Ω_{k+1}`): `θ = z ψ_{k+1}` at every site of `Ω_{k+1}`, `ψ_k` elsewhere (layer constant on `G′_V`).
- **Ruling request (proposed; for the author).** (a) *Recommended:* the complex radius of the H7 cube domains is of the
  order of their tolerance, as in P5 (1.36) (complex neighbourhoods of radius `ε_j`): in `DeltaC`, `DeltaPrimeC`
  (`LargeField/Characteristic/Analytic.lean`) the domain conjunct `InUnionDomainC G c₀ c₁ μ` becomes membership of the
  lifted datum in `Ψ̃^c(G; K ε, K ε)` (`InDomainC G μ (K ε) (K ε)`, `K` fixed, `K ε_j ≤ c₇`). Then the datum of the local
  pair (repaired by D1–D3) lies in `Ψ̃^c(δ_b, δ_b)` with `δ_b = K′ ε_{k+1}` by patching the per-cube data, and the
  room `ε_{k+1} → ε_k` pays the composite. Cost: the two definitions; the readers of the domain conjunct
  (`H7BridgeCube.deltaC_inUnionDomainC` and its users in `Theorem42*`, `CubeActionBound`) keep it through the inclusion
  `Ψ̃^c(Kε, Kε) ⊆ 𝒟` for `Kε ≤ c₁`; `h7Domain_composedMulti_of_inner` and the users of `H7Domain` as a whole
  (`LargeField/R/*`, `Def7*`) are generic in the cube tests.
  (b) Keep the BG radius, cap the complex part (`InUnionDomainC G (c₀/2) c₁`), and generalize the chain of the local pair
  to `Ψ̃^c(δ, ε)`: closes the margin but leaves no room across scales; not recommended. (c) `O(N, ℂ)`-covariance of the
  step (rotate the datum to near-real): fails for fields whose complex part varies over the local set (`V` is unbounded);
  not recommended.
- **Status of blocker 3 after W1154b.** Items (1)–(4) of the W1154b brief are blocked by this obstruction: (1) is false as
  stated and needs the ruling and D1–D3; the bound of (2)–(4) rests on (1); the identity (3) needs D3.
- **Reading HS-2 (W1154b, 2026-10-21; the repairs D1–D3 of reading HS-1′, beside the landed objects;
  `Spine/LFOldHS2.lean`).** (D3) the datum of the local pair is the restriction of the global mixed lift
  (`holeStepLoc2`: `θ = z ψ_{k+1}` on every block of `Ω_{k+1}`, `ψ_k` elsewhere; `holeStepLoc2_D'_Ψ_eq`: it is the
  datum of the step at the common data sites; `holeStepLoc2_D'_Ψ_congr`: it does not read `ψ_k` on `Ω_{k+1}`).
  (D2) the local set `V₂(X, J) = locSetXJ (X^{∼3}) J` (`stencilX`, `locSetXJ2`): its core is the `r`-collar of
  `Ω_{k+1} ∩ X^{∼3}`, so for `r′ ≥ L^{k+1+m₁}` the sites of `Ω_{k+1}` read by the cube tests of the H7 domain of `X`
  are unit points of the local pair (`mem_top_locG'_locSetXJ2`); the parameter core `X₁` (the `r`-collar of `A_X`,
  where the decoupling parameters are `1`) is unchanged. The resummation at a mark site holds for these local sets:
  `oldResumSite2_holds` (`OldResumSiteAt stencilX`), from the core `oldResumSiteAt_holds` with the cell count
  `card_cells_stencilCore_le` (`#cells_{k+1}(Ω_{k+1} ∩ X^{∼3}) ≤ 9^d c₁ (1 + d_k(X))`: a cube within 3 cubes of
  `u ∈ X` whose coarse cube is in `Ω_{k+1}` forces `u ∉ Z_k`, P5 (2.3)); the landed `oldResumSite_holds` is the
  instance `σ = id`, `c_S = c₁` of the same core (the bodies of `markBase`, `markSite`, `GoodJ`, `famAt`,
  `OldResumSite` are now built from `markBaseAt`, `markSiteAt`, `GoodJAt`, `famAtAt`, `OldResumSiteAt`,
  definitionally equal; landed statements unchanged). (D1) the named inputs ask the H7 domain at a set `Y_f`
  containing the cubes of `𝕋_k` and `𝕋_{k+1}` within 3 cubes of the sites read (`CubesNearIn`).
  Restated named inputs: `H7MixedInnerLoc2` (for every `X`, `J`, with `V = V₂(X, J)`; open) and `H7MixedDatumLoc2`
  (for every `V`; open, and false at zero sharp mass with the present cube domains, as for its predecessor; it is
  stated for the cube domains of the ruling request R14), with `h7Domain_composedMulti_loc2`. Not yet done: the
  chain of pieces 5c–5q (coefficient, marks, cluster terms, `oldB` and its bound) on `holeStepLoc2` and `V₂`; it
  waits for the decision on R14, which changes its domain hypotheses.
- **Reading HS-2, the chain on the local pairs (W1154c, 2026-10-21).** Pieces 5c–5q and W1158's coefficient clauses are
  cores over the readings of the local pair (`Spine/LFHoleStepLoc` … `Spine/LFOldBBound`, `Spine/LFOldD7*Loc`): the
  datum is a parameter `glob` of `holeStepLocAt` (`locTop`: the top set of the mixed lift is the global top layer
  `Ω_{k+1}` for `glob = true`, the top layer of the restricted set for `glob = false`), the local set of a label `X` is
  `V(σ X, J)`; the landed HS-1′ objects are the instances `glob = false`, `σ = id` (statements unchanged, bodies calls
  of the cores; `holeStepLoc` is now an `abbrev`). The cores take, in place of the named inputs, the two local
  conditions they use (`hD`: the datum in `Ψ̃^c(δ_b, δ_b)`; `hdom`: the composed multiscale field in the source H7
  domain at `X`), and at an output label `Y` the conditions for the old labels and families whose mark sites lie in
  `T` with `Ŷ(T) = Y` (`hloc`). Instances for HS-2 (`glob = true`, `σ = stencilX`): `oldCoefLoc2`,
  `norm_oldCoefLoc2_le_of_inputs`, `oldB2`, **`norm_oldB2_le`** (`Spine/LFOldHS2Chain`; conditional on
  `H7MixedInnerLoc2`, `H7MixedDatumLoc2`, with `OldResumSiteAt stencilX` proved by `oldResumSite2_holds`) and the
  coefficient clauses `oldCoefLoc2_rot`, `_im`, `_congr_fields`, `_analytic_family(_LF)`, `_euclid`,
  `holeStepLoc2_congr_hist_Z`, `stepReadsIn_outLabel2` (`Spine/LFOldHS2D7`).
  **Amendment of D1 (W1154c).** The named inputs of HS-2 ask the cubes of `𝕋_{k+1}` *of* the sites read to lie in `Y_f`
  (`CubesOfIn`; for `H7MixedInnerLoc2` the sites of the stencil `X^{∼3}` and the data sites of `G′_V`, for
  `H7MixedDatumLoc2` the data sites), not the cubes *within 3 cubes* of them (`CubesNearIn`, removed): the output label
  `Ŷ(T)` has no margin around the mark site (its `π′`-cubes start at the cells of the base sites), so the 3-neighbourhoods
  do not lie in it, while every site of `Ŷ(T)` has its cube there (`cubesOfIn_fineSet`); every site read is still read
  by the test at its own cube, which also reads its neighbours. The stencil of an old label lies in `Ŷ(T)`
  (`d7Pull_stencilX_subset_outLabel`: it is connected, `siteConnected_d7Pull_stencilX`, and its sites in `Ω_{k+1}` are
  sites of the core of `V₂(X, J)`, hence of the mark site). With this the conditions of the cores at an output label
  follow from the two named inputs (`locConds_of_h7MixedLoc2`).
  **The remaining inputs (open).** `H7MixedInnerLoc2` is P5 Lemma 2.1 in the complex domains (Balaban: "we will have to
  prove a more general statement in Sect. 2 of the third paper"): for the cubes of `𝕋_k` near `Ω_{k+1}` the composed field
  `ψ^{(k)}_loc(θ) + β_k^{-1/2} C^{(k)1/2}_loc ψ̂` passes the scale-`k` cube tests; its proof needs the datum of the local
  pair in the domain of I-4b (the background bounds; without it `decBgField` is `0`), the comparison of the background of
  the cube set `G_k(□)` at the composed field with the background of the local pair, and room conditions on `r_ψ`, `R`
  and the tolerances (the named input has none, so it is a schematic statement to be proved under them).
  `H7MixedDatumLoc2` waits for R14.

## Reading B-1 (ORCH-B, accepted 2026-10-21 by the main orchestrator; blocker 5, the box split)
- The small-field half of the last integral is the term of P7 (4.9)/(4.11) with no final large-field region: the fluctuation
  integral with the cutoff χ({|ψ'| < p₁}) of the whitened fluctuation field on every site (P4 (6.6)). The integral of
  `sfFactor2` over the whole torus (`sfIntegral`, cutoff χ_k) is not that term: on {χ_k ≠ 0} ∖ box the source creates new
  large-field regions (P7 pp. 530–531, the fluctuation integral as in P5 §3), and χ_k is a product of cube functions of ψ_k,
  not local in the whitened variable, so it cannot enter a polymer expansion over the product measure.
- Restated (`Spine/LastIntegral.lean`, names kept): `Ξ_box = Z_K ∫ 1_{box(p₁)} sfGaussIntegrand(centre h, K) dγ`
  (`sfBoxIntegral`), `K = β_k D` (`sfFinalK`, D the final Hessian; `pdQuad_sfFinalK`, `actStar2_univ_hessian_sfFinalHm`),
  box(p₁) = {w : |w_p| ≤ p₁ ∀ p}; `FinalSmallFieldInput`: Ξ_box = exp(E + ⟨g,h⟩ + Σ_j Σ_X q_j + Σ_X a); `FinalLargeFieldInput`:
  ∫ρ = Ξ_box exp(Σ_X b) (the tail joins the large-field half). Both take the cutoff `cut κ c₉ β_k = p₁` as a parameter and
  `lastIntegralInput_of_parts` combines them at the same cutoff. Constraints on p₁: χ_k = 1 on the box (B p₁ ≪ β_k^{1/2} δ_k),
  analyticity room (B(κ) β_k^{-1/2} p₁ < c ε_k), the tail (p₂ < 2p); p₁ = A₁ (log β_k)^{p₀}, A₁ ≪ A₀, meets all three.
  `H7MixedDatumLoc2` is stated for the cube domains of R14 (approved, below).
- **The (D7) clauses of the old part at an output label (W1154c, item (5)).** `Spine/LFOldBD7.lean`, generic in the
  readings (`glob`, `σ`) and in the interaction: an interaction family `LocIntFam` (labels and constants of Theorem 3.4
  fixed, activities over a parameter, `Fluctuation/MarkClusterFam`) so that the clauses comparing two values of the
  fields compare one cluster expansion. PROVED: `support` (`oldBAtAt_eq_zero_of_not_valid`), `loc_field`
  (`oldBAtAt_congr_fields`, from the record's clause through `oldCoefLocAt_congr_fields`), `real` (`oldBAtAt_im`), `rot`
  (`oldBAtAt_rot`), `analytic` (`oldBAtAt_analyticOnNhd`); `bound` is `norm_oldBAtAt_le_of_dom` / `norm_oldB2_le`. Their
  hypotheses are properties of the interaction family (locality, reality, covariance, analyticity in `(fields, u)`) and of
  the coefficients on the balls of the marks (`oldCoefLocAt_im`, `oldCoefLocAt_rot`, analyticity of the marks in the
  fields). Infrastructure: `Gst_conj`, `markTerm_conj` (`Fluctuation/MarkClusterReal`), `Gst_equiv`, `markTerm_equiv`,
  `HoleStep.markOf_rot` (`Fluctuation/MarkClusterEquiv`), `markTerm_analyticOnNhd` (`Fluctuation/MarkClusterAnalytic`).
  Open: `euclid` and `loc_hist` (transports between the cluster expansions of two regions, `Gst_transport`).
  **Findings for the identity (4).** (i) *The external field.* `oldBOf` ignores the argument `h` of the boundary terms and
  uses the fixed `h₀`, `hv`; the clause `rot` of (D7) rotates `h` with the fields but not `hv`, so for the step's terms the
  old part must read `h`: proposal, `h₀ := Re h`, `hv := Re h` (equal to the physical field on `hSetB hv = {hv}`; `rot` by
  `oldCoefLocAt_rot` since `Re (R h) = R (Re h)`; `real`, `loc_field` unchanged). (ii) *The histories.* The old part at a
  history `𝔸′` of the successor reads the record's terms at its representative `pre 𝔸′ ∈ rep.hist` (`Agree k k`), not at
  `𝔸′`; `oldBAtAt` already takes the region `H = 𝔸′.H` and the record history separately. (iii) *The families.* For the
  clauses the unit points, cubes and interaction family must not depend on the fields (`oldBOf` lets them depend on `ψ`).
  **Scope of (3) and (2).** The interaction of the measure of P5 (3.2) is the localization of P6 (4.29) + (4.32): the old
  terms (their re-expansion is the coefficient machinery above) and the action part (P6 Lemma 4.2, the Taylor remainders
  of (4.29) with the `δ₀` terms (4.30)–(4.31)). The landed engine of Proposition 3.3 (`Interaction*`, `Prop33*`, `FlCore`)
  is stated for level pairs (`IsLevel Hm k`, `IsLevel Gp (k+1)`, used in 26 files); the hole step's `G′` is not a level set.
  `H7MixedInnerLoc2` likewise: the landed real-domain P5 Lemma 2.1 (`Fluctuation/Lemma25`, `lemma25_field`) is stated for
  level pairs and real fields. Both need the non-level (region) forms of these files.
- **Ruling request R14, APPROVED (Scott, 2026-10-21, "approve all"; W1154b, applied by W1154c).** In
  `DeltaC`, `DeltaPrimeC` (`LargeField/Characteristic/Analytic.lean`) the domain conjunct `InUnionDomainC G c₀ c₁ μ`
  becomes `InDomainC G μ ε ε` (the lifted datum, resp. pair, in `Ψ̃^c(ε, ε)`, `K = 1`); the reader of the domain conjunct
  keeps it through `inUnionDomainC_of_inDomainC_eps` (`Ψ̃^c(ε, ε) ⊆ 𝒟` for `0 < ε ≤ c₁`, `μ L^{2q} ≤ 1`):
  `H7BridgeCube.deltaC_inUnionDomainC` takes these three hypotheses; `Theorem42WireGeom` reads the regularity part
  directly. In `Spine/LFOldH7Refute.lean` the refutation (`deltaC_rotConst`, `h7Domain_rotConst`,
  `not_h7MixedDatumLoc`, `not_h7MixedDatumLoc_of_le_c7`) no longer holds and is replaced by `not_mem_deltaC_of_im`:
  the new cube domains exclude constant fields with a coordinate of imaginary part `≥ 2 ε`.

## Reading B-1′ (ORCH-B, accepted 2026-10-21 by the main orchestrator with conditions; blocker 5, the whitening of the box)
- The last fluctuation integral is whitened with the localized square root, as in the source (P7 §4, pp. 530–531, "exactly as in Sect. 3 [5]"; P5 (2.39)): `ψ_k = h + β_k^{-1/2} L ψ̂`, ψ̂ standard Gaussian, the box in ψ̂, `L` the rows of `boxCut` at the localized parameters (B1's definition). With the exact `K^{-1/2}` the class cutoff χ_k is not local in the Gaussian variable.
- The change of variables is exact, at every invertible `A = β_k^{-1/2} L`: `∫ F dψ = |det A| (2π)^{n/2} ∫ F(h + Aψ̂) e^{|ψ̂|²/2} dγ(ψ̂)` (`integral_spin_whiten`); the Jacobian (`whitenNorm`) and the mismatch `exp(-½⟨ψ̂, (AᵀKA − 1)ψ̂⟩)` (`mismatchFactor`) are defined factors of the integrand (`integral_mul_sfFactor2_whiten`, `ctxBoxIntegralL`, `ctxFluctBoxIntegralL`); at `A = K^{-1/2}` the mismatch is 1 and the landed forms are the instances.
- The local form (`BoxLocalForm … A … ε_U W U`) carries the mismatch as an undilated even part `U` (pair terms; smallness and evenness proved by B1 from the row bounds); the parity argument dilates `W` only.
- Spine level: `sfBoxIntegral` (and so `FinalSmallFieldInput`, `FinalLargeFieldInput`, `lastIntegralInput_of_parts`) moves to B1's `L` when it lands, the same in both halves, never to a free whitening; until then the spine stays at the instance `K^{-1/2}` (`ctxBoxIntegral`).

## Reading B-1″ (ORCH-B, adopted 2026-10-21, accepted by the main orchestrator; blocker 5, the local-pair principle; `A64-DESIGN.md` §4)
- Every piece of the last integral at a localization domain `X` (whitening row, centre, Gaussian mismatch piece, localized term, Jacobian piece) is computed on the local pair `𝔓(X)`: the generating set and the massive final operator restricted to `X^{+m}`, as in reading HS-1′. Source: P5 (2.18), (2.35), (2.39), the local pairs `(□′, R_{k+1}(□′))`; P7 (4.11), the completion keeps the terms whose domains meet `Z′` and `Z′^c`.
- Why (obstruction O1): the rows of B-1′'s `boxCut` read the whole-torus `unconstrainedUnitOperator`, and its mismatch the whole-torus Hessian; the regional operators differ from them at every pair, so regional and whole-torus activities would differ everywhere by amounts depending on all of `Z′`, which are not couplings of a linked gas.
- Whitening: row `p` is row `p` of the inverse square root of the final Hessian of the massive problem on `𝔓(locDom p)` (B1), with one comparison lemma: for any ambient generating set (whole torus or regional) the local-pair row is close to the row of the ambient Hessian's inverse square root when `locDom p` lies deep in the ambient region.
- The three conditions of B-1′ stand: the whitening is a defined object fixed at the spine; the change of variables is exact, with the determinant and the mismatch in the integrand; the smallness of the mismatch is proved.
- Consequence: for every history and every piece whose local pair lies deep in `Ω_A`, the regional piece is the whole-torus piece (exact completion); `Ξ_box` is the instance `Z = ∅`.
