# Orchestrator handoff (Balaban campaign, phase 1)

Written 2026-10-12 ~06:45 UTC by the orchestrator session scott-41 (account claude-2, weekly quota
nearly exhausted). A new orchestrator session should read AGENTS.md, this file, and the last ~60 rows of
`orchestration/LEDGER.md`, then continue. Policies: at most 7 Sonnet + 1 Opus subagents (raised 2026-10-12), no
sub-subagents ("Do not launch subagents" in every brief), hard rules of AGENTS.md verbatim in every brief
(including rule 9: never kill processes you did not start). Heavy mathematics goes to astra
(codex, GPT-6-Sol xhigh, in tmux; AT MOST 3 astra sessions working at once — Scott 2026-10-12; close idle ones after committing results), Lean to Sonnet workers in worktrees.

## STATE (2026-10-13 early UTC, session on claude-1)

Claude workers (background subagents of this session):
| Worker | Branch / worktree | Task |
|---|---|---|
Deferred cleanup: the landed renormalization wrappers at R.t (`StepTowerRen*.lean`, `RenormSharedClass.lean`, `RenormLocC2ZeroTower.lean`, `RenormExpInputTower.lean`) duplicate the `_at` proofs of `RenormRadius*.lean`; make them corollaries when the lane is quiet.
OPEN DESIGN (RATES): after regrouping onto collar hulls the observable/mark coefficient rate (3/2·κdec)/60751 − 3375·log 2 is not positive at the tower's κdec; κdec is pinned by `κdec_eq` and not boosted by κmin. Also: coefficients not known to vanish off connected cube sets (remainder R in `thm31b_zeroClass_polymer_fromTower`).
| RATES / HATY decision | `notes/phase1/RATES.md`, `HATY.md`, ledger rows | marks and observable are indexed by the site sets `sitesOf T` themselves (already 𝒟_{k+1} domains, `dExt = sizeJ`, no loss); no collar hull, no `renYs` fibre map for them; tower numerals unchanged; open gate: common `IsLocExp` domain family with the determinant and C_i records (HATY leaf 5); `StepTowerG` on hold until that gate is designed |
| W571 (Opus) | `w571-step-identity-fibre` / W571 | uniform step identity on the fibre (TSTEPID leaves 1, 2, 3, 6); tell it when W570's `e0CoeffFamily_value_fromTower` is on main |
| W585 | `w585-obs-ev-raw-y` / W585 | exact locality of the observable's `Ev` (edits `ObsMarksAssembly`, `ObsCoeffAnalytic`, `ObsCoeffLocal`) |
| W587 | `w587-pair-spec-export` / W587 | export the pair's defining properties through the producer chain of the pair family (strengthening in place) |
| W588 | `w588-ren-class-witness` / W588 | RENJOIN leaf 1: class witnesses; extension of the three localization principles to the union family |
| landing queue | branches `w582-fan-geometry-dedup`, `w578-two-torus-box-geometry`, `w583-fnu-expansion-direct-raw-y` (worktree W583 is the integration worktree) | FINISHED; batch: merge the first two and origin/main into w583, rebuild there, then `scripts/land.sh w583-…` |
| W586 | `w586-obs-family-prefactor` / W586 | observable family bound in the form C·obsPrefactor (corollary by re-packing) |
| W589 | `w589-two-torus-thick-sets` / W589 (based on w578) | two-torus correspondence of `active`, `layerIndex`, `resDep`, `thickSet`, decoupling index type, `Ysites`, `compY` |
| W590 | `w590-ren-m0-site-record` / W590 | RENJOIN leaf 4: observable term at the renormalized datum as `IsLocExp` on site domains for a fixed source, generic in a family with exact locality |
| W591 | `w591-eterm-expansion-raw-y` / W591 (based on w583) | exact locality of the old-term (E, M) expansions; reading task T5(c): every statement between the sharp expansions and `physical_directTerms_eta(_scaled)` carrying the thick relation |
| exact locality through the assembly | `Balaban-scratch/astra-q13/SHARPREL.md` (running) | design question: sharpen the definition `physAgΘ` in place (126 occurrences, no statement text changes; producers must deliver exact locality) versus twin statements; do not start the assembly worker before the note is read |
| named witnesses | `notes/phase1/PAIRNAME.md`, `TORUSCOH2.md` | DECIDED (option A): the analytic pair stays existential with exported properties; explicit witnesses get formula exports. Next two-torus leaf available: TORUSCOH2 leaf 1 (`boxCompatible_unitBg`, source/fluctuation coordinate maps) |
| general record | `notes/phase1/STOWERG.md`, `GENLAYER.md` | **APPROVED by the author 2026-10-13** (record `StepTowerG` and mechanism B′: general theorems, 3,3,2 statements as corollaries in the same landing). Read `Balaban-scratch/astra-vmod/ROOTBOUND.md` (running: does the root's quantifier order κ, c₉ before L, M change the field list?) before the record is written; then STOWERG tasks 1–10 |
| generator ruling | `notes/phase1/GENERATOR.md`, `CHART.md` | **L APPROVED by the author 2026-10-13**: local generator 𝔹_j(X) in a versioned successor class; plan of leaves requested from astra (`GENL`), do not edit `IsSF2` consumers before the plan is filed |
No temporary rule-10 exemptions are open. Sonnet workers stall on large analytic briefs — give ONE bounded target per brief, with a written derivation where the mathematics is not in the landed files.
Next Sonnet packages: (1) Lemma I.3.9 locality in Lean → discharge QuietStepInput.quiet_local/Rq_eq; (2) joint witness at L ≥ 3 with a quiet component at k ≥ 1 (InhabitedJoint uses L = 2, BgHyp needs L ≥ 3); (3) psiZero (P3) once the effective action on Z₀ exists; (4) Lean for astra round-8 results.
astra (cap 3; state 2026-10-13, second update): q13 DETCAUCHY (tag DETCAUCHY, fresh conversation, prompt `~/Balaban-scratch/astra-q13/fresh_detcauchy.txt`: can the polydisc route close the rooted determinant bound — rate κ₁ − log 2 per cut with a volume-independent constant e^{N₀κ₁}, given the cut-factor support); fluctfix MARKS (physical first-order marks anchored at the root, as a family in the datum); vmod VMOD-34 READ-SPLIT (prove or refute active-only coefficient support for F♯). DONE and in notes/phase1 this session: ROOT, ROOTDET, VMOD-31, Q13-COMPOSED, Q13-ALIGN, DAPHYS, VMOD-32, PHYSCUBIC, VMOD-33, DETFOREST. KEY STATE: (1) rate route: zero-class rate preservation landed; smallness in the physical regime needs the scaled energy bound (E*) — elementary, W295 — then propagation through InteractionHatV/Prop33/sharp assembly (PHYSCUBIC package 3), source-zero assembly landed (W288), radius tower W294, numerics W297. (2) P6 item 14: build with F♯ (VMOD-33); top-cover files landed but unused; the open physical statement is active-only coefficient support (Roland item 14 third addendum in notes/QUESTIONS-ROLAND-2.md). (3) Q13: `inPsiTilde_genW_of_factors` landed with four named open inputs (ActiveFactor, R1/R2 over Y, mass smallness). (4) Determinant: cut expansion, zero cuts, block diagonality under provisos landed; W290 on provisos; route under review (DETCAUCHY). (5) D7 boundary size change LANDED (W249). OPEN DECISION WITH SCOTT: generator ruling L/G/M (recommendation L; hold `OutputTermSkeleton`, changes to `GsSpecStrong`/class clauses, CHART packages). ROLAND items ready to relay: 13 (three addenda), 14 (three addenda; the third supersedes the question part of the second). NEXT SONNET PACKAGES: PHYSCUBIC package 3 (after W295); `P6FineSourceCast`, `P6PairedIncidence` (VMOD-33 §4); `DetForestHull`/`DetForestChart` per DETCAUCHY; marks packages per MARKS; `GeneralWPhysicalMatch` is inside Opus W282; `LocalGenMixed`, `LocalGenHalo`; evenness of `vc.v1`; `AlignedI6Transport`; the fibre count m = L^{jd} for `jBlock`.
basek (BASE-KERNEL-3: remaining Prop II.7.9), rgfree (RGFREE-6: mass-uniform domain, FREE-ACT-TUBE,
SWITCH-JOINT), kf0 (Part G: heavy activity for gasOp_pe, (B.5), k_f=0). Idle: class, fluctfix, vacuity.

## Landing procedure (unchanged; NEW: every new hypothesis structure must come with a `Nonempty` witness)

1. Read the worker's handoff; `git diff --stat origin/main...HEAD`, grep new files for
   `sorry|^axiom|maxHeartbeats`.
2. Axiom probe in the worktree: a scratch `AxWnn.lean` with `import Balaban` and `#print axioms` of the
   main theorems (correct namespace!), `lake env lean AxWnn.lean`, then delete it. Do this BEFORE land.sh.
3. `cd /home/scott/Balaban && set -o pipefail && scripts/land.sh <branch> "<msg>" | tail -3` — use
   `pipefail` so a refusal is not masked; land.sh refuses if main has uncommitted changes outside notes/.
4. `git worktree remove --force /home/scott/Balaban-worktrees/Wnn && git branch -D <branch>`.
5. Ledger row; commit + push.
Worktree setup: `git worktree add -q <path> -b <branch>`, `mkdir -p <path>/.lake`,
`cp .lake/package-overrides.json <path>/.lake/`, `cp -a .lake/build <path>/.lake/`,
`(cd <path> && elan override set ocreg-throttled)`.

## Running at handoff

POLICY (Scott, 2026-10-12): keep 4 Sonnet (+≤1 Opus) Lean workers running regardless of quota; Scott resets
accounts when quota runs out.

Sonnet (W83–W86 launched ~08:35 UTC; background subagents of scott-41; they die with the session — if so, restart from the brief
in the ledger row and the branch state):
- W70: DONE (landed 017b7c9; χ^dom identity still open).


- W75: DONE (landed d6829a5).
- W81: DONE (landed 6dd2084; χ^dom identity false as formalized → queued item 8).
- W76: DONE (landed c9ac759).
- W79: DONE (landed dd7b11e).
- W80: DONE (landed; bridgeInf gives PremisesCore ∧ SumConds from the class).
- W77: DONE (landed 7c6b40b).
- W82: DONE (landed; Q1 complete, Q5/Q6 blocked on an under-specified Def II.7.6 → queued item 9).
- W83 (`w83-reynolds`): Reynolds average → full I-6 Premises from Def-6.
- W84: DONE (landed b1e5034).
- W89 (`w89-weighted51`): weighted Prop 5.1 → Lemma 4.1 unconditional; Lemma 3.5 analyticity.
- W90 (OPUS, `w90-i6-aniso`): anisotropic I-6 per notes/phase1/I6-ANISO.md.
Queued Sonnet (next free slots): (a) [running as W91] then I-5 with ψ′ on the new interface;
(b) base step Q5/Q6 per BASE-KERNEL.md (conditional on Prop II.7.9 parts).
- W85: DONE (landed b3b1f92; P4 estimate half). Found the vacuous-history defect.
- W87: DONE (landed 4a1bc48; histories inhabited).
- W91 (`w91-dec2-locality`): VMOD-4 locality interface on Dec2.
- W86: DONE (landed 6637c62; χ^dom identity proved).
- W88 (`w88-complex-g1`): det∘exp, complex log det, Lemma 2.4(a) complex.
- W78: DONE (landed c6f82f7).

astra (tmux sessions `astra-<name>`, scratch dirs /home/scott/Balaban-scratch/astra-<name>/, all on
codex-1; each prints "<TAG> DONE"; results are copied into notes/phase1/ and committed). Round 5 sent
~09:40 UTC (round 4 + vacuity audit committed in 6b82960):
- astra-basek: followup1.txt — BASE-KERNEL-2.md (C^{(0)} localization, cutoff transfer, first small-field
  integral / half-budget). Tag BASEK2.
- astra-vmod: followup4.txt — VMOD-5.md (mixed wall NC3, reverse partition, graph counting). Tag VMOD5.
- astra-rgfree: followup4.txt — RGFREE-5.md (FREE-ACT, SWITCH-JOINT on the repaired domain). Tag RGFREE5.
- astra-kf0: followup5.txt — Part F (sector weights → gasOp_pe form, (B.5), k_f=0 assembly). Tag KF0F.
- astra-fluctfix: followup3.txt — FLUCTUATION v2.3, Theorem 3.1(f). Tag FLUCTFIX4.
- astra-vacuity: followup1.txt — VACUITY-AUDIT-2.md (post-W87 re-audit, joint witnesses). Tag VACUITY2.
- astra-class: idle.
If a session shows "Selected model is at capacity", resend the one-line pointer message.
Sending to a codex TUI: `tmux send-keys -t S -l "<one line>"; tmux send-keys -t S Enter`
(long pastes get truncated — always point to a file).

## Queued Lean packages (in rough priority)

0. (new) I-5 with ψ′ (VMOD order 7) on the landed Dec2 layer, conditional on `CoverLocal` instances
   for the mixed pairs (theorem hypotheses = the instance; fields proved later from VMOD-3).

1. W78 DecCover abstraction (VMOD §3.2–3.3, orders 2, 4, 5): `DecCover C`, `CoverCompatible C H`,
   generalize DG/I-4a by hypotheses, concrete wrapper C = H. 3.5k–6k lines.
2. Def-6 amendments per CLASS-RULINGS (accepted): `momentSum` → `Edens`; `pavingSymGroup` +
   `fullJSymGroup`, `eucEloc/eucMloc`; thermodynamic (H.5) on an infinite-volume family T∞
   (stabilization + tail bound); Reynolds average over paving offsets; redirect the bridge
   (`Def6Bridge*`) to T∞.
3. Anisotropic I-6 rework once I6-ANISO.md lands (replace isotropic Tube premises by XiDom + radius
   ε_j; RenormSmall/RenormIso/RenormTermwiseIrrel).
4. LF `DmodOmega`: use nearest-neighbour components `nnComp` (CLASS-RULINGS Q-E), keep `starComp`.
5. Wire FLUCT Lemma 2.5 (`chiFl_absorbs_of`) to W71/W73 results after FLUCT v2.1 fixes the constants.
6. FLUCT modules 11 (Renorm, Lemma 3.5, Thm 3.1(g),(h)), 13 (Lemma 4.1), 14 (Switch scalar part);
   LFR Part III blocks P1–P16 (none started), Q1, Q5–Q7 after W77.
7. Doc touch-up: LFR IV.1.3 prefactor per FLUCT v2 FL-A04.
9. Base step Q5/Q6: needs an astra reconstruction of the k=0 kernel factor by factor (P5 (2.47) × P6 (3.2) at k=0: cube sets for P/Q/R/S, which bonds belong to the kernel, ψ′₀ factors), C^{(0)1/2}_loc and H, the explicit b₀; a `baseMainAction` with the spin-gradient energy on Λ₀. Then Q5/Q6 in Lean.
8. LF localized-field domain fix (W81 item 3): `subMultiscaleField` vs `genBlocksIn` on localized histories; decide the definition change (level-k field on the V-support, or restrict genBlocksIn to the component), then prove the χ^dom identity. Also `quietKernel_euclid` (II.5.10 lattice part; several thousand lines).

## Waiting on Scott

- Second-freeze proposal `notes/phase1/SURFACE-V2-PROPOSAL.md`.
- Roland questions (merges, small-field pockets, kernel locality, β-dependence; OBSERVABLES §6).

## Quota at handoff (06:34 UTC)

claude-2 14% (this session), claude-1 92%, claude-10 83%; codex-1 88%, codex-3 47%.
