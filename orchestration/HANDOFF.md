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
| W249 (Opus, FINISHED, HELD) | `w249-d7-fine-size` / W249 | D7 boundary size → fine chosen-cover size, pre and post records; branch b5ea946 checked by the worker; land with scripts/land.sh after Scott has seen the report (no objection = land) |
| W277 | `w277-param-carrier-local` / W277 | compact carrier of the step's block measures; locality and bound for parameter families of marks (PARAM package 4, generic) |
| W278 | `w278-root-det-chart` / W278 | RootDetChart: trace bound, cut expansion, bound of cut differences, endpoint identity (ROOTDET package 1) |
| W279 | `w279-p6-top-rooted-fiber` / W279 | fixed-support sum for the top cover (VMOD-31 package v) |
| W280 | `w280-root-det-zero` / W280 | decLog at zero cuts; DET-CUT-FACTOR stated (ROOTDET package 2, first half) |
| W281 | `w281-general-class-witness` / W281 | a non-zero class member matched to a step: ClassParamMatch, OldXiDomC, path analyticity instantiated |
| W282 (Opus) | `w282-general-activity` / W282 | general-class direct activity bound: general forms of Wone/Wtwo = hat functionals, StepActivityBound with preserved rate (GENERAL §3, packages 4–5) |
| W283 | `w283-root-marked-bound` / W283 | markedTerm: rooted class bound for the marked part of the new energy terms (ROOT (R7), marked part) |
| W276 | `w276-top-block-transport` / W276 | TopBlockTransport: datum sites and interface pairs of the retained shell read by ChiDomProp (Q13-COVER §2) |
No temporary rule-10 exemptions are open. Sonnet workers stall on large analytic briefs — give ONE bounded target per brief, with a written derivation where the mathematics is not in the landed files.
Next Sonnet packages: (1) Lemma I.3.9 locality in Lean → discharge QuietStepInput.quiet_local/Rq_eq; (2) joint witness at L ≥ 3 with a quiet component at k ≥ 1 (InhabitedJoint uses L = 2, BgHyp needs L ≥ 3); (3) psiZero (P3) once the effective action on Z₀ exists; (4) Lean for astra round-8 results.
astra (cap 3; state 2026-10-13): q13 Q13-ALIGN (tag Q13ALIGN, FRESH conversation started with `/new` and the self-contained prompt `/home/scott/Balaban-scratch/astra-q13/fresh_r31.txt` after the old conversation failed with "Error running remote compact task"; for later rounds in a fresh conversation keep prompts self-contained: preamble of fresh_r31.txt + task); fluctfix DAPHYS (tag DAPHYS: does the smallness (DA) of `stepActivityBound_zeroClass_direct` hold for large β at fixed block scale); vmod VMOD-32 TOP-PRODUCER (tag VMOD32: `P6_COEF_ROOTED_XB` for the top-only cover). Done this session and in notes/phase1: ROOT, ROOTDET, VMOD-31, Q13-COMPOSED. QUEUED astra rounds: DET-FOREST (connected trace forest for the differentiated decoupled logarithm, ROOTDET §2–§3), ROOT-MARK-ANCHOR (physical marks contain the root cube), `ParentDomainFromFactors`/`FactorBondLift` after W276 reports. OPEN DECISIONS WITH SCOTT: (1) generator ruling L/G/M (recommendation L; hold `OutputTermSkeleton`, changes to `GsSpecStrong`/class clauses, CHART packages); (2) W249 D7 boundary-size change (branch `w249-d7-fine-size`; first report recorded in the ledger; sent back to move the pre-R records to the fine size too; reported to Scott — land when the follow-up is checked unless he objects). ROLAND items ready to relay: 13 (three addenda), 14 (two addenda; VMOD-31/32 may replace the second addendum by the question whether P6 (4.32)–(4.34) permits a full-torus top-only auxiliary cover). NEXT SONNET PACKAGES (all generator-neutral): after W279 `P6SourceCoverCharge` (VMOD-25 (1.1)); `RootDetHull` once the hull assignment is specified by astra; `GeneralClassRegularC` (GENERAL package 4), `GeneralWPhysicalMatch` (5); `ParamMarksPhysical` (PARAM package 3) after W277's field-by-field table; `FactorBondLift`, `ScaledR12` (Q13-COVER); `LocalGenMixed`, `LocalGenHalo`; evenness of `vc.v1`; the repair of the A-term/correction lattice mismatch after Q13-ALIGN.
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
