# Orchestrator handoff (Balaban campaign, phase 1)

Written 2026-10-12 ~06:45 UTC by the orchestrator session scott-41 (account claude-2, weekly quota
nearly exhausted). A new orchestrator session should read AGENTS.md, this file, and the last ~60 rows of
`orchestration/LEDGER.md`, then continue. Policies: at most 4 Sonnet + 1 Opus subagents, no
sub-subagents ("Do not launch subagents" in every brief), hard rules of AGENTS.md verbatim in every brief
(including rule 9: never kill processes you did not start). Heavy mathematics goes to astra
(codex, GPT-6-Sol xhigh, in tmux), Lean to Sonnet workers in worktrees.

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
- W84 (`w84-fluct-wire`): FLUCT Lemma 2.5 source form, Lemma 3.5, Lemma 4.1.
- W85: DONE (landed b3b1f92; P4 estimate half). Found the vacuous-history defect.
- W87 (`w87-horizon`): fix vacuous FlowSteps/RegionSeq/RegionHistory (finite horizon), Nonempty witnesses, repair ~60 consumers. PRIORITY.
- W86 (`w86-lf-domain`): LF localized-field domain fix + χ^dom identity (queued item 8).
- W78: DONE (landed c6f82f7).

astra (tmux sessions `astra-<name>`, scratch dirs /home/scott/Balaban-scratch/astra-<name>/, all on
codex-1; each prints "<TAG> DONE"; results are copied into notes/phase1/ and committed). State at
~08:20 UTC (round 3 committed in e98dcbe):
- astra-kf0: followup4.txt — Route D: (B.5) activity estimate with hole normalization for gasOp_pe,
  torus-exact walk activities, k_f=0 assembly; LF-BASE-KF0 Part E. Tag KF0E.
- astra-class: followup1.txt — I6-ANISO.md (anisotropic I-6, Lean-ready). Tag I6ANISO. (long-running)
- astra-vmod: followup3.txt — VMOD-4.md: redesign the Dec2 locality fields (cubeP_sub/own_cover force
  equal first domains — VMOD-3 obstruction) and prove the replacements for mixed pairs. Tag VMOD4.
- astra-rgfree: followup3.txt — RGFREE-4.md: repaired switch domain / density class, mass-free IsSF
  domain, H7 domain (RGFREE-3 counterexample), SWITCH-JOINT, FREE-ACT. Tag RGFREE4.
- astra-fluctfix: IDLE (v2.2 committed). Next: Theorem 3.1(f) once I6-ANISO lands (needs anisotropic
  I-6 and the mixed-background H7 inclusion).
- astra-basek: prompt.txt — BASE-KERNEL.md (k=0 kernel, C^{(0)}, H, b₀, baseMainAction, II.7.7-8).
  Tag BASEK.
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
