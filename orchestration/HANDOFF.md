# Orchestrator handoff (Balaban campaign, phase 1)

Written 2026-10-12 ~06:45 UTC by the orchestrator session scott-41 (account claude-2, weekly quota
nearly exhausted). A new orchestrator session should read AGENTS.md, this file, and the last ~60 rows of
`orchestration/LEDGER.md`, then continue. Policies: at most 4 Sonnet + 1 Opus subagents, no
sub-subagents ("Do not launch subagents" in every brief), hard rules of AGENTS.md verbatim in every brief
(including rule 9: never kill processes you did not start). Heavy mathematics goes to astra
(codex, GPT-6-Sol xhigh, in tmux), Lean to Sonnet workers in worktrees.

## Landing procedure (unchanged)

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

Sonnet (background subagents of scott-41; they die with the session — if so, restart from the brief
in the ledger row and the branch state):
- W70: DONE (landed 017b7c9; χ^dom identity still open).


- W75: DONE (landed d6829a5).
- W81 (`w81-lf-consol`): DmodOmega nnComp (queued item 4), lattice II.5.10, χ^dom identity.
- W76: DONE (landed c9ac759).
- W79: DONE (landed dd7b11e).
- W80 (`w80-tinf-bridge`): T∞ summability, tail lemma, bridge redirected to T∞ with SumConds.
- W77: DONE (landed 7c6b40b).
- W82 (`w82-base`): LFR Q1, Q5, Q6 (base record, base kernels, (S2) at k=0).
- W78 (`w78-deccover`): DecCover abstraction (VMOD §3, orders 2, 4, 5) — queued item 1 below is now running.

astra (tmux sessions `astra-<name>`, scratch dirs /home/scott/Balaban-scratch/astra-<name>/, all on
codex-1; each prints "<TAG> DONE"; results are copied into notes/phase1/ and committed):
- astra-kf0: followup2.txt — choose kf = max(k̂_f, 1) (kf = 1 admissible for ν ∈ (7/8 L⁻², 1]),
  check LF-8 with final mass ≤ L², write LF-BASE-KF0 Part C; then base step Part A. Tag KF0C.
- astra-class: followup1.txt — I6-ANISO.md (anisotropic I-6, Lean-ready). Tag I6ANISO.
- astra-vmod: followup1.txt — VMOD-2.md (OPEN-COV-MARGIN, OPEN-NC-MIXED). Tag VMOD2.
- astra-rgfree: followup1.txt — RGFREE-2.md (mass-free fluctuation bound, switch joint, observable
  H7). Tag RGFREE2.
- astra-fluctfix: followup1.txt — FLUCTUATION v2.1 (Lemma 2.5 constants, Theorem 3.1(f)). Tag
  FLUCTFIX2.
If a session shows "Selected model is at capacity", resend the one-line pointer message.
Sending to a codex TUI: `tmux send-keys -t S -l "<one line>"; tmux send-keys -t S Enter`
(long pastes get truncated — always point to a file).

## Queued Lean packages (in rough priority)

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

## Waiting on Scott

- Second-freeze proposal `notes/phase1/SURFACE-V2-PROPOSAL.md`.
- Roland questions (merges, small-field pockets, kernel locality, β-dependence; OBSERVABLES §6).

## Quota at handoff (06:34 UTC)

claude-2 14% (this session), claude-1 92%, claude-10 83%; codex-1 88%, codex-3 47%.
