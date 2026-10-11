# Brief W21 — the global Hölder bound (G-2(iii) for all pairs; Hölder part of G-2(iv))

**Goal.** Complete G-2 of `notes/phase1/GREEN.md` (§3 statements (iii), (iv); proofs §4.5:
Proposition 4.9 and "Proof of G-2(iv) (global form)", including the remark "the Hölder norm of P2
(3.17) for `x ∈ Δ(y)`, `x' ∈ Δ̃(y)` involves points of neighbouring blocks, handled by the same
estimate with the ball enlarged by a factor 3"). Consumer: background fields I-1(e)
(`notes/phase1/BACKGROUND.md` v2, §5.2, "I-1(e) (Hölder, separate item)"), P1 (3.107).

Landed: `Balaban.Multiscale.prop49` (`Balaban/Multiscale/PointwiseHolderMain.lean`; nearby pairs
only: layer 1 with `pathDist ≤ 1`, or `d‖z‖ ≤ L^{j−1}`), `holder_bound`, `lemma_loc_c`,
`green_holder_sum`; `prop48`; `global_bound` (`GlobalBound.lean`, G-2(iv) without the Hölder part).

1. **All pairs of P2 (3.17).** Define the Hölder seminorm
   `|f|_{(θ),σ} = max_j sup_{y∈Λ_j} sup_{x∈Δ(y), x'∈Δ̃(y), x≠x'} ℓ_j^σ |x−x'|^{−(1−θ)} |f(x)−f(x')|` (GREEN.md
   §1.5 line 164, for bond functions `∂u` with bonds in the same direction) and prove G-2(iii) for all
   such pairs: far pairs (`r > ρ/4`) by `prop48` (`|∂u(b)−∂u(b')| ≤ 2 max U/ℓ_j`), near pairs by
   `prop49`/`holder_bound`, the pairs across neighbouring blocks by the enlarged ball.
2. **Global form.** `|∂Gf|_{(θ),2−θ} ≤ B_θ |f|₂`, `B_θ = C(d,L)/θ`, by the block decomposition and
   summation of `global_bound` (reuse its `blockPiece`/`sum_siteWeight_blockPiece`).
3. State the combined G-2(iv) (all four terms) as one theorem.

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `HolderGlobal.lean`) in your worktree
`/home/scott/Balaban-worktrees/W21` (branch `w21-global-holder`), plus import lines in
`Balaban.lean`. Small additions to landed files only if unavoidable (say which). Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
