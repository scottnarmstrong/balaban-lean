# Brief W17b — the Gaussian kernels at unit-lattice masses up to `ν_max` (I-G at the top scales)

**Goal.** Root-C's assembly (CORRELATIONS.md §3, Lemma 3.0 and Step B) uses the limits
`t_j^μ = lim_ℓ T_j^{ℓ,μ}` and the bound
`|T_j^{ℓ,μ}(x,y)|, |t_j^μ(x,y)| ≤ C_G L^{-j(d-2)} e^{-δ_G L^{-j}|x−y|}` (uniform in `ℓ`) at
`μ = νδ_j(ν)` for every `j < J(ν)`, where `L^{J(ν)}√ν ≤ L²` and `δ_j ≤ 2`. The unit-lattice mass of
the scale-`(j+1)` operator is then `μ L^{2(j+1)} ≤ 2L⁴`. W17 (landed: `Balaban.kernelHyp_holds`,
`Balaban/Correlations/Kernel*.lean`, `FineGreenLimits.lean`) proves (G1)–(G3), (G5) only for
`μ L^{2(j+1)} ≤ 1`, because the landed G-5 (`Balaban/Green/InfiniteVolume*.lean`,
`LimitCauchy.lean`) is stated for unit-lattice masses `ν ∈ [0,2]`. This package removes that limit
(CORRELATIONS.md §2.1 "Mass range (D-03)").

**Statements to prove** (names free; constants depending on `d, L, a, ν_max` only):
1. **G-5 for `ν ∈ [0, ν_max]`.** For every `ν_max ≥ 2`: the one-scale decay bounds, Lipschitz
   bounds and infinite-volume limits of `InfiniteVolume.lean`/`InfiniteVolumeUnique.lean` and the
   fine-level bounds of `FineGreenLimits.lean`, `KernelPointwise.lean` for `ν ∈ [0, ν_max]`. The
   operators are only more coercive for larger `ν`; the constants that grow are the operator-norm
   upper bounds (`‖H‖ ≤ 4dN² + ν + a`) entering Combes–Thomas and the Cauchy lemma. Prefer
   generalizing the landed statements by a parameter `ν_max` (keeping the old ones as the case
   `ν_max = 2`, so no consumer breaks) over copying them.
2. **(G1) and (G2) at the top scales.** With `t` the kernel family of `kernelHyp_holds`: for all
   `j`, `μ > 0` with `μ L^{2(j+1)} ≤ ν_max`, `T_j^{ℓ,μ}(x,y) → t_j^μ(x,y)` along tori through multiples
   of `L^{j+1}`, and the bound above for `T_j^{ℓ,μ}` (uniform in `ℓ`) and `t_j^μ`, with `C_G, δ_G`
   depending on `ν_max`. Make sure the limit kernel is the same function `t` that `kernelHyp_holds`
   produces on the overlap of the ranges (extend `tLim`, do not introduce a second family).
3. The corollary in the form Root-C needs: for `ν ∈ (0,1]`, `j < J` with `L^J√ν ≤ L²` and
   `μ ∈ (0, 2ν]`, the conclusions of 2 hold (take `ν_max = 2L⁴`).

**Coordination.** Worker W19 (Root-C assembly) is stating these facts as an explicit hypothesis
structure (`KernelHypLarge` or similar, in `Balaban/Correlations/`). If it has landed when you
finish, also prove that structure; otherwise state your theorems so that discharging it is a few
lines, and say how.

**Ownership.** New files under `Balaban/Correlations/` or `Balaban/Green/` (e.g.
`KernelLarge.lean`, `InfiniteVolumeMass.lean`) in your worktree
`/home/scott/Balaban-worktrees/W17b` (branch `w17b-large-masses`), plus import lines in
`Balaban.lean`; generalizing landed `Balaban/Green/*` and `Balaban/Correlations/Kernel*` statements
by a mass parameter is allowed (say which; keep the old names as specializations). Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; which landed statements were generalized;
checks and results; axioms; open questions; last commit hash.
