# Brief W17 — discharge the Gaussian kernel hypotheses (interface I-G, (G1)–(G3), (G5))

**Goal.** Make the Gaussian half of Root-C unconditional: construct the kernels `t`, `t0` and
constants `C_G, δ_G, C_P` and prove `Balaban.KernelHyp d L a t t0 C_G δ_G C_P`
(`Balaban/Correlations/GreenIdentification.lean`), so that `KernelHyp.tsum_eq_latticeGreen`
(Σ_j t_j^0 = Root-C's lattice Green's function) holds with no hypothesis. Mathematics:
`notes/phase1/CORRELATIONS.md` §2.1 (the definition of `T_j^{ℓ,μ}`, the dictionary
`T_j = L^{-j(d-2)} a_j² G_j Q_j^* C^{(j)}_{tr} Q_j G_j` (2.2), the closed form `b_j = L^{j(d-2)} a_j`,
"Mass range (D-03)", interface I-G (G1)–(G5)) and `notes/phase1/GREEN.md` G-5(a),(b).

**Landed inputs.**
- `Balaban/Correlations/TermKernel.lean` (`termKernel`, `termKernel_nested`),
  `Balaban/Gaussian/TermDictionary.lean` (`termDirect_freeSeq`, `fluctTerm_eq_termDirect`:
  the `j`-th term in closed one-shot form with `b_j`), `Balaban/Gaussian/Prolongation.lean`
  (`freeSeq`, `prolong`, `mul_prolong`).
- G-5 on unit lattices: `Balaban/Green/InfiniteVolume.lean` (`fineKernelAt`, `deltaAt`,
  `greenAt`, decay and Lipschitz bounds in `ν ∈ [0,2]`, `infiniteVolume_limits`) and
  `Balaban/Green/InfiniteVolumeUnique.lean` (`infiniteVolume_limits_unique`: limits along every
  sequence of tori, sequence-independent), `Balaban/Green/CauchyInverse.lean`
  (`cauchy_inv_entries`), `Balaban/Green/LimitCauchy.lean`.

**Steps.**
1. **Rescaling dictionary.** Express `termKernel d L (freeSeq d L a) μ (j+1) j m x y` (fine lattice,
   spacing 1, blocks of side `L^j`) through the unit-lattice objects of `InfiniteVolume.lean` with
   `k = j`, `N = L^j`, unit-lattice mass `ν_j = μ L^{2j}`, `a = a_j`, `a' = a` — the identity (2.2)
   of CORRELATIONS.md §2.1 in Lean, including the factor `L^{-j(d-2)}` and the treatment of `j = 0`
   (`T_0 = M_0^{-1}`, no `a_0`). State exactly what you prove; if the landed definitions force a
   slightly different dictionary, use theirs and say so.
2. **Mass range.** G-5 is landed for `ν ∈ [0,2]`. I-G needs (G1) for all `μ ∈ (0,2]` and all `j`
   (unit-lattice masses up to `2L^{2j}`) but (G2), (G3) only near `μ = 0`. Choose one and say which:
   (a) extend the needed parts of G-5 to `ν ∈ [0, ν_max]` with constants depending on `ν_max`
   (only uniformity in the torus matters for (G1)); or (b) weaken `KernelHyp` to what the consumers
   actually use (read every use of `g1`, `g2`, `g3`, `g5` in `GreenIdentification.lean` and in
   `Balaban/Correlations/*`; e.g. `g5` is used only through `sum_rule_limit` before `μ ↓ 0` at fixed
   `J`), changing `KernelHyp` and its consumers in place (non-frozen files; keep every downstream
   theorem's conclusion, in particular `KernelHyp.tsum_eq_latticeGreen`). Option (b) is preferred
   when it removes the need for large unit-lattice masses.
3. **(G1)** from `infiniteVolume_limits_unique` (limits of tori through multiples of `L^{j+1}`) and
   the dictionary; **(G3)** and **(G2) at `μ = 0`** from the Lipschitz bounds (limit as `ν ↓ 0`) and
   the decay bounds, converted from block-`L²`/unit-lattice form to pointwise fine-lattice form
   `|t_j^0(x,y)| ≤ C_G L^{-j(d-2)} e^{-δ_G L^{-j}|x−y|}` (`KernelDecay`); if a pointwise fine-lattice
   bound is not available from the landed block-`L²` statements, use the pointwise G-2(ii) layer
   (`Balaban.Multiscale.prop48`, single layer) or report the precise gap. **(G5)** the prolongation
   bound.
4. **Assembly.** `theorem kernelHyp_holds` (name free): for `d ≥ 3`, `L ≥ 2` (or whatever the
   landed G-5 needs; state it), `a` in the range of CORRELATIONS.md C-1* (`a_j ∈ (1/2, 3/2)`), there
   exist `t t0 C_G δ_G C_P` with `KernelHyp …`; and the unconditional corollary of
   `KernelHyp.tsum_eq_latticeGreen`.

**Ownership.** New files under `Balaban/Correlations/` (e.g. `KernelDictionary.lean`,
`KernelHypProof.lean`) in your worktree `/home/scott/Balaban-worktrees/W17` (branch
`w17-kernel-hyp`), plus import lines in `Balaban.lean`; in-place edits of
`Balaban/Correlations/GreenIdentification.lean` and its consumers only under option (b) of step 2
(say which). Small additions to landed `Balaban/Green/*` files only if unavoidable (say which).
Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`. Copy freely from any of the
author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Step 4, or about 2,500 lines, or a precise obstruction (a dictionary identity or
bound that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; which option in step 2; checks and results;
axioms; open questions; last commit hash.
