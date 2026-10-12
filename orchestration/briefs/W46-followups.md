# Brief W46 — three follow-ups: the ν-free RG matrix, (Ξ4) for the composed field, the block count

1. **`matrixFree`** (`notes/phase1/SMALLFIELD.md` v3 §3.7, Lemma 3.1′): the ν-free matrix for k < k₀
   (`a₁₁ = a`, `a₂₁ = 0`, `a₂₂ = 1`, `a₃₂ = (m/a)(−1 + aτ/24)`, `a₃₃ = ½`, `a₃₁ = ε[aτ/24 + m ϱ₃₁]` with
   `|ϱ₃₁| ≤ C_ϱ`, `m C_ϱ ≤ 2.4` as a hypothesis — ϱ₃₁ is not yet computed), `triangularBounds_matrixFree`,
   the `_map`/`_conj` compatibility lemmas and analyticity (as for the landed `matrixInfty` in
   `Balaban/Flow/MatrixInfty.lean`), and the convention selector by `k < k₀`. Then the analogue of
   `rg_step_infty` for the ν-free system (`Balaban/Flow/RGInfty.lean`) if it is a direct reuse.
2. **(Ξ4) for the composed field** (SMALLFIELD v3 §1.8; the landed reduction
   `Balaban.SmallField.composeField_eq_blockMean_ext`, `composeField_sub_blockMean_ext_le` in
   `XiComposeField.lean`; the Hölder bound `xiC_holder`/`bgFieldC_holder`): prove
   `|ψ_j(y+e_μ+e_ν) − ψ_j(y+e_μ) − ψ_j(y+e_ν) + ψ_j(y)| ≤ K_Σ s^{2−α₁} ε_k` for all μ, ν on the level-j
   lattice, `s = L^{−(k−j)}`, `K_Σ = 2(d+2)K₁C_{α₁} + 4` (or the constant your proof gives), under the
   explicit condition `L^j ≤ ℓ(x)` (§1.8: interface sites UNCERTAIN, excluded). Needs a block-translation
   lemma for the block mean `Q_n` and chaining of the Hölder bound along a path.
3. **Block count** (`notes/phase1/LOCALIZATION.md` v3 companion to GM2; W45 open item): the single-scale
   bound `n_j(X) ≤ L^{2d} C_d (treeLenCovOne X + 1)` (torus metric, a far-apart subfamily of cells,
   disjoint balls, `|W| ≤ |E| + 1`), and the multi-layer bound `n(Y) ≤ L^{2d} C_d (treeLenCov Y + 1)` under an
   explicit separation hypothesis `ϱ ≥ c M` (state the exact one you need), on
   `Balaban/Localization/TreeLengthCov.lean`.

**Ownership.** New files (e.g. `Balaban/Flow/MatrixFree.lean`, `Balaban/SmallField/XiFour.lean`,
`Balaban/Localization/BlockCount.lean`) in your worktree `/home/scott/Balaban-worktrees/W46` (branch
`w46-followups`), plus import lines in `Balaban.lean`. Workers W39 (`Localization/Decoupled*`), W41
(`LargeField/Counter/*`, `LargeField/History/*`), W43 (`SmallField/Renormalization*`) are active: do not
touch their files. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each item.

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction per item.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
