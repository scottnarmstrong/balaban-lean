# Brief W8a — multiscale generating sets and multiscale coercivity G-1(a)

**Goal.** Formalize the multiscale setting of `notes/phase1/GREEN.md` §1.2–§1.4 (final version)
and prove the multiscale coercivity G-1(a) (§3 statement, §4.1 proof):

1. **Definitions** (work on the fine torus `Torus d ℓ` with unit spacing, `ℓ = N₀·L^k`, and carry
   the lattice spacing `η` only as explicit scaling factors; record the dictionary to GREEN.md's
   `η`-units in the module docstring):
   - a *generating set*: a decreasing family `Ω₁ ⊇ Ω₂ ⊇ … ⊇ Ω_k` of finite sets of sites, each `Ω_j`
     a union of `j`-blocks (blocks of side `L^j`, `Balaban/Lattice/Blocks.lean`), with the
     separation condition (S) of §1.2 (`dist(Ω_j^c, Ω_{j+1}) > ϱ L^j` in fine units);
   - the layers (`Ω_j ∖ Ω_{j+1}`, `Ω_{k+1} = ∅`), the multiscale spacing `ℓ(x) = L^j` on layer `j`;
   - the multiscale averaging form `⟨u, Q^*aQ u⟩ = Σ_j a_j L^{−2j} Σ_{B ⊂ layer j} ‖P_B u‖²` (1.4), with
     `a_j ∈ [1/2, 2]` (1.5);
   - the Dirichlet operator `H_D(α) = −Δ_{Ω₁}^D + Q^*aQ + ν + α` on fields supported in `Ω₁` (1.6),
     as a complex matrix on `Ω₁` (use `restrictOp`-style restriction from
     `Balaban/Green/Restriction.lean` and `latticeLaplacian` from `Balaban/Lattice/Laplacian.lean`);
   - the path metric (1.9) (paths inside `Ω₁`, each bond costing `1/ℓ(b)` in fine units).
2. **G-1(a).** `Re⟨u, H_D(α) u⟩ ≥ c₁ (‖∂u‖² + ‖ℓ^{−1}u‖²)` for `|α(x)| ≤ c₁ ℓ(x)^{−2}/2`, with GREEN.md's
   explicit `c₁` (the proof: Neumann bracketing into layer blocks plus the block Poincaré
   inequality, already landed as `Balaban.blockPoincare` in `Balaban/Green/BlockPoincare.lean`;
   and `Balaban.blockHamiltonianC_isCoercive` for the single-scale pattern). Conclude
   `IsCoercive` (from `Balaban/Green/Coercive.lean`) for `H_D(α)` with constant
   `c₁ min_x ℓ(x)^{−2}`, hence invertibility.
3. If budget remains: the x-variant G-1(a′) (§1.3 (1.7), §4.1).

Infrastructure (G-1 provider work as editable targets; recorded reason: needed by G-2, I-1, I-4).

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `GeneratingSet.lean`,
`Operator.lean`, `PathMetric.lean`, `Coercivity.lean`) in your worktree
`/home/scott/Balaban-worktrees/W8a` (branch `w8a-multiscale`), plus import lines in `Balaban.lean`.
Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–2, or about 2,500 lines, or a precise obstruction (e.g. a definition
in GREEN.md §1 that is ambiguous — quote it, state your reading, and continue only if harmless).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; the definitions with their meaning; main theorem names with statements;
checks and results; axioms; open questions; last commit hash.
