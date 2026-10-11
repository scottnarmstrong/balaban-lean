# Brief W8c — the hard-spin constrained operator: G-1(d), G-2(v), G-2(v′)

**Goal.** Formalize the λ = ∞ constrained-operator results of `notes/phase1/GREEN.md` (final):
definition (1.8′) `Π = G φ₀ [φ₀·Gφ₀]^{−1} φ₀·G` and `Δ^{(k)} = Δ^{(k)}_unc + a_k² Q_k Π Q_k^*`;
G-1(d) (§4.5b): (1) `Π ⪰ 0` for real data, (2) the complex perturbation bound, (3) kernel decay of
`Q_k Π Q_k^*`; G-2(v) and (v′) (§4.5a): the bounds on the constraint sandwich, `L²` and
sup-weighted. Build on the landed `Balaban/Multiscale/*` (`dirichletOperator`, `green_G2i`,
`multiscale_coercive`), `Balaban/Green/*` (`IsCoercive`, `combesThomas`, `perturbation_tails`,
`unconstrainedUnitOperator`), `Balaban/Gaussian/Schur.lean`.

Field values in `ℂ^N` (or `Fin N → ℂ`), `φ₀ : Ω₁ → ℂ^N` near the unit sphere (state the
smallness/closeness hypotheses GREEN.md uses: real data close to unit length; complex data in an
`ε`-neighbourhood), the bilinear (non-conjugated) dot product `φ₀·Gφ₀` as GREEN.md §1.1 says.

**Ownership.** New files under `Balaban/Multiscale/` or `Balaban/Green/` (e.g.
`Constrained.lean`, `ConstraintSandwich.lean`) in your worktree
`/home/scott/Balaban-worktrees/W8c` (branch `w8c-constrained`), plus import lines in
`Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** G-1(d)(1)–(3) and G-2(v), or about 2,500 lines, or a precise obstruction (an
inequality of §4.5a–b that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
