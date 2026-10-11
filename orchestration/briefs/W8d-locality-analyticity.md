# Brief W8d — G-2(vi): analyticity in α and single-variation locality of the multiscale Green's function

**Goal.** Formalize G-2(vi) of `notes/phase1/GREEN.md` (final; §3 statement, proof in §4 — read
the review-revised form with γ₀/3 in each factor, re-review item N-2) on top of the landed
`Balaban/Multiscale/*` (W8a, W8b: `dirichletOperator`, `multiscale_coercive`,
`dirichletOperator_isCoercive`, `agmon_energy`, `agmon_block`, `green_G2i`, `pathDist`,
`truncDist`) and `Balaban/Green/*`:

1. **Analyticity in α.** On the polydisc `|α(x)| < c₁ ℓ(x)^{−2}/2` (or GREEN.md's `|α|₂ < γ₁`
   region), `α ↦ G_D(α)` is analytic (matrix-valued; via the Neumann series around a real α₀
   or via `Balaban.Analysis.analyticOnNhd_of_tendstoUniformlyOn`), with the bounds of G-2(i)
   holding uniformly on the polydisc.
2. **Single-variation locality.** If `α` and `α'` agree outside a set `V` (or the data of
   `H_D` differ only on `V`), then the difference `G_D(α) − G_D(α')`, tested between blocks
   `Δ(y)` and `Δ(y')`, is bounded by the product form
   `B e^{−(γ₀/3)(d(y,V) + d(V,y'))} ×` (the size of the variation), as GREEN.md G-2(vi) states;
   proof by the resolvent identity `G(α) − G(α') = −G(α)(α − α')G(α')` and two applications of
   the block decay (`green_G2i`/`agmon_block`), with the exponent split of N-2.
3. If budget remains: Lemma 4.4 (the counting lemma) and the conversion from block `L²` to
   `ℓ_{j'}^{d/2} ‖f‖_∞` used in (4.2).

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `Analyticity.lean`, `Locality.lean`)
in your worktree `/home/scott/Balaban-worktrees/W8d` (branch `w8d-locality`), plus import lines
in `Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–2 (3 if possible), or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
