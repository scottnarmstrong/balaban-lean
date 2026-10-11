# Brief W3b — the polymer-expansion theorem PE in Lean

**Goal.** Formalize the abstract polymer-expansion theorem of `notes/phase1/POLYMER.md` (revised
after review; read it in full, including "Review dispositions", and its review
`notes/phase1/POLYMER-review.md`), following its §6 Lean plan, in this order:

1. **PE (abstract, finite).** A finite set of polymers with a symmetric reflexive incompatibility
   relation, activities, the Kotecký–Preiss condition with weights `a, b` (POLYMER.md §2), and
   the conclusions: `Ξ = exp L` with `L` the absolutely convergent cluster sum, the weighted
   cluster-sum bound, and the bound `|Ξ| ≥ exp(−Σ a)` if stated there. Route as in POLYMER.md §3:
   the BKAR forest formula (ported: `Balaban/External/BKAR/`, namespace `BKAR`, flagship
   `BKAR.bkar_formula_forestIndex_cube_contributions`) for the sign and the Penrose tree bound of
   the Ursell function, a tree recursion for absolute convergence, and the exponential formula.
   If POLYMER.md's plan identifies a shorter route for a step, use it and say so.
2. **Holomorphic dependence.** Activities holomorphic in a parameter, uniform bounds ⇒ `L` and
   each cluster term holomorphic (use the holomorphy toolkit of W7 when it lands on `main`;
   until then state what you need as a clearly named local lemma and report it).
3. **PE-L (lattice corollary).** Polymers = nearest-neighbour connected block sets on a block
   torus (degree ≤ 2d), size = number of blocks, the animal bound proved directly for finite
   graphs of degree ≤ 2d (review R9), and the local polymer representation `L = Σ_Y P(Y)` with
   `Σ_{Y ∋ □} |P(Y)| e^{κ' d(Y)} ≤ α`.
4. If budget remains: the hole version and the marked version PE-M (§2.4–2.5 of POLYMER.md).

This is the PE interface's provider work as an editable target; the frozen PE statement will be
drafted for author approval separately and may differ in packaging — keep statements clean and
general.

**Ownership.** New files under `Balaban/Polymer/` in your worktree
`/home/scott/Balaban-worktrees/W3b` (branch `w3b-polymer`), plus their import lines in
`Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed):
e.g. `/home/scott/KPZ/cumulants/Lean/Polymers/` (Lean v4.26.0 — port what helps),
`/home/scott/mining/Frohlich-Spencer/FroehlichSpencer/Infra/Combinatorics/Animals.lean`.

**Checks.** `lake build` of your modules only (at most one build at a time; compiles are
throttled machine-wide and may wait; never bypass the throttle); zero warnings; `#print axioms`
standard on the main theorems; `python3 -I scripts/check_lean_modules.py --root .`.

**Stop condition.** Items 1–3, or about 4,000 lines, or a precise obstruction (state it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; which POLYMER.md statements are proved
and which remain; checks and results; axioms; open questions; last commit hash.
