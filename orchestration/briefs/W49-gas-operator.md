# Brief W49 — GAS and the polymer expansion with a hole for operator-valued weights (Part III Lean P10)

**Goal.** Formalize Lean item P10 of `notes/phase1/LF-RECONSTRUCTION.md` §III.L: `gasOp_eq`,
`gasOp_activity_bound`, `gasOp_pe_hole` — the abstract part of Lemma III.10.5: the gas of heavy
objects (GAS, `notes/phase1/POLYMER.md` §2.6) and the polymer expansion with a hole, for weights that
are **integral operators acting on disjoint sets of variables**, applied pointwise in the external
variables, with norms the sup bounds of (3.10″) (the operator norm used in Part III; read §III.8–III.10
for the exact norm and how products of operators on disjoint variables compose). The scalar versions
are landed: `gas_eq`, `gas_activity_bound`, `gas_pe` (`Balaban/Polymer/Gas*.lean`), `pe_hole`
(`Balaban/Polymer/Hole.lean`), `pe_PY_analyticOnNhd`, `mayer_*`. Choose an abstraction that makes the
scalar proofs reusable (e.g. weights in a commutative Banach algebra of functions/operators on a product
of variable spaces, multiplication = tensor product on disjoint supports), and prove the operator
versions by reduction to the scalar ones where possible; state precisely what algebraic structure is
used.

**Ownership.** New files under `Balaban/Polymer/` (e.g. `GasOperator.lean`, `HoleOperator.lean`) in
your worktree `/home/scott/Balaban-worktrees/W49` (branch `w49-gas-operator`), plus import lines in
`Balaban.lean`. Small additions (new lemmas) to landed `Balaban/Polymer/*` files only if unavoidable
(say which). Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** The three statements, or about 1,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; the abstraction (full text of the structure/class used); main theorem names with
statements; checks and results; axioms; last commit hash.
