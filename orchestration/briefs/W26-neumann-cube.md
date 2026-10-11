# Brief W26 — NC: the cut (Neumann-cube) operator, first milestone

**Goal.** Start statement NC of `notes/phase1/LOCALIZATION.md` v2 §3.1 (the Green's-function input of
the decoupled operator DG; it replaces GREEN.md's G-3; the main risk of the localization layer). The
cube operator `H_z(A)` is the multiscale Dirichlet operator `H_D(A)` restricted to a block-aligned
cube `□` (side `5M₁ℓ_m`) with the bonds crossing the cube faces removed (Neumann faces). First
milestone, in order:

1. **The bond-subset operator.** A definition of `H_D(A)` with a set of removed ("cut") bonds,
   general enough for the cube cuts of §1.2 (prefer: a predicate/Finset of retained bonds on top of the
   landed `Balaban/Multiscale/Operator.lean` `dirichletOperator`, so that the uncut case is
   definitionally or provably the landed operator). State the cube cut of §1.2 as an instance.
2. **NC1 (coercivity)** `Re⟨u, H_z(A)u⟩ ≥ ½‖∂ũ‖²_□ + ¼‖ℓ⁻¹u‖²`: re-run the landed
   `multiscale_coercive_sharp` (`CoercivitySharp.lean`) with the bond subset (the cut removes
   non-negative bond terms; block Poincaré is intact because the cube is block-aligned). Invertibility.
3. **NC2 (`L²` block decay)** with the path metric `d` of `Ω₁`: re-run the Agmon argument
   (`AgmonCore`, `AgmonDecay`, `Agmon`, `AgmonWeight`, `ScaleMismatch`, `green_G2i`) for the bond
   subset. Where the landed proofs are generic in the bond set, generalize them by a parameter (keep
   the old names as the uncut specialization); otherwise copy and adapt.
4. **NC3 (interior pointwise bounds)** on the inner cube `C⁺`, following the §3.1 proof sketch: on the
   ball `B(x, 2L²ℓ(x)) ⊂ □` away from the cut faces the equation is the uncut one, so the landed
   interior lemmas (`lemma_loc_a/b/c` with their ball hypotheses, `lemmaP` with `PtSetting G Λ`,
   `prop48`, `prop49`) apply — identify exactly which landed statements must take the cut operator or
   only a local equation, and generalize those. Then the weighted form of NC3 (§3.1, "proved").
5. **NC4** analyticity in `A` (Cramer's rule, as `analyticOnNhd_green_apply`).

The milestone is items 1–3 complete and item 4 at least for `|u(x)|` and `ℓ|∂u(x)|`. Report precisely
which landed lemmas had to be generalized and how.

**Ownership.** New files under `Balaban/Localization/` or `Balaban/Multiscale/` (e.g.
`CutOperator.lean`, `CutCoercivity.lean`, `CutAgmon.lean`, `CutPointwise.lean`) in your worktree
`/home/scott/Balaban-worktrees/W26` (branch `w26-neumann-cube`), plus import lines in
`Balaban.lean`. Generalizing landed `Balaban/Multiscale/*` lemmas by a bond-set parameter is
allowed when the old statement stays available under its old name (say which files). Worker W25 owns
`Balaban/Localization/AbstractExpansion.lean`, `Peierls.lean` — do not touch them. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** The milestone, or about 3,500 lines, or a precise obstruction (a step of the
landed proofs that does not survive the cut — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; generalized landed lemmas;
checks and results; axioms; open questions; last commit hash.
