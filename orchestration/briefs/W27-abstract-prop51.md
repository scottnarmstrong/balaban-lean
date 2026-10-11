# Brief W27 — Prop 5.1 for an abstract Green family, modes U and P (requirement R-B2)

**Goal.** Refactor the landed background-field contraction so that its fixed-point core does not
depend on `dirichletOperator`, as required by `notes/phase1/LOCALIZATION.md` v2 (requirement R-B2,
§3.2 "Theorem I-4a" and the paragraph "R-B2 (requirement on BG §5 …)", which lists the items).
Landed files: `Balaban/Background/Contraction.lean` (`Setup`, `CoreHyp`, `g_bd`, `dphi`, `dphi_eq`,
`dphi_diff`, `dphi_diff_sup`, `Nmap`, `Smap`, `Smap_lip`, `exists_fixed`, `prop51_core`,
`identity52`, `isPerturbed_dphi_iff`, `perturbed_of_fixed`, `prop51_exists_unique`),
`ContractionAnalytic.lean` (`prop51_analytic`), `Calculus.lean`.

1. **Abstract Green family.** A structure for `𝒢 : (G.Ω 1 → ℂ) → Matrix …` (a family indexed by the
   multiplier, possibly also by a parameter `s`) with exactly the hypotheses the core uses: the
   sup-norm bound `‖𝒢(α) f‖_* ≤ B|f|₂` (the bridge form of `GreenSetting.green_bound`), the Lipschitz
   (difference) bound replacing the resolvent identity (`dphi_diff`), and analyticity in `α` (and in
   the parameter) on the polydisc. Instance: `𝒢(α) = (dirichletOperator G a ν (α₀ + α))⁻¹` from the
   landed lemmas (`GreenSetting`, `green_sub_bound`, `analyticOnNhd_green_apply`).
2. **The core for the abstract family, two modes.** `dphi`, `Nmap` with the mode parameter `ι_U`
   (mode U: the `½H₀g̃` term; mode P: without it, LOCALIZATION v2 §3.2 Step 1–2), `Smap`, `Smap_lip`,
   `exists_fixed`, `prop51_core` and the analyticity theorem, stated for the abstract family.
3. **Re-derive the landed statements** `prop51_exists_unique` and `prop51_analytic` from the abstract
   core plus the `G_D`-specific step (`identity52`, `isPerturbed_dphi_iff`, `perturbed_of_fixed`),
   **with unchanged statements** (consumers: W23's `prop64`, `el_local_unique`,
   `composedSystem_unique`; check they still build).

**Ownership.** Edits to `Balaban/Background/Contraction.lean`, `ContractionAnalytic.lean` and new
files under `Balaban/Background/` (e.g. `AbstractGreen.lean`, `ContractionCore.lean`) in your
worktree `/home/scott/Balaban-worktrees/W27` (branch `w27-abstract-prop51`), plus import lines in
`Balaban.lean`. The public statements `prop51_exists_unique`, `prop51_analytic`, `Prop51Hyp`,
`IsPerturbed` must keep their exact types (other landed files use them). Worker W22 owns
`Balaban/Background/{BlockGeometry,BSpline,Interpolation,Approximate}.lean`-type files; do not touch
them. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,000 lines changed, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; the abstract structure (full Lean text); main theorem names with statements;
confirmation that the landed statements are unchanged; checks and results; axioms; open questions;
last commit hash.
