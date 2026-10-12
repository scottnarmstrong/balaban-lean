# Brief W45 — the covering size functional and the corrected GM2

**Goal.** Replace the landed `Balaban.Localization.gm2` (W38, `Balaban/Localization/TreeLength.lean`),
whose hypothesis `GM2Setup.contains` is false in general (`notes/phase1/CHECKS1-astra.md` §1,
U-shaped counterexample), by the repaired statement of `notes/phase1/LOCALIZATION.md` v3 §4.0, §4.2
(Def-L8 `treeLenCov` in §5.1):
1. **Definitions:** a chosen covering family (a subfamily of each cover `π′_n` whose cubes lie in
   `Y ∩ Λ_n` and whose union is `Y ∩ Λ_n`), `treeLenCov Y` (infimum jointly over chosen families and
   connected structures meeting every chosen cube), `treeLenCovOne X` (single scale). Reuse W38's
   `ConnStruct`, `bondW`, `Dbases`, `Ysites`.
2. **GM2 (v3):** with `𝒦_X`, `Γ₀`, `𝒬₀`, `X₁ = ⋃𝒬₀` as in v3 §4.2 (no `contains` hypothesis),
   `treeLenCov (Ysites …) ≤ L⁻¹ * treeLenCovOne X + d * (2L+1)^d * |𝒞|`, and that `𝒦_Y` is a chosen
   family of `Y`.
3. **Companions:** `treeLenCov ≤` W38's `dTilde` (P1's tree length), and the block count
   `n(Y) ≤ L^{2d} C_d (treeLenCov Y + 1)`.
4. **GM4 re-derived** from the new GM2 (W38's `gm4` combined `gm2` with the landed
   `exponent_inequality`); restate `gm4` accordingly.
5. Remove or rename the old `gm2`/`gm2_tree`/`gm4` and `GM2Setup.contains` so no theorem with the false
   hypothesis remains in the library (check consumers with grep; there should be none outside
   TreeLength/PolymerCount).

**Ownership.** Edits to `Balaban/Localization/{TreeLength,PolymerCount}.lean` and new files under
`Balaban/Localization/` (e.g. `TreeLengthCov.lean`) in your worktree
`/home/scott/Balaban-worktrees/W45` (branch `w45-treelen-cov`), plus import lines in `Balaban.lean`.
Worker W39 is writing `Balaban/Localization/Decoupled*.lean`; do not touch. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–5, or about 1,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; what was removed/renamed;
checks and results; axioms; last commit hash.
