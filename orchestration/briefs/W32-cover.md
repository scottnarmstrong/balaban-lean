# Brief W32 — localization: the cover, the partition of unity, the cut commutators (Cov, K)

**Goal.** Formalize `notes/phase1/LOCALIZATION.md` v2 §1.1b (the pair 𝔹_{k+1}/𝔹_k, `dropTop`,
`CubeAligned` with `m₁ ≥ 2`) and §1.2 (the cover by cubes `C_z` of side `M₁ℓ_{m(z)}` centred on the
cube centres `Z` of layers `1..k+1`, the B-spline partition of unity `χ_z` at cube scale, (Cov1)–(Cov4),
the interaction cubes `□_z` of side `5M₁ℓ_m`, the parameter cubes, `𝒬(z)` (cubes meeting the
thickened `□̂_z`, `ρ_* = 3L²ℓ_m`), the counts `N₀` and `c_d′ = 3·5^d`), and the cut commutator
`K_z = χ_z H − H χ_z` with its Leibniz bound (K) from `Balaban/Background/Calculus.lean`
(`commK_bound`, `negLap_mul`). Reuse the landed B-spline and bump machinery of
`Balaban/Background/{BSpline,Bump,Weights}.lean` (W22) for `χ_z` (at cube scale instead of block
scale), and the cut/cube definitions of `Balaban/Multiscale/{CutOperator,CutCube}.lean`
(`cubeCut`, `BlockAligned`). Additions to `Balaban/Multiscale/GeneratingSet.lean` (`dropTop`, the
cast lemma) are allowed if needed (keep existing statements unchanged).

Prove: (Cov1) `χ_z ≥ 0`, `Σ_z χ_z = 1` on `Ω₁`; (Cov2)/(Cov3) the support and difference bounds of
`χ_z` (`|∂χ_z| ≤ C_χ/(M₁ℓ)`, second differences, as §1.2 states); (Cov4) `□_z` contains the
`(2L²ℓ_m + 1)`-neighbourhood of `C_z` for `M₁ ≥ 4L²`; the multiplicity bound (a point lies in at most
`c_d′` interaction cubes); the bound on `N₀`; and (K): `|K_z u|₂ ≤ (1+2d) C_χ M₁⁻¹ ‖u‖_*`-type bound as
used in the proof of (DG1) (§3.1). Where §1.2 is marked UNCERTAIN (layer interfaces, the wall), state
exactly what you prove and what remains.

**Ownership.** New files under `Balaban/Localization/` (e.g. `Cover.lean`, `CutCommutator.lean`)
in your worktree `/home/scott/Balaban-worktrees/W32` (branch `w32-cover`), plus import lines in
`Balaban.lean`. Workers W28/W30 own new `Balaban/Background/` files (composition domains,
existence): do not touch them. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** The items above, or about 2,000 lines, or a precise obstruction (a cover
property that fails at layer interfaces — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions; main theorem names with statements; checks and results; axioms;
open questions; last commit hash.
