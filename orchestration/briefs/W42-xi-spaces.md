# Brief W42 — the analyticity spaces Ξ_j, Ξ^c_j at λ = ∞ and (Ξ1)–(Ξ4)

**Goal.** Formalize `notes/phase1/SMALLFIELD.md` v2 §1.7 (the spaces Ξ_n(𝔹; σ, ε), Ξ^c_n(𝔹; σ, ε) at
λ = ∞, defined through the background fields `bgField`/`bgFieldC`; the facts (D1) Ξ_j(σ, ε) ⊂ Ψ_j(3σ, ε)
and the same for Ξ^c (P1 Lemma 3.1 at λ = ∞), (D2) Ψ̄^c_j(δ, ε) ⊂ Ξ^c_j(1, ε̄) if ε + K₁δ ≤ ε̄; and the
four properties used by the localization expansion (`notes/phase1/LOCALIZATION.md` v2 §4.0, §4.3
Lemma DL): (Ξ1) Ξ^c_n(𝔹; 1, ε′) ⊂ Ψ̃^c(𝔹; 2(d+2)ε′, 2(d+2)ε′); (Ξ2) membership under perturbation
(BACKGROUND Prop 5.1 with K₂); (Ξ3) the composition map sends Ξ^c_k(σ) into Ξ^c_j(L^{n−p}σ) — the
scaled composition (R-S), landed as `Balaban.Background.scaledComposition` (with W28's restrictions:
|φc − φr|₀ ≤ ε and the restricted pair; state exactly which case you prove); (Ξ4) the second-difference
bound via I-1(e) (landed `bgFieldC_holder`, `phi0_sq`)). The `h′` conditions of Ξ^c are partly garbled
in the P3 scan (UNCERTAIN in SMALLFIELD §1.7): define them as SMALLFIELD v2 states and record the
docstring flag; the gap condition on (ε_j) (E) as a separate definition.

Landed inputs: `Balaban/Background/*` (Data: `InPsiTilde`, `InPsiTildeC`, domains; Def5: `bgField`,
`bgFieldC`, `bgMult`, `theorem71`, `theorem72*`; `Theorem52*`, `Perturb.lean`
`theorem52_perturb`; `ExistenceBounds.lean` `BgBounds`; `ScaledComposition.lean`;
`HolderFull.lean`; `Theorem73.lean`).

**Ownership.** New files under `Balaban/SmallField/` (new directory; e.g. `Xi.lean`, `XiProps.lean`)
in your worktree `/home/scott/Balaban-worktrees/W42` (branch `w42-xi-spaces`), plus import lines in
`Balaban.lean`. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** The definitions, (D1), (D2), (Ξ1)–(Ξ4), or about 2,000 lines, or a precise
obstruction (a property false as stated — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; definitions (full text of Ξ_j, Ξ^c_j); main theorem names with statements; checks
and results; axioms; open questions; last commit hash.
