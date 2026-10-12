# Brief W44 — (Ξ3) at the field level and (Ξ4) for the composed field

**Goal.** Close the two open points of W42 (landed `Balaban/SmallField/Xi*.lean`):
1. **(Ξ3) field level:** for a member of `Ξ^c_k(𝔹′; σ, ε)` with `𝔹 ≺ 𝔹′` and the scale gap of
   `xiC_scaledComposition`, the composed datum lies in `Ξ^c_j(𝔹; C₀θσ, ε)` (the restriction of the
   fields via `Balaban.Background.theorem73_real`/`theorem73_complex`, `bgField`/`bgFieldC` of the
   composed datum = restriction, and the `XiBounds`/`XiCBounds` of the restriction with σ scaled
   by θ = L^{−(k−j)}): `notes/phase1/SMALLFIELD.md` v2 §1.7 (Ξ3) and (R-S).
2. **(Ξ4) transport:** the second-difference / Hölder bound for the composed field
   `ψ(𝔹_j(X), 𝔹_k(X))` (`composeField` of `bgFieldExt`), as (Ξ4) is consumed by
   `notes/phase1/LOCALIZATION.md` v2 §4.3 (Lemma DL) and SMALLFIELD §2 (I-6).

Inputs: `Balaban/SmallField/{Xi,XiGeom,XiCompose,XiProps}.lean`, `Balaban/Background/{Theorem73,
ScaledComposition,CompositionDomain,HolderFull,Def5}.lean`.

**Ownership.** New files under `Balaban/SmallField/` (e.g. `XiComposeField.lean`) in your worktree
`/home/scott/Balaban-worktrees/W44` (branch `w44-xi-composition`), plus import lines in
`Balaban.lean`. Worker W43 is writing `Balaban/SmallField/Renormalization*.lean`; do not touch.
Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–2, or about 1,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
