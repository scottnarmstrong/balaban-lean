# Brief W25 — localization: the abstract expansion lemma AE and the Peierls count (GM3, GM4)

**Goal.** Formalize the model-free parts of the localization expansion of
`notes/phase1/LOCALIZATION.md` §4.1–4.2 (I-5; P3 (4.41), (4.43), (4.47), (4.50)):

1. **Lemma AE** (abstract interpolation–resummation), exactly as stated in §4.1: a finite set `Ω`
   with adjacency, `X₁ ⊂ Ω` connected, a finite family `𝔓` of subsets, `V(𝒞)`, `Y(𝒞)` (the component
   of `V(𝒞)` containing `X₁`), connected families; `F(s; u)` analytic in `s` near the closed
   polydisc of radius `R = e^{κ₁}` (`κ₁ ≥ 1`) with `|F| ≤ B_F` (AE1) and the locality (AE2).
   Conclusion: `F(1; u) = Σ_{𝒞 connected} F_𝒞(u)` with the integral formula for `F_𝒞`, `F_𝒞`
   depending only on `u|_{Y(𝒞)}`, `|F_𝒞| ≤ B_F (R−1)^{−|𝒞|} ≤ B_F e^{−(κ₁−1)|𝒞|}`, and joint
   analyticity in further parameters. Use the landed Cauchy estimates
   (`Balaban/Analysis/Cauchy.lean`: `norm_mixed_fderiv_le`, `norm_fderiv_single_le`) and
   `Balaban/Analysis/AnalyticLimit.lean`. State the data abstractly (types with restriction maps, or
   `u : Ω → E` with "agree on `Y`"), so that later instantiation is direct.
2. **GM3** (Peierls count) as an abstract counting statement: for a fixed set and layer
   decomposition, `Σ_{𝒞 : Y[𝒞] = Y} e^{−κ₂|𝒞|} ≤ 1` under the hypothesis of §4.2 — formalize it in the
   abstract form used by the proof (a family of sub-families with `|𝒞_n| ≥ N_n / G₀`,
   `𝒞_n ⊂ 𝔓_n(Y)` with `|𝔓_n(Y)| = A' N_n`; the product over layers), and **GM4** (the exponent
   inequality) as a real-number lemma.
3. If budget remains: the construction `D(P)`, `Y[𝒞]` and GM1 on the landed `GeneratingSet`.

**Ownership.** New files under `Balaban/Localization/` (new directory; e.g. `AbstractExpansion.lean`,
`Peierls.lean`) in your worktree `/home/scott/Balaban-worktrees/W25` (branch `w25-localization-ae`),
plus import lines in `Balaban.lean`. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.
Copy freely from any of the author's repositories (no attribution needed; the polymer/BKAR
material in `Balaban/Polymer/*`, `Balaban/External/BKAR/*` may help with the interpolation formula).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–2 (3 if possible), or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
