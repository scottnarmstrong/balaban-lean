# Brief W18 — G-2(v′): the constrained sandwich in the weighted sup norms

**Goal.** Formalize G-2(v′) of `notes/phase1/GREEN.md` (§3 statement; proof in §4.5a with the
global form of G-2(iv)), the form of the hard-spin constraint bounds that the background-field
problem uses (P2 (3.34)–(3.38); GREEN.md C15, F-16). Under the hypotheses of G-2(v) on `φ₀`
(`1/2 < |φ₀| < 3/2`, `|φ₀² − 1| < δ₀`, `|∂φ₀|₁ < δ₀`, `|Δφ₀|₂ < δ₀`, `δ₀ ≤ δ_*(d,L)`):

1. `|K(φ₀)·Gφ₀ f|₂ ≤ c_* δ₀ |f|₂` with `K(φ₀) = 2∇φ₀·∇ + Δφ₀ − [Q^*aQ, φ₀]` (the commutator form
   landed in `Balaban/Multiscale/ConstraintComm.lean`, `ConstraintSandwich.lean`), where
   `|f|₂ = sup_x ℓ(x)²|f(x)|`, `|u|₀ = sup|u|`, `|∂u|₁ = sup ℓ|∂u|` are the weighted sup norms of
   `Balaban.Multiscale.global_bound` (`Balaban/Multiscale/GlobalBound.lean`, just landed: the
   global G-2(iv) bound `|Gf|₀ + |∂Gf|₁ + |Δ^D Gf|₂ ≤ B|f|₂`, stated with `Cf` bounds).
2. `M = φ₀² − K(φ₀)·Gφ₀` is invertible with `|M^{-1} g|₂ ≤ 2|g|₂` (Neumann series in the `|·|₂`
   norm, from 1 and `|φ₀² − 1| < δ₀`).
3. `[φ₀·Gφ₀]^{-1} G = M^{-1}` (the landed identity behind `constraintM_isUnit`,
   `constraintForm_isUnit`; restate in the form needed) and the bound
   `|Πf|₀ + |∂Πf|₁ ≤ B₁′|f|₂` for `Π = G φ₀ [φ₀·Gφ₀]^{-1} φ₀·G`, together with the same bound for the
   constrained Green's function `G − Π` (`constrained_green_eq` in the x-variant files gives
   `G_c = G − Π`).
4. If budget remains: the `|Δ^D Π f|₂` part, and G-2(vi′) (locality of `Π` in `φ₀`, GREEN.md §4.6
   kernel-algebra outline: telescoping `Π − Π′` with one difference factor) in the `L²` block form.

The landed `L²`/Agmon versions are `constrained_weighted_bounds`, `constrained_block`,
`constrained_G2v`, `constrained_complex_lower` (W8c); reuse their algebra, change only the norms.
Complex `φ₀ = φ_r + iφ_i`, `α` as in `constrained_complex_lower` should be allowed if the landed
`Standing` structure allows it at no extra cost; otherwise real `φ₀` first and say so.

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `ConstraintSup.lean`) in your worktree
`/home/scott/Balaban-worktrees/W18` (branch `w18-constrained-sup`), plus import lines in
`Balaban.lean`. Small additions to landed files only if unavoidable (say which). Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`. Copy freely from any of the author's
repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 2,000 lines, or a precise obstruction (an inequality of
§4.5a that fails in the sup norms — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
