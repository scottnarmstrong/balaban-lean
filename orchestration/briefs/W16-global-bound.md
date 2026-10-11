# Brief W16 — G-2(iv): the global weighted bound (consumed by P2, C1)

**Goal.** Formalize the global corollary of G-2 in `notes/phase1/GREEN.md` (final; §3 G-2(iv),
consumed bound C1 in §2): for `u = G_D(α) f` on a generating set,
`|u|_0 + |∂u|_1 + |Δ^D u|_2 ≤ B₀ |f|_2`, with P2's weighted sup norms (GREEN.md §1.5:
`|f|_σ = max_j sup_{x ∈ layer j} ℓ_j^σ |f(x)|`; `|∂u|_1` over bonds with the spacing at both endpoints),
`B₀ = B₀(d, L)`, uniform in `k`, the volume, the generating set (with the separation hypothesis of
the landed results), `α` in the coercivity polydisc and `ν ∈ [0, 1]`. Proof: decompose `f` over
blocks `Δ(y')`, apply the landed pointwise decay `Balaban.Multiscale.prop48` (W12) to each piece
(`U(x) ≤ K₂ e^{−(ε₀/2) d(x,y')} ℓ_{j'}² ‖f|_{Δ(y')}‖_∞`, and `ℓ_{j'}² ‖f|_{Δ(y')}‖_∞ ≤ |f|_2`), sum over
blocks with the landed counting lemma `Balaban.Multiscale.sum_siteWeight_decay_le` (W8d). For the
Laplacian part use the equation `−Δ^D u = f − (Q^*aQ + ν + α)u` and the bounds already obtained
(GREEN.md (4.4), landed `laplacian_bound` in `Balaban/Multiscale/PointwisePotential.lean`).

**Ownership.** New file(s) under `Balaban/Multiscale/` (e.g. `GlobalBound.lean`) in your worktree
`/home/scott/Balaban-worktrees/W16` (branch `w16-global-bound`), plus import lines in
`Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** The global bound for `|u|_0`, `|∂u|_1`, `|Δ^D u|_2`, or about 1,200 lines, or a
precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
