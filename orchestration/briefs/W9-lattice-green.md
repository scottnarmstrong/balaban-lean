# Brief W9 — the lattice Green's function on ℤ^d (Lemma K)

**Goal.** Formalize Lemma K of `notes/phase1/GREEN.md` (§4.5, final version; read it in full with
its proof) for the nearest-neighbour Laplacian on `ℤ^d`, `d ≥ 3`:

1. **Construction.** The heat kernel `q_t(n) = (1/2π)∫_{−π}^{π} e^{inϑ − 2t(1−cos ϑ)} dϑ`,
   `p_t(x) = ∏_μ q_t(x_μ)`, and `C(x) = ∫_0^∞ p_t(x) dt` (or an equivalent Fourier-integral or
   random-walk definition, if cheaper — say which and prove the equivalence you use). Prove:
   `q_t ≥ 0`, `Σ_n q_t(n) = 1`, `∂_t p_t = Δ¹ p_t`, `C` finite for `d ≥ 3`, `C ≥ 0`,
   `−Δ¹ C = δ₀`, and `C(x) → 0` as `|x| → ∞`.
2. **Bounds.** `C(x) ≤ c⟨x⟩^{2−d}`, `|∂_μ C(x)| ≤ c⟨x⟩^{1−d}`, `|∂_μ∂_ν C(x)| ≤ c⟨x⟩^{−d}` (forward
   and backward differences; `⟨x⟩ = 1 + |x|`), via the one-dimensional bounds of Lemma K's proof
   step (2) (contour shift; for `t ≥ 1`: `q_t(n) ≤ c t^{−1/2} e^{−c′ min(n²/t, |n|)}` and the
   difference bounds; for `t ≤ 1`: `q_t(n) ≤ c t^{|n|}`). The third-difference bound is optional.
3. **Uniqueness (needed by Root-C).** A bounded function `h` on `ℤ^d` with `Δ¹ h = 0` and
   `h(x) → 0` as `|x| → ∞` is `0` (maximum principle); hence `C` is the unique solution of
   `−Δ¹G = δ₀`, `G → 0` — the Green's function in Root-C
   (`Balaban/Frozen/Roots/LowTemperatureCorrelations.lean` uses exactly
   `Σ_μ (2G x − G(x+e_μ) − G(x−e_μ)) = if x = 0 then 1 else 0` and `Tendsto G cofinite (𝓝 0)`; state
   your existence-and-uniqueness theorem in that form, for `G : (Fin d → ℤ) → ℝ`).
4. If budget remains: the massive version `(−Δ¹ + m²)^{−1}` with `e^{−c m|x|}` decay.

Infrastructure; recorded reason: G-2 step 3 (pointwise bounds, GREEN.md main risk), and Root-C's
Green's function (`notes/phase1/PLAN.md`).

**Ownership.** New files under `Balaban/Green/Lattice/` (e.g. `HeatKernel.lean`, `Green.lean`,
`GreenBounds.lean`, `Uniqueness.lean`) in your worktree `/home/scott/Balaban-worktrees/W9` (branch
`w9-lattice-green`), plus import lines in `Balaban.lean`. Templates: copy freely from any of the
author's repositories (no attribution needed), e.g.
`/home/scott/mining/Frohlich-Spencer/FroehlichSpencer/FS82/Infinite/FourierGreen.lean` (Fourier
Green's function on ℤ^4), `.../BKT/Lattice2D/*`, `/home/scott/EllipticRegularity`, Mathlib's
`Mathlib/Analysis/Fourier/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3, or about 3,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only (you
may import frozen *definitions*; never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`);
no file over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
