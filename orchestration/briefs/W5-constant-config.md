# Brief W5 — constant configurations at λ = ∞, and the O(N) reduction to invariants

**Goal.** Two self-contained pieces of the background-field and renormalization machinery, for
hard spins (λ = ∞):

1. **Constant configurations (P2 §2, Prop 2.1 and Lemma 2.1, pp. 613–617, specialised to λ = ∞).**
   For constant data the variational problem reduces to: minimize
   `(a/2)|ψ − φ|² + (ν/2)|φ − h|²` over `φ ∈ S^{N−1}` (`a ∈ (1/2, 3/2)`, `ν ∈ (0, 1]`, `ψ` near
   the unit sphere, `|h| = 1`). The Euler–Lagrange system `a(φ − ψ) + ν(φ − h) + αφ = 0`,
   `φ·φ = 1` has the explicit solution `φ = w/√(w·w)`, `w = aψ + νh`, with multiplier
   `α = √(w·w) − a − ν`. Prove: (i) for real data in the stated range this is the unique
   minimizer and the unique solution with `|α| < c`; (ii) it extends analytically to complex
   `(ψ, h)` in an explicit polydisc around real data (complex square root on `Re(w·w) > 0`), with
   the bounds of P2 (2.11)–(2.15) in the form valid at λ = ∞ (state them: `|φ − ψ| ≤ C|…|`,
   `|α| ≤ C(|z| + |ν² w²|)` with P2's invariants (2.6)); (iii) `O(N)` covariance
   `φ(Rψ, Rh) = Rφ(ψ, h)`. Use `Balaban/Analysis/*` (Cauchy, analytic contraction) where needed.
2. **The O(N) reduction (P1 (3.24)–(3.28), pp. 125–130).** An `O(N)`-invariant function `V(ψ, h)`
   of two vectors (`N ≥ 2`), analytic near `(e₁, e₁)` (complexified), equals
   `f(|ψ|, ψ̂·h, |h|² − (ψ̂·h)²)` with `f` analytic in its three arguments near `(1, 1, 0)`
   (P1's normal form via rotations `R₁, R₂`, (3.24)–(3.25)); state precisely the domains and the
   analyticity of `f`, including in the third argument (P1's `w²`). If the analytic statement is
   much harder than expected, prove the real-analytic or polynomial case first and report.

Infrastructure; recorded reason: needed by I-1 (P2 Prop 1.1 builds on Prop 2.1), the
renormalization conditions (P1 (H.6), P4 (H.5)) and the effective-potential analysis (P1 Prop 3.4)
(`notes/phase1/PLAN.md` W5).

**Sources.** P2 pp. 613–617 (`sources/BF02099510.pdf`, scan: read page images; PDF page =
journal page − 606), P1 pp. 125–130 (`sources/BF02099355.pdf`, scan; PDF page = journal − 102);
reviews `review/papers/P2-*.md` (§2, Lemma 2.1, Prop 2.1), `P1-*.md` (§3 (d)). Copy freely from
any of the author's repositories (no attribution needed); the orthogonal group and sphere
measures are in `/home/scott/Intermittency/Lean/Intermittency/Analysis/SphereLayer.lean`.

**Ownership.** New files under `Balaban/Background/` (e.g. `ConstantConfig.lean`) and
`Balaban/Symmetry/` (e.g. `InvariantReduction.lean`) in your worktree
`/home/scott/Balaban-worktrees/W5` (branch `w5-constant-config`), plus import lines in
`Balaban.lean`.

**Checks.** `lake build` (the whole default target, after merging the current `main` into your
branch — AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide and
may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; declaration names must not clash with
existing ones (search `Balaban/` first).

**Stop condition.** Items 1–2, or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
