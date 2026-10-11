# Brief W2c — G-4(b), (c) with exponential tails, and the summation lemma 4.10

**Goal.** Complete the unit-lattice interface G-4 of `notes/phase1/GREEN.md` (final version; §3
statement G-4, §4.4 proofs, Lemma 4.10 in §4.10, the dictionary §4.9) on top of the landed
`Balaban/Green/{Coercive,CombesThomas,Restriction,GeometricResolvent}.lean`:

1. **Lemma 4.10 (summation).** The convolution/summation lemma for kernels with exponential
   decay in `|z − w|` and exponential tails around a set `X'`, in the form §4.10 states (including
   the two-line splitting added for G-4(b)). Use the landed `norm_mul_entry_le` /
   `perturbation_decay` patterns.
2. **G-4(b) (domain difference, E3 (5.8)).** For `Λ' ⊂ Λ`, `x₁, x₂ ∈ Λ'`:
   `|(A_Λ+t)^{-1}(x₁,x₂) − (A_{Λ'}+t)^{-1}(x₁,x₂)| ≤ C (γ₀+t)^{-2} e^{−(μ₁/2)(D₁+D₂)}`,
   `D_i = d(x_i, Λ∖Λ')`, `μ₁ = min(ctRate, δ₀)`, `C = C(c₀, δ₀, κ, μ₀)` explicit. Proof from
   `greenFn_resolvent_identity`, `combesThomas_restrict` and Lemma 4.10.
3. **G-4(c) (perturbation with tails, E3 (5.10), (5.17), P4 (2.50)).** For `B` with
   `‖B(z,w)‖ ≤ c₀ e^{−δ₀|z−w|} e^{−δ₀(d(z,X') + d(w,X'))}` and `Re⟨u,(A+B)u⟩ ≥ γ₀‖u‖²`:
   `|(A_Λ+B_Λ+t)^{-1}(x₁,x₂) − (A_Λ+t)^{-1}(x₁,x₂)| ≤ C (γ₀+t)^{-2} e^{−(μ₁/2)(d(x₁,X') + d(x₂,X'))}`.
4. If budget remains: the `ℓ¹`-lattice instantiation of the ball-sum hypothesis `hK`
   (`sup_x Σ_{x'} e^{−(δ₀/4)|x−x'|₁} ≤ κ(d, δ₀)` on `Torus d m` and on finite subsets of `ℤ^d`,
   explicit `κ`) — GREEN.md §4.9 lists it as missing.

Work in the abstract setting of the landed files (finite index type with a pseudometric), with
`d(x, X') = ⨅ x' ∈ X', dist x x'` (state the convention for `X' = ∅` as GREEN.md does).

**Ownership.** New files under `Balaban/Green/` (e.g. `Summation.lean`, `DomainDifference.lean`,
`Perturbation.lean`, `BallSums.lean`) in your worktree `/home/scott/Balaban-worktrees/W2c`
(branch `w2c-g4-tails`), plus import lines in `Balaban.lean`. Do not edit landed files except to
add small missing lemmas (say which). Copy freely from any of the author's repositories (no
attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled
machine-wide and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3 (and 4 if possible), or about 1,500 lines, or a precise obstruction
(e.g. an inequality of §4.10 that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
