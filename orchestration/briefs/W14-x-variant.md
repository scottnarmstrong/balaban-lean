# Brief W14 — the x-variant: G-1(a′), G-2(vii)(i), G-6(b), (b′)

**Goal.** Formalize the x-variant results of `notes/phase1/GREEN.md` (final): the operator
`G_{k,x}(α₀)` of (1.7) (P3 (3.8)), with the bracket `S_x = a_k − a_k² A_{k,x}` on `Ω_{k+1}` and the
multiscale term on `Ω_{k+1}^c`, `x ≥ 0`:

1. **G-1(a′)** coercivity of the x-variant, uniformly in `x ≥ 0`, for `|α₀| ≤ a_{k+1}L^{−2}/12`
   (the range restored by re-review N-1), with the blockwise argument of §4.1 / §4.2 (F-04).
2. **G-2(vii)(i)** the `L²` Agmon block decay for `G_{k,x}`, uniformly in `x ≥ 0`, reusing the
   landed Agmon machinery (`Balaban/Multiscale/Agmon*.lean`, `ScaleMismatch.lean`): state how the
   bracket term modifies the commutator estimate (explicit `s₁, s₂` of F-04).
3. **G-6(b)** the x-variant reduction `C^{(k)}_x = A_{k,x} + a_k² A_{k,x} Q_k G_{k,x} Q_k^* A_{k,x}` on
   `Ω_{k+1}^{(k)}` (unconstrained), and **G-6(b′)** the constrained covariance
   `C^{(k)}_x = A + a² A Q (G_{k,x} − Π_{k,x}) Q^* A` derived with the embedding `E` of `φ₀^⊥` and the
   constrained inverse `G_c = E(E^*HE)^{−1}E^* = G − Π` (§4.7(b′)); both as exact finite-dimensional
   matrix identities (build on `Balaban/Gaussian/Schur.lean` and the constrained operator files
   of W8c if landed by then — check `main` first; if W8c is not on `main`, state the constrained
   part with your own local definition of `Π` and report).

Infrastructure (G-1/G-2/G-6 provider work as editable targets).

**Ownership.** New files under `Balaban/Multiscale/` (e.g. `XVariant.lean`, `XVariantAgmon.lean`,
`XVariantIdentities.lean`) in your worktree `/home/scott/Balaban-worktrees/W14` (branch
`w14-x-variant`), plus import lines in `Balaban.lean`. Copy freely from any of the author's
repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–3, or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
