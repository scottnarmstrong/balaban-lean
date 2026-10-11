# Brief W15 — Gaussian bookkeeping for Root-C (CORRELATIONS package G, finite-volume parts)

**Goal.** Formalize the finite-volume parts of `notes/phase1/CORRELATIONS.md` (revised) §2.1 and
§3.4–§3.5, package G of §6, on top of the landed `Balaban/Gaussian/Multiscale.lean`
(`laplacian_inv_eq_multiscale`, `fluct`, `prolong`, `effOp`), `Balaban/Gaussian/{Schur,BlockSpin}.lean`,
`Balaban/Lattice/*`, `Balaban/Green/Lattice/*` (W9: `latticeGreen`, `latticeGreen_existsUnique`,
`harmonic_eq_zero`) and `Balaban/Flow/RunningCoefficients.lean` (W4):

1. **The terms in P9's normalization** (§2.1, (2.1)–(2.2)): the `j`-th term `T_j^{ℓ,μ}` of the exact
   decomposition of `(−Δ + μ)^{−1}` on `Torus d ℓ`, `ℓ = L^J m`, with the free sequence
   `a_{k+1}^{−1} = a_k^{−1} + L^{−2k} a^{−1}` (P4 option (i); CORRELATIONS.md §2.3 "Free flow"), as
   the landed `fluct` terms rewritten on the fine torus via `prolong`; the dictionary lemma.
2. **(3.1), (3.2): prolongation composition** — iterated prolongation equals one-shot prolongation
   on nested tori ("iterated = one-shot"), and the identity `A₀ P_J A_J^{−1} P_J^⊤ = Q_{(J)}^⊤ P_J^⊤`
   used in §3.4.
3. **The sum rule on the torus** (§3.4, "The sum rule on the torus"): `Σ_{j<J} T_j^{ℓ,μ} + (remainder)
   = (−Δ + μ)^{−1}` in the form stated there, with the remainder identified.
4. **The (4.18) step** (§3.5): with `β_j` from `betaSeq` (W4) and `exists_inv_betaSeq_asymptotics`,
   the rewriting `Σ_j β_j^{−1} T_j = (βγ_∞)^{−1} Σ_j L^{−j(d−2)} T_j + (error)` with the error bound
   in terms of the kernel bounds (take the kernel bounds as explicit hypotheses named after
   (G1)–(G3) of §2.1; they will be supplied by W13 / G-5 — do not prove them here).
5. If budget remains: the infinite-volume identification `Σ_j t_j^0(x, y) = G(x − y)` (G4) given
   the (G1)–(G3) hypotheses, using `latticeGreen_existsUnique`.

**Ownership.** New files under `Balaban/Correlations/` or `Balaban/Gaussian/` (e.g.
`Gaussian/Prolongation.lean`, `Correlations/SumRule.lean`, `Correlations/Asymptotics.lean`) in your
worktree `/home/scott/Balaban-worktrees/W15` (branch `w15-gaussian-rootC`), plus import lines in
`Balaban.lean`. Copy freely from any of the author's repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–4 (5 if possible), or about 2,000 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
