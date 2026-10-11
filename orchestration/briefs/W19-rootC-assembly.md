# Brief W19 — Root-C from Root-F, C-1* and I-G (conditional assembly; CORRELATIONS package H)

**Goal.** Prove in Lean the conditional Theorem 3.1 of `notes/phase1/CORRELATIONS.md` (§3: Steps
A–E, Lemma 3.0, Lemma 3.0′): Root-F (as `Balaban.RootFStatement`, landed in
`Balaban/Correlations/Clauses.lean`, checked definitionally equal to the frozen Root-F), the
interface C-1* (§2.2, (F1)–(F3), finite-torus form) and the Gaussian kernel hypotheses I-G
(`Balaban.KernelHyp`, `Balaban/Correlations/GreenIdentification.lean`) imply Root-C.

This is also the test of the C-1* interface before it is proposed for freezing (surface v2): if
C-1* as written in §2.2 does not suffice, or is stronger than needed, say exactly where.

**Steps.**
1. `def RootCStatement (d N : ℕ) : Prop` — a verbatim copy of the type of the frozen
   `Balaban.lowTemperature_correlations` (`Balaban/Frozen/Roots/LowTemperatureCorrelations.lean`;
   read it, never import it), in the style of `RootFStatement` (same file conventions, docstring
   saying it is a copy). The orchestrator checks definitional equality with a scratch probe; do not
   import the root to do it yourself.
2. `structure C1Star …` (non-frozen file): the exact content of C-1* (F1)–(F3) of §2.2, with the
   quantifier order there (constants `a, γ₀, c_*, c_ξ, c', ρ₀, ρ₁, β_*, J` before `β`; then `ξ, μ_j,
   r^ℓ, e_m^ℓ`), the objects named as in §2.2 (the running sequences of
   `Balaban/Flow/RunningCoefficients.lean`, `termKernel` for `T_j^{ℓ,μ}`, the torus functions
   `m_ℓ, G_{tr,ℓ}, G_{lg,ℓ}` of Lemma 0.2 from the landed `Balaban/Correlations/*`). (F4) is not a
   hypothesis. Decide how C-1* is tied to Root-F's `L, M` (§2.2: "the integers of Root-F at
   `κ = κ_*`, `c₉ = 1`"); prefer a single joint hypothesis that the eventual flow theorem can supply
   (e.g. `∃ L M β₀`, Root-F's clauses at `κ_*`, `c₉ = 1` with these `L, M`, and `C1Star d N L M`),
   and explain the choice. No proof step may be a field (AGENTS.md hard rules): the fields are
   exactly (F1)–(F3).
3. The theorem (name free, e.g. `rootC_of_rootF_c1Star`): the joint Root-F/C-1* hypothesis and
   I-G (as `∃ t t0 C_G δ_G C_P, KernelHyp …` for the `a` of C-1*) imply `RootCStatement d N`, for
   `d ≥ 3`, `N ≥ 2`. Follow Steps A–E; reuse the landed `twoPoint_tendsto_along_multiples`,
   `abs_onePoint_sub_le`, Lemma 1.3/Tannery (`Series.lean`), `Asymptotics.lean`,
   `KernelHyp.tsum_eq_latticeGreen`, `goldstone_rewriting`, `Balaban.Flow.exists_gamma_infty`,
   `latticeGreen_existsUnique`.

**Coordination.** Worker W17 is discharging `KernelHyp` in parallel and may weaken its fields
(option (b) of its brief). Use `KernelHyp` only through its theorems (`tendsto_termKernel`,
`sum_rule_limit`, `sum_rule_zero`, `tsum_eq_latticeGreen`) and through the fields `g1`–`g3`, `g5`
where unavoidable; whoever lands second adapts.

**Ownership.** New files under `Balaban/Correlations/` (e.g. `RootCStatement.lean`,
`C1Star.lean`, `Assembly.lean`) in your worktree `/home/scott/Balaban-worktrees/W19` (branch
`w19-rootC-assembly`), plus import lines in `Balaban.lean`. Small additions to landed
`Balaban/Correlations/*` files only if unavoidable (say which). Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`. Copy freely from any of the author's
repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Step 3, or about 3,000 lines, or a precise obstruction (a step of §3 that does
not follow from (F1)–(F3), I-G and Root-F — quote it and stop; that is a finding about C-1*).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; `RootCStatement`, `C1Star` and the main theorem with full statements; how C-1*
is tied to Root-F; any change C-1* needs; checks and results; axioms; last commit hash.
