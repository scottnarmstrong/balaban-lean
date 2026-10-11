# Brief W28 — background fields IV: the composition domains (Lemmas 6.2, 6.3) and the scaled chain (R-S)

**Goal.** Formalize the domain statements for the composed field, on top of the landed
`Balaban/Background/{Data,Calculus,Contraction,Composition,CompositionSystem}.lean`
(`composeField`, `composeData`, `compWeight`, `Precedes`, `InPsiTilde` (R1)–(R4), `InPsiTildeC`
(C1)–(C3)):

1. **Lemma 6.2** (`notes/phase1/BACKGROUND.md` v2 §6.6, P2 Lemma 4.3): for real data
   `(Ψ′, h) ∈ Ψ̃(𝔹′_k; δ)` and a field `φ′` satisfying the bounds of Theorem 5.2(3)
   (`|φ′ − Q*ψ′|₀ ≤ K₁δ`, `|∂φ̄′|(b) ≤ K₁δ/ℓ′(b)`, `φ′·φ′ = 1`, the (R3)-type bound) — taken as explicit
   hypotheses on `φ′` (this is a lemma about any such field; the existence theorem will supply
   them later) — `composeData … ∈ Ψ̃(𝔹_j; C₄K₁δ)` with `C₄ = C₄(d)`, following (E1), (E2), (R1)–(R4),
   (E3) and the gap/collar cases of §6.6. Prove `a_p/a_n · L^{2(n−p)} ∈ [0, 1]` for the weights (6.1)
   (`compWeight`) — this was left open by W23.
2. **Lemma 6.3** (complex data), §6.6 end, with its hypotheses on `φ′^c − φ′^r`.
3. **(R-S) the scaled composition** (`notes/phase1/SMALLFIELD.md` v2 §1.7, requirement of review
   S-02): the statements (i)–(iii) with `s = L^{−(k−j)}`, `σ = C₀s`, including the second-order
   condition (R2′) `|ψ_j·ψ_j − 1| < σ²ε`, derived from formula (6.2) (the discrepancy carries `s²`).
   State the exact hypotheses you need on the input field (as in 1).
4. Realness: `composeData` is real for real `D′`, `φ′`.

**Ownership.** New files under `Balaban/Background/` (e.g. `CompositionDomain.lean`,
`ScaledComposition.lean`) in your worktree `/home/scott/Balaban-worktrees/W28` (branch
`w28-composition-domain`), plus import lines in `Balaban.lean`. Workers W22 (approximate field,
files like `BlockGeometry`, `BSpline`, `Interpolation`, `Approximate`) and W27 (refactoring
`Contraction.lean`, `ContractionAnalytic.lean`) are active: do not touch their files. If you need a
geometric lemma that W22 is likely to prove (block paths, layer adjacency), write your own under a
distinct name and say so. Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).

**Stop condition.** Items 1–3 (4 if cheap), or about 2,500 lines, or a precise obstruction (an
estimate of §6.6 or (R-S) that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
