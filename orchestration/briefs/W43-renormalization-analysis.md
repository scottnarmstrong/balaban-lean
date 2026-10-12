# Brief W43 — small field: I-6, the renormalization analysis (Theorem 2.1)

**Goal.** Formalize Theorem 2.1 of `notes/phase1/SMALLFIELD.md` v2 §2 (I-6: P1 §3, Prop 3.10,
Cor 3.11, with the document's new proof: second-order Taylor expansion and the O(N) identity that
removes the marginal gradient term via (H.5)(4), Step 5 as revised for review S-01), in the source
lemma form: hypotheses (H.2)–(H.4) and the first three conditions of (H.5) and the fourth (second
moment), with constants E₀, κ — these are the lemma's genuine premises (a conditional source lemma,
roadmap I-6), stated on the landed objects. Conclusion (a): the per-site decomposition
`𝓔^{(j)}(y; ψ) = 𝓥(ψ(y)) + A_y + 𝓘` with `Σ_y A_y = 0` and `|𝓥|, |𝓘| ≤ C E₀ (ε_k/ε_j)² s^{3−α₁}`; (b):
`|𝓔_k| ≤ C₆ E₀ |T₁^{(k)}|` on `Ξ^c_k(1, ε_k)`, uniformly in k. Read §2.2 (statement), §2.3 (proof), §2.4
(what is used / cited: I-1(e), I-2, P1 Lemma 3.1, path and volume bounds), §2.6.

Inputs available in Lean: the background fields `Balaban/Background/*` (I-1, I-1(e) `bgFieldC_holder`,
I-2 `theorem73_*`, `composeField`, `scaledComposition` for (R-S)), the polymer/localization
geometry (`Balaban/Localization/*`, `Balaban/LargeField/Geometry/*`), Cauchy estimates
(`Balaban/Analysis/*`, `Balaban/Localization/PartialDeriv.lean`). The analyticity spaces Ξ are being
written in parallel (W42, `Balaban/SmallField/Xi*.lean`, not yet landed): state the domain
hypothesis of Theorem 2.1 abstractly (a predicate on ψ given as a parameter, with the properties
(R-S)/(Σ1)–(Σ2) the proof uses as hypotheses that are genuine premises of the source lemma, not proof
steps), so that W42's spaces instantiate it later; say exactly which properties you require.

**Ownership.** New files under `Balaban/SmallField/` (e.g. `Renormalization.lean`,
`RenormalizationTaylor.lean`) in your worktree `/home/scott/Balaban-worktrees/W43` (branch
`w43-renormalization`), plus import lines in `Balaban.lean`. Do not create `Xi.lean`/`XiProps.lean`
(W42's). Never import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes (search `Balaban/` first).
Commit after each module.

**Stop condition.** Theorem 2.1 (a) and (b), or about 3,000 lines, or a precise obstruction (a step of
§2.3 that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`. AGENTS rule 4: theorem
hypotheses are only source premises and typing data — (H.2)–(H.5) are premises of the source lemma
(P1 Prop 3.10), but any intermediate estimate of §2.3 must be proved, not assumed.

**Handoff.** Files; the hypothesis structure (full text) and the main theorem statements; checks and
results; axioms; open questions; last commit hash.
