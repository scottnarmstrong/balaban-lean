# Brief W65 — the small-field class Def-6 in Lean (draft, not frozen)

**Goal.** Write the small-field class ℛ^sf_k of `notes/phase1/SMALLFIELD.md` v3 §1.1–§1.3, §1.6 (Def-6 =
the small-field part of LF Def-7: P5 (1.8)–(1.9) form for k ≤ k₀, the extra sum (1.8) on subdomains;
(CONT) as a class clause; analyticity domains via `Ξ`, `Ξ^c` (landed `Balaban/SmallField/Xi*.lean`) or the
data domains of radius Kε_j; P4 numbering with P1's in brackets) as Lean definitions, at λ = ∞:
(H.1) the density form `ρ_k = χ_k exp[𝒜_k + ℱ_k]` with the main action `A_k` at the background field
`bgField` (landed Def-5), the characteristic function of `Ξ_k(1, β_k^{−1/2}p(β_k))`; (H.2) the effective
action as a sum over scales of local terms of the composed fields `composeField` (I-2), analytic on
`Ξ^c_j(1, ε_j)`; (H.3) symmetries (O(N), Euclidean); (H.4) localization and bounds with the **covering
size functional** (`treeLenCov`, LOCALIZATION v3); (H.5) the renormalization conditions (match the
landed I-6 `Premises` of `Balaban/SmallField/RenormDefs.lean` — state a lemma that a member of the class
supplies `Premises` at each scale, or record exactly which fields are missing); (H.6) the running
coefficients (landed `Balaban/Flow/*`); (H.7) the ℱ part (external field g); and (CONT). Use the
landed objects throughout; definitions must mean the source objects on their whole carrier (no
placeholder or fallback branches; AGENTS rule 4). Also: the one/two-point additions (C-1a, X1–X7 of
`OBSERVABLES.md` v2) as a separate structure extending the class, if budget remains.

This is a draft for review (it will be proposed to the author for freezing later); write docstrings
citing the exact P4/P1/SMALLFIELD equation for each field.

**Ownership.** New files under `Balaban/SmallField/` (e.g. `Def6.lean`, `Def6Terms.lean`) in your worktree
`/home/scott/Balaban-worktrees/W65` (branch `w65-def6`), plus import lines. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`.

**Checks.** Before handoff merge the current `main` and build the whole default target (`lake build`;
AGENTS.md rule 8; at most one build at a time; throttled; never bypass); zero warnings; `#print axioms`
standard; `python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** (H.1)–(H.7), (CONT) and the Premises bridge, or about 2,500 lines, or a precise
obstruction (a clause that cannot be written faithfully with the landed objects — say which and why).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; the full Lean text of the class definition; the Premises bridge statement; open
faithfulness questions; checks; axioms; last commit hash.
