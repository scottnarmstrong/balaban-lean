# Brief W22 — background fields II: the approximate solution (Lemma 5.3)

**Goal.** Formalize the approximate hard-spin field of the background-field problem following
`notes/phase1/LEMMA53-astra.md` (a full proof replacing `notes/phase1/BACKGROUND.md` v2 §5.3,
Lemmas 5.3, 5.3a, 5.3b; it corrects 5.3a(b), which is false for the one-site collar in d ≥ 4: at
layer one the field is the local constant solution of its own block). Work in the order of its §6
("Lean lemma order and dependencies"), items 1–8:
1. block geometry; 2. separation consequences; 3. high-layer chain (only for layer ≥ 2);
4. local complex solution (the explicit formula `φ^B = w_B/√(w_B·w_B)`, principal square root;
   reuse `Balaban/Background/ConstantConfig*.lean`); 5. periodic B-spline bumps; 6. the normalized
   quotient; 7. interpolation bounds; 8. the approximate solution and its residual, then Lemma 5.3.

Use exactly the landed conventions the note names: `GeneratingSet.layerIndex`, `spacing`,
`IsSmoothField` (both signs of `e_μ` at the spacing of `x`, centred Laplacian), `vn` (Euclidean),
`PathCost` only inside `Ω₁` (never for collar paths). The data types (`BgData`, collar, the domain
predicates (R1)–(R4), (C1)–(C3)) are those of `Balaban/Background/Data.lean` from W20 — your branch
starts at W20's Data commit (781930a); W20 is still running in another worktree (it owns
`Balaban/Background/Calculus.lean`, `Data.lean`, `Contraction.lean`: do not edit those files; if
you need a change there, stop and report it).

**Ownership.** New files under `Balaban/Background/` (e.g. `BlockGeometry.lean`, `BSpline.lean`,
`Interpolation.lean`, `Approximate.lean`) in your worktree `/home/scott/Balaban-worktrees/W22`
(branch `w22-approximate-field`), plus import lines in `Balaban.lean`. Never import
`Balaban/Frozen/Roots/*` or `Balaban/Provider/*`. Copy freely from any of the author's
repositories (no attribution needed).

**Checks.** Before handoff merge the current `main` (it will contain W20 once landed; if W20 is not
landed yet, merge main anyway and say so) and build the whole default target (`lake build`; AGENTS.md
rule 8; at most one build at a time; compiles are throttled machine-wide and may wait; never bypass
the throttle); zero warnings; `#print axioms` standard; `python3 -I scripts/check_lean_modules.py
--root .`; no name clashes (search `Balaban/` first). Commit after each module.

**Stop condition.** Items 1–8 (Lemma 5.3 assembled), or about 3,500 lines, or a precise
obstruction (an estimate of the note that fails — quote it and stop).

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; no file
over 10,000 lines; commit on your branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
