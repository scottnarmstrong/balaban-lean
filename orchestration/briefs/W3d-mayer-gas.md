# Brief W3d — the Mayer layer MY and the boundary-term lemma GAS

**Goal.** Formalize the last two components of `notes/phase1/POLYMER.md` (revised; §2.4 MY,
§3.7 proof of MY, §2.6 GAS with the review-corrected statement (rate κ′ − 2, Z–Z′ overlap in the
contact relation), §3.9 its proof), on top of the landed `Balaban/Polymer/*` (`pe_xi_eq_exp`,
`pe_lattice`, `pe_sized`, `pe_hole`, `pe_blockTorus_frozen`, marked results in `Marked.lean`,
`pe_analyticOnNhd`):

1. **MY (Mayer layer for product measures).** For a product probability measure `ν` on a finite
   product of factor spaces and an interaction `exp(Σ_Y H(Y))` with local terms `H(Y)` (depending
   only on the coordinates in `Y`, bounded as in MY), expanding `e^{H} = 1 + (e^{H} − 1)` and
   integrating gives a polymer gas whose activities are integrals of products over connected
   families, with the bound MY (iii); then PE-L / `pe_sized` applies. Use `Measure.pi` and
   independence on disjoint coordinate sets. State MY with the hypotheses POLYMER.md lists, and the
   combined corollary (entropy bound required twice, for terms and unions — review R7).
2. **GAS (non-small boundary terms, P7 (3.26)–(3.29), (4.11)–(4.14)).** As restated in POLYMER.md
   §2.6 after review R8: activities that are not small but carry a volume decay `e^{−H|Z|}` absorb
   a fixed constant; give the lemma and its consequence for the polymer expansion with explicit
   constants.
3. If budget remains: the instance-free form of the P9 Prop 3.1 corollary (one and two functions,
   (3.11)–(3.13)) as a theorem about an integral `Ξ(λ) = ∫ exp Σ H_λ dν` under (H-MY) (POLYMER.md
   §4.1), connecting MY with the landed marked results.

**Ownership.** New files under `Balaban/Polymer/` (e.g. `Mayer.lean`, `Gas.lean`,
`TruncatedExpectation.lean`) in your worktree `/home/scott/Balaban-worktrees/W3d` (branch
`w3d-mayer`), plus import lines in `Balaban.lean`. Copy freely from any of the author's
repositories (no attribution needed), e.g. `/home/scott/KPZ/cumulants/Lean/Polymers/` (Lean
v4.26.0).

**Checks.** Before handoff merge the current `main` and build the whole default target
(`lake build`; AGENTS.md rule 8; at most one build at a time; compiles are throttled machine-wide
and may wait; never bypass the throttle); zero warnings; `#print axioms` standard;
`python3 -I scripts/check_lean_modules.py --root .`; no name clashes.

**Stop condition.** Items 1–2 (3 if possible), or about 2,500 lines, or a precise obstruction.

**Do not launch subagents (no Agent tool); work directly.**

**Hard rules** (from `AGENTS.md`): every `.lean` file is a module; no `axiom`, no `sorry`/`admit`,
no heartbeat overrides, no placeholder definitions, zero warnings; frozen files read-only; never
import `Balaban/Frozen/Roots/*` or `Balaban/Provider/*`; no file over 10,000 lines; commit on your
branch only, never push to `main`.

**Handoff.** Files; main theorem names with statements; checks and results; axioms; open
questions; last commit hash.
