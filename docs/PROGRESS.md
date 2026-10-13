# Progress

*Last updated: 2026-10-13.*

Neither main theorem is proved yet. Both are stated in Lean, and their proofs are the registered
placeholders `sorry`; see the [README](../README.md).

**Overall estimate: about 60% of the Lean by volume, and about 35% when weighted by difficulty and
risk.**

- **By volume.** About 555,000 lines are written. The finished formalization should need roughly
  0.8–1.0 million lines.
- **By risk.** The weighted figure is lower because the parts still open include the hardest
  estimates, and several depend on questions about the papers that are not yet answered; see
  [BLOCKERS.md](BLOCKERS.md).
- **How reliable.** Both figures are judgements made when results are merged, not measurements.
  They have moved by about ±10 points as new difficulties were found or resolved.

## By part of the proof

Each percentage estimates how much of the Lean needed for that part exists and is proved, without
`sorry` or axioms. Most results proved so far are at d = L = 3, N = 2, with general d, L, N as a
separate line below.

| Part | Papers | Estimate | Proved | Main things missing |
|---|---|---:|---|---|
| Model and statements | P1, P9 | 100% of statements | The model (torus, spin measure, energy, partition function, correlation functions), the polymer notion, and the two main theorems are stated and frozen. | The two main theorems are proved by everything below. |
| Lattice and analysis tools | E3, E11, D1–D3 | 90% | Lattice geometry, Gaussian integrals, cluster expansions, polymer gases, Green's functions, random-walk expansions and their decay. | Small additions as the later parts need them. |
| Background fields | P2, E5 | 90% | Existence, uniqueness, analyticity and decay of the constrained minimizer on multiscale generating sets; its local dependence on the data. | Generating sets adapted to a single polymer (blocker 6). |
| Localization expansions | P3, P6 | 75% | Expansion of background-dependent quantities into local terms; decoupling; the localized fluctuation solution and covariance; exact locality of each term on its own domain. | Analyticity on the local domains (blocker 6); the version for inherited boundary terms (blocker 3). |
| One step, no inherited terms | P4–P6 | 93% | The step identity for the next density. Analytic, bounded and exactly local coefficient families for the new energy and observable terms. The renormalization of the new terms, with one solution for all sources. All of it at every datum with constant external field. | The final combined statement (in progress). |
| One step, space-dependent external field | P1 (H.4)–(H.7) | 15% | The setting with a free datum and its comparison with the constant-field case; the critical point, tangent and fluctuation path at a free datum. | The step identity and the coefficient values at a non-constant field. |
| General inherited terms and the small-field induction | P4, P5 | 30% | The step identity and the activity bound for an arbitrary class member, under explicit hypotheses on its inherited terms; the split of the step into new terms and inherited terms; the inherited energy and observable terms as inputs of the step, given the chart inclusion and a composition identity on local generating sets. | The inherited terms as inputs of the expansion; the next class member; reality and symmetry clauses; the induction itself. |
| First step from the unit lattice | P4 (2.42)–(2.54) | 15% | The block-averaged density and the hemisphere chart identity. | Covariance, energy and observable terms of the first step; its large-field components. |
| Large-field regions | P5–P7, E8–E10 | 45% | Large-field records, region geometry, Peierls bounds, the R operation and its normalization, parts of the polymer gas. | Physical estimates for the regions; the gas of removed components (blockers 2–4). |
| Last integral | P7 §4 | 35% | The stopping scale; resolvent bounds for the final operator; a proposed cut family. | The physical final Hessian; the cut family (blocker 5). |
| No renormalization step (large field ν) | P7 §4 | 40% | The sector decomposition; the polymer gas for the sector where every spin is near h. | The sector containing reversed spins (blocker 1); currently paused. |
| Independence of the torus | P4 (H.4) | 45% | Two-torus correspondence of sites, cubes, blocks, size functions, dependency sets, decoupling indices, connected families, data and sources, the cube operators, the decoupled Green operator on a cut component, and the decoupled background on a cut component. | The decoupled fluctuation solution on a component; the coefficients; the reading of the clause (blocker 7). |
| General d, L, N and every unit h | — | 33% | General constant record, scale record and their producers, with an adjustable output decay rate; the fixed-parameter scale producer and the scalar lemmas of the record are now corollaries of the general ones. | Moving the step theorems from d = L = 3, N = 2 to general parameters. |
| Assembly of Root-F | P4, P7, P9 | 20% | Step domains are polymers in the theorem's sense; every admissible torus is a step torus at every scale; conversion of the decay rate; the new observable terms of one step as a family with the theorem's support, locality, analyticity and per-term bound c₉ L^{-j((d-2)/2+δ)} e^{-κ|X|/(ML^j)^d} at their birth scale. | The terms of earlier scales; the logarithm; the large-field and final terms. |
| Root-C from Root-F | P8, P9 | 30% | The deduction of the correlation estimates from the flow, assuming its inputs. | Infinite-volume limits, the limit ν ↓ 0, and the physical inputs. |

## Size of the Lean by area

Generated by `python3 scripts/progress_table.py --update docs/PROGRESS.md`. Line counts measure what
exists, not what is proved correct or what remains. Everything counted here compiles without
`sorry` or axioms, apart from the two main theorems.

<!-- BEGIN GENERATED SIZE TABLE -->
Computed at commit 3ad7ffe 2026-10-13.

| Section | Lean files | Lines | Declarations |
|---|---:|---:|---:|
| Frozen model and root statements | 19 | 2,011 | 142 |
| Lattice, analysis, Gaussian and polymer tools | 136 | 43,274 | 2,231 |
| Green's functions and random walks | 69 | 25,028 | 1,465 |
| Background fields and generating sets (P2) | 110 | 39,057 | 2,078 |
| Localization expansions (P3, P6) | 231 | 71,712 | 3,370 |
| Small-field class (P1, P4, P5) | 120 | 37,825 | 1,944 |
| Fluctuation step and renormalization (P4-P6) | 415 | 134,210 | 4,798 |
| Instantiated step at fixed parameters | 237 | 62,340 | 2,126 |
| Large-field regions (P5-P7, E9-E10) | 471 | 127,298 | 7,202 |
| Observables and correlations (P8, P9) | 69 | 16,695 | 660 |
| **Total** | **1877** | **559,450** | **26,016** |
<!-- END GENERATED SIZE TABLE -->

## How the estimates are made

After each batch of results is merged into `main`, every part is compared with its plan in
`notes/phase1/` and with the papers. A part counts as proved only when the exact statement has been
built in Lean. Results that hold only under explicit extra hypotheses are counted at the level of
what they actually prove. The design notes in `notes/phase1/` give, for each part, the remaining
steps as bounded tasks with an estimated size.

## History

| Date | By volume | Weighted | Main change |
|---|---:|---:|---|
| 2026-10-11 | ~10% | — | Statements frozen; work starts |
| 2026-10-12 | ~35% | 25–30% | Background fields, localization, the small-field class |
| 2026-10-13 | ~60% | ~35% | One step without inherited terms nearly complete; exact locality; general constant record; first step, two-torus and assembly lanes started |
