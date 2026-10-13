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
| One step, no inherited terms | P4–P6 | 96% | The step identity for the next density. Analytic, bounded and exactly local coefficient families for the new energy and observable terms. The renormalization of the new terms, with one solution for all sources. The combined statement at every scale, with constants independent of the scale. All of it at every datum with constant external field. | Identification of two representations of the energy bound. |
| One step, space-dependent external field | P1 (H.4)–(H.7) | 45% | The setting with a free datum; at a free datum: the critical point, tangent and fluctuation path, the raw step functions, the action expansion and the pointwise integrand; the step identity itself at a free datum (under explicit regularity and nonvanishing hypotheses). | The regularity input at a free datum; the coefficient values at a non-constant field. |
| General inherited terms and the small-field induction | P4, P5 | 30% | The step identity and the activity bound for an arbitrary class member, under explicit hypotheses on its inherited terms; the split of the step into new terms and inherited terms; the inherited energy and observable terms as inputs of the step, given the chart inclusion and a composition identity on local generating sets. | The inherited terms as inputs of the expansion; the next class member; reality and symmetry clauses; the induction itself. |
| First step from the unit lattice | P4 (2.42)–(2.54) | 30% | The block-averaged density, the hemisphere chart identity, the physical cutoff with its support at the background centre, the chart integrand at the variable centre, the identification of the lifted action with the physical one, the constrained chord identity, the physical Hessian with its coercivity, and the chart integral as a Gaussian integral times the hard-spin remainder. | Local covariance and determinant on a good component; energy and observable terms of the first step; its large-field components. |
| Large-field regions | P5–P7, E8–E10 | 45% | Large-field records, region geometry, Peierls bounds, the R operation and its normalization, parts of the polymer gas. | Physical estimates for the regions; the gas of removed components (blockers 2–4). |
| Last integral | P7 §4 | 38% | The stopping scale; resolvent bounds for the final operator; a proposed macroblock parametrix for a reference operator, with analytic resolvent and square-root families and row and column decay bounds at the same rate. | The physical final Hessian and its connection to the reference family; locality, determinant and torus comparison of the last terms (blocker 5). |
| No renormalization step (large field ν) | P7 §4 | 40% | The sector decomposition; the polymer gas for the sector where every spin is near h. | The sector containing reversed spins (blocker 1); currently paused. |
| Independence of the torus | P4 (H.4) | 75% | Two-torus correspondence of sites, cubes, blocks, size functions, dependency sets, decoupling indices, connected families, data and sources, the cube operators, the decoupled Green operators, the decoupled background and fluctuation solutions, the decoupled covariance and its square root on a cut component, the determinant activities and the marked energy coefficients. | The assembled coefficient values; the reading of the clause (blocker 7). |
| General d, L, N and every unit h | — | 55% | All tower records for general parameters with one producer; every fixed-parameter producer, the scale producer, the output constants and the scalar lemmas are corollaries of the general ones; the determinant terms, the zero-class activity bound at every scale, the source activities and most of the renormalization chain of one step for general parameters. | The coefficient families, the step identity and the final combined statement at general parameters; arbitrary unit h. |
| Assembly of Root-F | P4, P7, P9 | 20% | Step domains are polymers in the theorem's sense; every admissible torus is a step torus at every scale; conversion of the decay rate; the new observable terms of one step as a family with the theorem's support, locality, analyticity and per-term bound c₉ L^{-j((d-2)/2+δ)} e^{-κ|X|/(ML^j)^d} at their birth scale. | The terms of earlier scales; the logarithm; the large-field and final terms. |
| Root-C from Root-F | P8, P9 | 30% | The deduction of the correlation estimates from the flow, assuming its inputs. | Infinite-volume limits, the limit ν ↓ 0, and the physical inputs. |

## Size of the Lean by area

Generated by `python3 scripts/progress_table.py --update docs/PROGRESS.md`. Line counts measure what
exists, not what is proved correct or what remains. Everything counted here compiles without
`sorry` or axioms, apart from the two main theorems.

<!-- BEGIN GENERATED SIZE TABLE -->
Computed at commit 85953251 2026-10-13.

| Section | Lean files | Lines | Declarations |
|---|---:|---:|---:|
| Frozen model and root statements | 19 | 2,011 | 142 |
| Lattice, analysis, Gaussian and polymer tools | 143 | 50,880 | 2,404 |
| Green's functions and random walks | 71 | 25,349 | 1,474 |
| Background fields and generating sets (P2) | 110 | 39,057 | 2,078 |
| Localization expansions (P3, P6) | 231 | 71,712 | 3,370 |
| Small-field class (P1, P4, P5) | 121 | 37,950 | 1,945 |
| Fluctuation step and renormalization (P4-P6) | 425 | 136,296 | 4,865 |
| Instantiated step at fixed parameters | 253 | 67,478 | 2,292 |
| Large-field regions (P5-P7, E9-E10) | 477 | 129,925 | 7,305 |
| Observables and correlations (P8, P9) | 69 | 16,695 | 660 |
| **Total** | **1919** | **577,353** | **26,535** |
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
