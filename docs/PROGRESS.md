# Progress

*Last updated: 2026-10-14.*

Neither main theorem is proved yet. Both are stated in Lean, and their proofs are the registered
placeholders `sorry`; see the [README](../README.md).

**Overall estimate: about 77% of the Lean by volume, and about 48% when weighted by difficulty and
risk.**

- **By volume.** About 660,000 lines are written (the [size table](#size-of-the-lean-by-area)
  below has the exact count by area). The finished formalization should need roughly 0.8–1.0
  million lines.
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
| One step, space-dependent external field | P1 (H.4)–(H.7) | 80% | The setting with a free datum; at a free datum: the critical point, tangent and fluctuation path, the raw step functions, the action expansion and the pointwise integrand; the step identity itself at a free datum for the zero class with every hypothesis discharged; the E1 and M0 coefficient values at a free datum given the activity identity. At a free datum: the E1 common activity, the E1 coefficient sum and the observable activity, from the direct-term witness. The first-order energy coefficient family at every chart datum. The first-order energy and observable coefficient families at every chart datum. | The coefficient families at a free datum assembled; general classes (blocker 6). |
| General inherited terms and the small-field induction | P4, P5 | 42% | The step identity and the activity bound for an arbitrary class member, under explicit hypotheses on its inherited terms; the split of the step into new terms and inherited terms; the inherited energy and observable terms as inputs of the step, given the chart inclusion and a composition identity on local generating sets. The first-order marks of a general class member split into zero-class marks plus inherited-energy terms, with Cauchy bounds. The step identity for a general class member; inherited observable marks; renormalization inputs with nonzero budgets; a design for the decoupled form of inherited terms. Inherited terms re-expand exactly around a localized generator; the per-label identity with the term at the composed pair; marks of inherited terms; the local zero class. Localizing inherited terms needs local term generators (blocker 6). Lossless chart composition (the chart test holds for classes with inherited terms). | The inherited terms as inputs of the expansion; the next class member; reality and symmetry clauses; the induction itself. |
| First step from the unit lattice | P4 (2.42)–(2.54) | 60% | The block-averaged density, the hemisphere chart identity, the physical cutoff with its support at the background centre, the chart integrand at the variable centre, the identification of the lifted action with the physical one, the constrained chord identity, the physical Hessian with its coercivity, and the chart integral as a Gaussian integral times the hard-spin remainder. The full-torus cut covariance and its inverse square root, restricted to a cut component, equal the component ones with volume-independent exponential bounds; the determinant of the cut operator factorizes over components. The real inverse square root of the Gaussian form and the tangent Gaussian identity for complex integrands. The cut family of the physical chart, the selection of the good region and its cut, and the Gaussian normalization at the selected cut, which factorizes over the cut. A plan of the remaining seventeen pieces (BASEPLAN). The parametrix on the full parameter discs, the constrained covariance from it, the retained-spin chart integral, the site-local remainder, the x-variant without k ≥ 1. | The Gaussian normalization of the chart integral; the choice of the cut component in the physical sector; energy and observable terms of the first step; its large-field components. |
| Large-field regions | P5–P7, E8–E10 | 45% | Large-field records, region geometry, Peierls bounds, the R operation and its normalization, parts of the polymer gas. | Physical estimates for the regions; the gas of removed components (blockers 2–4). |
| Last integral | P7 §4 | 55% | The stopping scale; resolvent bounds for the final operator; a proposed macroblock parametrix for a reference operator, with analytic resolvent and square-root families and row and column decay bounds at the same rate. Coefficients vanish unless their support is connected; the row, column and square-root estimates hold for any coercive decaying matrix (the variable saddle). The square-root cut family vanishes at the origin of its parameters, so the localized determinant needs another parametrization. The localization rebuilt: no square-root family needed; the determinant ratio det(U+E)/det(U) as a product of local, bounded factors; the cutoff interaction analytic on the full parameter polydisc with local coefficients; the final-scale term bound in Root-F's form from an activity bound. | The physical final Hessian and its connection to the reference family; locality, determinant and torus comparison of the last terms (blocker 5). |
| No renormalization step (large field ν) | P7 §4 | 40% | The sector decomposition; the polymer gas for the sector where every spin is near h. | The sector containing reversed spins (blocker 1); currently paused. |
| Independence of the torus | P4 (H.4) | 92% | Two-torus correspondence of sites, cubes, blocks, size functions, dependency sets, decoupling indices, connected families, data and sources, the cube operators, the decoupled Green operators, the decoupled background and fluctuation solutions, the decoupled covariance and its square root on a cut component, the determinant activities, the marked energy terms and corrected marks on corresponding labels, and the box sums. The E1 and E0 coefficients agree on two tori, from the tower, for labels in a common box; generic transport of observable coefficients. The two-torus E1 and E0 statements hold from the tower without extra radius or margin hypotheses. The observable coefficient agrees on two tori from the tower at zero source. | The coefficient values through fixed formulas on both tori; the last scales and the reading of the clause (blocker 7). |
| General d, L, N and every unit h | — | 92% | All tower records for general parameters with one producer; every fixed-parameter producer, the scale producer, the output constants and the scalar lemmas are corollaries of the general ones; the determinant terms, the zero-class activity bound at every scale, the source activities and most of the renormalization chain of one step for general parameters. The observable families, the source exponent family and the step pieces of one step are now general too. The step identity, the zero-class families and sites, Theorems 3.1(a) and 3.1(b) with site domains, the observable root terms and the renormalization records are general; the fixed-parameter theorems are corollaries. Every unit external field h: Root-F's clauses transfer from the coordinate direction by a rotation, and the chain to the root-term families holds at source radius √N. | The step identity and the final combined statement at general parameters; arbitrary unit h. |
| Assembly of Root-F | P4, P7, P9 | 20% | Step domains are polymers in the theorem's sense; every admissible torus is a step torus at every scale; conversion of the decay rate; the new observable terms of one step as a family with the theorem's support, locality, analyticity and per-term bound c₉ L^{-j((d-2)/2+δ)} e^{-κ|X|/(ML^j)^d} at their birth scale. | The terms of earlier scales; the logarithm; the large-field and final terms. |
| Root-C from Root-F | P8, P9 | 30% | The deduction of the correlation estimates from the flow, assuming its inputs. | Infinite-volume limits, the limit ν ↓ 0, and the physical inputs. |

## Size of the Lean by area

Generated by `python3 scripts/progress_table.py --update docs/PROGRESS.md`. Line counts measure what
exists, not what is proved correct or what remains. Everything counted here compiles without
`sorry` or axioms, apart from the two main theorems.

<!-- BEGIN GENERATED SIZE TABLE -->
Computed at commit fbd2253b 2026-10-14.

| Section | Lean files | Lines | Declarations |
|---|---:|---:|---:|
| Frozen model and root statements | 19 | 2,011 | 142 |
| Lattice, analysis, Gaussian and polymer tools | 160 | 63,450 | 2,606 |
| Green's functions and random walks | 90 | 35,672 | 1,734 |
| Background fields and generating sets (P2) | 111 | 39,282 | 2,096 |
| Localization expansions (P3, P6) | 238 | 75,515 | 3,512 |
| Small-field class (P1, P4, P5) | 130 | 39,645 | 2,021 |
| Fluctuation step and renormalization (P4-P6) | 466 | 154,297 | 5,245 |
| Instantiated step at fixed parameters | 289 | 95,508 | 2,666 |
| Large-field regions (P5-P7, E9-E10) | 499 | 136,992 | 7,484 |
| Observables and correlations (P8, P9) | 70 | 16,758 | 663 |
| **Total** | **2072** | **659,130** | **28,169** |
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
| 2026-10-13 (evening) | ~65% | ~38% | General d, L, N through the step's records, determinant, activities, marks and E1/E0 families; two-torus comparison of every coefficient ingredient; zero-class step identity at a free datum; first-step chart and Hessian; research route for blockers 3–4 |
| 2026-10-13 (night) | ~66% | ~38% | First-step covariance and determinant on a cut component; observable families, source exponent family and step pieces for general d, L, N; blocker 3: two workarounds ruled out, question drafted |
| 2026-10-13 (late night) | ~68% | ~39% | General d, L, N nearly complete for the step; E1 and E0 coefficients on two tori from the tower; off-fibre activities at a free datum; first-step Gaussian normalization; blocker 6 local datum by restriction (radius loss too large at the same radius) |
| 2026-10-13 (midnight) | ~69% | ~40% | Step identity for a general class member; first-step Gaussian at the selected cut; two-torus E1/E0 from the tower without extra hypotheses; route for arbitrary unit h |
| 2026-10-14 (early) | ~71% | ~41% | Arbitrary unit h through the chain and at the root; off-fibre E1 and M0 families at every datum; observable coefficient on two tori; last-integral connected supports and generic estimates; blocker 6: radius bookkeeping settled, composition and engine obstacles identified |
| 2026-10-14 (later) | ~73% | ~43% | Last integral localized (determinant ratio, interaction, term bound); blocker 6: lossless composition, background and fluctuation engine on the local generating set; first step through the parametrix |
| 2026-10-14 (evening) | ~74% | ~44% | Blocker 6: replacement identity for two generating sets, local covariance and fluctuation variable; last integral on two tori (up to winding terms); Root-F constants satisfiable in the root's quantifier order; blocker 7 analysed at the last scales |
| 2026-10-14 (night) | ~75% | ~45% | Blocker 6: replacement identity at the local generating set with a collar and the local fluctuation variable; last integral: second-order bound of the interaction, amplitude β^{-1} as in the papers, determinant ratio proportional to the perturbation; two-torus closeness of the final operator; Root-F skeleton re-audited |
| 2026-10-16 | ~76% | ~47% | Blockers re-read against the Yang–Mills account; blocker 4 resolved in Lean up to the physical inputs (clusters on the core); blocker 6 local class: locality, bound, rotation, extension off the domain; first step: shifted resolvent and square root uniform in the shift; last scale: two-torus closeness uniform in the scale; root constants for every dimension, principal logarithm |
| 2026-10-16 (late) | ~77% | ~48% | Blocker 6 local class assembled at the new level (energy and source parts; design review of the filing of old terms running); blocker 7 last scale: resummation with the infinite-volume limit and a two-torus closeness uniform in the support size; first step: background identified with the step's, logarithm at the physical point, localization; blocker 4 gas bound down to the small factor of removed components; blocker 2 route leaves |
