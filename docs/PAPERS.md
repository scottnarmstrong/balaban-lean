# Papers

The formalization follows Balaban's series on the low-temperature classical N-vector (O(N)) model,
together with his earlier papers on lattice gauge theories, whose methods the series uses. Keys
(P0–P9, E1–E11, D1–D3) are the ones used throughout the repository: in Lean docstrings, in the
design notes in `notes/`, and in the reviews in `review/`.

The papers are under publisher copyright and are not part of this repository's public content. Use
the DOIs below to find them.

## The O(N) series

| Key | Paper | Role in the proof |
|---|---|---|
| P0 | T. Balaban, *A low temperature expansion and "spin wave picture" for classical N-vector models*. In *Constructive Physics* (Lecture Notes in Physics 446), Springer, 1995. | Survey of the whole programme. |
| P1 | T. Balaban, *A low temperature expansion for classical N-vector models. I. A renormalization group flow*. Commun. Math. Phys. 167 (1995) 103–154. [doi:10.1007/BF02099355](https://doi.org/10.1007/BF02099355) | The block-spin transformation, the small-field effective actions and the inductive hypotheses (H.1)–(H.7). |
| P2 | T. Balaban, *The variational problems for classical N-vector models*. Commun. Math. Phys. 175 (1996) 607–642. [doi:10.1007/BF02099510](https://doi.org/10.1007/BF02099510) | The background field: existence, uniqueness, analyticity and decay of the constrained minimizer given the block averages. |
| P3 | T. Balaban, *Localization expansions. I. Functions of the "background" configurations*. Commun. Math. Phys. 182 (1996) 33–82. [doi:10.1007/BF02506385](https://doi.org/10.1007/BF02506385) | Expanding functions of the background field into sums of local terms with exponential decay; the local generating sets 𝔹(Y). |
| P4 | T. Balaban, *A low temperature expansion for classical N-vector models. II. Renormalization group equations*. Commun. Math. Phys. 182 (1996) 675–721. | One renormalization step in the small-field region: the fluctuation integral and the new effective action; the first step from the unit lattice. |
| P5 | T. Balaban, *A low temperature expansion for classical N-vector models. III. A complete inductive description, fluctuation integrals*. Commun. Math. Phys. 196 (1998) 485–521. [doi:10.1007/s002200050433](https://doi.org/10.1007/s002200050433) | The full inductive description with large-field regions; the fluctuation integrals. |
| P6 | T. Balaban, *Renormalization and localization expansions. II. Expectation values of the "fluctuation" measures*. Commun. Math. Phys. 198 (1998) 1–45. [doi:10.1007/s002200050470](https://doi.org/10.1007/s002200050470) | Localization of expectations with respect to the fluctuation measures; boundary terms. |
| P7 | T. Balaban, *The large field renormalization operation for classical N-vector models*. Commun. Math. Phys. 198 (1998) 493–534. [doi:10.1007/s002200050486](https://doi.org/10.1007/s002200050486) | The large-field renormalization operation, the polymer gas of large-field regions, and the last integral. |
| P8 | T. Balaban, M. O'Carroll, *A simple method for correlation functions via the effective actions in the renormalization group framework*. Ann. Physics 260 (1997) 1–8. | How correlation functions are read off the effective actions with a source. |
| P9 | T. Balaban, M. O'Carroll, *Low temperature properties for correlation functions in classical N-vector spin models*. Commun. Math. Phys. 199 (1999) 493–520. [doi:10.1007/s002200050510](https://doi.org/10.1007/s002200050510) | The main theorem on correlation functions (Theorem 1.1), formalized as Root-C. |

## Earlier papers and other sources used

| Key | Paper | Used for |
|---|---|---|
| E1 | C. Cammarota, *Decay of correlations for infinite range interactions in unbounded spin systems*. Commun. Math. Phys. 85 (1982) 517–528. [doi:10.1007/BF01403502](https://doi.org/10.1007/BF01403502) | Cluster-expansion estimates (cited in P4). |
| E2 | T. Balaban, *(Higgs)₂,₃ quantum fields in a finite volume. I. A lower bound*. Commun. Math. Phys. 85 (1982) 603–626. [doi:10.1007/BF01403506](https://doi.org/10.1007/BF01403506) | Cited in P4. |
| E3 | T. Balaban, *Regularity and decay of lattice Green's functions*. Commun. Math. Phys. 89 (1983) 571–597. [doi:10.1007/BF01214744](https://doi.org/10.1007/BF01214744) | Random-walk expansions and decay of Green's functions (P2, P3, P5, P6). |
| E4 | T. Balaban, *Propagators and renormalization transformations for lattice gauge theories. I*. Commun. Math. Phys. 95 (1984) 17–40. [doi:10.1007/BF01215753](https://doi.org/10.1007/BF01215753) | Background for E5. |
| E5 | T. Balaban, *Propagators and renormalization transformations for lattice gauge theories. II*. Commun. Math. Phys. 96 (1984) 223–250. [doi:10.1007/BF01240221](https://doi.org/10.1007/BF01240221) | Propagators on generating sets (P2, P3). |
| E6 | T. Balaban, *Renormalization group approach to lattice gauge field theories. I. Generation of effective actions in a small field approximation*. Commun. Math. Phys. 109 (1987) 249–301. [doi:10.1007/BF01215223](https://doi.org/10.1007/BF01215223) | Small-field effective actions (P1). |
| E7 | T. Balaban, *Renormalization group approach to lattice gauge field theories. II. Cluster expansions*. Commun. Math. Phys. 116 (1988) 1–22. [doi:10.1007/BF01239022](https://doi.org/10.1007/BF01239022) | Cluster expansions. |
| E8 | T. Balaban, *Convergent renormalization expansions for lattice gauge theories*. Commun. Math. Phys. 119 (1988) 243–285. [doi:10.1007/BF01217741](https://doi.org/10.1007/BF01217741) | The inductive scheme with large fields (P5, P6). |
| E9 | T. Balaban, *Large field renormalization. I. The basic step of the R operation*. Commun. Math. Phys. 122 (1989) 175–202. [doi:10.1007/BF01257412](https://doi.org/10.1007/BF01257412) | The large-field operation R (P5, P6). |
| E10 | T. Balaban, *Large field renormalization. II. Localization, exponentiation, and bounds for the R operation*. Commun. Math. Phys. 122 (1989) 355–392. [doi:10.1007/BF01238433](https://doi.org/10.1007/BF01238433) | Localization and bounds for R (P5, P6). |
| E11 | D. Brydges, *A short course on cluster expansions*. In *Critical Phenomena, Random Systems, Gauge Theories* (Les Houches 1984), Elsevier, 1986. | The cluster-expansion formulas (P5–P7). |
| D1 | J. Dimock, *The renormalization group according to Balaban I. Small fields*. Rev. Math. Phys. 25 (2013) 1330010. [arXiv:1108.1335](https://arxiv.org/abs/1108.1335) | Exposition of the small-field method (for φ⁴ in d = 3), used to check readings of the papers. |
| D2 | J. Dimock, *The renormalization group according to Balaban II. Large fields*. J. Math. Phys. 54 (2013). [arXiv:1212.5562](https://arxiv.org/abs/1212.5562) | Exposition of the large-field method. |
| D3 | J. Dimock, *The renormalization group according to Balaban III. Convergence*. Ann. Henri Poincaré 15 (2014) 2133–2175. [arXiv:1304.0705](https://arxiv.org/abs/1304.0705) | Exposition of the convergence argument. |

## Where the papers are used in the repository

- `review/papers/` has one review per paper: its content, its main statements with page and
  equation numbers, and the points that needed checking. `review/BIG_PICTURE.md` puts the series
  together. `review/FORMALIZATION_ROADMAP.md` is the plan derived from it.
- `notes/ERRATA.md` records misprints and gaps found in the papers and how the formalization
  handles each.
- Lean docstrings cite the papers by key, page and equation number, for example "P3 (4.44)–(4.47)".
