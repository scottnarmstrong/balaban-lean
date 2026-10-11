# Sources: Balaban's low-temperature O(N) / Heisenberg series

All PDFs live in `../sources/`. Keys P0–P9 are used throughout `review/`.
Reading order follows the logical dependency of the series.
The papers treat classical lattice O(N) ("N-vector") models with N >= 2 in
dimension d >= 3; the 3d classical Heisenberg model is the case N = 3, d = 3.

| Key | File | Paper | Pages |
|---|---|---|---|
| P0 | `3-540-59190-7_30.pdf` | T. Balaban, "A low temperature expansion and 'spin wave picture' for classical N-vector models", Springer proceedings chapter (ISBN 3-540-59190-7, 1995; probably Lecture Notes in Physics 446, *Constructive Physics*) — survey | 18 |
| P1 | `BF02099355.pdf` | T. Balaban, "A low temperature expansion for classical N-vector models. I. A renormalization group flow", Commun. Math. Phys. 167 (1995) 103–154 | 52 |
| P2 | `BF02099510.pdf` | T. Balaban, "The variational problems for classical N-vector models", Commun. Math. Phys. 175 (1996) 607–642 | 36 |
| P3 | `BF02506385.pdf` | T. Balaban, "Localization expansions. I. Functions of the 'background' configurations", Commun. Math. Phys. 182 (1996) 33–82 | 50 |
| P4 | `Balaban.pdf` | T. Balaban, "A low temperature expansion for classical N-vector models. II. Renormalization group equations", Commun. Math. Phys. 182 (1996) 675–721 | 48 |
| P5 | `s002200050433 (1).pdf` | T. Balaban, "A low temperature expansion for classical N-vector models. III. A complete inductive description, fluctuation integrals", Commun. Math. Phys. 196 (1998) 485–521 | 37 |
| P6 | `s002200050470.pdf` | T. Balaban, "Renormalization and localization expansions. II. Expectation values of the 'fluctuation' measures", Commun. Math. Phys. 198 (1998) 1–45 | 45 |
| P7 | `s002200050486.pdf` | T. Balaban, "The large field renormalization operation for classical N-vector models", Commun. Math. Phys. 198 (1998) 493–534 | 42 |
| P8 | `1-s2.0-S0003491697956906-main.pdf` | T. Balaban, M. O'Carroll, "A simple method for correlation functions via the effective actions in the renormalization group framework", Ann. Physics 260 (1997) 1–8 | 8 |
| P9 | `s002200050510.pdf` | T. Balaban, M. O'Carroll, "Low temperature properties for correlation functions in classical N-vector spin models", Commun. Math. Phys. 199 (1999) 493–520 | 28 |

Total: 364 pages.

Notes:
- P1–P4 and P0 are scans; their embedded OCR text is unreliable (e.g. "TV-vector" for
  "N-vector"). Read page images; use `pdftotext` only to locate things.
- P5–P9 are typeset (DVI-derived) PDFs with usable text layers.

Per-paper reviews: `papers/P<k>-<slug>.md`. Synthesis: `BIG_PICTURE.md`,
`FORMALIZATION_ROADMAP.md`.

## External sources (outside the original bundle)

Added 2026-10-11 at the request of the synthesis (see `FORMALIZATION_ROADMAP.md` §8).
Keys E1–E10 are Balaban's earlier papers and other cited works, in date order;
D1–D3 are Dimock's exposition of Balaban's method. Reviews:
`papers/E<k>-<slug>.md`, `papers/D<k>-<slug>.md`. DOIs checked against Crossref.

| Key | File | Paper | DOI | Pages | Cited by |
|---|---|---|---|---|---|
| E1 | `BF01403502.pdf` | C. Cammarota, "Decay of correlations for infinite range interactions in unbounded spin systems", Commun. Math. Phys. 85 (1982) 517–528 | 10.1007/BF01403502 | 12 | P4 [5] |
| E2 | `BF01403506.pdf` | T. Balaban, "(Higgs)_{2,3} quantum fields in a finite volume. I. A lower bound", Commun. Math. Phys. 85 (1982) 603–626 | 10.1007/BF01403506 | 24 | P4 [3] as printed (possibly a misprint) |
| E3 | `BF01214744.pdf` | T. Balaban, "Regularity and decay of lattice Green's functions", Commun. Math. Phys. 89 (1983) 571–597 | 10.1007/BF01214744 | 27 | P2 [2a], P3, P5 [5a], P6 [6a] |
| E4 | `BF01215753.pdf` | T. Balaban, "Propagators and renormalization transformations for lattice gauge theories. I", Commun. Math. Phys. 95 (1984) 17–40 | 10.1007/BF01215753 | 24 | background for E5 |
| E5 | `BF01240221.pdf` | T. Balaban, "Propagators and renormalization transformations for lattice gauge theories. II", Commun. Math. Phys. 96 (1984) 223–250 | 10.1007/BF01240221 | 28 | P2 [2b], P3 [2b] |
| E6 | `BF01215223.pdf` | T. Balaban, "Renormalization group approach to lattice gauge field theories. I. Generation of effective actions in a small field approximation", Commun. Math. Phys. 109 (1987) 249–301 | 10.1007/BF01215223 | 53 | P1 [2d] |
| E7 | `BF01239022.pdf` | T. Balaban, "Renormalization group approach to lattice gauge field theories. II. Cluster expansions", Commun. Math. Phys. 116 (1988) 1–22 | 10.1007/BF01239022 | 22 | background (cluster expansions) |
| E8 | — NOT YET OBTAINED — | T. Balaban, "Convergent renormalization expansions for lattice gauge theories", Commun. Math. Phys. 119 (1988) 243–285 | 10.1007/BF01217741 | 43 | P5 [5b], P6 [6b] |
| E9 | — NOT YET OBTAINED — | T. Balaban, "Large field renormalization. I. The basic step of the R operation", Commun. Math. Phys. 122 (1989) 175–202 | 10.1007/BF01257412 | 28 | P5 [5c], P6 [6c] |
| E10 | — NOT YET OBTAINED — | T. Balaban, "Large field renormalization. II. Localization, exponentiation, and bounds for the R operation", Commun. Math. Phys. 122 (1989) 355–392 | 10.1007/BF01238433 | 38 | P5 [5d], P6 [6d] (P6 Prop. 3.2) |
| D1 | `Dimock-I-arXiv-1108.1335.pdf` | J. Dimock, "The renormalization group according to Balaban I. Small fields", Rev. Math. Phys. 25 (2013) 1330010; arXiv:1108.1335 | 10.1142/S0129055X13300100 | 52 | — |
| D2 | `Dimock-II-arXiv-1212.5562.pdf` | J. Dimock, "The renormalization group according to Balaban II. Large fields", J. Math. Phys. 54 (2013); arXiv:1212.5562 | 10.1063/1.4821275 | 94 | — |
| D3 | `Dimock-III-arXiv-1304.0705.pdf` | J. Dimock, "The renormalization group according to Balaban III. Convergence", Ann. Henri Poincaré 15 (2014) 2133–2175; arXiv:1304.0705 | 10.1007/s00023-013-0303-3 | 37 | — |

Not obtained, no DOI: D. Brydges, "A short course on cluster expansions", in
*Critical Phenomena, Random Systems, Gauge Theories* (Les Houches 1984),
Elsevier 1986 (cited by P5 [6], P6 [7]).

Notes: E1–E7 are scans (unreliable OCR; read page images). D1–D3 are arXiv
typeset PDFs with good text layers.
