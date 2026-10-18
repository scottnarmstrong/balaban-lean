# Balaban's low-temperature renormalization group for O(N) spin models, in Lean 4

This repository is a formalization in progress, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of Tadeusz Balaban's
renormalization-group analysis of the classical O(N) spin model at low temperature. The papers it
follows were published in 1995–1999, the last two with Michael O'Carroll; [docs/PAPERS.md](docs/PAPERS.md)
lists them.

**Status: unfinished.** The two main theorems are stated in Lean and frozen, but neither is proved.
As of October 2026, about 836,000 lines of Lean (about 650,000 without comments and blank
lines) have been written towards them. The project contains no axioms and no `sorry` other than the
two registered placeholders for the main theorems themselves. See
[docs/PROGRESS.md](docs/PROGRESS.md) for the current size of each part and an estimate of how far it
has come, and [docs/BLOCKERS.md](docs/BLOCKERS.md) for the mathematical questions that currently
block it.

## Where the work stands

As of 18 October 2026. The small-field part of one renormalization step (background fields,
localization, the fluctuation integral and its expansion, the inductive class of effective actions)
is largely formalized, for general d, L and N. The remaining work is concentrated in seven blockers,
described in [docs/BLOCKERS.md](docs/BLOCKERS.md). The current fronts:

- **The large-field gas (blocker 4).** The gas of removed large-field components is bounded from
  the bound of each removed outcome, summed over histories. The composed window bound is now
  proved (the intermediate Gaussian variables integrated exactly, the steps' actions summed into
  the window's, the cancellation identity of P7 (2.58′)), from named P7 source estimates. For the
  comparison of the steps' actions with the window's, every premise is now proved for the actual
  pieces (read transport, coefficient, source and pair estimates, with constants uniform in the
  scale), and so are the stability of the background under a change of generating set (P7 (2.14))
  and the background hypotheses of the window. Following P7, the pieces and the window are evaluated
  at one configuration, which gives the window's domain from the pieces' domains, and the window
  point's field restricts to the pieces' data. The reference datum of the cancellation chain was
  found to be outside the domain on the collar (it is zero there), which made that chain's hypothesis
  unsatisfiable; it is being restated with the collar data required by the collar ruling. R's output is being written as a gas of removed clusters
  (ruling R4).
- **The last integral and the case with no renormalization step (blockers 5 and 1).** The
  large-field part cannot be one factor per bad block times boundary terms: a good block between
  two bad blocks couples them (`notes/phase1/astra/KF0B.md`, Theorem B.7). P7 instead expands into
  linked terms, switched on by a possibly disconnected set of bad blocks and reading a connected
  region. The gas for such terms is proved (exact identity and activity bound, with the large
  boundary constant paid by the heavy charge), and so is the bound on the coefficient summed over
  all linked clusters with a given footprint; their identification with P7's operator is in
  progress. The first large-field component of the base case has its local pieces; its physical
  kernel waits on a change of the base carrier (ruling R7).
- **The general inductive class (blocker 6).** The inherited terms enter through their irrelevant
  parts (P1 Prop. 3.10). The chain is proved at towers for every scale with one threshold β₀: the
  step radius follows the class radius (t_k = ε_{k+1}), the fluctuation radius is separate, and the
  collar is the papers' wider one, so the step's chart covers the next class's chart while the
  inherited terms keep room in their domains (with the narrower collar used before, the two are
  proved incompatible). The filed torus defect is bounded at every centre. The coefficients of the
  chain are invariant under spin rotations, label by label, at the final theorem. The new level's
  terms must be computed with the local generating set of each polymer, as in P3 (4.44)–(4.47):
  mapping a local field to the step's chart is impossible in general (a local field can wind around a
  hole of the polymer). This needs the step's objects for a general background generating set
  (ruling R8 asked); the parts that need no ruling are in progress.
- **Two tori (blocker 7).** The clause at the gap scales is proved at the tower, on one family of
  tori of every size, with the energy, determinant and observable terms tied to the step terms and
  the geometry proved. What it takes as input is the agreement of the earlier scales' data on two
  tori (the induction over scales); for Root-F, the sum over roots and the inherited terms remain.
- **From one step to the next (the backbone).** The old terms are transported to the next scale's
  torus, and on domains frozen at each level's birth mass (ruling R6) they keep all the clauses of
  the class, including torus independence and the renormalization conditions. The step's large-field
  data carry the vacuum constants of the step that created each region (ruling R5). For the new
  level, the labels from the chain on the hull of their read sets, the sum of their bounds (every
  class rate κ ≤ 1/200 at d = L = 3), the covariance of its densities under the full symmetry group,
  the closure of its energy constant (one chain carrying any property of the coefficients from the
  core to the final theorem), the renormalized field in the step's chart and the second-order
  counterterms at the towers are proved; its terms on the local charts, the old terms of a general
  class at the renormalized field and the assembly of the new energy density remain. Root-C's coefficient flow is
  formalized for the parts that do not depend on the next class.
- **Blockers 2 and 3.** The change of background along the flow is being implemented (ruling R2:
  separate background and cutoff masses, extended direction tests, complex sources). For old
  boundary terms across a long hole, the sufficient condition is proved in exponent arithmetic; its
  physical producer needs the linked construction of the last integral.

We no longer wait for the author's answers to source questions: where the papers are ambiguous we
choose a reading and prove what it needs ([`notes/phase1/PLAN-B.md`](notes/phase1/PLAN-B.md)).

## The mathematics

The model is the classical N-vector (O(N)) model on the lattice ℤ^d, d ≥ 3, N ≥ 2, with hard spins
φ(x) ∈ S^{N-1}, at inverse temperature β, in a weak external field νh (|h| = 1, 0 < ν ≤ 1). For N = d = 3
it is the classical Heisenberg model. At low temperature (large β) the spins are aligned. The
correlations then decay like a power law in the directions transverse to the magnetization: these
are the Goldstone modes, or spin waves. The external field cuts the power law off at distance ν^{-1/2}.

Balaban's proof is a multiscale renormalization group. At each scale the lattice is divided into
blocks. A *background field* minimizes the action given the block averages, and the fluctuation
around it is integrated out. The effective action that results is kept in a fixed inductive class
of local, analytic terms. Regions where the field is not smooth (*large fields*) are handled by
separate estimates and contribute to a convergent polymer expansion. The construction runs through
about 360 pages of interlocking estimates (P1–P9 in [docs/PAPERS.md](docs/PAPERS.md)).

## The two main theorems

Both are stated in Lean in `Balaban/Frozen/Roots/`. Their statements were approved before any proof
work began and cannot be changed.

**Root-F, `Balaban.logPartition_multiscale`** (`Balaban/Frozen/Roots/LogPartitionMultiscale.lean`).
This is the renormalization-group flow in observable form (P4, P7, P9). There is δ > 0 such that,
for every decay rate κ > 0 and constant c₉ > 0, there are a block size L, a cube size M and a
threshold β₀ with the following property. For β ≥ β₀, every field strength ν ∈ (0, 1] and every
unit vector h, the logarithm of the generating function on every admissible torus is a sum of local
terms:

    log(Z(g)/Z(0)) = ⟨g, h⟩ + Σ_{j=1}^{k_f+1} Σ_x Σ_{X ∋ x} ⟨g(x), T_j(x, X; g)⟩.

The terms satisfy the following:

- T_j(x, X; ·) vanishes unless X is a connected polymer at scale j containing x.
- T_j(x, X; ·) depends only on the source g restricted to X.
- It is analytic in g on the unit ℓ¹ ball.
- It is bounded by c₉ L^{-j((d-2)/2+δ)} exp(-κ|X|/(M L^j)^d).
- It is the same on two tori of different sizes when X does not wind around either.

**Root-C, `Balaban.lowTemperature_correlations`** (`Balaban/Frozen/Roots/LowTemperatureCorrelations.lean`).
These are the low-temperature correlation functions: Theorem 1.1 of P9 (Balaban–O'Carroll) for hard
spins. For β large, the one- and two-point functions converge in infinite volume. The magnetization
is m(ν) = 1 + O(β^{-1+ρ₁}). The transverse and longitudinal two-point functions are bounded by
c (1+|x|)^{-(d-2)} e^{-c'√ν|x|}. As ν ↓ 0, the transverse part is asymptotic to
m(0)²/(βγ_∞) times the lattice Green's function, with a correction of relative order |x|^{-ρ₀}.

The model itself is a set of frozen definitions in `Balaban/Frozen/Model/`: the torus, the a-priori
measure on spins, the energy, the partition function, Gibbs expectations, and the one- and
two-point functions. A further frozen definition, `Balaban/Frozen/Geometry/IsPolymer.lean`, says
what a polymer is.

## How the development is organized

- **Frozen statements.** `frozen/manifest.json` lists the frozen declarations: eight definitions,
  all `SEALED`, and the two main theorems, both `DRAFT_SORRY`. `scripts/check_frozen_anchors.py`
  checks that their text has not changed and that nothing else depends on the placeholder proofs.
- **Proofs below the statements.** Everything else in `Balaban/` is ordinary Lean that proves
  intermediate results towards the two theorems. Each piece is a bounded target with an exact
  statement.
- **Strict hygiene.** No axioms, no unregistered `sorry`, no heartbeat overrides. Every file is a
  Lean module (`scripts/check_lean_modules.py`). Every addition is merged into `main` only after a
  full build.
- **Design and audit notes.** `notes/phase1/` holds the design notes for each part of the proof, in
  plain mathematics with references to the papers. It also holds refute-first audits that check
  landed statements against the papers. `review/` holds the per-paper reviews written before the
  formalization started, and the overall plan (`review/FORMALIZATION_ROADMAP.md`).
  `notes/phase0/` holds the drafts of the frozen statements as submitted for approval, with their
  audit. Questions about the papers, and the answers received, are in `notes/QUESTIONS-*.md` and
  `review/ROLAND_ANSWERS.md`.
- **Work log.** `orchestration/` holds the ledger of tasks and results (`LEDGER.md`), the brief
  given for each task (`briefs/`), and the handoff notes between orchestrating sessions
  (`HANDOFF.md`).
- **Paper errata.** Places where the papers are inaccurate, and how the formalization handles them,
  are recorded in `notes/ERRATA.md`.

### Repository map

| Path | Contents |
|---|---|
| `Balaban/Frozen/` | the frozen model definitions and the two main theorems |
| `Balaban/Model/` | properties of the frozen model: analyticity of the partition function, derivatives of its logarithm, symmetries, block structure of the correlation functions, the sphere measure |
| `Balaban/Provider/` | placeholder modules that will hold the proofs of the two main theorems; only the frozen theorem may import them |
| `Balaban.lean`, `Balaban/Basic.lean` | the import list of the whole library, and a placeholder root module |
| `Balaban/Lattice`, `Analysis`, `Gaussian`, `Polymer`, `Symmetry`, `External` | lattice geometry, analysis, Gaussian integrals, cluster and polymer expansions |
| `Balaban/Green/` | lattice Green's functions, random-walk expansions, decay estimates |
| `Balaban/Background/`, `Balaban/Multiscale/` | the background-field variational problem (P2) and the multiscale generating sets |
| `Balaban/Localization/` | localization expansions of background-dependent quantities (P3, P6) |
| `Balaban/SmallField/` | the inductive class of small-field effective actions (P1, P4, P5) |
| `Balaban/Fluctuation/` | one renormalization step: the fluctuation integral, its expansion and renormalization (P4–P6) |
| `Balaban/Flow/` | the renormalization-group equations for the running coefficients β_k, ν_k and their limits γ_∞, δ_∞ (P4 §5, P5) |
| `Balaban/Inhabited/` | the step at concrete parameter values, with all constants chosen |
| `Balaban/LargeField/` | large-field regions and the large-field renormalization operation (P5–P7) |
| `Balaban/Observables/`, `Balaban/Correlations/` | the observable terms and the passage to correlation functions (P8, P9) |
| `notes/`, `review/` | design notes, audits, paper reviews, errata, open questions |
| `frozen/` | the manifest of frozen declarations and the record of the author's approvals |
| `orchestration/` | the task ledger, task briefs and handoff notes |
| `scripts/` | the hygiene checks, the landing script, the progress table and the public mirror |
| `docs/` | public status pages |

## Building

The toolchain is `leanprover/lean4:v4.35.0-rc2` with the matching Mathlib release (see
`lean-toolchain` and `lakefile.lean`). With [elan](https://github.com/leanprover/elan) installed:

    lake exe cache get   # Mathlib build cache
    lake build           # more than 2,000 project modules on top of Mathlib

A full build from scratch takes several hours on a typical workstation. The only warnings expected
are the two `declaration uses 'sorry'` warnings for the main theorems. Checks:

    python3 scripts/check_lean_modules.py
    python3 scripts/check_frozen_anchors.py --root . --manifest frozen/manifest.json

## How it is being built

The formalization is directed by Scott Armstrong. Most of the Lean code and design notes are
written by AI agents (Anthropic's Claude and OpenAI's Codex models), working on bounded tasks with
exact target statements, under the rules above. The papers are the authority throughout. Every
claim of progress rests on a full Lean build of the stated theorem, not on an agent's description.
The two main theorems, and the model definitions they use, were fixed by the author before the
proof work started, so that the target could not drift towards what was easy to prove.

## Status pages

- [docs/PROGRESS.md](docs/PROGRESS.md): estimated completion, section by section, kept up to date.
- [docs/BLOCKERS.md](docs/BLOCKERS.md): the mathematical issues that currently block the proof.
- [docs/PAPERS.md](docs/PAPERS.md): Balaban's papers and the other sources used.

## Acknowledgements

The public repository [ethanwsussman/Yang--Mills-LLM-experiment](https://github.com/ethanwsussman/Yang--Mills-LLM-experiment)
contains an account of Bałaban's renormalization group for lattice Yang–Mills theory, whose papers are
the ancestors of the O(N) papers formalized here. Its reading of Bałaban's Yang–Mills large-field gas
(clusters formed after removing the retained large-field components) suggested the route we now
follow for the large-field gas ([blocker 4](docs/BLOCKERS.md)), and it informs our reading of the
torus-independence clause (blocker 7), of the first renormalization step (blocker 1), and the design
we now follow for the change of background along the flow (blocker 2). Details:
[notes/phase1/YMACCOUNT.md](notes/phase1/YMACCOUNT.md), [notes/phase1/VMOD-43.md](notes/phase1/VMOD-43.md),
[notes/phase1/Q13-YM.md](notes/phase1/Q13-YM.md).

## License

The Lean sources and documentation are released under the Apache License 2.0; see [LICENSE](LICENSE).
The papers themselves are not included (see [docs/PAPERS.md](docs/PAPERS.md)).
