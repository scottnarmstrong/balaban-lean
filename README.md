# Balaban's low-temperature renormalization group for O(N) spin models, in Lean 4

This repository is a formalization in progress, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of Tadeusz Balaban's
renormalization-group analysis of the classical O(N) spin model at low temperature. The papers it
follows were published in 1995–1999, the last two with Michael O'Carroll; [docs/PAPERS.md](docs/PAPERS.md)
lists them.

**Status: unfinished.** The two main theorems are stated in Lean and frozen, but neither is proved.
As of October 2026, more than 650,000 lines of Lean (about 520,000 without comments and blank
lines) have been written towards them. The project contains no axioms and no `sorry` other than the
two registered placeholders for the main theorems themselves. See
[docs/PROGRESS.md](docs/PROGRESS.md) for the current size of each part and an estimate of how far it
has come, and [docs/BLOCKERS.md](docs/BLOCKERS.md) for the mathematical questions that currently
block it.

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

## License

The Lean sources and documentation are released under the Apache License 2.0; see [LICENSE](LICENSE).
The papers themselves are not included (see [docs/PAPERS.md](docs/PAPERS.md)).
