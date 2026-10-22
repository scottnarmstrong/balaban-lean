# Balaban's low-temperature renormalization group for O(N) spin models, in Lean 4

This repository is a formalization in progress, in [Lean 4](https://lean-lang.org/) with
[Mathlib](https://github.com/leanprover-community/mathlib4), of Tadeusz Balaban's
renormalization-group analysis of the classical O(N) spin model at low temperature. The papers it
follows were published in 1995–1999, the last two with Michael O'Carroll; [docs/PAPERS.md](docs/PAPERS.md)
lists them.

**Status: unfinished.** The two main theorems are stated in Lean and frozen, but neither is proved.
As of October 2026, about 1,068,000 lines of Lean (about 846,000 without comments and blank
lines) have been written towards them. The project contains no axioms and no `sorry` other than the
two registered placeholders for the main theorems themselves. See
[docs/PROGRESS.md](docs/PROGRESS.md) for the current size of each part and an estimate of how far it
has come, and [docs/BLOCKERS.md](docs/BLOCKERS.md) for the mathematical questions that currently
block it.

## Where the work stands

Balaban's argument has two parts. The first treats one renormalization step in the regions where the
spin field is smooth: it computes the effective action at the next scale and shows that it has the same
form as at the previous one. This part is largely formalized. The second part treats the rare regions
where the field is not smooth (*large fields*), and then combines all the scales into the two main
theorems. Most of the remaining work is in this second part.

The first main theorem has already been reduced, by a complete Lean proof, to seven intermediate
results, each of them a theorem of the papers. What is left is to prove those seven results.

In seven places the papers, as written, do not give what the next step of the argument needs: either a
step is stated without a proof that we could reconstruct, or an estimate is weaker than the one used
later. [docs/BLOCKERS.md](docs/BLOCKERS.md) describes these seven *blockers* and names, for each, the
Lean statement that closes it.
The second blocker no longer exists: a change to the definitions approved by the author on 21 October asks the
large-field boundary terms to be analytic and bounded only at the physical external field, and the whole project
builds without the statement the blocker concerned, which has been removed. (The estimate it asked for is not
proved; in the form first stated it is false.) The other six are open. Two of their closing
statements are proved: the case of the flow with no renormalization step (part of the first blocker) and the
bound on the vacuum energy of a step (part of the fourth).

How far each one is under control, as of the morning of 22 October (details in [docs/BLOCKERS.md](docs/BLOCKERS.md)).
No blocker is stuck: each has a proof route that we are carrying out. Several turned out to need more work than
estimated, mostly because the Lean transcription of a definition differed from what the papers print; each such
case was corrected by a change approved by the author (R12–R29; R27 was withdrawn as not needed). For blockers 1, 3,
4 and the first half of 5, the final assembly is now proved as a theorem from a fixed list of named remaining pieces,
so what is left is exactly that list (sizes below).

| Blocker | Grade | In one line |
|---|---|---|
| 1. The first renormalization step | route clear, substantial work left | final assembly proved from 21 named pieces and the first-step map; about 19,000 lines remain, none an open question |
| 2. Switching backgrounds | resolved | removed by an approved change to the definitions |
| 3. Old boundary terms across a new hole | route clear, substantial work left | final assembly proved; the data estimate proved; about 9,400 lines remain (the region form of P5 Lemma 2.1 and the old-part identity) |
| 4. The small factor of removed large-field regions | route clear, substantial work left | final assembly proved from three constructions and seven named conditions; the constructions are defined and checked against P7; about 5,000–7,500 lines remain |
| 5. The last integral | route clear, substantial work left | small-field half: assembly proved, two design points settled, about 3,000 lines remain; large-field half: about fourteen pieces remain |
| 6. The new level's terms on local generating sets | route clear, substantial work left | the step chain is done; the step map, the local families of the new level, the new source terms and the torus independence remain |
| 7. Exact agreement on two tori | route clear at each step, open at the last scale | the cell term and the step's coefficient agree on two tori; the class's torus independence and the last scale remain |

Changes to approved definitions are made only with the author's approval; each is recorded in `AGENTS.md`.
Where the papers can be read in more than one way, we choose a reading, record the choice, and prove
everything it requires ([notes/phase1/PLAN-B.md](notes/phase1/PLAN-B.md)).
[docs/PROGRESS.md](docs/PROGRESS.md) estimates how far each part has come, with a dated log.

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
    lake build           # about 3,200 project modules on top of Mathlib

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
