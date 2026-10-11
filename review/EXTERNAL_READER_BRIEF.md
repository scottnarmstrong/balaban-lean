# Reader brief for external sources (E- and D-keys)

Read `READER_BRIEF.md` first: its reading method, standards and output template
apply unchanged, with the additions below. Then read `SOURCES.md` (both tables:
the bundle P0–P9 and the external sources E1–E10, D1–D3), `BIG_PICTURE.md` §§1–5
(the big picture of the O(N) series, already written), and `ROLAND_ANSWERS.md`.

## Context

The project formalizes in Lean 4 Balaban's renormalization-group theory of the
low-temperature classical O(N) / Heisenberg model (bundle P0–P9). The paper you
are reviewing is outside the bundle. It is either one of Balaban's earlier papers
(on Higgs or lattice gauge theories) that the bundle cites for essential inputs,
a cited cluster-expansion paper, or J. Dimock's later exposition of Balaban's
method for the φ⁴₃ model. Roland (who requested the formalization) has said:
large fields are essential ("the crux of the matter"); hard spins (λ = ∞) with
general d ≥ 3, N ≥ 2 are fine; finite volume on tori with uniform bounds is fine;
and **different proofs of the Green's function estimates are fine, in fact
encouraged** ("he probably proved [them] in a strange way").

## Additions to the template

Keep sections 0–8 of the READER_BRIEF template. In section 0, state which bundle
papers cite this paper and for what (use `SOURCES.md`, and grep
`/home/scott/Balaban/review/papers/P*.md` and `BIG_PICTURE.md` for its volume
number, e.g. "CMP 96", "96, 223", "[2b]", "[6d]"). Add two sections:

```
## 9. What the O(N) series uses from this paper
For each place where P0–P9 cite this paper: the exact item cited (section,
proposition, equation number), its precise statement here (LaTeX), its
hypotheses, and whether it applies as stated to the scalar O(N) setting of the
bundle or needs adaptation (gauge fields → scalar fields, covariant Laplacian →
ordinary lattice Laplacian with block-averaging terms Q*aQ, Higgs → O(N), etc.).
Say what the adaptation would involve. If the bundle cites an item that you
cannot find here, say so explicitly — this matters for settling defective
citations.

## 10. Relevance to the formalization
What this paper contributes to a Lean formalization of the O(N) series (with
large fields in scope): which statements would become interfaces, which
arguments are reusable, which are gauge-specific and irrelevant. For Green's
function / propagator results, note whether a different, more standard proof
of the needed bound looks available (e.g. Combes–Thomas, Neumann series with
block decomposition, discrete elliptic regularity) — flag this as a suggestion,
not a claim.
```

Output path: given in your task. Work only in
`/home/scott/Balaban/review/papers/`; write only your own file.
