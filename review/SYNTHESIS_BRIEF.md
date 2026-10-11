# Synthesis brief: Balaban's 3d Heisenberg theory — big picture and formalization roadmap

## Context

Scott Armstrong (the author/orchestrator of this project) has been asked by
Roland to formalize in Lean 4 "Balaban's theory for the Heisenberg model".
Roland's words, verbatim:

> "Balaban applied his method to YM3, YM4 and Heisenberg. 3d Heisenberg was
> last. I think these papers are probably the best written. We should try to
> lean formalize it."

Roland supplied the ten papers in `/home/scott/Balaban/sources/` as
"Balaban's work on Heisenberg". They are mapped to keys P0–P9 in
`/home/scott/Balaban/review/SOURCES.md`. Ten independent readers (one per
paper) have written detailed reviews in
`/home/scott/Balaban/review/papers/P*.md`, following
`/home/scott/Balaban/review/READER_BRIEF.md`.

Your job: produce two separate documents.

1. `/home/scott/Balaban/review/BIG_PICTURE.md` — write this FIRST.
2. `/home/scott/Balaban/review/FORMALIZATION_ROADMAP.md` — write this second,
   building on the first.

## Inputs and how to use them

- Read SOURCES.md, READER_BRIEF.md, QC_LOG.md and all ten reviews in full.
  QC_LOG.md records the orchestrator's spot-checks against the PDFs, known
  printing errors in the bibliographies, a warning that the inductive
  hypotheses are numbered differently in P1 ((H.1)–(H.9)) and in P0/P4/P5
  ((H.1)–(H.7)) — build a concordance table — and the external sources
  identified so far. Note also that P8 is about the 2d Gross–Neveu model,
  not O(N).
- The reviews were written by readers who each saw only one paper. They may
  disagree with each other, miss cross-paper connections, or contain errors.
  Reconcile them. For anything load-bearing — the main theorems, the
  inductive hypotheses, the statement of each paper's output that another
  paper consumes, the parameter hierarchy — go back to the PDF and check
  (Read tool on the PDF with `pages`, at most 20 pages per call; the
  1995–96 scans P0–P4 have garbled OCR, so read page images). Record in each
  document a short list of places where you corrected or could not confirm a
  reviewer's claim.
- Where the reviews flag weak spots, decide whether they are real gaps in
  Balaban's argument, deferred steps that are carried out elsewhere in the
  bundle, or reviewer confusion. Check the PDFs when it matters.
- Use the bundle keys P0–P9 throughout, with result/equation/page numbers.

## Document 1: BIG_PICTURE.md

A mathematically serious account, for a reader who knows constructive QFT /
probability but has not read Balaban. Cover at least:

1. **The model and the main theorems.** The lattice O(N) model, the
   low-temperature regime, what exactly is proved at the end of the series
   (state the final theorems precisely, with all quantifiers), and what is
   general (N >= 2, d >= 3) versus specific to Heisenberg (N = 3, d = 3).
2. **The strategy in order.** Block averaging and the renormalization
   transformations; how the spherical constraint is handled; background
   configurations from the variational problems; fluctuation fields and
   fluctuation integrals; small-field / large-field decomposition;
   localization (polymer) expansions; analyticity domains and norms; the
   inductive hypotheses and how one RG step preserves them; the RG equations
   for the effective couplings; the large-field renormalization operation;
   the passage to correlation functions. Explain the mechanism and the key
   estimates, not just the vocabulary.
3. **How the ten papers fit together.** A dependency diagram (Mermaid or
   ASCII) at the level of papers and, for the core, at the level of main
   results; for each paper one paragraph on what it supplies and to whom.
4. **The parameter hierarchy.** All the constants, the order of choice, and
   the constraints.
5. **Prerequisites outside the bundle.** Which external papers the series
   genuinely depends on (e.g. Balaban's earlier gauge-theory papers on
   propagators, random-walk expansions, averaging operations; cluster
   expansion results), with full references and what is used from each.
   Flag which ones we would need to obtain and study.
6. **Context.** Briefly: how this compares with the Fröhlich–Simon–Spencer
   infrared-bound proof of long-range order (what Balaban gives that FSS
   does not), and with modern RG approaches (e.g. Bauerschmidt–Brydges–Slade)
   — only as far as it helps the formalization decision.
7. **Corrections/unconfirmed claims** relative to the reviews.

## Document 2: FORMALIZATION_ROADMAP.md

1. **What does Roland really want?** Interpret the request. Note that
   long-range order for the 3d Heisenberg model already has a much shorter
   proof (Fröhlich–Simon–Spencer infrared bounds, reflection positivity), so
   the interest is presumably in Balaban's multiscale RG method itself
   (Roland mentions YM3/YM4, where the method is the only route). Say what
   this implies for the choice of headline theorem.
2. **Scope options**, as tiers, each with the precise mathematical statement
   that would be the Lean headline theorem, what it requires, rough size and
   risk:
   (A) the correlation-function theorems of P9 (full endpoint);
   (B) the complete RG flow: all inductive hypotheses hold at every scale,
       uniformly in volume (P1–P7, main theorems as formulated in P5);
   (C) one RG step / the small-field analysis;
   (D) self-contained components or warm-ups (e.g. the variational problems
       of P2, the method of P8, propagator / random-walk-expansion bounds).
   Also consider restricting to d = 3, N = 3 versus keeping N >= 2, d >= 3,
   and finite volume with uniform bounds versus infinite volume.
   Give a recommendation and justify it.
3. **Candidate frozen surface.** Scott's campaign method freezes a small set
   (~20) of author-approved Lean statements: the root theorem(s) plus the
   major interfaces; everything else is an editable target. Propose, in
   mathematical (not Lean) form, the roots and the major interfaces for the
   recommended scope.
4. **Component dependency graph** of the formalization (modules / layers),
   from basic infrastructure up to the roots.
5. **Infrastructure.** What Mathlib provides and what it lacks for this
   (Gaussian measures on finite-dimensional spaces, lattice Laplacians and
   Green's functions, analytic functions of several complex variables and
   Cauchy estimates, polymer/cluster expansions, etc.). Then survey Scott's
   own Lean repos for reusable infrastructure BEFORE declaring anything
   missing — in particular:
   - `/home/scott/FroehlichSpencer` (FS83 Anderson multiscale analysis; BKT
     and FS81/FS82 campaigns: lattice Gaussian free field, spin waves,
     Villain models, Kotecký–Preiss / polymer expansions, Wilson/ℤ_N/XY;
     see `docs/*.md` and `FroehlichSpencer/Infra`, `FroehlichSpencer/BKT`),
   - `/home/scott/CoarseGraining`, `/home/scott/EllipticRegularity`,
     `/home/scott/CoarseDeGiorgi`, `/home/scott/MarkovProcess`,
     `/home/scott/homogenisation_for_field_theories`, `/home/scott/KPZ`,
     and anything else under `/home/scott` that looks relevant.
   Read READMEs/docs and grep the Lean sources; do not build anything.
   Report concrete reusable files/declarations by path.
6. **Phasing and milestones**, with early wins that de-risk the campaign.
7. **Size estimate** (pages of source per tier, rough Lean line counts by
   analogy with Scott's completed campaigns — e.g. FroehlichSpencer,
   CoarseGraining — if you can find their sizes) and **risk register**:
   places where Balaban's proofs are sketchy, "analogous to", deferred, or
   depend on external papers; places where formalization will be
   disproportionately expensive (e.g. heavy combinatorics of large-field
   domains, analyticity bookkeeping).
8. **Missing sources** to obtain before starting.
9. **Questions for Roland** — a short, sharp list whose answers would change
   the plan.

For background on Scott's methodology you may read the skill files in
`/home/scott/.claude/skills/` — especially `lean-project-architecture`,
`lean-orchestrator`, `build-proof-dependency-graph` and `lean-learnings`
(each has a SKILL.md). Align the roadmap with them.

## Rules

- Write only the two output files. Do not modify the reviews, the sources,
  or any other repository. Do not run Lean or builds; reading and grepping
  is fine.
- Plain mathematical prose; precise statements in LaTeX; page/result
  references for every claim about the papers. No marketing language, and
  avoid words like "calibration", "robust", "leverage", "crucially".
- When done, reply with: the two paths, the recommended scope in two
  sentences, the headline theorem(s) in one line each, the top five risks,
  and the questions for Roland.
