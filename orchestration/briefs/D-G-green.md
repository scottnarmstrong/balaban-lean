# Brief D-G — the Green's function document (`notes/phase1/GREEN.md`)

You are an analyst writing a phase-1 document of a Lean 4 formalization of Balaban's
renormalization-group analysis of the low-temperature classical O(N) model (hard spins, d ≥ 3,
N ≥ 2). Repository: /home/scott/Balaban (read AGENTS.md first). You write mathematics on paper; you
do not write or run Lean. **Do not launch subagents (no Agent tool); work directly.**

## Context

Balaban's series consumes many Green's function bounds for multiscale elliptic operators (P2, P3,
P4, P6, P7, P9), proved in his earlier papers (E3 = CMP 89, E4/E5 = CMP 95/96) by random-walk
expansions. The review found that E3 and E5 do not cover the operator the series uses (Dirichlet
conditions, mass ν, complex potential α, general multiscale coefficient a on a generating set).
Roland Bauerschmidt ruled (2026-10-11): **our own proofs of the Green's function estimates are
fine, in fact encouraged**. Hard spins only (λ = ∞), which removes some bounds (roadmap §3.4 table
column "At λ = ∞").

Read: `review/FORMALIZATION_ROADMAP.md` §3.4 (the interface G-1..G-6, the table C1–C14 of what the
series consumes, and the proposed proof routes), §7 (infrastructure; Scott's repositories, in
particular `/home/scott/mining/Frohlich-Spencer/FroehlichSpencer/Infra/Green/CombesThomas.lean`, the
continuum Agmon template under `/home/scott/Superdiffusion*`, and
`/home/scott/CoarseGraining/Homogenization/Sobolev/Foundations/DifferenceQuotient.lean`); the
reviews `review/papers/P2-*.md`, `P3-*.md`, `E3-*.md`, `E4-*.md`, `E5-*.md`, `D1-*.md` (Dimock's
Lemma 30 is a quadratic-form Combes–Thomas argument); `notes/ERRATA.md` rows for P2, P3, E3, E5.
Check every consumed bound against the PDFs in `sources/` (map `review/SOURCES.md`; Read tool
with `pages`, ≤ 20 pages per call; P1–P4 and E-papers are scans — read page images; text
extractions of several papers already exist in
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/green/ from an earlier attempt and may be reused).

## Task: write `/home/scott/Balaban/notes/phase1/GREEN.md`

This document will be the source from which the Green's function interfaces are frozen and their
Lean proofs written. Sections:

1. **Setting and definitions.** The lattices (torus and ℤ^d, scaled lattices T_η, unit lattices
   T_1^{(k)}), block averaging Q_k, Q_k^*, the multiscale generating sets 𝔹_k and regions
   Ω_1 ⊃ … ⊃ Ω_k (P2 (1.1)–(1.3)), the multiscale spacing ℓ(x), the operators
   H_D(α) = −Δ^η_D + (Q^*aQ)_D + ν + α on the domains 𝒟 (Dirichlet on Ω_1; cubes with Neumann
   faces, P3 (2.3)), the x-variant G_{k,x} (P3 (3.8)), the unit-lattice operators
   Δ^{(k)} = a_k − a_k²Q_kG_k(0)Q_k^*, and the norms used. Fix all normalizations and say where
   Balaban's conventions differ.
2. **What is consumed, precisely.** For each item C1–C14 of roadmap §3.4 (and any missing), the
   exact inequality as used, the page, the parameters it must be uniform in, and whether it
   survives at λ = ∞. Correct the roadmap's table where it is wrong.
3. **The interface statements G-1..G-6**, each a precise theorem with hypotheses, quantifiers and
   the dependence of constants (only on d, L and fixed exponents — never on k, η, the volume, M,
   the generating set, or x).
4. **Proofs.** Complete proofs, paper style, every inequality written out, of: G-1 (coercivity:
   Neumann bracketing, block Poincaré, the Schur-complement form of Δ^{(k)}); G-2 step 1 (L² decay
   by a quadratic-form Agmon/Combes–Thomas argument with a multiscale path metric, complex α) and
   step 2 (scale mismatch); G-4 (unit-lattice operators: operator-norm Combes–Thomas and the
   geometric resolvent identity; say exactly how FroehlichSpencer's `combesThomas_core` must be
   generalized); G-6 (the exact identities). For G-2 step 3 (pointwise, gradient and Hölder bounds
   by discrete elliptic regularity at scale ℓ_j) give a detailed plan: the lemmas in order, each
   with statement and proof sketch, and the cheapest route that gives exactly what is consumed
   (check whether the Hölder bound is consumed at λ = ∞, and with which exponent). For G-3 (the
   random-walk representation) decide whether any consumer needs it given G-2.
5. **Size estimate and risks** for the Lean formalization of each piece.
6. **Questions**, if any.

Standards: exact page/equation references; distinguish what you prove from what you cite; mark
doubts "UNCERTAIN:". Plain mathematical prose; no marketing words; avoid "calibration", "robust",
"leverage", "crucially". LaTeX in $...$. Expect 8,000–15,000 words; write the file section by
section as you go (so partial work survives), finishing §§1–3 before §§4–6.

Rules: write only `/home/scott/Balaban/notes/phase1/GREEN.md` (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/green/ allowed). Read other repositories read-only. Do not
edit any other file, do not commit, do not run Lean or lake. When done, reply with: the list of
interface statements (one line each), which proofs are complete in the document, the main risk,
and any questions.
