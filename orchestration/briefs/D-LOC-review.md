# Brief D-LOC-review — refute-first review of `notes/phase1/LOCALIZATION.md`

You are an independent referee for the localization document of the Lean formalization of Balaban's
RG analysis of the low-temperature O(N) model (hard spins, λ = ∞). Repository /home/scott/Balaban
(read AGENTS.md first). You write a review; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Material
`notes/phase1/LOCALIZATION.md` (brief `orchestration/briefs/D-LOC-localization.md`); P3 = CMP 182
(1996) 33–82 (`sources/BF02506385.pdf`; text layer plus page images); D1 (Dimock I, `review/papers/D1-*`
and the source in `sources/`), P5–P7, P9 as needed; `review/papers/P3-localization-I.md`;
`notes/ERRATA.md` (ER-042–057); `notes/phase1/GREEN.md` (§3 G-3, Options A/B, Q2),
`BACKGROUND.md` v2, `SMALLFIELD.md`, `POLYMER.md`; landed Lean statements in
`Balaban/Multiscale/*` (constrained operator, `constrained_locality_block`, `global_g2iv`) and
`Balaban/Background/*` (`prop51_exists_unique`, `Prop51Hyp`).

## What to check (try to refute)
1. **The Option A decision**: is the argument that Option B cannot give an exactly local analytic
   family on a polydisc of radius e^{κ₁} correct? Is there a cheaper route the document missed
   (e.g. interpolation in s of the data rather than of the operator)?
2. **The simplified expansion**: the one-sided Schwarz parametrix and multiplicative walk weights;
   does the claimed convergence hold, and is the cost M₁ ≥ c e^{N₀κ₁} acceptable for the constant
   chain (the document found no upper bound on M₁ or M in P3, P5–P7: check LF-ARCHITECTURE.md v4 §5
   and P5–P7 for any constraint on M)?
3. **NC** (interior bounds of the Neumann cube operator): is the statement right and sufficient,
   and is the claim that boundary regularity is not needed correct?
4. **I-4a/b/c and I-5**: statements precise enough to freeze or to be internal lemmas; proofs marked
   complete — check the main estimates; the exponent bookkeeping κ₀ ≤ κ/3 − 1 and 2κ; the domain
   lemma and the spaces Ξ^c_j.
5. Requirements R-B1, R-B2 on the background-field layer: are they needed, and what exactly must
   change in the landed `prop51_exists_unique` (an abstract Green family; two constraint modes)?
6. Errata candidates N-1 … N-8; the dropped claim δα_k(s) = 0 on zero cubes (question 4).
7. The size estimate (18k–29k Lean lines).

## Deliverable
Write `notes/phase1/LOCALIZATION-review.md`: findings L-01, … with severity (BLOCKER / MAJOR /
MINOR), location, argument, proposed fix; answers to the document's questions where the sources
decide them; overall verdict (APPROVE / APPROVE-WITH-CHANGES / CHANGES-REQUIRED). Plain mathematical
prose; exact page/equation references; avoid "calibration", "robust", "leverage", "crucially".
Write only that file (scratch under /tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/locr/ allowed); do not commit;
do not run Lean. Reply with the verdict and the findings (one line each).
