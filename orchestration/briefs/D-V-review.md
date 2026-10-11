# Brief D-V-review — refute-first review of `notes/phase1/BACKGROUND.md`

You are an independent referee for the background-field document of the Lean formalization of
Balaban's RG analysis of the low-temperature O(N) model (hard spins, λ = ∞). Repository
/home/scott/Balaban (read AGENTS.md first). You write a review; you do not write Lean.
**Do not launch subagents (no Agent tool); work directly.**

## Material
- `notes/phase1/BACKGROUND.md` (the document under review; brief `orchestration/briefs/D-V-background-fields.md`).
- P2 = CMP 175 (1996), `sources/BF02099510.pdf` (a scan: read page images; PDF page = journal
  page − 606); review `review/papers/P2-*.md`; `notes/ERRATA.md` (P2 rows); roadmap
  `review/FORMALIZATION_ROADMAP.md` §3.3 (I-1, I-2, Def-5); `notes/phase1/GREEN.md` (§2 C1–C3,
  G-2(iv), (v), (v′)).
- Landed Lean statements the proofs claim to use (read statements only):
  `Balaban.Multiscale.global_bound` (G-2(iv) without Hölder), `Balaban.Multiscale.constrained_sup`
  (G-2(v′)), `Balaban.Multiscale.prop48`, `prop49`, `Balaban/Background/ConstantConfig*.lean`,
  `Balaban.Analysis.exists_analytic_fixedPoint`.

## What to check (try to refute)
1. **Prop 5.1** (the perturbed system, "proved"): the contraction, the exact Leibniz identity, every
   norm inequality, the constants; that the norms used are exactly those of the landed
   `global_bound`/`constrained_sup` (sup norms `|·|₀, |∂·|₁, |·|₂`, constants depending on `d, L, N`).
2. **Theorem 5.2 / Lemma 5.3**: the approximate solution and its residual (sketched — is the sketch
   complete enough to formalize? which estimate is the weakest?); the minimiser identity
   $A(\sigma)-A(\phi_*)=\frac12\langle\sigma-\phi_*,H_D(\alpha_*)(\sigma-\phi_*)\rangle$ on the sphere and the
   positivity it needs (for real data, is $H_D(\alpha_*)$ positive on the relevant space?);
   uniqueness among solutions with $|\alpha|_2<c_0$.
3. **I-2 (Theorem 6.1, Prop 6.4)**: the formula (6.2), the composition identities, the domain
   membership (Lemmas 6.2/6.3), the claimed correction of P2 (4.24)–(4.28) ($C_4$ depending on $L$).
4. **Def-5 (§7)**: are the `∃!` theorems and characterization theorems stated so that they can be
   written as exact Lean declarations (carriers, data domain, quantifier order)? Is the data domain
   (§1.3) a faithful translation of P2 (1.11)–(1.12) at λ = ∞ (the author's question 1)? Is anything
   a proof step disguised as a hypothesis?
5. The document's claims about errors (the P2 review's extra factor in (1.15); P2 (4.24)–(4.28)):
   check against the page images.
6. The questions of §10: give your answer to each where the sources decide it.

## Deliverable
Write `notes/phase1/BACKGROUND-review.md`: findings numbered V-01, … with severity (BLOCKER /
MAJOR / MINOR), location, argument, proposed fix; answers to §10; overall verdict (APPROVE /
APPROVE-WITH-CHANGES / CHANGES-REQUIRED). Plain mathematical prose; exact page/equation references;
avoid "calibration", "robust", "leverage", "crucially". Write only that file (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/bgr/ allowed); do not commit; do not run Lean.
Reply with the verdict and the findings (one line each).
