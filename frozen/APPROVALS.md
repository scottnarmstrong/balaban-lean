# Author approvals and rulings

Each entry records the date, the approver, the exact package approved (path and sha256), and the
rulings it contains. Frozen files and manifest entries cite these entries by anchor.

## surface-v1

**2026-10-11, Scott Armstrong: "approve all defaults".**

Package: `notes/phase0/surface-v1-for-approval.md` v1.2, sha256
`a4a9f045310c56eb7b85df172abc80d7c37d02830be8414a34a99ec897a08f08` (git `d66ce10`). Approved as
written: the ten files of its §1–§2 (sha256 as listed there), with every decision at its
recommended default. Audit record: `notes/phase0/surface-v1-audit.md` (audit of v1.0 and re-audit
of v1.1).

Rulings (the recommended defaults of the package, now author rulings):

- **S0-Q01 (roots).** Root-F `Balaban.logPartition_multiscale` (main deliverable) and Root-C
  `Balaban.lowTemperature_correlations` (final deliverable). P7 Thm 5 stays an interface (LF-7),
  frozen only after the phase-1 large-field reconstruction.
- **S0-Q02 (tori).** Cubic tori `(ℤ/ℓℤ)^d` of every side; Root-F on sides divisible by
  `M L^{k_f+1}`; Root-C's limits along sides divisible by `q^n`, `q ≥ 2` fixed with the constants.
- **S0-Q03 (polymers).** Nearest-neighbour connected unions of blocks of side `M L^j`; size =
  number of blocks; decay `e^{−κ·size}` in place of P1's tree length.
- **S0-Q04 (content of Root-F).** Identity, locality, analyticity, bounds, independence of the
  torus on non-winding polymers (box `|y_μ| < min(ℓ, ℓ')/4`); no covariance clauses; top-scale
  pieces folded into scale `k_f + 1`.
- **S0-Q05 (constants of Root-F).** `∃δ > 0, ∀κ > 0, ∀c₉ > 0, ∃L ≥ 2, M ≥ 1, β₀, …, ∃k_f` with
  `L^{k_f}√ν ≤ L` and `1/2 ≤ L^{k_f+1}√ν`.
- **S0-Q06 (source domain).** Analyticity and identity on `∑_x∑_i|g_i(x)| < 1`; bounds on `≤ 1/2`.
- **S0-Q07 (constants of Root-C).** `β₀, c, c', ρ₀, ρ₁, q` before `β`; `0 < ρ₁ < 1`; `m, G_tr, G_lg`
  after `β`, before `h`. Subject to Roland's answer to question 6.
- **S0-Q08 (infinite-volume objects).** Existentials inside Root-C; the Green's function
  characterized by `−ΔG = δ₀`, `G → 0`. The thermodynamic and `ν ↓ 0` limits are reconstruction
  items.
- **S0-Q09 (model conventions).** As in the package (P9 (1.1) at `λ = ∞`, unnormalized surface
  measure, bilinear complex source, sup norm on `ℤ^d`, `(1 + |x|)` in the decay bounds).
- **S0-Q10 (freeze procedure).** One stage: eight definitions `SEALED`, two roots `DRAFT_SORRY`.
- **m1–m4** as in the package (names and paths; `hd`, `hN` kept; side-2 tori; the regime
  `ν > (7/8)L^{−2}` added to the reconstruction list).

Freeze (orchestrator, 2026-10-11): the eight definition files are byte-identical to the package.
Following the freeze procedure of the package (§5) and the FroehlichSpencer precedent, the two root
files gained only the private provider import (`import Balaban.Provider.<Root>`) and the
`FROZEN_ANCHOR_*` marker comments around the unchanged statement and its `by sorry` body. The
provider modules `Balaban/Provider/{LogPartitionMultiscale,LowTemperatureCorrelations}.lean` are
empty placeholders, quarantined until their anchors are sealed.

## LF rulings 1–2 (2026-10-11)

Author (Scott Armstrong), 2026-10-11: "Approve large-field rulings." This approves rulings 1 and 2 of
`notes/phase1/LF-ARCHITECTURE.md` v4 §7: (1) the reconstructed bookkeeping (A′) — budget invariant
(H6′) with spines, clocks and pre-window/pending/active window states; ripeness of covered windows
with merge strips as the trigger of R; R on windows of up to ν_max merged pieces; components by
"distance < ω_k cubes" — for Def-7, LF-2 and LF-4; (2) the Def-7 design — `IsRep_k` predicate on
representations, deterministic bookkeeping on the a-priori sequence λ̂, (D5) at every scale j ≤ k,
LF-4 existential. These are design rulings for reconstructed interfaces (roadmap §3.5); no
declaration is frozen by them. The exact Lean statements of Def-7 and LF-4 will be submitted for
approval separately when the reconstruction document Parts I–III are approved.
