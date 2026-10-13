# LFDIMOCK: Dimock's holes and blockers 3–4

**Verdict (2026-10-13). REFUTED as a direct import; OPEN as a two-part repair.** Dimock D2 supplies
an *active-root localization* and an *active-overlap gas*; D3 pays the volume of a large-field
region only after the final large-field integral. Neither paper supplies a factor for a long
**retained** O(N) hole in an individual P6 H7 coefficient or in P7's removed-component gas. A
Roland-independent route exists if the two incidence statements below can be proved for the physical
O(N) generators; this is not yet closure.

**Evidence/scope.** Read D2 `sources/Dimock-II-arXiv-1212.5562.pdf` (arXiv v2, printed pp. 20,
31–33, 45, 66–68, 91–92), D3 `sources/Dimock-III-arXiv-1304.0705.pdf` (v1, pp. 19–21, 27–32), and
the source reviews `review/papers/D2-dimock-II-large-fields.md`, `D3-dimock-III-convergence.md`.
Compare `docs/BLOCKERS.md` 3–4, `VMOD-40`–`42`, and `QUESTIONS-ROLAND-2` 14, 16. All page numbers
here are the printed arXiv page numbers. Input revision: `ddfac312c61cded624cab30eeaf9e2c9df942e50`
(D2 SHA256 `9b5216ec475c98c1`; D3 `280155600421bc18`; VMOD-41 `6bae8f02de0bc455`; VMOD-42
`83d9dd93959691f9`). Those hash prefixes identify the frozen readings, not an audit of every proof
in D2/D3.

## Refute first: what cannot pay

**REFUTED (the proposed per-hole import).** D2 (149)–(150), p. 20, requires a polymer to contain or
avoid each whole component of `Ω_k^c`. Its tree visits cubes of `X∩Ω_k`; it does not visit every
cube of a hole, but its *ordinary tree length* pays the distance between two active attachments,
including passage through a hole. This is the same relevant feature of P5 (1.34), p. 496, and
`dcovModE`; it is not a contracted-hole norm. In particular D2 (151) is rooted at an **active** cube
and does not price arbitrary choices of exits from one uncharged hole.

**REFUTED (new-seed payment for blocker 3).** D3 extracts a factor `exp[-c₂ Σ_j p²_{0,j}|C_j|]` from
violated `P_j,Q_j,R_j` tests (182)–(183), p. 27. Its geometry bounds final `Vol(Λ_k^c)` by seeded
collars, Lemma 14 (195), pp. 28–30, and only *after all fields are integrated* obtains `|K′(Θ)| ≤
λ^{n₀} exp[-κ′|Θ|_M]`, Lemma 15 (204), p. 30. Thus a long old component can be paid by its **old
history** in D3's final sum; there is no fresh per-cube factor at a seedless step. P6 (4.34), p. 34,
instead requires a bound on the new coefficient alone. P7 (3.10), p. 520, is once per **removed**
component, not per retained hole. D3 (204) cannot be inserted into either bound without a new joint
operator/coefficient invariant and a no-double-use history ledger. D3's scalar quartic/mass action
and final integration do not prove that invariant for hard spins or P5's inductive class.

**REFUTED (unrestricted gas union).** VMOD-41's two labels have bounded separate modular size,
overlap only in a retained hole of length `T`, and their union has size `Ω(T)`; two fixed
removed-component factors from P7 (3.10) cannot cover `T`. D3 can use ordinary overlap at the
*final* polymer step because its `Θ_γ` carries `exp[-κ′|Θ_γ|_M]` (212), p. 31; Lemma 16 (214)–(215),
pp. 31–32, explicitly joins boundary trees to that charged `Θ_γ` tree. This is a different estimate
from P7 (3.26)–(3.28), pp. 527–28, where the long hole is retained, not a removed object.

## Q1–Q2: what Dimock actually does

**PROVED (D2 source reading).** The nested history is `Λ₀ ⊃ Ω₁ ⊃ Λ₁ ⊃ ⋯ ⊃ Ω_k ⊃ Λ_k` with buffered
separation (144)–(148), pp. 19–20. Characteristic functions first select averaging failures `P` via
(232)–(236), pp. 32–33, then background/fluctuation failures `Q,R` via (323)–(330), pp. 44–45. The
complements grow by thickening old complements and adding neighborhoods of new failures, (234),
(328). The inductive density separates active `B(X)` with `exp[-κ d_M(X,mod Ω_k^c)]` from inactive,
component-additive `B̃`, (201), (215)–(219), pp. 28–30. D2 Remark 3 after (222), p. 31, explicitly
says the Balaban recycling `R` operation is unnecessary for this scalar model. Its `R_{k,Π}` is a
tiny remainder, not P7's `R` operation.

**PROVED (D2 source reading).** In Lemma 3.17, pp. 65–68, an old `B(X)` wholly in `Ω_{k+1}^c`
becomes inactive; otherwise (476) reblocks it, and (477)–(478) weakens fields only with a root
`Y∩Ω_{k+1}`. The new label `Z` is made by adjoining marked `Y₁` and completing hole components
(479). The decisive inequalities are (482)–(484): old modular tree controls the old **new-active**
part, while `|Ȳ₁−(Y∩Ω_{k+1})|` pays every newly marked active cube. Since completion adds only
complement cubes, `Z∩Ω_{k+1}=Z₀∩Ω_{k+1}` (485). This yields (489), the output modular bound, with no
charge for an unvisited hole interior. It uses exact alignment/support and active-root analyticity;
it does not state P6's claimed modular substitution in P3 (4.48).

**PROVED (D2 stated rule; proof sketched).** Appendix F, Theorem F.1 (633)–(636), pp. 90–91, integrates an
**ultralocal** measure on `Λ⊂Ω`. It declares two polymers linked only if `X₁∩X₂∩Ω ≠ ∅`, even if
their full labels overlap inside `Ω^c` (p. 91). The connected-cluster inequality (641) then pays at
most one cube per active link; (637)–(638) root entropy in active cubes. The factorization (643)
uses disjoint integrated `Y_i∩Λ`. A retained-hole-only overlap is not a Mayer edge in this theorem.
The theorem is for scalar ultralocal integration and assumes the activities already obey its modular
bound; it creates no hole-volume gain.

## Q3: smallest conditional O(N) change

**OPEN-3 (active-root assignment).** Reconstruct P6 (4.32)–(4.34) so every nonzero marked cover
component is rooted at `X∩Ω_{k+1}` (or pays its entire unrooted corridor), including old-wall
Green/background and `C_loc^{1/2}` rows. For each assigned `Y`, prove a D2-(482)–(485)-type
inequality `D_+(Y) ≤ L⁻¹D_-(X)+C|marks|+b_ret`, with coefficient gain `exp(-κ b_ret)`; the best case
is `b_ret=0` because completing a hole creates no additional active cover obligations. The
straddling `π′` cubes and source-tree visits in P5/P3 make this an actual proof obligation. Without
that identity, D2's argument does not repair P6; its scalar analytic domains do not establish the
background-field small-field class required for hard spins.

**OPEN-4 (conditional factorization).** Rebuild the P7 (3.26) gas conditional on retained spins and
require an exact product/factorization identity: labels meeting distinct removed components but
sharing only a retained hole must have no Mayer edge unless a physical operator interaction connects
their *active or removed-core* supports. Then use an active-overlap tree (`G3_dcov`) and charge
newly active removed cells once (`SizeModExtend`/`RExtraSize`), before the two-size gas estimate.
Shared spectator spins do not themselves prove the identity: P7's background, denominator, and
action-conversion operators must factor with the required analyticity and locality. If an
interaction survives, it needs an explicit corridor decay `exp(-κ b_ret)` from that operator.

**Change map.** Keep P5 (1.34) and landed `dcovModE`, `d7Size*`, G1/G2/G3, `SizeModExtend`, and
`R/RExtraSize.lean` as full-length geometry; do not quotient holes. Replace the *P6 (4.32)–(4.34)
localization proof/producer* by OPEN-3; replace the *P7 (3.26)–(3.28) ordinary-overlap gas producer*
by OPEN-4 and a two-size bound. `Fluctuation/SizeModUnion.lean:G3_dcov` may be invoked only for active overlap. The VMOD-42
`P6InheritedHoleAssignment` and `R/D7RetainedBridge` leaves become incidence-or-paid-corridor
alternatives; `P5FineRealization` remains necessary to compare P5's continuous tree with `d7Size`.
If OPEN-4 fails, a D3-like joint H7/operator norm with a reserve per retained history component
would replace P5 H7's coefficient clause (1.38)–(1.39), and require new P6/P7 producers and a
history-spend invariant. D3 proves none of that for O(N).

## Q4: ordered work and risk

**OPEN route independent of Roland's answers 14/16.** (1) Audit P6's actual interpolation reads and
prove/deny active rooting for both background and covariance square root; then prove OPEN-3 or
exhibit its residual payment. (2) Audit the physical P7 ratio/operator generator conditional on
retained spins; prove/deny the factorization identity. (3) If true, prove active-overlap G3 and
exact halos, apply landed `R/D7GasRootEntropy.lean` to the physical labels, and extend size with one
charge. (4) Prove the absolute two-size gas bound, its `p₂` reserve, and post-H7 transport;
separately establish `P5FineRealization`. (5) If (1) or (2) fails, seek a physical corridor estimate
or design and fund the joint norm before Lean work. The highest risk is the **physical
incidence/factorization** at (1)–(2), not the landed geometric inequalities. No D2/D3 result
licenses closing either blocker now, but Roland's reply is not logically required to test this
route.
