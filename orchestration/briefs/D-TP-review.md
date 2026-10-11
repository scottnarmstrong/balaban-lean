# Brief D-TP-review — refute-first review of `notes/phase1/OBSERVABLES.md`

You are an independent referee (Lean formalization of Balaban's RG analysis of the low-temperature
O(N) model, hard spins). Repository /home/scott/Balaban (read AGENTS.md first). You write a review;
you do not write Lean. **Do not launch subagents (no Agent tool); work directly.**

## Material
`notes/phase1/OBSERVABLES.md` (brief `orchestration/briefs/D-TP-observables.md`); P9 = CMP 199
(1999) 493–520 (`sources/s002200050510.pdf`), P1, P4–P7 as needed (`review/SOURCES.md`); the
landed Lean statements `Balaban/Correlations/C1Star.lean` (`C1Star`, `C1StarF1`–`F3`,
`RootFAndC1Star`), `Assembly.lean`, `BoundsNu.lean`, `ZeroLimit.lean`, `RootCFromFlow.lean`, and the
frozen Root-F/Root-C statements `Balaban/Frozen/Roots/*.lean` (read only); `CORRELATIONS.md`
§§2–3, `SMALLFIELD.md` v2 (§3.5, §6), `LF-ARCHITECTURE.md` v4, `POLYMER.md` (PE-M).

## What to check (try to refute)
1. **F-A** (the document says `C1Star`'s field `J` must move after β because the flow's last scale
   depends on β): is that true? Root-F's frozen `kf` is determined by `L^kf √ν ≤ L`,
   `1/2 ≤ L^{kf+1}√ν` (no β). Which last scale does the derivation of C-1* actually use, and does it
   depend on β (e.g. through k₀ = the P4 §6 threshold β_kν_k ≤ 1)? Decide whether F-A is needed.
2. **F-B** (the `C1StarF3` remainder bound `c_*(1+|x−y|)^{−(d−2+ρ₀)} e^{−c′√ν|x−y|}` is false because
   the last Gaussian term has size β⁻¹L^{−J(d−2)} ≈ β⁻¹ν^{(d−2)/2} in the window
   `L^{J(d−2)/(d−2+ρ₀)} ≪ |z| ≪ L^J`): verify; check the proposed fix (add a `ν^{(d−2)/2}` term) and
   that Root-C's frozen bounds still follow (which constant changes).
3. Lemma 2.1 (the exact Gaussian kernel at ψ ≡ h, longitudinal part 0), Lemma 4.2 (mass
   reconciliation in the ν-free regime), the exponent recomputations, the five LF-4 requirements,
   the β-dependence answer (§6).
4. Questions 2–3 of §7.6 (addressed to "seaturtle2" by mistake; answer them from P9/P4 yourself):
   is the final covariance massive or regular, does F_{k+1} contain the tail term; are the Gaussian
   kernels massless or massive for j ≤ k₀?
5. The main risk (P9 (3.13) on subdomains; product-measure hypothesis of PE-M for the non-product
   Gaussian measure).

## Deliverable
Write `notes/phase1/OBSERVABLES-review.md`: findings O-01, … (BLOCKER / MAJOR / MINOR), location,
argument, fix; explicit verdicts on F-A and F-B with the exact Lean change if needed; answers to
§7.6 questions 2–3; overall verdict. Plain mathematical prose; exact references; avoid
"calibration", "robust", "leverage", "crucially". Write only that file (scratch under
/tmp/claude-1004/-home-scott/11eef0d0-febc-449e-a360-14f8cd69b1e5/scratchpad/obsr/ allowed); do not commit; do not run Lean. Reply with the verdict,
F-A/F-B verdicts and the findings (one line each).
