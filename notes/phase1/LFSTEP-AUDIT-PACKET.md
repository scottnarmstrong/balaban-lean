# LFSTEP audit packet (W1136, refute-first): `lfStepInput_of_parts`, `Spine/LFStep.lean`

Target: `LFStepInput … Φ ΦE` (A4-1h, `Spine/SFStep.lean`), unchanged. Read with SPINE.md "LFStepInput sub-inputs (W1136)".
Every part is `LFImageInput … Q` (the quantifier prefix and hypotheses of `LFStepInput`, verbatim); clause parts are
`rec.SuccFams (Φ rec.F.sf) (Λ rec) Q` = `∀ SD, (Λ rec).Matches SD → Q (fam (Φ rec.F.sf) rec.κK SD (rec.succKD _))`.

## The parts and their sources (one source statement each)
1. `LFHistInput` — `IsComplete (k+1) (k+1)` of `Λ.hist`: LF-3 (c) (Def. I.3.1, (R8)).
2. `LFStepDataInput` — `∃ StepData` at `cs'` with `ker = Λ.ker` and `VacuumTie Set.univ (vacExt rec.Ev k ΦE)`: LF-3 (d); Lemmas
   II.5.14, IV.1.3, IV.1.4, IV.1.6; (S0) P6 (2.32)–(2.33), (3.3); R5, R5′, P6 (3.2).
3. `LFBdryInput` — `D7Bdry` of `ℬ^{(k+1)}` at the physical field (`B_st`, `3κ/2`): Lemma IV.1.5; P5 p. 512; P6 pp. 14–15, 34.
4. `LFBdrySrcInput` — `D7BdryBall` (fields `h' ∈ hSetB2 h r_h`, `h' ≠ h`): blocker 2 leaf 5; Q13-YM §§2, 5; R2.
5. `LFFormInput` — `D1PreForm2` of `stepDensity … Λ.s ρ` for every `vc'` with `D1CorrLim`: P5 §§2–3, P6 §2, (3.3), P5 (1.8).
6. `LFOpBoundInput` — `D5Bound (k+1)`: Lemma II.6.3 (a); **proved** from 7 (`lfOpBoundInput_of_signs`, `Rep.opBound_of_data`).
7. `LFSignInput` — `z_j > 0`, `1 ≤ j ≤ k+1`: P1 (1.11), P4 (4.1).
8. `LFPinInput` — `D4Pin (k+1)`: (D4) of the input; LF-3 (c) (histories restrict to the input's).
9. `LFBudgetInput` — `D6Pre`: LF-2 (i); **proved** from 8 and `PrefixInput` (`lfBudgetInput_of_pin`, `Rep.budgetPre_of_LF2_trunc`).
10. `LFCoherenceInput` — `LFCoherent` of the successor: LF-3 (h), D-IV.9.
11. `LFCorrInput` — `∃ St' vc', D1CorrLim` of the image: P1 (3.106)–(3.110).
Not parts (Lean definitions, clauses proved): `cs' = succCs`, `P' = succP` (`Coh`: `coh_succ`, `FieldClauses`: `field_succ`, ties),
the kept data `succKD = KeptData.upTo` ((S3) via `chiDomAt_congr`; "no kept data are created by a step").

## Why the assembly is not circular and hides no step
* No part mentions `LFStepInput`, `IsRepPre2` or a conjunction of its clauses; each `Q` is one clause (or `StepData` existence).
  `IsRepPre2` is built field by field; (D2), (D8), (D9) are the hypotheses of `LFStepInput`.
* `cs'`, `P'`, `succKD` are definitions: `rec`'s constants and kept data at the scales `≤ k`, the image's running constants at
  `k + 1` (and kept beyond, read by no clause at `k + 1`), zero kept kernels above `k`. Nothing about them is assumed.
* `∀ SD, Matches SD → …` quantifies over data the clauses read only through `ker` (`preOpTop_congr`, `locOp_congr`; `D4Pin`, `D6Pre`
  read no step data; `LFCoherent` reads `ker`), so it does not strengthen a part; existence of such `SD` is part 2
  (non-vacuity of `Matches`: `LFStepRaw.matches_zero`).
* `vc'` is not a free choice: `D1CorrLim` (`src_pos` with `ν_{k+1} > 0`, the limits) fixes `vc'.v1 j`, `vc'.v2 j` for `1 ≤ j ≤ k+1`,
  the only values `D1PreForm2` reads (`EresK2` over `Icc 1 (k+1)`). Refute target: is any other value of `vc'` read?
* (D7) v2 = part 3 at `h' = h` plus part 4 at `h' ≠ h` (`D7Bdry.toD7Bdry2_of_ball`, a case split; the structural clauses from 3).
* Refute targets: (a) a part false for the true construction because of carrier padding (`cs'` beyond `k + 1`; steps `j ≥ k + 1` of
  `StepData` tied to `ΦE`); (b) part 2 at the old steps `j < k` asks the tie of `rec`'s kernels, which `RepRec` does not carry
  (the A4-2v estimate, R10; `norm_stepVacuumTerm_le_of_stepData` shows the pre-R10 inconsistency for `E ≠ 0`); (c) part 7 at `j ≤ k`
  is about `rec`, and no clause of `RepRec` gives it; (d) the SF→LF decision (`muBg_eq_sfBgMass_of_fieldClauses`; no exponent of
  `IsRepPre2` evaluated at `lfBgMass`); (e) `KeptData.upTo`: does (S3) at `cs'` read `cs'` beyond `δ_i, p₀(β_i), C_ψ`, `i ≤ k`?
