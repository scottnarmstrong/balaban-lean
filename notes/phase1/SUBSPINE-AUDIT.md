# SUBSPINE-AUDIT — refute-first audit of the six landed sub-spines (W1120, 2026-10-18)

Scope: `Balaban/Spine/{ClassStep,LastIntegral,InheritedBound,InheritedAgree,BaseStep,KfZero,KfZeroGood,FrozenStep,RStep}.lean` at origin/main (6b8cf1f7),
read with `RootFInputs.lean`, `Coherence.lean`, `SPINE.md`, `SPINE-AUDIT.md`, `SPINE-AUDIT-2.md`, and the carriers they read
(`Def7.lean` D4Pin/D5Bound/D6Budget, `Def7SmallField.lean` SFData, `Def7v2Class.lean`, `Def6.lean` IsSFFamily/CoeffBounds,
`QuietLocalInput.lean` StepData, `StepVacuumR5.lean`). No Lean was changed or built; no probe files were needed.
"Likely FALSE" marks an argument that is a sketch, not a Lean proof.

## 1. Verdicts

| Sub-input | Verdict | Exact clause; source |
|---|---|---|
| `SFStepInput` | FAITHFUL (open); WEAKER-THAN-NEEDED (low) | Hyp `RepClassAt k`, `1 ≤ k < k₀`; concl `PreClassAt (k+1) k` + `IntegralStep`. LFR Thm IV.1.1. No tie `F'.sf.β j, ν j = F.sf.β j, ν j` for `j ≤ k` (defect 5). |
| `RInput` (the spine input, read as the consumer) | FAITHFUL | `1 ≤ k ≤ k₀`, `PreClassAt k k` ⇒ `RepClassAt k` same `νk`, same integral; LFR Thm III.10.8, Lemma III.8.4, P7 (1.7). |
| `FlowRateInput` | FAITHFUL (proved satisfiable) | `c₈ q ≤ (1-q)/20`, `q = L^{-2γ}`; LFR Thm IV.3.2 (d); clause of `PrefixInput`; `flowRateInput_of_lower`. |
| `InheritedBoundInput` | FAITHFUL (proved from `PrefixInput`) | Support, analyticity, bound `c₉/2 · L^{-j((d-2)/2+δ)} e^{-κ|X|/(ML^j)^d}` of `inhObs`, `j ≤ k`; LFR Thm IV.5.3 items 2,4,5; P4 (H.7). |
| `InheritedAgreeInput` | FAITHFUL (proved, `β₀ = 0`, from `FlatRep` alone) | `ActAgree` of `inhObs`; LFR Thm IV.5.3 item 7, `D8SF.M_eq`, `Geo.hc`. |
| `FinalSmallFieldInput` | STRONGER-THAN-SOURCE (mild); VACUOUS-RISK | `sfIntegral = exp(E+⟨g,h⟩+Σ_{j≤k}Σ q_j+Σ a)` with `q = inhObs` pinned, `a` complete `ObservableActivities` at `c₉/2` (so `c₉/4`). P4 §6, P7 (4.1)–(4.9),(4.15)–(4.17). |
| `FinalLargeFieldInput` | FAITHFUL (open); VACUOUS-RISK | `∫ρ = sfIntegral · exp(Σ b)`, `b` complete at `c₉/2`; P7 (4.9)–(4.14), P5 (3.18), LFR Lemma IV.4.2. |
| `BasePreStepInput` | FAITHFUL (open); VACUOUS-RISK | `∃ z₁>0 νk, PreClassAt kf 1 0 (firstDensity z₁) νk` for `k₀ ≥ 1`; LFR Thm II.7.10 (b)–(d), P4 (2.42)–(2.54). |
| `BaseFlatStepInput` | FAITHFUL (open); VACUOUS-RISK | same with `FlatClassAt kf 1`, `ν₁ ≤ 9/10`, for `k₀ = 0`; LFR Thm II.7.10, (D9♭). |
| `KF0GoodSectorInput` | FAITHFUL for `0 < thr`; FALSE for `thr ≤ 0` (proved, W1117) | `Z_∅ = exp(E+⟨g,h⟩+Σ a)`; LF-BASE-KF0 Part F.2, Thm F.1. |
| `KF0BadSectorInput` | FAITHFUL for small `thr`; TRIVIAL for `thr > 2` (`b = 0`) | `Σ_B Z_B = Z_∅ exp(Σ b)`; LF-BASE-KF0 Parts D, E, G; P7 (4.11)–(4.14). |
| `FrozenSFStepInput` | FAITHFUL (open); WEAKER-THAN-NEEDED (low) | `FlatClassAt k`, `max(k₀,1) ≤ k < k̂_f`, `ν_k L² ≤ 7/8` ⇒ `FlatPreAt (k+1) k (ν_k = νk)` + `IntegralStep`; LFR Thm IV.2.2. Only `ν_k` is tied (defect 5). |
| `RVacuumInput` | INDEX-OR-TYPE ERROR (then FALSE or a hidden gauge) | `VacuumTied`: `SD.VacuumTie univ rec.F.sf.E dpp dppp` reads the torus-indexed `sf.E` as the scale-indexed flow `E_j` (defect 2). |
| `RKeptInput` | WEAKER-THAN-NEEDED (near trivial) | `∃ lf₁` with `IsComplete`, `SD` equal, `KeptOutput`; the kept kernel values are not tied to `ρ` (defect 1). |
| `RGasInput` | likely FALSE (universal over the kept data) | `∀ lf₁` with `KeptOutput`, `∃ B' Rpp ρ'`, `GasOutput` incl. `∫ρ'=∫ρ` (defect 1). |

Consumption: every `…_of_parts` theorem consumes all its inputs (`classStepInput_of_parts`: hSF, hR, hQ; `lastIntegralInput_of_parts`: hB, hA, hS, hL, each in
the `p`, the clauses or the identity; `baseStepInput_of_parts`: hP, hR, hQ (via `PreClassAt.succ`), hF; `kfZeroInput_of_parts`: hG, hB; `frozenStepInput_of_parts`:
hSF, hQ (both (I.2) and the mass bound); `rInput_of_parts`: hV, hK, hG; hV is used only to produce `hvac` for hG). No use is vacuous in the Lean sense:
the output fields `form`, `bdry`, `coherent`, `sfData`, `complete`, `pin`, `opBound`, `budget` of `rInput_of_parts` are each read from a sub-input
or carried by `coh_addRem`, ….

Order of constants: all `β₀` are chosen after `κ, c₉` and before `β`; `thr κ c₉ β ν` may depend on `β` but not on `h, kf`; `δ` is fixed before `κ, c₉`; the
existential `z₁`, `νk`, `p`, `E`, `a`, `b`, `B'`, `Rpp`, `ρ'` are all chosen after `β, ν, h, kf, k, ρ`. No wrong-order defect found.

## 2. Defects, by severity

**1 (high). `RGasInput` quantifies over every kept datum `lf₁` with `KeptOutput`; the data do not determine `lf₁` from `ρ`. `RKeptInput` is near trivial.**
`KeptOutput` is `D4Pin (k+1)` (the exponents `κK` of kept components), `D5Bound (k+1)` (`PkgBound`: an upper bound on the kept operators), `D6Budget`
(an inequality between `tStar`, `tau`, `sigma`, `W`, `Gpost`, with no kernel value) and `LFCoherent` of the family with zero boundary terms. All four
survive replacing every kept kernel of `lf₁` by half of itself (or by zero): bounds only get smaller, exponents are unchanged, a constant factor is torus
coherent. `RKeptInput` (`∃ lf₁`) is then satisfied by the zero kept kernels, so it carries no content about `ρ`; `RGasInput` (`∀ lf₁ …`) asks for `ρ'` with
`D1Form2` for the family built on that `lf₁` and `∫ρ' = ∫ρ`. For the halved kept kernels the `D1Form2` sum differs from the true one by the contribution of
every history with a kept component, which is positive and `g`-dependent; `B'` and `Rpp` are only bounded by (D7) and the allowance `1/2` of `RTermsH4`, so
they cannot make up an `O(1)` relative change of those terms. This is the "universally quantified form can be false" pattern of W1118, in the interface
between the kept and the gas half (SPINE.md says the later stage quantifies over the earlier one's output "under the earlier one's properties"; the
properties are inequalities, so they do not pin the output).
*Fix.* One sub-input `RKeptGasInput`: for `rec` with `VacuumTied`, `∃ lf₁ B' Rpp ρ'` with `IsComplete`, `SD` equal, `KeptOutput rec.hkK rec.F lf₁` and
`GasOutput … lf₁ B' Rpp`. `rInput_of_parts` takes `RVacuumInput` and this one; the proof changes only in destructuring. (Alternative: keep two inputs and
add to `KeptOutput` the equation of the kept data with the kept operators of R applied to `rec`; no landed operator names them, so the merge is the
realistic repair.)

**2 (high). `VacuumTied` reads `sf.E` as a scale-indexed flow; it is indexed by the Def-6 torus.**
`SFData.E : ℕ → ℝ` is "the constant `E_k` of `E_k|T^{(k)}_1|` on the Def-6 torus `N₁`" (`Def7SmallField.lean:75`; used as `sf.E N₁` in `IsSF`
(`Def6.lean:204`: `Ek N₁ · (N₁ L^{m₁})^d`) and in `EresK2` (`Def7v2Form.lean:125`: `C.sf.E C.N₁ * volK M Y`)). `StepData.VacuumTie SD T E dpp dppp` asks
`SD.vacE k a = E k` for the scale `k` of the creating step. In `VacuumTied` the argument is `rec.F.sf.E`, so the scale `k` is read as a torus
index. Consequences: (i) the data of the class contain no `E_j` for `j < k` (only the current scale's constant per torus), so the tie to the flow cannot
be stated; (ii) if `sf.E` is constant in `N₁` (as the physical `E_k` is), the tie forces `vacE_j = E_k` for all `j`, contradicting `b0_bound`
(`b0` bounded by `(C_b log β_j + C_b B₀)·vol` with `E_{j+1} - E_j ≈ ½N log β_j + O(1)`) once `k - j` is large; (iii) a satisfying `rec` would have to use an
unphysical `N₁`-dependent gauge of `sf.E`. The statement is therefore false or vacuous in a way that hides the real content (`b0_bound` for the flow
constants). This is W1119's finding; it is confirmed from the carriers.
*Fix.* `RVacuumInput` concludes `∃ rec, ∃ Ev dpp dppp : ℕ → ℝ, (∀ N₁, sf.E N₁ = Ev k) ∧ ∀ nK, (rec.F.lf nK).SD.VacuumTie univ Ev dpp dppp`
(a scale-indexed flow, offsets outside `∀ nK` since `δ″_k, δ‴_k` are explicit functions of `β_k, N, L, p₁` (P4 (2.1), (2.41), (2.63))), and the
gas input takes the triple as part of its hypothesis (`VacuumTied rec Ev dpp dppp` as a structure produced by the vacuum input). Or add the flow
`Eflow : ℕ → ℝ` to `SFData` (needs a Def-7 ruling and the audit of Def-7). With defect 1 merged, the vacuum input stays separate.

**3 (medium). Non-vacuity at the used configurations is open for all fifteen sub-inputs.**
Every hypothesis is `RepClassAt`/`FlatClassAt`/`FlatRep`/`PreRec` at `K = k̂_f + 1 ≥ k + 2`, where no witness exists (D4 of SPINE-AUDIT, `Witness.lean`
at `kf = 0`, `K = k = 1`). `LastIntegral` (four inputs, `FlatRep` hypothesis), `RStep`, `FrozenStep`, `ClassStep` are vacuous if the class is empty there; the
ledger exemption covers it. Known cheap facts: `KF0BadSectorInput` holds with `b = 0` for `thr > 2`, and then `KF0GoodSectorInput` is the whole of `KfZeroInput`
at half amplitude, so the split carries content only for `0 < thr ≤ 2`. `KF0GoodSectorInput` is false for `thr ≤ 0` (`not_kf0GoodSectorInput_of_thr_nonpos`).
*Fix.* (a) a witness of `FlatRep` at `kf = 1`, `K = 2`, zero terms, which needs `quietStepData'` (SPINE.md, non-vacuity); (b) record in the statement of
`kfZeroInput_of_parts` a premise `∀ κ c₉ β ν, 0 < thr κ c₉ β ν ∧ thr κ c₉ β ν ≤ √2` (the source range), so that the provider cannot choose a threshold at which one
sub-input is trivially true and the other false.

**4 (medium). `FinalSmallFieldInput` pins `q = inhObs` and asks `a`, `b` complete at all scales `≤ k+1`.**
(i) `ObservableActivities … (k+1) kf a` also constrains `a` at scales `j ≤ k` (support, bound), which `lastIntegralInput_of_parts` removes with `actAt (k+1)`;
this is harmless (the provider takes `a_j = 0` there) but it is a clause the source does not state. (ii) The pin `q = inhObs F.sf P6.m₀ h` is the form of LFR
Def. IV.5.2; if `ℳ^{(j)}` at the constant configuration `(constFld h, constFld h)` differs from the source object (open item (a) of A6-1, proved only as a bound), A6-3 changes
with it. (iii) The exact `ActAgree` of `a`, `b` needs the complete localization (SPINE-AUDIT-2 (d), W1088: closeness is landed, not equality).
*Fix.* State `a`, `b` with `ObservableActivitiesAt (k+1)` (only the scale `k+1`, i.e. `ActSupportAt/ActBoundAt` for `j = k+1`), keep `ActAnalyticAt`, `ActLocalAt`,
`ActAgree`; prove one agreement lemma from `LFCoherent` and `D8SF`, so that (iii) is a single named obligation. No change to the sub-spine proofs beyond `actAt`.

**5 (medium-low). The step outputs do not tie the earlier running constants.**
`SFStepInput` and `FrozenSFStepInput` (and `RGasInput` through `rec`) assert `β_0 = β`, `ν_0 = ν`, (I.2) up to `k`, and (frozen only) `ν_k = νk`; `F'.sf.β j`, `F'.sf.ν j`
for `1 ≤ j ≤ k` need not equal those of the input. The domain `sfDom = birthXiDom P6 ⟨k₀, sf.ν⟩ sf.a` (R6, applied) reads `sf.ν j` at every level, so the inherited
terms of `F.sf` lie in the birth domain of `F'` only if `ν'_j = ν_j`; and the mass bound `ν_{k+1} ≤ (81/79)ν_k L²` of `frozenStepInput_of_parts` is about the
`ν_k` of the output, which is tied to the input mass only for the frozen step. Not false (the provider chooses `F'`), but a provider that builds `F'` from `F` must prove
the ties, and the three classes cannot be compared across a step in Lean.
*Fix.* Add to the output `∀ j ≤ k, F'.sf.β j = F.sf.β j ∧ F'.sf.ν j = F.sf.ν j ∧ F'.sf.a j = F.sf.a j` (and `z`, `E` for `j ≤ k`) in `SFStepInput` and
`FrozenSFStepInput`; `ClassStep` and `FrozenStep` proofs are unchanged (they read `F'` only). This also makes the running mass sequence one object along the flow.

**6 (low). Documentation drift.** SPINE.md (ClassStep section, "A landed definition must change", and the first FrozenStep paragraph) says R6 is "not yet applied":
`sfDom` is `birthXiDom` on main (`Def7v2Class.lean:59`). `PreClassAt` is `Nonempty PreRec` (W1118); SPINE.md's "the body is written a second time" in the RInput
section is outdated. The text of SPINE.md for `RVacuumInput` ("`VacuumTied` for every torus … `rec.F.sf.E`") should be replaced when defect 2 is fixed.

**7 (low). `RVacuumInput` offsets inside `∀ nK`.** `∃ dpp dppp` is chosen per torus; the physical offsets do not depend on the torus. Covered by the fix of defect 2.

## 3. Checks that passed (no defect)

* Index of `inhObs`: `N₁ = ℓ/(L^{m₁}L^k)` is the Def-6 torus of `RepFam.ctx` (`sideDiv_eq_sfIdx`), `ℓ = M n_K L^{kf+1}` is divisible by `L^{m₁+k}`; `E nK` in `LastIntegralInput`
  is indexed by the top-torus count `nK`, `E ℓ` in `KfZeroInput` by the side, each consistent with its own statement.
* Scale conventions: `SFStepInput` `k < k₀` (output at `k+1 ≤ k₀`), `RInput` at `k+1 ≤ k₀` (`hk` gives it), `Rep … k` with `IsComplete k (k+1)`, `D4Pin (k+1)` for `IsRep_k`
  (the documented `top = k+1`); frozen steps `k < k̂_f` so `k+1 ≤ K`; `PreClassAt.succ` uses `CoeffBounds … (k+1)` at the scale `k+1` of the `PreRec`.
* `nu_succ_le_of_coeffBounds`: `‖ξ^{(k)}‖ ≤ (c₈/4)q^{k+1} ≤ (1-q)/80 ≤ 1/80` and `(1+1/80)/(1-1/80) = 81/79`, `81/79 · 7/8 = 567/632 < 9/10`; indices `ξ k 1` (`ξ₂`), `ξ k 2` (`ξ₃`)
  match `Flow.nuSeq`, `Flow.gammaSeq`.
* `integral_firstDensityAt` holds for every `z₁ > 0`, so the existential `z₁` of the base inputs costs nothing in `IntegralIsZ`; `firstSide_eq` matches `ℓ = L · (M n_K L^{K-1})`.
* `kfZeroInput_of_parts`: the sector identity holds for every `thr` (the sectors partition the configurations), the amplitudes `c₉/4 + c₉/4` give `c₉/2` (`add_halves`).
* `lastIntegralInput_of_parts`: the exponent `E + ⟨g,h⟩ + Σ_{j ≤ k} q_j + Σ(a+b)` is assembled by `sum_actAdd_actAt` with `q_j = 0` above `k`; `ActBoundAt.add_actAt_succ` keeps
  `c₉/2` at `j ≤ k` and `c₉/4+c₉/4` at `k+1`.

## 4. Order of work suggested

1. Merge `RKeptInput`/`RGasInput` into one existential and repair `VacuumTied` (defects 1, 2): small edits in `RStep.lean`, `rInput_of_parts` re-proved, `classStepInput_of_parts` unchanged.
2. Add the running-constant ties to the outputs of `SFStepInput`, `FrozenSFStepInput` (defect 5).
3. Restate the scale of `ObservableActivities` for `a`, `b` (defect 4) and add the `thr` range premise (defect 3b).
4. Build the `FlatRep`/`RepClassAt` witness at `kf = 1`, `K = 2` (defect 3a), then request the ledger exemption only for the genuinely open inputs.
