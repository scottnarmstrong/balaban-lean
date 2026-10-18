# SPINE-AUDIT — refute-first audit of the Root-F spine (W1096, 2026-10-18)

**Scope.** I read the spine at `a4b9d79a` (`Balaban/Spine/{RootFInputs,Activities,RootF,RootC,Witness}.lean`, `SPINE.md`), the frozen
roots, ROOTASM2 §1 and §3, LFR §I.1, §II.7.6, Part IV, LF-BASE-KF0, the carriers (`Def7.lean`, `Def7v2Class.lean`,
`Def7v2Variants.lean`, `Def6.lean`, `Def6v2.lean`, `LemmaB.lean`), and P5 pp. 498–501, P6 pp. 2–3, P7 pp. 529–533, P9 pp. 515–516
(text layers). P4 is cited through LFR. No Lean was changed or built. "Sketch" marks an argument that is not a Lean proof.

## 1. Verdicts

| Input | Verdict | Exact clause; source |
|---|---|---|
| `PrefixInput` | FAITHFUL (deliberately weak) | `2 ≤ L ∧ 1 ≤ M ∧ 20c₈q ≤ 1−q`; LFR rows 3, 6, 10 allow it (c₈ ∈ (0, c₈′]). It omits constraints the classes need (D5). |
| `BaseStepInput` | FAITHFUL | `∃ ρ ∈ ℛ₁ / ℛ♭₁` with `ν₀ = ν`, `∫ρ₁ = cZ(g)`; LFR Thm II.7.10 (a), (b), P4 (2.42)–(2.54). Its conclusion carries neither large-field (D8) nor `β₀ = β`, so later inputs cannot use them (D1, D2). |
| `ClassStepInput` | STRONGER-THAN-SOURCE | hypothesis `RepClassAt … k ρ νk`; LF-3/LF-4 (Thm IV.1.1, III.10.8) assume (A-IV.2) (running constants of the flow, (I.2)) and full (D8) (D-IV.9); the class has neither (D1, D2). |
| `TransferInput` | STRONGER-THAN-SOURCE (mild) | same hypothesis gap as `ClassStepInput` (D2); statement otherwise = Lemma IV.2.1; no landed route at `K = k̂_f + 1` (D3). |
| `FrozenStepInput` | STRONGER-THAN-SOURCE; VACUOUS-RISK | hypothesis `FlatClassAt … k ρ νk` lacks (I.2) (D2); `FlatClassAt` is not witnessed at any configuration the inputs use (D4). LFR Thm IV.2.2. |
| `LastIntegralInput` | STRONGER-THAN-SOURCE; expected FALSE as stated | the agreement conjunct of `ObservableActivities` (`RootFInputs.lean:162–168`) is required for every member of `FlatClassAt`, whose large-field data on different tori are unrelated (D1); LFR Thm IV.5.3 item 7 derives it from (D8) v1.2 of all data. Bounds and identity match P7 (4.9)–(4.17), P9 (4.4)–(4.7). |
| `KfZeroInput` | FAITHFUL | = the one-scale input of LF-BASE-KF0 (line 137) in absolute form (`E ℓ` free makes it equivalent to the ratio form of `rootF_kf0_partial_of_oneScaleInput`); no paper treats `k_f = 0`; its exact torus lift needs a localized expansion (LF-BASE-KF0 l. 209). |

## 2. Defects, by severity, with fixes

**D1 (high). The classes carry no large-field torus coherence; `LastIntegralInput` and `ClassStepInput` conclude coherence anyway.**
`RepClassAt`/`FlatClassAt` are `IsRep2`/`IsRepFlat2`, which tie the tori `n_K` together only through the one small-field datum
`F.sf` (`coherent : D8SF`). The large-field data `F.lf nK` (histories, step data, boundary terms `ℬ`) and hence `ρ nK` are
independent per torus; `Def7.lean:702–706`: "The large-field part of (D8) is not formalized". Two consequences:
* `LastIntegralInput` asks, for every member, activities that agree exactly on the quarter box of any two tori. *Sketch of a
  counterexample:* take a member with a `g`-dependent boundary term and multiply every `ℬ` on one large torus `n_K` by `t ∈ (0,1)`
  (and redefine `ρ n_K` by (D1)). (D7) survives (locality, reality, analyticity, rotation and torus symmetry are linear; the bound
  shrinks); (D4)–(D6) do not read `ℬ`; the other clauses read only `F.sf`, `cs`. Then `log ∫ρ n_K` changes by a `g`-dependent local
  amount near the origin, of fixed size (weighted by the large-field probability), while the box activities are pinned by a second
  torus and the polymers leaving the box are bounded by `c₉ e^{−κ ℓ/(4ML^j)}`. For `ℓ` large the change cannot be absorbed.
* `ClassStepInput` concludes `IsRep2 … (k+1)`, whose `D8SF.R_eq` asks torus independence of `ℛ^{(k+1)}_m`; `R` adds to `ℛ_m` the
  function `ℛ''_m` made from the removed large-field regions (P5 Thm 2, p. 500), i.e. from `F.lf n_K`, which the hypothesis does not
  make coherent.
The docstring `RootFInputs.lean:54–55` ("the coherence (D8) of the class (carried by A3, A4)") is inaccurate: the spine never reads
(D8), and A3/A4 carry only `D8SF`. Separately, even with full (D8) the last integral must be expanded so that every term is exactly
local (P6 p. 3: "a complete localization"); the landed last-scale A11 results give only closeness (W1088).
*Fix.* Define the large-field half of (D8) as LFR D-IV.9 states it (for `X` in the image of a box of side `< ℓ/2`, the localized
history records, step and kept data and `ℬ(X)` on the torus `n_K` are the push-forward of one `ℤ^d` datum), and add it as a conjunct
of `RepClassAt` and `FlatClassAt` (or as a field of `IsRep2`/`IsRepFlat2`, which needs a Def-7 ruling and audit). Then
`BaseStepInput`, `ClassStepInput`, `TransferInput`, `FrozenStepInput` must also produce it (LF-6 (d), LF-3 (h), LF-5 by the same
proof), and `LastIntegralInput`, `ClassStepInput` may use it. No change to Root-F or to `rootF_of_spine`'s proof is needed.

**D2 (high). The classes pin `ν₀ = ν` but not `β₀ = β`.** `RepClassAt`/`FlatClassAt` add `F.sf.ν 0 = ν`; the running coupling is
free up to `β_k > B L^{k(d−2)}` (`CoeffBounds.flow` has `∃ β₀`; `Coh` ties `cs.beta`, `P.beta` to `sf.β`, and `lam_eq` ties `λ̂` to
the bare `β`). LFR proves LF-3, LF-4, Lemma IV.2.1, Thm IV.2.2, Thm IV.4.1 under (A-IV.2) with (I.2) `β_k = β L^{k(d−2)}γ_k`; its
budget arithmetic uses (I.3) `λ_k ≤ λ̂_k ≤ λ_k + 2` (Lemma B, Lemma II.1.2 (b), Lemma IV.4.2: `log β_{k_f} ≤ dλ̂_{k₀}`), and the
source-estimate pass after D-IV.2 uses `R^run_j ≤ R̂_j`. In Lean, `BudgetSetup` (`LemmaB.lean:37–45`) contains
`run : RunningHyp … β … P.beta` with `lam_eq` at the same `β`, and it is a premise of `IsRep2.toFlat` and `Rep.budgetFlat_of_LF2`;
`IsRep2.p2_le_Gpost` and `IsRepFlat2.p2_le_Gpost_flat` take `RunningHyp` explicitly. So for a member with `β₀ ≫ β` (gains larger,
(H6′) still plausible) the four step inputs and `LastIntegralInput` are not covered by any source argument.
*Fix.* Add `F.sf.β 0 = β` to both class predicates (`BaseStepInput` produces it: `β₁ = βL^{d−2}γ₁`). With `CoeffBounds.flow` and
`PrefixInput`'s `20c₈q ≤ 1−q` it gives (I.2) up to scale `k` with `ε ≤ 1/20`, by the computation of `stop_of_flatClassAt`. The
landed `RunningHyp` is stated for every `k`; a version truncated at the current scale (or `P.beta` pinned beyond `k`) is needed.

**D3 (medium). No landed producer of (H6♭) at the spine's torus horizon.** `FlatClassAt` is `IsRepFlat2 … k k̂_f` on tori with
`K = k̂_f + 1`. `Rep.budgetFlat_of_LF2` (`Def7Basic.lean:201`) needs `K ≤ khat`, and `IsRep2.toFlat` (`Def7v2Basic.lean:119`) needs
`K ≤ k₀ + 1`: `Rep.lf2Hyp` builds the counter history only when the torus horizon is below the pinned top scale
(`hKtop : K ≤ top`), and `frozen_budget` asks `K ≤ khat`. In LFR, LF-2 (ii) runs to the last scale of
the abstract history and Thm IV.2.2 uses `K = k+1 ≤ k_f`; the torus horizon is (A-IV.3) only. So the statements of `TransferInput`,
`FrozenStepInput` and `BaseStepInput` (`k₀ = 0`) are faithful, but none has a landed route, and SPINE.md item 5's "Landed:
`Rep.budgetFlat_of_LF2`" does not apply. *Fix.* Re-prove LF-2 (ii) for a representation with the counter history truncated at
`top = k + 1` (premises `k + 1 ≤ top`, `k ≤ khat`, no relation between `K` and `khat`), then `IsRep2.toFlat` for every `K`.

**D4 (medium). Non-vacuity is shown only at configurations the inputs never use.** `repClassAt_witness` has `kf = 0`, `K = k = 1`,
`ν = 1/(27β)` with `wβ > 10`; there `IsHorizon 3 ν 0` is false (`9ν = 1/(3β) < 1`). Every input uses `RepClassAt` with `IsHorizon`
and `k ≤ k₀ ≤ kf`; `k₀ ≥ 1` forces `ν ≤ 1/(βL^d)`, hence `k̂_f ≥ (log_L(βL^d) − 2)/2`, i.e. `K = k̂_f + 1 ≫ k` for large `β`.
The witness exercises no scale between `k` and `K`. For `FlatClassAt` the same witness works by inspection (`wIsRepFlat2` with `khat := 0`: at
`k = 1`, `W(2,0) = W(2,1) = 0`, so `D6Flat 0 = D6Flat 1`), so SPINE.md's "a witness with `k̂ = K − 1` is open" is too pessimistic,
but again at an unused configuration. The ledger records no rule-10 exemption for the seven inputs or the two predicates.
*Fix.* Witness `RepClassAt` and `FlatClassAt` with `IsHorizon L ν kf`, `K = kf + 1 ≥ k + 2` (zero terms, histories up to `K`), or
record the exemption with this limitation stated.

**D5 (medium–low). A constant constraint missing from `PrefixInput` empties the classes at large `k`.** `Coh.a_free` pins
`sf.a k = compWeight L a k = a(1−L⁻²)/(1−L⁻²ᵏ) → a(1−L⁻²)`, and `CoeffBounds.a_ge/a_lt` ask `9/10 (1−L⁻²)⁻¹ ≤ a_k < 3/2` at every
scale used (up to `k̂_f`, unbounded as `ν ↓ 0`). This needs `L ≥ 3` and `9/10 (1−L⁻²)⁻² ≤ a < 3/2`. LFR §I.1.1's choice
`a = (1−L⁻²)⁻¹` (ARCH row 3) gives at `L = 3`: `a₂ = 81/80`, `a₃ = 729/728 < 81/80`, so `ℛ_k = ∅` for `k ≥ 3` while
`BaseStepInput` and `ClassStepInput` at `k = 1` force `ℛ₂ ≠ ∅`: the inputs cannot all hold when `k₀ ≥ 3`. The
range `a ∈ [9/10(1−L⁻²)⁻¹, 3/2)` of LFR Thm IV.5.4 is not enough either. *Fix.* Add `3 ≤ L`, `9/10 ≤ a(1−L⁻²)²`, `a < 3/2` (with
`a = cs₀.aKer`) to `PrefixInput`, and correct LFR §I.1.1 / Thm IV.5.4 (or the source of `a_ge`, if P4's range means something else).

**D6 (low). `ObservableActivities` bounds the vacuum activities `p_j(X;0)`.** Only increments are consumed (`ratio_eq_exp`,
`rootFClauses_of_activities` use `q(g) − q(0)`). The extra bound is source-supported (Thm IV.4.1 bounds `sup|f(Y)|`; LF-BASE-KF0 (ii)),
so it is not a defect of truth. *Optional fix:* bound `‖p_j(X;g) − p_j(X;0)‖` and ask agreement of increments only.

**D7 (low). SPINE.md coverage is overstated in three places.** (a) Item 6, A11: `finalCoef_close_quarterBox_weighted`,
`fibre_hcoef_of_quarterBox_weighted`, `resum_lastScale_rootF_weighted_of_block_large` give closeness between tori, not the exact
agreement `LastIntegralInput` asks (W1088); `e0CoeffFamily_value_fromTowerG_core_twoTorus` is exact only for the core family (W1090).
(b) Item 5: `Rep.budgetFlat_of_LF2` is inapplicable at `K = k̂_f + 1` (D3). (c) Non-vacuity paragraph: see D4.

**Watch items (not defects of the spine).** (i) The SF→LF interface is not in `IsRep2` (`IsRep2WithInterface`; Q13 ruling forbids
writing it); if the scheme-A step needs it of its input, `ClassStepInput` is stronger than that step. (ii) `D2SF2.sfClass` quantifies
over every Def-6 torus `N₁ ≥ 1`, while `RepFam` reads only `N₁ = L^{m₀} n_k`; the landed chain covers `3 ∣ N₁`, `5 < N₁`, `3^{m₀} ∣ N₁`.

## 3. Constants as data (question 3)

The design respects Root-F's order. `δ` is fixed before `κ, c₉` (LFR row 1: `δ = γ/2 = 1/8`). `Ty, P6, C7, PB, cs₀, M1, c, rH, ϱ` are
rows 3–15, all `β`-free (the `Typing` fields contain no `λ̂`); `λ̂`, `R̂`, `k₀` are built from `β` inside `𝒮[…]` and `Coh`; the running
constants are existential; `β₀` is the maximum of the input thresholds, after `L, M`. A fixed `c₈` (row 10, `c₈ ∈ (0, c₈′]`) is weaker
than LF-7 (d)'s `c_ξ/β` and suffices for `β ≥ c_ξ/c₈`. A fixed `rH` is consistent with the pinned-ball condition `m r_h ≪ ε_j²`,
`m ≍ β⁻¹` (Q13-ANSWER-astra). Nothing is chosen too early; the only gaps are the omitted constraints of D2 and D5.

## 4. The proof of `rootF_of_spine` (question 4)

Correct and as documented. `KfZeroInput` is used only in the branch `νL² > 7/8` (`RootF.lean:422–431`). The stop is proved:
`stop_of_flatClassAt` (`RootF.lean:234–287`) uses (H.6) of the class, `ν₀ = ν` and `PrefixInput`'s inequality, as in LFR Lemma
IV.5.1 (b). All seven inputs are used (`hA1`: `L, M, c₈`; `hA3`: both branches; `hA4` in `class_flow`; `hA4t` once at `k₀`;
`hA4f` in `frozen_flow`; `hA6` at the first `k ≥ max(k₀,1)` with `ν_k > 7/8 L⁻²`, which is LFR's `k_f`; `hA7`). No input is used
vacuously: `IntegralIsZ` links every class member to `Z(g)`, and `BaseStepInput`, `TransferInput` force the classes to be inhabited.
`k₀ ≤ k̂_f` is proved from `β > 1`. The only inaccuracy is the A11 docstring (D1).

## 5. Coverage and the gap to the carriers

The 43 landed declaration names that SPINE.md cites as coverage exist on main (checked by `grep`; generality spot-checked). Per input (what is landed; what is missing):
* **A1.** `exists_rootParams_consts_all` (`L = 7`, `c₈ = 1`): satisfies `2 ≤ L`, `1 ≤ M`, not the `c₈` clause; D5 adds constraints.
* **A3.** `Base/` first-step pieces, general `d, L` (e.g. `baseFirst_partition_integral` over `{d N L M K}`); nothing produces
  `IsRep2 … 1`, `IsRepFlat2 … 1` or `IntegralIsZ`; carrier R7 (W1093) in progress.
* **A4 class.** The chain (`StepTowerRotChainRen.lean:34`) is at `d = L = 3`, `N = 2`, over `StepClass`; LF-4R pieces over the v1
  `D7BdryPost` (usable from v2 via `D7Bdry2Post.toD7BdryPost`, `rH > 0`) with named inputs. No step theorem.
* **A4 transfer / frozen.** `IsRep2.toFlat`, `D2SF2.toFlat2`, `D9Coeff.toFlat` exist; the budget half is blocked by D3 and D2.
* **A6.** `Green/` final pieces at general `3 ≤ d′`, `3 ≤ L`, `N` (e.g. `norm_coef_cutoff_class_le_levels_of_large`); A9, A10 pieces
  at the tower; A11 only closeness at the last scale (D7). Nothing over `IsRepFlat2`.
* **A7.** Only the shape (`hprov` of `rootF_kf0_partial_of_oneScaleInput`, itself a hypothesis); LF-BASE-KF0 B′ open.

**From the landed chain to `IsRep2 … (k+1)`, what must be proved.** The chain returns, for one Def-6 torus with `3 ∣ N₁`, `5 < N₁`,
`3^{m₀} ∣ N₁`, `m₀ ≥ 7`, mass `ν·3^{2(k+1)} ≤ 1`, a given `StepClass C` with `SFTermClauses P Dom C.Tm` and named premises (chart
room, `ChosenOne`, `ConnStruct`, `0 ≤ E₀`), the new-level local energy coefficients. The carrier's (D2) needs:
1. **generality**: the chain at `StepTowerG d L N` (A8/A11 pieces already there, with `T.m₀ = 1`; whether this `m₀` is the
   `StepClass` exponent `≥ 7` is to be checked), at the `L` fixed by D5 and A1;
2. **the bridge chain ⇒ `IsSFFamily2 P6 ⟨k₀, ν′⟩ β′ a′ (sfDom P6 k₀ sf′) Tm′ ρsf′ E′`**: (H.1) `IsSF2.density` in the `expo2` form
   (physical mass in the action, `sfBgMass` in the solver, `χ_k` at `p(β_k)/√β_k`); `SFTermClauses` on the wide domain `sfDom`
   (`xiFieldDom` at `sfBgMass`, radius `P6.eps`) rather than the chain's premise domain with radii `t_k = λε_{k+1}`; `gsStrong`;
   `torusIndep` and `D8SF` for every `N₁ ≥ 1` (or a carrier restricted to `N₁ ∈ L^{m₀}ℕ`); `renorm` (H.5) through the `ℤ^d` limit;
   `coeff` (H.6) with the step's `ξ` (`rg_step_infty`) under one `c₈` and with `β₀ = β` (D2); `RTermsH4` for `ℛ^{(k+1)}_m`, which the
   chain does not produce; the inherited terms (W1090), ruling R8, the counterterms;
3. **the large-field clauses at `k+1`**: (D1) `D1Form2` as a sum over the complete history set, (D4)–(D7) for the new step data and
   `R` (blockers 2–4, 6), `Coh`, `FieldClauses`, and the large-field (D8) of D1;
4. **the family**: one `F.sf` for all Def-6 tori and `F.lf n_K` for every `n_K` at `K = k̂_f + 1`, with `ν₀ = ν`, `β₀ = β`.
