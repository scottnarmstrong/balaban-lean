/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.HistCanon
public import Balaban.Spine.AgreeTransportRep
public import Balaban.LargeField.R.RHistoryLabels
public import Balaban.LargeField.Def7Counts
public import Balaban.LargeField.Def7Basic

/-!
# The kept half of `R`: the large-field part `lf₁` of the output

LFR Theorem III.8.9 (a), (b); P7 (1.3)--(1.6).  On one torus, from the pre-`R` large-field part
`r₀ = rec.F.lf nK` the output large-field part is

* the histories `canonHist k (k+1)` (a complete set at `(k, k+1)`, `canonHist_complete`);
* the step data of `r₀` (and its boundary terms, replaced later by `ℬ'`);
* the kept exponents `κ'`: those of `r₀` at the scales `i ≠ k`, and at the scale `k` the pinned
  exponent `κ_k = κ^pre_k` (`pinnedExp`);
* the kept data `KD'` (the five kept outcomes `ϰ₁, …, ϰ₅` of `R` at the scale `k`: `KeptScaleData`).

**History enumeration (OPEN-R-HISTORY-ENUM, with ruling R12).** The new set of histories is not
enumerated outcome by outcome: any set complete at `(k, k+1)` has exactly one history for every
pair (history `A` of the pre-`R` set, realized outcome assignment `f`) (`canonHist_enum`).  The
realized assignments include the removal outcome; histories with a removal record are in the set and
their term of (D1) vanishes by R12 (`postTerm2_of_rem`), so removal histories are counted once and
do not enter the kept half.

**Proved here** (`keptRep_*`): completeness at `(k, k+1)`, the step data, `D4Pin k` (by the pin along
`Agree`, `d4Pin_of_agree_le`), `D4Pin (k+1)` from the locality of `κ^pre_k` (`KappaPreLocal`),
`D5Bound (k+1)` (LFR Lemma II.6.3 (a), `Rep.opBound_of_data_le`) and `D6Budget` (LF-2 (i),
`Rep.budget_of_LF2_trunc`).

**Named residuals** (the hypotheses; nothing else is assumed): `KappaPreLocal` (OPEN-R-TOP-PIN: the
exponent `κ^pre_k(Z, 𝔸 ∩ Z)` of a kept component is a function of its localized history; the
kept costs `γ_j(ϰ)` below `k` enter it, so this is the statement that they do not distinguish
histories with the same localized history), and `KeptScaleData` (the kept kernels of the five
outcomes at the scale `k`, with the bound (1.26) at the exponent
`κ_k - C_R λ̂_k^{2d+1} + γ_k(ϰ)`: `keptKernel_one_kerBound` to `keptKernel_five_kerBound`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

section Generic

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- `Agree` is monotone in the scale of the step records. -/
theorem agree_mono_left {k k' r : ℕ} {A B : LabHist S n R k0 K} (h : A.Agree k r B)
    (hk : k' ≤ k) : A.Agree k' r B :=
  ⟨fun j hj => h.1 j (by omega), h.2⟩

/-- **The enumeration of the outcomes by a set complete at `(k, k+1)`** (OPEN-R-HISTORY-ENUM): for
every history `A` and every realized outcome assignment `f` (the removal outcome included) there is
exactly one history of the set that agrees with `A` at `(k, k)` and has the outcome `f` at the
scale `k`. -/
theorem enum_of_isComplete_succ {𝔄' : Finset (LabHist S n R k0 K)} (h : IsComplete k (k + 1) 𝔄')
    (A : LabHist S n R k0 K) (f) (hf : f ∈ Realized k A) :
    ∃! B, B ∈ 𝔄' ∧ B.Agree k k A ∧ B.outcomeAt k = f := by
  obtain ⟨C, hCA, rfl⟩ := hf
  obtain ⟨B, ⟨hB, hCB⟩, huniq⟩ := h C
  obtain ⟨h1, h2⟩ := (agree_succ_iff_outcome k C B).mp hCB
  refine ⟨B, ⟨hB, LabHist.agree_trans (LabHist.agree_symm h1) hCA, h2.symm⟩, ?_⟩
  rintro B' ⟨hB', hB'A, hB'f⟩
  exact huniq B' ⟨hB', (agree_succ_iff_outcome k C B').mpr
    ⟨LabHist.agree_trans hCA (LabHist.agree_symm hB'A), hB'f.symm⟩⟩

/-- The canonical set of histories enumerates the outcomes. -/
theorem canonHist_enum (A : LabHist S n R k0 K) (f) (hf : f ∈ Realized k A) :
    ∃! B, B ∈ canonHist S n R k0 K k (k + 1) ∧ B.Agree k k A ∧ B.outcomeAt k = f :=
  enum_of_isComplete_succ (canonHist_complete k (k + 1)) A f hf

/-! ### The exponents -/

variable {H : RegionHistory S n R k0 K}

/-- `κ_j` reads the kept exponents only up to the scale `j`. -/
theorem kappa_congr (P : BudgetConsts) (κ₁ κ₂ : ∀ k, H.Comp k → ℝ) :
    ∀ j, (∀ i, i ≤ j → ∀ c, κ₁ i c = κ₂ i c) → ∀ c, H.kappa P κ₁ j c = H.kappa P κ₂ j c
  | 0, _, c => by simp only [RegionHistory.kappa]
  | j + 1, h, c => by
    classical
    simp only [RegionHistory.kappa]
    split_ifs with hk
    · exact h _ le_rfl c
    · unfold RegionHistory.kappaPre
      congr 1
      refine Finset.sum_congr rfl fun c' _ => ?_
      exact kappa_congr P κ₁ κ₂ j (fun i hi => h i (by omega)) c'

/-- **`κ^pre_j` reads the kept exponents and costs only below `j`.** -/
theorem kappaPreH_congr (r₁ r₂ : Rep S n R k0 K M N geo cs P k) (A : LabHist S n R k0 K) (j : ℕ)
    (hκ : ∀ i, i < j → r₁.κK i = r₂.κK i)
    (hgam : ∀ i, i < j → ∀ l, r₁.KD.gam i l = r₂.KD.gam i l) (Z : A.H.Comp j) :
    r₁.kappaPreH A j Z = r₂.kappaPreH A j Z := by
  cases j with
  | zero => rfl
  | succ j =>
    show A.H.kappaPre P j (r₁.kappaH A j) Z = A.H.kappaPre P j (r₂.kappaH A j) Z
    unfold RegionHistory.kappaPre
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold Rep.kappaH
    refine kappa_congr P _ _ j (fun i hi c' => ?_) c
    unfold Rep.keptExp
    rw [hκ i (by omega), hgam i (by omega)]

/-! ### The pinned exponent -/

/-- **The pinned exponent** `κ_k(a) = κ^pre_k(Z, 𝔸 ∩ Z)` of the localized history `a` of a kept
component (the value of `r₀.kappaPreH` at some kept component with that localized history, `0` if
there is none). -/
noncomputable def pinnedExp (r₀ : Rep S n R k0 K M N geo cs P k)
    (hist : Finset (LabHist S n R k0 K)) (k : ℕ) (a : LocalHistory S n M K) : ℝ := by
  classical
  exact if h : ∃ A ∈ hist, ∃ Z : A.H.Comp k, IsKept A.H k Z ∧ Z.1 ∉ A.H.rem k ∧
      A.H.localHistory M K k Z = a then
    r₀.kappaPreH h.choose k h.choose_spec.2.choose else 0

/-- **OPEN-R-TOP-PIN, the locality of `κ^pre_k`**: the exponent `κ^pre_k(Z, 𝔸 ∩ Z)` of the kept
non-removed components of the histories of `hist` is a function of the localized history of the
component. -/
def KappaPreLocal (r₀ : Rep S n R k0 K M N geo cs P k) (hist : Finset (LabHist S n R k0 K))
    (k : ℕ) : Prop :=
  ∀ A ∈ hist, ∀ Z : A.H.Comp k, IsKept A.H k Z → Z.1 ∉ A.H.rem k →
    ∀ B ∈ hist, ∀ Z' : B.H.Comp k, IsKept B.H k Z' → Z'.1 ∉ B.H.rem k →
      A.H.localHistory M K k Z = B.H.localHistory M K k Z' →
        r₀.kappaPreH A k Z = r₀.kappaPreH B k Z'

theorem pinnedExp_spec {r₀ : Rep S n R k0 K M N geo cs P k} {hist : Finset (LabHist S n R k0 K)}
    (hloc : KappaPreLocal r₀ hist k) {A : LabHist S n R k0 K} (hA : A ∈ hist)
    (Z : A.H.Comp k) (hK : IsKept A.H k Z) (hr : Z.1 ∉ A.H.rem k) :
    pinnedExp r₀ hist k (A.H.localHistory M K k Z) = r₀.kappaPreH A k Z := by
  classical
  have hex : ∃ B ∈ hist, ∃ Z' : B.H.Comp k, IsKept B.H k Z' ∧ Z'.1 ∉ B.H.rem k ∧
      B.H.localHistory M K k Z' = A.H.localHistory M K k Z := ⟨A, hA, Z, hK, hr, rfl⟩
  unfold pinnedExp
  simp only [hex, dite_true]
  obtain ⟨hB, hZ'⟩ := hex.choose_spec
  obtain ⟨hK', hr', hloc'⟩ := hZ'.choose_spec
  exact hloc _ hB _ hK' hr' A hA Z hK hr hloc'

/-- The kept exponents of the output: those of `r₀` except at the scale `k`, where they are pinned. -/
noncomputable def keptExpOut (r₀ : Rep S n R k0 K M N geo cs P k)
    (hist : Finset (LabHist S n R k0 K)) (k : ℕ) :
    ℕ → LocalHistory S n M K → ℝ :=
  fun i a => open Classical in if i = k then pinnedExp r₀ hist k a else r₀.κK i a

/-- **The kept data of the five outcomes of `R` at the scale `k`** on one torus: kept data with the
exponents `keptExpOut` whose costs `γ_i(ϰ)` below the scale `k` are those of `r₀` (the exponents
`κ^pre_k` read them). -/
structure KeptScaleData (r₀ : Rep S n R k0 K M N geo cs P k) where
  KD : KeptData k0 geo cs N (keptExpOut r₀ (canonHist S n R k0 K k (k + 1)) k) S.lam
  gam_eq : ∀ i, i < k → ∀ l, KD.gam i l = r₀.KD.gam i l

/-! ### The large-field part of the output -/

/-- **The large-field part `lf₁` of the output of `R`** on one torus. -/
noncomputable def keptRep (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀) :
    Rep S n R k0 K M N geo cs P k where
  hist := canonHist S n R k0 K k (k + 1)
  κK := keptExpOut r₀ (canonHist S n R k0 K k (k + 1)) k
  SD := r₀.SD
  KD := D.KD
  B := r₀.B

theorem keptRep_complete (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀) :
    IsComplete k (k + 1) (keptRep r₀ D).hist :=
  canonHist_complete k (k + 1)

theorem keptRep_SD (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀) :
    (keptRep r₀ D).SD = r₀.SD := rfl

/-- **`D4Pin k` of the output**: the pins below the scale `k` are those of `r₀`, transported along
`Agree` (every history of the output agrees at `(k-1, k)` with a history of `r₀`). -/
theorem keptRep_pin_below (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀)
    (hcomp : IsComplete k k r₀.hist) (hpin : D4Pin k r₀) : D4Pin k (keptRep r₀ D) := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · intro A _ j hj1 hjt; omega
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  subst hm
  refine d4Pin_of_agree_le r₀ (keptRep r₀ D) m (fun i hi => ?_) (fun j hj l => D.gam_eq j (by omega) l)
    rfl rfl (fun _ _ => rfl) hpin ?_
  · funext a
    show (open Classical in if i = m + 1 then _ else _) = _
    simp only [show i ≠ m + 1 by omega, ite_false]
  · intro A _
    obtain ⟨B, ⟨hB, hAB⟩, -⟩ := hcomp A
    exact ⟨B, hB, agree_mono_left hAB (by omega)⟩

/-- **`D4Pin (k+1)` of the output**: the pins below `k` and the pin at the scale `k`, which is the
definition of the pinned exponent on the locality `KappaPreLocal`. -/
theorem keptRep_pin (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀)
    (hcomp : IsComplete k k r₀.hist) (hpin : D4Pin k r₀)
    (hloc : KappaPreLocal r₀ (canonHist S n R k0 K k (k + 1)) k) : D4Pin (k + 1) (keptRep r₀ D) := by
  refine (d4Pin_succ_iff (keptRep r₀ D) k).2 ⟨keptRep_pin_below r₀ D hcomp hpin, fun _ A hA Z hK hr => ?_⟩
  have h1 : (keptRep r₀ D).κK k (A.H.localHistory M K k Z) =
      r₀.kappaPreH A k Z := by
    show keptExpOut r₀ _ k k _ = _
    unfold keptExpOut
    simp only [ite_true]
    exact pinnedExp_spec hloc hA Z hK hr
  rw [h1]
  refine (kappaPreH_congr r₀ (keptRep r₀ D) A k (fun i hi => ?_) (fun i hi l => (D.gam_eq i hi l).symm) Z)
  funext a
  show _ = keptExpOut r₀ _ k i a
  unfold keptExpOut
  simp only [show i ≠ k by omega, ite_false]

/-- **`D5Bound (k+1)` of the output** (LFR Lemma II.6.3 (a): (D4) implies (D5)): the localized
operators of the scales `≤ k`, with the kept operators of `D.KD` at the ripe components. The signs
`z_{j+1} > 0`, `β_j a L^{d-2} ≥ 0` are needed for `j + 1 ≤ k`. -/
theorem keptRep_opBound (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀)
    (hz : ∀ j, j + 1 ≤ k → 0 < cs.z (j + 1))
    (hc : ∀ j, j + 1 ≤ k → 0 ≤ cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (hkK : k ≤ K) :
    D5Bound (k + 1) hkK (keptRep r₀ D) :=
  (keptRep r₀ D).opBound_of_data_le hz hc (k + 1) hkK

/-- **`D6Budget` of the output** (LF-2 (i), LFR Theorem I.5.4 (i), the counter history truncated
at the scale `k`): from `D4Pin (k+1)`, the setting `Good` and the budget setup up to `k`. -/
theorem keptRep_budget (r₀ : Rep S n R k0 K M N geo cs P k) (D : KeptScaleData r₀)
    (hpin : D4Pin (k + 1) (keptRep r₀ D)) (G : S.Good) (B : BudgetSetupTo S P k) (hk1 : 1 ≤ k)
    (hk0 : k ≤ k0) (hkK : k ≤ K) : D6Budget (keptRep r₀ D) :=
  (keptRep r₀ D).budget_of_LF2_trunc G B hpin hkK (Nat.le_succ k) hk1 hk0 le_rfl (Nat.lt_succ_self k)

end Generic

end Balaban.RootFSpine
