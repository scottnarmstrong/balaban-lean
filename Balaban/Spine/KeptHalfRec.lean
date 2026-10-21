/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KeptHalf
public import Balaban.Spine.KappaLocal
public import Balaban.Spine.KeptCoherence
public import Balaban.Spine.RStep
public import Balaban.Spine.BudgetSetupCore

/-!
# The kept half of `RKeptGasInput` on a record of `ℛ^pre_k`

For a record `rec` of `ℛ^pre_k` (I.2 up to `k`), the large-field part of the output of `R` is
`keptLF rec data` (`keptRep` on every torus) for kept data `data` of the five outcomes at the scale
`k`.  `keptOutput_of_scaleData` proves the first conjunct of `RKeptGasInput` (histories complete at
`(k, k+1)`, the step data of the input) and `KeptOutput` (`D4Pin (k+1)`, `D5Bound (k+1)`,
`D6Budget`, `LFCoherent`) from the named residuals of `Spine/KeptHalf.lean`: the kept data
(`KeptScaleData`) and the datum clause of the torus coherence of their kernels (`KeptDatumCoh`); the
locality of `κ^pre_k` (`KappaPreLocal`, `kappaPreLocal_of_gam_indep`) and the torus coherence of the
output family (`lfCoherent_post`: the pinned exponent is coherent, `pinnedExp_corr`) are proved.  The signs `z_j > 0` and `β_j a L^{d-2} ≥ 0` (`j ≤ k`) come from the record, the
budget setup from the prefix (`budget_good_setup`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 RegionHistory

section Rec

variable (d N : ℕ) (T : ℝ → ℝ → Typing) (P6 : ℝ → ℝ → Def6.Consts)
  (C7 : ℝ → ℝ → Consts7) (PB : ℝ → ℝ → BudgetConsts) (cs₀ : ℝ → ℝ → OpConsts)
  (M1 c : ℝ → ℝ → ℕ) (rH ϱ : ℝ → ℝ → ℝ)

/-- **The large-field part of the output of `R`** of a record, from the kept data. -/
noncomputable abbrev keptLF {κ c₉ β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {kf k : ℕ}
    [NeZero (T κ c₉).L] [NeZero (T κ c₉).M]
    {ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]} {νk : ℝ}
    (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
      (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk)
    (data : ∀ (nK : ℕ) [NeZero nK], KeptScaleData (rec.F.lf nK)) :
    ∀ (nK : ℕ) [NeZero nK], Rep 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
      (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) (T κ c₉).M N
      (rec.geo nK) rec.cs rec.P k :=
  fun nK _ => keptRep (rec.F.lf nK) (data nK)

variable {d N T P6 C7 PB cs₀ M1 c rH ϱ}

/-- **The kept half of `RKeptGasInput` from its residuals.** For `β` large (the budget setup of the
prefix), a record `rec` of `ℛ^pre_k`, `1 ≤ k ≤ k₀`, kept data `data` of the five outcomes at the
scale `k` (on every torus) and their torus coherence (`KeptDatumCoh`):
the large-field part `keptLF rec data` has complete histories at `(k, k+1)`, the step data of the
input, and `KeptOutput`. -/
theorem keptOutput_of_scaleData {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ}
    (hκ : 0 < κ) {c₉ : ℝ} (hc₉ : 0 < c₉) :
    ∃ b : ℝ, ∀ β : ℝ, b ≤ β → ∀ ν : ℝ, ∀ (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
      [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (k : ℕ), 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk)
      (data : ∀ (nK : ℕ) [NeZero nK], KeptScaleData (rec.F.lf nK)),
      KeptDatumCoh
        (fun nK _ => keptExpOut (rec.F.lf nK) (canonHist 𝒮[d, T κ c₉, β, (cs₀ κ c₉).aKer]
          (sides (T κ c₉).L (kf + 1) nK) rec.R (kZero d (T κ c₉).L β ν) (kf + 1) k (k + 1)) k)
        (fun nK _ => (data nK).KD) →
      (∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1) (keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec data nK).hist ∧
        (keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec data nK).SD = (rec.F.lf nK).SD) ∧
      KeptOutput rec.hkK rec.F (keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec data) := by
  obtain ⟨b, hb⟩ := budget_good_setup hP hκ hc₉
  refine ⟨b, fun β hβ ν h kf _ _ k hk1 hk0 ρ νk rec data hdat => ?_⟩
  obtain ⟨hG, hB⟩ := hb β hβ
  have hz : ∀ j, j + 1 ≤ k → 0 < rec.cs.z (j + 1) := fun j hj => by
    rw [rec.pre.coh.z_cs _ hj]
    exact rec.zpos _ (by omega) hj
  have hbeta : ∀ j, j ≤ k → 0 < rec.cs.beta j := fun j hj => by
    rw [rec.pre.coh.beta_cs j hj]
    obtain ⟨γ, hγ, -, hj'⟩ := rec.run.beta_eq j hj
    rw [hj']
    have hL : (0 : ℝ) < (T κ c₉).L := by
      have := rec.run.hL; exact_mod_cast (by omega : 0 < (T κ c₉).L)
    have := rec.run.hβ
    positivity
  have hc' : ∀ j, j + 1 ≤ k → 0 ≤ rec.cs.beta j * rec.cs.aKer * ((T κ c₉).L : ℝ) ^ (d - 2) :=
    fun j hj => by
    have hL : (0 : ℝ) < (T κ c₉).L := by
      have := rec.run.hL; exact_mod_cast (by omega : 0 < (T κ c₉).L)
    have ha : 0 < rec.cs.aKer := by rw [rec.tie_aKer]; linarith [rec.run.ha1]
    have := hbeta j (by omega)
    positivity
  obtain ⟨B⟩ := hB rec.P ν rec.F.sf.ν k rec.tie_H0 rec.tie_c1 rec.tie_c2
    (runningHypTo_congr rec.run (fun j hj => rec.pre.coh.beta_P j hj) (fun _ _ => rfl))
  have hk0' : k ≤ kZero d (T κ c₉).L β ν := hk0
  have hkK := rec.hkK
  have hkK' : k ≤ kf + 1 := hkK
  refine ⟨fun nK _ => ⟨keptRep_complete _ _, keptRep_SD _ _⟩, fun nK _ => ?_,
    lfCoherent_post rec.coh data hk1 hkK' (fun nK _ => keptRep_pin_below (rec.F.lf nK) (data nK)
      (rec.pre.complete nK) (rec.pre.pin nK)) hdat⟩
  have hpin := keptRep_pin (rec.F.lf nK) (data nK) (rec.pre.complete nK) (rec.pre.pin nK)
    (kappaPreLocal_of_gam_indep _ _ hkK' fun i hi => (data nK).gam_indep_below hi)
  exact ⟨hpin, keptRep_opBound _ (data nK) hz hc' hkK',
    keptRep_budget _ (data nK) hpin hG B hk1 hk0' hkK'⟩

end Rec

end Balaban.RootFSpine
