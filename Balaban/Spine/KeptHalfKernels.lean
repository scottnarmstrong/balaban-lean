/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KeptHalfRec
public import Balaban.Spine.KeptParts

/-!
# The kept half of `RKeptGasInput` from the kernels of the five outcomes

`keptOutput_of_kernels` is `keptOutput_of_scaleData` with the kept data of the output built from the
kernels of the five outcomes at the scale `k` (`KeptScaleData.ofKernels`).  The residuals of the
kept half are then the structure `KeptScaleKernels` at the scale `k` (the five kernels and their
bound (1.26) at the pinned exponent, the covariances) and its datum coherence; the kept costs of
the input are the constants `γ_i` by the class invariant `PreRec.gamVal`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2
  Balaban.SmallField Balaban.SmallField.Def6 RegionHistory

section Rec

variable {d N : ℕ} {T : ℝ → ℝ → Typing} {P6 : ℝ → ℝ → Def6.Consts}
  {C7 : ℝ → ℝ → Consts7} {PB : ℝ → ℝ → BudgetConsts} {cs₀ : ℝ → ℝ → OpConsts}
  {M1 c : ℝ → ℝ → ℕ} {rH ϱ : ℝ → ℝ → ℝ}

/-- **The kept half of `RKeptGasInput` from the kernels of the five outcomes at the scale `k`.** -/
theorem keptOutput_of_kernels {δ : ℝ} (hP : PrefixInput d δ T P6 C7 PB cs₀ M1 c ϱ) {κ : ℝ}
    (hκ : 0 < κ) {c₉ : ℝ} (hc₉ : 0 < c₉) :
    ∃ b : ℝ, ∀ β : ℝ, b ≤ β → ∀ ν : ℝ, ∀ (h : EuclideanSpace ℝ (Fin N)) (kf : ℕ)
      [NeZero (T κ c₉).L] [NeZero (T κ c₉).M] (k : ℕ), 1 ≤ k → k ≤ kZero d (T κ c₉).L β ν →
      ∀ (ρ : 𝒟[d, N, T κ c₉, β, (cs₀ κ c₉).aKer, kf + 1, k]) (νk : ℝ)
      (rec : PreRec d N (T κ c₉) (P6 κ c₉) (C7 κ c₉) (PB κ c₉) (cs₀ κ c₉) (M1 κ c₉) (c κ c₉)
        (rH κ c₉) (ϱ κ c₉) β ν h kf k k ρ νk)
      (Ks : ∀ (nK : ℕ) [NeZero nK], KeptScaleKernels (rec.F.lf nK)),
      KeptDatumCohAt (K := kf + 1) (M := (T κ c₉).M) (R := rec.R) (k0 := kZero d (T κ c₉).L β ν)
        k (fun nK _ a ϰ => (Ks nK).datum a ϰ) →
      (∀ (nK : ℕ) [NeZero nK], IsComplete k (k + 1)
          (keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec
            (fun nK _ => KeptScaleData.ofKernels (rec.F.lf nK) (fun i _ l => rec.gamVal nK i l) (Ks nK)) nK).hist ∧
        (keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec
          (fun nK _ => KeptScaleData.ofKernels (rec.F.lf nK) (fun i _ l => rec.gamVal nK i l) (Ks nK)) nK).SD =
            (rec.F.lf nK).SD) ∧
      KeptOutput rec.hkK rec.F (keptLF d N T P6 C7 PB cs₀ M1 c rH ϱ rec
        (fun nK _ => KeptScaleData.ofKernels (rec.F.lf nK) (fun i _ l => rec.gamVal nK i l) (Ks nK))) := by
  obtain ⟨b, hb⟩ := keptOutput_of_scaleData hP hκ hc₉
  refine ⟨b, fun β hβ ν h kf _ _ k hk1 hk0 ρ νk rec Ks hKs => ?_⟩
  exact hb β hβ ν h kf k hk1 hk0 ρ νk rec
    (fun nK _ => KeptScaleData.ofKernels (rec.F.lf nK) (fun i _ l => rec.gamVal nK i l) (Ks nK))
    (keptDatumCoh_of_kernels rec.coh (fun nK _ i _ l => rec.gamVal nK i l) Ks hKs)

end Rec

end Balaban.RootFSpine
