/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassDensityIrrelStepChart
public import Balaban.Fluctuation.StepActivityClassChart

/-!
# The radius room of the composed step data (`LocalClassDensityIrrelStepRoom`)

At the composition constant `b = 1` the composed step data of a label (the data
`D2raw Gk Gj a Fk (d1Triple Gp Gk Hm a t)` of the realizable triples `t`) lie in the data domain
`Ξ^c_j(𝔹_j(X); 1, ε)` (`XiDom`) as soon as `ε' + K₂δ₃ + K₂δ_fl ≤ ε`, `ε'` the radius of the step
chart: no constant multiplies `ε'` (`d2raw_d1Triple_mem_xiDom`).  This is the room condition of
the class chain in the form in which the source pays it (WIDEGEN, W1040 (B)): with the step radius
`ε' = ε_{k+1}` and `ε_{k+1} ≤ L^{-α} ε_k ≤ L^{-α} ε_j` (`j ≤ k`) it leaves the margin
`(1 - L^{-α}) ε_j` for the corrections `K₂(δ₃ + δ_fl)`, also at `L = 3`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Localization Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
  {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {a₁ ν c BG κ r₀ eps δ₃ : ℝ} {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
  {Kc Cx c₂ BG₂ δ₁ δfl : ℝ}

/-- **The composed step data lie in the data domain of the class level with no radius loss.**
For a realizable triple `t` with layer-constant fluctuation, the composed datum of `𝔹_j(X)` lies in
`Ξ^c_j(𝔹_j(X); 1, ε)` (`XiDom`) whenever `ε' + K₂δ₃ + K₂δ_fl ≤ ε`, `ε'` the radius of the step
chart (composition constant `b = 1` in `d2raw_d1Triple_mem_xiCRaw`). -/
theorem d2raw_d1Triple_mem_xiDom
    (hB : BgSetting N Gp Gk Gj a₁ ν c BG κ r₀ eps δ₃ X₀ X₁f j)
    (hF : FlSetting N Gp Gk Hm a₁ ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl X₁f)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))}
    (ht : t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) {ε : ℝ}
    (hε : eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl ≤ ε) :
    XiDom Gj (compWeight L a₁) ν j ε
      (D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2)).1
      (D2raw Gk Gj (compWeight L a₁) Fk
        (d1Triple Gp Gk Hm (compWeight L a₁) t.1.1 t.2.1 t.2.2)).2 := by
  obtain ⟨D, hD, hr⟩ := d2raw_d1Triple_mem_xiCRaw (b := 1) le_rfl (one_le_scaledC0 d) hB hF hFk ht
  rw [hr]
  exact xiDom_of_xiCData_of_one_le le_rfl (by simpa using hε) hD

end Balaban.Fluctuation
