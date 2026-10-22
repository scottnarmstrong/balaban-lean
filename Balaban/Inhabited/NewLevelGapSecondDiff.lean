/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelLabelGap
public import Balaban.SmallField.XiFourData

/-!
# The second differences at the composed data of a label (M3)

`composedChartP_second_diff`: on the composed chart whose sources have the scale gap `θ` with the
term generator `Gj`, the second differences of the field on the plaquettes of a layer of `Gj` are at
most `K_Σ θ^{2-θ'} ε` (`composeData_second_diff_of_xiCData`).  `composedChartGap_second_diff`: its
instance at the scale gap of the composition pair (`LabelGap`), `θ = L^j / L^k`, the constant `K₂`
of P1 (3.107) at the data the step reads.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField

variable {d L : ℕ} [NeZero L]

/-- **The second differences on the composed chart with a scale gap of the source** (P1 (3.107)):
if every source admitted by `Pr` has the scale gap `θ ∈ (0, 1]` with `Gj`, the field of every datum of
`composedChartP Pr Gj` has second differences at most `K_Σ θ^{2-θ'} ε` on the plaquettes of a layer
of `Gj`, for every exponent `θ' ∈ (0, 1)`. -/
theorem composedChartP_second_diff (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 → ∀ {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ θ : ℝ}
      {Pr : ∀ ϱ₁ : ℝ, GeneratingSet d L (N₁ * L ^ m₁) K ϱ₁ → Prop}
      {Gj : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a₁ ν : ℝ} {j : ℕ} {b ε : ℝ},
      0 < a₁ → (∀ ϱ₁ G, Pr ϱ₁ G → ScaleGap Gj G θ ∧ 0 < θ ∧ θ ≤ 1) →
      (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1 → xiC1 d * ε ≤ bgC1 d L N →
      ∀ r ∈ composedChartP (N := N) Pr Gj (compWeight L a₁) ν j b ε,
      ∀ {n : ℕ}, 1 ≤ n → n ≤ K →
        ∀ (e e' : Fin d) {x : Torus d ((N₁ * L ^ m₁) * L ^ K)}, x ∈ Gj.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) ∈ Gj.layer n →
        x + Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) ∈ Gj.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) +
          Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) ∈ Gj.layer n →
        ‖r.1 (x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K)) +
                Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) -
            r.1 (x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) -
            r.1 (x + Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ K))) + r.1 x‖ ≤
          xiSigma d L N B θh * θ ^ (2 - θh) * ε := by
  obtain ⟨B, hB0, hB⟩ := composeData_second_diff_of_xiCData (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N₁ m₁ K N _ ϱ θ Pr Gj a₁ ν j b ε ha₁ hPr hsm hc1 r hr n hn1 hnK e e' x h00
    h10 h01 h11
  obtain ⟨ϱ₁, G, hq, -, HB, hP, D, hD, -, rfl⟩ := hr
  obtain ⟨hgap, hθ0, hθ1⟩ := hPr ϱ₁ G hP
  exact hB hθh0 hθh1 hq ha₁ HB hgap hθ0 hθ1 hsm hc1 D hD hn1 hnK e e' h00 h10 h01 h11

/-- **The second differences at the composed data of a label** (P1 (3.107), M3): on the composed
chart whose source has the scale gap of the composition pair (`composedChartGap`), the second
differences of the field on the plaquettes of a layer of `Gj` are at most
`K_Σ (L^j / L^k)^{2-θ'} ε`.  The instance of `composedChartP_second_diff` at `θ = L^j / L^k`. -/
theorem composedChartGap_second_diff (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θh : ℝ}, 0 < θh → θh < 1 → ∀ {N₁ m₁ k N : ℕ} [NeZero N₁] {ϱ : ℝ}
      {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a₁ ν : ℝ} {j : ℕ} {b ε : ℝ},
      0 < a₁ → (4 * d + 6) * ((2 * d + 1) * ε) ≤ 1 → xiC1 d * ε ≤ bgC1 d L N →
      ∀ r ∈ composedChartGap (N := N) Gj (compWeight L a₁) ν j b ε,
      ∀ {n : ℕ}, 1 ≤ n → n ≤ k + 1 →
        ∀ (e e' : Fin d) {x : Torus d ((N₁ * L ^ m₁) * L ^ (k + 1))}, x ∈ Gj.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) ∈ Gj.layer n →
        x + Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) ∈ Gj.layer n →
        x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) +
          Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) ∈ Gj.layer n →
        ‖r.1 (x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1))) +
                Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
            r.1 (x + Pi.single e ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) -
            r.1 (x + Pi.single e' ((L ^ n : ℕ) : ZMod ((N₁ * L ^ m₁) * L ^ (k + 1)))) + r.1 x‖ ≤
          xiSigma d L N B θh * ((L : ℝ) ^ j / (L : ℝ) ^ k) ^ (2 - θh) * ε := by
  obtain ⟨B, hB0, hB⟩ := composedChartP_second_diff (d := d) (L := L) hd hL
  refine ⟨B, hB0, ?_⟩
  intro θh hθh0 hθh1 N₁ m₁ k N _ ϱ Gj a₁ ν j b ε ha₁ hsm hc1 r hr n
  have hP : ∀ (ϱ₁ : ℝ) (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁), LabelGap G Gj j →
      ScaleGap Gj G ((L : ℝ) ^ j / (L : ℝ) ^ k) ∧ 0 < (L : ℝ) ^ j / (L : ℝ) ^ k ∧
        (L : ℝ) ^ j / (L : ℝ) ^ k ≤ 1 :=
    fun _ _ h => ⟨h.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2⟩
  exact hB hθh0 hθh1 ha₁ hP hsm hc1 r hr

end Balaban.Inhabited
