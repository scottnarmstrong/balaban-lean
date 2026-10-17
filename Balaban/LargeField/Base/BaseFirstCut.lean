module

public import Balaban.LargeField.Base.BaseFirstChartIntegral
public import Balaban.LargeField.Base.BaseChartComponentGauss
public import Balaban.LargeField.Base.BaseChartHessian

/-!
# The local first cut on record-supported background data

The background multiplier bounds use the local spin support, so they apply even if the
first record has failed cubes outside its good region.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix Classical

/-- The local background multiplier satisfies the base resolvent threshold on record-supported
data. -/
theorem baseFirstCut_multiplier_bound
    {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ ν δ₀ : ℝ}
    (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ)
    (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    (D : BgData G N) (H : BgHyp d L 1 ϱ a ν)
    (S : BaseSpinSupport G ν δ₀ φ h D)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N) (x : G.Ω 1) :
    ‖bgMult G a ν D x‖ ≤ 1 / (8 * (L : ℝ) ^ 2) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hsmall : 4 * d * L * δ₀ ≤ 1 / 1024 :=
    (approxDelta_le d L (bgC1_facts d L N hd0 hΛ1).1).1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  have hδpos : 0 < 4 * d * L * δ₀ := by
    have := S.delta_pos
    positivity
  have hU : InUnionDomainR G (bgC1 d L N) ν D :=
    ⟨4 * d * L * δ₀, hδpos, hΛ1, inDomainR_base H S hsmall⟩
  obtain ⟨δ, hδ0, hδc, hDδ⟩ := hU
  have hb := ((theorem71 (G := G) H ⟨δ, hδ0, hδc, hDδ⟩).2.2.2.2)
    δ hδ0 hδc hDδ
  have hc := (bgC1_facts d L N hd0 hδc).2.2.2
  have hbound : bgK1 d L N * δ ≤ 1 / 32 := by
    have := bgC0_le d L N
    linarith
  have hs : (L : ℝ) ^ 2 * ‖bgMult G a ν D x‖ ≤ 1 / 32 := by
    have hs' := hb.alpha x
    rw [spacing_one G x.property] at hs'
    exact hs'.trans hbound
  have hL : 0 < (L : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne L))
  have hsq : 0 < (L : ℝ) ^ 2 := pow_pos hL _
  calc
    ‖bgMult G a ν D x‖ ≤ (1 / 8 : ℝ) / (L : ℝ) ^ 2 :=
      (le_div_iff₀ hsq).2 (by nlinarith [hs])
    _ = 1 / (8 * (L : ℝ) ^ 2) := by ring

/-- The local multiplier is real when the selected record supplies real spin support. -/
theorem baseFirstCut_multiplier_real
    {d L N₀ N : ℕ} [NeZero N₀] [NeZero L] {ϱ ν δ₀ : ℝ}
    (G : GeneratingSet d L N₀ 1 ϱ) (a : ℕ → ℝ)
    (φ : Torus d (N₀ * L ^ 1) → Fin N → ℝ) (h : Fin N → ℝ)
    (D : BgData G N) (H : BgHyp d L 1 ϱ a ν)
    (S : BaseSpinSupport G ν δ₀ φ h D)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N) (x : G.Ω 1) :
    (bgMult G a ν D x).im = 0 := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hsmall : 4 * d * L * δ₀ ≤ 1 / 1024 :=
    (approxDelta_le d L (bgC1_facts d L N hd0 hΛ1).1).1
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
  have hδpos : 0 < 4 * d * L * δ₀ := by
    have := S.delta_pos
    positivity
  have hU : InUnionDomainR G (bgC1 d L N) ν D :=
    ⟨4 * d * L * δ₀, hδpos, hΛ1, inDomainR_base H S hsmall⟩
  obtain ⟨δ, hδ0, hδc, hDδ⟩ := hU
  obtain ⟨φb, α, hs, _, hu, _, hmin, huniq⟩ := bg_real (G := G) H hδ0 hδc hDδ
  have hreal : D.IsReal := isReal_of_inDomainR hDδ
  have hc := (hu _ _ (isSmallSolution_conj D hreal hs)).2
  have hf : bgField G a ν D = φb := bgField_eq hmin huniq
  have hm : bgMult G a ν D = α := by
    funext y
    unfold bgMult
    rw [hf]
    exact mult_formula hs.1 y
  rw [hm, ← Complex.conj_eq_iff_im]
  exact congrFun hc x

end Balaban.LargeField
