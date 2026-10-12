/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31a
public import Balaban.Polymer.MayerPE
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The partition function `Z_{s,t}` of the step as a polymer integral

(COMPLETE-STEP §2, (2.1), and §5 row 6.)  If the exponent `W₁(s,ψ̂) + W₂(t,ψ̂; g)` of the
interpolating measure is, `ν_{p₁}`-almost everywhere, a sum of block-local label activities
(`LabelAct` of the marked expansion) and `ν_{p₁}` splits as a product of block measures
(`BlockSplit`), then
* `Zst_eq_integral_pi`: `Z_{s,t}` is the integral `∫ exp (∑_y H(y; Φ)) d⨂_b ν_b`;
* `Zst_eq_polymerPartition`: `Z_{s,t}` is the polymer partition function `Ξ` (`Polymer.Xi`) of the
  Mayer activities `mayerK` of the pre-summed activities `H̃(S)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.SmallField.Def6 MeasureTheory

section Id

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
  (g : Fld d L N₁ m₁ (k + 1) N) {m₀ : ℕ} (BS : BlockSplit S m₀)

/-- **`Z_{s,t}` is the product-measure integral of the exponentiated block activities.** -/
theorem StepSetting.Zst_eq_integral_pi {Lb : Type*} [Fintype Lb] (H : Lb → (∀ b, BS.Ωb b) → ℂ)
    (hHm : ∀ y, Measurable (H y)) (s t : ℝ)
    (hW : ∀ᵐ x ∂S.nuFl, S.Wone C s x + S.Wtwo C g t x = ∑ y, H y (BS.restr x)) :
    S.Zst C g s t = ∫ Φ, Complex.exp (∑ y, H y Φ) ∂(Measure.pi BS.μ) := by
  have hmeas : Measurable (fun Φ : ∀ b, BS.Ωb b => Complex.exp (∑ y, H y Φ)) :=
    Complex.measurable_exp.comp (Finset.measurable_sum _ fun y _ => hHm y)
  rw [← BS.map_eq, integral_map BS.meas.aemeasurable hmeas.aestronglyMeasurable]
  unfold StepSetting.Zst partFun₂
  refine integral_congr_ae ?_
  filter_upwards [hW] with x hx
  rw [hx]

open Classical in
/-- **`Z_{s,t}` is the polymer partition function of the block activities**: the integral equals
`Ξ` of the Mayer activities of the pre-summed (one per support) terms. -/
theorem Zst_eq_polymerPartition (hN : L ^ m₀ ∣ N₁)
    {Lb : Type} [Fintype Lb] {Lab : CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
      m₀ (k + 1) Set.univ Lb} {εH κH κ0 Kc : ℝ} (A : LabelAct Lab BS.Ωb εH κH κ0 Kc)
    (hεpos : 0 < εH) (hκ : κ0 ≤ κH) (hKc : 1 ≤ Kc) (s t : ℝ)
    (hW : ∀ᵐ x ∂S.nuFl, S.Wone C s x + S.Wtwo C g t x = ∑ y, A.H y (BS.restr x)) :
    S.Zst C g s t = Xi (shareBlock (Subtype.val : NePoly (CubeB (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) → Finset _))
      (mayerK BS.μ (Subtype.val : NePoly (CubeB (d := d) (L := L) (N₁ := N₁)
        (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ) → Finset _) (presum Lab A.H)) := by
  have hΩ : IsPiUnion m₀ (k + 1) (Set.univ : Set (CTorus d L N₁ m₁ (k + 1))) :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ (k + 1)) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ (k + 1)) z, Set.subset_univ _⟩
  rw [StepSetting.Zst_eq_integral_pi S C g BS A.H A.meas s t hW]
  have hsum : ∀ Φ : ∀ b, BS.Ωb b, ∑ y, A.H y Φ = ∑ T, presum Lab A.H T Φ := fun Φ =>
    (presum_sum Lab hN le_rfl hΩ A.H Φ).symm
  simp_rw [hsum]
  refine mayer_integral_eq BS.μ (fun T => T.2) (fun T => A.presum_dep T)
    (fun T => A.presum_meas T) (fun T => ⟨εH * Kc, fun Φ => ?_⟩)
  refine (A.presum_bound hN le_rfl hΩ hεpos.le hκ T Φ).trans ?_
  have h1 : Real.exp (-(κH - κ0) * dExt T.1) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [dExt_nonneg T.1])
  have h0 : 0 ≤ εH * Kc := by positivity
  nlinarith

end Id

end Balaban.Fluctuation
