/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomPatchGeom
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The small-polymer class-chart comparison

The inverse-rotated full field and the rotated polydisc field both lie in the class chart at
the term's mass. The existing `CRotE` bridge then identifies the class term with its tube
extension at the local datum.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- The tube extension equals the class term when the datum in the real-centre frame is
locally within the spin radius and its field coordinates satisfy the source tube estimates. -/
theorem trickFnA_shiftTerm_eq_of_local_bounds
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hcr : CRotE P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hν : 0 < ν)
    (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hS : ∀ z ∈ X, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S)
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    (c : Cfg d N S) (hc : c ∈ TubeAniso i₀ ν r S)
    (hlocal : ∀ z, unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (z - y) ∈ S →
      ∀ i, ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) i -
        (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hb : ∀ i, ‖c (Sum.inr i) - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖c (Sum.inr i₀) - (ν : ℂ)‖ < r ^ 2) :
    trickFnA i₀ ν r (fun c' : Cfg d N S =>
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c' (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c')) c =
      Tm.E j y X
        (fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y))
        (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) := by
  obtain ⟨R, hR, hRb, hRc⟩ := tubeAniso_witness_isCRot hne hc
  let Ψ₂ : Fld d L N₁ m₁ k N := fun z => fieldOf (L := L) (N₁ := N₁)
    (m₁ := m₁) (k := k) j i₀ S (rotCfgL R S c) (z - y)
  let Ψ₁ : Fld d L N₁ m₁ k N := rotField R.transpose Ψ₂
  have hy0 : unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (y - y) ∈ S := hS y hyX
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have hB0 : 0 ≤ rotB N := by unfold rotB; positivity
  let ρs : ℝ := r * (1 + N * rotB N)
  have hρs0 : 0 ≤ ρs := by dsimp [ρs]; positivity
  have hρ : r ≤ ρs := by
    dsimp [ρs]
    nlinarith [mul_nonneg hr0.le (mul_nonneg (Nat.cast_nonneg N) hB0)]
  have hδr : r < δ := by
    have hN4 : (1 : ℝ) < 4 * N := by nlinarith
    nlinarith [mul_nonneg (by linarith : 0 ≤ (4 : ℝ) * N - 1) hρs0]
  have hρh : 2 * N * r ≤ δ := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (2 : ℝ) * N)
      (sub_nonneg.mpr hρ)]
  have hρl : r ^ 2 < δ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hδr) (by linarith : 0 < δ + r)]
  have hXi₂ : XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ₂
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (rotCfgL R S c)) := by
    exact xiDom_shift_poly hBg (hcl.gs_spec j hj1 hjk X hX).2 hjk hν hμν i₀ hy
      hδ0 hδc0 hδc1 hr0 hr1 (by
        nlinarith [mul_nonneg (by positivity : 0 ≤ (4 : ℝ) * N)
          (sub_nonneg.mpr hρ)]) hε hRc
  have hΨ₁ : ∀ z i, ‖Ψ₁ z i - (Pi.single i₀ 1 : Spin N) i‖ ≤ ρs :=
    inverse_rotated_field_close hr0.le hR.1 hRb hRc hy0 hlocal
  have hΨ₁b : ∀ z z', jBlock d L (N₁ * L ^ m₁) k j z =
      jBlock d L (N₁ * L ^ m₁) k j z' → Ψ₁ z = Ψ₁ z' := by
    intro z z' heq
    change R.transpose.mulVec (Ψ₂ z) = R.transpose.mulVec (Ψ₂ z')
    congr 1
    exact shiftField_block hjk hy (rotCfgL R S c) heq
  have hXi₁ : XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ₁
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) := by
    exact xiDom_of_fieldM hBg (hcl.gs_spec j hj1 hjk X hX).2 hjk hν hμν i₀
      hδ0 hδc0 hδc1 hρs0 hr0.le hrδ hρh hρl hε Ψ₁
      (fun i => c (Sum.inr i)) hΨ₁ hΨ₁b hb hbl.le
  have hrotΨ : Ψ₂ = rotField R Ψ₁ := by
    funext z i
    change Ψ₂ z i = (R.mulVec (R.transpose.mulVec (Ψ₂ z))) i
    rw [Matrix.mulVec_mulVec, isOrth_mul_transpose hR.1, Matrix.one_mulVec]
  have hroth : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (rotCfgL R S c) =
      rotField R (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) :=
    hOf_rot ν R c
  have hag₁ : ∀ z ∈ X,
      Ψ₁ z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S c (z - y) ∧
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c) z =
        hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S c z := by
    intro z hz
    refine ⟨?_, rfl⟩
    have hrot := fieldOf_rot (j := j) (i₀ := i₀) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) R c (hS z hz)
    change Ψ₂ z = R.mulVec (fieldOf j i₀ S c (z - y)) at hrot
    change R.transpose.mulVec (Ψ₂ z) = _
    rw [hrot, Matrix.mulVec_mulVec, hR.1, Matrix.one_mulVec]
  have hag₂ : ∀ z ∈ X,
      Ψ₂ z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
        (rotCfgL R S c) (z - y) ∧
      (hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (rotCfgL R S c)) z =
        hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (rotCfgL R S c) z := by
    intro z hz
    exact ⟨rfl, rfl⟩
  exact trickFnA_shiftTerm_eq_of_full_chart_rot hcl hcr hBg hν hμν hj1 hjk hy hX hyX
    hS hne ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ c R hR hRb hRc
    Ψ₁ (hOf ν S c) Ψ₂ (hOf ν S (rotCfgL R S c)) hXi₁ hXi₂ hrotΨ hroth hag₁ hag₂

end Balaban.SmallField.Def6v2
