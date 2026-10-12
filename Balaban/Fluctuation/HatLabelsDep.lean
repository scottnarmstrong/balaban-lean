/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsSplit
public import Balaban.Fluctuation.HatLabelsGeom
public import Balaban.Fluctuation.InteractionHatV
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The hat variable as a function of the block variables

The block variable of the `π_{k+1}`-cube `b` is the family of the fluctuation variables at the
unit points of `b` (`StepSetting.blockSplit`).  The hat variable `ψ̂ ∈ ℂ^{T^{(k)}_1 × [N]}` of the
expansion of Proposition 3.3 is recovered from the block variables (`StepSetting.hatOf`), after a
pointwise radial projection onto the closed disk `|ψ̂(u)_i| ≤ ρ` (`clampC`), which is the identity
on the support of `ν_{p₁}` for `p₁ ≤ ρ`.  The locality of a term under `AgHatF Y` (agreement at the
unit points of `blockThick Y`) becomes dependence on the block variables of the cubes inside the
thickening `Z` of `Y` (`thick_spec`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer

section Clamp

/-- Radial projection of `z ∈ ℂ` onto the closed disk of radius `ρ`. -/
noncomputable def clampC (ρ : ℝ) (z : ℂ) : ℂ := z / ((max 1 (‖z‖ / ρ) : ℝ) : ℂ)

theorem clampC_of_le {ρ : ℝ} (hρ : 0 < ρ) {z : ℂ} (h : ‖z‖ ≤ ρ) : clampC ρ z = z := by
  have : max 1 (‖z‖ / ρ) = 1 := max_eq_left ((div_le_one hρ).2 h)
  simp [clampC, this]

theorem norm_clampC_le {ρ : ℝ} (hρ : 0 < ρ) (z : ℂ) : ‖clampC ρ z‖ ≤ ρ := by
  have h1 : (1 : ℝ) ≤ max 1 (‖z‖ / ρ) := le_max_left _ _
  have h0 : (0 : ℝ) < max 1 (‖z‖ / ρ) := by linarith
  unfold clampC
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h0.le, div_le_iff₀ h0]
  have : ‖z‖ / ρ ≤ max 1 (‖z‖ / ρ) := le_max_right _ _
  rw [div_le_iff₀ hρ] at this
  linarith

theorem continuous_clampC (ρ : ℝ) : Continuous (clampC ρ) := by
  unfold clampC
  refine continuous_id.div (Complex.continuous_ofReal.comp
    (continuous_const.max (continuous_norm.div_const ρ))) fun z => ?_
  have h1 : (1 : ℝ) ≤ max 1 (‖z‖ / ρ) := le_max_left _ _
  exact_mod_cast (by linarith : max 1 (‖z‖ / ρ) ≠ 0)

end Clamp

section Hat

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ)

open Classical in
/-- **The hat variable of the block variables**: the coordinates of the block variable of the cube
containing the unit point `u`, projected onto the disk of radius `ρ`. -/
noncomputable def StepSetting.hatOf (ρ : ℝ) (hp : 0 < S.p₁)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : S.U × Fin N → ℂ :=
  fun q => clampC ρ ((Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩ q.2 : ℝ) : ℂ)

/-- The complexification of a real fluctuation field. -/
noncomputable def StepSetting.hatC (x : S.E) : S.U × Fin N → ℂ := fun q => ((x q.1 q.2 : ℝ) : ℂ)

theorem StepSetting.hatOf_restr {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < S.p₁) (x : S.E)
    (hx : ∀ u, ‖x u‖ ≤ ρ) : S.hatOf m₀ ρ hp ((S.blockSplit m₀ hp).restr x) = S.hatC x := by
  funext q
  unfold StepSetting.hatOf StepSetting.hatC
  refine clampC_of_le hρ ?_
  rw [Complex.norm_real]
  exact (PiLp.norm_apply_le (x q.1) q.2).trans (hx q.1)

/-- The disk of hat variables `|ψ̂(u)_i| ≤ ρ`. -/
def hatDisk (U : Type) (N : ℕ) (ρ : ℝ) : Set (U × Fin N → ℂ) := {ψ | ∀ p, ‖ψ p‖ ≤ ρ}

theorem StepSetting.hatOf_mem {ρ : ℝ} (hρ : 0 < ρ) (hp : 0 < S.p₁)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) : S.hatOf m₀ ρ hp Φ ∈ hatDisk S.U N ρ :=
  fun _ => norm_clampC_le hρ _

/-- The hat variable of the block variables is measurable (as a map into the disk). -/
theorem StepSetting.measurable_hatOf (ρ : ℝ) (hρ : 0 < ρ) (hp : 0 < S.p₁) :
    Measurable (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      (⟨S.hatOf m₀ ρ hp Φ, S.hatOf_mem m₀ hρ hp Φ⟩ : hatDisk S.U N ρ)) := by
  refine Measurable.subtype_mk (Measurable.of_eval fun q => ?_)
  have hc : Measurable (clampC ρ) := (continuous_clampC ρ).measurable
  refine hc.comp (Complex.measurable_ofReal.comp ?_)
  have h1 : Measurable (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
      Φ (S.cellOf m₀ q.1) ⟨q.1, rfl⟩) :=
    (measurable_pi_apply (⟨q.1, rfl⟩ : {u : S.U // S.cellOf m₀ u = S.cellOf m₀ q.1})).comp
      (measurable_pi_apply (S.cellOf m₀ q.1))
  exact (EuclideanSpace.proj q.2).continuous.measurable.comp h1

theorem cubeOfSite_eq_of_jBlock_eq {x x' : CTorus d L N₁ m₁ (k + 1)}
    (h : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x = jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x') :
    cubeOfSite m₀ x = cubeOfSite m₀ x' := by
  refine Subtype.ext (funext fun i => ?_)
  have hℓ : N₁ * L ^ m₁ * L ^ (k + 1) = L ^ (k + 1) * (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) :=
    side_eq (N₀ := N₁ * L ^ m₁) (L := L) (k := k + 1) (j := k + 1) le_rfl
  have h1 := (blockMap_eq_iff_val hℓ x x').1 h i
  have hcs : cellSide L m₀ m₁ (k + 1) = L ^ (k + 1) * L ^ (m₀ + m₁) := by
    unfold cellSide; rw [← pow_add]; congr 1; ring
  have h2 : (x i).val / cellSide L m₀ m₁ (k + 1) = (x' i).val / cellSide L m₀ m₁ (k + 1) := by
    rw [hcs, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, h1]
  simp only [cubeOfSite, cbase]
  rw [h2]

/-- **Locality in the hat variable becomes dependence on the block variables of the thickening.**
If the cube of every site of `psiThick Y` lies in `Z`, then `AgHatF Y` holds for the hat variables
of two block configurations that agree on the cubes inside `Z`. -/
theorem StepSetting.agHatF_hatOf {Y Z : Set (CTorus d L N₁ m₁ (k + 1))}
    (hZ : ∀ y ∈ psiThick Y, box (cbase (cellSide L m₀ m₁ (k + 1)) y) (cellSide L m₀ m₁ (k + 1)) ⊆ Z)
    (ρ : ℝ) (hp : 0 < S.p₁) (Φ Φ' : ∀ b, (S.blockSplit m₀ hp).Ωb b)
    (h : ∀ b ∈ blocksOf m₀ (k + 1) Set.univ Z, Φ b = Φ' b) :
    AgHatF S.G' S.hG' Y (S.hatOf m₀ ρ hp Φ) (S.hatOf m₀ ρ hp Φ') := by
  intro y hy i
  obtain ⟨y₂, hy₂, hyy₂⟩ := hy
  have hcube : S.cellOf m₀ (unitPt S.hG' y) ∈ blocksOf m₀ (k + 1) Set.univ Z := by
    rw [S.cellOf_unitPt, cubeOfSite_eq_of_jBlock_eq m₀ hyy₂]
    exact mem_blocksOf.2 (hZ y₂ hy₂)
  have := h _ hcube
  simp only [StepSetting.hatOf]
  rw [this]

end Hat

end Balaban.Fluctuation
