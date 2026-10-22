/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusStepGeometry
public import Balaban.Polymer.TwoTorusThickSets
public import Balaban.SmallField.GsSpecHat

/-!
# The boxes `□(y)` and the sets `X̂` under `boxMap`

`image_cubeAt_boxMap`: the image of the box `box (cbase a y - ⌊·⌋) s` through a site `y` of the
centred box is the same box through `boxMap y`.  `hatSet_boxMap`, `polySet`-type unions follow.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer Balaban.Polymer.TwoTorusStep
  Balaban.SmallField Balaban.SmallField.GsSpec

section Img

variable {d n n' : ℕ} [NeZero n] [NeZero n']

theorem image_cubeAt_boxMap {a h s R : ℕ} (ha0 : 0 < a) (hdn : a ∣ n) (hdn' : a ∣ n')
    (hh : h + a ≤ s) (hn : 2 * (R + 2 * s) + s + 1 < n) {y : Torus d n} (hy : InBox d R n y) :
    boxMap n n' '' box (cbase a y - natT fun _ => h) s =
      box (cbase a (boxMap n n' y) - natT fun _ => h) s := by
  set c := cbase a y with hc
  set c' : Torus d n := c - natT fun _ => h with hc'
  -- `y` lies in the box
  have hyb : y ∈ box c' s := by
    refine ⟨fun μ => h + (y μ).val % a, fun μ => ?_, ?_⟩
    · have := Nat.mod_lt (y μ).val ha0
      show h + (y μ).val % a < s
      omega
    · funext μ
      simp only [hc', hc, Pi.add_apply, Pi.sub_apply, natT_apply, cbase_eq_sub]
      push_cast
      ring
  have hs0 : 0 < s := by omega
  have hbR : InBox d (R + s) n c' := inBox_of_mem_box_left (by omega) hy hyb
  have hbox : ∀ z ∈ box c' s, InBox d (R + s + s) n z := fun z hz =>
    inBox_of_mem_box_right (by omega) hbR hz
  have himg := image_box_boxMap (n' := n') (r := R + s + s) (by omega) hs0 hbox
  rw [himg]
  congr 1
  -- the base point
  have hcR : InBox d (R + a) n c :=
    inBox_of_mem_cell (by omega) hy (mem_box_self (cbase a y) ha0)
  have hcc' : c' + natT (fun _ => h) = c := by
    simp only [hc']; abel
  have hbw : InBox d (R + s + s) n (c' + natT fun _ => h) := by
    rw [hcc']; exact inBox_mono (by omega) hcR
  have hadd := boxMap_add_natT (n' := n') (r := R + s + s) (a := h + 1) (by omega)
    (b := c') (w := fun _ => h) (fun _ => by omega) (inBox_mono (by omega) hbR) hbw
  rw [hcc'] at hadd
  have hcb := cbase_boxMap (n' := n') (a := a) (r := R + s + s) hdn hdn' ha0 (by omega) y
    (fun z hz => inBox_mono (by omega) (inBox_of_mem_cell (by omega) hy hz))
  rw [← hc] at hcb
  funext μ
  have := congrFun hadd μ
  have hcbμ := congrFun hcb μ
  simp only [Pi.add_apply, natT_apply] at this
  simp only [hc', Pi.sub_apply, natT_apply]
  rw [hcbμ] at this
  linear_combination -this

/-- The site lies in the box through its own cell base (`h + a ≤ s`). -/
theorem mem_cubeAt_box {a h s : ℕ} (ha0 : 0 < a) (hh : h + a ≤ s) (y : Torus d n) :
    y ∈ box (cbase a y - natT fun _ => h) s := by
  refine ⟨fun μ => h + (y μ).val % a, fun μ => ?_, ?_⟩
  · have := Nat.mod_lt (y μ).val ha0
    show h + (y μ).val % a < s
    omega
  · funext μ
    simp only [Pi.add_apply, Pi.sub_apply, natT_apply, cbase_eq_sub]
    push_cast
    ring

/-- **The box through a site of the box of radius `R` lies in the box of radius `R + 2 s`.** -/
theorem inBox_of_cubeAt {a h s R : ℕ} (ha0 : 0 < a) (hh : h + a ≤ s)
    (hn : 2 * (R + 2 * s) + 1 < n) {y z : Torus d n} (hy : InBox d R n y)
    (hz : z ∈ box (cbase a y - natT fun _ => h) s) : InBox d (R + s + s) n z :=
  inBox_of_mem_box_right (by omega)
    (inBox_of_mem_box_left (by omega) hy (mem_cubeAt_box ha0 hh y)) hz

end Img

section Sets

variable {d L N₁ N₂ m₁ k : ℕ} [NeZero L] [NeZero N₁] [NeZero N₂]

/-- **`X̂` of the image is the image of `X̂`.** -/
theorem hatSet_boxMap {m₀ j : ℕ} (hN : L ^ m₀ ∣ N₁) (hN' : L ^ m₀ ∣ N₂) (hjk : j ≤ k)
    {R : ℕ} {X : Set (CTorus d L N₁ m₁ k)}
    (hX : ∀ y ∈ X, InBox d R ((N₁ * L ^ m₁) * L ^ k) y)
    (hn : 2 * (R + 2 * ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j)) +
      (2 * (L / 2) + 1) * cellSide L m₀ m₁ j + 1 < (N₁ * L ^ m₁) * L ^ k) :
    hatSet m₀ j (boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k) '' X) =
      boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k) '' hatSet m₀ j X := by
  have hd1 := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₁) hN hjk
  have hd2 := cellSide_dvd (K := k) (m₁ := m₁) (L := L) (N₁ := N₂) hN' hjk
  have ha0 := cellSide_pos (L := L) m₀ m₁ j
  have hh : L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j ≤
      (2 * (L / 2) + 1) * cellSide L m₀ m₁ j := by
    have : L / 2 * cellSide L m₀ m₁ j + cellSide L m₀ m₁ j = (L / 2 + 1) * cellSide L m₀ m₁ j := by ring
    rw [this]
    exact Nat.mul_le_mul_right _ (by omega)
  have key : ∀ y ∈ X, boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k) ''
      Localization.box (cbase (cellSide L m₀ m₁ j) y - natT fun _ => L / 2 * cellSide L m₀ m₁ j)
        ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j) =
      Localization.box (cbase (cellSide L m₀ m₁ j)
          (boxMap ((N₁ * L ^ m₁) * L ^ k) ((N₂ * L ^ m₁) * L ^ k) y) -
        natT fun _ => L / 2 * cellSide L m₀ m₁ j) ((2 * (L / 2) + 1) * cellSide L m₀ m₁ j) :=
    fun y hy => image_cubeAt_boxMap ha0 hd1 hd2 hh hn (hX y hy)
  ext z
  constructor
  · rintro ⟨y', ⟨y, hy, rfl⟩, hz⟩
    rw [← key y hy] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    exact ⟨w, ⟨y, hy, hw⟩, rfl⟩
  · rintro ⟨w, ⟨y, hy, hw⟩, rfl⟩
    exact ⟨_, ⟨y, hy, rfl⟩, by rw [← key y hy]; exact ⟨w, hw, rfl⟩⟩

end Sets

end Balaban.Inhabited
