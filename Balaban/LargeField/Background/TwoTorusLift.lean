/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.Coherence

/-!
# Integer lifts of two tori on a common box

Points of the tori `𝕋_{m₁}`, `𝕋_{m₂}` are compared through integer vectors: `zcast m w` is the
point of `𝕋_m` with integer representative `w`. On the box `InBox m₁ m₂ c` (`4|w - c| < min m`) the
map `zcast m` is injective and its inverse is `liftNear c` (`liftNear_zcast`). Corresponding points
(`PtCorr`) are the images `zcast m₁ w`, `zcast m₂ w` of one `w` in the box
(`ptCorr_iff_exists`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban

section Zcast

variable {d : ℕ}

/-- The point of `𝕋_m` with integer representative `w`. -/
def zcast (m : ℕ) (w : Fin d → ℤ) : Torus d m := fun μ => ((w μ : ℤ) : ZMod m)

theorem zcast_apply (m : ℕ) (w : Fin d → ℤ) (μ : Fin d) : zcast m w μ = ((w μ : ℤ) : ZMod m) :=
  rfl

theorem zcast_add (m : ℕ) (w v : Fin d → ℤ) : zcast m (w + v) = zcast m w + zcast m v := by
  funext μ
  simp [zcast]

theorem zcast_single (m : ℕ) (μ : Fin d) :
    zcast m (Pi.single μ (1 : ℤ)) = (Pi.single μ (1 : ZMod m) : Fin d → ZMod m) := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [zcast]
  · simp [zcast, h]

theorem zcast_add_single (m : ℕ) (w : Fin d → ℤ) (μ : Fin d) :
    zcast m (w + Pi.single μ 1) = zcast m w + Pi.single μ 1 := by
  rw [zcast_add, zcast_single]

theorem zcast_sub_single (m : ℕ) (w : Fin d → ℤ) (μ : Fin d) :
    zcast m (w - Pi.single μ 1) = zcast m w - Pi.single μ 1 := by
  funext ν
  by_cases h : ν = μ
  · subst h; simp [zcast]
  · simp [zcast, h]

theorem zcast_eq_iff (m : ℕ) (w w' : Fin d → ℤ) :
    zcast m w = zcast m w' ↔ ∀ μ, (m : ℤ) ∣ w μ - w' μ := by
  constructor
  · intro h μ
    have := congrFun h μ
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub (w' μ) (w μ) m).1 this.symm
  · intro h
    funext μ
    exact ((ZMod.intCast_eq_intCast_iff_dvd_sub (w' μ) (w μ) m).2 (h μ)).symm

variable {m : ℕ} [NeZero m] {c w : Fin d → ℤ}

theorem liftNear_zcast (h : ∀ μ, 2 * |w μ - c μ| < (m : ℤ)) : liftNear c (zcast m w) = w := by
  funext μ
  unfold liftNear
  have h1 : zcast m w μ - (c μ : ZMod m) = (((w μ - c μ : ℤ)) : ZMod m) := by
    simp [zcast]
  rw [h1]
  have h2 : ZMod.valMinAbs (((w μ - c μ : ℤ)) : ZMod m) = w μ - c μ := by
    rw [ZMod.valMinAbs_spec]
    refine ⟨rfl, ?_⟩
    have h3 := h μ
    refine ⟨?_, ?_⟩
    · rcases abs_cases (w μ - c μ) with ⟨h7, _⟩ | ⟨h7, _⟩ <;> omega
    · rcases abs_cases (w μ - c μ) with ⟨h7, _⟩ | ⟨h7, _⟩ <;> omega
  rw [h2]; ring

theorem liftNear_abs_le (c : Fin d → ℤ) (x : Torus d m) (μ : Fin d) :
    2 * |liftNear c x μ - c μ| ≤ (m : ℤ) := by
  unfold liftNear
  have h := ZMod.valMinAbs_mem_Ioc (x μ - (c μ : ZMod m))
  rw [show c μ + ZMod.valMinAbs (x μ - (c μ : ZMod m)) - c μ = ZMod.valMinAbs (x μ - (c μ : ZMod m))
    by ring]
  obtain ⟨h1, h2⟩ := h
  rcases abs_cases (ZMod.valMinAbs (x μ - (c μ : ZMod m))) with ⟨h3, _⟩ | ⟨h3, _⟩ <;> omega

omit [NeZero m] in
theorem zcast_liftNear (x : Torus d m) : zcast m (liftNear c x) = x := by
  funext μ
  unfold liftNear zcast
  push_cast
  ring

end Zcast

/-! ### The box with a margin -/

section BoxK

variable {d : ℕ}

/-- `w` lies in the box with margin `K`: the points within `K` of `w` lie in `InBox`
(`4 (|w - c| + K) < min m`). -/
def InBoxK (K : ℕ) (m₁ m₂ : ℕ) (c w : Fin d → ℤ) : Prop :=
  ∀ μ, 4 * (|w μ - c μ| + K) < (m₁ : ℤ) ∧ 4 * (|w μ - c μ| + K) < (m₂ : ℤ)

theorem inBoxK_zero_iff {m₁ m₂ : ℕ} {c w : Fin d → ℤ} :
    InBoxK 0 m₁ m₂ c w ↔ InBox m₁ m₂ c w := by
  unfold InBoxK InBox
  simp

theorem InBoxK.mono {K K' m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBoxK K m₁ m₂ c w) (hK : K' ≤ K) :
    InBoxK K' m₁ m₂ c w := fun μ => by
  have := h μ
  have : (K' : ℤ) ≤ K := by exact_mod_cast hK
  constructor <;> omega

theorem InBoxK.inBox {K m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBoxK K m₁ m₂ c w) :
    InBox m₁ m₂ c w :=
  inBoxK_zero_iff.1 (h.mono (Nat.zero_le _))

theorem InBoxK.symm {K m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBoxK K m₁ m₂ c w) :
    InBoxK K m₂ m₁ c w := fun μ => ⟨(h μ).2, (h μ).1⟩

theorem InBox.symm {m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBox m₁ m₂ c w) : InBox m₂ m₁ c w :=
  fun μ => ⟨(h μ).2, (h μ).1⟩

theorem InBoxK.add_single {K m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBoxK (K + 1) m₁ m₂ c w)
    (μ : Fin d) : InBoxK K m₁ m₂ c (w + Pi.single μ 1) := fun ν => by
  have h1 := h ν
  by_cases hν : ν = μ
  · subst hν
    simp only [Pi.add_apply, Pi.single_eq_same]
    have : |w ν + 1 - c ν| ≤ |w ν - c ν| + 1 := by
      have := abs_add_le (w ν - c ν) 1
      rw [show w ν + 1 - c ν = w ν - c ν + 1 by ring]; simpa using this
    constructor <;> push_cast at h1 ⊢ <;> omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hν, add_zero]
    constructor <;> push_cast at h1 ⊢ <;> omega

theorem InBoxK.sub_single {K m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBoxK (K + 1) m₁ m₂ c w)
    (μ : Fin d) : InBoxK K m₁ m₂ c (w - Pi.single μ 1) := fun ν => by
  have h1 := h ν
  by_cases hν : ν = μ
  · subst hν
    simp only [Pi.sub_apply, Pi.single_eq_same]
    have : |w ν - 1 - c ν| ≤ |w ν - c ν| + 1 := by
      have := abs_sub (w ν - c ν) 1
      rw [show w ν - 1 - c ν = w ν - c ν - 1 by ring]; simpa using this
    constructor <;> push_cast at h1 ⊢ <;> omega
  · simp only [Pi.sub_apply, Pi.single_eq_of_ne hν, sub_zero]
    constructor <;> push_cast at h1 ⊢ <;> omega

variable {m : ℕ} [NeZero m]

theorem inBox_two_mul_lt {m₁ m₂ : ℕ} {c w : Fin d → ℤ} (h : InBox m₁ m₂ c w) (μ : Fin d) :
    2 * |w μ - c μ| < (m₁ : ℤ) ∧ 2 * |w μ - c μ| < (m₂ : ℤ) := by
  have h1 := h μ
  have := abs_nonneg (w μ - c μ)
  constructor <;> omega

theorem InBox.liftNear_zcast₁ {m₁ m₂ : ℕ} [NeZero m₁] {c w : Fin d → ℤ} (h : InBox m₁ m₂ c w) :
    liftNear c (zcast m₁ w) = w :=
  liftNear_zcast fun μ => (inBox_two_mul_lt h μ).1

theorem InBox.liftNear_zcast₂ {m₁ m₂ : ℕ} [NeZero m₂] {c w : Fin d → ℤ} (h : InBox m₁ m₂ c w) :
    liftNear c (zcast m₂ w) = w :=
  liftNear_zcast fun μ => (inBox_two_mul_lt h μ).2

/-- On the box, `zcast m₁` is injective. -/
theorem InBox.zcast₁_inj {m₁ m₂ : ℕ} [NeZero m₁] {c w v : Fin d → ℤ} (hw : InBox m₁ m₂ c w)
    (hv : InBox m₁ m₂ c v) : zcast m₁ w = zcast m₁ v ↔ w = v := by
  constructor
  · intro h
    have := congrArg (liftNear c) h
    rwa [hw.liftNear_zcast₁, hv.liftNear_zcast₁] at this
  · rintro rfl; rfl

theorem InBox.zcast₂_inj {m₁ m₂ : ℕ} [NeZero m₂] {c w v : Fin d → ℤ} (hw : InBox m₁ m₂ c w)
    (hv : InBox m₁ m₂ c v) : zcast m₂ w = zcast m₂ v ↔ w = v := by
  constructor
  · intro h
    have := congrArg (liftNear c) h
    rwa [hw.liftNear_zcast₂, hv.liftNear_zcast₂] at this
  · rintro rfl; rfl


theorem zcast_add_single_iff {m₁ m₂ m : ℕ} [NeZero m] {c w v : Fin d → ℤ}
    (hm : ∀ u u', InBox m₁ m₂ c u → InBox m₁ m₂ c u' → (zcast m u = zcast m u' ↔ u = u'))
    (hw : InBoxK 1 m₁ m₂ c w) (hv : InBox m₁ m₂ c v) (μ : Fin d) :
    zcast m v = zcast m w + Pi.single μ 1 ↔ v = w + Pi.single μ 1 := by
  rw [← zcast_add_single]
  exact hm _ _ hv (hw.add_single μ).inBox

theorem zcast_sub_single_iff {m₁ m₂ m : ℕ} [NeZero m] {c w v : Fin d → ℤ}
    (hm : ∀ u u', InBox m₁ m₂ c u → InBox m₁ m₂ c u' → (zcast m u = zcast m u' ↔ u = u'))
    (hw : InBoxK 1 m₁ m₂ c w) (hv : InBox m₁ m₂ c v) (μ : Fin d) :
    zcast m v = zcast m w - Pi.single μ 1 ↔ v = w - Pi.single μ 1 := by
  rw [← zcast_sub_single]
  exact hm _ _ hv (hw.sub_single μ).inBox

theorem two_abs_sub_lt {m₁ m₂ : ℕ} {c w v : Fin d → ℤ} (hw : InBox m₁ m₂ c w)
    (hv : InBox m₁ m₂ c v) (μ : Fin d) :
    2 * |w μ - v μ| < (m₁ : ℤ) ∧ 2 * |w μ - v μ| < (m₂ : ℤ) := by
  have h1 := hw μ
  have h2 := hv μ
  have h3 : |w μ - v μ| ≤ |w μ - c μ| + |v μ - c μ| := by
    have := abs_sub_le (w μ) (c μ) (v μ)
    simpa [abs_sub_comm] using this
  constructor <;> omega

end BoxK

/-! ### Blocks of integer lifts -/

section BlockLift

variable {d : ℕ}

theorem blockCoord_intCast {ℓ P n : ℕ} [NeZero ℓ] (hℓ : ℓ = P * n) (hP : 0 < P) (w : ℤ) :
    blockCoord P n ((w : ℤ) : ZMod ℓ) = ((w / (P : ℤ) : ℤ) : ZMod n) := by
  unfold blockCoord
  have hv : (((w : ZMod ℓ)).val : ℤ) = w % (ℓ : ℤ) := ZMod.val_intCast w
  have h1 : ((((w : ZMod ℓ)).val / P : ℕ) : ZMod n) =
      ((((((w : ZMod ℓ)).val / P : ℕ) : ℤ)) : ZMod n) := (Int.cast_natCast _).symm
  rw [h1, Int.natCast_div, hv]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  have hPn : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  have h2 : w = w % (ℓ : ℤ) + (P : ℤ) * ((n : ℤ) * (w / (ℓ : ℤ))) := by
    have := Int.emod_add_mul_ediv w (ℓ : ℤ)
    rw [hℓ] at this ⊢
    push_cast at this ⊢
    linarith [this]
  have h3 : w / (P : ℤ) = w % (ℓ : ℤ) / (P : ℤ) + (n : ℤ) * (w / (ℓ : ℤ)) := by
    conv_lhs => rw [h2]
    exact Int.add_mul_ediv_left _ _ hPn
  rw [h3]
  exact ⟨w / (ℓ : ℤ), by ring⟩

theorem blockMap_zcast {ℓ P n : ℕ} [NeZero ℓ] (hℓ : ℓ = P * n) (hP : 0 < P) (w : Fin d → ℤ) :
    blockMap P n (zcast ℓ w) = zcast n (fun μ => w μ / (P : ℤ)) := by
  funext μ
  exact blockCoord_intCast hℓ hP (w μ)

end BlockLift

end Balaban.RootFSpine
