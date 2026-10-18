/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusGenCubeInt

/-!
# A neighbourhood of a component lies in the box, with margin

If the fine sites of the `r`-neighbourhood (in cubes of side `P`) of a set `Zc` of cubes lie in the
box (`V`), then every point `w` of the box whose cube is in `Zc` has the margin `6 P`: the points
within `6 P` of `w` lie in the box (`zone_inBoxK`, `r ≥ 6`, at least `24` cubes per side).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField

section Zone

variable {d : ℕ}

theorem bidx_add_shift {P : ℕ} (hP : 0 < P) (w t : Fin d → ℤ) :
    bidx P (w + fun μ => (P : ℤ) * t μ) = bidx P w + t := by
  have hP' : (P : ℤ) ≠ 0 := by exact_mod_cast hP.ne'
  funext μ
  simp only [bidx, Pi.add_apply]
  rw [Int.add_mul_ediv_left _ _ hP']

theorem zone_inBoxK {ℓ ℓ' n P r : ℕ} [NeZero ℓ] [NeZero n] (hP : 0 < P) (hℓ : ℓ = P * n)
    (hn : 24 ≤ n) {cc w : Fin d → ℤ} (hw : InBox ℓ ℓ' cc w) (Zc : Set (Torus d n)) (hr : 6 ≤ r)
    (V : Set (Torus d ℓ)) (hV : ∀ x ∈ V, InBox ℓ ℓ' cc (liftNear cc x))
    (hVZ : ∀ x : Torus d ℓ, blockMap P n x ∈ nbhd r Zc → x ∈ V)
    (hcube : blockMap P n (zcast ℓ w) ∈ Zc) : InBoxK (6 * P) ℓ ℓ' cc w := by
  intro μ
  have hPi : (0 : ℤ) < P := by exact_mod_cast hP
  have hℓi : (ℓ : ℤ) = P * n := by rw [hℓ]; push_cast; ring
  have hnZ : (24 : ℤ) ≤ n := by exact_mod_cast hn
  -- the shifted point
  obtain ⟨σ, hσ⟩ : ∃ σ : ℤ, (σ = 6 ∨ σ = -6) ∧ |w μ + P * σ - cc μ| = |w μ - cc μ| + 6 * P := by
    by_cases h : cc μ ≤ w μ
    · refine ⟨6, Or.inl rfl, ?_⟩
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]; ring
    · refine ⟨-6, Or.inr rfl, ?_⟩
      have : w μ - cc μ < 0 := by linarith
      rw [abs_of_neg this, abs_of_neg (by linarith)]; ring
  set t : Fin d → ℤ := Pi.single μ σ with ht
  set u : Fin d → ℤ := w + fun μ' => (P : ℤ) * t μ' with hu
  have huμ : u μ = w μ + P * σ := by simp [hu, ht]
  have hbd : bidx P u = bidx P w + t := bidx_add_shift hP w t
  have htr : ∀ μ', |t μ'| ≤ r := by
    intro μ'
    by_cases h : μ' = μ
    · subst h
      simp only [ht, Pi.single_eq_same]
      rcases hσ.1 with h6 | h6 <;> rw [h6] <;> simp <;> omega
    · simp [ht, h]
  have hxV : zcast ℓ u ∈ V := by
    apply hVZ
    rw [blockMap_zcast hℓ hP]
    show zcast n (bidx P u) ∈ nbhd r Zc
    rw [mem_nbhd_zcast (bidx P u)]
    refine ⟨fun μ' => -t μ', fun μ' => by simpa using htr μ', ?_⟩
    have : bidx P u + (fun μ' => -t μ') = bidx P w := by
      rw [hbd]; funext μ'; simp
    rw [this]
    have := hcube
    rw [blockMap_zcast hℓ hP] at this
    exact this
  have hu2 : ∀ μ', 2 * |u μ' - cc μ'| < (ℓ : ℤ) := by
    intro μ'
    have h1 := (hw μ').1
    have h2 : |u μ' - cc μ'| ≤ |w μ' - cc μ'| + 6 * P := by
      by_cases h : μ' = μ
      · subst h; rw [huμ, hσ.2]
      · simp only [hu, ht, Pi.add_apply, Pi.single_eq_of_ne h, mul_zero, add_zero]; linarith
    rw [hℓi] at h1 ⊢
    nlinarith
  have hxe : liftNear cc (zcast ℓ u) = u := liftNear_zcast hu2
  have hb := hV _ hxV μ
  rw [hxe, huμ, hσ.2] at hb
  have hK : ((6 * P : ℕ) : ℤ) = 6 * P := by push_cast; ring
  rw [hK]
  exact hb

end Zone

end Balaban.RootFSpine
