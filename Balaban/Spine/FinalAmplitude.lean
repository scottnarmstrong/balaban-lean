/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RootBoundsArith

/-!
# The amplitude `c₉/4` of the final activities

A6-3 (e), arithmetic. The scale-`(k+1)` activity splits into a part `ℳ^{(k+1)}_0` bounded through
the prefix ties by `a₁ L^{-(k+1)θ} e^{-κ|X|_#}` and a rest bounded by `C β_k^{-2} e^{-κ|X|_#}`,
`θ = (d-2)/2 + δ`. The rest is small in `β`: for `β₀` large, `C β_k^{-2} ≤ a₂ L^{-(k+1)θ}`
(`rest_small_in_beta`, from `betaK_inv_sq_le`), so the sum is at most `(a₁ + a₂) L^{-(k+1)θ}
e^{-κ|X|_#}` (`amplitude_split`), and with `a₁ + a₂ ≤ c₉/4` it has the amplitude `c₉/4`.
-/

@[expose] public section

open Balaban.Inhabited.RootBoundsArith

namespace Balaban.RootFSpine

/-- **The rest is small in `β`**: `C β_k^{-2} ≤ a L^{-(k+1)((d-2)/2+δ)}` for every `k` when
`L^{(d-2)/2+δ} ≤ (a/(C+1)) β₀²`. -/
theorem rest_small_in_beta {d L k : ℕ} {β0 C a δ : ℝ} (hd : 3 ≤ d) (hL : 2 ≤ L) (ha : 0 < a)
    (hC : 0 ≤ C) (hβ0 : 0 < β0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((d : ℝ) - 2) / 2)
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ a / (C + 1) * β0 ^ 2) :
    C * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹ ≤
      a * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
  have hC1 : 0 < C + 1 := by linarith
  have h := betaK_inv_sq_le (d := d) (L := L) (k := k) (c₉ := a / (C + 1)) hd hL
    (div_pos ha hC1) hβ0 hδ0 hδ hβ
  have hpos : 0 ≤ (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) :=
    Real.rpow_nonneg (by positivity) _
  calc C * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹
      ≤ C * (a / (C + 1) * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) :=
        mul_le_mul_of_nonneg_left h hC
    _ = (C / (C + 1)) * a * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
        field_simp
    _ ≤ 1 * a * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
        have : C / (C + 1) ≤ 1 := by rw [div_le_one hC1]; linarith
        gcongr
    _ = _ := by ring

/-- **The amplitude of a split activity**: if the main part is at most `a₁ L^{-jθ} E` and the rest
at most `C β_k^{-2} E` with `E ≥ 0` (`E = e^{-κ|X|_#}`, `j = k + 1`), and `β₀` is large as in
`rest_small_in_beta` with `a₂`, the sum is at most `(a₁ + a₂) L^{-jθ} E`. -/
theorem amplitude_split {d L k : ℕ} {β0 C a₁ a₂ δ E u₁ u₂ : ℝ} (hd : 3 ≤ d) (hL : 2 ≤ L)
    (ha₂ : 0 < a₂) (hC : 0 ≤ C) (hβ0 : 0 < β0) (hδ0 : 0 ≤ δ) (hδ : δ ≤ ((d : ℝ) - 2) / 2)
    (hβ : (L : ℝ) ^ (((d : ℝ) - 2) / 2 + δ) ≤ a₂ / (C + 1) * β0 ^ 2) (hE : 0 ≤ E)
    (h₁ : ‖u₁‖ ≤ a₁ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * E)
    (h₂ : ‖u₂‖ ≤ C * ((Balaban.LargeField.ActionConv.betaK d L k β0) ^ 2)⁻¹ * E) :
    ‖u₁ + u₂‖ ≤ (a₁ + a₂) * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * E := by
  have h := rest_small_in_beta (d := d) (L := L) (k := k) hd hL ha₂ hC hβ0 hδ0 hδ hβ
  calc ‖u₁ + u₂‖ ≤ ‖u₁‖ + ‖u₂‖ := norm_add_le _ _
    _ ≤ a₁ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * E +
        a₂ * (L : ℝ) ^ (-(((k + 1 : ℕ) : ℝ) * (((d : ℝ) - 2) / 2 + δ))) * E :=
        add_le_add h₁ (h₂.trans (mul_le_mul_of_nonneg_right h hE))
    _ = _ := by ring

end Balaban.RootFSpine
