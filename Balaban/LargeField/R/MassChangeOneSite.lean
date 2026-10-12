/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# The one-site example (INTERFACE-A §1, (1.4))

On `S¹`: one interior spin `φ`, block target `q = e₁`, one exterior fixed spin
`p = (cos ϑ, sin ϑ)`, `h = q`.  The P7-type regional action (one crossing bond counted by half) is
`A_{m,Y}(φ) = ½|φ - q|² + ¼|φ - p|² + (m/2)|φ - q|²`; the complete and the massless minimizers are
`φᵐ = ((1+m)q + p)/|(1+m)q + p|` and `φ⁰ = (q + p)/|q + p|`.

`oneSite_slope_tendsto`: `(A_{m,Y}(φ⁰) - A_{m,Y}(φᵐ))/m → (1 - cos ϑ)/(4 √(2 + 2 cos ϑ))` as `m ↓ 0`.
Consequently (`oneSite_beta_limit`, `oneSite_beta_msq_limit`) with `β m = c₀` fixed, `β ΔA` tends to
the positive constant `c₀ (1 - cos ϑ)/(4 s₀)` while `β m² → 0`: the localized form of
W2-RESOLVE (3.5) without a wall term is false.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Filter Topology

/-- The regional action of the one-site example at the point `(x, y)`, `p = (c, s)`, `q = (1, 0)`. -/
noncomputable def oneSiteAction (c s m x y : ℝ) : ℝ :=
  (1 / 2) * ((x - 1) ^ 2 + y ^ 2) + (1 / 4) * ((x - c) ^ 2 + (y - s) ^ 2) +
    m / 2 * ((x - 1) ^ 2 + y ^ 2)

/-- The norm `|(1+m)q + p|`. -/
noncomputable def oneSiteNorm (c s m : ℝ) : ℝ := Real.sqrt ((1 + m + c) ^ 2 + s ^ 2)

/-- The complete minimizer `φᵐ`. -/
noncomputable def oneSitePhi (c s m : ℝ) : ℝ × ℝ :=
  ((1 + m + c) / oneSiteNorm c s m, s / oneSiteNorm c s m)

/-- The mass-switch difference `A_{m,Y}(φ⁰) - A_{m,Y}(φᵐ)` of the example. -/
noncomputable def oneSiteDiff (c s m : ℝ) : ℝ :=
  oneSiteAction c s m (oneSitePhi c s 0).1 (oneSitePhi c s 0).2 -
    oneSiteAction c s m (oneSitePhi c s m).1 (oneSitePhi c s m).2

theorem oneSiteAction_unit {c s m x y : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hxy : x ^ 2 + y ^ 2 = 1) :
    oneSiteAction c s m x y = 3 / 2 + m - (x * (1 + m + c / 2) + y * (s / 2)) := by
  unfold oneSiteAction
  linear_combination (1 / 2 + m / 2 + 1 / 4) * hxy + (1 / 4) * hcs

theorem oneSitePhi_unit {c s : ℝ} (m : ℝ) (h : 0 < (1 + m + c) ^ 2 + s ^ 2) :
    (oneSitePhi c s m).1 ^ 2 + (oneSitePhi c s m).2 ^ 2 = 1 := by
  unfold oneSitePhi oneSiteNorm
  have h1 := Real.sq_sqrt h.le
  have h2 := Real.sqrt_pos.2 h
  simp only
  field_simp
  linarith

/-- The closed form `F m - G m` of the difference. -/
noncomputable def oneSiteF (c m : ℝ) : ℝ :=
  ((1 + m + c) * (1 + m + c / 2) + (1 - c ^ 2) / 2) / Real.sqrt ((1 + m + c) ^ 2 + (1 - c ^ 2))

noncomputable def oneSiteG (c m : ℝ) : ℝ :=
  ((1 + c) * (1 + m + c / 2) + (1 - c ^ 2) / 2) / Real.sqrt (2 + 2 * c)

theorem oneSiteDiff_eq {c s : ℝ} (hcs : c ^ 2 + s ^ 2 = 1) (hc : -1 < c) {m : ℝ} (hm : 0 ≤ m) :
    oneSiteDiff c s m = oneSiteF c m - oneSiteG c m := by
  have hs : s ^ 2 = 1 - c ^ 2 := by linarith
  have hp : ∀ t : ℝ, 0 ≤ t → 0 < (1 + t + c) ^ 2 + s ^ 2 := fun t ht => by
    have : 0 < 1 + t + c := by linarith
    positivity
  have h0 : 0 < (1 + 0 + c) ^ 2 + s ^ 2 := hp 0 le_rfl
  have hu := oneSitePhi_unit (c := c) (s := s) m (hp m hm)
  have hv := oneSitePhi_unit (c := c) (s := s) 0 h0
  unfold oneSiteDiff
  rw [oneSiteAction_unit hcs hu, oneSiteAction_unit hcs hv]
  have hV : oneSiteNorm c s 0 = Real.sqrt (2 + 2 * c) := by
    unfold oneSiteNorm; congr 1; nlinarith
  have hU : oneSiteNorm c s m = Real.sqrt ((1 + m + c) ^ 2 + (1 - c ^ 2)) := by
    unfold oneSiteNorm; rw [hs]
  have hUp : 0 < oneSiteNorm c s m := Real.sqrt_pos.2 (hp m hm)
  have hVp : 0 < oneSiteNorm c s 0 := Real.sqrt_pos.2 h0
  unfold oneSiteF oneSiteG
  rw [← hU, ← hV]
  unfold oneSitePhi
  simp only [add_zero]
  field_simp
  rw [hs]
  ring

theorem oneSiteDiff_slope {c : ℝ} (hc : -1 < c) :
    HasDerivAt (fun m => oneSiteF c m - oneSiteG c m)
      ((1 - c) / (4 * Real.sqrt (2 + 2 * c))) 0 := by
  have hV0 : 0 < 2 + 2 * c := by linarith
  have hVp := Real.sqrt_pos.2 hV0
  have hVsq := Real.sq_sqrt hV0.le
  have hP : 0 < (1 + 0 + c) ^ 2 + (1 - c ^ 2) := by nlinarith
  have hPd : HasDerivAt (fun m : ℝ => (1 + m + c) ^ 2 + (1 - c ^ 2)) (2 * (1 + 0 + c)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_add 1 |>.add_const c).pow 2 |>.add_const (1 - c ^ 2)
    simpa using this
  have hU := hPd.sqrt hP.ne'
  have hN : HasDerivAt (fun m : ℝ => (1 + m + c) * (1 + m + c / 2) + (1 - c ^ 2) / 2)
      ((1 + 0 + c / 2) + (1 + 0 + c)) 0 := by
    have h1 : HasDerivAt (fun m : ℝ => 1 + m + c) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).add_const c
    have h2 : HasDerivAt (fun m : ℝ => 1 + m + c / 2) 1 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add 1).add_const (c / 2)
    have := (h1.mul h2).add_const ((1 - c ^ 2) / 2)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hF := hN.div hU (Real.sqrt_pos.2 hP).ne'
  have hG : HasDerivAt (fun m : ℝ => oneSiteG c m) ((1 + c) / Real.sqrt (2 + 2 * c)) 0 := by
    unfold oneSiteG
    have : HasDerivAt (fun m : ℝ => (1 + c) * (1 + m + c / 2) + (1 - c ^ 2) / 2) (1 + c) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).const_add 1).add_const (c / 2)).const_mul (1 + c)
        |>.add_const ((1 - c ^ 2) / 2)
      simpa using this
    exact this.div_const _
  have := hF.sub hG
  refine this.congr_deriv ?_
  have e1 : (1 + c) ^ 2 + (1 - c ^ 2) = 2 + 2 * c := by ring
  simp only [add_zero, e1]
  generalize Real.sqrt (2 + 2 * c) = V at hVp hVsq ⊢
  field_simp
  nlinarith [hVsq]

/-- **The one-site limit** (INTERFACE-A (1.4)): `ΔA/m → (1 - cos ϑ)/(4 s₀)`, `s₀ = √(2+2cos ϑ)`. -/
theorem oneSite_slope_tendsto (ϑ : ℝ) (hϑ : -1 < Real.cos ϑ) :
    Tendsto (fun m => oneSiteDiff (Real.cos ϑ) (Real.sin ϑ) m / m) (𝓝[>] 0)
      (𝓝 ((1 - Real.cos ϑ) / (4 * Real.sqrt (2 + 2 * Real.cos ϑ)))) := by
  have hcs : Real.cos ϑ ^ 2 + Real.sin ϑ ^ 2 = 1 := by
    rw [add_comm]; exact Real.sin_sq_add_cos_sq ϑ
  have h := (hasDerivAt_iff_tendsto_slope_zero.1 (oneSiteDiff_slope hϑ)).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun t (ht : 0 < t) => ne_of_gt ht))
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with m hm
  have hm' : 0 < m := hm
  have e0 : oneSiteF (Real.cos ϑ) 0 - oneSiteG (Real.cos ϑ) 0 = 0 := by
    have := oneSiteDiff_eq hcs hϑ (le_refl (0 : ℝ))
    have h0 : oneSiteDiff (Real.cos ϑ) (Real.sin ϑ) 0 = 0 := by
      unfold oneSiteDiff; ring
    linarith
  simp only [zero_add, e0, sub_zero, smul_eq_mul]
  rw [oneSiteDiff_eq hcs hϑ hm'.le]
  field_simp

/-- With `β m = c₀` fixed: `β ΔA → c₀ (1 - cos ϑ)/(4 s₀)`, a nonzero constant. -/
theorem oneSite_beta_limit (ϑ : ℝ) (hϑ : -1 < Real.cos ϑ) (c₀ : ℝ) :
    Tendsto (fun m => (c₀ / m) * oneSiteDiff (Real.cos ϑ) (Real.sin ϑ) m) (𝓝[>] 0)
      (𝓝 (c₀ * ((1 - Real.cos ϑ) / (4 * Real.sqrt (2 + 2 * Real.cos ϑ))))) := by
  refine ((oneSite_slope_tendsto ϑ hϑ).const_mul c₀).congr' ?_
  filter_upwards with m
  ring

/-- With `β m = c₀` fixed, `β m² = c₀ m → 0`. -/
theorem oneSite_beta_msq_limit (c₀ : ℝ) :
    Tendsto (fun m : ℝ => (c₀ / m) * m ^ 2) (𝓝[>] 0) (𝓝 0) := by
  have h : Tendsto (fun m : ℝ => c₀ * m) (𝓝[>] 0) (𝓝 (c₀ * 0)) :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).const_mul c₀
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with m hm
  have : m ≠ 0 := ne_of_gt hm
  field_simp

/-- The limit is nonzero for `c₀ > 0` and `-1 < cos ϑ < 1`. -/
theorem oneSite_limit_pos (ϑ : ℝ) (hϑ : -1 < Real.cos ϑ) (hϑ' : Real.cos ϑ < 1) {c₀ : ℝ}
    (hc₀ : 0 < c₀) :
    0 < c₀ * ((1 - Real.cos ϑ) / (4 * Real.sqrt (2 + 2 * Real.cos ϑ))) := by
  have : 0 < Real.sqrt (2 + 2 * Real.cos ϑ) := Real.sqrt_pos.2 (by linarith)
  have : 0 < 1 - Real.cos ϑ := by linarith
  positivity

end Balaban.LargeField.ActionConv
