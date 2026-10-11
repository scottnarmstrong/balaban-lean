/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Multiscale.KernelBase
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Standard composition rules with a localized factor (GREEN.md §4.6)

`Balaban.Multiscale.Dec.comp` has free parameters; here they are fixed in terms of the rate
`e = agmonRate d`: scale rate `κ = e / (400 d)`, summation loss `θ = e / 100`, tail rate `e / 10`.

* `Dec.mul_std`: `Dec · Dec`, loses `e / 50` of the rate;
* `Dec.mul_out`: `Dec · (Dec with output localized near Z)`, gives the tail `τ_Z`
  (`τ_Z(y, y') = e^{-γ_t d(y,Z)} e^{-γ_t d(y',Z)}`), loses `e / 8`;
* `Dec.mul_tail`: `(Dec with tail τ_Z) · Dec`, loses `e / 8`.
-/

@[expose] public section

namespace Balaban.Multiscale

open Finset Matrix Balaban

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The scale rate `κ = e / (400 d)`; the hypothesis `log L ≤ κ (ϱ - 1)` says that `ϱ` is large. -/
noncomputable def locKappa (d : ℕ) : ℝ := agmonRate d / (400 * d)

/-- The summation loss `θ = e / 100`. -/
noncomputable def locTheta (d : ℕ) : ℝ := agmonRate d / 100

/-- The tail rate `e / 10`. -/
noncomputable def locTail (d : ℕ) : ℝ := agmonRate d / 10

theorem locKappa_nonneg (d : ℕ) : 0 ≤ locKappa d := by
  unfold locKappa agmonRate poincareConst
  positivity

theorem locKappa_mul_le (hd : 0 < d) (n : ℕ) (hn : n ≤ 4) :
    locKappa d * n ≤ agmonRate d / 100 := by
  have hdd : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have he := agmonRate_pos hd
  have h1 : locKappa d ≤ agmonRate d / 400 := by
    unfold locKappa
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : (n : ℝ) ≤ 4 := by exact_mod_cast hn
  have h3 : locKappa d * n ≤ agmonRate d / 400 * 4 :=
    mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
  linarith

omit [NeZero L] in
theorem locCount (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1)) :
    2 * d * Real.log L ≤ locTheta d / 2 * (ϱ - 1) := by
  have hr : 0 < ϱ - 1 := by linarith
  have hdd : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 : 2 * d * Real.log L ≤ 2 * d * (locKappa d * (ϱ - 1)) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  have e : 2 * (d : ℝ) * (locKappa d * (ϱ - 1)) = locTheta d / 2 * (ϱ - 1) := by
    unfold locKappa locTheta
    field_simp
    ring
  linarith

/-- The tail weight `e^{-γ_t d(y,Z)} e^{-γ_t d(y',Z)}`. -/
noncomputable def tailZ (G : GeneratingSet d L N₀ k ϱ) (γt : ℝ) (Z : Finset (G.Ω 1)) :
    Torus d (N₀ * L ^ k) → Torus d (N₀ * L ^ k) → ℝ :=
  fun y y' => decay γt (G.distSet y Z) * decay γt (G.distSet y' Z)

theorem tailZ_nonneg (G : GeneratingSet d L N₀ k ϱ) (γt : ℝ) (Z : Finset (G.Ω 1)) (y y') :
    0 ≤ tailZ G γt Z y y' :=
  mul_nonneg (decay_nonneg _ _) (decay_nonneg _ _)

omit [NeZero N₀] [NeZero L] in
theorem noTail_nonneg : ∀ y y' : Torus d (N₀ * L ^ k), 0 ≤ noTail y y' := fun _ _ => zero_le_one

/-- The constant of a plain composition. -/
noncomputable def cmpC (d L : ℕ) (θ C₁ C₂ B : ℝ) (μ : ℕ) : ℝ :=
  C₁ * C₂ * B * (L : ℝ) ^ μ * countConst d L θ

section Std

variable {ι₁ ι₂ ι₃ : Type*} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
variable {G : GeneratingSet d L N₀ k ϱ}

omit [NeZero N₀] [NeZero L] in
theorem countConst_nonneg (d L : ℕ) (θ : ℝ) : 0 ≤ countConst d L θ := by
  unfold countConst
  exact tsum_nonneg fun m => by positivity

/-- **Plain composition** (`Dec · Dec`), rate loss `e / 50`. -/
theorem Dec.mul_std {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γT γS C₁ C₂ : ℝ}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1))
    (hμ : w.natAbs + w'.natAbs ≤ 4) (hγ : agmonRate d / 50 ≤ γ) (hT : γ ≤ γT) (hS : γ ≤ γS)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hTd : Dec G s₁ s₂ T w γT noTail C₁) (hSd : Dec G s₂ s₃ S w' γS noTail C₂) :
    Dec G s₁ s₃ (T * S) (w + w') (γ - agmonRate d / 50) noTail
      (cmpC d L (locTheta d) C₁ C₂ 1 (w.natAbs + w'.natAbs)) := by
  have he := agmonRate_pos hd
  have hκ := locKappa_mul_le hd _ hμ
  have hθ : 0 < locTheta d := by unfold locTheta; positivity
  have := Dec.comp (G := G) (T := T) (S := S) (τ₁ := noTail) (τ₂ := noTail) (τ := noTail)
    (γ := γ) (γ'' := γ - agmonRate d / 50) (θ := locTheta d) (ρ := 0) (κ := locKappa d) (B := 1)
    hϱ hlog hθ (locCount hd hϱ hlog) (by
      push_cast at hκ ⊢
      unfold locTheta
      linarith) (by linarith) hC₁ hC₂ zero_le_one noTail_nonneg noTail_nonneg noTail_nonneg
    (fun _ => True) (fun _ _ _ x hx => absurd trivial hx) (by
      intro y y' x _ _ _
      simp [noTail])
    (hTd.mono_rate noTail_nonneg hC₁ hT) (hSd.mono_rate noTail_nonneg hC₂ hS)
  exact this

/-- The distance to `Z` satisfies the triangle inequality. -/
theorem distSet_le_add (G : GeneratingSet d L N₀ k ϱ) (Z : Finset (G.Ω 1))
    (y x : Torus d (N₀ * L ^ k)) : G.distSet y Z ≤ G.pathDist y x + G.distSet x Z := by
  by_cases hZ : Z.Nonempty
  · obtain ⟨z, hz, hmin⟩ := Finset.exists_mem_eq_inf Z hZ (fun z => G.pathDist x (z : Torus d (N₀ * L ^ k)))
    have e : G.distSet x Z = G.pathDist x z := hmin
    rw [e]
    exact (G.distSet_le y hz).trans (G.pathDist_triangle y x z)
  · have : Z = ∅ := Finset.not_nonempty_iff_eq_empty.1 hZ
    subst this
    simp [GeneratingSet.distSet]

/-- The output of `T` on blocks far from `Z` vanishes. -/
def OutNear {ι ι₂ : Type*} [Fintype ι] [Fintype ι₂] (G : GeneratingSet d L N₀ k ϱ)
    (s : ι → G.Ω 1) (Z : Finset (G.Ω 1)) (c : ℝ) (T : Matrix ι ι₂ ℂ) : Prop :=
  ∀ (j : ℕ) (y : Torus d (N₀ * L ^ k)), 1 ≤ j → j ≤ k → y ∈ G.layer j →
    ¬ (G.distSet y Z ≤ ENNReal.ofReal c) → ∀ g : ι₂ → ℂ, bn G s j y (T *ᵥ g) = 0

/-- **Composition with a factor localized near `Z`** (output side): the product has the tails
`τ_Z`.  Rate loss `e / 8`. -/
theorem Dec.mul_out {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γT γS C₁ C₂ c : ℝ}
    {Z : Finset (G.Ω 1)}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1))
    (hμ : w.natAbs + w'.natAbs ≤ 4) (hγ : agmonRate d / 8 ≤ γ) (hT : γ ≤ γT) (hS : γ ≤ γS)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (hc : 0 ≤ c)
    (hTd : Dec G s₁ s₂ T w γT noTail C₁) (hSd : Dec G s₂ s₃ S w' γS noTail C₂)
    (hE : OutNear G s₂ Z c S) :
    Dec G s₁ s₃ (T * S) (w + w') (γ - agmonRate d / 8) (tailZ G (locTail d) Z)
      (cmpC d L (locTheta d) C₁ C₂ (Real.exp (2 * locTail d * c)) (w.natAbs + w'.natAbs)) := by
  have he := agmonRate_pos hd
  have hκ := locKappa_mul_le hd _ hμ
  have hθ : 0 < locTheta d := by unfold locTheta; positivity
  have hγt : 0 ≤ locTail d := by unfold locTail; positivity
  refine Dec.comp (G := G) (T := T) (S := S) (τ₁ := noTail) (τ₂ := noTail)
    (τ := tailZ G (locTail d) Z) (γ := γ) (γ'' := γ - agmonRate d / 8) (θ := locTheta d)
    (ρ := locTail d) (κ := locKappa d) (B := Real.exp (2 * locTail d * c))
    hϱ hlog hθ (locCount hd hϱ hlog) (by
      push_cast at hκ ⊢
      unfold locTheta locTail
      linarith) (by linarith) hC₁ hC₂ (Real.exp_pos _).le noTail_nonneg noTail_nonneg
    (tailZ_nonneg G _ Z) (fun x => G.distSet (x : Torus d (N₀ * L ^ k)) Z ≤ ENNReal.ofReal c)
    ?_ ?_ (hTd.mono_rate noTail_nonneg hC₁ hT) (hSd.mono_rate noTail_nonneg hC₂ hS)
  · intro j' y' f x hx
    obtain ⟨hx1, hxk, hxl⟩ := G.layerIndex_spec x.2
    exact hE _ _ hx1 hxk hxl hx _
  · intro y y' x hx hp hq
    have hxZ : G.distSet (x : Torus d (N₀ * L ^ k)) Z ≤ ENNReal.ofReal c := hx
    set pr := (G.pathDist y x).toReal with hpr
    set qr := (G.pathDist x y').toReal with hqr
    have hp0 : 0 ≤ pr := ENNReal.toReal_nonneg
    have hq0 : 0 ≤ qr := ENNReal.toReal_nonneg
    have h1 : G.distSet y Z ≤ ENNReal.ofReal (pr + c) := by
      refine (distSet_le_add G Z y x).trans ?_
      rw [ENNReal.ofReal_add hp0 hc, ENNReal.ofReal_toReal hp]
      exact add_le_add le_rfl hxZ
    have h2 : G.distSet y' Z ≤ ENNReal.ofReal (qr + c) := by
      refine (distSet_le_add G Z y' x).trans ?_
      rw [ENNReal.ofReal_add hq0 hc, GeneratingSet.pathDist_comm y' x, ENNReal.ofReal_toReal hq]
      exact add_le_add le_rfl hxZ
    have d1 := decay_ofReal_ge hγt (by positivity : 0 ≤ pr + c) h1
    have d2 := decay_ofReal_ge hγt (by positivity : 0 ≤ qr + c) h2
    unfold tailZ noTail
    have : (1 : ℝ) = Real.exp (2 * locTail d * c) * (Real.exp (-(locTail d * (pr + c))) *
        Real.exp (-(locTail d * (qr + c)))) * Real.exp (locTail d * (pr + qr)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; simp only [← Real.exp_zero]; congr 1; ring
    calc (1 : ℝ) * 1 = 1 := by ring
      _ = _ := this
      _ ≤ _ := by
        have e1 := decay_nonneg (locTail d) (G.distSet y Z)
        have e2 := decay_nonneg (locTail d) (G.distSet y' Z)
        have e3 := Real.exp_pos (locTail d * (pr + qr))
        have e4 := Real.exp_pos (2 * locTail d * c)
        have h12 : Real.exp (-(locTail d * (pr + c))) * Real.exp (-(locTail d * (qr + c))) ≤
            decay (locTail d) (G.distSet y Z) * decay (locTail d) (G.distSet y' Z) :=
          mul_le_mul d1 d2 (Real.exp_pos _).le e1
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h12 e4.le) e3.le

/-- **Tail times plain**: `(Dec with tail τ_Z) · Dec` has the tail `τ_Z`.  Rate loss `e / 8`. -/
theorem Dec.mul_tail {s₁ : ι₁ → G.Ω 1} {s₂ : ι₂ → G.Ω 1} {s₃ : ι₃ → G.Ω 1}
    {T : Matrix ι₁ ι₂ ℂ} {S : Matrix ι₂ ι₃ ℂ} {w w' : ℤ} {γ γT γS C₁ C₂ : ℝ}
    {Z : Finset (G.Ω 1)}
    (hd : 0 < d) (hϱ : 1 < ϱ) (hlog : Real.log L ≤ locKappa d * (ϱ - 1))
    (hμ : w.natAbs + w'.natAbs ≤ 4) (hγ : agmonRate d / 8 ≤ γ) (hT : γ ≤ γT) (hS : γ ≤ γS)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hTd : Dec G s₁ s₂ T w γT (tailZ G (locTail d) Z) C₁) (hSd : Dec G s₂ s₃ S w' γS noTail C₂) :
    Dec G s₁ s₃ (T * S) (w + w') (γ - agmonRate d / 8) (tailZ G (locTail d) Z)
      (cmpC d L (locTheta d) C₁ C₂ 1 (w.natAbs + w'.natAbs)) := by
  have he := agmonRate_pos hd
  have hκ := locKappa_mul_le hd _ hμ
  have hθ : 0 < locTheta d := by unfold locTheta; positivity
  have hγt : 0 ≤ locTail d := by unfold locTail; positivity
  refine Dec.comp (G := G) (T := T) (S := S) (τ₁ := tailZ G (locTail d) Z) (τ₂ := noTail)
    (τ := tailZ G (locTail d) Z) (γ := γ) (γ'' := γ - agmonRate d / 8) (θ := locTheta d)
    (ρ := locTail d) (κ := locKappa d) (B := 1)
    hϱ hlog hθ (locCount hd hϱ hlog) (by
      push_cast at hκ ⊢
      unfold locTheta locTail
      linarith) (by linarith) hC₁ hC₂ zero_le_one (tailZ_nonneg G _ Z) noTail_nonneg
    (tailZ_nonneg G _ Z) (fun _ => True) (fun _ _ _ x hx => absurd trivial hx) ?_
    (hTd.mono_rate (tailZ_nonneg G _ Z) hC₁ hT) (hSd.mono_rate noTail_nonneg hC₂ hS)
  intro y y' x _ hp hq
  set pr := (G.pathDist y x).toReal with hpr
  set qr := (G.pathDist x y').toReal with hqr
  have hp0 : 0 ≤ pr := ENNReal.toReal_nonneg
  have hq0 : 0 ≤ qr := ENNReal.toReal_nonneg
  have h1 : G.distSet y' Z ≤ G.pathDist x y' + G.distSet x Z := by
    rw [GeneratingSet.pathDist_comm x y']; exact distSet_le_add G Z y' x
  have h2 := decay_anti_dist hγt h1
  rw [decay_add_dist, decay_of_ne_top hq] at h2
  have h3 : decay (locTail d) (G.distSet x Z) ≤
      Real.exp (locTail d * (pr + qr)) * decay (locTail d) (G.distSet y' Z) := by
    have h4 : Real.exp (-(locTail d * qr)) * decay (locTail d) (G.distSet x Z) ≤
        decay (locTail d) (G.distSet y' Z) := h2
    have h5 : decay (locTail d) (G.distSet x Z) =
        Real.exp (locTail d * qr) * (Real.exp (-(locTail d * qr)) * decay (locTail d) (G.distSet x Z)) := by
      rw [← mul_assoc, ← Real.exp_add]; simp
    rw [h5]
    have h6 : Real.exp (locTail d * qr) ≤ Real.exp (locTail d * (pr + qr)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hγt)
    have hY := decay_nonneg (locTail d) (G.distSet x Z)
    calc Real.exp (locTail d * qr) * (Real.exp (-(locTail d * qr)) *
          decay (locTail d) (G.distSet x Z))
        ≤ Real.exp (locTail d * (pr + qr)) * (Real.exp (-(locTail d * qr)) *
          decay (locTail d) (G.distSet x Z)) :=
          mul_le_mul_of_nonneg_right h6 (mul_nonneg (Real.exp_pos _).le hY)
      _ ≤ _ := mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
  unfold tailZ noTail
  have hy0 := decay_nonneg (locTail d) (G.distSet y Z)
  calc decay (locTail d) (G.distSet y Z) * decay (locTail d) (G.distSet x Z) * 1
      = decay (locTail d) (G.distSet y Z) * decay (locTail d) (G.distSet x Z) := by ring
    _ ≤ decay (locTail d) (G.distSet y Z) * (Real.exp (locTail d * (pr + qr)) *
          decay (locTail d) (G.distSet y' Z)) := mul_le_mul_of_nonneg_left h3 hy0
    _ = _ := by ring

end Std

end Balaban.Multiscale
