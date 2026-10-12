/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovLocal

/-!
# I-4c (v), two backgrounds: locality of `C^{1/2}` in `(α, φ, s)`

The theorems of `DecoupledCovLocal` fix one background `(α, φ)` and compare two parameter vectors.
Here both the background and the parameters may differ: if `α = α'` on `S_Y`, `φ = φ'` on `Y`,
and `s`, `s'` agree on the parameters meeting `Y`, the decoupled covariance `C_x`, and its square
root, agree at the unit points whose `(k+1)`-block lies in `Y` (inputs agreeing on the unit
points of the output blocks and of the blocks meeting `S_Y`).  The proof is that of
`DecoupledCovLocal`, the background difference vanishing on the region.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Two

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
variable {N : ℕ} {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α α' : G.Ω 1 → ℂ}
  {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {X₁ Y : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}

theorem xDirichlet_apply_eq {z : G.Ω 1} (h : α z = α' z) (y : G.Ω 1) :
    xDirichletOperator G a aT x₀ ν α z y = xDirichletOperator G a aT x₀ ν α' z y := by
  unfold xDirichletOperator
  simp only [Matrix.add_apply, Matrix.diagonal_apply]
  by_cases hzy : z = y
  · subst hzy; simp [h]
  · simp [hzy]

theorem commK_apply_eq2 {ι : Type*} [Fintype ι] [DecidableEq ι] {H H' : Matrix ι ι ℂ}
    {ψ ψ' : ι → Fin N → ℂ} {u u' : ι × Fin N → ℂ} {z : ι}
    (hH : ∀ y, H z y = H' z y) (hz : ψ z = ψ' z)
    (h : ∀ y, H z y ≠ 0 → ψ y = ψ' y ∧ ∀ i, u (y, i) = u' (y, i)) :
    (commK H ψ *ᵥ u) z = (commK H' ψ' *ᵥ u') z := by
  rw [commK_mulVec, commK_mulVec]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  by_cases h0 : H z y = 0
  · rw [← hH y, h0]; simp
  · obtain ⟨h1, h2⟩ := h y h0
    rw [← hH y, h2 i, h1, hz]

theorem Gvec_local2 (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
    (hα' : AdmPot G α')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x₀ ν α' s'))
    {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w) (y, i) =
        (liftOp N (Gsx G a aT x₀ ν α' s') *ᵥ w') (y, i) := by
  intro y hy i
  rw [liftOp_mulVec, liftOp_mulVec]
  exact dg5x'_inner S hx H.conn H.nn H.pot hα' hU hU' H.s1 H.s0 H.ag hA
    (f := fun b => w (b, i)) (f' := fun b => w' (b, i)) (fun b hb => hw b hb i) y hy

section ZLocal

variable (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s') (hα' : AdmPot G α')
  (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
  (hφ : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
  (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x₀ ν α' s'))
include S hx H hα' hA hφ hU hU'

theorem commK_Gvec_local2 {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w)) z =
      (commK (xDirichletOperator G a aT x₀ ν α') (restrictField G φ') *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α' s') *ᵥ w')) z := by
  refine commK_apply_eq2 (xDirichlet_apply_eq (hA z hz)) (hφ z (SY_subset hz)) ?_
  intro y hy
  have hyY := row_in_Y S hz hy
  exact ⟨hφ y hyY, fun i => Gvec_local2 S hx H hα' hA hU hU' hw y hyY i⟩

theorem decN_local2 {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (decN G a aT x₀ ν α s φ *ᵥ w) z = (decN G a aT x₀ ν α' s' φ' *ᵥ w') z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ w) z =
      ((fieldMul (restrictField G φ'))ᵀ *ᵥ w') z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hφ z (SY_subset hz)
    simp only [restrictField]
    rw [this, hw z hz i]
  rw [e1, commK_Gvec_local2 S hx H hα' hA hφ hU hU' hw hz]

theorem decM_local2 {v v' : G.Ω 1 → ℂ}
    (hv : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → v y = v' y)
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (decM G a aT x₀ ν α s φ *ᵥ v) z = (decM G a aT x₀ ν α' s' φ' *ᵥ v') z := by
  rw [decM_mulVec_eq, decM_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v)) z =
      ((fieldMul (restrictField G φ'))ᵀ *ᵥ (fieldMul (restrictField G φ') *ᵥ v')) z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fieldMul_mulVec, fieldMul_mulVec, hv z hz]
    simp only [restrictField]
    rw [hφ z (SY_subset hz)]
  have e2 := commK_Gvec_local2 S hx H hα' hA hφ hU hU'
    (w := fieldMul (restrictField G φ) *ᵥ v) (w' := fieldMul (restrictField G φ') *ᵥ v')
    (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]
      simp only [restrictField]
      rw [hφ y (SY_subset hy)]) hz
  rw [e1, e2]

end ZLocal

section ZLocal2

variable {δ κ : ℝ} (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
  (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
  (hφY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
  (D : XData G a aT ν x₀ α κ s) (D' : XData G a aT ν x₀ α' κ s')
  (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include S hx H hA hφY D D' hφ hφ' hδ hsm

/-- **Two-background locality of `Z_s = Ĝ_s - Π_s`.**  If `w = w'` on `S_Y`, `α = α'` on `S_Y` and
`φ = φ'` on `Y`, then `Z_{α,φ,s} w = Z_{α',φ',s'} w'` on all of `Y ∩ Ω₁`. -/
theorem decZ_local2 {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (decZ G a aT x₀ ν α s φ *ᵥ w) (y, i) = (decZ G a aT x₀ ν α' s' φ' *ᵥ w') (y, i) := by
  classical
  have hU := D.isUnit_one_sub
  have hU' := D'.isUnit_one_sub
  have hα' := D'.pot
  have H0 : XWeight G 0 (fun _ => 0) := D.weight_zero
  have H0' : XWeight G 0 (fun _ => 0) := D'.weight_zero
  have hMs := decM_isUnit D hφ hδ hsm
  have hMs' := decM_isUnit D' hφ' hδ hsm
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hMs
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hMs'
  obtain ⟨v, hv⟩ : ∃ v : G.Ω 1 → ℂ, v = (decM G a aT x₀ ν α s φ)⁻¹ *ᵥ
      (decN G a aT x₀ ν α s φ *ᵥ w) := ⟨_, rfl⟩
  obtain ⟨v', hv'⟩ : ∃ v : G.Ω 1 → ℂ, v = (decM G a aT x₀ ν α' s' φ')⁻¹ *ᵥ
      (decN G a aT x₀ ν α' s' φ' *ᵥ w') := ⟨_, rfl⟩
  have hMv : decM G a aT x₀ ν α s φ *ᵥ v = decN G a aT x₀ ν α s φ *ᵥ w := by
    rw [hv, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hMv' : decM G a aT x₀ ν α' s' φ' *ᵥ v' = decN G a aT x₀ ν α' s' φ' *ᵥ w' := by
    rw [hv', Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mulVec]
  obtain ⟨T, hT⟩ : ∃ T : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ), T = fun u =>
      decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u := ⟨_, rfl⟩
  obtain ⟨T', hT'⟩ : ∃ T : (G.Ω 1 → ℂ) → (G.Ω 1 → ℂ), T = fun u =>
      decN G a aT x₀ ν α' s' φ' *ᵥ w' + u - decM G a aT x₀ ν α' s' φ' *ᵥ u := ⟨_, rfl⟩
  have hTv : ∀ u, T u - v = (u - v) - decM G a aT x₀ ν α s φ *ᵥ (u - v) := by
    intro u
    subst hT
    show decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u - v = _
    rw [Matrix.mulVec_sub, hMv]
    abel
  have hTv' : ∀ u, T' u - v' = (u - v') - decM G a aT x₀ ν α' s' φ' *ᵥ (u - v') := by
    intro u
    subst hT'
    show decN G a aT x₀ ν α' s' φ' *ᵥ w' + u - decM G a aT x₀ ν α' s' φ' *ᵥ u - v' = _
    rw [Matrix.mulVec_sub, hMv']
    abel
  have hS0 := agmonSource_nonneg G 0 (fun _ => 0)
  have hc : ∀ u, agmonSource G 0 (fun _ => 0) (T u - v) ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v) := by
    intro u
    rw [hTv]
    refine (decM_error_le D H0 hφ hδ (u - v)).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hc' : ∀ u, agmonSource G 0 (fun _ => 0) (T' u - v') ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v') := by
    intro u
    rw [hTv']
    refine (decM_error_le D' H0' hφ' hδ (u - v')).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hag : ∀ u u' : G.Ω 1 → ℂ,
      (∀ z ∈ {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y}, u z = u' z) →
      ∀ z ∈ {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y}, T u z = T' u' z := by
    intro u u' huu z hz
    have hz' : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y := hz
    subst hT hT'
    show (decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u) z =
      (decN G a aT x₀ ν α' s' φ' *ᵥ w' + u' - decM G a aT x₀ ν α' s' φ' *ᵥ u') z
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [decN_local2 S hx H hα' hA hφY hU hU' hw hz', huu z hz,
      decM_local2 S hx H hα' hA hφY hU hU' (fun y hy => huu y hy) hz']
  have hfix := fixed_point_agree T T' v v' {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y}
    hc hc' hag
  intro y hy i
  have hZ : ∀ (aa : G.Ω 1 → ℂ) (ss : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ)
      (pp : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) (ww : G.Ω 1 × Fin N → ℂ) (Mi : G.Ω 1 → ℂ),
      Mi = (decM G a aT x₀ ν aa ss pp)⁻¹ *ᵥ (decN G a aT x₀ ν aa ss pp *ᵥ ww) →
      decZ G a aT x₀ ν aa ss pp *ᵥ ww = liftOp N (Gsx G a aT x₀ ν aa ss) *ᵥ ww -
        liftOp N (Gsx G a aT x₀ ν aa ss) *ᵥ (fieldMul (restrictField G pp) *ᵥ Mi) := by
    intro aa ss pp ww Mi hMi
    unfold decZ decPi
    rw [Matrix.sub_mulVec, hMi]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have e1 := Gvec_local2 S hx H hα' hA hU hU' hw y hy i
  have e2 := Gvec_local2 S hx H hα' hA hU hU' (w := fieldMul (restrictField G φ) *ᵥ v)
    (w' := fieldMul (restrictField G φ') *ᵥ v') (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hfix y hy]
      simp only [restrictField]
      rw [hφY y (SY_subset hy)]) y hy i
  rw [hZ α s φ w v hv, hZ α' s' φ' w' v' hv', Pi.sub_apply, Pi.sub_apply, e1, e2]

end ZLocal2

section UnitLocal2

open MeasureTheory Set

variable {δ κ : ℝ}

/-- **I-4c (v), two backgrounds, at fixed `x`.**  If `α = α'` on `S_Y`, `φ = φ'` on `Y`, and the
inputs agree on the unit points at the output block and on the blocks meeting `S_Y`, then
`C_x(α, φ, s)` and `C_x(α', φ', s')` agree at every unit point whose `(k+1)`-block lies in `Y`. -/
theorem decCov_local2 (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
    (D : XData G a aT ν x₀ α κ s) (D' : XData G a aT ν x₀ α' κ s')
    (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b') → ∀ i, h (b', i) = h' (b', i)) :
    ∀ b : unitPts G, UnitOut G Y b → ∀ i,
      (decCov G a aT x₀ ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
        (decCov G a aT x₀ ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  classical
  intro b hb i
  rw [decCov_mulVec_eq, decCov_mulVec_eq, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  have hbo : ∀ b3 : unitPts G, unitP G b b3 ≠ 0 → UnitOut G Y b3 := by
    intro b3 hP y hy
    exact hb y (hy.trans (unitP_ne_zero_imp hP).symm)
  have t0 : (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h) (b, i) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h') (b, i) := by
    refine covA_apply_congr _ _ _ _ _ _ _ (hh b (Or.inl hb) i) ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact hh b3 (Or.inl (hbo b3 hP)) _
  have z1 : ∀ b2 : unitPts G, (∃ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y ∧
      unitBlock (y : CTorus d L N₁ m₁ (k + 1)) = b2.1) → ∀ j,
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h) (b2, j) =
        (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h') (b2, j) := by
    rintro b2 ⟨y, hy, hyb⟩ j
    have hin : UnitIn G X₁ 𝒞 Y b2 := ⟨y, hy, by rw [hyb]⟩
    refine covA_apply_congr _ _ _ _ _ _ _ (hh b2 (Or.inr hin) j) ?_
    rintro ⟨b3, j'⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    refine hh b3 (Or.inr ⟨y, hy, ?_⟩) _
    rw [hyb]; exact unitP_ne_zero_imp hP
  have z2 : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ j,
      ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h)) (y, j) =
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h')) (y, j) := by
    intro y hy j
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨b2, j'⟩ hq
    rw [liftRect_transpose] at hq
    obtain ⟨hj, hQ⟩ := liftRect_ne_zero_imp _ hq
    simp only at hj hQ
    subst hj
    exact z1 b2 ⟨y, hy, unitQ_ne_zero_imp (by simpa using hQ)⟩ _
  have z3 := decZ_local2 S hx H hA hφY D D' hφ hφ' hδ hsm z2
  have z4 : ∀ b3 : unitPts G, UnitOut G Y b3 → ∀ j,
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h))))
        (b3, j) =
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α' s' φ' *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h'))))
        (b3, j) := by
    intro b3 hb3 j
    refine mulVec_apply_congr _ _ _ _ ?_
    rintro ⟨y, j'⟩ hq
    obtain ⟨hj, hQ⟩ := liftRect_ne_zero_imp _ hq
    simp only at hj hQ
    subst hj
    exact z3 y (hb3 y (by rw [unitQ_ne_zero_imp hQ])) _
  have t1 : (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α s φ *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h)))))
        (b, i) =
      (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ
      (liftRect N (unitQ G) *ᵥ (decZ G a aT x₀ ν α' s' φ' *ᵥ
        ((liftRect N (unitQ G))ᵀ *ᵥ (covA (a k) (aT / (L : ℝ) ^ 2) x₀ (liftOp N (unitP G)) *ᵥ h')))))
        (b, i) := by
    refine covA_apply_congr _ _ _ _ _ _ _ (z4 b hb i) ?_
    rintro ⟨b3, j⟩ hq
    obtain ⟨hj, hP⟩ := liftOp_ne_zero_imp _ hq
    simp only at hj hP
    subst hj
    exact z4 b3 (hbo b3 hP) _
  rw [t0, t1]

/-- **I-4c (v), two backgrounds: locality of `C^{1/2}`** (comparison form).  For `α = α'` on `S_Y`,
`φ = φ'` on `Y`, parameters `s`, `s'` agreeing on the cubes meeting `Y`, and inputs agreeing on the
unit points of the output blocks and of the blocks meeting `S_Y`, the outputs of
`C^{1/2}(α, φ, s)` and `C^{1/2}(α', φ', s')` agree at the unit points with `(k+1)`-block in `Y`. -/
theorem I4c_local_sqrt2 (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α' κ s')
    (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
    (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b') → ∀ i, h (b', i) = h' (b', i))
    {b : unitPts G} (hb : UnitOut G Y b) (i : Fin N) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  classical
  have Hs := (standing_pair hfam hφ hδ hsm).1
  have Hs' := (standing_pair hfam' hφ' hδ hsm).1
  have S := (hfam 0 le_rfl).st
  have e1 := intMat_mulVec_apply (integrable_decSqrtInt Hs) h (b, i)
  have e2 := intMat_mulVec_apply (integrable_decSqrtInt Hs') h' (b, i)
  have e3 : ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x *ᵥ h) (b, i) =
      ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α' s' φ' (unitQ G) (unitP G) x *ᵥ h') (b, i) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 ≤ x := (mem_Ioi.mp hx).le
    simp only [decSqrtInt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [decCov_local2 S hx0 H hA hφY (hfam x hx0) (hfam' x hx0) hφ hφ' hδ hsm h h' hh b hb i]
  simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, e3]

end UnitLocal2

end Two

end Balaban.Localization
