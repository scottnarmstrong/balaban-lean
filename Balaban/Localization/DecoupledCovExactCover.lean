/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovClose
public import Balaban.Localization.DecoupledCovLocal

/-!
# Agreement of `Z = Ĝ - Π` for two backgrounds, from agreement of the Green function

The common core of the two locality statements for the decoupled correction `Z_{α,φ,s}`:
`DecoupledCovLocal2` (cover chain `LocHyp`, two backgrounds, mass bound) and `BaseXLocal`
(`decZ_exact`, one background, abstract dichotomy).  Both prove that `Ĝ` agrees on `Y` for inputs
agreeing on `R ⊆ Y`; everything else is the same chain:

* `Gvec_agree`: the vector form of the agreement of `Ĝ`;
* `commK_Gvec_agree`, `decN_agree`, `decM_agree`: the commutator term, `N` and `M` agree on `R`
  when the backgrounds agree (`α` on `R`, `φ` on `Y`) and the rows of the operator `H_x` from `R`
  stay in `Y`;
* `decZ_agree`: the fixed point of the contraction `u ↦ N w + u - M u` on `R`, and then `Z`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Core

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x₀ ν : ℝ}
variable {N : ℕ} {φ φ' : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {α α' : G.Ω 1 → ℂ}
  {s s' : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {R Y : Finset (CTorus d L N₁ m₁ (k + 1))}

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

section Agree

variable
  (hG : ∀ g g' : G.Ω 1 → ℂ,
    (∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → g y = g' y) →
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
      (Gsx G a aT x₀ ν α s *ᵥ g) y = (Gsx G a aT x₀ ν α' s' *ᵥ g') y)
  (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ R → α x = α' x)
  (hφY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
  (hRY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y)
  (hrow : ∀ z y : G.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∈ R →
    xDirichletOperator G a aT x₀ ν α z y ≠ 0 → (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y)

omit hA hφY hRY hrow in
include hG in
/-- The vector form of the agreement of `Ĝ` on `Y`. -/
theorem Gvec_agree {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → ∀ i, w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w) (y, i) =
        (liftOp N (Gsx G a aT x₀ ν α' s') *ᵥ w') (y, i) := by
  intro y hy i
  rw [liftOp_mulVec, liftOp_mulVec]
  exact hG (fun b => w (b, i)) (fun b => w' (b, i)) (fun b hb => hw b hb i) y hy

include hG hA hφY hRY hrow

theorem commK_Gvec_agree {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ R) :
    (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w)) z =
      (commK (xDirichletOperator G a aT x₀ ν α') (restrictField G φ') *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α' s') *ᵥ w')) z := by
  refine commK_apply_eq2 (xDirichlet_apply_eq (hA z hz)) (hφY z (hRY z hz)) ?_
  intro y hy
  have hyY := hrow z y hz hy
  exact ⟨hφY y hyY, fun i => Gvec_agree hG hw y hyY i⟩

theorem decN_agree {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ R) :
    (decN G a aT x₀ ν α s φ *ᵥ w) z = (decN G a aT x₀ ν α' s' φ' *ᵥ w') z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ w) z =
      ((fieldMul (restrictField G φ'))ᵀ *ᵥ w') z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hφY z (hRY z hz)
    simp only [restrictField]
    rw [this, hw z hz i]
  rw [e1, commK_Gvec_agree hG hA hφY hRY hrow hw hz]

theorem decM_agree {v v' : G.Ω 1 → ℂ}
    (hv : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → v y = v' y)
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ R) :
    (decM G a aT x₀ ν α s φ *ᵥ v) z = (decM G a aT x₀ ν α' s' φ' *ᵥ v') z := by
  rw [decM_mulVec_eq, decM_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ (fieldMul (restrictField G φ) *ᵥ v)) z =
      ((fieldMul (restrictField G φ'))ᵀ *ᵥ (fieldMul (restrictField G φ') *ᵥ v')) z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fieldMul_mulVec, fieldMul_mulVec, hv z hz]
    simp only [restrictField]
    rw [hφY z (hRY z hz)]
  have e2 := commK_Gvec_agree hG hA hφY hRY hrow
    (w := fieldMul (restrictField G φ) *ᵥ v) (w' := fieldMul (restrictField G φ') *ᵥ v')
    (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]
      simp only [restrictField]
      rw [hφY y (hRY y hy)]) hz
  rw [e1, e2]

section ZAgree

variable {δ κ Cx Cx' : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x₀ α κ s Cx)
  (D' : Dec2.XData (coverOf G) G a aT ν x₀ α' κ s' Cx')
  (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include D D' hφ hφ' hδ hsm

/-- **Agreement of `Z = Ĝ - Π` for two backgrounds.**  If `Ĝ` agrees on `Y` for sources agreeing
on `R ⊆ Y`, `α = α'` on `R`, `φ = φ'` on `Y`, and the rows of `H_x` from `R` stay in `Y`, then
`w = w'` on `R` gives `Z_{α,φ,s} w = Z_{α',φ',s'} w'` on all of `Y`. -/
theorem decZ_agree {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ R → ∀ i, w (y, i) = w' (y, i)) :
    ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → ∀ i,
      (decZ G a aT x₀ ν α s φ *ᵥ w) (y, i) = (decZ G a aT x₀ ν α' s' φ' *ᵥ w') (y, i) := by
  classical
  have H0 : XWeight G 0 (fun _ => 0) := D.weight_zero
  have H0' : XWeight G 0 (fun _ => 0) := D'.weight_zero
  have hMs := decM_isUnit_cover D hφ hδ hsm
  have hMs' := decM_isUnit_cover D' hφ' hδ hsm
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
    refine (decM_error_le_cover D H0 hφ hδ (u - v)).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hc' : ∀ u, agmonSource G 0 (fun _ => 0) (T' u - v') ≤
      (1 / 4) * agmonSource G 0 (fun _ => 0) (u - v') := by
    intro u
    rw [hTv']
    refine (decM_error_le_cover D' H0' hφ' hδ (u - v')).trans ?_
    exact mul_le_mul_of_nonneg_right hsm (hS0 _)
  have hag : ∀ u u' : G.Ω 1 → ℂ,
      (∀ z ∈ {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ R}, u z = u' z) →
      ∀ z ∈ {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ R}, T u z = T' u' z := by
    intro u u' huu z hz
    have hz' : (z : CTorus d L N₁ m₁ (k + 1)) ∈ R := hz
    subst hT hT'
    show (decN G a aT x₀ ν α s φ *ᵥ w + u - decM G a aT x₀ ν α s φ *ᵥ u) z =
      (decN G a aT x₀ ν α' s' φ' *ᵥ w' + u' - decM G a aT x₀ ν α' s' φ' *ᵥ u') z
    simp only [Pi.sub_apply, Pi.add_apply]
    rw [decN_agree hG hA hφY hRY hrow hw hz', huu z hz,
      decM_agree hG hA hφY hRY hrow (fun y hy => huu y hy) hz']
  have hfix := fixed_point_agree T T' v v' {z : G.Ω 1 | (z : CTorus d L N₁ m₁ (k + 1)) ∈ R}
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
  have e1 := Gvec_agree hG hw y hy i
  have e2 := Gvec_agree hG (w := fieldMul (restrictField G φ) *ᵥ v)
    (w' := fieldMul (restrictField G φ') *ᵥ v') (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hfix y hy]
      simp only [restrictField]
      rw [hφY y (hRY y hy)]) y hy i
  rw [hZ α s φ w v hv, hZ α' s' φ' w' v' hv', Pi.sub_apply, Pi.sub_apply, e1, e2]

end ZAgree

end Agree

end Core

end Balaban.Localization
