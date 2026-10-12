/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovLocal2Free

/-!
# I-4c (v), narrow agreement: locality of `C^{1/2}` on the rows of the interaction boxes

Parallel versions of `I4c_local_sqrt2` and `I4c_local_sqrt3` (FOOTPRINT, package 3b, item 4).  Write
`B = S_Y` and `R(B)` (`rowsCov_R`) for `B` together with the sites at which a row of the `x`-variant
Dirichlet operator at a site of `B` has a nonzero entry.  The background field is compared on `R(B)`
only (instead of all of `Y`), the multipliers on `B`, and the hat inputs on the unit points whose
`(k+1)`-block lies in `Y` (instead of those and the blocks meeting `S_Y`), given that `Y` is a union
of complete `(k+1)`-blocks (`CompleteBlocks`).  The fluctuation and fan versions (FOOTPRINT items 6, 7)
and the physical-reads lemma are not proved here.  The landed theorems are unchanged.

## Where the landed proofs use agreement (`DecoupledCovLocal2`, line numbers of that file)

| use | set on which agreement is needed |
| --- | --- |
| `commK_Gvec_local2` l.84, field at the centre `z` of the row | `z ∈ B` |
| `commK_Gvec_local2` l.87, field at the row sites `y` (entries `≠ 0` of `xDirichletOperator` at `z ∈ B`) | `R(B)` |
| `commK_Gvec_local2` l.87, `Gvec_local2` at row sites (`dg5x'_inner`) | the data `w` and `α` on `B` only; `row_in_Y` is used only to place `y` in `Y` |
| `decN_local2` l.98, `decM_local2` l.114, l.120 (field in `fieldMul`, `restrictField`) | `z ∈ B` |
| `decZ_local2` l.197-198 (fixed-point step), l.216 (field in the final identity) | `B` |
| `decCov_local2` `t0`, `t1` (`unitP` reads one `(k+1)`-block) | hat input on the `UnitOut` blocks |
| `decCov_local2` `z1`, `z2` (`unitQ` reads one `k`-block) | hat input on the blocks meeting `B` (`UnitIn`) |

The field is never needed outside `R(B)`; `α` is never needed outside `B`.  The hat input is read
on `UnitOut` blocks and on `UnitIn` blocks (blocks meeting `B`); with `CompleteBlocks` every
`UnitIn` block is a `UnitOut` block (`unitOut_of_unitIn_or`).  No block straddling the boundary of
`Y`, and no neighbour's block, is read in the `UnitOut` setting; so nothing contradicts the note.
The free branch of `I4c_local_sqrt3` (`decCov_free`) uses no field and no multiplier agreement.
In `hatPsiF_local` (HatEngineLocal) `blockThick Y` is needed for the conclusion at neighbours of
`Y` and, inside `Y`, only where the `(k+1)`-block of the site is not inside `Y`; under
`CompleteBlocks` it is needed for neighbours only.
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

/-- The sites read by the rows of the `x`-variant Dirichlet operator (`xDirichletOperator`, for some
`x ≥ 0`) at the sites of `B = S_Y`, together with `B` itself: the set `R(B)` of the field
comparison.  It depends on the multiplier `α` only through which matrix entries vanish. -/
def rowsCov_R (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν : ℝ)
    (α : G.Ω 1 → ℂ) (X₁ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))) (Y : Finset (CTorus d L N₁ m₁ (k + 1))) :
    Set (CTorus d L N₁ m₁ (k + 1)) :=
  {u | u ∈ SY G X₁ 𝒞 Y ∨ ∃ z y : G.Ω 1, (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y ∧
    (y : CTorus d L N₁ m₁ (k + 1)) = u ∧ ∃ x₀ : ℝ, 0 ≤ x₀ ∧
      xDirichletOperator G a aT x₀ ν α z y ≠ 0}

/-- Every site of `Y` has its whole `(k+1)`-block (in `Ω₁`) inside `Y`: `Y` is a union of complete
`(k+1)`-blocks. -/
def CompleteBlocks (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Y : Finset (CTorus d L N₁ m₁ (k + 1))) : Prop :=
  ∀ y y' : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y →
    unitBlock1 (unitBlock (y' : CTorus d L N₁ m₁ (k + 1))) =
      unitBlock1 (unitBlock (y : CTorus d L N₁ m₁ (k + 1))) → (y' : CTorus d L N₁ m₁ (k + 1)) ∈ Y

theorem unitOut_of_unitIn_or {Y : Finset (CTorus d L N₁ m₁ (k + 1))}
    {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ (k + 1))}
    (hc : CompleteBlocks G Y) {b : unitPts G} (hb : UnitOut G Y b ∨ UnitIn G X₁ 𝒞 Y b) :
    UnitOut G Y b := by
  rcases hb with hb | ⟨y, hy, hyb⟩
  · exact hb
  · intro y' hy'
    exact hc y y' (SY_subset hy) (hy'.trans hyb.symm)

section ZLocal

variable (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s') (hα' : AdmPot G α')
  (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
  (hφR : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y → φ y = φ' y)
  (hU : IsUnit (1 - Kcalx G a aT x₀ ν α s)) (hU' : IsUnit (1 - Kcalx G a aT x₀ ν α' s'))
include S hx H hα' hA hφR hU hU'

theorem commK_Gvec_rows {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (commK (xDirichletOperator G a aT x₀ ν α) (restrictField G φ) *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α s) *ᵥ w)) z =
      (commK (xDirichletOperator G a aT x₀ ν α') (restrictField G φ') *ᵥ
        (liftOp N (Gsx G a aT x₀ ν α' s') *ᵥ w')) z := by
  refine commK_apply_eq2 (xDirichlet_apply_eq (hA z hz)) (hφR z (Or.inl hz)) ?_
  intro y hy
  have hyY := row_in_Y S hz hy
  exact ⟨hφR y (Or.inr ⟨z, y, hz, rfl, x₀, hx, hy⟩), fun i => Gvec_local2 S hx H hα' hA hU hU' hw y hyY i⟩

theorem decN_rows {w w' : G.Ω 1 × Fin N → ℂ}
    (hw : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → ∀ i, w (y, i) = w' (y, i))
    {z : G.Ω 1} (hz : (z : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y) :
    (decN G a aT x₀ ν α s φ *ᵥ w) z = (decN G a aT x₀ ν α' s' φ' *ᵥ w') z := by
  rw [decN_mulVec_eq, decN_mulVec_eq, Pi.sub_apply, Pi.sub_apply]
  have e1 : ((fieldMul (restrictField G φ))ᵀ *ᵥ w) z =
      ((fieldMul (restrictField G φ'))ᵀ *ᵥ w') z := by
    rw [fieldMul_transpose_mulVec, fieldMul_transpose_mulVec]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := hφR z (Or.inl hz)
    simp only [restrictField]
    rw [this, hw z hz i]
  rw [e1, commK_Gvec_rows S hx H hα' hA hφR hU hU' hw hz]

theorem decM_rows {v v' : G.Ω 1 → ℂ}
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
    rw [hφR z (Or.inl hz)]
  have e2 := commK_Gvec_rows S hx H hα' hA hφR hU hU'
    (w := fieldMul (restrictField G φ) *ᵥ v) (w' := fieldMul (restrictField G φ') *ᵥ v')
    (fun y hy i => by
      rw [fieldMul_mulVec, fieldMul_mulVec, hv y hy]
      simp only [restrictField]
      rw [hφR y (Or.inl hy)]) hz
  rw [e1, e2]

end ZLocal

section ZLocal2

variable {δ κ : ℝ} (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
  (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
  (hφR : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y → φ y = φ' y)
  (D : XData G a aT ν x₀ α κ s) (D' : XData G a aT ν x₀ α' κ s')
  (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
include S hx H hA hφR D D' hφ hφ' hδ hsm

/-- **Two-background locality of `Z_s = Ĝ_s - Π_s`.**  If `w = w'` on `S_Y`, `α = α'` on `S_Y` and
`φ = φ'` on `Y`, then `Z_{α,φ,s} w = Z_{α',φ',s'} w'` on all of `Y ∩ Ω₁`. -/
theorem decZ_rows {w w' : G.Ω 1 × Fin N → ℂ}
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
    rw [decN_rows S hx H hα' hA hφR hU hU' hw hz', huu z hz,
      decM_rows S hx H hα' hA hφR hU hU' (fun y hy => huu y hy) hz']
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
      rw [hφR y (Or.inl hy)]) y hy i
  rw [hZ α s φ w v hv, hZ α' s' φ' w' v' hv', Pi.sub_apply, Pi.sub_apply, e1, e2]

end ZLocal2

section UnitLocal2

open MeasureTheory Set

variable {δ κ : ℝ}

/-- **I-4c (v), two backgrounds, at fixed `x`.**  If `α = α'` on `S_Y`, `φ = φ'` on `Y`, and the
inputs agree on the unit points at the output block and on the blocks meeting `S_Y`, then
`C_x(α, φ, s)` and `C_x(α', φ', s')` agree at every unit point whose `(k+1)`-block lies in `Y`. -/
theorem decCov_rows (S : XSetting G a aT ν) (hx : 0 ≤ x₀) (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφR : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y → φ y = φ' y)
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
  have z3 := decZ_rows S hx H hA hφR D D' hφ hφ' hδ hsm z2
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

/-- **Rows version of `I4c_local_sqrt2`, landed form of the hat hypothesis.**  Only the field
hypothesis is narrowed: `φ = φ'` on `R(B)` instead of on `Y`. -/
theorem I4c_local_sqrt2_rows (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α' κ s')
    (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφR : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y →
      φ y = φ' y)
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
    rw [decCov_rows S hx0 H hA hφR (hfam x hx0) (hfam' x hx0) hφ hφ' hδ hsm h h' hh b hb i]
  simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
  rw [e1, e2, e3]

/-- **Rows version of `I4c_local_sqrt2`.**  The background field is compared only on `R(B)`
(`rowsCov_R`), the multipliers `α, α'` on `B = S_Y`, and the hat inputs only at the unit points
whose `(k+1)`-block lies in `Y`; the hypothesis `hcomp` says that the `(k+1)`-block of every site of
`Y` lies in `Y`.  The conclusion is that of `I4c_local_sqrt2`. -/
theorem I4c_local_sqrt_rows (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α' κ s')
    (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφR : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y →
      φ y = φ' y)
    (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcomp : CompleteBlocks G Y)
    (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, UnitOut G Y b' → ∀ i, h (b', i) = h' (b', i))
    {b : unitPts G} (hb : UnitOut G Y b) (i : Fin N) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) :=
  I4c_local_sqrt2_rows hfam hfam' H hA hφR hφ hφ' hδ hsm h h'
    (fun b' hb' i' => hh b' (unitOut_of_unitIn_or hcomp hb') i') hb i

/-- **T5.**  `I4c_local_sqrt2` from `I4c_local_sqrt2_rows`, when `R(B) ⊆ Y`. -/
theorem I4c_local_sqrt2_of_rows_subset (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α' κ s')
    (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hRY : ∀ u ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y, u ∈ Y)
    (hφY : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Y → φ y = φ' y)
    (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (h h' : unitPts G × Fin N → ℂ)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ UnitIn G X₁ 𝒞 Y b') → ∀ i, h (b', i) = h' (b', i))
    {b : unitPts G} (hb : UnitOut G Y b) (i : Fin N) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) :=
  I4c_local_sqrt2_rows hfam hfam' H hA (fun y hy => hφY y (hRY _ hy)) hφ hφ' hδ hsm h h' hh hb i

end UnitLocal2

section Sqrt3

open MeasureTheory Set

variable {δ κ : ℝ}

/-- **Rows version of `I4c_local_sqrt3`** (the `FreeBlk` setting).  The free branch uses no field
agreement.  The `UnitOut` branch is `I4c_local_sqrt_rows`; under `CompleteBlocks` the free branch is
not needed for blocks inside `Y`, and is kept for the blocks next to `Y`. -/
theorem I4c_local_sqrt3_rows (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s)
    (hfam' : ∀ x, 0 ≤ x → XData G a aT ν x α' κ s')
    (H : LocHyp G X₁ 𝒞 Y α s s')
    (hA : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ (k + 1)) ∈ SY G X₁ 𝒞 Y → α x = α' x)
    (hφR : ∀ y : G.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ rowsCov_R G a aT ν α X₁ 𝒞 Y →
      φ y = φ' y)
    (hφ : IsConstraintField G δ φ) (hφ' : IsConstraintField G δ φ') (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcomp : CompleteBlocks G Y)
    (h h' : unitPts G × Fin N → ℂ) {b : unitPts G}
    (hb : UnitOut G Y b ∨ FreeBlk G s s' b)
    (hh : ∀ b' : unitPts G, (UnitOut G Y b' ∨ unitBlock1 b.1 = unitBlock1 b'.1) →
      ∀ i, h (b', i) = h' (b', i))
    (i : Fin N) :
    (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ h) (b, i) =
      (decCovSqrt G a aT ν α' s' φ' (unitQ G) (unitP G) *ᵥ h') (b, i) := by
  rcases hb with hb | hb
  · exact I4c_local_sqrt_rows hfam hfam' H hA hφR hφ hφ' hδ hsm hcomp h h'
      (fun b' hb' => hh b' (Or.inl hb')) hb i
  · classical
    have Hs := (standing_pair hfam hφ hδ hsm).1
    have Hs' := (standing_pair hfam' hφ' hδ hsm).1
    have e1 := intMat_mulVec_apply (integrable_decSqrtInt Hs) h (b, i)
    have e2 := intMat_mulVec_apply (integrable_decSqrtInt Hs') h' (b, i)
    have e3 : ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x *ᵥ h) (b, i) =
        ∫ x in Ioi (0:ℝ), (decSqrtInt G a aT ν α' s' φ' (unitQ G) (unitP G) x *ᵥ h') (b, i) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
      simp only [decSqrtInt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
      rw [decCov_free b hb h h' (fun b' hb' => hh b' (Or.inr hb')) i]
    simp only [decCovSqrt, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul]
    rw [e1, e2, e3]

end Sqrt3

end Two

end Balaban.Localization
