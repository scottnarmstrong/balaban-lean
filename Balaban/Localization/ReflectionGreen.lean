/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectionOperator
public import Balaban.Multiscale.CutAgmon
import Mathlib.Tactic.Linarith

/-!
# The Green's function identity (NC3, Lemma R4)

* `Balaban.Reflection.cubeOf_blockAligned`: the folded cube is `BlockAligned`, so that the cube cut
  is `CutAligned` (`cubeCut_aligned`);
* `Balaban.Reflection.reflU_inv`: the even extension of `u = H_cut(α)⁻¹ f` is
  `H*_D(α∘F)⁻¹ (E f)`, for every source `f` on `Ω₁`.
-/

@[expose] public section

namespace Balaban.Reflection

open Matrix Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

theorem mem_cubeOf_of_jBlock_eq (h : FoldSetting G q s c) {j : ℕ} (hjq : j ≤ q)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ cubeOf N₀ L k q s c)
    (hb : jBlock d L N₀ k j x' = jBlock d L N₀ k j x) : x' ∈ cubeOf N₀ L k q s c := by
  classical
  obtain ⟨p, rfl⟩ := exists_foldMap_eq (ℓ := N₀ * L ^ k) (two_mul_side L q s) hx
  obtain ⟨himg, -⟩ := image_fold_block h hjq p
  have : x' ∈ Finset.univ.filter (fun x' : Torus d (N₀ * L ^ k) =>
      jBlock d L N₀ k j x' = jBlock d L N₀ k j (foldTo N₀ L k q s c p)) :=
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hb⟩
  rw [← himg] at this
  obtain ⟨p', -, rfl⟩ := Finset.mem_image.1 this
  exact foldTo_mem_cubeOf p'

/-- The folded cube is a union of blocks of every layer that it meets. -/
theorem cubeOf_blockAligned (h : FoldSetting G q s c) :
    BlockAligned G (cubeOf N₀ L k q s c) := by
  intro j hj1 hjk x x' hx hb
  by_cases hjq : j ≤ q
  · exact ⟨fun hxc => mem_cubeOf_of_jBlock_eq h hjq hxc hb,
      fun hxc => mem_cubeOf_of_jBlock_eq h hjq hxc hb.symm⟩
  · have hx' := layer_of_jBlock_eq G hj1 hjk hx hb
    have hxΩ : x ∈ G.Ω (q + 1) :=
      G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 hx).1
    have hxΩ' : x' ∈ G.Ω (q + 1) :=
      G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 hx').1
    exact ⟨fun hxc => absurd hxΩ (h.noTop x hxc), fun hxc => absurd hxΩ' (h.noTop x' hxc)⟩

theorem cubeCut_aligned' (h : FoldSetting G q s c) :
    CutAligned G (cubeCut G (cubeOf N₀ L k q s c)) :=
  cubeCut_aligned G (cubeOf_blockAligned h)

theorem reflAlpha_bound (h : FoldSetting G q s c) {α : G.Ω 1 → ℂ} {B : ℝ}
    (hα : ∀ x, ‖α x‖ ≤ B / (2 * (G.spacing x) ^ 2)) (p : (reflectedGS G h).Ω 1) :
    ‖reflAlpha h α p‖ ≤ B / (2 * ((reflectedGS G h).spacing p) ^ 2) := by
  rw [spacing_reflectedGS h]
  exact hα _

omit [NeZero s] in
theorem isAdmissibleWeights_refl (h : FoldSetting G q s c) {a : ℕ → ℝ}
    (ha : IsAdmissibleWeights k a) : IsAdmissibleWeights q a :=
  fun j hj1 hjq => ha j hj1 (hjq.trans h.q_le)

/-- **Lemma R4 (the Green's function identity).** The even extension of `H_cut(α)⁻¹ f` is
`H*_D(α∘F)⁻¹ (E f)`. -/
theorem reflU_inv (h : FoldSetting G q s c) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (f : G.Ω 1 → ℂ) :
    reflU h ((cutOperator G a ν (cubeCut G (cubeOf N₀ L k q s c)) α)⁻¹ *ᵥ f) =
      (dirichletOperator (reflectedGS G h) a ν (reflAlpha h α))⁻¹ *ᵥ reflU h f := by
  have hU := dirichletOperator_isUnit (reflectedGS G h) hd hν (isAdmissibleWeights_refl h ha)
    (reflAlpha h α) (reflAlpha_bound h hα)
  have heq : dirichletOperator (reflectedGS G h) a ν (reflAlpha h α) *ᵥ
      reflU h ((cutOperator G a ν (cubeCut G (cubeOf N₀ L k q s c)) α)⁻¹ *ᵥ f) = reflU h f := by
    funext p
    rw [operator_intertwine h a ν α]
    have := cutOperator_mulVec_inv G (cubeCut_aligned' h) hd hν ha α hα f
    rw [this]
    rfl
  rw [← heq, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]

end Balaban.Reflection
