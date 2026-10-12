/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiGeom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# (D1) for real data: `Ξ_k(𝔹; σ, ε) ⊆ Ψ̃(𝔹; C σ ε)` (P1 Lemma 3.1 at `λ = ∞`)

The field `φ = bgField` of a datum of `Ξ` satisfies the hypotheses `FieldBounds` of the composition
estimates with `η = (2d+1) σ ε`, for the *identity composition* `𝔹 ≺ 𝔹`, under which the composed
field (6.2) is the datum itself (`compVec_self`).  The estimates of `Lemma 6.2` then give (R2),
(R3) on `Ω₁`; (R1) is `interface_gen`; the collar is treated by hand.

* `Balaban.SmallField.xiEta`: `η = (2d+1) σ ε`;
* `Balaban.SmallField.xi_fieldBounds`: `Ξ ⇒ FieldBounds G η`;
* `Balaban.SmallField.xi_inPsiTilde`: **(D1) real**: `InPsiTilde G ν (C₄ η) Ψ₀ h₀`.

*Deviation from the notes.*  P1 Lemma 3.1 asserts the constant `3`.  With the one-site collar and
the `FieldBounds` machinery the constant is `C₄(d) (2d+1) = (4d+8)(2d+1)` (and smallness
`(4d+6) η ≤ 1`); the constant `3` would need the sharper block comparison of P1 pp. 121-122.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The size `η = (2d+1) σ ε` of the field bounds obtained from `Ξ(σ, ε)`. -/
noncomputable def xiEta (d : ℕ) (σ ε : ℝ) : ℝ := (2 * d + 1) * (σ * ε)

theorem precedes_refl (G : GeneratingSet d L N₀ k ϱ) : Precedes G G := fun _ _ _ => subset_rfl

section Identity

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ}

/-- **The identity composition**: for `𝔹 ≺ 𝔹` the composed field (6.2) is the datum. -/
theorem compVec_self (ha : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0) (D : BgData G N)
    (φ : G.Ω 1 × Fin N → ℂ) (x : Torus d (N₀ * L ^ k)) : compVec G G a φ D.Ψ x = D.Ψ x := by
  funext i
  unfold compVec
  by_cases hx : x ∈ G.Ω 1
  · rw [composeField_of_mem a φ D.Ψ hx i]
    obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec hx
    have han := ha _ hn1 hnk
    have hL : (0 : ℝ) < ((L : ℝ) ^ G.layerIndex x) ^ 2 := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    have e : a (G.layerIndex x) / a (G.layerIndex x) *
        (((L : ℝ) ^ G.layerIndex x) ^ 2 / ((L : ℝ) ^ G.layerIndex x) ^ 2) = 1 := by
      rw [div_self han, div_self hL.ne', one_mul]
    rw [e]; push_cast; ring
  · by_cases hc : x ∈ collar G
    · rw [composeField_of_collar a φ D.Ψ hc i]
      simp [barField, hx]
    · have hd : x ∉ dataSites G := fun h => ((mem_dataSites G).1 h).elim hx hc
      rw [composeField_of_not_mem a φ D.Ψ hd i, D.Ψ_zero x hd]
      rfl

end Identity

section Context

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ} {D : BgData G N}
  {h₀ : Fin N → ℝ} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}

theorem xi_smooth (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hX : XiBounds G ν n σ ε D h₀ φ α) : IsSmoothField G (σ * ε) (barVec G D.Ψ φ) where
  grad x hx μ := ⟨(hX.grad x hx μ).1.le, (hX.grad x hx μ).2.le⟩
  lap x hx := by
    refine (hX.lap x hx).le.trans ?_
    have hp : 0 < G.spacing x ^ 2 := by have := G.spacing_ge_one x; positivity
    refine div_le_div_of_nonneg_right ?_ hp.le
    nlinarith [mul_pos hσ hε]

theorem xi_mean (hX : XiBounds G ν n σ ε D h₀ φ α) {x : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) :
    vn (fun i => D.Ψ x i - blockMean G (G.layerIndex x) (fun y => barVec G D.Ψ φ y i) x) ≤
      σ ^ 2 * ε := by
  have h := (hX.close x hx).le
  have e : ∀ i, blockAvg G φ x i =
      blockMean G (G.layerIndex x) (fun y => barVec G D.Ψ φ y i) x := fun i => by
    have := blockMean_svec_eq_bar (G := G) (G' := G) D.Ψ φ (G.layerIndex x) x
      (fun y hy => (blk_mem_Ω1' (precedes_refl G) hx hy).2) i
    exact this
  simp only [e] at h
  exact h

theorem smooth_mono {f : Torus d (N₀ * L ^ k) → Fin N → ℂ} {A A' : ℝ}
    (hs : IsSmoothField G A f) (hA : A ≤ A') : IsSmoothField G A' f where
  grad x hx μ := by
    have hp : 0 < G.spacing x := by have := G.spacing_ge_one x; positivity
    obtain ⟨h1, h2⟩ := hs.grad x hx μ
    exact ⟨h1.trans (div_le_div_of_nonneg_right hA hp.le),
      h2.trans (div_le_div_of_nonneg_right hA hp.le)⟩
  lap x hx := by
    have hp : 0 < G.spacing x ^ 2 := by have := G.spacing_ge_one x; positivity
    exact (hs.lap x hx).trans (div_le_div_of_nonneg_right hA hp.le)

end Context

section FieldBoundsSection

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ} {n : ℕ} {D : BgData G N}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}

theorem xiEta_pos (hσ : 0 < σ) (hε : 0 < ε) : 0 < xiEta d σ ε := by
  unfold xiEta; positivity

theorem le_xiEta (hσ : 0 < σ) (hε : 0 < ε) : σ * ε ≤ xiEta d σ ε := by
  unfold xiEta
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_pos hσ hε]

/-- The real field of a datum of `Ξ` is a unit field with the bounds of Theorem 5.2 (3). -/
theorem xi_unit (H : BgHyp d L k ϱ a ν) (hX : XiAt G a ν n σ ε D Ψ₀ h₀) :
    (∀ (z : G.Ω 1) i, (bgField G a ν D (z, i)).im = 0) ∧
      ∀ z : G.Ω 1, ∑ i, bgField G a ν D (z, i) * bgField G a ν D (z, i) = 1 := by
  obtain ⟨-, hD, -⟩ := hX
  obtain ⟨-, hu, hs, -⟩ := theorem71 H hD
  exact ⟨fun z i => (hu z).1 i, hs.1.2⟩

theorem xi_fieldBounds (H : BgHyp d L k ϱ a ν) (hσ : 0 < σ) (hε : 0 < ε) (hσ1 : σ ≤ 1)
    (hX : XiAt G a ν n σ ε D Ψ₀ h₀) :
    FieldBounds G (xiEta d σ ε) D.Ψ (bgField G a ν D) := by
  have hb := hX.2.2
  have hs := xi_smooth hσ hε hσ1 hb
  have hA : 0 ≤ σ * ε := (mul_pos hσ hε).le
  have hsη := smooth_mono hs (le_xiEta (d := d) hσ hε)
  obtain ⟨-, hunit⟩ := xi_unit H hX
  refine ⟨fun z => ?_, hsη, hunit⟩
  have h1 := psi_sub_le (G := G) (f := barVec G D.Ψ (bgField G a ν D)) (ψ := D.Ψ) hA hs z.2
    (xi_mean hb z.2) (x_mem_blk (G := G) (G.layerIndex z.1) z.1)
  have e : (fun i => bgField G a ν D (z, i) - D.Ψ z i) =
      fun i => -(D.Ψ z i - barVec G D.Ψ (bgField G a ν D) z i) := by
    funext i; simp [barVec, barField, z.2]
  rw [e, vn_neg]
  refine h1.trans ?_
  unfold xiEta
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith [mul_pos hσ hε, mul_nonneg this (mul_pos hσ hε).le]

end FieldBoundsSection

section D1

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν σ ε : ℝ} {D : BgData G N}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} {φ : G.Ω 1 × Fin N → ℂ}
  {α : G.Ω 1 → ℂ}

omit [NeZero L] [NeZero N₀] in
theorem weights_ne (H : BgHyp d L k ϱ a ν) : ∀ j, 1 ≤ j → j ≤ k → a j ≠ 0 := fun j h1 h2 => by
  have := (H.weights j h1 h2).1
  intro h; rw [h] at this; norm_num at this

theorem realizes_vn {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (hR : Realizes D Ψ₀ h₀) {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G)
    (hx' : x' ∈ dataSites G) :
    vn (D.Ψ x - D.Ψ x') = rn (fun i => Ψ₀ x i - Ψ₀ x' i) := by
  have e : D.Ψ x - D.Ψ x' = (fun i => (Ψ₀ x i : ℂ)) - fun i => (Ψ₀ x' i : ℂ) := by
    funext i; simp [hR.1 x hx i, hR.1 x' hx' i]
  rw [e, vn_cast_sub]

theorem realizes_layerConst (hR : Realizes D Ψ₀ h₀) : IsLayerConstant G Ψ₀ := by
  intro n hn1 hnk x hx x' hx'
  funext i
  have hxΩ : x ∈ G.Ω 1 := G.layer_subset hn1 hnk hx
  have hx'l : x' ∈ G.layer n := (G.mem_layer_iff hn1 hnk (GeneratingSet.mem_blk.1 hx')).2 hx
  have hx'Ω : x' ∈ G.Ω 1 := G.layer_subset hn1 hnk hx'l
  have := congrFun (D.Ψ_layerConst n hn1 hnk x hx x' hx') i
  rw [hR.1 x' ((mem_dataSites G).2 (Or.inl hx'Ω)) i, hR.1 x ((mem_dataSites G).2 (Or.inl hxΩ)) i]
    at this
  exact_mod_cast this

/-- The mass bound of `Ξ` at a site of layer `m ≤ k`: `ν L^{2m} | |h₀|² - 1 | < (σ ε)²`. -/
theorem hnorm_layer (hν : 0 ≤ ν) (hb : XiBounds G ν k σ ε D h₀ φ α) (x : Torus d (N₀ * L ^ k)) :
    ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * |∑ i, h₀ i ^ 2 - 1| < (σ * ε) ^ 2 := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  refine lt_of_le_of_lt ?_ hb.hnorm
  refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
    (pow_le_pow_right₀ hL1 (layerIndex_le_k G x)) 2) hν

end D1

end Balaban.SmallField
