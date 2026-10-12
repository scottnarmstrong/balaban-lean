/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FarDecay
public import Balaban.Background.WeightedProp51Basic
public import Balaban.Localization.Decoupled2Close
public import Balaban.Localization.Decoupled2Dg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The weighted form of BG Proposition 5.1 (corrected statement `WeightedProp51S`)

`WeightedProp51` of `Balaban/Fluctuation/FarDecay.lean` (landed, left untouched) is not provable as
stated: it lacks the defect condition `g = φ₀·φ₀ - 1 = 0` on `Ω₁` (with a zero source and a nonzero
defect the solution of the perturbed system moves, contradicting the weighted bound `K_w · 0`), and
its separation hypothesis (`GreenSetting`, `agmonRate/4`) is weaker than the separation
`OpSetting` (`agmonRate/16`) required by the weighted Green bound `Dec2.dirichlet_weighted`.
`WeightedProp51S` below carries both premises as source/typing premises and is proved
(`weightedProp51S_exists`) for `3 ≤ d`, `3 ≤ L`; it supersedes `WeightedProp51`.

Proof: the unweighted solution of `prop51_exists_unique` is the given one (uniqueness); `δφ` is
the Green's function applied to `F_s - δα φ₀`, hence weighted by `dirichlet_weighted`; `δα = 𝒩(δφ)`
(identity (5.2) and the constraint), weighted by `commK_weighted`, `Rvec_bound_weighted`; the
resulting inequality is absorbed on `A* = inf {r ≥ 0 | SmallW δα r}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Basic

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {w : CTorus d L N₁ m₁ K → ℝ}

theorem SupBoundsW.mono {u : G.Ω 1 × Fin N → ℂ} {V V' : ℝ} (h : SupBoundsW G w u V)
    (hV : V ≤ V') : SupBoundsW G w u V' := by
  refine ⟨fun x i => (h.val x i).trans hV, fun x hx μ i => (h.fwd x hx μ i).trans hV,
    fun x hx μ i => (h.bwd x hx μ i).trans hV, fun x hx i => (h.lap x hx i).trans hV⟩

theorem SupBoundsW.star {u : G.Ω 1 × Fin N → ℂ} {V : ℝ} (h : SupBoundsW G w u V)
    (hV : 0 ≤ V) : StarBoundW G w u V := by
  refine ⟨fun y i => ?_, h.fwd, h.bwd⟩
  by_cases hy : y ∈ G.Ω 1
  · simpa [svec_of_mem (G := G) u ⟨y, hy⟩ i] using h.val ⟨y, hy⟩ i
  · rw [svec_of_not_mem G u hy, norm_zero, mul_zero]; exact hV

/-- The backward difference bound from the forward one, for a weight of rate `γ ≥ 0`
(constant `L e^γ`; the sites outside `Ω₁` have layer index `1`). -/
theorem bwd_of_fwd {γ : ℝ} (hγ : 0 ≤ γ) (hw : IsWeight G γ w) (hϱ : 1 < ϱ) (hL : 1 ≤ L)
    {u : G.Ω 1 × Fin N → ℂ} {V : ℝ} (hV : 0 ≤ V)
    (hval : ∀ (x : G.Ω 1) (i : Fin N), w x * ‖u (x, i)‖ ≤ V)
    (hfwd : ∀ x ∈ G.Ω 1, ∀ (μ : Fin d) (i : Fin N),
      w x * (G.spacing x * ‖svec G u (x + Pi.single μ 1) i - svec G u x i‖) ≤ V)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1) (μ : Fin d) (i : Fin N) :
    w x * (G.spacing x * ‖svec G u (x - Pi.single μ 1) i - svec G u x i‖) ≤
      (L * Real.exp γ) * V := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hE : 1 ≤ Real.exp γ := Real.one_le_exp hγ
  have hwx := hw.pos x
  have hLE : 0 ≤ (L : ℝ) * Real.exp γ := by positivity
  by_cases hp : x - Pi.single μ 1 ∈ G.Ω 1
  · set p := x - Pi.single μ 1 with hpdef
    have hadj : Adj p x := by
      have := adj_add_single p μ
      rwa [hpdef, sub_add_cancel] at this
    have h1 := hfwd p hp μ i
    have hpe : p + Pi.single μ 1 = x := by rw [hpdef, sub_add_cancel]
    rw [hpe] at h1
    have hsp : G.spacing x ≤ L * G.spacing p := spacing_adj_le G hϱ.le hp hx hadj
    have hwp : w x ≤ w p * Real.exp γ := by
      have := (weight_adj_le hγ hw hp hx hadj).2
      refine (this.trans ?_)
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (hw.pos p).le
      have hb := G.bondCost_le_inv_left p x
      have := G.spacing_ge_one p
      have h3 : 1 / G.spacing p ≤ 1 := by
        rw [div_le_one (by linarith)]; exact this
      nlinarith
    rw [norm_sub_rev]
    have hn : 0 ≤ ‖svec G u x i - svec G u p i‖ := norm_nonneg _
    have hspx := (G.spacing_ge_one x)
    calc w x * (G.spacing x * ‖svec G u x i - svec G u p i‖)
        ≤ (w p * Real.exp γ) * ((L * G.spacing p) * ‖svec G u x i - svec G u p i‖) :=
          mul_le_mul hwp (mul_le_mul_of_nonneg_right hsp hn)
            (mul_nonneg (spacing_pos G).le hn) (mul_nonneg (hw.pos p).le (Real.exp_pos γ).le)
      _ = (L * Real.exp γ) * (w p * (G.spacing p * ‖svec G u x i - svec G u p i‖)) := by ring
      _ ≤ (L * Real.exp γ) * V := mul_le_mul_of_nonneg_left h1 hLE
  · rw [svec_of_not_mem G u hp, zero_sub, norm_neg, svec_of_mem G u ⟨x, hx⟩ i]
    have hadj : Adj x (x - Pi.single μ 1) := adj_sub_single x μ
    have hs := spacing_le_of_adj_not_mem G hϱ hL hx hp hadj
    have := hval ⟨x, hx⟩ i
    calc w x * (G.spacing x * ‖u (⟨x, hx⟩, i)‖) ≤ w x * (L * ‖u (⟨x, hx⟩, i)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs (norm_nonneg _)) hwx.le
      _ = L * (w x * ‖u (⟨x, hx⟩, i)‖) := by ring
      _ ≤ L * V := mul_le_mul_of_nonneg_left this (by linarith)
      _ ≤ (L * Real.exp γ) * V := by
          refine mul_le_mul_of_nonneg_right ?_ hV
          nlinarith

end Basic

section Green

/-- **The weighted Green's function bound for vector sources** (`Dec2.dirichlet_weighted`
componentwise; the constant includes the backward-difference factor `L e^{γ_w}`).  The
separation is `OpSetting` (`agmonRate/16`). -/
theorem weighted_green_vec (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Bw : ℝ, 0 ≤ Bw ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, Dec2.OpSetting G a ν →
      ∀ {α : G.Ω 1 → ℂ}, AdmPot G α → ∀ {w : CTorus d L N₁ m₁ K → ℝ},
      IsWeight G (gammaW d) w → ∀ (g : G.Ω 1 × Fin N → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ (x : G.Ω 1) (i : Fin N), w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖g (x, i)‖) ≤
        Cb) →
      SupBoundsW G w (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) (Bw * Cb) := by
  obtain ⟨Bd, hBd, hDw⟩ := Dec2.dirichlet_weighted (d := d) (L := L) hd hL
  have hd0 : 0 < d := by omega
  have hγ0 := gammaW_nonneg hd0
  have hL1 : 1 ≤ L := by omega
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  refine ⟨L * Real.exp (gammaW d) * Bd, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν S α hα w hw g Cb hCb hg
  have hϱ := S.one_lt_rho
  have hcomp := fun i : Fin N => hDw G S hα hw (comp G g i) hCb (fun x => by
    show w x * (G.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖g (x, i)‖ ≤ Cb
    rw [mul_assoc]; exact hg x i)
  have hE : 1 ≤ L * Real.exp (gammaW d) := by
    have := Real.one_le_exp hγ0
    nlinarith
  have hBC : Bd * Cb ≤ L * Real.exp (gammaW d) * Bd * Cb := by
    have := mul_nonneg hBd hCb
    nlinarith
  have hs : ∀ y i, svec G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) y i =
      solExt G (dirichletOperator G a ν α)⁻¹ (comp G g i) y :=
    fun y i => svec_liftOp _ g i y
  have hval : ∀ (x : G.Ω 1) (i : Fin N),
      w x * ‖(liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) (x, i)‖ ≤ Bd * Cb := by
    intro x i
    have := (hcomp i).1 x.2
    rw [← svec_of_mem G (liftOp N (dirichletOperator G a ν α)⁻¹ *ᵥ g) x i, hs]
    exact this
  have hBdC : 0 ≤ Bd * Cb := mul_nonneg hBd hCb
  refine ⟨fun x i => (hval x i).trans hBC, fun x hx μ i => ?_, fun x hx μ i => ?_,
    fun x hx i => ?_⟩
  · simp only [hs]
    exact ((hcomp i).2.1 hx μ).trans hBC
  · have := bwd_of_fwd (G := G) hγ0 hw hϱ hL1 hBdC hval (fun x hx μ i => by
      simp only [hs]; exact ((hcomp i).2.1 hx μ)) hx μ i
    refine this.trans ?_
    calc (L : ℝ) * Real.exp (gammaW d) * (Bd * Cb) = L * Real.exp (gammaW d) * Bd * Cb := by ring
      _ ≤ _ := le_rfl
  · simp only [hs]
    exact ((hcomp i).2.2 hx).trans hBC

end Green

section Main

/-- The infimum `A*` of the admissible weighted radii of `δα`. -/
theorem exists_smallW_inf (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (w : CTorus d L N₁ m₁ K → ℝ) (δα : G.Ω 1 → ℂ) (hw : ∀ x, 0 ≤ w x) :
    ∃ A : ℝ, 0 ≤ A ∧ SmallW G w δα A ∧ ∀ r : ℝ, 0 ≤ r → SmallW G w δα r → A ≤ r := by
  classical
  set S : Set ℝ := {r | 0 ≤ r ∧ SmallW G w δα r} with hS
  have hne : S.Nonempty := by
    refine ⟨∑ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖),
      Finset.sum_nonneg fun x _ => mul_nonneg (hw x) (mul_nonneg (by positivity) (norm_nonneg _)),
      fun x => ?_⟩
    exact Finset.single_le_sum (f := fun x : G.Ω 1 =>
      w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖))
      (fun y _ => mul_nonneg (hw y) (mul_nonneg (by positivity) (norm_nonneg _)))
      (Finset.mem_univ x)
  have hbdd : BddBelow S := ⟨0, fun r hr => hr.1⟩
  refine ⟨sInf S, le_csInf hne fun r hr => hr.1, fun x => le_csInf hne fun r hr => hr.2 x,
    fun r hr hsm => csInf_le hbdd ⟨hr, hsm⟩⟩

/-- **The corrected weighted form of BG Proposition 5.1** (rate `γ_w = gammaW d`).

For the data of Proposition 5.1 (`Prop51Hyp`, sizes `δ₀, δ₁ ≤ δ_w`) with the defect
`g = φ₀·φ₀ - 1` vanishing on `Ω₁` (true when `φ₀` solves (EL)) and the separation of
`OpSetting` (the weighted Green's function bound), every weight `w` of rate `γ_w`, every source
with `w ℓ² |F_s| ≤ C` and every solution `(δφ, δα)` of the perturbed system with `|δα|₂ ≤ c₆`:
`w ℓ² |δα| ≤ K_w C` and the weighted `SupBoundsW` of `δφ` with `K_w C`. -/
def WeightedProp51S (d L N : ℕ) [NeZero L] (Kw δw : ℝ) : Prop :=
  ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ)
    (ν : ℝ) (α₀ : G.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ) (δ₀ δ₁ : ℝ),
    Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁ → Dec2.OpSetting G a ν → (∀ x : G.Ω 1, gdef G φ₀ x = 0) →
    δ₀ ≤ δw → δ₁ ≤ δw →
    ∀ (w : CTorus d L N₁ m₁ K → ℝ), IsWeight G (gammaW d) w → ∀ C : ℝ, 0 ≤ C →
    (∀ (x : G.Ω 1) (i : Fin N), w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖pertSource G a δΨ f₁ (x, i)‖) ≤ C) →
    ∀ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
    IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ δα →
    Small G δα (c6 d L N) → SmallW G w δα (Kw * C) ∧ SupBoundsW G w δφ (Kw * C)

end Main

section Pointwise

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} {α₀ : G.Ω 1 → ℂ}
  {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} {δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ}
  {f₁ : G.Ω 1 × Fin N → ℂ} {δ₀ δ₁ : ℝ}

/-- `δα = 𝒩(δφ)` for a solution of the perturbed system with vanishing defect. -/
theorem delta_alpha_eq (hg : ∀ x : G.Ω 1, gdef G φ₀ x = 0) {δφ : G.Ω 1 × Fin N → ℂ}
    {δα : G.Ω 1 → ℂ} (hpert : IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ δα)
    (x : G.Ω 1) :
    δα x = ∑ i, (φ₀ x i + δφ (x, i)) * pertSource G a δΨ f₁ (x, i)
      - (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x
      + (1 / 2) * Rvec (dirichletOperator G a ν α₀) δφ δφ x := by
  have hu : ∀ y : G.Ω 1, 2 * ∑ i, φ₀ y i * δφ (y, i) + ∑ i, δφ (y, i) * δφ (y, i) +
      gdef G φ₀ y = 0 := fun y => (constraint_iff_u φ₀ δφ y).1 (hpert.2 y)
  have hg0 : gdef G φ₀ = 0 := funext hg
  have h52 := identity52 a ν α₀ δα φ₀ (pertSource G a δΨ f₁) δφ hpert.1 x
  have hu0 : (fun y : G.Ω 1 => 2 * ∑ i, φ₀ y i * δφ (y, i) +
      ∑ i, δφ (y, i) * δφ (y, i) + gdef G φ₀ y) = 0 := funext hu
  have hz : (dirichletOperator G a ν (α₀ + 2 * δα) *ᵥ fun y : G.Ω 1 =>
      2 * ∑ i, φ₀ y i * δφ (y, i) + ∑ i, δφ (y, i) * δφ (y, i) + gdef G φ₀ y) = 0 := by
    rw [hu0, Matrix.mulVec_zero]
  rw [congrFun hz x] at h52
  have h2 : (2 : ℂ) * (Nmap G (dirichletOperator G a ν α₀) true φ₀ (pertSource G a δΨ f₁)
      δφ x - δα x) = 0 := by simpa using h52.symm
  have h3 := sub_eq_zero.1 ((mul_eq_zero.1 h2).resolve_left (by norm_num))
  unfold Nmap at h3
  simp only [↓reduceIte, hg0, Matrix.mulVec_zero, Pi.zero_apply, mul_zero, add_zero] at h3
  exact h3.symm

/-- The weighted pointwise bound of `δα = 𝒩(δφ)`. -/
theorem delta_alpha_weighted (hP : Prop51Hyp G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁)
    (hg : ∀ x : G.Ω 1, gdef G φ₀ x = 0) {w : CTorus d L N₁ m₁ K → ℝ}
    (hw : IsWeight G (gammaW d) w) (hγpos : 0 < gammaW d) {C V κ : ℝ} (hV0 : 0 ≤ V) (hκ0 : 0 ≤ κ)
    (hFs : ∀ (x : G.Ω 1) (i : Fin N), w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖pertSource G a δΨ f₁ (x, i)‖) ≤ C)
    {δφ : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ}
    (hpert : IsPerturbed G a ν α₀ φ₀ (pertSource G a δΨ f₁) δφ δα)
    (hstar : StarBoundW G w δφ V) (hSup : StarBound G δφ κ) (x : G.Ω 1) :
    w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖) ≤
      N * ((3 / 2 + κ) * C) + commKConstW d N (gammaW d) * δ₀ * V +
        1 / 2 * (N * (RConstW d (gammaW d) * (V * κ))) := by
  have hγ0 := hγpos.le
  have hα01 : ∀ x : G.Ω 1, G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖α₀ x‖ ≤ 1 :=
    fun x => (hP.alpha0 x).trans (hP.δ₀_le.trans deltaStar_le_one)
  have hp : 0 ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
  have hwx : 0 ≤ w x := (hw.pos x).le
  have t1 : w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖∑ i, (φ₀ x i + δφ (x, i)) * pertSource G a δΨ f₁ (x, i)‖) ≤ N * ((3 / 2 + κ) * C) := by
    calc _ ≤ w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          ∑ i, ‖(φ₀ x i + δφ (x, i)) * pertSource G a δΨ f₁ (x, i)‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (norm_sum_le _ _) hp) hwx
      _ = ∑ i, ‖φ₀ x i + δφ (x, i)‖ * (w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          ‖pertSource G a δΨ f₁ (x, i)‖)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [norm_mul]; ring
      _ ≤ ∑ _i : Fin N, ((3 / 2 + κ) * C) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (hP.phiBd x x.2)
          have h2 : ‖δφ (x, i)‖ ≤ κ := by simpa [svec_of_mem] using hSup.val x i
          exact mul_le_mul ((norm_add_le _ _).trans (add_le_add h1 h2)) (hFs x i)
            (by positivity) (by positivity)
      _ = _ := by simp
  have t2 := commK_weighted hγpos hw hP.green.weights ν α₀ hP.smooth hP.δ₀_nn hV0 hstar x
  have t3 := Rvec_bound_weighted hγ0 hw hP.green.weights hP.green.mass hP.green.massLe hα01
    hV0 hκ0 hstar hSup x
  rw [delta_alpha_eq hg hpert x]
  calc w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖∑ i, (φ₀ x i + δφ (x, i)) * pertSource G a δΨ f₁ (x, i) -
          (commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x +
          1 / 2 * Rvec (dirichletOperator G a ν α₀) δφ δφ x‖)
      ≤ w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        (‖∑ i, (φ₀ x i + δφ (x, i)) * pertSource G a δΨ f₁ (x, i)‖ +
        ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x‖ +
        1 / 2 * ‖Rvec (dirichletOperator G a ν α₀) δφ δφ x‖)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hp) hwx
        refine (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) ?_)
        simp only [norm_mul, norm_div, norm_one, Complex.norm_ofNat]
        exact le_of_eq (by ring)
    _ = w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖∑ i, (φ₀ x i + δφ (x, i)) * pertSource G a δΨ f₁ (x, i)‖) +
        w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖(commK (dirichletOperator G a ν α₀) (restrictField G φ₀) *ᵥ δφ) x‖) +
        1 / 2 * (w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
        ‖Rvec (dirichletOperator G a ν α₀) δφ δφ x‖)) := by ring
    _ ≤ _ := by linarith

end Pointwise


section Exists

variable (N) in
/-- **`WeightedProp51S` holds** for some `K_w, δ_w > 0` (`3 ≤ d`, `3 ≤ L`). -/
theorem weightedProp51S_exists (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ WeightedProp51S d L N Kw δw := by
  classical
  obtain ⟨Bw, hBw, hGreen⟩ := weighted_green_vec (N := N) hd hL
  have hd0 : 0 < d := by omega
  have hγ0 : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hγpos : 0 < gammaW d := by unfold gammaW; have := agmonRate_pos hd0; positivity
  set K2 := cK2 d L N with hK2def
  have hK2 : 0 ≤ K2 := by
    have := cB1_ge d L; have := cF_pos d L; have := cN_pos d L N
    rw [hK2def]; unfold cK2; positivity
  set cw := commKConstW d N (gammaW d) with hcw
  set rw' := RConstW d (gammaW d) with hrw
  have hcw0 : 0 ≤ cw := commKConstW_nonneg _ _ _
  have hrw0 : 0 ≤ rw' := RConstW_nonneg _ _
  set E := Bw * (cw + N * rw' * K2) with hE
  have hE0 : 0 ≤ E := by positivity
  have hds := deltaStar_pos d L N hd0
  set δw := min (min (deltaStar d L N) 1) (1 / (3 * E + 1)) with hδw
  have hδw0 : 0 < δw := lt_min (lt_min hds one_pos) (by positivity)
  have hδw1 : δw ≤ 1 := (min_le_left _ _).trans (min_le_right _ _)
  have hδws : δw ≤ deltaStar d L N := (min_le_left _ _).trans (min_le_left _ _)
  have hEδ : E * δw ≤ 1 / 3 := by
    have h1 : δw ≤ 1 / (3 * E + 1) := min_le_right _ _
    calc E * δw ≤ E * (1 / (3 * E + 1)) := mul_le_mul_of_nonneg_left h1 hE0
      _ = E / (3 * E + 1) := by ring
      _ ≤ 1 / 3 := by rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  set c0 : ℝ := N * (3 / 2 + K2) + 1 / 3 with hc0
  have hN0 : (0 : ℝ) ≤ N * (3 / 2 + K2) := by positivity
  have hc00 : 1 / 3 ≤ c0 := by rw [hc0]; linarith
  set Kw : ℝ := 2 * c0 + Bw * (1 + 3 * c0) with hKw
  refine ⟨Kw, δw, by rw [hKw]; have := mul_nonneg hBw (by linarith : (0 : ℝ) ≤ 1 + 3 * c0); linarith,
    hδw0, ?_⟩
  intro N₁ m₁ K _ ϱ G a ν α₀ φ₀ δΨ f₁ δ₀ δ₁ hP hOp hg hδ₀ hδ₁ w hw C hC hFs δφ δα hpert hsmall
  have hw0 : ∀ x, 0 ≤ w x := fun x => (hw.pos x).le
  -- the unweighted solution
  obtain ⟨δφs, δαs, -, hSm, hSup, huniq⟩ := prop51_exists_unique hd0 hP
  obtain ⟨e1, e2⟩ := huniq δφ δα hpert hsmall
  subst e1 e2
  set κ := K2 * δ₁ with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg hK2 hP.δ₁_nn
  have hκK : κ ≤ K2 := by
    rw [hκ]; nlinarith [(hδ₁.trans hδw1), hK2]
  have hκδ : κ ≤ K2 * δw := mul_le_mul_of_nonneg_left hδ₁ hK2
  -- polydisc
  have hc6 : c6 d L N ≤ gamma1 d / 4 := min_le_left _ _
  have hδ₀s : δ₀ ≤ gamma1 d / 4 := hP.δ₀_le.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hα1 : Small G (α₀ + δα) (gamma1 d) := fun x =>
    (((show Small G α₀ δ₀ from hP.alpha0).add hsmall) x).trans
      (by have := gamma1_pos hd0; linarith)
  have hdφ := (isPerturbed_dphi_iff hP.green hα1 δφ).1 hpert.1
  -- A*
  obtain ⟨A, hA0, hAsm, hAmin⟩ := exists_smallW_inf G w δα hw0
  set Cb : ℝ := C + 3 / 2 * A with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  -- weighted source of the linear problem
  have hsrc : ∀ (x : G.Ω 1) (i : Fin N), w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖Fsrc φ₀ (pertSource G a δΨ f₁) δα (x, i)‖) ≤ Cb := by
    intro x i
    have hφ : ‖φ₀ x i‖ ≤ 3 / 2 := (norm_le_vn _ i).trans (hP.phiBd x x.2)
    have hp : 0 ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 := by positivity
    have hwx := hw0 x
    calc w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          ‖Fsrc φ₀ (pertSource G a δΨ f₁) δα (x, i)‖)
        ≤ w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          (‖pertSource G a δΨ f₁ (x, i)‖ + ‖δα x‖ * ‖φ₀ x i‖)) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hp) hwx
          refine (norm_sub_le _ _).trans ?_
          rw [norm_mul]
      _ = w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖pertSource G a δΨ f₁ (x, i)‖) +
          (w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖)) * ‖φ₀ x i‖ := by ring
      _ ≤ C + A * (3 / 2) := add_le_add (hFs x i)
          (mul_le_mul (hAsm x) hφ (norm_nonneg _) hA0)
      _ = Cb := by rw [hCb]; ring
  have hGr := hGreen G hOp (alpha_mem_polydisc hα1) hw (Fsrc φ₀ (pertSource G a δΨ f₁) δα)
    hCb0 hsrc
  have hδφeq : δφ = liftOp N (dirichletOperator G a ν (α₀ + δα))⁻¹ *ᵥ
      Fsrc φ₀ (pertSource G a δΨ f₁) δα := hdφ
  rw [← hδφeq] at hGr
  have hV0 : 0 ≤ Bw * Cb := mul_nonneg hBw hCb0
  have hstar := hGr.star hV0
  have hpt : ∀ x : G.Ω 1, w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 * ‖δα x‖) ≤
      c0 * C + 1 / 2 * A := by
    intro x
    have key := delta_alpha_weighted hP hg hw hγpos hV0 hκ0 hFs hpert hstar
      (Balaban.Background.SupBounds.star hSup) x
    refine key.trans ?_
    have hs : cw * δ₀ + 1 / 2 * (N * (rw' * κ)) ≤ (cw + N * rw' * K2) * δw := by
      have h1 : cw * δ₀ ≤ cw * δw := mul_le_mul_of_nonneg_left hδ₀ hcw0
      have h2 : N * (rw' * κ) ≤ N * (rw' * (K2 * δw)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hκδ hrw0) (by positivity)
      have h3 : (0 : ℝ) ≤ N * (rw' * (K2 * δw)) := by positivity
      nlinarith
    have h4 : cw * δ₀ * (Bw * Cb) + 1 / 2 * (N * (rw' * ((Bw * Cb) * κ))) =
        (Bw * Cb) * (cw * δ₀ + 1 / 2 * (N * (rw' * κ))) := by ring
    have h5 : (Bw * Cb) * (cw * δ₀ + 1 / 2 * (N * (rw' * κ))) ≤
        (Bw * Cb) * ((cw + N * rw' * K2) * δw) :=
      mul_le_mul_of_nonneg_left hs hV0
    have h6 : (Bw * Cb) * ((cw + N * rw' * K2) * δw) = Cb * (E * δw) := by
      rw [hE]; ring
    have h7 : Cb * (E * δw) ≤ Cb * (1 / 3) := mul_le_mul_of_nonneg_left hEδ hCb0
    have h8 : N * ((3 / 2 + κ) * C) ≤ N * ((3 / 2 + K2) * C) := by
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hC) (by positivity)
      linarith
    have h9 : Cb * (1 / 3) = 1 / 3 * C + 1 / 2 * A := by rw [hCb]; ring
    have h10 : c0 * C = N * ((3 / 2 + K2) * C) + 1 / 3 * C := by rw [hc0]; ring
    linarith
  -- absorption
  have hAle : A ≤ c0 * C + 1 / 2 * A := hAmin _ (by positivity) hpt
  have hA2 : A ≤ 2 * c0 * C := by linarith
  have hKwC : 2 * c0 * C ≤ Kw * C := by
    refine mul_le_mul_of_nonneg_right ?_ hC
    rw [hKw]; have := mul_nonneg hBw (by linarith : (0 : ℝ) ≤ 1 + 3 * c0); linarith
  refine ⟨fun x => (hpt x).trans (by linarith), ?_⟩
  refine hGr.mono ?_
  have : Bw * Cb ≤ Bw * ((1 + 3 * c0) * C) := by
    refine mul_le_mul_of_nonneg_left ?_ hBw
    rw [hCb]; linarith
  refine this.trans ?_
  rw [hKw]
  have h1 : 0 ≤ 2 * c0 * C := by positivity
  linarith [mul_nonneg hBw (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + 3 * c0) hC)]

end Exists

end Balaban.Fluctuation
