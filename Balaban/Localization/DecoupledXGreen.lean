/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledXBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

/-!
# (DG1), (DG2) for the x-variant decoupled Green's operator, weighted `L²` form

* `XData`, `XWeight`: the standing hypotheses and the weight data;
* `XData.dg1`: `‖ℓ w 𝒦_{x,s} f‖² ≤ (1/16) ‖ℓ w f‖²`;
* `XData.isUnit_one_sub`, `XData.neumann_src`: `1 - 𝒦_{x,s}` is invertible and
  `‖ℓ w (1 - 𝒦)⁻¹ f‖² ≤ (16/9) ‖ℓ w f‖²`;
* `XData.dg2_cwsq`: `‖ℓ⁻¹ w G_{k,x,s} f‖² ≤ B ‖ℓ w f‖²`;
* `XData.dg2_grad`: `‖w ∂ G_{k,x,s} f‖² ≤ B ‖ℓ w f‖²`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ k : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The standing data of (DG7): the setting, the potential, `x ≥ 0`, the decoupling vector `s` with
`|s_P| ≤ e^{κ}` and `M₁ ≥ c_* e^{N₀ κ}`. -/
structure XData (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (a : ℕ → ℝ) (aT ν x : ℝ)
    (α : G.Ω 1 → ℂ) (κ : ℝ) (s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ) : Prop where
  st : XSetting G a aT ν
  pot : AdmPot G α
  x0 : 0 ≤ x
  κ0 : 0 ≤ κ
  big : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁
  sb : ∀ P, ‖s P‖ ≤ Real.exp κ

/-- The weight `e^{ε r}`: `r` an Agmon weight and `0 ≤ ε ≤ ε_x`. -/
structure XWeight (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) (ε : ℝ)
    (r : CTorus d L N₁ m₁ (k + 1) → ℝ) : Prop where
  agm : IsAgmonWeight G r
  ε0 : 0 ≤ ε
  ε1 : ε ≤ xAgmonRate d L

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ} {aT x ν : ℝ}
  {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ}

theorem agmonSource_add_le_t (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (u v : G.Ω 1 → ℂ)
    {t : ℝ} (ht : 0 < t) :
    agmonSource G ε r (u + v) ≤
      (1 + t) * agmonSource G ε r u + (1 + 1 / t) * agmonSource G ε r v := by
  simp only [agmonSource_eq, Pi.add_apply]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun y _ => ?_
  have h := norm_add_le (u y) (v y)
  have hA := norm_nonneg (u y)
  have hB := norm_nonneg (v y)
  have h1 : ‖u y + v y‖ ^ 2 ≤ (‖u y‖ + ‖v y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h 2
  have h2 : 2 * ‖u y‖ * ‖v y‖ ≤ t * ‖u y‖ ^ 2 + (1 / t) * ‖v y‖ ^ 2 := by
    rw [← sub_nonneg]
    have : t * ‖u y‖ ^ 2 + (1 / t) * ‖v y‖ ^ 2 - 2 * ‖u y‖ * ‖v y‖ =
        (t * ‖u y‖ - ‖v y‖) ^ 2 / t := by
      field_simp; ring
    rw [this]; positivity
  have h2' : ‖u y + v y‖ ^ 2 ≤ (1 + t) * ‖u y‖ ^ 2 + (1 + 1 / t) * ‖v y‖ ^ 2 := by
    nlinarith
  have h0 : 0 ≤ G.spacing y ^ 2 * Real.exp (ε * r y) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2' h0]

theorem XData.dg1 (D : XData G a aT ν x α κ s) (W : XWeight G ε r) (f : G.Ω 1 → ℂ) :
    agmonSource G ε r (Kcalx G a aT x ν α s *ᵥ f) ≤ (1 / 16) * agmonSource G ε r f :=
  dg1x D.st D.pot D.x0 D.κ0 D.big D.sb W.agm W.ε0 W.ε1 f

theorem XData.isUnit_one_sub (D : XData G a aT ν x α κ s) :
    IsUnit (1 - Kcalx G a aT x ν α s) := by
  have hW : XWeight G 0 (fun _ => 0) :=
    ⟨isAgmonWeight_zero G, le_rfl, by
      have hd : 0 < d := by have := D.st.dg.hd; omega
      exact (xAgmonRate_pos hd D.st.dg.hL).le⟩
  rw [← Matrix.mulVec_injective_iff_isUnit]
  intro v w hvw
  set z := v - w with hz
  have h0 : (1 - Kcalx G a aT x ν α s) *ᵥ z = 0 := by
    rw [hz, Matrix.mulVec_sub, hvw, sub_self]
  have h1 : z = Kcalx G a aT x ν α s *ᵥ z := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h0
    exact sub_eq_zero.1 h0
  have h2 := D.dg1 hW z
  have h3 : agmonSource G 0 (fun _ => 0) z ≤ (1 / 16) * agmonSource G 0 (fun _ => 0) z := by
    calc _ = agmonSource G 0 (fun _ => 0) (Kcalx G a aT x ν α s *ᵥ z) := by rw [← h1]
      _ ≤ _ := h2
  have hz0 : z = 0 := eq_zero_of_agmonSource_zero (by
    have := agmonSource_nonneg G 0 (fun _ => 0) z
    linarith)
  exact sub_eq_zero.1 hz0

theorem XData.neumann_src (D : XData G a aT ν x α κ s) (W : XWeight G ε r) (f : G.Ω 1 → ℂ) :
    agmonSource G ε r ((1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f) ≤ (16 / 9) * agmonSource G ε r f := by
  set g := (1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f with hg
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit_one_sub
  have hgf : g = f + Kcalx G a aT x ν α s *ᵥ g := by
    have : (1 - Kcalx G a aT x ν α s) *ᵥ g = f := by
      rw [hg, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at this
    rw [← this]; abel
  have h1 := agmonSource_add_le_t (G := G) ε r f (Kcalx G a aT x ν α s *ᵥ g) (t := 1 / 3)
    (by norm_num)
  have h2 := D.dg1 W g
  rw [← hgf] at h1
  have hS := agmonSource_nonneg G ε r g
  norm_num at h1
  linarith

theorem Gsx_mulVec (f : G.Ω 1 → ℂ) :
    Gsx G a aT x ν α s *ᵥ f =
      Gstarx G a aT x ν α s *ᵥ ((1 - Kcalx G a aT x ν α s)⁻¹ *ᵥ f) := by
  unfold Gsx
  rw [Matrix.mulVec_mulVec]


/-! ### The value bound -/

section Value

theorem zeroExt_mem' {ι : Type*} [DecidableEq ι] {Λ : Finset ι} (u : Λ → ℂ) {z : ι} (hz : z ∈ Λ) :
    zeroExt Λ u z = u ⟨z, hz⟩ := zeroExt_mem Λ u ⟨z, hz⟩

theorem chi_mem_Icc (S : XSetting G a aT ν) {q : ℕ × CTorus d L N₁ m₁ (k + 1)}
    (hq : q ∈ cubeIdx G) (z : G.Ω 1) : 0 ≤ chi G q z ∧ chi G q z ≤ 1 := by
  obtain ⟨hn1, hnK, hxl⟩ := G.layerIndex_spec z.2
  have hd0 : 0 < d := by have := S.dg.hd; omega
  have hL2 : 2 ≤ L := by have := S.dg.hL; omega
  exact ⟨chi_nonneg S.dg.aligned hL2 hn1 hnK hxl ⟨0, hd0⟩ hq,
    chi_le_one S.dg.aligned hL2 hn1 hnK hxl ⟨0, hd0⟩ hq⟩

/-- The zero extension of `G*_{x,s} g` is `∑_q s_q χ_q ũ_q`. -/
theorem zeroExt_Gstarx (g : G.Ω 1 → ℂ) (z : CTorus d L N₁ m₁ (k + 1)) :
    zeroExt (G.Ω 1) (Gstarx G a aT x ν α s *ᵥ g) z =
      ∑ q ∈ cubeIdx G, sProd G s q * (((chi G q z : ℝ) : ℂ) *
        zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z) := by
  by_cases hz : z ∈ G.Ω 1
  · rw [zeroExt_mem' _ hz, Gstarx_mulVec]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [chiD_mulVec, zeroExt_mem' _ hz]
  · rw [zeroExt_not_mem _ _ hz]
    symm
    refine Finset.sum_eq_zero fun q _ => ?_
    rw [zeroExt_not_mem _ _ hz]; simp

theorem norm_sq_Gstarx_le (D : XData G a aT ν x α κ s) (g : G.Ω 1 → ℂ)
    (z : CTorus d L N₁ m₁ (k + 1)) :
    ‖zeroExt (G.Ω 1) (Gstarx G a aT x ν α s *ᵥ g) z‖ ^ 2 ≤
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ cubeIdx G,
        ‖zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z‖ ^ 2) := by
  have hL1 : 1 ≤ L := by have := D.st.dg.hL; omega
  by_cases hz : z ∈ G.Ω 1
  · set y : G.Ω 1 := ⟨z, hz⟩ with hy
    rw [zeroExt_Gstarx]
    set F : ℕ × CTorus d L N₁ m₁ (k + 1) → G.Ω 1 → ℂ := fun q y' =>
      sProd G s q * (((chi G q y' : ℝ) : ℂ) * (cubeGx G a aT x ν α q *ᵥ g) y') with hF
    have hFs : ∀ q ∈ cubeIdx G, ∀ y' : G.Ω 1,
        (y' : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q → F q y' = 0 := by
      intro q hq y' hy'
      simp only [hF]
      rw [cubeGx_supp D.st D.pot D.x0 hq g y' hy']; simp
    have h := sq_norm_sum_overlap D.st hFs y
    have e : ∑ q ∈ cubeIdx G, sProd G s q * (((chi G q z : ℝ) : ℂ) *
        zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z) = ∑ q ∈ cubeIdx G, F q y := by
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [hF, zeroExt_mem' _ hz]
      rfl
    rw [e]
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hsp : ‖sProd G s q‖ ≤ Real.exp (N0 d L * κ) :=
      norm_sProd_le D.st.dg.aligned D.st.dg.cover_sep D.st.dg.hM hL1 hq D.κ0 D.sb
    have hc := chi_mem_Icc D.st hq y
    have hn : ‖F q y‖ ≤ Real.exp (N0 d L * κ) * ‖zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z‖ := by
      simp only [hF, norm_mul, Complex.norm_real, Real.norm_of_nonneg hc.1, zeroExt_mem' _ hz]
      calc ‖sProd G s q‖ * (chi G q y * ‖(cubeGx G a aT x ν α q *ᵥ g) y‖)
          ≤ Real.exp (N0 d L * κ) * (1 * ‖(cubeGx G a aT x ν α q *ᵥ g) y‖) :=
            mul_le_mul hsp (mul_le_mul_of_nonneg_right hc.2 (norm_nonneg _)) (by
              have := hc.1; positivity) (Real.exp_pos _).le
        _ = _ := by ring
    calc ‖F q y‖ ^ 2 ≤ (Real.exp (N0 d L * κ) *
          ‖zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hn 2
      _ = _ := by ring
  · rw [zeroExt_not_mem _ _ hz]
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    positivity

theorem cwsq_Gstarx_le (D : XData G a aT ν x α κ s) (W : XWeight G ε r) (g : G.Ω 1 → ℂ) :
    cwsq G (agmonField G ε r (Gstarx G a aT x ν α s *ᵥ g)) ≤
      256 * (3 * 5 ^ d : ℝ) ^ 2 * Real.exp (N0 d L * κ) ^ 2 * agmonSource G ε r g := by
  have hn0 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
  unfold cwsq
  have h1 : ∀ z : CTorus d L N₁ m₁ (k + 1), invSqSpacing G z *
      ‖agmonField G ε r (Gstarx G a aT x ν α s *ᵥ g) z‖ ^ 2 ≤
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ cubeIdx G,
        invSqSpacing G z * ‖agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g) z‖ ^ 2) := by
    intro z
    have h := norm_sq_Gstarx_le D g z
    have hi := invSqSpacing_nonneg G z
    have hw := Real.exp_pos (ε * r z)
    rw [norm_agmonField, mul_pow]
    calc invSqSpacing G z * (Real.exp (ε * r z) ^ 2 *
          ‖zeroExt (G.Ω 1) (Gstarx G a aT x ν α s *ᵥ g) z‖ ^ 2)
        ≤ invSqSpacing G z * (Real.exp (ε * r z) ^ 2 * ((3 * 5 ^ d : ℝ) *
          (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ cubeIdx G,
            ‖zeroExt (G.Ω 1) (cubeGx G a aT x ν α q *ᵥ g) z‖ ^ 2))) := by
          gcongr
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
            Finset.mul_sum]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [norm_agmonField]; ring
  calc ∑ z, invSqSpacing G z * ‖agmonField G ε r (Gstarx G a aT x ν α s *ᵥ g) z‖ ^ 2
      ≤ ∑ z, (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ cubeIdx G,
        invSqSpacing G z * ‖agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g) z‖ ^ 2) :=
        Finset.sum_le_sum fun z _ => h1 z
    _ = (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ cubeIdx G,
        cwsq G (agmonField G ε r (cubeGx G a aT x ν α q *ᵥ g))) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm]
        rfl
    _ ≤ (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) ^ 2 * ∑ q ∈ cubeIdx G,
        256 * agmonSource G ε r (cD G q *ᵥ g)) := by
        gcongr with q hq
        exact cube_cwsq_le D.st D.pot D.x0 hq W.agm W.ε0 W.ε1 g
    _ = 256 * (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) ^ 2 *
        ∑ q ∈ cubeIdx G, agmonSource G ε r (cD G q *ᵥ g) := by
        rw [← Finset.mul_sum]; ring
    _ ≤ 256 * (3 * 5 ^ d : ℝ) * Real.exp (N0 d L * κ) ^ 2 *
        ((3 * 5 ^ d : ℝ) * agmonSource G ε r g) := by
        gcongr
        exact sum_agmonSource_cD_le D.st ε r g
    _ = _ := by ring

end Value

end Balaban.Localization
