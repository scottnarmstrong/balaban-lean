/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Dg

/-!
# (DG2) for a cover `C` and an operator `H`

The representation of `G*_s g` (`Gstar_apply`, `Gstar_repr`), the bounds of one centre
(`perq_bounds`), and the pointwise bounds `dg2_all`, `dg2_sup`, `Gs_one`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Kc Cx : ℝ} {α : H.Ω 1 → ℂ}


/-- `H*_s g = ∑_z s_z χ_z ũ_z` pointwise on the whole torus (zero extension). -/
theorem Gstar_apply (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (g : H.Ω 1 → ℂ)
    (y : CTorus d L N₁ m₁ K) :
    zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) y =
      ∑ q ∈ C.cubeIdx, C.sProd s q * (((C.chi q y : ℝ) : ℂ) * cubeSolE H a ν α q g y) := by
  by_cases hy : y ∈ H.Ω 1
  · rw [zeroExt_of_mem' hy]
    unfold Gstar
    rw [Matrix.sum_mulVec, Finset.sum_apply]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, ← Matrix.mulVec_mulVec, chiD_mulVec,
      cubeG_mulVec]
    congr 2
    unfold cubeSolE solExt
    rw [zeroExt_of_mem' hy]
  · rw [zeroExt_not_mem _ _ hy]
    refine (Finset.sum_eq_zero fun q _ => ?_).symm
    rw [cubeSolE_of_not_mem q g hy]; simp


theorem chi_grad_real {δ : ℝ} {q : ℕ × CTorus d L N₁ m₁ K}
    (hsm : IsSmoothField H δ (C.chiField q)) {y : CTorus d L N₁ m₁ K} (hy : y ∈ H.Ω 1)
    (μ : Fin d) :
    H.spacing y * |C.chi q (y + Pi.single μ 1) - C.chi q y| ≤ δ ∧
    H.spacing y * |C.chi q (y - Pi.single μ 1) - C.chi q y| ≤ δ := by
  obtain ⟨h1, h2⟩ := hsm.grad y hy μ
  have hsp := spacing_pos H (x := y)
  have e : ∀ z : CTorus d L N₁ m₁ K,
      C.chiField q z - C.chiField q y = fun _ => ((C.chi q z - C.chi q y : ℝ) : ℂ) := by
    intro z; funext i; simp [DecCover.chiField]
  rw [e, vn_const_one, le_div_iff₀ hsp] at h1 h2
  exact ⟨by linarith, by linarith⟩

theorem chi_lap_real {δ : ℝ} {q : ℕ × CTorus d L N₁ m₁ K}
    (hsm : IsSmoothField H δ (C.chiField q)) {y : CTorus d L N₁ m₁ K} (hy : y ∈ H.Ω 1) :
    (H.spacing y) ^ 2 * |∑ μ : Fin d, (C.chi q (y + Pi.single μ 1) +
      C.chi q (y - Pi.single μ 1) - 2 * C.chi q y)| ≤ δ := by
  have h := hsm.lap y hy
  have hsp := spacing_pos H (x := y)
  have e : (fun i : Fin 1 => ∑ μ : Fin d, (C.chiField q (y + Pi.single μ 1) i +
      C.chiField q (y - Pi.single μ 1) i - 2 * C.chiField q y i)) =
      fun _ => ((∑ μ : Fin d, (C.chi q (y + Pi.single μ 1) + C.chi q (y - Pi.single μ 1) -
        2 * C.chi q y) : ℝ) : ℂ) := by
    funext i; simp [DecCover.chiField]
  rw [e, vn_const_one, le_div_iff₀ (by positivity)] at h
  linarith


/-- **The three bounds for one centre**: value, forward difference and Laplacian of the product
`χ_z ũ_z` at an interior point. -/
theorem perq_bounds (S : CoverBase C H a ν Kc Cx) (hCx : 0 ≤ Cx) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ C.cubeIdx)
    {u : CTorus d L N₁ m₁ K → ℂ} (hux : ∀ y, y ∉ H.Ω 1 → u y = 0) {x : H.Ω 1} {V : ℝ}
    (hV : 0 ≤ V) (hst : StarBd H u x V) :
    ‖((C.chi q x : ℝ) : ℂ) * u x‖ ≤ V ∧
    (∀ μ : Fin d, H.spacing (x : CTorus d L N₁ m₁ K) *
      ‖((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - ((C.chi q x : ℝ) : ℂ) * u x‖ ≤
      (1 + Cx) * V) ∧
    (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖∑ μ : Fin d, (2 * (((C.chi q x : ℝ) : ℂ) * u x) -
      ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
      ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1))‖ ≤
      (1 + Cx + d * Cx * (1 + L)) * V := by
  have hd0 : 0 < d := by have := S.hd; omega
  have hL2 : 2 ≤ L := by have := S.hL; omega
  have hM1 : (1 : ℝ) ≤ (L : ℝ) ^ m₁ := one_le_pow₀ (by exact_mod_cast (by omega : 1 ≤ L))
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hxΩ : (x : CTorus d L N₁ m₁ K) ∈ H.Ω 1 := x.2
  have hCc := hCx
  set δ : ℝ := Cx / (L : ℝ) ^ m₁ with hδ
  have hδ0 : 0 ≤ δ := div_nonneg hCc (by positivity)
  have hδC : δ ≤ Cx := div_le_self hCc hM1
  have hsm := S.chi_smooth q hq
  set ℓ : ℝ := H.spacing (x : CTorus d L N₁ m₁ K) with hℓ
  have hℓ0 : 0 < ℓ := spacing_pos H
  -- the data at `x`
  have hc0 := S.chi_unit q hq (x := (x : CTorus d L N₁ m₁ K)) x.2 (Or.inl rfl)
  have hcp : ∀ μ : Fin d, 0 ≤ C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) ∧
      C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) ≤ 1 := fun μ =>
    S.chi_unit q hq x.2 (Or.inr ⟨μ, Or.inl rfl⟩)
  have hcm : ∀ μ : Fin d, 0 ≤ C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ∧
      C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) ≤ 1 := fun μ =>
    S.chi_unit q hq x.2 (Or.inr ⟨μ, Or.inr rfl⟩)
  have hu0 : ‖u x‖ ≤ V := hst.val x hxΩ (by simp [H.pathDist_self hxΩ])
  -- values at the neighbours
  have hnbr : ∀ y : CTorus d L N₁ m₁ K, Adj (x : CTorus d L N₁ m₁ K) y → ‖u y‖ ≤ V := by
    intro y hadj
    by_cases hyΩ : y ∈ H.Ω 1
    · refine hst.val y hyΩ ?_
      refine (H.pathDist_le_bondCost hxΩ hyΩ hadj).trans ?_
      refine (ENNReal.ofReal_le_ofReal (H.bondCost_le_one hxΩ y)).trans ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have : (1 : ℝ) ≤ d := by exact_mod_cast hd0
      linarith
    · rw [hux y hyΩ, norm_zero]; exact hV
  have hup : ∀ μ : Fin d, ‖u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1)‖ ≤ V := fun μ =>
    hnbr _ ⟨μ, Or.inl rfl⟩
  have hum : ∀ μ : Fin d, ‖u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)‖ ≤ V := fun μ =>
    hnbr _ ⟨μ, Or.inr (by simp)⟩
  have hgr := fun μ => chi_grad_real hsm hxΩ μ
  have hlapχ := chi_lap_real hsm hxΩ
  have hnorm : ∀ (c : ℝ) (z : ℂ), ‖(c : ℂ) * z‖ = |c| * ‖z‖ := fun c z => by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine ⟨?_, fun μ => ?_, ?_⟩
  · rw [hnorm, abs_of_nonneg hc0.1]
    calc C.chi q x * ‖u x‖ ≤ 1 * V := mul_le_mul hc0.2 hu0 (norm_nonneg _) zero_le_one
      _ = V := one_mul V
  · have e : ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
        u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - ((C.chi q x : ℝ) : ℂ) * u x =
        ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          (u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x) +
        ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x : ℝ) : ℂ) * u x := by
      push_cast; ring
    rw [e]
    have h1 := hst.fwd μ
    have h2 := (hgr μ).1
    have hc := hcp μ
    calc ℓ * ‖((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          (u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x) +
          ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x : ℝ) : ℂ) * u x‖
        ≤ ℓ * (‖((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          (u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x)‖ +
          ‖((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x : ℝ) : ℂ) * u x‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) hℓ0.le
      _ = |C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1)| *
            (ℓ * ‖u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x‖) +
          (ℓ * |C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x|) * ‖u x‖ := by
          rw [hnorm, hnorm]; ring
      _ ≤ 1 * V + δ * V := by
          rw [abs_of_nonneg hc.1]
          have a1 : C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) *
              (ℓ * ‖u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - u x‖) ≤ 1 * V :=
            mul_le_mul hc.2 h1 (by positivity) zero_le_one
          have a2 : (ℓ * |C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x|) *
              ‖u x‖ ≤ δ * V := mul_le_mul h2 hu0 (norm_nonneg _) hδ0
          linarith
      _ ≤ (1 + Cx) * V := by nlinarith
  · -- Laplacian
    set c0 : ℂ := ((C.chi q x : ℝ) : ℂ) with hc0def
    set cp : Fin d → ℂ := fun μ => ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ)
      with hcpdef
    set cm : Fin d → ℂ := fun μ => ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ)
      with hcmdef
    set up : Fin d → ℂ := fun μ => u ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) with hupdef
    set um : Fin d → ℂ := fun μ => u ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) with humdef
    have e := lap_sum_aux c0 (u x) cp cm up um
    show ℓ ^ 2 * ‖∑ μ : Fin d, (2 * (c0 * u x) - cp μ * up μ - cm μ * um μ)‖ ≤ _
    rw [e]
    have hΔu := hst.lap
    have hr : ∑ μ : Fin d, (2 * c0 - cp μ - cm μ) =
        -(((∑ μ : Fin d, (C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) +
          C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - 2 * C.chi q x) : ℝ)) : ℂ) := by
      push_cast
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun μ _ => by simp only [hc0def, hcpdef, hcmdef]; ring
    set r : ℝ := ∑ μ : Fin d, (C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) +
          C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - 2 * C.chi q x) with hrdef
    rw [hr]
    have hdiff : ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ * ℓ ^ 2 ≤
        d * (δ * V + δ * (L * V)) := by
      calc ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ * ℓ ^ 2
          ≤ (∑ μ : Fin d, ‖(cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x)‖) * ℓ ^ 2 :=
            mul_le_mul_of_nonneg_right (norm_sum_le _ _) (by positivity)
        _ = ∑ μ : Fin d, ‖(cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2 := by
            rw [Finset.sum_mul]
        _ ≤ ∑ _μ : Fin d, (δ * V + δ * (L * V)) := by
            refine Finset.sum_le_sum fun μ _ => ?_
            have h1 : ‖(cp μ - c0) * (up μ - u x)‖ * ℓ ^ 2 ≤ δ * V := by
              have : (cp μ - c0) = (((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
                C.chi q x : ℝ)) : ℂ) := by simp [hcpdef, hc0def]
              rw [norm_mul, this, Complex.norm_real, Real.norm_eq_abs]
              have := (hgr μ).1
              have h3 := hst.fwd μ
              calc |C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x| *
                    ‖up μ - u x‖ * ℓ ^ 2
                  = (ℓ * |C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - C.chi q x|) *
                    (ℓ * ‖up μ - u x‖) := by ring
                _ ≤ δ * V := mul_le_mul this h3 (by positivity) hδ0
            have h2 : ‖(cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2 ≤ δ * (L * V) := by
              have : (cm μ - c0) = (((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) -
                C.chi q x : ℝ)) : ℂ) := by simp [hcmdef, hc0def]
              rw [norm_mul, this, Complex.norm_real, Real.norm_eq_abs]
              have := (hgr μ).2
              have h3 := hst.bwd μ
              calc |C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - C.chi q x| *
                    ‖um μ - u x‖ * ℓ ^ 2
                  = (ℓ * |C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) - C.chi q x|) *
                    (ℓ * ‖um μ - u x‖) := by ring
                _ ≤ δ * (L * V) := mul_le_mul this h3 (by positivity) hδ0
            calc ‖(cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2
                ≤ (‖(cp μ - c0) * (up μ - u x)‖ + ‖(cm μ - c0) * (um μ - u x)‖) * ℓ ^ 2 :=
                  mul_le_mul_of_nonneg_right (norm_add_le _ _) (by positivity)
              _ = ‖(cp μ - c0) * (up μ - u x)‖ * ℓ ^ 2 + ‖(cm μ - c0) * (um μ - u x)‖ * ℓ ^ 2 := by
                  ring
              _ ≤ δ * V + δ * (L * V) := add_le_add h1 h2
        _ = d * (δ * V + δ * (L * V)) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hA : ℓ ^ 2 * ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ)‖ ≤ V := by
      rw [norm_mul, hc0def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc0.1]
      calc ℓ ^ 2 * (C.chi q x * ‖∑ μ : Fin d, (2 * u x - up μ - um μ)‖)
          = C.chi q x * (ℓ ^ 2 * ‖∑ μ : Fin d, (2 * u x - up μ - um μ)‖) := by ring
        _ ≤ 1 * V := mul_le_mul hc0.2 hΔu (by positivity) zero_le_one
        _ = V := one_mul V
    have hB : ℓ ^ 2 * ‖u x * (-((r : ℝ) : ℂ))‖ ≤ δ * V := by
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
      have hr' : ℓ ^ 2 * |r| ≤ δ := by
        have := hlapχ
        rw [hrdef]
        exact this
      calc ℓ ^ 2 * (‖u x‖ * |r|) = ‖u x‖ * (ℓ ^ 2 * |r|) := by ring
        _ ≤ V * δ := mul_le_mul hu0 hr' (by positivity) hV
        _ = δ * V := by ring
    calc ℓ ^ 2 * ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ) + u x * (-((r : ℝ) : ℂ)) -
          ∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖
        ≤ ℓ ^ 2 * (‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ)‖ + ‖u x * (-((r : ℝ) : ℂ))‖ +
          ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc _ ≤ ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ) + u x * (-((r : ℝ) : ℂ))‖ +
                ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ :=
                norm_sub_le _ _
            _ ≤ _ := by
                have := norm_add_le (c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ))
                  (u x * (-((r : ℝ) : ℂ)))
                linarith
      _ = ℓ ^ 2 * ‖c0 * ∑ μ : Fin d, (2 * u x - up μ - um μ)‖ +
          ℓ ^ 2 * ‖u x * (-((r : ℝ) : ℂ))‖ +
          ‖∑ μ : Fin d, ((cp μ - c0) * (up μ - u x) + (cm μ - c0) * (um μ - u x))‖ * ℓ ^ 2 := by
          ring
      _ ≤ V + δ * V + d * (δ * V + δ * (L * V)) := add_le_add (add_le_add hA hB) hdiff
      _ ≤ (1 + Cx + d * Cx * (1 + L)) * V := by
          have hd1 : (0 : ℝ) ≤ d := by positivity
          have h1 : δ * V ≤ Cx * V := mul_le_mul_of_nonneg_right hδC hV
          have h2 : d * (δ * V + δ * (L * V)) ≤ d * (Cx * V + Cx * (L * V)) := by
            apply mul_le_mul_of_nonneg_left _ hd1
            have h3 : δ * (L * V) ≤ Cx * (L * V) :=
              mul_le_mul_of_nonneg_right hδC (by positivity)
            linarith
          nlinarith

/-- Only the centres whose interaction cube has `x` in its interior contribute to `H*_s g` at
`x` and its neighbours. -/
theorem Gstar_repr (S : CoverBase C H a ν Kc Cx) (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ)
    (g : H.Ω 1 → ℂ) (x : H.Ω 1) :
    ∃ A : Finset (ℕ × CTorus d L N₁ m₁ K), (∀ q ∈ A, q ∈ C.cubeIdx ∧ Inner q x) ∧
      A.card ≤ 3 * 5 ^ d ∧ ∀ y : CTorus d L N₁ m₁ K,
      (y = (x : CTorus d L N₁ m₁ K) ∨ ∃ μ : Fin d, y = (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨
        y = (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) →
      zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) y =
        ∑ q ∈ A, C.sProd s q * (((C.chi q y : ℝ) : ℂ) * cubeSolE H a ν α q g y) := by
  classical
  refine ⟨(C.cubeIdx).filter (fun q => Inner q (x : CTorus d L N₁ m₁ K)), ?_, ?_, ?_⟩
  · intro q hq
    exact (Finset.mem_filter.1 hq)
  · refine le_trans (Finset.card_le_card ?_) (S.card_box _ x.2)
    intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.1, hq.2.self⟩
  · intro y hy
    rw [Gstar_apply]
    symm
    refine Finset.sum_filter_of_ne fun q hq hne => ?_
    by_contra hI
    apply hne
    by_cases hyΩ : y ∈ H.Ω 1
    · have hchi : C.chi q y = 0 := by
        by_contra hne'
        apply hI
        rcases hy with rfl | ⟨μ, hμ | hμ⟩
        · exact inner_of_chi_ne_zero S hq x.2 hne'
        · exact S.inner_near q hq x.2 hne' (Or.inl ⟨μ, Or.inl hμ⟩)
        · exact S.inner_near q hq x.2 hne' (Or.inl ⟨μ, Or.inr hμ⟩)
      rw [hchi]; simp
    · rw [cubeSolE_of_not_mem q g hyΩ]; simp



/-- The constant multiplying the bounds of a single centre. -/
noncomputable def Fc (d L : ℕ) (Cx : ℝ) : ℝ := (1 + Cx) * (1 + d) * (1 + L)

theorem Fc_bounds (d L : ℕ) (hCx : 0 ≤ Cx) :
    1 ≤ Fc d L Cx ∧ 1 + Cx ≤ Fc d L Cx ∧
      1 + Cx + d * Cx * (1 + L) ≤ Fc d L Cx ∧ L * (1 + Cx) ≤ Fc d L Cx := by
  have hC := hCx
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  unfold Fc
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith [mul_nonneg hC hd, mul_nonneg hC hL, mul_nonneg hd hL,
    mul_nonneg (mul_nonneg hC hd) hL, mul_nonneg (mul_nonneg hC hd) hd,
    mul_nonneg (mul_nonneg hC hL) hL, mul_nonneg (mul_nonneg hd hL) hL]



theorem Kcal_weighted_of_dg1
    {s : ℕ × CTorus d L N₁ m₁ K → ℂ} {w : CTorus d L N₁ m₁ K → ℝ}
    (hK : ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      ∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
        ‖(Kcal C H a ν α s *ᵥ f) x‖ ≤ Cb / 4) :
    ∀ (h : H.Ω 1 → ℂ) (Cb : ℝ), 0 ≤ Cb →
      WBd (fun x : H.Ω 1 => w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h Cb →
      WBd (fun x : H.Ω 1 => w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2)
        (Kcal C H a ν α s *ᵥ h) (Cb / 4) :=
  fun h _ hC hh => hK h hC hh

/-- **(DG1)--(DG3), pointwise form, with the contraction.** -/
theorem dg2_all (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      (IsUnit (1 - Kcal C H a ν α s) ∧
      SupBdW H w (zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ f)) (BG * Real.exp (N0 d L * κ) * Cb)) ∧
      (∀ (f' : H.Ω 1 → ℂ) {C' : ℝ}, 0 ≤ C' →
        (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f' x‖ ≤ C') →
        ∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 *
          ‖(Kcal C H a ν α s *ᵥ f') x‖ ≤ C' / 4) := by
  obtain ⟨cstar, hcs, hD1⟩ := dg1 (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  obtain ⟨Bw, hBw, hS⟩ := cube_star (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc
  have hFc := Fc_bounds d L hCx
  have hF0 : 0 ≤ Fc d L Cx := by linarith [hFc.1]
  refine ⟨cstar, 3 * 5 ^ d * (4 / 3) * Bw * Real.exp (2 * gammaW d * d) * Fc d L Cx, hcs, by positivity, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hMκ s hs w hw f Cb hC hfC
  have hd0 : 0 < d := by omega
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hγ0 := gammaW_nonneg hd0
  have hρ := S.one_lt_rho
  have hspos : ∀ x : H.Ω 1, 0 < (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x => by
    have := spacing_pos H (x := (x : CTorus d L N₁ m₁ K)); positivity
  -- invertibility
  have hw1 : IsWeight H (gammaW d) (fun _ => (1 : ℝ)) := IsWeight.one H hγ0
  have hK1 : ∀ (h : H.Ω 1 → ℂ) (Cb : ℝ), 0 ≤ Cb →
      WBd (fun x : H.Ω 1 => (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) h Cb →
      WBd (fun x : H.Ω 1 => (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) (Kcal C H a ν α s *ᵥ h) (Cb / 4) := by
    intro h Cb0 hC0 hh x
    have := hD1 C H S hα hκ hMκ hs hw1 h hC0 (fun y => by simpa using hh y) x
    simpa using this
  have hU : IsUnit (1 - Kcal C H a ν α s) := neumann_isUnit hspos hK1
  refine ⟨⟨hU, ?_⟩, fun f' C' hC' hf' => hD1 C H S hα hκ hMκ hs hw f' hC' hf'⟩
  -- the solution of `(1 - 𝒦) g = f`
  set g : H.Ω 1 → ℂ := (1 - Kcal C H a ν α s)⁻¹ *ᵥ f with hgdef
  have hg : g - Kcal C H a ν α s *ᵥ g = f := by
    have h1 : (1 - Kcal C H a ν α s) *ᵥ g = f := by
      rw [hgdef, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hU), Matrix.one_mulVec]
    rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h1
    exact h1
  have hωpos : ∀ x : H.Ω 1, 0 < w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 := fun x =>
    mul_pos (hw.pos x) (hspos x)
  have hKw := Kcal_weighted_of_dg1 (a := a) (ν := ν) (α := α) (s := s)
    (fun f' C' hC' hf' => hD1 C H S hα hκ hMκ hs hw f' hC' hf')
  have hgW : WBd (fun x : H.Ω 1 => w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2) g (4 * Cb / 3) :=
    neumann_bound hωpos hKw hg (fun x => hfC x)
  have hgC : ∀ z : H.Ω 1, w z * (H.spacing (z : CTorus d L N₁ m₁ K)) ^ 2 * ‖g z‖ ≤ 4 * Cb / 3 :=
    fun z => hgW z
  have hGsf : Gs C H a ν α s *ᵥ f = Gstar C H a ν α s *ᵥ g := by
    rw [hgdef, Gs, ← Matrix.mulVec_mulVec]
  rw [hGsf]
  set v : CTorus d L N₁ m₁ K → ℂ := zeroExt (H.Ω 1) (Gstar C H a ν α s *ᵥ g) with hvdef
  -- the pointwise analysis
  have hpt : ∀ x : H.Ω 1,
      (∃ A : Finset (ℕ × CTorus d L N₁ m₁ K),
        (A.card : ℝ) ≤ 3 * 5 ^ d ∧ (∀ q ∈ A, q ∈ C.cubeIdx) ∧
        (∀ y : CTorus d L N₁ m₁ K, (y = (x : CTorus d L N₁ m₁ K) ∨ ∃ μ : Fin d,
          y = (x : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨ y = (x : CTorus d L N₁ m₁ K) - Pi.single μ 1) →
          v y = ∑ q ∈ A, C.sProd s q * (((C.chi q y : ℝ) : ℂ) * cubeSolE H a ν α q g y)) ∧
        ∀ q ∈ A, ‖((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x‖ * w x ≤
            Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) ∧
          (∀ μ : Fin d, H.spacing (x : CTorus d L N₁ m₁ K) *
            ‖((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
              ((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x‖ * w x ≤
            (1 + Cx) * (Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d))) ∧
          (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖∑ μ : Fin d, (2 * (((C.chi q x : ℝ) : ℂ) *
              cubeSolE H a ν α q g x) -
            ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
            ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1))‖ * w x ≤
            (1 + Cx + d * Cx * (1 + L)) *
              (Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d))) := by
    intro x
    obtain ⟨A, hA1, hAc, hrepr⟩ := Gstar_repr S α s g x
    refine ⟨A, by exact_mod_cast hAc, fun q hq => (hA1 q hq).1, fun y hy => hrepr y hy,
      fun q hq => ?_⟩
    obtain ⟨hqi, hIq⟩ := hA1 q hq
    obtain ⟨hsupp, hgq⟩ := cD_source q g (by positivity : (0 : ℝ) ≤ 4 * Cb / 3) hgC
    have hst := hS C H S hα hqi hw (cD H q *ᵥ g) hsupp (by positivity : (0 : ℝ) ≤ 4 * Cb / 3) hgq hIq
    have hwx := hw.pos x
    have hux : ∀ y, y ∉ H.Ω 1 → cubeSolE H a ν α q g y = 0 := fun y hy => cubeSolE_of_not_mem q g hy
    have hV0 : 0 ≤ Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) / w x := by positivity
    have hper := perq_bounds S hCx hqi hux hV0 hst
    have hVw : Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) / w x * w x =
        Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) := by field_simp
    refine ⟨?_, fun μ => ?_, ?_⟩
    · calc _ ≤ Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) / w x * w x :=
            mul_le_mul_of_nonneg_right hper.1 hwx.le
        _ = _ := hVw
    · calc _ ≤ (1 + Cx) * (Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) / w x) * w x :=
            mul_le_mul_of_nonneg_right (hper.2.1 μ) hwx.le
        _ = _ := by rw [mul_assoc, hVw]
    · calc _ ≤ (1 + Cx + d * Cx * (1 + L)) *
            (Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) / w x) * w x :=
            mul_le_mul_of_nonneg_right hper.2.2 hwx.le
        _ = _ := by rw [mul_assoc, hVw]
  -- assembling the four bounds
  set Wc : ℝ := Bw * (4 * Cb / 3) * Real.exp (2 * gammaW d * d) with hWc
  have hWc0 : 0 ≤ Wc := by positivity
  have hE0 : 0 < Real.exp (N0 d L * κ) := Real.exp_pos _
  have htarget : 3 * 5 ^ d * (4 / 3) * Bw * Real.exp (2 * gammaW d * d) * Fc d L Cx *
      Real.exp (N0 d L * κ) * Cb = (3 * 5 ^ d) * (Real.exp (N0 d L * κ) * (Fc d L Cx * Wc)) := by
    rw [hWc]; ring
  have hmono : ∀ c : ℝ, c ≤ Fc d L Cx →
      (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * (c * Wc)) ≤
        3 * 5 ^ d * (4 / 3) * Bw * Real.exp (2 * gammaW d * d) * Fc d L Cx *
          Real.exp (N0 d L * κ) * Cb := by
    intro c hc
    rw [htarget]
    gcongr
  have hcoef : ∀ q ∈ C.cubeIdx, ‖C.sProd s q‖ ≤ Real.exp (N0 d L * κ) := fun q hq =>
    C.norm_sProd_le (S.card_qset q hq) hκ hs
  refine ⟨fun x hx => ?_, fun x hx μ => ?_, fun x hx μ hxe => ?_, fun x hx => ?_⟩
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    rw [hrepr x (Or.inl rfl)]
    refine (sum_scaled_bound A hcard (hw.pos x).le hE0.le hWc0 (fun q => C.sProd s q)
      (fun q => ((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x)
      (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_)).trans (hmono 1 (Fc_bounds d L hCx).1 |>.trans_eq' ?_)
    · have := (hq q hqA).1
      simpa [mul_comm] using this
    · ring
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    have e : v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x = ∑ q ∈ A, C.sProd s q *
        (((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        ((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x) := by
      rw [hrepr _ (Or.inr ⟨μ, Or.inl rfl⟩), hrepr x (Or.inl rfl), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    rw [e, ← mul_assoc]
    refine (sum_scaled_bound A hcard (mul_nonneg (hw.pos x).le (spacing_pos H).le) hE0.le
      (mul_nonneg (by linarith [hCx]) hWc0) (fun q => C.sProd s q)
      (fun q => ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        ((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x)
      (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_)).trans (hmono (1 + Cx) (Fc_bounds d L hCx).2.1)
    have := (hq q hqA).2.1 μ
    nlinarith [this]
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    have e : v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x = ∑ q ∈ A, C.sProd s q *
        (((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
          cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        ((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x) := by
      rw [hrepr _ (Or.inr ⟨μ, Or.inl rfl⟩), hrepr x (Or.inl rfl), ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun q _ => by ring
    have hadj : Adj (x : CTorus d L N₁ m₁ K) ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) :=
      ⟨μ, Or.inl rfl⟩
    have hsp := spacing_adj_le H hρ.le hx hxe hadj
    have hmain : w x * (H.spacing (x : CTorus d L N₁ m₁ K) *
        ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖) ≤
        (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * ((1 + Cx) * Wc)) := by
      rw [e, ← mul_assoc]
      refine (sum_scaled_bound A hcard (mul_nonneg (hw.pos x).le (spacing_pos H).le) hE0.le
        (mul_nonneg (by linarith [hCx]) hWc0) (fun q => C.sProd s q)
        (fun q => ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
          ((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x)
        (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_))
      have := (hq q hqA).2.1 μ
      nlinarith [this]
    have hnn := norm_nonneg (v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x)
    have hw0 := (hw.pos x).le
    calc w x * (H.spacing ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) *
          ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖)
        ≤ w x * ((L * H.spacing (x : CTorus d L N₁ m₁ K)) *
          ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖) := by gcongr
      _ = L * (w x * (H.spacing (x : CTorus d L N₁ m₁ K) *
          ‖v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) - v x‖)) := by ring
      _ ≤ L * ((3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * ((1 + Cx) * Wc))) := by gcongr
      _ = (3 * 5 ^ d : ℝ) * (Real.exp (N0 d L * κ) * ((L * (1 + Cx)) * Wc)) := by ring
      _ ≤ _ := hmono _ (Fc_bounds d L hCx).2.2.2
  · obtain ⟨A, hcard, hAq, hrepr, hq⟩ := hpt ⟨x, hx⟩
    have e : ∑ μ : Fin d, (2 * v x - v ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
        v ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) = ∑ q ∈ A, C.sProd s q *
        ∑ μ : Fin d, (2 * (((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x) -
          ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
          ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) := by
      calc _ = ∑ μ : Fin d, ∑ q ∈ A, C.sProd s q *
            (2 * (((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x) -
            ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
            ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) := by
            refine Finset.sum_congr rfl fun μ _ => ?_
            rw [hrepr x (Or.inl rfl), hrepr _ (Or.inr ⟨μ, Or.inl rfl⟩),
              hrepr _ (Or.inr ⟨μ, Or.inr rfl⟩), Finset.mul_sum, ← Finset.sum_sub_distrib,
              ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun q _ => by ring
        _ = ∑ q ∈ A, ∑ μ : Fin d, C.sProd s q *
            (2 * (((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x) -
            ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
            ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
              cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)) :=
            Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun q _ => (Finset.mul_sum _ _ _).symm
    rw [e, ← mul_assoc]
    have hCc := hCx
    have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    have hFl : 0 ≤ 1 + Cx + d * Cx * (1 + L) := by positivity
    refine (sum_scaled_bound A hcard (mul_nonneg (hw.pos x).le (by positivity)) hE0.le
      (mul_nonneg hFl hWc0) (fun q => C.sProd s q)
      (fun q => ∑ μ : Fin d, (2 * (((C.chi q x : ℝ) : ℂ) * cubeSolE H a ν α q g x) -
          ((C.chi q ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) + Pi.single μ 1) -
          ((C.chi q ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1) : ℝ) : ℂ) *
            cubeSolE H a ν α q g ((x : CTorus d L N₁ m₁ K) - Pi.single μ 1)))
      (fun q hqA => hcoef q (hAq q hqA)) (fun q hqA => ?_)).trans
      (hmono (1 + Cx + d * Cx * (1 + L)) (Fc_bounds d L hCx).2.2.1)
    have := (hq q hqA).2.2
    nlinarith [this]

/-- **(DG1)--(DG3), pointwise form.** -/
theorem dg2_sup (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar BG : ℝ, 0 ≤ cstar ∧ 0 ≤ BG ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → ∀ {κ : ℝ}, 0 ≤ κ →
      cstar * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁ →
      ∀ {s : ℕ × CTorus d L N₁ m₁ K → ℂ}, (∀ P, ‖s P‖ ≤ Real.exp κ) →
      ∀ {w : CTorus d L N₁ m₁ K → ℝ}, IsWeight H (gammaW d) w →
      ∀ (f : H.Ω 1 → ℂ) {Cb : ℝ}, 0 ≤ Cb →
      (∀ x : H.Ω 1, w x * (H.spacing (x : CTorus d L N₁ m₁ K)) ^ 2 * ‖f x‖ ≤ Cb) →
      IsUnit (1 - Kcal C H a ν α s) ∧
      SupBdW H w (zeroExt (H.Ω 1) (Gs C H a ν α s *ᵥ f)) (BG * Real.exp (N0 d L * κ) * Cb) := by
  obtain ⟨c, B, hc, hB, Hh⟩ := dg2_all (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨c, B, hc, hB, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα κ hκ hMκ s hs w hw f Cb hC hfC
  exact (Hh C H S hα hκ hMκ hs hw f hC hfC).1

/-- **(DG1), the identity `G_1(A) = G_D(A)`**: for `M₁ ≥ c_*`. -/
theorem Gs_one (hd : 3 ≤ d) (hL : 3 ≤ L) (hKc : 0 ≤ Kc) (hCx : 0 ≤ Cx) :
    ∃ cstar : ℝ, 0 ≤ cstar ∧ ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ}
      (C : DecCover d L N₁ m₁ K) (H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) {a : ℕ → ℝ} {ν : ℝ}, CoverBase C H a ν Kc Cx →
      ∀ {α : H.Ω 1 → ℂ}, AdmPot H α → cstar ≤ (L : ℝ) ^ m₁ →
      IsUnit (1 - Kcal C H a ν α (fun _ => 1)) ∧
      Gs C H a ν α (fun _ => 1) = (dirichletOperator H a ν α)⁻¹ := by
  obtain ⟨cstar, BG, hc, hB, Hh⟩ := dg2_sup (d := d) (L := L) (Kc := Kc) (Cx := Cx) hd hL hKc hCx
  refine ⟨cstar, hc, ?_⟩
  intro N₁ m₁ K _ ϱ C H a ν S α hα hM
  have hd0 : 0 < d := by omega
  obtain ⟨hU, -⟩ := Hh C H S hα (κ := 0) le_rfl (by simpa using hM) (s := fun _ => 1) (by simp)
    (w := fun _ => 1) (IsWeight.one H (gammaW_nonneg hd0)) 0 (Cb := 0) le_rfl (by simp)
  refine ⟨hU, ?_⟩
  have hHU := dirichletOperator_isUnit H hd0 S.mass S.weights α hα
  have hdetH := (Matrix.isUnit_iff_isUnit_det _).1 hHU
  have hdetK := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hpar := parametrix S hα
  have h1 : dirichletOperator H a ν α * Gs C H a ν α (fun _ => 1) = 1 := by
    unfold Gs
    rw [← Matrix.mul_assoc, hpar, Matrix.mul_nonsing_inv _ hdetK]
  exact (Matrix.inv_eq_right_inv h1).symm

end Balaban.Localization.Dec2
