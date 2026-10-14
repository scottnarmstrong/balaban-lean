/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledCovClose
public import Balaban.Localization.DecoupledCovPrincipal
public import Balaban.Localization.DecoupledCovUnit
public import Balaban.Localization.DecoupledFieldX0

/-!
# I-4c (vi): closeness of `C^{1/2}(s)` and `𝕃(s)` to `s ≡ 1` on the unit lattice

LOCALIZATION.md §3.4, Theorem I-4c (vi), for the concrete unit lattice `unitQ`, `unitP` of
`Balaban/Localization/DecoupledCovUnit.lean`. The weight on the unit lattice is the minimum over the
block of the truncated path distance to `W` (`unitRho`); it is compatible with `Q` (`ρ(b) ≤ r(y)` on
the support of `Q`) and with `P` (`ρ(b) ≤ ρ(b') + 2d` on the `L`-blocks, from the oscillation of the
Agmon weight on the blocks of the top layer).

* `sum_wQ_le`, `sum_wQ_vec_le`, `sum_w_covA_le`: the block average and `A_{k,x}` in the weighted norm;
* `decCov_sub_decCov_eq`, `sum_w_decCov_sub_le`: `‖e^{ε ρ} (C_x(s) - C_x(1)) h‖² ≤ B (a_k+x)⁻⁴ ‖h‖²`
  from `vecM_decZ_sub_le` (`Balaban/Localization/DecoupledCovClose.lean`);
* `sum_w_sqrt_sub_le`, `sum_w_log_sub_le`: the `x`-integrals;
* `I4c_close_sqrt_entry`, `I4c_close_log_entry`: the matrix elements of `C^{1/2}(s) - C^{1/2}(1)`
  and `𝕃(s) - 𝕃(1)` at a unit point at distance `≥ D` from `W` are `≤ B e^{-γ_w D}`,
  `γ_w = xAgmonRate d L` (output side only: the input is unweighted);
* `I4c_close_sqrt_X0`: the consequence on `X₀` with `r₁ M₁ = (r₀ - 4 d L³) L^{m₁} / L`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Weighted

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι] {Q : Matrix κι (G.Ω 1) ℂ} {P : Matrix κι κι ℂ}
variable {a : ℕ → ℝ} {aT x ν : ℝ} {α : G.Ω 1 → ℂ} {κ δ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

theorem cwsq_agmonField_eq_sum (ε : ℝ) (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (s : G.Ω 1 → ℂ) :
    cwsq G (agmonField G ε r s) =
      ∑ x : G.Ω 1, ((G.spacing x) ^ 2)⁻¹ * (Real.exp (ε * r x) ^ 2 * ‖s x‖ ^ 2) := by
  unfold cwsq
  rw [Green.sum_eq_sum_subtype (G.Ω 1) _ (fun i hi => by
    simp [norm_agmonField, zeroExt_not_mem _ _ hi])]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [invSqSpacing_eq G x.2, norm_agmonField, zeroExt_mem]
  simp [mul_pow]

omit [DecidableEq κι] in
/-- Weighted contraction of the block average: if `ρ(b) ≤ r(y)` on the support of `Q`, then
`∑_b e^{2ε ρ(b)} |(Q f)(b)|² ≤ L^{2(k+1)} ∑_y ℓ⁻² e^{2ε r(y)} |f(y)|²`. -/
theorem sum_wQ_le (hU : IsUnitLattice G Q P) (hQn : ∀ b y, Q b y = ((‖Q b y‖ : ℝ) : ℂ))
    {ρ : κι → ℝ} {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ}
    (hρ : ∀ b (y : G.Ω 1), Q b y ≠ 0 → ρ b ≤ r y) (hε : 0 ≤ ε) (f : G.Ω 1 → ℂ) :
    ∑ b, Real.exp (ε * ρ b) ^ 2 * ‖(Q *ᵥ f) b‖ ^ 2 ≤
      ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ y : G.Ω 1,
        ((G.spacing y) ^ 2)⁻¹ * (Real.exp (ε * r y) ^ 2 * ‖f y‖ ^ 2) := by
  classical
  set ĝ : G.Ω 1 → ℂ := fun y => ((Real.exp (ε * r y) * ‖f y‖ : ℝ) : ℂ) with hĝ
  have hpt : ∀ b, Real.exp (ε * ρ b) * ‖(Q *ᵥ f) b‖ ≤ ‖(Q *ᵥ ĝ) b‖ := by
    intro b
    have h1 : ‖(Q *ᵥ f) b‖ ≤ ∑ y, ‖Q b y‖ * ‖f y‖ := by
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun y _ => (norm_mul _ _).le
    have h2 : (Q *ᵥ ĝ) b = ((∑ y, ‖Q b y‖ * (Real.exp (ε * r y) * ‖f y‖) : ℝ) : ℂ) := by
      simp only [Matrix.mulVec, dotProduct, hĝ]
      push_cast
      refine Finset.sum_congr rfl fun y _ => ?_
      nth_rewrite 1 [hQn b y]
      rfl
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (Finset.sum_nonneg fun y _ => by positivity)]
    calc Real.exp (ε * ρ b) * ‖(Q *ᵥ f) b‖ ≤ Real.exp (ε * ρ b) * ∑ y, ‖Q b y‖ * ‖f y‖ :=
          mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
      _ = ∑ y, Real.exp (ε * ρ b) * (‖Q b y‖ * ‖f y‖) := by rw [Finset.mul_sum]
      _ ≤ ∑ y, ‖Q b y‖ * (Real.exp (ε * r y) * ‖f y‖) := Finset.sum_le_sum fun y _ => by
          by_cases hq : Q b y = 0
          · simp [hq]
          · have hle := hρ b y hq
            have hexp : Real.exp (ε * ρ b) ≤ Real.exp (ε * r y) :=
              Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hle hε)
            have := mul_le_mul_of_nonneg_right hexp (mul_nonneg (norm_nonneg (Q b y)) (norm_nonneg (f y)))
            nlinarith
  calc ∑ b, Real.exp (ε * ρ b) ^ 2 * ‖(Q *ᵥ f) b‖ ^ 2 ≤ ∑ b, ‖(Q *ᵥ ĝ) b‖ ^ 2 := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) (hpt b) 2
    _ = Green.sqNorm (Q *ᵥ ĝ) := rfl
    _ ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * ∑ y : G.Ω 1, ((G.spacing y) ^ 2)⁻¹ * ‖ĝ y‖ ^ 2 :=
        sqNorm_Q_le hU ĝ
    _ = _ := by
        congr 1
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [hĝ]
        simp only [Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (ε * r y) * ‖f y‖)]
        rw [mul_pow]

omit [DecidableEq κι] in
theorem sum_wQ_vec_le (hU : IsUnitLattice G Q P) (hQn : ∀ b y, Q b y = ((‖Q b y‖ : ℝ) : ℂ))
    {ρ : κι → ℝ} {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ}
    (hρ : ∀ b (y : G.Ω 1), Q b y ≠ 0 → ρ b ≤ r y) (hε : 0 ≤ ε) (u : G.Ω 1 × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(liftRect N Q *ᵥ u) p‖ ^ 2 ≤
      ((L : ℝ) ^ (k + 1)) ^ 2 * vecM G ε r u := by
  classical
  rw [Fintype.sum_prod_type, Finset.sum_comm, vecM_eq, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have e : ∀ b : κι, (liftRect N Q *ᵥ u) (b, i) = (Q *ᵥ comp G u i) b := fun b =>
    liftRect_mulVec Q u b i
  simp only [e]
  rw [cwsq_agmonField_eq_sum]
  exact sum_wQ_le hU hQn hρ hε (comp G u i)

section CovAW

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem covA_mulVec_eq {c b x : ℝ} (Pm : Matrix ι ι ℂ) (h : ι → ℂ) :
    covA c b x Pm *ᵥ h = (((c + x)⁻¹ : ℝ) : ℂ) • h +
      ((((c + x + b)⁻¹ - (c + x)⁻¹ : ℝ)) : ℂ) • (Pm *ᵥ h) := by
  unfold covA
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec,
    Matrix.one_mulVec, smul_sub]
  have h1 : ((c : ℂ) + x)⁻¹ = (((c + x)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  have h2 : ((c : ℂ) + x + b)⁻¹ = (((c + x + b)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [h1, h2]
  push_cast
  module

omit [DecidableEq ι] in
theorem n2_le_of_norm_le {u v : ι → ℂ} (h : ∀ i, ‖u i‖ ≤ ‖v i‖) : n2 u ≤ n2 v := by
  unfold n2
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (h i) 2

end CovAW

section CovAW2

variable {d L N₁ m₁ k N : ℕ}
variable {κι : Type*} [Fintype κι] [DecidableEq κι] {P : Matrix κι κι ℂ}

theorem sum_w_covA_le {ρ : κι → ℝ} {ε c₀ : ℝ} (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀)
    (hρP : ∀ b b', P b b' ≠ 0 → ρ b ≤ ρ b' + c₀)
    (hPh : Pᴴ = P) (hPi : P * P = P) (hPn : ∀ b b', P b b' = ((‖P b b'‖ : ℝ) : ℂ))
    {c b x : ℝ} (hcx : 0 < c + x) (hb : 0 ≤ b) (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(covA c b x (liftOp N P) *ᵥ h) p‖ ^ 2 ≤
      (2 * Real.exp (ε * c₀) * (c + x)⁻¹) ^ 2 *
        ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖h p‖ ^ 2 := by
  classical
  set α : ℝ := (c + x)⁻¹ with hα
  set β : ℝ := (c + x + b)⁻¹ with hβ
  have hα0 : 0 < α := inv_pos.2 hcx
  have hβ0 : 0 < β := inv_pos.2 (by linarith)
  have hβα : β ≤ α := inv_anti₀ hcx (by linarith)
  set γ : ℝ := (α - β) * Real.exp (ε * c₀) with hγ
  have hE1 : 1 ≤ Real.exp (ε * c₀) := Real.one_le_exp (mul_nonneg hε hc₀)
  have hγ0 : 0 ≤ γ := mul_nonneg (by linarith) (Real.exp_pos _).le
  set ĥ : κι × Fin N → ℂ := fun p => ((Real.exp (ε * ρ p.1) * ‖h p‖ : ℝ) : ℂ) with hĥ
  set Pm : Matrix (κι × Fin N) (κι × Fin N) ℂ := liftOp N P with hPm
  have hPmh : Pmᴴ = Pm := by
    rw [hPm, liftOp_conjTranspose, hPh]
  have hPmi : Pm * Pm = Pm := by rw [hPm, ← liftOp_mul, hPi]
  -- pointwise bound
  have hpt : ∀ p : κι × Fin N, Real.exp (ε * ρ p.1) * ‖(covA c b x Pm *ᵥ h) p‖ ≤
      ‖(((α : ℝ) : ℂ) • ĥ + ((γ : ℝ) : ℂ) • (Pm *ᵥ ĥ)) p‖ := by
    rintro ⟨b0, i0⟩
    have hPĥ : (Pm *ᵥ ĥ) (b0, i0) =
        ((∑ b', ‖P b0 b'‖ * (Real.exp (ε * ρ b') * ‖h (b', i0)‖) : ℝ) : ℂ) := by
      rw [hPm, liftOp_mulVec]
      simp only [hĥ, Matrix.mulVec, dotProduct]
      push_cast
      refine Finset.sum_congr rfl fun b' _ => ?_
      nth_rewrite 1 [hPn b0 b']
      rfl
    have hPh' : ‖(Pm *ᵥ h) (b0, i0)‖ ≤ ∑ b', ‖P b0 b'‖ * ‖h (b', i0)‖ := by
      rw [hPm, liftOp_mulVec]
      simp only [Matrix.mulVec, dotProduct]
      refine (norm_sum_le _ _).trans ?_
      exact Finset.sum_le_sum fun b' _ => (norm_mul _ _).le
    have hw : Real.exp (ε * ρ b0) * ‖(Pm *ᵥ h) (b0, i0)‖ ≤
        Real.exp (ε * c₀) * ∑ b', ‖P b0 b'‖ * (Real.exp (ε * ρ b') * ‖h (b', i0)‖) := by
      calc Real.exp (ε * ρ b0) * ‖(Pm *ᵥ h) (b0, i0)‖ ≤
          Real.exp (ε * ρ b0) * ∑ b', ‖P b0 b'‖ * ‖h (b', i0)‖ :=
            mul_le_mul_of_nonneg_left hPh' (Real.exp_pos _).le
        _ = ∑ b', Real.exp (ε * ρ b0) * (‖P b0 b'‖ * ‖h (b', i0)‖) := by rw [Finset.mul_sum]
        _ ≤ ∑ b', Real.exp (ε * c₀) * (‖P b0 b'‖ * (Real.exp (ε * ρ b') * ‖h (b', i0)‖)) :=
            Finset.sum_le_sum fun b' _ => by
              by_cases hq : P b0 b' = 0
              · simp [hq]
              · have hle := hρP b0 b' hq
                have hexp : Real.exp (ε * ρ b0) ≤ Real.exp (ε * c₀) * Real.exp (ε * ρ b') := by
                  rw [← Real.exp_add]
                  exact Real.exp_le_exp.2 (by nlinarith)
                have := mul_le_mul_of_nonneg_right hexp
                  (mul_nonneg (norm_nonneg (P b0 b')) (norm_nonneg (h (b', i0))))
                nlinarith
        _ = Real.exp (ε * c₀) * ∑ b', ‖P b0 b'‖ * (Real.exp (ε * ρ b') * ‖h (b', i0)‖) := by
            rw [Finset.mul_sum]
    rw [covA_mulVec_eq]
    have hv : (((α : ℝ) : ℂ) • ĥ + ((γ : ℝ) : ℂ) • (Pm *ᵥ ĥ)) (b0, i0) =
        ((α * (Real.exp (ε * ρ b0) * ‖h (b0, i0)‖) + γ *
          ∑ b', ‖P b0 b'‖ * (Real.exp (ε * ρ b') * ‖h (b', i0)‖) : ℝ) : ℂ) := by
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, hPĥ]
      have hh0 : ĥ (b0, i0) = ((Real.exp (ε * ρ b0) * ‖h (b0, i0)‖ : ℝ) : ℂ) := rfl
      rw [hh0]
      push_cast; ring
    rw [hv, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    calc Real.exp (ε * ρ b0) * ‖((α : ℂ) * h (b0, i0) + (((β - α : ℝ)) : ℂ) * (Pm *ᵥ h) (b0, i0))‖
        ≤ Real.exp (ε * ρ b0) * (‖(α : ℂ) * h (b0, i0)‖ +
            ‖(((β - α : ℝ)) : ℂ) * (Pm *ᵥ h) (b0, i0)‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (Real.exp_pos _).le
      _ = α * (Real.exp (ε * ρ b0) * ‖h (b0, i0)‖) + (α - β) *
            (Real.exp (ε * ρ b0) * ‖(Pm *ᵥ h) (b0, i0)‖) := by
          simp only [norm_mul, Complex.norm_real, Real.norm_of_nonneg hα0.le,
            Real.norm_eq_abs, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hβα)]
          ring
      _ ≤ α * (Real.exp (ε * ρ b0) * ‖h (b0, i0)‖) + (α - β) * (Real.exp (ε * c₀) *
            ∑ b', ‖P b0 b'‖ * (Real.exp (ε * ρ b') * ‖h (b', i0)‖)) := by
          gcongr
      _ = _ := by rw [hγ]; ring
  set v : κι × Fin N → ℂ := ((α : ℝ) : ℂ) • ĥ + ((γ : ℝ) : ℂ) • (Pm *ᵥ ĥ) with hv
  have hsum : ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(covA c b x Pm *ᵥ h) p‖ ^ 2 ≤
      Green.sqNorm v := by
    unfold Green.sqNorm
    refine Finset.sum_le_sum fun p _ => ?_
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (hpt p) 2
  have hn2 : n2 v ≤ (α + γ) * n2 ĥ := by
    have h1 := n2_add_le (((α : ℝ) : ℂ) • ĥ) (((γ : ℝ) : ℂ) • (Pm *ᵥ ĥ))
    rw [n2_smul, n2_smul, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hα0.le, Real.norm_of_nonneg hγ0] at h1
    have h2 : n2 (Pm *ᵥ ĥ) ≤ n2 ĥ := by
      have := sqNorm_proj hPmh hPmi ĥ
      have h3 : Green.sqNorm (Pm *ᵥ ĥ) ≤ Green.sqNorm ĥ := by
        have := sqNorm_nonneg' ((1 - Pm) *ᵥ ĥ)
        linarith
      unfold n2
      exact Real.sqrt_le_sqrt h3
    calc n2 v ≤ α * n2 ĥ + γ * n2 (Pm *ᵥ ĥ) := h1
      _ ≤ α * n2 ĥ + γ * n2 ĥ := by gcongr
      _ = (α + γ) * n2 ĥ := by ring
  have hĥs : Green.sqNorm ĥ = ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖h p‖ ^ 2 := by
    unfold Green.sqNorm
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [hĥ]
    simp only [Complex.norm_real, Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp (ε * ρ p.1) * ‖h p‖)]
    rw [mul_pow]
  have hcoef : α + γ ≤ 2 * Real.exp (ε * c₀) * α := by
    rw [hγ]
    nlinarith [mul_le_mul_of_nonneg_left hE1 hα0.le, mul_nonneg hβ0.le (Real.exp_pos (ε * c₀)).le]
  calc _ ≤ Green.sqNorm v := hsum
    _ = (n2 v) ^ 2 := (n2_sq v).symm
    _ ≤ ((α + γ) * n2 ĥ) ^ 2 := pow_le_pow_left₀ (n2_nonneg _) hn2 2
    _ = (α + γ) ^ 2 * Green.sqNorm ĥ := by rw [mul_pow, n2_sq]
    _ ≤ (2 * Real.exp (ε * c₀) * α) ^ 2 * Green.sqNorm ĥ := by
        refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hcoef 2) ?_
        exact sqNorm_nonneg' ĥ
    _ = _ := by rw [hĥs]

end CovAW2

section DecCovW

/-- The constant of the weighted covariance closeness. -/
noncomputable def covCloseSq (d L : ℕ) (ak κ ε c₀ : ℝ) : ℝ :=
  ak ^ 4 * (L : ℝ) ^ 4 * 4 * Real.exp (ε * c₀) ^ 2 * zCloseConst d L * Real.exp (N0 d L * κ) ^ 2

theorem covCloseSq_nonneg (d L : ℕ) (ak κ ε c₀ : ℝ) : 0 ≤ covCloseSq d L ak κ ε c₀ := by
  unfold covCloseSq zCloseConst closeConstX gradCloseConstX gradStarConstX valConstX
  have := commXConst_nonneg d L
  positivity

theorem decCov_sub_decCov_eq :
    decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P =
      (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) •
        (covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) * liftRect N Q *
          (decZ G a aT x ν α s φ - decZ G a aT x ν α (fun _ => 1) φ) * (liftRect N Q)ᵀ *
          covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) := by
  unfold decCov decZ
  simp only [Matrix.mul_sub, Matrix.sub_mul, smul_sub]
  abel

end DecCovW

section DecCovW2Cover

variable {Cx : ℝ} (D : Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ xAgmonRate d L) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P)
  (hQn : ∀ b y, Q b y = ((‖Q b y‖ : ℝ) : ℂ)) (hPn : ∀ b b', P b b' = ((‖P b b'‖ : ℝ) : ℂ))
  {ρ : κι → ℝ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
  (hρQ : ∀ b (y : G.Ω 1), Q b y ≠ 0 → ρ b ≤ truncSetDistR G W T y)
  (hρP : ∀ b b', P b b' ≠ 0 → ρ b ≤ ρ b' + c₀)
include D hW hε0 hε1 hφ hδ hsm hU hQn hPn hc₀ hρQ hρP

/-- **Weighted closeness of the covariance** for the data `Dec2.XData` of the pair
`(coverOf G, G)`:
`∑ e^{2ε ρ} |(C_x(s) - C_x(1)) h|² ≤ B (a_k + x)⁻⁴ ‖h‖²`. -/
theorem sum_w_decCov_sub_le_cover (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖((decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P) *ᵥ h) p‖ ^ 2 ≤
      covCloseSq d L (a k) κ ε c₀ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm h := by
  classical
  have hak : a k ∈ Set.Icc (1 / 2 : ℝ) 2 := ⟨D.st.hak1, D.st.hak2⟩
  have hcx : 0 < a k + x := by have := D.x0; linarith [hak.1]
  have hb : 0 ≤ aT / (L : ℝ) ^ 2 := by
    have := D.st.haT1
    positivity
  obtain ⟨hPh, hPi⟩ := liftOp_herm_idem (N := N) hU
  have hPh' : Pᴴ = P := hU.herm
  have hPi' : P * P = P := hU.idem
  set r := truncSetDistR G W T with hrdef
  set Av := covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P) with hAv
  set cs : ℂ := (((a k) ^ 2 / (L : ℝ) ^ (2 * k) : ℝ) : ℂ) with hcs
  set Zd := decZ G a aT x ν α s φ - decZ G a aT x ν α (fun _ => 1) φ with hZd
  rw [decCov_sub_decCov_eq]
  have hrw : (cs • (Av * liftRect N Q * Zd * (liftRect N Q)ᵀ * Av)) *ᵥ h =
      cs • (Av *ᵥ (liftRect N Q *ᵥ (Zd *ᵥ ((liftRect N Q)ᵀ *ᵥ (Av *ᵥ h))))) := by
    rw [Matrix.smul_mulVec]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hrw]
  set Λ : ℝ := (L : ℝ) ^ (k + 1) with hΛ
  set z := Av *ᵥ h with hz
  have s1 : Green.sqNorm z ≤ ((a k + x)⁻¹) ^ 2 * Green.sqNorm h := sqNorm_covA_le hcx hb hPh hPi h
  set w := (liftRect N Q)ᵀ *ᵥ z with hw
  have hw_supp : ∀ y i, w (y, i) ≠ 0 → (y : CTorus d L N₁ m₁ (k + 1)) ∈ G.layer (k + 1) := by
    intro y i hne
    by_contra hy
    apply hne
    rw [hw, liftRect_transpose, liftRect_mulVec]
    simp only [mulVec, dotProduct, transpose_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : Q b y = 0 := by
      by_contra hne'
      exact hy (hU.layer b y hne')
    simp [this]
  have s2 : Green.sqNorm w ≤ Green.sqNorm z := by
    rw [hw, liftRect_transpose]; exact sqNorm_liftRect_le hU.contrT z
  have s3 : vecSrc G 0 (fun _ => 0) w ≤ Λ ^ 2 * Green.sqNorm w := vecSrc0_le_of_supp w hw_supp
  set u := Zd *ᵥ w with hu
  have s4 := vecM_decZ_sub_le_cover D hW T hε0 hε1 hφ hδ hsm w
  set v := liftRect N Q *ᵥ u with hv
  have s5 : ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖v p‖ ^ 2 ≤
      Λ ^ 2 * vecM G ε r u := sum_wQ_vec_le hU hQn hρQ hε0 u
  have s6 := sum_w_covA_le (ρ := ρ) hε0 hc₀ hρP hPh' hPi' hPn hcx hb v
  have hα0 : 0 ≤ ((a k + x)⁻¹) ^ 2 := by positivity
  have hΛ0 : 0 ≤ Λ ^ 2 := by positivity
  have hcs2 : ‖cs‖ ^ 2 * Λ ^ 2 * Λ ^ 2 = (a k) ^ 4 * (L : ℝ) ^ 4 := by
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    have : ‖cs‖ = (a k) ^ 2 / (L : ℝ) ^ (2 * k) := by
      rw [hcs, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    rw [this, hΛ]
    field_simp
    ring
  have hcs0 : 0 ≤ ‖cs‖ ^ 2 := by positivity
  have hsh := sqNorm_nonneg' h
  have hsw := sqNorm_nonneg' w
  have hsv : 0 ≤ vecSrc G 0 (fun _ => 0) w := vecSrc_nonneg G 0 _ w
  have hzc : 0 ≤ zCloseConst d L := by
    unfold zCloseConst closeConstX gradCloseConstX gradStarConstX valConstX
    have := commXConst_nonneg d L
    positivity
  have hE0 : 0 ≤ Real.exp (N0 d L * κ) ^ 2 := sq_nonneg _
  have hMn : 0 ≤ vecM G ε r u := vecM_nonneg G ε r u
  set Eκ := Real.exp (N0 d L * κ) ^ 2 with hEκ
  set e2 := Real.exp (ε * c₀) with he2
  have he2p : 0 < e2 := Real.exp_pos _
  -- the weighted sum of the final vector
  have hfin : ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
      ‖(cs • (Av *ᵥ v)) p‖ ^ 2 =
      ‖cs‖ ^ 2 * ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(Av *ᵥ v) p‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow]
    ring
  rw [hfin]
  have hchain : ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(Av *ᵥ v) p‖ ^ 2 ≤
      (2 * e2 * (a k + x)⁻¹) ^ 2 * (Λ ^ 2 * (zCloseConst d L * Eκ *
        (Λ ^ 2 * (((a k + x)⁻¹) ^ 2 * Green.sqNorm h)))) := by
    refine s6.trans ?_
    refine mul_le_mul_of_nonneg_left (s5.trans ?_) (by positivity)
    refine mul_le_mul_of_nonneg_left (s4.trans ?_) hΛ0
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact s3.trans (mul_le_mul_of_nonneg_left (s2.trans s1) hΛ0)
  calc ‖cs‖ ^ 2 * ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(Av *ᵥ v) p‖ ^ 2
      ≤ ‖cs‖ ^ 2 * ((2 * e2 * (a k + x)⁻¹) ^ 2 * (Λ ^ 2 * (zCloseConst d L * Eκ *
        (Λ ^ 2 * (((a k + x)⁻¹) ^ 2 * Green.sqNorm h))))) :=
        mul_le_mul_of_nonneg_left hchain hcs0
    _ = covCloseSq d L (a k) κ ε c₀ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm h := by
        unfold covCloseSq
        rw [← hcs2]
        ring

end DecCovW2Cover

section DecCovW2

variable (D : XData G a aT ν x α κ s) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ xAgmonRate d L) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) (hU : IsUnitLattice G Q P)
  (hQn : ∀ b y, Q b y = ((‖Q b y‖ : ℝ) : ℂ)) (hPn : ∀ b b', P b b' = ((‖P b b'‖ : ℝ) : ℂ))
  {ρ : κι → ℝ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
  (hρQ : ∀ b (y : G.Ω 1), Q b y ≠ 0 → ρ b ≤ truncSetDistR G W T y)
  (hρP : ∀ b b', P b b' ≠ 0 → ρ b ≤ ρ b' + c₀)
include D hW hε0 hε1 hφ hδ hsm hU hQn hPn hc₀ hρQ hρP

/-- **Weighted closeness of the covariance**:
`∑ e^{2ε ρ} |(C_x(s) - C_x(1)) h|² ≤ B (a_k + x)⁻⁴ ‖h‖²`. -/
theorem sum_w_decCov_sub_le (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖((decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P) *ᵥ h) p‖ ^ 2 ≤
      covCloseSq d L (a k) κ ε c₀ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm h :=
  sum_w_decCov_sub_le_cover D.toCover hW T hε0 hε1 hφ hδ hsm hU hQn hPn hc₀ hρQ hρP h

end DecCovW2

section IntW

open MeasureTheory Set

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_sq_mul_eq_sqNorm_diag (w : ι → ℝ) (v : ι → ℂ) :
    ∑ p, w p ^ 2 * ‖v p‖ ^ 2 = Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ v) := by
  unfold Green.sqNorm
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mulVec_diagonal, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- A weighted operator bound passes to the `x`-integral. -/
theorem sqNorm_diag_intMat_le (μ : Measure ℝ) (w : ι → ℝ) (F : ℝ → Matrix ι ι ℂ)
    (hint : ∀ p q, Integrable (fun x => F x p q) μ) (g : ℝ → ℝ) (hg : Integrable g μ)
    (hg0 : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hbd : ∀ᵐ x ∂μ, ∀ f : ι → ℂ,
      Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (F x *ᵥ f)) ≤ g x ^ 2 * Green.sqNorm f)
    (f : ι → ℂ) :
    Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (intMat μ F *ᵥ f)) ≤
      (∫ x, g x ∂μ) ^ 2 * Green.sqNorm f := by
  have h1 : Matrix.diagonal (fun p => (w p : ℂ)) * intMat μ F =
      intMat μ (fun x => Matrix.diagonal (fun p => (w p : ℂ)) * F x) :=
    intMat_mul_left hint _
  rw [Matrix.mulVec_mulVec, h1]
  refine sqNorm_intMat_le μ (fun x => Matrix.diagonal (fun p => (w p : ℂ)) * F x) ?_ g hg hg0 ?_ f
  · intro p q
    simp only [Matrix.diagonal_mul]
    exact (hint p q).const_mul _
  · filter_upwards [hbd] with x hx f
    rw [← Matrix.mulVec_mulVec]
    exact hx f

end IntW

section SqrtLogW

open MeasureTheory Set

/-- The constant of the weighted closeness of `C^{1/2}`. -/
noncomputable def covWSqrt (d L : ℕ) (ak κ ε c₀ : ℝ) : ℝ :=
  Real.sqrt (covCloseSq d L ak κ ε c₀) * (ak⁻¹ / Real.sqrt ak)

/-- The constant of the weighted closeness of `𝕃`. -/
noncomputable def covWLog (d L : ℕ) (ak κ ε c₀ : ℝ) : ℝ :=
  Real.sqrt (covCloseSq d L ak κ ε c₀) / ak

/-! ### The `x`-integral for the data `Dec2.XData` of the pair `(coverOf G, G)` -/

section SqrtCover

variable {Cx : ℝ} (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hfam1 : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α 0 (fun _ => 1) Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hsm1 : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4) (hU : IsUnitLattice G Q P)
  {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ xAgmonRate d L)
  (hQn : ∀ b y, Q b y = ((‖Q b y‖ : ℝ) : ℂ)) (hPn : ∀ b b', P b b' = ((‖P b b'‖ : ℝ) : ℂ))
  {ρ : κι → ℝ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
  (hρQ : ∀ b (y : G.Ω 1), Q b y ≠ 0 → ρ b ≤ truncSetDistR G W T y)
  (hρP : ∀ b b', P b b' ≠ 0 → ρ b ≤ ρ b' + c₀)
include hfam hfam1 hφ hδ hsm hsm1 hU hW hε0 hε1 hQn hPn hc₀ hρQ hρP

/-- **Weighted closeness of `C^{1/2}`** for the data `Dec2.XData` of the pair `(coverOf G, G)`. -/
theorem sum_w_sqrt_sub_le_cover (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖((decCovSqrt G a aT ν α s φ Q P - decCovSqrt G a aT ν α (fun _ => 1) φ Q P) *ᵥ h) p‖ ^ 2 ≤
      (covWSqrt d L (a k) κ ε c₀) ^ 2 * Green.sqNorm h := by
  classical
  have hak := aux_hak_cover hfam
  have hcc := covCloseSq_nonneg d L (a k) κ ε c₀
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set w : κι × Fin N → ℝ := fun p => Real.exp (ε * ρ p.1) with hw
  set F : ℝ → Matrix (κι × Fin N) (κι × Fin N) ℂ := fun x =>
    ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (decCov G a aT x ν α s φ Q P -
      decCov G a aT x ν α (fun _ => 1) φ Q P) with hF
  have hFeq : F = fun x => decSqrtInt G a aT ν α s φ Q P x -
      decSqrtInt G a aT ν α (fun _ => 1) φ Q P x := by
    funext x; simp only [hF, decSqrtInt, smul_sub]
  have hint : ∀ p q, Integrable (fun x => F x p q) μ := by
    intro p q
    rw [hFeq]
    exact (integrable_decSqrtInt_cover hfam hφ hδ hsm hU p q).sub
      (integrable_decSqrtInt_cover hfam1 hφ hδ hsm1 hU p q)
  have hdiff : decCovSqrt G a aT ν α s φ Q P - decCovSqrt G a aT ν α (fun _ => 1) φ Q P =
      ((1 / Real.pi : ℝ) : ℂ) • intMat μ F := by
    unfold decCovSqrt
    rw [← smul_sub, hFeq, intMat_sub' (integrable_decSqrtInt_cover hfam hφ hδ hsm hU)
      (integrable_decSqrtInt_cover hfam1 hφ hδ hsm1 hU)]
  set g : ℝ → ℝ := fun x => Real.sqrt (covCloseSq d L (a k) κ ε c₀) *
    (x ^ (-(1 / 2 : ℝ)) * ((a k + x)⁻¹) ^ 2) with hg
  have hgi : Integrable g μ := (integrableOn_rpow_inv_add_sq hak).const_mul _
  have hg0 : ∀ᵐ x ∂μ, 0 ≤ g x := (ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun x hx => by
      have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos (mem_Ioi.mp hx) _
      simp only [hg]; positivity)
  have hbd : ∀ᵐ x ∂μ, ∀ f : κι × Fin N → ℂ,
      Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (F x *ᵥ f)) ≤ g x ^ 2 * Green.sqNorm f := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx f => ?_)
    have hx0 : 0 < x := mem_Ioi.mp hx
    have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
    have hpt := sum_w_decCov_sub_le_cover (hfam x hx0.le) hW T hε0 hε1 hφ hδ hsm hU hQn hPn hc₀
      hρQ hρP f
    have e : Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (F x *ᵥ f) =
        ((x ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) • (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ
          ((decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P) *ᵥ f)) := by
      simp only [hF, Matrix.smul_mulVec, Matrix.mulVec_smul]
    rw [e, sqNorm_smul, Complex.norm_real, Real.norm_of_nonneg h3.le]
    have e2 : Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ
        ((decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P) *ᵥ f)) =
        ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
          ‖((decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P) *ᵥ f) p‖ ^ 2 := by
      unfold Green.sqNorm
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Matrix.mulVec_diagonal, norm_mul, mul_pow, hw, Complex.norm_real,
        Real.norm_of_nonneg (Real.exp_pos _).le]
    rw [e2]
    have hs0 := sqNorm_nonneg' f
    calc (x ^ (-(1 / 2 : ℝ))) ^ 2 * ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * _
        ≤ (x ^ (-(1 / 2 : ℝ))) ^ 2 * (covCloseSq d L (a k) κ ε c₀ * ((a k + x)⁻¹) ^ 4 *
          Green.sqNorm f) := mul_le_mul_of_nonneg_left hpt (sq_nonneg _)
      _ = g x ^ 2 * Green.sqNorm f := by
          simp only [hg, mul_pow]
          rw [Real.sq_sqrt hcc]
          ring
  have hmain := sqNorm_diag_intMat_le μ w F hint g hgi hg0 hbd h
  have hI : ∫ x, g x ∂μ ≤ Real.sqrt (covCloseSq d L (a k) κ ε c₀) *
      ((a k)⁻¹ * (Real.pi / Real.sqrt (a k))) := by
    rw [hg]
    simp only []
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (integral_rpow_inv_add_sq_le hak) (Real.sqrt_nonneg _)
  have hI0 : 0 ≤ ∫ x, g x ∂μ := integral_nonneg_of_ae hg0
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [hdiff]
  have e3 : ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
      ‖((((1 / Real.pi : ℝ) : ℂ) • intMat μ F) *ᵥ h) p‖ ^ 2 =
      (1 / Real.pi) ^ 2 * Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (intMat μ F *ᵥ h)) := by
    have e4 : (((1 / Real.pi : ℝ) : ℂ) • intMat μ F) *ᵥ h =
        ((1 / Real.pi : ℝ) : ℂ) • (intMat μ F *ᵥ h) := Matrix.smul_mulVec _ _ _
    rw [e4]
    have e5 : ∀ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖(((1 / Real.pi : ℝ) : ℂ) • (intMat μ F *ᵥ h)) p‖ ^ 2 =
        (1 / Real.pi) ^ 2 * (w p ^ 2 * ‖(intMat μ F *ᵥ h) p‖ ^ 2) := by
      intro p
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : 0 ≤ 1 / Real.pi), hw]
      ring
    simp only [e5]
    rw [← Finset.mul_sum, sum_sq_mul_eq_sqNorm_diag]
  rw [e3]
  have hs0 := sqNorm_nonneg' h
  calc (1 / Real.pi) ^ 2 * Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (intMat μ F *ᵥ h))
      ≤ (1 / Real.pi) ^ 2 * ((∫ x, g x ∂μ) ^ 2 * Green.sqNorm h) :=
        mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = ((1 / Real.pi) * ∫ x, g x ∂μ) ^ 2 * Green.sqNorm h := by ring
    _ ≤ (covWSqrt d L (a k) κ ε c₀) ^ 2 * Green.sqNorm h := by
        refine mul_le_mul_of_nonneg_right ?_ hs0
        refine pow_le_pow_left₀ (by positivity) ?_ 2
        calc (1 / Real.pi) * ∫ x, g x ∂μ ≤ (1 / Real.pi) * (Real.sqrt (covCloseSq d L (a k) κ ε c₀) *
            ((a k)⁻¹ * (Real.pi / Real.sqrt (a k)))) :=
              mul_le_mul_of_nonneg_left hI (by positivity)
          _ = covWSqrt d L (a k) κ ε c₀ := by
              unfold covWSqrt
              have : Real.sqrt (a k) ≠ 0 := (Real.sqrt_pos.2 hak).ne'
              field_simp

end SqrtCover

variable (H : CovStanding G a aT ν α κ s δ φ Q P)
  (H1 : CovStanding G a aT ν α 0 (fun _ => 1) δ φ Q P)
  {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) (T : ℝ) {ε : ℝ} (hε0 : 0 ≤ ε)
  (hε1 : ε ≤ xAgmonRate d L)
  (hQn : ∀ b y, Q b y = ((‖Q b y‖ : ℝ) : ℂ)) (hPn : ∀ b b', P b b' = ((‖P b b'‖ : ℝ) : ℂ))
  {ρ : κι → ℝ} {c₀ : ℝ} (hc₀ : 0 ≤ c₀)
  (hρQ : ∀ b (y : G.Ω 1), Q b y ≠ 0 → ρ b ≤ truncSetDistR G W T y)
  (hρP : ∀ b b', P b b' ≠ 0 → ρ b ≤ ρ b' + c₀)
include H H1 hW hε0 hε1 hQn hPn hc₀ hρQ hρP

omit H1 in
theorem sum_w_decCov_sub_le' {x : ℝ} (hx : 0 ≤ x) (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖((decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P) *ᵥ h) p‖ ^ 2 ≤
      covCloseSq d L (a k) κ ε c₀ * ((a k + x)⁻¹) ^ 4 * Green.sqNorm h :=
  sum_w_decCov_sub_le (H.fam x hx) hW T hε0 hε1 H.field H.nonneg H.small H.unit hQn hPn hc₀ hρQ hρP h

theorem sum_w_sqrt_sub_le (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖((decCovSqrt G a aT ν α s φ Q P - decCovSqrt G a aT ν α (fun _ => 1) φ Q P) *ᵥ h) p‖ ^ 2 ≤
      (covWSqrt d L (a k) κ ε c₀) ^ 2 * Green.sqNorm h :=
  sum_w_sqrt_sub_le_cover (fun x hx => (H.fam x hx).toCover) (fun x hx => (H1.fam x hx).toCover)
    H.field H.nonneg H.small H1.small H.unit hW T hε0 hε1 hQn hPn hc₀ hρQ hρP h

theorem sum_w_log_sub_le (h : κι × Fin N → ℂ) :
    ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 *
        ‖((decLog G a aT ν α s φ Q P - decLog G a aT ν α (fun _ => 1) φ Q P) *ᵥ h) p‖ ^ 2 ≤
      (covWLog d L (a k) κ ε c₀) ^ 2 * Green.sqNorm h := by
  classical
  have hak := H.hak
  have hcc := covCloseSq_nonneg d L (a k) κ ε c₀
  set μ := volume.restrict (Ioi (0 : ℝ)) with hμ
  set w : κι × Fin N → ℝ := fun p => Real.exp (ε * ρ p.1) with hw
  set F : ℝ → Matrix (κι × Fin N) (κι × Fin N) ℂ := fun x =>
    decCov G a aT x ν α s φ Q P - decCov G a aT x ν α (fun _ => 1) φ Q P with hF
  have hint : ∀ p q, Integrable (fun x => F x p q) μ := by
    intro p q
    have := (integrable_decSub H p q).sub (integrable_decSub H1 p q)
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF, Matrix.sub_apply, Pi.sub_apply]
    ring
  have hdiff : decLog G a aT ν α s φ Q P - decLog G a aT ν α (fun _ => 1) φ Q P =
      -intMat μ F := by
    unfold decLog
    have hI := intMat_sub' (μ := μ) (integrable_decSub H) (integrable_decSub H1)
    have hF' : (fun x => (decCov G a aT x ν α s φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P)) -
        (decCov G a aT x ν α (fun _ => 1) φ Q P - covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N P))) = F := by
      funext x; simp only [hF]; abel
    rw [hF'] at hI
    rw [hI]; abel
  set g : ℝ → ℝ := fun x => Real.sqrt (covCloseSq d L (a k) κ ε c₀) * ((a k + x)⁻¹) ^ 2 with hg
  have hgi : Integrable g μ := (integrableOn_inv_add_sq hak).const_mul _
  have hg0 : ∀ᵐ x ∂μ, 0 ≤ g x := (ae_restrict_iff' measurableSet_Ioi).2
    (Filter.Eventually.of_forall fun x hx => by
      simp only [hg]; positivity)
  have hbd : ∀ᵐ x ∂μ, ∀ f : κι × Fin N → ℂ,
      Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (F x *ᵥ f)) ≤ g x ^ 2 * Green.sqNorm f := by
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx f => ?_)
    have hx0 : 0 < x := mem_Ioi.mp hx
    have hpt := sum_w_decCov_sub_le' H hW T hε0 hε1 hQn hPn hc₀ hρQ hρP hx0.le f
    rw [← sum_sq_mul_eq_sqNorm_diag]
    refine hpt.trans ?_
    simp only [hg, mul_pow]
    rw [Real.sq_sqrt hcc]
    have : ((a k + x)⁻¹) ^ 2 ^ 2 = ((a k + x)⁻¹) ^ 4 := by ring
    rw [← pow_mul]
  have hmain := sqNorm_diag_intMat_le μ w F hint g hgi hg0 hbd h
  have hI : ∫ x, g x ∂μ = Real.sqrt (covCloseSq d L (a k) κ ε c₀) / a k := by
    rw [hg]
    simp only []
    rw [integral_const_mul, hμ, integral_inv_add_sq hak]
    ring
  rw [hdiff]
  have hs0 := sqNorm_nonneg' h
  have e3 : ∑ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖((-intMat μ F) *ᵥ h) p‖ ^ 2 =
      Green.sqNorm (Matrix.diagonal (fun p => (w p : ℂ)) *ᵥ (intMat μ F *ᵥ h)) := by
    rw [Matrix.neg_mulVec]
    have : ∀ p : κι × Fin N, Real.exp (ε * ρ p.1) ^ 2 * ‖(-(intMat μ F *ᵥ h)) p‖ ^ 2 =
        w p ^ 2 * ‖(intMat μ F *ᵥ h) p‖ ^ 2 := by
      intro p; simp [hw, norm_neg]
    simp only [this]
    exact sum_sq_mul_eq_sqNorm_diag w _
  rw [e3]
  refine hmain.trans ?_
  rw [hI]
  unfold covWLog
  exact le_rfl

end SqrtLogW

section Final

open Classical in
/-- The weight on the unit lattice: the minimum over the block of a weight on the fine sites. -/
noncomputable def unitRho (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (b : UnitTorus d L N₁ m₁ k) : ℝ :=
  if h : (Finset.univ.filter fun y : CTorus d L N₁ m₁ (k + 1) => unitBlock y = b).Nonempty then
    (Finset.univ.filter fun y : CTorus d L N₁ m₁ (k + 1) => unitBlock y = b).inf' h r else 0

theorem unitRho_le (r : CTorus d L N₁ m₁ (k + 1) → ℝ) {b : UnitTorus d L N₁ m₁ k}
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : unitBlock y = b) : unitRho r b ≤ r y := by
  classical
  have hne : (Finset.univ.filter fun y : CTorus d L N₁ m₁ (k + 1) => unitBlock y = b).Nonempty :=
    ⟨y, by simp [hy]⟩
  simp only [unitRho, hne, ↓reduceDIte]
  exact Finset.inf'_le _ (by simp [hy])

theorem exists_unitRho_eq (r : CTorus d L N₁ m₁ (k + 1) → ℝ) (b : UnitTorus d L N₁ m₁ k) :
    ∃ y, unitBlock y = b ∧ unitRho r b = r y := by
  classical
  obtain ⟨y0, hy0⟩ := unitBlock_surj (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) b
  have hne : (Finset.univ.filter fun y : CTorus d L N₁ m₁ (k + 1) => unitBlock y = b).Nonempty :=
    ⟨y0, by simp [hy0]⟩
  obtain ⟨y, hy, hmin⟩ := Finset.exists_mem_eq_inf' hne r
  refine ⟨y, by simpa using hy, ?_⟩
  simp only [unitRho, hne, ↓reduceDIte]
  exact hmin

theorem le_unitRho {r : CTorus d L N₁ m₁ (k + 1) → ℝ} {b : UnitTorus d L N₁ m₁ k} {D : ℝ}
    (h : ∀ y, unitBlock y = b → D ≤ r y) : D ≤ unitRho r b := by
  obtain ⟨y, hy, he⟩ := exists_unitRho_eq r b
  rw [he]; exact h y hy

theorem unitQ_nonneg_real (b : unitPts G) (y : G.Ω 1) :
    unitQ G b y = ((‖unitQ G b y‖ : ℝ) : ℂ) := by
  unfold unitQ
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  · simp

theorem unitP_nonneg_real (b b' : unitPts G) :
    unitP G b b' = ((‖unitP G b b'‖ : ℝ) : ℂ) := by
  unfold unitP
  split_ifs
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  · simp

theorem XData.toOne {a : ℕ → ℝ} {aT ν x : ℝ} {α : G.Ω 1 → ℂ} {κ : ℝ}
    {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ} (D : XData G a aT ν x α κ s) :
    XData G a aT ν x α 0 (fun _ => 1) :=
  ⟨D.st, D.pot, D.x0, le_rfl, by
    simp only [mul_zero, Real.exp_zero, mul_one]
    have := cstarX_pos d L
    have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
    nlinarith [D.big], fun P => by simp⟩

/-- The data of (DG7) of a pair `(C, G)` at `s` give those at `s ≡ 1`, `κ = 0`. -/
theorem Dec2.XData.toOne {C : DecCover d L N₁ m₁ (k + 1)} {Cx : ℝ} {a : ℕ → ℝ} {aT ν x : ℝ}
    {α : G.Ω 1 → ℂ} {κ : ℝ} {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
    (D : Dec2.XData C G a aT ν x α κ s Cx) : Dec2.XData C G a aT ν x α 0 (fun _ => 1) Cx :=
  ⟨D.st, D.Cx_nn, D.pot, D.x0, le_rfl, by
    simp only [mul_zero, Real.exp_zero, mul_one]
    have := Dec2.cstarX_pos d L D.Cx_nn
    have hE1 : 1 ≤ Real.exp (N0 d L * κ) := Real.one_le_exp (by have := D.κ0; positivity)
    nlinarith [D.big], fun P => by simp⟩

theorem unitRho_ge {W : Finset (CTorus d L N₁ m₁ (k + 1))} {D : ℝ} (hD : 0 ≤ D)
    {b : UnitTorus d L N₁ m₁ k}
    (hb : ∀ y, unitBlock y = b → ENNReal.ofReal D ≤ siteSetDist G W y) :
    D ≤ unitRho (truncSetDistR G W D) b := by
  refine le_unitRho fun y hy => ?_
  have h := hb y hy
  unfold truncSetDistR
  rw [min_eq_right h, ENNReal.toReal_ofReal hD]

theorem unitRho_P_compat (W : Finset (CTorus d L N₁ m₁ (k + 1))) (T : ℝ) (b b' : unitPts G)
    (h : unitP G b b' ≠ 0) :
    unitRho (truncSetDistR G W T) b.1 ≤ unitRho (truncSetDistR G W T) b'.1 + 2 * d := by
  obtain ⟨y0, hy0, he0⟩ := exists_unitRho_eq (truncSetDistR G W T) b.1
  obtain ⟨y1, hy1, he1⟩ := exists_unitRho_eq (truncSetDistR G W T) b'.1
  have hP1 : unitBlock1 b.1 = unitBlock1 b'.1 := by
    by_contra hne; apply h; simp [unitP, hne]
  have hy0l : y0 ∈ G.layer (k + 1) := (unitBlock_mem_iff G y0).1 (hy0 ▸ b.2)
  have hj : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y1 =
      jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y0 := by
    rw [← unitBlock1_unitBlock, ← unitBlock1_unitBlock, hy0, hy1]; exact hP1.symm
  have hb := (isAgmonWeight_truncSetDistR G W T).block (k + 1) (by omega) le_rfl y0 y1 hy0l hj
  rw [he0, he1]
  have := (abs_le.1 hb).2
  linarith

theorem unitRho_Q_compat (W : Finset (CTorus d L N₁ m₁ (k + 1))) (T : ℝ) (b : unitPts G)
    (y : G.Ω 1) (h : unitQ G b y ≠ 0) :
    unitRho (truncSetDistR G W T) b.1 ≤ truncSetDistR G W T y := by
  refine unitRho_le _ ?_
  by_contra hne; apply h; simp [unitQ, hne]

theorem entry_le_of_sum_w {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℂ) (w : ι → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (h : ∀ v : ι → ℂ, ∑ p, w p ^ 2 * ‖(M *ᵥ v) p‖ ^ 2 ≤ B ^ 2 * Green.sqNorm v) (p q : ι) :
    w p * ‖M p q‖ ≤ B := by
  have h1 := h (Pi.single q 1)
  have h2 : Green.sqNorm (Pi.single q (1 : ℂ) : ι → ℂ) = 1 := by
    unfold Green.sqNorm
    rw [Finset.sum_eq_single q]
    · simp
    · intro j _ hj; simp [hj]
    · simp
  have h3 : (M *ᵥ (Pi.single q 1 : ι → ℂ)) p = M p q := by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [h2, mul_one] at h1
  have h4 : w p ^ 2 * ‖M p q‖ ^ 2 ≤ ∑ p', w p' ^ 2 * ‖(M *ᵥ (Pi.single q 1 : ι → ℂ)) p'‖ ^ 2 := by
    calc w p ^ 2 * ‖M p q‖ ^ 2 = w p ^ 2 * ‖(M *ᵥ (Pi.single q 1 : ι → ℂ)) p‖ ^ 2 := by rw [h3]
      _ ≤ _ := Finset.single_le_sum (f := fun p' => w p' ^ 2 * ‖(M *ᵥ (Pi.single q 1 : ι → ℂ)) p'‖ ^ 2)
          (fun i _ => by positivity) (Finset.mem_univ p)
  have h5 : (w p * ‖M p q‖) ^ 2 ≤ B ^ 2 := by rw [mul_pow]; exact h4.trans h1
  exact (abs_le_of_sq_le_sq' h5 hB).2

section FinalCover

variable {Cx : ℝ} (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) {D : ℝ} (hD : 0 ≤ D)
  {b b' : unitPts G}
  (hb : ∀ y, unitBlock y = b.1 → ENNReal.ofReal D ≤ siteSetDist G W y) (i i' : Fin N)
include hfam hφ hδ hsm hW hD hb

/-- **Theorem I-4c (vi), closeness of `C^{1/2}`, for the data `Dec2.XData` of the pair
`(coverOf G, G)`** (no `DGSetting`): if every cube with `s_z ≠ 1` has its interaction cube inside
`W` and the block of the unit point `b` is at distance `≥ D` from `W` in the scaled path metric,
then every matrix element of `C^{1/2}(s) - C^{1/2}(1)` at `b` is at most `B e^{-γ_w D}`,
`γ_w = xAgmonRate d L`, `B = covWSqrt …`. -/
theorem I4c_close_sqrt_entry_cover :
    ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) -
        decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ ≤
      covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) * Real.exp (-(xAgmonRate d L * D)) := by
  have hU := (isUnitLatticeB_unit G).toIsUnitLattice
  have D0 := hfam 0 le_rfl
  have hsm1 : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left (smallConstX_mono d L D0.κ0) (sq_nonneg δ)) hsm
  have hε0 : 0 ≤ xAgmonRate d L := (xAgmonRate_pos (by have := D0.st.hd; omega) D0.st.hL).le
  have hε1 : xAgmonRate d L ≤ xAgmonRate d L := le_rfl
  have hc₀ : (0 : ℝ) ≤ 2 * d := by positivity
  have hsum := sum_w_sqrt_sub_le_cover hfam (fun x hx => (hfam x hx).toOne) hφ hδ hsm hsm1 hU hW D
    hε0 hε1 (fun b y => unitQ_nonneg_real b y) (fun b b' => unitP_nonneg_real b b') hc₀
    (ρ := fun b : unitPts G => unitRho (truncSetDistR G W D) b.1)
    (fun b y h => unitRho_Q_compat W D b y h) (fun b b' h => unitRho_P_compat W D b b' h)
  have hB : 0 ≤ covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) := by
    unfold covWSqrt; have := covCloseSq_nonneg d L (a k) κ (xAgmonRate d L) (2 * d)
    have := aux_hak_cover hfam; positivity
  have hent := entry_le_of_sum_w (decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) -
      decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G))
    (fun p : unitPts G × Fin N => Real.exp (xAgmonRate d L * unitRho (truncSetDistR G W D) p.1.1))
    hB hsum (b, i) (b', i')
  have hρ := unitRho_ge hD hb
  have hexp : Real.exp (xAgmonRate d L * D) ≤
      Real.exp (xAgmonRate d L * unitRho (truncSetDistR G W D) b.1) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hρ hε0)
  have hpos : 0 < Real.exp (xAgmonRate d L * D) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc _ ≤ ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) -
        decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ *
        Real.exp (xAgmonRate d L * unitRho (truncSetDistR G W D) b.1) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ ≤ _ := by rw [mul_comm]; exact hent

end FinalCover

section FinalThms

theorem standing_pair (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s) (hφ : IsConstraintField G δ φ)
    (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    CovStanding G a aT ν α κ s δ φ (unitQ G) (unitP G) ∧
      CovStanding G a aT ν α 0 (fun _ => 1) δ φ (unitQ G) (unitP G) := by
  have hU := (isUnitLatticeB_unit G).toIsUnitLattice
  have hsm1 : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_left (smallConstX_mono d L (hfam 0 le_rfl).κ0)
      (sq_nonneg δ)) hsm
  exact ⟨⟨hfam, hφ, hδ, hsm, hU⟩, ⟨fun x hx => (hfam x hx).toOne, hφ, hδ, hsm1, hU⟩⟩

theorem xAgmonRate_nonneg_of_fam (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s) :
    0 ≤ xAgmonRate d L := by
  have D0 := hfam 0 le_rfl
  exact (xAgmonRate_pos (by have := D0.st.dg.hd; omega) D0.st.dg.hL).le

variable (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ s) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {W : Finset (CTorus d L N₁ m₁ (k + 1))}
  (hW : ∀ z ∈ cubeIdx G, sProd G s z ≠ 1 → intBox z ⊆ W) {D : ℝ} (hD : 0 ≤ D)
  {b b' : unitPts G}
  (hb : ∀ y, unitBlock y = b.1 → ENNReal.ofReal D ≤ siteSetDist G W y) (i i' : Fin N)
include hfam hφ hδ hsm hW hD hb

/-- **Theorem I-4c (vi), closeness of `C^{1/2}`.** If every cube with `s_z ≠ 1` has its interaction
cube inside `W` and the block of the unit point `b` is at distance `≥ D` from `W` in the scaled path
metric, then every matrix element of `C^{1/2}(s) - C^{1/2}(1)` at `b` is at most
`B e^{-γ_w D}`, `γ_w = xAgmonRate d L`, `B = covWSqrt …` (of the form `B₅ e^{N₀ κ}`). -/
theorem I4c_close_sqrt_entry :
    ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) -
        decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ ≤
      covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) * Real.exp (-(xAgmonRate d L * D)) :=
  I4c_close_sqrt_entry_cover (fun x hx => (hfam x hx).toCover) hφ hδ hsm hW hD hb i i'

/-- **Theorem I-4c (vi), closeness of `𝕃`.** -/
theorem I4c_close_log_entry :
    ‖(decLog G a aT ν α s φ (unitQ G) (unitP G) -
        decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ ≤
      covWLog d L (a k) κ (xAgmonRate d L) (2 * d) * Real.exp (-(xAgmonRate d L * D)) := by
  obtain ⟨H, H1⟩ := standing_pair hfam hφ hδ hsm
  have hε0 := xAgmonRate_nonneg_of_fam hfam
  have hε1 : xAgmonRate d L ≤ xAgmonRate d L := le_rfl
  have hc₀ : (0 : ℝ) ≤ 2 * d := by positivity
  have hsum := sum_w_log_sub_le H H1 hW D hε0 hε1 (fun b y => unitQ_nonneg_real b y)
    (fun b b' => unitP_nonneg_real b b') hc₀
    (ρ := fun b : unitPts G => unitRho (truncSetDistR G W D) b.1)
    (fun b y h => unitRho_Q_compat W D b y h) (fun b b' h => unitRho_P_compat W D b b' h)
  have hB : 0 ≤ covWLog d L (a k) κ (xAgmonRate d L) (2 * d) := by
    unfold covWLog; have := covCloseSq_nonneg d L (a k) κ (xAgmonRate d L) (2 * d)
    have := H.hak; positivity
  have hent := entry_le_of_sum_w (decLog G a aT ν α s φ (unitQ G) (unitP G) -
      decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G))
    (fun p : unitPts G × Fin N => Real.exp (xAgmonRate d L * unitRho (truncSetDistR G W D) p.1.1))
    hB hsum (b, i) (b', i')
  have hρ := unitRho_ge hD hb
  have hexp : Real.exp (xAgmonRate d L * D) ≤
      Real.exp (xAgmonRate d L * unitRho (truncSetDistR G W D) b.1) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hρ hε0)
  have hpos : 0 < Real.exp (xAgmonRate d L * D) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos]
  calc _ ≤ ‖(decLog G a aT ν α s φ (unitQ G) (unitP G) -
        decLog G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ *
        Real.exp (xAgmonRate d L * unitRho (truncSetDistR G W D) b.1) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
    _ ≤ _ := by rw [mul_comm]; exact hent

end FinalThms

section X0Cover

variable {Cx : ℝ} {s' : DecParams G}
  (hfam : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ (extS G s') Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {X₀ X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {r₀ : ℝ}
  (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx G), P ∉ parCubes G X₁ →
    s' ⟨P, hP⟩ = 1)
  (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
  (hdist : ∀ y ∈ X₀, y ∈ G.Ω 1 →
    ENNReal.ofReal ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L) ≤ siteSetDist G (Wpar G X₁) y)
  {b b' : unitPts G} (hX : ∀ y, unitBlock y = b.1 → y ∈ X₀) (i i' : Fin N)
include hfam hφ hδ hsm hs1 hr₀ hdist hX

/-- **Theorem I-4c (vi) on `X₀` from the distance of `X₀` to `𝒲`**, for the data `Dec2.XData` of the
pair `(coverOf G, G)`: for the parameters equal to `1` off the parameter cubes, if every site of
`X₀ ∩ Ω₁` is at scaled distance `≥ T = ((r₀ - 4 d L³)/L) M₁` from `𝒲 = Wpar G X₁`, the matrix
elements of `C^{1/2}(s) - C^{1/2}(1)` at the unit points of `X₀` are at most `B e^{-γ_w T}`.  The
common step of `I4c_close_sqrt_X0` (`DGSetting`) and `I4c_close_sqrt_X0_sup` (a sup-separated
cover). -/
theorem I4c_close_sqrt_X0_of_dist :
    ‖(decCovSqrt G a aT ν α (extS G s') φ (unitQ G) (unitP G) -
        decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ ≤
      covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) *
        Real.exp (-(xAgmonRate d L * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
  have hL1 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hD : 0 ≤ (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L := by
    have : 0 ≤ r₀ - 4 * d * (L : ℝ) ^ 3 := by linarith
    positivity
  refine I4c_close_sqrt_entry_cover hfam hφ hδ hsm (hW_of_par hs1) hD (b := b) (b' := b') ?_ i i'
  intro y hy
  have hyl : y ∈ G.layer (k + 1) := (unitBlock_mem_iff G y).1 (hy ▸ b.2)
  exact hdist y (hX y hy) (G.layer_subset (by omega) le_rfl hyl)

end X0Cover

section X0

variable {s' : DecParams G} (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α κ (extS G s') ) (hφ : IsConstraintField G δ φ)
  (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  {X₀ X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {r₀ : ℝ}
  (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx G), P ∉ parCubes G X₁ →
    s' ⟨P, hP⟩ = 1)
  (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ (k + 1),
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
  (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
  {b b' : unitPts G} (hX : ∀ y, unitBlock y = b.1 → y ∈ X₀) (i i' : Fin N)
include hfam hφ hδ hsm hs1 hN hr hr₀ hX

/-- **Theorem I-4c (vi) on `X₀`** (`r₁ M₁ = (r₀ - 4 d L³) L^{m₁} / L`, as in `i4a_close_X0`):
for the parameters equal to `1` off the parameter cubes, the matrix elements of
`C^{1/2}(s) - C^{1/2}(1)` at the unit points of `X₀` are at most `B e^{-γ_w r₁ M₁}`. -/
theorem I4c_close_sqrt_X0 :
    ‖(decCovSqrt G a aT ν α (extS G s') φ (unitQ G) (unitP G) -
        decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G)) (b, i) (b', i')‖ ≤
      covWSqrt d L (a k) κ (xAgmonRate d L) (2 * d) *
        Real.exp (-(xAgmonRate d L * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) :=
  I4c_close_sqrt_X0_of_dist (fun x hx => (hfam x hx).toCover) hφ hδ hsm hs1 hr₀
    (fun _ hy hyΩ => siteSetDist_X0 (hfam 0 le_rfl).st.dg hN hr hy hyΩ) hX i i'

end X0

end Final

end Weighted

end Balaban.Localization
