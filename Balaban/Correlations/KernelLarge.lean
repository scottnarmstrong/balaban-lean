module

public import Balaban.Correlations.KernelHypProof
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Gaussian kernels at unit-lattice masses up to `ν_max` (interface I-G at the top scales)

`kernelHyp_holds` (landed) covers `μ L^{2(j+1)} ≤ 1`.  Here the mass range is extended to
`μ L^{2(j+1)} ≤ ν_max`, for any `ν_max ≥ 0`, with the same kernel family `tLim` that
`kernelHyp_holds` uses.

* `tLim_decay_le`: `|t_j^μ(x, y)| ≤ C_G L^{-j(d-2)} e^{-δ_G |x - y| / L^j}` for
  `μ L^{2(j+1)} ≤ ν_max`, with `C_G, δ_G` depending on `d, L, a, ν_max` only.
* `tendsto_termKernel_nested`: the torus kernels `T_j^{ℓ,μ}` of the `J`-step decomposition, `J > j`,
  converge to `tLim d L a μ j x y` for every `μ > 0` (no mass restriction is needed for the limit).
* `kernelHypLarge_holds`: both facts together (this is what the `KernelHypLarge` structure of
  `Balaban.Correlations.MainTerm` asks for), and `kernelHypLarge_holds_two_L4` for
  `ν_max = 2 L⁴`.

The ingredients generalized in place (old statements kept as the case of mass cap `1`):
`Balaban.Green.coarseGreen_decay_of_nonneg` (no mass restriction at all),
`Balaban.Multiscale.prop48` / `lemmaP` (mass cap `Λ`), `Balaban.Green.oneScale_pointwise_le`,
`Balaban.Green.fineGreen_decay_le`, `Balaban.gent_decay_le`, `Balaban.term_bound_succ_le`,
`Balaban.tLim_decay_succ_le`, `Balaban.tLim_decay_zero_le`.
-/

@[expose] public section

namespace Balaban

open Filter Topology Balaban.Green

variable {d L : ℕ} [NeZero L]

/-- **(G2) for `t_j^μ` at masses `μ L^{2(j+1)} ≤ ν_max`.** -/
theorem tLim_decay_le (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (νmax : ℝ) (hνmax : 0 ≤ νmax) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ (j : ℕ) {μ : ℝ}, 0 < μ → μ * (L : ℝ) ^ (2 * (j + 1)) ≤ νmax →
      ∀ x y : Fin d → ℤ, |tLim d L a μ j x y| ≤
        C * ((L : ℝ) ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ * ‖x - y‖ / (L : ℝ) ^ j)) := by
  have hL1 : 1 < L := by omega
  have hx : (1 : ℝ) < L := by exact_mod_cast hL1
  obtain ⟨C₀, δ₀, hC₀, hδ₀, h₀⟩ := tLim_decay_zero_le νmax hνmax hd hL1 hlo hhi
  obtain ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ := tLim_decay_succ_le νmax hνmax hd hL hlo hhi
  refine ⟨max C₀ C₁, min δ₀ δ₁, hC₀.trans (le_max_left _ _), lt_min hδ₀ hδ₁, ?_⟩
  intro j μ hμ hμ1 x y
  have hLpj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hnorm : 0 ≤ ‖x - y‖ := norm_nonneg _
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h2 : μ * (L : ℝ) ^ 2 ≤ νmax := by simpa using hμ1
    refine (h₀ hμ h2 x y).trans ?_
    simp only [zero_mul, pow_zero, inv_one, mul_one, div_one]
    exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 (by nlinarith [min_le_left δ₀ δ₁]))
      (Real.exp_pos _).le (by positivity)
  · have hmj : μ * ((L : ℝ) ^ j) ^ 2 ≤ νmax := by
      refine le_trans (mul_le_mul_of_nonneg_left ?_ hμ.le) hμ1
      rw [← pow_mul, mul_comm j 2]
      exact pow_le_pow_right₀ hx.le (by omega)
    refine (h₁ hμ hj hmj x y).trans ?_
    have hinv : 0 ≤ ((L : ℝ) ^ (j * (d - 2)))⁻¹ := by positivity
    have e1 : Real.exp (-(δ₁ * ‖x - y‖ / (L : ℝ) ^ j)) ≤
        Real.exp (-(min δ₀ δ₁ * ‖x - y‖ / (L : ℝ) ^ j)) := by
      apply Real.exp_le_exp.2
      have : min δ₀ δ₁ * ‖x - y‖ / (L : ℝ) ^ j ≤ δ₁ * ‖x - y‖ / (L : ℝ) ^ j := by
        apply div_le_div_of_nonneg_right _ hLpj.le
        exact mul_le_mul_of_nonneg_right (min_le_right _ _) hnorm
      linarith
    exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hinv) e1
      (Real.exp_pos _).le (by positivity)

/-- The torus kernels of the `J`-step decomposition converge to `t_j^μ` for `J > j`, for every
mass `μ > 0`. -/
theorem tendsto_termKernel_nested (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) {J j : ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hj : j < J) (x y : Fin d → ℤ) :
    Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ J j m x y) atTop
      (𝓝 (tLim d L a μ j x y)) := by
  have hL1 : 1 < L := by omega
  have ha : 0 < a := by linarith [half_le_of_lo hL1 hlo]
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 + j := ⟨J - j - 1, by omega⟩
  have hpos : 1 ≤ L ^ n := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hm' : ∀ m : ℕ, (L ^ n * (m + 1) - 1) + 1 = L ^ n * (m + 1) := fun m => by
    have : 1 ≤ L ^ n * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hle : ∀ m : ℕ, m ≤ L ^ n * (m + 1) - 1 := fun m => by
    have : m + 1 ≤ L ^ n * (m + 1) := Nat.le_mul_of_pos_left _ hpos
    omega
  have hcomp := (tendsto_tLim hd hL1 hlo hhi hμ j x y).comp
    (tendsto_atTop_mono hle tendsto_id)
  refine hcomp.congr fun m => ?_
  simp only [Function.comp]
  exact (termKernel_nested hμ (fun i => freeSeq_pos ha i) n j m _ (hm' m) x y).symm

/-- **The Gaussian kernel facts at unit-lattice masses up to `ν_max`** (G1 on the nested tori and G2
for the limit kernels `tLim`, the family of `kernelHyp_holds`). -/
theorem kernelHypLarge_holds (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) (νmax : ℝ) (hνmax : 0 ≤ νmax) :
    ∃ C_G δ_G : ℝ, 0 ≤ C_G ∧ 0 < δ_G ∧
      (∀ (J j : ℕ) (μ : ℝ), j < J → 0 < μ → ∀ x y : Fin d → ℤ,
        Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ J j m x y) atTop
          (𝓝 (tLim d L a μ j x y))) ∧
      (∀ (j : ℕ) (μ : ℝ), 0 < μ → μ * (L : ℝ) ^ (2 * (j + 1)) ≤ νmax → ∀ x y : Fin d → ℤ,
        |tLim d L a μ j x y| ≤
          C_G * ((L : ℝ) ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ_G * ‖x - y‖ / (L : ℝ) ^ j))) := by
  obtain ⟨C, δ, hC, hδ, h⟩ := tLim_decay_le hd hL hlo hhi νmax hνmax
  exact ⟨C, δ, hC, hδ, fun J j μ hj hμ x y => tendsto_termKernel_nested hd hL hlo hhi hμ hj x y,
    fun j μ hμ hμ1 x y => h j hμ hμ1 x y⟩

/-- The corollary in the form used by Root-C: `ν_max = 2 L⁴`. -/
theorem kernelHypLarge_holds_two_L4 (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ C_G δ_G : ℝ, 0 ≤ C_G ∧ 0 < δ_G ∧
      (∀ (J j : ℕ) (μ : ℝ), j < J → 0 < μ → ∀ x y : Fin d → ℤ,
        Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ J j m x y) atTop
          (𝓝 (tLim d L a μ j x y))) ∧
      (∀ (j : ℕ) (μ : ℝ), 0 < μ → μ * (L : ℝ) ^ (2 * (j + 1)) ≤ 2 * (L : ℝ) ^ 4 →
        ∀ x y : Fin d → ℤ, |tLim d L a μ j x y| ≤
          C_G * ((L : ℝ) ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ_G * ‖x - y‖ / (L : ℝ) ^ j))) :=
  kernelHypLarge_holds hd hL hlo hhi (2 * (L : ℝ) ^ 4) (by positivity)

omit [NeZero L] in
/-- The mass range of Root-C: for `ν ∈ (0, 1]`, `j < J` with `L^J √ν ≤ L²` (written
`ν (L^J)² ≤ L⁴`) and `μ ∈ (0, 2ν]`, the unit-lattice mass satisfies `μ L^{2(j+1)} ≤ 2 L⁴`. -/
theorem mass_range_le_two_L4 {ν μ : ℝ} {J j : ℕ} (hL : 1 ≤ L) (hj : j < J) (hμ : μ ≤ 2 * ν)
    (hν0 : 0 ≤ ν) (hνJ : ν * ((L : ℝ) ^ J) ^ 2 ≤ (L : ℝ) ^ 4) :
    μ * (L : ℝ) ^ (2 * (j + 1)) ≤ 2 * (L : ℝ) ^ 4 := by
  have hx : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (L : ℝ) ^ (2 * (j + 1)) ≤ ((L : ℝ) ^ J) ^ 2 := by
    rw [← pow_mul, mul_comm J 2]
    exact pow_le_pow_right₀ hx (by omega)
  calc μ * (L : ℝ) ^ (2 * (j + 1)) ≤ (2 * ν) * ((L : ℝ) ^ J) ^ 2 :=
        mul_le_mul hμ h1 (by positivity) (by positivity)
    _ = 2 * (ν * ((L : ℝ) ^ J) ^ 2) := by ring
    _ ≤ _ := by linarith

end Balaban
