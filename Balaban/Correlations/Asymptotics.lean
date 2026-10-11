module

public import Balaban.Flow.RunningCoefficients
public import Balaban.Correlations.Series
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Goldstone asymptotics: the (4.18) step

CORRELATIONS.md §3.5 (P9 (4.16)-(4.18)). Let `K_j(x, y)` be the real kernel attached to the
scale `j` in the normalisation of `Balaban.Gaussian.Multiscale` (the plain unit `T_j`; the
coefficient of `T_j` in the transverse two-point function is `(β γ_j)⁻¹ = β_j⁻¹ L^{j(d-2)}`, see
`betaSeq_eq`). The decay bound (G2) of §2.1 is taken as the hypothesis `KernelDecay`:
`|T_j(x, y)| ≤ C_G L^{-j(d-2)} exp(-δ_G L^{-j} |x - y|)`.

`goldstone_rewriting` : with `γ_∞ = lim γ_j` from `exists_inv_betaSeq_asymptotics`,
`∑_j β_j⁻¹ L^{j(d-2)} T_j(x, y) = (β γ_∞)⁻¹ ∑_j T_j(x, y) + 𝓔(x, y)` with
`|𝓔(x, y)| ≤ C ‖β⁻¹‖ (1 + |x - y|)^{-(d-2+2γ)}`, where `q = L^{-2γ}` is the rate of the
running coefficients.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban

open Flow

/-- The kernel decay (G2) of CORRELATIONS.md §2.1 at one pair of points at distance `r`:
`|T_j| ≤ C L^{-j(d-2)} exp(-δ r / L^j)`. -/
def KernelDecay (d : ℕ) (L : ℝ) (C δ r : ℝ) (t : ℕ → ℝ) : Prop :=
  ∀ j, |t j| ≤ C * (L ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ * r / L ^ j))

/-- Coefficient comparison: `‖β_j⁻¹ L^{j(d-2)} - (β γ)⁻¹‖ ≤ K ‖β⁻¹‖ q^j`. -/
theorem norm_inv_betaSeq_mul_sub_le {L : ℝ} (hL : 0 < L) (d : ℕ) {γ : ℂ} {β : ℂ} {q K : ℝ}
    {ξ : ℕ → Fin 3 → ℂ} (j : ℕ)
    (h : ‖(betaSeq L d ξ β j)⁻¹ - (β * γ)⁻¹ * ((L : ℂ) ^ (j * (d - 2)))⁻¹‖ ≤
      K * ‖β⁻¹‖ * ((L ^ (j * (d - 2)))⁻¹ * q ^ j)) :
    ‖(betaSeq L d ξ β j)⁻¹ * (L : ℂ) ^ (j * (d - 2)) - (β * γ)⁻¹‖ ≤ K * ‖β⁻¹‖ * q ^ j := by
  have hLp : (L : ℂ) ^ (j * (d - 2)) ≠ 0 := pow_ne_zero _ (by exact_mod_cast hL.ne')
  have hn : ‖(L : ℂ) ^ (j * (d - 2))‖ = L ^ (j * (d - 2)) := by
    rw [norm_pow, Complex.norm_of_nonneg hL.le]
  have e : (betaSeq L d ξ β j)⁻¹ * (L : ℂ) ^ (j * (d - 2)) - (β * γ)⁻¹ =
      ((betaSeq L d ξ β j)⁻¹ - (β * γ)⁻¹ * ((L : ℂ) ^ (j * (d - 2)))⁻¹) *
        (L : ℂ) ^ (j * (d - 2)) := by
    rw [sub_mul, mul_assoc, inv_mul_cancel₀ hLp, mul_one]
  rw [e, norm_mul, hn]
  have hpos : 0 < L ^ (j * (d - 2)) := by positivity
  calc _ ≤ K * ‖β⁻¹‖ * ((L ^ (j * (d - 2)))⁻¹ * q ^ j) * L ^ (j * (d - 2)) :=
        mul_le_mul_of_nonneg_right h hpos.le
    _ = K * ‖β⁻¹‖ * q ^ j := by field_simp

/-- **The (4.18) step** (CORRELATIONS.md §3.5). Let `ξ` satisfy the running-coefficient hypothesis
`‖ξ_k‖ ≤ (c₈/4) q^{k+1}`, `q = L^{-2γ₀}`, and let `γ = γ_∞ = lim γ_j`. For every sequence of
real kernel values `t_j` (the `T_j(x, y)` of the sum rule, in plain units) satisfying the decay
(G2) at distance `r = |x - y|`,
`∑_j β_j⁻¹ L^{j(d-2)} t_j = (β γ)⁻¹ ∑_j t_j + 𝓔` with
`‖𝓔‖ ≤ e² (c₈ q / (2 (1 - q))) ‖β⁻¹‖ C C' (1 + r)^{-(d-2+2γ₀)}`, where `C'` depends only on
`d, L, γ₀, δ`. Both series converge absolutely. -/
theorem goldstone_rewriting {L : ℝ} (hL : 1 < L) (d : ℕ) (hd : 3 ≤ d) {γ₀ δ c₈ : ℝ}
    (hγ₀ : 0 < γ₀) (hδ : 0 < δ) (hc : 0 ≤ c₈) {ξ : ℕ → Fin 3 → ℂ}
    (hs : c₈ * rate L γ₀ ≤ 1 - rate L γ₀)
    (hξ : ∀ k, ‖ξ k‖ ≤ c₈ / 4 * rate L γ₀ ^ (k + 1)) :
    ∃ γ : ℂ, Tendsto (gammaSeq ξ) atTop (𝓝 γ) ∧
      ‖γ - 1‖ ≤ c₈ * rate L γ₀ / (2 * (1 - rate L γ₀)) ∧
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (β : ℂ) (C r : ℝ) (t : ℕ → ℝ), 0 ≤ C → 0 ≤ r →
        KernelDecay d L C δ r t →
        Summable (fun j => (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ))) ∧
        ‖∑' j, (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
            (β * γ)⁻¹ * ∑' j, (t j : ℂ)‖ ≤
          Real.exp 2 * (c₈ * rate L γ₀ / (2 * (1 - rate L γ₀))) * ‖β⁻¹‖ * C * C' *
            (1 + r) ^ (-(((d - 2 : ℕ) : ℝ) + 2 * γ₀)) := by
  have hL0 : 0 < L := by linarith
  have hq0 : 0 ≤ rate L γ₀ := (rate_pos hL0 γ₀).le
  have hq1 : rate L γ₀ < 1 := rate_lt_one hL hγ₀
  obtain ⟨γ, hT, hγ1, hasym⟩ :=
    exists_inv_betaSeq_asymptotics hL0 d hq0 hq1 hc hs hξ
  have hσ : 0 < ((d - 2 : ℕ) : ℝ) + 2 * γ₀ := by positivity
  obtain ⟨C', hC'0, hC'⟩ := Correlations.sum_pow_exp_le hσ hδ hL
  refine ⟨γ, hT, hγ1, C', hC'0, ?_⟩
  intro β C r t hC hr ht
  set q := rate L γ₀ with hqdef
  set K : ℝ := Real.exp 2 * (c₈ * q / (2 * (1 - q))) with hK
  set σ : ℝ := ((d - 2 : ℕ) : ℝ) + 2 * γ₀ with hσdef
  have hK0 : 0 ≤ K := by
    have : 0 < 1 - q := by linarith
    rw [hK]; positivity
  -- the comparison terms
  set h : ℕ → ℝ := fun j => L ^ (-((j : ℝ) * σ)) * Real.exp (-(δ * r / L ^ j)) with hh
  have hh0 : ∀ j, 0 ≤ h j := fun j => by positivity
  set f : ℕ → ℝ := fun j => K * ‖β⁻¹‖ * C * h j with hf
  have hhsum : ∀ J, ∑ j ∈ range J, h j ≤ C' * (1 + r) ^ (-σ) := fun J => hC' J r hr
  have hhS : Summable h := summable_of_sum_range_le hh0 hhsum
  have hhtsum : ∑' j, h j ≤ C' * (1 + r) ^ (-σ) :=
    Real.tsum_le_of_sum_range_le hh0 hhsum
  have hfS : Summable f := hhS.mul_left _
  -- term bound
  have hterm : ∀ j, ‖(betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
      (β * γ)⁻¹ * (t j : ℂ)‖ ≤ f j := by
    intro j
    have hco := norm_inv_betaSeq_mul_sub_le hL0 d (γ := γ) (β := β) (q := q) (K := K) (ξ := ξ) j
      (by simpa only [hK, hqdef, mul_assoc] using hasym β j)
    have e : (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
        (β * γ)⁻¹ * (t j : ℂ) =
        ((betaSeq L d ξ β j)⁻¹ * (L : ℂ) ^ (j * (d - 2)) - (β * γ)⁻¹) * (t j : ℂ) := by ring
    rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hinv := inv_pow_mul_rate_pow hL0 γ₀ d j
    have h2 : K * ‖β⁻¹‖ * q ^ j * (C * (L ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ * r / L ^ j))) =
        f j := by
      simp only [hf, hh]
      rw [← hσdef] at hinv
      rw [← hinv, hqdef]
      ring
    rw [← h2]
    exact mul_le_mul hco (ht j) (abs_nonneg _) (by positivity)
  -- summability of the kernel series
  have htS : Summable (fun j => (t j : ℂ)) := by
    have hgeo : Summable (fun j : ℕ => C * (((L ^ (d - 2))⁻¹) ^ j)) := by
      refine Summable.mul_left _ (summable_geometric_of_lt_one (by positivity) ?_)
      exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ hL (by omega))
    refine Summable.of_norm_bounded hgeo fun j => ?_
    rw [Complex.norm_real, Real.norm_eq_abs]
    refine (ht j).trans ?_
    have hex : Real.exp (-(δ * r / L ^ j)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ δ * r / L ^ j := by positivity
      linarith
    have hx : (L ^ (j * (d - 2)))⁻¹ = ((L ^ (d - 2))⁻¹) ^ j := by
      rw [inv_pow, ← pow_mul, mul_comm]
    rw [hx]
    calc _ ≤ C * ((L ^ (d - 2))⁻¹) ^ j * 1 := by
          apply mul_le_mul_of_nonneg_left hex (by positivity)
      _ = _ := by ring
  have hdiffS : Summable (fun j => (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
      (β * γ)⁻¹ * (t j : ℂ)) := Summable.of_norm_bounded hfS hterm
  have huS : Summable (fun j => (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ))) := by
    have := hdiffS.add (htS.mul_left ((β * γ)⁻¹))
    simpa using this
  refine ⟨huS, ?_⟩
  have hsub : ∑' j, (betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
      (β * γ)⁻¹ * ∑' j, (t j : ℂ) =
      ∑' j, ((betaSeq L d ξ β j)⁻¹ * ((L : ℂ) ^ (j * (d - 2)) * (t j : ℂ)) -
        (β * γ)⁻¹ * (t j : ℂ)) := by
    rw [Summable.tsum_sub huS (htS.mul_left _), Summable.tsum_mul_left _ htS]
  rw [hsub]
  refine (tsum_of_norm_bounded hfS.hasSum hterm).trans ?_
  rw [hf]
  simp only
  rw [tsum_mul_left]
  calc K * ‖β⁻¹‖ * C * ∑' j, h j ≤ K * ‖β⁻¹‖ * C * (C' * (1 + r) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left hhtsum (by positivity)
    _ = _ := by rw [hσdef]; ring

/-- The summed kernel decay: if `|t_j| ≤ C L^{-j(d-2)} exp(-δ r / L^j)` for all `j`, then `∑ t_j`
converges absolutely and `|∑_j t_j| ≤ C C' (1 + r)^{-(d-2)}` (CORRELATIONS.md Lemma 1.3 with
`σ = d - 2`). -/
theorem KernelDecay.tsum_abs_le {L : ℝ} (hL : 1 < L) (d : ℕ) (hd : 3 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (C r : ℝ) (t : ℕ → ℝ), 0 ≤ C → 0 ≤ r → KernelDecay d L C δ r t →
      Summable t ∧ |∑' j, t j| ≤ C * C' / (1 + r) ^ (d - 2) := by
  have hL0 : 0 < L := by linarith
  have hσ : 0 < ((d - 2 : ℕ) : ℝ) := by
    have : 1 ≤ d - 2 := by omega
    exact_mod_cast this
  obtain ⟨C', hC'0, hC'⟩ := Correlations.sum_pow_exp_le hσ hδ hL
  refine ⟨C', hC'0, fun C r t hC hr ht => ?_⟩
  set σ : ℝ := ((d - 2 : ℕ) : ℝ) with hσdef
  set h : ℕ → ℝ := fun j => L ^ (-((j : ℝ) * σ)) * Real.exp (-(δ * r / L ^ j)) with hh
  have hh0 : ∀ j, 0 ≤ h j := fun j => by positivity
  have hhsum : ∀ J, ∑ j ∈ range J, h j ≤ C' * (1 + r) ^ (-σ) := fun J =>
    hC' J r hr
  have hhS : Summable h := summable_of_sum_range_le hh0 hhsum
  have hhtsum : ∑' j, h j ≤ C' * (1 + r) ^ (-σ) := Real.tsum_le_of_sum_range_le hh0 hhsum
  have hbd : ∀ j, ‖t j‖ ≤ C * h j := by
    intro j
    rw [Real.norm_eq_abs]
    refine (ht j).trans (le_of_eq ?_)
    have : (L ^ (j * (d - 2)))⁻¹ = L ^ (-((j : ℝ) * σ)) := by
      rw [Real.rpow_neg hL0.le, ← Real.rpow_natCast]
      push_cast
      rfl
    rw [hh]
    simp only
    rw [← this]
    ring
  have htS : Summable t := Summable.of_norm_bounded (hhS.mul_left C) hbd
  refine ⟨htS, ?_⟩
  have h1 : |∑' j, t j| ≤ C * ∑' j, h j := by
    have := tsum_of_norm_bounded (hhS.mul_left C).hasSum hbd
    rw [tsum_mul_left] at this
    simpa [Real.norm_eq_abs] using this
  refine h1.trans ?_
  calc C * ∑' j, h j ≤ C * (C' * (1 + r) ^ (-σ)) := mul_le_mul_of_nonneg_left hhtsum hC
    _ = C * C' / (1 + r) ^ (d - 2) := by
        rw [Real.rpow_neg (by positivity), hσdef, Real.rpow_natCast]
        ring

end Balaban
