module

public import Balaban.LargeField.R.RRemovedShellTree
public import Balaban.LargeField.R.RhoZero
public import Balaban.LargeField.R.PsiZeroSpace
public import Balaban.LargeField.Operators.PiTools
public import Balaban.LargeField.R.RRipeCard
public import Balaban.LargeField.Budget.Exponents

/-!
# Volume factors per block (Lemma III.8.7, step (3))

The arithmetic of the per-block factors: `v_N (3δ_k)^N (w/π)^{N/2}` (`w = β_k a_z ≤ 2β_k`) and
`v_N (C₆ β_k^{-1/2} p₀)^N e^{(N/2) log β_k}` are at most `e^{N p₀ log λ_k + C_vol}` with
`C_vol = log (v_N max{3, C₆}^N A₀^N)` when `δ_k = β_k^{-1/2} p₀(β_k)` and `p₀(β_k) = A₀ λ_k^{p₀}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory ENNReal

section Arith

variable {N : ℕ}

theorem unitBallVol_pos :
    0 < (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal :=
  ENNReal.toReal_pos (Metric.measure_ball_pos _ _ one_pos).ne' measure_ball_lt_top.ne

/-- `vol B(0, r) = v_N r^N` (as an `ofReal`). -/
theorem volume_ball_eq_ofReal (hN : 0 < N) {r : ℝ} (hr : 0 ≤ r) :
    volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) r) =
      ENNReal.ofReal ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * r ^ N) := by
  rw [volume_ball_eq hN, ENNReal.ofReal_mul (unitBallVol_pos (N := N)).le, ENNReal.ofReal_toReal
    measure_ball_lt_top.ne, ENNReal.ofReal_pow hr, mul_comm]

/-- `v_N (c p)^N ≤ e^{N p₀ log λ + log (v_N M^N A₀^N)}` for `0 ≤ c ≤ M`, `p = A₀ λ^{p₀}`. -/
theorem vol_const_le {c M A0 lam : ℝ} (pe : ℕ) (hc : 0 ≤ c) (hcM : c ≤ M)
    (hM : 0 < M) (hA0 : 0 < A0) (hlam : 0 < lam) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * (c * (A0 * lam ^ pe)) ^ N ≤
      Real.exp ((N : ℝ) * pe * Real.log lam +
        Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * M ^ N * A0 ^ N)) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal with hV
  have hV0 : 0 < V := unitBallVol_pos (N := N)
  have hX : 0 < V * M ^ N * A0 ^ N := by positivity
  rw [Real.exp_add, Real.exp_log hX]
  have h1 : Real.exp ((N : ℝ) * pe * Real.log lam) = lam ^ (N * pe) := by
    have : (N : ℝ) * pe * Real.log lam = ((N * pe : ℕ) : ℝ) * Real.log lam := by push_cast; ring
    rw [this, Real.exp_nat_mul, Real.exp_log hlam]
  rw [h1]
  have h2 : (c * (A0 * lam ^ pe)) ^ N = c ^ N * A0 ^ N * lam ^ (N * pe) := by
    rw [mul_pow, mul_pow, ← pow_mul, mul_comm pe N]; ring
  rw [h2]
  have h3 : c ^ N ≤ M ^ N := pow_le_pow_left₀ hc hcM N
  have h4 : 0 ≤ lam ^ (N * pe) := by positivity
  calc V * (c ^ N * A0 ^ N * lam ^ (N * pe)) = V * c ^ N * A0 ^ N * lam ^ (N * pe) := by ring
    _ ≤ V * M ^ N * A0 ^ N * lam ^ (N * pe) := by gcongr
    _ = _ := by ring

theorem sqrt_inv_eq {β : ℝ} (hβ : 0 < β) : β ^ (-(1 / 2 : ℝ)) = (Real.sqrt β)⁻¹ := by
  rw [Real.rpow_neg hβ.le, Real.sqrt_eq_rpow]

/-- **Per-block factor on `Z^c_0 ∩ Z`** (step (3)): with `δ = β^{-1/2} p₀v`, `p₀v = A₀ λ^{p₀}`,
`0 ≤ w ≤ 2β`: `v_N (3δ)^N (w/π)^{N/2} ≤ e^{N p₀ log λ + C_vol}`,
`C_vol = log (v_N max{3, C₆}^N A₀^N)`. -/
theorem tree_block_factor_le {β w δ A0 lam C6 : ℝ} (pe : ℕ) (hβ : 0 < β)
    (hw0 : 0 ≤ w) (hw : w ≤ 2 * β) (hδ : δ = β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe))
    (hA0 : 0 < A0) (hlam : 0 < lam) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal * (3 * δ) ^ N *
        (w / Real.pi) ^ ((N : ℝ) / 2) ≤
      Real.exp ((N : ℝ) * pe * Real.log lam +
        Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
          (max 3 C6) ^ N * A0 ^ N)) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal with hV
  have hV0 : 0 < V := unitBallVol_pos (N := N)
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have hwπ : w / Real.pi ≤ β := by
    rw [div_le_iff₀ Real.pi_pos]
    nlinarith [Real.pi_gt_three]
  have hq : (w / Real.pi) ^ ((N : ℝ) / 2) ≤ Real.sqrt β ^ N := by
    rw [← sqrt_pow_nat _ (div_nonneg hw0 Real.pi_pos.le)]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hwπ) N
  have hp : 0 ≤ A0 * lam ^ pe := by positivity
  have h3 : (3 * δ) ^ N * Real.sqrt β ^ N = (3 * (A0 * lam ^ pe)) ^ N := by
    rw [hδ, sqrt_inv_eq hβ, ← mul_pow]
    congr 1
    field_simp
  calc V * (3 * δ) ^ N * (w / Real.pi) ^ ((N : ℝ) / 2)
      ≤ V * (3 * δ) ^ N * Real.sqrt β ^ N := by
        gcongr
        rw [hδ]; positivity
    _ = V * (3 * (A0 * lam ^ pe)) ^ N := by rw [mul_assoc, h3]
    _ ≤ _ := vol_const_le pe (by norm_num) (le_max_left _ _) (lt_max_of_lt_left (by norm_num))
        hA0 hlam

/-- **Per-block factor on `Z_0`** (step (3)): the ball of radius `C₆ β^{-1/2} p₀v` against
`e^{(N/2) log β}` costs at most `e^{N p₀ log λ + C_vol}`. -/
theorem zero_block_factor_le {β A0 lam C6 : ℝ} (pe : ℕ) (hβ : 0 < β) (hC6 : 0 ≤ C6)
    (hA0 : 0 < A0) (hlam : 0 < lam) :
    (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
        (C6 * β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe)) ^ N * Real.exp ((N : ℝ) / 2 * Real.log β) ≤
      Real.exp ((N : ℝ) * pe * Real.log lam +
        Real.log ((volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal *
          (max 3 C6) ^ N * A0 ^ N)) := by
  set V := (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal with hV
  have hsb : 0 < Real.sqrt β := Real.sqrt_pos.mpr hβ
  have h1 : Real.exp ((N : ℝ) / 2 * Real.log β) = Real.sqrt β ^ N := by
    rw [sqrt_pow_nat _ hβ.le, Real.rpow_def_of_pos hβ]
    congr 1; ring
  have h2 : (C6 * β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe)) ^ N * Real.sqrt β ^ N =
      (C6 * (A0 * lam ^ pe)) ^ N := by
    rw [sqrt_inv_eq hβ, ← mul_pow]
    congr 1
    field_simp
  calc V * (C6 * β ^ (-(1 / 2 : ℝ)) * (A0 * lam ^ pe)) ^ N * Real.exp ((N : ℝ) / 2 * Real.log β)
      = V * (C6 * (A0 * lam ^ pe)) ^ N := by rw [h1, mul_assoc, h2]
    _ ≤ _ := vol_const_le pe hC6 (le_max_right _ _) (lt_max_of_lt_left (by norm_num)) hA0 hlam

end Arith

section ZeroBall

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- Reading the coordinates `u (z, ·)` of `u ∈ ℝ^{Zf × N}` block by block is measure preserving
onto the product over the blocks of the Lebesgue measure of `ℝ^N`. -/
theorem measurePreserving_suppSpace (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) :
    MeasurePreserving (fun (u : SuppSpace Zf N) (z : ↥Zf) (i : Fin N) => u (z, i))
      (volume : Measure (SuppSpace Zf N))
      (Measure.pi fun _ : ↥Zf => (volume : Measure (Fin N → ℝ))) := by
  have h0 := PiLp.volume_preserving_ofLp (↥Zf × Fin N)
  have h1 := PiTools.measurePreserving_reindex (Equiv.sigmaEquivProd ↥Zf (Fin N))
    (β := fun _ => ℝ) (γ := fun _ => ℝ) (fun _ => (volume : Measure ℝ)) (fun _ => volume)
    (fun _ v => v) (fun _ => MeasurePreserving.id _)
  have h2 := PiTools.measurePreserving_piCurry (ι := ↥Zf) (κ := fun _ => Fin N)
    (fun _ _ => ℝ) (fun _ _ => (volume : Measure ℝ))
  have h3 := h2.comp h1
  have h4 := h3.comp h0
  exact h4

/-- **The ball of `χ_{Z₀}`** (step (3), `ψ_k` on `Z_0`): the configurations of `ψ_k↾Z₀` with
`‖ψ_k(z) - ψ⁰_k(z)‖ < r` for all `z ∈ Z₀` have volume at most `vol B(0, r)^{|Z₀|}`. -/
theorem volume_zeroCutoff_le (hN : 0 < N) (Zf : Finset (Torus d (N₀ * L ^ (k - k))))
    (ψ0 : BlockField d L N₀ k N) (r : ℝ) :
    (volume : Measure (SuppSpace Zf N)) {u | ZeroCutoff ψ0 r u} ≤
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) r) ^ Zf.card := by
  have hset : ∀ c : Fin N → ℝ, {x : Fin N → ℝ | rn (fun i => x i - c i) < r} =
      (@WithLp.toLp 2 (Fin N → ℝ)) ⁻¹' Metric.ball (WithLp.toLp 2 c) r := by
    intro c
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Metric.mem_ball, dist_eq_norm,
      EuclideanSpace.norm_eq, rn]
    simp [Real.norm_eq_abs, sq_abs]
  have hmeas : ∀ c : Fin N → ℝ, MeasurableSet {x : Fin N → ℝ | rn (fun i => x i - c i) < r} := by
    intro c
    rw [hset]
    exact (PiLp.volume_preserving_toLp (Fin N)).measurable Metric.isOpen_ball.measurableSet
  have hpre : {u : SuppSpace Zf N | ZeroCutoff ψ0 r u} =
      (fun (u : SuppSpace Zf N) (z : ↥Zf) (i : Fin N) => u (z, i)) ⁻¹'
        Set.pi Set.univ (fun z : ↥Zf => {x : Fin N → ℝ | rn (fun i => x i - ψ0 z i) < r}) := by
    ext u
    simp [ZeroCutoff]
  rw [hpre, (measurePreserving_suppSpace (N := N) Zf).measure_preimage
    (MeasurableSet.univ_pi fun z => hmeas _).nullMeasurableSet, Measure.pi_pi]
  have hz : ∀ z : ↥Zf, volume {x : Fin N → ℝ | rn (fun i => x i - ψ0 z i) < r} =
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin N)) r) := by
    intro z
    rw [hset, (PiLp.volume_preserving_toLp (Fin N)).measure_preimage
      Metric.isOpen_ball.measurableSet.nullMeasurableSet, volume_ball_eq hN _ r,
      volume_ball_eq hN 0 r]
  simp [hz]

end ZeroBall

section Count

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- **The block count** (step (3), Lemma III.1.2 (d)): a removed component of `𝕋_k` has
`M^d` sites per cube, so its volume `|Z|_k = M^d · #cubes` is at most `(M crit_k)^d`,
`crit_k = 2ρ_k + 10`. -/
theorem removed_cubeVol_le (G : S.Good)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) (hadm : H.Admissible) {k : ℕ}
    (hkK : k ≤ K) {c : H.Comp k} (hc : c.1 ∈ H.rem k) :
    BudgetConsts.cubeVol S c.1.card ≤ ((S.M : ℝ) * (S.crit k : ℝ)) ^ S.d := by
  have h := RegionHistory.removed_card_le G hT hadm hkK hc
  have h' : (c.1.card : ℝ) ≤ (S.crit k : ℝ) ^ S.d := by
    have : c.1.card ≤ S.crit k ^ S.d := by simpa [Setting.crit] using h
    exact_mod_cast this
  unfold BudgetConsts.cubeVol
  rw [mul_pow]
  gcongr

end Count

end Balaban.LargeField
