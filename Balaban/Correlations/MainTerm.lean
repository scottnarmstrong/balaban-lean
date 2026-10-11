/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.LimAlong
public import Balaban.Correlations.RealSequences
public import Balaban.Correlations.GreenIdentification

/-!
# The main terms of C-1* and their bounds (CORRELATIONS.md §3.1-3.2)

* `KernelHypLarge.limAlong_mainTr`: the Gaussian main term of (F3) on the tori converges to the
  infinite-volume main term built from the kernels `t_j^μ` (Lemma 3.0);
* `KernelMassDecay`: the decay (G2) of `t_j^μ` uniformly in the mass `μ ∈ (0, 2]` (the landed
  `KernelHyp.g2` states it only at `μ = 0`);
* `abs_magJ_sub_one_le`: `|m_J - 1| ≤ K β^{-1+ρ₁}`;
* `abs_mainSum_le`: `|∑_{j<J} (β γ_j)⁻¹ t_j^{ν δ_j}| ≤ C β⁻¹ (1+|z|)^{-(d-2)} e^{-c √ν |z|}`;
* `gtr_eq`, `glg_eq`: the infinite-volume form of (F3) (Lemma 3.0).
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

variable {d L : ℕ} [NeZero L]

/-- The decay of the Gaussian kernels `t_j^μ(x, y)` for all masses `μ ∈ (0, 2]`, with constants
independent of `μ` (the form of (G2) used in Step B of CORRELATIONS.md §3.2). -/
def KernelMassDecay (d L : ℕ) (C_G δ_G : ℝ)
    (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) : Prop :=
  ∀ (μ : ℝ), 0 < μ → μ ≤ 2 → ∀ x y : Fin d → ℤ,
    KernelDecay d (L : ℝ) C_G δ_G ‖x - y‖ (fun j => t j μ x y)

section Kernel

variable {a : ℝ} {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
  {C_G δ_G : ℝ}

/-- The facts on the Gaussian kernels at the unit-lattice masses `μ ∈ (0, 2]` used by Lemma 3.0
and Step B of CORRELATIONS.md §3, beyond the range of `KernelHyp` (which asks `μ L^{2J} ≤ 1`):
(G1) the limit of the torus kernels `T_j^{ℓ,μ}` as the torus grows, for every `J > j`, and
(G2) the decay of `t_j^μ` uniform in `μ ∈ (0, 2]`. -/
structure KernelHypLarge (d L : ℕ) [NeZero L] (a : ℝ)
    (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (C_G δ_G : ℝ) : Prop where
  g1 : ∀ (J j : ℕ) (μ : ℝ), j < J → 0 < μ → μ ≤ 2 → ∀ x y,
    Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ J j m x y) atTop (𝓝 (t j μ x y))
  g2 : KernelMassDecay d L C_G δ_G t

theorem KernelHypLarge.limAlong_termKernel (H : KernelHypLarge d L a t C_G δ_G)
    {M : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L) {μ : ℝ} (hμ : 0 < μ) (hμ2 : μ ≤ 2) {J j : ℕ} (hj : j < J)
    (x y : Fin d → ℤ) :
    LimAlong (M * L) (fun ℓ _ => termKernel d L (freeSeq d L a) μ J j (ℓ / L ^ J - 1) x y)
      (t j μ x y) := by
  intro ε hε
  have ht := H.g1 J j μ hj hμ hμ2 x y
  obtain ⟨m0, hm0⟩ := Metric.tendsto_atTop.1 ht ε hε
  refine ⟨J + m0 + 1, fun ℓ _ hd => ?_⟩
  have hq : 2 ≤ M * L := by nlinarith
  have hℓpos : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
  have hLpos : 0 < L ^ J := pow_pos (by omega) J
  have h1 : (m0 + 1) * L ^ J ≤ ℓ := by
    have hle := Nat.le_of_dvd hℓpos hd
    have e1 : m0 + 1 ≤ (M * L) ^ (m0 + 1) := (Nat.lt_pow_self (by omega)).le
    have e2 : L ^ J ≤ (M * L) ^ J := Nat.pow_le_pow_left (Nat.le_mul_of_pos_left L (by omega)) J
    calc (m0 + 1) * L ^ J ≤ (M * L) ^ (m0 + 1) * (M * L) ^ J := Nat.mul_le_mul e1 e2
      _ = (M * L) ^ (J + m0 + 1) := by ring
      _ ≤ ℓ := hle
  have h2 : m0 ≤ ℓ / L ^ J - 1 := by
    have : m0 + 1 ≤ ℓ / L ^ J := (Nat.le_div_iff_mul_le hLpos).2 h1
    omega
  simpa [Real.dist_eq] using hm0 _ h2

theorem KernelHypLarge.limAlong_mainTr (H : KernelHypLarge d L a t C_G δ_G)
    {M : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L) {ξ : ℕ → Fin 3 → ℝ} {β ν : ℝ} {J : ℕ}
    (hμ : ∀ j < J, 0 < ν * deltaR ξ j ∧ ν * deltaR ξ j ≤ 2) (x y : Fin d → ℤ) :
    LimAlong (M * L) (fun ℓ _ => mainTr d L a ξ β ν J ℓ x y)
      (∑ j ∈ range J, (β * gammaR ξ j)⁻¹ * t j (ν * deltaR ξ j) x y) := by
  unfold mainTr
  refine LimAlong.sum (range J) (F := fun j ℓ _ => (β * gammaR ξ j)⁻¹ *
    termKernel d L (freeSeq d L a) (ν * deltaR ξ j) J j (ℓ / L ^ J - 1) x y)
    (a := fun j => (β * gammaR ξ j)⁻¹ * t j (ν * deltaR ξ j) x y) fun j hj => ?_
  exact LimAlong.const_mul _ (H.limAlong_termKernel hM hL (hμ j (mem_range.1 hj)).1
    (hμ j (mem_range.1 hj)).2 (mem_range.1 hj) x y)

end Kernel

theorem inv_sqrt_le {β b : ℝ} (hβ : 0 < β) (hb : β / 2 ≤ b) :
    (Real.sqrt b)⁻¹ ≤ Real.sqrt 2 * β ^ (-(1 / 2 : ℝ)) := by
  have hb0 : 0 < b := lt_of_lt_of_le (by positivity) hb
  have h1 : Real.sqrt (β / 2) ≤ Real.sqrt b := Real.sqrt_le_sqrt hb
  have h2 : β ^ (-(1 / 2 : ℝ)) = (Real.sqrt β)⁻¹ := by
    rw [Real.rpow_neg hβ.le, Real.sqrt_eq_rpow]
  rw [h2]
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsβ : 0 < Real.sqrt β := Real.sqrt_pos.2 hβ
  have h3 : Real.sqrt (β / 2) = Real.sqrt β / Real.sqrt 2 := Real.sqrt_div hβ.le 2
  calc (Real.sqrt b)⁻¹ ≤ (Real.sqrt (β / 2))⁻¹ := inv_anti₀ (by positivity) h1
    _ = Real.sqrt 2 * (Real.sqrt β)⁻¹ := by rw [h3]; field_simp

omit [NeZero L] in
/-- One term of `m_J - 1`: `|(√β_j)⁻¹ μ_{j+1}| ≤ √2 c_* β^{-1+ρ₁} r^{j+1}`, `r = L^{-ρ₀}`. -/
theorem abs_term_le {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ} (HS : SeqHyp L γ₀ c₈ ξ)
    {ρ₀ ρ₁ cS β : ℝ} (hβ : 0 < β)
    {μ : ℕ → (Fin d → ℤ) → ℝ} {x : Fin d → ℤ}
    (hμ : ∀ j, 1 ≤ j → |μ j x| ≤ cS * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀)))
    (j : ℕ) :
    |(Real.sqrt (betaR L d ξ β j))⁻¹ * μ (j + 1) x| ≤
      Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * ((L : ℝ) ^ (-ρ₀)) ^ (j + 1) := by
  have hL0 : (0 : ℝ) < L := by linarith [HS.hL1]
  set r : ℝ := (L : ℝ) ^ (-ρ₀) with hr
  rw [abs_mul, abs_of_nonneg (inv_nonneg.2 (Real.sqrt_nonneg _))]
  have h1 := inv_sqrt_le hβ (HS.betaR_ge (d := d) hβ j)
  have h2 := hμ (j + 1) (by omega)
  have h3 : (L : ℝ) ^ (-(((j + 1 : ℕ) : ℝ) * ρ₀)) = r ^ (j + 1) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    congr 1
    push_cast
    ring
  rw [h3] at h2
  have h4 : β ^ (-(1 / 2 : ℝ)) * β ^ (-(1 / 2 : ℝ) + ρ₁) = β ^ (-1 + ρ₁) := by
    rw [← Real.rpow_add hβ]; congr 1; ring
  calc (Real.sqrt (betaR L d ξ β j))⁻¹ * |μ (j + 1) x|
      ≤ (Real.sqrt 2 * β ^ (-(1 / 2 : ℝ))) * (cS * β ^ (-(1 / 2 : ℝ) + ρ₁) * r ^ (j + 1)) :=
        mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
    _ = Real.sqrt 2 * cS * (β ^ (-(1 / 2 : ℝ)) * β ^ (-(1 / 2 : ℝ) + ρ₁)) * r ^ (j + 1) := by
        ring
    _ = _ := by rw [h4]

omit [NeZero L] in
/-- `|m_J - 1| ≤ √2 c_* (r / (1 - r)) β^{-1+ρ₁}`, `r = L^{-ρ₀}` (CORRELATIONS.md §3.2, one-point). -/
theorem abs_magJ_sub_one_le {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ} (HS : SeqHyp L γ₀ c₈ ξ)
    {ρ₀ ρ₁ cS β : ℝ} (hρ₀ : 0 < ρ₀) (hcS : 0 ≤ cS) (hβ : 0 < β)
    {μ : ℕ → (Fin d → ℤ) → ℝ} {x : Fin d → ℤ} (J : ℕ)
    (hμ : ∀ j, 1 ≤ j → |μ j x| ≤ cS * β ^ (-(1 / 2 : ℝ) + ρ₁) * (L : ℝ) ^ (-((j : ℝ) * ρ₀))) :
    |magJ L d ξ μ β J x - 1| ≤
      Real.sqrt 2 * cS * ((L : ℝ) ^ (-ρ₀) / (1 - (L : ℝ) ^ (-ρ₀))) * β ^ (-1 + ρ₁) := by
  have hL0 : (0 : ℝ) < L := by linarith [HS.hL1]
  set r : ℝ := (L : ℝ) ^ (-ρ₀) with hr
  have hr0 : 0 ≤ r := (Real.rpow_pos_of_pos hL0 _).le
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg HS.hL1 (by linarith)
  have hterm : ∀ j ∈ range J, |(Real.sqrt (betaR L d ξ β j))⁻¹ * μ (j + 1) x| ≤
      Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * r ^ (j + 1) := fun j _ =>
    abs_term_le HS hβ hμ j
  have hsum : |magJ L d ξ μ β J x - 1| ≤ ∑ j ∈ range J,
      Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * r ^ (j + 1) := by
    have : magJ L d ξ μ β J x - 1 =
        -∑ j ∈ range J, (Real.sqrt (betaR L d ξ β j))⁻¹ * μ (j + 1) x := by
      unfold magJ; ring
    rw [this, abs_neg]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  have hps := ratePartialSum_le hr0 hr1 J
  rw [ratePartialSum] at hps
  calc Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * ∑ j ∈ range J, r ^ (j + 1)
      ≤ Real.sqrt 2 * cS * β ^ (-1 + ρ₁) * (r / (1 - r)) :=
        mul_le_mul_of_nonneg_left hps (by positivity)
    _ = _ := by ring

omit [NeZero L] in
/-- The bound of `exists_abs_mainSum_le` for a given constant `C'`. -/
def MainSumBound (d L : ℕ) (C_G δ_G C' : ℝ) : Prop :=
  ∀ {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ}, SeqHyp L γ₀ c₈ ξ → ∀ {β ν : ℝ},
      0 < β → 0 < ν → ∀ {J : ℕ}, (L : ℝ) ^ J * Real.sqrt ν ≤ (L : ℝ) ^ 2 →
      ∀ {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}, KernelMassDecay d L C_G δ_G t →
      (∀ j < J, 0 < ν * deltaR ξ j ∧ ν * deltaR ξ j ≤ 2) → ∀ x y : Fin d → ℤ,
      |∑ j ∈ range J, (β * gammaR ξ j)⁻¹ * t j (ν * deltaR ξ j) x y| ≤
        2 / β * C_G * C' * (1 + ‖x - y‖) ^ (-((d : ℝ) - 2)) *
          Real.exp (-(δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * ‖x - y‖))

omit [NeZero L] in
/-- The main sum of (F3) in infinite volume, bounded by the mass decay (G2) uniform in `μ`
(CORRELATIONS.md §3.2). -/
theorem exists_abs_mainSum_le (hd : 3 ≤ d) (hL : 2 ≤ L) {C_G δ_G : ℝ} (hδ : 0 < δ_G)
    (hC : 0 ≤ C_G) :
    ∃ C' : ℝ, 0 ≤ C' ∧ MainSumBound d L C_G δ_G C' := by
  have hL1 : (1 : ℝ) < L := by exact_mod_cast hL
  have hL0 : (0 : ℝ) < L := by linarith
  have hσ : 0 < (d : ℝ) - 2 := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨C', hC'0, hC'⟩ := sum_pow_exp_le hσ (show 0 < δ_G / 2 by positivity) hL1
  refine ⟨C', hC'0, fun {γ₀ c₈ ξ} HS {β ν} hβ hν {J} hJ {t} ht hμ x y => ?_⟩
  set r : ℝ := ‖x - y‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg _
  set E : ℝ := Real.exp (-(δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * r)) with hE
  have hE0 : 0 ≤ E := (Real.exp_pos _).le
  set σ : ℝ := (d : ℝ) - 2 with hσdef
  have hterm : ∀ j ∈ range J, |(β * gammaR ξ j)⁻¹ * t j (ν * deltaR ξ j) x y| ≤
      2 / β * C_G * E * (L ^ (-((j : ℝ) * σ)) * Real.exp (-(δ_G / 2 * r / L ^ j))) := by
    intro j hj
    have hj' : j < J := mem_range.1 hj
    have hg := (HS.gammaR_bounds j).1
    have hgpos := HS.gammaR_pos j
    have h1 : |(β * gammaR ξ j)⁻¹| ≤ 2 / β := by
      rw [abs_of_pos (inv_pos.2 (by positivity))]
      calc (β * gammaR ξ j)⁻¹ ≤ (β / 2)⁻¹ :=
            inv_anti₀ (by positivity) (by nlinarith)
        _ = 2 / β := by field_simp
    have h2 := ht (ν * deltaR ξ j) (hμ j hj').1 (hμ j hj').2 x y j
    have hcast : (((j * (d - 2) : ℕ)) : ℝ) = (j : ℝ) * σ := by
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 2 ≤ d)]; push_cast; ring
    have h3 : ((L : ℝ) ^ (j * (d - 2)))⁻¹ = (L : ℝ) ^ (-((j : ℝ) * σ)) := by
      rw [Real.rpow_neg hL0.le, ← hcast, Real.rpow_natCast]
    rw [h3] at h2
    have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
    have hkey : δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * r ≤ δ_G / 2 * r / (L : ℝ) ^ j := by
      have a1 : Real.sqrt ν * (L : ℝ) ^ j ≤ (L : ℝ) ^ 2 := by
        calc Real.sqrt ν * (L : ℝ) ^ j ≤ Real.sqrt ν * (L : ℝ) ^ J := by
              gcongr; exact hL1.le
          _ = (L : ℝ) ^ J * Real.sqrt ν := mul_comm _ _
          _ ≤ (L : ℝ) ^ 2 := hJ
      have a2 : Real.sqrt ν / (L : ℝ) ^ 2 ≤ 1 / (L : ℝ) ^ j := by
        rw [div_le_div_iff₀ (by positivity) hLj]; linarith
      have a3 : δ_G / (2 * (L : ℝ) ^ 2) * Real.sqrt ν * r =
          (δ_G * r / 2) * (Real.sqrt ν / (L : ℝ) ^ 2) := by field_simp
      have a4 : δ_G / 2 * r / (L : ℝ) ^ j = (δ_G * r / 2) * (1 / (L : ℝ) ^ j) := by
        field_simp
      rw [a3, a4]
      exact mul_le_mul_of_nonneg_left a2 (by positivity)
    have h4 : Real.exp (-(δ_G * r / (L : ℝ) ^ j)) ≤
        Real.exp (-(δ_G / 2 * r / (L : ℝ) ^ j)) * E := by
      rw [hE, ← Real.exp_add]
      refine Real.exp_le_exp.2 ?_
      have : δ_G * r / (L : ℝ) ^ j = 2 * (δ_G / 2 * r / (L : ℝ) ^ j) := by field_simp
      rw [this]; linarith
    rw [abs_mul]
    calc |(β * gammaR ξ j)⁻¹| * |t j (ν * deltaR ξ j) x y|
        ≤ (2 / β) * (C_G * (L : ℝ) ^ (-((j : ℝ) * σ)) * Real.exp (-(δ_G * r / (L : ℝ) ^ j))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
      _ ≤ (2 / β) * (C_G * (L : ℝ) ^ (-((j : ℝ) * σ)) *
            (Real.exp (-(δ_G / 2 * r / (L : ℝ) ^ j)) * E)) := by
          gcongr
      _ = _ := by ring
  have hS := hC' J r hr0
  calc |∑ j ∈ range J, (β * gammaR ξ j)⁻¹ * t j (ν * deltaR ξ j) x y|
      ≤ ∑ j ∈ range J, |(β * gammaR ξ j)⁻¹ * t j (ν * deltaR ξ j) x y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ range J, 2 / β * C_G * E *
        ((L : ℝ) ^ (-((j : ℝ) * σ)) * Real.exp (-(δ_G / 2 * r / (L : ℝ) ^ j))) :=
        Finset.sum_le_sum hterm
    _ = 2 / β * C_G * E * ∑ j ∈ range J,
        ((L : ℝ) ^ (-((j : ℝ) * σ)) * Real.exp (-(δ_G / 2 * r / (L : ℝ) ^ j))) := by
        rw [← Finset.mul_sum]
    _ ≤ 2 / β * C_G * E * (C' * (1 + r) ^ (-σ)) :=
        mul_le_mul_of_nonneg_left hS (by positivity)
    _ = _ := by rw [hσdef]; ring

end Balaban.Correlations
