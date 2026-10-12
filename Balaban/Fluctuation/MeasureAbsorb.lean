/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MeasureProduct
import Mathlib.MeasureTheory.Measure.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 2.5: only `χ_fl` remains (FLUCTUATION.md §2.5)

On `X = (ℝ^N)^T` (sup norm over the sites), `χ_fl(ψ̂) = ∏_x 1[|ψ̂(x)| < p₁]` (`chiFl`), and a
finite family of conditions `q i (ψ) < b i` (the conditions of `χ_k` and of (2.2)) is encoded by
`chiCond`.  `chiFl_absorbs_of` is the identity
`χ_k(ψ) χ_{(2.2)}(θ,ψ) χ_fl(ψ̂) = χ_fl(ψ̂)` for `ψ = ψ^{(k)}(θ) + β^{-1/2} C^{1/2} ψ̂`, with the
inputs from Lemma 2.2 / 2.3 (d) / 2.4 (c) as explicit numerical hypotheses; see the docstring.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Set

variable {T : Type*} [Fintype T] {N : ℕ}

/-- `χ_fl(ψ̂) = ∏_{x} 1[|ψ̂(x)| < p₁]`. -/
noncomputable def chiFl (T : Type*) [Fintype T] (N : ℕ) (p : ℝ) (ψ : T → Rn N) : ℝ :=
  ∏ x : T, if ‖ψ x‖ < p then 1 else 0

/-- The product of indicators `∏_i 1[q i ψ < b i]` of a finite family of conditions. -/
noncomputable def chiCond {X ι : Type*} [Fintype ι] (q : ι → X → ℝ) (b : ι → ℝ) (ψ : X) : ℝ :=
  ∏ i : ι, if q i ψ < b i then 1 else 0

theorem chiFl_eq_one_iff {p : ℝ} (hp : 0 < p) (ψ : T → Rn N) :
    chiFl T N p ψ = 1 ↔ ‖ψ‖ < p := by
  unfold chiFl
  rw [pi_norm_lt_iff hp]
  constructor
  · intro h x
    by_contra hx
    have : (∏ x : T, if ‖ψ x‖ < p then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ x) (by simp [hx])
    rw [this] at h; exact zero_ne_one h
  · intro h
    exact Finset.prod_eq_one fun x _ => by simp [h x]

theorem chiFl_eq_zero_or_one (p : ℝ) (ψ : T → Rn N) : chiFl T N p ψ = 0 ∨ chiFl T N p ψ = 1 := by
  by_cases h : ∀ x, ‖ψ x‖ < p
  · right; exact Finset.prod_eq_one fun x _ => by simp [h x]
  · left
    push Not at h
    obtain ⟨x, hx⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ x) (by simp [not_lt.2 hx])

theorem chiCond_eq_one_iff {X ι : Type*} [Fintype ι] (q : ι → X → ℝ) (b : ι → ℝ) (ψ : X) :
    chiCond q b ψ = 1 ↔ ∀ i, q i ψ < b i := by
  unfold chiCond
  constructor
  · intro h i
    by_contra hi
    have : (∏ i : ι, if q i ψ < b i then (1 : ℝ) else 0) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
    rw [this] at h; exact zero_ne_one h
  · intro h
    exact Finset.prod_eq_one fun i _ => by simp [h i]

/-- **Lemma 2.5 (identity for `χ_fl`), internal form.**

`X = (ℝ^N)^T` carries the sup norm over sites; `ψ0 = ψ^{(k)}(θ)` is the background,
`C` the operator `C^{(k)1/2}`, `ψ = ψ0 + β^{-1/2} C ψ̂`.  The conditions of `χ_k` and (2.2) are
`q i ψ < b i` (`i ∈ ι`).  The inputs, taken as hypotheses (and to be discharged by the
critical-point lemma 2.2, Lemma 2.3 (d) and Lemma 2.4 (c)):

* `hbase` (Lemma 2.2 at `ψ̂ = 0`): every condition holds at `ψ0` with room `δ/3`:
  `q i ψ0 + δ/3 ≤ b i`;
* `hLip` (Lemma 2.3 (d)): the conditions move by at most `K₂ |ψ'|` under `ψ0 ↦ ψ0 + ψ'`,
  for `|ψ'| ≤ B₅ β^{-1/2} p₁`;
* `hB5` (Lemma 2.4 (c)): `|C ψ̂| ≤ B₅ |ψ̂|` in the sup norm;
* `hp40` (P4 (2.40)): `p₁/p₀ ≤ (3 B₅ K₂)⁻¹` with `p₀ = β^{1/2} δ`.

Conclusion: `χ_cond(ψ) χ_fl(ψ̂) = χ_fl(ψ̂)`. -/
theorem chiFl_absorbs_of {ι : Type*} [Fintype ι] (q : ι → (T → Rn N) → ℝ) (b : ι → ℝ)
    (ψ0 : T → Rn N) (C : (T → Rn N) →ₗ[ℝ] (T → Rn N))
    {β δ K₂ B₅ p₁ : ℝ} (hβ : 0 < β) (hδ : 0 < δ) (hK₂ : 0 < K₂) (hB₅ : 0 < B₅) (hp₁ : 0 < p₁)
    (hbase : ∀ i, q i ψ0 + δ / 3 ≤ b i)
    (hLip : ∀ i (ψ' : T → Rn N), ‖ψ'‖ ≤ B₅ * β ^ (-(1 / 2 : ℝ)) * p₁ →
      |q i (ψ0 + ψ') - q i ψ0| ≤ K₂ * ‖ψ'‖)
    (hB5 : ∀ ψh : T → Rn N, ‖C ψh‖ ≤ B₅ * ‖ψh‖)
    (hp40 : p₁ / (β ^ (1 / 2 : ℝ) * δ) ≤ (3 * B₅ * K₂)⁻¹) (ψh : T → Rn N) :
    chiCond q b (ψ0 + (β ^ (-(1 / 2 : ℝ))) • C ψh) * chiFl T N p₁ ψh = chiFl T N p₁ ψh := by
  rcases chiFl_eq_zero_or_one p₁ ψh with h0 | h1
  · rw [h0, mul_zero]
  · rw [h1, mul_one]
    have hnorm := (chiFl_eq_one_iff hp₁ ψh).1 h1
    have hc : 0 < β ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hβ _
    have hsq : 0 < β ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hβ _
    have hcs : β ^ (-(1 / 2 : ℝ)) * β ^ (1 / 2 : ℝ) = 1 := by
      rw [← Real.rpow_add hβ]; simp
    -- (2.40): K₂ B₅ β^{-1/2} p₁ ≤ δ / 3
    have h240 : K₂ * (B₅ * β ^ (-(1 / 2 : ℝ)) * p₁) ≤ δ / 3 := by
      have h1 : p₁ ≤ (3 * B₅ * K₂)⁻¹ * (β ^ (1 / 2 : ℝ) * δ) := by
        rwa [div_le_iff₀ (by positivity)] at hp40
      have h2 : K₂ * (B₅ * β ^ (-(1 / 2 : ℝ)) * p₁) ≤
          K₂ * (B₅ * β ^ (-(1 / 2 : ℝ)) * ((3 * B₅ * K₂)⁻¹ * (β ^ (1 / 2 : ℝ) * δ))) := by
        gcongr
      refine h2.trans (le_of_eq ?_)
      field_simp
      exact hcs
    set ψ' : T → Rn N := (β ^ (-(1 / 2 : ℝ))) • C ψh with hψ'
    have hψ'n : ‖ψ'‖ < B₅ * β ^ (-(1 / 2 : ℝ)) * p₁ := by
      rw [hψ', norm_smul, Real.norm_of_nonneg hc.le]
      calc β ^ (-(1 / 2 : ℝ)) * ‖C ψh‖ ≤ β ^ (-(1 / 2 : ℝ)) * (B₅ * ‖ψh‖) := by
            gcongr; exact hB5 ψh
        _ < β ^ (-(1 / 2 : ℝ)) * (B₅ * p₁) := by gcongr
        _ = _ := by ring
    rw [chiCond_eq_one_iff]
    intro i
    have hl := hLip i ψ' hψ'n.le
    have h3 : q i (ψ0 + ψ') - q i ψ0 < δ / 3 := by
      have := (le_abs_self _).trans hl
      have h4 : K₂ * ‖ψ'‖ < K₂ * (B₅ * β ^ (-(1 / 2 : ℝ)) * p₁) := by gcongr
      linarith
    linarith [hbase i]

/-- `ν_{p₁}`-almost every `ψh` has `χ_fl(ψh) = 1`: the product measure (2.5) lives on the set where
`χ_fl = 1`. -/
theorem ae_chiFl_fluctMeasure (T : Type*) [Fintype T] (N : ℕ) {p : ℝ} (hp : 0 < p) :
    ∀ᵐ ψ ∂fluctMeasure T N p, chiFl T N p ψ = 1 := by
  have := isProbabilityMeasure_fluctMeasure1 N hp
  have h1 : ∀ᵐ x ∂fluctMeasure1 N p, ‖x‖ < p := by
    unfold fluctMeasure1
    refine Measure.ae_smul_measure ?_ _
    rw [ae_withDensity_iff (measurable_fluctDensity N p).ennreal_ofReal]
    refine ae_of_all _ fun x hx => ?_
    by_contra h
    exact hx (by simp [fluctDensity, h])
  have h2 : ∀ x : T, ∀ᵐ ψ ∂fluctMeasure T N p, ‖ψ x‖ < p := fun x =>
    (measurePreserving_eval (fun _ : T => fluctMeasure1 N p) x).quasiMeasurePreserving.ae h1
  filter_upwards [ae_all_iff.2 h2] with ψ hψ
  exact (chiFl_eq_one_iff hp ψ).2 ((pi_norm_lt_iff hp).2 hψ)

end Balaban.Fluctuation
