/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovarianceWeighted

/-!
# The `ℓ^∞` bound of `C^{1/2}` (FLUCTUATION.md Lemma 2.4 (c), Finding F-5)

Integrating the `x`-uniform kernel decay `cov_entry_decay` against `x^{-1/2}` gives the kernel
bound `|C^{1/2}(p,i; q,i')| ≤ E e^{-(γ/L) dist(p,q)}` (`cov_sqrt_entry_decay`) with
`∫₀^∞ x^{-1/2} (a_k + x)⁻¹ dx = π / √a_k`; summing over the unit torus with the ball sum bound
gives `‖C^{1/2} v‖_∞ ≤ B_∞ ‖v‖_∞` (`cov_sqrt_supNorm`).
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Finset Matrix MeasureTheory Set

namespace Balaban.Fluctuation


variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ : ℝ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- The entry constant of the kernel of `C^{1/2}`. -/
noncomputable def covSqrtEntryConst (d L : ℕ) (ak : ℝ) : ℝ :=
  covDecayConst d L ak (xAgmonRate d L) * Real.exp (xAgmonRate d L * d / L) / Real.sqrt ak

omit [NeZero L] in
theorem covSqrtEntryConst_nonneg {ak : ℝ} (hak : 0 < ak) :
    0 ≤ covSqrtEntryConst d L ak := by
  have : 0 ≤ valConstX d := by unfold valConstX; positivity
  unfold covSqrtEntryConst covDecayConst
  positivity

theorem cov_sqrt_entry_decay (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (p q : unitPts G) (i i' : Fin N) :
    ‖decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covSqrtEntryConst d L (a k) *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have D0 := hfam 0 le_rfl
  have hak : 0 < a k := by linarith [((⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)).1]
  set B0 : ℝ := covDecayConst d L (a k) (xAgmonRate d L) * Real.exp (xAgmonRate d L * d / L) *
    Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) with hB0
  have hKnn : 0 ≤ covDecayConst d L (a k) (xAgmonRate d L) := by
    have hε := xAgmonRate_nonneg_of_fam hfam
    have : 0 ≤ valConstX d := by unfold valConstX; positivity
    unfold covDecayConst; positivity
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  unfold decCovSqrt
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold intMat
  have hint : Integrable (fun y : ℝ => B0 * (y ^ (-(1 / 2 : ℝ)) * (a k + y)⁻¹))
      (volume.restrict (Ioi (0 : ℝ))) := (integrableOn_rpow_inv_add hak).const_mul B0
  have hbound := norm_integral_le_of_norm_le (f := fun x => decSqrtInt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) x (p, i) (q, i')) hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => by
      have hx0 : 0 < x := mem_Ioi.mp hx
      have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      unfold decSqrtInt
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h3.le]
      have := cov_entry_decay hfam hφ hδ hsm hx0.le p q i i'
      calc x ^ (-(1 / 2 : ℝ)) * ‖decCov G a aT x ν α (fun _ => 1) φ (unitQ G) (unitP G) (p, i) (q, i')‖
          ≤ x ^ (-(1 / 2 : ℝ)) * (B0 * (a k + x)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ h3.le
            refine this.trans (le_of_eq ?_)
            rw [hB0]; ring
        _ = _ := by ring))
  rw [integral_const_mul, integral_rpow_inv_add hak] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (a k) := Real.sqrt_pos.2 hak
  rw [abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖∫ x in Ioi (0 : ℝ), decSqrtInt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) x (p, i) (q, i')‖
      ≤ 1 / Real.pi * (B0 * (Real.pi / Real.sqrt (a k))) := by gcongr
    _ = _ := by
        rw [hB0]; unfold covSqrtEntryConst; field_simp


/-- The `ℓ^∞ → ℓ^∞` constant of `C^{1/2}`. -/
noncomputable def covSupConst (d L N : ℕ) (ak : ℝ) : ℝ :=
  N * Green.ballConst d (xAgmonRate d L / L) * covSqrtEntryConst d L ak

theorem cov_sqrt_supNorm (hfam : ∀ x, 0 ≤ x → XData G a aT ν x α 0 (fun _ => 1))
    (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L 0 ≤ 1 / 4)
    (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConst d L N (a k) * c := by
  classical
  have D0 := hfam 0 le_rfl
  have hd : 0 < d := by have := D0.st.dg.hd; omega
  have hr : 0 < xAgmonRate d L / L := by
    have h1 := xAgmonRate_pos hd D0.st.dg.hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set E := covSqrtEntryConst d L (a k) with hE
  have hE0 : 0 ≤ E := by
    have hak : 0 < a k := by linarith [((⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _)).1]
    exact covSqrtEntryConst_nonneg hak
  set f : unitPts G → ℝ := fun q => Real.exp (-(xAgmonRate d L / L) *
    Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1.1 q.1) with hf
  have hball : ∑ q, f q ≤ Green.ballConst d (xAgmonRate d L / L) := by
    have h1 : ∑ q : unitPts G, f q = ∑ y ∈ unitPts G, Real.exp (-(xAgmonRate d L / L) *
        Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1.1 y) :=
      Finset.sum_coe_sort (unitPts G) (fun y => Real.exp (-(xAgmonRate d L / L) *
        Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1.1 y))
    rw [h1]
    exact (Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le).trans
      (Green.ballSum_torus d _ hr p.1.1)
  calc ‖(decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) *ᵥ v) p‖
      ≤ ∑ q : unitPts G × Fin N, ‖decCovSqrt G a aT ν α (fun _ => 1) φ (unitQ G) (unitP G) p q‖ * c := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hv q) (norm_nonneg _)
    _ ≤ ∑ q : unitPts G × Fin N, (E * f q.1) * c := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ hc
        exact cov_sqrt_entry_decay hfam hφ hδ hsm p.1 q.1 p.2 q.2
    _ = N * (E * ∑ q, f q) * c := by
        rw [Fintype.sum_prod_type_right]
        simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ N * (E * Green.ballConst d (xAgmonRate d L / L)) * c := by gcongr
    _ = _ := by unfold covSupConst; rw [← hE]; ring

end Balaban.Fluctuation
