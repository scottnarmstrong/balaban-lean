/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovSqrtSupComplex

/-!
# The `ℓ^∞` bounds of `C^{1/2}(s)` and `𝕃(s)` on the decoupling domain

`decCovSqrt_supNorm`: for every `e = (s, φ₀, α₀) ∈ DecDom G N κ δ`, `‖C^{1/2}(s) v‖_∞ ≤ K ‖v‖_∞`
with `K = covSupConstC d L N (a k) κ`; `decLog_supNorm`: the same for the diagonal `𝕃(s)`, with
`K = covLogSupConst d L N (a k) (aT / L²) κ`. Both constants depend only on `(d, L, N, a k, κ)`
(and `aT` for the logarithm), not on the torus size or on `e`.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Finset Matrix MeasureTheory Set

namespace Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- **Sup bound of `C^{1/2}(s)` on the decoupling domain.** -/
theorem decCovSqrt_supNorm (S : XSetting G a aT ν) (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N} (he : e ∈ DecDom G N κ δ)
    (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ p, ‖v p‖ ≤ c)
    (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConstC d L N (a k) κ * c := by
  have H := covStanding_of_mem S hκ hM hδ hsm (isUnitLatticeB_unit (G := G)).toIsUnitLattice he
  exact covC_sqrt_supNorm H.fam H.field H.nonneg H.small v hc hv p

/-! ### The logarithm -/

section Log

variable (H : ∀ x, 0 ≤ x → XData G a aT ν x α κ s) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

omit [NeZero N₁] in
theorem covWVec_sub {κι : Type*} (ε : ℝ) (ρ : κι → ℝ) (u v : κι × Fin N → ℂ) :
    covWVec ε ρ (u - v) = covWVec ε ρ u - covWVec ε ρ v := by
  funext p; simp [covWVec, mul_sub]

/-- The constant of the weighted bound of the projection `P`. -/
noncomputable def covPConst (d : ℕ) (ε : ℝ) : ℝ := 2 * (1 + 2 * Real.exp (ε * (2 * d)))

/-- The constant of the weighted bound of `log a_k (1 - P) + log (a_k + b) P`. -/
noncomputable def covL0Const (d : ℕ) (ak b ε : ℝ) : ℝ :=
  |Real.log ak| + |Real.log (ak + b) - Real.log ak| * covPConst d ε

theorem covC_wP {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : XWeight G ε r)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) (liftOp N (unitP G) *ᵥ h)) ≤
      covPConst d ε * n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  have hA := covC_wA (N := N) hr (c := 1) (b := 1) (x := 0) (by norm_num) (by norm_num) h
  have hid : liftOp N (unitP G) *ᵥ h =
      (2 : ℂ) • (h - covA 1 1 0 (liftOp N (unitP G)) *ᵥ h) := by
    rw [covA_mulVec_eq]
    ext p
    simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
    norm_num
    ring
  rw [hid, covWVec_smul, n2_smul, covWVec_sub]
  have hn := n2_nonneg (covWVec ε (fun b : unitPts G => unitRho r b.1) h)
  refine (mul_le_mul_of_nonneg_left (n2_sub_le _ _) (by simp)).trans ?_
  unfold covPConst
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  simp only [h2, inv_one, add_zero, mul_one] at hA ⊢
  nlinarith [hA]

theorem covC_wL0 {ε : ℝ} {r : CTorus d L N₁ m₁ (k + 1) → ℝ} (hr : XWeight G ε r) (ak b : ℝ)
    (h : unitPts G × Fin N → ℂ) :
    n2 (covWVec ε (fun b : unitPts G => unitRho r b.1)
        (((((Real.log ak : ℝ) : ℂ) • (1 - liftOp N (unitP G)) +
          ((Real.log (ak + b) : ℝ) : ℂ) • liftOp N (unitP G)) *ᵥ h))) ≤
      covL0Const d ak b ε * n2 (covWVec ε (fun b : unitPts G => unitRho r b.1) h) := by
  have hP := covC_wP (N := N) hr h
  have hid : (((Real.log ak : ℝ) : ℂ) • (1 - liftOp N (unitP G)) +
          ((Real.log (ak + b) : ℝ) : ℂ) • liftOp N (unitP G)) *ᵥ h =
      ((Real.log ak : ℝ) : ℂ) • h +
        ((Real.log (ak + b) - Real.log ak : ℝ) : ℂ) • (liftOp N (unitP G) *ᵥ h) := by
    ext p
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec,
      Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    push_cast
    ring
  rw [hid, covWVec_add, covWVec_smul, covWVec_smul]
  refine (n2_add_le _ _).trans ?_
  rw [n2_smul, n2_smul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs]
  have hn := n2_nonneg (covWVec ε (fun b : unitPts G => unitRho r b.1) h)
  unfold covL0Const
  nlinarith [mul_le_mul_of_nonneg_left hP (abs_nonneg (Real.log (ak + b) - Real.log ak))]

/-- Row sums of a kernel with `ℓ¹`-exponential decay. -/
theorem covC_sup_of_entry (hr : 0 < xAgmonRate d L / L)
    (M : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) {E : ℝ} (hE0 : 0 ≤ E)
    (hM : ∀ (p q : unitPts G) (i i' : Fin N), ‖M (p, i) (q, i')‖ ≤
      E * Real.exp (-(xAgmonRate d L / L) *
        Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1))
    (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ p, ‖v p‖ ≤ c)
    (p : unitPts G × Fin N) :
    ‖(M *ᵥ v) p‖ ≤ N * Green.ballConst d (xAgmonRate d L / L) * E * c := by
  classical
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
  calc ‖(M *ᵥ v) p‖ ≤ ∑ q : unitPts G × Fin N, ‖M p q‖ * c := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hv q) (norm_nonneg _)
    _ ≤ ∑ q : unitPts G × Fin N, (E * f q.1) * c := by
        refine Finset.sum_le_sum fun q _ => ?_
        exact mul_le_mul_of_nonneg_right (hM p.1 q.1 p.2 q.2) hc
    _ = N * (E * ∑ q, f q) * c := by
        rw [Fintype.sum_prod_type_right]
        simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ N * (E * Green.ballConst d (xAgmonRate d L / L)) * c := by gcongr
    _ = _ := by ring

/-- The entry constant of the kernel of `𝕃(s)`. -/
noncomputable def covLogEntryConst (d L : ℕ) (ak b κ : ℝ) : ℝ :=
  (covL0Const d ak b (xAgmonRate d L) + covTConst d L ak (xAgmonRate d L) κ / ak) *
    Real.exp (xAgmonRate d L * d / L)

/-- The `ℓ^∞ → ℓ^∞` constant of `𝕃(s)` on the polydisc `|s_P| ≤ e^κ`. -/
noncomputable def covLogSupConst (d L N : ℕ) (ak b κ : ℝ) : ℝ :=
  N * Green.ballConst d (xAgmonRate d L / L) * covLogEntryConst d L ak b κ

include H hφ hδ hsm in
theorem covC_log_entry_decay (p q : unitPts G) (i i' : Fin N) :
    ‖decLog G a aT ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covLogEntryConst d L (a k) (aT / (L : ℝ) ^ 2) κ *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have D0 := H 0 le_rfl
  have hak : 0 < a k := D0.st.hak_pos
  have hε0 := xAgmonRate_nonneg_of_fam H
  set ε := xAgmonRate d L with hε
  set ex := Real.exp (-(ε / L) * Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1)
    with hex
  have hex0 : 0 ≤ ex := (Real.exp_pos _).le
  have hT0 := covTConst_nonneg d L (a k) ε κ
  set B0 : ℝ := covTConst d L (a k) ε κ * Real.exp (ε * d / L) * ex with hB0
  have hB0nn : 0 ≤ B0 := by rw [hB0]; positivity
  -- the constant part
  set L0 : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ :=
    ((Real.log (a k) : ℝ) : ℂ) • (1 - liftOp N (unitP G)) +
      ((Real.log (a k + aT / (L : ℝ) ^ 2) : ℝ) : ℂ) • liftOp N (unitP G) with hL0
  have hL0e := covC_entry_of_weighted (G := G) hε0 L0
    (K := covL0Const d (a k) (aT / (L : ℝ) ^ 2) ε)
    (by unfold covL0Const covPConst; positivity)
    (fun r hr h => covC_wL0 (N := N) hr (a k) (aT / (L : ℝ) ^ 2) h) p q i i'
  -- the integral part
  have hint : Integrable (fun y : ℝ => B0 * ((a k + y)⁻¹) ^ 2) (volume.restrict (Ioi (0 : ℝ))) :=
    (integrableOn_inv_add_sq hak).const_mul B0
  have hbound := norm_integral_le_of_norm_le
    (f := fun x => (decCov G a aT x ν α s φ (unitQ G) (unitP G) -
      covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) (p, i) (q, i')) hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => by
      have hx0 : 0 < x := mem_Ioi.mp hx
      have hK : 0 ≤ covTConst d L (a k) ε κ * ((a k + x)⁻¹) ^ 2 := by positivity
      have := covC_entry_of_weighted (G := G) hε0
        (decCov G a aT x ν α s φ (unitQ G) (unitP G) -
          covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) hK
        (fun r hr h => covC_wT H hφ hδ hsm hx0.le hr h) p q i i'
      refine this.trans (le_of_eq ?_)
      rw [hB0]; ring))
  rw [integral_const_mul, integral_inv_add_sq hak] at hbound
  unfold decLog
  rw [Matrix.sub_apply]
  refine (norm_sub_le _ _).trans ?_
  have h2 : ‖intMat (volume.restrict (Ioi (0 : ℝ)))
      (fun x => decCov G a aT x ν α s φ (unitQ G) (unitP G) -
        covA (a k) (aT / (L : ℝ) ^ 2) x (liftOp N (unitP G))) (p, i) (q, i')‖ ≤
      B0 * (a k)⁻¹ := by
    unfold intMat; simpa using hbound
  calc _ ≤ covL0Const d (a k) (aT / (L : ℝ) ^ 2) ε * Real.exp (ε * d / L) * ex + B0 * (a k)⁻¹ :=
        add_le_add hL0e h2
    _ = _ := by
        rw [hB0]; unfold covLogEntryConst; rw [← hε]; field_simp

include H hφ hδ hsm in
theorem covC_log_supNorm (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decLog G a aT ν α s φ (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covLogSupConst d L N (a k) (aT / (L : ℝ) ^ 2) κ * c := by
  have D0 := H 0 le_rfl
  have hd : 0 < d := by have := D0.st.dg.hd; omega
  have hr : 0 < xAgmonRate d L / L := by
    have h1 := xAgmonRate_pos hd D0.st.dg.hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hak : 0 < a k := D0.st.hak_pos
  have hE0 : 0 ≤ covLogEntryConst d L (a k) (aT / (L : ℝ) ^ 2) κ := by
    have := covTConst_nonneg d L (a k) (xAgmonRate d L) κ
    unfold covLogEntryConst covL0Const covPConst
    positivity
  have := covC_sup_of_entry hr _ hE0 (covC_log_entry_decay H hφ hδ hsm) v hc hv p
  unfold covLogSupConst
  linarith

end Log

/-- **Sup bound of `𝕃(s)` on the decoupling domain.** -/
theorem decLog_supNorm (S : XSetting G a aT ν) (hκ : 0 ≤ κ)
    (hM : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
    (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4) {e : DecData G N} (he : e ∈ DecDom G N κ δ)
    (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c) (hv : ∀ p, ‖v p‖ ≤ c)
    (p : unitPts G × Fin N) :
    ‖(decLog G a aT ν e.2.2 (extS G e.1) e.2.1 (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covLogSupConst d L N (a k) (aT / (L : ℝ) ^ 2) κ * c := by
  have H := covStanding_of_mem S hκ hM hδ hsm (isUnitLatticeB_unit (G := G)).toIsUnitLattice he
  exact covC_log_supNorm H.fam H.field H.nonneg H.small v hc hv p

end Balaban.Fluctuation
