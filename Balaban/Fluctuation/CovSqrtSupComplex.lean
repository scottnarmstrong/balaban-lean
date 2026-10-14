/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CovSqrtSupComplexWeighted

/-!
# The `ℓ^∞` bound of `C^{1/2}(s)` at complex decoupling parameters

The complex-`s` version of `cov_sqrt_supNorm` (FLUCTUATION.md Lemma 2.4 (c)). From the weighted
bound `covC_wC` of the resolvent at `(κ, s)` we get the entry decay
`|C_x(s)(p,i; q,i')| ≤ K₁ (a_k + x)⁻¹ e^{-(γ/L) dist(p,q)}` (`covC_entry_decay`), integrate it
against `x^{-1/2}` (`covC_sqrt_entry_decay`), and sum over the unit torus
(`covC_sqrt_supNorm`). `decCovSqrt_supNorm` is the statement on the domain `DecDom`: the constant
`covSupConstC d L N (a k) κ` depends only on `(d, L, N, a k, κ)`.
-/

@[expose] public section

open Balaban Balaban.Localization Balaban.Multiscale Finset Matrix MeasureTheory Set

namespace Balaban.Fluctuation

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
  {a : ℕ → ℝ} {aT ν : ℝ} {α : G.Ω 1 → ℂ} {δ κ : ℝ}
  {s : ℕ × CTorus d L N₁ m₁ (k + 1) → ℂ}
  {φ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ}

/-- Entry decay from a family of weighted operator bounds. -/
theorem covC_entry_of_weighted (hε0 : 0 ≤ xAgmonRate d L)
    (M : Matrix (unitPts G × Fin N) (unitPts G × Fin N) ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hM : ∀ r : CTorus d L N₁ m₁ (k + 1) → ℝ, XWeight G (xAgmonRate d L) r →
      ∀ h : unitPts G × Fin N → ℂ,
        n2 (covWVec (xAgmonRate d L) (fun b : unitPts G => unitRho r b.1) (M *ᵥ h)) ≤
          K * n2 (covWVec (xAgmonRate d L) (fun b : unitPts G => unitRho r b.1) h))
    (p q : unitPts G) (i i' : Fin N) :
    ‖M (p, i) (q, i')‖ ≤ K * Real.exp (xAgmonRate d L * d / L) *
      Real.exp (-(xAgmonRate d L / L) *
        Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  classical
  set ε := xAgmonRate d L with hε
  set ud := Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1 with hud
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  obtain ⟨r, WW, hρq, hρp⟩ := cov_exists_weight (G := G) p q hε0 (le_refl ε)
  have hDd1 : (ud - d) / L ≤ unitRho r p.1 := (le_max_right _ _).trans hρp
  have hmain := hM r WW (Pi.single (q, i') 1 : unitPts G × Fin N → ℂ)
  rw [cov_n2_single, hρq, mul_zero, Real.exp_zero, mul_one] at hmain
  have hent := cov_entry_le_n2 (N := N) ε (fun b : unitPts G => unitRho r b.1) M p q i i'
  have hpos : 0 < Real.exp (ε * unitRho r p.1) := Real.exp_pos _
  have hfin : ‖M (p, i) (q, i')‖ ≤ K * Real.exp (-(ε * unitRho r p.1)) := by
    rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ hpos, mul_comm]
    exact hent.trans hmain
  have hexp : Real.exp (-(ε * unitRho r p.1)) ≤
      Real.exp (ε * d / L) * Real.exp (-(ε / L) * ud) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have e : ε * ((ud - d) / L) = ε * ud / L - ε * d / L := by ring
    have e2 : -(ε / L) * ud = -(ε * ud / L) := by ring
    have := mul_le_mul_of_nonneg_left hDd1 hε0
    rw [e2]; linarith
  calc _ ≤ _ := hfin
    _ ≤ K * (Real.exp (ε * d / L) * Real.exp (-(ε / L) * ud)) :=
        mul_le_mul_of_nonneg_left hexp hK
    _ = _ := by ring

/-- The entry constant of the kernel of `C^{1/2}(s)`. -/
noncomputable def covSqrtEntryConstC (d L : ℕ) (ak κ : ℝ) : ℝ :=
  covC1Const d L ak (xAgmonRate d L) κ * Real.exp (xAgmonRate d L * d / L) / Real.sqrt ak

/-- The `ℓ^∞ → ℓ^∞` constant of `C^{1/2}(s)` on the polydisc `|s_P| ≤ e^κ`. -/
noncomputable def covSupConstC (d L N : ℕ) (ak κ : ℝ) : ℝ :=
  N * Green.ballConst d (xAgmonRate d L / L) * covSqrtEntryConstC d L ak κ

section CoverSup

variable {Cx : ℝ} (Hc : ∀ x, 0 ≤ x → Dec2.XData (coverOf G) G a aT ν x α κ s Cx)
  (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ) (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include Hc hφ hδ hsm in
/-- Entry decay of `C_x(s)` at complex `s`, uniform in `x ≥ 0`. -/
theorem covC_entry_decay_cover {x : ℝ} (hx : 0 ≤ x) (p q : unitPts G) (i i' : Fin N) :
    ‖decCov G a aT x ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covC1Const d L (a k) (xAgmonRate d L) κ * (a k + x)⁻¹ *
        Real.exp (xAgmonRate d L * d / L) *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have D := Hc x hx
  have hak0 : 0 < a k := (by have := (⟨D.st.hak1, D.st.hak2⟩ : _ ∧ _); linarith [this.1])
  have hcx : 0 < a k + x := by linarith
  have hK : 0 ≤ covC1Const d L (a k) (xAgmonRate d L) κ * (a k + x)⁻¹ :=
    mul_nonneg (covC1Const_nonneg d L hak0 _ _) (inv_pos.2 hcx).le
  exact covC_entry_of_weighted ((xAgmonRate_pos (by have := (Hc 0 le_rfl).st.hd; omega) (Hc 0 le_rfl).st.hL).le) _ hK
    (fun r hr h => covC_wC_cover Hc hφ hδ hsm hx hr h) p q i i'

include Hc hφ hδ hsm in
theorem covC_sqrt_entry_decay_cover (p q : unitPts G) (i i' : Fin N) :
    ‖decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covSqrtEntryConstC d L (a k) κ *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) := by
  have D0 := Hc 0 le_rfl
  have hak : 0 < a k := (by have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _); linarith [this.1])
  set B0 : ℝ := covC1Const d L (a k) (xAgmonRate d L) κ * Real.exp (xAgmonRate d L * d / L) *
    Real.exp (-(xAgmonRate d L / L) *
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) with hB0
  have hB0nn : 0 ≤ B0 := by
    have := covC1Const_nonneg d L hak (xAgmonRate d L) κ
    rw [hB0]; positivity
  unfold decCovSqrt
  simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  unfold intMat
  have hint : Integrable (fun y : ℝ => B0 * (y ^ (-(1 / 2 : ℝ)) * (a k + y)⁻¹))
      (volume.restrict (Ioi (0 : ℝ))) := (integrableOn_rpow_inv_add hak).const_mul B0
  have hbound := norm_integral_le_of_norm_le
    (f := fun x => decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x (p, i) (q, i')) hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun x hx => by
      have hx0 : 0 < x := mem_Ioi.mp hx
      have h3 : 0 < x ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hx0 _
      unfold decSqrtInt
      simp only [Matrix.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg h3.le]
      have := covC_entry_decay_cover Hc hφ hδ hsm hx0.le p q i i'
      calc x ^ (-(1 / 2 : ℝ)) *
            ‖decCov G a aT x ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖
          ≤ x ^ (-(1 / 2 : ℝ)) * (B0 * (a k + x)⁻¹) := by
            refine mul_le_mul_of_nonneg_left ?_ h3.le
            refine this.trans (le_of_eq ?_)
            rw [hB0]; ring
        _ = _ := by ring))
  rw [integral_const_mul, integral_rpow_inv_add hak] at hbound
  have hpi : 0 < Real.pi := Real.pi_pos
  have hsq : 0 < Real.sqrt (a k) := Real.sqrt_pos.2 hak
  rw [abs_of_pos (by positivity)]
  calc 1 / Real.pi * ‖∫ x in Ioi (0 : ℝ),
        decSqrtInt G a aT ν α s φ (unitQ G) (unitP G) x (p, i) (q, i')‖
      ≤ 1 / Real.pi * (B0 * (Real.pi / Real.sqrt (a k))) := by gcongr
    _ = _ := by
        rw [hB0]; unfold covSqrtEntryConstC; field_simp

include Hc hφ hδ hsm in
theorem covC_sqrt_supNorm_cover (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConstC d L N (a k) κ * c := by
  classical
  have D0 := Hc 0 le_rfl
  have hd : 0 < d := by have := D0.st.hd; omega
  have hr : 0 < xAgmonRate d L / L := by
    have h1 := xAgmonRate_pos hd D0.st.hL
    have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  set E := covSqrtEntryConstC d L (a k) κ with hE
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
  have hE0 : 0 ≤ E := by
    have hak : 0 < a k := (by have := (⟨D0.st.hak1, D0.st.hak2⟩ : _ ∧ _); linarith [this.1])
    have := covC1Const_nonneg d L hak (xAgmonRate d L) κ
    rw [hE]; unfold covSqrtEntryConstC; positivity
  calc ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ v) p‖
      ≤ ∑ q : unitPts G × Fin N,
          ‖decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) p q‖ * c := by
        simp only [Matrix.mulVec, dotProduct]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hv q) (norm_nonneg _)
    _ ≤ ∑ q : unitPts G × Fin N, (E * f q.1) * c := by
        refine Finset.sum_le_sum fun q _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ hc
        exact covC_sqrt_entry_decay_cover Hc hφ hδ hsm p.1 q.1 p.2 q.2
    _ = N * (E * ∑ q, f q) * c := by
        rw [Fintype.sum_prod_type_right]
        simp only [← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul]
        ring
    _ ≤ N * (E * Green.ballConst d (xAgmonRate d L / L)) * c := by gcongr
    _ = _ := by unfold covSupConstC; rw [← hE]; ring

end CoverSup

section Main

variable (H : ∀ x, 0 ≤ x → XData G a aT ν x α κ s) (hφ : IsConstraintField G δ φ) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)

include H hφ hδ hsm in
/-- Entry decay of `C_x(s)` at complex `s`, uniform in `x ≥ 0`. -/
theorem covC_entry_decay {x : ℝ} (hx : 0 ≤ x) (p q : unitPts G) (i i' : Fin N) :
    ‖decCov G a aT x ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covC1Const d L (a k) (xAgmonRate d L) κ * (a k + x)⁻¹ *
        Real.exp (xAgmonRate d L * d / L) *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) :=
  covC_entry_decay_cover (fun x hx => (H x hx).toCover) hφ hδ hsm hx p q i i'

include H hφ hδ hsm in
theorem covC_sqrt_entry_decay (p q : unitPts G) (i i' : Fin N) :
    ‖decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) (p, i) (q, i')‖ ≤
      covSqrtEntryConstC d L (a k) κ *
        Real.exp (-(xAgmonRate d L / L) *
          Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1 - k)) p.1 q.1) :=
  covC_sqrt_entry_decay_cover (fun x hx => (H x hx).toCover) hφ hδ hsm p q i i'

include H hφ hδ hsm in
theorem covC_sqrt_supNorm (v : unitPts G × Fin N → ℂ) {c : ℝ} (hc : 0 ≤ c)
    (hv : ∀ p, ‖v p‖ ≤ c) (p : unitPts G × Fin N) :
    ‖(decCovSqrt G a aT ν α s φ (unitQ G) (unitP G) *ᵥ v) p‖ ≤
      covSupConstC d L N (a k) κ * c :=
  covC_sqrt_supNorm_cover (fun x hx => (H x hx).toCover) hφ hδ hsm v hc hv p

end Main

end Balaban.Fluctuation
