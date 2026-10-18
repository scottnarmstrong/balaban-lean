/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerNewLevelE0Beta
public import Balaban.Inhabited.StepTowerNewLevelE0Close
public import Balaban.Inhabited.StepTowerScaleT

/-!
# The closure of `E₀` at the towers (`StepTowerNewLevelE0Tower`)

`tower_E0_closure_agree`: for the towers `T` that agree with a reference tower `T₀` (on `m₁, BG, BG₂, κ`,
hence on all rates) and every radius `t ≥ c 3^{-α(k+1)}`, `2 α < 1`: let `Γ ≥ 0`, `A₁ ≥ 0`, `Q₁ ≥ 0` and
`E₀ = 2 Γ (A₁ + C_PE (K₀ + n₂ K₀))`, `n₂ = n_fibre e^{κ₀ c_Br}`.  Beyond one threshold `β₀` of `β`
(uniform in the scale `k` and in `t`), every `B` with the explicit bound of the class chain
(`e0CoeffFamily_class_exists_tower_struct_step_agree_explicitB`, the class amplitude `Q = Q₁ E₀`)
satisfies `(A₁ + B) Γ ≤ E₀`, and the class amplitude satisfies the smallness premise of the chain.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Polymer Balaban.Multiscale Balaban.Inhabited.MarkBudgetAudit

/-- **The closure of `E₀` at the towers**: see the module doc-string. -/
theorem tower_E0_closure_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {c α : ℝ} (hc : 0 < c) (hα : 2 * α < 1) {Γ A₁' Q₁ E₀ : ℝ} (hΓ : 0 ≤ Γ) (hA₁' : 0 ≤ A₁')
    (hQ : 0 ≤ Q₁)
    (hE₀ : E₀ = 2 * Γ * (A₁' + CPE 3 3 (2 * (K0 3 3 T₀.κ0 + 1) +
      (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) + rootUnionK 3 3 1 T₀.m₁ T₀.κ0)
      (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' * (K0 3 3 T₀.κ0 + ((nFibre 3 3 : ℕ) : ℝ) *
      Real.exp (T₀.κ0 * cBr 3 3) * K0 3 3 T₀.κ0))) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → ∀ k : ℕ, 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β → 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ T.t →
      ∀ B : ℝ, B ≤ CPE 3 3 (2 * (K0 3 3 T₀.κ0 + 1) +
        (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) + rootUnionK 3 3 1 T₀.m₁ T₀.κ0)
        (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' *
        (corrF0 T k β p₁ * K0 3 3 T₀.κ0 +
          Q₁ * E₀ / (2 * corrR T k (β * 3 ^ k) p₁) *
            (((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T₀.κdec - 1) * cBr 3 3)) * K0 3 3 T₀.κ0 +
          ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T₀.κ0 * cBr 3 3) * K0 3 3 T₀.κ0) →
      (A₁' + B) * Γ ≤ E₀ ∧ corrU / (2 * corrR T k (β * 3 ^ k) p₁) * (Q₁ * E₀) ≤
        1 / (8 * (2 * (K0 3 3 T₀.κ0 + 1) + (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) +
          rootUnionK 3 3 1 T₀.m₁ T₀.κ0) ^ 3 * c1 3 3 *
          Real.exp (((2 * T₀.κdec - 1) - 2 * T₀.κ0) * cG 3 3 + c1 3 3 + T₀.κ' * cG 3 3)) := by
  set Kc : ℝ := 2 * (K0 3 3 T₀.κ0 + 1) + (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) +
    rootUnionK 3 3 1 T₀.m₁ T₀.κ0 with hKc
  set Cp : ℝ := CPE 3 3 Kc (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' with hCp
  set Nf₁ : ℝ := ((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T₀.κdec - 1) * cBr 3 3) with hNf₁
  set Nf₂ : ℝ := ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T₀.κ0 * cBr 3 3) with hNf₂
  have hc1 := one_le_c1 3 3
  have hK0 := K0_pos 3 3 T₀.κ0
  have hK0' : 0 ≤ rootUnionK 3 3 1 T₀.m₁ T₀.κ0 := rootUnionK_nonneg 1 T₀.κ0
  have hKc0 : 0 < Kc := by rw [hKc]; positivity
  have hCp0 : 0 ≤ Cp := by rw [hCp]; unfold CPE; positivity
  have hNf₁0 : 0 ≤ Nf₁ := by rw [hNf₁]; positivity
  have hNf₂0 : 0 ≤ Nf₂ := by rw [hNf₂]; positivity
  have hE0 : 0 ≤ E₀ := by
    rw [hE₀]
    exact mul_nonneg (mul_nonneg two_pos.le hΓ)
      (add_nonneg hA₁' (mul_nonneg hCp0 (add_nonneg hK0.le (mul_nonneg hNf₂0 hK0.le))))
  set S : ℝ := 1 / (8 * Kc ^ 3 * c1 3 3 *
    Real.exp (((2 * T₀.κdec - 1) - 2 * T₀.κ0) * cG 3 3 + c1 3 3 + T₀.κ' * cG 3 3)) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set Rn : ℝ := max (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ) (corrU * (Q₁ * E₀) / (2 * S)) + 1 with hRn
  have hRn0 : 0 < Rn := by
    have : 0 ≤ max (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ) (corrU * (Q₁ * E₀) / (2 * S)) :=
      (by positivity : 0 ≤ Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ).trans (le_max_left _ _)
    rw [hRn]; linarith
  obtain ⟨β₀, h3, H⟩ := exists_beta0_closure_agree T₀ hA.le p hc hRn0 hα
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ k hk β p₁ hβ hp hp₁ hct B hB => ?_⟩
  obtain ⟨hR, hF⟩ := H T hm₁ hBG hBG₂ hκ k hk β p₁ hβ hp hp₁ hct
  have hβ0 : 0 < β := by linarith
  have hR0 : 0 < corrR T k (β * 3 ^ k) p₁ := lt_of_lt_of_le hRn0 hR
  have h1 : Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ ≤ corrR T k (β * 3 ^ k) p₁ := by
    refine le_trans ?_ hR
    rw [hRn]
    linarith [le_max_left (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ) (corrU * (Q₁ * E₀) / (2 * S))]
  have h2 : corrU * (Q₁ * E₀) ≤ 2 * S * corrR T k (β * 3 ^ k) p₁ := by
    have h := le_trans (le_max_right (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ)
      (corrU * (Q₁ * E₀) / (2 * S))) (by rw [hRn] at hR; linarith : _ ≤ corrR T k (β * 3 ^ k) p₁)
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  exact closure_numeric hA₁' hCp0 hK0.le hF (corrF0_pos T hk hβ0 hp).le hQ hNf₁0 hNf₂0 hΓ hR0
    (by rw [hE₀]) (by simpa [mul_assoc] using hB) h1 h2

/-- **The closure of `E₀` at the towers with the decoupled step radius `δ₁ ≤ T.t`** (the chain of
`e0CoeffFamily_class_exists_tower_struct_step_dec_agree_collar_explicitB`): as `tower_E0_closure_agree`
with `R = δ₁/(4 decMR)`, the radius `c 3^{-α(k+1)} ≤ δ₁`. -/
theorem tower_E0_closure_dec_agree {κmin : ℝ} (T₀ : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    {c α : ℝ} (hc : 0 < c) (hα : 2 * α < 1) {Γ A₁' Q₁ E₀ : ℝ} (hΓ : 0 ≤ Γ) (hA₁' : 0 ≤ A₁')
    (hQ : 0 ≤ Q₁)
    (hE₀ : E₀ = 2 * Γ * (A₁' + CPE 3 3 (2 * (K0 3 3 T₀.κ0 + 1) +
      (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) + rootUnionK 3 3 1 T₀.m₁ T₀.κ0)
      (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' * (K0 3 3 T₀.κ0 + ((nFibre 3 3 : ℕ) : ℝ) *
      Real.exp (T₀.κ0 * cBr 3 3) * K0 3 3 T₀.κ0))) :
    ∃ β₀ : ℝ, 3 ≤ β₀ ∧ ∀ T : StepTower κmin, T.m₁ = T₀.m₁ → T.BG = T₀.BG → T.BG₂ = T₀.BG₂ →
      T.κ = T₀.κ → ∀ δ₁ : ℝ, δ₁ ≤ T.t → ∀ k : ℕ, 1 ≤ k → ∀ β p₁ : ℝ, β₀ ≤ β → 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * 3 ^ k) → c * (3 : ℝ) ^ (-(α * ((k : ℝ) + 1))) ≤ δ₁ →
      ∀ B : ℝ, B ≤ CPE 3 3 (2 * (K0 3 3 T₀.κ0 + 1) +
        (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) + rootUnionK 3 3 1 T₀.m₁ T₀.κ0)
        (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' *
        (corrF0 T k β p₁ * K0 3 3 T₀.κ0 +
          Q₁ * E₀ / (2 * (δ₁ / (4 * decMR T k (β * 3 ^ k) p₁))) *
            (((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T₀.κdec - 1) * cBr 3 3)) * K0 3 3 T₀.κ0 +
          ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T₀.κ0 * cBr 3 3) * K0 3 3 T₀.κ0) →
      (A₁' + B) * Γ ≤ E₀ ∧ corrU / (2 * (δ₁ / (4 * decMR T k (β * 3 ^ k) p₁))) * (Q₁ * E₀) ≤
        1 / (8 * (2 * (K0 3 3 T₀.κ0 + 1) + (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) +
          rootUnionK 3 3 1 T₀.m₁ T₀.κ0) ^ 3 * c1 3 3 *
          Real.exp (((2 * T₀.κdec - 1) - 2 * T₀.κ0) * cG 3 3 + c1 3 3 + T₀.κ' * cG 3 3)) := by
  set Kc : ℝ := 2 * (K0 3 3 T₀.κ0 + 1) + (K0 3 3 T₀.κ0 + rootUnionK 3 3 1 T₀.m₁ T₀.κ0) +
    rootUnionK 3 3 1 T₀.m₁ T₀.κ0 with hKc
  set Cp : ℝ := CPE 3 3 Kc (2 * T₀.κdec - 1) T₀.κ0 T₀.κ' with hCp
  set Nf₁ : ℝ := ((nFibre 3 3 : ℕ) : ℝ) * Real.exp ((2 * T₀.κdec - 1) * cBr 3 3) with hNf₁
  set Nf₂ : ℝ := ((nFibre 3 3 : ℕ) : ℝ) * Real.exp (T₀.κ0 * cBr 3 3) with hNf₂
  have hc1 := one_le_c1 3 3
  have hK0 := K0_pos 3 3 T₀.κ0
  have hK0' : 0 ≤ rootUnionK 3 3 1 T₀.m₁ T₀.κ0 := rootUnionK_nonneg 1 T₀.κ0
  have hKc0 : 0 < Kc := by rw [hKc]; positivity
  have hCp0 : 0 ≤ Cp := by rw [hCp]; unfold CPE; positivity
  have hNf₁0 : 0 ≤ Nf₁ := by rw [hNf₁]; positivity
  have hNf₂0 : 0 ≤ Nf₂ := by rw [hNf₂]; positivity
  have hE0 : 0 ≤ E₀ := by
    rw [hE₀]
    exact mul_nonneg (mul_nonneg two_pos.le hΓ)
      (add_nonneg hA₁' (mul_nonneg hCp0 (add_nonneg hK0.le (mul_nonneg hNf₂0 hK0.le))))
  set S : ℝ := 1 / (8 * Kc ^ 3 * c1 3 3 *
    Real.exp (((2 * T₀.κdec - 1) - 2 * T₀.κ0) * cG 3 3 + c1 3 3 + T₀.κ' * cG 3 3)) with hS
  have hS0 : 0 < S := by rw [hS]; positivity
  set Rn : ℝ := max (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ) (corrU * (Q₁ * E₀) / (2 * S)) + 1 with hRn
  have hRn0 : 0 < Rn := by
    have : 0 ≤ max (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ) (corrU * (Q₁ * E₀) / (2 * S)) :=
      (by positivity : 0 ≤ Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ).trans (le_max_left _ _)
    rw [hRn]; linarith
  obtain ⟨β₀, h3, H⟩ := exists_beta0_closure_agree T₀ hA.le p hc hRn0 hα
  refine ⟨β₀, h3, fun T hm₁ hBG hBG₂ hκ δ₁ hδ₁T k hk β p₁ hβ hp hp₁ hcδ B hB => ?_⟩
  have hδ₁0 : 0 < δ₁ := lt_of_lt_of_le (by positivity) hcδ
  obtain ⟨T', hT't, hT'm, -, hT'B, hT'κ, -, hT'B₂, -, -, -⟩ := exists_stepTower_shrink T hδ₁0 hδ₁T
  obtain ⟨-, hF⟩ := H T hm₁ hBG hBG₂ hκ k hk β p₁ hβ hp hp₁ (hcδ.trans hδ₁T)
  obtain ⟨hR', -⟩ := H T' (hT'm.trans hm₁) (hT'B.trans hBG) (hT'B₂.trans hBG₂) (hT'κ.trans hκ) k hk
    β p₁ hβ hp hp₁ (hcδ.trans_eq hT't.symm)
  have hcr : corrR T' k (β * 3 ^ k) p₁ = δ₁ / (4 * decMR T k (β * 3 ^ k) p₁) := by
    unfold corrR
    rw [hT't]
    unfold decMR
    rw [hT'κ]
  rw [hcr] at hR'
  have hβ0 : 0 < β := by linarith
  have hR0 : 0 < δ₁ / (4 * decMR T k (β * 3 ^ k) p₁) := lt_of_lt_of_le hRn0 hR'
  have h1 : Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ ≤ δ₁ / (4 * decMR T k (β * 3 ^ k) p₁) := by
    refine le_trans ?_ hR'
    rw [hRn]
    linarith [le_max_left (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ) (corrU * (Q₁ * E₀) / (2 * S))]
  have h2 : corrU * (Q₁ * E₀) ≤ 2 * S * (δ₁ / (4 * decMR T k (β * 3 ^ k) p₁)) := by
    have h := le_trans (le_max_right (Cp * Q₁ * Nf₁ * K0 3 3 T₀.κ0 * Γ)
      (corrU * (Q₁ * E₀) / (2 * S))) (by rw [hRn] at hR'; linarith :
        _ ≤ δ₁ / (4 * decMR T k (β * 3 ^ k) p₁))
    rw [div_le_iff₀ (by positivity)] at h
    linarith
  exact closure_numeric hA₁' hCp0 hK0.le hF (corrF0_pos T hk hβ0 hp).le hQ hNf₁0 hNf₂0 hΓ hR0
    (by rw [hE₀]) (by simpa [mul_assoc] using hB) h1 h2

end Balaban.Inhabited
