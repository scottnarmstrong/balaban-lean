/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.DomainDifference

/-!
# G-4(c): perturbation with exponential tails

Let `A` and `A + B` be `γ₀`-coercive with entries `≤ c₀ e^{-δ₀ dist}` and
`‖B z w‖ ≤ c₀ e^{-δ₀ dist z w} e^{-δ₀ (d z + d w)}`, `d = setDist X'`.  Then for `Λ : Finset ι`
and `x₁ x₂ ∈ Λ`
`‖(A_Λ + B_Λ + t)⁻¹ x₁ x₂ - (A_Λ + t)⁻¹ x₁ x₂‖
   ≤ 4 c₀ κ'² (γ₀+t)⁻² e^{-(μ₁/2)(d x₁ + d x₂)}`,
`μ₁ = min (ctRate (2c₀) δ₀ γ₀ κ) δ₀` (`Balaban.Green.perturbation_tails`).  Proof: the resolvent
identity `G_{A+B} - G_A = -G_A B_Λ G_{A+B}`, Combes–Thomas for both operators (the entries of
`A + B` are bounded by `2 c₀ e^{-δ₀ dist}`) and the summation Lemma 4.10 (`sum_tail_le`).
-/

@[expose] public section

open Matrix Finset

namespace Balaban.Green

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [PseudoMetricSpace ι]

lemma ctRate_anti {c c' δ₀ γ₀ κ : ℝ} (hc : 0 ≤ c) (hcc : c ≤ c') (hδ : 0 < δ₀) (hγ : 0 < γ₀)
    (hκ : 0 ≤ κ) : ctRate c' δ₀ γ₀ κ ≤ ctRate c δ₀ γ₀ κ := by
  unfold ctRate
  refine min_le_min le_rfl ?_
  have h0 : 0 < 4 * c * κ / δ₀ + 1 := by positivity
  have h1 : 4 * c * κ / δ₀ ≤ 4 * c' * κ / δ₀ := by gcongr
  exact div_le_div_of_nonneg_left hγ.le (by positivity) (by linarith)

omit [Fintype ι] [DecidableEq ι] [PseudoMetricSpace ι] in
lemma restrictOp_add (A B : Matrix ι ι ℂ) (Λ : Finset ι) :
    restrictOp (A + B) Λ = restrictOp A Λ + restrictOp B Λ := by
  ext x y; simp [restrictOp]

omit [DecidableEq ι] in
/-- Ball sums pass to a finite subset (with the subtype metric). -/
lemma ballSum_subtype {r κ : ℝ} (Λ : Finset ι)
    (hK : ∀ x : ι, ∑ y, Real.exp (-r * dist x y) ≤ κ) (x : Λ) :
    ∑ y : Λ, Real.exp (-r * dist x y) ≤ κ := by
  calc ∑ y : Λ, Real.exp (-r * dist x y)
      = ∑ y ∈ Λ, Real.exp (-r * dist (x : ι) y) := by
        rw [← Finset.sum_coe_sort Λ]; rfl
    _ ≤ ∑ y, Real.exp (-r * dist (x : ι) y) :=
        Finset.sum_le_univ_sum_of_nonneg fun _ => (Real.exp_pos _).le
    _ ≤ κ := hK x

/-- **G-4(c)**: perturbation with exponential tails around `X'`. -/
theorem perturbation_tails {A B : Matrix ι ι ℂ} {c₀ δ₀ γ₀ κ κ' : ℝ} (X' : Set ι) (hc : 0 ≤ c₀)
    (hδ : 0 < δ₀) (hγ : 0 < γ₀) (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ')
    (hA : ∀ x y, ‖A x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y))
    (hB : ∀ z w, ‖B z w‖ ≤ c₀ * Real.exp (-δ₀ * dist z w) *
      Real.exp (-δ₀ * (setDist X' z + setDist X' w)))
    (hK : ∀ x : ι, ∑ y, Real.exp (-(δ₀ / 4) * dist x y) ≤ κ)
    (hK' : ∀ x : ι, ∑ y, Real.exp (-(min (ctRate (2 * c₀) δ₀ γ₀ κ) δ₀ / 2) * dist x y) ≤ κ')
    (hcoer : IsCoercive A γ₀) (hcoer' : IsCoercive (A + B) γ₀) (Λ : Finset ι) {t : ℝ}
    (ht : 0 ≤ t) (x₁ x₂ : Λ) :
    ‖((restrictOp A Λ + restrictOp B Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ))⁻¹ -
        (restrictOp A Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ))⁻¹) x₁ x₂‖ ≤
      4 * c₀ * κ' * κ' / (γ₀ + t) ^ 2 *
        Real.exp (-(min (ctRate (2 * c₀) δ₀ γ₀ κ) δ₀ / 2) *
          (setDist X' (x₁ : ι) + setDist X' (x₂ : ι))) := by
  set μ := ctRate (2 * c₀) δ₀ γ₀ κ with hμ
  have hc2 : 0 ≤ 2 * c₀ := by positivity
  have hμ0 : 0 < μ := ctRate_pos hc2 hδ hγ hκ
  set m := min μ δ₀ with hm
  have hm0 : 0 < m := lt_min hμ0 hδ
  have hγt : 0 < γ₀ + t := by linarith
  have hd0 : ∀ z, 0 ≤ setDist X' z := fun z => setDist_nonneg X' z
  have hAB : ∀ x y, ‖(A + B) x y‖ ≤ 2 * c₀ * Real.exp (-δ₀ * dist x y) := by
    intro x y
    have h1 := hB x y
    have h2 : Real.exp (-δ₀ * (setDist X' x + setDist X' y)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [hd0 x, hd0 y])
    have h3 : ‖B x y‖ ≤ c₀ * Real.exp (-δ₀ * dist x y) := by
      refine h1.trans ?_
      calc _ ≤ c₀ * Real.exp (-δ₀ * dist x y) * 1 := by gcongr
        _ = _ := mul_one _
    calc ‖(A + B) x y‖ ≤ ‖A x y‖ + ‖B x y‖ := norm_add_le _ _
      _ ≤ _ := by linarith [hA x y]
  have cA := combesThomas_restrict hc hδ hγ hκ hA hK hcoer Λ ht
  have cAB := combesThomas_restrict hc2 hδ hγ hκ hAB hK hcoer' Λ ht
  set MA := restrictOp A Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ) with hMA
  set MAB := restrictOp A Λ + restrictOp B Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ) with hMAB
  have hMAB' : MAB = restrictOp (A + B) Λ + (t : ℂ) • (1 : Matrix Λ Λ ℂ) := by
    rw [hMAB, restrictOp_add]
  have uA : IsUnit MA := cA.1
  have uAB : IsUnit MAB := by rw [hMAB']; exact cAB.1
  have dA := (Matrix.isUnit_iff_isUnit_det _).1 uA
  have dAB := (Matrix.isUnit_iff_isUnit_det _).1 uAB
  have hid : MAB⁻¹ - MA⁻¹ = -(MA⁻¹ * restrictOp B Λ * MAB⁻¹) := by
    have e : restrictOp B Λ = MAB - MA := by rw [hMAB, hMA]; abel
    rw [e, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_nonsing_inv_cancel_right _ _ dAB,
      Matrix.nonsing_inv_mul _ dA, Matrix.one_mul]
    abel
  have gA : ∀ x y : Λ, ‖MA⁻¹ x y‖ ≤ 2 * (γ₀ + t)⁻¹ * Real.exp (-μ * dist x y) := by
    intro x y
    refine (cA.2 x y).trans ?_
    have hr := ctRate_anti (c' := 2 * c₀) hc (by linarith) hδ hγ hκ
    have : Real.exp (-ctRate c₀ δ₀ γ₀ κ * dist (x : ι) y) ≤ Real.exp (-μ * dist x y) :=
      Real.exp_le_exp.2 (by rw [Subtype.dist_eq]; nlinarith [dist_nonneg (x := (x : ι)) (y := y)])
    gcongr
  have gAB : ∀ x y : Λ, ‖MAB⁻¹ x y‖ ≤ 2 * (γ₀ + t)⁻¹ * Real.exp (-μ * dist x y) := by
    intro x y
    rw [hMAB']; exact cAB.2 x y
  have hentry : (MA⁻¹ * restrictOp B Λ * MAB⁻¹) x₁ x₂ =
      ∑ z : Λ, ∑ w : Λ, MA⁻¹ x₁ z * restrictOp B Λ z w * MAB⁻¹ w x₂ := by
    simp only [Matrix.mul_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [Matrix.sub_apply] at *
  have hidx := congrFun (congrFun hid x₁) x₂
  rw [Matrix.sub_apply, Matrix.neg_apply, hentry] at hidx
  rw [hidx, norm_neg]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ z : Λ, ‖∑ w : Λ, MA⁻¹ x₁ z * restrictOp B Λ z w * MAB⁻¹ w x₂‖ ≤
      ∑ w : Λ, 4 * c₀ / (γ₀ + t) ^ 2 * (Real.exp (-μ * dist x₁ z) *
        (Real.exp (-δ₀ * (setDist X' (z : ι) + setDist X' (w : ι))) *
          Real.exp (-δ₀ * dist z w)) * Real.exp (-μ * dist w x₂)) := by
    intro z
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    rw [norm_mul, norm_mul]
    have g1 := gA x₁ z
    have g2 := gAB w x₂
    have b1 : ‖restrictOp B Λ z w‖ ≤ c₀ * Real.exp (-δ₀ * dist z w) *
        Real.exp (-δ₀ * (setDist X' (z : ι) + setDist X' (w : ι))) := by
      simpa [restrictOp, Subtype.dist_eq] using hB z w
    calc _ ≤ (2 * (γ₀ + t)⁻¹ * Real.exp (-μ * dist x₁ z)) *
          (c₀ * Real.exp (-δ₀ * dist z w) *
            Real.exp (-δ₀ * (setDist X' (z : ι) + setDist X' (w : ι)))) *
          (2 * (γ₀ + t)⁻¹ * Real.exp (-μ * dist w x₂)) := by gcongr
      _ = _ := by field_simp; ring
  refine (Finset.sum_le_sum fun z _ => hterm z).trans ?_
  have hsum := sum_tail_le (ι := Λ) (μ := μ) (δ := δ₀) (m := m) (κ₁ := κ') (κδ := κ') hm0
    (min_le_left _ _) (min_le_right _ _) hκ'
    (ballSum_subtype Λ hK') (fun z => by
      refine (Finset.sum_le_sum fun w _ => Real.exp_le_exp.2 ?_).trans (ballSum_subtype Λ hK' z)
      have : m ≤ δ₀ := min_le_right _ _
      nlinarith [dist_nonneg (x := z) (y := w)])
    (d := fun z : Λ => setDist X' (z : ι)) (fun z => hd0 _)
    (fun x z => setDist_le_dist_add X' _ _) x₁ x₂
  simp only [← Finset.mul_sum]
  calc _ ≤ 4 * c₀ / (γ₀ + t) ^ 2 * (κ' * κ' * Real.exp (-(m / 2) *
        (setDist X' (x₁ : ι) + setDist X' (x₂ : ι)))) := by
        have h0 : 0 ≤ 4 * c₀ / (γ₀ + t) ^ 2 := by positivity
        have := mul_le_mul_of_nonneg_left hsum h0
        calc _ ≤ _ := this
          _ = _ := by ring
    _ = _ := by ring

end Balaban.Green
