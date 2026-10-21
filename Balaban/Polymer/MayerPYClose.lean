/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.MayerClose
public import Balaban.Polymer.Size

/-!
# Closeness of the local terms of the Mayer gas

* `pe_size_sub_bound` (PE-L with a size, closeness): activities `K, K₂` with `|K|, |K₂| ≤ ε e^{-κ d}`
  and `|K - K₂| ≤ ε e^{-κ d} e^{-λ m}` (`m ≥ 0` decreasing under inclusion) have local terms with
  `∑_{Y ∋ □} |P_K(Y) - P_{K₂}(Y)| e^{κ'(d(Y) + c) + λ m(Y)} ≤ 2 ε K₀ e^{c₁ + κ' c}`, under the conditions
  of `pe_size` with `2 ε` in place of `ε`;
* `mayer_PY_sub_bound`: the same for the Mayer activities of two families of local terms on one
  product space whose difference is at most `H₀ e^{-(κ₀ + κ₁) d(t)} e^{-λ m(t)}` (`mayerK_sub_bound_margin`
  and `pe_size_sub_bound`), and `mayer_PY_sub_bound_single`: one set `Y`, the closeness needed only on
  the terms inside `Y`;
* the two-system version is `PY_mayer_close_transport` (`Polymer/MayerPYTransport.lean`).
-/

@[expose] public section

noncomputable section

open scoped Classical

open Finset MeasureTheory

namespace Balaban.Polymer

section Size

variable {P : Type*} [Fintype P] {B : Type*} [Fintype B] (supp : P → Finset B)
  (d : Finset B → ℝ) {ε κ κ' κ0 K0 c c1 : ℝ}

/-- **PE-L with a size, closeness of the local terms.** -/
theorem pe_size_sub_bound (hε : 0 ≤ ε) (hκ' : 0 ≤ κ') (hc : 0 ≤ c) (hd : ∀ Y, 0 ≤ d Y)
    (hG1 : ∀ x, ((supp x).card : ℝ) ≤ c1 * (1 + d (supp x)))
    (hG2 : ∀ b : B, ∑ x, (if b ∈ supp x then Real.exp (-κ0 * d (supp x)) else 0) ≤ K0)
    (hG3 : ∀ (n : ℕ) (X : Fin (n + 1) → P), (clusterGraph (shareBlock supp) X).Connected →
      d (unionOf supp X) ≤ ∑ i, d (supp (X i)) + c * n)
    (hκ : κ' + κ0 + c1 ≤ κ) (hα : 2 * ε * K0 * Real.exp (c1 + κ' * c) ≤ 1)
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam) (K K₂ : P → ℂ) (hK : ∀ x, ‖K x‖ ≤ ε * Real.exp (-κ * d (supp x)))
    (hK₂ : ∀ x, ‖K₂ x‖ ≤ ε * Real.exp (-κ * d (supp x)))
    (hKK : ∀ x, ‖K x - K₂ x‖ ≤ ε * Real.exp (-κ * d (supp x)) * Real.exp (-lam * m (supp x)))
    (b : B) :
    ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock supp) supp K Y - PY (shareBlock supp) supp K₂ Y‖ *
          Real.exp (κ' * (d Y + c) + lam * m Y) ≤
      2 * ε * K0 * Real.exp (c1 + κ' * c) := by
  have h2ε : 0 ≤ 2 * ε := by positivity
  have hent := size_entropy supp d h2ε hd hG1 hG2 hκ (by simpa [mul_assoc] using hα)
  have hKP := kp_of_entropy supp (sizeW supp d (2 * ε) κ κ' c) (sizeW_nonneg supp d h2ε) hent
  have hmain := pe_PY_sub_bound (shareBlock supp) supp (fun Y => κ' * (d Y + c)) 0 le_rfl
    (fun Y => by have := hd Y; positivity) (size_g_G3 supp d hκ' hG3) m hm hmono hlam
    (κ0 := fun x => ε * Real.exp (-κ * d (supp x)))
    (fun x => by unfold sizeW; ring_nf) hKP K K₂ hK hK₂ hKK b
  exact hmain.trans (hent b)

end Size

section Mayer

variable {B : Type*} [Fintype B] {Ω : B → Type*} [∀ b, MeasurableSpace (Ω b)]
  (μ : ∀ b, Measure (Ω b)) [∀ b, IsProbabilityMeasure (μ b)]
  {H H₂ : NePoly B → (∀ b, Ω b) → ℂ} {d : Finset B → ℝ}
  {H0 κ0 κ1 c K0 c1 κ' κ0P K0P cP : ℝ}

/-- **Closeness of the local terms of the Mayer gas** (one product space). Two families of local
terms on the nonempty sets of blocks, both with the bound of MY, whose difference is at most
`H₀ e^{-(κ₀ + κ₁) d(t)} e^{-λ m(t)}` (`m ≥ 0` decreasing under inclusion): with
`ε = 4 q₂ c₁`, `q₂ = 2 (2 H₀) K₀ e^{κ₁ c}`, the local terms of their Mayer gases satisfy
`∑_{Y ∋ □} |P(Y) - P₂(Y)| e^{κ'(d(Y) + c_P) + λ m(Y)} ≤ 2 ε K₀ᴾ e^{c₁ + κ' c_P}`. -/
theorem mayer_PY_sub_bound (hmeas : ∀ t, Measurable (H t)) (hmeas₂ : ∀ t, Measurable (H₂ t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1))
    (hH₂ : ∀ t Φ, ‖H₂ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1))
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t : NePoly B => b ∈ t.1),
      Real.exp (-κ0 * d t.1) ≤ K0)
    (hG3T : ∀ C : Finset (NePoly B), ConnSet (fun t : NePoly B => t.1) C →
      d (unionCs (fun t : NePoly B => t.1) C) ≤ ∑ t ∈ C, d t.1 + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * (2 * H0) * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (4 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1) * K0P *
      Real.exp (c1 + κ' * cP) ≤ 1)
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam)
    (hHH : ∀ t Φ, ‖H t Φ - H₂ t Φ‖ ≤
      H0 * Real.exp (-(κ0 + κ1) * d t.1) * Real.exp (-lam * m t.1)) (b : B) :
    ∑ Y ∈ (Finset.univ : Finset (Finset B)).filter (fun Y => b ∈ Y),
        ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
            (mayerK μ (fun X : NePoly B => X.1) H) Y -
          PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
            (mayerK μ (fun X : NePoly B => X.1) H₂) Y‖ *
          Real.exp (κ' * (d Y + cP) + lam * m Y) ≤
      2 * (4 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1) * K0P * Real.exp (c1 + κ' * cP) := by
  set q₂ := 2 * (2 * H0) * K0 * Real.exp (κ1 * c) with hq₂
  obtain ⟨b0⟩ : Nonempty B := ⟨b⟩
  have hK0 : 0 ≤ K0 := le_trans (Finset.sum_nonneg (fun t _ => (Real.exp_pos _).le))
    (hG2T b0)
  have hq₂0 : 0 ≤ q₂ := by positivity
  set ε := 4 * q₂ * c1 with hεdef
  have hε : 0 ≤ ε := by positivity
  have hq1 : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2 := by
    have : 2 * H0 * K0 * Real.exp (κ1 * c) * c1 ≤ q₂ * c1 := by
      rw [hq₂]
      have : 0 ≤ 2 * H0 * K0 * Real.exp (κ1 * c) * c1 := by positivity
      nlinarith
    linarith
  have hKb : ∀ (H' : NePoly B → (∀ b, Ω b) → ℂ), (∀ t Φ, ‖H' t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1)) →
      ∀ x : NePoly B, ‖mayerK μ (fun X : NePoly B => X.1) H' x‖ ≤
        ε * Real.exp (-(κ1 - 3 / 2) * d x.1) := by
    intro H' hH' x
    refine (mayer_activity_bound μ (sup := fun X : NePoly B => X.1) hH0 hH0' hκ0 hκ1 hc hd
      (fun t => t.2) hH' hG2T hG3T hc1 hq1 x (hG1 x)).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
    rw [hεdef, hq₂]
    have : 0 ≤ 2 * H0 * K0 * Real.exp (κ1 * c) * c1 := by positivity
    nlinarith
  have hKK : ∀ x : NePoly B, ‖mayerK μ (fun X : NePoly B => X.1) H x -
      mayerK μ (fun X : NePoly B => X.1) H₂ x‖ ≤
        ε * Real.exp (-(κ1 - 3 / 2) * d x.1) * Real.exp (-lam * m x.1) := by
    intro x
    refine (mayerK_sub_bound_margin μ (sup := fun X : NePoly B => X.1) hmeas hmeas₂ hH0 hH0' hκ0
      hκ1 hc hd (fun t => t.2) hH hH₂ m hm hmono hlam hG2T hG3T hc1 hq x (hG1 x)
      (fun t _ Φ => hHH t Φ)).trans (le_of_eq ?_)
    rw [hεdef]
    ring
  exact pe_size_sub_bound (Subtype.val : NePoly B → Finset B) d hε hκ' hcP hd
    (fun x => hG1 x) hG2P hG3P hκ hα m hm hmono hlam _ _ (hKb H hH) (hKb H₂ hH₂) hKK b

omit [∀ b, IsProbabilityMeasure (μ b)] in
/-- The Mayer activity of `x` depends only on the terms inside `x`. -/
theorem mayerK_congr_terms {H H' : NePoly B → (∀ b, Ω b) → ℂ} (x : NePoly B)
    (h : ∀ t : NePoly B, t.1 ⊆ x.1 → H t = H' t) :
    mayerK μ (fun X : NePoly B => X.1) H x = mayerK μ (fun X : NePoly B => X.1) H' x := by
  unfold mayerK mayerAct polyAct
  refine integral_congr_ae (Filter.Eventually.of_forall fun Φ => ?_)
  refine Finset.sum_congr rfl fun C hC => Finset.prod_congr rfl fun t ht => ?_
  exact congrArg (fun F : (∀ b, Ω b) → ℂ => Complex.exp (F Φ) - 1) (h t (sub_of_mem_Cfam hC ht))

/-- **Closeness of the local terms of the Mayer gas at one set `Y`**: the hypotheses of
`mayer_PY_sub_bound`, with the closeness of the terms required only inside `Y`, give
`|P(Y) - P₂(Y)| ≤ 2 ε K₀ᴾ e^{c₁ + κ' c_P} e^{-κ'(d(Y) + c_P) - λ m(Y)}`, `ε = 4 q₂ c₁`. -/
theorem mayer_PY_sub_bound_single (hmeas : ∀ t, Measurable (H t))
    (hmeas₂ : ∀ t, Measurable (H₂ t))
    (hH0 : 0 ≤ H0) (hH0' : H0 ≤ Real.log 2) (hκ0 : 0 ≤ κ0) (hκ1 : 0 ≤ κ1) (hc : 0 ≤ c)
    (hd : ∀ Y, 0 ≤ d Y)
    (hH : ∀ t Φ, ‖H t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1))
    (hH₂ : ∀ t Φ, ‖H₂ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1))
    (hG2T : ∀ b : B, ∑ t ∈ Finset.univ.filter (fun t : NePoly B => b ∈ t.1),
      Real.exp (-κ0 * d t.1) ≤ K0)
    (hG3T : ∀ C : Finset (NePoly B), ConnSet (fun t : NePoly B => t.1) C →
      d (unionCs (fun t : NePoly B => t.1) C) ≤ ∑ t ∈ C, d t.1 + c * ((C.card : ℝ) - 1))
    (hc1 : 0 ≤ c1) (hq : 2 * (2 * H0) * K0 * Real.exp (κ1 * c) * c1 ≤ 1 / 2)
    (hG1 : ∀ Y : NePoly B, (Y.1.card : ℝ) ≤ c1 * (1 + d Y.1))
    (hκ' : 0 ≤ κ') (hcP : 0 ≤ cP)
    (hG2P : ∀ b : B, ∑ Y : NePoly B, (if b ∈ Y.1 then Real.exp (-κ0P * d Y.1) else 0) ≤ K0P)
    (hG3P : ∀ (n : ℕ) (X : Fin (n + 1) → NePoly B),
      (clusterGraph (shareBlock (Subtype.val : NePoly B → Finset B)) X).Connected →
        d (unionOf (Subtype.val : NePoly B → Finset B) X) ≤ ∑ i, d (X i).1 + cP * n)
    (hκ : κ' + κ0P + c1 ≤ κ1 - 3 / 2)
    (hα : 2 * (4 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1) * K0P *
      Real.exp (c1 + κ' * cP) ≤ 1)
    (m : Finset B → ℝ) (hm : ∀ Y, 0 ≤ m Y) (hmono : ∀ X Y, X ⊆ Y → m Y ≤ m X) {lam : ℝ}
    (hlam : 0 ≤ lam) (Y : Finset B) (hY : Y.Nonempty)
    (hHH : ∀ t : NePoly B, t.1 ⊆ Y → ∀ Φ, ‖H t Φ - H₂ t Φ‖ ≤
      H0 * Real.exp (-(κ0 + κ1) * d t.1) * Real.exp (-lam * m t.1)) :
    ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerK μ (fun X : NePoly B => X.1) H) Y -
        PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
          (mayerK μ (fun X : NePoly B => X.1) H₂) Y‖ ≤
      2 * (4 * (2 * (2 * H0) * K0 * Real.exp (κ1 * c)) * c1) * K0P * Real.exp (c1 + κ' * cP) *
        Real.exp (-(κ' * (d Y + cP) + lam * m Y)) := by
  let H₃ : NePoly B → (∀ b, Ω b) → ℂ := fun t => if t.1 ⊆ Y then H₂ t else H t
  have hmeas₃ : ∀ t, Measurable (H₃ t) := fun t => by
    by_cases ht : t.1 ⊆ Y
    · simp only [H₃, ht, ↓reduceIte]; exact hmeas₂ t
    · simp only [H₃, ht, ↓reduceIte]; exact hmeas t
  have hH₃ : ∀ t Φ, ‖H₃ t Φ‖ ≤ H0 * Real.exp (-(κ0 + κ1) * d t.1) := fun t Φ => by
    by_cases ht : t.1 ⊆ Y
    · simp only [H₃, ht, ↓reduceIte]; exact hH₂ t Φ
    · simp only [H₃, ht, ↓reduceIte]; exact hH t Φ
  have hHH₃ : ∀ t Φ, ‖H t Φ - H₃ t Φ‖ ≤
      H0 * Real.exp (-(κ0 + κ1) * d t.1) * Real.exp (-lam * m t.1) := fun t Φ => by
    by_cases ht : t.1 ⊆ Y
    · simp only [H₃, ht, ↓reduceIte]; exact hHH t ht Φ
    · simp only [H₃, ht, ↓reduceIte, sub_self, norm_zero]; positivity
  have h23 : PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (mayerK μ (fun X : NePoly B => X.1) H₂) Y =
      PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (mayerK μ (fun X : NePoly B => X.1) H₃) Y :=
    PY_congr _ _ Y fun x hx => mayerK_congr_terms μ x fun t ht => by
      have : t.1 ⊆ Y := ht.trans hx
      simp only [H₃, this, ↓reduceIte]
  obtain ⟨b, hb⟩ := hY
  have hsum := mayer_PY_sub_bound μ hmeas hmeas₃ hH0 hH0' hκ0 hκ1 hc hd hH hH₃ hG2T hG3T hc1 hq
    hG1 hκ' hcP hG2P hG3P hκ hα m hm hmono hlam hHH₃ b
  have hone := (Finset.single_le_sum (f := fun Y' : Finset B =>
    ‖PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (mayerK μ (fun X : NePoly B => X.1) H) Y' -
      PY (shareBlock (Subtype.val : NePoly B → Finset B)) Subtype.val
        (mayerK μ (fun X : NePoly B => X.1) H₃) Y'‖ *
      Real.exp (κ' * (d Y' + cP) + lam * m Y')) (fun _ _ => by positivity)
    (Finset.mem_filter.2 ⟨Finset.mem_univ Y, hb⟩)).trans hsum
  rw [h23, Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  exact hone


end Mayer

end Balaban.Polymer
