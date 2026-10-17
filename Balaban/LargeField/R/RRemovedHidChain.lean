/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidTube

/-!
# The weight of the operator of a quiet window with the shell indicators separated (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstructions (1), (5).  `window_chain_le`: the weight of the
operator of `Z` along a quiet window (`locOp_absW_le_chain` with the bound `absW_quiet_le` of every step) is
at most the product of the Gaussian products of the steps, times `exp (B_w)` times the indicator that all
the shell conditions of the steps hold, times the product of the weights of the core operators.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Chain

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The weight of the operator along a quiet window, shells separated.**  `TB k Z' o x` is the shell
condition of the step `k → k + 1` of `Z'` (`hTB`), `cst k Z'` the exponent of its constant, `Bst` the bound of
`absW_quiet_le` (`hBst`); `bw0` bounds the sum of the exponents over the steps of the window. -/
theorem window_chain_le {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hQuiet : ∀ j, k1 ≤ j → j ≤ m' → ∀ c' : H.Comp (j + 1), H.Desc (j + 1) (m' + 1) c' Z →
      IsQuiet (H.locRH (j + 1) c') j c'.1)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 ≤ cs.delta k) (hdL : 1 ≤ S.d * S.L) (hβ : ∀ k, 0 ≤ cs.beta k)
    (haw : ∀ n, 0 ≤ cs.aw n) (hμ : ∀ k, 0 ≤ cs.muAct k)
    (r : ℕ → ℝ) (hr : ∀ k, r k = 3 * (S.d : ℝ) * S.L * cs.delta k)
    (TB : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → Prop)
    (hTB : ∀ k Z' o x, TB k Z' o x ↔
      ((∀ y : {y : BlockAt S n M K (k + 1) //
          y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
            newOutP (H.localHistory M K (k + 1) Z') k y},
        |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| < r k) ∧
      (∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
        |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
          r k)))
    (cst : ∀ (k : ℕ), H.Comp (k + 1) → ℝ)
    (hcst : ∀ k Z', cst k Z' = (cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
      volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
        z ∉ (H.localHistory M K (k + 1) Z').Z k})
    (bw0 : ℝ)
    (hbw0 : cst m' Z + ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ∑ c : ↥(H.parts (j.1 + 1) P.1), cst j.1 c.1 ≤ bw0)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.absW o x hv g ≤
      (ENNReal.ofReal (gaussProd N (H.localHistory M K (m' + 1) Z) m' cs o
          (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x)) *
        (∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∏ c : ↥(H.parts (j.1 + 1) P.1),
            ENNReal.ofReal (gaussProd N (H.localHistory M K (j.1 + 1) c.1) j.1 cs
              (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))))) *
      (ENNReal.ofReal (Real.exp bw0) *
        (if (TB m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)),
            TB j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) then 1 else 0)) *
      ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
        (locOp geo cs SD KD hH lab k1
          ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
          (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
          (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g := by
  classical
  let Bst : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → ℝ≥0∞ := fun k Z' o x =>
    ENNReal.ofReal (Real.exp (cst k Z')) * (if TB k Z' o x then 1 else 0)
  have hBst : ∀ j, k1 ≤ j ∧ j ≤ m' → ∀ (c' : H.Comp (j + 1)), H.Desc (j + 1) (m' + 1) c' Z →
      j + 1 ≤ K → ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
        (SD.ker j (H.localHistory M K (j + 1) c')).absW o x hv g ≤
          ENNReal.ofReal (gaussProd N (H.localHistory M K (j + 1) c') j cs o x) *
            Bst j c' o x := by
    intro j hj c' hd hjK o x hv g hg
    have h1 := absW_quiet_le geo cs SD (by omega : 1 ≤ j) hjK hH c'
      (hQuiet j hj.1 hj.2 c' hd) (hz j) (hc j) (hδ j) hdL (hβ (j + 1)) haw (hμ (j + 1)) o x hv g hg
    refine h1.trans (le_of_eq ?_)
    simp only [Bst]
    rw [← hr j, hcst j c', ite_zero_mul_ite_zero, mul_one]
    exact congrArg _ (congrArg _ (if_congr (hTB j c' o x).symm rfl rfl))
  have hch := locOp_absW_le_chain geo cs SD KD hk1 hm Z hq Bst hBst ρ hρ o x hv g hg
  refine hch.trans ?_
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
  have hBle : ∀ k Z' o x, Bst k Z' o x ≤ ENNReal.ofReal (Real.exp (cst k Z')) := by
    intro k Z' o x
    simp only [Bst]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact zero_le
  have hexp : ∀ {ι : Type} [Fintype ι] (f : ι → ℝ),
      ∏ i, ENNReal.ofReal (Real.exp (f i)) = ENNReal.ofReal (Real.exp (∑ i, f i)) := by
    intro ι _ f
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  split_ifs with hT
  · rw [mul_one]
    calc _ ≤ ENNReal.ofReal (Real.exp (cst m' Z)) * ∏ j : ↥(Finset.Ico k1 m'),
          ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ∏ c : ↥(H.parts (j.1 + 1) P.1),
            ENNReal.ofReal (Real.exp (cst j.1 c.1)) :=
          mul_le_mul' (hBle _ _ _ _) (Finset.prod_le_prod fun j _ => Finset.prod_le_prod fun P _ =>
            Finset.prod_le_prod fun c _ => hBle _ _ _ _)
      _ = ENNReal.ofReal (Real.exp (cst m' Z + ∑ j : ↥(Finset.Ico k1 m'),
          ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ∑ c : ↥(H.parts (j.1 + 1) P.1),
            cst j.1 c.1)) := by
          simp_rw [hexp, Real.exp_add]
          rw [ENNReal.ofReal_mul (Real.exp_pos _).le]
      _ ≤ ENNReal.ofReal (Real.exp bw0) :=
          ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hbw0)
  · rw [mul_zero]
    refine le_of_eq ?_
    rw [not_and_or] at hT
    rcases hT with h | h
    · have : Bst m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) = 0 := by
        simp only [Bst, h, ↓reduceIte, mul_zero]
      rw [this, zero_mul]
    · push Not at h
      obtain ⟨j, P, c, hc'⟩ := h
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ P)
        (Finset.prod_eq_zero (Finset.mem_univ c) (by simp only [Bst, hc', ↓reduceIte, mul_zero]))), mul_zero]

end Chain

end Balaban.LargeField
