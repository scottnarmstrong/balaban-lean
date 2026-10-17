/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainSplit
public import Balaban.LargeField.Operators.QuietBound

/-!
# The weight of a quiet step keeps the factor `e^{-𝒜}` of the main action (W936)

`notes/phase1/LF4R-PLAN.md` §8.  `quietRest_le_exp`: `quietRest ≤ e^{-𝒜_{k+1}(Z'; ψ)}` (every other factor
is an indicator); `absW_quiet_le_action`: the weight of a quiet step is at most its Gaussian product
times `e^{-𝒜}` times the bound of `absW_quiet_le`.  The factor `e^{-𝒜}` is the step's part of
`e^{-𝒜_win}` of P7 (2.58′); `absW_quiet_le` is the case `e^{-𝒜} ≤ 1`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section QuietAct

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ}
  (g : Geo S n R M) (Hl : RegionHistory S n R k0 K) (k : ℕ) (Zc : Finset (Torus S.d (n (k + 1))))
  (hZc : Zc ∈ comps (S.omega (k + 1)) (Hl.F.Zp (k + 1))) (hk : k + 1 ≤ K) (cs : OpConsts)
  (hrem : ∀ j, Hl.rem j = ∅)

open Classical in
theorem quietRest_le_exp (o : OutT N R (locHist Hl M K (k + 1) Zc) (k + 1))
    (x : NewCfg N (locHist Hl M K (k + 1) Zc) k) (hv : EuclideanSpace ℝ (Fin N)) :
    quietRest g Hl k Zc hZc hk cs hrem o x hv ≤
      Real.exp (-mainActionLoc g Hl k Zc hZc hk cs hrem o x hv) := by
  unfold quietRest
  refine mul_le_of_le_one_left (Real.exp_pos _).le ?_
  refine (unit_mul (unit_mul (unit_mul (unit_mul (unit_mul ?_ ?_) ?_) ?_) ?_) ?_).2
  · exact cubeProd_unit (fun y x => ⟨by unfold chiK; exact charFn_nonneg' _ _,
      by unfold chiK; exact charFn_le_one' _ _⟩) _ _
  · exact cubeProd_unit (fun y x => ⟨by unfold chiPrimeNew; exact charFn_nonneg' _ _,
      by unfold chiPrimeNew; exact charFn_le_one' _ _⟩) _ _
  · exact cubeProd_unit (fun y x => ⟨by unfold chiPrimeNew; exact charFn_nonneg' _ _,
      by unfold chiPrimeNew; exact charFn_le_one' _ _⟩) _ _
  · exact cubeProd_unit (fun y x => ⟨by unfold chiNext chiK; exact charFn_nonneg' _ _,
      by unfold chiNext chiK; exact charFn_le_one' _ _⟩) _ _
  · unfold chiNew; exact ⟨charFn_nonneg' _ _, charFn_le_one' _ _⟩
  · split_ifs <;> norm_num

end QuietAct

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs : ℕ → LocalHistory S n M K → ℝ}
  (SD : StepData k0 geo cs N κs)

open Classical in
/-- **The weight of a quiet step with the action factor kept.**  On `g ∈ l1Ball`, the
weight `K e^{Re b}` of a quiet step is at most `gaussProd` times
`e^{-𝒜_{k+1}(Z'; ψ)} · exp ((C_b log β_k + C_b B_0) volScale) · 1[new outputs in the shell] · 1[new′ variables in the shell]`:
the second factor reads neither the Gaussian blocks nor any node variable. -/
theorem absW_quiet_le_action {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ K) (hadm : H.Admissible)
    (Z' : H.Comp (k + 1)) (hQ : IsQuiet (H.locRH (k + 1) Z') k Z'.1) (hz : 0 ≤ cs.z (k + 1))
    (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (hδ : 0 ≤ cs.delta k)
    (hdL : 1 ≤ S.d * S.L)
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    (SD.ker k (H.localHistory M K (k + 1) Z')).absW o x hv g ≤
      ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs o x) *
        (ENNReal.ofReal (Real.exp (-mainActionLoc geo (H.locRH (k + 1) Z') k Z'.1
            (locComp_mem H hk Z') hk cs (locRH_rem (k + 1) Z') o x hv)) *
          ENNReal.ofReal (Real.exp ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
            volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
              z ∉ (H.localHistory M K (k + 1) Z').Z k})) *
          ((if ∀ y : {y : BlockAt S n M K (k + 1) //
              y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
                newOutP (H.localHistory M K (k + 1) Z') k y},
              |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| <
                3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0) *
           (if ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
              |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
                3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0))) := by
  rw [absW_quiet_split geo cs SD hk hadm Z' hQ hz hc o x hv g]
  refine mul_le_mul' le_rfl ?_
  by_cases hchi : ChiNewAt geo cs H k Z' o x
  · have hunit := quietRest_le_exp (N := N) geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
      (locRH_rem (k + 1) Z') o x hv
    have h2 : Real.exp ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g).re ≤
        Real.exp ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
          volScale S (k + 1) {z | z ∈ (H.localHistory M K (k + 1) Z').Z (k + 1) ∧
            z ∉ (H.localHistory M K (k + 1) Z').Z k}) :=
      Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans
        (SD.b_bound H hadm k Z' o x hv g hg hchi))
    have hI1 : (if ∀ y : {y : BlockAt S n M K (k + 1) //
        y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
          newOutP (H.localHistory M K (k + 1) Z') k y},
        |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| <
          3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0) = 1 := by
      have hall : ∀ y : {y : BlockAt S n M K (k + 1) //
          y ∈ Vblk R (H.localHistory M K (k + 1) Z') (k + 1) ∧
            newOutP (H.localHistory M K (k + 1) Z') k y},
          |‖restrictOutPart o (newOutP (H.localHistory M K (k + 1) Z') k) y‖ ^ 2 - 1| <
            3 * (S.d : ℝ) * S.L * cs.delta k := by
        intro y
        have := shell_newOut geo cs hk Z' o x hchi y.1 y.2.2
        simpa [restrictOutPart, outField, y.2.1] using this
      simp only [hall, implies_true, ↓reduceIte]
    have hI2 : (if ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
        |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
          3 * (S.d : ℝ) * S.L * cs.delta k then (1 : ℝ≥0∞) else 0) = 1 := by
      have hall : ∀ p : ↥(newPrimeVars (H.localHistory M K (k + 1) Z') k),
          |‖VarVal.toEuc (restrictSub (newPrimeVars_sub (H.localHistory M K (k + 1) Z') k) x p)‖ ^ 2 - 1| <
            3 * (S.d : ℝ) * S.L * cs.delta k := fun p =>
        shell_newPrime geo cs hk hk1 hδ hdL Z' hQ o x hchi p.1 p.2
      simp only [hall, implies_true, ↓reduceIte]
    rw [hI1, hI2, mul_one, mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    exact mul_le_mul hunit (h2) (Real.exp_pos _).le (Real.exp_pos _).le
  · have hz0 := quietRest_eq_zero geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
      (locRH_rem (k + 1) Z') o x hv hchi
    rw [hz0, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end Bound

end Balaban.LargeField
