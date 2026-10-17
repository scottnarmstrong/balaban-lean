/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainSplit
public import Balaban.LargeField.Operators.QuietBound

/-!
# The weight of a quiet step is bounded uniformly in the Gaussian variables (W923)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, item (3).  For a quiet step the weight is at most the
Gaussian product times a bound that does not read the Gaussian blocks: the constant
`exp ((C_b log β_k + C_b B_0) |Z^c_k ∩ Z'|_{k+1})` times the indicators of the shells of the new′ and the
new output variables (`absW_quiet_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs : ℕ → LocalHistory S n M K → ℝ}
  (SD : StepData k0 geo cs N κs)

open Classical in
/-- **The weight of a quiet step, bounded uniformly in the Gaussian variables.**  On `g ∈ l1Ball`, the
weight `K e^{Re b}` of a quiet step is at most `gaussProd` times
`exp ((C_b log β_k + C_b B_0) volScale) · 1[new outputs in the shell] · 1[new′ variables in the shell]`:
the second factor reads neither the Gaussian blocks nor any node variable. -/
theorem absW_quiet_le {k : ℕ} (hk1 : 1 ≤ k) (hk : k + 1 ≤ K) (hadm : H.Admissible)
    (Z' : H.Comp (k + 1)) (hQ : IsQuiet (H.locRH (k + 1) Z') k Z'.1) (hz : 0 ≤ cs.z (k + 1))
    (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (hδ : 0 ≤ cs.delta k)
    (hdL : 1 ≤ S.d * S.L) (hβ : 0 ≤ cs.beta (k + 1)) (haw : ∀ n, 0 ≤ cs.aw n)
    (hμ : 0 ≤ cs.muAct (k + 1))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) (hg : g ∈ l1Ball (GIdx S n M K N)) :
    (SD.ker k (H.localHistory M K (k + 1) Z')).absW o x hv g ≤
      ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs o x) *
        (ENNReal.ofReal (Real.exp ((cs.Cb * Real.log (cs.beta k) + cs.Cb * cs.B0) *
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
  gcongr
  by_cases hchi : ChiNewAt geo cs H k Z' o x
  · have hunit := quietRest_unit (N := N) geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
      (locRH_rem (k + 1) Z') hβ haw hμ o x hv
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
    rw [hI1, hI2, mul_one, mul_one]
    refine ENNReal.ofReal_le_ofReal ?_
    calc _ ≤ 1 * Real.exp ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g).re :=
          mul_le_mul_of_nonneg_right hunit.2 (Real.exp_pos _).le
      _ ≤ _ := by rw [one_mul]; exact h2
  · have hz0 := quietRest_eq_zero geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
      (locRH_rem (k + 1) Z') o x hv hchi
    rw [hz0, zero_mul, ENNReal.ofReal_zero]
    exact zero_le

end Bound

section Chain

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The weight of the operator of `Z` along a quiet window, bounded uniformly in the Gaussian
variables.**  Let `Bst` bound the weight of every quiet step of the window by its Gaussian product times
`Bst` (`hBst`, e.g. `absW_quiet_le`).  Then the weight of the operator of `Z` is at most the product of all
the Gaussian products of the steps of the window (the right-hand side of `gaussProd_unroll_eq`) times the
product of the `Bst` of the steps and of the weights of the core operators of the ancestors of scale `k₁`. -/
theorem locOp_absW_le_chain {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (Z : H.Comp (m' + 1))
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (Bst : ∀ (k : ℕ) (Z' : H.Comp (k + 1)),
      OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
        NewCfg N (H.localHistory M K (k + 1) Z') k → ℝ≥0∞)
    (hBst : ∀ j, k1 ≤ j ∧ j ≤ m' → ∀ (c' : H.Comp (j + 1)), H.Desc (j + 1) (m' + 1) c' Z →
      j + 1 ≤ K → ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
        (SD.ker j (H.localHistory M K (j + 1) c')).absW o x hv g ≤
          ENNReal.ofReal (gaussProd N (H.localHistory M K (j + 1) c') j cs o x) * Bst j c' o x)
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
      ((Bst m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x)) *
        ∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∏ c : ↥(H.parts (j.1 + 1) P.1),
            Bst j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) *
      ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
        (locOp geo cs SD KD hH lab k1
          ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
          (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
          (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g := by
  rw [locOp_absW_unroll geo cs SD KD k1 m' hk1 hm Z hq ρ hρ o x hv g]
  have htop := hBst m' ⟨hk1, le_rfl⟩ Z (Desc.refl Z) hm o
    (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv g hg
  have hanc : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)),
      (SD.ker j.1 (H.localHistory M K (j.1 + 1) c.1)).absW
        (ancOut c.1 P.1 (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
          (mem_ancFin.mp P.2) x))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD
            ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv g ≤
      ENNReal.ofReal (gaussProd N (H.localHistory M K (j.1 + 1) c.1) j.1 cs
        (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
          (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD
            ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) *
        Bst j.1 c.1 (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
            (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
          (newRestrict (H.localHistory M K (j.1 + 1) c.1)
            (newVars_sub_locOp_A geo cs SD KD
              ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
              (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2))))
            (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) := by
    intro j P c
    have hj := Finset.mem_Ico.mp j.2
    exact hBst j.1 ⟨hj.1, by omega⟩ c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2))
      ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm) _ _ hv g hg
  refine (mul_le_mul' (mul_le_mul' htop (Finset.prod_le_prod fun j _ =>
    Finset.prod_le_prod fun P _ => Finset.prod_le_prod fun c _ => hanc j P c)) le_rfl).trans ?_
  simp only [Finset.prod_mul_distrib]
  refine le_of_eq ?_
  ring

end Chain

end Balaban.LargeField
