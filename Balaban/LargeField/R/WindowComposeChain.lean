/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainBound
public import Balaban.LargeField.R.RRemovedHidChain

/-!
# The weight of a quiet window with the action factor kept (blocker 4, item S7)

`notes/phase1/LF4R-PLAN.md` §9.3, item S7.  `locOp_absW_le_chain_hv` is `locOp_absW_le_chain` for a step bound
`Bst` that depends on the external direction `h` (the main action `𝒜_{k+1}(Z'; ψ)` reads `h`).
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
/-- **The weight of the operator of `Z` along a quiet window, with the bound of the steps depending on `h`.**  Let `Bst` bound the weight of every quiet step of the window by its Gaussian product times
`Bst` (`hBst`, e.g. `absW_quiet_le`).  Then the weight of the operator of `Z` is at most the product of all
the Gaussian products of the steps of the window (the right-hand side of `gaussProd_unroll_eq`) times the
product of the `Bst` of the steps and of the weights of the core operators of the ancestors of scale `k₁`. -/
theorem locOp_absW_le_chain_hv {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    (Z : H.Comp (m' + 1))
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (Bst : ∀ (k : ℕ) (Z' : H.Comp (k + 1)),
      OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
        NewCfg N (H.localHistory M K (k + 1) Z') k → EuclideanSpace ℝ (Fin N) → ℝ≥0∞)
    (hBst : ∀ j, k1 ≤ j ∧ j ≤ m' → ∀ (c' : H.Comp (j + 1)), H.Desc (j + 1) (m' + 1) c' Z →
      j + 1 ≤ K → ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
        (SD.ker j (H.localHistory M K (j + 1) c')).absW o x hv g ≤
          ENNReal.ofReal (gaussProd N (H.localHistory M K (j + 1) c') j cs o x) * Bst j c' o x hv)
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
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv) *
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
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv) *
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
              (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv := by
    intro j P c
    have hj := Finset.mem_Ico.mp j.2
    exact hBst j.1 ⟨hj.1, by omega⟩ c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2))
      ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm) _ _ hv g hg
  refine (mul_le_mul' (mul_le_mul' htop (Finset.prod_le_prod fun j _ =>
    Finset.prod_le_prod fun P _ => Finset.prod_le_prod fun c _ => hanc j P c)) le_rfl).trans ?_
  simp only [Finset.prod_mul_distrib]
  refine le_of_eq ?_
  ring


open Classical in
/-- **The weight of the operator along a quiet window, shells separated.**  `TB k Z' o x` is the shell
condition of the step `k → k + 1` of `Z'` (`hTB`), `cst k Z'` the exponent of its constant, `Bst` the bound of
`absW_quiet_le` (`hBst`); `bw0` bounds the sum of the exponents over the steps of the window. -/
theorem window_chain_le_action {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K)
    {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hQuiet : ∀ j, k1 ≤ j → j ≤ m' → ∀ c' : H.Comp (j + 1), H.Desc (j + 1) (m' + 1) c' Z →
      IsQuiet (H.locRH (j + 1) c') j c'.1)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (hδ : ∀ k, 0 ≤ cs.delta k) (hdL : 1 ≤ S.d * S.L)
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
      (ENNReal.ofReal (Real.exp (-(mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
            (locRH_rem (m' + 1) Z) o (newRestrict (H.localHistory M K (m' + 1) Z)
              (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv +
          ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
            ∑ c : ↥(H.parts (j.1 + 1) P.1),
              mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
                (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
                (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
                (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
                  (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
                (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                  (newVars_sub_locOp_A geo cs SD KD
                    ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                    (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                      (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                  (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv))) *
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
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) then 1 else 0))) *
      ∏ P : ↥(H.ancFin (k1 + 1) (m' + 1) Z), ∏ C : ↥(H.parts k1 P.1),
        (locOp geo cs SD KD hH lab k1
          ((desc_of_parts C.2 (mem_ancFin.mp P.2)).le.trans hm) C.1).T.absW
          (ancOut C.1 P.1 (ρ (k1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x))
          (ρ k1 le_rfl C.1 (desc_of_parts C.2 (mem_ancFin.mp P.2)) x) hv g := by
  classical
  let Bsub : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → ℝ≥0∞ := fun k Z' o x =>
    ENNReal.ofReal (Real.exp (cst k Z')) * (if TB k Z' o x then 1 else 0)
  let Bst : ∀ (k : ℕ) (Z' : H.Comp (k + 1)), OutT N R (H.localHistory M K (k + 1) Z') (k + 1) →
      NewCfg N (H.localHistory M K (k + 1) Z') k → EuclideanSpace ℝ (Fin N) → ℝ≥0∞ :=
    fun k Z' o x hv => if hk : k + 1 ≤ K then
      ENNReal.ofReal (Real.exp (-(mainActionLoc geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') o x hv))) * Bsub k Z' o x else 0
  have hBst : ∀ j, k1 ≤ j ∧ j ≤ m' → ∀ (c' : H.Comp (j + 1)), H.Desc (j + 1) (m' + 1) c' Z →
      j + 1 ≤ K → ∀ o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
        (SD.ker j (H.localHistory M K (j + 1) c')).absW o x hv g ≤
          ENNReal.ofReal (gaussProd N (H.localHistory M K (j + 1) c') j cs o x) *
            Bst j c' o x hv := by
    intro j hj c' hd hjK o x hv g hg
    have h1 := absW_quiet_le_action geo cs SD (by omega : 1 ≤ j) hjK hH c'
      (hQuiet j hj.1 hj.2 c' hd) (hz j) (hc j) (hδ j) hdL o x hv g hg
    refine h1.trans (le_of_eq ?_)
    simp only [Bst, Bsub, hjK, ↓reduceDIte]
    rw [← hr j, hcst j c', ite_zero_mul_ite_zero, mul_one, mul_assoc]
    exact congrArg _ (congrArg _ (congrArg _ (if_congr (hTB j c' o x).symm rfl rfl)))
  have hch := locOp_absW_le_chain_hv geo cs SD KD hk1 hm Z hq Bst hBst ρ hρ o x hv g hg
  refine hch.trans ?_
  refine mul_le_mul' (mul_le_mul' le_rfl ?_) le_rfl
  have hBeq : ∀ k (Z' : H.Comp (k + 1)) (hk : k + 1 ≤ K) o x,
      Bst k Z' o x hv = ENNReal.ofReal (Real.exp (-(mainActionLoc geo (H.locRH (k + 1) Z') k Z'.1
        (locComp_mem H hk Z') hk cs (locRH_rem (k + 1) Z') o x hv))) * Bsub k Z' o x := by
    intro k Z' hk o x
    simp only [Bst, hk, ↓reduceDIte]
  have hBle : ∀ k Z' o x, Bsub k Z' o x ≤ ENNReal.ofReal (Real.exp (cst k Z')) := by
    intro k Z' o x
    simp only [Bsub]
    split_ifs
    · rw [mul_one]
    · rw [mul_zero]; exact zero_le
  have hexp : ∀ {ι : Type} [Fintype ι] (f : ι → ℝ),
      ∏ i, ENNReal.ofReal (Real.exp (f i)) = ENNReal.ofReal (Real.exp (∑ i, f i)) := by
    intro ι _ f
    rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => (Real.exp_pos _).le), ← Real.exp_sum]
  have hprod : ∀ {ι1 : Type} [Fintype ι1] {ι2 : ι1 → Type} [∀ a, Fintype (ι2 a)]
      {ι3 : ∀ a, ι2 a → Type} [∀ a b, Fintype (ι3 a b)] (A : ∀ a b, ι3 a b → ℝ)
      (Bs : ∀ a b, ι3 a b → ℝ≥0∞),
      ∏ a, ∏ b, ∏ c, (ENNReal.ofReal (Real.exp (-A a b c)) * Bs a b c) =
        ENNReal.ofReal (Real.exp (-(∑ a, ∑ b, ∑ c, A a b c))) * ∏ a, ∏ b, ∏ c, Bs a b c := by
    intro ι1 _ ι2 _ ι3 _ A Bs
    simp only [Finset.prod_mul_distrib]
    simp_rw [hexp, Finset.sum_neg_distrib]
  have hjK : ∀ j : ↥(Finset.Ico k1 m'), j.1 + 1 ≤ K := fun j => by
    have := (Finset.mem_Ico.mp j.2).2; omega
  let Oj : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), OutT N R (H.localHistory M K (j.1 + 1) c.1) (j.1 + 1) :=
    fun j P c => ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
      (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x)
  let Xj : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), NewCfg N (H.localHistory M K (j.1 + 1) c.1) j.1 :=
    fun j P c => newRestrict (H.localHistory M K (j.1 + 1) c.1)
      (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
        (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
          (desc_of_parts c.2 (mem_ancFin.mp P.2))))
      (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
        (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)
  let Aj : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), ℝ :=
    fun j P c => mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1 (locComp_mem H (hjK j) c.1)
      (hjK j) cs (locRH_rem (j.1 + 1) c.1) (Oj j P c) (Xj j P c) hv
  have hpieces : ∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ∏ c : ↥(H.parts (j.1 + 1) P.1), Bst j.1 c.1 (Oj j P c) (Xj j P c) hv =
      ENNReal.ofReal (Real.exp (-(∑ j : ↥(Finset.Ico k1 m'),
        ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ∑ c : ↥(H.parts (j.1 + 1) P.1), Aj j P c))) *
      ∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∏ c : ↥(H.parts (j.1 + 1) P.1), Bsub j.1 c.1 (Oj j P c) (Xj j P c) := by
    rw [← hprod Aj (fun j P c => Bsub j.1 c.1 (Oj j P c) (Xj j P c))]
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun P _ =>
      Finset.prod_congr rfl fun c _ => hBeq j.1 c.1 (hjK j) _ _
  show Bst m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv *
    ∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
      ∏ c : ↥(H.parts (j.1 + 1) P.1), Bst j.1 c.1 (Oj j P c) (Xj j P c) hv ≤
    ENNReal.ofReal (Real.exp (-(mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
            (locRH_rem (m' + 1) Z) o (newRestrict (H.localHistory M K (m' + 1) Z)
              (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv +
          ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
            ∑ c : ↥(H.parts (j.1 + 1) P.1), Aj j P c))) *
      (ENNReal.ofReal (Real.exp bw0) *
        (if (TB m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)), TB j.1 c.1 (Oj j P c) (Xj j P c)) then 1 else 0))
  have hmain : Bsub m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) *
      ∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∏ c : ↥(H.parts (j.1 + 1) P.1), Bsub j.1 c.1 (Oj j P c) (Xj j P c) ≤
      ENNReal.ofReal (Real.exp bw0) *
        (if (TB m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) ∧
          ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)), TB j.1 c.1 (Oj j P c) (Xj j P c)) then 1 else 0) := by
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
      · have : Bsub m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
            (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) = 0 := by
          simp only [Bsub, h, ↓reduceIte, mul_zero]
        rw [this, zero_mul]
      · push Not at h
        obtain ⟨j, P, c, hc'⟩ := h
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (Finset.prod_eq_zero (Finset.mem_univ P)
          (Finset.prod_eq_zero (Finset.mem_univ c) (by simp only [Bsub, hc', ↓reduceIte, mul_zero]))),
          mul_zero]
  rw [hpieces, hBeq m' Z hm, neg_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc _ = ENNReal.ofReal (Real.exp (-mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
            (locRH_rem (m' + 1) Z) o (newRestrict (H.localHistory M K (m' + 1) Z)
              (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv)) *
          ENNReal.ofReal (Real.exp (-(∑ j : ↥(Finset.Ico k1 m'),
            ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ∑ c : ↥(H.parts (j.1 + 1) P.1), Aj j P c))) *
        (Bsub m' Z o (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) *
        ∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∏ c : ↥(H.parts (j.1 + 1) P.1), Bsub j.1 c.1 (Oj j P c) (Xj j P c)) := by ring
    _ ≤ _ := mul_le_mul' le_rfl hmain

end Chain

end Balaban.LargeField
