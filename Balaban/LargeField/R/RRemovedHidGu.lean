/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedHidChain
public import Balaban.LargeField.R.RRemovedChainSplit

/-!
# The Gaussian products of the steps of a quiet window as one product over the Gaussian blocks (W929)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, obstruction (2).  `gchain_eq`: the product of the
`ENNReal.ofReal` of the Gaussian products of the steps in `window_chain_le` is `ENNReal.ofReal` of the product,
over the Gaussian blocks of all the ancestors, of the Gaussian factors in the fields `fld`, `ft`
(`gaussProd_unroll_eq`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Gu

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
theorem gchain_eq {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hz : ∀ k, 0 ≤ cs.z (k + 1)) (hc : ∀ k, 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
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
    (fld : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hfld : ∀ s y, fld s y = subVarField N x s y) (hft : ∀ y, ft y = outField N o y) :
    ENNReal.ofReal (gaussProd N (H.localHistory M K (m' + 1) Z) m' cs o
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
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)))) =
      ENNReal.ofReal
        ((∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
            ∃ c' ∈ H.ancFin (m' + 1) (m' + 1) Z,
              y ∈ gaussBlocks (H.localHistory M K (m' + 1) c') m'),
          cs.z (m' + 1) ^ N * gaussDens (cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
            (cs.z (m' + 1) • ft y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
                blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), fld m' y')) *
        ∏ j ∈ Finset.Ico k1 m',
          ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
              ∃ c' ∈ H.ancFin (j + 1) (m' + 1) Z,
                y ∈ gaussBlocks (H.localHistory M K (j + 1) c') j),
            cs.z (j + 1) ^ N * gaussDens (cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
              (cs.z (j + 1) • fld (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                  blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), fld j y')) := by
  have h1 := gaussProd_unroll_eq geo cs SD KD (hH := hH) (lab := lab) hk1 hm hq ρ hρ o x
  have hfld' : fld = fun s y => subVarField N x s y := funext fun s => funext fun y => hfld s y
  have hft' : ft = fun y => outField N o y := funext hft
  subst hfld' hft'
  rw [← h1, ENNReal.ofReal_mul (gaussProd_nonneg N _ m' cs (hz m') (hc m') o _),
    ENNReal.ofReal_prod_of_nonneg]
  congr 1
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [ENNReal.ofReal_prod_of_nonneg]
  refine Finset.prod_congr rfl fun P _ => ?_
  rw [ENNReal.ofReal_prod_of_nonneg]
  · intro c _
    exact gaussProd_nonneg N _ j.1 cs (hz j.1) (hc j.1) _ _
  · intro P _
    exact Finset.prod_nonneg fun c _ => gaussProd_nonneg N _ j.1 cs (hz j.1) (hc j.1) _ _
  · intro j _
    exact Finset.prod_nonneg fun P _ => Finset.prod_nonneg fun c _ =>
      gaussProd_nonneg N _ j.1 cs (hz j.1) (hc j.1) _ _

end Gu

end Balaban.LargeField
