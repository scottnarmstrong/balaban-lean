/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRemovedChainLevel
public import Balaban.LargeField.Operators.QuietInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The weight of a quiet step: Gaussian factor times the rest (W918)

`notes/phase1/LF4R-PLAN.md`, leaf 6, blocker 4, items (b), (c).  The weight `K e^{Re b}` of a quiet step
kernel is the Gaussian product `gaussProd` times `quietRest e^{Re b}` (`absW_quiet_split`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale RegionHistory ENNReal

section Split

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs : ℕ → LocalHistory S n M K → ℝ}
  (SD : StepData k0 geo cs N κs)

/-- **The weight of a quiet step**: `K e^{Re b} = (∏ z^N t_k) · (quietRest e^{Re b})`. -/
theorem absW_quiet_split {k : ℕ} (hk : k + 1 ≤ K) (hadm : H.Admissible) (Z' : H.Comp (k + 1))
    (hQ : IsQuiet (H.locRH (k + 1) Z') k Z'.1) (hz : 0 ≤ cs.z (k + 1))
    (hc : 0 ≤ cs.beta k * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
    (o : OutT N R (H.localHistory M K (k + 1) Z') (k + 1))
    (x : NewCfg N (H.localHistory M K (k + 1) Z') k) (hv : EuclideanSpace ℝ (Fin N))
    (g : GIdx S n M K N → ℂ) :
    (SD.ker k (H.localHistory M K (k + 1) Z')).absW o x hv g =
      ENNReal.ofReal (gaussProd N (H.localHistory M K (k + 1) Z') k cs o x) *
        ENNReal.ofReal (quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
          (locRH_rem (k + 1) Z') o x hv *
          Real.exp ((SD.ker k (H.localHistory M K (k + 1) Z')).b o x hv g).re) := by
  have hK : (SD.ker k (H.localHistory M K (k + 1) Z')).K o x hv =
      gaussProd N (H.localHistory M K (k + 1) Z') k cs o x *
        quietRest geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
          (locRH_rem (k + 1) Z') o x hv :=
    (SD.quiet H hadm k hk Z' hQ o x hv).trans
      (quietKernel_eq geo (H.locRH (k + 1) Z') k Z'.1 (locComp_mem H hk Z') hk cs
        (locRH_rem (k + 1) Z') o x hv)
  unfold LFKernel.absW
  rw [hK, mul_assoc, ENNReal.ofReal_mul (gaussProd_nonneg N _ k cs hz hc o x)]

end Split

section Unroll

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **(b) The Gaussian factors of the quiet steps of a window, as one product over the Gaussian
blocks.**  Along a quiet window `[k₁, m' + 1)` of `Z`, the Gaussian product of the step kernel of `Z`
times the Gaussian products of the step kernels of its ancestors of scales `k₁ < j + 1 ≤ m'` (the
Gaussian factors appearing in `locOp_absW_unroll`) is the product, over the Gaussian blocks `y` of all
ancestors of scale `j + 1`, `k₁ ≤ j ≤ m'`, of `z_{j+1}^N g_{c_j}(z_{j+1} ψ_{j+1}(y) - L^{-d} ∑_{y'} ψ_j(y'))`,
with `ψ_{m'+1} = o` and every other field `ψ_s(y) = ` `subVarField x s y` read from the variables of
`Z` (the variables of the ancestors are among them). -/
theorem gaussProd_unroll_eq {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A) :
    gaussProd N (H.localHistory M K (m' + 1) Z) m' cs o
        (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) *
      (∏ j : ↥(Finset.Ico k1 m'), ∏ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∏ c : ↥(H.parts (j.1 + 1) P.1),
          gaussProd N (H.localHistory M K (j.1 + 1) c.1) j.1 cs
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
              (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) =
      (∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (m' + 1) =>
          ∃ c ∈ H.ancFin (m' + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (m' + 1) c) m'),
        cs.z (m' + 1) ^ N * gaussDens (cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
          (cs.z (m' + 1) • outField N o y - ((S.L : ℝ) ^ S.d)⁻¹ •
            ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
              blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), subVarField N x m' y')) *
      ∏ j ∈ Finset.Ico k1 m',
        ∏ y ∈ Finset.univ.filter (fun y : BlockAt S n M K (j + 1) =>
            ∃ c ∈ H.ancFin (j + 1) (m' + 1) Z, y ∈ gaussBlocks (H.localHistory M K (j + 1) c) j),
          cs.z (j + 1) ^ N * gaussDens (cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
            (cs.z (j + 1) • subVarField N x (j + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
              ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j =>
                blockMap S.L (M * n K * S.L ^ (K - (j + 1))) y' = y), subVarField N x j y') := by
  congr 1
  · rw [gaussProd_top_read geo cs SD KD hk1 hm hq o x]
    exact prod_gauss_top (β := ℝ) Z (fun y => cs.z (m' + 1) ^ N *
      gaussDens (cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
        (cs.z (m' + 1) • outField N o y - ((S.L : ℝ) ^ S.d)⁻¹ •
          ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K m' =>
            blockMap S.L (M * n K * S.L ^ (K - (m' + 1))) y' = y), subVarField N x m' y'))
  · rw [← Finset.prod_coe_sort (Finset.Ico k1 m')]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hj := (Finset.mem_Ico.mp j.2)
    have h1 : ∀ (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z)) (c : ↥(H.parts (j.1 + 1) P.1)),
        gaussProd N (H.localHistory M K (j.1 + 1) c.1) j.1 cs
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1)
              (by omega) P.1 (mem_ancFin.mp P.2) x))
            (newRestrict (H.localHistory M K (j.1 + 1) c.1)
              (newVars_sub_locOp_A geo cs SD KD
                ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                (hq (j.1 + 1) (by omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2))))
              (ρ (j.1 + 1) (by omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) =
          ∏ y : ↥(gaussBlocks (H.localHistory M K (j.1 + 1) c.1) j.1),
            cs.z (j.1 + 1) ^ N * gaussDens (cs.beta j.1 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
              (cs.z (j.1 + 1) • subVarField N x (j.1 + 1) y.1 - ((S.L : ℝ) ^ S.d)⁻¹ •
                ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j.1 =>
                  blockMap S.L (M * n K * S.L ^ (K - (j.1 + 1))) y' = y.1), subVarField N x j.1 y') :=
      fun P c => gaussProd_anc_read geo cs SD KD (hH := hH) (lab := lab) (by omega : k1 ≤ j.1) hm hq
        (mem_ancFin.mp P.2) c.2 x
        (ρ (j.1 + 1 + 1) (by omega) P.1 (mem_ancFin.mp P.2) x)
        (fun p => hρ _ _ _ _ _ p)
        (ρ (j.1 + 1) (by omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)
        (fun p => hρ _ _ _ _ _ p)
    simp_rw [h1]
    exact prod_gauss_level (β := ℝ) (j := j.1) (m := m' + 1) (by omega) (by omega) Z
      (fun y => cs.z (j.1 + 1) ^ N * gaussDens (cs.beta j.1 * cs.aKer * (S.L : ℝ) ^ (S.d - 2))
        (cs.z (j.1 + 1) • subVarField N x (j.1 + 1) y - ((S.L : ℝ) ^ S.d)⁻¹ •
          ∑ y' ∈ Finset.univ.filter (fun y' : BlockAt S n M K j.1 =>
            blockMap S.L (M * n K * S.L ^ (K - (j.1 + 1))) y' = y), subVarField N x j.1 y'))

end Unroll

end Balaban.LargeField
