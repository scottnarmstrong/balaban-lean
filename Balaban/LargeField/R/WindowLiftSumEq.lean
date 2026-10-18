/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowLiftSum

/-!
# The sum over the pieces of the window point in explicit form

The sum of the main actions over the family `Option (Σ j, Σ P, ↥(parts))` of the pieces of
`window_sum_pt` is the main action of the top piece plus the triple sum over the pieces
`(j, P, c)`, `k₁ ≤ j < m'`, the form in which `window_sum_pt` and `window_hbG` state it.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory Balaban.SmallField

section SumEq

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The sum of the main actions of the pieces of the window point, in explicit form**
(the left side of `window_sum_pt`). -/
theorem window_pieces_sum_eq {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ou : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), OutT N R (H.localHistory M K ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1))
    (xu : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), NewCfg N (H.localHistory M K ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1)
    (hou0 : ou none = o)
    (hxu0 : xu none = newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (Nat.lt_succ_of_le hk1) Z (Desc.refl Z))) x)
    (hou1 : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), ou (some ⟨j, P, c⟩) = ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
    (hxu1 : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), xu (some ⟨j, P, c⟩) =
        newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) :
    ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), mainActionLoc geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2.1
        (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) cs (locRH_rem ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2) (ou i) (xu i) hv =
      mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
        (locRH_rem (m' + 1) Z) o (newRestrict (H.localHistory M K (m' + 1) Z)
          (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (Nat.lt_succ_of_le hk1) Z (Desc.refl Z)))
          x) hv +
        ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
          ∑ c : ↥(H.parts (j.1 + 1) P.1),
            mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
              (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
              (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
              (ancOut (N := N) (R := R) c.1 P.1
                (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
                  (mem_ancFin.mp P.2) x))
              (newRestrict (H.localHistory M K (j.1 + 1) c.1)
                (newVars_sub_locOp_A geo cs SD KD
                  ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
                  (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                    (desc_of_parts c.2 (mem_ancFin.mp P.2))))
                (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
                  (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv := by
  classical
  rw [Fintype.sum_option, Fintype.sum_sigma]
  refine congrArg₂ (· + ·) ?_ ?_
  · show mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
      (locRH_rem (m' + 1) Z) (ou none) (xu none) hv = _
    rw [hou0, hxu0]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun c _ => ?_
    show mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
      (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
      (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
      (ou (some ⟨j, P, c⟩)) (xu (some ⟨j, P, c⟩)) hv = _
    rw [hou1 j P c, hxu1 j P c]

end SumEq

end Balaban.LargeField
