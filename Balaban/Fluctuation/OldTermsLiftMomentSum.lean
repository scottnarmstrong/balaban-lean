/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftMoment

/-!
# The inherited finite-torus moment

Analyticity at the reference field allows the slice comparison of second
derivatives. The finite sum then reindexes along the physical-site equivalence.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.SmallField Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- The full second-moment sum is invariant under the old-torus equivalence,
provided the full energy is analytic at the reference field on both sides. -/
theorem liftOldTerms_momentSum (m₀ j : ℕ)
    (Tm : Terms d L (L * N₁) m₁ k N ϱ) (i₀ i₁ : Fin N)
    (hAnNew : AnalyticAt ℂ
      (fun ψ : Fld d L N₁ m₁ (k + 1) N =>
        Edens m₀ (liftOldTerms Tm) j ψ
          (constFld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
            (Pi.single i₀ 1)))
      (constFld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
        (Pi.single i₀ 1)))
    (hAnOld : AnalyticAt ℂ
      (fun ψ : Fld d L (L * N₁) m₁ k N =>
        Edens m₀ Tm j ψ
          (constFld (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
            (Pi.single i₀ 1)))
      (constFld (d := d) (L := L) (N₁ := L * N₁) (m₁ := m₁) (k := k)
        (Pi.single i₀ 1))) :
    momentSum m₀ (liftOldTerms Tm) j i₀ i₁ = momentSum m₀ Tm j i₀ i₁ := by
  classical
  have hsum :
      (∑ x ∈ (Finset.univ : Finset (CTorus d L (L * N₁) m₁ k)).filter
          (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L (L * N₁) m₁ k N =>
          Edens m₀ Tm j ψ (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1))
          (blockDir L j x i₁) (blockDir L j 0 i₁) * (liftSq L j x : ℂ)) =
      (∑ x ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1))).filter
          (Aligned (L ^ j)),
        D2 (fun ψ : Fld d L N₁ m₁ (k + 1) N =>
          Edens m₀ (liftOldTerms Tm) j ψ (constFld (Pi.single i₀ 1)))
          (constFld (Pi.single i₀ 1))
          (blockDir L j x i₁) (blockDir L j 0 i₁) * (liftSq L j x : ℂ)) := by
    refine Finset.sum_equiv oldTorusEquiv (fun x => ?_) fun x _ => ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (oldTorusEquiv_aligned_iff j x).symm
    · have hAnOld' : AnalyticAt ℂ
          (fun ψ : Fld d L (L * N₁) m₁ k N =>
            Edens m₀ Tm j ψ
              (lowerNewField (constFld (d := d) (L := L) (N₁ := N₁)
                (m₁ := m₁) (k := k + 1) (Pi.single i₀ 1))))
          (lowerNewField (constFld (d := d) (L := L) (N₁ := N₁)
            (m₁ := m₁) (k := k + 1) (Pi.single i₀ 1))) := by
        simpa only [lowerNewField_constFld] using hAnOld
      have hD := liftOldTerms_D2 m₀ j Tm
        (constFld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
          (Pi.single i₀ 1))
        (constFld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1)
          (Pi.single i₀ 1))
        (blockDir L j (oldTorusEquiv x) i₁)
        (blockDir L j 0 i₁) hAnNew hAnOld'
      have hw : lowerNewField (blockDir L j
          (0 : CTorus d L N₁ m₁ (k + 1)) i₁) =
          blockDir L j (0 : CTorus d L (L * N₁) m₁ k) i₁ := by
        simpa only [oldTorusEquiv_zero] using
          (lowerNewField_blockDir (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
            j (0 : CTorus d L (L * N₁) m₁ k) i₁)
      simp only [lowerNewField_constFld, lowerNewField_blockDir, hw] at hD
      rw [oldTorusEquiv_liftSq]
      exact congrArg (fun z : ℂ => z * (liftSq L j x : ℂ)) hD.symm
  exact hsum.symm

end Balaban.Fluctuation
