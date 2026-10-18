/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomRotate

/-!
# Correcting the determinant of an anisotropic tube witness

A reflection in a transverse coordinate fixes the polydisc centre. Composing it on the left of
a determinant-negative witness keeps the rotated datum in the polydisc and produces `IsCRot`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.SmallField Balaban.SmallField.Def6

variable {d N : ℕ} {S : Finset (Site d)} {i₀ i₁ : Fin N} {ν r : ℝ}

/-- Every tube witness can be chosen in the complex rotation class of the rotation step,
provided there is a transverse coordinate. -/
theorem tubeAniso_witness_isCRot (hne : i₁ ≠ i₀) {c : Cfg d N S}
    (hc : c ∈ TubeAniso i₀ ν r S) :
    ∃ R : Matrix (Fin N) (Fin N) ℂ,
      IsCRot R ∧ EntryBd N R ∧ rotCfgL R S c ∈ polyAniso i₀ ν r S := by
  obtain ⟨R, hR, hRb, hRc⟩ := hc
  rcases det_isOrth hR with hd | hd
  · exact ⟨R, ⟨hR, Or.inr hd⟩, hRb, hRc⟩
  · let Pm := reflP N i₁
    let R' := Pm * R
    have hP : IsOrth Pm := (isRot_reflP i₁).1
    have hR' : IsOrth R' := by
      unfold IsOrth R'
      rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Pm.transpose,
        hP, Matrix.one_mul, hR]
    have hdet : R'.det = 1 := by
      rw [show R' = Pm * R from rfl, Matrix.det_mul]
      simp only [Pm, reflP_det, hd]
      ring
    have hRb' : EntryBd N R' := by
      intro i k
      change ‖(Pm * R) i k‖ ≤ rotBound N
      simp only [Pm, reflP, Matrix.diagonal_mul]
      by_cases hi : i = i₁
      · subst i
        simpa using hRb i₁ k
      · simpa [hi] using hRb i k
    have hRc' : rotCfgL R' S c ∈ polyAniso i₀ ν r S := by
      rw [show R' = Pm * R from rfl, rotCfgL_mul]
      exact rotCfgL_reflP_mem_polyAniso hne hRc
    exact ⟨R', ⟨hR', Or.inr hdet⟩, hRb', hRc'⟩

end Balaban.SmallField.Def6v2
