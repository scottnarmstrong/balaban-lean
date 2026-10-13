/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivPermute
public import Balaban.Localization.DecEquivTranslateStep

/-!
# A coordinate permutation at the top level set of the level step

At `lvTop 3 m₁ k ϱ` (`d = 3`) the transposition `swap 0 1` of the coordinates acts on the torus
by a map `coordPerm (swap 0 1)` different from the identity (`swap_ne_one`); the three symmetry
structures are inhabited there (`permuteLvTop_nonempty`), as they are at the composite of the
translation `stepVec` followed by the transposition (`composeLvTop_nonempty`).  Covariance of the
decoupled background field at both is `decBg_permute_lvTop` and `decBg_compose_lvTop`.  Covariance
of the output terms of the step is not proved.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Inhabited
  Balaban.Inhabited.LevelStep Finset

section Step

variable (m₁ k : ℕ)

/-- The transposition of the first two coordinates. -/
def swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

/-- The coordinate swap is not the identity of the step torus. -/
theorem swap_ne_one :
    (coordPerm (swap01) : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 := by
  intro h
  have h' := congrArg (fun σ : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1)) =>
    (σ (Pi.single 0 (stepVec m₁ k 0))) 0) h
  have e : (swap01).symm 0 = 1 := by decide
  simp only [coordPerm, Equiv.coe_fn_mk, Function.comp_apply, e, Equiv.Perm.coe_one, id_eq,
    Pi.single_apply] at h'
  simp at h'
  have h0 := stepVec_val m₁ k 0
  rw [← h', ZMod.val_zero] at h0
  exact (pow_pos (by norm_num : (0:ℕ) < 3) _).ne h0

variable (ϱ : ℝ) [NeZero (3 : ℕ)]

theorem permuteLvTop_nonempty :
    Nonempty (LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ) (coordPerm swap01)) ∧
    Nonempty (CoverSymm (coverOf (lvTop 3 m₁ k ϱ)) (coordPerm swap01)) ∧
    Nonempty (BlockSymm (lvTop 3 m₁ k ϱ) (coordPerm swap01)) :=
  ⟨⟨LatSymm.ofCoordPermLevel isLevel_lvTop _⟩, ⟨CoverSymm.ofCoordPerm isLevel_lvTop _⟩,
    ⟨BlockSymm.ofCoordPerm isLevel_lvTop _⟩⟩

/-- The translation `stepVec` followed by the coordinate swap: the three structures are inhabited. -/
theorem composeLvTop_nonempty :
    Nonempty (LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ)
      ((Equiv.addRight (stepVec m₁ k)).trans (coordPerm swap01))) ∧
    Nonempty (CoverSymm (coverOf (lvTop 3 m₁ k ϱ))
      ((Equiv.addRight (stepVec m₁ k)).trans (coordPerm swap01))) ∧
    Nonempty (BlockSymm (lvTop 3 m₁ k ϱ)
      ((Equiv.addRight (stepVec m₁ k)).trans (coordPerm swap01))) := by
  have hdv : ∀ μ, 3 ^ (k + 1) ∣ (stepVec m₁ k μ).val := fun μ =>
    (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)
  have T := LatSymm.ofTranslateLevel (isLevel_lvTop (m₁ := m₁) (k := k) (ϱ := ϱ)) _ hdv
  exact ⟨⟨T.trans (LatSymm.ofCoordPermLevel isLevel_lvTop _)⟩,
    ⟨(CoverSymm.ofTranslate isLevel_lvTop _ (stepVec_dvd m₁ k)).trans
      (CoverSymm.ofCoordPerm isLevel_lvTop _)⟩,
    ⟨(BlockSymm.ofTranslate isLevel_lvTop _ hdv).trans
      (BlockSymm.ofCoordPerm isLevel_lvTop _) T⟩⟩

/-- **Covariance of the decoupled background field at a coordinate swap.** -/
theorem decBg_permute_lvTop {N : ℕ} {a : ℕ → ℝ} {ν : ℝ} (ρ : ℝ)
    (s : DecParams (lvTop 3 m₁ k ϱ)) (D : BgData (lvTop 3 m₁ k ϱ) N) :
    let H := lvTop 3 m₁ k ϱ
    let S := LatSymm.ofCoordPermLevel (G := H) (m₁ := m₁) isLevel_lvTop swap01
    let CS := CoverSymm.ofCoordPerm (G := H) (m₁ := m₁) isLevel_lvTop swap01
    decBgField H a ν ρ (CS.par s) (S.sym D) = S.fld (decBgField H a ν ρ s D) ∧
      decBgMult H a ν ρ (CS.par s) (S.sym D) = S.mul (decBgMult H a ν ρ s D) :=
  decBg_sym _ _ (BlockSymm.ofCoordPerm isLevel_lvTop swap01) ρ s D

/-- **Covariance of the decoupled background field at the composite of `stepVec` and the swap.** -/
theorem decBg_compose_lvTop {N : ℕ} {a : ℕ → ℝ} {ν : ℝ} (ρ : ℝ)
    (s : DecParams (lvTop 3 m₁ k ϱ)) (D : BgData (lvTop 3 m₁ k ϱ) N) :
    let H := lvTop 3 m₁ k ϱ
    let hdv : ∀ μ, 3 ^ (k + 1) ∣ (stepVec m₁ k μ).val := fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)
    let T := LatSymm.ofTranslateLevel (G := H) isLevel_lvTop (stepVec m₁ k) hdv
    let S := T.trans (LatSymm.ofCoordPermLevel (G := H) (m₁ := m₁) isLevel_lvTop swap01)
    let CS := (CoverSymm.ofTranslate (G := H) isLevel_lvTop (stepVec m₁ k) (stepVec_dvd m₁ k)).trans
      (CoverSymm.ofCoordPerm (G := H) (m₁ := m₁) isLevel_lvTop swap01)
    decBgField H a ν ρ (CS.par s) (S.sym D) = S.fld (decBgField H a ν ρ s D) ∧
      decBgMult H a ν ρ (CS.par s) (S.sym D) = S.mul (decBgMult H a ν ρ s D) :=
  decBg_sym _ _ ((BlockSymm.ofTranslate isLevel_lvTop (stepVec m₁ k) fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)).trans
    (BlockSymm.ofCoordPerm isLevel_lvTop swap01)
    (LatSymm.ofTranslateLevel isLevel_lvTop (stepVec m₁ k) fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ))) ρ s D

end Step

end Balaban.Localization.DecEquiv
