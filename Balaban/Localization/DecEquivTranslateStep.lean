/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivTranslate
public import Balaban.Inhabited.LevelStepSetting

/-!
# A non-identity symmetry at a landed step: covariance of the decoupled background field

At the top level set `lvTop 3 m₁ k ϱ` of the level step (`d = L = 3`, `N₁ = 3`, torus of side
`3 ^ (k + m₁ + 2)`), translation by the vector `(3 ^ (k + 1 + m₁), …)` is a nonzero element of the
torus divisible by the cube side `3 ^ (k + 1 + m₁)`.  `translate_ne_one` says that it is not the
identity, and the three symmetry structures are inhabited there
(`translateLvTop_nonempty`).  The first covariance statement at a non-identity symmetry is
`decBg_translate_lvTop`: the decoupled background field and multiplier of the translated datum
are the translated field and multiplier.  Covariance of the output terms of the step is not proved.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Inhabited
  Balaban.Inhabited.LevelStep Finset

section Step

variable (m₁ k : ℕ)

/-- The translation vector `(3 ^ (k + 1 + m₁), …, 3 ^ (k + 1 + m₁))` of the step torus. -/
def stepVec : CTorus 3 3 3 m₁ (k + 1) := fun _ => ((3 ^ (k + 1 + m₁) : ℕ) : ZMod _)

theorem stepVec_val (μ : Fin 3) : (stepVec m₁ k μ).val = 3 ^ (k + 1 + m₁) := by
  unfold stepVec
  apply ZMod.val_natCast_of_lt
  have : (3 * 3 ^ m₁) * 3 ^ (k + 1) = 3 * 3 ^ (k + 1 + m₁) := by ring
  rw [this]
  have : 0 < 3 ^ (k + 1 + m₁) := by positivity
  omega

theorem stepVec_dvd (μ : Fin 3) : 3 ^ (k + 1 + m₁) ∣ (stepVec m₁ k μ).val :=
  (stepVec_val m₁ k μ).symm ▸ dvd_rfl

/-- The translation by `stepVec` is not the identity. -/
theorem translate_ne_one :
    (Equiv.addRight (stepVec m₁ k) : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 := by
  intro h
  have := congrArg (fun σ : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1)) => (σ 0) 0) h
  simp only [Equiv.coe_addRight, Equiv.Perm.coe_one, id_eq, Pi.add_apply, Pi.zero_apply,
    zero_add] at this
  have h0 := stepVec_val m₁ k 0
  rw [this] at h0
  rw [ZMod.val_zero] at h0
  exact (pow_pos (by norm_num : (0:ℕ) < 3) _).ne h0

variable (ϱ : ℝ) [NeZero (3 : ℕ)]

/-- The three symmetry structures are inhabited at the top level set of the step for the
non-identity translation `stepVec`. -/
theorem translateLvTop_nonempty :
    Nonempty (LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ) (Equiv.addRight (stepVec m₁ k))) ∧
    Nonempty (CoverSymm (coverOf (lvTop 3 m₁ k ϱ)) (Equiv.addRight (stepVec m₁ k))) ∧
    Nonempty (BlockSymm (lvTop 3 m₁ k ϱ) (Equiv.addRight (stepVec m₁ k))) :=
  ⟨⟨LatSymm.ofTranslateLevel isLevel_lvTop _ fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)⟩,
    ⟨CoverSymm.ofTranslate isLevel_lvTop _ (stepVec_dvd m₁ k)⟩,
    ⟨BlockSymm.ofTranslate isLevel_lvTop _ fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)⟩⟩

/-- **First covariance statement at a non-identity symmetry.**  At the top level set of the step,
the decoupled background field and multiplier of the translated datum (decoupling parameters
`s ∘ τ⁻¹`) are the translates of the decoupled background field and multiplier. -/
theorem decBg_translate_lvTop {N : ℕ} {a : ℕ → ℝ} {ν : ℝ} (ρ : ℝ)
    (s : DecParams (lvTop 3 m₁ k ϱ)) (D : BgData (lvTop 3 m₁ k ϱ) N) :
    let H := lvTop 3 m₁ k ϱ
    let S := LatSymm.ofTranslateLevel (G := H) isLevel_lvTop (stepVec m₁ k) fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)
    let CS := CoverSymm.ofTranslate (G := H) isLevel_lvTop (stepVec m₁ k) (stepVec_dvd m₁ k)
    decBgField H a ν ρ (CS.par s) (S.sym D) = S.fld (decBgField H a ν ρ s D) ∧
      decBgMult H a ν ρ (CS.par s) (S.sym D) = S.mul (decBgMult H a ν ρ s D) :=
  decBg_sym _ _ (BlockSymm.ofTranslate isLevel_lvTop (stepVec m₁ k) fun μ =>
      (pow_dvd_pow 3 (by omega)).trans (stepVec_dvd m₁ k μ)) ρ s D

end Step

end Balaban.Localization.DecEquiv
