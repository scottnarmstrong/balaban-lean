/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivReflect
public import Balaban.Localization.DecEquivPermuteStep
public import Balaban.Localization.DecEquivReflectPolymer

/-!
# A reflection at the top level set of the level step

At `lvTop 3 m₁ k ϱ` (`d = L = N₁ = 3`, torus of side `3 ^ (k + m₁ + 2)`) the reflection
`x_μ₀ ↦ c - 1 - x_μ₀` is a symmetry of the three structures when `3 ^ (k + 1 + m₁) ∣ c.val`
(cube side); the values `c = 0` and `c = 3 ^ (k + 1 + m₁)` are admissible
(`stepVec m₁ k 0`).  It is not the identity as soon as `c.val ≠ 1`
(`reflect_ne_one`).  `decBg_reflect_lvTop` is the covariance of the decoupled background field and
multiplier at the reflection.  Covariance of the output terms of the step is not proved here.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Inhabited
  Balaban.Inhabited.LevelStep Balaban.Analysis Finset

section Step

variable (m₁ k : ℕ)

/-- The reflection of the first coordinate is not the identity of the step torus when
`c.val ≠ 1` (in particular for `c = 0` and for `c` divisible by `3`). -/
theorem reflect_ne_one (μ₀ : Fin 3) (c : ZMod ((3 * 3 ^ m₁) * 3 ^ (k + 1))) (hc : c.val ≠ 1) :
    (reflPerm μ₀ c : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 := by
  have hM : 1 < (3 * 3 ^ m₁) * 3 ^ (k + 1) := by
    have ha : 1 ≤ 3 ^ m₁ := Nat.one_le_pow _ _ (by norm_num)
    have hb : 1 ≤ 3 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  have : Fact (1 < (3 * 3 ^ m₁) * 3 ^ (k + 1)) := ⟨hM⟩
  intro h
  have h' := congrArg (fun σ : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1)) => (σ 0) μ₀) h
  simp only [reflPerm, Equiv.coe_fn_mk, Function.update_self, Equiv.Perm.coe_one, id_eq,
    Pi.zero_apply, sub_zero] at h'
  have : c = 1 := by
    have := sub_eq_zero.1 h'
    exact this
  exact hc (by rw [this, ZMod.val_one])

variable (ϱ : ℝ) [NeZero (3 : ℕ)]

/-- The three symmetry structures are inhabited at a reflection of the top level set of the step
whenever `3 ^ (k + 1 + m₁) ∣ c.val`. -/
theorem reflectLvTop_nonempty (μ₀ : Fin 3) (c : ZMod ((3 * 3 ^ m₁) * 3 ^ (k + 1)))
    (hc : 3 ^ (k + 1 + m₁) ∣ c.val) :
    Nonempty (LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ) (reflPerm μ₀ c)) ∧
    Nonempty (CoverSymm (coverOf (lvTop 3 m₁ k ϱ)) (reflPerm μ₀ c)) ∧
    Nonempty (BlockSymm (lvTop 3 m₁ k ϱ) (reflPerm μ₀ c)) :=
  ⟨⟨LatSymm.ofReflectLevel isLevel_lvTop μ₀ c ((pow_dvd_pow 3 (by omega)).trans hc)⟩,
    ⟨CoverSymm.ofReflect isLevel_lvTop μ₀ c hc⟩,
    ⟨BlockSymm.ofReflect isLevel_lvTop μ₀ c ((pow_dvd_pow 3 (by omega)).trans hc)⟩⟩

/-- `c = 0` is admissible, and the reflection is then not the identity. -/
theorem reflectLvTop_zero (μ₀ : Fin 3) :
    (reflPerm μ₀ (0 : ZMod ((3 * 3 ^ m₁) * 3 ^ (k + 1))) :
        Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 ∧
    (Nonempty (LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ) (reflPerm μ₀ (0 : ZMod _))) ∧
    Nonempty (CoverSymm (coverOf (lvTop 3 m₁ k ϱ)) (reflPerm μ₀ (0 : ZMod _))) ∧
    Nonempty (BlockSymm (lvTop 3 m₁ k ϱ) (reflPerm μ₀ (0 : ZMod _)))) :=
  ⟨reflect_ne_one m₁ k μ₀ 0 (by simp), reflectLvTop_nonempty m₁ k ϱ μ₀ 0 (by simp)⟩

/-- `c = 3 ^ (k + 1 + m₁)` (the first coordinate of `stepVec`) is admissible, and the reflection
is then not the identity. -/
theorem reflectLvTop_stepVec (μ₀ : Fin 3) :
    (reflPerm μ₀ (stepVec m₁ k 0) : Equiv.Perm (CTorus 3 3 3 m₁ (k + 1))) ≠ 1 ∧
    (Nonempty (LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ) (reflPerm μ₀ (stepVec m₁ k 0))) ∧
    Nonempty (CoverSymm (coverOf (lvTop 3 m₁ k ϱ)) (reflPerm μ₀ (stepVec m₁ k 0))) ∧
    Nonempty (BlockSymm (lvTop 3 m₁ k ϱ) (reflPerm μ₀ (stepVec m₁ k 0)))) := by
  refine ⟨reflect_ne_one m₁ k μ₀ _ ?_, reflectLvTop_nonempty m₁ k ϱ μ₀ _ (stepVec_dvd m₁ k 0)⟩
  rw [stepVec_val]
  have : 3 ≤ 3 ^ (k + 1 + m₁) := by
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- **Covariance of the decoupled background field at the reflection** `x_μ₀ ↦ c - 1 - x_μ₀`,
`3 ^ (k + 1 + m₁) ∣ c.val`, of the top level set of the step. -/
theorem decBg_reflect_lvTop {N : ℕ} {a : ℕ → ℝ} {ν : ℝ} (ρ : ℝ) (μ₀ : Fin 3)
    (c : ZMod ((3 * 3 ^ m₁) * 3 ^ (k + 1))) (hc : 3 ^ (k + 1 + m₁) ∣ c.val)
    (s : DecParams (lvTop 3 m₁ k ϱ)) (D : BgData (lvTop 3 m₁ k ϱ) N) :
    let H := lvTop 3 m₁ k ϱ
    let S := LatSymm.ofReflectLevel (G := H) isLevel_lvTop μ₀ c
      ((pow_dvd_pow 3 (by omega)).trans hc)
    let CS := CoverSymm.ofReflect (G := H) isLevel_lvTop μ₀ c hc
    decBgField H a ν ρ (CS.par s) (S.sym D) = S.fld (decBgField H a ν ρ s D) ∧
      decBgMult H a ν ρ (CS.par s) (S.sym D) = S.mul (decBgMult H a ν ρ s D) :=
  decBg_sym _ _ (BlockSymm.ofReflect isLevel_lvTop μ₀ c ((pow_dvd_pow 3 (by omega)).trans hc))
    ρ s D

/-- **`PolymerSymm` is inhabited at the reflections of the top level set of the step**
(`m₀ = 0`, `3 ^ (k + 1 + m₁) ∣ c.val`). -/
theorem polymerSymm_reflect_lvTop (μ₀ : Fin 3) (c : ZMod ((3 * 3 ^ m₁) * 3 ^ (k + 1)))
    (hc : 3 ^ (k + 1 + m₁) ∣ c.val) :
    Nonempty (PolymerSymm (lvTop 3 m₁ k ϱ) 0 (reflPerm μ₀ c) (reflectCover μ₀ c)) :=
  ⟨PolymerSymm.ofReflect isLevel_lvTop (by simp) μ₀ c (by simpa only [Nat.add_zero] using hc)⟩

/-- **Covariance of the expansion terms `𝓔(X, Y)` at a reflection of the step**
(`3 ^ (k + 1 + m₁) ∣ c.val`; `c = 0` and `c = 3 ^ (k + 1 + m₁)` are admissible): the term of the
transported function at the reflected sets equals the original term. -/
theorem evTerm_reflect_lvTop (μ₀ : Fin 3) (c : ZMod ((3 * 3 ^ m₁) * 3 ^ (k + 1)))
    (hc : 3 ^ (k + 1 + m₁) ∣ c.val)
    (S : LatSymm (lvTop 3 m₁ k ϱ) (lvTop 3 m₁ k ϱ) (reflPerm μ₀ c)) {R : ℝ} (hR : 1 < R)
    (X₁ Y : Set (CTorus 3 3 3 m₁ (k + 1)))
    {U U' : Type*} {F : U → ((coverOf (lvTop 3 m₁ k ϱ)).cubeIdx → ℂ) → ℂ}
    {F' : U' → ((coverOf (lvTop 3 m₁ k ϱ)).cubeIdx → ℂ) → ℂ} {u : U} {u' : U'} :
    let G := lvTop 3 m₁ k ϱ
    let CS := CoverSymm.ofReflect (G := G) isLevel_lvTop μ₀ c hc
    let κ : (coverOf G).cubeIdx ≃ (coverOf G).cubeIdx :=
      Equiv.subtypeEquiv CS.τ fun q => (CS.idx q).symm
    AnalyticOnNhd ℂ (F u) (polydisc (0 : (coverOf G).cubeIdx → ℂ) (fun _ => R)) →
    AnalyticOnNhd ℂ (F' u') (polydisc (0 : (coverOf G).cubeIdx → ℂ) (fun _ => R)) →
    (∀ s ∈ unitCube (coverOf G).cubeIdx, F' u' s = F u (s ∘ κ)) →
    evTerm (fun i : (coverOf G).cubeIdx => i.1) G 0 ((reflPerm μ₀ c) '' X₁)
        F' ((reflPerm μ₀ c) '' Y) u' =
      evTerm (fun i : (coverOf G).cubeIdx => i.1) G 0 X₁ F Y u := by
  intro G CS κ hF hF' hff
  classical
  exact evTerm_relabel (fun i : (coverOf G).cubeIdx => i.1) (fun i : (coverOf G).cubeIdx => i.1)
    κ hR (PolymerSymm.ofReflect isLevel_lvTop (by simp) μ₀ c (by simpa only [Nat.add_zero] using hc))
    S (fun _ => rfl) (fun i => i.2) X₁ Y hF hF' hff

end Step

end Balaban.Localization.DecEquiv
