/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityWitnessRay
public import Balaban.Fluctuation.StepActivityWitnessSplit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A non-degenerate `StepActivityBound`

The datum of `StepRegWitness` (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `β = T²/3 > 0`, constant unit
`θ`, zero class) with the cutoff radius `p₁` of `χ_fl` taken small (`β` stays large, as `RayData`
requires; `p⁺ = 2`), and the source `g = λ 1_{(y₁,i₁)}` of small size `λ`.  On the support of
`ν_{p₁}` the exponent of the interpolation is `-β V^{(k)}(ψ^{(k)} + sψ') + λ (svec φ_k(ψ^{(k)} +
tψ')(y₁)_{i₁} - svec φ_k(ψ^{(k)})(y₁)_{i₁})`; the first term is small because `V^{(k)}(ψ^{(k)}) = 0`
and `V^{(k)}` is continuous (`exists_small_radius`), the second because `g` is small, and at one
point the sum is nonzero (the background field moves, `RayData.bgField_ne`).  Hence the exponent is
below `stepActivityThreshold` and `stepActivityBound_of_small_gen` applies.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.SmallField.Def6 Balaban.SmallField Balaban.Polymer Finset Set Filter

theorem stepActivityThreshold_pos (d L N₁ m₁ K : ℕ) [NeZero L] [NeZero N₁] :
    0 < stepActivityThreshold d L N₁ m₁ K := by
  have hK0 : 0 < K0 d L (aEnt d L + 1) := by
    unfold K0
    have : Real.exp (-1) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
    exact div_pos (Real.exp_pos _) (by linarith [aEnt_nonneg d L])
  have hc1 := one_le_c1 d L
  have hc1' : 0 < c1 d L := by linarith
  unfold stepActivityThreshold
  positivity

theorem segment_mem {p : ℝ × ℝ} (hp : p ∈ stepSegments) :
    p.1 ∈ Icc (0 : ℝ) 1 ∧ p.2 ∈ Icc (0 : ℝ) 1 := by
  rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, by rw [h2]; exact ⟨le_rfl, zero_le_one⟩⟩
  · exact ⟨by rw [h1]; exact ⟨zero_le_one, le_rfl⟩, h2⟩

namespace StepSetting

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {S : StepSetting d L N₁ m₁ k 2 ϱ}
  {pp : ℝ}

theorem Wone_zeroClass (S : StepSetting d L N₁ m₁ k 2 ϱ) (s : ℝ) (x : S.E) :
    S.Wone (zeroClass d L N₁ m₁ k 2 ϱ) s x = -(S.β : ℂ) * S.Vk (S.psiAt s x) := by
  unfold Wone dE
  show -(S.β : ℂ) * _ + (EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) 2 ϱ) S.a S.ν (Nat.le_succ k) _ -
    EcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) 2 ϱ) S.a S.ν (Nat.le_succ k) _) = _
  rw [EcompAt_zero, EcompAt_zero]; simp

/-- The exponent `W₂` of the zero class with the source `λ 1_{(y₁,i₁)}`. -/
theorem Wtwo_single (S : StepSetting d L N₁ m₁ k 2 ϱ) (y₁ : CTorus d L N₁ m₁ (k + 1))
    (i₁ : Fin 2) (lam : ℝ) (t : ℝ) (x : S.E) :
    S.Wtwo (zeroClass d L N₁ m₁ k 2 ϱ)
        (fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0) t x =
      (lam : ℂ) * (S.bgComp y₁ i₁ (t, x) - S.bgComp y₁ i₁ (0, x)) := by
  classical
  unfold Wtwo dF
  show FcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) 2 ϱ) S.a S.ν (Nat.le_succ k) _ _ -
    FcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) 2 ϱ) S.a S.ν (Nat.le_succ k) _ _ = _
  rw [FcompAt_zero_eq, FcompAt_zero_eq]
  have hsum : ∀ φ : (stepG d L N₁ m₁ k ϱ).Ω 1 × Fin 2 → ℂ,
      ∑ y : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin 2,
        (fun y i => if y = y₁ ∧ i = i₁ then (lam : ℂ) else 0) y i *
          svec (stepG d L N₁ m₁ k ϱ) φ y i = (lam : ℂ) * svec (stepG d L N₁ m₁ k ϱ) φ y₁ i₁ := by
    intro φ
    simp [ite_and, ite_mul]
  rw [hsum, hsum]
  unfold bgComp
  rw [psiAt_zero]
  ring

/-- Measurability of the truncated exponents of the zero class. -/
theorem measurable_zeroClass (R : S.RayData pp) (hp : 0 < S.p₁) (hlt : S.p₁ < pp)
    (g : Fld d L N₁ m₁ (k + 1) 2) :
    ∀ p ∈ stepSegments, Measurable (fun x => S.WoneT (zeroClass d L N₁ m₁ k 2 ϱ) p.1 x +
      S.WtwoT (zeroClass d L N₁ m₁ k 2 ϱ) g p.2 x) := by
  intro p hpm
  obtain ⟨h1, h2⟩ := segment_mem hpm
  obtain ⟨U, hU⟩ := S.isC1Family_WVT R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 R.hfam R.hsm R.hχu
    R.hnorm R.hβ R.hpp R.hB5 R.hK2 R.hp40 R.hrad hp hlt
  obtain ⟨V, E', F', hE, hF⟩ := (classRegular_zeroClass R hp hlt g).c1
  have e : (fun x => S.WoneT (zeroClass d L N₁ m₁ k 2 ϱ) p.1 x +
      S.WtwoT (zeroClass d L N₁ m₁ k 2 ϱ) g p.2 x) = fun x => S.WVT p.1 x +
      S.dET (zeroClass d L N₁ m₁ k 2 ϱ) p.1 x + S.WtwoT (zeroClass d L N₁ m₁ k 2 ϱ) g p.2 x := by
    funext x; rw [WoneT_eq_add]
  rw [e]
  exact ((hU.measurable p.1 (hU.Icc_subset h1)).add (hE.measurable p.1 (hE.Icc_subset h1))).add
    (hF.measurable p.2 (hF.Icc_subset h2))

end StepSetting

end Balaban.Fluctuation
