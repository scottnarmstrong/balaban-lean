/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31Witness
public import Balaban.Fluctuation.Thm31cde
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 3.1 (a), (c), (d), (e) at an actual step

At the datum of `exists_e1Marks_datum` (`d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `β > 0`, zero
class, `p₁` small), the landed theorems `thm31a_of_input`, `thm31c_of_input`, `thm31d_of_input`,
`thm31e_of_input` are applied to the `E1Marks` of `nonempty_e1Marks` with their size hypotheses
discharged.  (c), (d), (e) are the generic interpolation-average expansions applied to the integrand
of `ℰ₁(0)`, with `β_k = β_{k+1} = S.β`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Polymer Balaban.Localization.I5Inhabited
  Balaban.SmallField.Def6 Balaban.SmallField MeasureTheory Set Filter Finset

/-- **Theorem 3.1 (a) at an actual step, unconditionally**: `ℰ₀^{(2)}(0) = ∑_S E(S)` with
`|E(S)| ≤ (c_mark + c_det) e^{-κ' d_Ω(S)}`. -/
theorem thm31a_witness :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      ∃ (I : E1Marks S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS
          (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))) (cdet : ℝ),
        ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (K := 1 + 1) 0 (1 + 1)
            Set.univ) → ℂ,
          S.E0loc (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))
              (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) = ∑ T, E T ∧
          ∀ T, ‖E T‖ ≤ (CPE 3 3 I.Kc I.κH I.κ0 I.κ' *
              (∑ i, I.F0 i * Real.exp (-I.κ0 * I.Lab.dl (I.y0 i))) + cdet) *
            Real.exp (-I.κ' * dExt T) := by
  obtain ⟨m₁, S, BS, hβ, hp, -, hR, I, -⟩ := exists_e1Marks_datum (fun _ => 1) (fun _ _ => one_pos)
  obtain ⟨cdet, ⟨D⟩⟩ := nonempty_detExpansion S 0
    (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (κ'' := I.κ') (by
      have := I.hκ'; exact this)
  obtain ⟨E, h1, h2⟩ := thm31a_of_input I (le_refl _) D
  exact ⟨m₁, S, BS, hβ, hp, hR, I, cdet, E, h1, h2⟩

/-- **Theorem 3.1 (c) at an actual step, unconditionally**: the interpolation average of the
integrand of `ℰ₁(0)` is `∑_S E(S)` with `|E(S)| ≤ β⁻¹ e^{-κ' d_Ω(S)}` (`β_k = S.β`). -/
theorem thm31c_witness :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      ∃ (I : E1Marks S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS
          (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))),
        ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (K := 1 + 1) 0 (1 + 1)
            Set.univ) → ℂ,
          interpAvg S.nuFl (S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (fun s x =>
              (fderiv ℝ (S.Phi1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (s • S.shiftU x))
                (S.maskU (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (S.shiftU x))) =
            ∑ T, E T ∧
          ∀ T, ‖E T‖ ≤ S.β⁻¹ * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨m₁, S, BS, hβ, hp, -, hR, I, hB⟩ := exists_e1Marks_datum (fun β => β⁻¹)
    (fun _ h => inv_pos.2 h)
  obtain ⟨E, h1, h2⟩ := thm31c_of_input I (κa := I.κ') (βk := S.β) rfl hB
  exact ⟨m₁, S, BS, hβ, hp, hR, I, E, h1, h2⟩

/-- **Theorem 3.1 (d) at an actual step, unconditionally** (`β_{k+1} = S.β`): for every `m`,
`|E(S)| ≤ ½ β^{-m-1} e^{-κ' d_Ω(S)}`. -/
theorem thm31d_witness (m : ℕ) :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      ∃ (I : E1Marks S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS
          (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))),
        ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (K := 1 + 1) 0 (1 + 1)
            Set.univ) → ℂ,
          interpAvg S.nuFl (S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (fun s x =>
              (fderiv ℝ (S.Phi1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (s • S.shiftU x))
                (S.maskU (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (S.shiftU x))) =
            ∑ T, E T ∧
          ∀ T, ‖E T‖ ≤ (1 / 2) * S.β ^ (-(m : ℤ) - 1) * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨m₁, S, BS, hβ, hp, -, hR, I, hB⟩ := exists_e1Marks_datum
    (fun β => (1 / 2) * β ^ (-(m : ℤ) - 1)) (fun _ h => by positivity)
  obtain ⟨E, h1, h2⟩ := thm31d_of_input I (κb := I.κ') (β' := S.β) m rfl hB
  exact ⟨m₁, S, BS, hβ, hp, hR, I, E, h1, h2⟩

/-- **Theorem 3.1 (e) at an actual step, unconditionally** (`β_{k+1} = S.β`): for every `n`,
`|E(S)| ≤ ½ β^{-n} e^{-κ' d_Ω(S)}`. -/
theorem thm31e_witness (n : ℕ) :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (BS : BlockSplit S 0),
      0 < S.β ∧ 0 < S.p₁ ∧ Nonempty (S.RayData 2) ∧
      ∃ (I : E1Marks S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) BS
          (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))))),
        ∃ E : Finset (CubeB (d := 3) (L := 3) (N₁ := 6) (m₁ := m₁) (K := 1 + 1) 0 (1 + 1)
            Set.univ) → ℂ,
          interpAvg S.nuFl (S.Wone (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (fun s x =>
              (fderiv ℝ (S.Phi1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁))) (s • S.shiftU x))
                (S.maskU (0 : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1)))) (S.shiftU x))) =
            ∑ T, E T ∧
          ∀ T, ‖E T‖ ≤ (1 / 2) * S.β ^ (-(n : ℤ)) * Real.exp (-I.κ' * dExt T) := by
  obtain ⟨m₁, S, BS, hβ, hp, -, hR, I, hB⟩ := exists_e1Marks_datum
    (fun β => (1 / 2) * β ^ (-(n : ℤ))) (fun _ h => by positivity)
  obtain ⟨E, h1, h2⟩ := thm31e_of_input I (κb := I.κ') (β' := S.β) n rfl hB
  exact ⟨m₁, S, BS, hβ, hp, hR, I, E, h1, h2⟩

end Balaban.Fluctuation
