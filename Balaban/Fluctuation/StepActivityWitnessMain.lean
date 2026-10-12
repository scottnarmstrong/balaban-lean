/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityWitness
public import Balaban.Fluctuation.StepLocal
public import Balaban.Fluctuation.StepObs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The non-degenerate datum with a `StepActivityBound`, and the step identities at it

`exists_activity_datum`: a step datum `d = L = 3`, `N₁ = 6`, `k = 1`, `N = 2`, `β > 0`, `p₁ > 0`,
`p₁ < p⁺ = 2`, with `RayData`, the zero class and a nonzero source `g`, carrying a
`StepActivityBound` whose exponent `W₁ + W₂` on the segments is not identically zero.
`nondegenerate_step_identities`: at this datum `prop26_complex_class_of_activity`, `F0_eq_pair`
and `sum_E1loc` hold with all premises discharged.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.Localization.I5Inhabited Balaban.SmallField.Def6 Balaban.SmallField Balaban.Polymer
  Finset Set Filter

/-- The background of the block datum of the witness setting is the constant unit field. -/
theorem activityWitness_bgField {m₁ : ℕ} {β δ : ℝ} (R : (witnessSetting m₁ β δ).RayData 2) :
    bgField (witnessSetting m₁ β δ).G' (witnessSetting m₁ β δ).a (witnessSetting m₁ β δ).ν
      (witnessSetting m₁ β δ).D' = unitPhi (witnessSetting m₁ β δ).G' hN2 := by
  have hcons := theta_consts (d := 3) (L := 3) (N := 2) (by norm_num) R.hδ'0 R.hδ'
  have hDU : InUnionDomainR (witnessSetting m₁ β δ).G' (bgC1 3 3 2) (witnessSetting m₁ β δ).ν
      (witnessSetting m₁ β δ).D' := ⟨R.δ', R.hδ'0, hcons.2.2.1, R.hD'R⟩
  have ha : ∀ n, 0 ≤ compWeight 3 (1 : ℝ) n := fun n => compWeight_nonneg_three 1 zero_le_one n
  exact bgField_unitBg (isLevel_GP m₁) hN2 (a := compWeight 3 1) ha (unitVec hN2) R.H hDU

/-- A small perturbation parameter `λ` keeping the exponent nonzero at the chosen point. -/
theorem exists_lam_ne {a w : ℂ} (hw : w ≠ 0) {l₀ : ℝ} (hl : 0 < l₀) :
    ∃ l : ℝ, 0 < l ∧ l ≤ l₀ ∧ a + (l : ℂ) * w ≠ 0 := by
  by_contra h
  push Not at h
  have h1 := h l₀ hl le_rfl
  have h2 := h (l₀ / 2) (by positivity) (by linarith)
  push_cast at h1 h2
  have : (l₀ : ℂ) / 2 * w = 0 := by linear_combination h1 - h2
  have hl' : (l₀ : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  rcases mul_eq_zero.1 this with h3 | h3
  · exact hl' (by simpa using h3)
  · exact hw h3

/-- **A non-degenerate `StepActivityBound`** (see the module docstring). -/
theorem exists_activity_datum :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 6 m₁ 2 2),
      0 < S.β ∧ 0 < S.p₁ ∧ S.p₁ < 2 ∧ Nonempty (S.RayData 2) ∧
      Nonempty (StepActivityBound S (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
      (∃ p ∈ stepSegments, ∃ x : S.E, S.WoneT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) p.1 x +
        S.WtwoT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g p.2 x ≠ 0) := by
  classical
  obtain ⟨m₁, δ, δ', T, hm, hbig, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨R0⟩ := rayData_witness hm hbig hδ hsm hδ'0 hδ'a hδ'b hδ'c hT hT1 hT2
  set S0 := witnessSetting m₁ (T ^ 2 / 3) δ with hS0
  have hbg0 := activityWitness_bgField R0
  have hβ : 0 < S0.β := R0.hβ
  have hT0 := stepActivityThreshold_pos 3 3 6 m₁ 2
  set T0 := stepActivityThreshold 3 3 6 m₁ 2 with hT0def
  have hε : 0 < T0 / (2 * S0.β) := by positivity
  obtain ⟨p, hp0, hpp, hbound, x₀, hx₀, y₁, i₁, hne⟩ :=
    S0.exists_small_radius R0 rfl hbg0 (show (0 : ℝ) < S0.p₁ from one_pos)
      (show S0.p₁ < 2 by show (1 : ℝ) < 2; norm_num) hε
  let S1 : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁) := { S0 with p₁ := p }
  have R1 : S1.RayData 2 :=
    { ha₁ := R0.ha₁, H := R0.H, δ' := R0.δ', hδ'0 := R0.hδ'0, hδ' := R0.hδ', hD'R := R0.hD'R,
      hδ0 := R0.hδ0, hfam := R0.hfam, hsm := R0.hsm, hχu := R0.hχu, hnorm := R0.hnorm,
      hβ := R0.hβ, hpp := R0.hpp, B₅ := R0.B₅, K₂ := R0.K₂, hB5 := R0.hB5, hK2 := R0.hK2,
      hp40 := R0.hp40, hrad := R0.hrad }
  have hw : S1.bgComp y₁ i₁ (1, x₀) - S1.bgComp y₁ i₁ (0, x₀) ≠ 0 := sub_ne_zero.2 hne
  obtain ⟨l, hl0, hl1, hlne⟩ := exists_lam_ne (a := -(S1.β : ℂ) * S1.Vk (S1.psiAt 1 x₀)) hw
    (l₀ := T0 / 2) (by positivity)
  set g : Fld 3 3 6 m₁ 2 2 := fun y i => if y = y₁ ∧ i = i₁ then (l : ℂ) else 0 with hg
  have hp1 : 0 < S1.p₁ := hp0
  have hlt1 : S1.p₁ < 2 := hpp
  have hmeas := S1.measurable_zeroClass R1 hp1 hlt1 g
  have hx₀χ : chiFl S1.U 2 S1.p₁ x₀ = 1 := (chiFl_eq_one_iff hp1 x₀).2 hx₀
  -- the exponent
  have hexp : ∀ s t : ℝ, ∀ x : S1.E, chiFl S1.U 2 S1.p₁ x = 1 →
      S1.WoneT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) s x +
        S1.WtwoT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g t x =
      -(S1.β : ℂ) * S1.Vk (S1.psiAt s x) + (l : ℂ) * (S1.bgComp y₁ i₁ (t, x) -
        S1.bgComp y₁ i₁ (0, x)) := by
    intro s t x hx
    rw [S1.WoneT_of_chi _ s x hx, S1.WtwoT_of_chi _ g t x hx, S1.Wone_zeroClass,
      S1.Wtwo_single y₁ i₁ l t x]
  have hsmall : ∀ q ∈ stepSegments, ∀ x,
      ‖S1.WoneT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) q.1 x +
        S1.WtwoT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g q.2 x‖ ≤ T0 := by
    intro q hq x
    by_cases hx : chiFl S1.U 2 S1.p₁ x = 1
    · obtain ⟨hq1, hq2⟩ := segment_mem hq
      have hxn : ‖x‖ < p := (chiFl_eq_one_iff hp1 x).1 hx
      rw [hexp q.1 q.2 x hx]
      obtain ⟨hV, -⟩ := hbound x hxn q.1 hq1
      obtain ⟨-, hB⟩ := hbound x hxn q.2 hq2
      have h1 : ‖-(S1.β : ℂ) * S1.Vk (S1.psiAt q.1 x)‖ ≤ T0 / 2 := by
        rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hβ]
        calc S1.β * ‖S1.Vk (S1.psiAt q.1 x)‖ ≤ S1.β * (T0 / (2 * S0.β)) :=
              mul_le_mul_of_nonneg_left hV.le hβ.le
          _ = T0 / 2 := by
              show S0.β * (T0 / (2 * S0.β)) = T0 / 2
              field_simp
      have h2 : ‖(l : ℂ) * (S1.bgComp y₁ i₁ (q.2, x) - S1.bgComp y₁ i₁ (0, x))‖ ≤ T0 / 2 := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl0]
        calc l * ‖S1.bgComp y₁ i₁ (q.2, x) - S1.bgComp y₁ i₁ (0, x)‖ ≤ l * 1 :=
              mul_le_mul_of_nonneg_left (hB y₁ i₁).le hl0.le
          _ ≤ T0 / 2 := by linarith
      exact (norm_add_le _ _).trans (by linarith)
    · have : S1.WoneT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) q.1 x = 0 := by
        simp [StepSetting.WoneT, hx]
      have h2 : S1.WtwoT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g q.2 x = 0 := by
        simp [StepSetting.WtwoT, hx]
      rw [this, h2, add_zero, norm_zero]; exact hT0.le
  obtain ⟨I⟩ := stepActivityBound_of_small_gen S1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g hp1
    hmeas hsmall
  refine ⟨m₁, S1, g, hβ, hp1, hlt1, ⟨R1⟩, ⟨I⟩, ⟨(1, 1), Or.inr ⟨rfl, ⟨zero_le_one, le_rfl⟩⟩,
    x₀, ?_⟩⟩
  show S1.WoneT _ 1 x₀ + S1.WtwoT _ g 1 x₀ ≠ 0
  rw [hexp 1 1 x₀ hx₀χ]
  exact hlne

/-- **The step identities at a datum with genuine content.**  At the datum of
`exists_activity_datum` (`β > 0`, `N = 2`, nonzero activities), with `StepActivityBound` in place of
`StepNonvanishing`: `Prop. 2.6` (`prop26_complex_class_of_activity`), the formula
`ℱ₀(g) = β_k^{-1/2} ∑ g M₀(g)` (`F0_eq_pair`) and `∑_z ℰ₁(z) = ℰ₁` (`sum_E1loc`), with all premises
discharged. -/
theorem nondegenerate_step_identities :
    ∃ (m₁ : ℕ) (S : StepSetting 3 3 6 m₁ 1 2 (rhoSep m₁)) (g : Fld 3 3 6 m₁ 2 2),
      0 < S.β ∧ 0 < S.p₁ ∧
      (∃ p ∈ stepSegments, ∃ x : S.E, S.WoneT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) p.1 x +
        S.WtwoT (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g p.2 x ≠ 0) ∧
      S.Tstep (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = Complex.exp (-(S.β : ℂ) * (S.Anew : ℂ) +
        EcompAt (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀ (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm
          S.a S.ν (Nat.le_succ 1) S.psiKd -
          (S.Eppp (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) : ℂ) * (S.nU : ℂ) +
        FcompAt (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).m₀ (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)).Tm
          S.a S.ν (Nat.le_succ 1) S.psiKd g + S.E0 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) +
        S.F0 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g) ∧
      S.F0 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g = ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
        ∑ y : CTorus 3 3 6 m₁ 2, ∑ i : Fin 2, g y i *
          S.M0 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) g y i ∧
      ∑ z : Torus 3 (6 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))),
        S.E1loc (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) z = S.E1 (zeroClass 3 3 6 m₁ 1 2 (rhoSep m₁)) := by
  obtain ⟨m₁, S, g, hβ, hp, hlt, ⟨R⟩, ⟨I⟩, hnz⟩ := exists_activity_datum
  refine ⟨m₁, S, g, hβ, hp, hnz, ?_, ?_, ?_⟩
  · exact prop26_complex_class_of_activity S _ R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R R.hδ0 R.hfam R.hsm
      R.hχu R.hnorm R.hβ hp hlt R.hB5 R.hK2 R.hp40 R.hrad g (classRegular_zeroClass R hp hlt g) I
  · exact S.F0_eq_pair _ hp hβ g (classRegularObs_zeroClass R hp hlt g)
      (stepNonvanishing_of_activityBound I)
  · exact S.sum_E1loc _ hp g (classRegularLoc_zeroClass R hp hlt g)
      (stepNonvanishing_of_activityBound I)

end Balaban.Fluctuation
