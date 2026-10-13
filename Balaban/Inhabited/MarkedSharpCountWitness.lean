/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedSharpCount
public import Balaban.Inhabited.DAPhysicalTower
public import Balaban.Inhabited.StepActivityDirectScaledWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# `marked_count_scaled` at the landed witness step

At the witness step `hatStep m₁ β (pLog 1 2 β) δ` (`d = L = 3`, `N = 2`, `k = 1`, cutoff
`p₁ = pLog 1 2 β`) all the structural hypotheses of `StepSetting.marked_count_scaled`
(`FlCore`, the cover data `covSetup`/`X1_eq_univ`/`hopt`/`treeLen_zero`, `hatConn`, `rowInHat`,
the margins, `hZV`, `hmarV`, the decay and the entropy constants of `tower_core_fixed`) are
discharged by the landed witness theorems used for `stepActivityBound_zeroClass_direct_physical`.
The statement below is the count itself for every marked block `z`: for every marked datum
satisfying the radius condition of `marked_term_cauchy`, the output sums `markedOut` are bounded by
a constant times `e^{-(2 κ_dec - 1) d(Y')}` and are anchored at the root.

What is not discharged: the existence of a non-trivial marked datum `(x, u)` with the coordinate
bound `vn (shiftUC x) ≤ Y₀` and the radius inequality.  The radius inequality itself, with
`Y₀ = √N |c_c| covSupConstC p₁`, is `marked_radius_and_derivative_at_witness`; the coordinate bound
of `shiftUC` is not stated as a landed theorem.  The datum `x = 0`, `u = 0` is admissible.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6

/-- The witness step at the cutoff `p₁ = pLog 1 2 β`. -/
noncomputable abbrev wStep (m₁ : ℕ) (β δ : ℝ) : StepSetting 3 3 9 m₁ 1 2 (rhoSep m₁) :=
  hatStep m₁ β (pLog 1 2 β) δ

open Classical in
/-- **Non-vacuity of `marked_count_scaled`.**  There are fixed data `m₁, t, δ, κ_dec` and a
threshold `β₀` such that for every `β ≥ β₀` and every marked block `z`, the block terms of the
expansion exist and, for every marked datum satisfying the hypotheses of the count, the output
sums are bounded and anchored. -/
theorem marked_count_scaled_at_witness :
    ∃ (m₁ : ℕ) (t δ κdec β₀ : ℝ), 2 ≤ β₀ ∧ 0 < t ∧ aEnt 3 3 + 1 ≤ 2 * κdec - 1 ∧
      ∀ β : ℝ, β₀ ≤ β → ∀ z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))),
      ∃ Ev : Torus 3 (9 * 3 ^ m₁ * 3 ^ (1 + 1 - (1 + 1))) → Set (CTorus 3 3 9 m₁ (1 + 1)) →
          RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2 × (CTorus 3 3 9 m₁ (1 + 1) → Fin 2 → ℂ) → ℂ,
        ∀ {Y₀ R₁ r t₁ t₀ : ℝ}, 0 ≤ Y₀ → ∀ {x : (wStep m₁ β δ).E} {u : ℂ},
          (∀ q : (wStep m₁ β δ).U, vn (fun i => (wStep m₁ β δ).shiftUC x (q, i)) ≤ Y₀) →
          (R₁ + r) * (‖u‖ + t₁) * Y₀ < t → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
          ∀ {Θ : RawData 3 3 (9 * 3 ^ m₁) (1 + 1) 2},
            Θ ∈ XiCRaw (wStep m₁ β δ).G' (compWeight 3 1) nuW (1 + 1) 1 t →
          ∃ F₀ : ℝ, 0 ≤ F₀ ∧ (∀ Y' : Set (CTorus 3 3 9 m₁ (1 + 1)),
            ‖markedOut 1 (fun _ => Set.univ)
                (fun _ => polyDom (wStep m₁ β δ).G' (Finset.univ) 1 1
                  ({0} : Set (CTorus 3 3 9 m₁ (1 + 1))))
                z Ev taylorWeight (liftC (wStep m₁ β δ).hG' (u • (wStep m₁ β δ).shiftUC x))
                (liftC (wStep m₁ β δ).hG' ((wStep m₁ β δ).maskUC z ((wStep m₁ β δ).shiftUC x)))
                Θ Y'‖ ≤ F₀ * Real.exp (-(2 * κdec - 1) * treeLenCovOne 1 (1 + 1) Y')) ∧
            (∀ Y' : Set (CTorus 3 3 9 m₁ (1 + 1)),
            markedOut 1 (fun _ => Set.univ)
                (fun _ => polyDom (wStep m₁ β δ).G' (Finset.univ) 1 1
                  ({0} : Set (CTorus 3 3 9 m₁ (1 + 1))))
                z Ev taylorWeight (liftC (wStep m₁ β δ).hG' (u • (wStep m₁ β δ).shiftUC x))
                (liftC (wStep m₁ β δ).hG' ((wStep m₁ β δ).maskUC z ((wStep m₁ β δ).shiftUC x)))
                Θ Y' ≠ 0 →
              IsDj 1 (1 + 1) Y' ∧ rootCube (m₀ := 1) z ∈ blocksOf 1 (1 + 1) Set.univ Y') := by
  classical
  obtain ⟨-, δ, δ', T, -, -, hδ, hsm, hδ'0, hδ'a, hδ'b, hδ'c, hT, -, hT1, hT2⟩ :=
    exists_witness_params (fun _ => 0)
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, g1, g2, g3, g4, g5, hκE, hκa, hB0⟩ := tower_core_fixed 2
  have hbig : cstarX 3 3 ≤ (3 : ℝ) ^ m₁ := by
    have hκdec0 : 0 ≤ κdec := by linarith
    have hκ_nn : 0 ≤ κ := le_trans (by positivity) hκ
    have h := Localization.cstarX_pos 3 3
    have h2 : cstarX 3 3 ≤ cstarX 3 3 * Real.exp ((N0 3 3 : ℝ) * κ) :=
      le_mul_of_one_le_right h.le (Real.one_le_exp (by positivity))
    have h3 : ((3 : ℕ) : ℝ) ^ m₁ = (3 : ℝ) ^ m₁ := by norm_num
    linarith
  obtain ⟨β₀t, hβ₀t, hitems⟩ := tower_C_items (A₁ := 1) one_pos 2 m₁ h4 hbig κ ht0 hδ hsm hδ'0
    hδ'a hδ'b hδ'c
  refine ⟨m₁, t, δ, κdec, β₀t, hβ₀t, ht0, by linarith, ?_⟩
  intro β hβ z
  obtain ⟨hp, hcψ0, hr0, hδ₁, hc, hlt, ⟨R0⟩⟩ := hitems β hβ
  have hmain := (wStep m₁ β δ).marked_count_scaled z (Hm := Hm m₁ (rhoSep m₁))
    (jV := fun _ => 1) (XV := fun _ => Xr) (𝒦XV := fun _ => {0}) (X₁V := fun _ => Finset.univ)
    (m₀ := 1) hC (fun _ => covSetup)
    (fun _ => by rw [Finset.coe_univ]; exact X1_eq_univ.symm)
    hatConn (rowInHat_level (dgSettingNu h4) isLevel_Hm isLevel_Gp) (fun _ => hopt)
    (fun _ => treeLen_zero) hκ0 hκdec (by exact_mod_cast hκ) h1 hlog isLevel_Hm
    (fun _ _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
    (fun _ => blockMargin_univ fun x _ _ => mem_some_intBox h4 x) (by norm_num)
  obtain ⟨Ev, -, hmain⟩ := hmain
  refine ⟨Ev, ?_⟩
  intro Y₀ R₁ r t₁ t₀ hY0 x u hY hrad hR₁ hr ht₀ ht₀₁ Θ hΘ
  obtain ⟨-, hB, hanc, -⟩ := hmain hY0 hY hrad hR₁ hr ht₀ ht₀₁ hΘ
  have hc1 : 0 ≤ c1 3 3 := by unfold c1; positivity
  refine ⟨_, ?_, hB, hanc⟩
  have hn : (0 : ℝ) ≤ (nFibre 3 3 : ℝ) := Nat.cast_nonneg _
  generalize (nFibre 3 3 : ℝ) = nf at hn ⊢
  positivity

end Balaban.Inhabited
