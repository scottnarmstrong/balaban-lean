/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.DetCollarHullSymm
public import Balaban.Inhabited.DetOutputTermsWitness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Non-vacuity of the covariance of the regrouped determinant terms

At the step `hatStep m₁ 1 1 1` of the landed witness (`d = L = 3`, `N₁ = 9`, `k = 1`, `m₀ = 0`)
the hypotheses of `exists_detExpansionLocC_grouped_sym` are satisfied together, for the
non-identity symmetry "translation by the vector with all coordinates equal to the cell side,
then the reflection `x₀ ↦ -1 - x₀`".  The numerical hypotheses are those of
`detOutputTerms_nonempty` (the output `directWitness_core_amp` of the tower); the landed
`detCollarGrouped_scale` witness is existential in the record and does not expose them, so the
witness here repeats the instantiation of `detOutputTerms_nonempty`.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Analysis Balaban.SmallField.Def6 Balaban.Polymer Balaban.Inhabited.LevelStep
  Balaban.Localization.DecEquiv

/-- The translation by the cell side in every coordinate. -/
def cellVec (m₁ : ℕ) : CTorus 3 3 9 m₁ (1 + 1) :=
  fun _ => ((3 ^ (1 + 1 + 0 + m₁) : ℕ) : ZMod (9 * 3 ^ m₁ * 3 ^ (1 + 1)))

theorem cellVec_val (m₁ : ℕ) (μ : Fin 3) : (cellVec m₁ μ).val = 3 ^ (1 + 1 + 0 + m₁) := by
  unfold cellVec
  apply ZMod.val_natCast_of_lt
  have : 9 * 3 ^ m₁ * 3 ^ (1 + 1) = 9 * 3 ^ (1 + 1 + 0 + m₁) := by ring
  rw [this]
  have : 0 < 3 ^ (1 + 1 + 0 + m₁) := by positivity
  omega

/-- The symmetry: translation by `cellVec`, then the reflection `x₀ ↦ -1 - x₀`. -/
noncomputable def witnessSymm (m₁ : ℕ) : Equiv.Perm (CTorus 3 3 9 m₁ (1 + 1)) :=
  (Equiv.addRight (cellVec m₁)).trans (reflPerm 0 0)

theorem genSymm_witnessSymm (m₁ : ℕ) : GenSymm 3 9 m₁ (1 + 1) (1 + 1) 0 (witnessSymm m₁) :=
  GenSymm.trans (GenSymm.translate _ fun μ => by rw [cellVec_val])
    (GenSymm.reflect 0 0 (by simp))

theorem witnessSymm_ne_one (m₁ : ℕ) : witnessSymm m₁ ≠ 1 := by
  intro h
  have h0 := congrFun (congrArg (fun σ : Equiv.Perm (CTorus 3 3 9 m₁ (1 + 1)) => (σ 0)) h) 1
  have h1 : cellVec m₁ 1 = 0 := by simpa [witnessSymm, reflPerm] using h0
  have := cellVec_val m₁ 1
  rw [h1, ZMod.val_zero] at this
  exact (pow_pos (by norm_num : (0 : ℕ) < 3) _).ne this

open Classical in
/-- **The hypotheses of the covariance of the regrouped determinant terms hold together.**  At the
step `hatStep m₁ 1 1 1` (`d = L = 3`, `N₁ = 9`, `m₀ = 0`) there is a non-identity element `σ` of the
generated group (a translation followed by an admissible reflection) such that, for every root
`z`, there are records `E` (root `z`) and `E'` (root `rootAct σ z`) and a lattice symmetry `Sy`
with the data of the chart preserved, `E'.term (Sy.sym D) (σ • T) = E.term D T`, and
`E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X`. -/
theorem detGrouped_sym_nonempty :
    ∃ (m₁ : ℕ) (t : ℝ) (σ : Equiv.Perm (CTorus 3 3 9 m₁ (1 + 1))),
      0 < t ∧ σ ≠ 1 ∧ GenSymm 3 9 m₁ (1 + 1) (1 + 1) 0 σ ∧
      XiCData (hatStep m₁ 1 1 1).G' (hatStep m₁ 1 1 1).a (hatStep m₁ 1 1 1).ν (1 + 1) 1 t
        (hatStep m₁ 1 1 1).D' ∧
      ∀ z, ∃ (κ'' cdet : ℝ) (E : DetExpansionLocC (hatStep m₁ 1 1 1) 0 z t κ'' cdet)
        (E' : DetExpansionLocC (hatStep m₁ 1 1 1) 0 (rootAct σ z) t κ'' cdet)
        (Sy : LatSymm (hatStep m₁ 1 1 1).G' (hatStep m₁ 1 1 1).G' σ),
        (∀ D : BgData (hatStep m₁ 1 1 1).G' 2,
          XiCData (hatStep m₁ 1 1 1).G' (hatStep m₁ 1 1 1).a (hatStep m₁ 1 1 1).ν (1 + 1) 1 t D →
          XiCData (hatStep m₁ 1 1 1).G' (hatStep m₁ 1 1 1).a (hatStep m₁ 1 1 1).ν (1 + 1) 1 t
            (Sy.sym D)) ∧
        (∀ (D : BgData (hatStep m₁ 1 1 1).G' 2) T,
          E'.term (Sy.sym D) (cubeAct σ T) = E.term D T) ∧
        ∀ (D : BgData (hatStep m₁ 1 1 1).G' 2) (X : Set (CTorus 3 3 9 m₁ (1 + 1))),
          E'.detGrouped (Sy.sym D) (σ '' X) = E.detGrouped D X := by
  obtain ⟨m₁, c, BG, κ, t, c₂, BG₂, κdec, κ0, δc, h4, ht0, ⟨hC⟩, hκ0, hκdec, hκ, h1, hlog, hc7,
    hMX, hdm, hα, hsmX, -⟩ := directWitness_core_amp 2 1
  have hκ57 : (57 : ℝ) ≤ κ := by
    have e : 4 * ((3 : ℕ) : ℝ) * (((2 * 3 + 1) ^ 3 : ℕ) : ℝ) = 4116 := by norm_num
    rw [e] at hκ
    linarith
  have hz := detDeg_three_rate hκ57
  have hd0 : 0 < (3 : ℕ) := by norm_num
  have hδc : 0 ≤ δc := by
    have : 0 ≤ decDomMargin 3 3 2 BG κ (xiC1 3 * t) := by
      have : 0 < K4 3 3 2 BG κ := K4_pos hC.hS.fam.2.1 hd0
      have := one_le_xiC1 3
      unfold decDomMargin; positivity
    linarith
  have hD : XiCData (hatStep m₁ 1 1 1).G' (compWeight 3 1) nuW (1 + 1) 1 t
      (hatStep m₁ 1 1 1).D' := by
    refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
      exists_xiC (bgHypNu m₁) (Gp m₁ (rhoSep m₁)) hN2 (by unfold nuW; norm_num) ht0, ?_, ?_⟩
    · intro x hx i
      have := unitBg_Ψ_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
      rw [this]; simp
    · intro x hx i
      have := unitBg_h_of_mem (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2) hx i
      show (unitBg (Gp m₁ (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
      rw [this]; simp
  have hN : (3 : ℕ) ^ 0 ∣ 9 := by norm_num
  refine ⟨m₁, t, witnessSymm m₁, ht0, witnessSymm_ne_one m₁, genSymm_witnessSymm m₁, hD,
    fun z => ?_⟩
  obtain ⟨E, E', Sy, h1, h2, h3⟩ := exists_detExpansionLocC_grouped_sym (hatStep m₁ 1 1 1) hC hδc
    hMX hdm hα hsmX LevelPair.hatConn hN hz (hatStep m₁ 1 1 1).hG' rfl (genSymm_witnessSymm m₁) z
  exact ⟨_, _, E, E', Sy, h1, h2, h3⟩

end Balaban.Inhabited
