/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityWitnessMin
public import Balaban.Fluctuation.StepRegWitness
public import Balaban.Fluctuation.StepIdentityReg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The background field of the step moves along the ray

For a step datum with `N = 2` whose block datum `θ` has the constant unit background
(`bgField G' θ = e₀`), the background field `φ_k(ψ^{(k)}) = e₀` is the constant unit field
(Lemma 2.2 (2.2)).  If the perpendicular mean of the spin `ψ = ψ^{(k)} + y` differs from that of
`ψ^{(k)}` (e.g. `y` a nonzero constant in the direction `e₁`), the constant `e₀` is not a
minimizer for `ψ` (`sum_perp_eq_zero`), so `φ_k(ψ) ≠ φ_k(ψ^{(k)})`, and some component
`svec φ_k` differs (`exists_bgComp_ne`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Inhabited
  Balaban.SmallField.Def6 Finset

theorem unitPhi_eq_constPhi {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
    (G : GeneratingSet d L N₀ K ϱ) : unitPhi G hN2 = constPhi G (N := 2) ![1, 0] := by
  funext p
  obtain ⟨x, i⟩ := p
  fin_cases i <;> simp [unitPhi, constPhi, unitVec]

namespace StepSetting

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {S : StepSetting d L N₁ m₁ k 2 ϱ}
  {pp : ℝ}

/-- **`φ_k(ψ^{(k)}) = e₀`** when the block datum has the constant unit background. -/
theorem RayData.bgField_psi0 (R : S.RayData pp)
    (hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2) :
    bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU S.psi0) =
      constPhi (stepG d L N₁ m₁ k ϱ) (N := 2) ![1, 0] := by
  obtain ⟨hDU', -⟩ := S.D'_domains R.H R.hδ'0 R.hδ' R.hD'R
  have h := (criticalPoint_real R.ha₁ S.hG S.hG' (le_refl (k + 1)) R.H R.H S.D' hDU').2.2.2.2.2.2.1
  rw [S.dataU_psi0 R.ha₁ R.H R.hδ'0 R.hδ' R.hD'R]
  refine h.trans ?_
  rw [hbg0, unitPhi_eq_constPhi]
  rfl

theorem RayData.weight_pos (R : S.RayData pp) :
    0 < S.a k / ((L : ℝ) ^ k) ^ 2 := by
  have hL : 2 ≤ L := by have := R.H.hL; omega
  have := compWeight_pos hL R.ha₁ S.hk1
  have hL' : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  exact div_pos this (by positivity)

/-- A minimizer property of the unit constant at the datum `ψ` forces the perpendicular mean of
`ψ` to equal that of the datum it is a minimizer for. -/
theorem RayData.bgField_ne (R : S.RayData pp)
    (hν : S.ν = 0) (hbg0 : bgField S.G' S.a S.ν S.D' = unitPhi S.G' hN2) {ψ : S.E}
    (hdom : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU ψ)) {η : ℝ}
    (hη : η ≠ 0) (hψ : ∀ x, liftU S.hG' ψ x 1 = liftU S.hG' S.psi0 x 1 + η) :
    bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ) ≠
      bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU S.psi0) := by
  intro heq
  have hdom0 : InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU S.psi0) := by
    have := R.dom (q := (0, 0)) (by simp [R.hpp])
    simpa [psiAt_zero] using this
  have hreal : ∀ ψ' : S.E, ∀ x i, ((S.dataU ψ').Ψ x i).im = 0 := by
    intro ψ' x i; rw [S.dataU_Ψ]; simp
  have hmin : ∀ ψ' : S.E, InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU ψ') →
      IsMinimizer (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ')
        (bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ')) := by
    intro ψ' hd
    obtain ⟨φ, hφ, hu⟩ := (theorem71 R.H hd).1
    rw [bgField_eq hφ hu]; exact hφ
  have hc0 := R.bgField_psi0 hbg0
  have key : ∀ ψ' : S.E, InUnionDomainR (stepG d L N₁ m₁ k ϱ) (bgC1 d L 2) S.ν (S.dataU ψ') →
      bgField (stepG d L N₁ m₁ k ϱ) S.a S.ν (S.dataU ψ') =
        constPhi (stepG d L N₁ m₁ k ϱ) (N := 2) ![1, 0] →
      ∑ x : (stepG d L N₁ m₁ k ϱ).Ω 1, (liftU S.hG' ψ' x 1) = 0 := by
    intro ψ' hd hb
    have := sum_perp_eq_zero S.hG S.a (S.dataU ψ') (hreal ψ') R.weight_pos (by
      intro σ hσ
      have h1 := (hmin ψ' hd).2.2 σ hσ
      rw [hb] at h1
      rw [hν] at h1
      exact h1)
    simpa [S.dataU_Ψ] using this
  have h1 := key S.psi0 hdom0 hc0
  have h2 := key ψ hdom (heq.trans hc0)
  have hsum : ∑ x : (stepG d L N₁ m₁ k ϱ).Ω 1, liftU S.hG' ψ x 1 =
      ∑ x : (stepG d L N₁ m₁ k ϱ).Ω 1, liftU S.hG' S.psi0 x 1 +
        η * (Fintype.card ((stepG d L N₁ m₁ k ϱ).Ω 1) : ℝ) := by
    rw [Finset.sum_congr rfl fun x _ => hψ x.1, Finset.sum_add_distrib]
    simp [mul_comm]
  have hcard : (0 : ℝ) < (Fintype.card ((stepG d L N₁ m₁ k ϱ).Ω 1) : ℝ) := by
    have : Nonempty ((stepG d L N₁ m₁ k ϱ).Ω 1) := ⟨⟨0, (S.hG 0).1⟩⟩
    exact_mod_cast Fintype.card_pos
  rw [h1, h2] at hsum
  have : η * (Fintype.card ((stepG d L N₁ m₁ k ϱ).Ω 1) : ℝ) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact hη h
  · exact hcard.ne' h

end StepSetting

end Balaban.Fluctuation
