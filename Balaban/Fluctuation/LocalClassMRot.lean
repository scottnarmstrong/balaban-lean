/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassRot
public import Balaban.Fluctuation.LocalClassM
public import Balaban.Green.FinalConnectedSupport

/-!
# Rotation covariance of the source terms `ℳ` on the local chart (clause `rotM`)

The coefficient `coef f C` of the localization expansion is linear in `f` for functions analytic on
a polydisc of radius `R > 1` (`coef_sum_linear`): by Möbius inversion of
`f (1_A) = ∑_{B ⊆ A} coef f B` (`sum_powerset_coef`).  Hence the term `evTerm` is linear in the
function expanded (`evTerm_sum_linear`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban.Analysis Balaban.Green Finset

section CoefLinear

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- **The expansion at a vertex of the cube**: for `f` analytic on the polydisc of radius
`R > 1`, `f (1_A) = ∑_{B ⊆ A} coef f B`, where `1_A` is the indicator of `A`. -/
theorem sum_powerset_coef {R : ℝ} (hR : 1 < R) {f : (ι → ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (polydisc (0 : ι → ℂ) (fun _ => R))) (A : Finset ι) :
    f (fun i => if i ∈ A then 1 else 0) = ∑ B ∈ A.powerset, coef f B := by
  classical
  have hR0 : 0 < R := by linarith
  have hA := analyticOnNhd_comp_proj hf A hR0
  have h1 := sum_coef_eq hR hA
  have h1' : f (fun i => if i ∈ A then 1 else 0) =
      ∑ C : Finset ι, coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C := h1
  rw [h1']
  have hz : ∀ C ∈ (Finset.univ : Finset (Finset ι)), C ∉ A.powerset →
      coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C = 0 := by
    intro C _ hC
    rw [Finset.mem_powerset] at hC
    obtain ⟨i₀, hi₀C, hi₀A⟩ := Finset.not_subset.1 hC
    refine coef_eq_zero_of_inv hi₀C ?_
    intro w _ τ
    dsimp only
    congr 1
    funext i
    by_cases hi : i ∈ A
    · have : i ≠ i₀ := fun h => hi₀A (h ▸ hi)
      simp [hi, Pi.single_eq_of_ne this]
    · simp [hi]
  calc ∑ C : Finset ι, coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C
      = ∑ C ∈ A.powerset, coef (fun s : ι → ℂ => f (fun i => if i ∈ A then s i else 0)) C :=
        (Finset.sum_subset (Finset.subset_univ _) hz).symm
    _ = ∑ B ∈ A.powerset, coef f B := by
        refine Finset.sum_congr rfl fun C hC => coef_congr fun w hw => ?_
        rw [Finset.mem_powerset] at hC
        congr 1
        funext i
        by_cases hi : i ∈ A
        · simp [hi]
        · simp [hi, hw i (fun hiC => hi (hC hiC))]

/-- **The coefficient `coef` is linear** on functions analytic on the polydisc of radius `R > 1`. -/
theorem coef_sum_linear {R : ℝ} (hR : 1 < R) {J : Type*} (𝒥 : Finset J) (a : J → ℂ)
    (f : J → (ι → ℂ) → ℂ)
    (hf : ∀ j ∈ 𝒥, AnalyticOnNhd ℂ (f j) (polydisc (0 : ι → ℂ) (fun _ => R))) (C : Finset ι) :
    coef (fun s => ∑ j ∈ 𝒥, a j * f j s) C = ∑ j ∈ 𝒥, a j * coef (f j) C := by
  classical
  have hg : AnalyticOnNhd ℂ (fun s => ∑ j ∈ 𝒥, a j * f j s)
      (polydisc (0 : ι → ℂ) (fun _ => R)) := fun s hs =>
    Finset.analyticAt_fun_sum _ fun j hj => analyticAt_const.mul (hf j hj s hs)
  induction C using Finset.strongInduction with
  | H C ih =>
    have hCmem : C ∈ C.powerset := Finset.mem_powerset.2 (Finset.Subset.refl C)
    have e0 := sum_powerset_coef hR hg C
    have e1 : ∀ j ∈ 𝒥, f j (fun i => if i ∈ C then 1 else 0) = ∑ B ∈ C.powerset, coef (f j) B :=
      fun j hj => sum_powerset_coef hR (hf j hj) C
    rw [← Finset.add_sum_erase _ _ hCmem] at e0
    have e2 : ∑ j ∈ 𝒥, a j * f j (fun i => if i ∈ C then 1 else 0) =
        ∑ j ∈ 𝒥, a j * (coef (f j) C + ∑ B ∈ C.powerset.erase C, coef (f j) B) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [e1 j hj, ← Finset.add_sum_erase _ _ hCmem]
    have e3 : ∑ B ∈ C.powerset.erase C, coef (fun s => ∑ j ∈ 𝒥, a j * f j s) B =
        ∑ j ∈ 𝒥, a j * ∑ B ∈ C.powerset.erase C, coef (f j) B := by
      rw [Finset.sum_congr rfl (fun B hB => ih B (Finset.ssubset_iff_subset_ne.2 ⟨Finset.mem_powerset.1
        (Finset.mem_of_mem_erase hB), Finset.ne_of_mem_erase hB⟩)), Finset.sum_comm]
      simp only [Finset.mul_sum]
    have e4 : ∑ j ∈ 𝒥, a j * f j (fun i => if i ∈ C then 1 else 0) =
        (fun s => ∑ j ∈ 𝒥, a j * f j s) (fun i => if i ∈ C then 1 else 0) := rfl
    have := e0.symm.trans (e4.symm.trans e2)
    simp only [mul_add, Finset.sum_add_distrib] at this
    rw [e3] at this
    exact add_right_cancel this

end CoefLinear

end Balaban.Localization
