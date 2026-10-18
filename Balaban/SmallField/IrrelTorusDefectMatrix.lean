/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, GPT-6-Sol
-/
module

public import Balaban.SmallField.IrrelTorusDefectSmallSum
public import Balaban.SmallField.Def6AvgMomTorus

/-!
# Translation of the raw density Hessian

The second derivative of the full density at any aligned centre is transported to the origin
entry by entry. This uses `eucEloc` through `LiftCtx.D2_Eloc_translate'` and retains the full
two-index tensor, before taking its trace.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

/-- The exact algebra needed after spatial covariance of the raw moment has been proved:
reflections kill the off-diagonal entries, coordinate exchanges identify the diagonal entries,
and the renormalization condition kills their common trace. -/
theorem matrix_zero_of_hypercubic_symmetry {d : ℕ} (hd : 0 < d)
    (M : Fin d → Fin d → ℂ)
    (htrace : ∑ μ, M μ μ = 0)
    (hoff : ∀ μ ν, μ ≠ ν → M μ ν = 0)
    (hdiag : ∀ μ ν, M μ μ = M ν ν) :
    ∀ μ ν, M μ ν = 0 := by
  intro μ ν
  by_cases h : μ = ν
  · subst ν
    have hsum : (d : ℂ) * M μ μ = 0 := by
      calc
        (d : ℂ) * M μ μ = ∑ ξ : Fin d, M μ μ := by simp
        _ = ∑ ξ : Fin d, M ξ ξ := Finset.sum_congr rfl fun ξ _ => hdiag μ ξ
        _ = 0 := htrace
    have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
    exact (mul_eq_zero.mp hsum).resolve_left hd0
  · exact hoff μ ν h

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ} {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}

/-- The complete Hessian of `Eloc` at every aligned centre is the translated Hessian at the
origin. The class supplies `eucEloc`; the standard small-field numerical conditions produce
the analytic neighbourhood in which its derivatives may be taken. -/
theorem IsSFFamily2.D2_Eloc_translate
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hn : MomNum d L N k j ϱ P) (i₀ i₁ : Fin N)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (x v : CTorus d L N₁ m₁ k) :
    D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ (Tm N₁) j y ψ
        (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
        (blockDir L j x i₁) (blockDir L j v i₁) =
      D2 (fun ψ : Fld d L N₁ m₁ k N => Eloc P.m₀ (Tm N₁) j 0 ψ
        (eFld d L N₁ m₁ k N i₀)) (eFld d L N₁ m₁ k N i₀)
        (blockDir L j (x - y) i₁) (blockDir L j (v - y) i₁) := by
  obtain ⟨β', ν', -, -, hL⟩ := hF.toLanded
  have hn' := hn.noChi
  have hε := eps_pos (d := d) (L := L) hL.admissible.α₀_pos j
  have hρ0 := liftRadius_pos (d := d) (L := L) (N := N) hε i₀
  have hrad := liftRadius_spec (d := d) (L := L) (N := N) hε i₀ hn'.hsmall
  have ctx := hL.liftCtx N₁ hn'.hd hn'.hL hn'.hϱ hn'.hj1 hn'.hjk hρ0 hrad
  exact ctx.D2_Eloc_translate' i₀ i₁ hy x v

/-- The existing renormalization condition gives the trace of the infinite-volume second
moment at every integer centre. The off-diagonal and diagonal-equality identities still
require spatial covariance of the raw pair moment before this trace can imply a zero matrix. -/
theorem IsSFFamily2.raw_second_trace_zero
    (hF : IsSFFamily2 P Rg β a (completeXiDom P Rg a) Tm ρd Ek)
    {j : ℕ} (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) :
    ∃ β' ν' : ℕ → ℝ, ν' k = Rg.ν k ∧
      ∀ y : Site d, ∑' X' : Finset (Site d),
        MomY P.noChi β' ν' a Tm j i₀ i₁ y X' = 0 := by
  obtain ⟨β', ν', hν', -, hL⟩ := hF.toLanded
  exact ⟨β', ν', hν', fun y => momY_tsum_zero hL hn.noChi hne y⟩

end Balaban.SmallField.Def6v2
