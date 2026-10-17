/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.OldTermsLiftRenorm
public import Balaban.Fluctuation.OldTermsLiftMomentSum

/-!
# The inherited thermodynamic second-moment condition

The old renormalization condition converges along every cofinal subsequence.
The old sides `L * (n + 1)` form such a subsequence.  The finite-torus
identity is supplied by `liftOldTerms_momentSum` once analyticity at the
reference field is known.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.SmallField.Def6 Filter Topology

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {m₀ : ℕ}
  {Tm : ∀ (N₂ : ℕ) [NeZero N₂], Terms d L N₂ m₁ k N ϱ}
  {j : ℕ} {νk : ℝ} {i₀ i₁ : Fin N}

/-- Cofinality of the old physical side parameters. -/
theorem oldSideSeq_tendsto_atTop :
    Tendsto (fun n : ℕ => L * (n + 1) - 1) atTop atTop := by
  apply Filter.tendsto_atTop.2
  intro b
  filter_upwards [Filter.eventually_ge_atTop b] with n hn
  have hle : n + 1 ≤ L * (n + 1) :=
    Nat.le_mul_of_pos_left _ (NeZero.pos L)
  omega

/-- A pointwise finite-torus moment transport yields the inherited moment limit. -/
theorem liftOldTermsFam_renormMoment_of_eq
    (hEq : ∀ (N₂ : ℕ) [NeZero N₂],
      momentSum m₀ (liftOldTerms (Tm (L * N₂))) j i₀ i₁ =
        momentSum m₀ (Tm (L * N₂)) j i₀ i₁)
    (hR : RenormCond m₀ k νk Tm j) (hne : i₀ ≠ i₁) :
    Tendsto (fun n : ℕ => haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
      momentSum m₀ (liftOldTermsFam Tm (n + 1)) j i₀ i₁) atTop (𝓝 0) := by
  have hlim := (hR.moment i₀ i₁ hne).comp
    (oldSideSeq_tendsto_atTop (L := L))
  have hindex (n : ℕ) : (L * (n + 1) - 1) + 1 = L * (n + 1) := by
    have hpos : 0 < L * (n + 1) := Nat.mul_pos (NeZero.pos L) (Nat.succ_pos n)
    omega
  simp only [Function.comp_def] at hlim
  have hfun :
      (fun n : ℕ => haveI : NeZero (n + 1) := ⟨Nat.succ_ne_zero n⟩
        momentSum m₀ (liftOldTermsFam Tm (n + 1)) j i₀ i₁) =
      (fun n : ℕ => haveI : NeZero (L * (n + 1)) :=
          ⟨Nat.mul_ne_zero (NeZero.ne L) (Nat.succ_ne_zero n)⟩
        momentSum m₀ (Tm (L * (n + 1))) j i₀ i₁) := by
    funext n
    simpa only [liftOldTermsFam_apply] using hEq (n + 1)
  rw [hfun]
  convert hlim using 1
  funext n
  let F : ℕ → ℂ := fun t =>
    if ht : t = 0 then 0 else
      letI : NeZero t := ⟨ht⟩
      momentSum m₀ (Tm t) j i₀ i₁
  have ha : F (L * (n + 1) - 1 + 1) =
      momentSum m₀ (Tm (L * (n + 1) - 1 + 1)) j i₀ i₁ := by
    simp [F]
  have hb : F (L * (n + 1)) =
      momentSum m₀ (Tm (L * (n + 1))) j i₀ i₁ := by
    have hne : L * (n + 1) ≠ 0 :=
      Nat.mul_ne_zero (NeZero.ne L) (Nat.succ_ne_zero n)
    simp [F, hne]
  calc
    momentSum m₀ (Tm (L * (n + 1))) j i₀ i₁ = F (L * (n + 1)) := hb.symm
    _ = F (L * (n + 1) - 1 + 1) := congrArg F (hindex n).symm
    _ = momentSum m₀ (Tm (L * (n + 1) - 1 + 1)) j i₀ i₁ := ha

/-- All four inherited renormalization conditions, with the finite-torus
moment equality displayed as the remaining analytic input. -/
theorem liftOldTermsFam_renormCond
    (hT : TorusIndep m₀ Tm)
    (hR : RenormCond m₀ k νk Tm j) (hν : 0 < νk)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (νK : ℝ)
    (hEq : ∀ (i₀ i₁ : Fin N), i₀ ≠ i₁ → ∀ (N₂ : ℕ) [NeZero N₂],
      momentSum m₀ (liftOldTerms (Tm (L * N₂))) j i₀ i₁ =
        momentSum m₀ (Tm (L * N₂)) j i₀ i₁) :
    RenormCond m₀ (k + 1) νK (liftOldTermsFam Tm) j where
  val i₀ := liftOldTermsFam_renormVal hT hR hj1 hjk i₀
  dh i₀ _ := liftOldTermsFam_renormDh hT hR hν hj1 hjk i₀
  dpsi i₀ := liftOldTermsFam_renormDpsi hT hR hj1 hjk i₀
  moment i₀ i₁ hne := liftOldTermsFam_renormMoment_of_eq (hEq i₀ i₁ hne) hR hne

end Balaban.Fluctuation
