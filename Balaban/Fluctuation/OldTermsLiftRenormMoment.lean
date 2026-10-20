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
The old sides `L * idx' n` of a sequence of new tori form such a subsequence.  The finite-torus
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

/-- The old sides `L * (n + 1)` along the tori `n + 1` are cofinal in the tori `n + 1`; for the
read tori `L^{m₀} (n + 1)` the old side `L * L^{m₀} (n + 1)` is the torus of index `L (n + 1) - 1`. -/
theorem torusSeq_old_side (m₀ n : ℕ) :
    L * torusSeq L m₀ n = torusSeq L m₀ (L * (n + 1) - 1) := by
  have hpos : 0 < L * (n + 1) := Nat.mul_pos (NeZero.pos L) (Nat.succ_pos n)
  unfold torusSeq
  rw [Nat.sub_add_cancel hpos]
  ring

/-- A pointwise finite-torus moment transport yields the inherited moment limit, along any
sequence `idx'` of new tori whose old sides `L * idx' n` are the terms `idx (φ n)` of the sequence
`idx` of the old limit, with `φ` tending to infinity. -/
theorem liftOldTermsFam_renormMoment_of_eq {idx idx' φ : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}
    (hidx' : ∀ n, idx' n ≠ 0) (hφ : Tendsto φ atTop atTop)
    (hrel : ∀ n, L * idx' n = idx (φ n))
    (hEq : ∀ n, haveI : NeZero (idx' n) := ⟨hidx' n⟩
      momentSum m₀ (liftOldTerms (Tm (L * idx' n))) j i₀ i₁ =
        momentSum m₀ (Tm (L * idx' n)) j i₀ i₁)
    (hR : RenormCondAlong m₀ k νk Tm j idx hidx) (hne : i₀ ≠ i₁) :
    Tendsto (fun n : ℕ => haveI : NeZero (idx' n) := ⟨hidx' n⟩
      momentSum m₀ (liftOldTermsFam Tm (idx' n)) j i₀ i₁) atTop (𝓝 0) := by
  have hlim := (hR.moment i₀ i₁ hne).comp hφ
  refine hlim.congr fun n => ?_
  have key : ∀ t t' : ℕ, t = t' → ∀ (h : NeZero t) (h' : NeZero t'),
      momentSum m₀ (Tm t) j i₀ i₁ = momentSum m₀ (Tm t') j i₀ i₁ := by
    intro t t' e; subst e; intros; rfl
  have : NeZero (idx' n) := ⟨hidx' n⟩
  have h1 := hEq n
  simp only [Function.comp_apply]
  rw [liftOldTermsFam_apply]
  rw [h1]
  exact (key _ _ (hrel n) _ _).symm

/-- All four inherited renormalization conditions, with the finite-torus
moment equality displayed as the remaining analytic input. -/
theorem liftOldTermsFam_renormCond {idx idx' φ : ℕ → ℕ} {hidx : ∀ n, idx n ≠ 0}
    (hidx' : ∀ n, idx' n ≠ 0) (hφ : Tendsto φ atTop atTop)
    (hrel : ∀ n, L * idx' n = idx (φ n))
    (hT : TorusIndep m₀ Tm)
    (hR : RenormCondAlong m₀ k νk Tm j idx hidx) (hν : 0 < νk)
    (hj1 : 1 ≤ j) (hjk : j ≤ k) (νK : ℝ)
    (hEq : ∀ (i₀ i₁ : Fin N), i₀ ≠ i₁ → ∀ n, haveI : NeZero (idx' n) := ⟨hidx' n⟩
      momentSum m₀ (liftOldTerms (Tm (L * idx' n))) j i₀ i₁ =
        momentSum m₀ (Tm (L * idx' n)) j i₀ i₁) :
    RenormCondAlong m₀ (k + 1) νK (liftOldTermsFam Tm) j idx' hidx' where
  val i₀ := liftOldTermsFam_renormVal hT hR hj1 hjk i₀
  dh i₀ _ := liftOldTermsFam_renormDh hT hR hν hj1 hjk i₀
  dpsi i₀ := liftOldTermsFam_renormDpsi hT hR hj1 hjk i₀
  moment i₀ i₁ hne := liftOldTermsFam_renormMoment_of_eq hidx' hφ hrel (hEq i₀ i₁ hne) hR hne

end Balaban.Fluctuation
