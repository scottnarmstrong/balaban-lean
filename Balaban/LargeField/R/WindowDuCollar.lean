/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Lemma25

/-!
# A datum with zero collar is not in the real data domain (blocker 4)

The datum `Du` of `window_hbG_sum` has `Du.Ψ = 0` off `Ω₁` (`_hDu0`), hence on the collar
`C(Ω₁)`.  The real domain `Ψ̃(G; δ)` (clause (R2): `|∑_i Ψ(x)_i² - 1| < δ` on all `dataSites`,
collar included) with `δ ≤ c₁ ≤ 1/1024` does not contain such a datum as soon as the collar is
nonempty.  `not_inUnionDomainR_of_collar_zero`: a datum vanishing at one collar site is not in
`𝒟_ℝ`, for any mass.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **A datum vanishing at a collar site is not in the real domain `𝒟_ℝ`.** -/
theorem not_inUnionDomainR_of_collar_zero (hd : 0 < d) {G : GeneratingSet d L N₀ k ϱ}
    (D : BgData G N) {c : Torus d (N₀ * L ^ k)} (hc : c ∈ collar G) (h0 : ∀ i, D.Ψ c i = 0)
    (ν : ℝ) : ¬ InUnionDomainR G (bgC1 d L N) ν D := by
  rintro ⟨δ, hδ0, hδ1, Ψ, h, hdom, hΨ, -⟩
  have hcd : c ∈ dataSites G := (mem_dataSites G).2 (Or.inr hc)
  have hz : ∀ i, Ψ c i = 0 := fun i => by
    have := hΨ c hcd i
    rw [h0 i] at this
    exact_mod_cast this.symm
  have h2 := hdom.r2 c hcd
  simp only [hz, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero,
    zero_sub, abs_neg, abs_one] at h2
  have h3 := bgC1_le_small d L N hd
  linarith

end Balaban.LargeField
