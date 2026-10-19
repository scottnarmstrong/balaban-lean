/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomMass

/-!
# The real domain of a datum from its sphere and pair bounds (blocker 4)

`inDomainR_of_r1_r2`: a real datum `D` of a generating set `G` with the constant direction `h`
(`|h| = 1`) on `Ω₁` lies in `Ψ̃(G; ν, δ)` as soon as

* (R2) `| Σ_i Re Ψ(x)_i² - 1 | < δ` at the data sites,
* (R1) `rn (Re Ψ(x) - Re Ψ(x')) < δ` for the interface pairs,
* `2 ν L^{2k} < δ²` (the clauses (R3), (R4) are then automatic: `|1 - u·h/|u|| ≤ 2` and
  `|h|² = 1`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The real domain from the sphere and pair bounds.** -/
theorem inDomainR_of_r1_r2 (G : GeneratingSet d L N₀ k ϱ) (D : BgData G N) (hv : Fin N → ℝ)
    {ν δ : ℝ} (hν : 0 ≤ ν) (hsum : ∑ i, hv i ^ 2 = 1) (hδ : 0 < δ)
    (hmass : 2 * ν * ((L : ℝ) ^ k) ^ 2 < δ ^ 2)
    (hreal : ∀ x ∈ dataSites G, ∀ i, (D.Ψ x i).im = 0)
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (hv i : ℂ))
    (hR1 : ∀ x x', IsInterfacePair G x x' →
      rn (fun i => (D.Ψ x i).re - (D.Ψ x' i).re) < δ)
    (hR2 : ∀ x ∈ dataSites G, |∑ i, ((D.Ψ x i).re) ^ 2 - 1| < δ) :
    InDomainR G ν δ D := by
  refine ⟨fun x i => (D.Ψ x i).re, hv, ⟨?_, hR1, hR2, ?_, ?_⟩, ?_, hh⟩
  · intro n hn1 hnk x hx x' hx'
    funext i
    have := D.Ψ_layerConst n hn1 hnk x hx x' hx'
    simp only [this]
  · intro x hx
    have h2 := abs_one_sub_inner_div_rn_le_two (u := fun i => (D.Ψ x i).re) (h := hv) hsum
    have hℓ : ((L : ℝ) ^ G.layerIndex x) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 := by
      have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast NeZero.pos L
      have := pow_le_pow_right₀ hL1 (layerIndex_le_k G x)
      exact pow_le_pow_left₀ (by positivity) this 2
    have hnn : 0 ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 := by positivity
    calc ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
          |1 - (∑ i, (D.Ψ x i).re * hv i) / rn (fun i => (D.Ψ x i).re)|
        ≤ ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * 2 := mul_le_mul_of_nonneg_left h2 hnn
      _ ≤ ν * ((L : ℝ) ^ k) ^ 2 * 2 := by
          have := mul_le_mul_of_nonneg_left hℓ hν
          linarith
      _ < δ ^ 2 := by linarith
  · simp only [hsum, sub_self, abs_zero, mul_zero]
    positivity
  · intro x hx i
    apply Complex.ext
    · simp
    · simpa using hreal x hx i

end Balaban.LargeField
