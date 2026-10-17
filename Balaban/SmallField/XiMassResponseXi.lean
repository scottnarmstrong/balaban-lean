/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiMassResponseBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The mass response of the class domain at a fixed level (decision D2(b), Step 2, part 3)

* `xiCOne_of_xiAt`: the real datum of a member of `Ξ_k(𝔹; 1, e)` is a member of `Ξ^c_k(𝔹; 1, e)`
  with the zero displacement;
* `xiC_massResponse_top`: `Ξ^c_k(𝔹; 1, e)` at the mass `ν` lies in `Ξ^c_k(𝔹; 1, e (1 + K_m |t|))`
  at the mass `μ = ν (1 + t)`, `K_m = 1 + 16 (N + 1) K₂`;
* `xiC_massResponse`: the same at a level `j`, given the top-level norm clause.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban.Background Balaban.Multiscale Balaban.Fluctuation Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Real

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν e : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}

/-- A real datum of `Ξ_k(𝔹; 1, e)` is a datum of `Ξ^c_k(𝔹; 1, e)` with zero displacement. -/
theorem xiCOne_of_xiAt (H : BgHyp d L k ϱ a ν) (hε : 0 < e) {Dr : BgData G N}
    (hXr : XiAt G a ν k 1 e Dr Ψ₀ h₀) : XiCOne G a ν e Dr := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨hR, hDom, hbr⟩ := hXr
  obtain ⟨hf, hm⟩ := theorem72_real H hDom
  have hR' : RealizesC Dr Ψ₀ h₀ 0 0 :=
    ⟨fun x hx i => by simpa using hR.1 x hx i, fun x hx i => by simpa using hR.2 x hx i⟩
  have hp : ∀ x : Torus d (N₀ * L ^ k), 0 < G.spacing x := fun x => spacing_pos G
  refine ⟨Ψ₀, h₀, 0, 0, ⟨one_pos, hε, Dr, Dr, ⟨hR, hDom, hbr⟩, hR',
    inUnionDomainC_of_R hd0 H.massLe hDom, ?_⟩, hR'⟩
  rw [hf, hm]
  have hz : vn (fun _ : Fin N => (0 : ℂ)) = 0 := vn_zero
  have hb0 : ∀ (x : Torus d (N₀ * L ^ k)) (i : Fin N),
      blockAvg G (0 : G.Ω 1 × Fin N → ℂ) x i = 0 := fun x i => by
    have := blockAvg_add (G := G) 0 0 x i
    simpa using this
  refine ⟨fun x hx m => ⟨?_, ?_⟩, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz' z'' hz'' hadj => ?_, fun x hx => ?_, fun x => ?_⟩
  · simpa [hz] using div_pos (by linarith : 0 < 1 * e) (hp x)
  · simpa [hz] using div_pos (by linarith : 0 < 1 * e) (hp x)
  · have : 0 < 1 ^ 2 * e / G.spacing x ^ 2 := div_pos (by linarith) (by have := hp x; positivity)
    simpa [hz] using this
  · simpa using hε
  · simpa [hz] using hε
  · simp [hb0, hz]; positivity
  · simp [hz]; positivity
  · simp [vn_zero]; positivity
  · simp; positivity

end Real

section Response

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν μ : ℝ}
  {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
  {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}

/-- **The mass response of the real background** (deliverable (1)): for a real datum of
`Ξ_k(𝔹; 1, e)` at the mass `ν` and `μ = ν (1 + t)`, the datum lies in the real union domain at the
mass `μ` and `bgField`, `bgMult` at `μ` are those at `ν` plus an increment `(δφ, δα)` with
`‖δφ‖_*, |δα|₂ ≤ 8 K₂ e |t|`.  Proof: `xiCOne_of_xiAt` and `massResponse_single`, with
`theorem72_real` identifying the complex and the real backgrounds at both masses. -/
theorem massResponse_real (H : BgHyp d L k ϱ a ν) (H' : BgHyp d L k ϱ a μ) {e t r : ℝ}
    (hε : 0 < e) (hsm : (4 * d + 6) * ((2 * d + 1) * e) ≤ 1)
    (hc1 : 4 * (xiC1 d * e) ≤ bgC1 d L N) (hμ : μ = ν * (1 + t)) (ht1 : |t| ≤ 1)
    (htr : |t| < r) (hr : r ≤ 1 / 16)
    (hK : bgK1 d L N * (xiC1 d * e) + 3 * r ≤ deltaStar d L N)
    (hζ : 8 * e * r ≤ deltaStar d L N) {Dr : BgData G N}
    (hXr : XiAt G a ν k 1 e Dr Ψ₀ h₀) :
    InUnionDomainR G (bgC1 d L N) μ Dr ∧
      ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
        bgField G a μ Dr = bgField G a ν Dr + δφ ∧ bgMult G a μ Dr = bgMult G a ν Dr + δα ∧
        SupBounds G δφ (cK2 d L N * (8 * e * |t|)) ∧
        Small G δα (cK2 d L N * (8 * e * |t|)) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hC1 := one_le_xiC1 d
  have hδ0 : 0 < xiC1 d * e := by positivity
  have ht0 := abs_nonneg t
  have hXi : Xi G a ν k 1 e Ψ₀ h₀ := ⟨one_pos, hε, Dr, hXr⟩
  have hP : InPsiTilde G ν (xiC1 d * (1 * e)) Ψ₀ h₀ :=
    xi_subset_psiTilde H le_rfl (by simpa using hsm) hXi
  rw [one_mul] at hP
  have hDR : InDomainR G ν (xiC1 d * e) Dr := ⟨Ψ₀, h₀, hP, hXr.1.1, hXr.1.2⟩
  have hμle : μ ≤ (1 + |t|) * ν := by
    rw [hμ, mul_comm ν]
    exact mul_le_mul_of_nonneg_right (by linarith [le_abs_self t]) H.mass
  have hrad : (1 + |t|) * (xiC1 d * e) ≤ bgC1 d L N := by nlinarith
  have hDR' : InUnionDomainR G (bgC1 d L N) μ Dr :=
    inUnionDomainR_of_scaled hδ0 ht0 hμle hrad hDR
  refine ⟨hDR', ?_⟩
  obtain ⟨-, δφ, δα, hf, hm, hsup, hsmall⟩ :=
    massResponse_single H H' hε hsm hc1 hμ ht1 htr hr hK hζ (xiCOne_of_xiAt H hε hXr)
  obtain ⟨f1, m1⟩ := theorem72_real H hXr.2.1
  obtain ⟨f2, m2⟩ := theorem72_real H' hDR'
  exact ⟨δφ, δα, by rw [← f2, hf, f1], by rw [← m2, hm, m1], hsup, hsmall⟩

end Response

end Balaban.SmallField
