/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalValue
public import Balaban.Localization.I5Chain
public import Balaban.LargeField.Background.CubeUnitBg

/-!
# The constant datum lies in the class chart `Ξ^c`

A6-3 (a), step (P2), `hθ`: the physical point of the last integral is the constant configuration
`ψ_k ≡ h`, whose datum is `(e, e)`. For every generating set, weights, mass `ν` with `BgHyp`, level
`n`, and radii `σ, ε > 0`, the constant unit datum is a member of `Ξ^c_n(𝔹; σ, ε)` (`XiCData`):
the background is the constant field with multiplier `0`, and every inequality of `XiBounds` and
`XiCBounds` is a strict inequality between `0` and a positive number.
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField Balaban.SmallField
  Balaban.Localization Balaban.RootFSpine

namespace Balaban.RootFSpine

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **`hθ` at the physical point**: the constant unit datum is in the class chart `Ξ^c_n(𝔹; σ, ε)`
for all `n`, `σ, ε > 0`. -/
theorem constUnitBg_xiCData (H : BgHyp d L K ϱ a ν) {e : Fin N → ℝ} (he : ∑ i, e i ^ 2 = 1)
    (n : ℕ) {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    XiCData G a ν n σ ε (constUnitBg G e) := by
  classical
  have hf : bgField G a ν (constUnitBg G e) = constUnitPhi G e := bgField_constUnitBg H he
  have hα : bgMult G a ν (constUnitBg G e) = 0 := bgMult_constUnitBg H he
  have hfC : bgFieldC G a ν (bgC0 d L N) (constUnitBg G e) = constUnitPhi G e :=
    bgFieldC_constUnitBg H he
  have hαC : bgMultC G a ν (bgC0 d L N) (constUnitBg G e) = 0 := bgMultC_constUnitBg H he
  have hbar : ∀ y ∈ dataSites G, ∀ i, barField G (constUnitBg G e).Ψ (constUnitPhi G e) y i =
      (e i : ℂ) := fun y hy i => barField_constUnitPhi e hy i
  have hΨ : ∀ y ∈ dataSites G, ∀ i, (constUnitBg G e).Ψ y i = (e i : ℂ) :=
    fun y hy i => constUnitBg_Ψ hy i
  have hz : (fun i : Fin N => (e i : ℂ) - (e i : ℂ)) = 0 := funext fun i => sub_self _
  have hvn0 : vn (fun i : Fin N => (e i : ℂ) - (e i : ℂ)) = 0 := by rw [hz]; exact vn_zero
  have hσε : 0 < σ * ε := mul_pos hσ hε
  have hpos : ∀ x : Torus d (N₁ * L ^ m₁ * L ^ K), 0 < G.spacing x := fun x => spacing_pos G
  have hXiAt : XiAt G a ν n σ ε (constUnitBg G e) (fun _ => e) e := by
    refine ⟨⟨fun x hx i => hΨ x hx i, fun x hx i => constUnitBg_h hx i⟩,
      constUnitBg_inUnionDomainR H he, ?_⟩
    rw [hf, hα]
    refine ⟨fun x hx μ => ⟨?_, ?_⟩, fun x hx => ?_, fun x => ?_, fun x hx => ?_,
      fun z hz z' hz' _ => ?_, fun z => ?_, ?_⟩
    · have h1 := hbar _ (mem_dataSites_add hx μ)
      have h0 := hbar _ ((mem_dataSites G).2 (Or.inl hx))
      simp only [h1, h0, hvn0]; exact div_pos hσε (hpos x)
    · have h1 := hbar _ (mem_dataSites_sub hx μ)
      have h0 := hbar _ ((mem_dataSites G).2 (Or.inl hx))
      simp only [h1, h0, hvn0]; exact div_pos hσε (hpos x)
    · have hlap : (fun i : Fin N => ∑ μ : Fin d,
          (barField G (constUnitBg G e).Ψ (constUnitPhi G e) (x + Pi.single μ 1) i +
            barField G (constUnitBg G e).Ψ (constUnitPhi G e) (x - Pi.single μ 1) i -
            2 * barField G (constUnitBg G e).Ψ (constUnitPhi G e) x i)) = 0 := by
        funext i
        refine Finset.sum_eq_zero fun μ _ => ?_
        rw [hbar _ (mem_dataSites_add hx μ), hbar _ (mem_dataSites_sub hx μ),
          hbar _ ((mem_dataSites G).2 (Or.inl hx))]
        ring
      rw [hlap, vn_zero]
      exact div_pos (mul_pos (pow_pos hσ 2) hε) (pow_pos (hpos x) 2)
    · simp only [Pi.zero_apply, norm_zero, mul_zero]
      exact mul_pos (pow_pos hσ 2) hε
    · have : (fun i : Fin N => (constUnitBg G e).Ψ x i - blockAvg G (constUnitPhi G e) x i) = 0 := by
        funext i
        rw [hΨ x ((mem_dataSites G).2 (Or.inl hx)), blockAvg_constUnitPhi e hx]
        simp
      rw [this, vn_zero]
      exact mul_pos (pow_pos hσ 2) hε
    · have : (fun i : Fin N => (constUnitBg G e).Ψ z i - (constUnitBg G e).Ψ z' i) = 0 := by
        funext i
        rw [hΨ z ((mem_dataSites G).2 (Or.inr hz)), hΨ z' ((mem_dataSites G).2 (Or.inr hz'))]
        simp
      rw [this, vn_zero]
      exact hσε
    · have : (fun i : Fin N => constUnitPhi G e (z, i) - ((e i : ℝ) : ℂ)) = 0 := by
        funext i; simp [constUnitPhi]
      rw [this, vn_zero, mul_zero]
      exact hσε
    · have : ∑ i, e i ^ 2 - 1 = 0 := by rw [he]; simp
      rw [this]
      simpa using pow_pos hσε 2
  refine ⟨fun _ => e, e, 0, 0, ⟨hσ, hε, constUnitBg G e, constUnitBg G e, hXiAt,
    ⟨fun x hx i => by simpa using hΨ x hx i, fun x hx i => by simpa using constUnitBg_h hx i⟩,
    (constUnitBg_inUnionDomainC H he).mono (bgC2_le_bgC1 d L N), ?_⟩,
    ⟨fun x hx i => by simpa using hΨ x hx i, fun x hx i => by simpa using constUnitBg_h hx i⟩⟩
  rw [hf, hαC, hfC, hα]
  have hv0 : vn (fun _ : Fin N => (0 : ℂ)) = 0 := vn_zero
  have hsq : 0 < σ ^ 2 * ε := mul_pos (pow_pos hσ 2) hε
  refine ⟨fun x hx μ => ⟨?_, ?_⟩, fun x hx => ?_, fun x => ?_, fun x => ?_, fun x hx => ?_,
    fun z hz z' hz' _ => ?_, fun x hx => ?_, fun x => ?_⟩
  · simp only [sub_self, hv0]; exact div_pos hσε (hpos x)
  · simp only [sub_self, hv0]; exact div_pos hσε (hpos x)
  · simp only [sub_self, add_zero, mul_zero, Finset.sum_const_zero, hv0]
    exact div_pos hsq (pow_pos (hpos x) 2)
  · simp only [Pi.zero_apply, sub_self, norm_zero, mul_zero]; exact hsq
  · simp only [sub_self, hv0]; exact hε
  · have : constUnitPhi G e - constUnitPhi G e = 0 := sub_self _
    simp only [this, blockAvg_zero, Pi.zero_apply, sub_self, hv0]; exact hsq
  · simp only [Pi.zero_apply, sub_self, hv0]; exact hσε
  · simp only [Pi.zero_apply, vn_zero, mul_zero]
    exact div_pos (pow_pos hσε 2) hε
  · simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, norm_zero]
    exact pow_pos hσε 2

end Balaban.RootFSpine