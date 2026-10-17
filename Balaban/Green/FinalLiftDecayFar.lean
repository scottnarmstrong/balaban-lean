/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLiftDecayData
public import Balaban.Green.FinalLiftDecayGeo
public import Balaban.Green.FinalLiftDecayLocal
public import Balaban.Green.FinalLiftDecayResponse
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The far response of the composed datum of the lift (blocker 5)

`lift_far_bound`: two data of the polydisc differing by at most `a` and agreeing near a set `B` have
composed data differing on `B` by at most `5 e^{2dγ_w} K_w C_F N a e^{-γ_w n}`.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField

namespace Balaban.Green

variable {d' : ℕ} {L : ℕ} [NeZero L] {N : ℕ}

/-- **The far response of the composed datum of the lift** (`composeField_response_le` for the data
of two points of the polydisc): if `D, D'` of `Ξ^c_{k+1}(𝔹_k; 1, ε₁)` have the same `h`, differ in `Ψ`
by at most `a` at every site, and agree at the sites of `B` and at the sites `x` with a site `z ∈ B`
at path distance `< n` from a site `ω ∈ Ω₁` equal or adjacent to `x`, then the composed data differ
on `B` by at most `5 e^{2dγ_w} K_w C_F N a e^{-γ_w n}`. -/
theorem lift_far_bound (hd3 : 3 ≤ d') (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ kS : ℕ} [NeZero N₁] {ϱ : ℝ} (S : StepSetting d' L N₁ m₁ kS N ϱ)
        (_ : BgHyp d' L (kS + 1) ϱ S.a S.ν) (_ : Dec2.OpSetting (stepG d' L N₁ m₁ kS ϱ) S.a S.ν)
        {j : ℕ} (hjk : j ≤ kS) {ε₁ a : ℝ} (_ : 0 < ε₁) (_ : 0 ≤ a)
        (_ : (4 * d' + 6) * ((2 * d' + 1) * ε₁) ≤ 1)
        (_ : xiC1 d' * ε₁ ≤ bgC0 d' L N) (_ : xiC1 d' * ε₁ ≤ bgC1 d' L N)
        (_ : bgK1 d' L N * (xiC1 d' * ε₁) ≤ deltaStar d' L N)
        (_ : bgK1 d' L N * (xiC1 d' * ε₁) ≤ δw)
        (_ : (N : ℝ) * a ≤ deltaStar d' L N) (_ : (N : ℝ) * a ≤ δw)
        {Dw Dw' : BgData (stepG d' L N₁ m₁ kS ϱ) N}
        (_ : XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ Dw)
        (_ : XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε₁ Dw')
        (_ : ∀ x i, Dw'.h x i = Dw.h x i)
        (_ : ∀ x i, ‖Dw'.Ψ x i - Dw.Ψ x i‖ ≤ a)
        {Bs : Set (CTorus d' L N₁ m₁ (kS + 1))} (n : ℕ)
        (_ : ∀ (x : CTorus d' L N₁ m₁ (kS + 1)) (i : Fin N),
          (x ∈ Bs ∨ ∃ z ∈ Bs, ∃ ω ∈ (stepG d' L N₁ m₁ kS ϱ).Ω 1, (ω = x ∨ Adj ω x) ∧
            (stepG d' L N₁ m₁ kS ϱ).pathDist z ω < ENNReal.ofReal (n : ℝ)) →
          Dw'.Ψ x i = Dw.Ψ x i),
        ∀ x ∈ Bs, ∀ i : Fin N,
          ‖(composedDataAtC S.a S.ν hjk (Nat.le_succ kS) Dw').Ψ x i -
              (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) Dw).Ψ x i‖ ≤
            5 * Real.exp (gammaW d' * (2 * d')) * (Kw * (cF d' L * ((N : ℝ) * a))) *
              Real.exp (-(gammaW d' * n)) := by
  classical
  obtain ⟨Kw, δw, hK, hδw, hresp⟩ := composeField_response_le (d := d') (L := L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ kS _ ϱ S HB hOp j hjk ε₁ a hε₁ ha hsm1 hc0 hc1 hK1s hKw hstar hδw' Dw Dw' hDw hDw'
    hh hdiff Bs n hag x hx i
  have hxc : 0 < xiC1 d' * ε₁ := by
    have := one_le_xiC1 d'
    positivity
  have hNa : 0 ≤ (N : ℝ) * a := by positivity
  have hshadow : ∀ ω ∈ Balaban.Fluctuation.shadow (stepG d' L N₁ m₁ kS ϱ)
      (Finset.univ.filter fun y => ∃ i, Dw'.Ψ y i ≠ Dw.Ψ y i),
      ENNReal.ofReal (n : ℝ) ≤ (stepG d' L N₁ m₁ kS ϱ).pathDist x ω := fun ω hω =>
    shadow_far (G := stepG d' L N₁ m₁ kS ϱ) (B := Bs) (n := (n : ℝ)) (f := Dw.Ψ)
      (f' := Dw'.Ψ) hag hx hω
  exact hresp HB hOp (levelGS_precedes_at hjk (Nat.le_succ kS)) hxc hc0 hc1
    (inDomainC_of_xiCData HB hsm1 hDw) (inDomainC_of_xiCData HB hsm1 hDw') hK1s hKw
    (Finset.univ.filter fun y => ∃ i, Dw'.Ψ y i ≠ Dw.Ψ y i)
    (fun y hy => by
      funext i
      by_contra hne
      exact hy (by simp [Finset.mem_filter]; exact ⟨i, hne⟩)) hh hNa hstar hδw'
    (fun x _ => vn_le_card_mul ha (fun i => hdiff x i)) x (n : ℝ) hshadow
    (funext fun i => hag x i (Or.inl hx)) i


end Balaban.Green
