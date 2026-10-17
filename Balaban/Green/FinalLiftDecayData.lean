/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalPolydiscLocal
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Data of the polydisc and of the lifts, for the decay of the lift (blocker 5)

Statements that unpack the data of the polydisc of radius `R` around `φ₀`:
* `polydisc_dataUC_xiCData`: the datum of every `w` of the polydisc lies in
  `Ξ^c_{k+1}(𝔹_k; 1, ε₀ + K₂' N R)`;
* `xiCData_composedDataAtC`: its composition to the level `j` lies in `Ξ^c_{k+1}(𝔹_j; 1, ε)`;
* `inDomainC_of_xiCData`: a member of `Ξ^c_K(𝔹; 1, ε)` lies in the data domain `Ψ̃^c(C₁ ε, C₁ ε)`.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban Balaban.Multiscale Balaban.Background
  Balaban.Localization Balaban.Analysis Balaban.SmallField Balaban.SmallField.Def6
  Balaban.SmallField.Def6v2 Balaban.SmallField.GsSpec Balaban.Fluctuation Balaban.Inhabited
  Balaban.LargeField

namespace Balaban.Green

theorem epsSeq_pos' (L : ℕ) [NeZero L] {α α₀ : ℝ} (hα₀ : 0 < α₀) (j : ℕ) :
    0 < epsSeq L α α₀ j := by
  unfold epsSeq
  have := epsTail_pos j
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

variable {d N₀ : ℕ} [NeZero N₀] {L : ℕ} [NeZero L] {d' : ℕ} {N₁ m₁ kS N : ℕ} [NeZero N₁] {ϱ : ℝ}

omit [NeZero N₀] in
/-- **The datum of every point of the polydisc lies in the chart of `𝔹_k`.** -/
theorem polydisc_dataUC_xiCData (S : StepSetting d' L N₁ m₁ kS N ϱ) (e : L1Torus d N₀ ≃ S.U × Fin N)
    (HB : BgHyp d' L (kS + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε₀ R : ℝ}
    (hθ : XiCData S.G' S.a S.ν (kS + 1) 1 ε₀ S.D')
    (hsmall : (4 * d' + 6) * ((2 * d' + 1) * ε₀) ≤ 1) (hth : xiC1 d' * ε₀ ≤ thm73C1 d' L N)
    (hR : 0 ≤ R) (hm1 : (N : ℝ) * R ≤ 1) (hδ₂ : xiC1 d' * ε₀ + 5 * ((N : ℝ) * R) ≤ bgC1 d' L N)
    (hstar : (N : ℝ) * R ≤ deltaStar d' L N)
    (hK1s : bgK1 d' L N * (xiC1 d' * ε₀) ≤ deltaStar d' L N)
    (hsm : bgK1 d' L N * (xiC1 d' * ε₀) + cK2 d' L N * ((N : ℝ) * R) < bgC0 d' L N)
    {w : L1Torus d N₀ → ℂ} (hw : w ∈ polydisc (fun q => S.psi0C (e q)) (fun _ => R)) :
    XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1
      (ε₀ + xiK2 d' L N * ((N : ℝ) * R)) (S.dataUC (fun q => w (e.symm q))) :=
  dataUC_xiCData_of_close S HB ha₁ hθ hsmall hth hR hm1 hδ₂ hstar hK1s hsm (fun q => by
    have := hw (e.symm q)
    simp only [Equiv.apply_symm_apply] at this
    exact this.le)

/-- **The composition of a datum of `Ξ^c_{k+1}(𝔹_k; 1, ε)` to the level `j ≤ k` lies in
`Ξ^c_{k+1}(𝔹_j; 1, ε)`** (the datum `composedDataAtC` of (H.2)). -/
theorem xiCData_composedDataAtC (S : StepSetting d' L N₁ m₁ kS N ϱ)
    (HB : BgHyp d' L (kS + 1) ϱ S.a S.ν) (ha₁ : 0 < S.a₁) {ε : ℝ}
    {D : BgData (stepG d' L N₁ m₁ kS ϱ) N}
    (hD : XiCData (stepG d' L N₁ m₁ kS ϱ) S.a S.ν (kS + 1) 1 ε D)
    (hsmall : (4 * d' + 6) * ((2 * d' + 1) * ε) ≤ 1) (hth : xiC1 d' * ε ≤ thm73C1 d' L N)
    {j : ℕ} (hjk : j ≤ kS) :
    XiCData (levelGS (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kS + 1) (ϱ := ϱ) j
      (hjk.trans (Nat.le_succ kS))) S.a S.ν (kS + 1) 1 ε
      (composedDataAtC S.a S.ν hjk (Nat.le_succ kS) D) := by
  have h1 := xiCData_compose_of_one_le (G := levelGS (d := d') (L := L) (N₁ := N₁) (m₁ := m₁)
    (k := kS + 1) (ϱ := ϱ) j (hjk.trans (Nat.le_succ kS))) (G' := stepG d' L N₁ m₁ kS ϱ) (b := 1)
    le_rfl ha₁ HB HB (levelGS_precedes_at hjk (Nat.le_succ kS)) (fun z _ => (S.hG z).1) hsmall hth hD
  rw [one_mul] at h1
  exact h1

/-- **A member of `Ξ^c_K(𝔹; 1, ε)` lies in the data domain** `Ψ̃^c(C₁ ε, C₁ ε)`. -/
theorem inDomainC_of_xiCData {K : ℕ} {ϱ' : ℝ} {G : GeneratingSet d' L (N₁ * L ^ m₁) K ϱ'}
    {a : ℕ → ℝ} {ν ε : ℝ} (H : BgHyp d' L K ϱ' a ν)
    (hsmall : (4 * d' + 6) * ((2 * d' + 1) * ε) ≤ 1) {D : BgData G N}
    (hD : XiCData G a ν K 1 ε D) : InDomainC G ν (xiC1 d' * ε) (xiC1 d' * ε) D := by
  obtain ⟨Ψ₀, h₀, Ψ'', h'', hX, hC⟩ := hD
  exact ⟨Ψ₀, h₀, Ψ'', h'', xiC_one_subset H hsmall hX, hC.1, hC.2⟩

end Balaban.Green
