/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Thm31b
public import Balaban.Fluctuation.Thm31a

/-!
# Theorem 3.1 (b) for the actual step: `ℳ₀^{(k+1)}(y; g)`

`S.M0 C g y i = β_k^{1/2} ∫₀¹ dt ⟨∂_t ℳ_k(y; ψ^{(k)} + tψ′, g)⟩_{1,t}` (P4 (2.53)); the average is the
`avgFun` of the exponent `W₁(1,·) + W₂(t,·)`, so `thm31b_of_input` applies.  The conclusion is the
localization expansion of `β_k^{-1/2} ℳ₀^{(k+1)}(y; g)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6
  MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **Theorem 3.1 (b), conditional on `ObsMarks`**: `β_k^{-1/2} ℳ₀^{(k+1)}(y; g) = ∑_W E(W)` over the
sets `W` of `π_{k+1}`-cubes, with `E(W) = 0` unless `W ∋ x` and
`|E(W)| ≤ (B₁ + B₂) e^{-κ_b d_Ω(W)}` for every `κ_b ≤ min(κ_h, κ') - κ₀ - 1`. -/
theorem thm31b_of_input_M0 (S : StepSetting d L N₁ m₁ k N ϱ) (C : StepClass d L N₁ m₁ k N ϱ)
    {m₀ : ℕ} (BS : BlockSplit S m₀) (g : Fld d L N₁ m₁ (k + 1) N)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    {bx : CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1) Set.univ}
    (I : ObsMarks S.nuFl BS (fun t x => S.Wone C 1 x + S.Wtwo C g t x)
      (fun t x => deriv (fun r => McompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k)
        (S.dataU (S.psiAt r x)) g y i) t) bx)
    {κb : ℝ} (hκb : κb ≤ min I.κh I.κ' - I.κ0 - 1) :
    ∃ E : Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1) m₀ (k + 1)
        Set.univ) → ℂ,
      S.M0 C g y i = ((S.betaU ^ (1 / 2 : ℝ) : ℝ) : ℂ) * ∑ T, E T ∧ (∀ T, bx ∉ T → E T = 0) ∧
      ∀ T, ‖E T‖ ≤ (I.B1 + I.B2) * Real.exp (-κb * dExt T) := by
  obtain ⟨E, h1, h2, h3⟩ := thm31b_of_input I hκb
  refine ⟨E, ?_, h2, h3⟩
  rw [← h1]
  rfl

end Balaban.Fluctuation
