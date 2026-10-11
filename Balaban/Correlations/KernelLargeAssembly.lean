module

public import Balaban.Correlations.KernelLarge
public import Balaban.Correlations.MainTerm
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The kernel hypotheses of Root-C, discharged

`kernelHyp_and_large_holds` is exactly the kernel hypothesis of
`Balaban.Correlations.rootC_of_rootF_c1Star_kernelLarge`: for `L ≥ 3` and `a` in the range of C-1*
there are kernels `t, t0` and constants with `KernelHyp` and `KernelHypLarge` for the same `t`.
-/

@[expose] public section

namespace Balaban

open Filter Topology Balaban.Correlations

theorem kernelHyp_and_large_holds (d : ℕ) (hd : 3 ≤ d) (L : ℕ) [NeZero L] (a : ℝ) (hL : 3 ≤ L)
    (ha1 : 1 / (2 * (1 - ((L : ℝ) ^ 2)⁻¹)) < a) (ha2 : a < 3 / 2) :
    ∃ (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
      (t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (C_G δ_G C_P C' δ' : ℝ),
      KernelHyp d L a t t0 C_G δ_G C_P ∧ KernelHypLarge d L a t C' δ' := by
  have hx : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have h1 : ((L : ℝ) ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ hx (by norm_num))
  have hpos : 0 < 1 - ((L : ℝ) ^ 2)⁻¹ := by linarith
  have hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹) := by
    rw [div_lt_iff₀ (by positivity)] at ha1
    nlinarith
  have hhi : a ≤ 2 := by linarith
  obtain ⟨t0, C_G, δ_G, C_P, H⟩ := kernelHyp_holds_tLim hd hL hlo hhi
  obtain ⟨C', δ', hC', hδ', g1, g2⟩ := kernelHypLarge_holds_two_L4 hd hL hlo hhi
  exact ⟨_, t0, C_G, δ_G, C_P, C', δ', H,
    ⟨fun J j μ hj hμ _ x y => g1 J j μ hj hμ x y,
      fun j μ hμ hμ1 x y => g2 j μ hμ hμ1 x y, hδ'⟩⟩

end Balaban
