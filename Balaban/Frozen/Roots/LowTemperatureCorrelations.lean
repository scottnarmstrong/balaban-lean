module

public import Balaban.Frozen.Model.TwoPointTruncated
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Order.Filter.Cofinite
import Balaban.Provider.LowTemperatureCorrelations

/-!
# Root-C: low-temperature correlation functions

P9 Theorem 1.1 (pp. 494–495) for hard spins (`λ = ∞`). There are `β₀` and constants
`c, c', ρ₀, ρ₁` (depending only on `d, N`) and an integer `q ≥ 2` such that for `β ≥ β₀`:

* for every `ν ∈ (0, 1]` and every unit vector `h`, the one- and two-point functions converge
  along the tori whose side is divisible by `q^n`, `n → ∞`, to `m(ν) h` and
  `G_tr(ν, x - y) (I - h ⊗ h) + G_lg(ν, x - y) h ⊗ h`;
* `|m(ν) - 1| ≤ c β^{-1+ρ₁}` and `|G_tr(ν, x)|, |G_lg(ν, x)| ≤ c (1 + |x|)^{-(d-2)} e^{-c' √ν |x|}`;
* as `ν ↓ 0`, `m`, `G_tr`, `G_lg` converge, and with the lattice Green's function `G`
  (`-ΔG = δ₀`, `G → 0` at infinity) and some `γ_∞` with `|γ_∞ - 1| ≤ c/β`,
  `|G_tr(0, x) - m(0)² / (β γ_∞) G(x)| ≤ c (1 + |x|)^{-(d-2+ρ₀)}` and
  `|G_lg(0, x)| ≤ c (1 + |x|)^{-(d-2+ρ₀)}`.

`|x|` is the sup norm on `ℤ^d`. Decision record: `notes/phase0/surface-v1-for-approval.md`.
-/

-- FROZEN_ANCHOR_PREFIX_BEGIN
@[expose] public section

namespace Balaban

open Filter Topology

/-- Root-C (final deliverable): P9 Theorem 1.1 for the hard-spin model. -/
theorem lowTemperature_correlations (d N : ℕ) (hd : 3 ≤ d) (hN : 2 ≤ N) :
    ∃ β₀ c c' ρ₀ ρ₁ : ℝ, ∃ q : ℕ, 2 ≤ q ∧ 0 < c ∧ 0 < c' ∧ 0 < ρ₀ ∧ 0 < ρ₁ ∧ ρ₁ < 1 ∧
    ∀ β : ℝ, β₀ ≤ β →
    ∃ (m : ℝ → ℝ) (Gtr Glg : ℝ → (Fin d → ℤ) → ℝ),
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 → ∀ h : EuclideanSpace ℝ (Fin N), ‖h‖ = 1 →
        ∀ x y : Fin d → ℤ, ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ,
          ∀ (ℓ : ℕ) [NeZero ℓ], q ^ n₀ ∣ ℓ →
            (∀ i, |onePoint d N ℓ β ν h (fun μ => (x μ : ZMod ℓ)) i - m ν * h i| < ε) ∧
            ∀ i k, |twoPointTruncated d N ℓ β ν h (fun μ => (x μ : ZMod ℓ))
                (fun μ => (y μ : ZMod ℓ)) i k
              - (Gtr ν (x - y) * ((if i = k then 1 else 0) - h i * h k)
                  + Glg ν (x - y) * (h i * h k))| < ε) ∧
      (∀ ν : ℝ, 0 < ν → ν ≤ 1 →
        |m ν - 1| ≤ c * β ^ (-1 + ρ₁) ∧
        ∀ x : Fin d → ℤ,
          |Gtr ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖)) ∧
          |Glg ν x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) * Real.exp (-(c' * Real.sqrt ν * ‖x‖))) ∧
      ∃ (m₀ γ : ℝ) (Gtr₀ Glg₀ G : (Fin d → ℤ) → ℝ),
        Tendsto m (𝓝[>] 0) (𝓝 m₀) ∧
        (∀ x, Tendsto (fun ν => Gtr ν x) (𝓝[>] 0) (𝓝 (Gtr₀ x))) ∧
        (∀ x, Tendsto (fun ν => Glg ν x) (𝓝[>] 0) (𝓝 (Glg₀ x))) ∧
        (∀ x, ∑ μ : Fin d, (2 * G x - G (x + Pi.single μ 1) - G (x - Pi.single μ 1))
          = if x = 0 then 1 else 0) ∧
        Tendsto G cofinite (𝓝 0) ∧
        0 < γ ∧ |γ - 1| ≤ c / β ∧
        ∀ x : Fin d → ℤ,
          |Gtr₀ x - m₀ ^ 2 / (β * γ) * G x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) ∧
          |Glg₀ x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2 + ρ₀)) :=
  -- FROZEN_ANCHOR_PROOF_BEGIN
  by sorry
  -- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end Balaban
-- FROZEN_ANCHOR_SUFFIX_END
