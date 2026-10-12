/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.GraphGmTree
public import Balaban.Localization.GraphGmCount
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The modular exponent bound and the fixed-output count with rates (GRAPH-GM-2 §4)

* `modular_size_le_of_witnesses`: the size bound (3.1) for the modular covering sizes of
  `FLUCTUATION.md` Definition 1.1: `d^cov_{k+1}(Y(𝒞) mod Ω^c) ≤ L⁻¹ Δ + d (2L+1)^d |𝒞|` with
  `Δ = d^cov_k(X mod Ωk^c)`, for an old pair realizing `Δ` (it exists:
  `exists_admissible_eq_dcovMod`).
* `boundary_gm4_modular_of_witnesses`: (4.6), the arithmetic of the landed `gm4`
  (`exponent_arith_graph`) for the modular sizes with the constant `C_graph = d (2L+1)^d`.
* `boundary_gm3_fixed_Y_rate`: (4.3) under the explicit rate conditions (4.5).

All conditional on the named assertions of OPEN-P6-WITNESS-GEOMETRY, which are exactly the
hypotheses `hSN hSB hatt hcard hcov hKgen` (see `modular_tree_of_witnesses`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Fluctuation Finset

section Main

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ k : ℕ}
variable (hK : k + 1 = K) (hN : L ^ m₀ ∣ N₁) (hL : 3 ≤ L) (hd : 3 ≤ d)
  (hM : 4 * L ^ 2 ≤ L ^ m₁)
variable (Ω Ωk X 𝒦X : Set (CTorus d L N₁ m₁ K)) (W₀ : Finset (CTorus d L N₁ m₁ K))
  (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K))
variable (Q0 : Finset (ZCell d))
variable (hQtype : ∀ Q ∈ Q0, Q.side = L * cellSide L m₀ m₁ K ∧
  ∀ μ, ((cellSide L m₀ m₁ K : ℕ) : ℤ) ∣ Q.base μ)
variable (hSN : ∀ Q ∈ Q0, ∃ q ∈ 𝒦X, box q (L * cellSide L m₀ m₁ k) ⊆ Q.sites L N₁ m₁ K)
variable (hSB : X ∩ Ω ⊆ ⋃ Q ∈ Q0, Q.sites L N₁ m₁ K)
variable (C : Finset (ZCell d)) (D : ZCell d → Finset (ZCell d)) (home : ZCell d → ZCell d)
variable (hP : ∀ P ∈ C, 0 < P.side) (hhome : ∀ P ∈ C, home P ∈ D P ∧ P.pts ⊆ (home P).pts)
variable (hlayer : ∀ P ∈ C, ∀ g ∈ D P, g.Layered L m₀ m₁ K)
variable (hcard : ∀ P ∈ C, (D P).card ≤ (2 * L + 1) ^ d)
variable (hatt : ∀ g ∈ C.biUnion D, ∃ P₀ ∈ C, (∃ Q ∈ Q0, ZFaceAdj Q P₀) ∧
  Relation.ReflTransGen (fun u v => u ∈ C.biUnion D ∧ v ∈ C.biUnion D ∧ ZFaceAdj u v)
    (home P₀) g)
variable (Kgen : Finset (CTorus d L N₁ m₁ K))
variable (hKgen : ∀ b ∈ Kgen, Aligned (cellSide L m₀ m₁ K) b ∧
  box b (L * cellSide L m₀ m₁ K) ⊆ outputY L N₁ m₁ K Ω X Q0 C D ∧
  (b ∈ Q0.image (fun Q => zTorus L N₁ m₁ K Q.base) ∨
    ∃ g ∈ C.biUnion D, g.sites L N₁ m₁ K ⊆ box b (L * cellSide L m₀ m₁ K)))
variable (hcov : ∀ g ∈ C.biUnion D, g.sites L N₁ m₁ K ⊆ ⋃ b ∈ Kgen, box b (L * cellSide L m₀ m₁ K))
variable (hΓ : ModAdmissible m₀ k Ωk X 𝒦X W₀ E₀)
  (hΔ : bondCost (scaleW L m₀ m₁ k) E₀ = dcovMod m₀ k Ωk X)

include hK hN hL hd hM hΓ hΔ hQtype hSN hSB hP hhome hlayer hcard hatt hKgen hcov in
/-- **The size bound (GRAPH-GM-2 (3.1)) for the modular covering sizes.**  `Δ = d^cov_k(X mod
Ωk^c)` is realized by the old pair `(𝒦X, W₀, E₀)` (`hΔ`; such a pair exists whenever the old
domain is admissible, `exists_admissible_eq_dcovMod`).  Conclusion:
`d^cov_{k+1}(Y(𝒞) mod Ω^c) ≤ L⁻¹ Δ + d (2L+1)^d |𝒞|`. -/
theorem modular_size_le_of_witnesses :
    dcovMod m₀ K Ω (outputY L N₁ m₁ K Ω X Q0 C D) ≤
      dcovMod m₀ k Ωk X / L + d * (((2 * L + 1) ^ d : ℕ) : ℝ) * C.card := by
  obtain ⟨𝒦, W, E, hadm, hcost⟩ := modular_tree_of_witnesses hK hN hL hd hM Ω Ωk X 𝒦X W₀ E₀ hΓ Q0
    hQtype hSN hSB C D home hP hhome hlayer hcard hatt Kgen hKgen hcov
  rw [← hΔ]
  exact (dcovMod_le_of_admissible hadm).trans hcost

include hK hN hL hd hM hΓ hΔ hQtype hSN hSB hP hhome hlayer hcard hatt hKgen hcov in
/-- **(GM4) for the modular sizes (GRAPH-GM-2 (4.6)).**  With `Δ = d^cov_k(X mod Ωk^c)` and
`D = d^cov_{k+1}(Y(𝒞) mod Ω^c)`, if `κ₀ ≥ 0`, `κ ≥ 3κ₀ + 3`, `κ₁ ≥ 4 d (2L+1)^d κ`:
`(κ₁ - 1)|𝒞| + (κ - 1)Δ ≥ (κ₁/2 - 1)|𝒞| + κ₀ Δ + 2 κ D`. -/
theorem boundary_gm4_modular_of_witnesses (κ κ₀ κ₁ : ℝ) (hκ₀ : 0 ≤ κ₀) (hκ : 3 * κ₀ + 3 ≤ κ)
    (hκ₁ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κ ≤ κ₁) :
    (κ₁ - 1) * C.card + (κ - 1) * dcovMod m₀ k Ωk X ≥
      (κ₁ / 2 - 1) * C.card + κ₀ * dcovMod m₀ k Ωk X +
        2 * κ * dcovMod m₀ K Ω (outputY L N₁ m₁ K Ω X Q0 C D) := by
  have hD := modular_size_le_of_witnesses hK hN hL hd hM Ω Ωk X 𝒦X W₀ E₀ Q0 hQtype hSN hSB C D
    home hP hhome hlayer hcard hatt Kgen hKgen hcov hΓ hΔ
  exact exponent_arith_graph L (d * (((2 * L + 1) ^ d : ℕ) : ℝ)) κ κ₀ κ₁ C.card
    (dcovMod m₀ k Ωk X) _ (by exact_mod_cast hL) hκ₀ hκ (by linarith) (Nat.cast_nonneg _)
    (dcovMod_nonneg _ _) hD

end Main

section Rate

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ : ℕ}

/-- **(4.3) with the explicit rate conditions (4.5).**  With `κ₂ = κ₁/2 - 1`, `κ₁ ≥ 6` and
`κ₁ ≥ 4 d log ((2L+1) L^{m₀}) + 2`, the weights `e^{-κ₂ |𝒞|}` of the effective derivative
families with a fixed whole output sum to at most `1`.  The premises on each family are the
witness assertions (derivative in a new output cell, ownership, at most `(2L+1)^d` completion
cells), see `boundary_gm3_fixed_Y`. -/
theorem boundary_gm3_fixed_Y_rate (hL1 : 1 ≤ L) (hN : L ^ m₀ ∣ N₁)
    (Deriv : Finset (ℕ × CTorus d L N₁ m₁ K))
    (hDeriv : ∀ P ∈ Deriv, P.1 ≤ K ∧ CubeBase (K := K) m₁ P.1 P.2)
    (D : ℕ × CTorus d L N₁ m₁ K → Finset (ℕ × CTorus d L N₁ m₁ K))
    (hD : ∀ P, (D P).card ≤ (2 * L + 1) ^ d)
    (Yc Bc : Finset (ℕ × CTorus d L N₁ m₁ K))
    (𝔉 : Finset (Finset (ℕ × CTorus d L N₁ m₁ K)))
    (h𝔉 : ∀ C ∈ 𝔉, C ⊆ Deriv ∧ (∀ P ∈ C, cellOfCube (L := L) m₀ m₁ P ∈ Yc \ Bc) ∧
      Yc \ Bc ⊆ C.biUnion D)
    (κ₁ : ℝ) (h6 : 6 ≤ κ₁)
    (hκ : 4 * d * Real.log (((2 * L + 1 : ℕ) : ℝ) * ((L ^ m₀ : ℕ) : ℝ)) + 2 ≤ κ₁) :
    ∑ C ∈ 𝔉, Real.exp (-(κ₁ / 2 - 1) * C.card) ≤ 1 := by
  obtain ⟨h1, h2⟩ := rate_conditions d L m₀ hL1 κ₁ h6 hκ
  exact boundary_gm3_fixed_Y hN Deriv hDeriv D hD Yc Bc 𝔉 h𝔉 (κ₁ / 2 - 1) h1 h2

end Rate

end Balaban.Localization
