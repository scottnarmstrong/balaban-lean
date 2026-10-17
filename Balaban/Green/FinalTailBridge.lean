/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalTailActivity
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The tail activity in the form of the polymer gas (W891, blocker 5)

Leaf L1 of `notes/phase1/FINALPHYS3.md` section 7.  The landed polymer gas
(`Balaban.Polymer.gas_activity_bound`) asks of a heavy object `Z` the bound
`‖τ Z‖ ≤ exp(-p - h |Z|)`.  The absolute activity of a set `Z` of large blocks,
`norm_setIntegral_blocksSplit_le`, is `B ∏_{z ∈ Z} (|blk z| 2^{dim W/2} e^{-ρ²/4})`.  If every
block has at most `m` sites, this is at most `B e^{-q |Z|}` with
`q = ρ²/4 - log m - (dim W/2) log 2`, and then at most `exp(-p - h |Z|)` as soon as
`B ≤ e^{b}`, `b + p ≤ q - h`, `0 ≤ q - h` and `Z` is nonempty.
-/

@[expose] public section

open MeasureTheory

namespace Balaban.Green

variable {ι β W E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [Fintype ι] [DecidableEq ι] in
/-- Each block factor of the tail activity is `exp(-q)` with
`q = ρ²/4 - log m - (dim W / 2) log 2`, when the block has at most `m` sites (`1 ≤ m`). -/
theorem blockTailFactor_le_exp (b : Finset ι) {m : ℕ} (hm : 1 ≤ m) (hb : b.card ≤ m) (ρ : ℝ)
    (W' : ℕ) :
    (b.card : ℝ) * (2 ^ ((W' : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)) ≤
      Real.exp (-(ρ ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h2 : (2 : ℝ) ^ ((W' : ℝ) / 2) = Real.exp ((W' : ℝ) / 2 * Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num), mul_comm]
  have hcard : (b.card : ℝ) ≤ m := by exact_mod_cast hb
  calc (b.card : ℝ) * (2 ^ ((W' : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))
      ≤ m * (2 ^ ((W' : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4)) := by gcongr
    _ = Real.exp (-(ρ ^ 2 / 4 - Real.log m - (W' : ℝ) / 2 * Real.log 2)) := by
        rw [h2, ← Real.exp_log hm0, ← Real.exp_add, ← Real.exp_add, Real.exp_log hm0]
        congr 1; ring

/-- **The tail activity of a set of large blocks in the gas form** (leaf L1).  Under the
hypotheses of `norm_setIntegral_blocksSplit_le`, blocks with at most `m` sites, `‖F‖ ≤ e^{b}` on
the set, `Z` nonempty, `0 ≤ q - h` and `b + p ≤ q - h` with
`q = ρ²/4 - log m - (dim W/2) log 2`, the integral has norm at most `exp(-p - h |Z|)`
(the hypothesis `hτ` of `Balaban.Polymer.gas_activity_bound`, with `zs Z = Z`). -/
theorem norm_setIntegral_blocksSplit_le_exp [Fintype β] (blk : β → Finset ι) (Z : Finset β)
    (hdisj : (Z : Set β).PairwiseDisjoint blk) {ρ : ℝ} (hρ : 0 ≤ ρ) {F : (ι → W) → E} {b : ℝ}
    (hF : ∀ ψ ∈ {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
      ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ}, ‖F ψ‖ ≤ Real.exp b)
    {m : ℕ} (hm : 1 ≤ m) (hblk : ∀ z ∈ Z, (blk z).card ≤ m) (hZ : Z.Nonempty) {p h : ℝ}
    (hq : 0 ≤ ρ ^ 2 / 4 - Real.log m - (Module.finrank ℝ W : ℝ) / 2 * Real.log 2 - h)
    (hbp : b + p ≤ ρ ^ 2 / 4 - Real.log m - (Module.finrank ℝ W : ℝ) / 2 * Real.log 2 - h) :
    ‖∫ ψ in {ψ : ι → W | (∀ z ∈ Z, ∃ x ∈ blk z, ρ < ‖ψ x‖) ∧
        ∀ z ∉ Z, ∀ x ∈ blk z, ‖ψ x‖ ≤ ρ}, F ψ ∂(pdGaussian ι W)‖ ≤
      Real.exp (-p - h * (Z.card : ℝ)) := by
  set q : ℝ := ρ ^ 2 / 4 - Real.log m - (Module.finrank ℝ W : ℝ) / 2 * Real.log 2 with hqdef
  refine (norm_setIntegral_blocksSplit_le blk Z hdisj hρ (Real.exp_pos b).le hF).trans ?_
  have hprod : ∏ z ∈ Z, ((blk z).card *
      (2 ^ ((Module.finrank ℝ W : ℝ) / 2) * Real.exp (-ρ ^ 2 / 4))) ≤
      ∏ z ∈ Z, Real.exp (-q) := by
    refine Finset.prod_le_prod₀ (fun z _ => by positivity) fun z hz => ?_
    exact blockTailFactor_le_exp (blk z) hm (hblk z hz) ρ (Module.finrank ℝ W)
  rw [Finset.prod_const, ← Real.exp_nat_mul] at hprod
  have hc : (1 : ℝ) ≤ Z.card := by exact_mod_cast hZ.card_pos
  calc _ ≤ Real.exp b * Real.exp (Z.card * -q) := by gcongr
    _ = Real.exp (b - q * Z.card) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp (-p - h * (Z.card : ℝ)) := by
        apply Real.exp_le_exp.2
        nlinarith [mul_le_mul_of_nonneg_left hc hq]

end Balaban.Green
