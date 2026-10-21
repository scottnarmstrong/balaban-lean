/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.BaseProductSlice

/-!
# The source-form bound of the first step's boundary factor

* `one_le_volScale_first`: the volume `|Z^c_0 ∩ Z'|_1` of the localized history of a component `Z'`
  of `Z^pre_1` is at least `1` (at `k = 0`, `Z_0 = ∅`, and `Z'` is a nonempty union of cubes of side
  `M L`, so its volume in units of scale-`1` cubes is `M^d |Z'| ≥ 1`);
* `StepSlice0.ofProductConst`: the slice of the step data from a product-form carrier whose total
  exponent `b(g) - b(0)` is bounded by a constant `B` on the `ℓ¹` ball and `χ^new_0` (LFR Lemma
  II.7.7 (b): the exponent is the logarithm of a normalised expectation of `e^{⟨g,φ⟩}` over unit
  spins, `|⟨g,φ⟩| ≤ ‖g‖₁ ≤ 1`), with `B ≤ C_b log β_0 + C_b B_0`. The vacuum constants at the
  scale `0` are `0` (no vacuum term in the bare density, BASE-KERNEL §1), so `b⁰ = b` and the
  bound (S0) of `b⁰` is that of `b`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background RegionHistory ENNReal

section Volume

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L]

theorem one_le_volScale_first (H : RegionHistory S n R k0 K) (hK : 1 ≤ K) (Z' : H.Comp 1) :
    1 ≤ volScale S 1 {z | z ∈ (H.localHistory M K 1 Z').Z 1 ∧ z ∉ (H.localHistory M K 1 Z').Z 0} := by
  classical
  have h1 := H.localHistory_Z (M := M) Z' hK (j := 1) le_rfl
  have h0 := H.localHistory_Z (M := M) Z' hK (j := 0) (Nat.zero_le 1)
  rw [H.lin_self] at h1
  rw [H.lin_zero] at h0
  have hset : {z | z ∈ (H.localHistory M K 1 Z').Z 1 ∧ z ∉ (H.localHistory M K 1 Z').Z 0} =
      RegionHistory.fineSet (S := S) (n := n) M K 1 ((Z'.1 : Finset _) : Set _) := by
    rw [h1, h0]
    ext x
    simp [RegionHistory.fineSet]
  unfold volScale
  rw [hset, card_fineSet H.F.hnn hK]
  have hc : 1 ≤ Z'.1.card := Finset.card_pos.2 (comp_nonempty Z'.2)
  have hL : (0 : ℝ) < (S.L : ℝ) := by exact_mod_cast NeZero.pos S.L
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast NeZero.pos M
  have hcR : (1 : ℝ) ≤ (Z'.1.card : ℝ) := by exact_mod_cast hc
  push_cast
  rw [le_div_iff₀ (by positivity), one_mul, one_mul, pow_one, mul_pow]
  have hMd : (1 : ℝ) ≤ (M : ℝ) ^ S.d := one_le_pow₀ hM
  have hLd : (0 : ℝ) < (S.L : ℝ) ^ S.d := by positivity
  nlinarith [mul_le_mul hMd hcR zero_le_one (by positivity : (0:ℝ) ≤ (M:ℝ)^S.d)]

end Volume

section Slice

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {N : ℕ}
  {M K : ℕ} [NeZero M] {k0 : ℕ} {geo : Geo S n R M} {cs : OpConsts}
  (D : BaseProductData M K k0 geo cs N)

/-- **The slice of the step data from a product-form carrier, with the source-form bound**: the
total exponent `b(g) - b(0)` is bounded by `B` on the `ℓ¹` ball and `χ^new_0` (hypothesis `hconst`),
and `B ≤ C_b log β_0 + C_b B_0` (`hB`, a condition on the constants); the vacuum constants are `0`
at the scale `0`. The one-step bound (S2) (`hgauss`, LFR Lemma II.7.8) is the other hypothesis. -/
noncomputable def StepSlice0.ofProductConst (hK : 1 ≤ K) (hz : 0 ≤ cs.z (0 + 1))
    (hc : 0 ≤ cs.beta 0 * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (κ0 : LocalHistory S n M K → ℝ)
    (B : ℝ)
    (hconst : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
      ∀ (Z' : H.Comp (0 + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
      ChiNewAt geo cs H 0 Z' o x →
      ‖D.b (H.localHistory M K (0 + 1) Z') g o x hv - D.b (H.localHistory M K (0 + 1) Z') 0 o x hv‖ ≤ B)
    (hB : B ≤ cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0)
    (hgauss : ∀ (H : RegionHistory S n R k0 K), H.Admissible → ∀ (Z' : H.Comp (0 + 1)),
      GaussStepSpec cs R (H.localHistory M K (0 + 1) Z') 0 (κ0 (H.localHistory M K (0 + 1) Z'))
        (D.ker hz hc (H.localHistory M K (0 + 1) Z')) (D.wit (H.localHistory M K (0 + 1) Z'))) :
    StepSlice0 k0 geo cs N κ0 :=
  have hb : ∀ (H : RegionHistory S n R k0 K), H.Admissible →
      ∀ (Z' : H.Comp (0 + 1)) o x hv (g : GIdx S n M K N → ℂ), g ∈ l1Ball (GIdx S n M K N) →
      ChiNewAt geo cs H 0 Z' o x →
      ‖(D.ker hz hc (H.localHistory M K (0 + 1) Z')).b o x hv g‖ ≤
        (cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0) *
          volScale S (0 + 1) {z | z ∈ (H.localHistory M K (0 + 1) Z').Z (0 + 1) ∧
            z ∉ (H.localHistory M K (0 + 1) Z').Z 0} := by
    intro H hH Z' o x hv g hg hc'
    have h1 := hconst H hH Z' o x hv g hg hc'
    have h2 := one_le_volScale_first (M := M) H hK Z'
    have h0 : 0 ≤ B := (norm_nonneg _).trans h1
    have : (0 : ℝ) ≤ cs.Cb * Real.log (cs.beta 0) + cs.Cb * cs.B0 := h0.trans hB
    show ‖D.b _ g o x hv - D.b _ 0 o x hv‖ ≤ _
    nlinarith
  StepSlice0.ofProduct D hz hc (fun _ => 0) (fun _ => 0) (fun _ => 0) κ0 hb
    (fun H hH Z' o x hv g hg hc' => by
      have := hb H hH Z' o x hv g hg hc'
      simpa [stepVacuumTerm] using this) hgauss

end Slice

end Balaban.LargeField
