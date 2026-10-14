/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalLogDetLocal
public import Balaban.Green.FinalComplexMatrix

import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized determinant ratio of the perturbed final operator (W787, FINALPHYS2 leaves E1, E2)

Let `U = finalOp` and let `E` be a complex matrix with `WSmall r η E`.  The perturbed defect
`K_E(s, t) = 1 - (U + E + t) G_*(s, t)` is built with the box resolvents `G_z` of `U` (not of
`U + E`); its tagged entries are the tagged entries of `R_z - E χ_z G_z`.  At `s = 1` it is
`1 - (U + E + t) ∑_z χ_z G_z`, so `det (1 - K_E(1, t)) = det (U + E + t) · det (∑_z χ_z G_z)`, with the
SAME block factor `∑_z χ_z G_z` as for `E = 0`; the block factor cancels in the ratio.

* E1 (`taggedKE_row_sum`, `taggedKE_isUnit_inv_weighted`): the weighted row sums of `K_E` on the
  closed polydisc `‖s p‖ ≤ e^κ` are at most `B e^{Hκ}/M + 2 e^{Hκ} ballConst(3ε/4) η / g_*`;
  hence `1 - K_E` is invertible with weighted row sums of the inverse at most `2`.
* E2 (`exists_series_log_det_taggedKE`, `det_finalOp_add_eq_mul_prod_exp_coef_sub`): analytic
  logarithms `ell_E`, `ell_0` with `det (U + E + t) = det (U + t) · ∏_C exp (coef ell_E C - coef ell_0 C)`;
  locality (`coef_eq_of_agree_taggedKE`), vanishing at separated supports and the volume-uniform
  bound `|C| (8M+1)^d / (e^κ - 1)^{|C|}`.
-/

@[expose] public section

open Finset Matrix

namespace Balaban.Green

section GenericFamily

open Balaban.Localization Balaban.Analysis

variable {d N₀ M : ℕ} [NeZero N₀]

local notation "𝐓[" a ", " s "]" => taggedMat Finset.univ (macTags d N₀ M) a s

theorem tm_zero (hM : 0 < M) (hd : 0 < d)
    (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) :
    𝐓[a, (0 : MacIdx d N₀ M → ℂ)] = 0 := by
  ext x y
  simp [taggedMat, tagMon_macTags_zero hM hd]

theorem tm_continuous (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) :
    Continuous fun s : MacIdx d N₀ M → ℂ => 𝐓[a, s] :=
  continuous_matrix fun x y => continuous_iff_continuousAt.2 fun s0 =>
    (taggedMat_analytic _ _ _ x y s0).continuousAt

theorem tm_row_eq_zero (hM : 0 < M) (hd : 0 < d)
    (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {C : Finset (MacIdx d N₀ M)}
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ supportedOn C) {x : L1Torus d N₀}
    (hx : x ∉ macRegion d N₀ M C) (y : L1Torus d N₀) : 𝐓[a, s] x y = 0 := by
  rw [taggedMat_apply_of_supportedOn _ _ _ hs]
  exact Finset.sum_eq_zero fun z hz =>
    absurd (macTags_cover_box_and_ends hM hd (Finset.mem_filter.1 hz).2).2.1 hx

/-- Locality of the logarithm in the entry family. -/
theorem tm_coef_eq_of_agree {R : ℝ} (hR : 1 < R)
    {a a' : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ}
    {C : Finset (MacIdx d N₀ M)}
    (hag : ∀ z, ∀ x y, macTags d N₀ M z x y ⊆ C → a z x y = a' z x y)
    {ell ell' : (MacIdx d N₀ M → ℂ) → ℂ} (hell : ContinuousOn ell (Metric.ball 0 R))
    (hell' : ContinuousOn ell' (Metric.ball 0 R)) (h0 : ell 0 = 0) (h0' : ell' 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) R, (1 - 𝐓[a, s]).det = Complex.exp (ell s))
    (hdet' : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) R,
      (1 - 𝐓[a', s]).det = Complex.exp (ell' s)) :
    coef ell C = coef ell' C := by
  classical
  have hR0 : 0 < R := by linarith
  set S : Set (MacIdx d N₀ M → ℂ) := Metric.ball 0 R ∩ supportedOn C with hSdef
  have hSconv : Convex ℝ S := (convex_ball _ _).inter (convex_supportedOn C)
  have h0S : (0 : MacIdx d N₀ M → ℂ) ∈ S := ⟨Metric.mem_ball_self hR0, fun i _ => rfl⟩
  have heq : ∀ s ∈ S, ell s = ell' s := by
    refine eq_of_exp_eq_of_continuousOn hSconv.isPreconnected h0S (hell.mono Set.inter_subset_left)
      (hell'.mono Set.inter_subset_left) (by rw [h0, h0']) fun s hs => ?_
    rw [← hdet s hs.1, ← hdet' s hs.1,
      taggedMat_congr_supportedOn Finset.univ (macTags d N₀ M) (fun z _ x y hT => hag z x y hT) hs.2]
  have hproj : ∀ f : (MacIdx d N₀ M → ℂ) → ℂ, coef f C =
      coef (fun s => f (fun i => if i ∈ C then s i else 0)) C := fun f =>
    coef_congr fun w hw => by
      congr 1; funext i; by_cases hi : i ∈ C
      · simp [hi]
      · simp [hi, hw i hi]
  rw [hproj ell, hproj ell']
  refine coef_congr_polydisc hR (fun s hs => heq _ ⟨?_, fun i hi => by simp [hi]⟩) C
  rw [← polydisc_eq_ball hR0]
  intro i
  by_cases hi : i ∈ C
  · simpa [hi] using hs i
  · simpa [hi] using hR0

/-- The log-determinant is the trace series on the closed polydisc, for a tagged family. -/
theorem tm_eq_neg_tsum (hM : 0 < M) (hd : 0 < d)
    (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {κ q : ℝ} (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x, ∑ y, ‖𝐓[a, s] x y‖ ≤ q)
    {ell : (MacIdx d N₀ M → ℂ) → ℂ} (hell : ContinuousOn ell (Metric.closedBall 0 (Real.exp κ)))
    (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ),
      (1 - 𝐓[a, s]).det = Complex.exp (ell s)) :
    ∀ s ∈ Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ),
      ell s = -∑' n : ℕ, ((𝐓[a, s]) ^ (n + 1)).trace / ((n : ℂ) + 1) := by
  have hκ : (0 : ℝ) < Real.exp κ := Real.exp_pos κ
  exact eq_neg_tsum_trace_of_exp_eq (convex_closedBall _ _).isPreconnected
    (Metric.mem_closedBall_self hκ.le) (fun s => 𝐓[a, s]) (tm_continuous a)
    (tm_zero hM hd a) hq0 hq1
    (fun s hs i => hKU s (fun p => (norm_le_pi_norm s p).trans (mem_closedBall_zero_iff.1 hs)) i)
    hell h0 hdet

/-- The tagged family splits over a separated decomposition of the support. -/
theorem tm_split_of_separated (hM : 0 < M) (hd : 0 < d)
    (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    (hcol : ∀ z x y, a z x y ≠ 0 → y ∈ macBox d N₀ M z)
    {C A : Finset (MacIdx d N₀ M)}
    (hAC : A ⊆ C) (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)))
    {s : MacIdx d N₀ M → ℂ} (hs : s ∈ supportedOn C) :
    𝐓[a, s] = 𝐓[a, fun i => if i ∈ A then s i else 0] +
        𝐓[a, fun i => if i ∈ C \ A then s i else 0] ∧
      𝐓[a, fun i => if i ∈ A then s i else 0] *
        𝐓[a, fun i => if i ∈ C \ A then s i else 0] = 0 ∧
      𝐓[a, fun i => if i ∈ C \ A then s i else 0] *
        𝐓[a, fun i => if i ∈ A then s i else 0] = 0 := by
  classical
  set B : Finset (MacIdx d N₀ M) := C \ A with hBdef
  have hAB : Disjoint A B := Finset.disjoint_sdiff
  have hBC : B ⊆ C := Finset.sdiff_subset
  have hBA : Disjoint B A := hAB.symm
  have hsep' : ∀ a ∈ A, ∀ b ∈ B, ∀ p, p ∈ macBox d N₀ M a → p ∈ macBox d N₀ M b → False :=
    fun a ha b hb p h1 h2 => Set.disjoint_left.1 hsep (mem_macRegion.2 ⟨a, ha, h1⟩)
      (mem_macRegion.2 ⟨b, hb, h2⟩)
  have hCAB : C ⊆ A ∪ B := by
    intro i hi
    by_cases hiA : i ∈ A
    · exact Finset.mem_union_left _ hiA
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨hi, hiA⟩)
  have hsplitTags : ∀ z x y, y ∈ macBox d N₀ M z → (macTags d N₀ M z x y).Nonempty ∧
      (macTags d N₀ M z x y ⊆ A ∨ macTags d N₀ M z x y ⊆ B ∨ ¬ macTags d N₀ M z x y ⊆ C) :=
    fun z x y hy => ⟨⟨_, macZ_end_mem_macTags hM hd z x y⟩, by
      by_cases hVC : macTags d N₀ M z x y ⊆ C
      · rcases macTags_subset_or hM hd hy hsep' (hVC.trans hCAB) with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr hVC)⟩
  have hend : ∀ z x y, macZ M y ∈ macTags d N₀ M z x y := fun z x y =>
    macZ_end_mem_macTags hM hd z x y
  have hstart : ∀ z x y, macZ M x ∈ macTags d N₀ M z x y := fun z x y =>
    macZ_start_mem_macTags hM hd z x y
  refine ⟨?_, ?_, ?_⟩
  · exact taggedMat_split _ _ _ hAB hAC hBC hs (fun _ => rfl) (fun _ => rfl)
      fun z _ x y h => hsplitTags z x y (hcol z x y h)
  · exact taggedMat_mul_eq_zero _ _ _ _ hAB (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)
  · exact taggedMat_mul_eq_zero _ _ _ _ hBA (fun _ => rfl) (fun _ => rfl) (macZ M)
      (fun z _ x y _ => hend z x y) (fun z _ x y _ => hstart z x y)

/-- Vanishing of the coefficient at a separated support, for a tagged family. -/
theorem tm_coef_eq_zero_of_separated (hM : 0 < M) (hd : 0 < d)
    (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ)
    (hcol : ∀ z x y, a z x y ≠ 0 → y ∈ macBox d N₀ M z) {κ q : ℝ} (hκ : 0 < κ) (hq0 : 0 ≤ q)
    (hq1 : q < 1)
    (hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x, ∑ y, ‖𝐓[a, s] x y‖ ≤ q)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ', (1 - 𝐓[a, s]).det = Complex.exp (ell s))
    {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty) (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef ell C = 0 := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  have hcb : Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
    Metric.closedBall_subset_ball hρ'
  have hser := tm_eq_neg_tsum hM hd a hq0 hq1 hKU (hell.continuousOn.mono hcb) h0
    (fun s hs => hdet s (hcb hs))
  have hbd : ∀ s : MacIdx d N₀ M → ℂ, ‖s‖ ≤ Real.exp κ → ∀ p, ‖s p‖ ≤ Real.exp κ :=
    fun s hs p => (norm_le_pi_norm s p).trans hs
  have hproj : ∀ (X : Finset (MacIdx d N₀ M)) (s : MacIdx d N₀ M → ℂ), ‖s‖ ≤ Real.exp κ →
      ‖(fun i => if i ∈ X then s i else 0 : MacIdx d N₀ M → ℂ)‖ ≤ Real.exp κ := by
    intro X s hs
    refine (pi_norm_le_iff_of_nonneg hR0.le).2 fun p => ?_
    by_cases hp : p ∈ X
    · simpa [hp] using (norm_le_pi_norm s p).trans hs
    · simpa [hp] using hR0.le
  refine coef_eq_zero_of_split hR (hell.mono ?_) Finset.disjoint_sdiff hAC Finset.sdiff_subset hA hB
    (fun s hs hsC => ?_)
  · intro s hs
    rw [polydisc_eq_ball hR0] at hs
    exact Metric.ball_subset_ball hρ'.le hs
  · rw [polydisc_eq_ball hR0] at hs
    have hs1 : ‖s‖ ≤ Real.exp κ := (mem_ball_zero_iff.1 hs).le
    obtain ⟨hK, h1, h2⟩ := tm_split_of_separated hM hd a hcol hAC hsep hsC
    have hsA := hproj A s hs1
    have hsB := hproj (C \ A) s hs1
    have hsum := fun (r : MacIdx d N₀ M → ℂ) (hr : ‖r‖ ≤ Real.exp κ) =>
      det_one_sub_eq_exp_tsum_trace (𝐓[a, r]) hq1 (hKU r (hbd r hr))
    rw [hser s (mem_closedBall_zero_iff.2 hs1), hser _ (mem_closedBall_zero_iff.2 hsA),
      hser _ (mem_closedBall_zero_iff.2 hsB), ← neg_add, hK]
    congr 1
    rw [← (hsum _ hsA).1.tsum_add (hsum _ hsB).1]
    refine tsum_congr fun n => ?_
    rw [add_pow_succ_of_mul_eq_zero h1 h2, Matrix.trace_add, add_div]

/-- Volume-uniform bound of the coefficients, for a tagged family. -/
theorem tm_norm_coef_le (hM : 0 < M) (hd : 0 < d)
    (a : MacIdx d N₀ M → Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) {κ q : ℝ} (hκ : 0 < κ)
    (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hKU : ∀ s : MacIdx d N₀ M → ℂ, (∀ p, ‖s p‖ ≤ Real.exp κ) → ∀ x, ∑ y, ‖𝐓[a, s] x y‖ ≤ q)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ', (1 - 𝐓[a, s]).det = Complex.exp (ell s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ell C‖ ≤ (C.card * ((8 * M + 1) ^ d * (q / (1 - q)))) /
      (Real.exp κ - 1) ^ C.card := by
  classical
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  have hcb : Metric.closedBall (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ' :=
    Metric.closedBall_subset_ball hρ'
  have hser := tm_eq_neg_tsum hM hd a hq0 hq1 hKU (hell.continuousOn.mono hcb) h0
    (fun s hs => hdet s (hcb hs))
  have hpoly : polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ) ⊆ Metric.ball 0 ρ' := by
    intro s hs
    rw [polydisc_eq_ball hR0] at hs
    exact Metric.ball_subset_ball hρ'.le hs
  have hproj : coef ell C = coef (fun s => ell (fun i => if i ∈ C then s i else 0)) C :=
    coef_congr fun w hw => by
      congr 1; funext i; by_cases hi : i ∈ C
      · simp [hi]
      · simp [hi, hw i hi]
  rw [hproj]
  set Y : Finset (L1Torus d N₀) := C.biUnion (macBoxF d N₀ M) with hY
  have hYc : (Y.card : ℝ) ≤ C.card * (8 * M + 1) ^ d := by
    exact_mod_cast card_biUnion_macBoxF_le hM C
  set B : ℝ := C.card * ((8 * M + 1) ^ d * (q / (1 - q))) with hB
  have hq' : 0 ≤ q / (1 - q) := div_nonneg hq0 (by linarith)
  refine norm_coef_le hR (analyticOnNhd_comp_proj (hell.mono hpoly) C hR0) (B := B) ?_ C
  intro s hs
  rw [polydisc_eq_ball hR0] at hs
  have hs1 : ‖s‖ ≤ Real.exp κ := (mem_ball_zero_iff.1 hs).le
  have hsC : ‖(fun i => if i ∈ C then s i else 0 : MacIdx d N₀ M → ℂ)‖ ≤ Real.exp κ := by
    refine (pi_norm_le_iff_of_nonneg hR0.le).2 fun p => ?_
    by_cases hp : p ∈ C
    · simpa [hp] using (norm_le_pi_norm s p).trans hs1
    · simpa [hp] using hR0.le
  set sC : MacIdx d N₀ M → ℂ := fun i => if i ∈ C then s i else 0 with hsCdef
  have hsupp : sC ∈ supportedOn C := fun i hi => by simp [hsCdef, hi]
  rw [hser sC (mem_closedBall_zero_iff.2 hsC), norm_neg]
  have hterm : ∀ n : ℕ, ‖((𝐓[a, sC]) ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤
      Y.card * q * q ^ n := by
    intro n
    rw [norm_div]
    have hn : (1 : ℝ) ≤ ‖((n : ℂ) + 1)‖ := by
      have : ((n : ℂ) + 1) = ((n + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this, Complex.norm_natCast]; exact_mod_cast Nat.succ_pos n
    calc ‖((𝐓[a, sC]) ^ (n + 1)).trace‖ / ‖((n : ℂ) + 1)‖ ≤
          ‖((𝐓[a, sC]) ^ (n + 1)).trace‖ := div_le_self (norm_nonneg _) hn
      _ ≤ Y.card * q ^ (n + 1) := norm_trace_pow_le_of_rows_zero _
          (hKU sC (fun p => (norm_le_pi_norm sC p).trans hsC))
          Y (fun x hx y => tm_row_eq_zero hM hd a hsupp
            (fun h => hx (mem_biUnion_macBoxF.2 h)) y) (Nat.succ_pos n)
      _ = Y.card * q * q ^ n := by ring
  have hgeo := (hasSum_geometric_of_lt_one hq0 hq1).mul_left (Y.card * q)
  calc ‖∑' n : ℕ, ((𝐓[a, sC]) ^ (n + 1)).trace / ((n : ℂ) + 1)‖ ≤
        Y.card * q * (1 - q)⁻¹ := tsum_of_norm_bounded hgeo hterm
    _ = Y.card * (q / (1 - q)) := by rw [div_eq_mul_inv]; ring
    _ ≤ B := by
        rw [hB]
        calc (Y.card : ℝ) * (q / (1 - q)) ≤ (C.card * (8 * M + 1) ^ d) * (q / (1 - q)) :=
              mul_le_mul_of_nonneg_right hYc hq'
          _ = _ := by ring

end GenericFamily

section Mixed

open Balaban.Localization Balaban.Analysis

variable {d N₀ M : ℕ} [NeZero N₀]

/-- The tagged perturbed defect `K_E(s, t)`: entries `∑_z τ_z (R_z - E χ_z G_z)_{xy}`, where `R_z`
and `G_z` are the defect and the box resolvent of `U` (not of `U + E`). -/
local notation "𝐊E[" U ", " E ", " t ", " s "]" =>
  taggedMat Finset.univ (macTags d N₀ M)
    (fun z => boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
      E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG U (macBoxF d N₀ M z) t)) s

/-- A nonzero entry of `R_z - E χ_z G_z` has its column in the box of `z`. -/
theorem mix_col (hM : 0 < M) (U E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ)
    (z : MacIdx d N₀ M) (x y : L1Torus d N₀)
    (h : (boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
      E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG U (macBoxF d N₀ M z) t)) x y ≠ 0) : y ∈ macBox d N₀ M z := by
  by_contra hy
  have hyB : y ∉ macBoxF d N₀ M z := fun h' => hy (mem_macBoxF.1 h')
  apply h
  have hcB : ∀ w, ((macChi d N₀ M z w : ℝ) : ℂ) ≠ 0 → w ∈ macBoxF d N₀ M z := fun w hw =>
    macChi_ne_zero_mem_macBoxF hM hw
  have h1 : boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t x y = 0 := by
    by_contra h1
    exact hyB (mem_of_boxR_ne_zero hcB h1)
  have h2 : (E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
      boxG U (macBoxF d N₀ M z) t)) x y = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun w _ => ?_
    have : (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG U (macBoxF d N₀ M z) t) w y = 0 := by
      by_contra h3
      exact hyB (mem_of_diag_mul_boxG_ne_zero h3)
    rw [this, mul_zero]
  rw [Matrix.sub_apply, h1, h2, sub_zero]

/-- Locality of the entries of `R_z - E χ_z G_z`. -/
theorem mix_agree (hM : 0 < M) (hd : 0 < d)
    {U U' E E' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {t : ℝ} {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    (hE : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, E x y = E' x y)
    (z : MacIdx d N₀ M) (x y : L1Torus d N₀) (hT : macTags d N₀ M z x y ⊆ C) :
    (boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
      E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG U (macBoxF d N₀ M z) t)) x y =
    (boxR U' (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
      E' * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG U' (macBoxF d N₀ M z) t)) x y := by
  have hcov := macTags_cover_box_and_ends hM hd hT
  have hBB : ∀ u ∈ macBoxF d N₀ M z, ∀ v ∈ macBoxF d N₀ M z, U u v = U' u v := fun u hu v hv =>
    hU u (hcov.1 (mem_macBoxF.1 hu)) v (hcov.1 (mem_macBoxF.1 hv))
  have hG := boxG_congr_of_agree_on_box (t := t) hBB
  rw [Matrix.sub_apply, Matrix.sub_apply]
  congr 1
  · exact boxR_apply_congr_of_agree hBB (fun w hw => macChi_ne_zero_mem_macBoxF hM hw)
      (fun w hw => hU x hcov.2.1 w (hcov.1 (mem_macBoxF.1 hw))) y
  · rw [hG, Matrix.mul_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    by_cases hw : (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG U' (macBoxF d N₀ M z) t) w y = 0
    · rw [hw, mul_zero, mul_zero]
    · have hwB : ((macChi d N₀ M z w : ℝ) : ℂ) ≠ 0 := by
        intro h0
        apply hw
        rw [Matrix.diagonal_mul, h0, zero_mul]
      rw [hE x hcov.2.1 w (hcov.1 (mem_macBoxF.1 (macChi_ne_zero_mem_macBoxF hM hwB)))]

/-- At `s = 1`: `K_E(1, t) = 1 - (U + E + t) ∑_z χ_z G_z`. -/
theorem mix_one (U E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) :
    𝐊E[U, E, t, (fun _ : MacIdx d N₀ M => (1 : ℂ))] =
      1 - shiftMat (U + E) t * ∑ z : MacIdx d N₀ M,
        Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) * boxG U (macBoxF d N₀ M z) t := by
  rw [taggedMat_one, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have h := parametrix_identity (Finset.univ : Finset (MacIdx d N₀ M)) (macBoxF d N₀ M)
    (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (fun u => by
      exact_mod_cast macChi_sum (d := d) (m := N₀) (M := M) u) U t
  have hs : shiftMat (U + E) t = shiftMat U t + E := by
    unfold shiftMat; abel
  have h' : ∑ z : MacIdx d N₀ M, boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t =
      1 - shiftMat U t * ∑ z : MacIdx d N₀ M,
        Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) * boxG U (macBoxF d N₀ M z) t := by
    rw [h]; abel
  rw [h', hs, add_mul]; abel

/-- The determinant of `1 - K_E(1, t)`. -/
theorem mix_det_one (U E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ) :
    (1 - 𝐊E[U, E, t, (fun _ : MacIdx d N₀ M => (1 : ℂ))]).det =
      (shiftMat (U + E) t).det * (taggedG Finset.univ (macBoxF d N₀ M)
        (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M) U t (fun _ => 1)).det := by
  rw [mix_one, taggedG_one, sub_sub_cancel, Matrix.det_mul]

end Mixed

section Estimates

open Balaban.Localization Balaban.Analysis

variable {d L N₀ k M : ℕ} [NeZero N₀] [NeZero L] {v a : ℝ}

/-- **Row sums of the `E`-part of the perturbed defect.**  For `WSmall rE η E` with
`pdEps d L / 4 ≤ rE`, on the closed polydisc `‖s p‖ ≤ e^κ` and for `0 ≤ r ≤ pdEps d L / 8`,
`κ 7^d ≤ (pdEps d L / 8) M`:
`∑_y e^{r dist x y} ‖∑_z τ_z (E χ_z G_z)_{xy}‖ ≤ e^{Hκ} (2 / g_*) η ballConst(3 ε / 4)`. -/
theorem taggedE_row_sum (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {rE η : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
    (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ)
    (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) *
        ‖taggedMat Finset.univ (macTags d N₀ M)
          (fun z => E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s x y‖ ≤
      Real.exp (pdH d * κ) * (2 / finalGap d L * η * ballConst d (3 * pdEps d L / 4)) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hg : 0 < finalGap d L := finalGap_pos hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hε0 : 0 < pdEps d L := pdEps_pos hd
  set ε : ℝ := pdEps d L with hε
  set σ : ℝ := r + κ * 7 ^ d / M with hσdef
  have hσ0 : 0 ≤ σ := by positivity
  have hσ : σ ≤ ε / 4 := by
    have : κ * 7 ^ d / M ≤ ε / 8 := by rw [div_le_iff₀ hM']; linarith
    linarith
  have hη0 : 0 ≤ η := le_trans (by positivity) (hE.1 x)
  have hEσ : ∑ w, ‖E x w‖ * Real.exp (σ * dist x w) ≤ η :=
    (Finset.sum_le_sum fun w _ => mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right (hσ.trans hrE) dist_nonneg))
      (norm_nonneg _)).trans (hE.1 x)
  have hεc : ε ≤ ctRate (finalDecayC d L) (blockDecayRate d) (finalGap d L)
      (ballConst d (blockDecayRate d / 4)) := min_le_right _ _
  have hGb : ∀ z w y, ‖boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t w y‖ ≤
      2 / finalGap d L * Real.exp (-ε * dist w y) := by
    intro z w y
    have h := boxG_entry_bound_of_coercive (finalOp d L N₀ k v a) (finalDecayC_pos hd).le
      (blockDecayRate_pos hd) hg (finalMass_isCoercive hd hv0 hv1 ha1 hmass)
      (finalMass_entry_decay hd hk hv0 ha1 ha2) ht (macBoxF d N₀ M z) w y
    refine h.trans (mul_le_mul ?_ ?_ (Real.exp_pos _).le (by positivity))
    · exact div_le_div_of_nonneg_left (by norm_num) hg (by linarith)
    · exact Real.exp_le_exp.2 (by nlinarith [dist_nonneg (x := w) (y := y)])
  -- the tag bound
  have hT : ∀ (y : L1Torus d N₀) (z : MacIdx d N₀ M), ‖tagMon (macTags d N₀ M z x y) s‖ ≤
      Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) := by
    intro y z
    refine (norm_tagMon_le _ hs).trans ?_
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have := macTags_card_le hM z x y
    unfold pdH
    nlinarith
  -- entrywise bound of one box term
  have hone : ∀ (z : MacIdx d N₀ M) (y : L1Torus d N₀),
      ‖(E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) x y‖ ≤
        ∑ w, ‖E x w‖ * (macChi d N₀ M z w * (2 / finalGap d L * Real.exp (-ε * dist w y))) := by
    intro z y
    rw [Matrix.mul_apply]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun w _ => ?_)
    rw [norm_mul, Matrix.diagonal_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (macChi_nonneg z w)]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hGb z w y) (macChi_nonneg z w))
      (norm_nonneg _)
  have hentry : ∀ y : L1Torus d N₀, ‖taggedMat Finset.univ (macTags d N₀ M)
      (fun z => E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
        boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s x y‖ ≤
      Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M)) *
        ∑ w, ‖E x w‖ * (2 / finalGap d L * Real.exp (-ε * dist w y)) := by
    intro y
    simp only [taggedMat, Matrix.of_apply]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ z : MacIdx d N₀ M, ‖tagMon (macTags d N₀ M z x y) s * (E *
          (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) x y‖
        ≤ ∑ z : MacIdx d N₀ M, (Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M))) *
          ∑ w, ‖E x w‖ * (macChi d N₀ M z w * (2 / finalGap d L * Real.exp (-ε * dist w y))) :=
          Finset.sum_le_sum fun z _ => by
            rw [norm_mul]
            exact mul_le_mul (hT y z) (hone z y) (norm_nonneg _) (by positivity)
      _ = (Real.exp (pdH d * κ) * Real.exp (κ * 7 ^ d * (dist x y / M))) *
          ∑ w, ‖E x w‖ * (2 / finalGap d L * Real.exp (-ε * dist w y)) := by
          rw [← Finset.mul_sum, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun w _ => ?_
          have h1 := macChi_sum (d := d) (m := N₀) (M := M) w
          calc ∑ z : MacIdx d N₀ M, ‖E x w‖ * (macChi d N₀ M z w *
                (2 / finalGap d L * Real.exp (-ε * dist w y)))
              = ‖E x w‖ * ((∑ z : MacIdx d N₀ M, macChi d N₀ M z w) *
                (2 / finalGap d L * Real.exp (-ε * dist w y))) := by
                rw [Finset.sum_mul, Finset.mul_sum]
            _ = _ := by rw [h1, one_mul]
  have hexp : ∀ y : L1Torus d N₀, Real.exp (r * dist x y) *
      Real.exp (κ * 7 ^ d * (dist x y / M)) = Real.exp (σ * dist x y) := by
    intro y
    rw [← Real.exp_add]; congr 1; simp only [hσdef]; ring
  have hball : ∀ w : L1Torus d N₀, ∑ y, Real.exp (-(3 * ε / 4) * dist w y) ≤
      ballConst d (3 * ε / 4) := fun w => ballSum_L1Torus d N₀ (by positivity) w
  calc _ ≤ ∑ y : L1Torus d N₀, Real.exp (pdH d * κ) * (Real.exp (σ * dist x y) *
        ∑ w, ‖E x w‖ * (2 / finalGap d L * Real.exp (-ε * dist w y))) := by
        refine Finset.sum_le_sum fun y _ => ?_
        calc _ ≤ Real.exp (r * dist x y) * (Real.exp (pdH d * κ) *
            Real.exp (κ * 7 ^ d * (dist x y / M)) *
            ∑ w, ‖E x w‖ * (2 / finalGap d L * Real.exp (-ε * dist w y))) :=
            mul_le_mul_of_nonneg_left (hentry y) (Real.exp_pos _).le
          _ = _ := by rw [← hexp y]; ring
    _ = Real.exp (pdH d * κ) * ∑ y : L1Torus d N₀, ∑ w : L1Torus d N₀,
          Real.exp (σ * dist x y) * (‖E x w‖ * (2 / finalGap d L * Real.exp (-ε * dist w y))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum]
    _ ≤ Real.exp (pdH d * κ) * ∑ y : L1Torus d N₀, ∑ w : L1Torus d N₀,
          (‖E x w‖ * Real.exp (σ * dist x w)) * (2 / finalGap d L *
            Real.exp (-(3 * ε / 4) * dist w y)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => Finset.sum_le_sum
          fun w _ => ?_) (Real.exp_pos _).le
        have htri : σ * dist x y ≤ σ * dist x w + σ * dist w y := by
          nlinarith [dist_triangle x w y]
        have e1 : Real.exp (σ * dist x y) * Real.exp (-ε * dist w y) ≤
            Real.exp (σ * dist x w) * Real.exp (-(3 * ε / 4) * dist w y) := by
          rw [← Real.exp_add, ← Real.exp_add]
          apply Real.exp_le_exp.2
          nlinarith [dist_nonneg (x := w) (y := y)]
        calc Real.exp (σ * dist x y) * (‖E x w‖ * (2 / finalGap d L * Real.exp (-ε * dist w y)))
            = ‖E x w‖ * (2 / finalGap d L) *
              (Real.exp (σ * dist x y) * Real.exp (-ε * dist w y)) := by ring
          _ ≤ ‖E x w‖ * (2 / finalGap d L) *
              (Real.exp (σ * dist x w) * Real.exp (-(3 * ε / 4) * dist w y)) :=
              mul_le_mul_of_nonneg_left e1 (by positivity)
          _ = _ := by ring
    _ = Real.exp (pdH d * κ) * ∑ w : L1Torus d N₀, (‖E x w‖ * Real.exp (σ * dist x w)) *
          (2 / finalGap d L * ∑ y, Real.exp (-(3 * ε / 4) * dist w y)) := by
        rw [Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
    _ ≤ Real.exp (pdH d * κ) * ∑ w : L1Torus d N₀, (‖E x w‖ * Real.exp (σ * dist x w)) *
          (2 / finalGap d L * ballConst d (3 * ε / 4)) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun w _ => ?_) (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hball w) (by positivity))
          (by positivity)
    _ = Real.exp (pdH d * κ) * ((∑ w : L1Torus d N₀, ‖E x w‖ * Real.exp (σ * dist x w)) *
          (2 / finalGap d L * ballConst d (3 * ε / 4))) := by rw [Finset.sum_mul]
    _ ≤ Real.exp (pdH d * κ) * (η * (2 / finalGap d L * ballConst d (3 * ε / 4))) := by
        have hb : 0 ≤ ballConst d (3 * ε / 4) := ballConst_decay_nonneg (by positivity)
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hEσ (by positivity))
          (Real.exp_pos _).le
    _ = _ := by ring

/-- **Row sums of the perturbed defect `K_E`** (E1).  Under the hypotheses of `taggedK_row_sum` and
`taggedE_row_sum`:
`∑_y e^{r dist x y} ‖K_E(s, t) x y‖ ≤ B e^{Hκ}/M + e^{Hκ} (2 / g_*) η ballConst(3 ε / 4)`. -/
theorem taggedKE_row_sum (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {rE η : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
    (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ r : ℝ} (hκ : 0 ≤ κ)
    (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8) (hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) (x : L1Torus d N₀) :
    ∑ y, Real.exp (r * dist x y) *
        ‖taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s x y‖ ≤
      pdB d L * Real.exp (pdH d * κ) / M +
        Real.exp (pdH d * κ) * (2 / finalGap d L * η * ballConst d (3 * pdEps d L / 4)) := by
  have hsplit : taggedMat Finset.univ (macTags d N₀ M)
      (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
          (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s =
      taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t s -
      taggedMat Finset.univ (macTags d N₀ M)
        (fun z => E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s := by
    ext x y
    simp only [taggedK, taggedMat, Matrix.of_apply, Matrix.sub_apply, mul_sub,
      Finset.sum_sub_distrib]
  rw [hsplit]
  calc _ ≤ ∑ y, (Real.exp (r * dist x y) * ‖taggedK Finset.univ (macBoxF d N₀ M)
          (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ)) (macTags d N₀ M)
          (finalOp d L N₀ k v a) t s x y‖ + Real.exp (r * dist x y) *
        ‖taggedMat Finset.univ (macTags d N₀ M)
        (fun z => E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s x y‖) := by
        refine Finset.sum_le_sum fun y _ => ?_
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left (by simpa using norm_sub_le _ _) (Real.exp_pos _).le
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add
        (taggedK_row_sum hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hr0 hr hκM hs x)
        (taggedE_row_sum hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hr0 hr hκM hs x)

section Defect

variable (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2)
  (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
  {rE η : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
  (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 ≤ κ)
  (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
  (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η * ballConst d (3 * pdEps d L / 4))) ≤ 1)

include hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hMB hMκ hη

/-- Row sums of `K_E` are at most `1/2` on the closed polydisc. -/
theorem taggedKE_rowsum_le_half {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ)
    (x : L1Torus d N₀) :
    ∑ y, ‖taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s x y‖ ≤ 1 / 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have := taggedKE_row_sum hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ le_rfl
    (div_nonneg (pdEps_pos hd).le (by norm_num)) hκM hs x
  simpa using this.trans (by linarith)

/-- **E1.  Invertibility of the perturbed defect on the full closed polydisc.**  For
`0 ≤ r ≤ pdEps d L / 8` and every `s` with `‖s p‖ ≤ e^κ`, `1 - K_E(s, t)` is invertible and the
weighted row sums of its inverse are at most `2`. -/
theorem taggedKE_isUnit_inv_weighted {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ pdEps d L / 8)
    {s : MacIdx d N₀ M → ℂ} (hs : ∀ p, ‖s p‖ ≤ Real.exp κ) :
    IsUnit (1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s) ∧
      ∀ x, ∑ y, Real.exp (r * dist x y) *
        ‖(1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s)⁻¹ x y‖ ≤ 2 := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hq : pdB d L * Real.exp (pdH d * κ) / M ≤ 1 / 4 := by
    rw [div_le_iff₀ hM']; linarith
  have hκM : κ * 7 ^ d ≤ pdEps d L / 8 * M := by linarith
  have hw1 : ∀ x y : L1Torus d N₀, 1 ≤ Real.exp (r * dist x y) := fun x y =>
    Real.one_le_exp (mul_nonneg hr0 dist_nonneg)
  have hww : ∀ x : L1Torus d N₀, Real.exp (r * dist x x) = 1 := fun x => by simp
  have hsub : ∀ x u y : L1Torus d N₀,
      Real.exp (r * dist x y) ≤ Real.exp (r * dist x u) * Real.exp (r * dist u y) := by
    intro x u y
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [dist_triangle x u y])
  have hinv := weightedRow_inv_le (fun x y : L1Torus d N₀ => Real.exp (r * dist x y)) hw1 hww hsub
    (taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s) (q := 1 / 2) (by norm_num)
    (fun x => (taggedKE_row_sum hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hr0 hr hκM hs x).trans
      (by linarith))
  have h2 : 1 / (1 - (1 / 2 : ℝ)) = 2 := by norm_num
  rw [h2] at hinv
  exact hinv

/-- **E2, existence.**  There are `ρ' > e^κ` and `ell`, analytic on the polydisc `‖s p‖ < ρ'`, with
`det (1 - K_E(s, t)) = exp (ell s)` there, `ell 0 = 0` and
`exp (ell 1) = det (finalOp + E + t) · det (∑_z χ_z G_z)`; the block factor is that of `finalOp`. -/
theorem exists_log_det_taggedKE :
    ∃ ρ' : ℝ, Real.exp κ < ρ' ∧ ∃ ell : (MacIdx d N₀ M → ℂ) → ℂ,
      AnalyticOnNhd ℂ ell (Metric.ball 0 ρ') ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det = Complex.exp (ell s)) ∧
      ell 0 = 0 ∧
      Complex.exp (ell (fun _ => 1)) = (shiftMat (finalOp d L N₀ k v a + E) t).det *
        (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det := by
  obtain ⟨ρ', hρ', ell, h1, h2, h3⟩ := exists_analytic_log_det_one_sub
    (fun s => taggedMat Finset.univ (macTags d N₀ M)
      (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
          (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s)
    (fun x y s0 => taggedMat_analytic _ _ _ x y s0) (tm_zero hM hd _)
    (Real.exp_pos κ).le fun s hs =>
      (taggedKE_isUnit_inv_weighted hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hMB hMκ hη
        le_rfl (div_nonneg (pdEps_pos hd).le (by norm_num)) (s := s)
        (fun p => (norm_le_pi_norm s p).trans hs)).1
  have h1mem : (fun _ : MacIdx d N₀ M => (1 : ℂ)) ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ' := by
    rw [mem_ball_zero_iff]
    refine lt_of_le_of_lt ?_ hρ'
    refine (pi_norm_le_iff_of_nonneg (Real.exp_pos κ).le).2 fun p => ?_
    simpa using Real.one_le_exp hκ
  refine ⟨ρ', hρ', ell, h1, h2, h3, ?_⟩
  rw [← h2 _ h1mem]
  exact mix_det_one _ _ _

/-- **E2, vanishing at separated supports** for the perturbed logarithm. -/
theorem taggedKE_coef_eq_zero_of_separated (hκ' : 0 < κ)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det = Complex.exp (ell s))
    {C A : Finset (MacIdx d N₀ M)} (hAC : A ⊆ C) (hA : A.Nonempty) (hB : (C \ A).Nonempty)
    (hsep : Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A))) :
    coef ell C = 0 :=
  tm_coef_eq_zero_of_separated hM hd _ (fun z x y h => mix_col hM _ E t z x y h) hκ'
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (fun s hs x => taggedKE_rowsum_le_half hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hMB hMκ hη
      hs x) hρ' hell h0 hdet hAC hA hB hsep

/-- **E2, volume-uniform bound** for the perturbed logarithm:
`‖coef ell C‖ ≤ |C| (8M + 1)^d / (e^κ - 1)^{|C|}`. -/
theorem taggedKE_norm_coef_le (hκ' : 0 < κ)
    {ρ' : ℝ} (hρ' : Real.exp κ < ρ') {ell : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ')) (h0 : ell 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det = Complex.exp (ell s))
    (C : Finset (MacIdx d N₀ M)) :
    ‖coef ell C‖ ≤ (C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card := by
  have h := tm_norm_coef_le hM hd _ hκ' (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
    (fun s hs x => taggedKE_rowsum_le_half hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ hMB hMκ hη
      hs x) hρ' hell h0 hdet C
  have e : (1 / 2 : ℝ) / (1 - 1 / 2) = 1 := by norm_num
  rwa [e, mul_one] at h

end Defect

section Locality

variable {d N₀ M : ℕ} [NeZero N₀]

/-- **E2, locality in the operator and the perturbation.**  If `(U, E)` and `(U', E')` agree on
`Y(C) × Y(C)`, the logarithms of `det (1 - K_E)` and `det (1 - K'_{E'})` have the same coefficient
at `C`. -/
theorem coef_eq_of_agree_taggedKE (hM : 0 < M) (hd : 0 < d) {R : ℝ} (hR : 1 < R)
    {U U' E E' : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {t : ℝ} {C : Finset (MacIdx d N₀ M)}
    (hU : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, U x y = U' x y)
    (hE : ∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, E x y = E' x y)
    {ell ell' : (MacIdx d N₀ M → ℂ) → ℂ} (hell : ContinuousOn ell (Metric.ball 0 R))
    (hell' : ContinuousOn ell' (Metric.ball 0 R)) (h0 : ell 0 = 0) (h0' : ell' 0 = 0)
    (hdet : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) R,
      (1 - taggedMat Finset.univ (macTags d N₀ M)
        (fun z => boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
          E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG U (macBoxF d N₀ M z) t)) s).det = Complex.exp (ell s))
    (hdet' : ∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) R,
      (1 - taggedMat Finset.univ (macTags d N₀ M)
        (fun z => boxR U' (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
          E' * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG U' (macBoxF d N₀ M z) t)) s).det = Complex.exp (ell' s)) :
    coef ell C = coef ell' C :=
  tm_coef_eq_of_agree hR (fun z x y hT => mix_agree hM hd hU hE z x y hT) hell hell' h0 h0'
    hdet hdet'

/-- For `E = 0` the perturbed defect is the defect. -/
theorem taggedKE_zero_eq (U : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) (t : ℝ)
    (s : MacIdx d N₀ M → ℂ) :
    taggedMat Finset.univ (macTags d N₀ M)
      (fun z => boxR U (macBoxF d N₀ M z) (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
        (0 : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ) *
          (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
            boxG U (macBoxF d N₀ M z) t)) s =
      taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) U t s := by
  simp [taggedK]

end Locality


/-- **The determinant ratio as a product over cell sets.**  Let `ell0` and `ellE` be analytic
logarithms of `det (1 - K(s, t))` and `det (1 - K_E(s, t))` on the polydisc of radius `ρ0`, `ρE`
`> e^κ`, with the values at `s = 1` given by the products with the common block factor
`det (∑_z χ_z G_z)` of `finalOp`.  Then
`det (finalOp + E + t) = det (finalOp + t) · ∏_C exp (coef ellE C - coef ell0 C)`. -/
theorem det_shiftMat_add_eq_mul_prod_exp_coef_sub {t κ : ℝ} (hκ : 0 < κ)
    {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} {ρ0 ρE : ℝ} (hρ0 : Real.exp κ < ρ0)
    (hρE : Real.exp κ < ρE) {ell0 ellE : (MacIdx d N₀ M → ℂ) → ℂ}
    (hell0 : AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ0))
    (hellE : AnalyticOnNhd ℂ ellE (Metric.ball 0 ρE))
    (h10 : Complex.exp (ell0 (fun _ => 1)) = (shiftMat (finalOp d L N₀ k v a) t).det *
      (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det)
    (h1E : Complex.exp (ellE (fun _ => 1)) = (shiftMat (finalOp d L N₀ k v a + E) t).det *
      (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det) :
    (shiftMat (finalOp d L N₀ k v a + E) t).det = (shiftMat (finalOp d L N₀ k v a) t).det *
      ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ellE C - coef ell0 C) := by
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hR0 : 0 < Real.exp κ := by linarith
  have hsum := fun (ρ : ℝ) (hρ : Real.exp κ < ρ) (ell : (MacIdx d N₀ M → ℂ) → ℂ)
    (hell : AnalyticOnNhd ℂ ell (Metric.ball 0 ρ)) =>
    sum_coef_eq hR (hell.mono (fun s hs => by
      rw [polydisc_eq_ball hR0] at hs
      exact Metric.ball_subset_ball hρ.le hs))
  have hP0 : (shiftMat (finalOp d L N₀ k v a) t).det *
      (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det =
      ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ell0 C) := by
    rw [← h10, show (fun _ : MacIdx d N₀ M => (1 : ℂ)) = 1 from rfl, hsum ρ0 hρ0 ell0 hell0,
      Complex.exp_sum]
  have hPE : (shiftMat (finalOp d L N₀ k v a + E) t).det *
      (taggedG Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
        (macTags d N₀ M) (finalOp d L N₀ k v a) t (fun _ => 1)).det =
      ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ellE C) := by
    rw [← h1E, show (fun _ : MacIdx d N₀ M => (1 : ℂ)) = 1 from rfl, hsum ρE hρE ellE hellE,
      Complex.exp_sum]
  have hne : ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ell0 C) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun C _ => Complex.exp_ne_zero _
  have hd0 := left_ne_zero_of_mul (hP0 ▸ hne)
  have hdB := right_ne_zero_of_mul (hP0 ▸ hne)
  have hquot : ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ellE C - coef ell0 C) =
      (∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ellE C)) /
        ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ell0 C) := by
    rw [← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun C _ => Complex.exp_sub _ _
  rw [hquot, ← hPE, ← hP0]
  field_simp

/-- **The localized determinant ratio of the perturbed final operator** (E1, E2).  For
`WSmall rE η E` with `pdEps d L / 4 ≤ rE`, `η` small in the sense of `hη`, `M ≥ 4 B e^{Hκ}`,
`8 κ 7^d ≤ ε M`: there are `ρ' > e^κ` and functions `ell0`, `ellE` of the cut parameters, analytic on
the polydisc `‖s p‖ < ρ'`, with `ell0 0 = ellE 0 = 0`, `det (1 - K(s, t)) = exp (ell0 s)`,
`det (1 - K_E(s, t)) = exp (ellE s)`, and
* the ratio `det (finalOp + E + t) = det (finalOp + t) · ∏_C exp (coef ellE C - coef ell0 C)`;
* locality: `coef ellE C = coef ell0 C` when `E = 0` on `Y(C) × Y(C)`;
* vanishing: both coefficients vanish at a separated support;
* the bound `‖coef ellE C - coef ell0 C‖ ≤ 2 |C| (8M + 1)^d / (e^κ - 1)^{|C|}`. -/
theorem exists_det_ratio_localized (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    {rE η : ℝ} {E : Matrix (L1Torus d N₀) (L1Torus d N₀) ℂ} (hE : WSmall rE η E)
    (hrE : pdEps d L / 4 ≤ rE) {t : ℝ} (ht : 0 ≤ t) (hM : 0 < M) {κ : ℝ} (hκ : 0 < κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    (hη : 4 * (Real.exp (pdH d * κ) * (2 / finalGap d L * η *
      ballConst d (3 * pdEps d L / 4))) ≤ 1) :
    ∃ ρ' : ℝ, Real.exp κ < ρ' ∧ ∃ ell0 ellE : (MacIdx d N₀ M → ℂ) → ℂ,
      AnalyticOnNhd ℂ ell0 (Metric.ball 0 ρ') ∧ AnalyticOnNhd ℂ ellE (Metric.ball 0 ρ') ∧
      ell0 0 = 0 ∧ ellE 0 = 0 ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedK Finset.univ (macBoxF d N₀ M) (fun z u => ((macChi d N₀ M z u : ℝ) : ℂ))
          (macTags d N₀ M) (finalOp d L N₀ k v a) t s).det = Complex.exp (ell0 s)) ∧
      (∀ s ∈ Metric.ball (0 : MacIdx d N₀ M → ℂ) ρ',
        (1 - taggedMat Finset.univ (macTags d N₀ M)
          (fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
              (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
            E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
              boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t)) s).det =
          Complex.exp (ellE s)) ∧
      (shiftMat (finalOp d L N₀ k v a + E) t).det = (shiftMat (finalOp d L N₀ k v a) t).det *
        ∏ C : Finset (MacIdx d N₀ M), Complex.exp (coef ellE C - coef ell0 C) ∧
      (∀ C : Finset (MacIdx d N₀ M),
        (∀ x ∈ macRegion d N₀ M C, ∀ y ∈ macRegion d N₀ M C, E x y = 0) →
          coef ellE C = coef ell0 C) ∧
      (∀ C A : Finset (MacIdx d N₀ M), A ⊆ C → A.Nonempty → (C \ A).Nonempty →
        Disjoint (macRegion d N₀ M A) (macRegion d N₀ M (C \ A)) →
          coef ellE C = 0 ∧ coef ell0 C = 0) ∧
      (∀ C : Finset (MacIdx d N₀ M), ‖coef ellE C - coef ell0 C‖ ≤
        2 * ((C.card * (8 * M + 1) ^ d) / (Real.exp κ - 1) ^ C.card)) := by
  obtain ⟨ρ0, hρ0, ell0, g1, g2, g3, g4, -⟩ := exists_series_log_det_taggedDefect (N₀ := N₀) hd hk
    hv0 hv1 ha1 ha2 hmass ht hM hκ.le hMB hMκ
  obtain ⟨ρE, hρE, ellE, f1, f2, f3, f4⟩ := exists_log_det_taggedKE hd hk hv0 hv1 ha1 ha2 hmass hE
    hrE ht hM hκ.le hMB hMκ hη
  have hR : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  have hρ : Real.exp κ < min ρ0 ρE := lt_min hρ0 hρE
  have hb0 : Metric.ball (0 : MacIdx d N₀ M → ℂ) (min ρ0 ρE) ⊆ Metric.ball 0 ρ0 :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hbE : Metric.ball (0 : MacIdx d N₀ M → ℂ) (min ρ0 ρE) ⊆ Metric.ball 0 ρE :=
    Metric.ball_subset_ball (min_le_right _ _)
  have hbR0 : Metric.ball (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρ0 :=
    Metric.ball_subset_ball hρ0.le
  have hbRE : Metric.ball (0 : MacIdx d N₀ M → ℂ) (Real.exp κ) ⊆ Metric.ball 0 ρE :=
    Metric.ball_subset_ball hρE.le
  refine ⟨min ρ0 ρE, hρ, ell0, ellE, g1.mono hb0, f1.mono hbE, g3, f3,
    fun s hs => g2 s (hb0 hs), fun s hs => f2 s (hbE hs),
    det_shiftMat_add_eq_mul_prod_exp_coef_sub hκ hρ0 hρE g1 f1 g4 f4, ?_, ?_, ?_⟩
  · intro C hC
    refine (tm_coef_eq_of_agree (a := fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
        (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t -
        E * (Matrix.diagonal (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) *
          boxG (finalOp d L N₀ k v a) (macBoxF d N₀ M z) t))
      (a' := fun z => boxR (finalOp d L N₀ k v a) (macBoxF d N₀ M z)
        (fun u => ((macChi d N₀ M z u : ℝ) : ℂ)) t) hR
      (fun z x y hT => ?_) (f1.continuousOn.mono hbRE) (g1.continuousOn.mono hbR0) f3 g3
      (fun s hs => f2 s (hbRE hs)) (fun s hs => g2 s (hbR0 hs)))
    have := mix_agree hM hd (U := finalOp d L N₀ k v a) (U' := finalOp d L N₀ k v a) (E := E)
      (E' := 0) (t := t) (C := C) (fun _ _ _ _ => rfl)
      (fun x hx y hy => by rw [hC x hx y hy]; rfl) z x y hT
    simpa using this
  · intro C A hAC hA hB hsep
    exact ⟨taggedKE_coef_eq_zero_of_separated hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ.le hMB
      hMκ hη hκ hρE f1 f3 f2 hAC hA hB hsep,
      coef_eq_zero_final_of_separated hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ hρ0 g1 g3 g2
        hAC hA hB hsep⟩
  · intro C
    have h1 := taggedKE_norm_coef_le hd hk hv0 hv1 ha1 ha2 hmass hE hrE ht hM hκ.le hMB hMκ hη hκ
      hρE f1 f3 f2 C
    have h2 := norm_coef_le_final hd hk hv0 hv1 ha1 ha2 hmass ht hM hκ hMB hMκ hρ0 g1 g3 g2 C
    have hpos : 0 ≤ (C.card * (8 * M + 1) ^ d : ℝ) / (Real.exp κ - 1) ^ C.card :=
      div_nonneg (by positivity) (pow_nonneg (by linarith) _)
    have e : (C.card * ((8 * M + 1) ^ d * (1 / 3)) : ℝ) / (Real.exp κ - 1) ^ C.card =
        (1 / 3) * ((C.card * (8 * M + 1) ^ d : ℝ) / (Real.exp κ - 1) ^ C.card) := by
      ring
    rw [e] at h2
    calc ‖coef ellE C - coef ell0 C‖ ≤ ‖coef ellE C‖ + ‖coef ell0 C‖ := norm_sub_le _ _
      _ ≤ _ := by linarith

end Estimates

end Balaban.Green
