/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HatLabelsDep
public import Balaban.Fluctuation.Thm31Avg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Labels and activities of the hat expansion (FLUCTUATION.md §3.4, Theorem 3.4)

* `thickLabels`: the `CubeLabels` whose sites are a finite family of domains `Z ∈ 𝒟_j`, with the
  size `𝗱(Z) = d^cov_j(Z)`; `entropy_thick` is the entropy clause `∑_{Z ⊇ □} e^{-κ₀ 𝗱(Z)} ≤ K₀`
  (G2).
* `hat_real_bound`: the arithmetic that turns the bound `ε_U e^{-a d^cov(Y)}` of the terms of a
  domain `Y` into a bound `ε_H e^{-κ_H d^cov(Z)}` for the sum over the domains with the same
  thickening `Z`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer

section Labels

variable {d L N₁ m₁ K : ℕ} [NeZero L] [NeZero N₁] {m₀ j : ℕ}

/-- **The labels of a finite family of domains**: the domain `Z` itself, of size `d^cov_j(Z)`. -/
noncomputable def thickLabels (𝒵 : Finset (Set (CTorus d L N₁ m₁ K))) (h : ∀ Z ∈ 𝒵, IsDj m₀ j Z) :
    CubeLabels (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ {Z // Z ∈ 𝒵} where
  ysite Z := Z.1
  dl Z := treeLenCovOne m₀ j Z.1
  isDj Z := h Z.1 Z.2
  meets Z := by
    obtain ⟨x, hx⟩ := (h Z.1 Z.2).1
    exact ⟨x, hx, Set.mem_univ x⟩
  size Z := Or.inl rfl

open Classical in
/-- **Entropy clause for the thickened labels** (G2): for `κ₀ ≥ a_ent + 1`, the sum over the
labels containing a given cube `□` of `e^{-κ₀ 𝗱}` is at most `K₀`. -/
theorem entropy_thick (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (𝒵 : Finset (Set (CTorus d L N₁ m₁ K)))
    (h : ∀ Z ∈ 𝒵, IsDj m₀ j Z) {κ0 : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0)
    (b : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Set.univ) :
    ∑ Z : {Z // Z ∈ 𝒵}, (if box b.1 (cellSide L m₀ m₁ j) ⊆ Z.1 then
        Real.exp (-κ0 * treeLenCovOne m₀ j Z.1) else 0) ≤ K0 d L κ0 := by
  have hG2 := G2_X (m₀ := m₀) (j := j) hN hj (Ω := Set.univ)
    (fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z, Set.subset_univ _⟩)
    b.2.1 b.2.2 hκ0
  rw [Finset.sum_coe_sort 𝒵 (fun Z => if box b.1 (cellSide L m₀ m₁ j) ⊆ Z then
    Real.exp (-κ0 * treeLenCovOne m₀ j Z) else 0), ← Finset.sum_filter]
  refine le_trans ?_ hG2
  calc ∑ Z ∈ 𝒵.filter (fun Z => box b.1 (cellSide L m₀ m₁ j) ⊆ Z), Real.exp (-κ0 * treeLenCovOne m₀ j Z)
      = ∑ Z ∈ 𝒵.filter (fun Z => box b.1 (cellSide L m₀ m₁ j) ⊆ Z),
          Real.exp (-κ0 * dcovMod m₀ j Set.univ Z) := by
        refine Finset.sum_congr rfl fun Z _ => ?_
        rw [dcovMod_of_subset (Set.subset_univ Z)]
    _ ≤ _ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun Z hZ => ?_) (fun _ _ _ => (Real.exp_pos _).le)
        obtain ⟨hZ1, hZ2⟩ := Finset.mem_filter.1 hZ
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨⟨h Z hZ1, fun z hz => absurd (Set.mem_univ z) hz⟩, hZ2⟩

theorem hat_exp_bound {a A B tY tZ : ℝ} (hA : 0 < A) (ha : 0 ≤ a) (hZY : tZ ≤ A * tY + B) :
    Real.exp (-a * tY) ≤ Real.exp (a * B / A) * Real.exp (-(a / A) * tZ) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.2 ?_
  have h : a * B / A - a / A * tZ + a * tY = a * (A * tY + B - tZ) / A := by
    field_simp; ring
  have h2 : 0 ≤ a * (A * tY + B - tZ) / A :=
    div_nonneg (mul_nonneg ha (by linarith)) hA.le
  nlinarith

theorem two_pow_le_exp {m : ℕ} {c : ℝ} (hm : (m : ℝ) ≤ c) : ((2 : ℝ) ^ m) ≤ Real.exp c := by
  have h1 : (2 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  rw [h1]
  refine Real.exp_le_exp.2 ?_
  have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  nlinarith

open Classical in
/-- The number of domains with the same thickening `Z` is at most `e^{c₁ (1 + d^cov_j(Z))}`:
a domain is determined by the cubes it contains, which are cubes of `Z`. -/
theorem card_fiber_thick (hN : L ^ m₀ ∣ N₁) (hj : j ≤ K) (𝒴 : Finset (Set (CTorus d L N₁ m₁ K)))
    (hdom : ∀ Y ∈ 𝒴, IsDj m₀ j Y) (Zf : Set (CTorus d L N₁ m₁ K) → Set (CTorus d L N₁ m₁ K))
    (hsub : ∀ Y ∈ 𝒴, Y ⊆ Zf Y) {Z : Set (CTorus d L N₁ m₁ K)} (hZ : IsDj m₀ j Z) :
    ((𝒴.filter (fun Y => Zf Y = Z)).card : ℝ) ≤ Real.exp (c1 d L * (1 + treeLenCovOne m₀ j Z)) := by
  have hΩ : IsPiUnion m₀ j (Set.univ : Set (CTorus d L N₁ m₁ K)) :=
    fun z _ => ⟨cbase (cellSide L m₀ m₁ j) z, aligned_cbase z,
      mem_box_cbase (cellSide_pos (L := L) m₀ m₁ j) z, Set.subset_univ _⟩
  have h1 : (𝒴.filter (fun Y => Zf Y = Z)).card ≤ 2 ^ (blocksOf m₀ j Set.univ Z).card := by
    rw [← Finset.card_powerset]
    refine Finset.card_le_card_of_injOn (fun Y => blocksOf m₀ j Set.univ Y) (fun Y hY => ?_) ?_
    · obtain ⟨hY1, hY2⟩ := Finset.mem_filter.1 hY
      refine Finset.mem_coe.2 (Finset.mem_powerset.2 fun b hb => mem_blocksOf.2 ?_)
      exact (mem_blocksOf.1 hb).trans (hY2 ▸ hsub Y hY1)
    · intro Y hY Y' hY' h
      have e1 := sitesOf_blocksOf hN hj hΩ (hdom Y (Finset.mem_filter.1 (Finset.mem_coe.1 hY)).1).2.1
      have e2 := sitesOf_blocksOf hN hj hΩ (hdom Y' (Finset.mem_filter.1 (Finset.mem_coe.1 hY')).1).2.1
      simp only [Set.inter_univ] at e1 e2
      rw [← e1, ← e2]
      exact congrArg sitesOf h
  have h2 := card_blocksOf_le hN hj hZ
  have h3 : ((𝒴.filter (fun Y => Zf Y = Z)).card : ℝ) ≤ (2 : ℝ) ^ (blocksOf m₀ j Set.univ Z).card := by
    exact_mod_cast h1
  exact h3.trans (two_pow_le_exp h2)

end Labels

end Balaban.Fluctuation
