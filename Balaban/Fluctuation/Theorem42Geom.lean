/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.TraceEntropy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Theorem 4.2, Step 4: the geometry of the action cubes (FLUCTUATION.md §4.2)

The action cubes of Step 3 are the `π'_j`-cubes `X_b = box b (L a_j)` (`a_j = cellSide j`) with
aligned base `b`, of the localization expansion at scale `j`.

* `treeLenCovOne_box`: `d^cov_j(X_b) = 0` (one cube: the structure is the single point `b`);
* `hopt_box`: the optimal structure required by `cube_expansion` exists;
* `card_aligned_in_box`: a box `box b' (R a)` contains at most `R^d` aligned points of side `a`;
* `card_cubes_in_Y`: the number of action cubes whose base lies in a multiscale polymer domain
  `Y` is at most `L^{(K-j)d}` times the number of cells of `Y` (the "one unit per cube" of (G1)),
  hence at most `L^{(K-j)d} c_B (d̃^cov(Y) + 1)` by the block count.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale

section Box

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ}

omit [NeZero N₁] [NeZero L] in
theorem chosenOne_box (b : CTorus d L N₁ m₁ K) (hb : Aligned (cellSide L m₀ m₁ j) b) :
    ChosenOne m₀ j (box b (L * cellSide L m₀ m₁ j)) {b} :=
  ⟨fun b' hb' => by rw [Set.mem_singleton_iff.1 hb']; exact ⟨hb, subset_rfl⟩,
    fun z hz => ⟨b, rfl, hz⟩⟩

omit [NeZero N₁] [NeZero L] in
theorem connStruct_single (b : CTorus d L N₁ m₁ K) :
    ConnStruct ({b} : Finset (CTorus d L N₁ m₁ K)) ∅ :=
  ⟨Finset.singleton_nonempty b, by simp, fun x hx y hy => by
    rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy]⟩

omit [NeZero N₁] in
theorem meetsOne_box (b : CTorus d L N₁ m₁ K) :
    MeetsOne m₀ j ({b} : Set (CTorus d L N₁ m₁ K)) ({b} : Finset (CTorus d L N₁ m₁ K)) := by
  intro b' hb'
  rw [Set.mem_singleton_iff.1 hb']
  exact ⟨b, Finset.mem_singleton_self b, mem_box_self b (Nat.mul_pos (Nat.pos_of_ne_zero
    (NeZero.ne L)) (cellSide_pos m₀ m₁ j))⟩

omit [NeZero N₁] in
/-- **A single `π'_j`-cube has covering size `0`.** -/
theorem treeLenCovOne_box (b : CTorus d L N₁ m₁ K) (hb : Aligned (cellSide L m₀ m₁ j) b) :
    treeLenCovOne m₀ j (box b (L * cellSide L m₀ m₁ j)) = 0 := by
  have hpos : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  refine le_antisymm ?_ (treeLenCovOne_nonneg m₀ j _)
  unfold treeLenCovOne
  refine csInf_le ⟨0, ?_⟩ ⟨{b}, {b}, ∅, chosenOne_box b hb, connStruct_single b, ?_,
    meetsOne_box b, by simp [bondCost]⟩
  · rintro x ⟨𝒦, W, E, -, -, -, -, rfl⟩
    refine Finset.sum_nonneg fun p _ => ?_
    unfold scaleW; positivity
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_singleton] at hx
    rw [hx]; exact mem_box_self b hpos

omit [NeZero N₁] in
/-- The optimal structure required by `cube_expansion` for the cube `X_b`. -/
theorem hopt_box (b : CTorus d L N₁ m₁ K) (hb : Aligned (cellSide L m₀ m₁ j) b) :
    ∃ (W₀ : Finset (CTorus d L N₁ m₁ K)) (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ box b (L * cellSide L m₀ m₁ j)) ∧
        MeetsOne m₀ j ({b} : Set (CTorus d L N₁ m₁ K)) W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j (box b (L * cellSide L m₀ m₁ j)) := by
  have hpos : 0 < L * cellSide L m₀ m₁ j :=
    Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne L)) (cellSide_pos m₀ m₁ j)
  refine ⟨{b}, ∅, connStruct_single b, ?_, meetsOne_box b, ?_⟩
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_singleton] at hx
    rw [hx]; exact mem_box_self b hpos
  · rw [treeLenCovOne_box b hb]; simp [bondCost]

end Box

section Count

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

open Classical in
/-- A box `box b' (R a)` contains at most `R^d` aligned points of side `a`. -/
theorem card_aligned_in_box {n a R : ℕ} [NeZero n] (ha : a ∣ n) (ha0 : 0 < a) {b' : Torus d n}
    (hb' : Aligned a b') :
    (Finset.univ.filter fun b : Torus d n => Aligned a b ∧ b ∈ box b' (R * a)).card ≤ R ^ d := by
  classical
  have hsub : (Finset.univ.filter fun b : Torus d n => Aligned a b ∧ b ∈ box b' (R * a)) ⊆
      (Fintype.piFinset fun _ : Fin d => Finset.range R).image
        (fun t : Fin d → ℕ => b' + natT (fun μ => a * t μ)) := by
    intro b hb
    obtain ⟨hal, w, hw, rfl⟩ := (Finset.mem_filter.1 hb).2
    rw [Finset.mem_image]
    refine ⟨fun μ => w μ / a, ?_, ?_⟩
    · rw [Fintype.mem_piFinset]
      intro μ
      rw [Finset.mem_range, Nat.div_lt_iff_lt_mul ha0]
      have := hw μ; linarith [mul_comm R a]
    · have hmod : ∀ μ, w μ % a = 0 := fun μ => by
        have := hal μ
        rwa [mod_of_aligned_add ha hb' μ] at this
      congr 2
      funext μ
      have := Nat.div_add_mod (w μ) a
      rw [hmod μ] at this
      omega
  calc _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Fintype.piFinset fun _ : Fin d => Finset.range R).card := Finset.card_image_le
    _ = R ^ d := by simp

variable (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (m₀ : ℕ)

open Classical in
/-- **(G1), cube count.**  For a multiscale polymer domain `Y`, the aligned (scale `j ≤ K`) points
of `Y ∩ Λ_K` number at most `L^{(K-j)d}` times the number of cells of `Y`. -/
theorem card_cubes_le_cells (hN : L ^ m₀ ∣ N₁) {j : ℕ} (hjK : j ≤ K)
    {Y : Set (CTorus d L N₁ m₁ K)} (hY : IsMultiDom G m₀ Y) (𝒬 : Finset (CTorus d L N₁ m₁ K))
    (hQ : ∀ q ∈ 𝒬, Aligned (cellSide L m₀ m₁ j) q ∧ q ∈ Y ∧ q ∈ (G.layer K : Set _)) (hK : 1 ≤ K) :
    (𝒬.card : ℝ) ≤ ((L ^ (K - j)) ^ d : ℕ) * (cellsOf G m₀ Y).card := by
  have hmaps : ∀ q ∈ 𝒬, cellOfSite G m₀ q ∈ cellsOf G m₀ Y :=
    fun q hq => (cellOfSite_mem G m₀ hN hY (hQ q hq).2.1).1
  have hfiber : ∀ v ∈ cellsOf G m₀ Y, (𝒬.filter fun q => cellOfSite G m₀ q = v).card ≤
      (L ^ (K - j)) ^ d := by
    intro v hv
    classical
    set a := cellSide L m₀ m₁ j with ha
    have ha0 : 0 < a := cellSide_pos m₀ m₁ j
    have hdvdN : a ∣ (N₁ * L ^ m₁) * L ^ K := cellSide_dvd (m₁ := m₁) (K := K) hN hjK
    by_cases hne : (𝒬.filter fun q => cellOfSite G m₀ q = v).Nonempty
    · obtain ⟨q₀, hq₀⟩ := hne
      obtain ⟨hq₀Q, hq₀v⟩ := Finset.mem_filter.1 hq₀
      have hlay : G.layerIndex q₀ = K := by
        have hq := (hQ q₀ hq₀Q).2.2
        have h1 : q₀ ∈ G.Ω 1 := G.layer_subset hK le_rfl hq
        exact G.layerIndex_eq hK le_rfl hq
      have hv1 : v.1 = K := by rw [← hq₀v]; simp [cellOfSite, hlay]
      have hside : cellSide L m₀ m₁ K = L ^ (K - j) * a := by
        simp only [cellSide, ha]
        rw [← pow_add]; congr 1; omega
      have hvbase : Aligned a v.2 := by
        rw [← hq₀v]
        refine aligned_of_dvd ?_ (aligned_cbase q₀)
        rw [hlay, ha]
        simp only [cellSide]
        exact pow_dvd_pow _ (by omega)
      refine le_trans (Finset.card_le_card ?_) (card_aligned_in_box (R := L ^ (K - j)) hdvdN ha0 hvbase)
      intro q hq
      obtain ⟨hqQ, hqv⟩ := Finset.mem_filter.1 hq
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, (hQ q hqQ).1, ?_⟩
      have hlayq : G.layerIndex q = K := G.layerIndex_eq hK le_rfl (hQ q hqQ).2.2
      have hbx := mem_box_cbase (a := cellSide L m₀ m₁ (G.layerIndex q)) (cellSide_pos m₀ m₁ _) q
      have e : cellOfSite G m₀ q = v := hqv
      rw [← e] at hv1 ⊢
      simp only [cellOfSite, hlayq] at hbx ⊢
      rw [← hside]
      exact hbx
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne]; simp
  have hcard := Finset.card_eq_sum_card_fiberwise (f := cellOfSite G m₀) (s := 𝒬)
    (t := cellsOf G m₀ Y) hmaps
  calc (𝒬.card : ℝ) = ((∑ v ∈ cellsOf G m₀ Y, (𝒬.filter fun q => cellOfSite G m₀ q = v).card : ℕ) : ℝ) := by
        rw [← hcard]
    _ ≤ ((∑ v ∈ cellsOf G m₀ Y, (L ^ (K - j)) ^ d : ℕ) : ℝ) := by
        exact_mod_cast Finset.sum_le_sum hfiber
    _ = _ := by simp [mul_comm]

end Count

end Balaban.Fluctuation
