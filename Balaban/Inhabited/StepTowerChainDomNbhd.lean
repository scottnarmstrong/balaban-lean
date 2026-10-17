/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Birth
public import Balaban.SmallField.Def6BridgeDomain
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A neighbourhood of the constant field in the class domains

The constant field `e_{i₀}` with zero source is the centre of the chart (P1 p. 123 (3.14)).  For
the class domains `xiFieldDom`, `pinFieldDom` (pinned at `e_{i₀}`) and `birthXiDom`, a field
constant on the `j`-blocks and within a radius `ρ` of `e_{i₀}` lies in the level-`j` domain at the
data `(Ψ, constFld e_{i₀})`.  The radius depends on the level `j`, the radius of the chart and the
standing constants of the background theory, and not on the generating set.

* `exists_xiDom_ball`: the domain `Ξ^c_j(G; a, ν, 1, ε)`;
* `exists_pin_ball`: the pinned domain `Pin e_{i₀} r_h` (`h'' = 0`);
* `exists_birthXiDom_ball`: the birth-mass domain.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ} {a : ℕ → ℝ} {ν : ℝ}

/-- A radius `ρ > 0` for which the ball of radius `ρ` around `e_{i₀}` lies in the level-`j`
domain (the constants `δ`, `ρ` of `xiDom_of_close`), independent of the generating set. -/
theorem exists_close_radius (hd : 0 < d) (i₀ : Fin N) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ ρ : ℝ, 0 < δ ∧ δ ≤ bgC0 d L N ∧ δ ≤ bgC1 d L N ∧ 0 < ρ ∧ (N : ℝ) * ρ < δ ^ 2 ∧
      (2 * bgK1 d L N + 2) * δ ≤ ε := by
  have hK := bgK1_pos d L N
  have h0 := bgC0_pos d L N hd
  have h1 := bgC1_pos' (L := L) (N := N) hd
  have hN : (0 : ℝ) < N := by exact_mod_cast Fin.pos i₀
  have hq : 0 < ε / (2 * bgK1 d L N + 2) := by positivity
  refine ⟨min (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2)),
    (min (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2))) ^ 2 / (2 * N),
    lt_min (lt_min h0 h1) hq, (min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans (min_le_right _ _), by positivity, ?_, ?_⟩
  · have hδ : 0 < min (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2)) :=
      lt_min (lt_min h0 h1) hq
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    nlinarith [pow_pos hδ 2]
  · have := min_le_right (min (bgC0 d L N) (bgC1 d L N)) (ε / (2 * bgK1 d L N + 2))
    calc _ ≤ (2 * bgK1 d L N + 2) * (ε / (2 * bgK1 d L N + 2)) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = ε := by field_simp

/-- **The real centre and zero displacement** (the chart datum of the constant field): a field
`Ψ`, constant on the `j`-blocks and within `ρ` of `e_{i₀}`, gives a member of
`Ξ^c_j(G; a, ν, 1, ε)` with the unit real witness `h₀ = e_{i₀}` and the displacement `h'' = 0`. -/
theorem xiC_of_close_const {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (H : BgHyp d L K ϱ a ν) {j : ℕ} (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ K)
    {δ ρ ε : ℝ} (i₀ : Fin N) (hδ0 : 0 < δ) (hδc0 : δ ≤ bgC0 d L N) (hδc1 : δ ≤ bgC1 d L N)
    (hρ0 : 0 < ρ) (hρ : (N : ℝ) * ρ < δ ^ 2) (hε : (2 * bgK1 d L N + 2) * δ ≤ ε)
    (Ψ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hΨ : ∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ)
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j x' →
      Ψ x = Ψ x') :
    XiC G a ν j 1 ε (fun _ => Pi.single i₀ 1) (Pi.single i₀ 1)
      (fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i) (fun _ _ => 0) := by
  have hP := inPsiTildeC_of_close (G := G) hΩ hjk H.mass i₀ hδ0 (hδc0.trans (bgC0_le d L N)) hρ0
    hρ Ψ (Pi.single i₀ 1) hΨ hΨb (fun i => by simp [hρ0.le])
  have hK := bgK1_pos d L N
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hδ0 le_rfl hδc0 hδc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg δ]) hP (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) (by simp [Pi.single_apply]) hX
  have h0 : (fun (_ : CTorus d L N₁ m₁ K) i => (Pi.single i₀ 1 : Fin N → ℂ) i -
      (Pi.single i₀ 1 : Fin N → ℂ) i) = fun _ _ => 0 := by
    funext _ i; exact sub_self _
  rw [h0] at hX'
  exact hX'

/-- **A neighbourhood of the constant field in `Ξ^c_j`**: for a level `j ≤ K`, `ε > 0` and the
standing hypotheses of the background theory, there is `ρ > 0` such that for every generating set
with the layers above `j` empty, every field `Ψ` constant on the `j`-blocks with
`‖Ψ - e_{i₀}‖ ≤ ρ` and the source `h = const e_{i₀}` lies in `XiDom G a ν j ε`. -/
theorem exists_xiDom_ball (H : BgHyp d L K ϱ a ν) (i₀ : Fin N) {j : ℕ} (hjk : j ≤ K) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ K N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j x' → Ψ x = Ψ x') →
      XiDom G a ν j ε Ψ (constFld (Pi.single i₀ 1)) := by
  obtain ⟨δ, ρ, hδ0, hδ0', hδ1, hρ0, hρ, hδε⟩ := exists_close_radius (d := d) (L := L) (N := N)
    (by have := H.hd; omega) i₀ hε
  refine ⟨ρ, hρ0, fun G hΩ Ψ hΨ hΨb => ?_⟩
  exact xiDom_of_close H hΩ hjk i₀ hδ0 hδ0' hδ1 hρ0 hρ hδε Ψ (Pi.single i₀ 1) hΨ hΨb
    (fun i => by simp [hρ0.le])

/-- **A neighbourhood of the constant field in the pinned domain** (pinned at `e_{i₀}`, any
`r_h > 0`): the displacement of the source is `h'' = 0`. -/
theorem exists_pin_ball (H : BgHyp d L K ϱ a ν) (i₀ : Fin N) {j : ℕ} (hjk : j ≤ K) {ε rH : ℝ}
    (hε : 0 < ε) (hrH : 0 < rH) :
    ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ K N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j x' → Ψ x = Ψ x') →
      Pin (Pi.single i₀ 1) rH G a ν j ε Ψ (constFld (Pi.single i₀ 1)) := by
  obtain ⟨δ, ρ, hδ0, hδ0', hδ1, hρ0, hρ, hδε⟩ := exists_close_radius (d := d) (L := L) (N := N)
    (by have := H.hd; omega) i₀ hε
  refine ⟨ρ, hρ0, fun G hΩ Ψ hΨ hΨb => ?_⟩
  have hX := xiC_of_close_const H hΩ hjk i₀ hδ0 hδ0' hδ1 hρ0 hρ hδε Ψ hΨ hΨb
  have hz : vn (fun _ : Fin N => (0 : ℂ)) = 0 := by unfold vn; exact norm_eq_zero.2 rfl
  refine ⟨by simp [Pi.single_apply], fun _ i => (Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i,
    fun x i => Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i, fun _ _ => 0, fun x i => ?_,
    fun x i => ?_, fun x => ?_, hX⟩
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    rw [hu]; ring
  · have hu : (((Pi.single i₀ (1 : ℝ) : Fin N → ℝ) i : ℝ) : ℂ) = (Pi.single i₀ 1 : Fin N → ℂ) i := by
      by_cases h : i = i₀ <;> simp [h]
    simp only [constFld, hu]; ring
  · rw [hz]; exact hrH

/-- **A neighbourhood of the constant field in the birth-mass domain** `birthXiDom`: the level-`j`
domain with the background mass fixed at the birth scale `j`. -/
theorem exists_birthXiDom_ball (P : Consts) (Rg : Regime L) (a₀ : ℕ → ℝ) (i₀ : Fin N) {j : ℕ}
    (hjk : j ≤ K)
    (H : BgHyp d L K ϱ (aIdeal L K (a₀ K)) (physMass L j (Rg.ν j)))
    (hε : 0 < P.eps d L j) :
    ∃ ρ > 0, ∀ G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ, (∀ i, j < i → G.Ω i = ∅) →
      ∀ Ψ : Fld d L N₁ m₁ K N, (∀ x i, ‖Ψ x i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ ρ) →
      (∀ x x', jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j x' → Ψ x = Ψ x') →
      (birthXiDom (d := d) (m₁ := m₁) (k := K) (N := N) (ϱ := ϱ) P Rg a₀ N₁).dom j G Ψ
        (constFld (Pi.single i₀ 1)) :=
  exists_xiDom_ball H i₀ hjk hε

end Balaban.Inhabited
