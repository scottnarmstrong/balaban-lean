/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.XiD2
public import Balaban.Fluctuation.RenormExpBounds
public import Balaban.Localization.I5Inhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The domain predicates `XiCData`, `XiCOne`, `XiCOneReal` are inhabited

The class domain `Ξ^c_k(𝔹; 1, ε)` is non-empty for every `ε > 0`.  The datum is the constant unit
field `Ψ ≡ h ≡ e₀` with no complex displacement, which lies in `Ψ̃^c(𝔹; δ, δ)` for every `δ > 0`
(`exists_inPsiTildeC`); (D2) (`psiTildeC_subset_xiC`) then gives the member of `Ξ^c`.

* `exists_xiC`: for a generating set with `BgHyp`, `ν L^{2k} ≤ 1`, and every `ε > 0`, the existence of
  `(Ψ₀, h₀)` with `XiC G a ν k 1 ε Ψ₀ h₀ 0 0`;
* `exists_xiCData`, `exists_xiCOne`, `exists_xiCOneReal`: the three predicates;
* `xiCData_concrete`: the concrete instance (`d = L = 3`, `N₁ = 6`, `K = 2`, `N = 2`, `ν = 0`,
  `a = compWeight 3 1`, `G` the whole-lattice level-two set of `I5Inhabited`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The first unit vector of `ℝ^N`. -/
noncomputable def unitVec (hN : 0 < N) : Fin N → ℝ := fun i => if i = ⟨0, hN⟩ then 1 else 0

theorem sum_sq_unitVec (hN : 0 < N) : ∑ i, unitVec hN i ^ 2 = 1 := by
  simp [unitVec, Finset.sum_ite_eq']

theorem rn_unitVec (hN : 0 < N) : rn (unitVec hN) = 1 := by
  unfold rn; rw [sum_sq_unitVec]; simp

/-- **The constant unit datum lies in every complex data domain `Ψ̃^c(𝔹; δ, ε)`.** -/
theorem exists_inPsiTildeC (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) (ν : ℝ) {δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 < ε) :
    InPsiTildeC G ν δ ε (fun _ => unitVec hN) (unitVec hN) (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ)
      (0 : Torus d (N₀ * L ^ k) → Fin N → ℂ) where
  layerConst := fun _ _ _ _ _ _ _ => rfl
  r1 := fun x x' _ => by simpa [rn] using hδ
  r2 := fun x _ => by simpa [sum_sq_unitVec hN] using hδ
  r3 := fun x _ => by
    have h : ∑ i, unitVec hN i * unitVec hN i = 1 := by
      simpa [pow_two] using sum_sq_unitVec hN
    simp only [h, rn_unitVec, div_one, sub_self, abs_zero, mul_zero]
    positivity
  r4 := by
    simp only [sum_sq_unitVec hN, sub_self, abs_zero, mul_zero]
    positivity
  eps_pos := hε
  layerConst' := fun _ _ _ _ _ _ _ => rfl
  hLayerConst' := fun _ _ _ _ _ _ _ => rfl
  c1 := fun x x' _ => by simpa [vn] using hδ
  c2a := fun x _ => by simpa [vn] using add_pos hε hδ
  c2b := fun x _ => by simpa using hδ
  c3a := fun x _ => by simp only [Pi.zero_apply]; simpa [vn] using by positivity
  c3b := fun x _ => by simp only [Pi.zero_apply]; simpa using by positivity

/-- **`Ξ^c_k(𝔹; 1, ε)` is non-empty for every `ε > 0`.** -/
theorem exists_xiC {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν) (G : GeneratingSet d L N₀ k ϱ)
    (hN : 0 < N) (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    XiC G a ν k 1 ε (fun _ : Torus d (N₀ * L ^ k) => unitVec hN) (unitVec hN) 0 0 := by
  have hK := bgK1_pos d L N
  have hc0 := bgC0_pos d L N (by have := H.hd; omega)
  have hc1 := bgC1_pos' (d := d) (L := L) (N := N) (by have := H.hd; omega)
  set δ : ℝ := min (ε / (2 * bgK1 d L N + 2)) (min (bgC0 d L N) (bgC1 d L N)) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδc0 : δ ≤ bgC0 d L N := (min_le_right _ _).trans (min_le_left _ _)
  have hδc1 : δ ≤ bgC1 d L N := (min_le_right _ _).trans (min_le_right _ _)
  have hδε : δ ≤ ε / (2 * bgK1 d L N + 2) := min_le_left _ _
  have hden : 0 < 2 * bgK1 d L N + 2 := by positivity
  have hP := exists_inPsiTildeC (G := G) (N := N) hN ν hδ0 hδ0
  refine psiTildeC_subset_xiC (a := a) H hδ0 le_rfl hδc0 hδc1 ?_ hP (εb := ε) ?_
  · have h1 : ν * ((L : ℝ) ^ k) ^ 2 * δ ^ 2 ≤ 1 * δ ^ 2 :=
      mul_le_mul_of_nonneg_right hν (by positivity)
    linarith
  · rw [le_div_iff₀ hden] at hδε
    nlinarith

section Predicates

variable {a : ℕ → ℝ} {ν : ℝ}

/-- `XiCData` (`Ξ^c_K(𝔹; 1, ε)` as a predicate on data of `BgData`) is inhabited. -/
theorem exists_xiCData {N₁ m₁ K : ℕ} [NeZero N₁] (H : BgHyp d L K ϱ a ν)
    (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (hN : 0 < N) (hν : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1)
    {ε : ℝ} (hε : 0 < ε) : ∃ D : BgData G N, XiCData G a ν K 1 ε D := by
  have hX := exists_xiC H G hN hν hε
  exact ⟨complexData G (fun _ => unitVec hN) (unitVec hN) 0 0 (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => rfl), _, _, 0, 0, hX,
    complexData_realizes (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ => rfl)⟩

/-- `XiCOne` (the domain of Lemma 3.5) is inhabited. -/
theorem exists_xiCOne (H : BgHyp d L k ϱ a ν) (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N)
    (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : BgData G N, XiCOne G a ν ε D := by
  have hX := exists_xiC H G hN hν hε
  exact ⟨complexData G (fun _ => unitVec hN) (unitVec hN) 0 0 (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => rfl), _, _, 0, 0, hX,
    complexData_realizes (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ => rfl)⟩

/-- `XiCOneReal` (the fixed-`h` class domain of Lemma 3.5) is inhabited. -/
theorem exists_xiCOneReal (H : BgHyp d L k ϱ a ν) (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N)
    (hν : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ D : BgData G N, XiCOneReal G a ν ε D := by
  have hX := exists_xiC H G hN hν hε
  exact ⟨complexData G (fun _ => unitVec hN) (unitVec hN) 0 0 (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
    (fun _ _ _ _ _ _ _ => rfl), _, _, 0, hX,
    complexData_realizes (fun _ _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ _ _ => rfl)
      (fun _ _ _ _ _ _ _ => rfl)⟩

end Predicates

section Concrete

open Balaban.Localization.I5Inhabited

/-- **Concrete instance.**  `d = L = 3`, `N₁ = 6`, `K = 2`, `N = 2`, `ν = 0`, `a = compWeight 3 1`,
`G` the whole-lattice level-two generating set: the three domain predicates are inhabited for every
`ε > 0`. -/
theorem xiC_domains_concrete (m₁ : ℕ) (ϱ : ℝ) (hH : BgHyp 3 3 2 ϱ (compWeight 3 1) 0) {ε : ℝ}
    (hε : 0 < ε) :
    (∃ D : BgData (GP (m₁ := m₁) (ϱ := ϱ)) 2, XiCData (GP (m₁ := m₁) (ϱ := ϱ)) (compWeight 3 1) 0 2 1 ε D) ∧
    (∃ D : BgData (GP (m₁ := m₁) (ϱ := ϱ)) 2, XiCOne (GP (m₁ := m₁) (ϱ := ϱ)) (compWeight 3 1) 0 ε D) ∧
    (∃ D : BgData (GP (m₁ := m₁) (ϱ := ϱ)) 2,
      XiCOneReal (GP (m₁ := m₁) (ϱ := ϱ)) (compWeight 3 1) 0 ε D) :=
  ⟨exists_xiCData hH _ (by norm_num) (by simp) hε, exists_xiCOne hH _ (by norm_num) (by simp) hε,
    exists_xiCOneReal hH _ (by norm_num) (by simp) hε⟩

end Concrete

end Balaban.Inhabited
