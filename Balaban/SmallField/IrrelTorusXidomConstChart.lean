/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBoundTube

/-!
# The constant configuration lies in the class chart (M3)

The data hypothesis of the non-special label estimate asks the configuration and its constant
version `(ψ(0), b)` in the class chart of the label.  For the constant configuration this follows
from the bounds the estimate assumes anyway: the real-frame centre `|ψ(0) - e_{i₀}| ≤ q ≤ r`, the
source bounds `|b - ν e_{i₀}| ≤ r`, `|b_{i₀} - ν| ≤ r²` and the radius condition
`AnisoRadiusOK`, through the anisotropic domain inclusion `xiDom_of_fieldM` at the mass of the
class (`constConfig_mem_chartDom`).
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- **The constant configuration lies in the class chart of the label**: with the real-frame
centre `|ψ(0) - e_{i₀}| ≤ q ≤ r`, the source bounds `|b_i - ν δ_{i i₀}| ≤ r`, `|b_{i₀} - ν| ≤ r²`,
the radius condition `AnisoRadiusOK` and `μ L^{2j} ≤ ν`, the fields placed at `y` of the constant
configuration `(ψ(0), b)` lie in `Ξ^c_j(G; 1, ε_j)` at the mass `μ`, for a generating set `G` with
no layer above `j`. -/
theorem constConfig_mem_chartDom {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} (hBg : BgHyp d L k ϱ a μ)
    {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ} (hΩ : ∀ i, j < i → G.Ω i = ∅)
    (hjk : j ≤ k) (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) {i₀ : Fin N} {r q : ℝ}
    (hrad : AnisoRadiusOK d L N P j r) (hq : q ≤ r) {y : CTorus d L N₁ m₁ k}
    (hy : Aligned (L ^ j) y) {S : Finset (Site d)} {X : Set (CTorus d L N₁ m₁ k)}
    {ψ0 b : Spin N} (hcentre : ∀ i, ‖ψ0 i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖b i - (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖b i₀ - (ν : ℂ)‖ ≤ r ^ 2) :
    ((fun _ : Site d => ψ0), b) ∈ {p : (Site d → Spin N) × Spin N | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S p.1 p.2) z) ∧
        XiDom G a μ j (P.eps d L j) Ψ' h'} := by
  obtain ⟨hr0, hr1, δ, hδ0, hδc0, hδc1, hε, hrδ⟩ := hrad
  have h4 := (aniK_old i₀ hr0 hrδ).2
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast Fin.pos i₀
  have h2 : 2 * (N : ℝ) * r ≤ δ := by nlinarith
  have hrδ' : r < δ := by nlinarith
  have hrl : r ^ 2 < δ ^ 2 := by nlinarith
  refine ⟨fun z => fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
      (pack S (fun _ : Site d => ψ0) b) (z - y),
    hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S (fun _ : Site d => ψ0) b),
    fun _ _ => ⟨rfl, rfl⟩, ?_⟩
  have hΨ : ∀ x i, ‖fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
      (pack S (fun _ : Site d => ψ0) b) (x - y) i - (Pi.single i₀ 1 : Fin N → ℂ) i‖ ≤ r := by
    intro x i
    unfold fieldOf
    split_ifs
    · simpa only [pack, Sum.elim_inl] using (hcentre i).trans hq
    · simpa using hr0.le
  have hX := xiDom_of_fieldM (ρs := r) (ρh := r) (ρl := r ^ 2) hBg hΩ hjk hν hμν i₀ hδ0 hδc0
    hδc1 hr0.le hr0.le h4 h2 hrl hε _ b hΨ (fun _ _ h => shiftField_block hjk hy _ h) hb hbl
  have hh : hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S (pack S (fun _ : Site d => ψ0) b) =
      fun _ i => b i / (ν : ℂ) := by
    funext z i
    simp only [hOf, pack, Sum.elim_inr]
  rw [hh]
  exact hX

end Balaban.SmallField.Def6v2
