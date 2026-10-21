/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeDomain
public import Balaban.SmallField.Def6Terms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The class chart `Ξ^c_j` from bounds at every site

A6-3 (a), the birth-domain transport (item 1): a real field that is constant on the `j`-blocks and
satisfies the bounds (R1), (R2), (R3) of the data domain `Ψ̃` at every site and every pair of
neighbouring sites lies in the data domain `Ψ̃(𝔹; η)` of every generating set whose layers above
`j` are empty (`inPsiTilde_of_allSites`), and, when `(2 K₁ + 2) η ≤ ε`, in the analyticity domain
`Ξ^c_j(𝔹; 1, ε)` (`xiDom_of_allSites`). This is the general form of `xiDom_const` (the case of the
constant field).
-/

@[expose] public section

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6

namespace Balaban.RootFSpine

section Bounds

variable {d L N₀ q N : ℕ}

/-- **The bounds of the data domain at every site**: a real field `f` on the torus of side
`N₀ L^q`, constant on the `j`-blocks, with `rn (f x - f x') < η` for neighbours,
`|f x · f x - 1| < η` and `m L^{2j} |1 - f x · h / rn (f x)| < η²` at every site. -/
structure AllSitesBounds (j : ℕ) (m η : ℝ) (f : Torus d (N₀ * L ^ q) → Fin N → ℝ)
    (h₀ : Fin N → ℝ) : Prop where
  block : ∀ x x', jBlock d L N₀ q j x = jBlock d L N₀ q j x' → f x = f x'
  adj : ∀ x x', Adj x x' → rn (fun i => f x i - f x' i) < η
  sphere : ∀ x, |∑ i, f x i ^ 2 - 1| < η
  dir : ∀ x, m * ((L : ℝ) ^ j) ^ 2 * |1 - (∑ i, f x i * h₀ i) / rn (f x)| < η ^ 2

end Bounds

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ} {j : ℕ}

/-- A site of `Ω₁` of a generating set whose layers above `j` are empty has layer index `≤ j`. -/
theorem layerIndex_le_of_empty (hΩ : ∀ i, j < i → G.Ω i = ∅)
    {x : CTorus d L N₁ m₁ k} (hx : x ∈ G.Ω 1) : G.layerIndex x ≤ j := by
  obtain ⟨-, -, hxl⟩ := G.layerIndex_spec hx
  by_contra h
  have := hΩ (G.layerIndex x) (by omega)
  have h2 := (G.mem_layer.1 hxl).1
  rw [this] at h2
  simp at h2

/-- **The data domain from bounds at every site**: a real field `f` constant on the `j`-blocks with
`rn (f x - f x') < η` for neighbours, `|f x · f x - 1| < η` and
`ν L^{2j} |1 - f x · h / rn (f x)| < η²` at every site, and a unit vector `h`, lies in
`Ψ̃(𝔹; η)` for every generating set `𝔹` with empty layers above `j` (and `ν ≥ 0`). -/
theorem inPsiTilde_of_allSites (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {ν η : ℝ}
    (hν : 0 ≤ ν) (hη : 0 < η) (f : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ)
    (hh₀ : ∑ i, h₀ i ^ 2 = 1) (hA : AllSitesBounds (N₀ := N₁ * L ^ m₁) (q := k) j ν η f h₀) :
    InPsiTilde G ν η f h₀ := by
  obtain ⟨hb, h1, h2, h3⟩ := hA
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLC : IsLayerConstant G f := isLayerConstant_of_jBlock hjk hΩ hb
  have hsame : ∀ x y, y ∈ blockSet G x → f y = f x := by
    intro x y hy
    unfold blockSet at hy
    by_cases hx : x ∈ G.Ω 1
    · simp only [hx, ↓reduceIte] at hy
      obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
      exact hLC _ hn1 hnk x hxl y hy
    · simp only [hx, ↓reduceIte, Finset.mem_singleton] at hy
      rw [hy]
  refine ⟨hLC, fun x x' hp => ?_, fun x _ => h2 x, fun x hx => ?_, ?_⟩
  · obtain ⟨-, -, -, y, hy, y', hy', hadj⟩ := hp
    rw [← hsame x y hy, ← hsame x' y' hy']
    exact h1 y y' hadj
  · refine lt_of_le_of_lt ?_ (h3 x)
    have hl : G.layerIndex x ≤ j := by
      by_cases hx1 : x ∈ G.Ω 1
      · exact layerIndex_le_of_empty hΩ hx1
      · rw [layerIndex_of_not_mem G hx1]; exact Nat.zero_le _
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hl) 2) hν
  · simp [hh₀]
    positivity

/-- A real datum in the data domain, with no complex displacement, is in the complex data domain
`Ψ̃^c(𝔹; δ, δ)`. -/
theorem inPsiTildeC_of_inPsiTilde {ν δ : ℝ} (hδ : 0 < δ) {f : CTorus d L N₁ m₁ k → Fin N → ℝ}
    {h₀ : Fin N → ℝ} (hP : InPsiTilde G ν δ f h₀) :
    InPsiTildeC G ν δ δ f h₀ (fun _ _ => 0) (fun _ _ => 0) := by
  have hz : vn (0 : Fin N → ℂ) = 0 := vn_zero
  have hδ2 : 0 < δ ^ 2 := by positivity
  have hconst : ∀ {β : Type} (c : β), IsLayerConstant G (fun _ : CTorus d L N₁ m₁ k => c) :=
    fun c _ _ _ _ _ _ _ => rfl
  refine
    { toInPsiTilde := hP
      eps_pos := hδ
      layerConst' := fun _ _ _ _ _ _ _ => rfl
      hLayerConst' := fun _ _ _ _ _ _ _ => rfl
      c1 := fun x x' _ => ?_
      c2a := fun x _ => ?_
      c2b := fun x _ => ?_
      c3a := fun x hx => ?_
      c3b := fun x hx => ?_ }
  · show vn ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) < δ
    have : ((fun _ => (0 : ℂ)) - fun _ => (0 : ℂ)) = (0 : Fin N → ℂ) := by funext i; simp
    rw [this, hz]; exact hδ
  · show vn (fun _ => (0 : ℂ)) < δ + δ
    have : (fun _ : Fin N => (0 : ℂ)) = (0 : Fin N → ℂ) := rfl
    rw [this, hz]; linarith
  · simp
    exact hδ
  · show _ * vn (fun _ => (0 : ℂ)) < δ ^ 2 / δ
    have : (fun _ : Fin N => (0 : ℂ)) = (0 : Fin N → ℂ) := rfl
    rw [this, hz, mul_zero]
    positivity
  · simp
    exact hδ2

/-- **The analyticity domain `Ξ^c_j(𝔹; 1, ε)` from bounds at every site**: under the standing
hypotheses `BgHyp` of the background theory, a real field as in `inPsiTilde_of_allSites` with
`0 < η ≤ min (c₀, c₁)` and `(2 K₁ + 2) η ≤ ε` lies in `XiDom` with the constant field `h`. -/
theorem xiDom_of_allSites {a : ℕ → ℝ} {ν : ℝ} (H : BgHyp d L k ϱ a ν)
    (hΩ : ∀ i, j < i → G.Ω i = ∅) (hjk : j ≤ k) {η ε : ℝ} (hη : 0 < η)
    (hηc0 : η ≤ bgC0 d L N) (hηc1 : η ≤ bgC1 d L N) (hε : (2 * bgK1 d L N + 2) * η ≤ ε)
    (f : CTorus d L N₁ m₁ k → Fin N → ℝ) (h₀ : Fin N → ℝ) (hh₀ : ∑ i, h₀ i ^ 2 = 1)
    (hA : AllSitesBounds (N₀ := N₁ * L ^ m₁) (q := k) j ν η f h₀) :
    XiDom G a ν j ε (fun x i => (f x i : ℂ)) (fun _ i => (h₀ i : ℂ)) := by
  have hP := inPsiTilde_of_allSites (G := G) hΩ hjk H.mass hη f h₀ hh₀ hA
  have hPC := inPsiTildeC_of_inPsiTilde hη hP
  have hK := bgK1_pos d L N
  have hX := psiTildeC_subset_xiC (G := G) (a := a) H hη le_rfl hηc0 hηc1
    (by
      have := H.massLe
      nlinarith [sq_nonneg η]) hPC (εb := ε) (by nlinarith)
  have hX' := xiC_level_irrel (n' := j) hh₀ hX
  exact ⟨f, h₀, fun _ _ => 0, fun _ _ => 0, fun x i => by simp, fun x i => by simp, hX'⟩

end Balaban.RootFSpine
