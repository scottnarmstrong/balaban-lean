/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.I5Glue
public import Balaban.Localization.DecoupledCompose
public import Balaban.Localization.DecoupledFieldX0
public import Balaban.Localization.I5Xi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The first stage of Lemma DL: closeness of the composed datum on `X₀`

For the composed datum `ψ(𝔹_k(X), 𝔹_{k+1}; s)` of the decoupled background field (I-4b (v)) the
difference with its value at `s ≡ 1` is bounded on the data sites of `𝔹_k(X)` by
`N · 10 e^{2dγ_w} closeConst · e^{-γ_w r₁ M₁}`, `r₁ = (r₀ - 4dL³)/L` (`composed_close_X0`): the
scaled distance from `X₀` to the set `𝒲` of the interaction cubes meeting a parameter cube is large
(`siteSetDist_X0`, from the physical neighbourhood of `X₀` lying in `X₁`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section Close

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'}
variable {a : ℕ → ℝ} {ν : ℝ}

/-- The bound of the difference of the composed data at `s` and at `s ≡ 1` on `X₀`. -/
noncomputable def composedCloseBound (d L N : ℕ) [NeZero L] (m₁ : ℕ) (BG κ δ r₀ : ℝ) : ℝ :=
  10 * Real.exp (gammaW d * (2 * d)) * closeConst d L N BG κ (lemma53Const d L * δ) *
    Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L)))

theorem composedCloseBound_nonneg {BG κ δ r₀ : ℝ} (hBG : 0 ≤ BG) (hδ : 0 ≤ δ) (hd : 0 < d) :
    0 ≤ composedCloseBound d L N m₁ BG κ δ r₀ := by
  have hcc := closeConst_nonneg (d := d) (L := L) (κ := κ) (N := N) hBG
    (mul_nonneg (lemma53Const_pos d L).le hδ) hd
  unfold composedCloseBound; positivity

/-- **From the decay at the scaled distance to the bound on `X₀`**: a quantity bounded by
`10 e^{2dγ_w} closeConst · e^{-γ_w D}` with `D ≥ T = ((r₀ - 4dL³)/L) M₁` (`4dL³ ≤ r₀`) is at most
`composedCloseBound`.  The common last step of `composed_close_X0` (one generating set) and
`composed_close_X0_sup` (a sup-separated cover). -/
theorem le_composedCloseBound_of_dist {BG κ δ r₀ : ℝ} (hBG : 0 ≤ BG) (hδ : 0 ≤ δ) (hd : 0 < d)
    (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀) {D : ENNReal}
    (hD : ENNReal.ofReal ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L) ≤ D) {u : ℝ}
    (hu : u ≤ 10 * Real.exp (gammaW d * (2 * d)) *
      closeConst d L N BG κ (lemma53Const d L * δ) * decay (gammaW d) D) :
    u ≤ composedCloseBound d L N m₁ BG κ δ r₀ := by
  have hγ0 : 0 ≤ gammaW d := gammaW_nonneg hd
  have hL1 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hT0 : 0 ≤ (r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L := by
    have : 0 ≤ r₀ - 4 * d * (L : ℝ) ^ 3 := by linarith
    positivity
  have hdec : decay (gammaW d) D ≤
      Real.exp (-(gammaW d * ((r₀ - 4 * d * (L : ℝ) ^ 3) * (L : ℝ) ^ m₁ / L))) := by
    have h' := decay_anti_dist hγ0 hD
    rw [decay_of_ne_top ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hT0] at h'
    exact h'
  refine hu.trans ?_
  unfold composedCloseBound
  have hcc := closeConst_nonneg (d := d) (L := L) (κ := κ) (N := N) hBG
    (mul_nonneg (lemma53Const_pos d L).le hδ) hd
  exact mul_le_mul_of_nonneg_left hdec (by positivity)

/-- **Closeness of the composed datum on `X₀`** (I-4b (v) with the geometry of `X₀`). -/
theorem composed_close_X0 {c BG : ℝ} (hS : DecSpecs d L c BG) (S : DGSetting G a ν)
    (HB : BgHyp d L K ϱ a ν) (hP : Precedes G' G) {κ : ℝ} (hκ : 0 ≤ κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {s : DecParams G}
    (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) {X₀ X₁ : Finset (CTorus d L N₁ m₁ K)} {r₀ : ℝ}
    (hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ K) (hP : P ∈ cubeIdx G), P ∉ parCubes G X₁ →
      s ⟨P, hP⟩ = 1)
    (hN : ∀ x ∈ X₀, x ∈ G.Ω 1 → ∀ y : CTorus d L N₁ m₁ K,
      Green.torusDist d ((N₁ * L ^ m₁) * L ^ K) x y < r₀ * (L : ℝ) ^ m₁ * G.spacing x → y ∈ X₁)
    (hr : r₀ * (L : ℝ) ^ m₁ ≤ ϱ - 1) (hr₀ : 4 * d * (L : ℝ) ^ 3 ≤ r₀)
    {δ ε : ℝ} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ c7 d L N BG κ)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2) {D : BgData G N} (hD : InDomainC G ν δ ε D)
    {φ φ1 : G.Ω 1 × Fin N → ℂ} {α α1 : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν (rho4 d L N BG κ) s D φ α)
    (h1 : IsDecBg G a ν (rho4 d L N BG κ) (fun _ => 1) D φ1 α1)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ X₀) (hxΩ : x ∈ G.Ω 1) (i : Fin N) :
    ‖composeField G' G a φ D.Ψ x i - composeField G' G a φ1 D.Ψ x i‖ ≤
      composedCloseBound d L N m₁ BG κ δ r₀ :=
  le_composedCloseBound_of_dist hS.fam.2.1 hδ0.le (by have := HB.hd; omega) hr₀
    (siteSetDist_X0 S hN hr hx hxΩ)
    (i4b_compose_close hS S HB hP hκ hM hs (hW_of_par hs1) hδ0 hδε hε hδ hνε hD h h1 x i)

end Close

end Balaban.Localization
