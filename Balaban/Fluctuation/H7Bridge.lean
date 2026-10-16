/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.CubeActionBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Torus-size bridge for the undecoupled Step 3 (FLUCTUATION.md §4.2, Step 1)

The cube action (`cubeActionC`, `cubeDiff_step3_quadratic`) is stated for the localization torus
`N₁ * L ^ m₁ * L ^ K` (`CTorus`), whereas the H7 generating sets `genCube` live on the torus
`M1 * N₁ * L ^ q` of `Characteristic/*`.  W105 found this size mismatch.  This file removes it:

* `shadowN`: the `Ω₁`-shadow of a set of sites on a torus of arbitrary size `N₀ * L ^ K`;
* `cubeDiff_step3_quadratic_gen`: `cubeDiff_step3_quadratic` for a generating set on any torus
  `N₀ * L ^ K` with `N₀ = N₁ * L ^ m₁` (the proof is `subst`; take `N₁ = N₀`, `m₁ = 0`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

open Classical in
/-- The `Ω₁`-shadow of a set `W` of sites on a torus of arbitrary size: the sites of `Ω₁` in `W` or
adjacent to a site of `W` (the same set as `shadow`, which is stated for `N₁ * L ^ m₁ * L ^ K`). -/
noncomputable def shadowN (G : GeneratingSet d L N₀ K ϱ) (W : Finset (Torus d (N₀ * L ^ K))) :
    Finset (Torus d (N₀ * L ^ K)) :=
  Finset.univ.filter fun x => x ∈ G.Ω 1 ∧ (x ∈ W ∨ ∃ y ∈ W, Adj x y)

/-- **`cubeDiff_step3_quadratic` on a torus of arbitrary size** `N₀ * L ^ K`, `N₀ = N₁ * L ^ m₁`:
the cube action difference of the two backgrounds is at most `C_F β |Q| r² e^{-γ_w Dist}` when the
data change is supported in `W`, bounded by `δ₁ ≤ C_δ r`, and the regularity inequalities hold on
`R ⊇ Q`. -/
theorem cubeDiff_step3_quadratic_gen (hd : 3 ≤ d) (hL : 3 ≤ L) {N : ℕ} {Cδ : ℝ} (hCδ : 0 ≤ Cδ) :
    ∃ CF δw : ℝ, 0 < CF ∧ 0 < δw ∧
      ∀ {N₀ K N₁ m₁ : ℕ} [NeZero N₀] (_hN : N₀ = N₁ * L ^ m₁) {ϱ : ℝ}
        {G : GeneratingSet d L N₀ K ϱ}
        {a : ℕ → ℝ} {ν : ℝ}, BgHyp d L K ϱ a ν → 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1) →
        ∀ {D Du : BgData G N} {δ ε δ' ε' : ℝ},
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G ν δ ε D →
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ K) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G ν δ' ε' Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ {δΨ : Torus d (N₀ * L ^ K) → Fin N → ℂ} (W : Finset (Torus d (N₀ * L ^ K))),
        (∀ y ∉ W, δΨ y = 0) →
        (∀ x i, Du.Ψ x i = D.Ψ x i + δΨ x i) → (∀ x i, Du.h x i = D.h x i) →
        ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G, vn (δΨ x) ≤ δ₁) →
        ∀ (Q R : Finset (Torus d (N₀ * L ^ K))) {r Dist : ℝ}, 0 ≤ r → 0 ≤ Dist → δ₁ ≤ Cδ * r →
        Q ⊆ R → (∀ x ∈ Q, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R) →
        (∀ x ∈ Q, x ∈ G.Ω 1 → ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ R) →
        RegIneq G a ν D r R R →
        (∀ y ∈ R, y ∈ G.Ω 1 → ∀ w ∈ shadowN G W, ENNReal.ofReal Dist ≤ G.pathDist y w) →
        ∀ β : ℝ, 0 ≤ β →
        ‖(β : ℂ) * (cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) Du) -
            cubeActionC G a ν Q D (bgFieldC G a ν (bgC0 d L N) D))‖ ≤
          CF * β * Q.card * r ^ 2 * Real.exp (-(gammaW d * Dist)) := by
  obtain ⟨CF, δw, hCF, hδw, hstep⟩ := cubeDiff_step3_quadratic (N := N) hd hL hCδ
  refine ⟨CF, δw, hCF, hδw, ?_⟩
  intro N₀ K N₁ m₁ _ hN ϱ G a ν H hsep D Du δ ε δ' ε' hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε'
    hDu hK1 hKw δΨ W hsupp hΨ hh δ₁ hδ₁0 hδ₁s hδ₁w hdΨ Q R r Dist hr hDist hδr hQR hQR1 hQblk hreg
    hdist β hβ
  subst hN
  have : NeZero N₁ := ⟨by rintro rfl; exact absurd (by simp) (NeZero.ne (0 * L ^ m₁))⟩
  have hOp : Dec2.OpSetting G a ν :=
    ⟨⟨H.hd, H.hL, H.mass, H.weights, hsep⟩, H.massLe⟩
  refine hstep H hOp hδ0 hδε hε hδ1 hνε hD hδ0' hδε' hε' hδ1' hνε' hDu hK1 hKw W hsupp hΨ hh
    hδ₁0 hδ₁s hδ₁w hdΨ Q R hr hDist hδr hQR hQR1 hQblk hreg ?_ β hβ
  intro y hy hyΩ
  refine le_iInf₂ fun w hw => hdist y hy hyΩ w ?_
  exact hw

end Balaban.Fluctuation
