/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.NewLevelHatTop
public import Balaban.Fluctuation.OldTermComposedChart

/-!
# The scale gap of the composition pair of a label (M4)

`LabelGap Gk Gj j`: the data sites of the term generator `Gj` lie in the top layer `k` of the
level-`k` local set `Gk` (on the torus of level `k + 1`), the layers of `Gj` are at most `j`, the
scale gap `ℓ_{Gj} ≤ θ ℓ_{Gk}` with `θ = L^j / L^k`, the collar condition `1 ≤ θ ℓ_{Gk}` on the
collar of `Gj`, and `L^j ≤ θ L^k`, `0 < θ ≤ 1`: the hypotheses `hnj`, `gap`, `hcol`, `hjθ`, `hθ0`,
`hθ1` of `HypSle` for `G = Gj`, `G' = Gk`, so `σ = C₀ L^{j-k}` at the composed data of the label.
`labelGap_of_hat` gives it for the sets of the settings of ruling R13 (`hat_gap`).
`composedChartGap Gj …`: the composed chart of `Gj` whose source satisfies the scale gap (the data
the step reads, at which `HypSle` applies).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Fluctuation Balaban.Localization Balaban.Multiscale Balaban.Background
  Balaban.SmallField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ₁ ϱ₂ : ℝ}

/-- **The scale gap of the composition pair of a label** (the hypotheses of `HypSle` with
`θ = L^j / L^k`, and the top layer of `Gk` on the data sites of `Gj`). -/
def LabelGap (Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁)
    (Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂) (j : ℕ) : Prop :=
  (∀ z ∈ dataSites Gj, z ∈ Gk.Ω k ∧ Gk.spacing z = (L : ℝ) ^ k) ∧
    (∀ x ∈ Gj.Ω 1, Gj.layerIndex x ≤ j) ∧
    ScaleGap Gj Gk ((L : ℝ) ^ j / (L : ℝ) ^ k) ∧
    (∀ z ∈ collar Gj, z ∈ Gk.Ω 1 ∧ 1 ≤ ((L : ℝ) ^ j / (L : ℝ) ^ k) * Gk.spacing z) ∧
    (L : ℝ) ^ j ≤ ((L : ℝ) ^ j / (L : ℝ) ^ k) * (L : ℝ) ^ k ∧
    0 < ((L : ℝ) ^ j / (L : ℝ) ^ k) ∧ ((L : ℝ) ^ j / (L : ℝ) ^ k) ≤ 1

/-- **The scale gap for the settings of ruling R13** (`hat_gap`): `Gj = 𝔹_j(X)` and
`Gk = 𝔹_k(castNbhd Y)` (cast) with `X ⊆ Y`. -/
theorem labelGap_of_hat {N₁' m₁' : ℕ} [NeZero N₁'] (hc : N₁' * L ^ m₁' = N₁ * L ^ m₁)
    (hL : 3 ≤ L) (hk1 : 1 ≤ k) {j : ℕ} (hjk : j ≤ k) {X Y : Set (CTorus d L N₁' m₁' (k + 1))}
    (hXY : X ⊆ Y) {hs₁ : ϱ₁ ≤ minSep L (L ^ m₁')} {hs₂ : ϱ₂ ≤ minSep L (L ^ m₁')}
    {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
    (hGj : Gj = castG hc (localB j (Nat.le_succ_of_le hjk) X hs₂))
    (hGk : Gk = castG hc (localB k (Nat.le_succ k) (castNbhd (N₁' := N₁') (m₁' := m₁') Y) hs₁)) :
    LabelGap Gk Gj j :=
  hat_gap hc hL hk1 hjk hXY hGj hGk

/-- **The composed chart with the scale gap of the source**: `composedChart` of `Gj` restricted to
the sources `G` with `LabelGap G Gj j` (the data composed into the class generating set of a label
from the chart of its level-`k` set, at which the sharp composition estimate `HypSle` applies with
`θ = L^{j-k}`). -/
def composedChartGap {N : ℕ} (Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂) (a : ℕ → ℝ)
    (ν : ℝ) (j : ℕ) (b e : ℝ) : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
  composedChartP (fun _ G => LabelGap G Gj j) Gj a ν j b e

theorem composedChartGap_subset {N : ℕ} {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
    {a : ℕ → ℝ} {ν : ℝ} {j : ℕ} {b e : ℝ} :
    composedChartGap (N := N) Gj a ν j b e ⊆ composedChart Gj a ν j b e :=
  composedChartP_subset

end Balaban.Inhabited
