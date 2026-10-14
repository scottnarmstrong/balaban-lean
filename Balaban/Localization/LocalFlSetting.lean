/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalFluctGen
public import Balaban.Fluctuation.SharpChartTestFlSup
public import Balaban.Localization.I5FluctNonempty
public import Balaban.Localization.P6PairLocFinal

/-!
# The fluctuation setting at the local generator pair

`localPair_flSetting_nonempty`: the hypotheses `FlSetting` of the fluctuation are met at the local
pair `(𝔹_{k+1}(Y), 𝔹_k(Y))` of `Fluctuation/LocalFluctGen.lean`, for any fluctuation generating set
`𝔹_k(X) ≺ 𝔹_{k+1}(Y)` without layer `k + 1`.  The cover constants `(c₂, BG₂)` of the second
decoupling are given (they exist, `localPair_decSpecs_exists`), with the scale condition
`c₂ e^{N₀ κ} ≤ M₁` (large `M₁`); the smallness constants `ε'`, `δ₃`, `δ₁`, `δ_fl` are produced.
The dependency set `X₁` is any finite set containing the composition footprints of the data sites.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.LargeField Finset

variable {d L N₁ m₁ K N : ℕ} [NeZero L] [NeZero N₁]

/-- The cover constants `(c₂, BG₂)` of the second decoupling exist at the local pair. -/
theorem localPair_decSpecs_exists (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ c₂ BG₂ : ℝ, Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ :=
  p6_decSpecs_exists hd hL

/-- **`FlSetting` is inhabited at the local pair** `(𝔹_{k+1}(Y), 𝔹_k(Y))`: for the cover constants
`(c₂, BG₂)` with `c₂ e^{N₀ κ} ≤ M₁` and every `X₁` containing the composition footprints, there are
`ε'`, `δ₃`, `δ₁`, `δ_fl` such that all fields hold (the pair fields are `localB_drop_pair`, the
order `𝔹_k(X) ≺ 𝔹_k(Y)` is `GsSpec.precedes_localB_drop`, the numerical fields are `flNum_nonempty`). -/
theorem localPair_flSetting_nonempty {k : ℕ} (hk : k + 1 ≤ K) (Y : Set (CTorus d L N₁ m₁ K))
    (hN : 5 < N₁) (hm₁ : 2 ≤ m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) {a₁ ν : ℝ} (hd : 3 ≤ d)
    (hL : 3 ≤ L) (hν : 0 ≤ ν) (hνL : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights K (compWeight L a₁))
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1))
    {ϱk : ℝ} {Gk : GeneratingSet d L (N₁ * L ^ m₁) K ϱk}
    (hP : Precedes Gk (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))))
    (htop : Gk.Ω (k + 1) = ∅) {κ BG c₂ BG₂ : ℝ}
    (hS2 : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂)
    (hM2 : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    {X₁f : Finset (CTorus d L N₁ m₁ K)}
    (depm : ∀ x ∈ dataSites Gk, ∀ y ∈ composeDep Gk
      (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁)))) x, y ∈ X₁f) :
    ∃ eps δ₃ δ₁ δfl : ℝ, Nonempty (FlSetting N
      (GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))) Gk
      (GsSpec.localB k (by omega)
        (↑((GsSpec.localB (k + 1) hk Y (le_refl (minSep L (L ^ m₁)))).Ω k) :
          Set (CTorus d L N₁ m₁ K)) (le_refl (minSep L (L ^ m₁))))
      a₁ ν κ BG eps δ₃ (Dec2.mixedKc d L) (Cchi d L) c₂ BG₂ δ₁ δfl X₁f) := by
  obtain ⟨hPd, -, hFoot, -⟩ := localB_drop_pair (N₁ := N₁) (m₁ := m₁) (K := K) (a := compWeight L a₁)
    (ν := ν) hk Y hN hm₁ hM hd hL hν hνL ha hag
  obtain ⟨t, ht, ⟨hnum⟩⟩ := flNum_nonempty (d := d) (L := L) (N := N) (by omega) BG
    (BG₂ := BG₂) hS2.fam.2.1 κ
  exact ⟨t, t, t, _, ⟨{
    hS2 := hS2, SM := hFoot, hM2 := hM2,
    hPm := GsSpec.precedes_localB_drop hk (by omega) Y le_rfl le_rfl hP htop,
    hPmp := hPd, depm := depm, num := hnum }⟩⟩

end Balaban.Localization
