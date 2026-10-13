/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.LevelRayTower
public import Balaban.Inhabited.ScaleActivityFinal
public import Balaban.Fluctuation.ParamActivitySubspace
import Mathlib.Tactic.Positivity

/-!
# The step datum at every scale is a point of a relatively open chart

At the step `hatStepK k m₁ hk ν β p₁ δ` (`d = L = 3`, `N = 2`, constant unit block datum), for every
scale `k ≥ 1`, every torus `N₁` and every mass `0 ≤ ν` with `ν · 3^{2(k+1)} ≤ 1`, and every chart
size `t > 0`:

* `hatStepK_xiCData`: the step datum `S.D'` satisfies `XiCData` (the chart `Ξ^c_{k+1}(𝔹; 1, t)`),
  with no condition on `β`, `p₁`, `δ`;
* `hatStepK_rawOf_mem_xiCRaw`: its raw datum `rawOf S.D'` lies in `XiCRaw`;
* `hatStepK_physV`: the set `physV` of the parameter space `rawSub × sources` is open, contains the
  step datum with source `0` (and with every source in the strict `ℓ¹` ball), and every point of it
  has a datum with `XiCData` and the given raw datum.

What is proved: relative openness of the chart in the subspace `rawSub` at the general-scale step
(it is the content of `isOpen_preimage_xiCRaw`).  What is not proved: any quantitative radius of the
neighbourhood, the marked disc, the determinant chart, the physical source-dependent theorem at
general scale, and the family of activities over the relative complex chart.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep

section Chart

variable {N₁ : ℕ} [NeZero N₁]

/-- **The step datum is in the chart.**  At every scale and every torus, for the masses with
`ν · 3^{2(k+1)} ≤ 1` and every chart size `t > 0`. -/
theorem hatStepK_xiCData (k m₁ : ℕ) (hk : 1 ≤ k) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t
      (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' := by
  have hHB := bgHyp_lv (k := k) (ν := ν) m₁ hν0 hν
  refine ⟨fun _ => unitVec hN2, unitVec hN2, 0, 0,
    exists_xiC hHB (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (massLe_lv hν) ht0, ?_, ?_⟩
  · intro x hx i
    have := unitBg_Ψ_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
    show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).Ψ x i = _
    rw [this]; simp
  · intro x hx i
    have := unitBg_h_of_mem (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2) hx i
    show (unitBg (lvTop N₁ m₁ k (rhoSep m₁)) hN2 (unitVec hN2)).h x i = _
    rw [this]; simp

/-- The raw datum of the step lies in `XiCRaw`. -/
theorem hatStepK_rawOf_mem_xiCRaw (k m₁ : ℕ) (hk : 1 ≤ k) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D' ∈
      XiCRaw (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t :=
  ⟨_, hatStepK_xiCData k m₁ hk hν0 hν β p₁ δ ht0, rfl⟩

/-- **A relatively open neighbourhood of the physical point at the general-scale step.**
The set `physV` of the parameter space `rawSub × sources` is open; it contains the step datum
`rawOf S.D'` with every source of the strict `ℓ¹` ball; and every point of it is the raw datum of a
datum satisfying `XiCData`.  No radius is asserted. -/
theorem hatStepK_physV (k m₁ : ℕ) (hk : 1 ≤ k) {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β p₁ δ : ℝ) {t : ℝ} (ht0 : 0 < t) :
    IsOpen (physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t) ∧
    (∀ g ∈ l1Ball 3 3 N₁ m₁ (k + 1) 2,
      (⟨rawOf (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).D',
          rawOf_mem_rawSub _⟩, g) ∈
        physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t) ∧
    (∀ e ∈ physV (N := 2) (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ) 1 ν t,
      ∃ D, XiCData (hatStepK (N₁ := N₁) k m₁ hk ν β p₁ δ).G' (compWeight 3 1) ν (k + 1) 1 t D ∧
        rawOf D = (e.1 : RawData 3 3 (N₁ * 3 ^ m₁) (k + 1) 2)) := by
  refine ⟨isOpen_physV _ _ _ _ (bgHyp_lv (k := k) (ν := ν) m₁ hν0 hν), ?_, ?_⟩
  · intro g hg
    exact ⟨hatStepK_rawOf_mem_xiCRaw k m₁ hk hν0 hν β p₁ δ ht0, hg⟩
  · intro e he
    obtain ⟨D, hD, h⟩ := he.1
    exact ⟨D, hD, h.symm⟩

end Chart

end Balaban.Inhabited
