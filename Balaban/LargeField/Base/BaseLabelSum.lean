/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseCellGraph
public import Balaban.LargeField.Base.BaseLabelSumAux
public import Balaban.LargeField.Base.BaseBgHull
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The coefficients of the rooted families with a given label

For coefficients `c x Cs` of the finite families `Cs` of cells of a decoupling cover (one family per
site `x`), non-zero only for the families rooted at a set of sites within `ρs` of `x`
(`IsRootedFamily (cellPatch C D)`), with `‖c x Cs‖ ≤ B e^{-(κ-1)|Cs|}`, the label of `(x, Cs)` is
the set `labelSet` of the hull of the root cube of `x` and the patches `labelJ` of the family.  The
sum of the coefficients with a given label `Y` is at most `labelAmp · e^{-labelRate · d^cov(Y)}`
(`norm_labelSum_le`), provided `Δ² e^{-(κ-1)} < 1` with `Δ = labelDelta`, a number independent of
`m₁` (it bounds the degree of the graph of cells, `cellGraph_degree_le`, and the number of cells
that meet the seed, `card_rootCells_le`).  The proof counts the families by rooted animals of that
graph (`rooted_tail_sum_le`), the sites `x` by the sites of `Y` (`ncard_le_of_isDj`), and uses the
size of the hull, at most `2 d L (A + 20^d |Cs|)` (`labelHull_spec`), to bound `|Cs|` from below.
-/

@[expose] public section

namespace Balaban.LargeField.Base

open Balaban Balaban.Localization Balaban.LargeField Balaban.Fluctuation Balaban.SmallField.Def6 Finset

section Main

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {m₀ : ℕ} (C : DecCover d L N₁ m₁ (k + 1))

/-- The label of a pair `(x, Cs)`: the sites of the hull of the root cube of `x` and the patches
`labelJ`. -/
noncomputable def labelSet (m₀ : ℕ) (x : Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) (ρs : ℕ)
    (Cs : Finset ↥C.cubeIdx) : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)) :=
  sitesOf (hullOf m₀ (blockIndex x) (labelJ C x ρs Cs))

/-- The degree `Δ = max (b + 1) b_root` of the graph of cells with the root adjoined. -/
def labelDelta (d L k ρs : ℕ) : ℕ := max (cellsNear d L k 18 + 1) (cellsRoot d L k ρs)

/-- The ratio `z = Δ² e^{-(κ-1)}` of the geometric series of rooted cells. -/
noncomputable def labelZ (d L k ρs : ℕ) (κ : ℝ) : ℝ :=
  ((labelDelta d L k ρs : ℕ) : ℝ) ^ 2 * Real.exp (-(κ - 1))

/-- The rate of the decay of the sum of the coefficients with a given label in the size of the label. -/
noncomputable def labelRate (d L k ρs : ℕ) (κ : ℝ) : ℝ :=
  -Real.log (labelZ d L k ρs κ) / ((2 * d * L : ℝ) * (20 : ℝ) ^ d) / 2

/-- The amplitude of that bound for coefficients of size `B e^{-(κ-1)|C|}`. -/
noncomputable def labelAmp (d L m₀ m₁ k ρs : ℕ) (κ B : ℝ) : ℝ :=
  (((L ^ (k + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d * c1 d L * B *
    Real.exp (-Real.log (labelZ d L k ρs κ) * (((2 * ρs / L ^ (k + 1 + m₁) + 2) ^ d : ℕ) : ℝ) /
      (20 : ℝ) ^ d) *
    (1 + 2 / (-Real.log (labelZ d L k ρs κ) / ((2 * d * L : ℝ) * (20 : ℝ) ^ d))) /
    (1 - labelZ d L k ρs κ)

theorem labelZ_pos (d L k ρs : ℕ) (κ : ℝ) : 0 < labelZ d L k ρs κ := by
  unfold labelZ labelDelta
  have : (0 : ℝ) < ((max (cellsNear d L k 18 + 1) (cellsRoot d L k ρs) : ℕ) : ℝ) :=
    by exact_mod_cast lt_of_lt_of_le (Nat.succ_pos _) (le_max_left _ _)
  positivity

theorem labelAmp_nonneg (d L m₀ m₁ k ρs : ℕ) (κ : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hz : labelZ d L k ρs κ < 1) : 0 ≤ labelAmp d L m₀ m₁ k ρs κ B := by
  have hz0 := labelZ_pos d L k ρs κ
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have h1z : 0 < 1 - labelZ d L k ρs κ := by linarith
  have hlam : 0 < -Real.log (labelZ d L k ρs κ) := by
    have := Real.log_neg hz0 hz; linarith
  unfold labelAmp
  have : 0 ≤ 1 + 2 / (-Real.log (labelZ d L k ρs κ) / ((2 * d * L : ℝ) * (20 : ℝ) ^ d)) := by positivity
  positivity

open Classical in
/-- **The sum of the rooted coefficients with a given label decays in the size of the label.**
Let `c x Cs` be coefficients of the finite families `Cs` of cells of a decoupling cover, non-zero
only for the families rooted at a set `S x` of sites within `ρs` of the site `pos x`, with
`‖c x Cs‖ ≤ B e^{-(κ-1)|Cs|}`.  If `Δ² e^{-(κ-1)} < 1` (`Δ = labelDelta`), then for every set `Y` the
sum, over the sites `x` and the families `Cs` whose label (the hull of the root cube and of the
patches of the family) is `Y`, of `c x Cs` is bounded by `labelAmp · e^{-labelRate · d^cov(Y)}`. -/
theorem norm_labelSum_le {ι : Type*} [Fintype ι] (hd : 0 < d)
    (pos : ι → Balaban.Localization.CTorus d L N₁ m₁ (k + 1))
    (hpos : Function.Injective pos) (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L) {D : ℕ}
    (hD : D ≤ L ^ (k + 1 + m₁)) (hm : 4 * L ^ 2 ≤ L ^ m₁)
    (hlay : ∀ q ∈ C.cubeIdx, 1 ≤ q.1 ∧ q.1 ≤ k + 1)
    (hal : ∀ q ∈ C.cubeIdx, Aligned (L ^ (q.1 + m₁)) q.2) {ρs : ℕ}
    (S : ι → Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1)))
    (hS : ∀ x, ∀ y ∈ S x, supDist (pos x) y ≤ ρs) (c : ι → Finset ↥C.cubeIdx → ℂ) {B κ : ℝ}
    (hB : 0 ≤ B) (hz : labelZ d L k ρs κ < 1)
    (hroot : ∀ x Cs, c x Cs ≠ 0 → Green.IsRootedFamily (cellPatch C D) (S x) Cs)
    (hbd : ∀ x Cs, ‖c x Cs‖ ≤ B * Real.exp (-(κ - 1)) ^ Cs.card)
    (Y : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) :
    ‖∑ x, ∑ Cs ∈ Finset.univ.filter (fun Cs : Finset ↥C.cubeIdx => labelSet C m₀ (pos x) ρs Cs = Y),
        c x Cs‖ ≤
      labelAmp d L m₀ m₁ k ρs κ B * Real.exp (-(labelRate d L k ρs κ) * treeLenCovOne m₀ (k + 1) Y) := by

  classical
  have hz0 := labelZ_pos d L k ρs κ
  have hlam : 0 < -Real.log (labelZ d L k ρs κ) := by
    have := Real.log_neg hz0 hz; linarith
  have hd0 : (0 : ℝ) < 2 * d * L := by
    have hd : (0 : ℝ) < d := by exact_mod_cast hd
    have hL0 : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
    positivity
  have hP0 : (0 : ℝ) < (20 : ℝ) ^ d := by positivity
  set z := labelZ d L k ρs κ with hzdef
  set A : ℝ := (((2 * ρs / L ^ (k + 1 + m₁) + 2) ^ d : ℕ) : ℝ) with hA
  by_cases hex : ∃ x Cs, c x Cs ≠ 0 ∧ labelSet C m₀ (pos x) ρs Cs = Y
  swap
  · have h0 : ∑ x, ∑ Cs ∈ Finset.univ.filter
        (fun Cs : Finset ↥C.cubeIdx => labelSet C m₀ (pos x) ρs Cs = Y), c x Cs = 0 :=
      Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun Cs hCs => by
        by_contra hne
        exact hex ⟨x, Cs, hne, (Finset.mem_filter.1 hCs).2⟩
    rw [h0, norm_zero]
    unfold labelAmp labelRate
    have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
    have h1z : 0 < 1 - z := by linarith
    have : 0 ≤ 1 + 2 / (-Real.log z / ((2 * d * L : ℝ) * (20 : ℝ) ^ d)) := by positivity
    positivity
  obtain ⟨x0, Cs0, hc0, hl0⟩ := hex
  have hspec : ∀ x Cs, c x Cs ≠ 0 → IsPolyDom m₀ (k + 1) (labelSet C m₀ (pos x) ρs Cs) ∧
      (∀ y, supDist (pos x) y ≤ ρs → y ∈ labelSet C m₀ (pos x) ρs Cs) ∧
      sizeJ m₀ (k + 1) (labelSet C m₀ (pos x) ρs Cs) ≤ (2 * d * L : ℝ) * (A + (Cs.card * 20 ^ d : ℕ)) :=
    fun x Cs h => labelHull_spec hN hL hD hm (fun q hq => (hlay q hq).2) (pos x) (hS x)
      (hroot x Cs h)
  have hY : IsPolyDom m₀ (k + 1) Y := hl0 ▸ (hspec x0 Cs0 hc0).1
  have hYDj : IsDj m₀ (k + 1) Y := isDj_of_isPolyDom hY
  set σ : ℝ := treeLenCovOne m₀ (k + 1) Y with hσ
  have hσ0 : 0 ≤ σ := treeLenCovOne_nonneg m₀ (k + 1) Y
  set n : ℕ := ⌈(σ / (2 * d * L : ℝ) - A) / (20 : ℝ) ^ d⌉₊ with hn
  set Xs : Finset ι := Finset.univ.filter (fun x => pos x ∈ Y) with hXs
  have hmain := norm_sum_label_le (Gr := cellGraph C D) (V := ↥C.cubeIdx)
    (b := cellsNear d L k 18) (b_root := cellsRoot d L k ρs)
    (cellGraph_degree_le hD hm hlay hal) (fun x => rootCells (C := C) D (S x))
    (fun x => card_rootCells_le hD hm hlay hal (pos x) (hS x))
    (t := Real.exp (-(κ - 1))) (Real.exp_pos _).le hz c hB
    (fun x Cs => labelSet C m₀ (pos x) ρs Cs) Y n Xs
    (fun x Cs h => Polymer.mem_rootedSets.2 (rooted_cellGraph (hroot x Cs h))) hbd
    (fun x Cs h hl => by
      refine Nat.ceil_le.2 ?_
      have h3 := (hspec x Cs h).2.2
      rw [hl] at h3
      have h4 : σ ≤ (2 * d * L : ℝ) * (A + (Cs.card * 20 ^ d : ℕ)) := h3
      rw [div_le_iff₀ (by positivity)]
      push_cast at h4
      have h5 : σ / (2 * d * L : ℝ) ≤ A + (Cs.card : ℝ) * 20 ^ d :=
        (div_le_iff₀ hd0).2 (by nlinarith [h4])
      linarith)
    (fun x Cs h hl => by
      rw [hXs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [← hl]
      exact (hspec x Cs h).2.1 (pos x) (by rw [supDist_self]; exact Nat.zero_le _))
  have hXcard : (Xs.card : ℝ) ≤ Y.ncard := by
    have h1 : Xs.card = (Xs.image pos).card := (Finset.card_image_of_injective _ hpos).symm
    have h2 : ((Xs.image pos : Finset _) : Set (Balaban.Localization.CTorus d L N₁ m₁ (k + 1))) ⊆ Y := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hy)
      exact (Finset.mem_filter.1 hx).2
    have h3 := Set.ncard_le_ncard h2 (Set.toFinite Y)
    rw [Set.ncard_coe_finset] at h3
    rw [h1]; exact_mod_cast h3
  have hYn := ncard_le_of_isDj hN (le_refl (k + 1)) hYDj
  have h1z : 0 < 1 - z := by linarith
  have hzn : 0 ≤ z ^ n := by positivity
  have hdec := tail_decay_aux hz0 hz hd0 hP0 hσ0 (Nat.le_ceil ((σ / (2 * d * L : ℝ) - A) / (20 : ℝ) ^ d))
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hcs : ((cellSide L m₀ m₁ (k + 1) : ℕ) : ℝ) = (((L ^ (k + 1 + m₀ + m₁) : ℕ) : ℝ)) := by
    unfold cellSide; rfl
  rw [hcs] at hYn
  set a : ℝ := (((L ^ (k + 1 + m₀ + m₁) : ℕ) : ℝ)) ^ d with ha
  have ha0 : 0 ≤ a := by positivity
  calc _ ≤ Xs.card * (B * (z ^ n / (1 - z))) := hmain
    _ ≤ (a * (c1 d L * (1 + σ))) * (B * (z ^ n / (1 - z))) := by
        refine mul_le_mul (hXcard.trans hYn) le_rfl (by positivity) (by positivity)
    _ = (a * c1 d L * B / (1 - z)) * ((1 + σ) * z ^ n) := by ring
    _ ≤ (a * c1 d L * B / (1 - z)) * (Real.exp (-Real.log z * A / (20 : ℝ) ^ d) *
          (1 + 2 / (-Real.log z / ((2 * d * L : ℝ) * (20 : ℝ) ^ d))) *
          Real.exp (-(-Real.log z / ((2 * d * L : ℝ) * (20 : ℝ) ^ d) / 2 * σ))) :=
        mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by
        unfold labelAmp labelRate
        rw [← hzdef]
        have : -(-Real.log z / ((2 * d * L : ℝ) * (20 : ℝ) ^ d) / 2 * σ) =
            -(-Real.log z / ((2 * d * L : ℝ) * (20 : ℝ) ^ d) / 2) * σ := by ring
        rw [this]
        ring

end Main

end Balaban.LargeField.Base
