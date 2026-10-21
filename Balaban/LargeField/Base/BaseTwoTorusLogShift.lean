/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseTwoTorusRows
public import Balaban.LargeField.Base.BaseXLogShiftRows
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The rows of the shifted logarithm on two tori (item 4)

For the whole-lattice generating sets `levelGS 1` of two first-step tori identified on a centred
box, the rows of the multiplier `σ_s = Σ_q s_q χ_q`, of the large-`x` coefficient `c(s)` and of the
shifted logarithm `baseCovXLogShift` at the sites of a set `Y` correspond under `boxMap`, under
the reading hypotheses of `BaseTwoTorusRows` (`Sr ⊆ Y`; every active cube inside `Sr` or disjoint
from `Y`; parameters corresponding on the cubes inside `Sr`; `φ₀` corresponding on `Y`).

* `cubeSigma_twoTorus`: `σ_{s'}(bm y) = σ_s(y)`;
* `baseCovXCoef_rows_twoTorus`: the entries of `c(s)` at two sites of `Y` correspond;
* `baseCovXShiftIntegrand_rows_twoTorus`, `baseCovXLogShift_rows_twoTorus`: the integrands (every
  `x ≥ 0`) and the integrals correspond.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.LargeField.Base.XC

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix Balaban.Polymer.TwoTorusStep
  MeasureTheory Set

section TwoTori

variable {d L N₁ N₁' m₁ N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {Cx : ℝ}

set_option hygiene false in
local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ 1) ((N₁' * L ^ m₁) * L ^ 1)
set_option hygiene false in
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := 1) (ϱ := ϱ) 1 le_rfl
set_option hygiene false in
local notation "ιb" x:max => Subtype.mk (bm (x : Balaban.Localization.CTorus d L N₁ m₁ 1))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := 1) (ϱ := ϱ)
    (le_refl 1) le_rfl _)

variable {a : ℕ → ℝ} {aT ν x κ δ : ℝ}
  {Sr Y : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)} {R : ℕ}
  {s : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
  {s' : ℕ × Balaban.Localization.CTorus d L N₁' m₁ 1 → ℂ}
  {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
  {φ : Balaban.Localization.CTorus d L N₁ m₁ 1 → Fin N → ℂ}
  {φ' : Balaban.Localization.CTorus d L N₁' m₁ 1 → Fin N → ℂ}


/-- **`σ_s` as a sum over the cubes inside `Sr`**: for `y ∈ Y`, the cubes meeting `Y` that carry a
non-zero product lie inside `Sr`. -/
theorem cubeSigma_eq_sum_inner {G : GeneratingSet d L (N₁ * L ^ m₁) 1 ϱ} {a : ℕ → ℝ}
    {aT ν₀ : ℝ} {C₀ : ℝ} (S : Dec2.XCover (coverOf G) G a aT ν₀ C₀)
    {s₀ : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1 → ℂ}
    {Sr₀ Y₀ : Finset (Balaban.Localization.CTorus d L N₁ m₁ 1)}
    (hdich : ∀ q ∈ (coverOf G).cubeIdx, (coverOf G).sProd s₀ q ≠ 0 →
      SubI G (intBox q) Sr₀ ∨ DisjI G (intBox q) Y₀)
    {y : G.Ω 1} (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y₀) :
    cubeSigma G s₀ y = ∑ q ∈ innerCentres G Sr₀,
      (coverOf G).sProd s₀ q * (((coverOf G).chi q y : ℝ) : ℂ) := by
  unfold cubeSigma
  symm
  refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hnq => ?_
  by_cases h0 : (coverOf G).sProd s₀ q = 0
  · rw [h0, zero_mul]
  · have hnsub : ¬ SubI G (intBox q) Sr₀ := fun h => hnq (Finset.mem_filter.2 ⟨hq, h⟩)
    rcases hdich q hq h0 with h | h
    · exact absurd h hnsub
    · have : (coverOf G).chi q y = 0 := by
        by_contra hc
        exact h y (mem_intBox_of_chi_ne_zero S hq hc) hy
      rw [this]; simp

section Sigma

variable (hSY : Sr ⊆ Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ 1) y)
  (hn : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
  (hn' : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
  (hdich : ∀ q ∈ (coverOf (GA)).cubeIdx, (coverOf (GA)).sProd s q ≠ 0 →
    SubI (GA) (intBox q) Sr ∨ DisjI (GA) (intBox q) Y)
  (hdich' : ∀ q ∈ (coverOf (GB)).cubeIdx, (coverOf (GB)).sProd s' q ≠ 0 →
    SubI (GB) (intBox q) (Sr.image bm) ∨ DisjI (GB) (intBox q) (Y.image bm))
  (hagree : ∀ q ∈ innerCentres (GA) Sr,
    (coverOf (GB)).sProd s' (Prod.map id bm q) = (coverOf (GA)).sProd s q)
include hSY hYR hn hn' hdich hdich' hagree

/-- **The rows of `σ_s` correspond on two tori**: `σ_{s'}(bm y) = σ_s(y)` for `y ∈ Y`. -/
theorem cubeSigma_twoTorus (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (y : (GA).Ω 1)
    (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) :
    cubeSigma (GB) s' (ιb y) = cubeSigma (GA) s y := by
  have hK1 : 1 ≤ L ^ 1 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hyB : ((ιb y : (GB).Ω 1) : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Y.image bm :=
    Finset.mem_image_of_mem _ hy
  rw [cubeSigma_eq_sum_inner SA hdich hy, cubeSigma_eq_sum_inner SB hdich' hyB]
  have hTR : ∀ x ∈ Sr, InBox d R ((N₁ * L ^ m₁) * L ^ 1) x := fun x hx => hYR x (hSY hx)
  have hyR := hYR _ hy
  have := sum_innerCentres_boxMap (K := 1) (j := 1) (N₁' := N₁') (le_refl 1) le_rfl rfl hTR
    (by omega) (by omega)
    (fun q => (coverOf (GA)).sProd s q * (((coverOf (GA)).chi q y : ℝ) : ℂ))
    (fun q => (coverOf (GB)).sProd s' q * (((coverOf (GB)).chi q (bm y) : ℝ) : ℂ))
    (fun q hq => by
      obtain ⟨y0, rfl, -, hy0T, -⟩ := inner_base_mem (ϱ := ϱ) (le_refl 1) le_rfl hq
      have hy0 := hTR y0 hy0T
      have hc := chi_boxMap (ϱ := ϱ) (N₁' := N₁') (ρ := R) (le_refl 1) le_rfl (by omega)
        (by omega) hyR (inBox_mono (by omega) hy0)
      simp only [hagree _ hq]
      have hc' : (coverOf (GB)).chi (Prod.map id bm ((1, y0) : ℕ × Balaban.Localization.CTorus d L N₁ m₁ 1))
          (bm y) = (coverOf (GA)).chi (1, y0) y := hc
      rw [hc'])
  exact this

end Sigma

section Vec

variable (hCx : 0 ≤ Cx) (hκ : 0 ≤ κ)
  (hM : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hδ : 0 ≤ δ)
  (hsm : δ ^ 2 * smallConstX d L κ ≤ 1 / 4)
  (hαA : AdmPot (GA) α) (hαB : AdmPot (GB) α')
  (hs : ∀ P, ‖s P‖ ≤ Real.exp κ) (hs' : ∀ P, ‖s' P‖ ≤ Real.exp κ)
  (hφA : IsConstraintField (GA) δ φ) (hφB : IsConstraintField (GB) δ φ')
  (hSY : Sr ⊆ Y) (hYR : ∀ y ∈ Y, InBox d R ((N₁ * L ^ m₁) * L ^ 1) y)
  (hn : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁ * L ^ m₁) * L ^ 1)
  (hn' : 4 * R + 12 * L ^ (1 + m₁) + 3 * L ^ 1 + 5 < (N₁' * L ^ m₁) * L ^ 1)
  (hα : ∀ y : (GA).Ω 1, (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr → α' (ιb y) = α y)
  (hdich : ∀ q ∈ (coverOf (GA)).cubeIdx, (coverOf (GA)).sProd s q ≠ 0 →
    SubI (GA) (intBox q) Sr ∨ DisjI (GA) (intBox q) Y)
  (hdich' : ∀ q ∈ (coverOf (GB)).cubeIdx, (coverOf (GB)).sProd s' q ≠ 0 →
    SubI (GB) (intBox q) (Sr.image bm) ∨ DisjI (GB) (intBox q) (Y.image bm))
  (hnbr : ∀ p q : (GA).Ω 1, (p : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Sr →
    ((q : Balaban.Localization.CTorus d L N₁ m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁ m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁ m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈
        (GA).blk ((GA).layerIndex (p : Balaban.Localization.CTorus d L N₁ m₁ 1)) p) →
    (q : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
  (hnbr' : ∀ p q : (GB).Ω 1, (p : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Sr.image bm →
    ((q : Balaban.Localization.CTorus d L N₁' m₁ 1) = p ∨
      (∃ μ : Fin d, (q : Balaban.Localization.CTorus d L N₁' m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁' m₁ 1) + Pi.single μ 1 ∨
        (q : Balaban.Localization.CTorus d L N₁' m₁ 1) =
          (p : Balaban.Localization.CTorus d L N₁' m₁ 1) - Pi.single μ 1) ∨
      (q : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈
        (GB).blk ((GB).layerIndex (p : Balaban.Localization.CTorus d L N₁' m₁ 1)) p) →
    (q : Balaban.Localization.CTorus d L N₁' m₁ 1) ∈ Y.image bm)
  (hagree : ∀ q ∈ innerCentres (GA) Sr,
    (coverOf (GB)).sProd s' (Prod.map id bm q) = (coverOf (GA)).sProd s q)
  (hφ : ∀ u ∈ Y, φ' (bm u) = φ u)
include hCx hκ hM hδ hsm hαA hαB hs hs' hφA hφB hSY hYR hn hn' hα hdich hdich' hnbr hnbr'
  hagree hφ

omit hCx hκ hM hδ hsm hαA hαB hs hs' hφA hφB hα hnbr hnbr' in
/-- **The entries of the large-`x` coefficient correspond on two tori.** -/
theorem baseCovXCoef_rows_twoTorus (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (y z : (GA).Ω 1)
    (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) (i j : Fin N) :
    baseCovXCoef (GB) s' φ' (ιb y, i) (ιb z, j) = baseCovXCoef (GA) s φ (y, i) (z, j) := by
  have hK1 : 1 ≤ L ^ 1 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hm' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (0 + 1) := by
    have h1 : L ^ (0 + 1) = L ^ 1 := rfl
    rw [h1]; omega
  obtain ⟨hinj, -, -⟩ := boxMap_bij_Sr (ϱ := ϱ) (k := 0) (N₁' := N₁') (T := Y) hYR hm'
  have hσ := cubeSigma_twoTorus hSY hYR hn hn' hdich hdich' hagree SA SB y hy
  rw [baseCovXCoef_apply, baseCovXCoef_apply]
  simp only [] at hσ ⊢
  rw [hσ]
  by_cases hyz : y = z
  · subst hyz
    have e : φ' (bm (y : Balaban.Localization.CTorus d L N₁ m₁ 1)) = φ y := hφ _ hy
    simp only [basePart_apply, fieldProj_apply, Matrix.one_apply, restrictField, ite_true]
    rw [e]
    simp
  · have hne : (ιb y : (GB).Ω 1) ≠ ιb z := fun h => hyz (hinj y z hy hz h)
    simp [basePart_apply, fieldProj_apply, hne, hyz]

/-- **The rows of the shifted logarithm correspond on two tori** (item 4).  Under the reading
hypotheses of `baseCovX_rows_twoTorus`, the entries at two sites of `Y` of the integrand
`(1+x)⁻¹ c(s) - C_x(s)` correspond for every `x ≥ 0`, hence so do those of `baseCovXLogShift`. -/
theorem baseCovXLogShift_rows_twoTorus (SA : Dec2.XCover (coverOf (GA)) (GA) a aT ν Cx)
    (SB : Dec2.XCover (coverOf (GB)) (GB) a aT ν Cx) (y z : (GA).Ω 1)
    (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y)
    (hz : (z : Balaban.Localization.CTorus d L N₁ m₁ 1) ∈ Y) (i j : Fin N) :
    (∀ x : ℝ, 0 ≤ x →
      baseCovXShiftIntegrand (GB) a aT ν α' s' φ' x (ιb y, i) (ιb z, j) =
        baseCovXShiftIntegrand (GA) a aT ν α s φ x (y, i) (z, j)) ∧
    baseCovXLogShift (GB) a aT ν α' s' φ' (ιb y, i) (ιb z, j) =
      baseCovXLogShift (GA) a aT ν α s φ (y, i) (z, j) := by
  have hpt : ∀ x : ℝ, 0 ≤ x →
      baseCovXShiftIntegrand (GB) a aT ν α' s' φ' x (ιb y, i) (ιb z, j) =
        baseCovXShiftIntegrand (GA) a aT ν α s φ x (y, i) (z, j) := by
    intro x hx
    have h := baseCovX_rows_twoTorus (xCover_add_mass SA hx) (xCover_add_mass SB hx)
      (hCx := hCx) (hκ := hκ) (hM := hM) (hδ := hδ) (hsm := hsm) (hαA := hαA) (hαB := hαB)
      (hs := hs) (hs' := hs') (hφA := hφA) (hφB := hφB) (hSY := hSY) (hYR := hYR) (hn := hn)
      (hn' := hn') (hα := hα) (hdich := hdich) (hdich' := hdich') (hnbr := hnbr)
      (hnbr' := hnbr') (hagree := hagree) (hφ := hφ) y z hy hz i j
    have hc := baseCovXCoef_rows_twoTorus hSY hYR hn hn' hdich hdich' hagree hφ SA SB y z hy hz i j
    unfold baseCovXShiftIntegrand
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] at h ⊢
    rw [hc, h]
  refine ⟨hpt, ?_⟩
  unfold baseCovXLogShift
  exact setIntegral_congr_fun measurableSet_Ioi fun x hx => hpt x (mem_Ioi.mp hx).le

end Vec

end TwoTori

end Balaban.LargeField.Base.XC
