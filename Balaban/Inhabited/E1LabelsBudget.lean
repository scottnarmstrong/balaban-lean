/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkCorrCountFromTower
public import Balaban.Inhabited.ZeroSourceActivityCommon
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Labels and numerical budget of the energy marks of the renormalization step

Preparatory facts for the marks record of the interpolation integral `ℰ₁^{(k+1)}(z)` at a scale of
the shared tower:

* `e1Dom_isDj`: the label domains `dom b` built from the scale covers consist of domains
  `𝒟_{k+1}` (`IsDj 1 (k + 1)`), as required by the common label system;
* `corrF0_pos`: the per-root constant of the corrected marks is positive;
* `corrBudget_fromTower`: beyond a threshold in `β`, `C_PE ∑ F₀ e^{-κ₀ d} ≤ K₀`, uniformly in the
  scale and in `p₁`, the constants `C_PE`, `K₀` depending only on the tower;
* `exists_beta0_e1`: one threshold for the activity, the Cauchy radius and the budget.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

/-- The label domains of the block `b`: the polymer domains of the cover of `b`. -/
noncomputable abbrev e1Dom {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting 3 3 N₁ m₁ k 2 ϱ) (b : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) :
    Finset (Set (CTorus 3 3 N₁ m₁ (k + 1))) :=
  polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
    (LocalCover.fam 1 (LocalCover.blockSite k b))

/-- **The label domains are domains of the level `k + 1`.** -/
theorem e1Dom_isDj {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
    {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) :
    ∀ b, ∀ Y ∈ e1Dom (T.step k hk N₁ ν β p₁) b, IsDj 1 (k + 1) Y := by
  obtain ⟨hV, -⟩ := D.covers
  intro b Y hY
  exact isDj_of_polyDom (T.step k hk N₁ ν β p₁).hG' (hV b).1 (by norm_num) (hV b).2.2.1 hY

open Classical in
/-- **The bridge family of every root is nonempty.**  The domain `X₁` of the cover of the block
`z` itself (the empty connected family) is a label; it contains the root site of `z`, so its
thickening meets the fine block of `z` and its bridge belongs to the family. -/
theorem e1Dom_bridgeFamily_nonempty {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1)) :
    (bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z).Nonempty := by
  obtain ⟨hV, -⟩ := D.covers
  obtain ⟨-, hX, -, -, -, -, hbs⟩ := hV z
  set X := X1 (T.step k hk N₁ ν β p₁).G' 1 k (LocalCover.fam 1 (LocalCover.blockSite k z))
  have hY : X ∈ e1Dom (T.step k hk N₁ ν β p₁) z := by
    unfold e1Dom polyDom polymerDomains
    rw [Finset.mem_image]
    refine ⟨∅, ?_, by simp [Ysites]; rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hroot : rootSite z ∈ blockSites 3 3 N₁ T.m₁ (k + 1) k z := by
    unfold blockSites
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, blockIndex_rootSite z⟩
  have hxX : rootSite z ∈ X := by
    have h := hbs (Finset.mem_coe.2 hroot)
    rw [hX] at h
    exact h
  exact ⟨bridge 1 z X, mem_bridgeFamily.2 ⟨z, X, hY, ⟨rootSite z, Set.mem_univ _, blockIndex_rootSite z⟩,
    ⟨rootSite z, Or.inl hxX, blockIndex_rootSite z⟩, rfl⟩⟩

/-- The per-root constant of the corrected marks is positive. -/
theorem corrF0_pos {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ}
    (hβ : 0 < β) (hp : 0 < p₁) : 0 < corrF0 T k β p₁ := by
  have hb0 : 0 < β * 3 ^ k := by positivity
  have hR := corrR_pos T hk hb0 hp
  have hE : 0 < Estar T k := by
    rw [Estar_eq T hk]
    have := Ecst_pos T (compWeight_three_mem hk).1
    positivity
  have hK := Kmark_pos T
  have hU := corrU_pos
  unfold corrF0
  rw [abs_of_pos hβ]
  positivity

/-- The coefficient of the mark budget depends on the tower only and is nonnegative. -/
theorem cpe_marks_nonneg {κmin : ℝ} (T : StepTower κmin) :
    0 ≤ CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' := by
  have := one_le_c1 3 3
  unfold CPE
  positivity

/-- **The budget of the marks, beyond a threshold in `β`.**  For every scale `k ≥ 1` and every
`p₁ ≤ pLog A₁ p (β 3^k)`, and every scale datum, the weighted sum over the bridge family of a root,
with the constant `F₀ = corrF0`, satisfies
`C_PE(K_c′, 2κ_dec − 1, κ₀, κ′) · ∑ F₀ e^{−κ₀ d} ≤ K₀(κ₀)`. -/
theorem corrBudget_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 1 ≤ β₀ ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ →
      ∀ (ν β : ℝ), β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
        CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
          (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1Dom (T.step k hk N₁ ν β p₁)) z},
            corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
          K0 3 3 T.κ0 := by
  have hP := cpe_marks_nonneg T
  have hε : 0 < 1 / (CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' + 1) := by positivity
  obtain ⟨β₀, h⟩ := exists_beta0_corrF0_le T hε hA p
  refine ⟨max 1 β₀, le_max_left _ _, fun k hk N₁ _ h3N ν β hβ p₁ hp hp₁ D z => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβ)
  have hF := h k hk β ((le_max_right _ _).trans hβ) p₁ hp hp₁
  have hF0 := (corrF0_pos T hk hβ0 hp).le
  have hent := bridgeFamily_entropy (m₀ := 1) (d := 3) (L := 3)
    (show 3 ^ 1 ∣ N₁ by simpa using h3N) (by norm_num) (reads := fun _ => Set.univ)
    (e1Dom_isDj T D) z T.marks_hκ0 hF0
  have hK := K0_pos 3 3 T.κ0
  refine (mul_le_mul_of_nonneg_left hent hP).trans ?_
  have h1 : corrF0 T k β p₁ * K0 3 3 T.κ0 ≤
      1 / (CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' + 1) * K0 3 3 T.κ0 :=
    mul_le_mul_of_nonneg_right hF hK.le
  have h2 : CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
      (1 / (CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  calc _ ≤ CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
        (1 / (CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' + 1) * K0 3 3 T.κ0) :=
        mul_le_mul_of_nonneg_left h1 hP
    _ = (CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
        (1 / (CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' + 1))) * K0 3 3 T.κ0 := by ring
    _ ≤ 1 * K0 3 3 T.κ0 := mul_le_mul_of_nonneg_right h2 hK.le
    _ = K0 3 3 T.κ0 := one_mul _

/-- **One threshold for the marks record.**  For any threshold `βa` (that of the activity
`zeroSourceActivity_common_fromTower`) there is `β₀ ≥ max 3 βa` such that for every `β ≥ β₀`, every
scale `k ≥ 1` and every `0 < p₁ ≤ pLog A₁ p (β 3^k)`: the Cauchy radius satisfies `2 U ≤ R`, and
the budget of the marks holds. -/
theorem exists_beta0_e1 {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ)
    (βa : ℝ) :
    ∃ β₀ : ℝ, max 3 βa ≤ β₀ ∧
      (∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
        p₁ ≤ pLog A₁ p (β * 3 ^ k) → 2 * corrU ≤ corrR T k (β * 3 ^ k) p₁) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], 3 ∣ N₁ →
        ∀ (ν β : ℝ), β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ → p₁ ≤ pLog A₁ p (β * 3 ^ k) →
        StepScaleData T k hk N₁ ν β p₁ →
        ∀ z : RootIdx 3 3 N₁ T.m₁ (k + 1),
          CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' *
            (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1Dom (T.step k hk N₁ ν β p₁)) z},
              corrF0 T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
            K0 3 3 T.κ0 := by
  obtain ⟨βR, hR⟩ := exists_beta0_corrR T hA p
  obtain ⟨βF, -, hF⟩ := corrBudget_fromTower T hA p
  refine ⟨max (max 3 βa) (max βR βF), le_max_left _ _, fun k hk β hβ p₁ hp hp₁ => ?_,
    fun k hk N₁ _ h3N ν β hβ p₁ hp hp₁ D z => ?_⟩
  · exact hR k hk β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) p₁ hp hp₁
  · exact hF k hk N₁ h3N ν β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) p₁ hp hp₁ D z

end Balaban.Inhabited
