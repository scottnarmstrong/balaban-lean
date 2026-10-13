/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkCorrCountFromTower
public import Balaban.Inhabited.E1LabelsBudgetG
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

/-- The fixed label domains are the general ones at `d = L = 3`, `N = 2`. -/
theorem e1DomG_three {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ} (S : StepSetting 3 3 N₁ m₁ k 2 ϱ)
    (b : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) : e1DomG S b = e1Dom S b := rfl

/-- **The label domains are domains of the level `k + 1`.** -/
theorem e1Dom_isDj {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁]
    {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁) :
    ∀ b, ∀ Y ∈ e1Dom (T.step k hk N₁ ν β p₁) b, IsDj 1 (k + 1) Y := by
  exact e1DomG_isDj T.toG rfl (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm

open Classical in
/-- **The bridge family of every root is nonempty.**  The domain `X₁` of the cover of the block
`z` itself (the empty connected family) is a label; it contains the root site of `z`, so its
thickening meets the fine block of `z` and its bridge belongs to the family. -/
theorem e1Dom_bridgeFamily_nonempty {κmin : ℝ} (T : StepTower κmin) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleData T k hk N₁ ν β p₁)
    (z : RootIdx 3 3 N₁ T.m₁ (k + 1)) :
    (bridgeFamily 1 (fun _ => Set.univ) (e1Dom (T.step k hk N₁ ν β p₁)) z).Nonempty := by
  exact e1DomG_bridgeFamily_nonempty T.toG rfl (T.scaleDataG_of_fixed D)
    (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm z

/-- The per-root constant of the corrected marks is positive. -/
theorem corrF0_pos {κmin : ℝ} (T : StepTower κmin) {k : ℕ} (hk : 1 ≤ k) {β p₁ : ℝ}
    (hβ : 0 < β) (hp : 0 < p₁) : 0 < corrF0 T k β p₁ := by
  rw [corrF0_toG]
  exact corrF0G_pos T.toG hk hβ hp

/-- The coefficient of the mark budget depends on the tower only and is nonnegative. -/
theorem cpe_marks_nonneg {κmin : ℝ} (T : StepTower κmin) :
    0 ≤ CPE 3 3 T.marksKc' (2 * T.κdec - 1) T.κ0 T.κ' := by
  exact cpe_marks_nonnegG T.toG

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
  obtain ⟨β₀, h1, h⟩ := corrBudget_fromTowerG T.toG rfl hA p
  refine ⟨β₀, h1, fun k hk N₁ _ h3N ν β hβ p₁ hp hp₁ D z => ?_⟩
  have hb : β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by norm_num
  have := h k hk N₁ (by simpa using h3N) ν β hβ p₁ hp (by rw [hb]; exact hp₁)
    (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm z
  simp only [corrF0_toG]
  exact this

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
  obtain ⟨β₀, hβ₀, hR, hF⟩ := exists_beta0_e1G T.toG rfl hA p βa
  have hb : ∀ (k : ℕ) (β : ℝ), β * ((3 : ℕ) : ℝ) ^ (k * (3 - 2)) = β * 3 ^ k := by
    intro k β; norm_num
  refine ⟨β₀, hβ₀, fun k hk β hβ p₁ hp hp₁ => ?_,
    fun k hk N₁ _ h3N ν β hβ p₁ hp hp₁ D z => ?_⟩
  · have := hR k hk β hβ p₁ hp (by rw [hb]; exact hp₁)
    rw [hb, ← corrR_toG] at this
    exact this
  · have := hF k hk N₁ (by simpa using h3N) ν β hβ p₁ hp (by rw [hb]; exact hp₁)
      (T.scaleDataG_of_fixed D) (ϱ := rhoSep T.m₁) (rhoSepG_three _).symm z
    simp only [corrF0_toG]
    exact this

end Balaban.Inhabited
