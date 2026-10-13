/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.DecMarkCorrFamilyFromTowerG
public import Balaban.Inhabited.StepTowerGScalars
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# Labels and numerical budget of the energy marks at the general tower

General versions of the facts of `E1LabelsBudget`:

* `e1DomG`: the label domains of the block `b` (the general definition with the body of `e1Dom`);
* `e1DomG_isDj`: they consist of domains `𝒟_{k+1}` (`IsDj 1 (k + 1)`);
* `e1DomG_bridgeFamily_nonempty`: the bridge family of every root is nonempty;
* `corrF0G_pos`, `cpe_marks_nonnegG`;
* `corrBudget_fromTowerG`: beyond a threshold in `β`, `C_PE ∑ F₀ e^{-κ₀ d} ≤ K₀`;
* `exists_beta0_e1G`: one threshold for the Cauchy radius and the budget.

The cover index of the marks is `1`, so the tower carries `T.m₀ = 1`.  The step setting is
`hatStepKG … ϱ …` for a separation parameter `ϱ = rhoSepG d L T.m₁`, so that the fixed
statements (over `rhoSep T.m₁`) are the instances.
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep
  Balaban.Inhabited.MarkBudgetAudit

/-- The label domains of the block `b`: the polymer domains of the cover of `b`
(general `d`, `L`, `N`). -/
noncomputable abbrev e1DomG {d L N N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
    (S : StepSetting d L N₁ m₁ k N ϱ) (b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    Finset (Set (CTorus d L N₁ m₁ (k + 1))) :=
  polyDom S.G' (LocalCover.nbhdF 1 (LocalCover.blockSite k b)) 1 k
    (LocalCover.fam 1 (LocalCover.blockSite k b))

/-- **The label domains are domains of the level `k + 1`.** -/
theorem e1DomG_isDj {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k} {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ}
    (D : StepScaleDataG T k hk N₁ ν β p₁) {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) :
    ∀ b, ∀ Y ∈ e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ) b, IsDj 1 (k + 1) Y := by
  subst hϱ
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  intro b Y hY
  exact isDj_of_polyDom (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).hG' (hV b).1
    T.hd (hV b).2.2.1 hY

open Classical in
/-- **The bridge family of every root is nonempty.** -/
theorem e1DomG_bridgeFamily_nonempty {d L N : ℕ} [NeZero L] {κmin : ℝ}
    (T : StepTowerG d L N κmin) (hm₀ : T.m₀ = 1) {k : ℕ} {hk : 1 ≤ k}
    {N₁ : ℕ} [NeZero N₁] {ν β p₁ : ℝ} (D : StepScaleDataG T k hk N₁ ν β p₁)
    {ϱ : ℝ} (hϱ : ϱ = rhoSepG d L T.m₁) (z : RootIdx d L N₁ T.m₁ (k + 1)) :
    (bridgeFamily 1 (fun _ => Set.univ)
      (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z).Nonempty := by
  subst hϱ
  obtain ⟨hV, -⟩ := D.covers
  rw [hm₀] at hV
  obtain ⟨-, hX, -, -, -, -, hbs⟩ := hV z
  set X := X1 (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ).G' 1 k
    (LocalCover.fam 1 (LocalCover.blockSite k z))
  have hY : X ∈ e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ (rhoSepG d L T.m₁) hk ν β p₁ T.δ) z := by
    unfold e1DomG polyDom polymerDomains
    rw [Finset.mem_image]
    refine ⟨∅, ?_, by simp [Ysites]; rfl⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  have hroot : rootSite z ∈ blockSites d L N₁ T.m₁ (k + 1) k z := by
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
theorem corrF0G_pos {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) {k : ℕ}
    (hk : 1 ≤ k) {β p₁ : ℝ} (hβ : 0 < β) (hp : 0 < p₁) : 0 < corrF0G T k β p₁ := by
  have hb0 : 0 < β * (L : ℝ) ^ (k * (d - 2)) := by
    have := scalePosG T k
    positivity
  have hR := corrRG_pos T hk hb0 hp
  have hE : 0 < EstarG T k := by
    rw [EstarG_eq T (compWeightG_mem T hk)]
    have := EcstG_pos T (compWeightG_mem T hk).1
    have := scalePosG T k
    positivity
  have hK := KmarkG_pos T
  unfold corrF0G
  rw [abs_of_pos hβ]
  positivity

/-- The coefficient of the mark budget depends on the tower only and is nonnegative. -/
theorem cpe_marks_nonnegG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin) :
    0 ≤ CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
      T.κ0 T.κ' := by
  have := one_le_c1 d L
  unfold CPE
  positivity

/-- **The budget of the marks, beyond a threshold in `β`.**  For every scale `k ≥ 1`, every
`p₁ ≤ pLog A₁ p (β L^{k(d-2)})` and every scale datum, the weighted sum over the bridge family of a
root, with the constant `F₀ = corrF0G`, satisfies
`C_PE(K_c′, 2κ_dec − 1, κ₀, κ′) · ∑ F₀ e^{−κ₀ d} ≤ K₀(κ₀)`. -/
theorem corrBudget_fromTowerG {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) :
    ∃ β₀ : ℝ, 1 ≤ β₀ ∧ ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
      ∀ (ν β : ℝ), β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
      p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
      StepScaleDataG T k hk N₁ ν β p₁ →
      ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
        CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
            T.κ0 T.κ' *
          (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
              (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z},
            corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
          K0 d L T.κ0 := by
  have hP := cpe_marks_nonnegG T
  have hε : 0 < 1 / (CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
      (2 * T.κdec - 1) T.κ0 T.κ' + 1) := by positivity
  obtain ⟨β₀, h⟩ := exists_beta0_corrF0_leG T hε hA p
  refine ⟨max 1 β₀, le_max_left _ _, fun k hk N₁ _ hdvd ν β hβ p₁ hp hp₁ D ϱ hϱ z => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le one_pos ((le_max_left _ _).trans hβ)
  have hF := h k hk β ((le_max_right _ _).trans hβ) p₁ hp hp₁
  have hF0 := (corrF0G_pos T hk hβ0 hp).le
  have hdvd1 : L ^ 1 ∣ N₁ := by rwa [hm₀] at hdvd
  have hent := bridgeFamily_entropy (m₀ := 1) (d := d) (L := L) hdvd1
    (by have := T.hL; omega) (reads := fun _ => Set.univ)
    (e1DomG_isDj T hm₀ D hϱ) z T.marks_hκ0 hF0
  have hK := K0_pos d L T.κ0
  refine (mul_le_mul_of_nonneg_left hent hP).trans ?_
  have h1 : corrF0G T k β p₁ * K0 d L T.κ0 ≤
      1 / (CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
        T.κ0 T.κ' + 1) * K0 d L T.κ0 :=
    mul_le_mul_of_nonneg_right hF hK.le
  have h2 : CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
      T.κ0 T.κ' * (1 / (CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
        (2 * T.κdec - 1) T.κ0 T.κ' + 1)) ≤ 1 := by
    rw [mul_one_div, div_le_one (by positivity)]
    linarith
  calc _ ≤ CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
        T.κ0 T.κ' * (1 / (CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
          (2 * T.κdec - 1) T.κ0 T.κ' + 1) * K0 d L T.κ0) :=
        mul_le_mul_of_nonneg_left h1 hP
    _ = (CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
        T.κ0 T.κ' * (1 / (CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0)
          (2 * T.κdec - 1) T.κ0 T.κ' + 1))) * K0 d L T.κ0 := by ring
    _ ≤ 1 * K0 d L T.κ0 := mul_le_mul_of_nonneg_right h2 hK.le
    _ = K0 d L T.κ0 := one_mul _

/-- **One threshold for the marks record.**  For any threshold `βa` there is `β₀ ≥ max 3 βa` such
that for every `β ≥ β₀`, every scale `k ≥ 1` and every `0 < p₁ ≤ pLog A₁ p (β L^{k(d-2)})`: the
Cauchy radius satisfies `2 (17/16) ≤ corrRG`, and the budget of the marks holds. -/
theorem exists_beta0_e1G {d L N : ℕ} [NeZero L] {κmin : ℝ} (T : StepTowerG d L N κmin)
    (hm₀ : T.m₀ = 1) {A₁ : ℝ} (hA : 0 < A₁) (p : ℕ) (βa : ℝ) :
    ∃ β₀ : ℝ, max 3 βa ≤ β₀ ∧
      (∀ k : ℕ, 1 ≤ k → ∀ β : ℝ, β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
        p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        2 * (17 / 16 : ℝ) ≤ corrRG T k (β * (L : ℝ) ^ (k * (d - 2))) p₁) ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁], L ^ T.m₀ ∣ N₁ →
        ∀ (ν β : ℝ), β₀ ≤ β → ∀ p₁ : ℝ, 0 < p₁ →
        p₁ ≤ pLog A₁ p (β * (L : ℝ) ^ (k * (d - 2))) →
        StepScaleDataG T k hk N₁ ν β p₁ →
        ∀ {ϱ : ℝ}, ϱ = rhoSepG d L T.m₁ → ∀ z : RootIdx d L N₁ T.m₁ (k + 1),
          CPE d L (2 * (K0 d L T.κ0 + 1) + rootUnionK d L T.m₀ T.m₁ T.κ0) (2 * T.κdec - 1)
              T.κ0 T.κ' *
            (∑ Y' : {Y' // Y' ∈ bridgeFamily 1 (fun _ => Set.univ)
                (e1DomG (hatStepKG (d := d) (L := L) (N₁ := N₁) T.hN k T.m₁ ϱ hk ν β p₁ T.δ)) z},
              corrF0G T k β p₁ * Real.exp (-T.κ0 * treeLenCovOne 1 (k + 1) Y'.1)) ≤
            K0 d L T.κ0 := by
  obtain ⟨βR, hR⟩ := exists_beta0_corrRG T hA p
  obtain ⟨βF, -, hF⟩ := corrBudget_fromTowerG T hm₀ hA p
  refine ⟨max (max 3 βa) (max βR βF), le_max_left _ _, fun k hk β hβ p₁ hp hp₁ => ?_,
    fun k hk N₁ _ hdvd ν β hβ p₁ hp hp₁ D ϱ hϱ z => ?_⟩
  · exact hR k hk β ((le_max_left _ _).trans ((le_max_right _ _).trans hβ)) p₁ hp hp₁
  · exact hF k hk N₁ hdvd ν β ((le_max_right _ _).trans ((le_max_right _ _).trans hβ)) p₁ hp hp₁
      D hϱ z

end Balaban.Inhabited
