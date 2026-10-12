/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroFinal
public import Balaban.SmallField.Def6Terms
public import Balaban.Fluctuation.StepRegUnit
public import Balaban.LargeField.R.SmallFactorAction
public import Balaban.Localization.CompWeightAdmissible
public import Balaban.Fluctuation.CriticalPoint
public import Balaban.Inhabited.XiCDomains

/-!
# A concrete instance of the hypotheses of `psiZero_exists_unique` (Lemma III.3.3)

For every `d ≥ 3`, `L ≥ 3`, `k ≥ 2`, `N₀ = N₁ L^{m₁} ≥ 5`: the whole-level generating set `levelGS k`, the box
`box 0 (2,…,2)` (`2^d` blocks) with its layer `shellOut`, `X = univ`, `N = 2`, `a ≡ 1`, `ϱ = bgR0 d L`, mass `0`,
and the constant block datum `ψ_k ≡ e₀`.  The concrete instance is `d = 3`, `L = 3`, `N₁ = 6`, `m₁ = 0`, `k = 2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField.Def6 Balaban.Fluctuation
  Balaban.Inhabited

section Generic

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The block datum equal to the constant unit vector. -/
noncomputable def constBlock (hN : 0 < N) : BlockField d L N₀ k N := fun _ => unitVec hN

theorem dataR_constBlock (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) :
    dataR G (constBlock (d := d) (L := L) (N₀ := N₀) (k := k) hN) = unitBg G hN (fun _ => 0) := by
  have h1 : ∀ x i, (dataR G (constBlock (d := d) (L := L) (N₀ := N₀) (k := k) hN)).Ψ x i =
      (unitBg G hN (fun _ => 0)).Ψ x i := by
    intro x i
    by_cases hx : x ∈ dataSites G
    · rw [dataR_Ψ G _ hx, unitBg_Ψ_of_mem G _ _ hx]; rfl
    · simp [dataR, dataC, liftSingle, unitBg, BgData.clip, hx]
  have h2 : ∀ x i, (dataR G (constBlock (d := d) (L := L) (N₀ := N₀) (k := k) hN)).h x i =
      (unitBg G hN (fun _ => 0)).h x i := by
    intro x i
    by_cases hx : x ∈ G.Ω 1
    · rw [unitBg_h_of_mem G _ _ hx]; simpa using dataR_h G _ hx i
    · simp [dataR, dataC, liftSingle, unitBg, BgData.clip, hx]
  cases h : dataR G (constBlock (d := d) (L := L) (N₀ := N₀) (k := k) hN)
  cases h' : unitBg G hN (fun _ => 0)
  rw [h, h'] at h1 h2
  simp only [BgData.mk.injEq]
  exact ⟨funext fun x => funext (h1 x), funext fun x => funext (h2 x)⟩

theorem tube_constBlock (G : GeneratingSet d L N₀ k ϱ) (hN : 0 < N) {δ : ℝ} (hδ : 0 < δ)
    (Y : Set (Torus d (N₀ * L ^ (k - k)))) : TubeOn G Y δ (constBlock hN) := by
  refine ⟨fun x x' _ _ _ => ?_, fun x _ _ => ?_⟩
  · simpa [rn, liftR, constBlock] using hδ
  · simpa [constBlock, sum_sq_unitVec] using hδ

/-- For a whole-level generating set and data in the tube, the constant unit datum has
`effAction = 0`. -/
theorem effAction_constBlock {n : ℕ} (G : GeneratingSet d L N₀ k ϱ) (hG : IsLevel G n) (hN : 0 < N)
    {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (H : BgHyp d L k ϱ a 0) :
    effAction G a (constBlock (d := d) (L := L) (N₀ := N₀) (k := k) hN) = 0 := by
  have hc1 : 0 < bgC1 d L N := Balaban.Localization.bgC1_pos' (d := d) (L := L) (N := N) (by have := H.hd; omega)
  have hD : InUnionDomainR G (bgC1 d L N) 0 (unitBg G hN (fun _ => 0)) := by
    rw [← dataR_constBlock]
    exact inUnionDomainR_of_tube G hc1 le_rfl (tube_constBlock G hN hc1 Set.univ)
  unfold effAction
  rw [dataR_constBlock, bgField_unitBg hG hN ha _ H hD]
  exact action_unitBg_eq_zero hG hN a _

end Generic

namespace PsiZeroWitness

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- The separation parameter. -/
noncomputable def ϱ (d L : ℕ) : ℝ := bgR0 d L

/-- The whole-level generating set at level `k`. -/
noncomputable def G (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] : GeneratingSet d L (N₁ * L ^ m₁) k (ϱ d L) :=
  levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ d L) k le_rfl

/-- The weights `a = compWeight L 1`. -/
noncomputable def a (L : ℕ) : ℕ → ℝ := compWeight L 1

/-- The corner of the box. -/
def b0 (d L N₁ m₁ k : ℕ) : Torus d (N₁ * L ^ m₁ * L ^ (k - k)) := fun _ => 0

/-- The side lengths of the box. -/
def w (d : ℕ) : Fin d → ℕ := fun _ => 2

/-- The region `X`. -/
def X (d L N₁ m₁ k : ℕ) : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k))) := Set.univ

theorem hw1 (d : ℕ) : ∀ i, 1 ≤ w d i := fun _ => by simp [w]
theorem hwD (d : ℕ) : ∀ i, w d i ≤ 2 := fun _ => by simp [w]
theorem hm (hN : 4 ≤ N₁) : 2 + 2 ≤ N₁ * L ^ m₁ * L ^ (k - k) := by
  have : 1 ≤ L ^ m₁ := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  simp only [Nat.sub_self, pow_zero, mul_one]
  nlinarith
theorem hXreg (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    box (b0 d L N₁ m₁ k) (w d) ∪ shellOut (box (b0 d L N₁ m₁ k) (w d)) ⊆ X d L N₁ m₁ k :=
  fun _ _ => Set.mem_univ _
theorem hΩ (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    OverTop (G d L N₁ m₁ k) (box (b0 d L N₁ m₁ k) (w d) ∪ shellOut (box (b0 d L N₁ m₁ k) (w d))) := by
  intro x _
  simp [G, levelGS]
theorem hdata (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    ∀ x ∈ dataSites (G d L N₁ m₁ k), jBlock d L (N₁ * L ^ m₁) k k x ∈ X d L N₁ m₁ k :=
  fun _ _ => Set.mem_univ _
theorem H (hd : 3 ≤ d) (hL : 3 ≤ L) : BgHyp d L k (ϱ d L) (a L) 0 where
  hd := hd
  hL := hL
  hϱ := le_rfl
  weights := isAdmissibleWeights_compWeight hL (by norm_num) (by norm_num) k
  mass := le_rfl
  massLe := by simp

theorem isLevel_G (hk : 1 ≤ k) : IsLevel (G d L N₁ m₁ k) k := isLevel_levelGS hk le_rfl

theorem box_nonempty (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] :
    (box (b0 d L N₁ m₁ k) (w d)).Nonempty :=
  ⟨b0 d L N₁ m₁ k, fun i => ⟨0, by simp [w], by simp⟩⟩

/-- The constant block datum `e₀ = (1, 0)`. -/
noncomputable def ψk (d L N₁ m₁ k : ℕ) [NeZero L] [NeZero N₁] : BlockField d L (N₁ * L ^ m₁) k 2 :=
  constBlock (by norm_num)

theorem tube_ψk {δ : ℝ} (hδ : 0 < δ) (Y : Set (Torus d (N₁ * L ^ m₁ * L ^ (k - k)))) :
    TubeOn (G d L N₁ m₁ k) Y δ (ψk d L N₁ m₁ k) := tube_constBlock _ _ hδ Y

/-- **The hypotheses of `psiZero_exists_unique` are jointly satisfied by a nonempty box**, and the
conclusion holds at the instance, with a datum in the tube at every admissible `δ`. -/
theorem psiZero_hyps_nonempty (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) :
    (box (b0 d L N₁ m₁ k) (w d)).Nonempty ∧ ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
      TubeOn (G d L N₁ m₁ k) (X d L N₁ m₁ k \ box (b0 d L N₁ m₁ k) (w d)) δ (ψk d L N₁ m₁ k) ∧
      ∃! ψ, PsiZeroSol (G d L N₁ m₁ k) (a L) (b0 d L N₁ m₁ k) (w d) (X d L N₁ m₁ k) (K * δ)
        (ψk d L N₁ m₁ k) ψ := by
  obtain ⟨K, c11, hK, hc, h⟩ := psiZero_exists_unique (N := 2) (D := 2) (G d L N₁ m₁ k) (a L)
    (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k)
    (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)
  exact ⟨box_nonempty d L N₁ m₁ k, K, c11, hK, hc, fun δ h0 h1 =>
    ⟨tube_ψk h0 _, h δ h0 h1 _ (tube_ψk h0 _)⟩⟩

/-- The concrete instance: `d = 3`, `L = 3`, `N₀ = 6`, `k = 2`. -/
theorem psiZero_hyps_nonempty_concrete :
    (box (b0 3 3 6 0 2) (w 3)).Nonempty ∧ ∃ K c11 : ℝ, 0 < K ∧ 0 < c11 ∧ ∀ δ : ℝ, 0 < δ → δ ≤ c11 →
      TubeOn (G 3 3 6 0 2) (X 3 3 6 0 2 \ box (b0 3 3 6 0 2) (w 3)) δ (ψk 3 3 6 0 2) ∧
      ∃! ψ, PsiZeroSol (G 3 3 6 0 2) (a 3) (b0 3 3 6 0 2) (w 3) (X 3 3 6 0 2) (K * δ) (ψk 3 3 6 0 2) ψ :=
  psiZero_hyps_nonempty (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The constant datum is a solution of (2.34) in every tube. -/
theorem sol_ψk (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hk : 1 ≤ k) {κ : ℝ} (hκ : 0 < κ) :
    PsiZeroSol (G d L N₁ m₁ k) (a L) (b0 d L N₁ m₁ k) (w d) (X d L N₁ m₁ k) κ (ψk d L N₁ m₁ k)
      (ψk d L N₁ m₁ k) := by
  refine ⟨tube_ψk hκ _, fun _ _ => rfl, fun ψ' _ _ => ?_⟩
  have h0 : effAction (G d L N₁ m₁ k) (a L) (ψk d L N₁ m₁ k) = 0 :=
    effAction_constBlock _ (isLevel_G hk) _ (fun _ => compWeight_nonneg (by omega) one_pos _) (H hd3 hL)
  rw [h0]
  exact action_nonneg_of (fun _ => compWeight_nonneg (by omega) one_pos _) le_rfl _ _

/-- **The minimizer `ψ⁰_k` for the constant datum is the constant configuration.** -/
theorem psiZero_ψk (hd3 : 3 ≤ d) (hL : 3 ≤ L) (hN : 4 ≤ N₁) (hk : 1 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
      (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL)) :
    psiZero 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
      (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc
      (tube_ψk hδ _) = ψk d L N₁ m₁ k :=
  ((psiZero_spec 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d) (hw1 d) (hwD d)
      (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k) (H hd3 hL) hδ hδc
      (tube_ψk hδ _)).2 _
    (sol_ψk hd3 hL hk (mul_pos (psiZeroK_pos 2 (G d L N₁ m₁ k) (a L) (by omega) hk (b0 d L N₁ m₁ k) (w d)
      (hw1 d) (hwD d) (hm hN) (hXreg d L N₁ m₁ k) (hΩ d L N₁ m₁ k) (hdata d L N₁ m₁ k)
      (H hd3 hL)) hδ))).symm

end PsiZeroWitness

end Balaban.LargeField
