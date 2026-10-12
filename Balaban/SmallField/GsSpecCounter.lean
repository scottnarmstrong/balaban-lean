/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6v2Inhabited

/-!
# `gs_spec` is too weak: the local and whole-level composed fields differ (RAY-DOMAIN §3)

`Terms.gs j X` is only required (`Def6.IsSF.gs_spec`) to contain `X` in `Ω₁` and to have no layers
above `j`.  `weakTerms` assigns `levelGS 1` to every level-2 polymer; it satisfies both fields
(`weakTerms_gs_spec`), but the composed field on `X` built from it
(`composeField_local_ne_whole`) uses the level-1 block mean, while the whole-level composite
`composedPairAt` (level-2 block mean) differs from it.
-/

@[expose] public section

namespace Balaban.SmallField.GsSpec

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

theorem levelGS_Ω (j : ℕ) (hj : j ≤ k) (i : ℕ) :
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hj).Ω i =
      if i ≤ j then Finset.univ else ∅ := rfl

theorem levelGS_layerIndex {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k) (x : CTorus d L N₁ m₁ k) :
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk).layerIndex x = j :=
  GeneratingSet.layerIndex_eq _ hj1 hjk
    ((GeneratingSet.mem_layer _).2 ⟨by simp [levelGS_Ω], by simp [levelGS_Ω]⟩)

/-- Layers of a whole-level set: only the layer `j`. -/
theorem levelGS_layer_eq {j n : ℕ} (hjk : j ≤ k) {x : CTorus d L N₁ m₁ k}
    (hx : x ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk).layer n) :
    n = j := by
  rw [GeneratingSet.mem_layer, levelGS_Ω, levelGS_Ω] at hx
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have h' : n + 1 ≤ j := by omega
    simp [h', show n ≤ j by omega] at hx
  · have h' : ¬ n ≤ j := by omega
    simp [h'] at hx

/-! ### The weak specification (`gs_spec` of `Def6.IsSF`) admits the level-1 set for a level-2
polymer -/

/-- A `Terms`-style local set that satisfies `gs_spec` but assigns the level-1 whole-lattice
set to every level-2 polymer. -/
noncomputable def weakTerms (d L N₁ m₁ k N : ℕ) [NeZero L] [NeZero N₁] (ϱ : ℝ) :
    Terms d L N₁ m₁ k N ϱ where
  E := fun _ _ _ _ _ => 0
  M := fun _ _ _ _ _ _ => 0
  gs := fun j _ => levelGS (min (if j = 2 then 1 else j) k) (min_le_right _ _)

/-- The two displayed fields of `gs_spec` hold for `weakTerms`. -/
theorem weakTerms_gs_spec (m₀ : ℕ) :
    ∀ j, 1 ≤ j → j ≤ k → ∀ X, IsPolyDom (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j X →
      X ⊆ (((weakTerms d L N₁ m₁ k N ϱ).gs j X).Ω 1 : Set (CTorus d L N₁ m₁ k)) ∧
        ∀ i, j < i → ((weakTerms d L N₁ m₁ k N ϱ).gs j X).Ω i = ∅ := by
  intro j hj1 hjk X _
  have h1 : 1 ≤ min (if j = 2 then 1 else j) k := by split_ifs <;> omega
  have h2 : min (if j = 2 then 1 else j) k ≤ j := by split_ifs <;> omega
  refine ⟨fun x _ => ?_, fun i hi => ?_⟩
  · simp [weakTerms, levelGS_Ω, h1]
  · have : ¬ i ≤ min (if j = 2 then 1 else j) k := by omega
    simp [weakTerms, levelGS_Ω, this]

theorem weakTerms_gs_two (X : Set (CTorus d L N₁ m₁ k)) (hk : 2 ≤ k) :
    (weakTerms d L N₁ m₁ k N ϱ).gs 2 X = levelGS 1 (by omega) := by
  simp only [weakTerms]
  congr 1
  all_goals (try simp)
  all_goals omega


theorem blockMean_indicator (G : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) (n : ℕ)
    (x0 : CTorus d L N₁ m₁ k) :
    blockMean G n (fun y => if y = x0 then (1 : ℂ) else 0) x0 =
      ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) := by
  unfold blockMean
  have : x0 ∈ G.blk n x0 := GeneratingSet.mem_blk.2 rfl
  simp [Finset.sum_ite_eq', this]

/-- **The weakness of `gs_spec`, in the composed field.**  For `k ≥ 2` and a level-2 polymer `X`
the set `weakTerms.gs 2 X = levelGS 1` satisfies the two fields of `gs_spec`
(`weakTerms_gs_spec`), but at `x₀ ∈ X` the composed field built from it differs from the one built
from the whole-level set `levelGS 2` (the datum is the point source `φ'` at `x₀` with the block
average `Ψ'` of level `k`; the first uses the level-1 block mean, the second the level-2 one). -/
theorem composeField_local_ne_whole (hd : 0 < d) (hL : 2 ≤ L) (hk : 2 ≤ k) (a : ℕ → ℝ)
    (i0 : Fin N) (x0 : CTorus d L N₁ m₁ k) {X : Set (CTorus d L N₁ m₁ k)} (m₀ : ℕ)
    (_hX : IsPolyDom m₀ 2 X) (_hx0 : x0 ∈ X) :
    let G' := topGS d L N₁ m₁ k ϱ
    let φ' : G'.Ω 1 × Fin N → ℂ := fun q => if q.1.1 = x0 ∧ q.2 = i0 then 1 else 0
    let Ψ' : CTorus d L N₁ m₁ k → Fin N → ℂ := fun x i =>
      blockMean G' k (fun y => svec G' φ' y i) x
    composeField ((weakTerms d L N₁ m₁ k N ϱ).gs 2 X) G' a φ' Ψ' x0 i0 ≠
      composeField (levelGS 2 (by omega) :
        GeneratingSet d L (N₁ * L ^ m₁) k ϱ) G' a φ' Ψ' x0 i0 := by
  intro G' φ' Ψ'
  have hk1 : 1 ≤ k := by omega
  have hsv : ∀ y, svec G' φ' y i0 = if y = x0 then (1 : ℂ) else 0 := fun y => by
    have hy : y ∈ G'.Ω 1 := by simp [G', topGS, levelGS_Ω, hk1]
    rw [svec_of_mem' _ hy]
    simp [φ']
  have hG'i : ∀ y, G'.layerIndex y = k := fun y => levelGS_layerIndex hk1 le_rfl y
  have key : ∀ (n : ℕ) (hn1 : 1 ≤ n) (hnk : n ≤ k),
      composeField (levelGS n hnk : GeneratingSet d L (N₁ * L ^ m₁) k ϱ) G' a φ' Ψ' x0 i0 =
        ((((((L : ℝ) ^ n) ^ d)⁻¹ : ℝ)) : ℂ) := by
    intro n hn1 hnk
    have hx : x0 ∈ (levelGS n hnk : GeneratingSet d L (N₁ * L ^ m₁) k ϱ).Ω 1 := by
      simp [levelGS_Ω, hn1]
    rw [composeField_of_mem a φ' Ψ' hx, levelGS_layerIndex hn1 hnk]
    have e : Ψ' x0 i0 = blockMean G' (G'.layerIndex x0) (fun y => svec G' φ' y i0) x0 := by
      rw [hG'i]
    rw [← e, sub_self, mul_zero, add_zero]
    simp only [hsv]
    exact blockMean_indicator _ _ _
  rw [weakTerms_gs_two X hk, key 1 le_rfl (by omega), key 2 (by omega) hk]
  intro h
  have h' := Complex.ofReal_injective h
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (by omega : 0 < L)
  have hLgt : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have h1 : ((L : ℝ) ^ 1) ^ d < ((L : ℝ) ^ 2) ^ d := by
    apply pow_lt_pow_left₀ _ (by positivity) hd.ne'
    exact pow_lt_pow_right₀ hLgt (by norm_num)
  have := inv_strictAnti₀ (by positivity) h1
  linarith

/-- **The repaired class excludes the counterexample**: if some level-2 polymer exists and
`k ≥ 2`, `weakTerms` are the terms of no member of `IsSF2` (they violate the clause `gsStrong`
at that polymer: `weakTerms.gs 2 X = levelGS 1` has layer index `1 ≠ 2` on `X`). -/
theorem weakTerms_not_isSF2 (hk : 2 ≤ k) {P : Consts} {Rg : Def6v2.Regime L} {β a : ℕ → ℝ}
    {Dom : Def6v2.FieldDom d L N₁ m₁ k N ϱ}
    {ρd : (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) → (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {Ek : ℝ} {X : Set (CTorus d L N₁ m₁ k)} (hX : IsPolyDom P.m₀ 2 X) (hne : X.Nonempty) :
    ¬ Def6v2.IsSF2 P Rg β a Dom (weakTerms d L N₁ m₁ k N ϱ) ρd Ek := by
  intro h
  obtain ⟨z, hz⟩ := hne
  have hs := h.gsStrong 2 (by norm_num) hk X hX
  have e := hs.layerEq z hz
  rw [weakTerms_gs_two X hk, levelGS_layerIndex (by norm_num) (by omega),
    levelGS_layerIndex (by norm_num) hk] at e
  omega

end Balaban.SmallField.GsSpec
