/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusRegDomain

/-!
# The background field, its extension and the block average at corresponding sites

For generating sets and data that agree on the box: the multiplier `bgMultC`, the extension
`barVec` of the background by the data, the block average `blockAvg` and the deviation
`blockDev` of two tori agree at corresponding sites (`PtCorr`).
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

/-- The value of "the unique solution, if any" is transported along a bijection of the
solution spaces. -/
theorem dite_unique_equiv {X Y β : Type*} [Zero β] (σ : X → Y) (hσ : Function.Bijective σ)
    (P : X → Prop) (Q : Y → Prop) (hPQ : ∀ s, Q (σ s) ↔ P s) (f : X → β) (g : Y → β)
    (hfg : ∀ s, g (σ s) = f s) :
    (open Classical in if H : ∃! t, Q t then g H.exists.choose else 0) =
      (open Classical in if H : ∃! s, P s then f H.exists.choose else 0) := by
  classical
  by_cases H : ∃! s, P s
  · have H' : ∃! t, Q t := by
      obtain ⟨s, hs, hu⟩ := H
      exact ⟨σ s, (hPQ s).2 hs, fun t ht => by
        obtain ⟨s', rfl⟩ := hσ.2 t
        rw [hu s' ((hPQ s').1 ht)]⟩
    have hspec := H.exists.choose_spec
    have e2 : H'.exists.choose = σ H.exists.choose :=
      H'.unique H'.exists.choose_spec ((hPQ _).2 hspec)
    simp only [H, H', ↓reduceDIte]
    rw [e2, hfg]
  · have H' : ¬ ∃! t, Q t := by
      rintro ⟨t, ht, hu⟩
      obtain ⟨s, rfl⟩ := hσ.2 t
      exact H ⟨s, (hPQ s).1 ht, fun s' hs' => hσ.1 (hu (σ s') ((hPQ s').2 hs'))⟩
    simp only [H, H', ↓reduceDIte]

section Shift

variable {d : ℕ} {m₁ m₂ : ℕ} {c : Fin d → ℤ} {x₁ : Torus d m₁} {x₂ : Torus d m₂}

theorem ptCorr_add_single [NeZero m₁] [NeZero m₂] (hp : PtCorr c x₁ x₂)
    (hm : InBoxK 1 m₁ m₂ c (liftNear c x₁)) (μ : Fin d) :
    PtCorr c (x₁ + Pi.single μ 1) (x₂ + Pi.single μ 1) := by
  obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  rw [hw.liftNear_zcast₁] at hm
  rw [← zcast_add_single, ← zcast_add_single]
  exact ptCorr_zcast (hm.add_single μ).inBox

theorem ptCorr_sub_single [NeZero m₁] [NeZero m₂] (hp : PtCorr c x₁ x₂)
    (hm : InBoxK 1 m₁ m₂ c (liftNear c x₁)) (μ : Fin d) :
    PtCorr c (x₁ - Pi.single μ 1) (x₂ - Pi.single μ 1) := by
  obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  rw [hw.liftNear_zcast₁] at hm
  rw [← zcast_sub_single, ← zcast_sub_single]
  exact ptCorr_zcast (hm.sub_single μ).inBox

end Shift

section Blocks

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem jBlock_zero_inj {x y : Torus d (N₀ * L ^ k)}
    (h : jBlock d L N₀ k 0 x = jBlock d L N₀ k 0 y) : x = y := by
  funext i
  have := congrFun h i
  unfold jBlock blockMap blockCoord at this
  simp only [pow_zero, Nat.div_one] at this
  have h2 : ((x i).val : ZMod (N₀ * L ^ k)) = ((y i).val : ZMod (N₀ * L ^ k)) := this
  rwa [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val] at h2

theorem blk_zero (G : GeneratingSet d L N₀ k ϱ) (x : Torus d (N₀ * L ^ k)) :
    G.blk 0 x = {x} := by
  ext y
  rw [GeneratingSet.mem_blk, Finset.mem_singleton]
  exact ⟨jBlock_zero_inj, fun h => by rw [h]⟩

end Blocks

section Field

variable {d L N₁ N₂ k Nv : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {c : Fin d → ℤ}
  {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv}

/-- **The multiplier of the Def-5 background of two tori agrees on the box.** -/
theorem GenAgree.bgMultC_eq (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂)
    (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) (a : ℕ → ℝ) (ν c₀ : ℝ) (x : G₁.Ω 1) :
    bgMultC G₂ a ν c₀ D₂ (hA.equiv x) = bgMultC G₁ a ν c₀ D₁ x := by
  classical
  have hF := fun x y : G₁.Ω 1 => hA.fullMatrix_eq hN₁ hN₂ a ν x y
  have hS := fun (x : G₁.Ω 1) (i : Fin Nv) => hA.source_eq hD a ν x i
  have hsp := fun x : G₁.Ω 1 => hA.spacing_eq x
  have hiff : ∀ s, IsSmallSolution G₂ a ν c₀ D₂ (solMap hA.equiv s).1 (solMap hA.equiv s).2 ↔
      IsSmallSolution G₁ a ν c₀ D₁ s.1 s.2 := fun s =>
    isSmallSolution_equiv_iff hA.equiv hF hS hsp s.1 s.2
  have hσ : Function.Bijective (solMap (N := Nv) hA.equiv) :=
    ⟨solMap_injective hA.equiv, solMap_surjective hA.equiv⟩
  unfold bgMultC
  rw [dite_apply, dite_apply]
  exact dite_unique_equiv (solMap hA.equiv) hσ _ _ hiff (fun s => s.2 x)
    (fun t => t.2 (hA.equiv x)) (fun s => by simp [solMap])

theorem GenAgree.bgFieldC_ptCorr (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂)
    (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) (a : ℕ → ℝ) (ν c₀ : ℝ) {y₁ : G₁.Ω 1} {y₂ : G₂.Ω 1}
    (hp : PtCorr c y₁.1 y₂.1) (i : Fin Nv) :
    bgFieldC G₂ a ν c₀ D₂ (y₂, i) = bgFieldC G₁ a ν c₀ D₁ (y₁, i) := by
  have : hA.equiv y₁ = y₂ := Subtype.ext (by rw [hA.equiv_coe]; exact (ptCorr_eq_transp hp).symm)
  rw [← this]
  exact hA.bgFieldC_eq hD hN₁ hN₂ a ν c₀ y₁ i

theorem GenAgree.bgMultC_ptCorr (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂)
    (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) (a : ℕ → ℝ) (ν c₀ : ℝ) {y₁ : G₁.Ω 1} {y₂ : G₂.Ω 1}
    (hp : PtCorr c y₁.1 y₂.1) :
    bgMultC G₂ a ν c₀ D₂ y₂ = bgMultC G₁ a ν c₀ D₁ y₁ := by
  have : hA.equiv y₁ = y₂ := Subtype.ext (by rw [hA.equiv_coe]; exact (ptCorr_eq_transp hp).symm)
  rw [← this]
  exact hA.bgMultC_eq hD hN₁ hN₂ a ν c₀ y₁

/-- The extension `φ̄` of the background by the data agrees at corresponding sites. -/
theorem GenAgree.barVec_ptCorr (hA : GenAgree G₁ G₂ c) (hD : DataAgree G₁ G₂ c D₁ D₂)
    (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) (a : ℕ → ℝ) (ν c₀ : ℝ) {x₁ : Torus d (N₁ * L ^ k)}
    {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    Balaban.LargeField.barVec G₂ D₂ (bgFieldC G₂ a ν c₀ D₂) x₂ = Balaban.LargeField.barVec G₁ D₁ (bgFieldC G₁ a ν c₀ D₁) x₁ := by
  funext i
  unfold Balaban.LargeField.barVec barField
  by_cases h1 : x₁ ∈ G₁.Ω 1
  · have h2 : x₂ ∈ G₂.Ω 1 := (hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).1 h1
    simp only [h1, h2, ↓reduceDIte]
    exact hA.bgFieldC_ptCorr hD hN₁ hN₂ a ν c₀ (y₁ := ⟨x₁, h1⟩) (y₂ := ⟨x₂, h2⟩) hp i
  · have h2 : x₂ ∉ G₂.Ω 1 := fun h => h1 ((hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).2 h)
    simp only [h1, h2, ↓reduceDIte]
    exact hD.psi_ptCorr hA hp i

theorem svec_ptCorr (hA : GenAgree G₁ G₂ c) {φ₁ : G₁.Ω 1 × Fin Nv → ℂ} {φ₂ : G₂.Ω 1 × Fin Nv → ℂ}
    (hφ : ∀ (y₁ : G₁.Ω 1) (y₂ : G₂.Ω 1), PtCorr c y₁.1 y₂.1 → ∀ i, φ₂ (y₂, i) = φ₁ (y₁, i))
    {y₁ : Torus d (N₁ * L ^ k)} {y₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c y₁ y₂) :
    svec G₂ φ₂ y₂ = svec G₁ φ₁ y₁ := by
  funext i
  unfold svec zeroExt
  by_cases h1 : y₁ ∈ G₁.Ω 1
  · have h2 : y₂ ∈ G₂.Ω 1 := (hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).1 h1
    simp only [h1, h2, ↓reduceDIte]
    exact hφ ⟨y₁, h1⟩ ⟨y₂, h2⟩ hp i
  · have h2 : y₂ ∉ G₂.Ω 1 := fun h => h1 ((hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).2 h)
    simp only [h1, h2, ↓reduceDIte]

/-- The block average agrees at corresponding sites. -/
theorem GenAgree.blockAvg_ptCorr (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {φ₁ : G₁.Ω 1 × Fin Nv → ℂ} {φ₂ : G₂.Ω 1 × Fin Nv → ℂ}
    (hφ : ∀ (y₁ : G₁.Ω 1) (y₂ : G₂.Ω 1), PtCorr c y₁.1 y₂.1 → ∀ i, φ₂ (y₂, i) = φ₁ (y₁, i))
    {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    blockAvg G₂ φ₂ x₂ = blockAvg G₁ φ₁ x₁ := by
  funext i
  unfold blockAvg
  rw [hA.layerIndex_ptCorr hp]
  congr 1
  by_cases hx : x₁ ∈ G₁.Ω 1
  · have hx2 : x₂ ∈ G₂.Ω 1 := (hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).1 hx
    obtain ⟨h1, h2, h3⟩ := G₁.layerIndex_spec hx
    have hj : G₁.layerIndex x₁ ≤ k := h2
    refine (sum_of_rel (G₁.blk (G₁.layerIndex x₁) x₁) (G₂.blk (G₁.layerIndex x₁) x₂)
      (PtCorr c) (fun y => svec G₁ φ₁ y i) (fun y => svec G₂ φ₂ y i) ?_ ?_
      (fun a b b' h h' => ptCorr_right_unique h h') (fun a a' b h h' => ptCorr_left_unique h h')
      ?_).symm
    · intro y hy
      have hyΩ : y ∈ G₁.Ω 1 := G₁.layer_subset h1 h2 (mem_layer_of_mem_blk G₁ h1 h2 h3 hy)
      have hb := (hA.supp₁ y hyΩ).inBox
      have hq := ptCorr_transp (m₂ := N₂ * L ^ k) hb
      exact ⟨_, (blk_ptCorr (G₁ := G₁) (G₂ := G₂) hN₁ hN₂ hj hp hq).1 hy, hq⟩
    · intro y hy
      have h3' : x₂ ∈ G₂.layer (G₁.layerIndex x₁) := (hA.layer_ptCorr h1 h2 hp).1 h3
      have hyΩ : y ∈ G₂.Ω 1 := G₂.layer_subset h1 h2 (mem_layer_of_mem_blk G₂ h1 h2 h3' hy)
      have hb := (hA.symm.supp₁ y hyΩ).inBox
      have hq := ptCorr_transp (m₂ := N₁ * L ^ k) hb
      exact ⟨_, (blk_ptCorr (G₁ := G₁) (G₂ := G₂) hN₁ hN₂ hj hp (ptCorr_symm hq)).2 hy,
        ptCorr_symm hq⟩
    · intro y₁ y₂ _ _ hq
      exact (congrFun (svec_ptCorr hA hφ hq) i).symm
  · have hx2 : x₂ ∉ G₂.Ω 1 := fun h => hx ((hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).2 h)
    have e1 := layerIndex_of_not_mem G₁ hx
    rw [e1, blk_zero, blk_zero, Finset.sum_singleton, Finset.sum_singleton]
    exact (congrFun (svec_ptCorr hA hφ hp) i)

end Field

end Balaban.RootFSpine
