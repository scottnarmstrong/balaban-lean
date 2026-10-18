/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusCubeLift

/-!
# Sites, layers, blocks and adjacency of two agreeing generating sets

For generating sets `G₁`, `G₂` that agree on the box (`GenAgree`), corresponding sites
(`PtCorr`) have the same membership in `Ω_n`, the same layer index, are both or neither in the
data sites and the collar, and have corresponding blocks and neighbours. Hence the interface
pairs (`IsInterfacePair`) of the two correspond.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background

section Basic

variable {d : ℕ}

theorem ptCorr_symm {m₁ m₂ : ℕ} {c : Fin d → ℤ} {x₁ : Torus d m₁} {x₂ : Torus d m₂}
    (h : PtCorr c x₁ x₂) : PtCorr c x₂ x₁ :=
  ⟨h.1.symm, by rw [← h.1]; exact h.2.symm⟩

theorem ptCorr_eq_transp {m₁ m₂ : ℕ} {c : Fin d → ℤ} {x₁ : Torus d m₁} {x₂ : Torus d m₂}
    (h : PtCorr c x₁ x₂) : x₂ = transp m₂ c x₁ := by
  unfold transp
  rw [h.1, zcast_liftNear]

theorem ptCorr_right_unique {m₁ m₂ : ℕ} {c : Fin d → ℤ} {x₁ : Torus d m₁} {x₂ x₂' : Torus d m₂}
    (h : PtCorr c x₁ x₂) (h' : PtCorr c x₁ x₂') : x₂ = x₂' := by
  rw [ptCorr_eq_transp h, ptCorr_eq_transp h']

theorem ptCorr_left_unique {m₁ m₂ : ℕ} {c : Fin d → ℤ} {x₁ x₁' : Torus d m₁} {x₂ : Torus d m₂}
    (h : PtCorr c x₁ x₂) (h' : PtCorr c x₁' x₂) : x₁ = x₁' :=
  ptCorr_right_unique (ptCorr_symm h) (ptCorr_symm h')

/-- A site whose representative lies in the box has a corresponding site. -/
theorem ptCorr_transp {m₁ m₂ : ℕ} {c : Fin d → ℤ} {x : Torus d m₁}
    (hx : InBox m₁ m₂ c (liftNear c x)) [NeZero m₁] [NeZero m₂] :
    PtCorr c x (transp m₂ c x) := by
  refine ⟨?_, hx⟩
  unfold transp
  rw [hx.liftNear_zcast₂]

end Basic

section Sites

variable {d L N₁ N₂ k : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {c : Fin d → ℤ}

theorem GenAgree.omega_iff (hA : GenAgree G₁ G₂ c) {n : ℕ} (h1 : 1 ≤ n) (h2 : n ≤ k + 1)
    {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    x₁ ∈ G₁.Ω n ↔ x₂ ∈ G₂.Ω n := by
  obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  exact hA.agree n h1 h2 w hw

theorem GenAgree.layer_ptCorr (hA : GenAgree G₁ G₂ c) {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k)
    {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    x₁ ∈ G₁.layer j ↔ x₂ ∈ G₂.layer j := by
  rw [G₁.mem_layer, G₂.mem_layer, hA.omega_iff h1 (by omega) hp,
    hA.omega_iff (by omega) (by omega) hp]

theorem GenAgree.layerIndex_ptCorr (hA : GenAgree G₁ G₂ c) {x₁ : Torus d (N₁ * L ^ k)}
    {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    G₂.layerIndex x₂ = G₁.layerIndex x₁ := by
  by_cases hx : x₁ ∈ G₁.Ω 1
  · obtain ⟨h1, h2, h3⟩ := G₁.layerIndex_spec hx
    exact G₂.layerIndex_eq h1 h2 ((hA.layer_ptCorr h1 h2 hp).1 h3)
  · have hx2 : x₂ ∉ G₂.Ω 1 := fun h => hx ((hA.omega_iff le_rfl (by omega) hp).2 h)
    rw [layerIndex_of_not_mem G₁ hx, layerIndex_of_not_mem G₂ hx2]

theorem GenAgree.dataSites_ptCorr_imp (hA : GenAgree G₁ G₂ c) {x₁ : Torus d (N₁ * L ^ k)}
    {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) (hx : x₁ ∈ dataSites G₁) :
    x₂ ∈ dataSites G₂ := by
  have hb := hA.inBoxK1_of_dataSites hx
  obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
  rw [hw.liftNear_zcast₁] at hb
  exact (hA.dataSites_iff hb).1 hx

theorem GenAgree.dataSites_ptCorr (hA : GenAgree G₁ G₂ c) {x₁ : Torus d (N₁ * L ^ k)}
    {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    x₁ ∈ dataSites G₁ ↔ x₂ ∈ dataSites G₂ :=
  ⟨hA.dataSites_ptCorr_imp hp, hA.symm.dataSites_ptCorr_imp (ptCorr_symm hp)⟩

theorem GenAgree.collar_ptCorr (hA : GenAgree G₁ G₂ c) {x₁ : Torus d (N₁ * L ^ k)}
    {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂) :
    x₁ ∈ collar G₁ ↔ x₂ ∈ collar G₂ := by
  have h := hA.dataSites_ptCorr hp
  have h' := hA.omega_iff le_rfl (by omega) hp
  rw [mem_dataSites, mem_dataSites] at h
  constructor
  · intro hc
    rcases h.1 (Or.inr hc) with h2 | h2
    · exact absurd ((mem_collar G₁).1 hc).1 (fun hn => hn (h'.2 h2))
    · exact h2
  · intro hc
    rcases h.2 (Or.inr hc) with h2 | h2
    · exact absurd ((mem_collar G₂).1 hc).1 (fun hn => hn (h'.1 h2))
    · exact h2

theorem adj_ptCorr {x₁ y₁ : Torus d (N₁ * L ^ k)}
    {x₂ y₂ : Torus d (N₂ * L ^ k)} (hx : PtCorr c x₁ x₂) (hy : PtCorr c y₁ y₂)
    (hm : InBoxK 1 (N₁ * L ^ k) (N₂ * L ^ k) c (liftNear c x₁)) : Adj x₁ y₁ ↔ Adj x₂ y₂ := by
  have ex := ptCorr_eq_transp hx
  have ey := ptCorr_eq_transp hy
  subst ex ey
  have hyb := hy.2
  unfold Adj
  refine exists_congr fun μ => ?_
  have h1 := transp_shift_iff hm hyb μ
  have h2 := transp_shift_iff' hm hyb μ
  rw [h1]
  have h3 : transp (N₂ * L ^ k) c x₁ = transp (N₂ * L ^ k) c y₁ + Pi.single μ 1 ↔
      transp (N₂ * L ^ k) c y₁ = transp (N₂ * L ^ k) c x₁ - Pi.single μ 1 := by
    constructor <;> intro h <;> rw [h] <;> abel
  have h4 : x₁ = y₁ + Pi.single μ 1 ↔ y₁ = x₁ - Pi.single μ 1 := by
    constructor <;> intro h <;> rw [h] <;> abel
  rw [h3, h4, h2]

theorem blk_ptCorr (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂) {j : ℕ}
    (hj : j ≤ k) {x₁ y₁ : Torus d (N₁ * L ^ k)} {x₂ y₂ : Torus d (N₂ * L ^ k)}
    (hx : PtCorr c x₁ x₂) (hy : PtCorr c y₁ y₂) :
    y₁ ∈ G₁.blk j x₁ ↔ y₂ ∈ G₂.blk j x₂ := by
  obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hx
  obtain ⟨v, hv, rfl, rfl⟩ := ptCorr_iff_exists.1 hy
  rw [GeneratingSet.mem_blk, GeneratingSet.mem_blk, jBlock_zcast_iff hN₁ hj hv hw,
    jBlock_zcast_iff hN₂ hj hv.symm hw.symm]

theorem GenAgree.mem_blockSet_ptCorr (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {x₁ y₁ : Torus d (N₁ * L ^ k)} {x₂ y₂ : Torus d (N₂ * L ^ k)} (hx : PtCorr c x₁ x₂)
    (hy : PtCorr c y₁ y₂) : y₁ ∈ blockSet G₁ x₁ ↔ y₂ ∈ blockSet G₂ x₂ := by
  unfold blockSet
  by_cases h1 : x₁ ∈ G₁.Ω 1
  · have h2 : x₂ ∈ G₂.Ω 1 := (hA.omega_iff le_rfl (by omega) hx).1 h1
    simp only [h1, h2, ↓reduceIte]
    rw [← hA.layerIndex_ptCorr hx]
    exact blk_ptCorr hN₁ hN₂ (G₂.layerIndex_spec h2).2.1 hx hy
  · have h2 : x₂ ∉ G₂.Ω 1 := fun h => h1 ((hA.omega_iff le_rfl (by omega) hx).2 h)
    simp only [h1, h2, ↓reduceIte, Finset.mem_singleton]
    constructor
    · rintro rfl; exact ptCorr_right_unique hy hx
    · rintro rfl; exact ptCorr_left_unique hy hx

theorem mem_dataSites_of_blockSet {x y : Torus d (N₁ * L ^ k)}
    (hx : x ∈ dataSites G₁) (hy : y ∈ blockSet G₁ x) : y ∈ dataSites G₁ := by
  unfold blockSet at hy
  by_cases h : x ∈ G₁.Ω 1
  · simp only [h, ↓reduceIte] at hy
    obtain ⟨h1, h2, h3⟩ := G₁.layerIndex_spec h
    exact (mem_dataSites G₁).2 (Or.inl (G₁.layer_subset h1 h2 (mem_layer_of_mem_blk G₁ h1 h2 h3 hy)))
  · simp only [h, ↓reduceIte, Finset.mem_singleton] at hy
    rw [hy]; exact hx

theorem GenAgree.interface_imp (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {x₁ y₁ : Torus d (N₁ * L ^ k)} {x₂ y₂ : Torus d (N₂ * L ^ k)} (hx : PtCorr c x₁ x₂)
    (hy : PtCorr c y₁ y₂) (h : IsInterfacePair G₁ x₁ y₁) : IsInterfacePair G₂ x₂ y₂ := by
  obtain ⟨hxd, hyd, hl, a, ha, b, hb, hab⟩ := h
  have hli := hA.layerIndex_ptCorr hx
  have hli' := hA.layerIndex_ptCorr hy
  refine ⟨(hA.dataSites_ptCorr hx).1 hxd, (hA.dataSites_ptCorr hy).1 hyd, ?_, ?_⟩
  · rw [hli, hli']; exact hl
  · have had := mem_dataSites_of_blockSet hxd ha
    have hbd := mem_dataSites_of_blockSet hyd hb
    have ha' := ptCorr_transp (m₂ := N₂ * L ^ k) (hA.inBoxK1_of_dataSites had).inBox
    have hb' := ptCorr_transp (m₂ := N₂ * L ^ k) (hA.inBoxK1_of_dataSites hbd).inBox
    refine ⟨_, (hA.mem_blockSet_ptCorr hN₁ hN₂ hx ha').1 ha, _,
      (hA.mem_blockSet_ptCorr hN₁ hN₂ hy hb').1 hb, ?_⟩
    exact (adj_ptCorr ha' hb' (hA.inBoxK1_of_dataSites had)).1 hab

theorem GenAgree.interface_ptCorr (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {x₁ y₁ : Torus d (N₁ * L ^ k)} {x₂ y₂ : Torus d (N₂ * L ^ k)} (hx : PtCorr c x₁ x₂)
    (hy : PtCorr c y₁ y₂) : IsInterfacePair G₁ x₁ y₁ ↔ IsInterfacePair G₂ x₂ y₂ :=
  ⟨hA.interface_imp hN₁ hN₂ hx hy,
    hA.symm.interface_imp hN₂ hN₁ (ptCorr_symm hx) (ptCorr_symm hy)⟩

end Sites

end Balaban.RootFSpine
