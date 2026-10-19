/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Background.TwoTorusRegSites
public import Balaban.LargeField.Characteristic.Reg

/-!
# The real data domain of two agreeing generating sets

If `G₁`, `G₂` agree on the box and their data `D₁`, `D₂` agree there, then `D₁ ∈ 𝒟_ℝ(G₁)` iff
`D₂ ∈ 𝒟_ℝ(G₂)` (`GenAgree.inUnionDomainR_iff`). The data agree at all corresponding sites
(`DataAgree.psi_ptCorr`, `DataAgree.h_ptCorr`), not only on the data sites.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField

section Dom

variable {d L N₁ N₂ k Nv : ℕ} [NeZero N₁] [NeZero N₂] [NeZero L] {ϱ₁ ϱ₂ : ℝ}
  {G₁ : GeneratingSet d L N₁ k ϱ₁} {G₂ : GeneratingSet d L N₂ k ϱ₂} {c : Fin d → ℤ}

/-- A data site of `G₂` has a corresponding data site of `G₁`. -/
theorem GenAgree.exists_partner (hA : GenAgree G₁ G₂ c) {x₂ : Torus d (N₂ * L ^ k)}
    (hx : x₂ ∈ dataSites G₂) :
    ∃ x₁, PtCorr c x₁ x₂ ∧ x₁ ∈ dataSites G₁ := by
  have hb := hA.symm.inBoxK1_of_dataSites hx
  have hp := ptCorr_transp (m₂ := N₁ * L ^ k) hb.inBox
  exact ⟨_, ptCorr_symm hp, (hA.dataSites_ptCorr (ptCorr_symm hp)).2 hx⟩

theorem DataAgree.symm (hA : GenAgree G₁ G₂ c) {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv}
    (hD : DataAgree G₁ G₂ c D₁ D₂) : DataAgree G₂ G₁ c D₂ D₁ where
  psi w hw hz i := by
    have hp := ptCorr_zcast (m₁ := N₁ * L ^ k) (m₂ := N₂ * L ^ k) hw.symm
    exact (hD.psi w hw.symm ((hA.dataSites_ptCorr hp).2 hz) i).symm
  h w hw hz i := by
    have hp := ptCorr_zcast (m₁ := N₁ * L ^ k) (m₂ := N₂ * L ^ k) hw.symm
    exact (hD.h w hw.symm ((hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).2 hz) i).symm

theorem DataAgree.psi_ptCorr (hA : GenAgree G₁ G₂ c) {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv}
    (hD : DataAgree G₁ G₂ c D₁ D₂) {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)}
    (hp : PtCorr c x₁ x₂) (i : Fin Nv) : D₂.Ψ x₂ i = D₁.Ψ x₁ i := by
  by_cases hx : x₁ ∈ dataSites G₁
  · obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
    exact (hD.psi w hw hx i).symm
  · have hx2 : x₂ ∉ dataSites G₂ := fun h => hx ((hA.dataSites_ptCorr hp).2 h)
    rw [D₁.Ψ_zero x₁ hx, D₂.Ψ_zero x₂ hx2]

theorem DataAgree.h_ptCorr (hA : GenAgree G₁ G₂ c) {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv}
    (hD : DataAgree G₁ G₂ c D₁ D₂) {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)}
    (hp : PtCorr c x₁ x₂) (i : Fin Nv) : D₂.h x₂ i = D₁.h x₁ i := by
  by_cases hx : x₁ ∈ G₁.Ω 1
  · obtain ⟨w, hw, rfl, rfl⟩ := ptCorr_iff_exists.1 hp
    exact (hD.h w hw hx i).symm
  · have hx2 : x₂ ∉ G₂.Ω 1 := fun h => hx ((hA.omega_iff le_rfl (Nat.le_add_left 1 k) hp).2 h)
    rw [D₁.h_zero x₁ hx, D₂.h_zero x₂ hx2]

open Classical in
/-- The datum `Ψ` of `G₁` transported to `G₂` along the box. -/
noncomputable def transpData (G₂ : GeneratingSet d L N₂ k ϱ₂) (c : Fin d → ℤ)
    (Ψ : Torus d (N₁ * L ^ k) → Fin Nv → ℝ) : Torus d (N₂ * L ^ k) → Fin Nv → ℝ :=
  fun x => if x ∈ dataSites G₂ then Ψ (transp (N₁ * L ^ k) c x) else 0

omit [NeZero N₁] in
theorem transpData_eq (Ψ : Torus d (N₁ * L ^ k) → Fin Nv → ℝ)
    {x₁ : Torus d (N₁ * L ^ k)} {x₂ : Torus d (N₂ * L ^ k)} (hp : PtCorr c x₁ x₂)
    (hx : x₂ ∈ dataSites G₂) : transpData G₂ c Ψ x₂ = Ψ x₁ := by
  unfold transpData
  simp only [hx, ↓reduceIte]
  rw [← ptCorr_eq_transp (ptCorr_symm hp)]

theorem GenAgree.inPsiTilde_transport (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {ν δ : ℝ} {Ψ : Torus d (N₁ * L ^ k) → Fin Nv → ℝ} {h : Fin Nv → ℝ}
    (hP : InPsiTilde G₁ ν δ Ψ h) : InPsiTilde G₂ ν δ (transpData G₂ c Ψ) h where
  layerConst := by
    intro n hn1 hnk x hx x' hx'
    have hxl := hx
    have hx'l : x' ∈ G₂.layer n := mem_layer_of_mem_blk G₂ hn1 hnk hx hx'
    have hxd : x ∈ dataSites G₂ :=
      (mem_dataSites G₂).2 (Or.inl (G₂.layer_subset hn1 hnk hx))
    have hx'd : x' ∈ dataSites G₂ :=
      (mem_dataSites G₂).2 (Or.inl (G₂.layer_subset hn1 hnk hx'l))
    obtain ⟨y, hy, -⟩ := hA.exists_partner hxd
    obtain ⟨y', hy', -⟩ := hA.exists_partner hx'd
    rw [transpData_eq Ψ hy hxd, transpData_eq Ψ hy' hx'd]
    have hl := (hA.layer_ptCorr hn1 hnk hy).2 hxl
    have hb := (blk_ptCorr (G₁ := G₁) (G₂ := G₂) hN₁ hN₂ hnk hy hy').2 (G₂.mem_blk.2
      (GeneratingSet.mem_blk.1 hx'))
    exact hP.layerConst n hn1 hnk y hl y' hb
  r1 := by
    intro x x' hxx
    obtain ⟨hxd, hx'd, -⟩ := id hxx
    obtain ⟨y, hy, -⟩ := hA.exists_partner hxd
    obtain ⟨y', hy', -⟩ := hA.exists_partner hx'd
    rw [transpData_eq Ψ hy hxd, transpData_eq Ψ hy' hx'd]
    exact hP.r1 y y' ((hA.interface_ptCorr hN₁ hN₂ hy hy').2 hxx)
  r2 := by
    intro x hx
    obtain ⟨y, hy, -⟩ := hA.exists_partner hx
    simp only [transpData_eq Ψ hy hx]
    exact hP.r2 y ((hA.dataSites_ptCorr hy).2 hx)
  r3 := by
    intro x hx
    obtain ⟨y, hy, hyd⟩ := hA.exists_partner hx
    simp only [transpData_eq Ψ hy hx]
    rw [hA.layerIndex_ptCorr hy]
    exact hP.r3 y hyd
  r4 := hP.r4

theorem GenAgree.inUnionDomainR_imp (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv} (hD : DataAgree G₁ G₂ c D₁ D₂) {c₁ ν : ℝ}
    (h : InUnionDomainR G₁ c₁ ν D₁) : InUnionDomainR G₂ c₁ ν D₂ := by
  obtain ⟨δ, h0, hc, Ψ, hh, hP, hΨ, hhh⟩ := h
  refine ⟨δ, h0, hc, transpData G₂ c Ψ, hh, hA.inPsiTilde_transport hN₁ hN₂ hP, ?_, ?_⟩
  · intro x hx i
    obtain ⟨y, hy, hyd⟩ := hA.exists_partner hx
    rw [transpData_eq Ψ hy hx, hD.psi_ptCorr hA hy, hΨ y hyd i]
  · intro x hx i
    obtain ⟨y, hy, hyd⟩ := hA.exists_partner ((mem_dataSites G₂).2 (Or.inl hx))
    have hyΩ : y ∈ G₁.Ω 1 := (hA.omega_iff le_rfl (Nat.le_add_left 1 k) hy).2 hx
    rw [hD.h_ptCorr hA hy, hhh y hyΩ i]

theorem GenAgree.inUnionDomainR_iff (hA : GenAgree G₁ G₂ c) (hN₁ : 2 ≤ N₁) (hN₂ : 2 ≤ N₂)
    {D₁ : BgData G₁ Nv} {D₂ : BgData G₂ Nv} (hD : DataAgree G₁ G₂ c D₁ D₂) {c₁ ν : ℝ} :
    InUnionDomainR G₁ c₁ ν D₁ ↔ InUnionDomainR G₂ c₁ ν D₂ :=
  ⟨hA.inUnionDomainR_imp hN₁ hN₂ hD, hA.symm.inUnionDomainR_imp hN₂ hN₁ (hD.symm hA)⟩

end Dom

end Balaban.RootFSpine
