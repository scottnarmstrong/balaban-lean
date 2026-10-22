/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.LocalIsoEv
import Mathlib.Tactic.Linarith

/-!
# Local generating sets on two tori: the block energy functional

The block energy `blockEnergyFun Gb Hm a ν k z` of a `(k+1)`-block `z` of the step, computed with
the local pair `(Gb, Hm)`, is one of the functionals `Φ` of the recomputed terms (the zero-source
terms and the bridge marks).  For `Gb`, `Hm` carried onto `Gb'`, `Hm'` by the box map, it takes
equal values on corresponding inputs at a block of the box and its image: this is the hypothesis
`hΦ` of `OmegaIso.FFmarkedBg_canon_eq` for `Φ = blockEnergyFun …` (with every input realizable).

* `OmegaIso.mem_iff_box`, `OmegaIso.svec_eq_box`, `OmegaIso.zeroExt_eq_box`: the domains and the
  zero extensions at the sites of any box with room;
* `OmegaIso.blockMean_eq`: the `k`-block means at the sites of `Ω₁(Hm)`;
* `OmegaIso.energyDensity_eq`, `OmegaIso.energyBlock_eq`, `OmegaIso.blockEnergyFun_eq`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Localization Balaban.Background Balaban.Multiscale Balaban.Polymer
  Balaban.Polymer.TwoTorusStep Balaban.Fluctuation Balaban.SmallField.Def6 Matrix

variable {d L N₁ N₁' m₁ k N : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱb ϱb' ϱm ϱm' : ℝ}

set_option hygiene false in
local notation "bk" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
set_option hygiene false in
local notation "bk'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))

namespace OmegaIso

variable {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {H : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'} {ρ : ℕ}

/-- **The domains `Ω₁` at the sites of any box with room** (outside the box of radius `ρ + 1`
neither site lies in `Ω₁`). -/
theorem mem_iff_box (hI : OmegaIso G H ρ) {R : ℕ}
    (hR : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) : bk x ∈ H.Ω 1 ↔ x ∈ G.Ω 1 := by
  by_cases hxρ : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) x
  · exact hI.mem_iff hxρ
  · constructor
    · intro h
      exfalso
      have hb := hI.boxH _ h
      have hv := valMinAbs_boxMap (m' := (N₁' * L ^ m₁) * L ^ (k + 1)) hR hx
      exact hxρ fun μ => by rw [← hv μ]; exact (hb μ).trans (by omega)
    · intro h
      exact absurd (hI.inBox_succ h) hxρ

/-- The zero extension of corresponding vector fields of `Ω₁` at the sites of a box with room. -/
theorem svec_eq_box (hI : OmegaIso G H ρ) {R : ℕ}
    (hR : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)) {δφ : G.Ω 1 × Fin N → ℂ}
    {δφ' : H.Ω 1 × Fin N → ℂ} (hδ : ∀ y i, δφ' (hI.e y, i) = δφ (y, i))
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) (i : Fin N) :
    svec H δφ' (bk x) i = svec G δφ x i := by
  by_cases h : x ∈ G.Ω 1
  · rw [svec_of_mem' _ ((hI.mem_iff_box hR hx).2 h), svec_of_mem' _ h, ← hδ ⟨x, h⟩ i]
    rfl
  · rw [svec_of_not_mem (hy := fun h' => h ((hI.mem_iff_box hR hx).1 h')),
      svec_of_not_mem (hy := h)]

/-- The zero extension of corresponding scalar fields of `Ω₁` at the sites of a box with room. -/
theorem zeroExt_eq_box (hI : OmegaIso G H ρ) {R : ℕ}
    (hR : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)) {α : G.Ω 1 → ℂ} {α' : H.Ω 1 → ℂ}
    (hα : ∀ x, α' (hI.e x) = α x) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    zeroExt (H.Ω 1) α' (bk x) = zeroExt (G.Ω 1) α x := by
  unfold zeroExt
  by_cases h : x ∈ G.Ω 1
  · have h' : bk x ∈ H.Ω 1 := (hI.mem_iff_box hR hx).2 h
    simp only [h, h', ↓reduceDIte]
    rw [← hα ⟨x, h⟩]
    rfl
  · have h' : bk x ∉ H.Ω 1 := fun hh => h ((hI.mem_iff_box hR hx).1 hh)
    simp only [h, h', ↓reduceDIte]

/-- **The `k`-block means at corresponding sites of `Ω₁`.** -/
theorem blockMean_eq (hI : OmegaIso G H ρ) {f : CTorus d L N₁ m₁ (k + 1) → ℂ}
    {f' : CTorus d L N₁' m₁ (k + 1) → ℂ}
    (hf : ∀ y, InBox d (ρ + L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1)) y → f' (bk y) = f y)
    {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ G.Ω 1) :
    blockMean H k f' (bk x) = blockMean G k f x := by
  have hK : L ^ k ≤ L ^ (k + 1) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ k)
  have ⟨h1, h2⟩ := hI.two_lt
  have hxb := hI.boxG x hx
  have hbox : ∀ z ∈ box (cbase (L ^ k) x) (L ^ k),
      InBox d (ρ + L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1)) z :=
    fun z hz => inBox_of_mem_cell (by omega) hxb hz
  have hblk := blk_image (r := ρ + L ^ k) (j := k) (N₁' := N₁') G
    (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱb) (k + 1) le_rfl)
    (Nat.le_succ k) (by omega) x hbox
  have hblkF : (G.blk k x).image bk = H.blk k (bk x) := by
    apply Finset.coe_injective
    rw [Finset.coe_image]
    exact hblk
  have hmem : ∀ y ∈ G.blk k x, InBox d (ρ + L ^ k) ((N₁ * L ^ m₁) * L ^ (k + 1)) y :=
    fun y hy => hbox y ((jBlock_eq_iff_mem_box (Nat.le_succ k) y x).1
      (GeneratingSet.mem_blk.1 hy))
  unfold blockMean
  rw [← hblkF, Finset.sum_image]
  · congr 1
    exact Finset.sum_congr rfl fun y hy => hf y (hmem y hy)
  · intro y hy y' hy' h
    exact boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ k) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
      (hmem y hy) (hmem y' hy') h

end OmegaIso

namespace OmegaIso

variable {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Gb' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱb'}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {Hm' : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱm'} {ρ : ℕ}

/-- **The energy density at corresponding sites of a box with room.** -/
theorem energyDensity_eq (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (a : ℕ → ℝ) (ν : ℝ)
    {R : ℕ} (hρR : ρ + L ^ k ≤ R) (hR : 2 * (R + 1) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hR1 : 2 * (R + 1) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    {α : Gb.Ω 1 → ℂ} {α' : Gb'.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x)
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (hδ : ∀ y i, δφ' (hH.e y, i) = δφ (y, i))
    {ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {ψ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hψ : FieldCorr (ρ + 1) ψ ψ') {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x) :
    energyDensity Gb' Hm' a ν k α' δφ' ψ' (bk x) = energyDensity Gb Hm a ν k α δφ ψ x := by
  have hR' : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ (k + 1) := by omega
  have hsv : ∀ y, InBox d (R + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) y → ∀ i,
      svec Hm' δφ' (bk y) i = svec Hm δφ y i := fun y hy i => hH.svec_eq_box hR hδ hy i
  have h1 : ∀ (μ : Fin d) (i : Fin N), svec Hm' δφ' (bk x + Pi.single μ 1) i =
      svec Hm δφ (x + Pi.single μ 1) i := by
    intro μ i
    rw [← boxMap_add_single (ρ := R) (by omega) (by omega) hx μ]
    exact hsv _ (inBox_add_single (by omega) hx μ) i
  have h0 : ∀ i, svec Hm' δφ' (bk x) i = svec Hm δφ x i := fun i =>
    hsv x (inBox_mono (Nat.le_succ R) hx) i
  have hz : zeroExt (Gb'.Ω 1) α' (bk x) = zeroExt (Gb.Ω 1) α x := hI.zeroExt_eq_box hR' hα hx
  have hmem : bk x ∈ Hm'.Ω 1 ↔ x ∈ Hm.Ω 1 := hH.mem_iff_box hR' hx
  unfold energyDensity
  by_cases hxH : x ∈ Hm.Ω 1
  · have hxH' : bk x ∈ Hm'.Ω 1 := hmem.2 hxH
    have hb : ∀ i, blockMean Hm' k (fun y => svec Hm' δφ' y i) (bk x) =
        blockMean Hm k (fun y => svec Hm δφ y i) x := fun i =>
      hH.blockMean_eq (fun y hy => hsv y (inBox_mono (by omega) hy) i) hxH
    have hψx : ψ' (bk x) = ψ x := hψ x (hH.inBox_succ hxH)
    simp only [hxH, hxH', ↓reduceIte, h0, h1, hb, hz, hψx]
  · have hxH' : bk x ∉ Hm'.Ω 1 := fun h => hxH (hmem.1 h)
    simp only [hxH, hxH', ↓reduceIte, h0, h1, hz]

/-- **The block energy at a block of the box and at its image.** -/
theorem energyBlock_eq (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (a : ℕ → ℝ) (ν : ℝ)
    {R : ℕ} (hρR : ρ + L ^ k ≤ R)
    (hn : 2 * (R + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (R + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : Gb.Ω 1 → ℂ} {α' : Gb'.Ω 1 → ℂ} (hα : ∀ x, α' (hI.e x) = α x)
    {δφ : Hm.Ω 1 × Fin N → ℂ} {δφ' : Hm'.Ω 1 × Fin N → ℂ}
    (hδ : ∀ y i, δφ' (hH.e y, i) = δφ (y, i))
    {ψ : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} {ψ' : CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ}
    (hψ : FieldCorr (ρ + 1) ψ ψ') {x₀ : CTorus d L N₁ m₁ (k + 1)}
    (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀) :
    energyBlock Gb' Hm' a ν k α' δφ' ψ' (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bk x₀)) =
      energyBlock Gb Hm a ν k α δφ ψ (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hKk : L ^ k ≤ L ^ (k + 1) :=
    Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.le_succ k)
  set S := blockSites d L N₁ m₁ (k + 1) k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) with hS
  have hSbox : ∀ x ∈ S, InBox d (R + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) x := by
    intro x hx
    have hxj : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
        jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀ := (Finset.mem_filter.1 hx).2
    exact inBox_of_jBlock_eq (N₁ := N₁) le_rfl (by omega) hx₀ hxj
  have hx₀' : InBox d R ((N₁' * L ^ m₁) * L ^ (k + 1)) (bk x₀) := inBox_boxMap (by omega) hx₀
  have himg : S.image bk = Finset.univ.filter (fun x' : CTorus d L N₁' m₁ (k + 1) =>
      jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) x' =
        jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bk x₀)) := by
    ext x'
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hxj : jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
          jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀ := (Finset.mem_filter.1 hx).2
      exact (jBlock_boxMap_iff (ρ := R + L ^ (k + 1)) le_rfl (by omega) (by omega) (hSbox x hx)
        (inBox_mono (Nat.le_add_right _ _) hx₀)).1 hxj
    · intro hx'
      have hx'R : InBox d (R + L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1)) x' :=
        inBox_of_jBlock_eq (N₁ := N₁') le_rfl (by omega) hx₀' hx'
      have hback : bk (bk' x') = x' := boxMap_boxMap (by omega) hx'R
      have hyR : InBox d (R + L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1)) (bk' x') :=
        inBox_boxMap (by omega) hx'R
      refine ⟨bk' x', ?_, hback⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      refine (jBlock_boxMap_iff (N₁' := N₁') (ρ := R + L ^ (k + 1)) le_rfl (by omega) (by omega)
        hyR (inBox_mono (Nat.le_add_right _ _) hx₀)).2 ?_
      rw [hback]; exact hx'
  unfold energyBlock
  rw [← himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun x hx => ?_
    exact hI.energyDensity_eq hH a ν (R := R + L ^ (k + 1)) (by omega) (by omega) (by omega) hα hδ
      hψ (hSbox x hx)
  · intro x hx x' hx' h
    exact boxMap_inj (hm' := (by omega : 2 * (R + L ^ (k + 1)) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1)))
      (hSbox x hx) (hSbox x' hx') h

/-- **The block energy functional at a block of the box and at its image**, on corresponding
inputs (the hypothesis `hΦ` of `FFmarkedBg_canon_eq` for `Φ = blockEnergyFun …`). -/
theorem blockEnergyFun_eq (hI : OmegaIso Gb Gb' ρ) (hH : OmegaIso Hm Hm' ρ) (a : ℕ → ℝ) (ν : ℝ)
    {R : ℕ} (hρR : ρ + L ^ k ≤ R)
    (hn : 2 * (R + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * (R + L ^ (k + 1) + 1) + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {x₀ : CTorus d L N₁ m₁ (k + 1)} (hx₀ : InBox d R ((N₁ * L ^ m₁) * L ^ (k + 1)) x₀)
    (t : ((Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)))
    (t' : ((Gb'.Ω 1 × Fin N → ℂ) × (Gb'.Ω 1 → ℂ)) × (Hm'.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁' * L ^ m₁) (k + 1) N × (CTorus d L N₁' m₁ (k + 1) → Fin N → ℂ)))
    (hα : ∀ x, t'.1.2 (hI.e x) = t.1.2 x) (hδ : ∀ y i, t'.2.1 (hH.e y, i) = t.2.1 (y, i))
    (hψ : FieldCorr (ρ + 1) t.2.2.2 t'.2.2.2) :
    blockEnergyFun Gb' Hm' a ν k (jBlock d L (N₁' * L ^ m₁) (k + 1) (k + 1) (bk x₀))
        t'.1 t'.2.1 t'.2.2 =
      blockEnergyFun Gb Hm a ν k (jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x₀) t.1 t.2.1 t.2.2 :=
  hI.energyBlock_eq hH a ν hρR hn hn' hα hδ hψ hx₀

end OmegaIso

end Balaban.Polymer.LocalIso
