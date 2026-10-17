/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapClose
public import Balaban.Fluctuation.InteractionEnergy
import Mathlib.Tactic.Ring

/-!
# Translation covariance of the block energy (item 24, blocker 7)

The block energy `energyBlock` of the chord form at the block of `x₀ + t` evaluated at the transported
data (multiplier `S.mul α`, fluctuation field `Sm.fld δφ`, tangent `symSite σ ψ`) equals the block
energy at the block of `x₀` at the original data, for a translation `t` by a multiple of the side of
the `(n+1)`-blocks.  This is the covariance used to produce the translated functional of the block
energy in the recentred transport (`hfamΦ` of `evDec_boxMap_of_diameter`).

* `jBlock_add_iff`: the translation maps `j`-blocks to `j`-blocks;
* `energyDensity_translate`, `energyBlock_translate`, `blockEnergyFun_translate`;
* `blockSites_translate`, `readSites_translate`: the sites of the block and the sites read by the
  block energy are translated with the block.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Analysis Balaban.Fluctuation Balaban.SmallField
  Balaban.Polymer Balaban.Multiscale Balaban.Background

section Translate

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

/-- Translation by a multiple of the side `L ^ j` of the `j`-blocks, `j ≤ K`, maps `j`-blocks to
`j`-blocks: two sites have the same `j`-block iff their translates do. -/
theorem jBlock_add_iff {j : ℕ} (hj : j ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ j ∣ (t μ).val) (x y : CTorus d L N₁ m₁ K) :
    jBlock d L (N₁ * L ^ m₁) K j (x + t) = jBlock d L (N₁ * L ^ m₁) K j (y + t) ↔
      jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j y := by
  have hℓ : N₁ * L ^ m₁ * L ^ K = L ^ j * (N₁ * L ^ m₁ * L ^ (K - j)) := side_eq hj
  have key : ∀ z : CTorus d L N₁ m₁ K, jBlock d L (N₁ * L ^ m₁) K j (z + t) =
      fun i => jBlock d L (N₁ * L ^ m₁) K j z i +
        (((t i).val / L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ (K - j))) :=
    fun z => funext fun i => by
      simp only [jBlock_apply, Pi.add_apply]
      rw [blockCoord_add_of_dvd hℓ _ _ (ht i)]
  rw [key, key]
  constructor
  · intro h; funext i; simpa using congrFun h i
  · intro h; funext i; simp [congrFun h i]

/-- The `j`-block of the translate: `jBlock (x + t) = jBlock x + t / L ^ j`. -/
theorem jBlock_add_eq {j : ℕ} (hj : j ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ j ∣ (t μ).val) (x : CTorus d L N₁ m₁ K) :
    jBlock d L (N₁ * L ^ m₁) K j (x + t) = fun i => jBlock d L (N₁ * L ^ m₁) K j x i +
        (((t i).val / L ^ j : ℕ) : ZMod (N₁ * L ^ m₁ * L ^ (K - j))) := by
  have hℓ : N₁ * L ^ m₁ * L ^ K = L ^ j * (N₁ * L ^ m₁ * L ^ (K - j)) := side_eq hj
  funext i
  simp only [jBlock_apply, Pi.add_apply]
  rw [blockCoord_add_of_dvd hℓ _ _ (ht i)]

variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}

/-- **The energy density is translation covariant.** -/
theorem energyDensity_translate {n : ℕ} (hn : n ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ n ∣ (t μ).val)
    (S : LatSymm Gp Gp (Equiv.addRight t)) (Sm : LatSymm Hm Hm (Equiv.addRight t))
    (a : ℕ → ℝ) (ν : ℝ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (ψ : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : CTorus d L N₁ m₁ K) :
    energyDensity Gp Hm a ν n (S.mul α) (Sm.fld δφ) (DecEquiv.symSite (Equiv.addRight t) ψ)
        (x + t) = energyDensity Gp Hm a ν n α δφ ψ x := by
  have hsv : ∀ y i, svec Hm (Sm.fld δφ) (y + t) i = svec Hm δφ y i := fun y i =>
    Sm.svec_sym δφ y i
  have hΩ : x + t ∈ Hm.Ω 1 ↔ x ∈ Hm.Ω 1 := Sm.mem_Ω1 x
  have hz : zeroExt (Gp.Ω 1) (S.mul α) (x + t) = zeroExt (Gp.Ω 1) α x := by
    unfold zeroExt
    by_cases hx : x ∈ Gp.Ω 1
    · have hx' : x + t ∈ Gp.Ω 1 := (S.mem_Ω1 x).2 hx
      simp only [hx, hx', dite_true]
      exact S.mul_apply α ⟨x, hx⟩
    · have hx' : x + t ∉ Gp.Ω 1 := fun h => hx ((S.mem_Ω1 x).1 h)
      simp [hx, hx']
  have hbm : ∀ i, blockMean Hm n (fun y => svec Hm (Sm.fld δφ) y i) (x + t) =
      blockMean Hm n (fun y => svec Hm δφ y i) x := by
    intro i
    unfold blockMean
    congr 1
    refine (Finset.sum_equiv (Equiv.addRight t) (fun y => ?_) (fun y _ => ?_)).symm
    · simp only [GeneratingSet.mem_blk, Equiv.coe_addRight]
      exact (jBlock_add_iff hn t ht y x).symm
    · exact (hsv y i).symm
  have hnb : ∀ (μ : Fin d) (i : Fin N), svec Hm (Sm.fld δφ) (x + t + Pi.single μ 1) i =
      svec Hm δφ (x + Pi.single μ 1) i := by
    intro μ i
    have : x + t + Pi.single μ 1 = (x + Pi.single μ 1) + t := by abel
    rw [this]; exact hsv _ i
  unfold energyDensity
  simp only [hΩ, hsv, hnb, hbm, hz, DecEquiv.symSite]
  have hψ : ∀ x, (Equiv.addRight t).symm (x + t) = x := fun x => by simp
  simp only [hψ]

/-- **The block energy is translation covariant.**  For `t` divisible by `L ^ (n + 1)`, `n + 1 ≤ K`. -/
theorem energyBlock_translate {n : ℕ} (hn : n + 1 ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + 1) ∣ (t μ).val)
    (S : LatSymm Gp Gp (Equiv.addRight t)) (Sm : LatSymm Hm Hm (Equiv.addRight t))
    (a : ℕ → ℝ) (ν : ℝ) (α : Gp.Ω 1 → ℂ) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (ψ : CTorus d L N₁ m₁ K → Fin N → ℂ) (x₀ : CTorus d L N₁ m₁ K) :
    energyBlock Gp Hm a ν n (S.mul α) (Sm.fld δφ) (DecEquiv.symSite (Equiv.addRight t) ψ)
        (jBlock d L (N₁ * L ^ m₁) K (n + 1) (x₀ + t)) =
      energyBlock Gp Hm a ν n α δφ ψ (jBlock d L (N₁ * L ^ m₁) K (n + 1) x₀) := by
  unfold energyBlock
  refine (Finset.sum_equiv (Equiv.addRight t) (fun y => ?_) (fun y _ => ?_)).symm
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Equiv.coe_addRight]
    exact (jBlock_add_iff hn t ht y x₀).symm
  · exact (energyDensity_translate (Nat.le_of_succ_le hn)
      t (fun μ => (pow_dvd_pow L (Nat.le_succ n)).trans (ht μ)) S Sm a ν α δφ ψ y).symm

/-- **The block functional is translation covariant.** -/
theorem blockEnergyFun_translate {n : ℕ} (hn : n + 1 ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + 1) ∣ (t μ).val)
    (S : LatSymm Gp Gp (Equiv.addRight t)) (Sm : LatSymm Hm Hm (Equiv.addRight t))
    (a : ℕ → ℝ) (ν : ℝ) (x₀ : CTorus d L N₁ m₁ K)
    (bg : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :
    blockEnergyFun Gp Hm a ν n (jBlock d L (N₁ * L ^ m₁) K (n + 1) (x₀ + t))
        (S.fld bg.1, S.mul bg.2) (Sm.fld δφ) (symU (Equiv.addRight t) u) =
      blockEnergyFun Gp Hm a ν n (jBlock d L (N₁ * L ^ m₁) K (n + 1) x₀) bg δφ u :=
  energyBlock_translate hn t ht S Sm a ν bg.2 δφ u.2 x₀

/-- The translate of the set of sites of the block of `x₀` is the set of sites of the block of
`x₀ + t`. -/
theorem image_blockSites_translate {n : ℕ} (hn : n + 1 ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + 1) ∣ (t μ).val) (x₀ : CTorus d L N₁ m₁ K) :
    (Equiv.addRight t) '' (↑(blockSites d L N₁ m₁ K n
        (jBlock d L (N₁ * L ^ m₁) K (n + 1) x₀)) : Set (CTorus d L N₁ m₁ K)) =
      ↑(blockSites d L N₁ m₁ K n (jBlock d L (N₁ * L ^ m₁) K (n + 1) (x₀ + t))) := by
  ext y
  obtain ⟨x, rfl⟩ : ∃ x, y = x + t := ⟨y - t, by abel⟩
  rw [show x + t = (Equiv.addRight t) x from rfl, (Equiv.addRight t).injective.mem_set_image]
  simp only [Finset.mem_coe, blockSites, Finset.mem_filter, Finset.mem_univ, true_and,
    Equiv.coe_addRight]
  exact (jBlock_add_iff hn t ht x x₀).symm

/-- A site of the block of `x₀ + t` is the translate of a site of the block of `x₀`. -/
theorem sub_mem_blockSites {n : ℕ} (hn : n + 1 ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + 1) ∣ (t μ).val) {x₀ y : CTorus d L N₁ m₁ K}
    (hy : y ∈ blockSites d L N₁ m₁ K n (jBlock d L (N₁ * L ^ m₁) K (n + 1) (x₀ + t))) :
    y - t ∈ blockSites d L N₁ m₁ K n (jBlock d L (N₁ * L ^ m₁) K (n + 1) x₀) := by
  have h := (Finset.mem_filter.1 hy).2
  refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
  exact (jBlock_add_iff hn t ht (y - t) x₀).1 (by simpa only [sub_add_cancel] using h)

/-- A site read by the block energy of the block of `x₀ + t` is the translate of a site read by the
block energy of the block of `x₀`. -/
theorem sub_mem_readSites {n : ℕ} (hn : n + 1 ≤ K) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + 1) ∣ (t μ).val) {x₀ w : CTorus d L N₁ m₁ K}
    (hw : w ∈ readSites Hm n (jBlock d L (N₁ * L ^ m₁) K (n + 1) (x₀ + t))) :
    w - t ∈ readSites Hm n (jBlock d L (N₁ * L ^ m₁) K (n + 1) x₀) := by
  obtain ⟨x, hx, h⟩ := hw
  refine ⟨x - t, sub_mem_blockSites hn t ht hx, ?_⟩
  rcases h with h | ⟨μ, h⟩ | h
  · exact Or.inl (by rw [h])
  · refine Or.inr (Or.inl ⟨μ, ?_⟩)
    rw [h]; abel
  · refine Or.inr (Or.inr ?_)
    rw [GeneratingSet.mem_blk] at h ⊢
    refine (jBlock_add_iff (Nat.le_of_succ_le hn) t
      (fun μ => (pow_dvd_pow L (Nat.le_succ n)).trans (ht μ)) (w - t) (x - t)).1 ?_
    simpa only [sub_add_cancel] using h

end Translate

section Margin

open Balaban.Localization.DecEquiv

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {n : ℕ}

/-- **The margin of a set of sites against the cover is translated.**  For a level set `G` and a
translation `t` by a multiple of `L ^ (n + m₁)`, the sites `Zα + t` have the margin against the
translated read region `X₁f + t` when `Zα` has it against `X₁f`. -/
theorem blockMargin_translate (hG : IsLevel G n) (t : CTorus d L N₁ m₁ K)
    (ht : ∀ μ, L ^ (n + m₁) ∣ (t μ).val) {X₁f : Finset (CTorus d L N₁ m₁ K)}
    {Zα : Set (CTorus d L N₁ m₁ K)} (h : BlockMargin G X₁f Zα) :
    BlockMargin G (X₁f.image (Equiv.addRight t)) ((Equiv.addRight t) '' Zα) := by
  classical
  have hn := hG.bounds
  have S := LatSymm.ofTranslateLevel hG t (fun μ => (pow_dvd_pow L (by omega)).trans (ht μ))
  let CS := CoverSymm.ofTranslate hG t ht
  rintro _ ⟨x, hx, rfl⟩ hxΩ
  have hxΩ0 : x ∈ G.Ω 1 := (S.mem_Ω1 x).1 hxΩ
  obtain ⟨z, hz, hbox, hQ, hSub⟩ := h x hx hxΩ0
  have hzn : z.1 = n := fst_eq_of_mem_cubeIdx hG hz
  have hzt : ((z.1, z.2 + t) : ℕ × CTorus d L N₁ m₁ K) = translateCentres t z := rfl
  refine ⟨(z.1, z.2 + t), (translate_mem_cubeIdx_iff hG t ht z).2 hz, ?_, ?_, ?_⟩
  · exact (CS.box z x).2 hbox
  · intro P hP hPpar
    have hP' : translateCentres t (P.1, P.2 - t) ∈ (coverOf G).Qset (translateCentres t z) := by
      simpa [translateCentres_apply] using hP
    have hP0 : (P.1, P.2 - t) ∈ (coverOf G).Qset z := (CS.qset z (P.1, P.2 - t)).1 hP'
    refine hQ _ hP0 ?_
    have hPi : P ∈ cubeIdx G := ((coverOf G).mem_Qset.1 hP).1
    have hP0i : (P.1, P.2 - t) ∈ cubeIdx G := ((coverOf G).mem_Qset.1 hP0).1
    refine Finset.mem_filter.2 ⟨hP0i, fun hsub => ?_⟩
    have hPp := (Finset.mem_filter.1 hPpar).2
    refine hPp (fun y hy => ?_)
    have hPn : P.1 = n := fst_eq_of_mem_cubeIdx hG hPi
    have hy0 : y - t ∈ cubeP (P.1, P.2 - t) := by
      rw [mem_cubeP]
      have := (sameCell_add_iff (dvd_side (by omega : P.1 ≤ K)) (y - t) (P.2 - t) t
        (fun μ => by rw [hPn]; exact (pow_dvd_pow L (by omega)).trans (ht μ) |>.trans dvd_rfl)).1
      simp only [sub_add_cancel] at this
      exact this (mem_cubeP.1 hy)
    exact Finset.mem_image.2 ⟨y - t, hsub hy0, by simp⟩
  · intro y hy
    have hy1 : (y : CTorus d L N₁ m₁ K) - t ∈ G.Ω 1 := by
      refine (S.mem_Ω1 ((y : CTorus d L N₁ m₁ K) - t)).1 ?_
      simp
    have hyb : (y : CTorus d L N₁ m₁ K) - t ∈ hatBox z := by
      have h1 : (y : CTorus d L N₁ m₁ K) ∈ boxSet m₁ z.1 (z.2 + t) (hatRad L m₁ z.1) := hy
      rw [mem_boxSet] at h1
      have h2 := (inBox_add_iff z.1 z.2 ((y : CTorus d L N₁ m₁ K) - t) t _).1
        (by simpa only [sub_add_cancel] using h1)
      exact mem_boxSet.2 h2
    have := hSub ⟨_, hy1⟩ hyb
    exact Finset.mem_image.2 ⟨_, this, by simp⟩

end Margin

end Balaban.Polymer.TwoTorusStep
