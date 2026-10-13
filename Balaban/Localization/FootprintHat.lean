/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Vmod7Local
public import Balaban.Localization.DecoupledFieldLocal
public import Balaban.Localization.Decoupled2
public import Balaban.Localization.P6TopCover
public import Balaban.Inhabited.LocalizationSettings
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The footprint of a cover centre lies in its thickened box

This is cover geometry; it makes no statement about the coefficients of any expansion.

A row of the Dirichlet operator `H_D(α)` at a site `b ∈ Ω₁(H)` is supported on `b`, its
nearest neighbours and the block of `b`.  When the interaction cube `□_z` is a union of
`H`-blocks of every layer (`BlockAligned H (intBox z)`, the field `blockAligned` of
`Dec2.CoverGeom`), the block of a site of `□_z` lies in `□_z` itself.  Hence the footprint of `z`
(the sites of `□_z` and the columns of their rows) consists of sites of `□_z` and nearest
neighbours of such sites.  Since `3 L² L^j ≥ 1`, this lies in the thickened cube `□̂_z`.

* `footprint_subset_nbhd`: every footprint site is a site of `□_z` or a nearest neighbour of one
  (the true margin is `1`, not `3 L² ℓ_j`).
* `footprint_subset_hatBox`: the footprint lies in `□̂_z`.  The only hypothesis is block
  alignment of `□_z`; no comparison between the layer of a site and the scale of `z` is needed,
  because the block is inside `□_z`.
* `Dec2.CoverGeom.footprint_subset_hatBox`, `FootprintHat.cubeIdx_footprint_subset_hatBox`: the
  same for the centres of a cover with `CoverGeom`.
* `*_of_coverGeom`: the consumers of `Vmod7Local` without the inclusion premise.
* `mem_Qset_of_mem_footprint`: the aligned cell of a footprint site belongs to `Qset z`; and for
  the top-layer cover the cell is a top cell.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section Core

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **The footprint lies within one step of `□_z`**: every site of the footprint of `z` is a
site of `□_z` or a nearest neighbour of one, provided `□_z` is a union of `H`-blocks. -/
theorem footprint_subset_nbhd {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : BlockAligned H (intBox z)) {t : CTorus d L N₁ m₁ K}
    (ht : t ∈ Dec2.footprint H a ν z) :
    ∃ b ∈ intBox z, t = b ∨ ∃ μ : Fin d, t = b + Pi.single μ 1 ∨ t = b - Pi.single μ 1 := by
  classical
  obtain ⟨b, hb, rfl | ⟨y, hy, rfl⟩⟩ := ht
  · exact ⟨_, hb, Or.inl rfl⟩
  · by_cases hyb : (y : CTorus d L N₁ m₁ K) = b
    · exact ⟨_, hb, Or.inl hyb⟩
    by_cases hnb : ∃ μ : Fin d, (y : CTorus d L N₁ m₁ K) = (b : CTorus d L N₁ m₁ K) + Pi.single μ 1 ∨
        (y : CTorus d L N₁ m₁ K) = (b : CTorus d L N₁ m₁ K) - Pi.single μ 1
    · exact ⟨_, hb, Or.inr hnb⟩
    by_cases hblk : (y : CTorus d L N₁ m₁ K) ∈ H.blk (H.layerIndex (b : CTorus d L N₁ m₁ K)) b
    · obtain ⟨hn1, hnK, hxl⟩ := H.layerIndex_spec b.2
      have hy' := H.mem_blk.1 hblk
      exact ⟨_, (hz _ hn1 hnK _ _ hxl hy').1 hb, Or.inl rfl⟩
    · exfalso
      apply hy
      refine dirichlet_entry_eq_zero (G := H) 0 hyb (fun μ => ?_) hblk
      push Not at hnb
      exact ⟨(hnb μ).1, (hnb μ).2⟩

/-- A site of `□_z` and its nearest neighbours lie in `□̂_z`. -/
theorem nbhd_subset_hatBox {z : ℕ × CTorus d L N₁ m₁ K} {b t : CTorus d L N₁ m₁ K}
    (hb : b ∈ intBox z)
    (ht : t = b ∨ ∃ μ : Fin d, t = b + Pi.single μ 1 ∨ t = b - Pi.single μ 1) :
    t ∈ hatBox z := by
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ z.1 := one_le_pow₀ hL1
  have hbig : (1 : ℝ) ≤ 3 * (L : ℝ) ^ 2 * (L : ℝ) ^ z.1 := by nlinarith
  rcases ht with rfl | ⟨μ, rfl | rfl⟩
  · exact box_subset_hatBox z hb
  · have hw : b + Pi.single μ 1 = b + (intTorus (Pi.single μ (1 : ℤ)) : CTorus d L N₁ m₁ K) := by
      congr 1
      funext ν'
      by_cases h' : ν' = μ <;> simp [intTorus_apply, h']
    rw [hw]
    refine inBox_hat_of_add_int hb _ (B := 1) (fun ν' => ?_) hbig
    by_cases h' : ν' = μ <;> simp [h']
  · have hw : b - Pi.single μ 1 = b + (intTorus (Pi.single μ (-1 : ℤ)) : CTorus d L N₁ m₁ K) := by
      funext ν'
      by_cases h' : ν' = μ <;> simp [intTorus_apply, h', sub_eq_add_neg]
    rw [hw]
    refine inBox_hat_of_add_int hb _ (B := 1) (fun ν' => ?_) hbig
    by_cases h' : ν' = μ <;> simp [h']

/-- **T1. The footprint of a centre lies in its thickened interaction cube.**  If `□_z` is a union
of `H`-blocks of every layer, then `footprint H a ν z ⊆ □̂_z`. -/
theorem footprint_subset_hatBox {z : ℕ × CTorus d L N₁ m₁ K}
    (hz : BlockAligned H (intBox z)) {t : CTorus d L N₁ m₁ K} (ht : t ∈ Dec2.footprint H a ν z) :
    t ∈ hatBox z := by
  obtain ⟨b, hb, h⟩ := footprint_subset_nbhd (a := a) (ν := ν) hz ht
  exact nbhd_subset_hatBox hb h

/-- **T1 for a cover with `CoverGeom`.**  For every centre `z` of the cover, the footprint lies in
`□̂_z`.  The hypotheses are the landed geometry of the pair (the field `blockAligned`). -/
theorem footprint_subset_hatBox_of_coverGeom {Cx : ℝ} (S : Dec2.CoverGeom C H a ν Cx)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ C.cubeIdx) {t : CTorus d L N₁ m₁ K}
    (ht : t ∈ Dec2.footprint H a ν z) : t ∈ hatBox z :=
  footprint_subset_hatBox (S.blockAligned z hz) ht

/-- The inclusion in the form of the premise of the landed consumers. -/
theorem footprint_hat_of_coverGeom {Cx : ℝ} (S : Dec2.CoverGeom C H a ν Cx) :
    ∀ z ∈ C.cubeIdx, ∀ t ∈ Dec2.footprint H a ν z, t ∈ hatBox z :=
  fun _ hz _ ht => footprint_subset_hatBox_of_coverGeom S hz ht

/-- **T3.** A cell `P` of the cover (an aligned cell of side `L^(P.1 + m₁)`) containing a
footprint site of `z` belongs to `𝒬(z)`. -/
theorem mem_Qset_of_mem_footprint {Cx : ℝ} (S : Dec2.CoverGeom C H a ν Cx)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ C.cubeIdx) {t : CTorus d L N₁ m₁ K}
    (ht : t ∈ Dec2.footprint H a ν z) {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ C.cubeIdx)
    (htP : t ∈ cubeP P) : P ∈ C.Qset z :=
  C.mem_Qset.2 ⟨hP, t, mem_cubeP.1 htP,
    mem_boxSet.1 (footprint_subset_hatBox_of_coverGeom S hz ht)⟩

/-- **T3, top-layer cover.**  For the cover of the top generating set, the cell of a footprint
site is a top cell: it belongs to `𝒬(z)` and has layer `K`. -/
theorem mem_Qset_of_mem_footprint_top {Cx : ℝ}
    {Ht : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
    (S : Dec2.CoverGeom (coverOf (topGS d L N₁ m₁ K ϱ)) Ht a ν Cx)
    {z : ℕ × CTorus d L N₁ m₁ K} (hz : z ∈ cubeIdx (topGS d L N₁ m₁ K ϱ))
    {t : CTorus d L N₁ m₁ K} (ht : t ∈ Dec2.footprint Ht a ν z)
    {P : ℕ × CTorus d L N₁ m₁ K} (hP : P ∈ cubeIdx (topGS d L N₁ m₁ K ϱ))
    (htP : t ∈ cubeP P) :
    P ∈ (coverOf (topGS d L N₁ m₁ K ϱ)).Qset z ∧ P.1 = K :=
  ⟨mem_Qset_of_mem_footprint S hz ht hP htP, layer_eq_top_of_mem_cubeIdx hP⟩

end Core

section Consumers

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {Cx : ℝ}

/-- `cycLt_footprint_param` without the inclusion premise. -/
theorem cycLt_footprint_param_of_coverGeom (S : Dec2.CoverGeom C H a ν Cx)
    {z P : ℕ × CTorus d L N₁ m₁ K} (hzC : z ∈ C.cubeIdx) (hP : P ∈ C.Qset z)
    (hPn : P.1 ≤ z.1 + 1) (hM₁ : 4 * L ^ 2 ≤ L ^ m₁)
    {t p : CTorus d L N₁ m₁ K} (ht : t ∈ Dec2.footprint H a ν z) (hp : p ∈ cubeP P) :
    CycLt (((L : ℝ) + 13 / 2) * (L : ℝ) ^ (z.1 + m₁)) t p :=
  cycLt_footprint_param (fun _ h => footprint_subset_hatBox_of_coverGeom S hzC h) hP hPn hM₁ ht hp

variable {X₁ : Finset (CTorus d L N₁ m₁ K)} {𝒞 : Finset (ℕ × CTorus d L N₁ m₁ K)}

/-- `cycLt_incidentFootprint` without the inclusion premise. -/
theorem cycLt_incidentFootprint_of_coverGeom (S : Dec2.CoverGeom C H a ν Cx) {m₀ : ℕ}
    (hscale : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hnear : ∀ z ∈ C.cubeIdx, ∀ P ∈ C.Qset z, P.1 ≤ z.1 + 1)
    (hM₁ : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : L + 9 ≤ L ^ m₀) {P : ℕ × CTorus d L N₁ m₁ K}
    {t p : CTorus d L N₁ m₁ K} (ht : t ∈ incidentFootprint C H a ν X₁ 𝒞 P) (hp : p ∈ cubeP P) :
    CycLt ((cellSide L m₀ m₁ K : ℕ) : ℝ) t p :=
  cycLt_incidentFootprint (footprint_hat_of_coverGeom S) hscale hnear hM₁ hm₀ ht hp

/-- `cellIdx_incidentFootprint_mem_moore` without the inclusion premise. -/
theorem cellIdx_incidentFootprint_mem_moore_of_coverGeom (S : Dec2.CoverGeom C H a ν Cx)
    {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (hscale : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hnear : ∀ z ∈ C.cubeIdx, ∀ P ∈ C.Qset z, P.1 ≤ z.1 + 1)
    (hM₁ : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : L + 9 ≤ L ^ m₀) {P : ℕ × CTorus d L N₁ m₁ K}
    {t p : CTorus d L N₁ m₁ K} (ht : t ∈ incidentFootprint C H a ν X₁ 𝒞 P) (hp : p ∈ cubeP P) :
    cellIdx (cellSide L m₀ m₁ K) t ∈ moore (cellSide L m₀ m₁ K) p :=
  cellIdx_incidentFootprint_mem_moore hN (footprint_hat_of_coverGeom S) hscale hnear hM₁ hm₀ ht hp

/-- `star_bound` without the inclusion premise. -/
theorem star_bound_of_coverGeom (S : Dec2.CoverGeom C H a ν Cx) {m₀ : ℕ} (hN : L ^ m₀ ∣ N₁)
    (hscale : ∀ z ∈ C.cubeIdx, z.1 ≤ K) (hnear : ∀ z ∈ C.cubeIdx, ∀ P ∈ C.Qset z, P.1 ≤ z.1 + 1)
    (hM₁ : 4 * L ^ 2 ≤ L ^ m₁) (hm₀ : L + 9 ≤ L ^ m₀) {P : ℕ × CTorus d L N₁ m₁ K}
    {p : CTorus d L N₁ m₁ K} (hp : p ∈ cubeP P) :
    ∃ (O : Finset (Fin d → ZMod ((N₁ * L ^ m₁ * L ^ K) / cellSide L m₀ m₁ K)))
      (w : (Fin d → ZMod ((N₁ * L ^ m₁ * L ^ K) / cellSide L m₀ m₁ K)) → CTorus d L N₁ m₁ K)
      (ℓ : (Fin d → ZMod ((N₁ * L ^ m₁ * L ^ K) / cellSide L m₀ m₁ K)) → ℕ),
      O.card ≤ 3 ^ d ∧
      (∀ t ∈ incidentFootprint C H a ν X₁ 𝒞 P, cellIdx (cellSide L m₀ m₁ K) t ∈ O) ∧
      (∀ c ∈ O, w c ∈ incidentFootprint C H a ν X₁ 𝒞 P ∧ cellIdx (cellSide L m₀ m₁ K) (w c) = c ∧
        ℓ c ≤ d * cellSide L m₀ m₁ K ∧ NNWalk p (w c) (ℓ c)) ∧
      ∑ c ∈ O, ℓ c ≤ d * 3 ^ d * cellSide L m₀ m₁ K :=
  star_bound hN (footprint_hat_of_coverGeom S) hscale hnear hM₁ hm₀ hp

end Consumers

section Witness

open Balaban.Inhabited Balaban.Localization.I5Inhabited

/-- **T4. Non-vacuity.**  On the landed self-cover witness of `LocalizationSettings` (the
generating set `GP`, with `Ω₁ = Ω₂ = 𝕋`, at a scale `m₁ ≥ 4`) the centre `(2, 0)` of the cover has a
footprint containing the site `0`, which lies in the thickened box, and the geometry `CoverGeom`
holds, so the inclusion of T1 is applied to it. -/
theorem footprint_witness :
    ∃ (m₁ : ℕ) (ϱ : ℝ) (H : GeneratingSet 3 3 (6 * 3 ^ m₁) 2 ϱ)
      (_ : Dec2.CoverGeom (coverOf H) H (compWeight 3 1) 0 (Cchi 3 3)),
      ∃ z ∈ (coverOf H).cubeIdx, ∃ t : CTorus 3 3 6 m₁ 2,
        t ∈ Dec2.footprint H (compWeight 3 1) 0 z ∧ t ∈ hatBox z := by
  obtain ⟨m₁, h4, -⟩ := exists_m₁_cstar
  have S := Dec2.coverGeom_self (dgSetting_rho h4)
  have hz : ((2, 0) : ℕ × CTorus 3 3 6 m₁ 2) ∈ cubeIdx (GP m₁ (rhoSep m₁)) := by
    refine (mem_cubeIdx _).2 ⟨⟨by norm_num, le_rfl⟩, ?_, fun μ => by simp⟩
    rw [GP_layer_two]; exact Finset.mem_univ _
  have hb : (0 : CTorus 3 3 6 m₁ 2) ∈ intBox ((2, 0) : ℕ × CTorus 3 3 6 m₁ 2) := by
    rw [mem_intBox]
    intro μ
    refine ⟨0, ?_⟩
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (2 + m₁) := one_le_pow₀ (by norm_num)
    simp only [Int.cast_zero, zero_mul, add_zero, abs_lt]
    simp
    constructor <;> linarith
  have hΩ : (0 : CTorus 3 3 6 m₁ 2) ∈ (GP m₁ (rhoSep m₁)).Ω 1 := by simp [GP_Ω]
  refine ⟨m₁, rhoSep m₁, GP m₁ (rhoSep m₁), S, (2, 0), hz, 0, ?_, ?_⟩
  · exact Dec2.mem_footprint_self (b := ⟨0, hΩ⟩) hb
  · exact footprint_subset_hatBox_of_coverGeom S hz (Dec2.mem_footprint_self (b := ⟨0, hΩ⟩) hb)

end Witness

end Balaban.Localization
