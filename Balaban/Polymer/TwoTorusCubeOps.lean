/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusThickSets
public import Balaban.Localization.DecoupledAlg
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The cube operators of the decoupled Green function on two tori

For the whole-lattice generating set `levelGS j` of two step tori `CTorus d L N₁ m₁ K` and
`CTorus d L N₁' m₁ K`, identified on a centred box by `boxMap`, this file shows that the cube
operators of the decoupled Green function correspond for a cube whose interaction box lies in the
box: the interaction box `intBox`, the partition weight `chi`, the entries of the Dirichlet and
cut operators, the commutator `Kz`, and the cube Green function `cubeG`.
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background

/-! ### Entries of the bond matrices and of the lattice Laplacian -/

section Entries

variable {d ℓ : ℕ} [NeZero ℓ]

theorem bondVec_apply (b : Torus d ℓ × Fin d) (w : Torus d ℓ) :
    bondVec b w = (if w = b.1 + Pi.single b.2 1 then 1 else 0) - (if w = b.1 then 1 else 0) := by
  simp [bondVec, Pi.single_apply]

theorem sum_shift_ite (x : Torus d ℓ) (e : Torus d ℓ) (f : Torus d ℓ → ℝ) :
    ∑ z, f z * (if x = z + e then 1 else 0) = f (x - e) := by
  rw [Finset.sum_eq_single (x - e)]
  · simp
  · intro z _ hz
    have : ¬ x = z + e := fun h => hz (by rw [h]; abel)
    simp [this]
  · simp

theorem sum_shift_ite_pair (x y : Torus d ℓ) (e : Torus d ℓ) (f : Torus d ℓ → ℝ) :
    ∑ z, f z * ((if x = z + e then 1 else 0) * (if y = z + e then 1 else 0)) =
      if x = y then f (x - e) else 0 := by
  by_cases hxy : x = y
  · subst hxy
    have h : ∀ z, f z * ((if x = z + e then (1 : ℝ) else 0) * (if x = z + e then (1 : ℝ) else 0)) =
        f z * (if x = z + e then 1 else 0) := fun z => by split_ifs <;> simp
    rw [Finset.sum_congr rfl fun z _ => h z, sum_shift_ite]
    simp
  · simp only [hxy, ↓reduceIte]
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h : x = z + e
    · have : ¬ y = z + e := fun h' => hxy (h.trans h'.symm)
      simp [this]
    · simp [h]

/-- **The entry of the sum of the bond matrices of a cut.** -/
theorem sum_bondMatrix_apply (cut : Finset (Torus d ℓ × Fin d)) (x y : Torus d ℓ) :
    (∑ b ∈ cut, bondMatrix b) x y = ∑ μ : Fin d,
      ((if x = y then ((if (x - Pi.single μ 1, μ) ∈ cut then (1 : ℝ) else 0) +
          (if (x, μ) ∈ cut then 1 else 0)) else 0)
        - (if x = y + Pi.single μ 1 then (if (y, μ) ∈ cut then (1 : ℝ) else 0) else 0)
        - (if y = x + Pi.single μ 1 then (if (x, μ) ∈ cut then (1 : ℝ) else 0) else 0)) := by
  rw [Matrix.sum_apply]
  have h1 : ∑ b ∈ cut, bondMatrix b x y =
      ∑ b : Torus d ℓ × Fin d, if b ∈ cut then bondVec b x * bondVec b y else 0 := by
    rw [← Finset.sum_filter]
    refine Finset.sum_congr (by ext; simp) fun b _ => ?_
    simp [bondMatrix, Matrix.vecMulVec_apply]
  rw [h1, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun μ _ => ?_
  obtain ⟨e, he⟩ : ∃ e : Torus d ℓ, e = Pi.single μ 1 := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : Torus d ℓ → ℝ, c = fun z => if (z, μ) ∈ cut then 1 else 0 := ⟨_, rfl⟩
  have h2 : ∀ z : Torus d ℓ, (if (z, μ) ∈ cut then bondVec (z, μ) x * bondVec (z, μ) y else 0) =
      c z * ((if x = z + e then 1 else 0) * (if y = z + e then 1 else 0))
        - c z * ((if x = z + e then 1 else 0) * (if y = z then 1 else 0))
        - c z * ((if x = z then 1 else 0) * (if y = z + e then 1 else 0))
        + c z * ((if x = z then 1 else 0) * (if y = z then 1 else 0)) := by
    intro z
    rw [bondVec_apply, bondVec_apply, ← he]
    by_cases hz : (z, μ) ∈ cut
    · have : c z = 1 := by simp [hc, hz]
      simp only [hz, ↓reduceIte, this]
      ring
    · have : c z = 0 := by simp [hc, hz]
      simp only [hz, ↓reduceIte, this]
      ring
  rw [Finset.sum_congr rfl fun z _ => h2 z, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, sum_shift_ite_pair x y e c]
  have h3 : ∑ z, c z * ((if x = z + e then 1 else 0) * (if y = z then 1 else 0)) =
      if x = y + e then c y else 0 := by
    by_cases h : x = y + e
    · simp only [h, ↓reduceIte]
      rw [Finset.sum_eq_single y]
      · simp [h]
      · intro z _ hz; simp [Ne.symm hz]
      · simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hz : y = z
      · subst hz; simp [h]
      · simp [hz]
  have h4 : ∑ z, c z * ((if x = z then 1 else 0) * (if y = z + e then 1 else 0)) =
      if y = x + e then c x else 0 := by
    by_cases h : y = x + e
    · simp only [h, ↓reduceIte]
      rw [Finset.sum_eq_single x]
      · simp
      · intro z _ hz; simp [Ne.symm hz]
      · simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hz : x = z
      · subst hz; simp [h]
      · simp [hz]
  have h5 : ∑ z, c z * ((if x = z then 1 else 0) * (if y = z then 1 else 0)) =
      if x = y then c x else 0 := by
    by_cases h : x = y
    · subst h
      simp only [↓reduceIte]
      rw [Finset.sum_eq_single x]
      · simp
      · intro z _ hz; simp [Ne.symm hz]
      · simp
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun z _ => ?_
      by_cases hz : x = z
      · subst hz; simp [Ne.symm h]
      · simp [hz]
  rw [h3, h4, h5]
  subst he
  subst hc
  by_cases hxy : x = y <;> simp only [hxy, ↓reduceIte] <;> ring

/-- The entry of the lattice Laplacian `-Δ + ν`. -/
theorem latticeLaplacian_apply (ν : ℝ) (x y : Torus d ℓ) :
    latticeLaplacian d ℓ ν x y = (2 * d + ν) * (if x = y then 1 else 0) -
      ∑ μ : Fin d, ((if y = x + Pi.single μ 1 then 1 else 0) +
        (if x = y + Pi.single μ 1 then 1 else 0)) := by
  unfold latticeLaplacian
  simp [Matrix.sub_apply, Matrix.sum_apply, Matrix.one_apply, shiftMatrix]

end Entries

/-! ### The operators of `levelGS j` on two tori -/

section Level

variable {d L N₁ N₁' m₁ K : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ} {j : ℕ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ K) ((N₁' * L ^ m₁) * L ^ K)
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ K) ((N₁ * L ^ m₁) * L ^ K)

theorem levelGS_mem_Ω_one (hj1 : 1 ≤ j) (hj : j ≤ K) (z : CTorus d L N₁ m₁ K) :
    z ∈ (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 := by
  simp [levelGS, hj1]

/-- The `j`-block of two sites of the box is the same on both tori. -/
theorem jBlock_boxMap_iff {ρ : ℕ} (hj : j ≤ K)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K) {x y : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j y ↔
      jBlock d L (N₁' * L ^ m₁) K j (bm x) = jBlock d L (N₁' * L ^ m₁) K j (bm y) := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have hbox : ∀ z ∈ box (cbase (L ^ j) y) (L ^ j), InBox d (ρ + L ^ j) ((N₁ * L ^ m₁) * L ^ K) z :=
    fun z hz => inBox_of_mem_cell (a := L ^ j) (by omega) hy hz
  have hblk := blk_image (r := ρ + L ^ j) (j := j)
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := 0) j hj)
    (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := 0) j hj) hj
    (by omega) y hbox
  constructor
  · intro h
    have h1 : x ∈ ((levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := 0) j hj).blk
        j y : Set (CTorus d L N₁ m₁ K)) := by
      simpa [GeneratingSet.mem_blk] using h
    have h2 := Set.mem_image_of_mem bm h1
    rw [hblk] at h2
    simpa [GeneratingSet.mem_blk] using h2
  · intro h
    have h1 : bm x ∈ ((levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := 0) j hj).blk
        j (bm y) : Set (CTorus d L N₁' m₁ K)) := by
      simpa [GeneratingSet.mem_blk] using h
    rw [← hblk] at h1
    obtain ⟨z, hz, hzx⟩ := h1
    have hz' : jBlock d L (N₁ * L ^ m₁) K j z = jBlock d L (N₁ * L ^ m₁) K j y := by
      simpa [GeneratingSet.mem_blk] using hz
    have hzb := hbox z ((jBlock_eq_iff_mem_box hj z y).1 hz')
    have hxb : InBox d (ρ + L ^ j) ((N₁ * L ^ m₁) * L ^ K) x := inBox_mono (by omega) hx
    have := boxMap_inj (hm' := (by omega : 2 * (ρ + L ^ j) + 1 < (N₁' * L ^ m₁) * L ^ K)) hzb hxb hzx
    rw [← this]; exact hz'

/-- The entry of the averaging matrix of `levelGS j`. -/
theorem avgMatrix_levelGS_apply (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ)
    (x y : CTorus d L N₁ m₁ K) :
    avgMatrix (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a x y =
      (a j / ((L : ℝ) ^ j) ^ 2) *
        (if jBlock d L (N₁ * L ^ m₁) K j x = jBlock d L (N₁ * L ^ m₁) K j y
          then ((((L ^ j : ℕ) : ℝ)) ^ d)⁻¹ else 0) := by
  unfold avgMatrix
  rw [Matrix.sum_apply, Finset.sum_eq_single j]
  · simp [layerProjMatrix, layer_levelGS, blockProjMatrix, jBlock]
  · intro j' _ hne
    simp [layerProjMatrix, layer_levelGS, hne]
  · intro h
    exact absurd (Finset.mem_Icc.2 ⟨hj1, hj⟩) h

theorem avgMatrix_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K) {x y : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    avgMatrix (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a
        (bm x) (bm y) =
      avgMatrix (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a x y := by
  rw [avgMatrix_levelGS_apply hj1 hj, avgMatrix_levelGS_apply hj1 hj]
  have := jBlock_boxMap_iff (m₁ := m₁) hj hn hn' hx hy
  congr 1
  exact if_congr this.symm rfl rfl

/-- **The full cut matrix.**  The entries at two sites of the box of `-Δ + ν + Q* a Q` with a cut
removed correspond, if the two cuts correspond at the bonds based in the box of radius `ρ + 1`.
Margin: `2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem cutFullMatrix_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {cut : Finset (CTorus d L N₁ m₁ K × Fin d)} {cut' : Finset (CTorus d L N₁' m₁ K × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bm z, μ) ∈ cut'))
    {x y : CTorus d L N₁ m₁ K} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) y) :
    cutFullMatrix (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        cut' (bm x) (bm y) =
      cutFullMatrix (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        cut x y := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  unfold cutFullMatrix cutLaplacian
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [latticeLaplacian_apply, latticeLaplacian_apply, sum_bondMatrix_apply, sum_bondMatrix_apply,
    avgMatrix_boxMap hj1 hj a hn hn' hx hy]
  have e0 : bm x = bm y ↔ x = y :=
    ⟨boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K)) hx hy,
      fun h => by rw [h]⟩
  have e1 : ∀ μ : Fin d, (bm y = bm x + Pi.single μ 1) ↔ (y = x + Pi.single μ 1) := fun μ =>
    (step_boxMap_iff (r := ρ) (by omega) (by omega) hx hy μ).symm
  have e2 : ∀ μ : Fin d, (bm x = bm y + Pi.single μ 1) ↔ (x = y + Pi.single μ 1) := fun μ =>
    (step_boxMap_iff (r := ρ) (by omega) (by omega) hy hx μ).symm
  have e3 : ∀ μ : Fin d, bm (x - Pi.single μ 1) = bm x - Pi.single μ 1 := fun μ =>
    boxMap_sub_single (ρ := ρ) (by omega) (by omega) hx μ
  have e4 : ∀ μ : Fin d, ((bm x - Pi.single μ 1, μ) ∈ cut') ↔ ((x - Pi.single μ 1, μ) ∈ cut) := by
    intro μ
    rw [← e3 μ]
    exact (hcut _ (inBox_sub_single (by omega) hx μ) μ).symm
  have e5 : ∀ μ : Fin d, ((bm x, μ) ∈ cut') ↔ ((x, μ) ∈ cut) := fun μ =>
    (hcut x (inBox_mono (Nat.le_succ ρ) hx) μ).symm
  have e6 : ∀ μ : Fin d, ((bm y, μ) ∈ cut') ↔ ((y, μ) ∈ cut) := fun μ =>
    (hcut y (inBox_mono (Nat.le_succ ρ) hy) μ).symm
  simp only [e0, e1, e2, e4, e5, e6]

/-- **The cube cut.**  The cube cuts of two sets `Λ`, `Λ'` correspond at the bonds based in the box
of radius `ρ + 1`, if the sets correspond on the box of radius `ρ + 2`. -/
theorem cubeCut_boxMap_iff {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {Λ : Finset (CTorus d L N₁ m₁ K)} {Λ' : Finset (CTorus d L N₁' m₁ K)}
    (hΛ : ∀ w, InBox d (ρ + 2) ((N₁ * L ^ m₁) * L ^ K) w → (w ∈ Λ ↔ bm w ∈ Λ'))
    {z : CTorus d L N₁ m₁ K} (hz : InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z) (μ : Fin d) :
    ((z, μ) ∈ cubeCut (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) Λ ↔
      (bm z, μ) ∈ cubeCut (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        Λ') := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  have h0 := hΛ z (inBox_mono (by omega) hz)
  have h1 := hΛ (z + Pi.single μ 1) (inBox_add_single (by omega) hz μ)
  rw [boxMap_add_single (ρ := ρ + 1) (by omega) (by omega) hz μ] at h1
  simp only [mem_cubeCut, levelGS_mem_Ω_one hj1 hj, true_and, h0, h1]

/-- **The entries of the cut operator.**  For two sites of the box, the entries of the cut operators
on the two tori agree, if the cuts and the potentials correspond. -/
theorem cutOperator_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {cut : Finset (CTorus d L N₁ m₁ K × Fin d)} {cut' : Finset (CTorus d L N₁' m₁ K × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ K) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bm z, μ) ∈ cut'))
    {α : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    {α' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    (hα : ∀ x : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
      InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
        α' ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ = α x)
    (x y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1)
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    cutOperator (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        cut' α' ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
        ⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ =
      cutOperator (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        cut α x y := by
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  unfold cutOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [cutFullMatrix_boxMap hj1 hj a ν hn hn' hcut hx hy]
  by_cases hxy : x = y
  · subst hxy
    simp [hα x hx]
  · have h2 : ¬ (⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ :
        (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1) =
        ⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ := by
      intro h
      apply hxy
      have h3 := congrArg Subtype.val h
      exact Subtype.ext (boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K)) hx hy h3)
    simp [hxy, h2]

/-! ### The interaction box -/

omit [NeZero N₁'] in
theorem dvd_valMinAbs_sub_val {n : ℕ} [NeZero n] (c : ZMod n) :
    (n : ℤ) ∣ c.valMinAbs - (c.val : ℤ) := by
  have h : (((c.val : ℤ)) : ZMod n) = ((c.valMinAbs : ℤ) : ZMod n) := by
    simp [ZMod.coe_valMinAbs]
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h

omit [NeZero N₁'] in
/-- **The interaction box in centred coordinates.**  If the base point `y0` is in the box of radius
`ρ₀` and `2 (ρ₀ + 3 L^(j+m₁)) + 1 < N₁ L^m₁ L^K`, the interaction box of the centre `(j, y0)`
consists of the sites of the box of radius `ρ₀ + 3 L^(j+m₁)` whose centred coordinates are within
`5/2 L^(j+m₁)` of the centre `y0 + (L^(j+m₁) - 1)/2` (the periodic translations do not enter). -/
theorem mem_intBox_iff {j ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K) :
    x ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x ∧
        ∀ μ, |((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2| <
          5 / 2 * (L : ℝ) ^ (j + m₁) := by
  rw [mem_intBox]
  have hP : (1 : ℝ) ≤ (L : ℝ) ^ (j + m₁) :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hPn : (((L ^ (j + m₁) : ℕ)) : ℝ) = (L : ℝ) ^ (j + m₁) := by push_cast; rfl
  set n : ℕ := (N₁ * L ^ m₁) * L ^ K with hnn
  set E : ℕ := ρ₀ + 3 * L ^ (j + m₁) with hE
  have hEr : (E : ℝ) = ρ₀ + 3 * (L : ℝ) ^ (j + m₁) := by rw [hE]; push_cast; ring
  have key : ∀ μ : Fin d,
      (∃ p : ℤ, |((x μ).val : ℝ) + p * (n : ℝ) - (((y0 μ).val : ℝ) +
        ((L : ℝ) ^ (j + m₁) - 1) / 2)| < 5 / 2 * (L : ℝ) ^ (j + m₁)) ↔
      (|(x μ).valMinAbs| ≤ (E : ℤ) ∧ |((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs -
        ((L : ℝ) ^ (j + m₁) - 1) / 2| < 5 / 2 * (L : ℝ) ^ (j + m₁)) := by
    intro μ
    obtain ⟨k0, hk0⟩ := dvd_valMinAbs_sub_val (y0 μ)
    obtain ⟨k1, hk1⟩ := dvd_valMinAbs_sub_val (x μ)
    have hk0r : ((y0 μ).valMinAbs : ℝ) - (y0 μ).val = n * k0 := by exact_mod_cast hk0
    have hk1r : ((x μ).valMinAbs : ℝ) - (x μ).val = n * k1 := by exact_mod_cast hk1
    have hy1 : |((y0 μ).valMinAbs : ℝ)| ≤ ρ₀ := by exact_mod_cast hy0 μ
    constructor
    · rintro ⟨p, hp⟩
      -- the centred representative of `x μ`
      set t : ℤ := ((x μ).val : ℤ) + (p + k0) * (n : ℤ) with ht
      have htc : ((t : ℤ) : ZMod n) = x μ := by
        rw [ht]; push_cast; simp [hnn]
      have htr : (t : ℝ) = (x μ).val + (p + k0) * n := by rw [ht]; push_cast; ring
      have hc0 : (0 : ℝ) ≤ ((L : ℝ) ^ (j + m₁) - 1) / 2 := by linarith
      have hb1 : |(t : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2| <
          5 / 2 * (L : ℝ) ^ (j + m₁) := by
        have : (t : ℝ) - (y0 μ).valMinAbs - ((L : ℝ) ^ (j + m₁) - 1) / 2 =
            ((x μ).val : ℝ) + p * n - (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) := by
          rw [htr]; linear_combination (-1) * hk0r
        rw [this]; exact hp
      have hbt : |t| ≤ (E : ℤ) := by
        have h1 : |(t : ℝ)| ≤ E := by
          rw [abs_lt] at hb1
          rw [abs_le] at hy1 ⊢
          rw [hEr]
          constructor <;> linarith [hb1.1, hb1.2, hy1.1, hy1.2]
        exact_mod_cast h1
      have hvm : (x μ).valMinAbs = t := by
        rw [← htc]
        exact valMinAbs_intCast_of_abs_le (r := E) hn hbt
      rw [hvm]
      exact ⟨hbt, hb1⟩
    · rintro ⟨-, hb⟩
      refine ⟨k1 - k0, ?_⟩
      have : ((x μ).val : ℝ) + ((k1 - k0 : ℤ) : ℝ) * n - (((y0 μ).val : ℝ) +
          ((L : ℝ) ^ (j + m₁) - 1) / 2) = ((x μ).valMinAbs : ℝ) - (y0 μ).valMinAbs -
          ((L : ℝ) ^ (j + m₁) - 1) / 2 := by
        push_cast
        linear_combination (-1) * hk1r + hk0r
      rw [this]; exact hb
  unfold Balaban.Localization.InBox Balaban.Polymer.InBox
  simp only
  rw [← forall_and]
  exact forall_congr' fun μ => key μ

end Level

end Balaban.Polymer.TwoTorusStep
