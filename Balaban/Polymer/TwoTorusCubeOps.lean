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
  Balaban.Multiscale Balaban.Background Matrix

/-! ### Entries of the bond matrices and of the lattice Laplacian -/

section Entries

variable {d ℓ : ℕ} [NeZero ℓ]

omit [NeZero ℓ] in
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
      · simp
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

/-- **T1 (the interaction box).**  For a centre `(j, y0)` with `y0` in the box of radius `ρ₀` and
`R = ρ₀ + 3 L^(j+m₁)`, a site `x` of the box of radius `R` lies in the interaction box iff its image
lies in the interaction box of the image centre.  Margin: `2 R + 1 < N₁ L^m₁ L^K`, same for `N₁'`. -/
theorem mem_intBox_boxMap_iff {j ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (hx : InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x) :
    x ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      bm x ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) :=
    inBox_boxMap (by omega) hy0
  rw [mem_intBox_iff hy0 hn, mem_intBox_iff hy0' hn']
  have hR : ∀ w : CTorus d L N₁ m₁ K, InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) w →
      ∀ μ, (bm w μ).valMinAbs = (w μ).valMinAbs := fun w hw μ =>
    valMinAbs_boxMap (by omega) hw μ
  have hy1 := valMinAbs_boxMap (m' := (N₁' * L ^ m₁) * L ^ K) (by omega : 2 * ρ₀ + 1 < _) hy0
  constructor
  · rintro ⟨-, h2⟩
    refine ⟨inBox_boxMap (by omega) hx, fun μ => ?_⟩
    rw [hR x hx μ, hy1 μ]; exact h2 μ
  · rintro ⟨-, h2⟩
    refine ⟨hx, fun μ => ?_⟩
    have := h2 μ
    rw [hR x hx μ, hy1 μ] at this; exact this

/-- **T1 (`intBox_image`).**  `bm '' intBox q = intBox (Prod.map id bm q)` for `q = (j, y0)` with
`y0` in the box of radius `ρ₀`.  Margin: `2 (ρ₀ + 3 L^(j+m₁)) + 1 < N₁ L^m₁ L^K` and the same for
`N₁'`. -/
theorem intBox_image {j ρ₀ : ℕ} {y0 : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K) :
    bm '' (↑(intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) : Set (CTorus d L N₁ m₁ K)) =
      (↑(intBox (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K) :
        ℕ × CTorus d L N₁' m₁ K)) : Set (CTorus d L N₁' m₁ K)) := by
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) :=
    inBox_boxMap (by omega) hy0
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxb := ((mem_intBox_iff hy0 hn).1 (Finset.mem_coe.1 hx)).1
    exact (mem_intBox_boxMap_iff (N₁' := N₁') hy0 hn hn' hxb).1 hx
  · intro hw
    have hwb := ((mem_intBox_iff hy0' hn').1 (Finset.mem_coe.1 hw)).1
    have hb : bm' w = bm' w := rfl
    have hww : bm (bm' w) = w := boxMap_boxMap (by omega) hwb
    have hxb : InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) (bm' w) :=
      inBox_boxMap (by omega) hwb
    refine ⟨bm' w, ?_, hww⟩
    rw [Finset.mem_coe, mem_intBox_boxMap_iff (N₁' := N₁') hy0 hn hn' hxb, hww]
    exact Finset.mem_coe.1 hw

/-! ### The partition weight -/

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
theorem castT_boxMap {n n' n₂ n₂' : ℕ} (h : n = n₂) (h' : n' = n₂') (c : Torus d n) :
    castT h' (boxMap n n' c) = boxMap n₂ n₂' (castT h c) := by
  subst h h'; rfl

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
theorem inBox_castT_iff {n n₂ r : ℕ} (h : n = n₂) (c : Torus d n) :
    InBox d r n₂ (castT h c) ↔ InBox d r n c := by
  subst h; exact Iff.rfl

omit [NeZero N₁] [NeZero N₁'] [NeZero L] in
theorem tor_boxMap (x : CTorus d L N₁ m₁ K) :
    tor (N₁ := N₁') m₁ (bm x) =
      boxMap (N₁ * L ^ (K + m₁)) (N₁' * L ^ (K + m₁)) (tor (N₁ := N₁) m₁ x) :=
  castT_boxMap (cubeSide_eq N₁ L m₁ K) (cubeSide_eq N₁' L m₁ K) x

/-- **The cube bump on two tori.**  For `x` in the box of radius `ρ` and the base `y0` in the box of
radius `ρ₂`, with `ρ + ρ₂ + 3 L^(j+m₁) ≤ N₁ L^m₁ L^K` (and for `N₁'`), `2ρ + 1`, `2ρ₂ + 1` below
the side of the second torus. -/
theorem cubeBump_boxMap {j ρ ρ₂ : ℕ} {x y0 : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) (hy : InBox d ρ₂ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : ρ + ρ₂ + 3 * L ^ (j + m₁) ≤ (N₁ * L ^ m₁) * L ^ K)
    (hn' : ρ + ρ₂ + 3 * L ^ (j + m₁) ≤ (N₁' * L ^ m₁) * L ^ K)
    (hx' : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ K) (hy' : 2 * ρ₂ + 1 < (N₁' * L ^ m₁) * L ^ K) :
    cubeBump m₁ j (bm y0) (bm x) = cubeBump m₁ j y0 x := by
  unfold cubeBump
  rw [tor_boxMap, tor_boxMap]
  have e1 : N₁ * L ^ (K + m₁) = (N₁ * L ^ m₁) * L ^ K := (cubeSide_eq N₁ L m₁ K).symm
  have e2 : N₁' * L ^ (K + m₁) = (N₁' * L ^ m₁) * L ^ K := (cubeSide_eq N₁' L m₁ K).symm
  exact bump_boxMap (N₀ := N₁) (N₀' := N₁') (k := K + m₁) (j + m₁) _ _
    ((inBox_castT_iff _ _).2 hx) ((inBox_castT_iff _ _).2 hy) (by rw [e1]; exact hn)
    (by rw [e2]; exact hn') (by rw [e2]; exact hx') (by rw [e2]; exact hy')

omit [NeZero N₁'] in
/-- The base of a cube whose bump is nonzero at a site of the box of radius `ρ` lies in the box of
radius `ρ + 2 L^(j+m₁)`. -/
theorem inBox_base_of_cubeBump_ne_zero {j ρ : ℕ} {x y0 : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hn : 2 * (ρ + 2 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (h : cubeBump m₁ j y0 x ≠ 0) :
    InBox d (ρ + 2 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) y0 := by
  have e1 : N₁ * L ^ (K + m₁) = (N₁ * L ^ m₁) * L ^ K := (cubeSide_eq N₁ L m₁ K).symm
  have h1 := inBox_of_bump_ne_zero (N₀ := N₁) (k := K + m₁) (j + m₁) (tor m₁ x) (tor m₁ y0)
    ((inBox_castT_iff _ _).2 hx) (by rw [e1]; exact hn) h
  exact (inBox_castT_iff (cubeSide_eq N₁ L m₁ K) y0).1 h1

/-- **T1 (the partition weight, denominator).**  The denominator of the cover of `levelGS j`
agrees at a site of the box of radius `ρ` and at its image.  Margin:
`2 ρ + 5 L^(j+m₁) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem coverDenom_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 5 * L ^ (j + m₁) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ (j + m₁) + 1 < (N₁' * L ^ m₁) * L ^ K) {x : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x) :
    coverDenom (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) (bm x) =
      coverDenom (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) x := by
  set ρ' : ℕ := ρ + 2 * L ^ (j + m₁) with hρ'
  have hbx : InBox d ρ ((N₁' * L ^ m₁) * L ^ K) (bm x) := inBox_boxMap (by omega) hx
  unfold coverDenom
  have hA : ∑ q ∈ cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj),
      cubeBump m₁ q.1 q.2 x = ∑ q ∈ (cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := K) (ϱ := ϱ) j hj)).filter (fun q => InBox d ρ' ((N₁ * L ^ m₁) * L ^ K) q.2),
      cubeBump m₁ q.1 q.2 x := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hnq => ?_
    by_contra hne
    obtain ⟨y, rfl, -⟩ := exists_of_mem_cubeIdx hj hq
    exact hnq (Finset.mem_filter.2 ⟨hq, inBox_base_of_cubeBump_ne_zero hx (by omega) hne⟩)
  have hB : ∑ q ∈ cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj),
      cubeBump m₁ q.1 q.2 (bm x) = ∑ q ∈ (cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁')
        (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)).filter (fun q => InBox d ρ' ((N₁' * L ^ m₁) * L ^ K) q.2),
      cubeBump m₁ q.1 q.2 (bm x) := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) fun q hq hnq => ?_
    by_contra hne
    obtain ⟨y, rfl, -⟩ := exists_of_mem_cubeIdx hj hq
    exact hnq (Finset.mem_filter.2 ⟨hq, inBox_base_of_cubeBump_ne_zero hbx (by omega) hne⟩)
  have hinj : Set.InjOn (Prod.map id bm : ℕ × CTorus d L N₁ m₁ K → ℕ × CTorus d L N₁' m₁ K)
      ↑((cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)).filter
        (fun q => InBox d ρ' ((N₁ * L ^ m₁) * L ^ K) q.2)) := fun a ha b hb h =>
    injOn_idxMap (N₁ := N₁) (ρ := ρ')
      (lt_of_le_of_lt (by omega : 2 * ρ' + 1 ≤ 2 * ρ + 5 * L ^ (j + m₁) + 1) hn')
      (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 h
  rw [hA, hB, cubeIdx_filter_image (ϱ := ϱ) (ρ := ρ') hj1 hj
      (lt_of_le_of_lt (by omega : 2 * ρ' + 1 ≤ 2 * ρ + 5 * L ^ (j + m₁) + 1) hn)
      (lt_of_le_of_lt (by omega : 2 * ρ' + 1 ≤ 2 * ρ + 5 * L ^ (j + m₁) + 1) hn'),
    Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun q hq => ?_
  obtain ⟨hq1, hq2⟩ := Finset.mem_filter.1 hq
  obtain ⟨y, rfl, -⟩ := exists_of_mem_cubeIdx hj hq1
  exact cubeBump_boxMap (j := j) hx hq2 (by omega) (by omega) (by omega) (by omega)

/-- **T1 (`chi_boxMap`).**  The partition weight `chi` of the centre `(j, y0)` with `y0` in the box
of radius `ρ + 2 L^(j+m₁)` is the same at a site of the box of radius `ρ` and at its image under
`Prod.map id bm`.  Margin: `2 ρ + 5 L^(j+m₁) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem chi_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K)
    (hn : 2 * ρ + 5 * L ^ (j + m₁) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 5 * L ^ (j + m₁) + 1 < (N₁' * L ^ m₁) * L ^ K) {x y0 : CTorus d L N₁ m₁ K}
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) x)
    (hy0 : InBox d (ρ + 2 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) y0) :
    chi (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) (bm x) =
      chi (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) (j, y0) x := by
  unfold chi
  rw [coverDenom_boxMap hj1 hj hn hn' hx]
  congr 1
  exact cubeBump_boxMap (j := j) hx hy0 (by omega) (by omega) (by omega) (by omega)

/-- The interaction box correspondence for sites of any box of radius `R' ≥ ρ₀ + 3 L^(j+m₁)`.
Margin: `2 R' + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem mem_intBox_boxMap_iff_of_le {j ρ₀ R' : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0) (hRR : ρ₀ + 3 * L ^ (j + m₁) ≤ R')
    (hn : 2 * R' + 1 < (N₁ * L ^ m₁) * L ^ K) (hn' : 2 * R' + 1 < (N₁' * L ^ m₁) * L ^ K)
    (hx : InBox d R' ((N₁ * L ^ m₁) * L ^ K) x) :
    x ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
      bm x ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := by
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) :=
    inBox_boxMap (by omega) hy0
  have hn1 : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K :=
    lt_of_le_of_lt (by omega) hn
  have hn2 : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁' * L ^ m₁) * L ^ K :=
    lt_of_le_of_lt (by omega) hn'
  constructor
  · intro h
    have hxb := ((mem_intBox_iff hy0 hn1).1 h).1
    exact (mem_intBox_boxMap_iff (N₁' := N₁') hy0 hn1 hn2 hxb).1 h
  · intro h
    have hwb := ((mem_intBox_iff hy0' hn2).1 h).1
    have hv : ∀ μ, (bm x μ).valMinAbs = (x μ).valMinAbs := valMinAbs_boxMap (by omega) hx
    have hxb : InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x := fun μ => by
      rw [← hv μ]; exact hwb μ
    exact (mem_intBox_boxMap_iff (N₁' := N₁') hy0 hn1 hn2 hxb).2 h

/-- **T2 (Dirichlet operator).**  The entries at two sites of the box of radius `ρ` of
`dirichletOperator` correspond, for potentials with `α'(bm x) = α x` on the box.  Margin:
`2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem dirichletOperator_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    {α : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    {α' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    (hα : ∀ x : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
      InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
        α' ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ = α x)
    (x y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1)
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    dirichletOperator (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        a ν α' ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
        ⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ =
      dirichletOperator (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj)
        a ν α x y := by
  rw [← cutOperator_empty, ← cutOperator_empty]
  exact cutOperator_boxMap hj1 hj a ν hn hn' (fun z _ μ => by simp) hα x y hx hy

/-- **T2 (`cubeH_boxMap`).**  The entries of the cube operator `cubeH` of the centre `(j, y0)`,
`y0` in the box of radius `ρ₀`, at two sites of the box of radius `ρ`, correspond.  Margins, with
`R' = ρ + 2 + ρ₀ + 3 L^(j+m₁)`: `2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` and `2 R' + 1 < N₁ L^m₁ L^K` (and
for `N₁'`). -/
theorem cubeH_boxMap {ρ ρ₀ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hm : 2 * (ρ + 2 + (ρ₀ + 3 * L ^ (j + m₁))) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hm' : 2 * (ρ + 2 + (ρ₀ + 3 * L ^ (j + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ K)
    {α : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    {α' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    (hα : ∀ x : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
      InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
        α' ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ = α x)
    (x y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1)
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    cubeH (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν α'
        (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K))
        ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
        ⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ =
      cubeH (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν α
        (j, y0) x y := by
  unfold cubeH
  refine cutOperator_boxMap hj1 hj a ν hn hn' (fun z hz μ => ?_) hα x y hx hy
  exact cubeCut_boxMap_iff (ρ := ρ) hj1 hj hn hn' (Λ' := intBox ((j, bm y0) :
    ℕ × CTorus d L N₁' m₁ K)) (fun w hw => mem_intBox_boxMap_iff_of_le (N₁' := N₁')
      (R' := ρ + 2 + (ρ₀ + 3 * L ^ (j + m₁))) hy0 (by omega) hm hm'
      (inBox_mono (by omega) hw)) (z := z) (inBox_mono (by omega) hz) μ

/-- The entries of the commutator `Kz`: `(Kz) x y = H₀ x y (χ x - χ y)`. -/
theorem Kz_apply {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (a : ℕ → ℝ) (ν : ℝ)
    (q : ℕ × CTorus d L N₁ m₁ K) (x y : G.Ω 1) :
    Kz G a ν q x y = dirichletOperator G a ν 0 x y *
      (((chi G q x : ℝ) : ℂ) - ((chi G q y : ℝ) : ℂ)) := by
  unfold Kz chiD
  simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  ring

/-- **T2 (`Kz_boxMap`).**  The entries of the commutator `Kz` of the centre `(j, y0)`, `y0` in the
box of radius `ρ + 2 L^(j+m₁)`, at two sites of the box of radius `ρ`, correspond.  Margins:
`2 ρ + 3 L^K + 5 < N₁ L^m₁ L^K` and `2 ρ + 5 L^(j+m₁) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem Kz_boxMap {ρ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) (a : ℕ → ℝ) (ν : ℝ)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d (ρ + 2 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * ρ + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * ρ + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hm : 2 * ρ + 5 * L ^ (j + m₁) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hm' : 2 * ρ + 5 * L ^ (j + m₁) + 1 < (N₁' * L ^ m₁) * L ^ K)
    (x y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1)
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    Kz (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν
        (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K))
        ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
        ⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ =
      Kz (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν (j, y0)
        x y := by
  rw [Kz_apply, Kz_apply,
    dirichletOperator_boxMap hj1 hj a ν hn hn' (fun _ _ => rfl) x y hx hy]
  simp only [chi_boxMap hj1 hj hm hm' hx hy0, chi_boxMap hj1 hj hm hm' hy hy0]
  rfl

/-! ### The cube resolvent -/

omit [NeZero N₁'] in
/-- A site of the interaction box lies in the box of radius `ρ₀ + 3 L^(j+m₁)`. -/
theorem inBox_of_mem_intBox {j ρ₀ : ℕ} {y0 x : CTorus d L N₁ m₁ K}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hn : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 1 < (N₁ * L ^ m₁) * L ^ K)
    (hx : x ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)) :
    InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) x :=
  ((mem_intBox_iff hy0 hn).1 hx).1

theorem cubeBase_boxMap {y0 : CTorus d L N₁ m₁ K} (hj : j ≤ K) (hb : CubeBase (K := K) m₁ j y0) :
    CubeBase (K := K) m₁ j (bm y0) :=
  aligned_boxMap (pow_dvd_side hj N₁) (pow_dvd_side hj N₁') hb

/-- The column of `cubeG` is the image of a basis vector. -/
theorem cubeG_mulVec_single {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {α : G.Ω 1 → ℂ} (q : ℕ × CTorus d L N₁ m₁ K) (x y : G.Ω 1) :
    (cubeG G a ν α q *ᵥ Pi.single y 1) x = cubeG G a ν α q x y := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `cubeG` vanishes at the columns outside the interaction box. -/
theorem cubeG_apply_of_not_mem {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {α : G.Ω 1 → ℂ} (q : ℕ × CTorus d L N₁ m₁ K) (x y : G.Ω 1)
    (hy : (y : CTorus d L N₁ m₁ K) ∉ intBox q) : cubeG G a ν α q x y = 0 := by
  have h := congrFun (congrFun (cubeG_mul_cD (G := G) (a := a) (ν := ν) (α := α) q) x) y
  unfold cD at h
  rw [Matrix.mul_diagonal] at h
  simp only [hy, ↓reduceIte, mul_zero] at h
  exact h.symm

/-- **Inverse of corresponding blocks.**  Let `H`, `H'` be invertible matrices on two finite types,
`S`, `S'` two subsets matched by a map `ι` (injective on `S`, onto `S'`), such that `H'` and `H`
have the same entries on `S × S`, `H` maps vectors supported in `S` to vectors supported in `S`,
and `H'⁻¹ D'` has output supported in `S'` (`D`, `D'` the restrictions to `S`, `S'`).  Then the
entries of `H⁻¹ D` on `S × S` are those of `H'⁻¹ D'` at the images. -/
theorem inv_block_transport {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (S : A → Prop) (S' : B → Prop) [DecidablePred S] [DecidablePred S'] (ι : A → B)
    (hinj : ∀ a b, S a → S b → ι a = ι b → a = b) (hmap : ∀ a, S a → S' (ι a))
    (hsurj : ∀ b, S' b → ∃ a, S a ∧ ι a = b)
    (H : Matrix A A ℂ) (H' : Matrix B B ℂ) (D : Matrix A A ℂ) (D' : Matrix B B ℂ)
    (hD : ∀ f x, (D *ᵥ f) x = if S x then f x else 0)
    (hD' : ∀ f x, (D' *ᵥ f) x = if S' x then f x else 0)
    (hH : ∀ x z, S x → S z → H' (ι x) (ι z) = H x z)
    (hdec : ∀ u : A → ℂ, (∀ z, ¬ S z → u z = 0) → ∀ x, ¬ S x → (H *ᵥ u) x = 0)
    (hU : IsUnit H) (hU' : IsUnit H')
    (hsupp' : ∀ f z, ¬ S' z → ((H'⁻¹ * D') *ᵥ f) z = 0)
    {x y : A} (hx : S x) (hy : S y) :
    (H'⁻¹ * D') (ι x) (ι y) = (H⁻¹ * D) x y := by
  have hdet := (Matrix.isUnit_iff_isUnit_det _).1 hU
  have hdet' := (Matrix.isUnit_iff_isUnit_det _).1 hU'
  set v' : B → ℂ := (H'⁻¹ * D') *ᵥ Pi.single (ι y) 1 with hv'
  have hHv' : H' *ᵥ v' = D' *ᵥ Pi.single (ι y) 1 := by
    rw [hv', Matrix.mulVec_mulVec, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet', Matrix.one_mul]
  have hsum : ∀ f' : B → ℂ, ∑ z : A, (if S z then f' (ι z) else 0) =
      ∑ z' : B, (if S' z' then f' z' else 0) := by
    intro f'
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    refine Finset.sum_bij (fun z _ => ι z) (fun z hz => ?_) (fun a ha b hb h => ?_)
      (fun z' hz' => ?_) (fun _ _ => rfl)
    · exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hmap z (Finset.mem_filter.1 hz).2⟩
    · exact hinj a b (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 h
    · obtain ⟨a, ha, rfl⟩ := hsurj z' (Finset.mem_filter.1 hz').2
      exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩, rfl⟩
  set w : A → ℂ := fun z => if S z then v' (ι z) else 0 with hw
  have hHw : H *ᵥ w = D *ᵥ Pi.single y 1 := by
    funext x
    by_cases hxc : S x
    · rw [hD]
      simp only [hxc, ↓reduceIte]
      have e1 : (H *ᵥ w) x = ∑ z : A, if S z then H' (ι x) (ι z) * v' (ι z) else 0 := by
        simp only [Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun z _ => ?_
        by_cases hzc : S z
        · simp only [hw, hzc, ↓reduceIte]
          rw [hH x z hxc hzc]
        · simp [hw, hzc]
      rw [e1, hsum (fun z' => H' (ι x) z' * v' z')]
      have e2 : ∀ z' : B, (if S' z' then H' (ι x) z' * v' z' else 0) = H' (ι x) z' * v' z' := by
        intro z'
        by_cases hz : S' z'
        · simp [hz]
        · have : v' z' = 0 := hsupp' _ z' hz
          simp [this]
      rw [Finset.sum_congr rfl fun z' _ => e2 z']
      have e4 : (H' *ᵥ v') (ι x) = ∑ z', H' (ι x) z' * v' z' := by
        simp [Matrix.mulVec, dotProduct]
      rw [← e4, hHv', hD']
      simp only [hmap x hxc, ↓reduceIte]
      by_cases hxy : x = y
      · subst hxy; simp
      · have : ι x ≠ ι y := fun h => hxy (hinj x y hxc hy h)
        simp [hxy, this]
    · rw [hdec w (fun z hz => by simp [hw, hz]) x hxc, hD]
      simp [hxc]
  have hwv : w = (H⁻¹ * D) *ᵥ Pi.single y 1 := by
    rw [← Matrix.mulVec_mulVec, ← hHw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec]
  have h1 := congrFun hwv x
  simp only [hw, hx, ↓reduceIte] at h1
  have e5 : ∀ (M : Matrix B B ℂ) (a b : B), (M *ᵥ Pi.single b 1) a = M a b := fun M a b => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have e6 : ∀ (M : Matrix A A ℂ) (a b : A), (M *ᵥ Pi.single b 1) a = M a b := fun M a b => by
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  rw [e6] at h1
  rw [← h1, hv', e5]

/-- **T3 (`cubeG_boxMap`).**  The entries of the cube resolvent `cubeG = cubeH⁻¹ cD` of the centre
`(j, y0)` correspond at two sites of the box of radius `R = ρ₀ + 3 L^(j+m₁)` (in particular at
every pair of sites of the interaction box), for potentials with `α'(bm x) = α x` on the box of
radius `R`.  Hypotheses: the landed standing hypotheses of the cube operator on each torus
(`DGSetting`, `AdmPot`, the centre in `cubeIdx`), as in `cubeG_supp`.  Margins:
`2 R + 3 L^K + 5 < N₁ L^m₁ L^K` and `2 (R + 2 + R) + 1 < N₁ L^m₁ L^K` (and for `N₁'`). -/
theorem cubeG_boxMap {ρ₀ : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ K) {a : ℕ → ℝ} {ν : ℝ}
    (SA : DGSetting (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν)
    (SB : DGSetting (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν)
    {y0 : CTorus d L N₁ m₁ K} (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ K) y0)
    (hq : ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ∈
      cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj))
    (hn : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 3 * L ^ K + 5 < (N₁ * L ^ m₁) * L ^ K)
    (hn' : 2 * (ρ₀ + 3 * L ^ (j + m₁)) + 3 * L ^ K + 5 < (N₁' * L ^ m₁) * L ^ K)
    (hm : 2 * ((ρ₀ + 3 * L ^ (j + m₁)) + 2 + (ρ₀ + 3 * L ^ (j + m₁))) + 1 <
      (N₁ * L ^ m₁) * L ^ K)
    (hm' : 2 * ((ρ₀ + 3 * L ^ (j + m₁)) + 2 + (ρ₀ + 3 * L ^ (j + m₁))) + 1 <
      (N₁' * L ^ m₁) * L ^ K)
    {α : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    {α' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 → ℂ}
    (hαA : AdmPot _ α) (hαB : AdmPot _ α')
    (hα : ∀ x : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
      InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K) →
        α' ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ = α x)
    (x y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1)
    (hx : InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) (x : CTorus d L N₁ m₁ K))
    (hy : InBox d (ρ₀ + 3 * L ^ (j + m₁)) ((N₁ * L ^ m₁) * L ^ K) (y : CTorus d L N₁ m₁ K)) :
    cubeG (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν α'
        (Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K))
        ⟨bm (x : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩
        ⟨bm (y : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ =
      cubeG (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν α
        (j, y0) x y := by
  classical
  rw [show Prod.map id bm ((j, y0) : ℕ × CTorus d L N₁ m₁ K) = (j, bm y0) from rfl]
  obtain ⟨hK1, hjK⟩ := pow_facts (L := L) hj
  set R : ℕ := ρ₀ + 3 * L ^ (j + m₁) with hR
  have hn1 : 2 * R + 1 < (N₁ * L ^ m₁) * L ^ K := lt_of_le_of_lt (by omega) hn
  have hn2 : 2 * R + 1 < (N₁' * L ^ m₁) * L ^ K := lt_of_le_of_lt (by omega) hn'
  have hy0' : InBox d ρ₀ ((N₁' * L ^ m₁) * L ^ K) (bm y0) := inBox_boxMap (by omega) hy0
  have hq' : ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) ∈
      cubeIdx (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) := by
    obtain ⟨y1, he, hb⟩ := exists_of_mem_cubeIdx hj hq
    have : y0 = y1 := (Prod.mk.inj he).2
    subst this
    exact (mem_cubeIdx_levelGS hj _).2 ⟨rfl, hj1, cubeBase_boxMap hj hb⟩
  obtain ⟨ι, hι⟩ : ∃ ι : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1 → (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
      ∀ z, ι z = ⟨bm (z : CTorus d L N₁ m₁ K), levelGS_mem_Ω_one hj1 hj _⟩ := ⟨_, fun _ => rfl⟩
  rw [← hι, ← hι]
  have hcubeA : ∀ z : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1, (z : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) →
      InBox d R ((N₁ * L ^ m₁) * L ^ K) (z : CTorus d L N₁ m₁ K) :=
    fun z h => inBox_of_mem_intBox hy0 hn1 h
  have hcubeB : ∀ z : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1, (z : CTorus d L N₁' m₁ K) ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) →
      InBox d R ((N₁' * L ^ m₁) * L ^ K) (z : CTorus d L N₁' m₁ K) :=
    fun z h => inBox_of_mem_intBox hy0' hn2 h
  have hiff : ∀ z : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ K) (z : CTorus d L N₁ m₁ K) →
      ((z : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ↔
        ((ι z : _) : CTorus d L N₁' m₁ K) ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K)) := by
    intro z hz
    rw [hι]
    exact mem_intBox_boxMap_iff_of_le (N₁' := N₁') hy0 le_rfl hn1 hn2 hz
  have hinj : ∀ a b : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1, InBox d R ((N₁ * L ^ m₁) * L ^ K) (a : CTorus d L N₁ m₁ K) →
      InBox d R ((N₁ * L ^ m₁) * L ^ K) (b : CTorus d L N₁ m₁ K) → ι a = ι b → a = b := by
    intro a b ha hb h
    rw [hι, hι] at h
    exact Subtype.ext (boxMap_inj (hm' := hn2) ha hb (congrArg Subtype.val h))
  have hsurj : ∀ z' : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1, (z' : CTorus d L N₁' m₁ K) ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) →
      ∃ z : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1,
        (z : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) ∧ ι z = z' := by
    intro z' h
    have hb' := hcubeB z' h
    have hback : bm (bm' (z' : CTorus d L N₁' m₁ K)) = z' := boxMap_boxMap hn1 hb'
    obtain ⟨zz, hzz⟩ : ∃ zz : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K)
        (ϱ := ϱ) j hj).Ω 1, (zz : CTorus d L N₁ m₁ K) = bm' (z' : CTorus d L N₁' m₁ K) :=
      ⟨⟨_, levelGS_mem_Ω_one hj1 hj _⟩, rfl⟩
    have hz1 : InBox d R ((N₁ * L ^ m₁) * L ^ K) (zz : CTorus d L N₁ m₁ K) := by
      rw [hzz]; exact inBox_boxMap hn1 hb'
    have hιz : ι zz = z' := by
      rw [hι]
      refine Subtype.ext ?_
      show bm (zz : CTorus d L N₁ m₁ K) = _
      rw [hzz]; exact hback
    refine ⟨zz, (hiff zz hz1).2 (by rw [hιz]; exact h), hιz⟩
  have hcore : ∀ x y : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j
      hj).Ω 1, (x : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) →
      (y : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K) →
      cubeG (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν α'
        (j, bm y0) (ι x) (ι y) =
      cubeG (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := K) (ϱ := ϱ) j hj) a ν α
        (j, y0) x y := by
    intro x y hxc hyc
    unfold cubeG
    refine inv_block_transport (fun z : (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := K) (ϱ := ϱ) j hj).Ω 1 => (z : CTorus d L N₁ m₁ K) ∈
        intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K))
      (fun z : (levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := K) (ϱ := ϱ) j hj).Ω 1 =>
        (z : CTorus d L N₁' m₁ K) ∈ intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K)) ι
      (fun a b ha hb h => hinj a b (hcubeA a ha) (hcubeA b hb) h)
      (fun z hz => (hiff z (hcubeA z hz)).1 hz) hsurj _ _ _ _
      (fun f z => cD_mulVec _ f z) (fun f z => cD_mulVec _ f z) ?_ ?_
      (cubeH_isUnit SA hαA hq) (cubeH_isUnit SB hαB hq') ?_ hxc hyc
    · intro x z hx hz
      rw [hι, hι]
      exact cubeH_boxMap (ρ := R) (ρ₀ := ρ₀) hj1 hj a ν hy0 hn hn' hm hm' hα x z
        (hcubeA x hx) (hcubeA z hz)
    · intro u hu x hx
      exact cutOperator_mulVec_apply_of_not_mem _
        (box_blockAligned SA.aligned SA.cover_sep (by have := SA.hL; omega) hq) α hu x hx
    · intro f z hz
      exact cubeG_supp SB hαB hq' f z hz
  by_cases hyc : (y : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)
  · by_cases hxc : (x : CTorus d L N₁ m₁ K) ∈ intBox ((j, y0) : ℕ × CTorus d L N₁ m₁ K)
    · exact hcore x y hxc hyc
    · have hxc' : ¬ ((ι x : _) : CTorus d L N₁' m₁ K) ∈
          intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := fun h => hxc ((hiff x hx).2 h)
      have e1 := cubeG_supp SA hαA hq (Pi.single y 1) x hxc
      have e2 := cubeG_supp SB hαB hq' (Pi.single (ι y) 1) (ι x) hxc'
      rw [cubeG_mulVec_single] at e1 e2
      rw [e1]; exact e2
  · have hyc' : ¬ ((ι y : _) : CTorus d L N₁' m₁ K) ∈
        intBox ((j, bm y0) : ℕ × CTorus d L N₁' m₁ K) := fun h => hyc ((hiff y hy).2 h)
    rw [cubeG_apply_of_not_mem _ _ _ hyc, cubeG_apply_of_not_mem _ _ _ hyc']

end Level

end Balaban.Polymer.TwoTorusStep
