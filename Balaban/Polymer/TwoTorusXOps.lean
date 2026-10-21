/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGreenRows
public import Balaban.Localization.DecoupledXLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The x-variant operators on two tori (entries, cube operator, commutator)

The covariance of the step at scale `k` is built from the x-variant decoupled Green operator
`G_{k,x,s}(A) = G*_{x,s}(A) (1 - 𝒦_{x,s}(A))⁻¹` (`Gsx`) of the generating set `levelGS (k + 1)` of
the fine torus `CTorus d L N₁ m₁ (k + 1)` (the top level: every site lies in the layer `k + 1`).
For two such tori, identified on a centred box by `boxMap`, this file proves the x-variant forms of
the landed comparisons of `TwoTorusCubeOps` and `TwoTorusGreenRows` (W616):

* `xAvgMatrix_levelTop_apply`, `xAvgMatrix_boxMap`: the x-variant averaging form of the top level
  reads the blocks of side `L^k` and `L^(k+1)` only, and its entries correspond on the box;
* `cutXFullMatrix_boxMap`, `cutXOperator_boxMap`, `xDirichletOperator_boxMap`, `cubeHx_boxMap`,
  `Kzx_boxMap`, `cubeGx_boxMap`: the entries of the cut x-variant operator, of the cube operator
  `H_{k,x,z}(A)`, of the commutator `K^x_z` and of the cube resolvent `G^{(z)}_x(A) c_z`;
* `Gstarx_block`, `Kcalx_block` and their corollaries (one torus): the block identities
  `P G*_{x,s} = G*_{x,s} P`, `P 𝒦_{x,s} = 𝒦_{x,s} P` for the indicator `P` of a set `T` such that
  every active interaction cube lies inside `T` or avoids it;
* `Gstarx_boxMap_apply`, `Kcalx_boxMap_apply`, `Gsx_boxMap_rows`, `xGreen_rows_transport`: the
  rows of `G_{k,x,s}(A) f` on a component correspond (block-diagonal resolvent argument,
  `resolvent_rows_transport`).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Localization Balaban.Fluctuation Balaban.SmallField.Def6 Balaban.Polymer
  Balaban.Multiscale Balaban.Background Matrix

/-! ### The cube operators of the x-variant at the top level -/

section XLevel

variable {d L N₁ N₁' m₁ k : ℕ} [NeZero N₁] [NeZero N₁'] [NeZero L] {ϱ : ℝ}

local notation "bm" => boxMap ((N₁ * L ^ m₁) * L ^ (k + 1)) ((N₁' * L ^ m₁) * L ^ (k + 1))
local notation "bm'" => boxMap ((N₁' * L ^ m₁) * L ^ (k + 1)) ((N₁ * L ^ m₁) * L ^ (k + 1))
local notation "GA" => levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "GB" => levelGS (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (k := k + 1) (ϱ := ϱ)
  (k + 1) le_rfl
local notation "ιb" x:max => Subtype.mk (bm (x : CTorus d L N₁ m₁ (k + 1)))
  (levelGS_mem_Ω_one (d := d) (L := L) (N₁ := N₁') (m₁ := m₁) (K := k + 1) (ϱ := ϱ)
    (Nat.le_add_left 1 k) le_rfl _)

omit [NeZero N₁'] in
/-- **The x-variant averaging form of the top level.**  For `levelGS (k + 1)` (every site in the
layer `k + 1`) the form reads the blocks of side `L^k` (weight `s₁`) and `L^(k+1)` (weight
`s₂ - s₁`). -/
theorem xAvgMatrix_levelTop_apply (a : ℕ → ℝ) (s₁ s₂ : ℝ) (x y : CTorus d L N₁ m₁ (k + 1)) :
    xAvgMatrix (GA) a s₁ s₂ x y =
      (s₁ / ((L : ℝ) ^ k) ^ 2) *
        (if jBlock d L (N₁ * L ^ m₁) (k + 1) k x = jBlock d L (N₁ * L ^ m₁) (k + 1) k y
          then ((((L ^ k : ℕ) : ℝ)) ^ d)⁻¹ else 0) +
      ((s₂ - s₁) / ((L : ℝ) ^ k) ^ 2) *
        (if jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x =
            jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) y
          then ((((L ^ (k + 1) : ℕ) : ℝ)) ^ d)⁻¹ else 0) := by
  unfold xAvgMatrix
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul]
  have h0 : ∀ j ∈ Finset.Icc 1 k, a j / ((L : ℝ) ^ j) ^ 2 * layerBlockMatrix (GA) j j x y = 0 := by
    intro j hj
    have : j ≠ k + 1 := by have := (Finset.mem_Icc.1 hj).2; omega
    simp [layerBlockMatrix, layer_levelGS, this]
  rw [Finset.sum_eq_zero h0, zero_add]
  simp [layerBlockMatrix, layer_levelGS, blockProjMatrix, jBlock]

/-- The entries of the x-variant averaging form of the top level correspond on the box.  Margin:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem xAvgMatrix_boxMap {ρ : ℕ} (a : ℕ → ℝ) (s₁ s₂ : ℝ)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    xAvgMatrix (GB) a s₁ s₂ (bm x) (bm y) = xAvgMatrix (GA) a s₁ s₂ x y := by
  rw [xAvgMatrix_levelTop_apply, xAvgMatrix_levelTop_apply]
  have h1 := jBlock_boxMap_iff (m₁ := m₁) (j := k) (by omega) hn hn' hx hy
  have h2 := jBlock_boxMap_iff (m₁ := m₁) (j := k + 1) le_rfl hn hn' hx hy
  rw [if_congr h1.symm rfl rfl, if_congr h2.symm rfl rfl]

/-- **The full cut x-variant matrix.**  Its entries at two sites of the box correspond, if the two
cuts correspond at the bonds based in the box of radius `ρ + 1`.  Margin:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem cutXFullMatrix_boxMap {ρ : ℕ} (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)}
    {cut' : Finset (CTorus d L N₁' m₁ (k + 1) × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bm z, μ) ∈ cut'))
    {x y : CTorus d L N₁ m₁ (k + 1)} (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) x)
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) y) :
    cutXFullMatrix (GB) a aT x₀ ν cut' (bm x) (bm y) =
      cutXFullMatrix (GA) a aT x₀ ν cut x y := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold cutXFullMatrix cutLaplacian
  simp only [Matrix.add_apply, Matrix.sub_apply]
  rw [latticeLaplacian_apply, latticeLaplacian_apply, sum_bondMatrix_apply, sum_bondMatrix_apply,
    xAvgMatrix_boxMap a _ _ hn hn' hx hy]
  have e0 : bm x = bm y ↔ x = y :=
    ⟨boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))) hx hy,
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

/-- **The entries of the cut x-variant operator** at two sites of the box correspond, if the cuts
correspond and the potentials correspond on the box. -/
theorem cutXOperator_boxMap {ρ : ℕ} (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {cut : Finset (CTorus d L N₁ m₁ (k + 1) × Fin d)}
    {cut' : Finset (CTorus d L N₁' m₁ (k + 1) × Fin d)}
    (hcut : ∀ z, InBox d (ρ + 1) ((N₁ * L ^ m₁) * L ^ (k + 1)) z → ∀ μ : Fin d,
      ((z, μ) ∈ cut ↔ (bm z, μ) ∈ cut'))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)) →
      α' (ιb x) = α x)
    (x y : (GA).Ω 1) (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1))) :
    cutXOperator (GB) a aT x₀ ν cut' α' (ιb x) (ιb y) = cutXOperator (GA) a aT x₀ ν cut α x y := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  unfold cutXOperator Green.restrictOp
  simp only [Matrix.add_apply, Matrix.submatrix_apply, Matrix.map_apply, Matrix.diagonal_apply]
  rw [cutXFullMatrix_boxMap a aT x₀ ν hn hn' hcut hx hy]
  by_cases hxy : x = y
  · subst hxy
    simp [hα x hx]
  · have h2 : ¬ (ιb x : (GB).Ω 1) = ιb y := by
      intro h
      apply hxy
      have h3 := congrArg Subtype.val h
      exact Subtype.ext
        (boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))) hx hy h3)
    simp [hxy, h2]

/-- **The entries of the x-variant operator** `H_{k,x}(A)` at two sites of the box correspond, for
potentials corresponding on the box. -/
theorem xDirichletOperator_boxMap {ρ : ℕ} (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)) →
      α' (ιb x) = α x)
    (x y : (GA).Ω 1) (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1))) :
    xDirichletOperator (GB) a aT x₀ ν α' (ιb x) (ιb y) =
      xDirichletOperator (GA) a aT x₀ ν α x y := by
  rw [← cutXOperator_empty, ← cutXOperator_empty]
  exact cutXOperator_boxMap a aT x₀ ν hn hn' (fun z _ μ => by simp) hα x y hx hy

/-- The entries of `H_{k,x}(A)` in a row whose potential corresponds: only the diagonal entry reads
the potential. -/
theorem xDirichletOperator_boxMap_row {ρ : ℕ} (a : ℕ → ℝ) (aT x₀ ν : ℝ)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ} (x y : (GA).Ω 1) (hαx : α' (ιb x) = α x)
    (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1))) :
    xDirichletOperator (GB) a aT x₀ ν α' (ιb x) (ιb y) =
      xDirichletOperator (GA) a aT x₀ ν α x y := by
  have hK1 : 1 ≤ L ^ (k + 1) := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hdec : ∀ {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} (β : G.Ω 1 → ℂ) (u v : G.Ω 1),
      xDirichletOperator G a aT x₀ ν β u v =
        xDirichletOperator G a aT x₀ ν 0 u v + if u = v then β u else 0 := by
    intro G β u v
    unfold xDirichletOperator
    simp [Matrix.diagonal_apply]
  have hdec' : ∀ {G : GeneratingSet d L (N₁' * L ^ m₁) (k + 1) ϱ} (β : G.Ω 1 → ℂ) (u v : G.Ω 1),
      xDirichletOperator G a aT x₀ ν β u v =
        xDirichletOperator G a aT x₀ ν 0 u v + if u = v then β u else 0 := by
    intro G β u v
    unfold xDirichletOperator
    simp [Matrix.diagonal_apply]
  rw [hdec' α', hdec α, xDirichletOperator_boxMap (α := (0 : (GA).Ω 1 → ℂ)) (α' := 0) a aT x₀ ν
    hn hn' (fun _ _ => rfl) x y hx hy]
  by_cases hxy : x = y
  · subst hxy
    simp [hαx]
  · have h2 : ¬ (ιb x : (GB).Ω 1) = ιb y := by
      intro h
      apply hxy
      have h3 := congrArg Subtype.val h
      exact Subtype.ext
        (boxMap_inj (hm' := (by omega : 2 * ρ + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))) hx hy h3)
    simp [hxy, h2]

/-- **The x-variant cube operator** `H_{k,x,z}(A)` of the centre `(k+1, y0)`: its entries at two
sites of the box of radius `ρ` correspond.  Margins, with `R' = ρ + 2 + ρ₀ + 3 L^(k+1+m₁)`:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 R' + 1 < N₁ L^m₁ L^(k+1)` (and for `N₁'`). -/
theorem cubeHx_boxMap {ρ ρ₀ : ℕ} (a : ℕ → ℝ) (aT x₀ ν : ℝ) {y0 : CTorus d L N₁ m₁ (k + 1)}
    (hy0 : InBox d ρ₀ ((N₁ * L ^ m₁) * L ^ (k + 1)) y0)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hm : 2 * (ρ + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * (ρ + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    {α : (GA).Ω 1 → ℂ} {α' : (GB).Ω 1 → ℂ}
    (hα : ∀ x : (GA).Ω 1, InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)) →
      α' (ιb x) = α x)
    (x y : (GA).Ω 1) (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1))) :
    cubeHx (GB) a aT x₀ ν α' (Prod.map id bm ((k + 1, y0) : ℕ × CTorus d L N₁ m₁ (k + 1)))
        (ιb x) (ιb y) =
      cubeHx (GA) a aT x₀ ν α (k + 1, y0) x y := by
  unfold cubeHx
  refine cutXOperator_boxMap a aT x₀ ν hn hn' (fun z hz μ => ?_) hα x y hx hy
  exact cubeCut_boxMap_iff (ρ := ρ) (Nat.le_add_left 1 k) le_rfl hn hn'
    (Λ' := intBox ((k + 1, bm y0) : ℕ × CTorus d L N₁' m₁ (k + 1)))
    (fun w hw => mem_intBox_boxMap_iff_of_le (N₁' := N₁')
      (R' := ρ + 2 + (ρ₀ + 3 * L ^ (k + 1 + m₁))) hy0 (by omega) hm hm'
      (inBox_mono (by omega) hw)) (z := z) (inBox_mono (by omega) hz) μ

/-- **The x-variant commutator** `K^x_z` of the centre `(k+1, y0)`, `y0` in the box of radius
`ρ + 2 L^(k+1+m₁)`: its entries at two sites of the box of radius `ρ` correspond.  Margins:
`2 ρ + 3 L^(k+1) + 5 < N₁ L^m₁ L^(k+1)` and `2 ρ + 5 L^(k+1+m₁) + 1 < N₁ L^m₁ L^(k+1)` (and for
`N₁'`). -/
theorem Kzx_boxMap {ρ : ℕ} (a : ℕ → ℝ) (aT x₀ ν : ℝ) {y0 : CTorus d L N₁ m₁ (k + 1)}
    (hy0 : InBox d (ρ + 2 * L ^ (k + 1 + m₁)) ((N₁ * L ^ m₁) * L ^ (k + 1)) y0)
    (hn : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hn' : 2 * ρ + 3 * L ^ (k + 1) + 5 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (hm : 2 * ρ + 5 * L ^ (k + 1 + m₁) + 1 < (N₁ * L ^ m₁) * L ^ (k + 1))
    (hm' : 2 * ρ + 5 * L ^ (k + 1 + m₁) + 1 < (N₁' * L ^ m₁) * L ^ (k + 1))
    (x y : (GA).Ω 1) (hx : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (x : CTorus d L N₁ m₁ (k + 1)))
    (hy : InBox d ρ ((N₁ * L ^ m₁) * L ^ (k + 1)) (y : CTorus d L N₁ m₁ (k + 1))) :
    Kzx (GB) a aT x₀ ν (Prod.map id bm ((k + 1, y0) : ℕ × CTorus d L N₁ m₁ (k + 1))) (ιb x) (ιb y) =
      Kzx (GA) a aT x₀ ν (k + 1, y0) x y := by
  rw [Kzx_apply a aT x₀ ν 0, Kzx_apply a aT x₀ ν 0,
    xDirichletOperator_boxMap a aT x₀ ν hn hn' (fun _ _ => rfl) x y hx hy]
  simp only [chi_boxMap (Nat.le_add_left 1 k) le_rfl hm hm' hx hy0,
    chi_boxMap (Nat.le_add_left 1 k) le_rfl hm hm' hy hy0]
  rfl

/-- The column of `cubeGx` is the image of a basis vector. -/
theorem cubeGx_mulVec_single {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ}
    {aT x₀ ν : ℝ} {α : G.Ω 1 → ℂ} (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (x y : G.Ω 1) :
    (cubeGx G a aT x₀ ν α q *ᵥ Pi.single y 1) x = cubeGx G a aT x₀ ν α q x y := by
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `cubeGx` vanishes at the columns outside the interaction box. -/
theorem cubeGx_apply_of_not_mem {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ} {a : ℕ → ℝ}
    {aT x₀ ν : ℝ} {α : G.Ω 1 → ℂ} (q : ℕ × CTorus d L N₁ m₁ (k + 1)) (x y : G.Ω 1)
    (hy : (y : CTorus d L N₁ m₁ (k + 1)) ∉ intBox q) : cubeGx G a aT x₀ ν α q x y = 0 := by
  have h := congrFun (congrFun (cubeGx_mul_cD (G := G) (a := a) (aT := aT) (x := x₀) (ν := ν)
    (α := α) q) x) y
  unfold cD at h
  rw [Matrix.mul_diagonal] at h
  simp only [hy, ↓reduceIte, mul_zero] at h
  exact h.symm

end XLevel

end Balaban.Polymer.TwoTorusStep
