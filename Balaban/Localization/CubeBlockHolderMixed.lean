/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldHolderCut
public import Balaban.Localization.CubeBlockBoundsMixed
public import Balaban.Localization.DecoupledCubeHolder

/-!
# `CubeBlockHolder` at a mixed physical wall (VMOD-10 Theorem 1.1)

`Dec2.cubeBlockHolder_mixed`: for an operator generating set `H` with `OpSetting H a ν`, an admissible
potential and a cube index `q` of a common cover (a cube index of a generating set `F` of the same torus,
`N₁ > 5`) whose interaction cube is `BlockAligned H`, the cut solution of the cube operator of `H`
satisfies the two-centre Hölder estimate `CubeBlockHolder` with the constant `K_h = mixedKh d L`, whatever
the position of the physical Dirichlet wall. `Dec2.cubeBlocks_mixed`: both `CubeBlockBounds` and
`CubeBlockHolder` at the same cube. `Dec2.coverBase_mixed`: a constructor of `Dec2.CoverBase` from the
cover geometry `CoverGeom`.
-/

@[expose] public section

namespace Balaban.Localization.Dec2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}

/-- **VMOD-10 Theorem 1.1 (the `CubeBlockHolder` field at a mixed physical wall).** -/
theorem cubeBlockHolder_mixed (hN : 5 < N₁) (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ')
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (S : OpSetting H a ν)
    {α : H.Ω 1 → ℂ} (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F)
    (hba : BlockAligned H (intBox q)) : CubeBlockHolder H a ν α q (mixedKh d L) := by
  classical
  have hd := S.hd
  have hL := S.hL
  obtain ⟨hϱ, hsepL⟩ := sep_consequences hd hL S.sep
  obtain ⟨⟨hm1, hmK⟩, -, -⟩ := (mem_cubeIdx F).1 hq
  have hbox := box_eq_cubeSet hN hq
  have hLpos : 0 < L ^ (q.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have : NeZero (5 * L ^ (q.1 + m₁)) := ⟨by positivity⟩
  have h6 := torusSide_ge (L := L) (m₁ := m₁) hN hmK
  have hSℓ : 5 * L ^ (q.1 + m₁) < (N₁ * L ^ m₁) * L ^ K := by omega
  have hSB : 5 * L ^ (q.1 + m₁) + L ^ (q.1 + m₁) ≤ (N₁ * L ^ m₁) * L ^ K := by omega
  have hB : 2 ≤ L ^ (q.1 + m₁) := by
    have : L ≤ L ^ (q.1 + m₁) := Nat.le_self_pow (by omega) L
    omega
  have hΛ : BlockAligned H (cubeSet ((N₁ * L ^ m₁) * L ^ K) (5 * L ^ (q.1 + m₁)) (boxCorner q)) := by
    rw [← hbox]; exact hba
  have hαa : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (H.spacing x) ^ 2) := hα
  refine ⟨fun {θ} hθ0 hθ1 {j'} {y'} hj'1 hj'k hy' hy'b f hsupp {Mf} hMf0 hMf {x} {x'} hxΩ hx'Ω hxb
    hx'b {μ} hxe hx'e hlay {z} hxz hz1 hzB => ?_⟩
  rw [hbox] at hy'b hxb hx'b hxe hx'e
  have hzB' : ‖z‖ < ((L ^ (q.1 + m₁) : ℕ) : ℝ) := by push_cast; exact hzB
  have hcore := cubeFold_holder_cut hd hL hϱ hsepL S.mass S.massLe S.weights hαa
    (5 * L ^ (q.1 + m₁)) (boxCorner q) hSℓ hΛ hB hSB hj'1 hj'k hy' hy'b hsupp hMf0 hMf hxΩ hx'Ω
    hxb hx'b hxe hx'e hlay hxz hz1 hzB' hθ0 hθ1
  rw [← hbox] at hcore
  exact hcore

/-- **VMOD-9 Theorem 1.1 and VMOD-10 Theorem 1.1 at the same cube**: both the three-field estimate
`CubeBlockBounds` and the two-centre Hölder estimate `CubeBlockHolder` of the cube operator of `H`,
whatever the position of the physical Dirichlet wall. -/
theorem cubeBlocks_mixed (hN : 5 < N₁) (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ')
    {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ} (S : OpSetting H a ν)
    {α : H.Ω 1 → ℂ} (hα : AdmPot H α) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx F)
    (hba : BlockAligned H (intBox q)) :
    CubeBlockBounds H a ν α q (mixedKc d L) ∧ CubeBlockHolder H a ν α q (mixedKh d L) :=
  ⟨cubeBlockBounds_mixed hN F S hα hq hba, cubeBlockHolder_mixed hN F S hα hq hba⟩

/-- **A `CoverBase` for a generating set whose wall is unrestricted.** Given the cover geometry
(`CoverGeom`) of a cover `C` whose cube indices are cube indices of a generating set `F` of the same
torus (the common cover), the property `nc` of `CoverBase` holds with the constant `K_c`, at any
position of the physical wall of `H`. -/
theorem coverBase_mixed (hN : 5 < N₁) (F : GeneratingSet d L (N₁ * L ^ m₁) K ϱ')
    {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    {Cx : ℝ} (G : CoverGeom C H a ν Cx) (hC : ∀ q ∈ C.cubeIdx, q ∈ cubeIdx F) :
    CoverBase C H a ν (mixedKc d L) Cx where
  toCoverGeom := G
  nc := fun {_} hα q hq => (cubeBlockBounds_mixed hN F G.toOpSetting hα (hC q hq)
    (G.blockAligned q hq))

end Balaban.Localization.Dec2
