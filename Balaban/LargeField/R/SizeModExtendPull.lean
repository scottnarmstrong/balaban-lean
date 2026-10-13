/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.RRipeCard
public import Balaban.Fluctuation.SizeModExtend
import Mathlib.Tactic.Linarith

/-!
# The fine lift of a set of cubes is a union of cells; the region-growth inequality for it

`d7Pull_isPiUnion`: for a set `Y` of cubes of `𝕋_k` the fine set `d7Pull F k Y` is a union of
cells of side `cellSide` (the block index is constant on a cell).  Consequently the region-growth
inequality `Fluctuation.dcovMod_le_add_of_region_grow` applies to the fine lifts of the raw and
post regions (`dcovMod_d7Pull_le_add`), the component hypothesis being the only input that the
operation `R` has to supply.  Nothing about the operation `R` is proved here.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Localization Def7

section Pull

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {M K m₀ m₁ : ℕ} [NeZero S.L]
  (F : FineSizeFrame S n M K m₀ m₁)

/-- The cube index is constant on a cell with aligned base. -/
theorem cubeIdx_cell (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {b : Balaban.Localization.CTorus S.d S.L F.N₁ m₁ K} (hb : Aligned (cellSide S.L m₀ m₁ k) b) {w : Fin S.d → ℕ}
    (hw : ∀ μ, w μ < cellSide S.L m₀ m₁ k) : cubeIdx F k (b + natT w) = cubeIdx F k b := by
  have hside := fine_side_eq F hnn hkK
  have hcs : cellSide S.L m₀ m₁ k = S.L ^ k * M := by
    unfold cellSide; rw [F.hM, ← pow_add]; congr 1; ring
  funext μ
  simp only [cubeIdx_apply, Pi.add_apply, natT_apply]
  rw [← hcs]
  have := blockIdx_add (nk := n k) (by rw [hside]) (b μ) (w μ) (hb μ)
  rw [this, Nat.div_eq_of_lt (hw μ)]
  simp

/-- **The fine lift `d7Pull F k Y` of a set of cubes of `𝕋_k` is a union of cells.** -/
theorem d7Pull_isPiUnion (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    (Y : Set (Torus S.d (n k))) : Fluctuation.IsPiUnion m₀ k (d7Pull F k Y) := by
  have ha0 := cellSide_pos (L := S.L) m₀ m₁ k
  intro z hz
  refine ⟨cbase (cellSide S.L m₀ m₁ k) z, aligned_cbase z, mem_box_cbase ha0 z, ?_⟩
  have hz' : cubeIdx F k (cbase (cellSide S.L m₀ m₁ k) z) ∈ Y := by
    obtain ⟨w, hw, hzw⟩ := mem_box_cbase ha0 z
    have := cubeIdx_cell F hnn hkK (aligned_cbase z) hw
    rw [← hzw] at this
    exact this ▸ hz
  rintro x ⟨w, hw, rfl⟩
  rw [d7Pull_iff, cubeIdx_cell F hnn hkK (aligned_cbase z) hw]
  exact hz'

/-- **The region-growth inequality for fine lifts.**  For coarse sets `Ym`, `Yp` (the raw and
post regions in the application to `R`) and a coarse set `X` whose fine lift is in `𝒟_k`, if
every cell-component of the fine lift of `X ∩ Ymᶜ` lies in the fine lift of `Yp` or misses it,
then the modular sizes satisfy the inequality of `Fluctuation.dcovMod_le_add_of_region_grow`.
The component hypothesis (in terms of fine cells) is the input that the operation `R` has to
supply; it is not proved here. -/
theorem dcovMod_d7Pull_le_add (hnn : ∀ i, i < K → n i = S.L * n (i + 1)) {k : ℕ} (hkK : k ≤ K)
    {Ym Yp X : Set (Torus S.d (n k))}
    (hX : Fluctuation.IsDj m₀ k (d7Pull F k X))
    (hsplit : ∀ Q ∈ Fluctuation.cellComps m₀ k (d7Pull F k X ∩ (d7Pull F k Ym)ᶜ),
      Q ⊆ d7Pull F k Yp ∨ Disjoint Q (d7Pull F k Yp)) :
    Fluctuation.dcovMod m₀ k (d7Pull F k Yp) (d7Pull F k X) ≤
      Fluctuation.dcovMod m₀ k (d7Pull F k Ym) (d7Pull F k X) +
        ((S.d : ℝ) * S.L + S.d + 3) *
          ((Fluctuation.cellsIn m₀ k
            (d7Pull F k X ∩ (d7Pull F k Yp \ d7Pull F k Ym))).card : ℝ) :=
  Fluctuation.dcovMod_le_add_of_region_grow F.divN₁ hkK hX (d7Pull_isPiUnion F hnn hkK Ym)
    (d7Pull_isPiUnion F hnn hkK Yp) hsplit

end Pull

end Balaban.LargeField
