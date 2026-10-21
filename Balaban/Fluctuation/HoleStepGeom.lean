/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.HoleStepStanding
public import Balaban.Fluctuation.LocalClassLocal

/-!
# The geometric conditions of the locality of the re-expansion (cover of a cube-aligned set)

The locality theorem `HoleStep.oldInterp_localityAEOn` has two geometric hypotheses on the core `X₁`
and the localization domains `X₁loc b` of the read unit points `b`: a centre covering each read point
with its footprint in the core and in the domain of the point (`hcov`), and the interaction boxes of
the centres with footprint in a domain away from the complement of `Ω₁(G′)` (`hlocdeep`).  For a
cube-aligned `G′` (`M₁ = L^{m₁}`, `4 L² ≤ M₁`) both follow from balls of radius a few top cells
(`L^{k+1+m₁}`):

* `sameCell_cbase`, `exists_top_cube`: the top cube of a site of the top layer;
* `supDist_le_of_mem_Qset`: the footprint cubes of a centre lie within `hatRad + 3/2` cells of its base;
* `mem_intBox_of_sameCell`: a site of the cell of a centre lies in its interaction box;
* `HoleStep.hcov_of_balls`: **`hcov`** when the core and the domain of every read point contain the
  ball of radius `6 L^{k+1+m₁}` around it;
* `HoleStep.hlocdeep_of_deep`: **`hlocdeep`** when every domain lies in the sites whose
  `4 L^{k+1+m₁}`-ball is in `Ω₁(G′)`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- A site and the base of its cell lie in one cell. -/
theorem sameCell_cbase {a : ℕ} (ha : 0 < a) (x : CTorus d L N₁ m₁ (k + 1)) :
    SameCell a x (cbase a x) := by
  intro μ
  have hlt : a * ((x μ).val / a) < (N₁ * L ^ m₁) * L ^ (k + 1) :=
    lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  simp only [cbase]
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt, Nat.mul_div_cancel_left _ ha]

variable {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}

/-- **The top cube of a site of the top layer** of a cube-aligned generating set: the centre of the
cover at layer `k + 1` whose cell contains the site. -/
theorem exists_top_cube (hG : CubeAligned G m₁) {x : CTorus d L N₁ m₁ (k + 1)}
    (hx : x ∈ G.Ω (k + 1)) :
    ∃ q ∈ cubeIdx G, q.1 = k + 1 ∧ SameCell (L ^ (k + 1 + m₁)) x q.2 := by
  have hpos : 0 < L ^ (k + 1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  refine ⟨(k + 1, cbase (L ^ (k + 1 + m₁)) x), ?_, rfl, sameCell_cbase hpos x⟩
  have hlay : G.layer (k + 1) = G.Ω (k + 1) := by
    unfold GeneratingSet.layer
    rw [G.top, Finset.sdiff_empty]
  refine (mem_cubeIdx G).2 ⟨⟨by omega, le_rfl⟩, ?_, fun μ => aligned_cbase x μ⟩
  rw [hlay]
  exact (hG.union (k + 1) (by omega) le_rfl x _ (sameCell_cbase hpos x)).1 hx

/-- **The footprint cubes of a centre lie near its base**: a site of the cell of a centre `P` of the
footprint `𝒬(q)` is within `hatRad + ½ cell(q) + cell(P)` of the base of `q`. -/
theorem supDist_le_of_mem_Qset {q P : ℕ × CTorus d L N₁ m₁ (k + 1)} (hP : P ∈ Qset G q)
    {y : CTorus d L N₁ m₁ (k + 1)} (hy : y ∈ cubeP P) :
    (supDist q.2 y : ℝ) ≤ hatRad L m₁ q.1 + (L : ℝ) ^ (q.1 + m₁) / 2 + (L : ℝ) ^ (P.1 + m₁) := by
  obtain ⟨-, z, hzP, hzq⟩ := (Localization.mem_Qset (G := G)).1 hP
  have hR : (0 : ℝ) ≤ hatRad L m₁ q.1 := by unfold hatRad; positivity
  have h1 := supDist_le_of_inBox hR hzq
  have hcell : 0 < L ^ (P.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hyz : supDist z y ≤ L ^ (P.1 + m₁) :=
    supDist_le_of_sameCell hcell (hzP.trans ((mem_cubeP).1 hy).symm)
  have h2 := supDist_triangle q.2 z y
  rw [supDist_comm q.2 z] at h2
  have h2' : (supDist q.2 y : ℝ) ≤ (supDist z q.2 : ℝ) + (supDist z y : ℝ) := by exact_mod_cast h2
  have h3 : (supDist z y : ℝ) ≤ (L : ℝ) ^ (P.1 + m₁) := by exact_mod_cast hyz
  linarith

/-- A site of the cell of a centre lies in the interaction box of the centre. -/
theorem mem_intBox_of_sameCell {q : ℕ × CTorus d L N₁ m₁ (k + 1)} {x : CTorus d L N₁ m₁ (k + 1)}
    (h : SameCell (L ^ (q.1 + m₁)) x q.2) : x ∈ intBox q := by
  have hcell : 0 < L ^ (q.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have hc1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := by exact_mod_cast hcell
  -- the base lies in the box of radius one cell, and the site is within one cell of the base
  have h0 : InBox m₁ q.1 q.2 ((L : ℝ) ^ (q.1 + m₁)) q.2 := fun μ => ⟨0, by
    simp only [Int.cast_zero, zero_mul, add_zero]
    rw [show ((q.2 μ).val : ℝ) - (((q.2 μ).val : ℝ) + ((L : ℝ) ^ (q.1 + m₁) - 1) / 2)
        = -(((L : ℝ) ^ (q.1 + m₁) - 1) / 2) by ring, abs_neg, abs_of_nonneg (by linarith)]
    linarith⟩
  have hd : supDist q.2 x ≤ L ^ (q.1 + m₁) := supDist_le_of_sameCell hcell h.symm
  have h1 := inBox_of_supDist_le h0 hd
  rw [mem_intBox]
  refine h1.mono ?_
  push_cast
  linarith

namespace HoleStep

variable {N : ℕ} {ϱ'' : ℝ} (S : HoleStep d L N₁ m₁ k N ϱ'' ϱ)

/-- **The covering condition `hcov`** of `oldInterp_localityAEOn`, when `G′` is cube aligned
(`4 L² ≤ M₁`) and the core and the domain of every read point contain the ball of radius
`6 L^{k+1+m₁}` around it: the top cube of the read point covers it, and its footprint lies in the
ball. -/
theorem hcov_of_balls (hG : CubeAligned S.G' m₁) (hM : 4 * L ^ 2 ≤ L ^ m₁) {Rd : Finset S.U}
    {X₁ : Finset (CTorus d L N₁ m₁ (k + 1))} {X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : ∀ b ∈ Rd, ∀ y : CTorus d L N₁ m₁ (k + 1),
      supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) y ≤ 6 * L ^ (k + 1 + m₁) → y ∈ X₁)
    (hloc : ∀ b ∈ Rd, ∀ y : CTorus d L N₁ m₁ (k + 1),
      supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) y ≤ 6 * L ^ (k + 1 + m₁) → y ∈ X₁loc b) :
    ∀ b ∈ Rd, ∃ q ∈ (coverOf S.G').cubeIdx,
      (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ intBox q ∧
        ∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁ ∧ cubeP P ⊆ X₁loc b := by
  intro b hb
  have hx : (unitRep b : CTorus d L N₁ m₁ (k + 1)) ∈ S.G'.Ω (k + 1) :=
    ((S.G'.mem_layer).1 (S.unitRep_mem_top b)).1
  obtain ⟨q, hq, hq1, hcell⟩ := exists_top_cube hG hx
  have hcellq : SameCell (L ^ (q.1 + m₁)) (unitRep b : CTorus d L N₁ m₁ (k + 1)) q.2 := by
    rw [hq1]; exact hcell
  refine ⟨q, hq, mem_intBox_of_sameCell hcellq, fun P hP => ?_⟩
  have hP' : P ∈ Qset S.G' q := hP
  have hPC : P ∈ cubeIdx S.G' := ((Localization.mem_Qset (G := S.G')).1 hP').1
  have hP1 : P.1 ≤ k + 1 := ((mem_cubeIdx S.G').1 hPC).1.2
  have hLpos : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hcellP : (L : ℝ) ^ (P.1 + m₁) ≤ (L : ℝ) ^ (k + 1 + m₁) :=
    pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) (by omega)
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hbase : supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) q.2 ≤ L ^ (k + 1 + m₁) :=
    supDist_le_of_sameCell (pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _) hcell
  have hball : ∀ y ∈ cubeP P,
      supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) y ≤ 6 * L ^ (k + 1 + m₁) := by
    intro y hy
    have h1 := supDist_le_of_mem_Qset hP' hy
    rw [hq1] at h1
    have h2 := supDist_triangle (unitRep b : CTorus d L N₁ m₁ (k + 1)) q.2 y
    have h2' : (supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) y : ℝ) ≤
        (supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) q.2 : ℝ) + (supDist q.2 y : ℝ) := by
      exact_mod_cast h2
    have h3 : (supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) q.2 : ℝ) ≤
        (L : ℝ) ^ (k + 1 + m₁) := by exact_mod_cast hbase
    have hrad : hatRad L m₁ (k + 1) ≤ (13 / 4 : ℝ) * (L : ℝ) ^ (k + 1 + m₁) := by
      unfold hatRad
      have e : (L : ℝ) ^ (k + 1 + m₁) = (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := by rw [pow_add]
      have hk : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by positivity
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_left hM' hk]
    have : (supDist (unitRep b : CTorus d L N₁ m₁ (k + 1)) y : ℝ) ≤
        6 * (L : ℝ) ^ (k + 1 + m₁) := by linarith
    exact_mod_cast this
  exact ⟨fun y hy => hX₁ b hb y (hball y hy), fun y hy => hloc b hb y (hball y hy)⟩

/-- **The depth condition `hlocdeep`** of `oldInterp_localityAEOn`, when every domain of a read point
lies in the sites whose `4 L^{k+1+m₁}`-ball is in `Ω₁(G′)` (`4 L² ≤ M₁`): a centre with footprint in
the domain has its base in the domain (`q ∈ 𝒬(q)`) and its interaction box within three of its cells
of the base. -/
theorem hlocdeep_of_deep (hM : 4 * L ^ 2 ≤ L ^ m₁) {Rd : Finset S.U}
    {X₁loc : S.U → Finset (CTorus d L N₁ m₁ (k + 1))}
    (hdeep : ∀ b ∈ Rd, ∀ y ∈ X₁loc b, ∀ z : CTorus d L N₁ m₁ (k + 1),
      supDist y z ≤ 4 * L ^ (k + 1 + m₁) → z ∈ S.G'.Ω 1) :
    ∀ b ∈ Rd, ∀ q ∈ (coverOf S.G').cubeIdx,
      (∀ P ∈ (coverOf S.G').Qset q, cubeP P ⊆ X₁loc b) → ∀ x ∈ intBox q,
        ∀ z : CTorus d L N₁ m₁ (k + 1), supDist x z ≤ 4 * L ^ (k + 1) → z ∈ S.G'.Ω 1 := by
  intro b hb q hq hfoot x hx z hz
  have hqC : q ∈ cubeIdx S.G' := hq
  have hself : q ∈ (coverOf S.G').Qset q := self_mem_Qset_zeroCuts (G := S.G') hqC
  have hq2 : q.2 ∈ X₁loc b := hfoot q hself ((mem_cubeP).2 (SameCell.refl _ _))
  have hq1 : q.1 ≤ k + 1 := ((mem_cubeIdx S.G').1 hqC).1.2
  have hcell : (L : ℝ) ^ (q.1 + m₁) ≤ (L : ℝ) ^ (k + 1 + m₁) :=
    pow_le_pow_right₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)) (by omega)
  have hR : (0 : ℝ) ≤ 5 / 2 * (L : ℝ) ^ (q.1 + m₁) := by positivity
  have h1 := supDist_le_of_inBox hR (mem_intBox.1 hx)
  have h2 := supDist_triangle q.2 x z
  rw [supDist_comm q.2 x] at h2
  have h2' : (supDist q.2 z : ℝ) ≤ (supDist x q.2 : ℝ) + (supDist x z : ℝ) := by exact_mod_cast h2
  have h3 : (supDist x z : ℝ) ≤ 4 * (L : ℝ) ^ (k + 1) := by exact_mod_cast hz
  have hM' : (4 : ℝ) * (L : ℝ) ^ 2 ≤ (L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h4 : 4 * (L : ℝ) ^ (k + 1) ≤ (L : ℝ) ^ (k + 1 + m₁) := by
    have e : (L : ℝ) ^ (k + 1 + m₁) = (L : ℝ) ^ (k + 1) * (L : ℝ) ^ m₁ := by rw [pow_add]
    have hk : (0 : ℝ) ≤ (L : ℝ) ^ (k + 1) := by positivity
    have hL2 : (1 : ℝ) ≤ (L : ℝ) ^ 2 := one_le_pow₀ hL1
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hM' hk]
  have : (supDist q.2 z : ℝ) ≤ 4 * (L : ℝ) ^ (k + 1 + m₁) := by linarith
  exact hdeep b hb q.2 hq2 z (by exact_mod_cast this)

end HoleStep

end Balaban.Fluctuation
