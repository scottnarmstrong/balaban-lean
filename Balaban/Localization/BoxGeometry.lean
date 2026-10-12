/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled

/-!
# The interaction cube as a union of cells; block alignment

For a centre `z = (j, y₀)` (`CubeBase`: the coordinates of `y₀` are multiples of `B = M₁ ℓ_j =
L ^ (j + m₁)`) the interaction cube `□_z = intBox z` is described in terms of the cells of side `B`:
a point lies in `□_z` iff in each coordinate its cell index differs from that of `y₀` by at most `2`
(periodically).  Consequences: `□_z` is a union of cells of side `B` (`box_sameCell`), it lies in the
layers `≤ j + 1` (`layer_le_of_mem_box`), hence is a union of blocks of every layer meeting it
(`box_blockAligned`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The elementary real inequality behind the cell description. -/
theorem abs_lt_cell_iff {B : ℝ} (hB : 1 ≤ B) (m : ℤ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ B - 1) :
    |B * m + (r - (B - 1) / 2)| < 5 / 2 * B ↔ |m| ≤ 2 := by
  constructor
  · intro h
    rw [abs_lt] at h
    by_contra hm
    rw [not_le] at hm
    have h3 : (3 : ℝ) ≤ |(m : ℝ)| := by
      have : (3 : ℤ) ≤ |m| := by omega
      have h' : ((3 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) := by exact_mod_cast this
      simpa using h'
    rcases le_abs'.1 h3 with h4 | h4
    · nlinarith [h.1]
    · nlinarith [h.2]
  · intro h
    have h1 : |(m : ℝ)| ≤ 2 := by
      have : ((|m| : ℤ) : ℝ) ≤ ((2 : ℤ) : ℝ) := by exact_mod_cast h
      simpa using this
    rw [abs_le] at h1
    rw [abs_lt]
    constructor <;> nlinarith [h1.1, h1.2]

omit [NeZero N₁] [NeZero L] in
theorem pow_dvd_torusSide (j : ℕ) (hj : j ≤ K) : L ^ (j + m₁) ∣ (N₁ * L ^ m₁) * L ^ K := by
  have : L ^ (j + m₁) ∣ L ^ m₁ * L ^ K := by
    rw [← pow_add]; exact pow_dvd_pow L (by omega)
  exact this.trans ⟨N₁, by ring⟩

omit [NeZero N₁] in
/-- Coordinatewise form of `InBox`: the cell index of `x` is within `2` of that of `y₀`,
periodically. -/
theorem inBox_coord_iff {j : ℕ} (hj : j ≤ K) {y0 x : CTorus d L N₁ m₁ K}
    (hb : CubeBase m₁ j y0) (μ : Fin d) :
    (∃ p : ℤ, |((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2)| < 5 / 2 * (L : ℝ) ^ (j + m₁)) ↔
    ∃ p : ℤ, |(((x μ).val / L ^ (j + m₁) : ℕ) : ℤ) - (((y0 μ).val / L ^ (j + m₁) : ℕ) : ℤ) +
      p * ((((N₁ * L ^ m₁) * L ^ K) / L ^ (j + m₁) : ℕ) : ℤ)| ≤ 2 := by
  have hBpos : 0 < L ^ (j + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  obtain ⟨n, hn⟩ := pow_dvd_torusSide (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) j hj
  have hnn : ((N₁ * L ^ m₁) * L ^ K) / L ^ (j + m₁) = n := by
    rw [hn]; exact Nat.mul_div_cancel_left _ hBpos
  rw [hnn]
  set B : ℕ := L ^ (j + m₁) with hBdef
  have hB1 : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hBpos
  have hBr : ((L : ℝ) ^ (j + m₁)) = (B : ℝ) := by rw [hBdef]; push_cast; rfl
  set a : ℕ := (x μ).val / B with ha
  set r : ℕ := (x μ).val % B with hr
  set b : ℕ := (y0 μ).val / B with hbdef
  have hx : (x μ).val = B * a + r := (Nat.div_add_mod _ _).symm
  have hy : (y0 μ).val = B * b := by
    exact (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb μ))).symm
  have hrB : r < B := Nat.mod_lt _ hBpos
  have hNr : (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) = (B : ℝ) * n := by
    rw [hn]; push_cast; ring
  have hxr : ((x μ).val : ℝ) = (B : ℝ) * a + r := by exact_mod_cast hx
  have hyr : ((y0 μ).val : ℝ) = (B : ℝ) * b := by exact_mod_cast hy
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hr1 : (r : ℝ) ≤ B - 1 := by
    have : r + 1 ≤ B := hrB
    have : ((r + 1 : ℕ) : ℝ) ≤ B := by exact_mod_cast this
    push_cast at this; linarith
  refine exists_congr fun p => ?_
  have e : ((x μ).val : ℝ) + p * (((N₁ * L ^ m₁) * L ^ K : ℕ) : ℝ) -
      (((y0 μ).val : ℝ) + ((L : ℝ) ^ (j + m₁) - 1) / 2) =
      (B : ℝ) * ((a : ℤ) - (b : ℤ) + p * (n : ℤ) : ℤ) + ((r : ℝ) - ((B : ℝ) - 1) / 2) := by
    rw [hNr, hxr, hyr, hBr]; push_cast; ring
  rw [e, hBr, abs_lt_cell_iff hB1 _ hr0 hr1]

/-- Cell description of `□_z`. -/
theorem mem_box_iff_cell {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {x : CTorus d L N₁ m₁ K} :
    x ∈ intBox q ↔ ∀ μ, ∃ p : ℤ,
      |(((x μ).val / L ^ (q.1 + m₁) : ℕ) : ℤ) - (((q.2 μ).val / L ^ (q.1 + m₁) : ℕ) : ℤ) +
        p * ((((N₁ * L ^ m₁) * L ^ K) / L ^ (q.1 + m₁) : ℕ) : ℤ)| ≤ 2 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  rw [mem_intBox]
  unfold InBox
  exact forall_congr' fun μ => inBox_coord_iff hmK hb μ

/-- `□_z` is a union of cells of side `M₁ ℓ_j`. -/
theorem box_sameCell {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {x x' : CTorus d L N₁ m₁ K} (h : SameCell (L ^ (q.1 + m₁)) x x') :
    x ∈ intBox q ↔ x' ∈ intBox q := by
  rw [mem_box_iff_cell hq, mem_box_iff_cell hq]
  refine forall_congr' fun μ => ?_
  rw [h μ]

/-! ### Layers and block alignment -/

/-- The points of `□_z` lie in layers `≤ j + 1`. -/
theorem layer_le_of_mem_box (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ) (hL : 1 ≤ L)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K)
    {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n) (hb : x ∈ intBox q) : n ≤ q.1 + 1 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hbase⟩ := (mem_cubeIdx G).1 hq
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hdist := torusDist_le_of_inBox ((mem_intBox).1 hb)
  have hd1 : (0 : ℝ) ≤ d := by positivity
  have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hLr
  have := layer_bounds_cube m₁ G hϱ hm1 hmK hn1 hnK hx hl
    (hdist.trans (by
      have := mul_nonneg (mul_nonneg hd1 (le_trans zero_le_one hl1))
        (by linarith : (0 : ℝ) ≤ 4 - (5 / 2 + 1 / 2))
      nlinarith)) hL
  exact this.1

/-- **`□_z` is a union of blocks of every layer meeting it.** -/
theorem box_blockAligned (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    BlockAligned G (intBox q) := by
  intro j hj1 hjK x x' hx hbl
  by_cases hj : j ≤ q.1 + m₁
  · have hcell : SameCell (L ^ j) x' x := sameCell_of_jBlock_eq hjK hbl
    exact (box_sameCell hq
      ((hcell.symm).mono (pow_dvd_pow L hj))).symm.symm
  · have hx' : x' ∈ G.layer j := (G.mem_layer_iff hj1 hjK hbl).2 hx
    have hm1 : 1 ≤ m₁ := by have := hG.two_le; omega
    constructor
    · intro h
      have := layer_le_of_mem_box hϱ hL hq hj1 hjK hx h
      omega
    · intro h
      have := layer_le_of_mem_box hϱ hL hq hj1 hjK hx' h
      omega

/-! ### Interior points -/

theorem intTorus_add_aux {m : ℕ} (w w' : Fin d → ℤ) :
    (intTorus w : Torus d m) + intTorus w' = intTorus (w + w') := by
  funext μ; simp [intTorus_apply]

/-- `x` is an interior point of `□_z`: the points `x + w`, `‖w‖_∞ ≤ 2`, lie in `□_z`. -/
def Inner (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) : Prop :=
  ∀ w : Fin d → ℤ, (∀ μ, |(w μ : ℝ)| ≤ 2) → x + (intTorus w : CTorus d L N₁ m₁ K) ∈ intBox q

/-- **Interior of the cover.** If `y ∈ C_z` and `x` is a neighbour of `y` or in the `n`-block of
`y`, then `x` is an interior point of `□_z`. -/
theorem inner_of_near (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hM : 4 * L ^ 2 ≤ L ^ m₁) (hL : 1 ≤ L) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G)
    {n : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K) {x y : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (hy : InBox m₁ q.1 q.2 (3 / 2 * (L : ℝ) ^ (q.1 + m₁)) y)
    (hnear : (∃ μ, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) ∨ SameCell (L ^ n) x y) :
    Inner q x := by
  intro w hw
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : (1 : ℝ) ≤ (L : ℝ) ^ q.1 := one_le_pow₀ hLr
  have key : ∀ w' : Fin d → ℤ, x = y + (intTorus w' : CTorus d L N₁ m₁ K) →
      (∀ μ, |(w' μ : ℝ)| ≤ L * (L : ℝ) ^ q.1) →
      x + (intTorus w : CTorus d L N₁ m₁ K) ∈ intBox q := by
    intro w' hw' hbd
    rw [mem_intBox, hw', add_assoc, intTorus_add_aux]
    refine inBox_cov4 hM hy (w' + w) (fun μ => ?_)
    simp only [Pi.add_apply, Int.cast_add]
    have h1 := hbd μ
    have h2 := hw μ
    have h3 : (L : ℝ) * (L : ℝ) ^ q.1 ≤ 2 * (L : ℝ) ^ 2 * (L : ℝ) ^ q.1 - 1 := by
      have : (1 : ℝ) ≤ (L : ℝ) * (L : ℝ) ^ q.1 := by nlinarith
      nlinarith
    calc |(w' μ : ℝ) + w μ| ≤ |(w' μ : ℝ)| + |(w μ : ℝ)| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hbig : (1 : ℝ) ≤ L * (L : ℝ) ^ q.1 := by nlinarith
  rcases hnear with ⟨μ, hμ | hμ⟩ | hcell
  · refine key (Pi.single μ (-1)) ?_ (fun ν => ?_)
    · funext ν
      by_cases h : ν = μ <;> simp [hμ, intTorus_apply, h]
    · by_cases h : ν = μ
      · subst h; simp; linarith
      · simp [h]; linarith
  · refine key (Pi.single μ 1) ?_ (fun ν => ?_)
    · funext ν
      by_cases h : ν = μ <;> simp [hμ, intTorus_apply, h]
    · by_cases h : ν = μ
      · subst h; simp; linarith
      · simp [h]; linarith
  · have hlpos : 0 < L ^ n := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) n
    have hxy : y ∈ G.layer n := (G.mem_layer_iff hn1 hnK (jBlock_eq_of_sameCell hcell)).1 hx
    have hdist := torusDist_le_of_inBox hy
    have hd1 : (0 : ℝ) ≤ d := by positivity
    have hl1 : (1 : ℝ) ≤ (L : ℝ) ^ (q.1 + m₁) := one_le_pow₀ hLr
    have hbound := layer_bounds_cube m₁ G hϱ hm1 hmK hn1 hnK hxy hl
      (hdist.trans (by
        have := mul_nonneg (mul_nonneg hd1 (le_trans zero_le_one hl1))
          (by linarith : (0 : ℝ) ≤ 4 - (3 / 2 + 1 / 2))
        nlinarith)) hL
    obtain ⟨w', hw', hwb⟩ := exists_int_of_sameCell hlpos hcell
    refine key w' hw' (fun ν => ?_)
    have h1 := hwb ν
    have h2 : (L : ℝ) ^ n ≤ (L : ℝ) ^ (q.1 + 1) := pow_le_pow_right₀ hLr (by omega)
    have h3 : (((L ^ n : ℕ)) : ℝ) = (L : ℝ) ^ n := by push_cast; rfl
    rw [h3] at h1
    have h4 : (L : ℝ) ^ (q.1 + 1) = L * (L : ℝ) ^ q.1 := by ring
    linarith

end Balaban.Localization
