/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapIdentCells
public import Balaban.Polymer.TwoTorusWideBand
public import Balaban.Fluctuation.LevelLocalCover
public import Balaban.Fluctuation.CubeSystem

/-!
# Cells of the root box and of the cover of a site (blocker 7)

The torus has `K` cells of side `a` per direction (`n = a K` sites); the cell of a site `x` is
`(x.val / a : ZMod K)`, with centred coordinates `valMinAbs`.

* `cell_add_natCast`: the cell of `y + w` is `(y.val + w) / a` modulo `K`.
* `cell_of_mem_box`: a site of the box `b + [0, L a)^d` of an aligned base `b` lies in a cell
  `cell(b) + j`, `0 ≤ j ≤ L - 1`.
* `cell_of_mem_cellNbhd`: a site of the neighbourhood `cellNbhd L a B` of an aligned base `B` lies in a
  cell `cell(B) + j - (L - 1)`, `0 ≤ j ≤ 2 (L - 1)`.
* `cbase_val_div`: the base of the cell of side `a` of `z` lies in the same cell of side `a M`.
* `rootBox_geom`, `cellNbhd_geom`: the distance and quarter-box conditions of the gap-scale clauses
  for the root box (resp. the cover of a site) together with the sites of the cells of `X`, when the
  cell of the root (resp. of the site) lies in `X`, `X` has spread `S` and lies `L` cells inside the
  quarter box.
* `natAbs_valMinAbs_intCast`, `card_ge_of_not_spread`: a polymer of the quarter box whose spread
  exceeds `S` has at least `S + 2` cells.
* `exists_cubes_of_cells`: the cubes of the cells of a support exist (the hypothesis on `Ycub` of the
  gap-scale clauses is satisfiable).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer Balaban.Localization

section Cells

variable {d : ℕ}

/-- **The cell of a translate.**  The cell of `y + w` is `(y.val + w) / a` modulo `K`. -/
theorem cell_add_natCast {a K : ℕ} [NeZero a] [NeZero K] (y : ZMod (a * K)) (w : ℕ) :
    ((((y + (w : ZMod (a * K))).val / a : ℕ)) : ZMod K) = ((((y.val + w) / a : ℕ)) : ZMod K) := by
  have h1 : y + (w : ZMod (a * K)) = ((y.val + w : ℕ) : ZMod (a * K)) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  rw [h1, ZMod.val_natCast, Nat.mod_mul_right_div_self, ZMod.natCast_mod]

/-- **The cells of a box of `L` cells.**  A site of `b + [0, L a)^d`, `b` aligned to `a`, lies in the
cell `cell(b) + j` with `j ≤ L - 1`. -/
theorem cell_of_mem_box {a K L : ℕ} [NeZero a] [NeZero K] {b : Balaban.Torus d (a * K)}
    (hb : Aligned a b) {x : Balaban.Torus d (a * K)} (hx : x ∈ box b (L * a)) (μ : Fin d) :
    ∃ j : ℕ, j + 1 ≤ L ∧ ((((x μ).val / a : ℕ)) : ZMod K) =
      ((((b μ).val / a : ℕ)) : ZMod K) + (j : ZMod K) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨w μ / a, ?_, ?_⟩
  · have : w μ / a < L := (Nat.div_lt_iff_lt_mul ha).2 (hw μ)
    omega
  · simp only [Pi.add_apply, natT_apply]
    rw [cell_add_natCast]
    obtain ⟨r, hr⟩ : ∃ r, (b μ).val = a * r :=
      ⟨_, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hb μ))).symm⟩
    rw [hr, Nat.mul_add_div ha, Nat.mul_div_cancel_left _ ha, Nat.cast_add]

/-- **The cells of the neighbourhood of a cell.**  A site of `cellNbhd L a B`, `B` aligned to `a`,
lies in the cell `c` with `c + (L - 1) = cell(B) + j`, `j ≤ 2 (L - 1)`. -/
theorem cell_of_mem_cellNbhd {a K L : ℕ} [NeZero a] [NeZero K] (hL : 1 ≤ L)
    {B : Balaban.Torus d (a * K)} (hB : Aligned a B) {x : Balaban.Torus d (a * K)}
    (hx : x ∈ cellNbhd L a B) (μ : Fin d) :
    ∃ j : ℕ, j ≤ 2 * (L - 1) ∧ ((((x μ).val / a : ℕ)) : ZMod K) + ((L - 1 : ℕ) : ZMod K) =
      ((((B μ).val / a : ℕ)) : ZMod K) + (j : ZMod K) := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  obtain ⟨w, hw, hxw⟩ := hx
  refine ⟨w μ / a, ?_, ?_⟩
  · have h2 : (L - 1) * a + L * a = (2 * L - 1) * a := by
      rw [← Nat.add_mul]; congr 1; omega
    have : w μ / a < 2 * L - 1 := (Nat.div_lt_iff_lt_mul ha).2 (h2 ▸ hw μ)
    omega
  · have hsum : x μ + (((L - 1) * a : ℕ) : ZMod (a * K)) = B μ + ((w μ : ℕ) : ZMod (a * K)) := by
      rw [hxw]; simp only [Pi.add_apply, Pi.sub_apply, natT_apply]; ring
    have e1 := cell_add_natCast (K := K) (x μ) ((L - 1) * a)
    have e2 := cell_add_natCast (K := K) (B μ) (w μ)
    rw [hsum, Nat.add_mul_div_right _ _ ha] at e1
    obtain ⟨r, hr⟩ : ∃ r, (B μ).val = a * r :=
      ⟨_, (Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hB μ))).symm⟩
    rw [hr, Nat.mul_add_div ha] at e2
    have h3 := e1.symm.trans e2
    rw [hr, Nat.mul_div_cancel_left _ ha]
    push_cast at h3 ⊢
    exact h3

/-- **The base of a cell in a coarser cell.**  For `0 < a`, the base `cbase a z` lies in the same
cell of side `a M` as `z`. -/
theorem cbase_val_div {n a M : ℕ} [NeZero n] (ha : 0 < a) (z : Balaban.Torus d n) (μ : Fin d) :
    ((cbase a z) μ).val / (a * M) = (z μ).val / (a * M) := by
  have hlt : a * ((z μ).val / a) < n := lt_of_le_of_lt (Nat.mul_div_le _ _) (ZMod.val_lt _)
  have h : ((cbase a z) μ).val = a * ((z μ).val / a) := by
    simp only [cbase]; rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
  rw [h, Nat.mul_div_mul_left _ _ ha, Nat.div_div_eq_div_mul]

/-- The centred coordinate of an integer of absolute value at most `K / 2`. -/
theorem natAbs_valMinAbs_intCast {K : ℕ} [NeZero K] {δ : ℤ} (h : 2 * |δ| ≤ K) :
    (((δ : ℤ) : ZMod K)).valMinAbs.natAbs = δ.natAbs := by
  have h1 : δ ≤ |δ| := le_abs_self δ
  have h2 : -δ ≤ |δ| := neg_le_abs δ
  have hK0 : (0 : ℤ) < K := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne K)
  by_cases h3 : δ * 2 = -(K : ℤ)
  · have : (((δ : ℤ) : ZMod K)).valMinAbs = -δ := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨?_, ?_⟩
      · rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
        exact ⟨1, by linarith⟩
      · rw [Set.mem_Ioc]; constructor <;> linarith
    rw [this, Int.natAbs_neg]
  · have : (((δ : ℤ) : ZMod K)).valMinAbs = δ := by
      rw [ZMod.valMinAbs_spec]
      refine ⟨rfl, ?_⟩
      rw [Set.mem_Ioc]
      constructor <;> omega
    rw [this]

/-- **A wide polymer of the quarter box has many cells.**  If the cells `X` of an animal `Y` lie in
the quarter box and two of them are more than `S` apart in a coordinate, `X` has at least `S + 2`
cells. -/
theorem card_ge_of_not_spread {K S : ℕ} [NeZero K] {Y : Finset (Balaban.Torus d K)}
    (hA : IsAnimal (blockGraph d K) Y)
    (hQ : ∀ x ∈ Y.image (fun b μ => (b μ).valMinAbs), ∀ μ, (x μ).natAbs ≤ K / 4)
    (hw : ¬ ∀ c ∈ Y.image (fun b μ => (b μ).valMinAbs), ∀ c' ∈ Y.image (fun b μ => (b μ).valMinAbs),
      ∀ μ, |c μ - c' μ| ≤ (S : ℤ)) :
    S + 2 ≤ (Y.image (fun b μ => (b μ).valMinAbs)).card := by
  push Not at hw
  obtain ⟨c, hc, c', hc', μ, hlt⟩ := hw
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hc
  obtain ⟨b', hb', rfl⟩ := Finset.mem_image.1 hc'
  have hinj : Function.Injective (fun (b : Balaban.Torus d K) μ => (b μ).valMinAbs) := by
    intro x y hxy
    funext ν
    have := congrFun hxy ν
    simpa [ZMod.coe_valMinAbs] using congrArg (fun t : ℤ => (t : ZMod K)) this
  rw [Finset.card_image_of_injective _ hinj]
  have h1 := card_ge_of_spread Y hA hb' hb μ
  have he : b μ - b' μ = (((b μ).valMinAbs - (b' μ).valMinAbs : ℤ) : ZMod K) := by
    simp
  have hq1 : |(b μ).valMinAbs| ≤ ((K / 4 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hQ _ hc μ
  have hq2 : |(b' μ).valMinAbs| ≤ ((K / 4 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast hQ _ hc' μ
  rw [abs_le] at hq1 hq2
  have hK4 : 4 * (K / 4) ≤ K := Nat.mul_div_le K 4
  have h2 : 2 * |(b μ).valMinAbs - (b' μ).valMinAbs| ≤ K := by
    have h5 : |(b μ).valMinAbs - (b' μ).valMinAbs| ≤ 2 * ((K / 4 : ℕ) : ℤ) := by
      rw [abs_le]; constructor <;> linarith
    have h6 : (4 : ℤ) * ((K / 4 : ℕ) : ℤ) ≤ K := by exact_mod_cast hK4
    linarith
  rw [he, natAbs_valMinAbs_intCast h2] at h1
  have hlt' : (S : ℤ) < |(b μ).valMinAbs - (b' μ).valMinAbs| := hlt
  have h3 : ((S + 1 : ℕ) : ℤ) ≤ (((b μ).valMinAbs - (b' μ).valMinAbs).natAbs : ℤ) := by
    rw [Int.natCast_natAbs]; push_cast; linarith
  have h4 : S + 1 ≤ ((b μ).valMinAbs - (b' μ).valMinAbs).natAbs := by exact_mod_cast h3
  omega

end Cells

section Geom

variable {d : ℕ}

/-- **The root box at a compact support.**  Let the cell of the aligned base `b` be `r0 ∈ X`, let `X`
have spread at most `S` and lie `L` cells inside the quarter box, `S + L - 1 ≤ Dc ≤ (K - 26) / 25`,
and let every site of `Ys` lie in a cell of `X`.  Then sites of the box `b + [0, L a)^d` and of
`Ys` are at centred distance at most `a (Dc + 1) - 1` from the sites of the box, and all have
centred coordinates at most `a (K / 4 + 1)`. -/
theorem rootBox_geom {n a K L S Dc : ℕ} [NeZero n] [NeZero a] [NeZero K] (hn : n = a * K)
    (hK : 26 ≤ K) (hL : 1 ≤ L) {b : Balaban.Torus d n} (hb : Aligned a b) {r0 : Fin d → ℤ}
    (hr0 : (fun μ => (((((b μ).val / a : ℕ)) : ZMod K)).valMinAbs) = r0) (X : Set (Fin d → ℤ))
    (hrX : r0 ∈ X) (hXq : ∀ c ∈ X, ∀ μ, (c μ).natAbs + L ≤ K / 4)
    (hXs : ∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ S) (hS : S + L - 1 ≤ Dc)
    (hD : Dc ≤ (K - 26) / 25) (Ys : Set (Balaban.Torus d n))
    (hYs : ∀ y ∈ Ys, (fun μ => (((((y μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X) :
    (∀ x ∈ box b (L * a), ∀ y ∈ box b (L * a) ∪ Ys, ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ ((a * (Dc + 1) - 1 : ℕ) : ℤ)) ∧
    (∀ x ∈ box b (L * a) ∪ Ys, ∀ μ, |(x μ).valMinAbs| ≤ ((a * (K / 4 + 1) : ℕ) : ℤ)) := by
  subst hn
  set XR : Set (Fin d → ℤ) := X ∪ {c | ∀ μ, r0 μ ≤ c μ ∧ c μ ≤ r0 μ + ((L - 1 : ℕ) : ℤ)} with hXR
  have hr0q := hXq r0 hrX
  have hbox : ∀ x ∈ box b (L * a), (fun μ => (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ XR := by
    intro x hx
    refine Or.inr fun μ => ?_
    obtain ⟨j, hj, hc⟩ := cell_of_mem_box (K := K) hb hx μ
    have hb' : ((((b μ).val / a : ℕ)) : ZMod K) = ((r0 μ : ℤ) : ZMod K) := by
      rw [← hr0]; exact (ZMod.coe_valMinAbs _).symm
    have hv : ((((x μ).val / a : ℕ)) : ZMod K) = ((r0 μ + j : ℤ) : ZMod K) := by
      rw [hc, hb']; push_cast; ring
    have hsmall : 2 * (K / 4) + 1 < K := by omega
    have hrμ := hr0q μ
    have hval : ((((x μ).val / a : ℕ)) : ZMod K).valMinAbs = r0 μ + j := by
      rw [hv]
      exact valMinAbs_intCast_of_abs_le hsmall (by rw [abs_le]; constructor <;> omega)
    simp only
    rw [hval]
    constructor <;> omega
  have hq : ∀ c ∈ XR, ∀ μ, (c μ).natAbs ≤ K / 4 := by
    rintro c (hc | hc) μ
    · have := hXq c hc μ; omega
    · have h1 := hc μ
      have := hr0q μ
      omega
  have hs : ∀ c ∈ XR, ∀ c' ∈ XR, ∀ μ, |c μ - c' μ| ≤ Dc := by
    have hr := fun c (hc : c ∈ X) μ => hXs c hc r0 hrX μ
    rintro c (hc | hc) c' (hc' | hc') μ
    · have := hXs c hc c' hc' μ; rw [abs_le] at this ⊢; constructor <;> omega
    · have h1 := hr c hc μ; have h2 := hc' μ; rw [abs_le] at h1 ⊢; constructor <;> omega
    · have h1 := hr c' hc' μ; have h2 := hc μ; rw [abs_le] at h1 ⊢; constructor <;> omega
    · have h1 := hc μ; have h2 := hc' μ; rw [abs_le]; constructor <;> omega
  have hmem : ∀ y ∈ box b (L * a) ∪ Ys,
      (fun μ => (((((y μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ XR := by
    rintro y (hy | hy)
    · exact hbox y hy
    · exact Or.inl (hYs y hy)
  refine ⟨fun x hx y hy μ => ?_, fun x hx μ => ?_⟩
  · exact cell_spread_le rfl hK hD XR hq hs (hbox x hx) (hmem y hy) μ
  · exact cell_box_le rfl hK XR hq (hmem x hx) μ

/-- **The cover of a site at a compact support.**  Let the cell of the aligned base `B` be
`x0 ∈ X`, let `X` have spread at most `S` and lie `L` cells inside the quarter box,
`S + L - 1 ≤ Dc`, `2 (L - 1) ≤ Dc ≤ (K - 26) / 25`, and let every site of `Ys` lie in a cell of `X`.
Then the sites of `cellNbhd L a B` and of `Ys` are at centred distance at most `a (Dc + 1) - 1`
from the sites of `cellNbhd L a B`, and all have centred coordinates at most `a (K / 4 + 1)`. -/
theorem cellNbhd_geom {n a K L S Dc : ℕ} [NeZero n] [NeZero a] [NeZero K] (hn : n = a * K)
    (hK : 26 ≤ K) (hL : 1 ≤ L) {B : Balaban.Torus d n} (hB : Aligned a B) {x0 : Fin d → ℤ}
    (hx0 : (fun μ => (((((B μ).val / a : ℕ)) : ZMod K)).valMinAbs) = x0) (X : Set (Fin d → ℤ))
    (hxX : x0 ∈ X) (hXq : ∀ c ∈ X, ∀ μ, (c μ).natAbs + L ≤ K / 4)
    (hXs : ∀ c ∈ X, ∀ c' ∈ X, ∀ μ, |c μ - c' μ| ≤ S) (hS : S + L - 1 ≤ Dc)
    (hL2 : 2 * (L - 1) ≤ Dc) (hD : Dc ≤ (K - 26) / 25) (Ys : Set (Balaban.Torus d n))
    (hYs : ∀ y ∈ Ys, (fun μ => (((((y μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ X) :
    (∀ x ∈ cellNbhd L a B, ∀ y ∈ cellNbhd L a B ∪ Ys, ∀ μ,
      |(x μ - y μ).valMinAbs| ≤ ((a * (Dc + 1) - 1 : ℕ) : ℤ)) ∧
    (∀ x ∈ cellNbhd L a B ∪ Ys, ∀ μ, |(x μ).valMinAbs| ≤ ((a * (K / 4 + 1) : ℕ) : ℤ)) := by
  subst hn
  set XO : Set (Fin d → ℤ) := X ∪ {c | ∀ μ, |c μ - x0 μ| ≤ ((L - 1 : ℕ) : ℤ)} with hXO
  have hx0q := hXq x0 hxX
  have hnb : ∀ x ∈ cellNbhd L a B, (fun μ => (((((x μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ XO := by
    intro x hx
    refine Or.inr fun μ => ?_
    obtain ⟨j, hj, hc⟩ := cell_of_mem_cellNbhd (K := K) hL hB hx μ
    have hb' : ((((B μ).val / a : ℕ)) : ZMod K) = ((x0 μ : ℤ) : ZMod K) := by
      rw [← hx0]; exact (ZMod.coe_valMinAbs _).symm
    have hv : ((((x μ).val / a : ℕ)) : ZMod K) = ((x0 μ + j - ((L - 1 : ℕ) : ℤ) : ℤ) : ZMod K) := by
      have := hc
      rw [hb'] at this
      push_cast
      linear_combination this
    have hsmall : 2 * (K / 4) + 1 < K := by omega
    have hxμ := hx0q μ
    have hval : ((((x μ).val / a : ℕ)) : ZMod K).valMinAbs = x0 μ + j - ((L - 1 : ℕ) : ℤ) := by
      rw [hv]
      exact valMinAbs_intCast_of_abs_le hsmall (by
        rw [abs_le]; push_cast [Nat.cast_sub hL]; constructor <;> omega)
    simp only
    rw [hval, abs_le]
    push_cast [Nat.cast_sub hL]
    constructor <;> omega
  have hq : ∀ c ∈ XO, ∀ μ, (c μ).natAbs ≤ K / 4 := by
    rintro c (hc | hc) μ
    · have := hXq c hc μ; omega
    · have h1 := hc μ
      have := hx0q μ
      rw [abs_le] at h1
      push_cast [Nat.cast_sub hL] at h1
      omega
  have hs : ∀ c ∈ XO, ∀ c' ∈ XO, ∀ μ, |c μ - c' μ| ≤ Dc := by
    have hr := fun c (hc : c ∈ X) μ => hXs c hc x0 hxX μ
    rintro c (hc | hc) c' (hc' | hc') μ
    · have := hXs c hc c' hc' μ; rw [abs_le] at this ⊢; constructor <;> omega
    · have h1 := hr c hc μ; have h2 := hc' μ
      rw [abs_le] at h1 h2 ⊢; push_cast [Nat.cast_sub hL] at h2; constructor <;> omega
    · have h1 := hr c' hc' μ; have h2 := hc μ
      rw [abs_le] at h1 h2 ⊢; push_cast [Nat.cast_sub hL] at h2; constructor <;> omega
    · have h1 := hc μ; have h2 := hc' μ
      rw [abs_le] at h1 h2 ⊢; push_cast [Nat.cast_sub hL] at h1 h2; constructor <;> omega
  have hmem : ∀ y ∈ cellNbhd L a B ∪ Ys,
      (fun μ => (((((y μ).val / a : ℕ)) : ZMod K)).valMinAbs) ∈ XO := by
    rintro y (hy | hy)
    · exact hnb y hy
    · exact Or.inl (hYs y hy)
  refine ⟨fun x hx y hy μ => ?_, fun x hx μ => ?_⟩
  · exact cell_spread_le rfl hK hD XO hq hs (hnb x hx) (hmem y hy) μ
  · exact cell_box_le rfl hK XO hq (hmem x hx) μ

end Geom

section Cubes

open Balaban.Fluctuation

/-- A site of the cell of an aligned base `b` has the cell of `b`. -/
theorem cell_eq_of_mem_box_aligned {d n a K : ℕ} [NeZero n] [NeZero a] [NeZero K] (hn : n = a * K)
    {b : Balaban.Torus d n} (hb : Aligned a b) {x : Balaban.Torus d n} (hx : x ∈ box b a)
    (μ : Fin d) :
    ((((x μ).val / a : ℕ)) : ZMod K) = ((((b μ).val / a : ℕ)) : ZMod K) := by
  subst hn
  obtain ⟨j, hj, h⟩ := cell_of_mem_box (K := K) (L := 1) hb (by rwa [one_mul]) μ
  obtain rfl : j = 0 := by omega
  simpa using h

/-- **The cubes of the cells of a support.**  On a torus with `K` cells of side
`a = cellSide L m₀ m₁ j` per direction there is, for every set `X` of centred cell coordinates, a set
of `π_j`-cubes whose sites are the sites of the cells of `X`. -/
theorem exists_cubes_of_cells {d L N₁ m₁ Kc m₀ j K : ℕ} [NeZero N₁] [NeZero L] [NeZero K]
    (hn : (N₁ * L ^ m₁) * L ^ Kc = cellSide L m₀ m₁ j * K) :
    ∃ Ycub : Finset (Fin d → ℤ) →
        Finset (CubeB (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := Kc) m₀ j Set.univ),
      ∀ X, sitesOf (Ycub X) = {x : CTorus d L N₁ m₁ Kc |
        (fun μ => (((((x μ).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs) ∈
          (↑X : Set (Fin d → ℤ))} := by
  have ha := cellSide_pos (L := L) m₀ m₁ j
  have : NeZero (cellSide L m₀ m₁ j) := ⟨ha.ne'⟩
  refine ⟨fun X => Finset.univ.filter fun b =>
    (fun μ => (((((b.1 μ).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs) ∈ X, fun X => ?_⟩
  ext x
  rw [mem_sitesOf]
  constructor
  · rintro ⟨b, hb, hx⟩
    have hb' := (Finset.mem_filter.1 hb).2
    have hc : (fun μ => (((((x μ).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs) =
        (fun μ => (((((b.1 μ).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs) :=
      funext fun μ => by rw [cell_eq_of_mem_box_aligned hn b.2.1 hx μ]
    show _ ∈ (↑X : Set (Fin d → ℤ))
    rw [hc]
    exact hb'
  · intro hx
    refine ⟨⟨cbase (cellSide L m₀ m₁ j) x, aligned_cbase x, Set.subset_univ _⟩, ?_,
      mem_box_cbase ha x⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    have hc : (fun μ => (((((cbase (cellSide L m₀ m₁ j) x μ).val / cellSide L m₀ m₁ j : ℕ)) :
        ZMod K)).valMinAbs) =
        (fun μ => (((((x μ).val / cellSide L m₀ m₁ j : ℕ)) : ZMod K)).valMinAbs) :=
      funext fun μ => by
        have h := cbase_val_div (M := 1) ha x μ
        rw [mul_one] at h
        rw [h]
    rw [hc]
    exact hx

end Cubes

end Balaban.Polymer.TwoTorusStep
