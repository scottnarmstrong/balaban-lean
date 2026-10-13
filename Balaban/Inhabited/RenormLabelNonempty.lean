/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.StepTowerOfG
public import Balaban.Inhabited.RenormLocC1ZeroWitness
public import Balaban.Fluctuation.RenormDomainParams
import Mathlib.Tactic.Linarith

/-!
# Nonempty cut labels for the renormalization localization at the scale setting

On the torus of `lvTop N₁ m₁ k ϱ` (`d = L = 3`, `m₀ = 1`) the region `X₁` of a block root is the
box of `5` cells of side `c = 3^{k+2+m₁}` per direction around the cell of the root, and the torus
has `N₁ / 3` such cells per direction.  If `15 < N₁` (with `3 ∣ N₁`, so `N₁ ≥ 18`) there is room
beside `X₁`: the cube of the top layer, of side `s = c / 3`, based at the corner of the root cell
moved by `3 c` in every coordinate, has a cell disjoint from `X₁`.  Hence `RenLabel` is nonempty
for every root.  For `N₁ ≤ 15` (`N₁ = 9, 12, 15`) the region `X₁` is the whole torus and the label
type is empty (`nbhdF_ne_univ` is the converse direction).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Analysis Balaban.Inhabited.LevelStep LocalCover

theorem renFar_mod_cases {u n : ℕ} (hn : 0 < n) (h : u < 3 * n) :
    u % n = u ∨ u % n + n = u ∨ u % n + 2 * n = u := by
  have h1 := Nat.mod_add_div u n
  have h2 : u / n < 3 := (Nat.div_lt_iff_lt_mul hn).2 (by omega)
  generalize u / n = q at h1 h2
  interval_cases q <;> omega

/-- Arithmetic core: a residue in a cell of side `s` based at `b + o` cannot be reached from the
box of width `5 c` based at `b - 2 c`, when `c = 3 s`, `n ≥ 6 c` and `o ∈ [3 c, 4 c - s]`. -/
theorem renFar_val_div_ne {n c s b o w : ℕ} [NeZero n] (hs : 0 < s) (hcs : c = 3 * s)
    (hn : 6 * c ≤ n) (hsn : s ∣ n) (hb : b < n) (hbs : b % s = 0) (hos : o % s = 0)
    (ho1 : 3 * c ≤ o) (ho2 : o + s ≤ 4 * c) (hw : w < 5 * c) :
    ((((b + (n - 2 * c) + w : ℕ)) : ZMod n).val) / s ≠ (((b + o : ℕ) : ZMod n).val) / s := by
  rw [ZMod.val_natCast, ZMod.val_natCast]
  intro h
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hv : (b + o) % n % s = 0 := by
    rw [Nat.mod_mod_of_dvd _ hsn, Nat.add_mod, hbs, hos]; simp
  have h1 := Nat.div_add_mod ((b + (n - 2 * c) + w) % n) s
  have h2 := Nat.div_add_mod ((b + o) % n) s
  have h3 := Nat.mod_lt ((b + (n - 2 * c) + w) % n) hs
  rw [h] at h1
  have hu := renFar_mod_cases hn0 (u := b + (n - 2 * c) + w) (by omega)
  have hv' := renFar_mod_cases hn0 (u := b + o) (by omega)
  generalize (b + (n - 2 * c) + w) % n = a at *
  generalize (b + o) % n = e at *
  generalize e / s = r at *
  omega

/-- The coordinate statement in `ZMod n`. -/
theorem renFar_coord {n c s o w : ℕ} [NeZero n] (hs : 0 < s) (hcs : c = 3 * s)
    (hn : 6 * c ≤ n) (hsn : s ∣ n) {B x y : ZMod n} (hBs : B.val % s = 0) (hos : o % s = 0)
    (ho1 : 3 * c ≤ o) (ho2 : o + s ≤ 4 * c) (hw : w < 5 * c)
    (hx : x = B - ((2 * c : ℕ) : ZMod n) + (w : ZMod n)) (hy : y = B + (o : ZMod n)) :
    x.val / s ≠ y.val / s := by
  have hB : B.val < n := ZMod.val_lt B
  have hx' : x = ((B.val + (n - 2 * c) + w : ℕ) : ZMod n) := by
    rw [hx, Nat.cast_add, Nat.cast_add, Nat.cast_sub (by omega), ZMod.natCast_zmod_val,
      ZMod.natCast_self]
    ring
  have hy' : y = ((B.val + o : ℕ) : ZMod n) := by
    rw [hy, Nat.cast_add, ZMod.natCast_zmod_val]
  rw [hx', hy']
  exact renFar_val_div_ne hs hcs hn hsn hB hBs hos ho1 ho2 hw

/-- **The far cube.**  The cube of the top layer based at the corner of the root cell moved by the
vector `o`. -/
def renFarCube {N₁ m₁ k : ℕ} [NeZero N₁] (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1))))
    (o : Fin 3 → ℕ) : ℕ × CTorus 3 3 N₁ m₁ (k + 1) :=
  (k + 1, corner 1 (blockSite k z) + natT o)

theorem renFarCube_mem {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (o : Fin 3 → ℕ)
    (ho : ∀ μ, o μ % 3 ^ (k + 1 + m₁) = 0) :
    renFarCube z o ∈ cubeIdx (lvTop N₁ m₁ k ϱ) := by
  rw [mem_cubeIdx]
  refine ⟨⟨by simp [renFarCube], by simp [renFarCube]⟩, ?_, ?_⟩
  · exact isLevel_lvTop.mem_layer _
  · have hd : 3 ^ (k + 1 + m₁) ∣ (N₁ * 3 ^ m₁) * 3 ^ (k + 1) :=
      ⟨N₁, by rw [pow_add 3 (k + 1) m₁]; ring⟩
    exact aligned_add_natT hd (aligned_corner_of_le 1 (Nat.le_succ k) _) ho

/-- **The far cube misses `X₁`.**  If `15 < N₁`, `3 ∣ N₁`, and the vector `o` is a multiple of the
cube side `s = 3^{k+1+m₁}` in every coordinate, with one coordinate `μ₀` in `[9 s, 11 s]`, then the
cube `renFarCube z o` of the top layer has its cell disjoint from `X₁` of the root `z`. -/
theorem renFarCube_disjoint {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁) (h15 : 15 < N₁)
    (o : Fin 3 → ℕ) (ho : ∀ μ, o μ % 3 ^ (k + 1 + m₁) = 0) (μ₀ : Fin 3)
    (ho1 : 9 * 3 ^ (k + 1 + m₁) ≤ o μ₀) (ho2 : o μ₀ + 3 ^ (k + 1 + m₁) ≤ 12 * 3 ^ (k + 1 + m₁)) :
    Disjoint (Pset m₁ (renFarCube z o))
      (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) := by
  rw [X1_eq isLevel_lvTop (by simpa using h3) (le_refl (k + 1))]
  rw [Set.disjoint_left]
  intro x hxP hxN
  obtain ⟨w, hw, hx⟩ := hxN
  have hs : 0 < 3 ^ (k + 1 + m₁) := by positivity
  have hcs : cellSide 3 1 m₁ (k + 1) = 3 * 3 ^ (k + 1 + m₁) := by
    unfold cellSide; rw [show k + 1 + 1 + m₁ = (k + 1 + m₁) + 1 by ring, pow_succ]; ring
  have hN18 : 18 ≤ N₁ := by obtain ⟨M, hM⟩ := h3; omega
  have hnN : (N₁ * 3 ^ m₁) * 3 ^ (k + 1) = N₁ * 3 ^ (k + 1 + m₁) := by
    rw [pow_add 3 (k + 1) m₁]; ring
  have hn : 6 * cellSide 3 1 m₁ (k + 1) ≤ (N₁ * 3 ^ m₁) * 3 ^ (k + 1) := by
    rw [hcs, hnN]
    have := Nat.mul_le_mul_right (3 ^ (k + 1 + m₁)) hN18
    omega
  have hsn : 3 ^ (k + 1 + m₁) ∣ (N₁ * 3 ^ m₁) * 3 ^ (k + 1) := ⟨N₁, by rw [hnN]; ring⟩
  have hB : (corner 1 (blockSite k z) μ₀).val % 3 ^ (k + 1 + m₁) = 0 :=
    aligned_corner_of_le 1 (Nat.le_succ k) _ μ₀
  have hw' := hw μ₀
  have hc := hxP μ₀
  refine renFar_coord (n := (N₁ * 3 ^ m₁) * 3 ^ (k + 1)) (c := cellSide 3 1 m₁ (k + 1))
    (s := 3 ^ (k + 1 + m₁)) (o := o μ₀) (w := w μ₀) hs hcs hn hsn hB (ho μ₀) ?_ ?_ ?_ ?_ ?_ hc
  · omega
  · omega
  · omega
  · have := congrFun hx μ₀
    rw [this]
    simp [natT, Nat.cast_mul]
  · simp [renFarCube, natT]

/-- The label of the far cube with offset `(9 + t μ) s` in the coordinate `μ`, `t μ ∈ {0, 1, 2}`. -/
theorem renFarCube_label {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁) (h15 : 15 < N₁)
    (t : Fin 3 → Fin 3) :
    renFarCube z (fun μ => (9 + (t μ : ℕ)) * 3 ^ (k + 1 + m₁)) ∈ cubeIdx (lvTop N₁ m₁ k ϱ) ∧
      Disjoint (Pset m₁ (renFarCube z (fun μ => (9 + (t μ : ℕ)) * 3 ^ (k + 1 + m₁))))
        (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) := by
  have ho : ∀ μ, (9 + (t μ : ℕ)) * 3 ^ (k + 1 + m₁) % 3 ^ (k + 1 + m₁) = 0 :=
    fun μ => Nat.mul_mod_left _ _
  refine ⟨renFarCube_mem z _ ho, renFarCube_disjoint z h3 h15 _ ho 0 ?_ ?_⟩
  · exact Nat.mul_le_mul_right _ (by omega)
  · have := (t 0).isLt
    have e : (9 + (t 0 : ℕ)) * 3 ^ (k + 1 + m₁) + 3 ^ (k + 1 + m₁) =
        (10 + (t 0 : ℕ)) * 3 ^ (k + 1 + m₁) := by ring
    rw [e]
    exact Nat.mul_le_mul_right _ (by omega)

/-- **T1.  The cut labels exist at the scale setting.**  For `3 ∣ N₁` and `15 < N₁` (that is
`N₁ ≥ 18`), and every root `z`, the label type of the region `X₁` of `z` on the torus of
`lvTop N₁ m₁ k ϱ` is nonempty; an explicit label is the cube `(k + 1, corner + 9 s)`, `s = 3^{k+1+m₁}`
(`renFarCube`). -/
theorem renLabel_nonempty {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁) (h15 : 15 < N₁) :
    Nonempty (RenLabel (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z)))) :=
  ⟨⟨_, renFarCube_label z h3 h15 (fun _ => 0)⟩⟩

/-- **T2.  At least `27` labels.**  The cubes with offsets `(9 + t μ) s`, `t : Fin 3 → Fin 3`,
are distinct labels. -/
theorem renLabel_card_ge {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁) (h15 : 15 < N₁) :
    27 ≤ Fintype.card
      (RenLabel (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z)))) := by
  have hN18 : 18 ≤ N₁ := by obtain ⟨M, hM⟩ := h3; omega
  have hs : 0 < 3 ^ (k + 1 + m₁) := by positivity
  have hnN : (N₁ * 3 ^ m₁) * 3 ^ (k + 1) = N₁ * 3 ^ (k + 1 + m₁) := by
    rw [pow_add 3 (k + 1) m₁]; ring
  let f : (Fin 3 → Fin 3) →
      RenLabel (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) :=
    fun t => ⟨_, renFarCube_label (ϱ := ϱ) z h3 h15 t⟩
  have hinj : Function.Injective f := by
    intro t t' h
    funext μ
    have h1 : renFarCube z (fun μ => (9 + (t μ : ℕ)) * 3 ^ (k + 1 + m₁)) =
        renFarCube z (fun μ => (9 + (t' μ : ℕ)) * 3 ^ (k + 1 + m₁)) := congrArg Subtype.val h
    have h2 := congrFun (congrArg Prod.snd h1) μ
    simp only [renFarCube, Pi.add_apply, natT_apply, add_right_inj] at h2
    have hlt : ∀ u : Fin 3 → Fin 3, (9 + (u μ : ℕ)) * 3 ^ (k + 1 + m₁) <
        (N₁ * 3 ^ m₁) * 3 ^ (k + 1) := by
      intro u
      rw [hnN]
      have := (u μ).isLt
      have h12 : 9 + (u μ : ℕ) < N₁ := by omega
      exact Nat.mul_lt_mul_of_pos_right h12 hs
    have h3' := congrArg ZMod.val h2
    rw [ZMod.val_natCast_of_lt (hlt t), ZMod.val_natCast_of_lt (hlt t')] at h3'
    have := Nat.eq_of_mul_eq_mul_right hs h3'
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective f hinj
  simpa using this

/-- Adding a residue below the cell side `s` to an aligned point stays in its cell. -/
theorem renFar_add_div {n s : ℕ} [NeZero n] (hs : 0 < s) (hsn : s ∣ n) {y : ZMod n}
    (hy : y.val % s = 0) {v : ℕ} (hv : v < s) : (y + (v : ZMod n)).val / s = y.val / s := by
  obtain ⟨r, hr⟩ := hsn
  obtain ⟨q, hq⟩ := Nat.dvd_of_mod_eq_zero hy
  have hlt := ZMod.val_lt y
  have hqr : q < r := by
    apply Nat.lt_of_mul_lt_mul_left (a := s)
    rw [← hq, ← hr]; exact hlt
  have h1 : s * (q + 1) ≤ s * r := Nat.mul_le_mul_left s hqr
  have h2 : y.val + v < n := by rw [Nat.mul_add] at h1; omega
  have e : y + (v : ZMod n) = ((y.val + v : ℕ) : ZMod n) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val]
  rw [e, ZMod.val_natCast_of_lt h2, hq, Nat.mul_add_div hs, Nat.div_eq_of_lt hv,
    Nat.mul_div_cancel_left _ hs]
  rfl

/-- A point in the cell of an aligned point is that point plus a residue below the cell side. -/
theorem renFar_exists_add {n s : ℕ} [NeZero n] (hs : 0 < s) {x y : ZMod n}
    (hy : y.val % s = 0) (h : x.val / s = y.val / s) : ∃ v : ℕ, v < s ∧ x = y + (v : ZMod n) := by
  refine ⟨x.val % s, Nat.mod_lt _ hs, ?_⟩
  have h1 := Nat.div_add_mod x.val s
  have h2 := Nat.div_add_mod y.val s
  rw [h] at h1
  have h3 : x.val = y.val + x.val % s := by omega
  conv_lhs => rw [← ZMod.natCast_zmod_val x, h3]
  rw [Nat.cast_add, ZMod.natCast_zmod_val]

/-- The cell of the far cube with offset `(9 s, 0, 0)` is the box `y0 + [0, s)^3`. -/
theorem renFar_pset_eq_box {N₁ m₁ k : ℕ} [NeZero N₁]
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (o : Fin 3 → ℕ)
    (ho : ∀ μ, o μ % 3 ^ (k + 1 + m₁) = 0) :
    Pset m₁ (renFarCube z o) = box (renFarCube z o).2 (3 ^ (k + 1 + m₁)) := by
  have hs : 0 < 3 ^ (k + 1 + m₁) := by positivity
  have hsn : 3 ^ (k + 1 + m₁) ∣ (N₁ * 3 ^ m₁) * 3 ^ (k + 1) := ⟨N₁, by rw [pow_add 3 (k + 1) m₁]; ring⟩
  have hd : 3 ^ (k + 1 + m₁) ∣ (N₁ * 3 ^ m₁) * 3 ^ (k + 1) := hsn
  have hal : ∀ μ, ((renFarCube z o).2 μ).val % 3 ^ (k + 1 + m₁) = 0 := fun μ =>
    aligned_add_natT hd (aligned_corner_of_le 1 (Nat.le_succ k) _) ho μ
  ext x
  constructor
  · intro hx
    have h : ∀ μ, ∃ v : ℕ, v < 3 ^ (k + 1 + m₁) ∧ x μ = (renFarCube z o).2 μ + (v : ZMod _) :=
      fun μ => renFar_exists_add hs (hal μ) (hx μ)
    choose v hv hxv using h
    exact ⟨v, hv, by funext μ; simp [natT, hxv μ]⟩
  · rintro ⟨w, hw, rfl⟩ μ
    simp only [natT_apply, Pi.add_apply]
    exact renFar_add_div hs hsn (hal μ) (hw μ)

/-- The site just before the far cube in the first coordinate lies in `X₁`. -/
theorem renFar_pred_mem {N₁ m₁ k : ℕ} [NeZero N₁]
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) {ϱ : ℝ} (h3 : 3 ∣ N₁) :
    (renFarCube z (Pi.single 0 (9 * 3 ^ (k + 1 + m₁)))).2 - Pi.single 0 1 ∈
      X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z)) := by
  rw [X1_eq isLevel_lvTop (by simpa using h3) (le_refl (k + 1))]
  have hs : 0 < 3 ^ (k + 1 + m₁) := by positivity
  have hcs : cellSide 3 1 m₁ (k + 1) = 3 * 3 ^ (k + 1 + m₁) := by
    unfold cellSide; rw [show k + 1 + 1 + m₁ = (k + 1 + m₁) + 1 by ring, pow_succ]; ring
  refine ⟨fun μ => if μ = 0 then 15 * 3 ^ (k + 1 + m₁) - 1 else 6 * 3 ^ (k + 1 + m₁), ?_, ?_⟩
  · intro μ
    by_cases h : μ = 0
    · simp only [h, ite_true]; omega
    · simp only [h, ite_false]; omega
  · funext μ
    fin_cases μ
    · simp [renFarCube, natT, hcs, Nat.cast_sub (show 1 ≤ 15 * 3 ^ (k + 1 + m₁) by omega)]
      ring
    · simp [renFarCube, natT, hcs]
      ring
    · simp [renFarCube, natT, hcs]
      ring

/-- **T2.  A second element of the Y-family.**  At the scale setting (`15 < N₁`, `3 ∣ N₁`) the
family `renYs` of the cover contains `X₁` itself (the empty connected family) and a strictly larger
set `Y ⊋ X₁`: the domain `Y[{i₀}]` of the connected family consisting of the label `i₀` of the
cube based at the corner of the root cell moved by `(9 s, 0, 0)`, whose cell is adjacent to `X₁`.
(`X₁ = ↑(nbhdF 1 (blockSite k z))` by `LocalCover.coe_nbhdF_eq_X1`.) -/
theorem renYs_second_element {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ : ℝ}
    (z : Torus 3 (N₁ * 3 ^ m₁ * 3 ^ (k + 1 - (k + 1)))) (h3 : 3 ∣ N₁) (h15 : 15 < N₁) :
    finOf (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) ∈
        renYs (renCube (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ m₁ k ϱ) 1 (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) ∧
      ∃ Y ∈ renYs (renCube (lvTop N₁ m₁ k ϱ) (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))))
          (lvTop N₁ m₁ k ϱ) 1 (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))),
        finOf (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) ⊆ Y ∧
          Y ≠ finOf (X1 (lvTop N₁ m₁ k ϱ) 1 k (fam 1 (blockSite k z))) := by
  classical
  set G := lvTop N₁ m₁ k ϱ with hG
  set X := X1 G 1 k (fam 1 (blockSite k z)) with hX
  have hs : 0 < 3 ^ (k + 1 + m₁) := by positivity
  have ho : ∀ μ, (Pi.single 0 (9 * 3 ^ (k + 1 + m₁)) : Fin 3 → ℕ) μ % 3 ^ (k + 1 + m₁) = 0 := by
    intro μ
    by_cases h : μ = 0
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]
  have hmem := renFarCube_mem (ϱ := ϱ) z _ ho
  have hdis : Disjoint (Pset m₁ (renFarCube z (Pi.single 0 (9 * 3 ^ (k + 1 + m₁)))))
      X :=
    renFarCube_disjoint z h3 h15 _ ho 0 (by simp) (by simp; omega)
  let i₀ : RenLabel G X := ⟨_, hmem, hdis⟩
  have hbox := renFar_pset_eq_box (N₁ := N₁) (m₁ := m₁) (k := k) z _ ho
  set y0 := (renFarCube z (Pi.single 0 (9 * 3 ^ (k + 1 + m₁)))).2 with hy0
  have hP : Pset m₁ (renCube G X i₀) = box y0 (3 ^ (k + 1 + m₁)) := hbox
  refine ⟨?_, finOf (Ysites G 1 (renCube G X) X {i₀}), ?_, ?_, ?_⟩
  · rw [mem_renYs, coe_finOf]
    unfold polymerDomains
    rw [Finset.mem_image]
    refine ⟨∅, ?_, by simp [Ysites]⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, fun i hi => absurd hi (Finset.notMem_empty i)⟩
  · apply finOf_mem_renYs
    unfold polymerDomains
    rw [Finset.mem_image]
    refine ⟨{i₀}, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    intro i hi x hx
    rw [Finset.mem_singleton] at hi
    subst hi
    have hx' : x ∈ box y0 (3 ^ (k + 1 + m₁)) := by rw [← hP]; exact hx
    have hbV : y0 - Pi.single 0 1 ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} :=
      Or.inl (renFar_pred_mem z h3)
    have hy0V : y0 ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} :=
      Or.inr (by simp only [Set.mem_iUnion, Finset.mem_singleton]; exact ⟨i₀, rfl, self_mem_Pset _⟩)
    have hboxV : box y0 (3 ^ (k + 1 + m₁)) ⊆
        patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} := by
      intro y hy
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_singleton]
      exact ⟨i₀, rfl, by rw [hP]; exact hy⟩
    refine ⟨y0 - Pi.single 0 1, renFar_pred_mem z h3, ?_⟩
    have h1 : Relation.ReflTransGen (fun a b => (latGraph 3 ((N₁ * 3 ^ m₁) * 3 ^ (k + 1))).Adj a b ∧
        a ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀} ∧
        b ∈ patchUnion X (fun i => Pset m₁ (renCube G X i)) {i₀}) (y0 - Pi.single 0 1) y0 := by
      by_cases he : y0 - Pi.single 0 1 = y0
      · rw [he]
      · exact Relation.ReflTransGen.single ⟨⟨he, ⟨0, Or.inl (by simp)⟩⟩, hbV, hy0V⟩
    exact h1.trans (chain_in_box y0 _ _ hboxV (mem_box_self _ hs) hx')
  · exact Finset.coe_subset.1 (by
      rw [coe_finOf, coe_finOf]; exact subset_Ysites (G := G) (m₀ := 1) (c := renCube G X) X {i₀})
  · intro h
    have h1 : y0 ∈ Ysites G 1 (renCube G X) X {i₀} := by
      refine Or.inr ?_
      simp only [Set.mem_iUnion, Finset.mem_singleton]
      exact ⟨i₀, rfl, Pset_subset_Dsites (layerUnion_of_isLevel isLevel_lvTop 1)
        (by simpa using h3) hmem (self_mem_Pset _)⟩
    have h2 : y0 ∈ finOf (Ysites G 1 (renCube G X) X {i₀}) := by
      rw [← Finset.mem_coe, coe_finOf]; exact h1
    rw [h, ← Finset.mem_coe, coe_finOf] at h2
    exact Set.disjoint_left.1 hdis (self_mem_Pset _) h2

/-- **T3.  The non-degenerate instance of `locC1`.**  At the scale `k = 1` with `N₁ = 18` on the
torus of `lvTop`, for every block root `z`: the localization principle of the renormalization
expansion (zero class, `ν = 0`, `κa = 0`, `r₀ = 1/16`) holds, and the label type of the cover
`renYs` of the same root is nonempty (at least `27` labels) and contains a set strictly larger
than `X₁`, so that the expansion is exercised
with cuts. -/
theorem renLocC1_nonempty_scale_one {κmin : ℝ} (T : StepTower κmin)
    (z : Torus 3 (18 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1)))) :
    HasLocPrinciple (N := 2) (lvTop 18 T.m₁ 1 (rhoSep T.m₁))
      (XiCOneReal (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) (compWeight 3 1) 0 T.t) (1 / 16)
      (renYs (renCube (lvTop 18 T.m₁ 1 (rhoSep T.m₁))
          (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z))))
        (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1
        (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z))))
      (renDY (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1) 0 1
      (fun D _ => bgClass (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 0
        ((2 + 2 * K4 3 3 2 T.BG T.κ * xiC1 3) * T.t) D)
      (fun D φ ξ => renC1On (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) (compWeight 3 1) 0 T.t
        (blockSites 3 3 18 T.m₁ (1 + 1) 1 z) D.Ψ D.h φ ξ)
      (fun D _ => bgFieldC (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) (compWeight 3 1) 0 (bgC0 3 3 2) D) ∧
    27 ≤ Fintype.card
      (RenLabel (lvTop 18 T.m₁ 1 (rhoSep T.m₁))
        (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z)))) ∧
    ∃ Y ∈ renYs (renCube (lvTop 18 T.m₁ 1 (rhoSep T.m₁))
          (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z))))
        (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1
        (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z))),
      finOf (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z))) ⊆ Y ∧
        Y ≠ finOf (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z))) := by
  refine ⟨?_, renLabel_card_ge z (by norm_num) (by norm_num),
    (renYs_second_element z (by norm_num) (by norm_num)).2⟩
  have h := renLocC1_scale_of_tower T 1 le_rfl 18 (by norm_num) (by norm_num) (ν := 0)
    le_rfl (by simp) (κa := 0) (r₀ := 1 / 16)
    (by have := T.κdec_lower; have := T.κ0_nonneg; linarith) (by norm_num) le_rfl z
  exact h

/-- The same, with the tower supplied by `exists_stepTower`. -/
theorem exists_renLocC1_nonempty_scale_one (κmin : ℝ) :
    ∃ T : StepTower κmin, ∀ z : Torus 3 (18 * 3 ^ T.m₁ * 3 ^ (1 + 1 - (1 + 1))),
      Nonempty (RenLabel (lvTop 18 T.m₁ 1 (rhoSep T.m₁))
        (X1 (lvTop 18 T.m₁ 1 (rhoSep T.m₁)) 1 1 (fam 1 (blockSite 1 z)))) := by
  obtain ⟨T⟩ := exists_stepTower κmin
  exact ⟨T, fun z => renLabel_nonempty z (by norm_num) (by norm_num)⟩

end Balaban.Inhabited
