/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6BridgeLift
public import Balaban.Fluctuation.SizeMod
public import Balaban.LargeField.Geometry.Small
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The bridge Def-6 to I-6: the geometric premises and the termwise premises of the class

The geometric fields of `PremisesTerm` for the lifted family `liftTF`, from the landed geometry
of the covering size (FLUCTUATION Lemma 1.2, `Balaban/Fluctuation/SizeMod*.lean`):

* `liftPolys_diam` (path bound, from (G5)): `|x|₁ ≤ A (1 + d_j(X))`, `A = diamA = √d M (1 + 2√d L)`;
* `liftPolys_card_le` (block count, from (G1)): `|X'| ≤ c₁ M^d (1 + d_j)`, the shape of a torus
  polymer counted in blocks (`card_Ypoly`: `|Ypoly X'| = |X'| L^{jd}` for non-winding `X'`);
* `liftPolys_count_le`, `liftPolys_summable` (counting, from (G2) with `κ₀ = κ - 2 ≥ a_ent + 1`):
  `∑ |X'|² (1 + d_j)⁶ e^{-(κ-1) d_j} ≤ K₀` with `K₀` independent of `j` and of the torus;
* `IsSFFamily.premisesTerm`: `PremisesTerm` for the lifted family, every field except the point
  group invariance `sym_mem`, `sym_inv`.

Typing data: `L^{m₀} ∣ N₁` (the cells tile the torus), `1 ≤ j ≤ k`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Balaban.SmallField Metric Set

section Blocks

/-- The block coordinate of `N * w` is `w`. -/
theorem blockCoord_intCast_mul {ℓ N m : ℕ} [NeZero m] [NeZero ℓ] (hℓ : ℓ = N * m) (w : ℤ) :
    blockCoord N m ((((N : ℤ) * w : ℤ)) : ZMod ℓ) = (w : ZMod m) := by
  have hm : (0 : ℤ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · exact absurd (by simpa [h] using hℓ) (NeZero.ne ℓ)
    · exact h
  set w' := w % (m : ℤ) with hw'
  have h0 : 0 ≤ w' := Int.emod_nonneg _ hm.ne'
  have h1 : w' < m := Int.emod_lt_of_pos _ hm
  obtain ⟨r, hr⟩ : ∃ r : ℕ, w' = r := ⟨w'.toNat, (Int.toNat_of_nonneg h0).symm⟩
  have hrm : r < m := by rw [hr] at h1; exact_mod_cast h1
  have e1 : (((N : ℤ) * w : ℤ) : ZMod ℓ) = (((N : ℤ) * (r : ℤ) : ℤ) : ZMod ℓ) := by
    refine (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).2 ?_
    have hdiv := Int.emod_add_mul_ediv w (m : ℤ)
    refine ⟨-(w / (m : ℤ)), ?_⟩
    rw [← hr]
    push_cast [hℓ]
    rw [← hw'] at hdiv
    have : (N : ℤ) * w' - N * w = -(N * (m * (w / m))) := by
      have : w = w' + m * (w / m) := by linarith
      nlinarith [this]
    rw [this]; ring
  have e2 : (((N : ℤ) * (r : ℤ) : ℤ) : ZMod ℓ) = ((N * r : ℕ) : ZMod ℓ) := by push_cast; rfl
  have e3 : (w : ZMod m) = ((r : ℕ) : ZMod m) := by
    have : (w : ZMod m) = ((w % (m : ℤ) : ℤ) : ZMod m) := (ZMod.intCast_mod w m).symm
    rw [this, ← hw', hr]; simp
  rw [e1, e2, e3]
  have hlt : N * r < ℓ := by rw [hℓ]; exact Nat.mul_lt_mul_of_pos_left hrm hN
  unfold blockCoord
  rw [ZMod.val_natCast_of_lt hlt, Nat.mul_div_cancel_left _ hN]


end Blocks

section Geom

variable {d L N₁ m₁ k : ℕ} [hL : NeZero L] [hN₁ : NeZero N₁]
include hL hN₁

/-- The fine site at the corner of the `j`-block with centred position `z`. -/
def ibase (j : ℕ) (z : Site d) : CTorus d L N₁ m₁ k :=
  fun μ => ((((L ^ j : ℕ) : ℤ) * z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k))

theorem unlift_ibase {j : ℕ} (hjk : j ≤ k) {z : Site d}
    (hz : ∀ μ, ZMod.valMinAbs (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) = z μ) :
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j z) = z := by
  funext μ
  unfold unlift
  have h : jBlock d L (N₁ * L ^ m₁) k j (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z) μ =
      ((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j))) := by
    unfold jBlock
    rw [blockMap_apply]
    exact blockCoord_intCast_mul (side_eq hjk) (z μ)
  rw [h]
  exact hz μ



theorem cycNorm_ibase {j : ℕ} (hjk : j ≤ k) {z : Site d}
    (hz : ∀ μ, ZMod.valMinAbs (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) = z μ) (μ : Fin d) :
    LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
      ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z - 0 : CTorus d L N₁ m₁ k) μ) =
      L ^ j * (z μ).natAbs := by
  have hℓ : N₁ * L ^ m₁ * L ^ k = L ^ j * (N₁ * L ^ m₁ * L ^ (k - j)) := side_eq hjk
  have h1 := ZMod.natAbs_valMinAbs_le (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j))))
  rw [hz μ] at h1
  have h2 : 2 * |((L ^ j : ℕ) : ℤ) * z μ| ≤ ((N₁ * L ^ m₁ * L ^ k : ℕ) : ℤ) := by
    rw [abs_mul, Nat.abs_cast, Int.abs_eq_natAbs (z μ), hℓ]
    push_cast
    have : 2 * (z μ).natAbs ≤ N₁ * L ^ m₁ * L ^ (k - j) := by omega
    have h3 : ((2 * (z μ).natAbs : ℕ) : ℤ) ≤ ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
      exact_mod_cast this
    push_cast at h3
    nlinarith [(by positivity : (0 : ℤ) ≤ (L : ℤ) ^ j)]
  have := LargeField.cycNorm_intCast_of_le h2
  simp only [Pi.sub_apply, Pi.zero_apply, sub_zero, ibase]
  rw [this, Int.natAbs_mul]
  simp


omit hL hN₁ in
theorem isDj_of_isPolyDom {m₀ j : ℕ} {Z : Set (CTorus d L N₁ m₁ k)} (hZ : IsPolyDom m₀ j Z) :
    IsDj m₀ j Z := by
  obtain ⟨hne, ⟨𝒦, hch⟩, hcon⟩ := hZ
  exact ⟨hne, fun z hz => by
    obtain ⟨b, hb, hzb⟩ := hch.2 z hz
    exact ⟨b, (hch.1 b hb).1, hzb, (hch.1 b hb).2⟩, hcon⟩

/-- The constant of the path bound: `√d M (1 + 2 √d L)`, `M = L^{m₀+m₁}`. -/
noncomputable def diamA (d L m₀ m₁ : ℕ) : ℝ :=
  Real.sqrt d * (L : ℝ) ^ (m₀ + m₁) * (1 + 2 * Real.sqrt d * L)

omit hL hN₁ in
theorem diamA_nonneg (d L m₀ m₁ : ℕ) : 0 ≤ diamA d L m₀ m₁ := by unfold diamA; positivity

/-- **Premise `diam` (from (G5))**: for a shape of the lifted family, `|x|₁ ≤ A (1 + d_j(X))`. -/
theorem liftPolys_diam {P : Consts} {j : ℕ} (hjk : j ≤ k)
    {X' : Finset (Site d)}
    (hX' : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) {x : Site d}
    (hx : x ∈ X') :
    ((∑ μ, |x μ| : ℤ) : ℝ) ≤ diamA d L P.m₀ m₁ * (1 + sizeJ (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  obtain ⟨h0, hnw, hX⟩ := hX'
  have hDj := isDj_of_isPolyDom hX
  have hxmem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ Ypoly j X' := by
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j x) ∈ X'
    rw [unlift_ibase hjk (hnw x hx)]; exact hx
  have hG := G5 hDj hxmem (zero_mem_Ypoly h0)
  set S : ℝ := ∑ μ, (((x μ).natAbs : ℕ) : ℝ) ^ 2 with hS
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have he : euclDist (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
      (0 : CTorus d L N₁ m₁ k) = (L : ℝ) ^ j * Real.sqrt S := by
    unfold euclDist
    have h1 : ∀ μ, ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
        ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) μ - (0 : CTorus d L N₁ m₁ k) μ) : ℕ) : ℝ)
        = (L : ℝ) ^ j * ((x μ).natAbs : ℝ) := by
      intro μ
      have := cycNorm_ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk (hnw x hx) μ
      simp only [Pi.sub_apply] at this
      rw [this]; push_cast; ring
    have h2 : ∑ μ, ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
        ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) μ - (0 : CTorus d L N₁ m₁ k) μ) : ℕ) : ℝ) ^ 2
        = ((L : ℝ) ^ j) ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by rw [h1 μ]; ring
    rw [h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hLj.le]
  have hT : ((∑ μ, |x μ| : ℤ) : ℝ) = ∑ μ, (((x μ).natAbs : ℕ) : ℝ) := by
    push_cast
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hT2 : (∑ μ, (((x μ).natAbs : ℕ) : ℝ)) ^ 2 ≤ d * S := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun μ => (((x μ).natAbs : ℕ) : ℝ))
    simpa [hS] using this
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT3 : (∑ μ, (((x μ).natAbs : ℕ) : ℝ)) ≤ Real.sqrt d * Real.sqrt S := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
    exact Real.le_sqrt_of_sq_le hT2
  have hcell : (cellSide L P.m₀ m₁ j : ℝ) = (L : ℝ) ^ j * (L : ℝ) ^ (P.m₀ + m₁) := by
    unfold cellSide; push_cast; rw [← pow_add]; congr 1; ring
  rw [he, hcell] at hG
  have hS1 : Real.sqrt S ≤ (L : ℝ) ^ (P.m₀ + m₁) *
      (sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X') + 2 * Real.sqrt d * L) := by
    have : (L : ℝ) ^ j * Real.sqrt S ≤ (L : ℝ) ^ j * ((L : ℝ) ^ (P.m₀ + m₁) *
        (sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X') + 2 * Real.sqrt d * L)) := by
      calc _ ≤ _ := hG
        _ = _ := by unfold sizeJ; ring
    exact le_of_mul_le_mul_left this hLj
  have hsz : 0 ≤ sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X') :=
    treeLenCovOne_nonneg _ _ _
  rw [hT]
  calc _ ≤ Real.sqrt d * Real.sqrt S := hT3
    _ ≤ Real.sqrt d * ((L : ℝ) ^ (P.m₀ + m₁) * (sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k) P.m₀ j (Ypoly j X') + 2 * Real.sqrt d * L)) :=
        mul_le_mul_of_nonneg_left hS1 (Real.sqrt_nonneg _)
    _ ≤ diamA d L P.m₀ m₁ * (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
        (Ypoly j X')) := by
        unfold diamA
        have hc : 0 ≤ 2 * Real.sqrt d * L := by positivity
        have hM : 0 ≤ Real.sqrt d * (L : ℝ) ^ (P.m₀ + m₁) := by positivity
        nlinarith [mul_nonneg hM hsz, mul_nonneg hM hc, mul_nonneg (mul_nonneg hM hc) hsz]


open Classical in
theorem card_unlift_fiber {j : ℕ} (hjk : j ≤ k) {z : Site d}
    (hz : ∀ μ, ZMod.valMinAbs (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) = z μ) :
    (Finset.univ.filter (fun x : CTorus d L N₁ m₁ k =>
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x = z)).card = (L ^ j) ^ d := by
  have hℓ : N₁ * L ^ m₁ * L ^ k = L ^ j * (N₁ * L ^ m₁ * L ^ (k - j)) := side_eq hjk
  set F : Fin d → Finset (ZMod (N₁ * L ^ m₁ * L ^ k)) := fun μ =>
    Finset.univ.filter (fun a => blockCoord (L ^ j) (N₁ * L ^ m₁ * L ^ (k - j)) a =
      ((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) with hF
  have hfil : Finset.univ.filter (fun x : CTorus d L N₁ m₁ k =>
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x = z) = Fintype.piFinset F := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hF]
    constructor
    · intro h μ
      have h1 := congrFun h μ
      simp only [unlift, jBlock, blockMap_apply] at h1
      rw [← hz μ] at h1
      exact ZMod.valMinAbs_inj.1 (by rw [hz μ] at h1 ⊢; exact h1)
    · intro h
      funext μ
      simp only [unlift, jBlock, blockMap_apply]
      rw [h μ]
      exact hz μ
  rw [hfil, Fintype.card_piFinset]
  have : ∀ μ, (F μ).card = L ^ j := fun μ => card_blockCoord_fibre hℓ _
  simp [this]

open Classical in
theorem card_Ypoly {j : ℕ} (hjk : j ≤ k) {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X') :
    (Finset.univ.filter (fun x : CTorus d L N₁ m₁ k =>
      unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X')).card = X'.card * (L ^ j) ^ d := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x : CTorus d L N₁ m₁ k =>
    unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) (t := X') (fun x hx => by
      simpa using hx)]
  rw [Finset.sum_congr rfl (g := fun _ => (L ^ j) ^ d)]
  · simp
  · intro z hz
    rw [← card_unlift_fiber hjk (hnw z hz)]
    congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨by rw [h]; exact hz, h⟩


open Classical in
theorem ncard_Ypoly {j : ℕ} (hjk : j ≤ k) {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X') :
    ((Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X').ncard) = X'.card * (L ^ j) ^ d := by
  have : Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X' = ↑(Finset.univ.filter
      (fun x : CTorus d L N₁ m₁ k => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ X')) := by
    ext x; simp [Ypoly]
  rw [this, Set.ncard_coe_finset]
  exact card_Ypoly hjk hnw

/-- **Block count (from (G1))**: `|X'| ≤ c₁ M^d (1 + d_j)` for a shape of the lifted family. -/
theorem liftPolys_card_le {P : Consts} {j : ℕ} (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X' : Finset (Site d)}
    (hX' : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) :
    (X'.card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d *
      (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  obtain ⟨h0, hnw, hX⟩ := hX'
  have hG := G1_card hN hjk (isDj_of_isPolyDom hX)
  rw [ncard_Ypoly hjk hnw] at hG
  have hcell : (cellSide L P.m₀ m₁ j : ℝ) = (L : ℝ) ^ j * (L : ℝ) ^ (P.m₀ + m₁) := by
    unfold cellSide; push_cast; rw [← pow_add]; congr 1; ring
  rw [hcell, mul_pow] at hG
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < ((L : ℝ) ^ j) ^ d := by positivity
  push_cast at hG
  unfold sizeJ
  refine le_of_mul_le_mul_right ?_ hLj
  calc (X'.card : ℝ) * ((L : ℝ) ^ j) ^ d ≤ _ := hG
    _ = _ := by ring

theorem zero_cell_subset {P : Consts} {j : ℕ} (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {Y : Set (CTorus d L N₁ m₁ k)} (hY : IsDj P.m₀ j Y) (h0 : (0 : CTorus d L N₁ m₁ k) ∈ Y) :
    box (0 : CTorus d L N₁ m₁ k) (cellSide L P.m₀ m₁ j) ⊆ Y := by
  obtain ⟨b, hb, hzb, hsub⟩ := hY.2.1 0 h0
  have ha0 := cellSide_pos (L := L) P.m₀ m₁ j
  have hdvd := cellSide_dvd (K := k) (m₁ := m₁) hN hjk
  have := cell_subset_cube hdvd ha0 hb hzb
  have hc : cbase (cellSide L P.m₀ m₁ j) (0 : CTorus d L N₁ m₁ k) = 0 := by
    funext μ; simp [cbase]
  rw [hc] at this
  exact this.trans hsub


theorem liftPolys_finite (P : Consts) (j : ℕ) :
    (liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j).Finite := by
  classical
  set r : ℕ := (N₁ * L ^ m₁ * L ^ (k - j)) / 2 with hr
  set B : Finset (Site d) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) r) with hB
  refine ((B.powerset : Set (Finset (Site d))).toFinite).subset ?_
  intro X' hX'
  obtain ⟨-, hnw, -⟩ := hX'
  show X' ∈ (B.powerset : Set (Finset (Site d)))
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  intro z hz
  simp only [hB, Fintype.mem_piFinset, Finset.mem_Icc]
  intro μ
  have h1 := ZMod.natAbs_valMinAbs_le (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j))))
  rw [hnw z hz μ] at h1
  have h2 : ((z μ).natAbs : ℤ) ≤ r := by exact_mod_cast h1
  constructor <;> omega

theorem liftPolys_injOn {P : Consts} {j : ℕ} (hjk : j ≤ k) :
    Set.InjOn (fun X' : Finset (Site d) => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')
      (liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) := by
  intro X₁ h₁ X₂ h₂ h
  have key : ∀ {A B : Finset (Site d)},
      A ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j →
      Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j A ⊆
        Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j B → A ⊆ B := by
    intro A B hA hAB z hz
    have hmem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ Ypoly j A := by
      show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j z) ∈ A
      rw [unlift_ibase hjk (hA.2.1 z hz)]; exact hz
    have := hAB hmem
    change unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j z) ∈ B at this
    rwa [unlift_ibase hjk (hA.2.1 z hz)] at this
  exact Finset.Subset.antisymm (key h₁ h.le) (key h₂ h.ge)

/-- The weight of a shape is controlled by `e^{-(κ-2) d_j}`. -/
theorem liftWt_le {P : Consts} {j : ℕ} (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    {X' : Finset (Site d)}
    (hX' : X' ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) :
    liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j ⟨X', hX'⟩ ≤
      (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        Real.exp (-(P.κ - 2) * sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly j X')) := by
  set t := sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X') with ht
  have ht0 : 0 ≤ t := treeLenCovOne_nonneg _ _ _
  have hc := liftPolys_card_le hjk hN hX'
  set C₁ := c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d with hC₁
  have hC₁0 : 0 ≤ C₁ := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  have hcard2 : (X'.card : ℝ) ^ 2 ≤ C₁ ^ 2 * (1 + t) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2
  have hpow : (1 + t) ^ 8 ≤ Nat.factorial 8 * Real.exp (1 + t) := by
    have := Real.pow_div_factorial_le_exp (1 + t) (by linarith) 8
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  unfold liftWt wt
  have e1 : Real.exp (1 + t) * Real.exp (-(P.κ - 1) * t) = Real.exp 1 * Real.exp (-(P.κ - 2) * t) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  calc (X'.card : ℝ) ^ 2 * (1 + t) ^ 6 * Real.exp (-(P.κ - 1) * t)
      ≤ C₁ ^ 2 * (1 + t) ^ 2 * (1 + t) ^ 6 * Real.exp (-(P.κ - 1) * t) := by
        gcongr
    _ = C₁ ^ 2 * (1 + t) ^ 8 * Real.exp (-(P.κ - 1) * t) := by ring
    _ ≤ C₁ ^ 2 * (Nat.factorial 8 * Real.exp (1 + t)) * Real.exp (-(P.κ - 1) * t) := by
        gcongr
    _ = C₁ ^ 2 * (Nat.factorial 8 * Real.exp 1) * Real.exp (-(P.κ - 2) * t) := by
        rw [mul_assoc, mul_assoc, e1]; ring


theorem liftPolys_summable (P : Consts) (j : ℕ) :
    Summable (liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) := by
  have : Finite ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) :=
    (liftPolys_finite P j).to_subtype
  exact Summable.of_finite

open Classical in
/-- **Premise `count_le` (from (G1), (G2))**: for `κ ≥ a_ent + 3`,
`∑_{X'} |X'|² (1 + d_j)⁶ e^{-(κ-1) d_j} ≤ K₀` with `K₀` independent of `j` and of the torus. -/
theorem liftPolys_count_le {P : Consts} {j : ℕ} (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁)
    (hκ : aEnt d L + 3 ≤ P.κ) :
    (∑' X, liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j X) ≤
      (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2) := by
  have : Finite ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j) :=
    (liftPolys_finite P j).to_subtype
  have := Fintype.ofFinite ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
  rw [tsum_fintype]
  set Cw := (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) with hCw
  have hCw0 : 0 ≤ Cw := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    rw [hCw]; positivity
  have ha0 := cellSide_pos (L := L) P.m₀ m₁ j
  have hΩ : IsPiUnion (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k) P.m₀ j Set.univ :=
    fun z _ => ⟨cbase (cellSide L P.m₀ m₁ j) z, aligned_cbase z, mem_box_cbase ha0 z,
      Set.subset_univ _⟩
  have ht0 : Aligned (cellSide L P.m₀ m₁ j) (0 : CTorus d L N₁ m₁ k) := by
    intro μ; simp
  have hG2 := G2_X (m₀ := P.m₀) (j := j) hN hjk hΩ ht0 (Set.subset_univ _) (κ₀ := P.κ - 2)
    (by linarith)
  calc ∑ X, liftWt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j X
      ≤ ∑ X : ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j),
        Cw * Real.exp (-(P.κ - 2) * sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly j X.1)) := Finset.sum_le_sum fun X _ => liftWt_le hjk hN X.2
    _ = Cw * ∑ X : ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j),
        Real.exp (-(P.κ - 2) * sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j
          (Ypoly j X.1)) := by rw [Finset.mul_sum]
    _ ≤ Cw * K0 d L (P.κ - 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hCw0
        have hinj : Function.Injective (fun X : ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k) P j) => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X.1) := fun X Y h =>
          Subtype.ext (liftPolys_injOn hjk X.2 Y.2 h)
        rw [← Finset.sum_image (f := fun Y : Set (CTorus d L N₁ m₁ k) =>
          Real.exp (-(P.κ - 2) * sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j Y))
          (s := Finset.univ) (g := fun X : ↥(liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
            (k := k) P j) => Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X.1)
          (fun X _ Y _ h => hinj h)]
        refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (t := Finset.univ.filter
          (fun X : Set (CTorus d L N₁ m₁ k) => DjMod P.m₀ j Set.univ X ∧
            box (0 : CTorus d L N₁ m₁ k) (cellSide L P.m₀ m₁ j) ⊆ X)) ?_
          (fun _ _ _ => (Real.exp_pos _).le)) ?_
        · intro Y hY
          obtain ⟨X, -, rfl⟩ := Finset.mem_image.1 hY
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          have hDj := isDj_of_isPolyDom X.2.2.2
          exact ⟨⟨hDj, fun z hz => absurd (Set.mem_univ z) hz⟩,
            zero_cell_subset hjk hN hDj (zero_mem_Ypoly X.2.1)⟩
        · refine le_trans (le_of_eq (Finset.sum_congr rfl fun Y hY => ?_)) hG2
          rw [dcovMod_of_subset (Set.subset_univ Y)]
          rfl


end Geom

section Final

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ}

/-- **`IsSFFamily.premisesTerm`**: a member of the class supplies the premises of the termwise I-6
at each scale `1 ≤ j ≤ k` on every torus (`N₁` divisible by `L^{m₀}`), for the lifted family
`liftTF`: the geometric fields from (G1), (G2), (G5) (with `κ ≥ a_ent + 3`), the analytic fields
from the class (radius `ρ = liftRadius ≍ ε_j²`; numerical condition `hsmall`).  Only the point-group invariance (`sym_mem`, `sym_inv`)
remains as the internal hypotheses (see the module docstring of `Def6BridgeLift`). -/
theorem IsSFFamily.premisesTerm {P : Consts} {β ν a : ℕ → ℝ} {Ek : ℕ → ℝ}
    {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
    {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
      (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
    {j : ℕ}
    (hF : IsSFFamily P β ν a Tm ρd Ek) (N₁ : ℕ) [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hϱ : bgR0 d L ≤ ϱ) (hκ : aEnt d L + 3 ≤ P.κ)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hsmall : P.eps d L j ≤ (2 * bgK1 d L N + 2) * min (bgC0 d L N) (bgC1 d L N))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    (sym_mem : ∀ r : Site d → Site d, IsLatGen r →
      ∀ X ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
        X.image r ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j)
    (sym_inv : ∀ r : Site d → Site d, IsLatGen r →
      ∀ X ∈ liftPolys (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P j,
        ∀ (ψ : Site d → Spin N) (b : Spin N),
          termL (Tm N₁) j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) (X.image r)
              (pack (X.image r) (fun x => ψ (r x)) b) =
            termL (Tm N₁) j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) X (pack X ψ b)) :
    PremisesTerm (liftTF P j i₀ (nuIdeal L k (ν k) j) (liftRadius d L N P j) (Tm N₁)) i₀ i₁
      (nuIdeal L k (ν k) j) (liftRadius d L N P j)
      P.E₀ P.κ (diamA d L P.m₀ m₁)
      ((c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (P.κ - 2)) (liftDom P β ν a (Tm N₁) j i₀) :=
  (hF.liftCtx N₁ hd hL hϱ hj1 hjk (liftRadius_pos (eps_pos hF.admissible.α₀_pos j) i₀)
    (liftRadius_spec (eps_pos hF.admissible.α₀_pos j) i₀ hsmall)).premisesTerm hne
    (fun _ hX _ hx => liftPolys_diam hjk hX hx) (liftPolys_summable P j)
    (liftPolys_count_le hjk hN hκ) sym_mem sym_inv

end Final

end Balaban.SmallField.Def6
