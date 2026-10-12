/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgLiftC

/-!
# Reynolds averaging: geometry of the polymers of `T∞` around an arbitrary centre

The two-point path bound (G5) and the counting (G1), (G2) for the polymers of `T∞` containing a
given centre `y` (the centred versions are `liftPolys_diam`, `sum_wt_dInf_le`):

* `diam2_torus`, `infPoly_diam2`: `|x - y|₁ ≤ A (1 + d_j(X'))` for `x, y ∈ X'`;
* `card_le_good`, `sum_wt_dInf_le_at`: `∑ |X'|² (1 + d)⁶ e^{-(κ-1) d} ≤ K₀` over polymers of `T∞`
  containing `y`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

theorem cycNorm_ibase_sub {j : ℕ} (hjk : j ≤ k) {x y : Site d}
    (hxy : ∀ μ, 2 * |x μ - y μ| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) (μ : Fin d) :
    LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
      ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y : CTorus d L N₁ m₁ k) μ) =
      L ^ j * (x μ - y μ).natAbs := by
  have hm : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  have hz : ∀ ν, ZMod.valMinAbs ((((x - y) ν : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j)))) = (x - y) ν :=
    fun ν => valMinAbs_intCast_of_small (by simpa using hxy ν)
  have := cycNorm_ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk hz μ
  have e : (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y : CTorus d L N₁ m₁ k) =
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y) - 0 := by
    funext ν; simp [ibase, mul_sub]
  rw [e]
  simpa using this


/-- **The two-point path bound (from (G5)) for a polymer of `𝒟_j` that does not wind**:
`|x - y|₁ ≤ A (1 + d_j(X))` for two blocks of the polymer that are not antipodal on the torus. -/
theorem diam2_torus {P : Consts} {j : ℕ} (hjk : j ≤ k) {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X')
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) {x y : Site d}
    (hx : x ∈ X') (hy : y ∈ X')
    (hxy : ∀ μ, 2 * |x μ - y μ| < ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ)) :
    ((∑ μ, |x μ - y μ| : ℤ) : ℝ) ≤ diamA d L P.m₀ m₁ * (1 + sizeJ (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
  have hDj := isDj_of_isPolyDom hX
  have hxmem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x ∈ Ypoly j X' := by
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j x) ∈ X'
    rw [unlift_ibase hjk (hnw x hx)]; exact hx
  have hymem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈ Ypoly j X' := by
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j y) ∈ X'
    rw [unlift_ibase hjk (hnw y hy)]; exact hy
  have hG := G5 hDj hxmem hymem
  set S : ℝ := ∑ μ, (((x μ - y μ).natAbs : ℕ) : ℝ) ^ 2 with hS
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have he : euclDist (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) = (L : ℝ) ^ j * Real.sqrt S := by
    unfold euclDist
    have h1 : ∀ μ, ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
        ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) μ -
          (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) μ) : ℕ) : ℝ)
        = (L : ℝ) ^ j * (((x μ - y μ).natAbs : ℕ) : ℝ) := by
      intro μ
      have := cycNorm_ibase_sub (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) hjk hxy μ
      simp only [Pi.sub_apply] at this
      rw [this]; push_cast; ring
    have h2 : ∑ μ, ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
        ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x) μ -
          (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) μ) : ℕ) : ℝ) ^ 2
        = ((L : ℝ) ^ j) ^ 2 * S := by
      rw [hS, Finset.mul_sum]
      exact Finset.sum_congr rfl fun μ _ => by rw [h1 μ]; ring
    rw [h2, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hLj.le]
  have hT : ((∑ μ, |x μ - y μ| : ℤ) : ℝ) = ∑ μ, (((x μ - y μ).natAbs : ℕ) : ℝ) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hT2 : (∑ μ, (((x μ - y μ).natAbs : ℕ) : ℝ)) ^ 2 ≤ d * S := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun μ => (((x μ - y μ).natAbs : ℕ) : ℝ))
    simpa [hS] using this
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT3 : (∑ μ, (((x μ - y μ).natAbs : ℕ) : ℝ)) ≤ Real.sqrt d * Real.sqrt S := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg d)]
    exact Real.le_sqrt_of_sq_le hT2
  have hcell : (cellSide L P.m₀ m₁ j : ℝ) = (L : ℝ) ^ j * (L : ℝ) ^ (P.m₀ + m₁) := by
    unfold cellSide; push_cast; rw [← pow_add]; congr 1; ring
  rw [he, hcell] at hG
  have hS1 : Real.sqrt S ≤ (L : ℝ) ^ (P.m₀ + m₁) *
      (sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X') +
        2 * Real.sqrt d * L) := by
    have : (L : ℝ) ^ j * Real.sqrt S ≤ (L : ℝ) ^ j * ((L : ℝ) ^ (P.m₀ + m₁) *
        (sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X') +
          2 * Real.sqrt d * L)) := by
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


/-- A shape is eventually separated from itself by less than half the torus. -/
theorem eventually_half {m₀ j : ℕ} (x y : Site d) :
    ∀ᶠ n in atTop, ∀ μ, 2 * |x μ - y μ| <
      ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
  rw [Filter.eventually_all]
  intro μ
  filter_upwards [Filter.eventually_ge_atTop ((x μ - y μ).natAbs * 2 + 1)] with n hn
  have hR := (succ_le_torusSeq (L := L) m₀ n).trans
    (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n j)
  have : ((x μ - y μ).natAbs : ℤ) * 2 + 1 ≤ n := by exact_mod_cast hn
  have h3 : (n : ℤ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by exact_mod_cast hR
  have h4 : |x μ - y μ| = ((x μ - y μ).natAbs : ℤ) := Int.abs_eq_natAbs _
  omega

/-- **The two-point path bound for a polymer of `T∞`**: `|x - y|₁ ≤ A (1 + d_j(X'))`. -/
theorem infPoly_diam2 {P : Consts} {j : ℕ} (hjk : j ≤ k) {X' : Finset (Site d)}
    (hX : InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') {x y : Site d} (hx : x ∈ X')
    (hy : y ∈ X') :
    ((∑ μ, |x μ - y μ| : ℤ) : ℝ) ≤ diamA d L P.m₀ m₁ * (1 + dInf L m₁ k P.m₀ j X') := by
  obtain ⟨n, hn, hxy⟩ := (hX.and (eventually_half (L := L) (m₁ := m₁) (k := k) (m₀ := P.m₀) (j := j)
    x y)).exists
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  refine (diam2_torus (P := P) hjk hn.1 hn.2 hx hy hxy).trans ?_
  refine mul_le_mul_of_nonneg_left ?_ (diamA_nonneg d L P.m₀ m₁)
  have := sizeSeq_le_dInf hjk (m₀ := P.m₀) (X' := X') (n := n) hn
  show 1 + sizeSeq L m₁ k P.m₀ j X' n ≤ 1 + dInf L m₁ k P.m₀ j X'
  linarith

/-- The block count of a polymer of `𝒟_j` that does not wind (from (G1)). -/
theorem card_le_good {P : Consts} {j : ℕ} (hjk : j ≤ k) (hN : L ^ P.m₀ ∣ N₁) {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X')
    (hX : IsPolyDom P.m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) :
    (X'.card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d *
      (1 + sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j (Ypoly j X')) := by
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

omit [NeZero N₁] in
/-- **Counting for `T∞` around a centre `y`** (from (G1), (G2)): `∑ |X'|² (1 + d)⁶ e^{-(κ-1) d} ≤ K₀`
over finitely many polymers of `T∞` containing `y`. -/
theorem sum_wt_dInf_le_at {P : Consts} {j : ℕ} (hjk : j ≤ k) {κ : ℝ} (hκ : aEnt d L + 3 ≤ κ)
    (y : Site d) (S : Finset (Finset (Site d)))
    (hS : ∀ X' ∈ S, y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) P.m₀ j X') :
    ∑ X' ∈ S, wt κ X' (dInf L m₁ k P.m₀ j X') ≤
      (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) *
        K0 d L (κ - 2) := by
  have hev : ∀ᶠ n in atTop, ∀ X' ∈ S, GoodAt L m₁ k P.m₀ j X' n := by
    rw [Filter.eventually_all_finset]
    exact fun X' hX' => (hS X' hX').2
  obtain ⟨n, hn⟩ := hev.exists
  have : NeZero (torusSeq L P.m₀ n) := ⟨torusSeq_ne_zero P.m₀ n⟩
  set Cw := (c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) ^ 2 * (Nat.factorial 8 * Real.exp 1) with hCw
  have hC₁0 : 0 ≤ c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d := by
    have : 0 ≤ c1 d L := by unfold c1; positivity
    positivity
  calc ∑ X' ∈ S, wt κ X' (dInf L m₁ k P.m₀ j X')
      ≤ ∑ X' ∈ S, Cw * Real.exp (-(κ - 2) * sizeSeq L m₁ k P.m₀ j X' n) := by
        refine Finset.sum_le_sum fun X' hX' => ?_
        have hgood := hn X' hX'
        have hs := sizeSeq_le_dInf hjk hgood
        have hs0 := sizeSeq_nonneg (L := L) (m₁ := m₁) (k := k) P.m₀ j X' n
        have hcard := card_le_good (P := P) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) hjk
          (torusSeq_dvd P.m₀ n) hgood.1 hgood.2
        have hseq : sizeJ (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) P.m₀ j
            (Ypoly (L := L) (N₁ := torusSeq L P.m₀ n) (m₁ := m₁) (k := k) j X') =
            sizeSeq L m₁ k P.m₀ j X' n := rfl
        rw [hseq] at hcard
        refine (wt_le_of_card_le (C₁ := c1 d L * ((L : ℝ) ^ (P.m₀ + m₁)) ^ d) (by linarith) ?_).trans ?_
        · refine hcard.trans ?_
          exact mul_le_mul_of_nonneg_left (by linarith) hC₁0
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity)
          have haE := aEnt_nonneg d L
          nlinarith
    _ = Cw * ∑ X' ∈ S, Real.exp (-(κ - 2) * sizeSeq L m₁ k P.m₀ j X' n) := by rw [Finset.mul_sum]
    _ ≤ Cw * K0 d L (κ - 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact exp_sum_le_at hjk (torusSeq_dvd P.m₀ n) (by linarith) y S fun X' hX' =>
          ⟨(hS X' hX').1, (hn X' hX').1, (hn X' hX').2⟩

end Balaban.SmallField.Def6
