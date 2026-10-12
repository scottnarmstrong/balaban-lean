/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.Def6AvgGeom

/-!
# Reynolds averaging: the thermodynamic limit of sums over shapes around an arbitrary centre

CLASS-RULINGS Q-C (2) at a centre `y` (the centred statement for the second moment is
`Def6InfTail`, `Def6BridgeInfMoment`):

* `cyc_lower`, `coord_le_of_good`: from (G5), the coordinates of a polymer of `𝒟_j` through `y`
  are bounded by its size, without any assumption on the polymer except that it does not wind;
* `infPoly_of_small`: a good shape through `y` whose size is below the threshold `tauY` (which
  tends to infinity) is a polymer of `T∞`;
* `tendsto_shapeSum`: if the torus quantities of the shapes through `y` agree with those of `T∞`
  on the polymers of `T∞` and both are bounded by `C e^{-κ d}` then the sums over the shapes of
  the `n`-th torus converge to the sum over the polymers of `T∞`.
-/

@[expose] public section

namespace Balaban.SmallField.Def6

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation
  Balaban.SmallField Filter

theorem cyc_lower {n W R : ℕ} (hn : n = W * R) (hW : 0 < W) [NeZero n] {z y : ℤ}
    (hz : 2 * |z| ≤ R) :
    (W : ℤ) * (|z| - |y|) ≤ (LargeField.cycNorm n (((W : ℤ) * (z - y) : ℤ) : ZMod n) : ℤ) := by
  subst hn
  set r := LargeField.cycNorm (W * R) (((W : ℤ) * (z - y) : ℤ) : ZMod (W * R)) with hr
  obtain ⟨t, ht, htc⟩ := (LargeField.cycNorm_le_iff (((W : ℤ) * (z - y) : ℤ) : ZMod (W * R)) r).mp le_rfl
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (((W : ℤ) * (z - y) : ℤ)) t (W * R)).mp htc.symm
  obtain ⟨q, hq⟩ := hdvd
  have hW0 : (0 : ℤ) < W := by exact_mod_cast hW
  set v := z - y + (R : ℤ) * q with hv
  have ht' : t = (W : ℤ) * v := by
    push_cast at hq
    rw [hv]; linarith
  have habs : |t| = (W : ℤ) * |v| := by
    rw [ht', abs_mul, abs_of_pos hW0]
  have hzv : |z| ≤ |y| + |v| := by
    by_cases hq0 : q = 0
    · have : z = y + v := by rw [hv, hq0]; ring
      have h3 : |y + v| ≤ |y| + |v| := abs_add_le _ _
      rw [this]; exact h3
    · have hRq : (R : ℤ) ≤ |(R : ℤ) * q| := by
        rw [abs_mul, Nat.abs_cast]
        have : 1 ≤ |q| := Int.one_le_abs hq0
        nlinarith [Nat.cast_nonneg (α := ℤ) R]
      have hyv : (R : ℤ) * q = y + v - z := by rw [hv]; ring
      have h1 : |(R : ℤ) * q| ≤ |y + v| + |z| := by
        rw [hyv]
        exact abs_sub _ _
      have h2 : |y + v| ≤ |y| + |v| := abs_add_le _ _
      linarith
  have hfin : (W : ℤ) * (|z| - |y|) ≤ (W : ℤ) * |v| := by nlinarith
  rw [← habs] at hfin
  exact hfin.trans ht

variable {d L N₁ m₁ k : ℕ} [NeZero L] [NeZero N₁]

/-- **Coordinates of a polymer from its size**: for two blocks `y, z` of a polymer of `𝒟_j` that does
not wind, `|z_μ| ≤ |y_μ| + M (d_j(X) + 2 √d L)` (from (G5), no assumption that the polymer is small). -/
theorem coord_le_of_good {m₀ j : ℕ} (hjk : j ≤ k) {X' : Finset (Site d)}
    (hnw : NonWind L N₁ m₁ k j X')
    (hX : IsPolyDom m₀ j (Ypoly (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j X')) {y z : Site d}
    (hy : y ∈ X') (hz : z ∈ X') (μ : Fin d) :
    ((|z μ| : ℤ) : ℝ) ≤ |y μ| + ((L : ℝ) ^ (m₀ + m₁)) * (sizeJ (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) m₀ j (Ypoly j X') + 2 * Real.sqrt d * L) := by
  have hDj := isDj_of_isPolyDom hX
  have hzmem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ∈ Ypoly j X' := by
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j z) ∈ X'
    rw [unlift_ibase hjk (hnw z hz)]; exact hz
  have hymem : ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ∈ Ypoly j X' := by
    show unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (ibase j y) ∈ X'
    rw [unlift_ibase hjk (hnw y hy)]; exact hy
  have hG := G5 hDj hzmem hymem
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hLj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
  have hside : N₁ * L ^ m₁ * L ^ k = L ^ j * (N₁ * L ^ m₁ * L ^ (k - j)) := side_eq hjk
  have hRpos : NeZero (N₁ * L ^ m₁ * L ^ (k - j)) := ⟨by
    have := NeZero.pos N₁; have := NeZero.pos L; positivity⟩
  -- the coordinate bound
  have hzR : 2 * |z μ| ≤ ((N₁ * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
    have h1 := ZMod.natAbs_valMinAbs_le (((z μ : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ (k - j))))
    rw [hnw z hz μ] at h1
    have h2 : |z μ| = ((z μ).natAbs : ℤ) := Int.abs_eq_natAbs _
    omega
  have hc := cyc_lower (n := N₁ * L ^ m₁ * L ^ k) (W := L ^ j)
    (R := N₁ * L ^ m₁ * L ^ (k - j)) hside (pow_pos (NeZero.pos L) j) (z := z μ) (y := y μ) hzR
  have hdiff : ((ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z μ -
      ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y μ : ZMod (N₁ * L ^ m₁ * L ^ k))) =
      ((((L ^ j : ℕ) : ℤ) * (z μ - y μ) : ℤ) : ZMod (N₁ * L ^ m₁ * L ^ k)) := by
    simp only [ibase]; push_cast; ring
  rw [← hdiff] at hc
  have hcμ : ((L : ℝ) ^ j) * ((|z μ| : ℝ) - |y μ|) ≤
      ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k) (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z μ -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y μ) : ℕ) : ℝ) := by
    have := (Int.cast_le (R := ℝ)).2 hc
    push_cast at this
    simpa using this
  have hed : ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k) (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z μ -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y μ) : ℕ) : ℝ) ≤
      euclDist (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z)
        (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y) := by
    unfold euclDist
    apply Real.le_sqrt_of_sq_le
    exact Finset.single_le_sum (f := fun ν => ((LargeField.cycNorm (N₁ * L ^ m₁ * L ^ k)
      (ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j z ν -
        ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j y ν) : ℕ) : ℝ) ^ 2)
      (fun ν _ => sq_nonneg _) (Finset.mem_univ μ)
  have hcell : (cellSide L m₀ m₁ j : ℝ) = (L : ℝ) ^ j * (L : ℝ) ^ (m₀ + m₁) := by
    unfold cellSide; push_cast; rw [← pow_add]; congr 1; ring
  rw [hcell] at hG
  have hmain : (L : ℝ) ^ j * ((|z μ| : ℝ) - |y μ|) ≤ (L : ℝ) ^ j * ((L : ℝ) ^ (m₀ + m₁) *
      (sizeJ (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j (Ypoly j X') +
        2 * Real.sqrt d * L)) := by
    calc _ ≤ _ := hcμ
      _ ≤ _ := hed
      _ ≤ _ := hG
      _ = _ := by unfold sizeJ; ring
  have := le_of_mul_le_mul_left hmain hLj
  simp only [Int.cast_abs] at this ⊢
  linarith

section Shapes

variable (L m₁ k) in
/-- The shapes containing the centre `y` that are good on the `n`-th torus of the sequence. -/
def ShAt (m₀ j : ℕ) (y : Site d) (n : ℕ) : Set (Finset (Site d)) :=
  {X' | y ∈ X' ∧ GoodAt L m₁ k m₀ j X' n}

theorem shAt_finite (m₀ j : ℕ) (y : Site d) (n : ℕ) :
    (ShAt (d := d) L m₁ k m₀ j y n).Finite := by
  classical
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  set r : ℕ := (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j)) / 2 with hr
  set B : Finset (Site d) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(r : ℤ)) r) with hB
  refine ((B.powerset : Set (Finset (Site d))).toFinite).subset ?_
  intro X' hX'
  obtain ⟨-, hnw, -⟩ := hX'
  show X' ∈ (B.powerset : Set (Finset (Site d)))
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
  intro z hz
  simp only [hB, Fintype.mem_piFinset, Finset.mem_Icc]
  intro μ
  have h1 := ZMod.natAbs_valMinAbs_le
    (((z μ : ℤ) : ZMod (torusSeq L m₀ n * L ^ m₁ * L ^ (k - j))))
  rw [hnw z hz μ] at h1
  have h2 : ((z μ).natAbs : ℤ) ≤ r := by exact_mod_cast h1
  constructor <;> omega

variable (d L m₁ k) in
/-- The size threshold below which a good shape through `y` on the `n`-th torus is small. -/
noncomputable def tauY (m₀ j n : ℕ) (y : Site d) : ℝ :=
  (((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 4 - ∑ μ, |(y μ : ℝ)| -
    ((L * L ^ (m₀ + m₁) : ℕ) : ℝ) - 1) / ((L : ℝ) ^ (m₀ + m₁)) - 2 * Real.sqrt d * L

/-- **The coordinates of a good shape through `y` whose size is below the threshold are small**
compared with the side of the torus. -/
theorem small_coords_of_tauY {m₀ j : ℕ} (hjk : j ≤ k) {y : Site d} {X' : Finset (Site d)} {n : ℕ}
    (hy : y ∈ X') (hgood : GoodAt L m₁ k m₀ j X' n)
    (hsz : sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y) :
    ∀ z ∈ X', ∀ μ, 4 * (|z μ| + ((L * L ^ (m₀ + m₁) : ℕ) : ℤ) + 1) <
      ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℤ) := by
  have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
  have hMb : (0 : ℝ) < (L : ℝ) ^ (m₀ + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    positivity
  intro z hz μ
  have h1 := coord_le_of_good (m₀ := m₀) hjk hgood.1 hgood.2 hy hz μ
  have h2 : |(y μ : ℝ)| ≤ ∑ ν, |(y ν : ℝ)| :=
    Finset.single_le_sum (f := fun ν => |(y ν : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ μ)
  have h3 : ((L : ℝ) ^ (m₀ + m₁)) * (sizeSeq L m₁ k m₀ j X' n + 2 * Real.sqrt d * L) <
      ((L : ℝ) ^ (m₀ + m₁)) * (tauY d L m₁ k m₀ j n y + 2 * Real.sqrt d * L) :=
    mul_lt_mul_of_pos_left (by linarith) hMb
  have h4 : ((L : ℝ) ^ (m₀ + m₁)) * (tauY d L m₁ k m₀ j n y + 2 * Real.sqrt d * L) =
      (((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 4 - ∑ μ, |(y μ : ℝ)| -
        ((L * L ^ (m₀ + m₁) : ℕ) : ℝ) - 1) := by
    unfold tauY; field_simp; ring
  have h5 : ((|z μ| : ℤ) : ℝ) < ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 4 -
      ((L * L ^ (m₀ + m₁) : ℕ) : ℝ) - 1 := by
    have : ((|z μ| : ℤ) : ℝ) ≤ |(y μ : ℝ)| + ((L : ℝ) ^ (m₀ + m₁)) *
        (sizeSeq L m₁ k m₀ j X' n + 2 * Real.sqrt d * L) := by
      simpa [Int.cast_abs, sizeSeq, sizeJ, Int.cast_abs] using h1
    linarith
  have h6 : (4 : ℝ) * (((|z μ| : ℤ) : ℝ) + ((L * L ^ (m₀ + m₁) : ℕ) : ℝ) + 1) <
      ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by linarith
  exact_mod_cast h6

/-- **A good shape through `y` whose size is below the threshold is a polymer of `T∞`** (it is
good on every later torus): its coordinates are small by (G5) (`coord_le_of_good`) and a small good
shape stays good (`goodAt_of_small`). -/
theorem infPoly_of_small {m₀ j : ℕ} (hjk : j ≤ k) {y : Site d} {X' : Finset (Site d)} {n : ℕ}
    (hy : y ∈ X') (hgood : GoodAt L m₁ k m₀ j X' n)
    (hsz : sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y) :
    InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' := by
  have hsmall := small_coords_of_tauY hjk hy hgood hsz
  show ∀ᶠ n' in atTop, _
  filter_upwards [Filter.eventually_ge_atTop n] with n' hn'
  exact goodAt_of_small hjk hgood hsmall hn'

theorem tendsto_tauY (m₀ j : ℕ) (y : Site d) :
    Tendsto (fun n => tauY d L m₁ k m₀ j n y) atTop atTop := by
  have hMb : (0 : ℝ) < (L : ℝ) ^ (m₀ + m₁) := by
    have : (0 : ℝ) < L := by exact_mod_cast NeZero.pos L
    positivity
  set c₁ : ℝ := ∑ μ, |(y μ : ℝ)| + ((L * L ^ (m₀ + m₁) : ℕ) : ℝ) + 1 with hc₁
  have hlow : ∀ n : ℕ, ((n : ℝ) + 1) / 4 - c₁ ≤
      ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) / 4 - ∑ μ, |(y μ : ℝ)| -
        ((L * L ^ (m₀ + m₁) : ℕ) : ℝ) - 1 := by
    intro n
    have h := (succ_le_torusSeq (L := L) m₀ n).trans
      (torusSeq_le_side (L := L) (m₁ := m₁) (k := k) m₀ n j)
    have h' : (n : ℝ) + 1 ≤ ((torusSeq L m₀ n * L ^ m₁ * L ^ (k - j) : ℕ) : ℝ) := by
      exact_mod_cast h
    rw [hc₁]; linarith
  have h1 : Tendsto (fun n : ℕ => (((n : ℝ) + 1) / 4 - c₁) / ((L : ℝ) ^ (m₀ + m₁)) -
      2 * Real.sqrt d * L) atTop atTop := by
    have h0 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / 4 - c₁) atTop atTop := by
      have := tendsto_atTop_add_const_right atTop (1 - 4 * c₁) h0
      have h3 := this.atTop_div_const (by norm_num : (0 : ℝ) < 4)
      refine h3.congr fun n => ?_
      ring
    have h4 := h2.atTop_div_const hMb
    exact tendsto_atTop_add_const_right atTop (-(2 * Real.sqrt d * L)) h4 |>.congr fun n => by ring
  refine tendsto_atTop_mono (fun n => ?_) h1
  unfold tauY
  have := div_le_div_of_nonneg_right (hlow n) hMb.le
  linarith

end Shapes

section Limit

open Classical in
/-- Summability of a family of shapes with the exponential bound. -/
theorem summable_shapes {m₀ j : ℕ} (hjk : j ≤ k) {κ : ℝ} (hκ : aEnt d L + 1 ≤ κ) (y : Site d)
    (ainf : Finset (Site d) → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h3 : ∀ X', y ∈ X' → InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' →
      ‖ainf X'‖ ≤ C * Real.exp (-κ * dInf L m₁ k m₀ j X'))
    (h4 : ∀ X', ¬ (y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X') → ainf X' = 0) :
    Summable (fun X' => ‖ainf X'‖) ∧ ∑' X', ‖ainf X'‖ ≤ C * K0 d L κ := by
  have hκ0 : 0 ≤ κ := by
    have := aEnt_nonneg d L; linarith
  have key : ∀ u : Finset (Finset (Site d)), ∑ X' ∈ u, ‖ainf X'‖ ≤ C * K0 d L κ := by
    intro u
    set u' := u.filter (fun X' => y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X') with hu'
    have h1 : ∑ X' ∈ u, ‖ainf X'‖ = ∑ X' ∈ u', ‖ainf X'‖ := by
      rw [hu', Finset.sum_filter]
      refine Finset.sum_congr rfl fun X' _ => ?_
      by_cases h : y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X'
      · rw [ite_eq_left h]
      · rw [ite_eq_right h, h4 X' h, norm_zero]
    have hev : ∀ᶠ n in atTop, ∀ X' ∈ u', GoodAt L m₁ k m₀ j X' n := by
      rw [Filter.eventually_all_finset]
      exact fun X' hX' => (Finset.mem_filter.1 hX').2.2
    obtain ⟨n, hn⟩ := hev.exists
    have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
    rw [h1]
    calc ∑ X' ∈ u', ‖ainf X'‖ ≤ ∑ X' ∈ u', C * Real.exp (-κ * sizeSeq L m₁ k m₀ j X' n) := by
          refine Finset.sum_le_sum fun X' hX' => ?_
          have hX'' := (Finset.mem_filter.1 hX').2
          refine (h3 X' hX''.1 hX''.2).trans ?_
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC
          have := sizeSeq_le_dInf hjk (hn X' hX')
          nlinarith
      _ = C * ∑ X' ∈ u', Real.exp (-κ * sizeSeq L m₁ k m₀ j X' n) := by rw [Finset.mul_sum]
      _ ≤ C * K0 d L κ := by
          refine mul_le_mul_of_nonneg_left ?_ hC
          exact exp_sum_le_at hjk (torusSeq_dvd m₀ n) hκ y u' fun X' hX' =>
            ⟨(Finset.mem_filter.1 hX').2.1, (hn X' hX').1, (hn X' hX').2⟩
  have hs : Summable (fun X' => ‖ainf X'‖) := summable_of_sum_le (fun _ => norm_nonneg _) key
  exact ⟨hs, hs.tsum_le_of_sum_le key⟩

open Classical in
/-- **The generic thermodynamic limit around a centre `y`**: if the torus quantities `an n X'` of the
shapes through `y` that are good on the `n`-th torus agree with the quantities `ainf X'` of `T∞` on
the good shapes of size below the threshold `tauY` (these are polymers of `T∞`), and both are
bounded by `C e^{-κ d}` (`κ > a_ent + 1`), then the sums over the shapes of the torus converge to the
sum of `T∞`. -/
theorem tendsto_shapeSum {m₀ j : ℕ} (hjk : j ≤ k) {κ : ℝ} (hκ : aEnt d L + 1 < κ) (y : Site d)
    (an : ℕ → Finset (Site d) → ℂ) (ainf : Finset (Site d) → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (h1 : ∀ n X', y ∈ X' → GoodAt L m₁ k m₀ j X' n →
      sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y → an n X' = ainf X')
    (h2 : ∀ n X', y ∈ X' → GoodAt L m₁ k m₀ j X' n →
      ‖an n X'‖ ≤ C * Real.exp (-κ * sizeSeq L m₁ k m₀ j X' n))
    (h3 : ∀ X', y ∈ X' → InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X' →
      ‖ainf X'‖ ≤ C * Real.exp (-κ * dInf L m₁ k m₀ j X'))
    (h4 : ∀ X', ¬ (y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X') → ainf X' = 0) :
    Tendsto (fun n => ∑ᶠ X' ∈ ShAt (d := d) L m₁ k m₀ j y n, an n X') atTop
      (nhds (∑' X', ainf X')) := by
  obtain ⟨hs, -⟩ := summable_shapes (m₀ := m₀) (j := j) hjk (by linarith) y ainf hC h3 h4
  set S : ℕ → Finset (Finset (Site d)) :=
    fun n => (shAt_finite (d := d) (L := L) (m₁ := m₁) (k := k) m₀ j y n).toFinset with hS
  have hmemS : ∀ n X', X' ∈ S n ↔ y ∈ X' ∧ GoodAt L m₁ k m₀ j X' n := by
    intro n X'; simp [hS, ShAt]
  have hfin : ∀ n, ∑ᶠ X' ∈ ShAt (d := d) L m₁ k m₀ j y n, an n X' = ∑ X' ∈ S n, an n X' :=
    fun n => finsum_mem_eq_finite_toFinset_sum _ _
  set f : ℕ → Finset (Site d) → ℂ := fun n X' =>
    if (X' ∈ S n ∧ sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y) then ainf X' else 0 with hf
  have hdec : ∀ n, ∑ X' ∈ S n, an n X' = ∑' X', f n X' +
      ∑ X' ∈ (S n).filter (fun X' => ¬ sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y),
        an n X' := by
    intro n
    rw [← Finset.sum_filter_add_sum_filter_not (S n)
      (fun X' => sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y)]
    congr 1
    rw [tsum_eq_sum (s := (S n).filter (fun X' => sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y))]
    · refine Finset.sum_congr rfl fun X' hX' => ?_
      have hX'' := Finset.mem_filter.1 hX'
      rw [hf]; simp only
      rw [ite_eq_left ⟨hX''.1, hX''.2⟩]
      exact h1 n X' ((hmemS n X').1 hX''.1).1 ((hmemS n X').1 hX''.1).2 hX''.2
    · intro X' hX'
      rw [hf]; simp only
      rw [ite_eq_right]
      intro h
      exact hX' (Finset.mem_filter.2 h)
  -- first part
  have hfirst : Tendsto (fun n => ∑' X', f n X') atTop (nhds (∑' X', ainf X')) := by
    refine tendsto_tsum_of_dominated_convergence (bound := fun X' => ‖ainf X'‖) hs ?_
      (Eventually.of_forall fun n X' => ?_)
    · intro X'
      by_cases h : y ∈ X' ∧ InfPoly (L := L) (m₁ := m₁) (k := k) m₀ j X'
      · refine tendsto_const_nhds.congr' ?_
        have hτ := (tendsto_tauY (L := L) (m₁ := m₁) (k := k) m₀ j y).eventually_gt_atTop
          (dInf L m₁ k m₀ j X')
        filter_upwards [h.2, hτ] with n hn hτn
        have hsz := sizeSeq_le_dInf hjk hn
        rw [hf]; simp only
        rw [ite_eq_left ⟨(hmemS n X').2 ⟨h.1, hn⟩, lt_of_le_of_lt hsz hτn⟩]
      · rw [h4 X' h]
        refine tendsto_const_nhds.congr fun n => ?_
        rw [hf]; simp only
        rw [ite_eq_right]
        rintro ⟨hm, hI⟩
        have hm' := (hmemS n X').1 hm
        exact h ⟨hm'.1, infPoly_of_small hjk hm'.1 hm'.2 hI⟩
    · rw [hf]; simp only
      by_cases h : X' ∈ S n ∧ sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y
      · rw [ite_eq_left h]
      · rw [ite_eq_right h, norm_zero]; exact norm_nonneg _
  -- tail
  set κ₁ : ℝ := aEnt d L + 1 with hκ₁
  have htail : ∀ n, ‖∑ X' ∈ (S n).filter
      (fun X' => ¬ sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y), an n X'‖ ≤
      C * K0 d L κ₁ * Real.exp (-((κ - κ₁) * tauY d L m₁ k m₀ j n y)) := by
    intro n
    have : NeZero (torusSeq L m₀ n) := ⟨torusSeq_ne_zero m₀ n⟩
    set T := (S n).filter (fun X' => ¬ sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y) with hT
    have hκκ : 0 ≤ κ - κ₁ := by rw [hκ₁]; linarith
    calc ‖∑ X' ∈ T, an n X'‖ ≤ ∑ X' ∈ T, ‖an n X'‖ := norm_sum_le _ _
      _ ≤ ∑ X' ∈ T, C * (Real.exp (-((κ - κ₁) * tauY d L m₁ k m₀ j n y)) *
            Real.exp (-κ₁ * sizeSeq L m₁ k m₀ j X' n)) := by
          refine Finset.sum_le_sum fun X' hX' => ?_
          have hX'' := Finset.mem_filter.1 hX'
          have hm := (hmemS n X').1 hX''.1
          refine (h2 n X' hm.1 hm.2).trans ?_
          refine mul_le_mul_of_nonneg_left ?_ hC
          have hτ : tauY d L m₁ k m₀ j n y ≤ sizeSeq L m₁ k m₀ j X' n := not_lt.1 hX''.2
          rw [← Real.exp_add]
          refine Real.exp_le_exp.2 ?_
          nlinarith
      _ = C * Real.exp (-((κ - κ₁) * tauY d L m₁ k m₀ j n y)) *
            ∑ X' ∈ T, Real.exp (-κ₁ * sizeSeq L m₁ k m₀ j X' n) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun X' _ => ?_; ring
      _ ≤ C * Real.exp (-((κ - κ₁) * tauY d L m₁ k m₀ j n y)) * K0 d L κ₁ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact exp_sum_le_at hjk (torusSeq_dvd m₀ n) le_rfl y T fun X' hX' => by
            have hm := (hmemS n X').1 (Finset.mem_filter.1 hX').1
            exact ⟨hm.1, hm.2.1, hm.2.2⟩
      _ = _ := by ring
  have hsecond : Tendsto (fun n => ∑ X' ∈ (S n).filter
      (fun X' => ¬ sizeSeq L m₁ k m₀ j X' n < tauY d L m₁ k m₀ j n y), an n X') atTop (nhds 0) := by
    have h1' : Tendsto (fun n => Real.exp (-((κ - κ₁) * tauY d L m₁ k m₀ j n y))) atTop (nhds 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_tauY (L := L) (m₁ := m₁) (k := k) m₀ j y).const_mul_atTop
          (by rw [hκ₁]; linarith))
    have h2' := h1'.const_mul (C * K0 d L κ₁)
    rw [mul_zero] at h2'
    refine squeeze_zero_norm (fun n => ?_) h2'
    have := htail n
    linarith
  have hsum := hfirst.add hsecond
  rw [add_zero] at hsum
  refine hsum.congr fun n => ?_
  rw [hfin n, hdec n]

end Limit

end Balaban.SmallField.Def6
