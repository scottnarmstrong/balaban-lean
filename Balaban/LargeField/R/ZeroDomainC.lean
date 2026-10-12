module

public import Balaban.LargeField.R.ZeroDomainB
public import Balaban.LargeField.R.RipeBox
public import Balaban.LargeField.History.BoxCover
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Geometry of the late scales (Part III, Lemma III.3.2 (b), (c), (d))

For a ripe component `Z` of `Z^pre_k` (`RipeWindow`):

* `RipeWindow.exists_desc`: `Z` has an ancestor at every scale `j ∈ (q, k]`;
* `RipeWindow.lin_box_late` (III.3.2 (b)): for `k₂ ≤ j ≤ k`, `Z_j` is one box of side `≤ crit_j`;
* `diam_Zk2_lt`, `diam_Zk3_lt` (III.3.2 (b)): `diam_k(Z_{k₂}) < 9/8 (2c₀+1)`, `diam_k(Z_{k₃}) < 9 (2c₀+1) M`;
* `ZzeroDD_in_box` (III.3.2 (c), III.5.0 (c)): `Z''₀` lies in a box of `π_k`-cubes of side `< D''₀ = 9(2c₀+1)+8`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  {H : RegionHistory S n R k0 K}

/-- A ripe component has an ancestor at every scale `j ∈ (q, k]` (the lineage has no new cube there,
so every component has an old part). -/
theorem RipeWindow.exists_desc {k : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hkK : k ≤ K) :
    ∀ {j : ℕ}, (H.bk k Z).q < j → j ≤ k → ∃ Y : H.Comp j, H.Desc j k Y Z := by
  have key : ∀ t j : ℕ, j + t = k → (H.bk k Z).q < j → ∃ Y : H.Comp j, H.Desc j k Y Z := by
    intro t
    induction t with
    | zero =>
      intro j hj _
      obtain rfl : j = k := by omega
      exact ⟨Z, Desc.refl Z⟩
    | succ t ih =>
      intro j hj hq
      obtain ⟨Y', hd'⟩ := ih (j + 1) (by omega) (by omega)
      have hsp := H.seed_pos (k := j) (by omega) Y'
      have hnew : (Y'.1 ∩ H.newCubes (j + 1)).card = 0 := by
        rw [Finset.card_eq_zero, ← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨x, hx⟩
        have h1 := W.no_new (j + 1) (by omega) (by omega)
        have hxl : x ∈ H.lin (j + 1) k Z := mem_lin.mpr ⟨Y', hd', (Finset.mem_inter.mp hx).1⟩
        have : x ∈ H.lin (j + 1) k Z ∩ H.newCubes (j + 1) := Finset.mem_inter.mpr ⟨hxl, (Finset.mem_inter.mp hx).2⟩
        rw [h1] at this
        simp at this
      obtain ⟨c, hc⟩ := Finset.card_pos.mp (by omega : 0 < (H.parts j Y').card)
      obtain ⟨hrem, hs⟩ := (H.mem_parts j c Y').mp hc
      exact ⟨c, (Desc.single hrem hs).trans hd'⟩
  intro j hq hjk
  exact key (k - j) j (by omega) hq

variable [NeZero S.L] [NeZero S.M]

/-- **Lemma III.3.2 (b)**: for `k₂ ≤ j ≤ k`, `Z_j` is one box, of sides in `[1, crit_j]`. -/
theorem RipeWindow.lin_box_late (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    {k : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hk0 : k ≤ k0) (hkK : k ≤ K)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) {j : ℕ} (hj : S.kTwo k ≤ j)
    (hjk : j ≤ k) :
    ∃ (a : Torus S.d (n j)) (sd : Fin S.d → ℕ), (H.lin j k Z : Set (Torus S.d (n j))) = box a sd ∧
      ∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit j := by
  have h3 := H.eight_le_L_mul_lateR k
  obtain ⟨-, hq2, hs2, -⟩ := G.lateScale_geom h18 W.core_window.1 W.point.2.1 h3
  obtain ⟨Y, hY⟩ := W.exists_desc hkK (by omega) hjk
  exact W.lin_eq_box hk0 hT (by omega) hY

theorem two_c0_le_lateR (G : S.Good) (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0) (j : ℕ) :
    2 * S.c0 + 10 ≤ S.lateR j := hR0.trans (G.ok.lateR_mono (Nat.zero_le _))

/-- **Lemma III.3.2 (b)**, `k₂`: `Z_{k₂}` is one box of `π_{k₂}`-cubes with
`diam_k(Z_{k₂}) = sd · M / L^{n₂} < 9/8 (2c₀ + 1)` in every direction (units of `k`-blocks). -/
theorem RipeWindow.diam_Zk2_lt (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0)
    {k : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hk0 : k ≤ k0) (hkK : k ≤ K)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) :
    ∃ (a : Torus S.d (n (S.kTwo k))) (sd : Fin S.d → ℕ),
      (H.lin (S.kTwo k) k Z : Set (Torus S.d (n (S.kTwo k)))) = box a sd ∧
      (∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit (S.kTwo k)) ∧
      ∀ i, (sd i : ℝ) * S.M / (S.L : ℝ) ^ S.lateN2 k < 9 / 8 * (2 * S.c0 + 1) := by
  have h3 := H.eight_le_L_mul_lateR k
  obtain ⟨a, sd, hbox, hsd⟩ := W.lin_box_late G h18 hk0 hkK hT le_rfl (G.ok.kTwo_le k)
  refine ⟨a, sd, hbox, hsd, fun i => ?_⟩
  obtain ⟨-, -, -, -, -, hlt, -⟩ := G.lateScale_geom h18 W.core_window.1 W.point.2.1 h3
  have ok := G.ok
  have hcrit := ok.crit_le_lateR (two_c0_le_lateR G hR0 (S.kTwo k))
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hpow : (0 : ℝ) < (S.L : ℝ) ^ S.lateN2 k := by positivity
  rw [div_lt_iff₀ hpow]
  push_cast at hlt
  have h1 : (S.M : ℝ) * S.lateR (S.kTwo k) < 9 / 8 * (S.L : ℝ) ^ S.lateN2 k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h2 : (sd i : ℝ) ≤ (2 * S.c0 + 1) * S.lateR (S.kTwo k) := by exact_mod_cast (hsd i).2.trans hcrit
  have hM : (0 : ℝ) ≤ S.M := Nat.cast_nonneg _
  have hc : (0 : ℝ) < 2 * S.c0 + 1 := by positivity
  calc (sd i : ℝ) * S.M ≤ (2 * S.c0 + 1) * S.lateR (S.kTwo k) * S.M := mul_le_mul_of_nonneg_right h2 hM
    _ = (2 * S.c0 + 1) * ((S.M : ℝ) * S.lateR (S.kTwo k)) := by ring
    _ < (2 * S.c0 + 1) * (9 / 8 * (S.L : ℝ) ^ S.lateN2 k) := mul_lt_mul_of_pos_left h1 hc
    _ = 9 / 8 * (2 * S.c0 + 1) * (S.L : ℝ) ^ S.lateN2 k := by ring

/-- **Lemma III.3.2 (b)**, `k₃`: `Z_{k₃}` is one box of `π_{k₃}`-cubes with
`diam_k(Z_{k₃}) = sd · M / L^{n₃} < 9 (2c₀ + 1) M` in every direction (units of `k`-blocks). -/
theorem RipeWindow.diam_Zk3_lt (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0)
    {k : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hk0 : k ≤ k0) (hkK : k ≤ K)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) :
    ∃ (a : Torus S.d (n (S.kThree k))) (sd : Fin S.d → ℕ),
      (H.lin (S.kThree k) k Z : Set (Torus S.d (n (S.kThree k)))) = box a sd ∧
      (∀ i, 1 ≤ sd i ∧ sd i ≤ S.crit (S.kThree k)) ∧
      ∀ i, (sd i : ℝ) * S.M / (S.L : ℝ) ^ S.lateN3 k < 9 * (2 * S.c0 + 1) * S.M := by
  have h3 := H.eight_le_L_mul_lateR k
  have ok := G.ok
  obtain ⟨-, hq2, hs2, h23, h3k, -, hlt⟩ := G.lateScale_geom h18 W.core_window.1 W.point.2.1 h3
  obtain ⟨a, sd, hbox, hsd⟩ := W.lin_box_late G h18 hk0 hkK hT h23 h3k
  refine ⟨a, sd, hbox, hsd, fun i => ?_⟩
  have hcrit := ok.crit_le_lateR (two_c0_le_lateR G hR0 (S.kThree k))
  have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hpow : (0 : ℝ) < (S.L : ℝ) ^ S.lateN3 k := by positivity
  rw [div_lt_iff₀ hpow]
  push_cast at hlt
  have h1 : (S.lateR (S.kThree k) : ℝ) < 9 * (S.L : ℝ) ^ S.lateN3 k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have h2 : (sd i : ℝ) ≤ (2 * S.c0 + 1) * S.lateR (S.kThree k) := by exact_mod_cast (hsd i).2.trans hcrit
  have hM : (0 : ℝ) ≤ S.M := Nat.cast_nonneg _
  have hMpos : (0 : ℝ) < S.M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.M)
  have hc : (0 : ℝ) < 2 * S.c0 + 1 := by positivity
  calc (sd i : ℝ) * S.M ≤ (2 * S.c0 + 1) * S.lateR (S.kThree k) * S.M := mul_le_mul_of_nonneg_right h2 hM
    _ < (2 * S.c0 + 1) * (9 * (S.L : ℝ) ^ S.lateN3 k) * S.M := by
        apply mul_lt_mul_of_pos_right _ hMpos
        exact mul_lt_mul_of_pos_left h1 hc
    _ = 9 * (2 * S.c0 + 1) * S.M * (S.L : ℝ) ^ S.lateN3 k := by ring

include H in
/-- The `π_k`-cubes meeting a box of `π_j`-cubes (`j ≤ k`) lie in a box of `π_k`-cubes. -/
theorem cubesMeetingZ3_subset_box {k : ℕ} (hkK : k ≤ K) (hk3 : S.kThree k ≤ k) (Z : H.Comp k)
    {a : Torus S.d (n (S.kThree k))} {sd : Fin S.d → ℕ}
    (hbox : (H.lin (S.kThree k) k Z : Set (Torus S.d (n (S.kThree k)))) ⊆ box a sd) :
    ∃ (b0 : Torus S.d (n k)) (w : Fin S.d → ℕ),
      (∀ i, w i ≤ (sd i * (S.M * S.L ^ S.kThree k) + S.M * S.L ^ k - 2) / (S.M * S.L ^ k) + 1) ∧
      H.cubesMeetingZ3 k Z ⊆ box b0 w := by
  have hN : fineSide S n k = (S.M * S.L ^ k) * n k := by unfold fineSide; ring
  have hu : fineSide S n k = (S.M * S.L ^ S.kThree k) * n (S.kThree k) :=
    H.F.fineSide_eq hk3 hkK
  refine ⟨fun i => blockCoord (S.M * S.L ^ k) (n k)
      (((a i).val * (S.M * S.L ^ S.kThree k) : ℕ) : ZMod (fineSide S n k)),
    fun i => (sd i * (S.M * S.L ^ S.kThree k) + S.M * S.L ^ k - 2) / (S.M * S.L ^ k) + 1,
    fun i => le_rfl, ?_⟩
  rintro c ⟨s, rfl, hs⟩ i
  obtain ⟨j, hj, hji⟩ := hbox hs i
  have hji' : blockCoord (S.M * S.L ^ S.kThree k) (n (S.kThree k)) (s i) = a i + (j : ZMod _) := hji
  obtain ⟨j', hj', hx⟩ := blockCoord_box_image hN hu (a i) (sd i) j hj (s i) hji'
  exact ⟨j', Nat.lt_succ_of_le hj', hx⟩

/-- **Lemma III.3.2 (c), III.5.0 (c)**: `Z''₀` (`ZzeroDD`) lies in a box of `π_k`-cubes of side
`< D''₀ = 9 (2c₀ + 1) + 8` in every direction, i.e. `diam_k(Z''₀) < D''₀ M` (`k`-blocks; a `π_k`-cube is
`M` blocks). -/
theorem ZzeroDD_in_box (G : S.Good)
    (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
    (hR0 : 2 * S.c0 + 10 ≤ S.lateR 0)
    {k : ℕ} {Z : H.Comp k} (W : H.RipeWindow k Z) (hk0 : k ≤ k0) (hkK : k ≤ K)
    (hT : ∀ j, 1 ≤ j → j ≤ k0 → 4 * S.rho j + 21 ≤ n j) :
    ∃ (b0 : Torus S.d (n k)) (w : Fin S.d → ℕ), (∀ i, w i < 9 * (2 * S.c0 + 1) + 8) ∧
      H.ZzeroDD k Z ⊆ box b0 w := by
  have h3 := H.eight_le_L_mul_lateR k
  have ok := G.ok
  obtain ⟨-, hq2, hs2, h23, h3k, -, hlt⟩ := G.lateScale_geom h18 W.core_window.1 W.point.2.1 h3
  obtain ⟨a, sd, hbox, hsd⟩ := W.lin_box_late G h18 hk0 hkK hT h23 h3k
  obtain ⟨b0, w0, hw0, hC⟩ := cubesMeetingZ3_subset_box (H := H) hkK h3k Z hbox.subset
  refine ⟨fun i => b0 i - ((3 : ℕ) : ZMod (n k)), fun i => w0 i + 2 * 3, fun i => ?_, ?_⟩
  · -- the arithmetic
    have hcrit := ok.crit_le_lateR (two_c0_le_lateR G hR0 (S.kThree k))
    have hR : S.lateR (S.kThree k) < 9 * S.L ^ S.lateN3 k := by
      have hL : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
      push_cast at hlt
      have : (S.lateR (S.kThree k) : ℝ) < 9 * (S.L : ℝ) ^ S.lateN3 k := by
        by_contra hcon
        push Not at hcon
        nlinarith
      exact_mod_cast this
    have hsdlt : sd i < 9 * (2 * S.c0 + 1) * S.L ^ S.lateN3 k := by
      have h1 : sd i ≤ (2 * S.c0 + 1) * S.lateR (S.kThree k) := (hsd i).2.trans hcrit
      have h2 : (2 * S.c0 + 1) * S.lateR (S.kThree k) < (2 * S.c0 + 1) * (9 * S.L ^ S.lateN3 k) :=
        Nat.mul_lt_mul_of_pos_left hR (by omega)
      calc sd i < (2 * S.c0 + 1) * (9 * S.L ^ S.lateN3 k) := lt_of_le_of_lt h1 h2
        _ = _ := by ring
    have hk : S.L ^ k = S.L ^ S.kThree k * S.L ^ S.lateN3 k := by
      rw [← pow_add]; congr 1; unfold Setting.lateN3; omega
    set P := S.M * S.L ^ S.kThree k with hP
    have hPpos : 0 < P := Nat.mul_pos (by have := NeZero.pos S.M; omega) (pow_pos (NeZero.pos S.L) _)
    have hA : S.M * S.L ^ k = P * S.L ^ S.lateN3 k := by rw [hk, hP]; ring
    have hdiv : (sd i * P + S.M * S.L ^ k - 2) / (S.M * S.L ^ k) ≤ 9 * (2 * S.c0 + 1) := by
      rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul (by rw [hA]; exact Nat.mul_pos hPpos (pow_pos (NeZero.pos S.L) _))]
      rw [hA]
      have h1 : (sd i + 1) * P ≤ 9 * (2 * S.c0 + 1) * S.L ^ S.lateN3 k * P :=
        Nat.mul_le_mul_right _ hsdlt
      have h2 : 0 < S.L ^ S.lateN3 k := pow_pos (NeZero.pos S.L) _
      have e1 : (sd i + 1) * P = sd i * P + P := by ring
      have e2 : 9 * (2 * S.c0 + 1) * S.L ^ S.lateN3 k * P =
          9 * ((2 * S.c0 + 1) * (P * S.L ^ S.lateN3 k)) := by ring
      have e3 : (9 * (2 * S.c0 + 1)).succ * (P * S.L ^ S.lateN3 k) =
          9 * ((2 * S.c0 + 1) * (P * S.L ^ S.lateN3 k)) + P * S.L ^ S.lateN3 k := by
        rw [Nat.succ_eq_add_one]; ring
      have e4 : P ≤ P * S.L ^ S.lateN3 k := Nat.le_mul_of_pos_right _ h2
      rw [e1, e2] at h1
      rw [e3]
      omega
    have := hw0 i
    show w0 i + 2 * 3 < 9 * (2 * S.c0 + 1) + 8
    omega
  · refine (nbhd_mono (le_refl 3) hC : nbhd 3 (H.cubesMeetingZ3 k Z) ⊆ nbhd 3 (box b0 w0)).trans ?_
    exact nbhd_box_subset 3 b0 w0

end RegionHistory

end Balaban.LargeField
