/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BPrimeOmegaBoxes

/-!
# The thickened interaction cubes of layer `1` inside `Ω₁(𝔹_k(W))`

The thickened cube `□̂_z` of a centre of layer `1` lifts to the integer box `hatLift` (half-width
`hatRad L m₁ 1` around the centre of the cube), and `Ω₁` lifts to the union of the boxes
`Q ± 5 M₁ (L² + ⋯ + L^k)` over the cubes `Q` of `W` (`mem_genW_Ω_iff_lift`).  Let `D` divide the
cube side `T = L^k c M₁` and the doubled thickening `2 r`, and `2 hatRad ≤ D`:

* `kconn_hatI_genWC`: `□̂_z ∩ Ω₁` is king connected (two boxes meeting `□̂_z` overlap or touch);
* `connIn_hatI_genWC`: if moreover no two boxes touch (`T (m - 1) ≠ 2 r` for `m ≥ 2`, `r ≥ 1`), it
  is nearest-neighbour connected;
* `hatConn_genWC`: hence `HatConn (𝔹_k(W))`, the connectedness used by `rBPrime_aggregate`, for
  `k ≥ 2` under `L ∤ 10`, `L ≥ 7`, `L^{m₁} ∣ M₁`, `4 L² ≤ L^{m₁}` (`D = M₁ L²`;
  `tSide_mul_ne_two_omRad`, `two_hatRad_le_cell`).

At `k = 1` the boxes are the cubes of `W` themselves (`r = 0`), which may touch at a corner only;
there `□̂_z ∩ Ω₁` is king connected (`kconn_hatI_genWC` with `D = T`, `two_hatRad_le_tSide`) but not
nearest-neighbour connected in general.  The step `R` does not need it: no component of `Z^pre_1` is
ripe (`not_ripe_one`), so `R^{(1)}` removes nothing and `ℬ′` vanishes at `k = 1`.
-/

@[expose] public section

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background

namespace SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ) (Y : Set (Torus S.d (n k)))

/-- The coordinate sets of the integer lift of the thickened cube `□̂_q`. -/
def hatLift (q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k) (μ : Fin S.d) : Set ℤ :=
  {t | |(t : ℝ) - boxCtr S.L m₁ q.1 q.2 μ| < hatRad S.L m₁ q.1}

theorem ordConnected_hatLift (q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k) (μ : Fin S.d) :
    (C.hatLift q μ).OrdConnected := by
  refine ⟨fun a ha b hb t ht => ?_⟩
  simp only [hatLift, Set.mem_ofPred_eq, abs_lt] at ha hb ⊢
  have h1 : (a : ℝ) ≤ t := by exact_mod_cast ht.1
  have h2 : (t : ℝ) ≤ b := by exact_mod_cast ht.2
  constructor <;> linarith [ha.1, hb.2]

/-- The cubes of `W` as integer vectors. -/
def WIdx : Type := {q : Fin S.d → ℤ // (intTorus q : Torus S.d (n k)) ∈ W2 R Y}

/-- The lower corners of the boxes of `Ω₁`. -/
def omLo (i : WIdx (R := R) Y) (μ : Fin S.d) : ℤ := (C.tSide : ℤ) * i.1 μ - C.omRad 1

/-- The upper corners of the boxes of `Ω₁`. -/
def omHi (i : WIdx (R := R) Y) (μ : Fin S.d) : ℤ :=
  (C.tSide : ℤ) * i.1 μ + C.tSide + C.omRad 1 - 1

/-- **`Ω₁(𝔹_k(W))` on integer lifts is the union of the boxes `Q ± 5 M₁ (L² + ⋯ + L^k)`.** -/
theorem mem_genWC_Ω_one_iff (hk : 1 ≤ k) (X : Fin S.d → ℤ) :
    (intTorus X : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ (C.genWC Y).Ω 1 ↔
      X ∈ ⋃ i : WIdx (R := R) Y, ZBox.box (C.omLo Y i) (C.omHi Y i) := by
  rw [mem_genWC_Ω, sfToBg_intTorus, C.mem_genW_Ω_iff_lift Y hk, Set.mem_iUnion]
  constructor
  · rintro ⟨q, hq, hX⟩
    refine ⟨⟨q, hq⟩, ZBox.mem_box.2 fun μ => ⟨(hX μ).1, ?_⟩⟩
    dsimp only [omHi]; have := (hX μ).2; omega
  · rintro ⟨i, hi⟩
    refine ⟨i.1, i.2, fun μ => ⟨(ZBox.mem_box.1 hi μ).1, ?_⟩⟩
    have := (ZBox.mem_box.1 hi μ).2
    unfold omHi at this; omega

/-- A point of `□̂_q ∩ Ω₁` has a lift in the lifted box and the lifted `Ω₁`. -/
theorem exists_lift_hatI (hk : 1 ≤ k) {q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k}
    {x : Localization.CTorus S.d S.L C.N₁ m₁ k} (hx : x ∈ hatI (C.genWC Y) q) :
    ∃ X : Fin S.d → ℤ, X ∈ Set.pi Set.univ (C.hatLift q) ∩
        ⋃ i : WIdx (R := R) Y, ZBox.box (C.omLo Y i) (C.omHi Y i) ∧ intTorus X = x := by
  classical
  unfold hatI at hx
  rw [Finset.mem_filter] at hx
  obtain ⟨X, hX, rfl⟩ := exists_lift_of_inBox (mem_boxSet.1 hx.1)
  exact ⟨X, ⟨fun μ _ => hX μ, (C.mem_genWC_Ω_one_iff Y hk X).1 hx.2⟩, rfl⟩

/-- The projection of a point of the lifted set lies in `□̂_q ∩ Ω₁`. -/
theorem intTorus_mem_hatI (hk : 1 ≤ k) {q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k}
    {X : Fin S.d → ℤ} (hX : X ∈ Set.pi Set.univ (C.hatLift q) ∩
      ⋃ i : WIdx (R := R) Y, ZBox.box (C.omLo Y i) (C.omHi Y i)) :
    (intTorus X : Localization.CTorus S.d S.L C.N₁ m₁ k) ∈ hatI (C.genWC Y) q := by
  classical
  unfold hatI hatBox
  rw [Finset.mem_filter, mem_boxSet]
  exact ⟨inBox_intTorus fun μ => hX.1 μ (Set.mem_univ _), (C.mem_genWC_Ω_one_iff Y hk X).2 hX.2⟩

/-- **The boxes of `Ω₁` meeting `□̂_q` overlap or touch** (`D ∣ T`, `D ∣ 2 r`, `2 hatRad ≤ D`). -/
theorem omBoxes_touch {q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k} (hq : q.1 = 1) {D : ℕ}
    (hDs : D ∣ C.tSide) (hDr : D ∣ 2 * C.omRad 1)
    (hR : 2 * hatRad S.L m₁ 1 ≤ D) (i j : WIdx (R := R) Y)
    (hi : (Set.pi Set.univ (C.hatLift q) ∩ ZBox.box (C.omLo Y i) (C.omHi Y i)).Nonempty)
    (hj : (Set.pi Set.univ (C.hatLift q) ∩ ZBox.box (C.omLo Y j) (C.omHi Y j)).Nonempty)
    (μ : Fin S.d) :
    C.omLo Y j μ ≤ C.omHi Y i μ + 1 ∧ C.omLo Y i μ ≤ C.omHi Y j μ + 1 := by
  obtain ⟨a, haH, ha⟩ := hi
  obtain ⟨b, hbH, hb⟩ := hj
  have ha' := ZBox.mem_box.1 ha μ
  have hb' := ZBox.mem_box.1 hb μ
  have hR' : 2 * hatRad S.L m₁ q.1 ≤ ((D : ℤ) : ℝ) := by rw [hq]; exact_mod_cast hR
  have hDs' : (D : ℤ) ∣ C.tSide := by exact_mod_cast hDs
  have hDr' : (D : ℤ) ∣ 2 * (C.omRad 1 : ℤ) := by exact_mod_cast hDr
  have haμ := haH μ (Set.mem_univ _)
  have hbμ := hbH μ (Set.mem_univ _)
  unfold omLo omHi at ha' hb' ⊢
  exact ⟨ZBox.touch_of_near hDs' hDr' hR' ha'.2 hb'.1 haμ hbμ,
    ZBox.touch_of_near hDs' hDr' hR' hb'.2 ha'.1 hbμ haμ⟩

/-- **The boxes of `Ω₁` meeting `□̂_q` overlap** when no two boxes touch. -/
theorem omBoxes_overlap {q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k} (hq : q.1 = 1) {D : ℕ}
    (hDs : D ∣ C.tSide) (hDr : D ∣ 2 * C.omRad 1) (hr : 1 ≤ C.omRad 1)
    (hnt : ∀ m : ℤ, 2 ≤ m → (C.tSide : ℤ) * (m - 1) ≠ 2 * C.omRad 1)
    (hR : 2 * hatRad S.L m₁ 1 ≤ D) (i j : WIdx (R := R) Y)
    (hi : (Set.pi Set.univ (C.hatLift q) ∩ ZBox.box (C.omLo Y i) (C.omHi Y i)).Nonempty)
    (hj : (Set.pi Set.univ (C.hatLift q) ∩ ZBox.box (C.omLo Y j) (C.omHi Y j)).Nonempty)
    (μ : Fin S.d) :
    C.omLo Y j μ ≤ C.omHi Y i μ ∧ C.omLo Y i μ ≤ C.omHi Y j μ := by
  obtain ⟨a, haH, ha⟩ := hi
  obtain ⟨b, hbH, hb⟩ := hj
  have ha' := ZBox.mem_box.1 ha μ
  have hb' := ZBox.mem_box.1 hb μ
  have hR' : 2 * hatRad S.L m₁ q.1 ≤ ((D : ℤ) : ℝ) := by rw [hq]; exact_mod_cast hR
  have hT : (0 : ℤ) < C.tSide := by exact_mod_cast C.tSide_pos
  have hDs' : (D : ℤ) ∣ C.tSide := by exact_mod_cast hDs
  have hDr' : (D : ℤ) ∣ 2 * (C.omRad 1 : ℤ) := by exact_mod_cast hDr
  have hr' : (1 : ℤ) ≤ C.omRad 1 := by exact_mod_cast hr
  have haμ := haH μ (Set.mem_univ _)
  have hbμ := hbH μ (Set.mem_univ _)
  unfold omLo omHi at ha' hb' ⊢
  exact ⟨ZBox.overlap_of_near hT hr' hDs' hDr' hnt hR' ha'.2 hb'.1 haμ hbμ,
    ZBox.overlap_of_near hT hr' hDs' hDr' hnt hR' hb'.2 ha'.1 hbμ haμ⟩

/-- **`□̂_q ∩ Ω₁(𝔹_k(W))` is king connected** at every centre of layer `1` (`k ≥ 1`), for a common
divisor `D` of the cube side and of the doubled thickening with `2 hatRad ≤ D`: two points are
joined by a chain of points of `□̂_q ∩ Ω₁` whose consecutive integer lifts differ by at most `1`
in every coordinate. -/
theorem kconn_hatI_genWC (hk : 1 ≤ k) {D : ℕ} (hDs : D ∣ C.tSide)
    (hDr : D ∣ 2 * C.omRad 1) (hR : 2 * hatRad S.L m₁ 1 ≤ D)
    (q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k) (hq : q.1 = 1) :
    ∀ x ∈ hatI (C.genWC Y) q, ∀ y ∈ hatI (C.genWC Y) q,
      Relation.ReflTransGen (fun a b => a ∈ hatI (C.genWC Y) q ∧ b ∈ hatI (C.genWC Y) q ∧
        ∃ A B : Fin S.d → ℤ, intTorus A = a ∧ intTorus B = b ∧ ∀ μ, |A μ - B μ| ≤ 1) x y := by
  intro x hx y hy
  obtain ⟨X, hX, rfl⟩ := C.exists_lift_hatI Y hk hx
  obtain ⟨Z, hZ, rfl⟩ := C.exists_lift_hatI Y hk hy
  have h := ZBox.kconn_inter_iUnion (C.ordConnected_hatLift q) (C.omLo Y) (C.omHi Y)
    (fun i j hi hj => C.omBoxes_touch Y hq hDs hDr hR i j hi hj) X hX Z hZ
  refine Relation.ReflTransGen.lift (fun A : Fin S.d → ℤ =>
    (intTorus A : Localization.CTorus S.d S.L C.N₁ m₁ k)) (fun A B hAB => ?_) _ _ h
  exact ⟨C.intTorus_mem_hatI Y hk hAB.1, C.intTorus_mem_hatI Y hk hAB.2.1, A, B, rfl, rfl,
    hAB.2.2⟩

/-- **`□̂_q ∩ Ω₁(𝔹_k(W))` is nearest-neighbour connected** at every centre of layer `1`, when no
two boxes of `Ω₁` touch (`T (m - 1) ≠ 2 r` for `m ≥ 2`, `r ≥ 1`). -/
theorem connIn_hatI_genWC (hk : 1 ≤ k) {D : ℕ} (hDs : D ∣ C.tSide)
    (hDr : D ∣ 2 * C.omRad 1) (hr : 1 ≤ C.omRad 1)
    (hnt : ∀ m : ℤ, 2 ≤ m → (C.tSide : ℤ) * (m - 1) ≠ 2 * C.omRad 1)
    (hR : 2 * hatRad S.L m₁ 1 ≤ D) (q : ℕ × Localization.CTorus S.d S.L C.N₁ m₁ k)
    (hq : q.1 = 1) : ConnIn (hatI (C.genWC Y) q) := by
  intro x hx y hy
  obtain ⟨X, hX, rfl⟩ := C.exists_lift_hatI Y hk hx
  obtain ⟨Z, hZ, rfl⟩ := C.exists_lift_hatI Y hk hy
  have h := ZBox.nconn_inter_iUnion (C.ordConnected_hatLift q) (C.omLo Y) (C.omHi Y)
    (fun i j hi hj => C.omBoxes_overlap Y hq hDs hDr hr hnt hR i j hi hj) X hX Z hZ
  refine Relation.ReflTransGen.lift (fun A : Fin S.d → ℤ =>
    (intTorus A : Localization.CTorus S.d S.L C.N₁ m₁ k)) (fun A B hAB => ?_) _ _ h
  refine ⟨C.intTorus_mem_hatI Y hk hAB.1, C.intTorus_mem_hatI Y hk hAB.2.1, ?_⟩
  obtain ⟨μ, he | he⟩ := hAB.2.2
  · refine ⟨μ, Or.inl ?_⟩
    rw [he]
    dsimp only
    rw [← intTorus_add_aux, intTorus_single_aux]
    simp
  · refine ⟨μ, Or.inr ?_⟩
    rw [he]
    dsimp only
    rw [← intTorus_add_aux, intTorus_single_aux]
    simp

/-! ### The constants -/

/-- `M₁ L²` divides the cube side for `k ≥ 2`. -/
theorem cell2_dvd_tSide (hk : 2 ≤ k) : C.geo.M1 * S.L ^ 2 ∣ C.tSide := by
  unfold tSide
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  exact ⟨S.L ^ t * C.geo.c, by ring⟩

/-- `M₁ L²` divides the doubled thickening of `Ω₁`. -/
theorem cell2_dvd_omRad : C.geo.M1 * S.L ^ 2 ∣ 2 * C.omRad 1 := by
  unfold omRad
  have h : S.L ^ 2 ∣ ∑ i ∈ Finset.Ioc 1 k, S.L ^ i :=
    Finset.dvd_sum fun i hi => pow_dvd_pow _ (by have := (Finset.mem_Ioc.1 hi).1; omega)
  obtain ⟨t, ht⟩ := h
  exact ⟨10 * t, by rw [ht]; ring⟩

/-- The thickening of `Ω₁` is positive for `k ≥ 2`. -/
theorem one_le_omRad_one (hk : 2 ≤ k) : 1 ≤ C.omRad 1 := by
  unfold omRad
  have h2 : 2 ∈ Finset.Ioc 1 k := Finset.mem_Ioc.2 ⟨by omega, hk⟩
  have hs : S.L ^ 2 ≤ ∑ i ∈ Finset.Ioc 1 k, S.L ^ i :=
    Finset.single_le_sum (f := fun i => S.L ^ i) (fun _ _ => Nat.zero_le _) h2
  have hL : 1 ≤ S.L ^ 2 := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne S.L))
  have hM : 1 ≤ C.geo.M1 := Nat.pos_of_ne_zero (NeZero.ne _)
  calc 1 ≤ 5 * 1 * 1 := by norm_num
    _ ≤ 5 * C.geo.M1 * ∑ i ∈ Finset.Ioc 1 k, S.L ^ i :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (hL.trans hs)

/-- **No two boxes of `Ω₁` touch for `k ≥ 2`** if `L ∤ 10`: `L^k c M₁ (m - 1) = 10 M₁ (L² + ⋯ + L^k)`
forces `c ∣ 10` at `k = 2` (impossible, `c ≥ 14`) and `L ∣ 10` at `k ≥ 3`. -/
theorem tSide_mul_ne_two_omRad (hk : 2 ≤ k) (hL10 : ¬ S.L ∣ 10) :
    ∀ m : ℤ, 2 ≤ m → (C.tSide : ℤ) * (m - 1) ≠ 2 * C.omRad 1 := by
  intro m hm he
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m - 1 = (m' : ℤ) := ⟨(m - 1).toNat, by omega⟩
  rw [hm'] at he
  have he' : C.tSide * m' = 2 * C.omRad 1 := by exact_mod_cast he
  have hM : 0 < C.geo.M1 := Nat.pos_of_ne_zero (NeZero.ne _)
  have hL : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
  have hsplit : ∑ i ∈ Finset.Ioc 1 k, S.L ^ i = S.L ^ 2 + ∑ i ∈ Finset.Ioc 2 k, S.L ^ i := by
    rw [← Finset.sum_Ioc_consecutive _ (by norm_num : 1 ≤ 2) hk, Nat.Ioc_succ_singleton,
      Finset.sum_singleton]
  -- cancel `M₁`
  have e1 : C.geo.M1 * (S.L ^ k * C.geo.c * m') =
      C.geo.M1 * (10 * (S.L ^ 2 + ∑ i ∈ Finset.Ioc 2 k, S.L ^ i)) := by
    unfold tSide omRad at he'
    rw [hsplit] at he'
    linarith [he']
  have e2 := Nat.eq_of_mul_eq_mul_left hM e1
  rcases Nat.lt_or_ge k 3 with hk3 | hk3
  · have hk2 : k = 2 := by omega
    subst hk2
    have hI : Finset.Ioc 2 2 = ∅ := Finset.Ioc_self 2
    rw [hI, Finset.sum_empty, add_zero] at e2
    have e3 : S.L ^ 2 * (C.geo.c * m') = S.L ^ 2 * 10 := by linarith [e2]
    have e4 := Nat.eq_of_mul_eq_mul_left (pow_pos hL 2) e3
    have hc := C.geo.hc
    have hm1 : 1 ≤ m' := by omega
    have : 14 * 1 ≤ C.geo.c * m' := Nat.mul_le_mul hc hm1
    omega
  · have hdl : S.L ^ 3 ∣ S.L ^ k * C.geo.c * m' := by
      have : S.L ^ 3 ∣ S.L ^ k := pow_dvd_pow _ hk3
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_right this _) _
    have hdr : S.L ^ 3 ∣ 10 * ∑ i ∈ Finset.Ioc 2 k, S.L ^ i :=
      Dvd.dvd.mul_left (Finset.dvd_sum fun i hi =>
        pow_dvd_pow _ (by have := (Finset.mem_Ioc.1 hi).1; omega)) _
    rw [e2, mul_add] at hdl
    have h3 : S.L ^ 3 ∣ 10 * S.L ^ 2 := (Nat.dvd_add_right hdr).1 (by
      rw [add_comm]; exact hdl)
    have h4 : S.L * S.L ^ 2 ∣ 10 * S.L ^ 2 := by rw [← pow_succ']; exact h3
    exact hL10 (Nat.dvd_of_mul_dvd_mul_right (pow_pos hL 2) h4)

/-- `2 hatRad L m₁ 1 ≤ M₁ L²` if `L ≥ 7`, `L^{m₁} ∣ M₁` and `4 L² ≤ L^{m₁}`. -/
theorem two_hatRad_le_cell (hL7 : 7 ≤ S.L) (hdvd : S.L ^ m₁ ∣ C.geo.M1)
    (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁) : 2 * hatRad S.L m₁ 1 ≤ ((C.geo.M1 * S.L ^ 2 : ℕ) : ℝ) := by
  have hM1 : S.L ^ m₁ ≤ C.geo.M1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) hdvd
  have hL : (7 : ℝ) ≤ S.L := by exact_mod_cast hL7
  have hM1' : ((S.L : ℝ)) ^ m₁ ≤ C.geo.M1 := by exact_mod_cast hM1
  have hM' : 4 * (S.L : ℝ) ^ 2 ≤ (S.L : ℝ) ^ m₁ := by exact_mod_cast hM
  unfold hatRad
  have hp : (S.L : ℝ) ^ (1 + m₁) = S.L * (S.L : ℝ) ^ m₁ := by rw [pow_add, pow_one]
  rw [hp]
  push_cast
  have hL0 : (0 : ℝ) ≤ S.L := by linarith
  have hA : (0 : ℝ) ≤ (S.L : ℝ) ^ m₁ := by positivity
  have h1 : (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ m₁ ≤ C.geo.M1 * (S.L : ℝ) ^ 2 := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hM1' (by positivity)
  have h2 : 7 * ((S.L : ℝ) * (S.L : ℝ) ^ m₁) ≤ (S.L : ℝ) ^ 2 * (S.L : ℝ) ^ m₁ := by
    rw [sq, mul_assoc]; exact mul_le_mul_of_nonneg_right hL (by positivity)
  have h3 : 4 * ((S.L : ℝ) * (S.L : ℝ) ^ 2) ≤ (S.L : ℝ) * (S.L : ℝ) ^ m₁ := by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hM' hL0
  have h4 : (S.L : ℝ) ^ 2 * (S.L : ℝ) = (S.L : ℝ) * (S.L : ℝ) ^ 2 := by ring
  nlinarith [h1, h2, h3, h4]

/-- `2 hatRad L m₁ 1 ≤ L c M₁` (the cube side at `k = 1`) if `L^{m₁} ∣ M₁` and `4 L² ≤ L^{m₁}`
(`c ≥ 14`). -/
theorem two_hatRad_le_tSide (hk : k = 1) (hdvd : S.L ^ m₁ ∣ C.geo.M1)
    (hM : 4 * S.L ^ 2 ≤ S.L ^ m₁) : 2 * hatRad S.L m₁ 1 ≤ ((C.tSide : ℕ) : ℝ) := by
  have hM1 : S.L ^ m₁ ≤ C.geo.M1 := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne _)) hdvd
  have hM1' : ((S.L : ℝ)) ^ m₁ ≤ C.geo.M1 := by exact_mod_cast hM1
  have hM' : 4 * (S.L : ℝ) ^ 2 ≤ (S.L : ℝ) ^ m₁ := by exact_mod_cast hM
  have hc : (14 : ℝ) ≤ C.geo.c := by exact_mod_cast C.geo.hc
  have hL0 : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
  unfold hatRad tSide
  subst hk
  have hp : (S.L : ℝ) ^ (1 + m₁) = S.L * (S.L : ℝ) ^ m₁ := by rw [pow_add, pow_one]
  rw [hp]
  push_cast
  have hA : (0 : ℝ) ≤ (S.L : ℝ) ^ m₁ := by positivity
  have h1 : (S.L : ℝ) * (S.L : ℝ) ^ m₁ ≤ S.L * C.geo.M1 := mul_le_mul_of_nonneg_left hM1' hL0
  have h3 : 4 * ((S.L : ℝ) * (S.L : ℝ) ^ 2) ≤ (S.L : ℝ) * (S.L : ℝ) ^ m₁ := by
    rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left hM' hL0
  have h5 : 14 * ((S.L : ℝ) * C.geo.M1) ≤ C.geo.c * ((S.L : ℝ) * C.geo.M1) :=
    mul_le_mul_of_nonneg_right hc (by positivity)
  have h4 : (S.L : ℝ) ^ 2 * (S.L : ℝ) = (S.L : ℝ) * (S.L : ℝ) ^ 2 := by ring
  nlinarith [h1, h3, h4, h5]

/-! ### `HatConn` for `k ≥ 2` -/

/-- **`HatConn (𝔹_k(W))` for `k ≥ 2`**: the thickened cubes of layer `≥ 2` lie in `Ω₁`
(`hatConn_of_layer_one`), those of layer `1` meet `Ω₁` in a connected set
(`connIn_hatI_genWC` with `D = M₁ L²`), under `L ∤ 10`, `L ≥ 7`, `L^{m₁} ∣ M₁` (and
`4 L² ≤ L^{m₁}`, `DGSetting.hM`). -/
theorem hatConn_genWC {a : ℕ → ℝ} {ν : ℝ}
    (hS : DGSetting (C.genWC Y) a ν) (hk : 2 ≤ k) (hL10 : ¬ S.L ∣ 10) (hL7 : 7 ≤ S.L)
    (hdvd : S.L ^ m₁ ∣ C.geo.M1) : HatConn (C.genWC Y) :=
  hatConn_of_layer_one hS fun q _ hq =>
    C.connIn_hatI_genWC Y (by omega) (C.cell2_dvd_tSide hk) C.cell2_dvd_omRad (C.one_le_omRad_one hk)
      (C.tSide_mul_ne_two_omRad hk hL10) (C.two_hatRad_le_cell hL7 hdvd hS.hM) q hq

end SFCtx

end Balaban.LargeField.Def7
