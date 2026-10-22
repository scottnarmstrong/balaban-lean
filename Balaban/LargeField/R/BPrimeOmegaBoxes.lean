/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.BoxUnionConn
public import Balaban.LargeField.R.BPrimeGenW
public import Balaban.Localization.DecoupledFieldLocal

/-!
# The layers of `𝔹_k(W)` as unions of boxes; the thickened interaction cubes inside `Ω₁`

The layers of the minimal generating set `𝔹_k(W)` (P3 (4.4)–(4.6), `minLayer`) are, on integer
lifts, unions of boxes: `Ω_k` is the union of the cubes `Q` of `W` (side `L^k c M₁`), and every
step `Ω_j = nearStep_j Ω_{j+1}` thickens by `5 L` cubes of side `L^j M₁`, so
`Ω_j = ⋃_{Q ∈ W} (Q ± 5 M₁ (L^{j+1} + ⋯ + L^k))` (`mem_genW_Ω_iff_lift`).

The thickened interaction cube `□̂_z` of a centre of layer `1` is a box of half-width
`hatRad L m₁ 1`.  Two boxes of `Ω₁` that meet `□̂_z` cannot be separated by a positive gap in a
coordinate once `2 hatRad ≤ D` for a common divisor `D` of the cube side and of the doubled
thickening (`D = M₁ L²` for `k ≥ 2`, `D = L c M₁` for `k = 1`).  Hence (`ZBox`):

* `kconn_hatI_genWC`: `□̂_z ∩ Ω₁` is king connected (the boxes overlap or touch), at every `k ≥ 1`;
* `connIn_hatI_genWC`: if moreover no two boxes touch (`T (m - 1) ≠ 2 r`), it is
  nearest-neighbour connected (`ConnIn`), and `𝔹_k(W)` satisfies `HatConn`
  (`hatConn_genWC`).  For `k ≥ 2` the touching is excluded by `L ∤ 10` (and `c ≥ 14`):
  `tSide_mul_ne_two_omRad`.
-/

@[expose] public section

namespace Balaban.LargeField.ZBox

/-- The floor quotient of an integer of `[b q, b q + b)` by `b > 0` is `q`. -/
theorem ediv_eq_of_mem {a b q : ℤ} (hb : 0 < b) (h1 : b * q ≤ a) (h2 : a < b * q + b) :
    a / b = q := by
  have e : a = (a - b * q) + b * q := by ring
  rw [e, Int.add_mul_ediv_left _ _ hb.ne', Int.ediv_eq_zero_of_lt (by linarith) (by linarith),
    zero_add]

/-- **One step of the thickening on integer lifts.**  For `ℓ > 0` dividing `A < B`, an integer `x`
has floor quotient within `m` of the floor quotient of a point of `[A, B)` iff
`x ∈ [A - m ℓ, B + m ℓ)`. -/
theorem exists_ediv_near_iff {ℓ m A B x : ℤ} (hℓ : 0 < ℓ) (hm : 0 ≤ m) (hA : ℓ ∣ A)
    (hB : ℓ ∣ B) (hAB : A < B) :
    (∃ y, A ≤ y ∧ y < B ∧ |x / ℓ - y / ℓ| ≤ m) ↔ A - m * ℓ ≤ x ∧ x < B + m * ℓ := by
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  have hu1 : ℓ * (x / ℓ) ≤ x := Int.mul_ediv_self_le hℓ.ne'
  have hu2 : x < ℓ * (x / ℓ) + ℓ := Int.lt_mul_ediv_self_add hℓ
  constructor
  · rintro ⟨y, h1, h2, h3⟩
    have hv1 : ℓ * (y / ℓ) ≤ y := Int.mul_ediv_self_le hℓ.ne'
    have hv2 : y < ℓ * (y / ℓ) + ℓ := Int.lt_mul_ediv_self_add hℓ
    have hav : a ≤ y / ℓ := by
      by_contra hc
      have : ℓ * (y / ℓ + 1) ≤ ℓ * a := mul_le_mul_of_nonneg_left (by omega) hℓ.le
      linarith
    have hvb : y / ℓ + 1 ≤ b := by
      by_contra hc
      have : ℓ * b ≤ ℓ * (y / ℓ) := mul_le_mul_of_nonneg_left (by omega) hℓ.le
      linarith
    rw [abs_le] at h3
    constructor
    · have : ℓ * (a - m) ≤ ℓ * (x / ℓ) := mul_le_mul_of_nonneg_left (by omega) hℓ.le
      linarith
    · have : ℓ * (x / ℓ + 1) ≤ ℓ * (b + m) := mul_le_mul_of_nonneg_left (by omega) hℓ.le
      linarith
  · rintro ⟨h1, h2⟩
    have hu : a - m ≤ x / ℓ := by
      rw [Int.le_ediv_iff_mul_le hℓ]; linarith
    have hu' : x / ℓ < b + m := by
      rw [Int.ediv_lt_iff_lt_mul hℓ]; linarith
    have hab : a < b := by
      by_contra hc
      have : ℓ * b ≤ ℓ * a := mul_le_mul_of_nonneg_left (by omega) hℓ.le
      linarith
    set v := max a (min (b - 1) (x / ℓ)) with hv
    have hva : a ≤ v := le_max_left _ _
    have hvb : v < b := by rw [hv]; simp only [max_def, min_def]; split_ifs <;> omega
    refine ⟨ℓ * v, mul_le_mul_of_nonneg_left hva hℓ.le, mul_lt_mul_of_pos_left hvb hℓ, ?_⟩
    rw [Int.mul_ediv_cancel_left _ hℓ.ne', abs_le, hv]
    simp only [max_def, min_def]
    split_ifs <;> omega

/-- **Two boxes whose gap is a positive multiple of `D` are not both met by a set of diameter
`< D`.**  The `μ`-intervals `[T qᵢ - r, T qᵢ + T + r - 1]`, `[T qⱼ - r, T qⱼ + T + r - 1]` of two
thickened cubes, each met by a point of the real interval `(c - R, c + R)` with `2 R ≤ D`, `D`
dividing `T` and `2 r`, overlap or touch. -/
theorem touch_of_near {T r D qi qj a b : ℤ} {ctr R : ℝ} (hDT : D ∣ T) (hDr : D ∣ 2 * r) (hR : 2 * R ≤ D) (ha : a ≤ T * qi + T + r - 1) (hb : T * qj - r ≤ b)
    (ha' : |(a : ℝ) - ctr| < R) (hb' : |(b : ℝ) - ctr| < R) :
    T * qj - r ≤ T * qi + T + r - 1 + 1 := by
  by_contra hc
  have hg : D ∣ T * (qj - qi - 1) - 2 * r := dvd_sub (dvd_mul_of_dvd_left hDT _) hDr
  have hgpos : 0 < T * (qj - qi - 1) - 2 * r := by
    have : T * (qj - qi - 1) = T * qj - T * qi - T := by ring
    omega
  have hgD : D ≤ T * (qj - qi - 1) - 2 * r := Int.le_of_dvd hgpos hg
  have hba : D + 1 ≤ b - a := by
    have : T * (qj - qi - 1) = T * qj - T * qi - T := by ring
    omega
  have hba' : ((D : ℤ) : ℝ) + 1 ≤ (b : ℝ) - a := by exact_mod_cast hba
  rw [abs_lt] at ha' hb'
  linarith [ha'.1, hb'.2]

/-- **The same with no touching**: if moreover `T (m - 1) ≠ 2 r` for `m ≥ 2` and `r ≥ 1`, the two
intervals overlap. -/
theorem overlap_of_near {T r D qi qj a b : ℤ} {ctr R : ℝ} (hT : 0 < T) (hr : 1 ≤ r)
    (hDT : D ∣ T) (hDr : D ∣ 2 * r) (hnt : ∀ m : ℤ, 2 ≤ m → T * (m - 1) ≠ 2 * r)
    (hR : 2 * R ≤ D) (ha : a ≤ T * qi + T + r - 1) (hb : T * qj - r ≤ b)
    (ha' : |(a : ℝ) - ctr| < R) (hb' : |(b : ℝ) - ctr| < R) :
    T * qj - r ≤ T * qi + T + r - 1 := by
  have h := touch_of_near hDT hDr hR ha hb ha' hb'
  by_contra hc
  have he : T * (qj - qi - 1) = 2 * r := by
    have : T * (qj - qi - 1) = T * qj - T * qi - T := by ring
    omega
  have hm : 2 ≤ qj - qi := by
    by_contra hm
    have : T * (qj - qi - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT.le (by omega)
    omega
  exact hnt (qj - qi) hm he

end Balaban.LargeField.ZBox

namespace Balaban.LargeField.Def7

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Background

namespace SFCtx

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} (C : SFCtx S n R M K N k m₁ ϱ)

/-- The side `L^k c M₁` of a cube of `𝕋_k`, in sites of the level-`k` torus. -/
def tSide : ℕ := S.L ^ k * (C.geo.c * C.geo.M1)

/-- The thickening `5 M₁ (L^{j+1} + ⋯ + L^k)` of the cubes of `W` in the layer `Ω_j(𝔹_k(W))`. -/
def omRad (j : ℕ) : ℕ := 5 * C.geo.M1 * ∑ i ∈ Finset.Ioc j k, S.L ^ i

theorem omRad_self : C.omRad k = 0 := by
  simp [omRad]

theorem omRad_of_lt {j : ℕ} (hj : j < k) :
    C.omRad j = C.omRad (j + 1) + 5 * C.geo.M1 * S.L ^ (j + 1) := by
  unfold omRad
  rw [← Finset.sum_Ioc_consecutive _ (Nat.le_succ j) hj, Nat.Ioc_succ_singleton,
    Finset.sum_singleton]
  ring

theorem tSide_pos : 0 < C.tSide :=
  Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
    (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne _)) (Nat.pos_of_ne_zero (NeZero.ne _)))

theorem tSide_mul : C.tSide * n k = C.geo.M1 * (C.geo.c * n k) * S.L ^ k := by
  unfold tSide; ring

/-- `L^j M₁` divides the cube side (`j ≤ k`). -/
theorem cell_dvd_tSide {j : ℕ} (hj : j ≤ k) : S.L ^ j * C.geo.M1 ∣ C.tSide := by
  unfold tSide
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact ⟨S.L ^ t * C.geo.c, by ring⟩

/-- `L^j M₁` divides the thickening of `Ω_{j+1}`. -/
theorem cell_dvd_omRad (j : ℕ) : S.L ^ j * C.geo.M1 ∣ C.omRad (j + 1) := by
  unfold omRad
  have h : S.L ^ j ∣ ∑ i ∈ Finset.Ioc (j + 1) k, S.L ^ i :=
    Finset.dvd_sum fun i hi => pow_dvd_pow _ (by have := (Finset.mem_Ioc.1 hi).1; omega)
  obtain ⟨t, ht⟩ := h
  exact ⟨5 * t, by rw [ht]; ring⟩

/-- The sites of the level-`k` torus of an integer vector. -/
theorem sfToBg_intTorus (X : Fin S.d → ℤ) :
    sfToBg C.geo C.hT (intTorus X : Localization.CTorus S.d S.L C.N₁ m₁ k) =
      (intTorus X : BgT C.geo k) := by
  funext μ
  apply ZMod.val_injective
  rw [sfToBg, torusCast_val]
  have h1 := ZMod.val_intCast (n := C.N₁ * S.L ^ m₁ * S.L ^ k) (X μ)
  have h2 := ZMod.val_intCast (n := C.geo.M1 * (C.geo.c * n k) * S.L ^ k) (X μ)
  have e : ((C.N₁ * S.L ^ m₁ * S.L ^ k : ℕ) : ℤ) = ((C.geo.M1 * (C.geo.c * n k) * S.L ^ k : ℕ) : ℤ) :=
    by rw [C.hT]
  simp only [intTorus_apply]
  have h3 : (((X μ : ZMod (C.N₁ * S.L ^ m₁ * S.L ^ k)).val : ℕ) : ℤ) =
      (((X μ : ZMod (C.geo.M1 * (C.geo.c * n k) * S.L ^ k)).val : ℕ) : ℤ) := by
    rw [h1, h2, e]
  exact_mod_cast h3

omit [NeZero S.L] in
/-- The supremum distance of two integer vectors on a torus: every coordinate difference has an
integer representative of absolute value `≤ m`. -/
theorem supDist_intTorus_le_iff {P : ℕ} [NeZero P] (A B : Fin S.d → ℤ) (m : ℕ) :
    supDist (intTorus A : Torus S.d P) (intTorus B) ≤ m ↔
      ∀ μ, ∃ t : ℤ, |t| ≤ m ∧ (t : ZMod P) = ((A μ - B μ : ℤ) : ZMod P) := by
  rw [supDist_le_iff]
  refine forall_congr' fun μ => ?_
  rw [cycNorm_le_iff]
  simp only [intTorus_apply, Int.cast_sub]

/-- **The layers of `𝔹_k(W)` on integer lifts** (P3 (4.4)–(4.6)): `X ∈ Ω_j` iff `X` lies in the
box `Q ± 5 M₁ (L^{j+1} + ⋯ + L^k)` of a cube `Q` of `W` (`j ≤ k`). -/
theorem mem_genW_Ω_iff_lift (Y : Set (Torus S.d (n k))) {j : ℕ} (hj : j ≤ k)
    (X : Fin S.d → ℤ) :
    (intTorus X : BgT C.geo k) ∈ (C.genW Y).Ω j ↔ ∃ q : Fin S.d → ℤ,
      (intTorus q : Torus S.d (n k)) ∈ W2 R Y ∧ ∀ μ,
        (C.tSide : ℤ) * q μ - C.omRad j ≤ X μ ∧ X μ < C.tSide * q μ + C.tSide + C.omRad j := by
  classical
  have hTpos : (0 : ℤ) < C.tSide := by exact_mod_cast C.tSide_pos
  suffices H : ∀ t j, j + t = k → ∀ X : Fin S.d → ℤ,
      ((intTorus X : BgT C.geo k) ∈ (C.genW Y).Ω j ↔ ∃ q : Fin S.d → ℤ,
        (intTorus q : Torus S.d (n k)) ∈ W2 R Y ∧ ∀ μ,
          (C.tSide : ℤ) * q μ - C.omRad j ≤ X μ ∧ X μ < C.tSide * q μ + C.tSide + C.omRad j) from
    H (k - j) j (by omega) X
  intro t
  induction t with
  | zero =>
    intro j hjt X
    have hjk : j = k := by omega
    subst hjk
    have hm : C.geo.c * n j * S.L ^ (j - j) = C.geo.c * n j := by simp
    have hU := isCubeUnion_cubePre (M1 := C.geo.M1) (N₁ := C.geo.c * n j) (L := S.L) (q := j)
      le_rfl hm (W2 R Y)
    show (intTorus X : BgT C.geo j) ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n j) (L := S.L)
      (c := C.geo.c) (n := n j) (le_refl j) (W2 R Y)).Ω j ↔ _
    unfold genSF
    rw [minimalGenSet_Ω, minLayer_self, hU.cubeInterior_eq, mem_cubePre, C.omRad_self]
    have hside : C.geo.M1 * (C.geo.c * n j) * S.L ^ j = S.L ^ j * (C.geo.c * C.geo.M1) * n j := by
      ring
    have hb : blockMap (S.L ^ j * (C.geo.c * C.geo.M1)) (n j) (intTorus X : BgT C.geo j) =
        intTorus (fun μ => X μ / (C.tSide : ℤ)) := by
      funext μ
      rw [blockMap_apply, Balaban.LargeField.blockCoord_intCast hside (intTorus X μ) (X μ) rfl]
      rfl
    rw [hb]
    constructor
    · intro h
      refine ⟨fun μ => X μ / (C.tSide : ℤ), h, fun μ => ⟨?_, ?_⟩⟩
      · have := Int.mul_ediv_self_le (x := X μ) hTpos.ne'
        push_cast; linarith
      · have := Int.lt_mul_ediv_self_add (x := X μ) hTpos
        push_cast; linarith
    · rintro ⟨q, hq, hX⟩
      have e : (fun μ => X μ / (C.tSide : ℤ)) = q := funext fun μ =>
        ZBox.ediv_eq_of_mem hTpos (by have := (hX μ).1; push_cast at this; linarith)
          (by have := (hX μ).2; push_cast at this; linarith)
      rw [e]
      exact hq
  | succ t ih =>
    intro j hjt X
    have hjk : j < k := by omega
    have hj1 := ih (j + 1) (by omega)
    set ℓ : ℕ := S.L ^ j * C.geo.M1 with hℓ
    have hℓpos : (0 : ℤ) < ℓ := by
      have : 0 < ℓ := Nat.mul_pos (pow_pos (Nat.pos_of_ne_zero (NeZero.ne S.L)) _)
        (Nat.pos_of_ne_zero (NeZero.ne _))
      exact_mod_cast this
    set P : ℕ := C.geo.c * n k * S.L ^ (k - j) with hP
    have : NeZero P := ⟨Nat.mul_ne_zero (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))
      (pow_ne_zero _ (NeZero.ne _))⟩
    have hside : C.geo.M1 * (C.geo.c * n k) * S.L ^ k = ℓ * P := by
      have e : S.L ^ k = S.L ^ j * S.L ^ (k - j) := by
        rw [← pow_add, Nat.add_sub_cancel' hjk.le]
      rw [hℓ, hP, e]
      ring
    have hPℓ : (ℓ : ℤ) * P = C.tSide * n k := by
      have := C.tSide_mul; exact_mod_cast hside.symm.trans this.symm
    have hfc : ∀ Z : Fin S.d → ℤ, fineCubeIdx C.geo.M1 (C.geo.c * n k) S.L k j
        (intTorus Z : BgT C.geo k) = (intTorus (fun μ => Z μ / (ℓ : ℤ)) : Torus S.d P) := by
      intro Z
      funext μ
      unfold fineCubeIdx
      rw [blockMap_apply, Balaban.LargeField.blockCoord_intCast hside (intTorus Z μ) (Z μ) rfl]
      rfl
    have hmem : (intTorus X : BgT C.geo k) ∈ (C.genW Y).Ω j ↔
        ∃ Z : Fin S.d → ℤ, (intTorus Z : BgT C.geo k) ∈ (C.genW Y).Ω (j + 1) ∧
          ∀ μ, ∃ t : ℤ, |t| ≤ (5 * S.L : ℕ) ∧
            (t : ZMod P) = ((X μ / ℓ - Z μ / ℓ : ℤ) : ZMod P) := by
      show (intTorus X : BgT C.geo k) ∈ (genSF (M1 := C.geo.M1) (N₁ := C.geo.c * n k)
        (L := S.L) (c := C.geo.c) (n := n k) (le_refl k) (W2 R Y)).Ω j ↔
        ∃ Z : Fin S.d → ℤ, (intTorus Z : BgT C.geo k) ∈ (genSF (M1 := C.geo.M1)
          (N₁ := C.geo.c * n k) (L := S.L) (c := C.geo.c) (n := n k) (le_refl k)
          (W2 R Y)).Ω (j + 1) ∧ _
      unfold genSF
      rw [minimalGenSet_Ω, minLayer_of_lt _ hjk, mem_nearStep]
      constructor
      · rintro ⟨y, hy, hd⟩
        refine ⟨fun μ => ((y μ).val : ℤ), ?_, ?_⟩
        · have e : (intTorus (fun μ => ((y μ).val : ℤ)) : BgT C.geo k) = y := by
            funext μ; simp [intTorus_apply]
          rw [minimalGenSet_Ω, e]; exact hy
        · have e : (intTorus (fun μ => ((y μ).val : ℤ)) : BgT C.geo k) = y := by
            funext μ; simp [intTorus_apply]
          rw [← e, hfc, hfc, supDist_intTorus_le_iff] at hd
          exact hd
      · rintro ⟨Z, hZ, hd⟩
        refine ⟨intTorus Z, by rw [minimalGenSet_Ω] at hZ; exact hZ, ?_⟩
        rw [hfc, hfc, supDist_intTorus_le_iff]
        exact hd
    rw [hmem, C.omRad_of_lt hjk]
    have hdA : ∀ q : ℤ, (ℓ : ℤ) ∣ (C.tSide : ℤ) * q - C.omRad (j + 1) := fun q =>
      dvd_sub (dvd_mul_of_dvd_left (by exact_mod_cast C.cell_dvd_tSide hjk.le) _)
        (by exact_mod_cast C.cell_dvd_omRad j)
    have hdB : ∀ q : ℤ, (ℓ : ℤ) ∣ (C.tSide : ℤ) * q + C.tSide + C.omRad (j + 1) := fun q =>
      dvd_add (dvd_add (dvd_mul_of_dvd_left (by exact_mod_cast C.cell_dvd_tSide hjk.le) _)
        (by exact_mod_cast C.cell_dvd_tSide hjk.le)) (by exact_mod_cast C.cell_dvd_omRad j)
    have hAB : ∀ q : ℤ, (C.tSide : ℤ) * q - C.omRad (j + 1) <
        (C.tSide : ℤ) * q + C.tSide + C.omRad (j + 1) := fun q => by
      have : (0 : ℤ) ≤ C.omRad (j + 1) := Nat.cast_nonneg _
      linarith
    have h5 : ((5 * S.L : ℕ) : ℤ) * ℓ = ((5 * C.geo.M1 * S.L ^ (j + 1) : ℕ) : ℤ) := by
      rw [hℓ]; push_cast; ring
    constructor
    · rintro ⟨Z, hZ, hd⟩
      obtain ⟨q, hq, hZq⟩ := (hj1 Z).1 hZ
      choose t ht htP using hd
      have hp : ∀ μ, ∃ p : ℤ, X μ / ℓ - Z μ / ℓ - t μ = P * p := fun μ => by
        have := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 (htP μ)
        obtain ⟨p, hp⟩ := this
        exact ⟨p, by rw [← hp]⟩
      choose p hp using hp
      refine ⟨fun μ => q μ + n k * p μ, ?_, fun μ => ?_⟩
      · have e : (intTorus (fun μ => q μ + n k * p μ) : Torus S.d (n k)) = intTorus q := by
          funext μ; simp [intTorus_apply]
        rw [e]; exact hq
      · have hshift : (Z μ + ℓ * (P * p μ)) / ℓ = Z μ / ℓ + P * p μ :=
          Int.add_mul_ediv_left _ _ hℓpos.ne'
        have key := (ZBox.exists_ediv_near_iff (x := X μ) (m := ((5 * S.L : ℕ) : ℤ)) hℓpos
          (by positivity) (hdA (q μ + n k * p μ)) (hdB (q μ + n k * p μ))
          (hAB (q μ + n k * p μ))).1 ⟨Z μ + ℓ * (P * p μ), ?_, ?_, ?_⟩
        · rw [h5] at key
          push_cast at key ⊢
          constructor <;> linarith [key.1, key.2]
        · have := (hZq μ).1
          have e : (C.tSide : ℤ) * (q μ + n k * p μ) = C.tSide * q μ + ℓ * (P * p μ) := by
            linear_combination (-(p μ)) * hPℓ
          rw [e]; linarith
        · have := (hZq μ).2
          have e : (C.tSide : ℤ) * (q μ + n k * p μ) = C.tSide * q μ + ℓ * (P * p μ) := by
            linear_combination (-(p μ)) * hPℓ
          rw [e]; linarith
        · rw [hshift]
          have : X μ / ℓ - (Z μ / ℓ + P * p μ) = t μ := by linarith [hp μ]
          rw [this]; exact ht μ
    · rintro ⟨q, hq, hXq⟩
      have hy : ∀ μ, ∃ y, (C.tSide : ℤ) * q μ - C.omRad (j + 1) ≤ y ∧
          y < (C.tSide : ℤ) * q μ + C.tSide + C.omRad (j + 1) ∧
          |X μ / ℓ - y / ℓ| ≤ ((5 * S.L : ℕ) : ℤ) := fun μ => by
        refine (ZBox.exists_ediv_near_iff hℓpos (by positivity) (hdA (q μ)) (hdB (q μ))
          (hAB (q μ))).2 ?_
        rw [h5]
        push_cast at hXq ⊢
        constructor <;> linarith [(hXq μ).1, (hXq μ).2]
      choose y hy1 hy2 hy3 using hy
      refine ⟨y, (hj1 y).2 ⟨q, hq, fun μ => ⟨hy1 μ, hy2 μ⟩⟩, fun μ =>
        ⟨X μ / ℓ - y μ / ℓ, hy3 μ, rfl⟩⟩

end SFCtx

end Balaban.LargeField.Def7
