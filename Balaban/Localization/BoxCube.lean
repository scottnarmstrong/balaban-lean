/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledAlg
public import Balaban.Localization.NC3Small

/-!
# The interaction cube as a coordinate cube of the NC3 setting

`box_eq_cubeSet`: for a centre `z = (j, y₀)` the interaction cube `□_z` (periodic box of
half-width `5/2 M₁ ℓ_j`) is the coordinate cube `{c + t : t < 5 L^(j+m₁)}^d` of the reflection
setting, with corner `c = y₀ + N - 2 L^(j+m₁)` (`N` the side of the torus), and
`aligned_cube`: it is an `AlignedCube` of scale `j` in the sense of `CubeRegimes`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.Reflection Finset Matrix

/-- One coordinate: the real description of the box and the coordinate interval agree. -/
theorem inBox_coord_iff_inCube1 {N B : ℕ} [NeZero N] (hB : 0 < B) (hBN : 2 * B ≤ N)
    (y0 x : ZMod N) :
    (∃ p : ℤ, |((x.val : ℕ) : ℝ) + p * (N : ℝ) - (((y0.val : ℕ) : ℝ) + ((B : ℝ) - 1) / 2)| <
      5 / 2 * (B : ℝ)) ↔ InCube1 N (5 * B) (y0.val + (N - 2 * B)) x := by
  unfold InCube1
  have hB1 : (1 : ℝ) ≤ B := by exact_mod_cast hB
  constructor
  · rintro ⟨p, hp⟩
    rw [abs_lt] at hp
    obtain ⟨hp1, hp2⟩ := hp
    set T : ℤ := (x.val : ℤ) + p * N - y0.val + 2 * B with hT
    have hTr : (T : ℝ) = (x.val : ℝ) + p * N - y0.val + 2 * B := by
      rw [hT]; push_cast; ring
    have h1 : 0 ≤ T := by
      by_contra hneg
      have : T ≤ -1 := by omega
      have : (T : ℝ) ≤ -1 := by exact_mod_cast this
      linarith
    have h2 : T ≤ 5 * (B : ℤ) - 1 := by
      by_contra hneg
      have : 5 * (B : ℤ) ≤ T := by omega
      have : ((5 * B : ℤ) : ℝ) ≤ T := by exact_mod_cast this
      push_cast at this
      linarith
    refine ⟨T.toNat, by omega, ?_⟩
    have hx : (x : ZMod N) = ((x.val : ℕ) : ZMod N) := (ZMod.natCast_zmod_val x).symm
    rw [hx]
    have key : (((x.val : ℕ) : ℤ) : ZMod N) = ((((y0.val + (N - 2 * B) + T.toNat : ℕ)) : ℤ) : ZMod N) := by
      rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
      refine ⟨p + 1, ?_⟩
      have hTn : (T.toNat : ℤ) = T := Int.toNat_of_nonneg h1
      push_cast [Nat.cast_sub hBN, hTn]
      rw [hT]; ring
    exact_mod_cast key
  · rintro ⟨t, ht, hx⟩
    have hv : x.val = (y0.val + (N - 2 * B) + t) % N := by
      rw [hx, ZMod.val_natCast]
    set r : ℕ := (y0.val + (N - 2 * B) + t) / N with hr
    have hdm := Nat.div_add_mod (y0.val + (N - 2 * B) + t) N
    rw [← hr, ← hv] at hdm
    refine ⟨(r : ℤ) - 1, ?_⟩
    have hNr : (N : ℝ) * r + x.val = (y0.val : ℝ) + ((N : ℝ) - 2 * B) + t := by
      have := congrArg (fun z : ℕ => (z : ℝ)) hdm
      push_cast [Nat.cast_sub hBN] at this
      linarith
    have htr : (t : ℝ) ≤ 5 * B - 1 := by
      have : t + 1 ≤ 5 * B := ht
      have : ((t + 1 : ℕ) : ℝ) ≤ ((5 * B : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg _
    have e : ((x.val : ℕ) : ℝ) + ((r : ℤ) - 1 : ℤ) * (N : ℝ) - (((y0.val : ℕ) : ℝ) +
        ((B : ℝ) - 1) / 2) = (t : ℝ) - 2 * B - ((B : ℝ) - 1) / 2 := by
      push_cast; linarith
    rw [e, abs_lt]
    constructor <;> linarith

section Centre

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- The corner of the coordinate cube `□_z`: `c = y₀ + (N - 2 M₁ ℓ_j)`. -/
def boxCorner (q : ℕ × CTorus d L N₁ m₁ K) : Fin d → ℕ :=
  fun i => (q.2 i).val + (((N₁ * L ^ m₁) * L ^ K) - 2 * L ^ (q.1 + m₁))

omit [NeZero N₁] in
theorem torusSide_ge (hN : 5 < N₁) {j : ℕ} (hj : j ≤ K) :
    6 * L ^ (j + m₁) ≤ (N₁ * L ^ m₁) * L ^ K := by
  have h1 : L ^ (j + m₁) ≤ L ^ m₁ * L ^ K := by
    rw [← pow_add]
    exact Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (by omega)
  calc 6 * L ^ (j + m₁) ≤ N₁ * (L ^ m₁ * L ^ K) :=
        (Nat.mul_le_mul (by omega) h1)
    _ = _ := by ring

theorem box_eq_cubeSet (hN : 5 < N₁) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    intBox q = cubeSet ((N₁ * L ^ m₁) * L ^ K) (5 * L ^ (q.1 + m₁)) (boxCorner q) := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hBpos : 0 < L ^ (q.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
  have h6 := torusSide_ge (L := L) (m₁ := m₁) hN hmK
  ext x
  rw [mem_intBox, mem_cubeSet]
  unfold InBox
  refine forall_congr' fun i => ?_
  have := inBox_coord_iff_inCube1 (N := (N₁ * L ^ m₁) * L ^ K) hBpos (by omega) (q.2 i) (x i)
  have e : ((L : ℝ) ^ (q.1 + m₁)) = ((L ^ (q.1 + m₁) : ℕ) : ℝ) := by push_cast; rfl
  rw [e]
  exact this

theorem boxCorner_dvd {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) (i : Fin d) :
    L ^ (q.1 + m₁) ∣ boxCorner q i := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  unfold boxCorner
  refine dvd_add (Nat.dvd_of_mod_eq_zero (hb i)) (Nat.dvd_sub ?_ ?_)
  · exact pow_dvd_torusSide (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) q.1 hmK
  · exact dvd_mul_left _ _

theorem chartPt_boxCorner (hN : 5 < N₁) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    chartPt ((N₁ * L ^ m₁) * L ^ K) (boxCorner q) (fun _ => 2 * L ^ (q.1 + m₁)) = q.2 := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have h6 := torusSide_ge (L := L) (m₁ := m₁) hN hmK
  funext i
  unfold chartPt boxCorner
  have : (q.2 i).val + (((N₁ * L ^ m₁) * L ^ K) - 2 * L ^ (q.1 + m₁)) + 2 * L ^ (q.1 + m₁) =
      (q.2 i).val + ((N₁ * L ^ m₁) * L ^ K) := by omega
  rw [this, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]

/-- **The interaction cube is an aligned cube of scale `j`** in the sense of `CubeRegimes`
(`q' = min K (j + 1)`, side `5 L^(j+m₁) = s L^q'`). -/
theorem alignedCube_box {a : ℕ → ℝ} {ν : ℝ} (S : DGSetting G a ν) {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    AlignedCube G m₁ q.1 (min K (q.1 + 1)) (5 * L ^ (q.1 + m₁ - min K (q.1 + 1)))
      (boxCorner q) := by
  obtain ⟨⟨hm1, hmK⟩, hl, hb⟩ := (mem_cubeIdx G).1 hq
  have hm₁ := S.aligned.two_le
  have h6 := torusSide_ge (L := L) (m₁ := m₁) S.big hmK
  refine ⟨hm1, hmK, by omega, rfl, ?_, boxCorner_dvd hq, ?_, ?_, S.cover_sep⟩
  · rw [mul_assoc, ← pow_add]
    rw [Nat.sub_add_cancel (le_trans (min_le_right _ _) (by omega))]
  · have hBpos : 0 < L ^ (q.1 + m₁) := pow_pos (Nat.pos_of_ne_zero (NeZero.ne L)) _
    exact Nat.lt_of_lt_of_le (by omega : 5 * L ^ (q.1 + m₁) < 6 * L ^ (q.1 + m₁)) h6
  · rw [chartPt_boxCorner S.big hq]; exact hl

end Centre

end Balaban.Localization
