module

public import Balaban.LargeField.Geometry.Continuous
import Mathlib.Tactic.Linarith

/-!
# Balaban's distances as index distances (Part I, Lemma I.2.2)

In scale-`k` cube units (cubes of side `1`), the sup-distance of the closed cubes `□_x`, `□_y` is
`cubeDist x y = max {d(x, y) - 1, 0}` (`cubeDist_eq`), hence for real `r ≥ 0`:
`cubeDist x y > r ↔ d(x, y) ≥ ⌊r⌋ + 2` and `cubeDist x y ≤ r ↔ d(x, y) ≤ ⌊r⌋ + 1`
(`cubeDist_gt_iff`, `cubeDist_le_iff`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ} [NeZero n]

/-- `dist_∞(□_x, □_y)`, the infimum of `‖q - q'‖` over the two closed cubes. -/
noncomputable def cubeDist (x y : Torus d n) : ℝ :=
  sInf {r | ∃ q ∈ cube x, ∃ q' ∈ cube y, r = ‖q - q'‖}

theorem le_norm_of_mem_cube {x y : Torus d n} {q q' : CTorus d n} (hq : q ∈ cube x)
    (hq' : q' ∈ cube y) : max ((supDist x y : ℝ) - 1) 0 ≤ ‖q - q'‖ := by
  refine max_le ?_ (norm_nonneg _)
  have hi : ∀ i, (cycNorm n (x i - y i) : ℝ) ≤ ‖q - q'‖ + 1 := by
    intro i
    obtain ⟨t, ht, hqi⟩ := hq i
    obtain ⟨t', ht', hqi'⟩ := hq' i
    have e : zc (x i - y i) = (q - q') i - (((t - t' : ℝ)) : AddCircle (n : ℝ)) := by
      simp only [Pi.sub_apply]
      rw [hqi, hqi', zc_sub, AddCircle.coe_sub]; abel
    have h1 : ‖(((t - t' : ℝ)) : AddCircle (n : ℝ))‖ ≤ 1 := by
      rw [norm_coe_le_iff]
      exact ⟨0, by simp only [Int.cast_zero, zero_mul, sub_zero]; rw [abs_le]; constructor <;>
        linarith [ht.1, ht.2, ht'.1, ht'.2]⟩
    have h2 : ‖(q - q') i‖ ≤ ‖q - q'‖ := norm_le_pi_norm _ i
    rw [← norm_zc, e]
    calc ‖(q - q') i - (((t - t' : ℝ)) : AddCircle (n : ℝ))‖
        ≤ ‖(q - q') i‖ + ‖(((t - t' : ℝ)) : AddCircle (n : ℝ))‖ := norm_sub_le _ _
      _ ≤ ‖q - q'‖ + 1 := by linarith
  have : supDist x y ≤ ⌊‖q - q'‖ + 1⌋₊ := supDist_le_iff.mpr fun i => by
    exact Nat.le_floor (hi i)
  have h3 : (supDist x y : ℝ) ≤ ‖q - q'‖ + 1 :=
    (Nat.cast_le.mpr this).trans (Nat.floor_le (by positivity))
  linarith

theorem exists_tt (u D : ℝ) (hD : |u| ≤ D) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ t' ∈ Set.Icc (0 : ℝ) 1, |u + (t - t')| ≤ max (D - 1) 0 := by
  have hb := abs_le.mp hD
  have m1 := le_max_left (D - 1) 0
  have m2 := le_max_right (D - 1) 0
  rcases le_total 1 u with h | h
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, 1, ⟨zero_le_one, le_rfl⟩, by
      rw [abs_le]; constructor <;> linarith⟩
  rcases le_total 0 u with h0 | h0
  · exact ⟨0, ⟨le_rfl, zero_le_one⟩, u, ⟨h0, h⟩, by
      rw [abs_le]; constructor <;> linarith⟩
  rcases le_total (-1) u with h1 | h1
  · exact ⟨-u, ⟨by linarith, by linarith⟩, 0, ⟨le_rfl, zero_le_one⟩, by
      rw [abs_le]; constructor <;> linarith⟩
  · exact ⟨1, ⟨zero_le_one, le_rfl⟩, 0, ⟨le_rfl, zero_le_one⟩, by
      rw [abs_le]; constructor <;> linarith⟩

theorem exists_mem_cube_norm_le (x y : Torus d n) :
    ∃ q ∈ cube x, ∃ q' ∈ cube y, ‖q - q'‖ ≤ max ((supDist x y : ℝ) - 1) 0 := by
  have hi : ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1, ∃ t' ∈ Set.Icc (0 : ℝ) 1,
      ‖(zc (x i) + ((t : ℝ) : AddCircle (n : ℝ))) - (zc (y i) + ((t' : ℝ) : AddCircle (n : ℝ)))‖ ≤
        max ((supDist x y : ℝ) - 1) 0 := by
    intro i
    obtain ⟨u, hu, hue⟩ := (cycNorm_le_iff (n := n) (x i - y i) _).mp le_rfl
    have hD : |(u : ℝ)| ≤ supDist x y := by
      have h3 : |u| ≤ (supDist x y : ℤ) := hu.trans (by exact_mod_cast cycNorm_le_supDist x y i)
      exact_mod_cast h3
    have h1 : zc (x i - y i) = ((u : ℝ) : AddCircle (n : ℝ)) := by rw [← hue, zc_intCast]
    rw [zc_sub] at h1
    obtain ⟨t, ht, t', ht', hle⟩ := exists_tt u _ hD
    refine ⟨t, ht, t', ht', ?_⟩
    have key : (zc (x i) + ((t : ℝ) : AddCircle (n : ℝ))) -
        (zc (y i) + ((t' : ℝ) : AddCircle (n : ℝ))) = (((u : ℝ) + (t - t') : ℝ) : AddCircle (n : ℝ)) := by
      rw [AddCircle.coe_add, AddCircle.coe_sub, ← h1]; abel
    rw [key, norm_coe_le_iff]
    exact ⟨0, by simpa using hle⟩
  choose t ht t' ht' hn using hi
  refine ⟨fun i => zc (x i) + ((t i : ℝ) : AddCircle (n : ℝ)), fun i => ⟨t i, ht i, rfl⟩,
    fun i => zc (y i) + ((t' i : ℝ) : AddCircle (n : ℝ)), fun i => ⟨t' i, ht' i, rfl⟩, ?_⟩
  rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
  exact hn

/-- **Lemma I.2.2**: the sup-distance of the closed cubes is `max {d(x, y) - 1, 0}`
(in units where the cubes have side `1`). -/
theorem cubeDist_eq (x y : Torus d n) : cubeDist x y = max ((supDist x y : ℝ) - 1) 0 := by
  obtain ⟨q, hq, q', hq', hle⟩ := exists_mem_cube_norm_le x y
  apply le_antisymm
  · have hbdd : BddBelow {r : ℝ | ∃ q ∈ cube x, ∃ q' ∈ cube y, r = ‖q - q'‖} :=
      ⟨0, by rintro _ ⟨_, _, _, _, rfl⟩; exact norm_nonneg _⟩
    exact (csInf_le hbdd ⟨q, hq, q', hq', rfl⟩).trans hle
  · refine le_csInf ⟨‖q - q'‖, q, hq, q', hq', rfl⟩ ?_
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact le_norm_of_mem_cube ha hb

/-- **Lemma I.2.2**: for real `r ≥ 0`, `dist_∞(□_x, □_y) > r ↔ d(x, y) ≥ ⌊r⌋ + 2`. -/
theorem cubeDist_gt_iff (x y : Torus d n) {r : ℝ} (hr : 0 ≤ r) :
    r < cubeDist x y ↔ ⌊r⌋₊ + 2 ≤ supDist x y := by
  rw [cubeDist_eq]
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  constructor
  · intro h
    have h' : r < (supDist x y : ℝ) - 1 := by
      rcases lt_max_iff.mp h with h | h
      · exact h
      · linarith
    have : (⌊r⌋₊ : ℝ) + 1 < supDist x y := by linarith
    have : ⌊r⌋₊ + 1 < supDist x y := by exact_mod_cast this
    omega
  · intro h
    have : (⌊r⌋₊ : ℝ) + 2 ≤ supDist x y := by exact_mod_cast h
    exact lt_max_of_lt_left (by linarith)

/-- **Lemma I.2.2**: for real `r ≥ 0`, `dist_∞(□_x, □_y) ≤ r ↔ d(x, y) ≤ ⌊r⌋ + 1`. -/
theorem cubeDist_le_iff (x y : Torus d n) {r : ℝ} (hr : 0 ≤ r) :
    cubeDist x y ≤ r ↔ supDist x y ≤ ⌊r⌋₊ + 1 := by
  rw [← not_lt, cubeDist_gt_iff x y hr]; omega

end Balaban.LargeField
