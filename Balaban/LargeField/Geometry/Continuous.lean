module

public import Balaban.LargeField.Geometry.Distance
public import Balaban.LargeField.Geometry.Coarsen
public import Mathlib.Topology.Instances.AddCircle.Real
public import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The continuous torus, cubes and `N_r` (Part I, Definition I.2.7)

`CTorus d n = (ℝ/nℤ)^d` (scale-`k` cube units, `n = n_k`) with the cyclic sup-distance
`‖p - q‖` (the sup norm on `Fin d → AddCircle n`). The cube of `x ∈ 𝕋_k` is
`cube x = x + [0,1]^d`, with centre `cubeCentre x = x + ½·1`.

For `Γ ⊂ 𝕋^c_k` and real `r ≥ 0`, `NR r Γ = N_r(Γ) = {x : dist_∞(Γ, □_x) ≤ r}`; the infimum
`dist_∞(Γ, □_x) = inf ‖γ - q‖` is encoded as `∀ ε > 0, ∃ γ ∈ Γ, ∃ q ∈ □_x, ‖γ - q‖ < r + ε`
(this is `inf ≤ r` on the nose, for every `Γ`, including the empty set).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

/-- The continuous torus `(ℝ/nℤ)^d`. -/
abbrev CTorus (d n : ℕ) : Type := Fin d → AddCircle (n : ℝ)

section Circle

variable {n : ℕ} [NeZero n]

private theorem npos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

/-- The point of `ℝ/nℤ` at the integer `a.val`. -/
noncomputable def zc (a : ZMod n) : AddCircle (n : ℝ) := ((a.val : ℝ) : AddCircle (n : ℝ))

omit [NeZero n] in
/-- Shifting a representative by a multiple of the period does not change the class. -/
theorem coe_add_int_mul (x : ℝ) (k : ℤ) : ((x + k * n : ℝ) : AddCircle (n : ℝ)) = (x : AddCircle (n : ℝ)) := by
  have h : (((k * n : ℝ)) : AddCircle (n : ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, h, add_zero]

theorem zc_intCast (z : ℤ) : zc (z : ZMod n) = ((z : ℝ) : AddCircle (n : ℝ)) := by
  unfold zc
  have hv := ZMod.val_intCast (n := n) z
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h1 : (((z : ZMod n).val : ℤ) : ℝ) = z + ((-(z / n) : ℤ) : ℝ) * n := by
    have : ((z : ZMod n).val : ℤ) = z + (-(z / n)) * n := by
      rw [hv]; have := Int.mul_ediv_add_emod z n; linarith
    exact_mod_cast this
  have h2 : (((z : ZMod n).val : ℝ)) = z + ((-(z / n) : ℤ) : ℝ) * n := by
    rw [← h1]; simp
  rw [h2, coe_add_int_mul]

theorem zc_natCast (j : ℕ) : zc (j : ZMod n) = ((j : ℝ) : AddCircle (n : ℝ)) := by
  simpa using zc_intCast (n := n) (j : ℤ)

theorem zc_add (a b : ZMod n) : zc (a + b) = zc a + zc b := by
  have ha : (a : ZMod n) = ((a.val : ℤ) : ZMod n) := by simp
  have hb : (b : ZMod n) = ((b.val : ℤ) : ZMod n) := by simp
  rw [ha, hb, ← Int.cast_add, zc_intCast, zc_intCast, zc_intCast]
  push_cast
  rw [AddCircle.coe_add]

theorem zc_sub (a b : ZMod n) : zc (a - b) = zc a - zc b := by
  have := zc_add (a - b) b
  rw [sub_add_cancel] at this
  rw [this]; abel

/-- The norm on `ℝ/nℤ`: `‖x‖ ≤ r` iff some translate of `x` by a multiple of `n` has
absolute value `≤ r`. -/
theorem norm_coe_le_iff (x r : ℝ) :
    ‖(x : AddCircle (n : ℝ))‖ ≤ r ↔ ∃ k : ℤ, |x - k * n| ≤ r := by
  rw [AddCircle.norm_eq]
  constructor
  · intro h
    exact ⟨round ((n : ℝ)⁻¹ * x), by simpa using h⟩
  · rintro ⟨k, hk⟩
    refine le_trans ?_ hk
    have h := round_le ((n : ℝ)⁻¹ * x) k
    have hn0 : (n : ℝ) ≠ 0 := npos.ne'
    have e1 : x - (round ((n : ℝ)⁻¹ * x) : ℝ) * n = n * ((n : ℝ)⁻¹ * x - round ((n : ℝ)⁻¹ * x)) := by
      field_simp
    have e2 : x - (k : ℝ) * n = n * ((n : ℝ)⁻¹ * x - k) := by
      field_simp
    rw [e1, e2, abs_mul, abs_mul, abs_of_pos npos]
    exact mul_le_mul_of_nonneg_left h npos.le

/-- `‖zc a‖ = |a|_n`. -/
theorem norm_zc (a : ZMod n) : ‖zc a‖ = cycNorm n a := by
  apply le_antisymm
  · obtain ⟨t, ht, rfl⟩ := (cycNorm_le_iff (n := n) a (cycNorm n a)).mp le_rfl
    rw [zc_intCast, norm_coe_le_iff]
    exact ⟨0, by simpa using (by exact_mod_cast ht : |(t : ℝ)| ≤ _)⟩
  · obtain ⟨k, hk⟩ := (norm_coe_le_iff (a.val : ℝ) ‖zc a‖).mp le_rfl
    have hz : ((((a.val : ℤ) - k * n : ℤ)) : ZMod n) = a := by simp
    set u : ℤ := (a.val : ℤ) - k * n with hu
    have h1 : |u| ≤ (u.natAbs : ℤ) := by rw [Int.abs_eq_natAbs]
    have h2 := (cycNorm_le_iff a u.natAbs).mpr ⟨u, h1, hz⟩
    have h3 : ((u.natAbs : ℕ) : ℝ) = |(u : ℝ)| := by
      rw [← Int.cast_abs, Int.abs_eq_natAbs]; simp
    have h4 : |(u : ℝ)| ≤ ‖zc a‖ := by simpa [hu] using hk
    calc (cycNorm n a : ℝ) ≤ (u.natAbs : ℝ) := by exact_mod_cast h2
      _ ≤ ‖zc a‖ := h3 ▸ h4

/-- Distance of `w` to `[0,1]` is at most `max (max (w - 1) (-w)) 0`, attained by clamping. -/
theorem exists_clamp (w : ℝ) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, |w - t| ≤ max (max (w - 1) (-w)) 0 := by
  rcases le_total w 0 with h | h
  · refine ⟨0, ⟨le_rfl, zero_le_one⟩, ?_⟩
    rw [sub_zero, abs_of_nonpos h]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  rcases le_total w 1 with h1 | h1
  · exact ⟨w, ⟨h, h1⟩, by simp⟩
  · refine ⟨1, ⟨zero_le_one, le_rfl⟩, ?_⟩
    rw [abs_of_nonneg (by linarith)]
    exact le_trans (le_max_left _ _) (le_max_left _ _)

end Circle

section Cubes

variable {d n : ℕ} [NeZero n]

/-- The closed cube `□_x = x + [0,1]^d` of `x ∈ 𝕋_k` in the continuous torus. -/
def cube (x : Torus d n) : Set (CTorus d n) :=
  {q | ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1, q i = zc (x i) + ((t : ℝ) : AddCircle (n : ℝ))}

/-- The centre `c(x) = x + ½·𝟙` of the cube `□_x`. -/
noncomputable def cubeCentre (x : Torus d n) : CTorus d n :=
  fun i => zc (x i) + (((1 / 2 : ℝ)) : AddCircle (n : ℝ))

/-- `N_r(Γ) = {x ∈ 𝕋_k : dist_∞(Γ, □_x) ≤ r}`, the infimum written as
`∀ ε > 0, ∃ γ ∈ Γ, ∃ q ∈ □_x, ‖γ - q‖ < r + ε`. -/
def NR (r : ℝ) (Γ : Set (CTorus d n)) : Set (Torus d n) :=
  {x | ∀ ε : ℝ, 0 < ε → ∃ γ ∈ Γ, ∃ q ∈ cube x, ‖γ - q‖ < r + ε}

omit [NeZero n] in
theorem NR_of_exists {r : ℝ} {Γ : Set (CTorus d n)} {x : Torus d n}
    (h : ∃ γ ∈ Γ, ∃ q ∈ cube x, ‖γ - q‖ ≤ r) : x ∈ NR r Γ := by
  obtain ⟨γ, hγ, q, hq, h⟩ := h
  exact fun ε hε => ⟨γ, hγ, q, hq, by linarith⟩

omit [NeZero n] in
theorem NR_mono {r r' : ℝ} (h : r ≤ r') {Γ Γ' : Set (CTorus d n)} (hΓ : Γ ⊆ Γ') :
    NR r Γ ⊆ NR r' Γ' := by
  intro x hx ε hε
  obtain ⟨γ, hγ, q, hq, h1⟩ := hx ε hε
  exact ⟨γ, hΓ hγ, q, hq, by linarith⟩

/-- Translating a point of `□_x` by `y - x` gives a point of `□_y` at distance `d(x, y)`. -/
theorem exists_shift (x y : Torus d n) {q : CTorus d n} (hq : q ∈ cube x) :
    ∃ q' ∈ cube y, ‖q - q'‖ ≤ supDist x y := by
  refine ⟨fun i => q i + zc (y i - x i), ?_, ?_⟩
  · intro i
    obtain ⟨t, ht, hqi⟩ := hq i
    exact ⟨t, ht, by dsimp only; rw [hqi, zc_sub]; abel⟩
  · rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    have : q i - (q i + zc (y i - x i)) = -zc (y i - x i) := by abel
    simp only [Pi.sub_apply]
    rw [this, norm_neg, norm_zc]
    have h1 := cycNorm_le_supDist y x i
    rw [supDist_comm y x] at h1
    exact_mod_cast h1

/-- **Lemma I.2.8 (a)**: `dist_∞(Γ, □_y) ≤ dist_∞(Γ, □_x) + d(x, y)`. -/
theorem NR_shift {r : ℝ} {Γ : Set (CTorus d n)} {x : Torus d n} (hx : x ∈ NR r Γ)
    (y : Torus d n) : y ∈ NR (r + supDist x y) Γ := by
  intro ε hε
  obtain ⟨γ, hγ, q, hq, h1⟩ := hx ε hε
  obtain ⟨q', hq', h2⟩ := exists_shift x y hq
  refine ⟨γ, hγ, q', hq', ?_⟩
  calc ‖γ - q'‖ = ‖(γ - q) + (q - q')‖ := by congr 1; abel
    _ ≤ ‖γ - q‖ + ‖q - q'‖ := norm_add_le _ _
    _ < r + supDist x y + ε := by linarith

/-- **Lemma I.2.8 (a)**: `N_r(Γ)^{∼m} ⊆ N_{r+m}(Γ)`. -/
theorem nbhd_NR_subset (m : ℕ) (r : ℝ) (Γ : Set (CTorus d n)) :
    nbhd m (NR r Γ) ⊆ NR (r + m) Γ := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_nbhd.mp hy
  have h1 := NR_shift hx y
  have h2 : (supDist x y : ℝ) ≤ m := by
    rw [supDist_comm] at hxy; exact_mod_cast hxy
  exact NR_mono (by linarith) subset_rfl h1

/-- **Lemma I.2.8 (a)**: `dist_∞(c(x), □_y) ≤ max {d(x, y) - ½, 0}`. -/
theorem mem_NR_cubeCentre (x y : Torus d n) :
    y ∈ NR (max ((supDist x y : ℝ) - 1 / 2) 0) {cubeCentre x} := by
  apply NR_of_exists
  have hi : ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ‖cubeCentre x i - (zc (y i) + ((t : ℝ) : AddCircle (n : ℝ)))‖ ≤
        max ((supDist x y : ℝ) - 1 / 2) 0 := by
    intro i
    obtain ⟨u, hu, hue⟩ := (cycNorm_le_iff (n := n) (x i - y i) _).mp le_rfl
    obtain ⟨t, ht, hw⟩ := exists_clamp ((u : ℝ) + 1 / 2)
    refine ⟨t, ht, ?_⟩
    have e : cubeCentre x i - (zc (y i) + ((t : ℝ) : AddCircle (n : ℝ))) =
        (((u : ℝ) + 1 / 2 - t : ℝ) : AddCircle (n : ℝ)) := by
      have h1 : zc (x i - y i) = ((u : ℝ) : AddCircle (n : ℝ)) := by rw [← hue, zc_intCast]
      rw [zc_sub] at h1
      unfold cubeCentre
      have : ((u : ℝ) + 1 / 2 - t : ℝ) = (u : ℝ) + 1 / 2 - t := rfl
      rw [AddCircle.coe_sub, AddCircle.coe_add, ← h1]; abel
    rw [e]
    refine (norm_coe_le_iff _ _).mpr ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, sub_zero]
    refine le_trans hw ?_
    have h2 : |(u : ℝ)| ≤ supDist x y := by
      have := cycNorm_le_supDist x y i
      have h3 : |u| ≤ (cycNorm n (x i - y i) : ℤ) := hu
      have : |u| ≤ (supDist x y : ℤ) := h3.trans (by exact_mod_cast this)
      exact_mod_cast this
    have h4 := abs_le.mp h2
    refine max_le (max_le ?_ ?_) (le_max_right _ _) <;> refine le_trans ?_ (le_max_left _ _) <;> linarith
  choose t ht hn using hi
  refine ⟨cubeCentre x, rfl, fun i => zc (y i) + ((t i : ℝ) : AddCircle (n : ℝ)),
    fun i => ⟨t i, ht i, rfl⟩, ?_⟩
  rw [pi_norm_le_iff_of_nonneg (le_max_right _ _)]
  exact hn

/-- A box `∏_i {a_i, …, a_i + s_i - 1}` of cyclic intervals. -/
def box (a : Torus d n) (s : Fin d → ℕ) : Set (Torus d n) :=
  {x | ∀ i, ∃ j : ℕ, j < s i ∧ x i = a i + (j : ZMod n)}

/-- The centre `c(B) = (a_i + s_i/2)_i` of the box `box a s`. -/
noncomputable def boxCentre (a : Torus d n) (s : Fin d → ℕ) : CTorus d n :=
  fun i => zc (a i) + (((s i : ℝ) / 2 : ℝ) : AddCircle (n : ℝ))

/-- **Lemma I.2.8 (d)**: a box of side `≤ 2ρ + 10` lies in `N_{ρ+4}` of its centre. -/
theorem box_subset_NR {ρ : ℕ} (a : Torus d n) (s : Fin d → ℕ) (hs : ∀ i, s i ≤ 2 * ρ + 10) :
    box a s ⊆ NR ((ρ : ℝ) + 4) {boxCentre a s} := by
  intro x hx
  apply NR_of_exists
  have hi : ∀ i, ∃ t ∈ Set.Icc (0 : ℝ) 1,
      ‖boxCentre a s i - (zc (x i) + ((t : ℝ) : AddCircle (n : ℝ)))‖ ≤ (ρ : ℝ) + 4 := by
    intro i
    obtain ⟨j, hj, hxj⟩ := hx i
    obtain ⟨t, ht, hw⟩ := exists_clamp ((s i : ℝ) / 2 - j)
    refine ⟨t, ht, ?_⟩
    have e : boxCentre a s i - (zc (x i) + ((t : ℝ) : AddCircle (n : ℝ))) =
        ((((s i : ℝ) / 2 - j - t : ℝ)) : AddCircle (n : ℝ)) := by
      rw [hxj, zc_add, zc_natCast]
      unfold boxCentre
      rw [AddCircle.coe_sub, AddCircle.coe_sub]
      abel
    rw [e]
    refine (norm_coe_le_iff _ _).mpr ⟨0, ?_⟩
    simp only [Int.cast_zero, zero_mul, sub_zero]
    refine le_trans hw ?_
    have h1 : (j : ℝ) + 1 ≤ s i := by exact_mod_cast hj
    have h2 : (s i : ℝ) ≤ 2 * ρ + 10 := by exact_mod_cast hs i
    have h3 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg ρ
    refine max_le (max_le ?_ ?_) (by linarith) <;> linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  choose t ht hn using hi
  refine ⟨boxCentre a s, rfl, fun i => zc (x i) + ((t i : ℝ) : AddCircle (n : ℝ)),
    fun i => ⟨t i, ht i, rfl⟩, ?_⟩
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  exact hn

/-- **Lemma I.2.8 (c)**: in every coordinate, the cubes of `N_{ρ+4}(p)` have their `i`-th index
in a cyclic interval of at most `2ρ + 10` points. -/
theorem NR_point_coord_interval (ρ : ℕ) (p : CTorus d n) :
    ∃ a : Fin d → ZMod n, ∀ x ∈ NR ((ρ : ℝ) + 4) {p}, ∀ i,
      ∃ j : ℕ, j < 2 * ρ + 10 ∧ x i = a i + (j : ZMod n) := by
  have hrep : ∀ i, ∃ P : ℝ, (P : AddCircle (n : ℝ)) = p i := fun i =>
    QuotientAddGroup.mk_surjective (p i)
  choose P hP using hrep
  refine ⟨fun i => ((⌈P i - ρ - 21 / 4⌉ : ℤ) : ZMod n), fun x hx i => ?_⟩
  obtain ⟨γ, hγ, q, hq, hlt⟩ := hx (1 / 4) (by norm_num)
  rw [Set.mem_singleton_iff] at hγ
  rw [hγ] at hlt
  obtain ⟨t, ht, hqi⟩ := hq i
  have h1 : ‖p i - q i‖ ≤ (ρ : ℝ) + 4 + 1 / 4 := by
    refine le_trans ?_ (hlt.le.trans (by norm_num))
    have := norm_le_pi_norm (p - q) i
    simpa using this
  have e : p i - q i = ((P i - (x i).val - t : ℝ) : AddCircle (n : ℝ)) := by
    rw [hqi, ← hP i]; unfold zc
    rw [AddCircle.coe_sub, AddCircle.coe_sub]; abel
  rw [e] at h1
  obtain ⟨k, hk⟩ := (norm_coe_le_iff _ _).mp h1
  set z : ℤ := (x i).val + k * n with hz
  have hzr : (z : ℝ) = (x i).val + k * n := by simp [hz]
  have hk' := abs_le.mp hk
  have ht0 := ht.1
  have ht1 := ht.2
  set a0 : ℤ := ⌈P i - ρ - 21 / 4⌉ with ha0
  have hlo : (a0 : ℝ) ≥ P i - ρ - 21 / 4 := Int.le_ceil _
  have hhi : (a0 : ℝ) < P i - ρ - 21 / 4 + 1 := Int.ceil_lt_add_one _
  have hza : a0 ≤ z := by
    rw [ha0]
    apply Int.ceil_le.mpr
    rw [hzr]; linarith [hk'.1, hk'.2]
  have hzb : z - a0 ≤ 2 * ρ + 9 := by
    have : (z : ℝ) - a0 < 2 * ρ + 10 := by rw [hzr]; linarith [hk'.1, hk'.2]
    have : z - a0 < 2 * (ρ : ℤ) + 10 := by exact_mod_cast this
    omega
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ℤ) = z - a0 := ⟨(z - a0).toNat, by omega⟩
  refine ⟨j, by omega, ?_⟩
  have : (x i) = ((z : ℤ) : ZMod n) := by simp [hz]
  rw [this]
  have : z = a0 + j := by omega
  rw [this]; push_cast; rfl

section Scale

variable {m : ℕ} [NeZero m]

/-- The map `p ↦ p / L` from `𝕋^c_k` to `𝕋^c_{k+1}` (coordinatewise `ℝ/nℤ → ℝ/mℤ`, `n = L m`),
written as the canonical identification `ℝ/nℤ ≃ ℝ/mℤ`, `x ↦ x · m / n`. -/
noncomputable def scaleDown (p : CTorus d n) : CTorus d m :=
  fun i => AddCircle.equivAddCircle (n : ℝ) (m : ℝ) (Nat.cast_ne_zero.mpr (NeZero.ne n))
    (Nat.cast_ne_zero.mpr (NeZero.ne m)) (p i)

variable {L : ℕ}

private theorem scale_factor (hn : n = L * m) : (n : ℝ)⁻¹ * m = 1 / L := by
  have hm : (m : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hL : (L : ℝ) ≠ 0 := by
    intro h; apply NeZero.ne n; rw [hn]; simp [Nat.cast_eq_zero.mp h]
  rw [hn]; push_cast; field_simp

theorem scaleDown_coe (hn : n = L * m) (p : CTorus d n) (i : Fin d) (x : ℝ)
    (hx : p i = (x : AddCircle (n : ℝ))) : scaleDown (m := m) p i = ((x / L : ℝ) : AddCircle (m : ℝ)) := by
  unfold scaleDown
  rw [hx, AddCircle.equivAddCircle_apply_mk, scale_factor hn]
  congr 1; ring

omit [NeZero m] in
private theorem Lpos (hn : n = L * m) : (0 : ℝ) < L := by
  have : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · exact absurd (by simpa [h] using hn) (NeZero.ne n)
    · exact h
  exact_mod_cast this

theorem scaleDown_sub (p q : CTorus d n) : scaleDown (m := m) (p - q) = scaleDown p - scaleDown q := by
  funext i
  simp [scaleDown]

/-- **Lemma I.2.8 (b)**, norm part: `p ↦ p/L` divides distances by `L`. -/
theorem norm_scaleDown_le (hn : n = L * m) (p : CTorus d n) :
    ‖scaleDown (m := m) p‖ ≤ ‖p‖ / L := by
  have hL := Lpos (m := m) hn
  rw [pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg _) hL.le)]
  intro i
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective (p i)
  have hzi : ‖(z : AddCircle (n : ℝ))‖ ≤ ‖p‖ := by
    have := norm_le_pi_norm p i
    rwa [← hz] at this
  obtain ⟨k, hk⟩ := (norm_coe_le_iff _ _).mp hzi
  rw [scaleDown_coe hn p i z (by rw [← hz]), norm_coe_le_iff]
  refine ⟨k, ?_⟩
  have e : z / L - k * m = (z - k * n) / L := by
    rw [hn]; push_cast; field_simp
  rw [e, abs_div, abs_of_pos hL]
  exact div_le_div_of_nonneg_right hk hL.le

/-- **Lemma I.2.8 (b)**, cube part: `p ↦ p/L` maps `□_x` into `□_{x^↑}`. -/
theorem scaleDown_mem_cube (hn : n = L * m) {x : Torus d n} {q : CTorus d n} (hq : q ∈ cube x) :
    scaleDown (m := m) q ∈ cube (blockMap L m x) := by
  have hL := Lpos (m := m) hn
  intro i
  obtain ⟨t, ht, hqi⟩ := hq i
  have hxd := Nat.div_add_mod (x i).val L
  have hr : (((x i).val % L : ℕ) : ℝ) ≤ (L : ℝ) - 1 := by
    have := Nat.mod_lt (x i).val (by exact_mod_cast hL : 0 < L)
    have : (((x i).val % L : ℕ) : ℝ) + 1 ≤ L := by exact_mod_cast this
    linarith
  have hr0 : (0 : ℝ) ≤ (((x i).val % L : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨((((x i).val % L : ℕ) : ℝ) + t) / L, ⟨by have := ht.1; positivity, ?_⟩, ?_⟩
  · rw [div_le_one hL]; linarith [ht.2]
  · have h1 : scaleDown (m := m) q i = ((((x i).val : ℝ) + t) / L : ℝ) := by
      apply scaleDown_coe hn q i _ 
      rw [hqi]; unfold zc; rw [AddCircle.coe_add]
    rw [h1]
    have h2 : zc (blockMap L m x i) = ((((x i).val / L : ℕ) : ℝ) : AddCircle (m : ℝ)) := by
      rw [blockMap_apply]; unfold blockCoord; rw [zc_natCast]
    rw [h2, ← AddCircle.coe_add]
    congr 1
    have : ((x i).val : ℝ) = L * (((x i).val / L : ℕ) : ℝ) + (((x i).val % L : ℕ) : ℝ) := by
      exact_mod_cast hxd.symm
    rw [this]; field_simp; ring

/-- **Lemma I.2.8 (b)**: `X ⊆ N_r(Γ)` implies `X^↑ ⊆ N_{r/L}(Γ/L)`. -/
theorem blockMap_subset_NR (hn : n = L * m) {X : Set (Torus d n)} {r : ℝ} {Γ : Set (CTorus d n)}
    (h : X ⊆ NR r Γ) : blockMap L m '' X ⊆ NR (r / L) (scaleDown (m := m) '' Γ) := by
  have hL := Lpos (m := m) hn
  rintro _ ⟨x, hx, rfl⟩ ε hε
  obtain ⟨γ, hγ, q, hq, hlt⟩ := h hx (L * ε) (by positivity)
  refine ⟨scaleDown γ, ⟨γ, hγ, rfl⟩, scaleDown q, scaleDown_mem_cube hn hq, ?_⟩
  rw [← scaleDown_sub]
  calc ‖scaleDown (m := m) (γ - q)‖ ≤ ‖γ - q‖ / L := norm_scaleDown_le hn _
    _ < (r + L * ε) / L := div_lt_div_of_pos_right hlt hL
    _ = r / L + ε := by field_simp

end Scale

end Cubes

end Balaban.LargeField
