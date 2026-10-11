module

public import Balaban.LargeField.Geometry.Distance
public import Balaban.LargeField.Geometry.Continuous
public import Mathlib.Data.Set.Card
import Mathlib.Order.Interval.Set.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Small sets, hulls and boxes (Part I, Definition I.2.9 and Lemma I.2.10, first part)

A cyclic interval is `cycInt a s = {a, a+1, …, a+s-1}`. A set `X ⊂ 𝕋_k` is *small*
(`IsSmall`) if every coordinate projection lies in a cyclic interval of length `s` with `2 s < n`.
For a coordinate `i`, `hullCoord X i` is the intersection of all such short intervals containing
the projection `X_i`; `hull X = ∏_i hullCoord X i`. Lemma I.2.10 (a) says that `hullCoord X i` is the
shortest cyclic interval containing `X_i` (`hullCoord_isCycInt`, `hullCoord_shortest`); `side X`
is the largest of the lengths.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

variable {d n : ℕ}

/-- The cyclic interval `{a, a+1, …, a+s-1}` of `ℤ/nℤ`. -/
def cycInt (a : ZMod n) (s : ℕ) : Set (ZMod n) := {y | ∃ j : ℕ, j < s ∧ y = a + (j : ZMod n)}

/-- The position `pos a y ∈ [0, n)` of `y` in the cyclic order starting at `a`. -/
def pos (a y : ZMod n) : ℕ := (y - a).val

section Pos

variable [NeZero n]

theorem pos_lt (a y : ZMod n) : pos a y < n := ZMod.val_lt _

theorem natCast_pos (a y : ZMod n) : ((pos a y : ℕ) : ZMod n) = y - a := ZMod.natCast_zmod_val _

theorem eq_add_pos (a y : ZMod n) : y = a + (pos a y : ZMod n) := by
  rw [natCast_pos]; ring

omit [NeZero n] in
theorem pos_add_natCast (a : ZMod n) {j : ℕ} (hj : j < n) : pos a (a + (j : ZMod n)) = j := by
  unfold pos
  rw [add_sub_cancel_left, ZMod.val_natCast_of_lt hj]

theorem mem_cycInt_iff {a y : ZMod n} {s : ℕ} (hs : s ≤ n) : y ∈ cycInt a s ↔ pos a y < s := by
  constructor
  · rintro ⟨j, hj, rfl⟩
    rw [pos_add_natCast a (lt_of_lt_of_le hj hs)]; exact hj
  · intro h
    exact ⟨pos a y, h, eq_add_pos a y⟩

omit [NeZero n] in
/-- Integers congruent modulo `n` and closer than `n` are equal. -/
theorem int_eq_of_cast_eq {u v : ℤ} (h : (u : ZMod n) = (v : ZMod n)) (hlt : |u - v| < n) :
    u = v := by
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub v u n).mp h.symm
  have := Int.eq_zero_of_abs_lt_dvd hd (by simpa using hlt)
  linarith

theorem cycNorm_intCast_of_le {u : ℤ} (hu : 2 * |u| ≤ n) : cycNorm n (u : ZMod n) = u.natAbs := by
  apply le_antisymm
  · exact (cycNorm_le_iff _ _).mpr ⟨u, by rw [Int.abs_eq_natAbs], rfl⟩
  · obtain ⟨t, ht, hte⟩ := (cycNorm_le_iff (n := n) (u : ZMod n) _).mp le_rfl
    by_cases htu : t = u
    · subst htu
      have : |t| = (t.natAbs : ℤ) := Int.abs_eq_natAbs t
      omega
    · have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub u t n).mp hte.symm
      obtain ⟨q, hq⟩ := hdvd
      have hq0 : q ≠ 0 := by
        rintro rfl; apply htu; linarith
      have hn : (n : ℤ) ≤ |t - u| := by
        have : t - u = n * q := by linarith
        rw [this, abs_mul, Nat.abs_cast]
        exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Int.one_le_abs hq0)
      have h1 : |t - u| ≤ |t| + |u| := abs_sub _ _
      have h2 : |t| ≤ (cycNorm n (u : ZMod n) : ℤ) := ht
      have h3 : |u| = (u.natAbs : ℤ) := Int.abs_eq_natAbs u
      omega

/-- Positions of points of a short cyclic interval compute the cyclic distance. -/
theorem cycNorm_sub_of_mem {a y y' : ZMod n} {s : ℕ} (hs : 2 * s < n) (hy : y ∈ cycInt a s)
    (hy' : y' ∈ cycInt a s) : (cycNorm n (y - y') : ℤ) = |(pos a y : ℤ) - pos a y'| := by
  have h1 := (mem_cycInt_iff (by omega)).mp hy
  have h2 := (mem_cycInt_iff (by omega)).mp hy'
  have e : y - y' = (((pos a y : ℤ) - pos a y' : ℤ) : ZMod n) := by
    push_cast; rw [natCast_pos, natCast_pos]; ring
  rw [e, cycNorm_intCast_of_le]
  · rw [Int.abs_eq_natAbs]
  · have : |(pos a y : ℤ) - pos a y'| < s := abs_sub_lt_iff.mpr ⟨by omega, by omega⟩
    omega

end Pos

/-- A set is small if each coordinate projection lies in a cyclic interval of length `s`
with `2 s < n`. -/
def IsSmall (X : Set (Torus d n)) : Prop :=
  ∀ i, ∃ (a : ZMod n) (s : ℕ), 2 * s < n ∧ ∀ x ∈ X, x i ∈ cycInt a s

/-- The `i`-th coordinate of the hull: the intersection of all short cyclic intervals
(`2 s < n`) containing the projection `X_i`. -/
def hullCoord (X : Set (Torus d n)) (i : Fin d) : Set (ZMod n) :=
  {y | ∀ (a : ZMod n) (s : ℕ), 2 * s < n → (∀ x ∈ X, x i ∈ cycInt a s) → y ∈ cycInt a s}

/-- `Hull(X) = ∏_i J_i`, `J_i` the shortest cyclic interval containing `X_i`
(Lemma I.2.10 (a)). -/
def hull (X : Set (Torus d n)) : Set (Torus d n) := {y | ∀ i, y i ∈ hullCoord X i}

section Between

variable [NeZero n]

/-- Core interval argument: if `u, v` and `y` lie in a short interval `(a, s)` with
`pos u ≤ pos y ≤ pos v`, and `u, v` also lie in another short interval `(a', s')`, then `y` does. -/
theorem mem_cycInt_of_between {a a' : ZMod n} {s s' : ℕ} (hs : 2 * s < n) (hs' : 2 * s' < n)
    {u v y : ZMod n} (hu : u ∈ cycInt a s) (hv : v ∈ cycInt a s)
    (hu' : u ∈ cycInt a' s') (hv' : v ∈ cycInt a' s')
    (h1 : pos a u ≤ pos a y) (h2 : pos a y ≤ pos a v) : y ∈ cycInt a' s' := by
  have pu := (mem_cycInt_iff (by omega : s ≤ n)).mp hu
  have pv := (mem_cycInt_iff (by omega : s ≤ n)).mp hv
  have pu' := (mem_cycInt_iff (by omega : s' ≤ n)).mp hu'
  have pv' := (mem_cycInt_iff (by omega : s' ≤ n)).mp hv'
  have eA : (((pos a v : ℤ) - pos a u : ℤ) : ZMod n) = (((pos a' v : ℤ) - pos a' u : ℤ) : ZMod n) := by
    push_cast; rw [natCast_pos, natCast_pos, natCast_pos, natCast_pos]; ring
  have hAB := int_eq_of_cast_eq eA (by rw [abs_lt]; constructor <;> omega)
  rw [mem_cycInt_iff (by omega : s' ≤ n)]
  have eD : ((pos a' y : ℤ) : ZMod n) = (((pos a' u : ℤ) + ((pos a y : ℤ) - pos a u) : ℤ) : ZMod n) := by
    push_cast; rw [natCast_pos, natCast_pos, natCast_pos, natCast_pos]; ring
  have := int_eq_of_cast_eq eD (by
    have := pos_lt a' y
    rw [abs_lt]; constructor <;> omega)
  omega

theorem hullCoord_char {X : Set (Torus d n)} {i : Fin d} {a : ZMod n} {s : ℕ} (hs : 2 * s < n)
    (hcov : ∀ x ∈ X, x i ∈ cycInt a s) {y : ZMod n} :
    y ∈ hullCoord X i ↔ y ∈ cycInt a s ∧ (∃ x ∈ X, pos a (x i) ≤ pos a y) ∧
      (∃ x ∈ X, pos a y ≤ pos a (x i)) := by
  constructor
  · intro hy
    have hya : y ∈ cycInt a s := hy a s hs hcov
    have py := (mem_cycInt_iff (by omega : s ≤ n)).mp hya
    refine ⟨hya, ?_, ?_⟩
    · by_contra hno
      push Not at hno
      apply (absurd (hy (a + ((pos a y + 1 : ℕ) : ZMod n)) (s - (pos a y + 1)) (by omega) ?_) ?_)
      · intro x hx
        have hpx := (mem_cycInt_iff (by omega : s ≤ n)).mp (hcov x hx)
        refine ⟨pos a (x i) - (pos a y + 1), by have := hno x hx; omega, ?_⟩
        have e := eq_add_pos a (x i)
        have : ((pos a (x i) - (pos a y + 1) : ℕ) : ZMod n) =
            (pos a (x i) : ZMod n) - ((pos a y + 1 : ℕ) : ZMod n) := by
          rw [Nat.cast_sub (by have := hno x hx; omega)]
        rw [this]; nth_rewrite 1 [e]; ring
      · rintro ⟨j, hj, hj'⟩
        have : ((pos a y : ℕ) : ZMod n) = ((pos a y + 1 + j : ℕ) : ZMod n) := by
          have : y - a = (((pos a y + 1 : ℕ) : ZMod n)) + (j : ZMod n) := by
            nth_rewrite 1 [hj']; ring
          rw [natCast_pos, this]; push_cast; ring
        have h2 := (ZMod.natCast_eq_natCast_iff' _ _ n).mp this
        rw [Nat.mod_eq_of_lt (pos_lt a y), Nat.mod_eq_of_lt (by omega)] at h2
        omega
    · by_contra hno
      push Not at hno
      have := hy a (pos a y) (by omega) (fun x hx => by
        rw [mem_cycInt_iff (by omega)]; exact hno x hx)
      rw [mem_cycInt_iff (by omega)] at this
      omega
  · rintro ⟨hya, ⟨u, hu, hu1⟩, ⟨v, hv, hv1⟩⟩ a' s' hs' hcov'
    exact mem_cycInt_of_between hs hs' (hcov u hu) (hcov v hv) (hcov' u hu) (hcov' v hv) hu1 hv1

end Between

section Main

variable [NeZero n]

omit [NeZero n] in
theorem ncard_cycInt {a : ZMod n} {s : ℕ} (hs : s ≤ n) : (cycInt a s).ncard = s := by
  have : cycInt a s = (fun j : ℕ => a + (j : ZMod n)) '' Set.Iio s := by
    ext y; simp [cycInt, eq_comm]
  have hinj : Set.InjOn (fun j : ℕ => a + (j : ZMod n)) (Set.Iio s) := by
    intro j hj k hk h
    simp only [add_right_inj] at h
    have := (ZMod.natCast_eq_natCast_iff' _ _ n).mp h
    rw [Nat.mod_eq_of_lt (lt_of_lt_of_le hj hs), Nat.mod_eq_of_lt (lt_of_lt_of_le hk hs)] at this
    exact this
  rw [this, Set.ncard_def, hinj.encard_image, ← Set.ncard_def]
  exact Set.ncard_Iio_nat s

omit [NeZero n] in
theorem subset_hull (X : Set (Torus d n)) : X ⊆ hull X :=
  fun x hx _ _ _ _ hcov => hcov x hx

omit [NeZero n] in
theorem hullCoord_subset {X : Set (Torus d n)} {i : Fin d} {a : ZMod n} {s : ℕ} (hs : 2 * s < n)
    (hcov : ∀ x ∈ X, x i ∈ cycInt a s) : hullCoord X i ⊆ cycInt a s :=
  fun _ hy => hy a s hs hcov

omit [NeZero n] in
/-- **Lemma I.2.10 (b)**: `Hull(Hull(X)) = Hull(X)`. -/
theorem hull_hull (X : Set (Torus d n)) : hull (hull X) = hull X := by
  have key : ∀ i, hullCoord (hull X) i = hullCoord X i := by
    intro i
    ext y
    constructor
    · intro hy a s hs hcov
      exact hy a s hs fun x hx => hullCoord_subset hs hcov (hx i)
    · intro hy a s hs hcov
      exact hy a s hs fun x hx => hcov x (subset_hull X hx)
  ext y
  show (∀ i, y i ∈ hullCoord (hull X) i) ↔ ∀ i, y i ∈ hullCoord X i
  simp only [key]

omit [NeZero n] in
/-- **Lemma I.2.10 (b)**: the hull of a small set is small. -/
theorem IsSmall.hull {X : Set (Torus d n)} (hX : IsSmall X) : IsSmall (hull X) := by
  intro i
  obtain ⟨a, s, hs, hcov⟩ := hX i
  exact ⟨a, s, hs, fun x hx => hullCoord_subset hs hcov (hx i)⟩

/-- **Lemma I.2.10 (a)**: for a nonempty small set, each coordinate of the hull is a cyclic
interval `cycInt b t` which is the shortest short interval containing `X_i` (it lies in every one),
with endpoints attained by points of `X`. -/
theorem hullCoord_isCycInt {X : Set (Torus d n)} (hne : X.Nonempty) (hX : IsSmall X) (i : Fin d) :
    ∃ (b : ZMod n) (t : ℕ), 1 ≤ t ∧ 2 * t < n ∧ hullCoord X i = cycInt b t ∧
      (∃ u ∈ X, u i = b) ∧ (∃ v ∈ X, v i = b + ((t - 1 : ℕ) : ZMod n)) := by
  obtain ⟨a, s, hs, hcov⟩ := hX i
  obtain ⟨u, hu, hmin⟩ := Set.exists_min_image X (fun x => pos a (x i)) (Set.toFinite X) hne
  obtain ⟨v, hv, hmax⟩ := Set.exists_min_image X (fun x => (pos a (x i) : ℤ) * (-1)) (Set.toFinite X) hne
  have hpu := (mem_cycInt_iff (by omega : s ≤ n)).mp (hcov u hu)
  have hpv := (mem_cycInt_iff (by omega : s ≤ n)).mp (hcov v hv)
  have hmax' : ∀ x ∈ X, pos a (x i) ≤ pos a (v i) := fun x hx => by
    have := hmax x hx; omega
  have hle : pos a (u i) ≤ pos a (v i) := hmin v hv
  refine ⟨a + ((pos a (u i) : ℕ) : ZMod n), pos a (v i) - pos a (u i) + 1, by omega, by omega, ?_, ?_, ?_⟩
  · ext y
    rw [hullCoord_char hs hcov]
    constructor
    · rintro ⟨hy, ⟨x, hx, h1⟩, ⟨x', hx', h2⟩⟩
      have h3 := hmin x hx
      have h4 := hmax' x' hx'
      have hyl : pos a (u i) ≤ pos a y := by omega
      have hyh : pos a y ≤ pos a (v i) := by omega
      refine ⟨pos a y - pos a (u i), by omega, ?_⟩
      rw [Nat.cast_sub hyl]
      nth_rewrite 1 [eq_add_pos a y]; ring
    · rintro ⟨j, hj, rfl⟩
      have hp : pos a (a + ((pos a (u i) : ℕ) : ZMod n) + (j : ZMod n)) = pos a (u i) + j := by
        rw [add_assoc, ← Nat.cast_add, pos_add_natCast a (by omega)]
      refine ⟨?_, ⟨u, hu, by omega⟩, ⟨v, hv, by omega⟩⟩
      rw [mem_cycInt_iff (by omega), hp]; omega
  · exact ⟨u, hu, eq_add_pos a (u i)⟩
  · refine ⟨v, hv, ?_⟩
    have : (((pos a (v i) - pos a (u i) + 1 - 1 : ℕ)) : ZMod n) =
        ((pos a (v i) : ℕ) : ZMod n) - ((pos a (u i) : ℕ) : ZMod n) := by
      rw [Nat.add_sub_cancel, Nat.cast_sub hle]
    rw [this]; nth_rewrite 1 [eq_add_pos a (v i)]; ring

/-- The side of a small nonempty set: the largest length of a coordinate interval of its hull. -/
noncomputable def side (X : Set (Torus d n)) : ℕ :=
  Finset.univ.sup fun i : Fin d => (hullCoord X i).ncard

theorem ncard_hullCoord_le {X : Set (Torus d n)} {i : Fin d} {a : ZMod n} {s : ℕ}
    (hs : 2 * s < n) (hcov : ∀ x ∈ X, x i ∈ cycInt a s) : (hullCoord X i).ncard ≤ s := by
  rw [← ncard_cycInt (a := a) (by omega : s ≤ n)]
  exact Set.ncard_le_ncard (hullCoord_subset hs hcov) (Set.toFinite _)

/-- **Lemma I.2.10 (a)** (uniqueness): a shortest short cyclic interval containing `X_i` equals
`hullCoord X i`. -/
theorem hull_unique {X : Set (Torus d n)} (hne : X.Nonempty) (hX : IsSmall X) (i : Fin d)
    {b : ZMod n} {t : ℕ} (ht : 2 * t < n) (hcov : ∀ x ∈ X, x i ∈ cycInt b t)
    (hmin : ∀ (a : ZMod n) (s : ℕ), 2 * s < n → (∀ x ∈ X, x i ∈ cycInt a s) → t ≤ s) :
    cycInt b t = hullCoord X i := by
  obtain ⟨b0, t0, h1, h2, h0, -, -⟩ := hullCoord_isCycInt hne hX i
  have hsub : hullCoord X i ⊆ cycInt b t := hullCoord_subset ht hcov
  have hcov0 : ∀ x ∈ X, x i ∈ cycInt b0 t0 := fun x hx => h0 ▸ subset_hull X hx i
  have ht0 : t ≤ t0 := hmin b0 t0 h2 hcov0
  have hc : (hullCoord X i).ncard = t0 := by rw [h0, ncard_cycInt (by omega)]
  have hc' : (cycInt b t).ncard = t := ncard_cycInt (by omega)
  exact (Set.eq_of_subset_of_ncard_le hsub (by omega) (Set.toFinite _)).symm

/-- **Lemma I.2.10 (c)**: if `X` has sup-diameter `≤ e` and `4 e + 2 < n`, then `X` is small and
`side X ≤ e + 1`. -/
theorem side_le_diam_succ {X : Set (Torus d n)} (hne : X.Nonempty) {e : ℕ}
    (hdiam : ∀ x ∈ X, ∀ y ∈ X, supDist x y ≤ e) (he : 4 * e + 2 < n) :
    IsSmall X ∧ side X ≤ e + 1 := by
  obtain ⟨x0, hx0⟩ := hne
  have hbase : ∀ i, ∀ x ∈ X, x i ∈ cycInt (x0 i - (e : ZMod n)) (2 * e + 1) := by
    intro i x hx
    obtain ⟨t, ht, hte⟩ := (cycNorm_le_iff (n := n) (x i - x0 i) e).mp
      ((cycNorm_le_supDist x x0 i).trans (hdiam x hx x0 hx0))
    have ht' := abs_le.mp ht
    refine ⟨(e + t).toNat, by omega, ?_⟩
    have : (((e + t).toNat : ℕ) : ℤ) = e + t := by omega
    have h2 : ((((e + t).toNat : ℕ) : ℤ) : ZMod n) = (e : ZMod n) + (t : ZMod n) := by
      rw [this]; push_cast; ring
    rw [Int.cast_natCast] at h2
    rw [h2, hte]; ring
  have hsm : IsSmall X := fun i => ⟨_, _, by omega, hbase i⟩
  refine ⟨hsm, Finset.sup_le fun i _ => ?_⟩
  obtain ⟨b, t, h1, h2, h0, ⟨u, hu, hub⟩, ⟨v, hv, hvb⟩⟩ := hullCoord_isCycInt ⟨x0, hx0⟩ hsm i
  have hc : (hullCoord X i).ncard = t := by rw [h0, ncard_cycInt (by omega)]
  rw [hc]
  -- distance between the endpoints
  have hu' : u i ∈ cycInt (x0 i - (e : ZMod n)) (2 * e + 1) := hbase i u hu
  have hv' : v i ∈ cycInt (x0 i - (e : ZMod n)) (2 * e + 1) := hbase i v hv
  have hd := cycNorm_sub_of_mem (by omega) hv' hu'
  have hvu : v i - u i = ((t - 1 : ℕ) : ZMod n) := by rw [hvb, hub]; ring
  have hle := cycNorm_le_supDist v u i
  have hle2 := hdiam v hv u hu
  have : cycNorm n ((t - 1 : ℕ) : ZMod n) = t - 1 := by
    have := cycNorm_intCast_of_le (n := n) (u := ((t - 1 : ℕ) : ℤ)) (by
      rw [Nat.abs_cast]; omega)
    simpa using this
  rw [← hvu] at this
  omega

/-- **Lemma I.2.10 (d)**: if `X ⊆ N_{ρ+4}(p)` for a point `p` and `n ≥ 4ρ + 21`, then `X` is
small and `side X ≤ 2ρ + 10`. -/
theorem small_of_subset_NR {X : Set (Torus d n)} {ρ : ℕ} {p : CTorus d n}
    (hX : X ⊆ NR ((ρ : ℝ) + 4) {p}) (hn : 4 * ρ + 21 ≤ n) :
    IsSmall X ∧ side X ≤ 2 * ρ + 10 := by
  obtain ⟨a, ha⟩ := NR_point_coord_interval ρ p
  have hcov : ∀ i, ∀ x ∈ X, x i ∈ cycInt (a i) (2 * ρ + 10) := fun i x hx => ha x (hX hx) i
  exact ⟨fun i => ⟨a i, 2 * ρ + 10, by omega, hcov i⟩,
    Finset.sup_le fun i _ => ncard_hullCoord_le (by omega) (hcov i)⟩

/-- **Lemma I.2.10 (e)**: a nonempty small set has an injective lift `ι` to `ℤ^d`, which preserves
`d` between points of `Hull(X)` and maps `Hull(X)` onto the integer hull `[lo, hi]` of the lift of
`X` (`lo i`, `hi i` are attained by points of `X`). -/
theorem lift_small {X : Set (Torus d n)} (hne : X.Nonempty) (hX : IsSmall X) :
    ∃ ι : Torus d n → (Fin d → ℤ), (∀ x i, ((ι x i : ℤ) : ZMod n) = x i) ∧
      Function.Injective ι ∧
      (∀ x ∈ hull X, ∀ y ∈ hull X, ∀ m : ℕ, supDist x y ≤ m ↔ ∀ i, |ι x i - ι y i| ≤ m) ∧
      ∃ lo hi : Fin d → ℤ, ι '' hull X = Set.Icc lo hi ∧
        ∀ i, (∃ x ∈ X, ι x i = lo i) ∧ (∃ x ∈ X, ι x i = hi i) := by
  choose b t h1 h2 h0 hu hv using hullCoord_isCycInt hne hX
  have hpos : ∀ (i : Fin d) (y : ZMod n), y ∈ hullCoord X i → pos (b i) y < t i := fun i y hy =>
    (mem_cycInt_iff (by have := h2 i; omega)).mp (h0 i ▸ hy)
  refine ⟨fun x i => ((b i).val : ℤ) + pos (b i) (x i), ?_, ?_, ?_, fun i => ((b i).val : ℤ),
    fun i => ((b i).val : ℤ) + t i - 1, ?_, fun i => ⟨?_, ?_⟩⟩
  · intro x i
    simp only
    push_cast
    rw [natCast_pos]; simp
  · intro x y hxy
    funext i
    have := congrFun hxy i
    simp only at this
    have e : ((pos (b i) (x i) : ℕ) : ZMod n) = (pos (b i) (y i) : ℕ) := by
      have : pos (b i) (x i) = pos (b i) (y i) := by omega
      rw [this]
    rw [natCast_pos, natCast_pos] at e
    exact sub_left_injective e
  · intro x hx y hy m
    rw [supDist_le_iff]
    refine forall_congr' fun i => ?_
    have hxi := h0 i ▸ hx i
    have hyi := h0 i ▸ hy i
    have hd := cycNorm_sub_of_mem (by have := h2 i; omega) hxi hyi
    simp only [add_sub_add_left_eq_sub]
    rw [← hd]
    exact (Nat.cast_le (α := ℤ)).symm
  · ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨fun i => ?_, fun i => ?_⟩
      · show ((b i).val : ℤ) ≤ ((b i).val : ℤ) + pos (b i) (y i)
        omega
      · have := hpos i (y i) (hy i)
        show ((b i).val : ℤ) + pos (b i) (y i) ≤ ((b i).val : ℤ) + t i - 1
        omega
    · rintro ⟨hlo, hhi⟩
      have hj : ∀ i, (z i - (b i).val).toNat < t i := fun i => by
        have := hhi i; have := hlo i
        simp only at *
        omega
      have hzi : ∀ i, (z i : ZMod n) = b i + (((z i - (b i).val).toNat : ℕ) : ZMod n) := fun i => by
        have : (((z i - (b i).val).toNat : ℕ) : ℤ) = z i - (b i).val := by
          have := hlo i; simp only at this; omega
        have h3 : ((((z i - (b i).val).toNat : ℕ) : ℤ) : ZMod n) = ((z i - (b i).val : ℤ) : ZMod n) := by
          rw [this]
        rw [Int.cast_natCast] at h3
        rw [h3]; push_cast; simp
      refine ⟨fun i => (z i : ZMod n), fun i => ?_, ?_⟩
      · rw [h0 i]
        exact ⟨_, hj i, hzi i⟩
      · funext i
        show ((b i).val : ℤ) + pos (b i) (z i : ZMod n) = z i
        have hp : pos (b i) (z i : ZMod n) = (z i - (b i).val).toNat := by
          rw [hzi i]
          exact pos_add_natCast _ (by have := hj i; have := h2 i; omega)
        have := hlo i
        simp only at this
        omega
  · obtain ⟨u, hu1, hu2⟩ := hu i
    exact ⟨u, hu1, by simp only; rw [hu2]; simp [pos]⟩
  · obtain ⟨v, hv1, hv2⟩ := hv i
    refine ⟨v, hv1, ?_⟩
    simp only
    rw [hv2, pos_add_natCast _ (by have := h2 i; omega)]
    have := h1 i
    omega

/-- A box: a product of cyclic intervals (of lengths between `1` and `n`). -/
def IsBox (B : Set (Torus d n)) : Prop :=
  ∃ (a : Torus d n) (s : Fin d → ℕ), (∀ i, 1 ≤ s i ∧ s i ≤ n) ∧ B = box a s

/-- **Lemma I.2.10 (a)/(b)**: the hull of a nonempty small set is a box whose side is `side X`. -/
theorem hull_eq_box {X : Set (Torus d n)} (hne : X.Nonempty) (hX : IsSmall X) :
    ∃ (a : Torus d n) (s : Fin d → ℕ), hull X = box a s ∧ (∀ i, 1 ≤ s i ∧ 2 * s i < n) ∧
      side X = Finset.univ.sup s := by
  choose b t h1 h2 h0 _ _ using hullCoord_isCycInt hne hX
  refine ⟨b, t, ?_, fun i => ⟨h1 i, h2 i⟩, ?_⟩
  · ext y
    simp only [hull, box, Set.mem_ofPred_eq]
    refine forall_congr' fun i => ?_
    rw [h0 i]
    simp [cycInt]
  · unfold side
    congr 1
    funext i
    rw [h0 i, ncard_cycInt (by have := h2 i; omega)]

theorem hull_isBox {X : Set (Torus d n)} (hne : X.Nonempty) (hX : IsSmall X) : IsBox (hull X) := by
  obtain ⟨a, s, h, hs, -⟩ := hull_eq_box hne hX
  exact ⟨a, s, fun i => ⟨(hs i).1, by have := (hs i).2; omega⟩, h⟩

end Main

end Balaban.LargeField
