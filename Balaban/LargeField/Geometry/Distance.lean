module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Order.Nat
public import Mathlib.Data.ENat.Lattice
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The index distance on the cube torus (Part I, Definition I.2.0 and Lemma I.2.1)

For the torus `Torus d n = Fin d → ZMod n` (the cubes of `𝕋_k`, `n = n_k`):

* `cycNorm n a = min (a.val) (n - a.val)` is the cyclic norm `|a|_n`;
* `supDist x y = max_i |x_i - y_i|_n` is the index distance `d(x, y)`;
* `setDist X Y` is the distance between sets (`⊤` if one is empty);
* `nbhd m X = X^{∼m}`, `nbhdNeg m X = X^{∼-m}`, `thick r X = X^{≈}`, `thick2 r X = X^{≈2}`
  (`r` stands for `[R_{j-1}]`).

The key tool is `cycNorm_le_iff`: `|a|_n ≤ k` iff `a` has an integer lift of absolute value `≤ k`.
Metric facts: `supDist_triangle`, `exists_split` (Lemma I.2.1 (b)), `exists_geodesic`
(Lemma I.2.1 (c)), `nbhd_nbhd`, `setDist_nbhd_ge`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban

/-- The cyclic norm `|a|_n = min {a.val, n - a.val}` on `ℤ/nℤ`. -/
def cycNorm (n : ℕ) (a : ZMod n) : ℕ := min a.val (n - a.val)

section Cyc

variable {n : ℕ} [NeZero n]

/-- `|a|_n ≤ k` iff `a` has an integer lift of absolute value at most `k`. -/
theorem cycNorm_le_iff (a : ZMod n) (k : ℕ) :
    cycNorm n a ≤ k ↔ ∃ t : ℤ, |t| ≤ k ∧ (t : ZMod n) = a := by
  constructor
  · intro h
    have hv : a.val < n := ZMod.val_lt a
    unfold cycNorm at h
    rcases le_total a.val (n - a.val) with h1 | h1
    · refine ⟨(a.val : ℤ), ?_, by simp⟩
      rw [abs_of_nonneg (by positivity)]
      have : a.val ≤ k := by omega
      exact_mod_cast this
    · refine ⟨(a.val : ℤ) - n, ?_, by simp⟩
      rw [abs_of_nonpos (by omega)]
      have : n - a.val ≤ k := by omega
      have h2 : ((n - a.val : ℕ) : ℤ) = n - a.val := by omega
      rw [neg_sub, ← h2]
      exact_mod_cast this
  · rintro ⟨t, ht, rfl⟩
    have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    have hval := ZMod.val_intCast (n := n) t
    have h0 : 0 ≤ t % n := Int.emod_nonneg _ hn.ne'
    have h1 : t % n < n := Int.emod_lt_of_pos _ hn
    have h2 : (n : ℤ) * (t / n) + t % n = t := Int.mul_ediv_add_emod t n
    have habs := abs_le.mp ht
    unfold cycNorm
    rcases le_or_gt 0 (t / n) with hq | hq
    · have : 0 ≤ (n : ℤ) * (t / n) := mul_nonneg hn.le hq
      have : ((ZMod.val (t : ZMod n) : ℕ) : ℤ) ≤ k := by rw [hval]; linarith
      have : ZMod.val (t : ZMod n) ≤ k := by exact_mod_cast this
      exact le_trans (min_le_left _ _) this
    · have : (n : ℤ) * (t / n) ≤ -n := by nlinarith
      have h3 : ((n - ZMod.val (t : ZMod n) : ℕ) : ℤ) = n - t % n := by
        have := ZMod.val_lt (t : ZMod n)
        push_cast [Nat.cast_sub this.le, hval]; ring
      have : ((n - ZMod.val (t : ZMod n) : ℕ) : ℤ) ≤ k := by rw [h3]; linarith
      exact le_trans (min_le_right _ _) (by exact_mod_cast this)

theorem cycNorm_zero_iff (a : ZMod n) : cycNorm n a = 0 ↔ a = 0 := by
  have := cycNorm_le_iff a 0
  constructor
  · intro h
    obtain ⟨t, ht, rfl⟩ := this.mp h.le
    have : t = 0 := by simpa using ht
    simp [this]
  · rintro rfl
    exact Nat.le_zero.mp (this.mpr ⟨0, by simp⟩)

theorem cycNorm_neg (a : ZMod n) : cycNorm n (-a) = cycNorm n a := by
  apply le_antisymm
  · rw [cycNorm_le_iff]
    obtain ⟨t, ht, rfl⟩ := (cycNorm_le_iff (n := n) a (cycNorm n a)).mp le_rfl
    exact ⟨-t, by simpa using ht, by simp⟩
  · rw [cycNorm_le_iff]
    obtain ⟨t, ht, h⟩ := (cycNorm_le_iff (n := n) (-a) (cycNorm n (-a))).mp le_rfl
    exact ⟨-t, by simpa using ht, by simp [h]⟩

theorem cycNorm_add_le (a b : ZMod n) : cycNorm n (a + b) ≤ cycNorm n a + cycNorm n b := by
  obtain ⟨s, hs, rfl⟩ := (cycNorm_le_iff (n := n) a (cycNorm n a)).mp le_rfl
  obtain ⟨t, ht, rfl⟩ := (cycNorm_le_iff (n := n) b (cycNorm n b)).mp le_rfl
  rw [cycNorm_le_iff]
  refine ⟨s + t, ?_, by simp⟩
  push_cast
  exact (abs_add_le _ _).trans (add_le_add hs ht)

theorem cycNorm_sub_comm (a b : ZMod n) : cycNorm n (a - b) = cycNorm n (b - a) := by
  rw [← cycNorm_neg, neg_sub]

theorem cycNorm_sub_le (a b c : ZMod n) :
    cycNorm n (a - c) ≤ cycNorm n (a - b) + cycNorm n (b - c) := by
  have := cycNorm_add_le (n := n) (a - b) (b - c)
  simpa using this

/-- Splitting a cyclic displacement: if `|a|_n ≤ s + t` there is `b` with `|b|_n ≤ s` and
`|a - b|_n ≤ t`. -/
theorem exists_cyc_split (a : ZMod n) {s t : ℕ} (h : cycNorm n a ≤ s + t) :
    ∃ b : ZMod n, cycNorm n b ≤ s ∧ cycNorm n (a - b) ≤ t := by
  obtain ⟨u, hu, rfl⟩ := (cycNorm_le_iff (n := n) a _).mp h
  have hu' := abs_le.mp hu
  push_cast at hu'
  refine ⟨((max (-(s : ℤ)) (min (s : ℤ) u) : ℤ) : ZMod n), ?_, ?_⟩
  · rw [cycNorm_le_iff]
    refine ⟨max (-(s : ℤ)) (min (s : ℤ) u), ?_, rfl⟩
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  · rw [← Int.cast_sub, cycNorm_le_iff]
    refine ⟨u - max (-(s : ℤ)) (min (s : ℤ) u), ?_, rfl⟩
    rw [abs_le]
    rcases le_total u (-(s : ℤ)) with h1 | h1
    · have : min (s : ℤ) u = u := min_eq_right (by linarith [(Nat.cast_nonneg s : (0:ℤ) ≤ s)])
      rw [this, max_eq_left h1]; constructor <;> linarith
    · rcases le_total u (s : ℤ) with h2 | h2
      · rw [min_eq_right h2, max_eq_right h1]; constructor <;> linarith
      · rw [min_eq_left h2, max_eq_right (by linarith [(Nat.cast_nonneg s : (0:ℤ) ≤ s)])]
        constructor <;> linarith

end Cyc

variable {d n : ℕ}

/-- The index distance `d(x, y) = max_i |x_i - y_i|_n` on `𝕋 = (ℤ/nℤ)^d`. -/
def supDist (x y : Torus d n) : ℕ := Finset.univ.sup fun i => cycNorm n (x i - y i)

theorem supDist_le_iff {x y : Torus d n} {m : ℕ} :
    supDist x y ≤ m ↔ ∀ i, cycNorm n (x i - y i) ≤ m := by
  simp [supDist, Finset.sup_le_iff]

theorem cycNorm_le_supDist (x y : Torus d n) (i : Fin d) :
    cycNorm n (x i - y i) ≤ supDist x y :=
  supDist_le_iff.mp le_rfl i

section Metric

variable [NeZero n]

omit [NeZero n] in
theorem supDist_self (x : Torus d n) : supDist x x = 0 := by
  have : supDist x x ≤ 0 := supDist_le_iff.mpr fun i => by simp [cycNorm]
  omega

theorem supDist_comm (x y : Torus d n) : supDist x y = supDist y x := by
  apply le_antisymm <;>
  exact supDist_le_iff.mpr fun i => by
    rw [cycNorm_sub_comm]; exact cycNorm_le_supDist _ _ i

theorem supDist_eq_zero {x y : Torus d n} : supDist x y = 0 ↔ x = y := by
  constructor
  · intro h
    funext i
    have := cycNorm_le_supDist x y i
    rw [h] at this
    exact sub_eq_zero.mp ((cycNorm_zero_iff _).mp (Nat.le_zero.mp this))
  · rintro rfl; exact supDist_self _

/-- **Lemma I.2.1 (a)**: the triangle inequality for `d`. (Together with `supDist_comm`,
`supDist_eq_zero`: `d` is a metric on the torus.) -/
theorem supDist_triangle (x y z : Torus d n) : supDist x z ≤ supDist x y + supDist y z :=
  supDist_le_iff.mpr fun i =>
    (cycNorm_sub_le (x i) (y i) (z i)).trans
      (add_le_add (cycNorm_le_supDist x y i) (cycNorm_le_supDist y z i))

/-- **Lemma I.2.1 (b)**: if `d(x, z) ≤ a + b` there is `y` with `d(x, y) ≤ a` and `d(y, z) ≤ b`. -/
theorem exists_split {x z : Torus d n} {a b : ℕ} (h : supDist x z ≤ a + b) :
    ∃ y, supDist x y ≤ a ∧ supDist y z ≤ b := by
  have hi : ∀ i, ∃ c : ZMod n, cycNorm n c ≤ a ∧ cycNorm n (x i - z i - c) ≤ b := fun i =>
    exists_cyc_split _ (supDist_le_iff.mp h i)
  choose c hc1 hc2 using hi
  refine ⟨fun i => x i - c i, supDist_le_iff.mpr fun i => ?_, supDist_le_iff.mpr fun i => ?_⟩
  · simpa using hc1 i
  · have : x i - c i - z i = x i - z i - c i := by ring
    simp only [this]; exact hc2 i

/-- **Lemma I.2.1 (c)**: a geodesic `x = z₀, …, z_t = z` with `d(z_{i-1}, z_i) = 1` and
`d(x, z_i) = i`, where `t = d(x, z)`. -/
theorem exists_geodesic (x z : Torus d n) :
    ∃ g : ℕ → Torus d n, g 0 = x ∧ g (supDist x z) = z ∧
      ∀ i ≤ supDist x z, supDist x (g i) = i ∧
        (i < supDist x z → supDist (g i) (g (i + 1)) = 1) := by
  -- by induction on `t`: a point `y` at distance `≤ t - 1` from `x` and `≤ 1` from `z`
  have key : ∀ t : ℕ, ∀ z : Torus d n, supDist x z = t →
      ∃ g : ℕ → Torus d n, g 0 = x ∧ g t = z ∧
        ∀ i ≤ t, supDist x (g i) = i ∧ (i < t → supDist (g i) (g (i + 1)) = 1) := by
    intro t
    induction t with
    | zero =>
      intro z hz
      refine ⟨fun _ => x, rfl, (supDist_eq_zero.mp hz), fun i hi => ?_⟩
      have : i = 0 := by omega
      subst this
      simp [supDist_self]
    | succ t ih =>
      intro z hz
      obtain ⟨y, hy1, hy2⟩ := exists_split (x := x) (z := z) (a := t) (b := 1) (by omega)
      have hyt : supDist x y = t := by
        apply le_antisymm hy1
        have := supDist_triangle x y z
        omega
      have hy1' : supDist y z = 1 := by
        apply le_antisymm hy2
        have := supDist_triangle x y z
        have h0 : supDist y z ≠ 0 := by
          intro h0; rw [supDist_eq_zero.mp h0] at hyt; omega
        omega
      obtain ⟨g, hg0, hgt, hg⟩ := ih y hyt
      refine ⟨fun i => if i = t + 1 then z else g i, by simp [hg0], by simp, fun i hi => ?_⟩
      by_cases hit : i = t + 1
      · subst hit; simp [hz]
      · have hi' : i ≤ t := by omega
        simp only [hit, ite_false]
        refine ⟨(hg i hi').1, fun hlt => ?_⟩
        by_cases hit2 : i + 1 = t + 1
        · have : i = t := by omega
          subst this
          simp only [ite_true]
          rw [hgt]; exact hy1'
        · simp only [hit2, ite_false]
          exact (hg i hi').2 (by omega)
  exact key _ z rfl

end Metric

/-- Distance between sets in the index distance; `⊤` if one is empty. -/
noncomputable def setDist (X Y : Set (Torus d n)) : ℕ∞ :=
  ⨅ x ∈ X, ⨅ y ∈ Y, (supDist x y : ℕ∞)

theorem setDist_le_iff {X Y : Set (Torus d n)} {m : ℕ} :
    setDist X Y ≤ m ↔ ∃ x ∈ X, ∃ y ∈ Y, supDist x y ≤ m := by
  unfold setDist
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have h1 : ((m + 1 : ℕ) : ℕ∞) ≤ ⨅ x ∈ X, ⨅ y ∈ Y, (supDist x y : ℕ∞) := by
      refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
      exact_mod_cast hne x hx y hy
    have := h1.trans h
    have : m + 1 ≤ m := by exact_mod_cast this
    omega
  · rintro ⟨x, hx, y, hy, h⟩
    exact (iInf₂_le x hx).trans ((iInf₂_le y hy).trans (by exact_mod_cast h))

theorem setDist_eq_top_iff {X Y : Set (Torus d n)} :
    setDist X Y = ⊤ ↔ X = ∅ ∨ Y = ∅ := by
  constructor
  · intro h
    by_contra hne
    push Not at hne
    obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := hne
    have := (setDist_le_iff (X := X) (Y := Y) (m := supDist x y)).mpr ⟨x, hx, y, hy, le_rfl⟩
    rw [h] at this
    exact absurd this (by simp)
  · rintro (rfl | rfl) <;> simp [setDist]

theorem setDist_comm [NeZero n] (X Y : Set (Torus d n)) : setDist X Y = setDist Y X := by
  have key : ∀ X Y : Set (Torus d n), setDist Y X ≤ setDist X Y := by
    intro X Y
    induction h : setDist X Y using ENat.recTopCoe with
    | top => exact le_top
    | coe m =>
      have := setDist_le_iff.mp h.le
      obtain ⟨x, hx, y, hy, hxy⟩ := this
      exact setDist_le_iff.mpr ⟨y, hy, x, hx, by rwa [supDist_comm]⟩
  exact le_antisymm (key Y X) (key X Y)

/-- `X^{∼m} = {y : d(y, X) ≤ m}`. -/
def nbhd (m : ℕ) (X : Set (Torus d n)) : Set (Torus d n) := {y | setDist {y} X ≤ m}

/-- The inner neighbourhood `X^{∼-m} = ((X^c)^{∼m})^c`. -/
def nbhdNeg (m : ℕ) (X : Set (Torus d n)) : Set (Torus d n) := (nbhd m Xᶜ)ᶜ

/-- The thick neighbourhood `X^≈ = X^{∼([R_{j-1}]+1)}`; the argument `r` stands for `[R_{j-1}]`. -/
def thick (r : ℕ) (X : Set (Torus d n)) : Set (Torus d n) := nbhd (r + 1) X

/-- `X^{≈2} = (X^≈)^≈`. -/
def thick2 (r : ℕ) (X : Set (Torus d n)) : Set (Torus d n) := thick r (thick r X)

theorem mem_nbhd {m : ℕ} {X : Set (Torus d n)} {y : Torus d n} :
    y ∈ nbhd m X ↔ ∃ x ∈ X, supDist y x ≤ m := by
  unfold nbhd
  simp only [Set.mem_ofPred_eq, setDist_le_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, rfl, x, hx, h⟩; exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, h⟩; exact ⟨y, rfl, x, hx, h⟩

theorem mem_nbhdNeg {m : ℕ} {X : Set (Torus d n)} {y : Torus d n} :
    y ∈ nbhdNeg m X ↔ ∀ x, supDist y x ≤ m → x ∈ X := by
  unfold nbhdNeg
  simp only [Set.mem_compl_iff, mem_nbhd, not_exists, not_and, not_le]
  constructor
  · intro h x hx
    by_contra hxX
    exact absurd hx (not_le.mpr (h x hxX))
  · intro h x hx
    by_contra hc
    exact absurd hx (not_not.mpr (h x (not_lt.mp hc)))

theorem subset_nbhd (m : ℕ) (X : Set (Torus d n)) [NeZero n] : X ⊆ nbhd m X :=
  fun x hx => mem_nbhd.mpr ⟨x, hx, by simp [supDist_self]⟩

theorem nbhd_mono {m m' : ℕ} (h : m ≤ m') {X Y : Set (Torus d n)} (hXY : X ⊆ Y) :
    nbhd m X ⊆ nbhd m' Y := by
  intro y hy
  obtain ⟨x, hx, hd⟩ := mem_nbhd.mp hy
  exact mem_nbhd.mpr ⟨x, hXY hx, hd.trans h⟩

section Facts

variable [NeZero n]

/-- **Lemma I.2.1 (b)**, iterated neighbourhoods: `(X^{∼a})^{∼b} = X^{∼(a+b)}`. -/
theorem nbhd_nbhd (a b : ℕ) (X : Set (Torus d n)) : nbhd b (nbhd a X) = nbhd (a + b) X := by
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, hzy⟩ := mem_nbhd.mp hz
    obtain ⟨x, hx, hyx⟩ := mem_nbhd.mp hy
    refine mem_nbhd.mpr ⟨x, hx, ?_⟩
    have := supDist_triangle z y x
    omega
  · intro hz
    obtain ⟨x, hx, hzx⟩ := mem_nbhd.mp hz
    obtain ⟨y, h1, h2⟩ := exists_split (x := x) (z := z) (a := a) (b := b)
      (by rw [supDist_comm]; exact hzx)
    exact mem_nbhd.mpr ⟨y, mem_nbhd.mpr ⟨x, hx, by rwa [supDist_comm]⟩, by rwa [supDist_comm]⟩

theorem thick2_eq (r : ℕ) (X : Set (Torus d n)) : thick2 r X = nbhd (2 * (r + 1)) X := by
  unfold thick2 thick
  rw [nbhd_nbhd]; congr 1; ring

/-- **Lemma I.2.1 (b)**, distance between a neighbourhood and a set. -/
theorem setDist_nbhd_ge {X Y : Set (Torus d n)} (a : ℕ) {k : ℕ}
    (h : ∀ x ∈ X, ∀ y ∈ Y, k ≤ supDist x y) :
    ∀ x ∈ nbhd a X, ∀ y ∈ Y, k ≤ supDist x y + a := by
  intro x hx y hy
  obtain ⟨x0, hx0, hxx0⟩ := mem_nbhd.mp hx
  have := supDist_triangle x0 x y
  have := h x0 hx0 y hy
  rw [supDist_comm x0 x] at *
  omega

end Facts

end Balaban.LargeField
