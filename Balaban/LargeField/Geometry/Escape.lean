module

public import Balaban.LargeField.Geometry.Lattice
public import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Paths to infinity in `ℤ^d`

Infinite nn paths that leave every finite set (`IsEscPath`), the property `JoinedToInf A y` of
being joined to infinity avoiding `A`, rays along a coordinate direction, and the facts that for
finite `A`:
* `JoinedToInf A y` iff the nn-component of `y` in `Aᶜ` is infinite (`joinedToInf_iff_infinite`);
* `JoinedToInf` is constant on nn-components of `Aᶜ` (`JoinedToInf.of_conn`);
* for `d ≥ 2` the complement of a box is nn-connected (`conn_shell`).
-/

@[expose] public section

namespace Balaban.LatticeGeom

open Function Filter

variable {d : ℕ}

/-- The cube `{x | ∀ i, |x i| ≤ R}`. -/
def box (R : ℤ) : Set (Pt d) := {x | ∀ i, |x i| ≤ R}

theorem box_finite (R : ℤ) : (box R : Set (Pt d)).Finite := by
  have : (box R : Set (Pt d)) = Set.pi Set.univ (fun _ => Set.Icc (-R) R) := by
    ext x
    simp only [box, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]
  rw [this]
  exact Set.Finite.pi (fun _ => Set.finite_Icc _ _)

theorem Set.Finite.subset_box {F : Set (Pt d)} (hF : F.Finite) : ∃ R : ℤ, F ⊆ box R := by
  obtain ⟨R, hR⟩ := (hF.image (fun x : Pt d => ∑ i, |x i|)).bddAbove
  refine ⟨R, fun x hx i => ?_⟩
  have h1 : |x i| ≤ ∑ k, |x k| :=
    Finset.single_le_sum (f := fun k => |x k|) (fun k _ => abs_nonneg _) (Finset.mem_univ i)
  exact h1.trans (hR ⟨x, hx, rfl⟩)

/-- An infinite nn path from `x` that leaves every finite set. -/
structure IsEscPath (x : Pt d) (p : ℕ → Pt d) : Prop where
  zero : p 0 = x
  step : ∀ n, NN (p n) (p (n + 1))
  esc : ∀ F : Set (Pt d), F.Finite → ∀ᶠ n in atTop, p n ∉ F

/-- `y` is joined to infinity avoiding `A`. -/
def JoinedToInf (A : Set (Pt d)) (y : Pt d) : Prop :=
  ∃ p, IsEscPath y p ∧ ∀ n, p n ∉ A

/-- The straight ray from `x` in direction `s • e_i`. -/
def ray (x : Pt d) (i : Fin d) (s : ℤ) (n : ℕ) : Pt d := Function.update x i (x i + s * n)

theorem ray_zero (x : Pt d) (i : Fin d) (s : ℤ) : ray x i s 0 = x := by
  simp [ray]

theorem ray_apply_self (x : Pt d) (i : Fin d) (s : ℤ) (n : ℕ) : ray x i s n i = x i + s * n := by
  simp [ray]

theorem ray_nn (x : Pt d) (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) (n : ℕ) :
    NN (ray x i s n) (ray x i s (n + 1)) := by
  refine ⟨i, ?_⟩
  rcases hs with rfl | rfl
  · left; ext l
    by_cases hl : l = i
    · subst hl; simp [ray]; ring
    · simp [ray, hl]
  · right; ext l
    by_cases hl : l = i
    · subst hl; simp [ray]; ring
    · simp [ray, hl]

theorem ray_esc (x : Pt d) (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) {F : Set (Pt d)}
    (hF : F.Finite) : ∀ᶠ n in atTop, ray x i s n ∉ F := by
  obtain ⟨R, hR⟩ := Set.Finite.subset_box hF
  rw [eventually_atTop]
  refine ⟨(x i).natAbs + R.toNat + 1, fun n hn hmem => ?_⟩
  have h := hR hmem i
  rw [ray_apply_self, abs_le] at h
  rcases hs with rfl | rfl <;> omega

theorem ray_isEscPath (x : Pt d) (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) :
    IsEscPath x (ray x i s) :=
  ⟨ray_zero x i s, ray_nn x i hs, fun _ hF => ray_esc x i hs hF⟩

/-- A ray whose `i`-th coordinate (times `s`) beyond every point of `T` avoids `T`. -/
theorem ray_not_mem (x : Pt d) (i : Fin d) {s : ℤ} (hs : s = 1 ∨ s = -1) {T : Set (Pt d)}
    (hT : ∀ w ∈ T, s * w i < s * x i) (n : ℕ) : ray x i s n ∉ T := by
  intro hmem
  have h := hT _ hmem
  rw [ray_apply_self] at h
  rcases hs with rfl | rfl <;> nlinarith [Nat.cast_nonneg (α := ℤ) n]

theorem IsEscPath.tail {x : Pt d} {p : ℕ → Pt d} (hp : IsEscPath x p) (n : ℕ) :
    IsEscPath (p n) (fun k => p (n + k)) :=
  ⟨by simp, fun k => by simpa [add_assoc] using hp.step (n + k), by
    intro F hF
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.esc F hF)
    exact eventually_atTop.mpr ⟨N, fun k hk => hN _ (by omega)⟩⟩

namespace JoinedToInf

variable {A : Set (Pt d)} {y z : Pt d}

theorem cons (hy : y ∉ A) (hn : NN y z) (h : JoinedToInf A z) : JoinedToInf A y := by
  obtain ⟨p, hp, hpA⟩ := h
  refine ⟨fun n => match n with | 0 => y | k + 1 => p k, ⟨rfl, ?_, ?_⟩, ?_⟩
  · intro n
    match n with
    | 0 => simpa [hp.zero] using hn
    | k + 1 => exact hp.step k
  · intro F hF
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.esc F hF)
    exact eventually_atTop.mpr ⟨N + 1, fun n hn => by
      match n, hn with
      | k + 1, hk => exact hN k (by omega)⟩
  · intro n
    match n with
    | 0 => exact hy
    | k + 1 => exact hpA k

theorem of_conn (h : Conn Aᶜ y z) (hz : JoinedToInf A z) : JoinedToInf A y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hz
  | head hab _ ih => exact ih |> cons hab.1 hab.2.2

theorem shift {p : ℕ → Pt d} (hp : IsEscPath y p) (hpA : ∀ n, p n ∉ A) (n : ℕ) :
    JoinedToInf A (p n) :=
  ⟨fun k => p (n + k), hp.tail n, fun _ => hpA _⟩

theorem not_mem (h : JoinedToInf A y) : y ∉ A := by
  obtain ⟨p, hp, hpA⟩ := h
  rw [← hp.zero]
  exact hpA 0

theorem conn_path {p : ℕ → Pt d} (hp : IsEscPath y p) (hpA : ∀ n, p n ∉ A) (n : ℕ) :
    Conn Aᶜ y (p n) := by
  induction n with
  | zero => rw [hp.zero]; exact Conn.refl _
  | succ n ih => exact ih.tail (hpA _) (hpA _) (hp.step n)

end JoinedToInf

/-- A point outside a box containing `A` is joined to infinity avoiding `A`. -/
theorem joinedToInf_of_far {A : Set (Pt d)} {R : ℤ} (hA : A ⊆ box R) {z : Pt d}
    (hz : z ∉ box R) : JoinedToInf A z := by
  have : ∃ i, R < |z i| := by
    by_contra h
    push Not at h
    exact hz h
  obtain ⟨i, hi⟩ := this
  have key : ∃ s : ℤ, (s = 1 ∨ s = -1) ∧ ∀ w ∈ box R, s * w i < s * z i := by
    rcases lt_abs.mp hi with h | h
    · refine ⟨1, Or.inl rfl, fun w hw => ?_⟩
      have := (abs_le.mp (hw i)).2; linarith
    · refine ⟨-1, Or.inr rfl, fun w hw => ?_⟩
      have := (abs_le.mp (hw i)).1; linarith
  obtain ⟨s, hs, hT⟩ := key
  exact ⟨ray z i s, ray_isEscPath z i hs, ray_not_mem z i hs (T := A) (fun w hw => hT w (hA hw))⟩

/-- For finite `A`, being joined to infinity is the same as having an infinite component. -/
theorem joinedToInf_iff_infinite {A : Set (Pt d)} (hA : A.Finite) {y : Pt d} :
    JoinedToInf A y ↔ {z | Conn Aᶜ y z}.Infinite := by
  constructor
  · rintro ⟨p, hp, hpA⟩ hfin
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hp.esc _ hfin)
    exact hN N le_rfl (JoinedToInf.conn_path hp hpA N)
  · intro hinf
    obtain ⟨R, hR⟩ := Set.Finite.subset_box hA
    have : ∃ z ∈ {z | Conn Aᶜ y z}, z ∉ box R := by
      by_contra h
      push Not at h
      exact hinf ((box_finite R).subset fun z hz => h z hz)
    obtain ⟨z, hz, hzR⟩ := this
    exact JoinedToInf.of_conn hz (joinedToInf_of_far hR hzR)

section Shell

variable {R : ℤ}

private theorem mem_shell {x : Pt d} (i : Fin d) (h : R < |x i|) : x ∈ (box R : Set (Pt d))ᶜ :=
  fun hx => absurd (hx i) (not_le.mpr h)

private theorem shell_clear (i : Fin d) :
    ∀ (J : Finset (Fin d)), i ∉ J → ∀ w : Pt d, R < |w i| →
      Conn (box R : Set (Pt d))ᶜ w (fun k => if k ∈ J then 0 else w k) := by
  classical
  intro J
  induction J using Finset.induction_on with
  | empty => intro _ w _; simpa using Conn.refl w
  | insert j J hj ih =>
    intro hiJ w hw
    have hij : i ≠ j := fun e => hiJ (e ▸ Finset.mem_insert_self _ _)
    have hiJ' : i ∉ J := fun h => hiJ (Finset.mem_insert_of_mem h)
    refine (ih hiJ' w hw).trans ?_
    have := Conn.update (S := (box R : Set (Pt d))ᶜ) j 0 (fun k => if k ∈ J then 0 else w k)
      (fun t _ => mem_shell i (by simpa [Function.update, hij, hiJ'] using hw))
    convert this using 1
    ext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [Function.update, hk]

private theorem shell_to_axis (hR : 0 ≤ R) {w : Pt d} {i : Fin d} (hw : R < |w i|) :
    ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧
      Conn (box R : Set (Pt d))ᶜ w (Pi.single i (σ * (R + 1))) := by
  classical
  have h1 := shell_clear (R := R) i (Finset.univ.erase i) (by simp) w hw
  have e : (fun k => if k ∈ Finset.univ.erase i then 0 else w k) = Pi.single i (w i) := by
    ext k
    by_cases hk : k = i
    · subst hk; simp
    · simp [hk]
  rw [e] at h1
  rcases lt_abs.mp hw with h | h
  · refine ⟨1, Or.inl rfl, h1.trans ?_⟩
    have := Conn.update (S := (box R : Set (Pt d))ᶜ) i (R + 1) (Pi.single i (w i)) (fun t ht => by
      apply mem_shell i
      rw [Set.mem_uIcc] at ht
      simp only [Function.update_self, Pi.single_eq_same] at ht ⊢
      rw [abs_of_pos (by omega)]
      omega)
    convert this using 1
    ext k; by_cases hk : k = i <;> simp [hk]
  · refine ⟨-1, Or.inr rfl, h1.trans ?_⟩
    have := Conn.update (S := (box R : Set (Pt d))ᶜ) i (-(R + 1)) (Pi.single i (w i)) (fun t ht => by
      apply mem_shell i
      rw [Set.mem_uIcc] at ht
      simp only [Function.update_self, Pi.single_eq_same] at ht ⊢
      rw [abs_of_neg (by omega)]
      omega)
    convert this using 1
    ext k; by_cases hk : k = i <;> simp [hk]

private theorem abs_axis (hR : 0 ≤ R) {σ : ℤ} (hσ : σ = 1 ∨ σ = -1) : |σ * (R + 1)| = R + 1 := by
  rcases hσ with rfl | rfl
  · simp [abs_of_nonneg (by omega : (0 : ℤ) ≤ R + 1)]
  · rw [neg_one_mul, abs_neg, abs_of_nonneg (by omega : (0 : ℤ) ≤ R + 1)]

private theorem shell_shift (hR : 0 ≤ R) {i j : Fin d} (hij : i ≠ j) {σ : ℤ}
    (hσ : σ = 1 ∨ σ = -1) :
    Conn (box R : Set (Pt d))ᶜ (Pi.single i (σ * (R + 1))) (Pi.single j (R + 1)) := by
  have hv := abs_axis hR hσ
  have h1 := Conn.update (S := (box R : Set (Pt d))ᶜ) j (R + 1) (Pi.single i (σ * (R + 1)))
    (fun t _ => mem_shell i (by
      rw [Function.update_of_ne hij, Pi.single_eq_same, hv]; omega))
  refine h1.trans ?_
  have h2 := Conn.update (S := (box R : Set (Pt d))ᶜ) i 0
    (Function.update (Pi.single i (σ * (R + 1))) j (R + 1))
    (fun t _ => mem_shell j (by
      rw [Function.update_of_ne hij.symm, Function.update_self,
        abs_of_nonneg (by omega : (0 : ℤ) ≤ R + 1)]
      omega))
  convert h2 using 1
  ext k
  by_cases hk : k = i
  · subst hk; simp [Function.update, hij]
  · by_cases hkj : k = j
    · subst hkj; simp [Function.update, hk]
    · simp [Function.update, hk, hkj]

/-- For `d ≥ 2` the complement of a cube is nn-connected. -/
theorem conn_shell (hd : 2 ≤ d) (hR : 0 ≤ R) {x y : Pt d} (hx : x ∉ box R) (hy : y ∉ box R) :
    Conn (box R : Set (Pt d))ᶜ x y := by
  let i0 : Fin d := ⟨0, by omega⟩
  let j0 : Fin d := ⟨1, by omega⟩
  have hij : i0 ≠ j0 := by simp [i0, j0, Fin.ext_iff]
  have toBase : ∀ z : Pt d, z ∉ box R →
      Conn (box R : Set (Pt d))ᶜ z (Pi.single i0 (R + 1)) := by
    intro z hz
    obtain ⟨i, hi⟩ : ∃ i, R < |z i| := by
      by_contra h; push Not at h; exact hz h
    obtain ⟨σ, hσ, hz1⟩ := shell_to_axis hR hi
    refine hz1.trans ?_
    by_cases hii : i = i0
    · subst hii
      rcases hσ with rfl | rfl
      · simp [Conn.refl]
      · exact (shell_shift hR hij (σ := -1) (Or.inr rfl)).trans
          (by simpa using shell_shift hR hij.symm (σ := 1) (Or.inl rfl))
    · exact shell_shift hR hii hσ
  exact (toBase x hx).trans (toBase y hy).symm

end Shell

end Balaban.LatticeGeom
