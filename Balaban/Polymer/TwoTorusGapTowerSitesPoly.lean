/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Polymer.TwoTorusGapTowerSitesCell

/-!
# Fine polymers in the quarter box do not depend on the torus (blocker 7)

For a finite set `A ⊂ ℤ^d` of fine sites in the quarter box shrunk by one block,
`4 (|y_μ| + D) < D K`, the image of `A` in `ℤ/(D K)` is a polymer of blocks of side `D`
(`Balaban.IsPolymer`) exactly when `A` is a nonempty union of blocks `{y | y / D = c}` that is
connected for the nearest-neighbour adjacency of `ℤ^d` (`isPolymer_image_cast_iff`).  The right side
does not mention the torus, so the polymer property of the image is the same on every torus
containing the box (`isPolymer_image_cast_iff_of_box`).
-/

@[expose] public section

namespace Balaban.Polymer.TwoTorusStep

open Balaban Balaban.Polymer

section Poly

variable {d D K : ℕ}

theorem cast_inj {n : ℕ} {z w : ℤ} (hz : 2 * |z| < n) (hw : 2 * |w| < n)
    (h : ((z : ℤ) : ZMod n) = ((w : ℤ) : ZMod n)) : z = w := by
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at h
  have h0 := Int.eq_zero_of_abs_lt_dvd h (by
    have := abs_sub w z
    omega)
  omega

theorem abs_lt_of_ediv_eq (hD : 0 < D) {z w : ℤ} (h : z / (D : ℤ) = w / (D : ℤ)) :
    |w| < |z| + D := by
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  have h1 := Int.mul_ediv_self_le (x := z) hDz.ne'
  have h2 := Int.lt_mul_ediv_self_add (x := z) hDz
  have h3 := Int.mul_ediv_self_le (x := w) hDz.ne'
  have h4 := Int.lt_mul_ediv_self_add (x := w) hDz
  rw [← h] at h3 h4
  have : |w - z| < D := abs_lt.2 ⟨by linarith, by linarith⟩
  have := abs_sub_abs_le_abs_sub w z
  linarith

theorem cast_add_single {n : ℕ} (y : Fin d → ℤ) (μ : Fin d) :
    (fun ν => ((((y + Pi.single μ 1 : Fin d → ℤ) ν : ℤ)) : ZMod n)) =
      (fun ν => ((y ν : ℤ) : ZMod n)) + Pi.single μ 1 := by
  funext ν
  by_cases hν : ν = μ <;> simp [hν]

/-- A fine point of the box lies in a block whose points are all in the box. -/
theorem box_of_ediv_eq (hD : 0 < D) {n : ℕ} {z w : ℤ} (h : z / (D : ℤ) = w / (D : ℤ))
    (hz : 4 * (|z| + D) < n) : 4 * |w| < n := by
  have := abs_lt_of_ediv_eq hD h
  omega

theorem eq_add_single_of_cast {n : ℕ} {y y2 : Fin d → ℤ} {μ : Fin d}
    (h : ∀ ν, 2 * |y ν| + 2 < n) (h2 : ∀ ν, 2 * |y2 ν| < n)
    (he : (fun ν => ((y2 ν : ℤ) : ZMod n)) = (fun ν => ((y ν : ℤ) : ZMod n)) + Pi.single μ 1) :
    y2 = y + Pi.single μ 1 := by
  funext ν
  refine cast_inj (h2 ν) ?_ ((congrFun he ν).trans (congrFun (cast_add_single y μ) ν).symm)
  have := h ν
  by_cases hν : ν = μ
  · subst hν
    have : |y ν + 1| ≤ |y ν| + 1 := by simpa using abs_add_le (y ν) 1
    simp only [Pi.add_apply, Pi.single_eq_same]
    omega
  · simp only [Pi.add_apply, Pi.single_eq_of_ne hν, add_zero]
    omega

theorem eq_add_single_of_cast' {n : ℕ} {y y2 : Fin d → ℤ} {μ : Fin d}
    (h : ∀ ν, 2 * |y2 ν| + 2 < n) (h2 : ∀ ν, 2 * |y ν| < n)
    (he : (fun ν => ((y ν : ℤ) : ZMod n)) = (fun ν => ((y2 ν : ℤ) : ZMod n)) + Pi.single μ 1) :
    y = y2 + Pi.single μ 1 :=
  eq_add_single_of_cast h h2 he

theorem isPolymer_fwd {n : ℕ} [NeZero n] (hn : n = D * K) (A : Finset (Fin d → ℤ))
    (hA : ∀ y ∈ A, ∀ μ, 4 * (|y μ| + D) < n)
    (h : IsPolymer d n D (A.image fun y μ => ((y μ : ℤ) : ZMod n))) :
    A.Nonempty ∧ (∀ y ∈ A, ∀ y' : Fin d → ℤ, (∀ μ, y μ / (D : ℤ) = y' μ / (D : ℤ)) → y' ∈ A) ∧
      ∀ y ∈ A, ∀ y' ∈ A, Relation.ReflTransGen
        (fun a b => a ∈ A ∧ b ∈ A ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        y y' := by
  classical
  have hD : 0 < D := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hn ▸ NeZero.ne n))
  have hK : 0 < K := Nat.pos_of_ne_zero (right_ne_zero_of_mul (hn ▸ NeZero.ne n))
  obtain ⟨hne, hsat, hconn⟩ := h
  have hbox1 : ∀ y ∈ A, ∀ μ, 2 * |y μ| + 2 < n := fun y hy μ => by
    have := hA y hy μ; omega
  have hbox2 : ∀ y ∈ A, ∀ μ, 2 * |y μ| < n := fun y hy μ => by
    have := hA y hy μ; omega
  have hinj : ∀ y ∈ A, ∀ y'' ∈ A, (fun μ => ((y μ : ℤ) : ZMod n)) =
      (fun μ => ((y'' μ : ℤ) : ZMod n)) → y = y'' := by
    intro y hy y'' hy'' he
    funext μ
    exact cast_inj (hbox2 y hy μ) (hbox2 y'' hy'' μ) (congrFun he μ)
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨y, hy, -⟩ := Finset.mem_image.1 hx
    exact ⟨y, hy⟩
  · intro y hy y' hyy'
    have hx : (fun μ => ((y μ : ℤ) : ZMod n)) ∈
        A.image fun y μ => ((y μ : ℤ) : ZMod n) := Finset.mem_image_of_mem _ hy
    have := hsat _ hx (fun μ => ((y' μ : ℤ) : ZMod n)) (fun μ => by
      have e1 := val_div_cast_int hn hD hK (y μ)
      have e2 := val_div_cast_int hn hD hK (y' μ)
      rw [hyy' μ] at e1
      exact_mod_cast e1.trans e2.symm)
    obtain ⟨y'', hy'', he⟩ := Finset.mem_image.1 this
    have : y'' = y' := by
      funext μ
      refine cast_inj (hbox2 y'' hy'' μ) ?_ (congrFun he μ)
      have h1 := box_of_ediv_eq hD (hyy' μ) (hA y hy μ)
      omega
    rwa [← this]
  · intro y0 hy0 y1 hy1
    have key : ∀ w, Relation.ReflTransGen (fun a b => a ∈ A.image (fun y μ =>
        ((y μ : ℤ) : ZMod n)) ∧ b ∈ A.image (fun y μ => ((y μ : ℤ) : ZMod n)) ∧
        ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        (fun μ => ((y0 μ : ℤ) : ZMod n)) w →
        ∃ y ∈ A, (fun μ => ((y μ : ℤ) : ZMod n)) = w ∧ Relation.ReflTransGen
          (fun a b => a ∈ A ∧ b ∈ A ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨
            a = b + Pi.single μ 1) y0 y := by
      intro w hw
      induction hw with
      | refl => exact ⟨y0, hy0, rfl, Relation.ReflTransGen.refl⟩
      | tail _ hstep ih =>
        obtain ⟨y, hy, rfl, hpath⟩ := ih
        obtain ⟨-, hb, μ, hμ⟩ := hstep
        obtain ⟨y2, hy2, rfl⟩ := Finset.mem_image.1 hb
        rcases hμ with hμ | hμ
        · have e := eq_add_single_of_cast (hbox1 y hy) (hbox2 y2 hy2) hμ
          exact ⟨y2, hy2, rfl, hpath.tail ⟨hy, hy2, μ, Or.inl e⟩⟩
        · have e := eq_add_single_of_cast' (hbox1 y2 hy2) (hbox2 y hy) hμ
          exact ⟨y2, hy2, rfl, hpath.tail ⟨hy, hy2, μ, Or.inr e⟩⟩
    obtain ⟨y, hy, he, hp⟩ := key _ (hconn _ (Finset.mem_image_of_mem _ hy0) _
      (Finset.mem_image_of_mem _ hy1))
    have : y = y1 := hinj y hy y1 hy1 he
    rwa [this] at hp

theorem isPolymer_bwd {n : ℕ} [NeZero n] (hn : n = D * K) (A : Finset (Fin d → ℤ))
    (h : A.Nonempty ∧
      (∀ y ∈ A, ∀ y' : Fin d → ℤ, (∀ μ, y μ / (D : ℤ) = y' μ / (D : ℤ)) → y' ∈ A) ∧
      ∀ y ∈ A, ∀ y' ∈ A, Relation.ReflTransGen
        (fun a b => a ∈ A ∧ b ∈ A ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨ a = b + Pi.single μ 1)
        y y') :
    IsPolymer d n D (A.image fun y μ => ((y μ : ℤ) : ZMod n)) := by
  classical
  have hD : 0 < D := Nat.pos_of_ne_zero (left_ne_zero_of_mul (hn ▸ NeZero.ne n))
  have hDz : (0 : ℤ) < D := by exact_mod_cast hD
  obtain ⟨hne, hsat, hconn⟩ := h
  refine ⟨hne.image _, ?_, ?_⟩
  · intro x hx z hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    let y' : Fin d → ℤ := fun μ => y μ - ((((y μ : ℤ) : ZMod n).val % D : ℕ) : ℤ) +
      (((z μ).val % D : ℕ) : ℤ)
    have hy'1 : ∀ μ, y μ / (D : ℤ) = y' μ / (D : ℤ) := by
      intro μ
      have e1 : ((((y μ : ℤ) : ZMod n).val % D : ℕ) : ℤ) = y μ % (D : ℤ) := by
        rw [Int.natCast_mod, ZMod.val_intCast]
        exact Int.emod_emod_of_dvd _ ⟨(K : ℤ), by rw [hn]; push_cast; rfl⟩
      have e2 : y' μ = (D : ℤ) * (y μ / (D : ℤ)) + (((z μ).val % D : ℕ) : ℤ) := by
        show y μ - _ + _ = _
        rw [e1]
        have := Int.mul_ediv_add_emod (y μ) D
        linarith
      rw [e2, Int.mul_add_ediv_left _ _ hDz.ne']
      have h0 : 0 ≤ (((z μ).val % D : ℕ) : ℤ) := by positivity
      have h1 : (((z μ).val % D : ℕ) : ℤ) < D := by exact_mod_cast Nat.mod_lt _ hD
      rw [Int.ediv_eq_zero_of_lt h0 h1]; ring
    have hy' := hsat y hy y' hy'1
    refine Finset.mem_image.2 ⟨y', hy', ?_⟩
    funext μ
    have hq : (((z μ).val / D : ℕ) : ZMod n) =
        ((((y μ : ℤ) : ZMod n).val / D : ℕ) : ZMod n) := by
      rw [hz μ]
    have hzc : z μ = (D : ZMod n) * (((z μ).val / D : ℕ) : ZMod n) +
        (((z μ).val % D : ℕ) : ZMod n) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (z μ), ← Nat.div_add_mod (z μ).val D]
      push_cast; ring
    have hxc : ((y μ : ℤ) : ZMod n) = (D : ZMod n) *
        ((((y μ : ℤ) : ZMod n).val / D : ℕ) : ZMod n) +
        ((((y μ : ℤ) : ZMod n).val % D : ℕ) : ZMod n) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val ((y μ : ℤ) : ZMod n),
        ← Nat.div_add_mod ((y μ : ℤ) : ZMod n).val D]
      push_cast; ring
    show ((y' μ : ℤ) : ZMod n) = z μ
    show (((y μ - ((((y μ : ℤ) : ZMod n).val % D : ℕ) : ℤ) +
      (((z μ).val % D : ℕ) : ℤ) : ℤ)) : ZMod n) = z μ
    simp only [Int.cast_add, Int.cast_sub, Int.cast_natCast]
    linear_combination (-1 : ZMod n) * hzc - (D : ZMod n) * hq + hxc
  · intro x hx x' hx'
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨y', hy', rfl⟩ := Finset.mem_image.1 hx'
    refine Relation.ReflTransGen.lift (fun y μ => ((y μ : ℤ) : ZMod n))
      (r := fun a b => a ∈ A ∧ b ∈ A ∧ ∃ μ : Fin d, b = a + Pi.single μ 1 ∨
        a = b + Pi.single μ 1) ?_ y y' (hconn y hy y' hy')
    rintro a b ⟨ha, hb, μ, hμ | hμ⟩
    · refine ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, μ, Or.inl ?_⟩
      rw [hμ]; exact cast_add_single a μ
    · refine ⟨Finset.mem_image_of_mem _ ha, Finset.mem_image_of_mem _ hb, μ, Or.inr ?_⟩
      rw [hμ]; exact cast_add_single b μ

/-- The image in `ℤ/n` of a finite set of fine sites in the shrunk quarter box is a polymer of
blocks of side `D` iff the image in `ℤ/n'` is, for any two tori `n = D K`, `n' = D K'` containing the
box. -/
theorem isPolymer_image_cast_iff_of_box {n n' K' : ℕ} [NeZero n] [NeZero n'] (hn : n = D * K)
    (hn' : n' = D * K') (A : Finset (Fin d → ℤ)) (hA : ∀ y ∈ A, ∀ μ, 4 * (|y μ| + D) < n)
    (hA' : ∀ y ∈ A, ∀ μ, 4 * (|y μ| + D) < n') :
    IsPolymer d n D (A.image fun y μ => ((y μ : ℤ) : ZMod n)) ↔
      IsPolymer d n' D (A.image fun y μ => ((y μ : ℤ) : ZMod n')) :=
  ⟨fun h => isPolymer_bwd hn' A (isPolymer_fwd hn A hA h),
    fun h => isPolymer_bwd hn A (isPolymer_fwd hn' A hA' h)⟩

end Poly


end Balaban.Polymer.TwoTorusStep
