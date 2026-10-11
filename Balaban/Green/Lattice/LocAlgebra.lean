/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.Main
public import Balaban.Green.Lattice.LocCutoff

/-!
# Lemma Loc: representation and Leibniz identities on `ℤ^d`

* `negLap v`: the unit-spacing discrete Laplacian `-Δ¹ v`.
* `sum_kernel_negLap`: the adjoint identity `∑_z K(x-z) (-Δ v)(z) = ∑_w v(w) (-Δ K)(x-w)` for
  finitely supported `v`.
* `green_representation`, `green_diff_representation`: `v = C * (-Δ v)` and its discrete gradient.
* `negLap_mul_cutoff`: the discrete Leibniz formula `-Δ(χ u) = χ (-Δ u) + R`.
* `sum_kernel_remainder`: moving the remainder `R` onto the kernel.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

/-- The unit-spacing discrete Laplacian `-Δ¹ v (z) = ∑_μ (2 v(z) - v(z + e_μ) - v(z - e_μ))`. -/
def negLap (v : (Fin d → ℤ) → ℂ) (z : Fin d → ℤ) : ℂ :=
  ∑ μ : Fin d, (2 * v z - v (z + Pi.single μ 1) - v (z - Pi.single μ 1))

/-- Translating the summation variable is harmless for functions supported well inside `S`. -/
theorem sum_shift {S T : Finset (Fin d → ℤ)} (F : (Fin d → ℤ) → ℂ) (a : Fin d → ℤ)
    (hT : ∀ y, y ∉ T → F y = 0) (hTS : T ⊆ S) (hTa : ∀ y ∈ T, y - a ∈ S) :
    ∑ z ∈ S, F (z + a) = ∑ y ∈ S, F y := by
  have h1 : ∑ y ∈ S, F y = ∑ y ∈ T, F y :=
    (Finset.sum_subset hTS fun y _ hy => hT y hy).symm
  have h2 : ∑ z ∈ S, F (z + a) = ∑ z ∈ T.image (· - a), F (z + a) := by
    symm
    refine Finset.sum_subset ?_ ?_
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.1 hz
      exact hTa y hy
    · intro z _ hz
      apply hT
      intro hzT
      exact hz (Finset.mem_image.2 ⟨z + a, hzT, by simp⟩)
  rw [h2, h1, Finset.sum_image]
  · exact Finset.sum_congr rfl fun y _ => by simp
  · intro y _ y' _ h
    simpa using h

/-- The adjoint identity `∑_z K(x-z) (-Δ v)(z) = ∑_w v(w) (-Δ K)(x-w)`. -/
theorem sum_kernel_negLap {S T : Finset (Fin d → ℤ)} (K : (Fin d → ℤ) → ℂ) (x : Fin d → ℤ)
    (v : (Fin d → ℤ) → ℂ) (hv : ∀ y, y ∉ T → v y = 0) (hTS : T ⊆ S)
    (hTe : ∀ y ∈ T, ∀ μ : Fin d, y + Pi.single μ 1 ∈ S ∧ y - Pi.single μ 1 ∈ S) :
    ∑ z ∈ S, K (x - z) * negLap v z =
      ∑ w ∈ S, v w * ∑ μ : Fin d,
        (2 * K (x - w) - K (x - w + Pi.single μ 1) - K (x - w - Pi.single μ 1)) := by
  have hp : ∀ μ : Fin d, ∑ z ∈ S, K (x - z) *
      (2 * v z - v (z + Pi.single μ 1) - v (z - Pi.single μ 1)) =
      ∑ w ∈ S, v w * (2 * K (x - w) - K (x - w + Pi.single μ 1) - K (x - w - Pi.single μ 1)) := by
    intro μ
    have s1 : ∑ z ∈ S, K (x - z) * v (z + Pi.single μ 1) =
        ∑ w ∈ S, K (x - w + Pi.single μ 1) * v w := by
      have := sum_shift (S := S) (T := T) (fun w => K (x - w + Pi.single μ 1) * v w)
        (Pi.single μ 1) (fun y hy => by simp [hv y hy]) hTS (fun y hy => (hTe y hy μ).2)
      have e : ∀ z : Fin d → ℤ, x - (z + Pi.single μ 1) + Pi.single μ 1 = x - z :=
        fun z => by abel
      simpa only [e] using this
    have s2 : ∑ z ∈ S, K (x - z) * v (z - Pi.single μ 1) =
        ∑ w ∈ S, K (x - w - Pi.single μ 1) * v w := by
      have := sum_shift (S := S) (T := T) (fun w => K (x - w - Pi.single μ 1) * v w)
        (-Pi.single μ 1) (fun y hy => by simp [hv y hy]) hTS
        (fun y hy => by rw [sub_neg_eq_add]; exact (hTe y hy μ).1)
      have e : ∀ z : Fin d → ℤ, x - (z - Pi.single μ 1) - Pi.single μ 1 = x - z :=
        fun z => by abel
      have e' : ∀ z : Fin d → ℤ, z + -Pi.single μ 1 = z - Pi.single μ 1 :=
        fun z => by abel
      simpa only [e', e] using this
    calc ∑ z ∈ S, K (x - z) * (2 * v z - v (z + Pi.single μ 1) - v (z - Pi.single μ 1))
        = ∑ z ∈ S, (2 * (K (x - z) * v z) - K (x - z) * v (z + Pi.single μ 1) -
            K (x - z) * v (z - Pi.single μ 1)) := Finset.sum_congr rfl fun z _ => by ring
      _ = 2 * ∑ z ∈ S, K (x - z) * v z - ∑ z ∈ S, K (x - z) * v (z + Pi.single μ 1) -
            ∑ z ∈ S, K (x - z) * v (z - Pi.single μ 1) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = 2 * ∑ w ∈ S, K (x - w) * v w - ∑ w ∈ S, K (x - w + Pi.single μ 1) * v w -
            ∑ w ∈ S, K (x - w - Pi.single μ 1) * v w := by rw [s1, s2]
      _ = ∑ w ∈ S, (2 * (K (x - w) * v w) - K (x - w + Pi.single μ 1) * v w -
            K (x - w - Pi.single μ 1) * v w) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = _ := Finset.sum_congr rfl fun w _ => by ring
  calc ∑ z ∈ S, K (x - z) * negLap v z
      = ∑ z ∈ S, ∑ μ : Fin d, K (x - z) *
          (2 * v z - v (z + Pi.single μ 1) - v (z - Pi.single μ 1)) := by
        simp only [negLap, Finset.mul_sum]
    _ = ∑ μ : Fin d, ∑ z ∈ S, K (x - z) *
          (2 * v z - v (z + Pi.single μ 1) - v (z - Pi.single μ 1)) := Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ w ∈ S, v w *
          (2 * K (x - w) - K (x - w + Pi.single μ 1) - K (x - w - Pi.single μ 1)) :=
        Finset.sum_congr rfl fun μ _ => hp μ
    _ = ∑ w ∈ S, ∑ μ : Fin d, v w *
          (2 * K (x - w) - K (x - w + Pi.single μ 1) - K (x - w - Pi.single μ 1)) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]

/-- The Green's function representation `v(x) = ∑_z C(x-z) (-Δ v)(z)` for finitely supported `v`. -/
theorem green_representation (hd : 3 ≤ d) {S T : Finset (Fin d → ℤ)}
    (v : (Fin d → ℤ) → ℂ) (hv : ∀ y, y ∉ T → v y = 0) (hTS : T ⊆ S)
    (hTe : ∀ y ∈ T, ∀ μ : Fin d, y + Pi.single μ 1 ∈ S ∧ y - Pi.single μ 1 ∈ S)
    (x : Fin d → ℤ) (hx : x ∈ S) :
    ∑ z ∈ S, ((latticeGreen d (x - z) : ℝ) : ℂ) * negLap v z = v x := by
  rw [sum_kernel_negLap (fun y => ((latticeGreen d y : ℝ) : ℂ)) x v hv hTS hTe]
  have hin : ∀ w : Fin d → ℤ, ∑ μ : Fin d, (2 * ((latticeGreen d (x - w) : ℝ) : ℂ) -
      ((latticeGreen d (x - w + Pi.single μ 1) : ℝ) : ℂ) -
      ((latticeGreen d (x - w - Pi.single μ 1) : ℝ) : ℂ)) =
      if x = w then 1 else 0 := by
    intro w
    have h := latticeGreen_equation hd (x - w)
    have h' : ((∑ μ : Fin d, (2 * latticeGreen d (x - w) - latticeGreen d (x - w + Pi.single μ 1) -
        latticeGreen d (x - w - Pi.single μ 1)) : ℝ) : ℂ) =
        ((if x - w = 0 then 1 else 0 : ℝ) : ℂ) := by rw [h]
    push_cast at h'
    rw [h']
    split_ifs <;> simp_all [sub_eq_zero]
  simp only [hin]
  rw [Finset.sum_eq_single_of_mem x hx]
  · simp
  · intro w _ hw
    simp [Ne.symm hw]

/-- The discrete gradient of the representation:
`v(x + e_ν) - v(x) = ∑_z (C(x + e_ν - z) - C(x - z)) (-Δ v)(z)`. -/
theorem green_diff_representation (hd : 3 ≤ d) {S T : Finset (Fin d → ℤ)}
    (v : (Fin d → ℤ) → ℂ) (hv : ∀ y, y ∉ T → v y = 0) (hTS : T ⊆ S)
    (hTe : ∀ y ∈ T, ∀ μ : Fin d, y + Pi.single μ 1 ∈ S ∧ y - Pi.single μ 1 ∈ S)
    (x : Fin d → ℤ) (ν : Fin d) (hx : x ∈ S) (hx' : x + Pi.single ν 1 ∈ S) :
    ∑ z ∈ S, (((latticeGreen d (x - z + Pi.single ν 1) - latticeGreen d (x - z) : ℝ)) : ℂ) *
        negLap v z = v (x + Pi.single ν 1) - v x := by
  have key := sum_kernel_negLap
    (fun y => (((latticeGreen d (y + Pi.single ν 1) - latticeGreen d y : ℝ)) : ℂ)) x v hv hTS hTe
  have hE : ∀ y : Fin d → ℤ, ∑ μ : Fin d, (2 * ((latticeGreen d y : ℝ) : ℂ) -
      ((latticeGreen d (y + Pi.single μ 1) : ℝ) : ℂ) -
      ((latticeGreen d (y - Pi.single μ 1) : ℝ) : ℂ)) = if y = 0 then 1 else 0 := by
    intro y
    have h := latticeGreen_equation hd y
    have h' : ((∑ μ : Fin d, (2 * latticeGreen d y - latticeGreen d (y + Pi.single μ 1) -
        latticeGreen d (y - Pi.single μ 1)) : ℝ) : ℂ) = ((if y = 0 then 1 else 0 : ℝ) : ℂ) := by
      rw [h]
    push_cast at h'
    rw [h']
    split_ifs <;> simp
  have hin : ∀ w : Fin d → ℤ, ∑ μ : Fin d,
      (2 * (((latticeGreen d (x - w + Pi.single ν 1) - latticeGreen d (x - w) : ℝ)) : ℂ) -
      (((latticeGreen d (x - w + Pi.single μ 1 + Pi.single ν 1) -
        latticeGreen d (x - w + Pi.single μ 1) : ℝ)) : ℂ) -
      (((latticeGreen d (x - w - Pi.single μ 1 + Pi.single ν 1) -
        latticeGreen d (x - w - Pi.single μ 1) : ℝ)) : ℂ)) =
      (if x + Pi.single ν 1 = w then 1 else 0) - (if x = w then 1 else 0) := by
    intro w
    have h1 := hE (x - w + Pi.single ν 1)
    have h2 := hE (x - w)
    have e1 : ∀ μ : Fin d, x - w + Pi.single μ 1 + Pi.single ν 1 =
        x - w + Pi.single ν 1 + Pi.single μ 1 := fun μ => add_right_comm _ _ _
    have e2 : ∀ μ : Fin d, x - w - Pi.single μ 1 + Pi.single ν 1 =
        x - w + Pi.single ν 1 - Pi.single μ 1 := fun μ => by abel
    have : ∑ μ : Fin d,
      (2 * (((latticeGreen d (x - w + Pi.single ν 1) - latticeGreen d (x - w) : ℝ)) : ℂ) -
      (((latticeGreen d (x - w + Pi.single μ 1 + Pi.single ν 1) -
        latticeGreen d (x - w + Pi.single μ 1) : ℝ)) : ℂ) -
      (((latticeGreen d (x - w - Pi.single μ 1 + Pi.single ν 1) -
        latticeGreen d (x - w - Pi.single μ 1) : ℝ)) : ℂ)) =
      ∑ μ : Fin d, (2 * ((latticeGreen d (x - w + Pi.single ν 1) : ℝ) : ℂ) -
        ((latticeGreen d (x - w + Pi.single ν 1 + Pi.single μ 1) : ℝ) : ℂ) -
        ((latticeGreen d (x - w + Pi.single ν 1 - Pi.single μ 1) : ℝ) : ℂ)) -
      ∑ μ : Fin d, (2 * ((latticeGreen d (x - w) : ℝ) : ℂ) -
        ((latticeGreen d (x - w + Pi.single μ 1) : ℝ) : ℂ) -
        ((latticeGreen d (x - w - Pi.single μ 1) : ℝ) : ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      rw [e1, e2]
      push_cast
      ring
    rw [this, h1, h2]
    have c1 : (x - w + Pi.single ν 1 = 0) ↔ (x + Pi.single ν 1 = w) := by
      rw [← sub_eq_zero (a := x + Pi.single ν 1), add_sub_right_comm]
    have c2 : (x - w = 0) ↔ (x = w) := sub_eq_zero
    simp only [c1, c2]
  simp only [hin] at key
  rw [key]
  have s1 : ∑ w ∈ S, v w * ((if x + Pi.single ν 1 = w then (1 : ℂ) else 0) -
      (if x = w then 1 else 0)) = v (x + Pi.single ν 1) - v x := by
    simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq S (x + Pi.single ν 1), Finset.sum_ite_eq S x]
    simp [hx, hx']
  exact s1

/-- The remainder in the discrete Leibniz formula. -/
def cutoffRemainder (χ : (Fin d → ℤ) → ℝ) (u : (Fin d → ℤ) → ℂ) (z : Fin d → ℤ) : ℂ :=
  ∑ μ : Fin d, (((χ z - χ (z + Pi.single μ 1) : ℝ) : ℂ) * u (z + Pi.single μ 1) +
    ((χ z - χ (z - Pi.single μ 1) : ℝ) : ℂ) * u (z - Pi.single μ 1))

/-- The discrete Leibniz formula `-Δ(χ u) = χ (-Δ u) + R`. -/
theorem negLap_cutoff_mul (χ : (Fin d → ℤ) → ℝ) (u : (Fin d → ℤ) → ℂ) (z : Fin d → ℤ) :
    negLap (fun w => (χ w : ℂ) * u w) z = (χ z : ℂ) * negLap u z + cutoffRemainder χ u z := by
  unfold negLap cutoffRemainder
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  push_cast
  ring

/-- Moving the remainder onto the kernel (summation by parts without derivatives). -/
theorem sum_kernel_remainder {S T : Finset (Fin d → ℤ)} (K : (Fin d → ℤ) → ℝ) (x : Fin d → ℤ)
    (χ : (Fin d → ℤ) → ℝ) (u : (Fin d → ℤ) → ℂ)
    (hχ : ∀ w, w ∉ T → χ w = 0 ∧ ∀ μ : Fin d,
      χ (w + Pi.single μ 1) = 0 ∧ χ (w - Pi.single μ 1) = 0)
    (hTS : T ⊆ S)
    (hTe : ∀ y ∈ T, ∀ μ : Fin d, y + Pi.single μ 1 ∈ S ∧ y - Pi.single μ 1 ∈ S) :
    ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * cutoffRemainder χ u z =
      ∑ w ∈ S, u w * ∑ μ : Fin d,
        ((K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
          K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) : ℝ) : ℂ) := by
  have hp : ∀ μ : Fin d, ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) *
      (((χ z - χ (z + Pi.single μ 1) : ℝ) : ℂ) * u (z + Pi.single μ 1) +
        ((χ z - χ (z - Pi.single μ 1) : ℝ) : ℂ) * u (z - Pi.single μ 1)) =
      ∑ w ∈ S, u w * ((K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
          K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) : ℝ) : ℂ) := by
    intro μ
    have s1 : ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * (((χ z - χ (z + Pi.single μ 1) : ℝ) : ℂ) *
        u (z + Pi.single μ 1)) =
        ∑ w ∈ S, ((K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) : ℝ) : ℂ) * u w := by
      have := sum_shift (S := S) (T := T)
        (fun w => ((K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) : ℝ) : ℂ) * u w)
        (Pi.single μ 1)
        (fun y hy => by
          obtain ⟨h0, h1⟩ := hχ y hy
          simp [h0, (h1 μ).2])
        hTS (fun y hy => (hTe y hy μ).2)
      have e : ∀ z : Fin d → ℤ, x - (z + Pi.single μ 1) + Pi.single μ 1 = x - z :=
        fun z => by abel
      simp only [e, add_sub_cancel_right] at this
      rw [← this]
      refine Finset.sum_congr rfl fun z _ => ?_
      push_cast
      ring
    have s2 : ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) * (((χ z - χ (z - Pi.single μ 1) : ℝ) : ℂ) *
        u (z - Pi.single μ 1)) =
        ∑ w ∈ S, ((K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) : ℝ) : ℂ) * u w := by
      have := sum_shift (S := S) (T := T)
        (fun w => ((K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) : ℝ) : ℂ) * u w)
        (-Pi.single μ 1)
        (fun y hy => by
          obtain ⟨h0, h1⟩ := hχ y hy
          simp [h0, (h1 μ).1])
        hTS (fun y hy => by rw [sub_neg_eq_add]; exact (hTe y hy μ).1)
      have e' : ∀ z : Fin d → ℤ, z + -Pi.single μ 1 = z - Pi.single μ 1 :=
        fun z => by abel
      have e : ∀ z : Fin d → ℤ, x - (z - Pi.single μ 1) - Pi.single μ 1 = x - z :=
        fun z => by abel
      have e'' : ∀ z : Fin d → ℤ, z - Pi.single μ 1 + Pi.single μ 1 = z :=
        fun z => by abel
      simp only [e', e, e''] at this
      rw [← this]
      refine Finset.sum_congr rfl fun z _ => ?_
      push_cast
      ring
    calc _ = ∑ z ∈ S, (((K (x - z) : ℝ) : ℂ) * (((χ z - χ (z + Pi.single μ 1) : ℝ) : ℂ) *
            u (z + Pi.single μ 1)) + ((K (x - z) : ℝ) : ℂ) *
            (((χ z - χ (z - Pi.single μ 1) : ℝ) : ℂ) * u (z - Pi.single μ 1))) :=
          Finset.sum_congr rfl fun z _ => by ring
      _ = _ := by
          rw [Finset.sum_add_distrib, s1, s2, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun w _ => ?_
          push_cast
          ring
  unfold cutoffRemainder
  calc _ = ∑ z ∈ S, ∑ μ : Fin d, ((K (x - z) : ℝ) : ℂ) *
        (((χ z - χ (z + Pi.single μ 1) : ℝ) : ℂ) * u (z + Pi.single μ 1) +
        ((χ z - χ (z - Pi.single μ 1) : ℝ) : ℂ) * u (z - Pi.single μ 1)) := by
        simp only [Finset.mul_sum]
    _ = ∑ μ : Fin d, ∑ z ∈ S, ((K (x - z) : ℝ) : ℂ) *
        (((χ z - χ (z + Pi.single μ 1) : ℝ) : ℂ) * u (z + Pi.single μ 1) +
        ((χ z - χ (z - Pi.single μ 1) : ℝ) : ℂ) * u (z - Pi.single μ 1)) := Finset.sum_comm
    _ = ∑ μ : Fin d, ∑ w ∈ S, u w * ((K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
          K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) : ℝ) : ℂ) :=
        Finset.sum_congr rfl fun μ _ => hp μ
    _ = ∑ w ∈ S, ∑ μ : Fin d, u w * ((K (x - w + Pi.single μ 1) * (χ (w - Pi.single μ 1) - χ w) +
          K (x - w - Pi.single μ 1) * (χ (w + Pi.single μ 1) - χ w) : ℝ) : ℂ) := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun w _ => by rw [Finset.mul_sum]

end Balaban.LatticeGreen
