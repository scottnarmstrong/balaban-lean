/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormDefs

/-!
# Lattice differences: path and Taylor estimates

For a field `ψ : ℤ^d → ℂ^N` with `‖ψ(y + e_μ) - ψ(y)‖ ≤ δ` (first differences) and
`‖∂_ν ψ(y + e_μ) - ∂_ν ψ(y)‖ ≤ K` (second differences):

* `norm_sub_le_l1`: `‖ψ(y + z) - ψ(y)‖ ≤ |z|₁ δ`;
* `norm_taylor_le`: `‖ψ(y + z) - ψ(y) - Σ_μ z_μ ∂_μψ(y)‖ ≤ |z|₁² K`.
-/

@[expose] public section

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The `ℓ¹` norm of a lattice point. -/
def l1 (z : Site d) : ℕ := ∑ μ, (z μ).natAbs

/-- The unit vector of the lattice. -/
def eU (μ : Fin d) : Site d := Pi.single μ 1

/-- The forward difference `∂_μ ψ(y) = ψ(y + e_μ) - ψ(y)`. -/
def fdiff (ψ : Site d → Spin N) (μ : Fin d) (y : Site d) : Spin N := ψ (y + eU μ) - ψ y

theorem l1_zero : l1 (0 : Site d) = 0 := by simp [l1]

theorem exists_step (z : Site d) (hz : z ≠ 0) :
    ∃ (μ : Fin d) (s : ℤ), (s = 1 ∨ s = -1) ∧ l1 (z - s • eU μ) + 1 = l1 z := by
  obtain ⟨μ, hμ⟩ : ∃ μ, z μ ≠ 0 := by
    by_contra h; exact hz (funext fun μ => by_contra fun h' => h ⟨μ, h'⟩)
  set sg : ℤ := if 0 < z μ then 1 else -1 with hsg
  have hsg1 : sg = 1 ∨ sg = -1 := by
    by_cases h : 0 < z μ <;> simp [hsg, h]
  refine ⟨μ, sg, hsg1, ?_⟩
  · unfold l1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ μ), ← Finset.add_sum_erase _ (fun ν => (z ν).natAbs) (Finset.mem_univ μ)]
    have h1 : ∀ ν ∈ Finset.univ.erase μ, ((z - sg • eU μ) ν).natAbs = (z ν).natAbs := by
      intro ν hν
      have : ν ≠ μ := Finset.ne_of_mem_erase hν
      simp [eU, this]
    rw [Finset.sum_congr rfl h1]
    have h2 : ((z - sg • eU μ) μ).natAbs + 1 = (z μ).natAbs := by
      simp only [eU, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      by_cases h : 0 < z μ
      · simp only [hsg, h, ite_true]; omega
      · have : z μ < 0 := lt_of_le_of_ne (not_lt.mp h) hμ
        simp only [hsg, h, ite_false]; omega
    omega

theorem l1_add_unit_le (z : Site d) (μ : Fin d) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    l1 (z + s • eU μ) ≤ l1 z + 1 := by
  unfold l1
  have : ∀ ν, ((z + s • eU μ) ν).natAbs ≤ (z ν).natAbs + (if ν = μ then 1 else 0) := by
    intro ν
    by_cases h : ν = μ
    · subst h; rcases hs with rfl | rfl <;> simp [eU] <;> omega
    · simp [eU, h]
  calc ∑ ν, ((z + s • eU μ) ν).natAbs ≤ ∑ ν, ((z ν).natAbs + (if ν = μ then 1 else 0)) :=
        Finset.sum_le_sum fun ν _ => this ν
    _ = _ := by simp [Finset.sum_add_distrib]

/-- Path estimate for a field with bounded first differences. -/
theorem norm_sub_le_l1 {ψ : Site d → Spin N} {δ : ℝ}
    (h : ∀ y μ, ‖ψ (y + eU μ) - ψ y‖ ≤ δ) (y z : Site d) :
    ‖ψ (y + z) - ψ y‖ ≤ (l1 z : ℝ) * δ := by
  suffices H : ∀ n, ∀ z : Site d, l1 z = n → ‖ψ (y + z) - ψ y‖ ≤ (l1 z : ℝ) * δ from H _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn
  by_cases hz : z = 0
  · subst hz; simp [l1_zero]
  obtain ⟨μ, s, hs, hl⟩ := exists_step z hz
  set z' := z - s • eU μ with hz'
  have hzz : z = z' + s • eU μ := by simp [hz']
  have h1 : ‖ψ (y + z') - ψ y‖ ≤ (l1 z' : ℝ) * δ := ih (l1 z') (by omega) z' rfl
  have h2 : ‖ψ (y + z) - ψ (y + z')‖ ≤ δ := by
    rcases hs with rfl | rfl
    · have := h (y + z') μ
      have e : y + z = y + z' + eU μ := by rw [hzz]; simp [add_assoc]
      rw [e]; simpa using this
    · have := h (y + z) μ
      have e : y + z' = y + z + eU μ := by
        rw [hzz]; simp [hz', eU]; abel
      rw [e, norm_sub_rev]; simpa using this
  have hl' : (l1 z : ℝ) = l1 z' + 1 := by exact_mod_cast hl.symm
  have hδ : 0 ≤ δ := le_trans (norm_nonneg _) (h 0 μ)
  calc ‖ψ (y + z) - ψ y‖ = ‖(ψ (y + z) - ψ (y + z')) + (ψ (y + z') - ψ y)‖ := by ring_nf
    _ ≤ δ + (l1 z' : ℝ) * δ := (norm_add_le _ _).trans (add_le_add h2 h1)
    _ = (l1 z : ℝ) * δ := by rw [hl']; ring

theorem sum_unit (g : Fin d → Spin N) (z : Site d) (μ : Fin d) (s : ℤ) :
    ∑ ν, (((z + s • eU μ) ν : ℤ) : ℂ) • g ν = ∑ ν, ((z ν : ℤ) : ℂ) • g ν + (s : ℂ) • g μ := by
  have : ∀ ν, (((z + s • eU μ) ν : ℤ) : ℂ) • g ν =
      ((z ν : ℤ) : ℂ) • g ν + (if ν = μ then (s : ℂ) • g μ else 0) := by
    intro ν
    by_cases h : ν = μ
    · subst h; simp [eU, add_smul]
    · simp [eU, h]
  simp only [this, Finset.sum_add_distrib]
  simp

/-- Second-order Taylor estimate on the lattice. -/
theorem norm_taylor_le {ψ : Site d → Spin N} {K : ℝ}
    (h2 : ∀ y μ ν, ‖fdiff ψ ν (y + eU μ) - fdiff ψ ν y‖ ≤ K) (y z : Site d) :
    ‖ψ (y + z) - ψ y - ∑ μ, ((z μ : ℤ) : ℂ) • fdiff ψ μ y‖ ≤ ((l1 z : ℝ)) ^ 2 * K := by
  have hgrad : ∀ ν (w : Site d), ‖fdiff ψ ν (y + w) - fdiff ψ ν y‖ ≤ (l1 w : ℝ) * K := fun ν w =>
    norm_sub_le_l1 (ψ := fdiff ψ ν) (δ := K) (fun y' μ => h2 y' μ ν) y w
  suffices H : ∀ n, ∀ z : Site d, l1 z = n →
      ‖ψ (y + z) - ψ y - ∑ μ, ((z μ : ℤ) : ℂ) • fdiff ψ μ y‖ ≤ ((l1 z : ℝ)) ^ 2 * K from
    H _ z rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro z hn
  by_cases hz : z = 0
  · subst hz; simp [l1_zero]
  obtain ⟨μ, s, hs, hl⟩ := exists_step z hz
  set z' := z - s • eU μ with hz'
  have hzz : z = z' + s • eU μ := by simp [hz']
  have hK : 0 ≤ K := le_trans (norm_nonneg _) (h2 0 μ μ)
  have h1 := ih (l1 z') (by omega) z' rfl
  have hl' : (l1 z : ℝ) = l1 z' + 1 := by exact_mod_cast hl.symm
  have hz'0 : (0 : ℝ) ≤ l1 z' := Nat.cast_nonneg _
  have hdiff : ‖(ψ (y + z) - ψ y - ∑ ν, ((z ν : ℤ) : ℂ) • fdiff ψ ν y) -
      (ψ (y + z') - ψ y - ∑ ν, ((z' ν : ℤ) : ℂ) • fdiff ψ ν y)‖ ≤ (l1 z : ℝ) * K := by
    have e : (ψ (y + z) - ψ y - ∑ ν, ((z ν : ℤ) : ℂ) • fdiff ψ ν y) -
        (ψ (y + z') - ψ y - ∑ ν, ((z' ν : ℤ) : ℂ) • fdiff ψ ν y) =
        (ψ (y + z) - ψ (y + z')) - (s : ℂ) • fdiff ψ μ y := by
      conv_lhs => rw [hzz, sum_unit]
      rw [← hzz]; abel
    rw [e]
    rcases hs with rfl | rfl
    · have : (ψ (y + z) - ψ (y + z')) - ((1 : ℤ) : ℂ) • fdiff ψ μ y =
          fdiff ψ μ (y + z') - fdiff ψ μ y := by
        have e2 : y + z = y + z' + eU μ := by rw [hzz]; simp [add_assoc]
        simp only [fdiff, e2]; simp
      rw [this]
      refine (hgrad μ z').trans ?_
      rw [hl']; nlinarith
    · have : (ψ (y + z) - ψ (y + z')) - ((-1 : ℤ) : ℂ) • fdiff ψ μ y =
          -(fdiff ψ μ (y + z) - fdiff ψ μ y) := by
        have e2 : y + z' = y + z + eU μ := by rw [hzz]; simp [eU]; abel
        simp only [fdiff, e2]; simp; abel
      rw [this, norm_neg]
      exact hgrad μ z
  calc _ = ‖(ψ (y + z') - ψ y - ∑ ν, ((z' ν : ℤ) : ℂ) • fdiff ψ ν y) +
        ((ψ (y + z) - ψ y - ∑ ν, ((z ν : ℤ) : ℂ) • fdiff ψ ν y) -
          (ψ (y + z') - ψ y - ∑ ν, ((z' ν : ℤ) : ℂ) • fdiff ψ ν y))‖ := by ring_nf
    _ ≤ ((l1 z' : ℝ)) ^ 2 * K + (l1 z : ℝ) * K := (norm_add_le _ _).trans (add_le_add h1 hdiff)
    _ ≤ ((l1 z : ℝ)) ^ 2 * K := by
        rw [hl']; nlinarith [mul_nonneg hz'0 hK]

end Balaban.SmallField
