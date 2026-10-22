/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.BlockPoly

/-!
# Solving the cell Hamiltonian, and the block Hamiltonian on cell polynomials

The Green function of `-Δ + ν` on the circle `ZMod M` is `gamC M ν 1`
(`cellGreen` plus the zero mode `1/(Mν)`); `gamC M ν j` is its `j`-th convolution power.
For `w ≥ 0`, `ν > 0` the cell equation `cellH w ν F = S` has the explicit solution
`solC w ν S = Γ * S - w avg(S) / (ν (w + ν))` with `avg (solC S) = avg S / (w + ν)`.

With it, every cell-polynomial source `(S₂, S₁, S₀)` is solved by the triple `polySol`
(`polyZ_polySol`): `F₂ = solC S₂`, `F₁ = solC (S₁ + 2δ_{-1} F₂(·+1) - 2δ₀ F₂(·-1))`,
`F₀ = solC (S₀ + δ_{-1}(F₂+F₁)(·+1) + δ₀(F₂-F₁)(·-1))`.
-/

@[expose] public section

namespace Balaban.Flow

open Finset

variable {M : ℕ} [NeZero M]

/-- `cellGreen` together with its zero mode, as a function on `ℤ`. -/
noncomputable def gamR (M : ℕ) [NeZero M] (ν : ℝ) (j : ℕ) (k : ℤ) : ℝ :=
  cellGreen M ν j k + 1 / ((M : ℝ) * ν ^ j)

/-- The `j`-th power of the Green function of `-Δ + ν` on `ZMod M`. -/
noncomputable def gamC (M : ℕ) [NeZero M] (ν : ℝ) (j : ℕ) (r : ZMod M) : ℂ :=
  ((gamR M ν j (r.val : ℤ) : ℝ) : ℂ)

theorem gamC_cast (ν : ℝ) (j : ℕ) (k : ℤ) : gamC M ν j (k : ZMod M) = ((gamR M ν j k : ℝ) : ℂ) := by
  unfold gamC gamR
  have : cellGreen M ν j (((k : ZMod M).val : ℕ) : ℤ) = cellGreen M ν j k :=
    cellGreen_congr ν j (by simp)
  rw [this]

theorem gamR_step {ν : ℝ} (hν : 0 < ν) (j : ℕ) (k : ℤ) :
    (2 + ν) * gamR M ν (j + 1) k - gamR M ν (j + 1) (k + 1) - gamR M ν (j + 1) (k - 1) =
      gamR M ν j k := by
  have h1 := cellGreen_eq (M := M) hν.le j k
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have he : ν * (1 / ((M : ℝ) * ν ^ (j + 1))) = 1 / ((M : ℝ) * ν ^ j) := by
    have : ν ≠ 0 := hν.ne'
    field_simp
    ring
  unfold gamR
  linear_combination h1 + he

theorem gamC_step {ν : ℝ} (hν : 0 < ν) (j : ℕ) (r : ZMod M) :
    (2 + (ν : ℂ)) * gamC M ν (j + 1) r - gamC M ν (j + 1) (r + 1) - gamC M ν (j + 1) (r - 1) =
      gamC M ν j r := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : ZMod M) = r := ⟨(r.val : ℤ), by simp⟩
  have e1 : ((k : ZMod M) + 1) = ((k + 1 : ℤ) : ZMod M) := by push_cast; rfl
  have e2 : ((k : ZMod M) - 1) = ((k - 1 : ℤ) : ZMod M) := by push_cast; rfl
  rw [e1, e2, gamC_cast, gamC_cast, gamC_cast, gamC_cast]
  exact_mod_cast gamR_step hν j k

theorem gamC_zero {ν : ℝ} (r : ZMod M) :
    gamC M ν 0 r = if r = 0 then 1 else 0 := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : ZMod M) = r := ⟨(r.val : ℤ), by simp⟩
  rw [gamC_cast]
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  unfold gamR
  rw [cellGreen_zero]
  split_ifs <;> simp

/-- Convolution with `gamC M ν j`. -/
noncomputable def convC (ν : ℝ) (j : ℕ) (S : ZMod M → ℂ) (r : ZMod M) : ℂ :=
  ∑ s, gamC M ν j (r - s) * S s

theorem convC_step {ν : ℝ} (hν : 0 < ν) (j : ℕ) (S : ZMod M → ℂ) (r : ZMod M) :
    (2 + (ν : ℂ)) * convC ν (j + 1) S r - convC ν (j + 1) S (r + 1) - convC ν (j + 1) S (r - 1) =
      convC ν j S r := by
  unfold convC
  have e1 : ∀ s, (r + 1 - s) = (r - s) + 1 := fun s => by ring
  have e2 : ∀ s, (r - 1 - s) = (r - s) - 1 := fun s => by ring
  simp only [e1, e2, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← gamC_step hν j (r - s)]; ring

theorem convC_zero (ν : ℝ) (S : ZMod M → ℂ) (r : ZMod M) : convC ν 0 S r = S r := by
  unfold convC
  simp only [gamC_zero, sub_eq_zero]
  simp

theorem sum_gamC {ν : ℝ} (hν : 0 < ν) : ∑ r, gamC M ν 1 r = 1 / (ν : ℂ) := by
  have h : ∀ r : ZMod M, (2 + (ν : ℂ)) * gamC M ν 1 r - gamC M ν 1 (r + 1) - gamC M ν 1 (r - 1)
      = if r = 0 then 1 else 0 := fun r => by rw [gamC_step hν 0 r, gamC_zero]
  have hs : ∑ r : ZMod M, ((2 + (ν : ℂ)) * gamC M ν 1 r - gamC M ν 1 (r + 1) - gamC M ν 1 (r - 1))
      = ∑ r : ZMod M, (if r = 0 then (1 : ℂ) else 0) := Finset.sum_congr rfl fun r _ => h r
  have e1 : ∑ r : ZMod M, gamC M ν 1 (r + 1) = ∑ r, gamC M ν 1 r :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod M)) _ _ fun _ => rfl
  have e2 : ∑ r : ZMod M, gamC M ν 1 (r - 1) = ∑ r, gamC M ν 1 r :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod M)) _ _ fun _ => rfl
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2] at hs
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte] at hs
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  field_simp
  linear_combination hs

theorem cellAvg_convC {ν : ℝ} (hν : 0 < ν) (S : ZMod M → ℂ) :
    cellAvg (convC ν 1 S) = cellAvg S / ν := by
  unfold cellAvg convC
  rw [Finset.sum_comm]
  have : ∀ s : ZMod M, ∑ r, gamC M ν 1 (r - s) * S s = (1 / (ν : ℂ)) * S s := fun s => by
    rw [← Finset.sum_mul, ← sum_gamC (M := M) hν]
    congr 1
    exact Fintype.sum_equiv (Equiv.subRight s) _ _ fun _ => rfl
  simp only [this, ← Finset.mul_sum]
  ring

theorem cellAvg_const (c : ℂ) : cellAvg (fun _ : ZMod M => c) = c := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  unfold cellAvg
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

/-- The solution of `cellH w ν F = S`. -/
noncomputable def solC (w ν : ℝ) (S : ZMod M → ℂ) (r : ZMod M) : ℂ :=
  convC ν 1 S r - (w : ℂ) * cellAvg S / ((ν : ℂ) * ((w : ℂ) + ν))

theorem cellAvg_sub_const (F : ZMod M → ℂ) (c : ℂ) :
    cellAvg (fun r => F r - c) = cellAvg F - c := by
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  unfold cellAvg
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  field_simp

theorem cellAvg_solC {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) (S : ZMod M → ℂ) :
    cellAvg (solC w ν S) = cellAvg S / ((w : ℂ) + ν) := by
  unfold solC
  rw [cellAvg_sub_const, cellAvg_convC hν]
  have h1 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have h2 : ((w : ℂ) + ν) ≠ 0 := by exact_mod_cast (by positivity : (w : ℝ) + ν ≠ 0)
  field_simp
  ring

theorem cellH_solC {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) (S : ZMod M → ℂ) :
    cellH w ν (solC w ν S) = S := by
  funext r
  have h1 : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have h2 : ((w : ℂ) + ν) ≠ 0 := by exact_mod_cast (by positivity : (w : ℝ) + ν ≠ 0)
  have hc := convC_step hν 0 S r
  rw [convC_zero] at hc
  have ha := cellAvg_solC hw hν S
  unfold cellH
  rw [ha]
  simp only [solC]
  have hc' : 2 * convC ν 1 S r - convC ν 1 S (r + 1) - convC ν 1 S (r - 1) + ν * convC ν 1 S r
      = S r := by linear_combination hc
  have hK3 : (w : ℂ) * (cellAvg S / (w + ν)) = ν * ((w : ℂ) * cellAvg S / (ν * (w + ν))) := by
    field_simp
  generalize (w : ℂ) * cellAvg S / (ν * (w + ν)) = K at hK3 ⊢
  linear_combination hc' + hK3

end Balaban.Flow
