/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.CellSolve

/-!
# Cell solutions for the first two Green iterates of a block-constant quadratic source

Let `H = -Δ + wP + ν` be the block Hamiltonian on `ℤ`.  The solution `Φ` of `H Φ = x²` (`x` the block
index) and then of `H Ψ = Φ` are cell polynomials `polyZ F₂ F₁ F₀` (`polyZ_solved`).  Their constant
cell coefficients are `Φ₂ = c`, `Ψ₂ = c²`, `c = 1/(w+ν)`, and the cell means of the constant terms are

* `cellAvg Φ₀ = 2 c² (1 + ν S₁) / M²` (`cellAvg_phiF0`);
* `cellAvg Ψ₀ = c (cellAvg Φ₀ + (2c² - 2cE + 4c²D)/M)` with `D = -(M-1-νS₁)/(2M)` and
  `E = (S₁ - ν S₂)/M` (`cellAvg_psiF0`),

where `S_j = ∑_{n ≠ 0} (λ_n + ν)^{-j}` are the nonzero-mode sums of the circle of `M` points.
-/

@[expose] public section

namespace Balaban.Flow

open Finset

variable {M : ℕ} [NeZero M]

/-- The first-order cell coefficient solving the triangular system. -/
noncomputable def solF1 (w ν : ℝ) (S₁ F₂ : ZMod M → ℂ) : ZMod M → ℂ :=
  solC w ν (fun r => S₁ r + 2 * cellLast r * F₂ (r + 1) - 2 * cellFirst r * F₂ (r - 1))

/-- The zeroth-order cell coefficient solving the triangular system. -/
noncomputable def solF0 (w ν : ℝ) (S₀ F₂ F₁ : ZMod M → ℂ) : ZMod M → ℂ :=
  solC w ν (fun r => S₀ r + cellLast r * (F₂ (r + 1) + F₁ (r + 1))
    + cellFirst r * (F₂ (r - 1) - F₁ (r - 1)))

theorem polyZ_solved {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) {S₂ S₁ S₀ F₂ : ZMod M → ℂ}
    (h2 : cellH w ν F₂ = S₂) (k : ℤ) :
    HZ M w ν (polyZ F₂ (solF1 w ν S₁ F₂) (solF0 w ν S₀ F₂ (solF1 w ν S₁ F₂))) k =
      polyZ S₂ S₁ S₀ k := by
  have e1 : (fun r => cellH w ν (solF1 w ν S₁ F₂) r - 2 * cellLast r * F₂ (r + 1)
      + 2 * cellFirst r * F₂ (r - 1)) = S₁ := by
    funext r
    have := congrFun (cellH_solC hw hν (fun r => S₁ r + 2 * cellLast r * F₂ (r + 1)
      - 2 * cellFirst r * F₂ (r - 1))) r
    unfold solF1; rw [this]; ring
  have e0 : (fun r => cellH w ν (solF0 w ν S₀ F₂ (solF1 w ν S₁ F₂)) r
      - cellLast r * (F₂ (r + 1) + solF1 w ν S₁ F₂ (r + 1))
      - cellFirst r * (F₂ (r - 1) - solF1 w ν S₁ F₂ (r - 1))) = S₀ := by
    funext r
    have := congrFun (cellH_solC hw hν (fun r => S₀ r + cellLast r * (F₂ (r + 1)
      + solF1 w ν S₁ F₂ (r + 1)) + cellFirst r * (F₂ (r - 1) - solF1 w ν S₁ F₂ (r - 1)))) r
    unfold solF0; rw [this]; ring
  rw [polyZ_H, h2, e1, e0]

theorem sum_cellLast_shift (g : ZMod M → ℂ) : ∑ r, cellLast r * g (r + 1) = g 0 := by
  simp [cellLast, ite_mul]

theorem sum_cellFirst_shift (g : ZMod M → ℂ) : ∑ r, cellFirst r * g (r - 1) = g (-1) := by
  simp [cellFirst, ite_mul]

theorem cellAvg_add (F G : ZMod M → ℂ) : cellAvg (fun r => F r + G r) = cellAvg F + cellAvg G := by
  unfold cellAvg; rw [Finset.sum_add_distrib]; ring

theorem cellAvg_solF0 {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) (S₀ F₂ F₁ : ZMod M → ℂ) :
    cellAvg (solF0 w ν S₀ F₂ F₁) = (cellAvg S₀ + (1 / (M : ℂ)) *
      (F₂ 0 + F₁ 0 + (F₂ (-1) - F₁ (-1)))) / ((w : ℂ) + ν) := by
  unfold solF0
  rw [cellAvg_solC hw hν]
  congr 1
  unfold cellAvg
  simp only [Finset.sum_add_distrib]
  rw [sum_cellLast_shift (fun r => F₂ r + F₁ r), sum_cellFirst_shift (fun r => F₂ r - F₁ r)]
  ring

theorem conv_cellLast (ν : ℝ) (r : ZMod M) : ∑ s, gamC M ν 1 (r - s) * cellLast s =
    gamC M ν 1 (r + 1) := by
  simp [cellLast]

theorem conv_cellFirst (ν : ℝ) (r : ZMod M) : ∑ s, gamC M ν 1 (r - s) * cellFirst s =
    gamC M ν 1 r := by
  simp [cellFirst]

theorem cellAvg_cellLast : cellAvg (cellLast (M := M)) = 1 / (M : ℂ) := by
  simp [cellAvg, cellLast]

theorem cellAvg_cellFirst : cellAvg (cellFirst (M := M)) = 1 / (M : ℂ) := by
  simp [cellAvg, cellFirst]

theorem gamC_neg (ν : ℝ) (j : ℕ) (r : ZMod M) : gamC M ν j (-r) = gamC M ν j r := by
  obtain ⟨k, rfl⟩ : ∃ k : ℤ, (k : ZMod M) = r := ⟨(r.val : ℤ), by simp⟩
  have : (-(k : ZMod M)) = ((-k : ℤ) : ZMod M) := by push_cast; rfl
  rw [this, gamC_cast, gamC_cast]
  unfold gamR
  rw [cellGreen_neg]

/-- The nonzero-mode sums `S_j = ∑_{n ≠ 0} (λ_n + ν)^{-j}` of the circle of `M` points. -/
noncomputable def cellSum (M : ℕ) [NeZero M] (ν : ℝ) (j : ℕ) : ℝ :=
  ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, 1 / (cellEig M n + ν) ^ j

theorem cellGreen_at_zero (ν : ℝ) (j : ℕ) : cellGreen M ν j 0 = cellSum M ν j / M := by
  unfold cellGreen cellSum
  simp [div_eq_inv_mul]

theorem gamC_one_sub_zero {ν : ℝ} (hν : 0 < ν) :
    gamC M ν 1 1 - gamC M ν 1 0 =
      -((((M : ℝ) - 1 - ν * cellSum M ν 1) / (2 * M) : ℝ) : ℂ) := by
  have h := gamC_cast (M := M) ν 1 1
  have h0 := gamC_cast (M := M) ν 1 0
  simp only [Int.cast_one, Int.cast_zero] at h h0
  rw [h, h0, ← Complex.ofReal_sub, ← Complex.ofReal_neg]
  congr 1
  unfold gamR
  have hd := cellGreen_diff (M := M) ν 1
  have hM : (M : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hsum : ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, cellEig M n / (cellEig M n + ν) ^ 1
      = ((M : ℝ) - 1) - ν * cellSum M ν 1 := by
    unfold cellSum
    rw [Finset.mul_sum, ← sub_eq_zero]
    have hc : ((Finset.univ : Finset (ZMod M)).erase 0).card = M - 1 := by
      simp [Finset.card_erase_of_mem]
    have hMge : 1 ≤ M := Nat.pos_of_ne_zero (NeZero.ne M)
    have : ((M : ℝ) - 1) = ∑ n ∈ (Finset.univ : Finset (ZMod M)).erase 0, (1 : ℝ) := by
      simp [hc, Nat.cast_sub hMge]
    rw [this, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun n hn => ?_
    have hp : 0 < cellEig M n + ν := by have := cellEig_pos (Finset.mem_erase.1 hn).1; linarith
    field_simp
    ring
  rw [hsum] at hd
  linear_combination hd

/-- The operator `T f = (2+ν) f - f(·+1) - f(·-1)` on the circle. -/
noncomputable def cellT (ν : ℝ) (f : ZMod M → ℂ) (s : ZMod M) : ℂ :=
  (2 + (ν : ℂ)) * f s - f (s + 1) - f (s - 1)

theorem sum_cellT_comm (ν : ℝ) (f g : ZMod M → ℂ) :
    ∑ s, f s * cellT ν g s = ∑ s, cellT ν f s * g s := by
  have a : ∑ s, f s * g (s + 1) = ∑ s, f (s - 1) * g s :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod M)) _ _ fun s => by simp
  have b : ∑ s, f s * g (s - 1) = ∑ s, f (s + 1) * g s :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod M)) _ _ fun s => by simp
  unfold cellT
  have e : ∀ s, f s * ((2 + (ν : ℂ)) * g s - g (s + 1) - g (s - 1)) =
      (2 + (ν : ℂ)) * (f s * g s) - f s * g (s + 1) - f s * g (s - 1) := fun s => by ring
  have e' : ∀ s, ((2 + (ν : ℂ)) * f s - f (s + 1) - f (s - 1)) * g s =
      (2 + (ν : ℂ)) * (f s * g s) - f (s + 1) * g s - f (s - 1) * g s := fun s => by ring
  simp only [e, e', Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [a, b]
  ring

theorem cellT_gamC {ν : ℝ} (hν : 0 < ν) (j : ℕ) (s : ZMod M) :
    cellT ν (gamC M ν (j + 1)) s = gamC M ν j s := gamC_step hν j s

theorem sum_gamC_sq {ν : ℝ} (hν : 0 < ν) :
    ∑ s, gamC M ν 1 s * gamC M ν 1 s = gamC M ν 2 0 := by
  have h1 : ∑ s, gamC M ν 1 s * cellT ν (gamC M ν 2) s =
      ∑ s, cellT ν (gamC M ν 1) s * gamC M ν 2 s := sum_cellT_comm ν _ _
  simp only [cellT_gamC hν, gamC_zero] at h1
  simpa using h1

theorem sum_gamC_diff_sq {ν : ℝ} (hν : 0 < ν) :
    ∑ s, (gamC M ν 1 (s + 1) - gamC M ν 1 s) ^ 2 =
      gamC M ν 1 0 - ν * gamC M ν 2 0 := by
  have h1 : ∑ s, gamC M ν 1 s * cellT ν (gamC M ν 1) s = gamC M ν 1 0 := by
    simp only [cellT_gamC hν, gamC_zero]; simp
  have a : ∑ s, gamC M ν 1 s * gamC M ν 1 (s + 1) =
      ∑ s, gamC M ν 1 (s - 1) * gamC M ν 1 s :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod M)) _ _ fun s => by simp
  have b : ∑ s, gamC M ν 1 s * gamC M ν 1 (s - 1) =
      ∑ s, gamC M ν 1 (s + 1) * gamC M ν 1 s :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod M)) _ _ fun s => by simp
  have c : ∑ s, gamC M ν 1 (s + 1) * gamC M ν 1 (s + 1) = ∑ s, gamC M ν 1 s * gamC M ν 1 s :=
    Fintype.sum_equiv (Equiv.addRight (1 : ZMod M)) _ _ fun s => rfl
  unfold cellT at h1
  simp only [mul_sub, Finset.sum_sub_distrib] at h1
  have e : ∀ s, (gamC M ν 1 (s + 1) - gamC M ν 1 s) ^ 2 =
      gamC M ν 1 (s + 1) * gamC M ν 1 (s + 1) + gamC M ν 1 s * gamC M ν 1 s
        - 2 * (gamC M ν 1 (s + 1) * gamC M ν 1 s) := fun s => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [c, ← sum_gamC_sq hν]
  have b' : ∑ s, gamC M ν 1 (s + 1) * gamC M ν 1 s = ∑ s, gamC M ν 1 s * gamC M ν 1 (s + 1) := by
    refine Finset.sum_congr rfl fun s _ => mul_comm _ _
  have h1' : ∑ x, gamC M ν 1 x * ((2 + (ν : ℂ)) * gamC M ν 1 x) =
      (2 + (ν : ℂ)) * ∑ x, gamC M ν 1 x * gamC M ν 1 x := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  rw [h1', b] at h1
  linear_combination h1 - b'

/-- The constant `c = 1/(w+ν)`. -/
noncomputable def ccC (w ν : ℝ) : ℂ := 1 / ((w : ℂ) + ν)

/-- The cell coefficient `Φ₂ = c` of the solution of `H Φ = x²`. -/
noncomputable def phiF2 (M : ℕ) (w ν : ℝ) : ZMod M → ℂ := fun _ => ccC w ν

/-- The cell coefficient `Φ₁` of the solution of `H Φ = x²`. -/
noncomputable def phiF1 (M : ℕ) [NeZero M] (w ν : ℝ) : ZMod M → ℂ :=
  solF1 w ν 0 (phiF2 M w ν)

/-- The cell coefficient `Φ₀` of the solution of `H Φ = x²`. -/
noncomputable def phiF0 (M : ℕ) [NeZero M] (w ν : ℝ) : ZMod M → ℂ :=
  solF0 w ν 0 (phiF2 M w ν) (phiF1 M w ν)

theorem cellH_const (w ν : ℝ) (a : ℂ) (r : ZMod M) :
    cellH w ν (fun _ : ZMod M => a) r = ((w : ℂ) + ν) * a := by
  unfold cellH; rw [cellAvg_const]; ring

theorem ne_wν {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) : ((w : ℂ) + ν) ≠ 0 := by
  exact_mod_cast (by positivity : (w : ℝ) + ν ≠ 0)

theorem cellH_phiF2 {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) :
    cellH w ν (phiF2 M w ν) = fun _ => 1 := by
  funext r
  have := ne_wν hw hν
  unfold phiF2 ccC; rw [cellH_const]; field_simp

/-- `H Φ = x²` for the cell polynomial `Φ`. -/
theorem polyZ_phi {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) (k : ℤ) :
    HZ M w ν (polyZ (phiF2 M w ν) (phiF1 M w ν) (phiF0 M w ν)) k =
      polyZ (fun _ : ZMod M => (1 : ℂ)) 0 0 k :=
  polyZ_solved hw hν (cellH_phiF2 hw hν) k

theorem cellAvg_delta (a : ℂ) :
    cellAvg (fun r : ZMod M => a * cellLast r - a * cellFirst r) = 0 := by
  unfold cellAvg
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  simp [cellLast, cellFirst]

theorem conv_delta (ν : ℝ) (a : ℂ) (r : ZMod M) :
    convC ν 1 (fun s : ZMod M => a * cellLast s - a * cellFirst s) r =
      a * (gamC M ν 1 (r + 1) - gamC M ν 1 r) := by
  unfold convC
  have hL : ∑ s, gamC M ν 1 (r - s) * (a * cellLast s) = a * gamC M ν 1 (r + 1) := by
    rw [← conv_cellLast, Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  have hF : ∑ s, gamC M ν 1 (r - s) * (a * cellFirst s) = a * gamC M ν 1 r := by
    rw [← conv_cellFirst, Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  simp only [mul_sub, Finset.sum_sub_distrib, hL, hF]

theorem solC_delta {w ν : ℝ} (a : ℂ) (r : ZMod M) :
    solC w ν (fun s : ZMod M => a * cellLast s - a * cellFirst s) r =
      a * (gamC M ν 1 (r + 1) - gamC M ν 1 r) := by
  unfold solC
  rw [cellAvg_delta, conv_delta]; simp

theorem phiF1_eq (w ν : ℝ) (r : ZMod M) :
    phiF1 M w ν r = 2 * ccC w ν * (gamC M ν 1 (r + 1) - gamC M ν 1 r) := by
  unfold phiF1 solF1
  have hsrc : (fun r : ZMod M => (0 : ZMod M → ℂ) r + 2 * cellLast r * phiF2 M w ν (r + 1)
      - 2 * cellFirst r * phiF2 M w ν (r - 1)) =
      fun r => (2 * ccC w ν) * cellLast r - (2 * ccC w ν) * cellFirst r := by
    funext r; simp [phiF2]; ring
  rw [hsrc, solC_delta]

theorem cellAvg_phiF1 {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) : cellAvg (phiF1 M w ν) = 0 := by
  unfold phiF1 solF1
  have hsrc : (fun r : ZMod M => (0 : ZMod M → ℂ) r + 2 * cellLast r * phiF2 M w ν (r + 1)
      - 2 * cellFirst r * phiF2 M w ν (r - 1)) =
      fun r => (2 * ccC w ν) * cellLast r - (2 * ccC w ν) * cellFirst r := by
    funext r; simp [phiF2]; ring
  rw [hsrc, cellAvg_solC hw hν, cellAvg_delta]; simp

theorem cellAvg_zero : cellAvg (0 : ZMod M → ℂ) = 0 := by simp [cellAvg]

/-- The cell mean of `Φ₀`: `2 c² (1 + ν S₁)/M²`. -/
theorem cellAvg_phiF0 {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) :
    cellAvg (phiF0 M w ν) =
      2 * ccC w ν ^ 2 * (1 + ν * (cellSum M ν 1 : ℝ)) / (M : ℂ) ^ 2 := by
  unfold phiF0
  rw [cellAvg_solF0 hw hν, cellAvg_zero]
  have hn : (-1 : ZMod M) = -(1 : ZMod M) := rfl
  have e1 := phiF1_eq (M := M) w ν 0
  have e2 := phiF1_eq (M := M) w ν (-1)
  rw [zero_add] at e1
  rw [neg_add_cancel, hn, gamC_neg] at e2
  have hD := gamC_one_sub_zero (M := M) hν
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hw' := ne_wν hw hν
  have hcc : ccC w ν * ((w : ℂ) + ν) = 1 := by unfold ccC; field_simp
  simp only [phiF2]
  rw [e1, e2]
  have hD' : gamC M ν 1 1 - gamC M ν 1 0 =
      -(((M : ℂ) - 1 - ν * (cellSum M ν 1 : ℝ)) / (2 * M)) := by
    rw [hD]; push_cast; ring
  have : gamC M ν 1 0 - gamC M ν 1 1 = -(gamC M ν 1 1 - gamC M ν 1 0) := by ring
  rw [this, hD']
  unfold ccC at *
  field_simp
  ring

/-- The cell coefficient `Ψ₂ = c²` of the solution of `H Ψ = Φ`. -/
noncomputable def psiF2 (M : ℕ) (w ν : ℝ) : ZMod M → ℂ := fun _ => ccC w ν * ccC w ν

/-- The cell coefficient `Ψ₁` of the solution of `H Ψ = Φ`. -/
noncomputable def psiF1 (M : ℕ) [NeZero M] (w ν : ℝ) : ZMod M → ℂ :=
  solF1 w ν (phiF1 M w ν) (psiF2 M w ν)

/-- The cell coefficient `Ψ₀` of the solution of `H Ψ = Φ`. -/
noncomputable def psiF0 (M : ℕ) [NeZero M] (w ν : ℝ) : ZMod M → ℂ :=
  solF0 w ν (phiF0 M w ν) (psiF2 M w ν) (psiF1 M w ν)

theorem cellH_psiF2 {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) :
    cellH w ν (psiF2 M w ν) = phiF2 M w ν := by
  funext r
  have := ne_wν hw hν
  unfold psiF2 phiF2 ccC; rw [cellH_const]; field_simp

/-- `H Ψ = Φ` for the cell polynomial `Ψ`. -/
theorem polyZ_psi {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) (k : ℤ) :
    HZ M w ν (polyZ (psiF2 M w ν) (psiF1 M w ν) (psiF0 M w ν)) k =
      polyZ (phiF2 M w ν) (phiF1 M w ν) (phiF0 M w ν) k :=
  polyZ_solved hw hν (cellH_psiF2 hw hν) k

theorem psiF1_src (w ν : ℝ) :
    (fun r : ZMod M => phiF1 M w ν r + 2 * cellLast r * psiF2 M w ν (r + 1)
      - 2 * cellFirst r * psiF2 M w ν (r - 1)) =
      fun r => phiF1 M w ν r + ((2 * (ccC w ν * ccC w ν)) * cellLast r
        - (2 * (ccC w ν * ccC w ν)) * cellFirst r) := by
  funext r; simp [psiF2]; ring

theorem cellAvg_psiSrc {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) :
    cellAvg (fun r : ZMod M => phiF1 M w ν r + ((2 * (ccC w ν * ccC w ν)) * cellLast r
        - (2 * (ccC w ν * ccC w ν)) * cellFirst r)) = 0 := by
  rw [cellAvg_add, cellAvg_phiF1 hw hν, cellAvg_delta]; simp

theorem psiF1_eq {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) (r : ZMod M) :
    psiF1 M w ν r = ∑ s, gamC M ν 1 (r - s) * (phiF1 M w ν s +
      ((2 * (ccC w ν * ccC w ν)) * cellLast s - (2 * (ccC w ν * ccC w ν)) * cellFirst s)) := by
  unfold psiF1 solF1
  rw [psiF1_src, solC]
  rw [cellAvg_psiSrc hw hν]
  simp [convC]

/-- The first-order cell coefficient of `Ψ` at the cell ends:
`Ψ₁(0) - Ψ₁(-1) = -2c E + 4c² (Γ(1) - Γ(0))`, `E = ∑ (Γ(s+1) - Γ(s))²`. -/
theorem psiF1_diff {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) :
    psiF1 M w ν 0 - psiF1 M w ν (-1) =
      -2 * ccC w ν * (∑ s, (gamC M ν 1 (s + 1) - gamC M ν 1 s) ^ 2)
        + 4 * (ccC w ν * ccC w ν) * (gamC M ν 1 1 - gamC M ν 1 0) := by
  rw [psiF1_eq hw hν, psiF1_eq hw hν, ← Finset.sum_sub_distrib]
  have hA : ∀ s : ZMod M, gamC M ν 1 (0 - s) = gamC M ν 1 s := fun s => by
    rw [zero_sub, gamC_neg]
  have hB : ∀ s : ZMod M, gamC M ν 1 (-1 - s) = gamC M ν 1 (s + 1) := fun s => by
    rw [show (-1 - s : ZMod M) = -(s + 1) by ring, gamC_neg]
  have hn : gamC M ν 1 (-1) = gamC M ν 1 1 := by
    rw [show (-1 : ZMod M) = -(1 : ZMod M) from rfl, gamC_neg]
  have e : ∀ s : ZMod M, gamC M ν 1 (0 - s) * (phiF1 M w ν s +
      ((2 * (ccC w ν * ccC w ν)) * cellLast s - (2 * (ccC w ν * ccC w ν)) * cellFirst s))
      - gamC M ν 1 (-1 - s) * (phiF1 M w ν s +
      ((2 * (ccC w ν * ccC w ν)) * cellLast s - (2 * (ccC w ν * ccC w ν)) * cellFirst s)) =
      -2 * ccC w ν * (gamC M ν 1 (s + 1) - gamC M ν 1 s) ^ 2
      + (2 * (ccC w ν * ccC w ν)) * ((gamC M ν 1 s - gamC M ν 1 (s + 1)) * cellLast s)
      - (2 * (ccC w ν * ccC w ν)) * ((gamC M ν 1 s - gamC M ν 1 (s + 1)) * cellFirst s) := by
    intro s
    rw [hA, hB, phiF1_eq]; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hL : ∑ s, (gamC M ν 1 s - gamC M ν 1 (s + 1)) * cellLast s =
      gamC M ν 1 (-1) - gamC M ν 1 0 := by simp [cellLast]
  have hF : ∑ s, (gamC M ν 1 s - gamC M ν 1 (s + 1)) * cellFirst s =
      gamC M ν 1 0 - gamC M ν 1 1 := by simp [cellFirst]
  rw [hL, hF, hn]
  ring

theorem gamC_zero_one {ν : ℝ} (j : ℕ) :
    gamC M ν j 0 = ((cellSum M ν j / M + 1 / (M * ν ^ j) : ℝ) : ℂ) := by
  have h := gamC_cast (M := M) ν j 0
  simp only [Int.cast_zero] at h
  rw [h]; unfold gamR; rw [cellGreen_at_zero]

/-- The cell mean of `Ψ₀`: `c (cellAvg Φ₀ + (2c² - 2cE + 4c²D)/M)` with
`D = -(M - 1 - νS₁)/(2M)` and `E = (S₁ - νS₂)/M`. -/
theorem cellAvg_psiF0 {w ν : ℝ} (hw : 0 ≤ w) (hν : 0 < ν) :
    cellAvg (psiF0 M w ν) = ccC w ν * (cellAvg (phiF0 M w ν) + (1 / (M : ℂ)) *
      (2 * (ccC w ν * ccC w ν)
        - 2 * ccC w ν * (((cellSum M ν 1 : ℝ) - ν * (cellSum M ν 2 : ℝ)) / M)
        - 2 * (ccC w ν * ccC w ν) * (((M : ℂ) - 1 - ν * (cellSum M ν 1 : ℝ)) / M))) := by
  unfold psiF0
  rw [cellAvg_solF0 hw hν]
  have hd := psiF1_diff (M := M) hw hν
  have hE := sum_gamC_diff_sq (M := M) hν
  have hD := gamC_one_sub_zero (M := M) hν
  have g1 := gamC_zero_one (M := M) (ν := ν) 1
  have g2 := gamC_zero_one (M := M) (ν := ν) 2
  rw [hE, hD, g1, g2] at hd
  have hM : (M : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have hν' : (ν : ℂ) ≠ 0 := by exact_mod_cast hν.ne'
  have hw' := ne_wν hw hν
  have hs : psiF2 M w ν 0 + psiF1 M w ν 0 + (psiF2 M w ν (-1) - psiF1 M w ν (-1)) =
      2 * (ccC w ν * ccC w ν) + (psiF1 M w ν 0 - psiF1 M w ν (-1)) := by
    simp only [psiF2]; ring
  rw [hs, hd]
  rw [div_eq_mul_one_div, show (1 / ((w : ℂ) + ν)) = ccC w ν from rfl, mul_comm]
  push_cast
  field_simp
  ring

end Balaban.Flow
