/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Flow.PairDecay
public import Balaban.Flow.Sawtooth
public import Balaban.Flow.CellMoments

/-!
# Second moments of the Green kernel of a whole-lattice level

Let `G` be a whole-lattice level `n` on the torus `(ZMod (N₀ L^K))^d`, `N = L^n` the block side,
`m = N₀ L^{K-n}` the number of blocks per side, `H = H_D(0)` the Dirichlet operator
(`-Δ + w P + ν`, `w = a_n L^{-2n}`) and `Gm = H⁻¹`.  With `g(y) = ∑_μ (signed block index of y_μ)²`
and `f₀` the indicator of the block of the origin, the pairings `f₀ ⬝ Gm g` and `f₀ ⬝ Gm Gm g` equal
`d N^d` times the cell means of `Φ₀` and `Ψ₀` (`cellAvg_phiF0`, `cellAvg_psiF0`) up to an error
that is bounded by a polynomial in `N₀` times `exp(-ε N₀/2)`.
-/

@[expose] public section

namespace Balaban.Flow

open Finset Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Matrix

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The sum over the coordinates of a function of one coordinate. -/
def liftSum {ℓ : ℕ} (U : ZMod ℓ → ℂ) : Torus d ℓ → ℂ := fun y => ∑ μ : Fin d, U (y μ)

theorem mulVec_liftSum {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) (ν : ℝ)
    (U : ZMod (N₀ * L ^ K) → ℂ) (x : G.Ω 1) :
    (dirichletOperator G a ν 0 *ᵥ (fun y : G.Ω 1 => liftSum (d := d) U (y : Torus d (N₀ * L ^ K)))) x =
      liftSum (d := d) (hamil1 (L ^ n) (N₀ * L ^ (K - n)) (a n / ((L : ℝ) ^ n) ^ 2) ν U)
        (x : Torus d (N₀ * L ^ K)) := by
  have h : ∀ μ : Fin d, (dirichletOperator G a ν 0 *ᵥ
      (fun y : G.Ω 1 => lift1 μ U (y : Torus d (N₀ * L ^ K)))) x =
      hamil1 (L ^ n) (N₀ * L ^ (K - n)) (a n / ((L : ℝ) ^ n) ^ 2) ν U
        ((x : Torus d (N₀ * L ^ K)) μ) := fun μ => dirichlet_lift1 hG a ν μ U x
  unfold liftSum
  simp only [Matrix.mulVec, dotProduct] at h ⊢
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun μ _ => h μ

omit [NeZero N₀] [NeZero L] in
theorem ell_eq {n : ℕ} (hnK : n ≤ K) : N₀ * L ^ K = L ^ n * (N₀ * L ^ (K - n)) := by
  rw [← mul_assoc, mul_comm (L ^ n), mul_assoc, ← pow_add, Nat.add_sub_cancel' hnK]

theorem polyZ_one_zero_zero {N : ℕ} [NeZero N] (k : ℤ) :
    polyZ (fun _ : ZMod N => (1 : ℂ)) 0 0 k = ((k / N : ℤ) : ℂ) ^ 2 := by
  simp [polyZ]

/-- `H` applied to the sawtooth of `Φ`: the weight `x²` plus the seam error. -/
theorem H_saw_phi {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) {ν : ℝ}
    (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2) (hν : 0 < ν) :
    dirichletOperator G a ν 0 *ᵥ (fun y : G.Ω 1 => liftSum (d := d)
      (saw (L ^ n) (N₀ * L ^ (K - n)) (phiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
        (phiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))
        (y : Torus d (N₀ * L ^ K))) =
      (fun y : G.Ω 1 => liftSum (d := d)
        (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
        (y : Torus d (N₀ * L ^ K))) +
      (fun y : G.Ω 1 => liftSum (d := d)
        (sawErr (L ^ n) (N₀ * L ^ (K - n)) (phiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
          (phiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))
        (y : Torus d (N₀ * L ^ K))) := by
  funext x
  have hnK := (IsLevel.bounds hG).2
  have hℓ := ell_eq (N₀ := N₀) (L := L) hnK
  rw [mulVec_liftSum hG]
  simp only [Pi.add_apply]
  unfold liftSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hamil1_saw hℓ, polyZ_phi hw hν, polyZ_one_zero_zero, slift_ediv]

/-- `H` applied to the sawtooth of `Ψ`: the sawtooth of `Φ` plus the seam error. -/
theorem H_saw_psi {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) {ν : ℝ}
    (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2) (hν : 0 < ν) :
    dirichletOperator G a ν 0 *ᵥ (fun y : G.Ω 1 => liftSum (d := d)
      (saw (L ^ n) (N₀ * L ^ (K - n)) (psiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
        (psiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (psiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))
        (y : Torus d (N₀ * L ^ K))) =
      (fun y : G.Ω 1 => liftSum (d := d)
        (saw (L ^ n) (N₀ * L ^ (K - n)) (phiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
        (phiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))
        (y : Torus d (N₀ * L ^ K))) +
      (fun y : G.Ω 1 => liftSum (d := d)
        (sawErr (L ^ n) (N₀ * L ^ (K - n)) (psiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
          (psiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (psiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))
        (y : Torus d (N₀ * L ^ K))) := by
  funext x
  have hnK := (IsLevel.bounds hG).2
  have hℓ := ell_eq (N₀ := N₀) (L := L) hnK
  rw [mulVec_liftSum hG]
  simp only [Pi.add_apply]
  unfold liftSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [hamil1_saw hℓ, polyZ_psi hw hν]
  rfl

/-- The indicator of the block of the origin, as a vector on `Ω₁`. -/
noncomputable def blockInd (G : GeneratingSet d L N₀ K ϱ) (N m : ℕ) [NeZero (N₀ * L ^ K)] :
    G.Ω 1 → ℂ := fun y =>
  if blockMap (d := d) (ℓ := N₀ * L ^ K) N m (y : Torus d (N₀ * L ^ K)) = 0 then 1 else 0

theorem blockInd_dot_liftSum {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n)
    (U : ZMod (N₀ * L ^ K) → ℂ) :
    blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ
        (fun y : G.Ω 1 => liftSum (d := d) U (y : Torus d (N₀ * L ^ K))) =
      (d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ (d - 1) *
        ∑ j : Fin (L ^ n), U (blockSite (ℓ := N₀ * L ^ K) (L ^ n) (0 : ZMod (N₀ * L ^ (K - n))) j) := by
  classical
  have hnK := (IsLevel.bounds hG).2
  have hℓ := ell_eq (N₀ := N₀) (L := L) hnK
  have : NeZero (N₀ * L ^ (K - n)) := ⟨Nat.mul_ne_zero (NeZero.ne N₀) (pow_ne_zero _ (NeZero.ne L))⟩
  unfold dotProduct blockInd
  beta_reduce
  rw [Finset.sum_coe_sort (G.Ω 1) (fun y : Torus d (N₀ * L ^ K) =>
    (if blockMap (L ^ n) (N₀ * L ^ (K - n)) y = 0 then (1 : ℂ) else 0) * liftSum (d := d) U y),
    IsLevel.Ω_one hG]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfil : (Finset.univ.filter fun y : Torus d (N₀ * L ^ K) =>
      blockMap (L ^ n) (N₀ * L ^ (K - n)) y = 0) = blockFibre (L ^ n) (N₀ * L ^ (K - n)) 0 := by
    ext y; simp [mem_blockFibre]
  rw [hfil]
  unfold liftSum
  rw [Finset.sum_comm]
  have hμ : ∀ μ : Fin d, ∑ y ∈ (blockFibre (L ^ n) (N₀ * L ^ (K - n)) (0 : Torus d (N₀ * L ^ (K - n))) :
      Finset.{0} (Torus d (N₀ * L ^ K))), U (y μ) =
      ((L ^ n : ℕ) : ℂ) ^ (d - 1) * ∑ j : Fin (L ^ n),
        U (blockSite (ℓ := N₀ * L ^ K) (L ^ n) (0 : ZMod (N₀ * L ^ (K - n))) j) := fun μ => by
    rw [sum_blockFibre_lift1 hℓ]
    simp only [Pi.zero_apply]
    rw [sum_fibre1 hℓ]
  rw [Finset.sum_congr rfl fun μ _ => hμ μ]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem sum_saw_block0 {ℓ N m : ℕ} [NeZero ℓ] [NeZero N] [NeZero m] (hℓ : ℓ = N * m)
    (F₂ F₁ F₀ : ZMod N → ℂ) :
    ∑ j : Fin N, saw N m F₂ F₁ F₀ (blockSite (ℓ := ℓ) N (0 : ZMod m) j) = ∑ r, F₀ r := by
  rw [← sum_fin_zmod F₀]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold saw
  rw [slift_blockSite hℓ _ j.2, ZMod.valMinAbs_zero]
  have hN : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have h0 : (((j : ℕ) : ℤ)) / (N : ℤ) = 0 := Int.ediv_eq_zero_of_lt (by positivity) (by exact_mod_cast j.2)
  unfold polyZ
  simp [h0]

theorem seam_sep {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n)
    (F₂ F₁ F₀ : ZMod (L ^ n) → ℂ) (x y : G.Ω 1) (hy : blockInd G (L ^ n) (N₀ * L ^ (K - n)) y ≠ 0)
    (hx : liftSum (d := d) (sawErr (L ^ n) (N₀ * L ^ (K - n)) F₂ F₁ F₀)
      (x : Torus d (N₀ * L ^ K)) ≠ 0) :
    (N₀ : ℝ) / 2 - 2 ≤
      Green.torusDist d (N₀ * L ^ K) (y : Torus d (N₀ * L ^ K)) x / (L : ℝ) ^ K := by
  have hnK := (IsLevel.bounds hG).2
  have hℓ := ell_eq (N₀ := N₀) (L := L) hnK
  have : NeZero (N₀ * L ^ (K - n)) := ⟨Nat.mul_ne_zero (NeZero.ne N₀) (pow_ne_zero _ (NeZero.ne L))⟩
  obtain ⟨μ, hμ⟩ : ∃ μ : Fin d, sawErr (L ^ n) (N₀ * L ^ (K - n)) F₂ F₁ F₀
      ((x : Torus d (N₀ * L ^ K)) μ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (Finset.sum_eq_zero fun μ _ => hcon μ)
  have hys : blockMap (L ^ n) (N₀ * L ^ (K - n)) (y : Torus d (N₀ * L ^ K)) = 0 := by
    by_contra hne; exact hy (by unfold blockInd; simp [hne])
  have hyv : ((y : Torus d (N₀ * L ^ K)) μ).val < L ^ n := by
    have h1 : blockCoord (L ^ n) (N₀ * L ^ (K - n)) ((y : Torus d (N₀ * L ^ K)) μ) = 0 := by
      have := congrFun hys μ; simpa [blockMap] using this
    have h2 := blockCoord_val hℓ ((y : Torus d (N₀ * L ^ K)) μ)
    rw [h1, ZMod.val_zero] at h2
    rcases Nat.div_eq_zero_iff.1 h2.symm with h | h
    · exact absurd h (pow_ne_zero _ (NeZero.ne L))
    · exact h
  have hseam := sawErr_ne_zero hℓ F₂ F₁ F₀ _ hμ
  have hds := dist_seam hℓ ((x : Torus d (N₀ * L ^ K)) μ) ((y : Torus d (N₀ * L ^ K)) μ) hyv hseam
  have hterm : (|Green.cycRep (((x : Torus d (N₀ * L ^ K)) μ) - (y : Torus d (N₀ * L ^ K)) μ)| : ℝ)
      ≤ Green.torusDist d (N₀ * L ^ K) (y : Torus d (N₀ * L ^ K)) x := by
    rw [Green.torusDist_comm_gen]
    unfold Green.torusDist
    have := Finset.single_le_sum (f := fun i : Fin d => ((Green.cycRep (((x : Torus d (N₀ * L ^ K)) i) -
      (y : Torus d (N₀ * L ^ K)) i)).natAbs : ℝ)) (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ μ)
    simpa [Nat.cast_natAbs] using this
  have hLK : (0 : ℝ) < (L : ℝ) ^ K := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hNL : ((L ^ n : ℕ) : ℝ) ≤ (L : ℝ) ^ K := by
    have : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
    push_cast; exact pow_le_pow_right₀ this hnK
  have hreal : ((L ^ n : ℕ) : ℝ) * (((N₀ * L ^ (K - n) : ℕ) : ℝ) - 4) ≤
      2 * (|Green.cycRep (((x : Torus d (N₀ * L ^ K)) μ) - (y : Torus d (N₀ * L ^ K)) μ)| : ℝ) := by
    exact_mod_cast hds
  have hprod : ((L ^ n : ℕ) : ℝ) * ((N₀ * L ^ (K - n) : ℕ) : ℝ) = (N₀ : ℝ) * (L : ℝ) ^ K := by
    have := congrArg (fun z : ℕ => (z : ℝ)) hℓ.symm
    simpa using this
  rw [le_div_iff₀ hLK]
  nlinarith [hNL, hprod, hreal, hterm]

/-- The bound of the seam error vector: `d · 4 · cellNorm · (m/2 + 2)²`. -/
noncomputable def seamBound (d m : ℕ) (cn : ℝ) : ℝ := d * (4 * cn * ((m : ℝ) / 2 + 2) ^ 2)

theorem norm_liftSum_sawErr_le {ℓ N m : ℕ} [NeZero ℓ] [NeZero N] [NeZero m] (F₂ F₁ F₀ : ZMod N → ℂ)
    (y : Torus d ℓ) :
    ‖liftSum (d := d) (sawErr N m F₂ F₁ F₀) y‖ ≤ seamBound d m (cellNorm F₂ F₁ F₀) := by
  unfold liftSum seamBound
  refine (norm_sum_le _ _).trans ?_
  calc ∑ μ : Fin d, ‖sawErr N m F₂ F₁ F₀ (y μ)‖ ≤ ∑ _μ : Fin d,
        4 * cellNorm F₂ F₁ F₀ * ((m : ℝ) / 2 + 2) ^ 2 :=
        Finset.sum_le_sum fun μ _ => norm_sawErr_le F₂ F₁ F₀ _
    _ = _ := by simp

theorem moment_R1 {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 < ν) (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2)
    (ha : IsAdmissibleWeights K a) (hU : IsUnit (dirichletOperator G a ν (0 : G.Ω 1 → ℂ))) :
    ‖blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ
        ((dirichletOperator G a ν (0 : G.Ω 1 → ℂ))⁻¹ *ᵥ
          (fun y : G.Ω 1 => liftSum (d := d)
            (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (N₀ * L ^ K)))) -
      (d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d * cellAvg (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)‖ ≤
      (Fintype.card (G.Ω 1) : ℝ) ^ 2 * (kernelConst d L n *
        Real.exp (-(agmonRate d) * ((N₀ : ℝ) / 2 - 2)) *
        seamBound d (N₀ * L ^ (K - n)) (cellNorm (phiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
          (phiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))) := by
  classical
  set w := a n / ((L : ℝ) ^ n) ^ 2 with hwdef
  set Hm := dirichletOperator G a ν (0 : G.Ω 1 → ℂ) with hHm
  set F₂ := phiF2 (L ^ n) w ν
  set F₁ := phiF1 (L ^ n) w ν
  set F₀ := phiF0 (L ^ n) w ν
  have hdet : IsUnit Hm.det := (Matrix.isUnit_iff_isUnit_det Hm).1 hU
  set u : G.Ω 1 → ℂ := fun y => liftSum (d := d) (saw (L ^ n) (N₀ * L ^ (K - n)) F₂ F₁ F₀)
    (y : Torus d (N₀ * L ^ K)) with hu
  set e : G.Ω 1 → ℂ := fun y => liftSum (d := d) (sawErr (L ^ n) (N₀ * L ^ (K - n)) F₂ F₁ F₀)
    (y : Torus d (N₀ * L ^ K)) with he
  set g : G.Ω 1 → ℂ := fun y => liftSum (d := d)
    (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
    (y : Torus d (N₀ * L ^ K)) with hg
  have hH : Hm *ᵥ u = g + e := H_saw_phi hG a hw hν
  have hGu : Hm⁻¹ *ᵥ g = u - Hm⁻¹ *ᵥ e := by
    have : Hm⁻¹ *ᵥ (Hm *ᵥ u) = u := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
    rw [hH, Matrix.mulVec_add] at this
    rw [← this]; abel
  have hmain : blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ u =
      (d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d * cellAvg F₀ := by
    rw [hu, blockInd_dot_liftSum hG, sum_saw_block0 (ell_eq (IsLevel.bounds hG).2)]
    unfold cellAvg
    have hd1 : ((L ^ n : ℕ) : ℂ) ^ d = ((L ^ n : ℕ) : ℂ) ^ (d - 1) * ((L ^ n : ℕ) : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    have hN : ((L ^ n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (NeZero.ne L)
    rw [hd1]; field_simp
  rw [hGu, dotProduct_sub, hmain, sub_sub_cancel_left, norm_neg]
  have hkd := kernel_decay hG hd hν.le ha hU
  refine pair_small (Hm⁻¹) (fun y x => Green.torusDist d (N₀ * L ^ K) (y : Torus d (N₀ * L ^ K)) x /
    (L : ℝ) ^ K) (by unfold kernelConst; exact Real.sqrt_nonneg _) ?_ (agmonRate_pos hd).le ?_ _ _ ?_ ?_ ?_
  · unfold seamBound; have : 0 ≤ cellNorm F₂ F₁ F₀ := Finset.sum_nonneg fun r _ => by positivity
    positivity
  · intro x x'; exact hkd x x'
  · intro y; unfold blockInd; split_ifs <;> simp
  · intro x; exact norm_liftSum_sawErr_le _ _ _ _
  · intro y x hy hx; exact seam_sep hG F₂ F₁ F₀ x y hy hx

theorem moment_R2 {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) (hd : 0 < d)
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 < ν) (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2)
    (ha : IsAdmissibleWeights K a) (hU : IsUnit (dirichletOperator G a ν (0 : G.Ω 1 → ℂ))) :
    ‖blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ
        ((dirichletOperator G a ν (0 : G.Ω 1 → ℂ))⁻¹ *ᵥ
          ((dirichletOperator G a ν (0 : G.Ω 1 → ℂ))⁻¹ *ᵥ
          (fun y : G.Ω 1 => liftSum (d := d)
            (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (N₀ * L ^ K))))) -
      (d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d * cellAvg (psiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)‖ ≤
      (Fintype.card (G.Ω 1) : ℝ) ^ 2 * (kernelConst d L n *
        Real.exp (-(agmonRate d) * ((N₀ : ℝ) / 2 - 2)) *
        seamBound d (N₀ * L ^ (K - n)) (cellNorm (psiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
          (psiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (psiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))) +
      (Fintype.card (G.Ω 1) : ℝ) ^ 3 * (kernelConst d L n ^ 2 *
        Real.exp (-(agmonRate d) * ((N₀ : ℝ) / 2 - 2)) *
        seamBound d (N₀ * L ^ (K - n)) (cellNorm (phiF2 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν)
          (phiF1 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν) (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))) := by
  classical
  set w := a n / ((L : ℝ) ^ n) ^ 2 with hwdef
  set Hm := dirichletOperator G a ν (0 : G.Ω 1 → ℂ) with hHm
  have hdet : IsUnit Hm.det := (Matrix.isUnit_iff_isUnit_det Hm).1 hU
  set u : G.Ω 1 → ℂ := fun y => liftSum (d := d) (saw (L ^ n) (N₀ * L ^ (K - n))
    (phiF2 (L ^ n) w ν) (phiF1 (L ^ n) w ν) (phiF0 (L ^ n) w ν)) (y : Torus d (N₀ * L ^ K)) with hu
  set e : G.Ω 1 → ℂ := fun y => liftSum (d := d) (sawErr (L ^ n) (N₀ * L ^ (K - n))
    (phiF2 (L ^ n) w ν) (phiF1 (L ^ n) w ν) (phiF0 (L ^ n) w ν)) (y : Torus d (N₀ * L ^ K)) with he
  set v : G.Ω 1 → ℂ := fun y => liftSum (d := d) (saw (L ^ n) (N₀ * L ^ (K - n))
    (psiF2 (L ^ n) w ν) (psiF1 (L ^ n) w ν) (psiF0 (L ^ n) w ν)) (y : Torus d (N₀ * L ^ K)) with hv
  set e' : G.Ω 1 → ℂ := fun y => liftSum (d := d) (sawErr (L ^ n) (N₀ * L ^ (K - n))
    (psiF2 (L ^ n) w ν) (psiF1 (L ^ n) w ν) (psiF0 (L ^ n) w ν)) (y : Torus d (N₀ * L ^ K)) with he'
  set g : G.Ω 1 → ℂ := fun y => liftSum (d := d)
    (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
    (y : Torus d (N₀ * L ^ K)) with hg
  have hH1 : Hm *ᵥ u = g + e := H_saw_phi hG a hw hν
  have hH2 : Hm *ᵥ v = u + e' := H_saw_psi hG a hw hν
  have hinv : ∀ z : G.Ω 1 → ℂ, Hm⁻¹ *ᵥ (Hm *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hGu : Hm⁻¹ *ᵥ g = u - Hm⁻¹ *ᵥ e := by
    have := hinv u
    rw [hH1, Matrix.mulVec_add] at this
    rw [← this]; abel
  have hGv : Hm⁻¹ *ᵥ u = v - Hm⁻¹ *ᵥ e' := by
    have := hinv v
    rw [hH2, Matrix.mulVec_add] at this
    rw [← this]; abel
  have hmain : blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ v =
      (d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d * cellAvg (psiF0 (L ^ n) w ν) := by
    rw [hv, blockInd_dot_liftSum hG, sum_saw_block0 (ell_eq (IsLevel.bounds hG).2)]
    unfold cellAvg
    have hd1 : ((L ^ n : ℕ) : ℂ) ^ d = ((L ^ n : ℕ) : ℂ) ^ (d - 1) * ((L ^ n : ℕ) : ℂ) := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    have hN : ((L ^ n : ℕ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero _ (NeZero.ne L)
    rw [hd1]; field_simp
  have hsplit : Hm⁻¹ *ᵥ (Hm⁻¹ *ᵥ g) = v - Hm⁻¹ *ᵥ e' - Hm⁻¹ *ᵥ (Hm⁻¹ *ᵥ e) := by
    rw [hGu, Matrix.mulVec_sub, hGv]
  rw [hsplit, dotProduct_sub, dotProduct_sub, hmain]
  have hkd := kernel_decay hG hd hν.le ha hU
  have hCk : 0 ≤ kernelConst d L n := by unfold kernelConst; exact Real.sqrt_nonneg _
  have hdist : ∀ y x : G.Ω 1, Green.torusDist d (N₀ * L ^ K) (y : Torus d (N₀ * L ^ K)) x /
      (L : ℝ) ^ K ≥ 0 := fun y x => by
    have : (0 : ℝ) < (L : ℝ) ^ K := by
      have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
      positivity
    exact div_nonneg (Green.torusDist_nonneg_gen _ _) this.le
  have hE : ∀ (F₂ F₁ F₀ : ZMod (L ^ n) → ℂ), 0 ≤ seamBound d (N₀ * L ^ (K - n)) (cellNorm F₂ F₁ F₀) := by
    intro F₂ F₁ F₀
    unfold seamBound
    have : 0 ≤ cellNorm F₂ F₁ F₀ := Finset.sum_nonneg fun r _ => by positivity
    positivity
  have p1 := pair_small (Hm⁻¹) (fun y x => Green.torusDist d (N₀ * L ^ K) (y : Torus d (N₀ * L ^ K)) x /
    (L : ℝ) ^ K) hCk (hE _ _ _) (agmonRate_pos hd).le (fun x x' => hkd x x')
    (blockInd G (L ^ n) (N₀ * L ^ (K - n))) e'
    (fun y => by unfold blockInd; split_ifs <;> simp)
    (fun x => norm_liftSum_sawErr_le _ _ _ _)
    (fun y x hy hx => seam_sep hG _ _ _ x y hy hx)
  have p2 := pair_small2 (Hm⁻¹) (fun y x => Green.torusDist d (N₀ * L ^ K) (y : Torus d (N₀ * L ^ K)) x /
    (L : ℝ) ^ K) hCk (hE _ _ _) (agmonRate_pos hd).le (fun x x' => hkd x x')
    (fun y z x => by
      have hL : (0 : ℝ) < (L : ℝ) ^ K := by
        have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
        positivity
      rw [← add_div]
      exact div_le_div_of_nonneg_right (Green.torusDist_triangle_gen _ _ _) hL.le)
    (blockInd G (L ^ n) (N₀ * L ^ (K - n))) e
    (fun y => by unfold blockInd; split_ifs <;> simp)
    (fun x => norm_liftSum_sawErr_le _ _ _ _)
    (fun y x hy hx => seam_sep hG _ _ _ x y hy hx)
  calc ‖(d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d * cellAvg (psiF0 (L ^ n) w ν) -
        blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ (Hm⁻¹ *ᵥ e') -
        blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ (Hm⁻¹ *ᵥ (Hm⁻¹ *ᵥ e)) -
        (d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d * cellAvg (psiF0 (L ^ n) w ν)‖
      = ‖blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ (Hm⁻¹ *ᵥ e') +
        blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ (Hm⁻¹ *ᵥ (Hm⁻¹ *ᵥ e))‖ := by
        rw [← norm_neg]; congr 1; ring
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add p1 p2)

theorem card_Ω_level {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} (hG : IsLevel G n) :
    Fintype.card (G.Ω 1) = (N₀ * L ^ K) ^ d := by
  rw [Fintype.card_coe, hG.Ω_one]
  simp [Finset.card_univ, Torus, ZMod.card]

theorem seamBound_le (m N₀' K' : ℕ) (hm : m ≤ N₀' * L ^ K') (cn : ℝ) (hcn : 0 ≤ cn) (d : ℕ) :
    seamBound d m cn ≤ d * (4 * cn * (2 * ((N₀' : ℝ) + 1) * (L : ℝ) ^ K') ^ 2) := by
  unfold seamBound
  have hL : (1 : ℝ) ≤ (L : ℝ) ^ K' := one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hm' : (m : ℝ) ≤ (N₀' : ℝ) * (L : ℝ) ^ K' := by exact_mod_cast hm
  have : (m : ℝ) / 2 + 2 ≤ 2 * ((N₀' : ℝ) + 1) * (L : ℝ) ^ K' := by
    have h0 : (0 : ℝ) ≤ N₀' := Nat.cast_nonneg _
    nlinarith
  have h2 : ((m : ℝ) / 2 + 2) ^ 2 ≤ (2 * ((N₀' : ℝ) + 1) * (L : ℝ) ^ K') ^ 2 :=
    pow_le_pow_left₀ (by positivity) this 2
  gcongr

open Filter Topology in
theorem tendsto_poly_exp (C ε : ℝ) (q : ℕ) (hε : 0 < ε) {Ns : ℕ → ℕ} (hNs : Tendsto Ns atTop atTop) :
    Tendsto (fun j => C * ((Ns j : ℝ) + 1) ^ q * Real.exp (-ε * ((Ns j : ℝ) / 2 - 2))) atTop (𝓝 0) := by
  have h0 : Tendsto (fun y : ℝ => y ^ q * Real.exp (-y)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero q
  have h1 : Tendsto (fun x : ℝ => (ε / 2 * x) ^ q * Real.exp (-(ε / 2 * x))) atTop (𝓝 0) :=
    h0.comp (tendsto_id.const_mul_atTop (half_pos hε))
  have h2 : Tendsto (fun x : ℝ => x ^ q * Real.exp (-(ε / 2) * x)) atTop (𝓝 0) := by
    have := h1.const_mul ((2 / ε) ^ q)
    rw [mul_zero] at this
    refine this.congr fun x => ?_
    rw [← mul_assoc, ← mul_pow, show 2 / ε * (ε / 2 * x) = x by field_simp, neg_mul]
  have h3 : Tendsto (fun j => (Ns j : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ ((tendsto_natCast_atTop_atTop).comp hNs)
  have h4 := (h2.comp h3).const_mul (C * Real.exp (ε / 2 + 2 * ε))
  rw [mul_zero] at h4
  refine h4.congr fun j => ?_
  simp only [Function.comp]
  have : -ε * ((Ns j : ℝ) / 2 - 2) = -(ε / 2) * ((Ns j : ℝ) + 1) + (ε / 2 + 2 * ε) := by ring
  have h5 : Real.exp (-ε * ((Ns j : ℝ) / 2 - 2)) =
      Real.exp (-(ε / 2) * ((Ns j : ℝ) + 1)) * Real.exp (ε / 2 + 2 * ε) := by
    rw [← Real.exp_add, this]
  rw [h5]; ring

open Filter Topology in
/-- **The second moment of the kernel `Q G Q*`**: along tori with `N₀ → ∞` the pairing
`f₀ ⬝ Gm g` tends to `d N^d` times the cell mean of `Φ₀`. -/
theorem moment_R1_tendsto {Ns : ℕ → ℕ} [hne : ∀ j, NeZero (Ns j)] (hNs : Tendsto Ns atTop atTop)
    {n : ℕ} (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 < ν) (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2)
    (ha : IsAdmissibleWeights K a) (Gs : ∀ j, GeneratingSet d L (Ns j) K ϱ)
    (hGs : ∀ j, IsLevel (Gs j) n)
    (hUs : ∀ j, IsUnit (dirichletOperator (Gs j) a ν (0 : (Gs j).Ω 1 → ℂ))) :
    Tendsto (fun j => blockInd (Gs j) (L ^ n) (Ns j * L ^ (K - n)) ⬝ᵥ
        ((dirichletOperator (Gs j) a ν (0 : (Gs j).Ω 1 → ℂ))⁻¹ *ᵥ
          (fun y : (Gs j).Ω 1 => liftSum (d := d)
            (fun s : ZMod (Ns j * L ^ K) => ((sb (L ^ n) (Ns j * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (Ns j * L ^ K)))))
      atTop (𝓝 ((d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d *
        cellAvg (phiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))) := by
  set w := a n / ((L : ℝ) ^ n) ^ 2
  set cn := cellNorm (phiF2 (L ^ n) w ν) (phiF1 (L ^ n) w ν) (phiF0 (L ^ n) w ν)
  have hcn : 0 ≤ cn := Finset.sum_nonneg fun r _ => by positivity
  have hLK : (1 : ℝ) ≤ (L : ℝ) ^ K :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hCk : 0 ≤ kernelConst d L n := by unfold kernelConst; exact Real.sqrt_nonneg _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_)
    (tendsto_poly_exp (((L : ℝ) ^ K) ^ (2 * d) * kernelConst d L n *
      (d * (4 * cn * (2 * (L : ℝ) ^ K) ^ 2))) (agmonRate d) (2 * d + 2)
      (agmonRate_pos hd) hNs)
  refine (moment_R1 (hGs j) hd hν hw ha (hUs j)).trans ?_
  have hcard := card_Ω_level (hGs j)
  have hsb := seamBound_le (L := L) (Ns j * L ^ (K - n)) (Ns j) K
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.sub_le K n)))
    cn hcn d
  have hx : (0 : ℝ) ≤ (Ns j : ℝ) := Nat.cast_nonneg _
  have hc2 : (Fintype.card ((Gs j).Ω 1) : ℝ) ≤ (((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ d := by
    rw [hcard]; push_cast
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have hE : 0 ≤ Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) := (Real.exp_pos _).le
  calc (Fintype.card ((Gs j).Ω 1) : ℝ) ^ 2 * (kernelConst d L n *
        Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) *
        seamBound d (Ns j * L ^ (K - n)) cn)
      ≤ ((((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ d) ^ 2 * (kernelConst d L n *
        Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) *
        (d * (4 * cn * (2 * ((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ 2))) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hc2 2)
          (mul_le_mul_of_nonneg_left hsb (mul_nonneg hCk hE))
          (mul_nonneg (mul_nonneg hCk hE) (by unfold seamBound; positivity)) (by positivity)
    _ = _ := by
        simp only [mul_pow, ← pow_mul]
        generalize ((Ns j : ℝ) + 1) = y
        ring

open Filter Topology in
/-- The same for `Gm Gm`: the pairing `f₀ ⬝ Gm Gm g` tends to `d N^d` times the cell mean of `Ψ₀`. -/
theorem moment_R2_tendsto {Ns : ℕ → ℕ} [hne : ∀ j, NeZero (Ns j)] (hNs : Tendsto Ns atTop atTop)
    {n : ℕ} (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 < ν) (hw : 0 ≤ a n / ((L : ℝ) ^ n) ^ 2)
    (ha : IsAdmissibleWeights K a) (Gs : ∀ j, GeneratingSet d L (Ns j) K ϱ)
    (hGs : ∀ j, IsLevel (Gs j) n)
    (hUs : ∀ j, IsUnit (dirichletOperator (Gs j) a ν (0 : (Gs j).Ω 1 → ℂ))) :
    Tendsto (fun j => blockInd (Gs j) (L ^ n) (Ns j * L ^ (K - n)) ⬝ᵥ
        ((dirichletOperator (Gs j) a ν (0 : (Gs j).Ω 1 → ℂ))⁻¹ *ᵥ
          ((dirichletOperator (Gs j) a ν (0 : (Gs j).Ω 1 → ℂ))⁻¹ *ᵥ
          (fun y : (Gs j).Ω 1 => liftSum (d := d)
            (fun s : ZMod (Ns j * L ^ K) => ((sb (L ^ n) (Ns j * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (Ns j * L ^ K))))))
      atTop (𝓝 ((d : ℂ) * ((L ^ n : ℕ) : ℂ) ^ d *
        cellAvg (psiF0 (L ^ n) (a n / ((L : ℝ) ^ n) ^ 2) ν))) := by
  set w := a n / ((L : ℝ) ^ n) ^ 2
  set cp := cellNorm (psiF2 (L ^ n) w ν) (psiF1 (L ^ n) w ν) (psiF0 (L ^ n) w ν)
  set cf := cellNorm (phiF2 (L ^ n) w ν) (phiF1 (L ^ n) w ν) (phiF0 (L ^ n) w ν)
  have hcp : 0 ≤ cp := Finset.sum_nonneg fun r _ => by positivity
  have hcf : 0 ≤ cf := Finset.sum_nonneg fun r _ => by positivity
  have hLK : (1 : ℝ) ≤ (L : ℝ) ^ K :=
    one_le_pow₀ (by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L))
  have hCk : 0 ≤ kernelConst d L n := by unfold kernelConst; exact Real.sqrt_nonneg _
  set C1 : ℝ := ((L : ℝ) ^ K) ^ (2 * d) * kernelConst d L n * (d * (4 * cp * (2 * (L : ℝ) ^ K) ^ 2))
  set C2 : ℝ := ((L : ℝ) ^ K) ^ (3 * d) * kernelConst d L n ^ 2 *
    (d * (4 * cf * (2 * (L : ℝ) ^ K) ^ 2))
  have hlim := (tendsto_poly_exp C1 (agmonRate d) (2 * d + 2) (agmonRate_pos hd) hNs).add
    (tendsto_poly_exp C2 (agmonRate d) (3 * d + 2) (agmonRate_pos hd) hNs)
  rw [add_zero] at hlim
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun j => norm_nonneg _) (fun j => ?_) hlim
  refine (moment_R2 (hGs j) hd hν hw ha (hUs j)).trans ?_
  have hcard := card_Ω_level (hGs j)
  have hx : (0 : ℝ) ≤ (Ns j : ℝ) := Nat.cast_nonneg _
  have hmle := Nat.mul_le_mul_left (Ns j) (Nat.pow_le_pow_right (Nat.pos_of_ne_zero (NeZero.ne L)) (Nat.sub_le K n))
  have hsbp := seamBound_le (L := L) (Ns j * L ^ (K - n)) (Ns j) K hmle cp hcp d
  have hsbf := seamBound_le (L := L) (Ns j * L ^ (K - n)) (Ns j) K hmle cf hcf d
  have hc2 : (Fintype.card ((Gs j).Ω 1) : ℝ) ≤ (((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ d := by
    rw [hcard]; push_cast
    exact pow_le_pow_left₀ (by positivity) (by nlinarith) d
  have hE : 0 ≤ Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) := (Real.exp_pos _).le
  have hy1 : (1 : ℝ) ≤ (Ns j : ℝ) + 1 := by linarith
  have hsp : 0 ≤ seamBound d (Ns j * L ^ (K - n)) cp := by unfold seamBound; positivity
  have hsf : 0 ≤ seamBound d (Ns j * L ^ (K - n)) cf := by unfold seamBound; positivity
  have t1 : (Fintype.card ((Gs j).Ω 1) : ℝ) ^ 2 * (kernelConst d L n *
        Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) * seamBound d (Ns j * L ^ (K - n)) cp)
      ≤ C1 * ((Ns j : ℝ) + 1) ^ (2 * d + 2) * Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) := by
    calc _ ≤ ((((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ d) ^ 2 * (kernelConst d L n *
        Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) *
        (d * (4 * cp * (2 * ((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ 2))) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hc2 2)
          (mul_le_mul_of_nonneg_left hsbp (mul_nonneg hCk hE))
          (mul_nonneg (mul_nonneg hCk hE) hsp) (by positivity)
      _ = _ := by
        simp only [mul_pow, ← pow_mul, C1]
        generalize ((Ns j : ℝ) + 1) = y
        ring
  have t2 : (Fintype.card ((Gs j).Ω 1) : ℝ) ^ 3 * (kernelConst d L n ^ 2 *
        Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) * seamBound d (Ns j * L ^ (K - n)) cf)
      ≤ C2 * ((Ns j : ℝ) + 1) ^ (3 * d + 2) * Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) := by
    calc _ ≤ ((((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ d) ^ 3 * (kernelConst d L n ^ 2 *
        Real.exp (-(agmonRate d) * ((Ns j : ℝ) / 2 - 2)) *
        (d * (4 * cf * (2 * ((Ns j : ℝ) + 1) * (L : ℝ) ^ K) ^ 2))) :=
        mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg _) hc2 3)
          (mul_le_mul_of_nonneg_left hsbf (mul_nonneg (pow_nonneg hCk 2) hE))
          (mul_nonneg (mul_nonneg (pow_nonneg hCk 2) hE) hsf) (by positivity)
      _ = _ := by
        simp only [mul_pow, ← pow_mul, C2]
        generalize ((Ns j : ℝ) + 1) = y
        ring
  exact add_le_add t1 t2

end Balaban.Flow
