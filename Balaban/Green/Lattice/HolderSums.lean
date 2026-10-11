/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.LocGreenSums
public import Balaban.Green.Lattice.HolderKernel

/-!
# Hölder sums of the lattice Green's function

For `θ ∈ (0, 1)`, `r ≥ 1`, a translation `a` with `‖a‖ ≤ r`, and a finite set `A ⊂ ℤ^d` with at
most as many points as the ball `B_R(0)`,

`∑_{z ∈ A} |F_ν(y₀ - z + a) - F_ν(y₀ - z)| ≤ (c/θ) (r + r^{1-θ} (R+1)^θ)`,

where `F_ν(y) = C(y + e_ν) - C(y)`.  (This is the last sum in Lemma Loc (c); the bound
`r (1 + log (ρ/r)) ≤ θ⁻¹ r^{1-θ} ρ^θ` of the plan is obtained directly from `⟨w⟩^{θ-d}`.)
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

variable {d : ℕ}

theorem card_latticeBall_translate (x₀ : Fin d → ℤ) (r : ℝ) :
    (latticeBall x₀ r).card = (latticeBall (0 : Fin d → ℤ) r).card := by
  unfold latticeBall
  rw [Fintype.card_piFinset, Fintype.card_piFinset]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Int.card_Icc, Int.card_Icc]
  simp only [Pi.zero_apply]
  congr 1
  ring

/-- `∑_{m < N} (m+1)^{θ-1} ≤ N^θ / θ`. -/
theorem sum_range_rpow_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (N : ℕ) :
    ∑ m ∈ Finset.range N, ((m : ℝ) + 1) ^ (θ - 1) ≤ (N : ℝ) ^ θ / θ := by
  induction N with
  | zero => simp [Real.zero_rpow hθ0.ne']
  | succ N ih =>
      rw [Finset.sum_range_succ]
      have hn : (0 : ℝ) < (N : ℝ) + 1 := by positivity
      have key : θ * ((N : ℝ) + 1) ^ (θ - 1) ≤ ((N : ℝ) + 1) ^ θ - (N : ℝ) ^ θ := by
        have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
        have h1 : (N : ℝ) = ((N : ℝ) + 1) * (1 + (-(1 / ((N : ℝ) + 1)))) := by
          field_simp; ring
        have hs : (-1 : ℝ) ≤ -(1 / ((N : ℝ) + 1)) := by
          have : 1 / ((N : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hn]; linarith
          linarith
        have h2 := rpow_one_add_le_one_add_mul_self hs hθ0.le hθ1
        have h3 : (N : ℝ) ^ θ = ((N : ℝ) + 1) ^ θ * (1 + (-(1 / ((N : ℝ) + 1)))) ^ θ := by
          conv_lhs => rw [h1]
          rw [Real.mul_rpow hn.le (by linarith)]
        have h4 : ((N : ℝ) + 1) ^ (θ - 1) = ((N : ℝ) + 1) ^ θ / ((N : ℝ) + 1) :=
          Real.rpow_sub_one hn.ne' θ
        rw [h3, h4]
        have h5 : 0 ≤ ((N : ℝ) + 1) ^ θ := by positivity
        calc θ * (((N : ℝ) + 1) ^ θ / ((N : ℝ) + 1)) =
            ((N : ℝ) + 1) ^ θ - ((N : ℝ) + 1) ^ θ * (1 + θ * (-(1 / ((N : ℝ) + 1)))) := by
              field_simp; ring
          _ ≤ ((N : ℝ) + 1) ^ θ - ((N : ℝ) + 1) ^ θ * (1 + (-(1 / ((N : ℝ) + 1)))) ^ θ := by
              have := mul_le_mul_of_nonneg_left h2 h5
              linarith
      push_cast
      have : ((N : ℝ) + 1) ^ (θ - 1) ≤ (((N : ℝ) + 1) ^ θ - (N : ℝ) ^ θ) / θ := by
        rw [le_div_iff₀ hθ0]; linarith
      calc _ ≤ (N : ℝ) ^ θ / θ + (((N : ℝ) + 1) ^ θ - (N : ℝ) ^ θ) / θ := add_le_add ih this
        _ = _ := by ring

theorem sum_ball_rpow_le (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {R : ℝ} (hR : 0 ≤ R) :
    ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, (1 + ‖w‖) ^ (θ - (d : ℝ)) ≤
      d * 2 ^ d * (R + 1) ^ θ / θ := by
  set M := ⌊R⌋₊ with hM
  have hball : latticeBall (0 : Fin d → ℤ) R = latticeBall 0 (M : ℝ) := by
    ext w
    rw [mem_latticeBall hR, mem_latticeBall (r := (M : ℝ)) (Nat.cast_nonneg _), sub_zero,
      norm_eq_latticeNorm]
    rw [← Nat.le_floor_iff hR]
    exact (Nat.cast_le (α := ℝ)).symm
  rw [hball]
  have hmaps : ∀ w ∈ latticeBall (0 : Fin d → ℤ) (M : ℝ), latticeNorm w ∈ Finset.range (M + 1) :=
    fun w hw => Finset.mem_range.2 (Nat.lt_succ_of_le (mem_latticeBall_nat.1 hw))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ m ∈ Finset.range (M + 1),
      ∑ w ∈ (latticeBall (0 : Fin d → ℤ) (M : ℝ)).filter (fun w => latticeNorm w = m),
        (1 + ‖w‖) ^ (θ - (d : ℝ)) ≤ d * 2 ^ d * ((m : ℝ) + 1) ^ (θ - 1) := by
    intro m hm
    have hmM : m ≤ M := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    have h1 : ∀ w ∈ (latticeBall (0 : Fin d → ℤ) (M : ℝ)).filter (fun w => latticeNorm w = m),
        (1 + ‖w‖) ^ (θ - (d : ℝ)) = (1 + (m : ℝ)) ^ (θ - (d : ℝ)) := by
      intro w hw
      rw [norm_eq_latticeNorm, (Finset.mem_filter.1 hw).2]
    rw [Finset.sum_congr rfl h1, Finset.sum_const, nsmul_eq_mul]
    have h2 := card_fiber_le hd m M hmM
    have hpos : 0 < ((m : ℝ) + 1) := by positivity
    have e : ((m : ℝ) + 1) ^ (d - 1) * (1 + (m : ℝ)) ^ (θ - (d : ℝ)) =
        ((m : ℝ) + 1) ^ (θ - 1) := by
      rw [add_comm (1 : ℝ) m, ← Real.rpow_natCast, ← Real.rpow_add hpos]
      congr 1
      rw [Nat.cast_sub hd]
      push_cast
      ring
    have hnn : 0 ≤ (1 + (m : ℝ)) ^ (θ - (d : ℝ)) := by positivity
    calc _ ≤ (d * 2 ^ d * ((m : ℝ) + 1) ^ (d - 1)) * (1 + (m : ℝ)) ^ (θ - (d : ℝ)) :=
          mul_le_mul_of_nonneg_right h2 hnn
      _ = d * 2 ^ d * (((m : ℝ) + 1) ^ (d - 1) * (1 + (m : ℝ)) ^ (θ - (d : ℝ))) := by ring
      _ = _ := by rw [e]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have h3 := sum_range_rpow_le hθ0 hθ1 (M + 1)
  have h4 : ((M + 1 : ℕ) : ℝ) ^ θ ≤ (R + 1) ^ θ := by
    apply Real.rpow_le_rpow (by positivity) _ hθ0.le
    push_cast
    linarith [Nat.floor_le hR]
  have hc : (0 : ℝ) ≤ d * 2 ^ d := by positivity
  calc _ ≤ d * 2 ^ d * (((M + 1 : ℕ) : ℝ) ^ θ / θ) := mul_le_mul_of_nonneg_left h3 hc
    _ ≤ d * 2 ^ d * ((R + 1) ^ θ / θ) := by
        apply mul_le_mul_of_nonneg_left _ hc
        exact div_le_div_of_nonneg_right h4 hθ0.le
    _ = _ := by ring

/-- **The Hölder sum.** -/
theorem green_holder_sum (hd : 3 ≤ d) :
    ∃ cH : ℝ, 0 ≤ cH ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {r : ℝ}, 1 ≤ r → ∀ (a : Fin d → ℤ),
      ‖a‖ ≤ r → ∀ (ν : Fin d) {R : ℝ}, 0 ≤ R → ∀ (A : Finset (Fin d → ℤ)),
      A.card ≤ (latticeBall (0 : Fin d → ℤ) R).card → ∀ y0 : Fin d → ℤ,
      ∑ z ∈ A, |greenDiff d ν (y0 - z + a) - greenDiff d ν (y0 - z)| ≤
        cH / θ * (r + r ^ (1 - θ) * (R + 1) ^ θ) := by
  classical
  obtain ⟨c1, hc1, h1⟩ := latticeGreen_diff1_le hd
  obtain ⟨ck, hck, hk⟩ := greenDiff_translate_bounds hd
  have hd1 : 1 ≤ d := by omega
  refine ⟨6 * c1 * (d * 2 ^ d) + ck * (d * 2 ^ d), by positivity, ?_⟩
  intro θ hθ0 hθ1 r hr a har ν R hR A hA y0
  have hr0 : 0 < r := by linarith
  have hgd : ∀ y : Fin d → ℤ, |greenDiff d ν y| ≤ c1 / (1 + ‖y‖) ^ (d - 1) := fun y => h1 y ν
  set P : (Fin d → ℤ) → Prop := fun z => ‖y0 - z‖ < 2 * r with hP
  rw [← Finset.sum_filter_add_sum_filter_not A P]
  -- near part
  have hnear : ∑ z ∈ A.filter P, |greenDiff d ν (y0 - z + a) - greenDiff d ν (y0 - z)| ≤
      6 * c1 * (d * 2 ^ d) * r := by
    set An := A.filter P with hAn
    have hcard : An.card ≤ (latticeBall (0 : Fin d → ℤ) (2 * r)).card := by
      rw [← card_latticeBall_translate y0 (2 * r)]
      apply Finset.card_le_card
      intro z hz
      have hzP := (Finset.mem_filter.1 hz).2
      rw [mem_latticeBall (by linarith), ← norm_neg, neg_sub]
      exact hzP.le
    have hφ : ∀ (y1 : Fin d → ℤ), ∑ z ∈ An, c1 * (1 / (1 + ‖y1 - z‖) ^ (d - 1)) ≤
        c1 * (d * 2 ^ d * (2 * r + 1)) := by
      intro y1
      have hs := sum_translate_le (fun s => c1 * (1 / (1 + s) ^ (d - 1)))
        (fun s hs => by positivity)
        (fun s s' hs hss => by
          have : (1 + s) ^ (d - 1) ≤ (1 + s') ^ (d - 1) :=
            pow_le_pow_left₀ (by linarith) (by linarith) _
          have h2 : 0 < (1 + s) ^ (d - 1) := by positivity
          exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h2 this) hc1)
        (by linarith : (0 : ℝ) ≤ 2 * r) An hcard y1
      refine hs.trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hc1
      have := sum_ball_pow_le hd1 (p := 1) le_rfl (by omega) (by linarith : (0 : ℝ) ≤ 2 * r)
      simpa using this
    have hsplit : ∀ z ∈ An, |greenDiff d ν (y0 - z + a) - greenDiff d ν (y0 - z)| ≤
        c1 * (1 / (1 + ‖y0 + a - z‖) ^ (d - 1)) + c1 * (1 / (1 + ‖y0 - z‖) ^ (d - 1)) := by
      intro z _
      refine (abs_sub _ _).trans (add_le_add ?_ ?_)
      · have e : y0 - z + a = y0 + a - z := by abel
        rw [e, mul_one_div]; exact hgd _
      · rw [mul_one_div]; exact hgd _
    refine (Finset.sum_le_sum hsplit).trans ?_
    rw [Finset.sum_add_distrib]
    calc _ ≤ c1 * (d * 2 ^ d * (2 * r + 1)) + c1 * (d * 2 ^ d * (2 * r + 1)) :=
          add_le_add (hφ _) (hφ _)
      _ ≤ _ := by
          have h5 : 0 ≤ c1 * ((d : ℝ) * 2 ^ d) := by positivity
          nlinarith [mul_nonneg h5 (by linarith : (0 : ℝ) ≤ r - 1)]
  -- far part
  have hfar : ∑ z ∈ A.filter (fun z => ¬ P z),
      |greenDiff d ν (y0 - z + a) - greenDiff d ν (y0 - z)| ≤
      ck * (d * 2 ^ d) * (r ^ (1 - θ) * (R + 1) ^ θ) / θ := by
    set φ : ℝ → ℝ := fun s => ck * r ^ (1 - θ) * (1 + s) ^ (θ - (d : ℝ)) with hφdef
    have hφ0 : ∀ s, 0 ≤ s → 0 ≤ φ s := fun s hs => by positivity
    have hφm : ∀ s s', 0 ≤ s → s ≤ s' → φ s' ≤ φ s := by
      intro s s' hs hss
      have : (1 + s') ^ (θ - (d : ℝ)) ≤ (1 + s) ^ (θ - (d : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by
          have : (1 : ℝ) ≤ d := by exact_mod_cast hd1
          linarith)
      exact mul_le_mul_of_nonneg_left this (by positivity)
    have hterm : ∀ z ∈ A.filter (fun z => ¬ P z),
        |greenDiff d ν (y0 - z + a) - greenDiff d ν (y0 - z)| ≤ φ ‖y0 - z‖ := by
      intro z hz
      have hzP : 2 * r ≤ ‖y0 - z‖ := not_lt.1 (Finset.mem_filter.1 hz).2
      have hb := (hk ν a r har (y0 - z) (by linarith [norm_nonneg (y0 - z)])).1
      refine hb.trans ?_
      have hw : 0 < 1 + ‖y0 - z‖ := by linarith [norm_nonneg (y0 - z)]
      have hrw : r ≤ 1 + ‖y0 - z‖ := by linarith
      have e1 : r = r ^ (1 - θ) * r ^ θ := by
        rw [← Real.rpow_add hr0]; simp
      have e2 : r ^ θ ≤ (1 + ‖y0 - z‖) ^ θ := Real.rpow_le_rpow hr0.le hrw hθ0.le
      have e3 : (1 + ‖y0 - z‖) ^ (θ - (d : ℝ)) = (1 + ‖y0 - z‖) ^ θ / (1 + ‖y0 - z‖) ^ d := by
        rw [Real.rpow_sub hw, Real.rpow_natCast]
      simp only [hφdef]
      rw [e3]
      calc ck * r / (1 + ‖y0 - z‖) ^ d = ck * (r ^ (1 - θ) * r ^ θ) / (1 + ‖y0 - z‖) ^ d := by
            rw [← e1]
        _ ≤ ck * (r ^ (1 - θ) * (1 + ‖y0 - z‖) ^ θ) / (1 + ‖y0 - z‖) ^ d := by
            gcongr
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hsub : ∑ z ∈ A.filter (fun z => ¬ P z), φ ‖y0 - z‖ ≤ ∑ z ∈ A, φ ‖y0 - z‖ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun z _ _ => hφ0 _ (norm_nonneg _))
    refine hsub.trans ((sum_translate_le φ hφ0 hφm hR A hA y0).trans ?_)
    simp only [hφdef]
    rw [← Finset.mul_sum]
    have := sum_ball_rpow_le hd1 hθ0 hθ1.le hR
    calc ck * r ^ (1 - θ) * ∑ w ∈ latticeBall (0 : Fin d → ℤ) R, (1 + ‖w‖) ^ (θ - (d : ℝ)) ≤
        ck * r ^ (1 - θ) * (d * 2 ^ d * (R + 1) ^ θ / θ) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = _ := by ring
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hX : 0 ≤ r ^ (1 - θ) * (R + 1) ^ θ := by positivity
  have hr' : 0 ≤ (6 * c1 * (d * 2 ^ d)) := by positivity
  have hck' : 0 ≤ ck * (d * 2 ^ d) := by positivity
  calc _ ≤ 6 * c1 * (d * 2 ^ d) * r + ck * (d * 2 ^ d) * (r ^ (1 - θ) * (R + 1) ^ θ) / θ :=
        add_le_add hnear hfar
    _ ≤ 6 * c1 * (d * 2 ^ d) * (1 / θ) * r + ck * (d * 2 ^ d) * (1 / θ) *
        (r ^ (1 - θ) * (R + 1) ^ θ) := by
        have a1 : 6 * c1 * (d * 2 ^ d) * r ≤ 6 * c1 * (d * 2 ^ d) * (1 / θ) * r := by
          have := mul_le_mul_of_nonneg_left hθ' hr'
          nlinarith
        have a2 : ck * (d * 2 ^ d) * (r ^ (1 - θ) * (R + 1) ^ θ) / θ =
            ck * (d * 2 ^ d) * (1 / θ) * (r ^ (1 - θ) * (R + 1) ^ θ) := by ring
        linarith
    _ ≤ _ := by
        have h1 : 0 ≤ 6 * c1 * (d * 2 ^ d) * (1 / θ) * (r ^ (1 - θ) * (R + 1) ^ θ) := by
          positivity
        have h2 : 0 ≤ ck * (d * 2 ^ d) * (1 / θ) * r := by positivity
        have e : (6 * c1 * (d * 2 ^ d) + ck * (d * 2 ^ d)) / θ * (r + r ^ (1 - θ) * (R + 1) ^ θ) =
            (6 * c1 * (d * 2 ^ d) * (1 / θ) * r + ck * (d * 2 ^ d) * (1 / θ) *
              (r ^ (1 - θ) * (R + 1) ^ θ)) +
            6 * c1 * (d * 2 ^ d) * (1 / θ) * (r ^ (1 - θ) * (R + 1) ^ θ) +
            ck * (d * 2 ^ d) * (1 / θ) * r := by ring
        rw [e]
        linarith

end Balaban.LatticeGreen
