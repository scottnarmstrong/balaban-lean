/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.Lattice.Main

/-!
# Lemma K: third differences of the lattice Green's function

`|∂_μ ∂_ν ∂_λ C(x)| ≤ c ⟨x⟩^{-d-1}` for all directions and all sign choices (forward and
backward differences).  Mixed third differences (no coordinate occurs three times) are integrals of
`heatDiffProd` with per-coordinate orders `≤ 2` (`latticeGreen_thirdDiff_mixed_le`).  A pure third
difference in one direction is reduced to mixed ones through `-ΔC = δ₀` away from the origin
(`latticeGreen_thirdDiff_pure_le`).
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open MeasureTheory Real Set Filter Topology

variable {d : ℕ}

/-- The third difference `Δ_c Δ_b Δ_a G (x)`. -/
def thirdDiff {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b c x : V) : ℝ :=
  secondDiff G a b (x + c) - secondDiff G a b x

theorem thirdDiff_neg_left {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b c x : V) :
    thirdDiff G (-a) b c x = -thirdDiff G a b c (x + -a) := by
  unfold thirdDiff
  rw [secondDiff_neg_left, secondDiff_neg_left, add_right_comm x c (-a)]
  ring

theorem thirdDiff_neg_mid {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b c x : V) :
    thirdDiff G a (-b) c x = -thirdDiff G a b c (x + -b) := by
  unfold thirdDiff
  rw [secondDiff_neg_right, secondDiff_neg_right, add_right_comm x c (-b)]
  ring

theorem thirdDiff_neg_right {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b c x : V) :
    thirdDiff G a b (-c) x = -thirdDiff G a b c (x + -c) := by
  unfold thirdDiff
  rw [neg_add_cancel_right]
  ring

/-- A mixed third difference is the integral of `heatDiffProd`. -/
theorem thirdDiff_eq_integral (hd : 3 ≤ d) (x : Fin d → ℤ) (μ ν l : Fin d) :
    thirdDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) (Pi.single l 1) x =
      ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1 + Pi.single ν 1 + Pi.single l 1) t x := by
  have hm2 : ∀ ρ, (Pi.single μ 1 + Pi.single ν 1 : Fin d → ℕ) ρ ≤ 2 := fun ρ => by
    simp only [Pi.add_apply, Pi.single_apply]; split_ifs <;> omega
  have hi : ∀ y : Fin d → ℤ, IntegrableOn
      (fun t => heatDiffProd d (Pi.single μ 1 + Pi.single ν 1 : Fin d → ℕ) t y) (Ioi 0) := by
    intro y
    obtain ⟨C, _, hC⟩ := heatDiffProd_integral_bound hd _ hm2
    exact (hC y).1
  have e1 : secondDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) (x + Pi.single l 1) =
      ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1 + Pi.single ν 1) t (x + Pi.single l 1) :=
    latticeGreen_shift_shift_sub hd (x + Pi.single l 1) μ ν
  have e2 : secondDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) x =
      ∫ t in Ioi 0, heatDiffProd d (Pi.single μ 1 + Pi.single ν 1) t x :=
    latticeGreen_shift_shift_sub hd x μ ν
  unfold thirdDiff
  rw [e1, e2, ← integral_sub (hi _) (hi _)]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ => heatDiffProd_shift _ l t x

/-- Mixed third differences (no direction used three times). -/
theorem latticeGreen_thirdDiff_mixed_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ ν l : Fin d), ¬ (μ = ν ∧ ν = l) →
      |thirdDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) (Pi.single l 1) x| ≤
        c / (1 + ‖x‖) ^ (d + 1) := by
  have h : ∀ p : Fin d × Fin d × Fin d, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Fin d → ℤ,
      ¬ (p.1 = p.2.1 ∧ p.2.1 = p.2.2) →
      |thirdDiff (latticeGreen d) (Pi.single p.1 1) (Pi.single p.2.1 1) (Pi.single p.2.2 1) x| ≤
        C / (1 + ‖x‖) ^ (d + 1) := by
    rintro ⟨μ, ν, l⟩
    by_cases hc : μ = ν ∧ ν = l
    · exact ⟨0, le_rfl, fun x hx => absurd hc hx⟩
    have hm : ∀ ρ, (Pi.single μ 1 + Pi.single ν 1 + Pi.single l 1 : Fin d → ℕ) ρ ≤ 2 := by
      intro ρ
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs <;> omega
    obtain ⟨C, hC0, hC⟩ := heatDiffProd_integral_bound hd _ hm
    refine ⟨C, hC0, fun x _ => ?_⟩
    rw [thirdDiff_eq_integral hd]
    have hx := (hC x).2
    have hs : d + ∑ ρ, (Pi.single μ 1 + Pi.single ν 1 + Pi.single l 1 : Fin d → ℕ) ρ - 2 =
        d + 1 := by
      simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single']
      simp
    rw [hs] at hx
    exact (abs_setIntegral_le _).trans hx
  choose C hC0 hC using h
  refine ⟨∑ p, C p, Finset.sum_nonneg fun p _ => hC0 p, fun x μ ν l hne => ?_⟩
  exact (hC (μ, ν, l) x hne).trans (div_le_div_of_nonneg_right
    (Finset.single_le_sum (fun j _ => hC0 j) (Finset.mem_univ (μ, ν, l)))
    (pow_nonneg (by linarith [norm_nonneg x]) _))

/-- The centred second difference `C(y+e_ν) + C(y-e_ν) - 2C(y)` in direction `ν`. -/
def centSecond (G : (Fin d → ℤ) → ℝ) (ν : Fin d) (y : Fin d → ℤ) : ℝ :=
  G (y + Pi.single ν 1) + G (y - Pi.single ν 1) - 2 * G y

theorem sum_centSecond (hd : 3 ≤ d) (y : Fin d → ℤ) :
    ∑ ν, centSecond (latticeGreen d) ν y = -(if y = 0 then 1 else 0) := by
  have h := latticeGreen_equation hd y
  rw [← h, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  unfold centSecond
  ring

theorem thirdDiff_pure_eq (G : (Fin d → ℤ) → ℝ) (μ : Fin d) (x : Fin d → ℤ) :
    thirdDiff G (Pi.single μ 1) (Pi.single μ 1) (Pi.single μ 1) x =
      centSecond G μ (x + Pi.single μ 1 + Pi.single μ 1) -
        centSecond G μ (x + Pi.single μ 1) := by
  unfold thirdDiff secondDiff centSecond
  simp only [add_sub_cancel_right]
  ring

theorem centSecond_shift_eq (G : (Fin d → ℤ) → ℝ) (ν μ : Fin d) (w : Fin d → ℤ) :
    centSecond G ν (w + Pi.single ν 1 + Pi.single μ 1) - centSecond G ν (w + Pi.single ν 1) =
      thirdDiff G (Pi.single ν 1) (Pi.single ν 1) (Pi.single μ 1) w := by
  unfold thirdDiff secondDiff centSecond
  have e1 : w + Pi.single ν 1 + Pi.single μ 1 + Pi.single ν 1 =
      w + Pi.single μ 1 + Pi.single ν 1 + Pi.single ν 1 := by abel
  have e2 : w + Pi.single ν 1 + Pi.single μ 1 - Pi.single ν 1 = w + Pi.single μ 1 := by abel
  have e3 : w + Pi.single ν 1 + Pi.single μ 1 = w + Pi.single μ 1 + Pi.single ν 1 := by abel
  rw [e1, e2, e3]
  simp only [add_sub_cancel_right]
  ring

/-- A pure third difference, via `-ΔC = δ₀` away from the origin. -/
theorem latticeGreen_thirdDiff_pure_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ : Fin d),
      |thirdDiff (latticeGreen d) (Pi.single μ 1) (Pi.single μ 1) (Pi.single μ 1) x| ≤
        c / (1 + ‖x‖) ^ (d + 1) := by
  obtain ⟨cm, hcm0, hcm⟩ := latticeGreen_thirdDiff_mixed_le hd
  obtain ⟨c0, hc00, hc0⟩ := latticeGreen_le hd
  have hCb : ∀ y : Fin d → ℤ, |latticeGreen d y| ≤ c0 := by
    intro y
    rw [abs_of_nonneg (latticeGreen_nonneg y)]
    refine (hc0 y).trans ?_
    have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ (d - 2) := one_le_pow₀ (by linarith [norm_nonneg y])
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  refine ⟨max (d * cm * 3 ^ (d + 1)) (8 * c0 * 3 ^ (d + 1)), by positivity, fun x μ => ?_⟩
  have hpos : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
  have hnorm : ‖(Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := norm_pi_single_le μ
  by_cases hsmall : x + Pi.single μ 1 = 0 ∨ x + Pi.single μ 1 + Pi.single μ 1 = 0
  · -- `‖x‖ ≤ 2`
    have hx : ‖x‖ ≤ 2 := by
      rcases hsmall with h | h
      · have : x = -Pi.single μ 1 := eq_neg_of_add_eq_zero_left h
        rw [this, norm_neg]; linarith
      · have : x = -(Pi.single μ 1 + Pi.single μ 1) := by
          rw [add_assoc] at h; exact eq_neg_of_add_eq_zero_left h
        rw [this, norm_neg]
        exact (norm_add_le _ _).trans (by linarith)
    have h8 : |thirdDiff (latticeGreen d) (Pi.single μ 1) (Pi.single μ 1) (Pi.single μ 1) x| ≤
        8 * c0 := by
      unfold thirdDiff secondDiff
      have := hCb (x + Pi.single μ 1 + Pi.single μ 1 + Pi.single μ 1)
      have := hCb (x + Pi.single μ 1 + Pi.single μ 1)
      have := hCb (x + Pi.single μ 1)
      have := hCb x
      have key : ∀ a b c d' e f g h : ℝ, |a| ≤ c0 → |b| ≤ c0 → |c| ≤ c0 → |d'| ≤ c0 → 
          |e| ≤ c0 → |f| ≤ c0 → |g| ≤ c0 → |h| ≤ c0 →
          |a - b - c + d' - (e - f - g + h)| ≤ 8 * c0 := by
        intro a b c d' e f g h ha hb hc hd he hf hg hh
        rw [abs_le] at *
        constructor <;> linarith [ha.1, ha.2, hb.1, hb.2, hc.1, hc.2, hd.1, hd.2, he.1, he.2,
          hf.1, hf.2, hg.1, hg.2, hh.1, hh.2]
      exact key _ _ _ _ _ _ _ _ (hCb _) (hCb _) (hCb _) (hCb _) (hCb _) (hCb _) (hCb _) (hCb _)
    refine h8.trans ?_
    rw [le_div_iff₀ hpos]
    have h3 : (1 + ‖x‖) ^ (d + 1) ≤ 3 ^ (d + 1) := pow_le_pow_left₀ (by positivity) (by linarith) _
    have : 0 ≤ 8 * c0 := by positivity
    calc 8 * c0 * (1 + ‖x‖) ^ (d + 1) ≤ 8 * c0 * 3 ^ (d + 1) := mul_le_mul_of_nonneg_left h3 this
      _ ≤ _ := le_max_right _ _
  · push Not at hsmall
    obtain ⟨hs1, hs2⟩ := hsmall
    set p1 := x + Pi.single μ 1 with hp1
    have hsum := fun p => sum_centSecond hd p
    have hS : ∀ p : Fin d → ℤ, p ≠ 0 →
        centSecond (latticeGreen d) μ p = -∑ ν ∈ Finset.univ.erase μ, centSecond (latticeGreen d) ν p := by
      intro p hp
      have h := hsum p
      rw [show (if p = 0 then (1 : ℝ) else 0) = 0 from by simp [hp],
        ← Finset.add_sum_erase _ _ (Finset.mem_univ μ)] at h
      linarith
    have e : centSecond (latticeGreen d) μ (p1 + Pi.single μ 1) -
        centSecond (latticeGreen d) μ p1 =
        -∑ ν ∈ Finset.univ.erase μ, (centSecond (latticeGreen d) ν (p1 + Pi.single μ 1) -
          centSecond (latticeGreen d) ν p1) := by
      rw [hS _ hs2, hS _ hs1, Finset.sum_sub_distrib]
      ring
    rw [thirdDiff_pure_eq, e, abs_neg]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ ν ∈ Finset.univ.erase μ,
        |centSecond (latticeGreen d) ν (p1 + Pi.single μ 1) - centSecond (latticeGreen d) ν p1| ≤
          3 ^ (d + 1) * cm / (1 + ‖x‖) ^ (d + 1) := by
      intro ν hν
      have hνμ : ν ≠ μ := Finset.ne_of_mem_erase hν
      have e2 : centSecond (latticeGreen d) ν (p1 + Pi.single μ 1) -
          centSecond (latticeGreen d) ν p1 =
          thirdDiff (latticeGreen d) (Pi.single ν 1) (Pi.single ν 1) (Pi.single μ 1)
            (x + (Pi.single μ 1 - Pi.single ν 1)) := by
        rw [← centSecond_shift_eq]
        have : x + (Pi.single μ 1 - Pi.single ν 1) + Pi.single ν 1 = p1 := by
          rw [hp1]; abel
        rw [this]
      rw [e2]
      have hF := bound_translate (F := fun y => thirdDiff (latticeGreen d) (Pi.single ν 1)
        (Pi.single ν 1) (Pi.single μ 1) y) hcm0
        (fun y => hcm y ν ν μ (by rintro ⟨h1, h2⟩; exact hνμ h2)) x
        (Pi.single μ 1 - Pi.single ν 1) (r := 2) ((norm_sub_le _ _).trans
          (by linarith [norm_pi_single_le (d := d) μ, norm_pi_single_le (d := d) ν]))
      have e3 : ((1 : ℝ) + 2) ^ (d + 1) = 3 ^ (d + 1) := by norm_num
      rw [e3] at hF
      exact hF
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hcard : ((Finset.univ.erase μ).card : ℝ) ≤ d := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ μ)]
      simp
    calc _ ≤ (d : ℝ) * (3 ^ (d + 1) * cm / (1 + ‖x‖) ^ (d + 1)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = (d * cm * 3 ^ (d + 1)) / (1 + ‖x‖) ^ (d + 1) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (le_max_left _ _) hpos.le

/-- Lemma K, third differences, forward. -/
theorem latticeGreen_thirdDiff_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ ν l : Fin d),
      |thirdDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) (Pi.single l 1) x| ≤
        c / (1 + ‖x‖) ^ (d + 1) := by
  obtain ⟨c1, hc1, h1⟩ := latticeGreen_thirdDiff_mixed_le hd
  obtain ⟨c2, hc2, h2⟩ := latticeGreen_thirdDiff_pure_le hd
  refine ⟨max c1 c2, le_max_of_le_left hc1, fun x μ ν l => ?_⟩
  have hpos : 0 < (1 + ‖x‖) ^ (d + 1) := by positivity
  by_cases hc : μ = ν ∧ ν = l
  · obtain ⟨rfl, rfl⟩ := hc
    exact (h2 x μ).trans (div_le_div_of_nonneg_right (le_max_right _ _) hpos.le)
  · exact (h1 x μ ν l hc).trans (div_le_div_of_nonneg_right (le_max_left _ _) hpos.le)

theorem thirdDiff_bound_flip_left {G : (Fin d → ℤ) → ℝ} {a b c : Fin d → ℤ} {c0 : ℝ}
    (hc0 : 0 ≤ c0) (ha : ‖a‖ ≤ 1) {k : ℕ}
    (h : ∀ y, |thirdDiff G a b c y| ≤ c0 / (1 + ‖y‖) ^ k) :
    ∀ y, |thirdDiff G (-a) b c y| ≤ 2 ^ k * c0 / (1 + ‖y‖) ^ k := by
  intro y
  rw [thirdDiff_neg_left, abs_neg]
  have := bound_translate (F := fun y => thirdDiff G a b c y) hc0 h y (-a) (r := 1)
    (by simpa using ha)
  norm_num at this
  exact this

theorem thirdDiff_bound_flip_mid {G : (Fin d → ℤ) → ℝ} {a b c : Fin d → ℤ} {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hb : ‖b‖ ≤ 1) {k : ℕ}
    (h : ∀ y, |thirdDiff G a b c y| ≤ c0 / (1 + ‖y‖) ^ k) :
    ∀ y, |thirdDiff G a (-b) c y| ≤ 2 ^ k * c0 / (1 + ‖y‖) ^ k := by
  intro y
  rw [thirdDiff_neg_mid, abs_neg]
  have := bound_translate (F := fun y => thirdDiff G a b c y) hc0 h y (-b) (r := 1)
    (by simpa using hb)
  norm_num at this
  exact this

theorem thirdDiff_bound_flip_right {G : (Fin d → ℤ) → ℝ} {a b c : Fin d → ℤ} {c0 : ℝ}
    (hc0 : 0 ≤ c0) (hc : ‖c‖ ≤ 1) {k : ℕ}
    (h : ∀ y, |thirdDiff G a b c y| ≤ c0 / (1 + ‖y‖) ^ k) :
    ∀ y, |thirdDiff G a b (-c) y| ≤ 2 ^ k * c0 / (1 + ‖y‖) ^ k := by
  intro y
  rw [thirdDiff_neg_right, abs_neg]
  have := bound_translate (F := fun y => thirdDiff G a b c y) hc0 h y (-c) (r := 1)
    (by simpa using hc)
  norm_num at this
  exact this

/-- **Lemma K, third differences, all sign combinations:**
`|∂_μ ∂_ν ∂_λ C(x)| ≤ c ⟨x⟩^{-d-1}` for forward and backward differences. -/
theorem latticeGreen_diff3_signs_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ ν l : Fin d) (σ τ υ : ℤ), (σ = 1 ∨ σ = -1) →
      (τ = 1 ∨ τ = -1) → (υ = 1 ∨ υ = -1) →
      |thirdDiff (latticeGreen d) (σ • Pi.single μ 1) (τ • Pi.single ν 1) (υ • Pi.single l 1) x| ≤
        c / (1 + ‖x‖) ^ (d + 1) := by
  obtain ⟨c, hc0, hc⟩ := latticeGreen_thirdDiff_le hd
  set q : ℝ := 2 ^ (d + 1) with hq
  have hq1 : 1 ≤ q := one_le_pow₀ (by norm_num)
  have hq0 : 0 ≤ q := by linarith
  have hmono : ∀ (c' : ℝ), c' ≤ q ^ 3 * c → ∀ y : Fin d → ℤ,
      c' / (1 + ‖y‖) ^ (d + 1) ≤ q ^ 3 * c / (1 + ‖y‖) ^ (d + 1) := fun c' h y =>
    div_le_div_of_nonneg_right h (by positivity)
  refine ⟨q ^ 3 * c, by positivity, fun x μ ν l σ τ υ hσ hτ hυ => ?_⟩
  have hA : ‖(Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := norm_pi_single_le μ
  have hB : ‖(Pi.single ν 1 : Fin d → ℤ)‖ ≤ 1 := norm_pi_single_le ν
  have hC : ‖(Pi.single l 1 : Fin d → ℤ)‖ ≤ 1 := norm_pi_single_le l
  have b0 := hc
  have hqc : 0 ≤ q * c := by positivity
  have hqqc : 0 ≤ q * (q * c) := by positivity
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> rcases hυ with rfl | rfl <;>
    simp only [one_smul, neg_smul]
  · exact (b0 x μ ν l).trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have := thirdDiff_bound_flip_right hc0 hC (fun y => b0 y μ ν l) x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have := thirdDiff_bound_flip_mid hc0 hB (fun y => b0 y μ ν l) x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have h1 := thirdDiff_bound_flip_mid hc0 hB (fun y => b0 y μ ν l)
    have := thirdDiff_bound_flip_right (by positivity) (a := Pi.single μ 1) (b := -Pi.single ν 1)
      hC h1 x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have := thirdDiff_bound_flip_left hc0 hA (fun y => b0 y μ ν l) x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have h1 := thirdDiff_bound_flip_left hc0 hA (fun y => b0 y μ ν l)
    have := thirdDiff_bound_flip_right (by positivity) (a := -Pi.single μ 1) (b := Pi.single ν 1)
      hC h1 x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have h1 := thirdDiff_bound_flip_left hc0 hA (fun y => b0 y μ ν l)
    have := thirdDiff_bound_flip_mid (by positivity) (a := -Pi.single μ 1) (b := Pi.single ν 1)
      (c := Pi.single l 1) hB h1 x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)
  · have h1 := thirdDiff_bound_flip_left hc0 hA (fun y => b0 y μ ν l)
    have h2 := thirdDiff_bound_flip_mid (by positivity) (a := -Pi.single μ 1) (b := Pi.single ν 1)
      (c := Pi.single l 1) hB h1
    have := thirdDiff_bound_flip_right (by positivity) (a := -Pi.single μ 1)
      (b := -Pi.single ν 1) hC h2 x
    exact this.trans (hmono _ (by nlinarith [mul_nonneg hc0 (sq_nonneg q)]) x)

end Balaban.LatticeGreen
