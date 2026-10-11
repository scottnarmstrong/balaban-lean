module

public import Balaban.Green.Lattice.Uniqueness

/-!
# The lattice Green's function on `ℤ^d`: main statements (Lemma K)

For `d ≥ 3` the function `latticeGreen d = ∫_0^∞ p_t dt` is the unique solution
`G : ℤ^d → ℝ` of `-Δ¹ G = δ₀`, `G → 0` at infinity (`latticeGreen_existsUnique`), it is
nonnegative, and it satisfies the bounds `C(x) ≤ c ⟨x⟩^{2-d}`, `|∂_μ C(x)| ≤ c ⟨x⟩^{1-d}` and
`|∂_μ ∂_ν C(x)| ≤ c ⟨x⟩^{-d}` for forward and backward differences, with `⟨x⟩ = 1 + ‖x‖`.
-/

@[expose] public section

noncomputable section

namespace Balaban.LatticeGreen

open Filter Topology

variable {d : ℕ}

theorem norm_pi_single_le (μ : Fin d) : ‖(Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro i
  by_cases h : i = μ
  · subst h; simp
  · simp [h]

theorem one_add_norm_le_of_translate (x w : Fin d → ℤ) {r : ℝ} (hr : ‖w‖ ≤ r) :
    1 + ‖x‖ ≤ (1 + r) * (1 + ‖x + w‖) := by
  have h1 : ‖x‖ ≤ ‖x + w‖ + ‖w‖ := by
    have := norm_sub_le (x + w) w
    simpa using this
  have h2 : 0 ≤ ‖x + w‖ := norm_nonneg _
  have h3 : 0 ≤ ‖w‖ := norm_nonneg _
  nlinarith

/-- Bounds of the form `c / (1 + ‖x‖)^k` are stable under translation by a bounded vector. -/
theorem bound_translate {F : (Fin d → ℤ) → ℝ} {c : ℝ} (hc : 0 ≤ c) {k : ℕ}
    (hF : ∀ y, |F y| ≤ c / (1 + ‖y‖) ^ k) (x w : Fin d → ℤ) {r : ℝ} (hr : ‖w‖ ≤ r) :
    |F (x + w)| ≤ (1 + r) ^ k * c / (1 + ‖x‖) ^ k := by
  refine (hF (x + w)).trans ?_
  have hr0 : 0 ≤ r := (norm_nonneg _).trans hr
  have h := one_add_norm_le_of_translate x w hr
  have hp : 0 < (1 + ‖x + w‖) ^ k := by positivity
  have hq : 0 < (1 + ‖x‖) ^ k := by positivity
  rw [div_le_div_iff₀ hp hq]
  have : (1 + ‖x‖) ^ k ≤ ((1 + r) * (1 + ‖x + w‖)) ^ k :=
    pow_le_pow_left₀ (by positivity) h k
  rw [mul_pow] at this
  calc c * (1 + ‖x‖) ^ k ≤ c * ((1 + r) ^ k * (1 + ‖x + w‖) ^ k) :=
        mul_le_mul_of_nonneg_left this hc
    _ = (1 + r) ^ k * c * (1 + ‖x + w‖) ^ k := by ring

theorem latticeGreen_existsUnique (hd : 3 ≤ d) :
    ∃! G : (Fin d → ℤ) → ℝ,
      (∀ x, ∑ μ : Fin d, (2 * G x - G (x + Pi.single μ 1) - G (x - Pi.single μ 1)) =
        if x = 0 then 1 else 0) ∧ Tendsto G cofinite (𝓝 0) := by
  refine ⟨latticeGreen d, ⟨latticeGreen_equation hd, latticeGreen_tendsto_zero hd⟩, ?_⟩
  rintro G ⟨hG, hGlim⟩
  have h := harmonic_eq_zero (by omega : 0 < d) (fun x => G x - latticeGreen d x)
    (fun x => by
      have e : ∑ μ : Fin d, (2 * (G x - latticeGreen d x) -
          (G (x + Pi.single μ 1) - latticeGreen d (x + Pi.single μ 1)) -
          (G (x - Pi.single μ 1) - latticeGreen d (x - Pi.single μ 1))) =
          (∑ μ : Fin d, (2 * G x - G (x + Pi.single μ 1) - G (x - Pi.single μ 1))) -
          ∑ μ : Fin d, (2 * latticeGreen d x - latticeGreen d (x + Pi.single μ 1) -
            latticeGreen d (x - Pi.single μ 1)) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun _ _ => by ring
      rw [e, hG x, latticeGreen_equation hd x, sub_self])
    (by simpa using hGlim.sub (latticeGreen_tendsto_zero hd))
  funext x
  have := congrFun h x
  simp only [Pi.zero_apply] at this
  linarith

theorem latticeGreen_bwd1_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ : Fin d),
      |latticeGreen d x - latticeGreen d (x - Pi.single μ 1)| ≤ c / (1 + ‖x‖) ^ (d - 1) := by
  obtain ⟨c, hc0, hc⟩ := latticeGreen_diff1_le hd
  refine ⟨2 ^ (d - 1) * c, by positivity, fun x μ => ?_⟩
  have h := bound_translate (F := fun y => latticeGreen d (y + Pi.single μ 1) - latticeGreen d y)
    hc0 (fun y => hc y μ) x (-Pi.single μ 1) (r := 1) (by simpa using norm_pi_single_le μ)
  have e : x + -Pi.single μ 1 = x - Pi.single μ 1 := by abel
  have e2 : x + -Pi.single μ 1 + Pi.single μ 1 = x := by abel
  rw [e2, e] at h
  norm_num at h
  exact h

theorem latticeGreen_fwd1_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ : Fin d),
      |latticeGreen d (x + Pi.single μ 1) - latticeGreen d x| ≤ c / (1 + ‖x‖) ^ (d - 1) :=
  latticeGreen_diff1_le hd

/-- The second difference `G(x+a+b) - G(x+a) - G(x+b) + G(x)`. -/
def secondDiff {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b x : V) : ℝ :=
  G (x + a + b) - G (x + a) - G (x + b) + G x

theorem secondDiff_comm {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b x : V) :
    secondDiff G a b x = secondDiff G b a x := by
  unfold secondDiff
  rw [add_right_comm x a b]; ring

theorem secondDiff_neg_left {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b x : V) :
    secondDiff G (-a) b x = -secondDiff G a b (x + -a) := by
  unfold secondDiff
  rw [neg_add_cancel_right, add_right_comm x (-a) b]
  ring

theorem secondDiff_neg_right {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b x : V) :
    secondDiff G a (-b) x = -secondDiff G a b (x + -b) := by
  rw [secondDiff_comm, secondDiff_neg_left, secondDiff_comm]

theorem secondDiff_neg_both {V : Type*} [AddCommGroup V] (G : V → ℝ) (a b x : V) :
    secondDiff G (-a) (-b) x = secondDiff G a b (x + -a + -b) := by
  rw [secondDiff_neg_right, secondDiff_neg_left, neg_neg, add_right_comm]

/-- Second differences, all four sign combinations (`σ, τ ∈ {1, -1}`). -/
theorem latticeGreen_diff2_signs_le (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ ν : Fin d) (σ τ : ℤ), (σ = 1 ∨ σ = -1) →
      (τ = 1 ∨ τ = -1) →
      |secondDiff (latticeGreen d) (σ • Pi.single μ 1) (τ • Pi.single ν 1) x| ≤
        c / (1 + ‖x‖) ^ d := by
  obtain ⟨c, hc0, hc⟩ := latticeGreen_diff2_le hd
  refine ⟨3 ^ d * c, by positivity, fun x μ ν σ τ hσ hτ => ?_⟩
  have hFb : ∀ y, |secondDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) y| ≤
      c / (1 + ‖y‖) ^ d := fun y => hc y μ ν
  have hnorm : ‖(Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := norm_pi_single_le μ
  have hnorm' : ‖(Pi.single ν 1 : Fin d → ℤ)‖ ≤ 1 := norm_pi_single_le ν
  have key : ∀ w : Fin d → ℤ, ‖w‖ ≤ 2 →
      |secondDiff (latticeGreen d) (Pi.single μ 1) (Pi.single ν 1) (x + w)| ≤
        3 ^ d * c / (1 + ‖x‖) ^ d := by
    intro w hw
    have := bound_translate hc0 hFb x w hw
    norm_num at this
    exact this
  rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl
  · simpa using key 0 (by simp)
  · simp only [one_smul, neg_smul, secondDiff_neg_right, abs_neg]
    exact key _ (by
      have : ‖(-Pi.single ν 1 : Fin d → ℤ)‖ ≤ 1 := by simpa using hnorm'
      linarith)
  · simp only [one_smul, neg_smul, secondDiff_neg_left, abs_neg]
    exact key _ (by
      have : ‖(-Pi.single μ 1 : Fin d → ℤ)‖ ≤ 1 := by simpa using hnorm
      linarith)
  · simp only [neg_smul, one_smul, secondDiff_neg_both]
    have h := key (-Pi.single μ 1 + -Pi.single ν 1) (by
      calc ‖(-Pi.single μ 1 + -Pi.single ν 1 : Fin d → ℤ)‖
          ≤ ‖(-Pi.single μ 1 : Fin d → ℤ)‖ + ‖(-Pi.single ν 1 : Fin d → ℤ)‖ := norm_add_le _ _
        _ ≤ 2 := by simp only [norm_neg]; linarith)
    rwa [← add_assoc] at h

theorem div_pow_eq_rpow (c y : ℝ) (hy : 0 ≤ y) {k : ℕ} {e : ℝ} (he : e = -(k : ℝ)) :
    c / y ^ k = c * y ^ e := by
  rw [he, Real.rpow_neg hy, Real.rpow_natCast, div_eq_mul_inv]

/-- Lemma K, pointwise bound: `C(x) ≤ c ⟨x⟩^{2-d}` with `⟨x⟩ = 1 + ‖x‖`. -/
theorem latticeGreen_le_rpow (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Fin d → ℤ,
      latticeGreen d x ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 2)) := by
  obtain ⟨c, hc0, hc⟩ := latticeGreen_le hd
  refine ⟨c, hc0, fun x => ?_⟩
  rw [← div_pow_eq_rpow c _ (by linarith [norm_nonneg x]) (k := d - 2)]
  · exact hc x
  · rw [Nat.cast_sub (by omega)]; push_cast; ring

/-- Lemma K, first differences: `|∂_μ C(x)| ≤ c ⟨x⟩^{1-d}` (forward and backward). -/
theorem latticeGreen_diff1_le_rpow (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ : Fin d),
      |latticeGreen d (x + Pi.single μ 1) - latticeGreen d x| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 1)) ∧
      |latticeGreen d x - latticeGreen d (x - Pi.single μ 1)| ≤ c * (1 + ‖x‖) ^ (-((d : ℝ) - 1)) := by
  obtain ⟨c1, hc1, h1⟩ := latticeGreen_diff1_le hd
  obtain ⟨c2, hc2, h2⟩ := latticeGreen_bwd1_le hd
  refine ⟨max c1 c2, le_max_of_le_left hc1, fun x μ => ?_⟩
  have e : -((d : ℝ) - 1) = -((d - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hx : 0 ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
  rw [← div_pow_eq_rpow _ _ hx e]
  have hp : 0 < (1 + ‖x‖) ^ (d - 1) := by positivity
  exact ⟨(h1 x μ).trans (div_le_div_of_nonneg_right (le_max_left _ _) hp.le),
    (h2 x μ).trans (div_le_div_of_nonneg_right (le_max_right _ _) hp.le)⟩

/-- Lemma K, second differences: `|∂_μ ∂_ν C(x)| ≤ c ⟨x⟩^{-d}` for all sign combinations. -/
theorem latticeGreen_diff2_le_rpow (hd : 3 ≤ d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ (x : Fin d → ℤ) (μ ν : Fin d) (σ τ : ℤ), (σ = 1 ∨ σ = -1) →
      (τ = 1 ∨ τ = -1) →
      |secondDiff (latticeGreen d) (σ • Pi.single μ 1) (τ • Pi.single ν 1) x| ≤
        c * (1 + ‖x‖) ^ (-(d : ℝ)) := by
  obtain ⟨c, hc0, hc⟩ := latticeGreen_diff2_signs_le hd
  refine ⟨c, hc0, fun x μ ν σ τ hσ hτ => ?_⟩
  rw [← div_pow_eq_rpow c _ (by linarith [norm_nonneg x]) (k := d) (by ring)]
  exact hc x μ ν σ τ hσ hτ

end Balaban.LatticeGreen
