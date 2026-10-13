/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.RealSequences
public import Balaban.Flow.RunningCoefficients
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Limits through sums over scales (pure analysis)

This file proves three analytic statements and asserts no clause of `C1Star`.

* `c1Star_remainder_limit_criterion`: a series over scales `j` whose summands `u j ℓ ν` converge
  along the tori (`LimAlong q`, `ℓ` divisible by higher and higher powers of `q`) for each fixed
  `ν ∈ (0, 1]`, are dominated by one summable sequence `b j`, and whose limits `v j ν` converge as
  `ν ↓ 0`, has a series with the same two limits, equal to the series of the limits.
* `c1Star_truncated_limit_criterion`: the same for the finite sums `∑ j < Jf ℓ ν` whose length tends
  to infinity along the tori.
* `inv_betaR_sub_le`: the real form of P9 (4.18) for `(betaR L d ξ β j)⁻¹` under `SeqHyp`.

An explicit instance of the criterion is `c1Star_limit_criterion_example`.
-/

@[expose] public section

open Filter Topology Finset

namespace Balaban.Correlations

open Balaban Balaban.Flow

/-- The torus sides `ℓ ≠ 0` divisible by `q ^ n`. -/
def toriiSet (q n : ℕ) : Set ℕ := {ℓ | ℓ ≠ 0 ∧ q ^ n ∣ ℓ}

/-- The filter "along the tori of side divisible by arbitrarily high powers of `q`". -/
noncomputable def toriFilter (q : ℕ) : Filter ℕ := ⨅ n : ℕ, 𝓟 (toriiSet q n)

theorem toriiSet_antitone {q : ℕ} : Antitone (toriiSet q) := by
  intro m n hmn ℓ hℓ
  exact ⟨hℓ.1, (pow_dvd_pow q hmn).trans hℓ.2⟩

theorem toriiSet_nonempty {q : ℕ} (hq : 1 ≤ q) (n : ℕ) : (toriiSet q n).Nonempty :=
  ⟨q ^ n, (pow_pos hq n).ne', dvd_rfl⟩

theorem toriDirected {q : ℕ} :
    Directed (· ≥ ·) fun n : ℕ => 𝓟 (toriiSet q n) := fun m n =>
  ⟨max m n, principal_mono.2 (toriiSet_antitone (le_max_left m n)),
    principal_mono.2 (toriiSet_antitone (le_max_right m n))⟩

theorem toriFilter_neBot {q : ℕ} (hq : 1 ≤ q) : (toriFilter q).NeBot := by
  have hd := toriDirected (q := q)
  refine iInf_neBot_of_directed' hd fun n => ?_
  exact principal_neBot_iff.2 (toriiSet_nonempty hq n)

theorem mem_toriFilter {q : ℕ} {s : Set ℕ} :
    s ∈ toriFilter q ↔ ∃ n, toriiSet q n ⊆ s := by
  have hd := toriDirected (q := q)
  rw [toriFilter, mem_iInf_of_directed hd]
  simp

theorem eventually_toriFilter {q : ℕ} {p : ℕ → Prop} :
    (∀ᶠ ℓ in toriFilter q, p ℓ) ↔ ∃ n, ∀ ℓ, ℓ ≠ 0 → q ^ n ∣ ℓ → p ℓ := by
  rw [Filter.Eventually, mem_toriFilter]
  exact exists_congr fun n => ⟨fun h ℓ h0 hd => h ⟨h0, hd⟩, fun h ℓ hℓ => h ℓ hℓ.1 hℓ.2⟩

/-- `LimAlong` is convergence along `toriFilter`. -/
theorem limAlong_iff_tendsto {q : ℕ} (g : ℕ → ℝ) (A : ℝ) :
    LimAlong q (fun ℓ _ => g ℓ) A ↔ Tendsto g (toriFilter q) (𝓝 A) := by
  rw [Metric.tendsto_nhds]
  refine forall₂_congr fun ε hε => ?_
  rw [eventually_toriFilter]
  constructor
  · rintro ⟨n, h⟩
    exact ⟨n, fun ℓ h0 hd => by
      have : NeZero ℓ := ⟨h0⟩
      simpa [Real.dist_eq] using h ℓ hd⟩
  · rintro ⟨n, h⟩
    exact ⟨n, fun ℓ _ hd => by
      have := h ℓ (NeZero.ne ℓ) hd
      simpa [Real.dist_eq] using this⟩

/-- Core Tannery statement along the tori, for summands defined for all `ℓ`. -/
theorem tannery_along_tori {q : ℕ} (w : ℕ → ℕ → ℝ) (v b : ℕ → ℝ)
    (hb : Summable b) (hw : ∀ j ℓ, |w j ℓ| ≤ b j)
    (ht : ∀ j, Tendsto (w j) (toriFilter q) (𝓝 (v j))) :
    Tendsto (fun ℓ => ∑' j, w j ℓ) (toriFilter q) (𝓝 (∑' j, v j)) :=
  tendsto_tsum_of_dominated_convergence hb ht (Eventually.of_forall fun ℓ j => by
    simpa [Real.norm_eq_abs] using hw j ℓ)

/-- A limit along the tori of functions bounded by `b` is bounded by `b`. -/
theorem abs_le_of_tendsto_tori {q : ℕ} (hq : 1 ≤ q) {f : ℕ → ℝ} {a c : ℝ}
    (hf : ∀ ℓ, |f ℓ| ≤ c) (h : Tendsto f (toriFilter q) (𝓝 a)) : |a| ≤ c := by
  have := toriFilter_neBot hq
  exact le_of_tendsto h.abs (Eventually.of_forall hf)

/-- **Tannery along tori and as `ν ↓ 0`.** Pure analysis: it asserts no clause of `C1Star`. -/
theorem c1Star_remainder_limit_criterion (q : ℕ) (hq : 1 ≤ q) (u : ℕ → ℕ → ℝ → ℝ)
    (v : ℕ → ℝ → ℝ) (v0 b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j) (hb : Summable b)
    (hu : ∀ j ℓ ν, ν ∈ Set.Ioc (0 : ℝ) 1 → |u j ℓ ν| ≤ b j)
    (ht : ∀ j ν, ν ∈ Set.Ioc (0 : ℝ) 1 → LimAlong q (fun ℓ _ => u j ℓ ν) (v j ν))
    (h0 : ∀ j, Tendsto (v j) (𝓝[>] 0) (𝓝 (v0 j))) :
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1, LimAlong q (fun ℓ _ => ∑' j, u j ℓ ν) (∑' j, v j ν)) ∧
    Tendsto (fun ν => ∑' j, v j ν) (𝓝[>] 0) (𝓝 (∑' j, v0 j)) := by
  have _ := hb0
  have ht' : ∀ j ν, ν ∈ Set.Ioc (0 : ℝ) 1 → Tendsto (fun ℓ => u j ℓ ν) (toriFilter q) (𝓝 (v j ν)) :=
    fun j ν hν => (limAlong_iff_tendsto _ _).1 (ht j ν hν)
  have hv : ∀ j ν, ν ∈ Set.Ioc (0 : ℝ) 1 → |v j ν| ≤ b j := fun j ν hν =>
    abs_le_of_tendsto_tori hq (fun ℓ => hu j ℓ ν hν) (ht' j ν hν)
  refine ⟨fun ν hν => ?_, ?_⟩
  · rw [limAlong_iff_tendsto]
    exact tannery_along_tori (fun j ℓ => u j ℓ ν) (fun j => v j ν) b hb
      (fun j ℓ => hu j ℓ ν hν) (fun j => ht' j ν hν)
  · refine tendsto_tsum_of_dominated_convergence hb h0 ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ν hν j
    simpa [Real.norm_eq_abs] using hv j ν ⟨hν.1, hν.2.le⟩

/-- **Tannery for sums of torus-dependent length.** If `Jf ℓ ν → ∞` along the tori, the finite
sums `∑_{j < Jf ℓ ν} u j ℓ ν` have the same two limits as in `c1Star_remainder_limit_criterion`. -/
theorem c1Star_truncated_limit_criterion (q : ℕ) (hq : 1 ≤ q) (u : ℕ → ℕ → ℝ → ℝ)
    (Jf : ℕ → ℝ → ℕ) (v : ℕ → ℝ → ℝ) (v0 b : ℕ → ℝ) (hb0 : ∀ j, 0 ≤ b j) (hb : Summable b)
    (hu : ∀ j ℓ ν, ν ∈ Set.Ioc (0 : ℝ) 1 → |u j ℓ ν| ≤ b j)
    (ht : ∀ j ν, ν ∈ Set.Ioc (0 : ℝ) 1 → LimAlong q (fun ℓ _ => u j ℓ ν) (v j ν))
    (hJ : ∀ ν ∈ Set.Ioc (0 : ℝ) 1, ∀ J, ∃ n₀, ∀ ℓ, q ^ n₀ ∣ ℓ → J ≤ Jf ℓ ν)
    (h0 : ∀ j, Tendsto (v j) (𝓝[>] 0) (𝓝 (v0 j))) :
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      LimAlong q (fun ℓ _ => ∑ j ∈ Finset.range (Jf ℓ ν), u j ℓ ν) (∑' j, v j ν)) ∧
    Tendsto (fun ν => ∑' j, v j ν) (𝓝[>] 0) (𝓝 (∑' j, v0 j)) := by
  refine ⟨fun ν hν => ?_, (c1Star_remainder_limit_criterion q hq u v v0 b hb0 hb hu ht h0).2⟩
  have ht' : ∀ j, Tendsto (fun ℓ => u j ℓ ν) (toriFilter q) (𝓝 (v j ν)) :=
    fun j => (limAlong_iff_tendsto _ _).1 (ht j ν hν)
  rw [limAlong_iff_tendsto]
  set w : ℕ → ℕ → ℝ := fun j ℓ => if j < Jf ℓ ν then u j ℓ ν else 0 with hw
  have hsum : ∀ ℓ, ∑ j ∈ Finset.range (Jf ℓ ν), u j ℓ ν = ∑' j, w j ℓ := fun ℓ => by
    rw [tsum_eq_sum (s := Finset.range (Jf ℓ ν))]
    · exact Finset.sum_congr rfl fun j hj => by simp [hw, Finset.mem_range.1 hj]
    · intro j hj; simp [hw, Finset.mem_range.not.1 hj |> not_lt.1 |> not_lt.2]
  simp_rw [hsum]
  refine tannery_along_tori w (fun j => v j ν) b hb (fun j ℓ => ?_) (fun j => ?_)
  · by_cases h : j < Jf ℓ ν
    · simpa [hw, h] using hu j ℓ ν hν
    · simpa [hw, h] using hb0 j
  · refine (ht' j).congr' ?_
    have : ∀ᶠ ℓ in toriFilter q, j + 1 ≤ Jf ℓ ν := by
      obtain ⟨n, hn⟩ := hJ ν hν (j + 1)
      exact (eventually_toriFilter).2 ⟨n, fun ℓ _ hd => hn ℓ hd⟩
    filter_upwards [this] with ℓ hℓ
    simp [hw, Nat.lt_of_succ_le hℓ]

/-! ### Real form of P9 (4.18) -/

section P9

variable {L d : ℕ} {γ₀ c₈ : ℝ} {ξ : ℕ → Fin 3 → ℝ}

/-- **P9 (4.18), real form.** Under `SeqHyp`, `β_j⁻¹ = (β γ_∞)⁻¹ L^{-j(d-2)} + O(β⁻¹ L^{-j(d-2)} q^j)`
with `q = rate L γ₀`, and `γ_∞` real in `[1/2, 2]`. -/
theorem inv_betaR_sub_le (H : SeqHyp L γ₀ c₈ ξ) {β : ℝ} (hβ : 0 < β) :
    ∃ gInf : ℝ, |gInf - 1| ≤ c₈ * rate (L : ℝ) γ₀ / (2 * (1 - rate (L : ℝ) γ₀)) ∧
      (1 / 2 ≤ gInf ∧ gInf ≤ 2) ∧
      ∀ j : ℕ, |(betaR L d ξ β j)⁻¹ - (β * gInf)⁻¹ * (((L : ℝ) ^ (j * (d - 2)))⁻¹)| ≤
        Real.exp 2 * (c₈ * rate (L : ℝ) γ₀ / (2 * (1 - rate (L : ℝ) γ₀))) * β⁻¹ *
          (((L : ℝ) ^ (j * (d - 2)))⁻¹ * rate (L : ℝ) γ₀ ^ j) := by
  have hL0 : (0 : ℝ) < L := by have := H.hL1; linarith
  obtain ⟨γ, hT, h1, h2⟩ := exists_inv_betaSeq_asymptotics hL0 d H.hq0 H.hq1 H.hc H.hs
    H.bound_xiC
  have hre : ∀ j, (gammaSeq (xiC ξ) j).re = gammaR ξ j := fun j => rfl
  have him : γ.im = 0 := by
    have := (Complex.continuous_im.tendsto γ).comp hT
    have h0 : (fun j => (gammaSeq (xiC ξ) j).im) = fun _ => (0 : ℝ) := by
      funext j; rw [gammaSeq_xiC, Complex.ofReal_im]
    have h1 : Tendsto (fun j => (gammaSeq (xiC ξ) j).im) atTop (𝓝 γ.im) := this
    rw [h0] at h1
    exact (tendsto_nhds_unique tendsto_const_nhds h1).symm
  have hγ : γ = ((γ.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hTr : Tendsto (fun j => gammaR ξ j) atTop (𝓝 γ.re) :=
    (Complex.continuous_re.tendsto γ).comp hT
  refine ⟨γ.re, ?_, ⟨?_, ?_⟩, fun j => ?_⟩
  · have : ‖γ - 1‖ = |γ.re - 1| := by
      rw [hγ]; rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs]; simp
    rwa [this] at h1
  · exact ge_of_tendsto hTr (Eventually.of_forall fun j => (H.gammaR_bounds j).1)
  · exact le_of_tendsto hTr (Eventually.of_forall fun j => (H.gammaR_bounds j).2)
  · have key := h2 (β : ℂ) j
    have hb : betaSeq (L : ℝ) d (xiC ξ) (β : ℂ) j = ((betaR L d ξ β j : ℝ) : ℂ) := by
      rw [betaR_eq, betaSeq_eq, gammaSeq_xiC, gammaR_eq]; push_cast; ring
    rw [hb, hγ] at key
    have e : ((betaR L d ξ β j : ℝ) : ℂ)⁻¹ - ((β : ℂ) * ((γ.re : ℝ) : ℂ))⁻¹ *
        ((((L : ℝ) : ℂ) ^ (j * (d - 2)))⁻¹) =
        (((betaR L d ξ β j)⁻¹ - (β * γ.re)⁻¹ * (((L : ℝ) ^ (j * (d - 2)))⁻¹) : ℝ) : ℂ) := by
      push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs] at key
    have e2 : ‖(β : ℂ)⁻¹‖ = β⁻¹ := by
      rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hβ)]
    rwa [e2] at key

end P9

/-! ### An explicit instance -/

section Example

/-- Summands `2^{-j} (1 + ν + 1/(ℓ+1))`. -/
noncomputable def exU (j ℓ : ℕ) (ν : ℝ) : ℝ := (1 / 2 : ℝ) ^ j * (1 + ν + 1 / ((ℓ : ℝ) + 1))

theorem exU_limAlong (j : ℕ) (ν : ℝ) :
    LimAlong 2 (fun ℓ _ => exU j ℓ ν) ((1 / 2 : ℝ) ^ j * (1 + ν)) := by
  rw [limAlong_iff_tendsto]
  have h : Tendsto (fun ℓ : ℕ => 1 / ((ℓ : ℝ) + 1)) (toriFilter 2) (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    rw [eventually_toriFilter]
    refine ⟨⌈1 / ε⌉₊, fun ℓ h0 hd => ?_⟩
    have h1 : ((2 ^ ⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ ℓ := by exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hd
    have h2 : (⌈1 / ε⌉₊ : ℝ) < ((2 ^ ⌈1 / ε⌉₊ : ℕ) : ℝ) := by exact_mod_cast Nat.lt_two_pow_self
    have h3 : 1 / ε ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h4 : 1 / ε < (ℓ : ℝ) + 1 := by linarith
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity), div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at h4
    linarith
  have := (h.const_add (1 + ν)).const_mul ((1 / 2 : ℝ) ^ j)
  simpa [exU, add_assoc] using this

theorem exU_bound (j ℓ : ℕ) (ν : ℝ) (hν : ν ∈ Set.Ioc (0 : ℝ) 1) :
    |exU j ℓ ν| ≤ 3 * (1 / 2 : ℝ) ^ j := by
  have h1 : 1 / ((ℓ : ℝ) + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg ℓ : (0 : ℝ) ≤ ℓ)]
  have h2 : 0 ≤ 1 / ((ℓ : ℝ) + 1) := by positivity
  have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ j := by positivity
  rw [exU, abs_of_nonneg (by have := hν.1; positivity)]
  nlinarith [hν.1, hν.2]

/-- Non-vacuity of `c1Star_remainder_limit_criterion` at `q = 2`: both limits are non-trivial,
`2 (1 + ν)` along the tori, then `2` as `ν ↓ 0`. -/
theorem c1Star_limit_criterion_example :
    (∀ ν ∈ Set.Ioc (0 : ℝ) 1,
      LimAlong 2 (fun ℓ _ => ∑' j, exU j ℓ ν) (2 * (1 + ν))) ∧
    Tendsto (fun ν : ℝ => 2 * (1 + ν)) (𝓝[>] 0) (𝓝 2) := by
  have hg : Summable fun j : ℕ => 3 * (1 / 2 : ℝ) ^ j :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left 3
  have hs : ∀ ν : ℝ, ∑' j : ℕ, (1 / 2 : ℝ) ^ j * (1 + ν) = 2 * (1 + ν) := fun ν => by
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  have hs0 : ∑' j : ℕ, (1 / 2 : ℝ) ^ j * 1 = 2 := by simpa using hs 0
  have := c1Star_remainder_limit_criterion 2 (by norm_num) exU
    (fun j ν => (1 / 2 : ℝ) ^ j * (1 + ν)) (fun j => (1 / 2 : ℝ) ^ j * 1)
    (fun j => 3 * (1 / 2 : ℝ) ^ j) (fun j => by positivity) hg
    (fun j ℓ ν hν => exU_bound j ℓ ν hν) (fun j ν _ => exU_limAlong j ν)
    (fun j => by
      have : Continuous fun ν : ℝ => (1 / 2 : ℝ) ^ j * (1 + ν) := by fun_prop
      simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds)
  simp only [hs, hs0] at this
  exact this

end Example

end Balaban.Correlations
