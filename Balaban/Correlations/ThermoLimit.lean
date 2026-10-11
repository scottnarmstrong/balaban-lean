/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Correlations.Tail

/-!
# The thermodynamic limit along tori with side divisible by `(M L)^n` (CORRELATIONS.md, §4)

Conditional on the clauses of Root-F; consumed by the Root-C provider.  Let
`RootFClauses d N L M β ν h kf κ c₉ δ T` hold.  For `x, y ∈ ℤ^d` read modulo `ℓ`
(`embedZ ℓ x`), the one-point function `⟨φ_i(x)⟩_ℓ` and the truncated two-point function
`G_{ik}(x, y)_ℓ` converge as `ℓ → ∞` through the multiples of `(M L)^n`
(`onePoint_tendsto_along_multiples`, `twoPoint_tendsto_along_multiples`), in the `ε`–`n₀` form
`∀ ε > 0, ∃ n₀, ∀ ℓ, (M L)^{n₀} ∣ ℓ → |· - limit| < ε`.  The key estimate is the comparison of
two admissible tori (`onePoint_cmp`, `twoPoint_cmp`; Lemma 4.2): the sums over the polymers
inside a box agree by the agreement clause, and the polymers leaving the box contribute at most
`O(c₉ 2^{-K})` if the box has size `s_J K + O(|x|)`.  The limits along two families of tori
agree if both exist (`eq_of_tendsto_along_multiples`, Lemma 3.0′).
-/

@[expose] public section

open scoped Classical

namespace Balaban.Correlations

open Balaban Finset

section Abstract

/-- A real function on `ℕ` converges to `A` along the multiples of `q^n`. -/
def TendstoAlongMultiples (F : ℕ → ℝ) (A : ℝ) (q : ℕ) : Prop :=
  ∀ ε > 0, ∃ n0 : ℕ, ∀ ℓ : ℕ, 0 < ℓ → q ^ n0 ∣ ℓ → |F ℓ - A| < ε

/-- Lemma 3.0′ (lcm): limits along the multiples of `a^n` and of `b^n` coincide. -/
theorem eq_of_tendsto_along_multiples {F : ℕ → ℝ} {A B : ℝ} {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hA : TendstoAlongMultiples F A a) (hB : TendstoAlongMultiples F B b) : A = B := by
  by_contra hne
  have hpos : 0 < |A - B| / 2 := by
    have : A - B ≠ 0 := sub_ne_zero.2 hne
    positivity
  obtain ⟨n0, h0⟩ := hA _ hpos
  obtain ⟨n1, h1⟩ := hB _ hpos
  have hℓ : 0 < a ^ n0 * b ^ n1 := by positivity
  have e0 := h0 _ hℓ (Dvd.intro _ rfl)
  have e1 := h1 _ hℓ (Dvd.intro_left _ rfl)
  have : |A - B| ≤ |F (a ^ n0 * b ^ n1) - A| + |F (a ^ n0 * b ^ n1) - B| := by
    calc |A - B| = |(F (a ^ n0 * b ^ n1) - B) - (F (a ^ n0 * b ^ n1) - A)| := by ring_nf
      _ ≤ _ := by rw [add_comm]; exact abs_sub _ _
  linarith

/-- A Cauchy condition along the multiples of `q^n` gives a limit. -/
theorem exists_tendsto_along_multiples {q : ℕ} (hq : 2 ≤ q) (F : ℕ → ℝ)
    (hF : ∀ ε > 0, ∃ n0 : ℕ, ∀ ℓ ℓ' : ℕ, 0 < ℓ → 0 < ℓ' → q ^ n0 ∣ ℓ → q ^ n0 ∣ ℓ' →
      |F ℓ - F ℓ'| < ε) :
    ∃ A : ℝ, TendstoAlongMultiples F A q := by
  have hq0 : 0 < q := by omega
  set u : ℕ → ℝ := fun n => F (q ^ n) with hu
  have hcauchy : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨n0, hn0⟩ := hF ε hε
    refine ⟨n0, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    exact hn0 _ _ (by positivity) (by positivity) (pow_dvd_pow q hm) (pow_dvd_pow q hn)
  obtain ⟨A, hA⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨A, fun ε hε => ?_⟩
  obtain ⟨n0, hn0⟩ := hF (ε / 2) (by positivity)
  refine ⟨n0, fun ℓ hℓ hdvd => ?_⟩
  have hlim : Filter.Tendsto (fun n => |F ℓ - u n|) Filter.atTop (nhds |F ℓ - A|) :=
    (continuous_abs.tendsto _).comp (tendsto_const_nhds.sub hA)
  have : |F ℓ - A| ≤ ε / 2 := by
    refine le_of_tendsto hlim ?_
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    exact (hn0 ℓ (q ^ n) hℓ (by positivity) hdvd (pow_dvd_pow q hn)).le
  linarith

end Abstract

section Compare

variable {d N L M kf : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {κ c₉ δ : ℝ}
  {T : RootFFamily d N}

theorem mem_boxZ_of_natAbs_le {R X0 : ℕ} (hR : X0 < R) {x : Fin d → ℤ}
    (hx : ∀ μ, (x μ).natAbs ≤ X0) : x ∈ boxZ d R :=
  mem_boxZ.2 fun μ => by
    have h1 := hx μ
    rw [Int.abs_eq_natAbs]
    exact_mod_cast lt_of_le_of_lt h1 hR

/-- The sum over the polymers through `x` splits into a box part and a small tail. -/
theorem onePoint_decomp [NeZero N] (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ)
    {ℓ : ℕ} [NeZero ℓ] (hdiv : M * L ^ (kf + 1) ∣ ℓ) {K X0 R : ℕ}
    (hRK : R = M * L ^ (kf + 1) * K + X0 + 1) (hℓR : 4 * R ≤ ℓ) {x : Fin d → ℤ}
    (hx : ∀ μ, (x μ).natAbs ≤ X0) (i : Fin N) :
    ∃ Tl : ℂ, ‖Tl‖ ≤ 6 * c₉ * (1 / 2) ^ (K + 1) ∧
      (onePoint d N ℓ β ν h (embedZ ℓ x) i : ℂ) =
        (h i : ℂ) + ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ A ∈ (boxZ d R).powerset,
          T ℓ j (embedZ ℓ x) (A.image (embedZ ℓ)) 0 i + Tl := by
  have hcl' := hcl.1 ℓ hdiv
  have hd1 : 1 ≤ d := by omega
  have hθ : 1 / 2 ≤ ((d : ℝ) - 2) / 2 + δ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X ∈ Finset.univ.filter
    (fun X : Finset (Torus d ℓ) => ¬ X ⊆ boxT d R ℓ), T ℓ j (embedZ ℓ x) X 0 i, ?_, ?_⟩
  · refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.Icc 1 (kf + 1),
          2 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) * (1 / 2) ^ (K + 1) :=
          sum_le_sum fun j hj => norm_tail_sum_le hcl' hdiv hd1 hc₉ hκ hj _ i K _
            (fun X hX hp hxX => by
              have hnot := (mem_filter.1 hX).2
              exact blockNumber_ge_of_not_subset (by omega) hj hdiv hRK hx hp hxX hnot)
      _ = 2 * c₉ * (1 / 2) ^ (K + 1) * ∑ j ∈ Finset.Icc 1 (kf + 1),
            (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ => by ring
      _ ≤ 2 * c₉ * (1 / 2) ^ (K + 1) * 3 :=
          mul_le_mul_of_nonneg_left (sum_rpow_le_three hL hθ _) (by positivity)
      _ = _ := by ring
  · have h4R : 4 * R ≤ ℓ := hℓR
    rw [onePoint_eq_of_clauses hcl' (embedZ ℓ x) i]
    simp_rw [sum_split h4R (fun X => T ℓ _ (embedZ ℓ x) X 0 i)]
    rw [Finset.sum_add_distrib]
    ring

theorem onePoint_cmp [NeZero N] (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ)
    {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hdiv : M * L ^ (kf + 1) ∣ ℓ)
    (hdiv' : M * L ^ (kf + 1) ∣ ℓ') {K X0 R : ℕ}
    (hRK : R = M * L ^ (kf + 1) * K + X0 + 1) (hℓR : 4 * R ≤ ℓ) (hℓR' : 4 * R ≤ ℓ')
    {x : Fin d → ℤ} (hx : ∀ μ, (x μ).natAbs ≤ X0) (i : Fin N) :
    |onePoint d N ℓ β ν h (embedZ ℓ x) i - onePoint d N ℓ' β ν h (embedZ ℓ' x) i| ≤
      12 * c₉ * (1 / 2) ^ (K + 1) := by
  obtain ⟨Tl, hTl, h1⟩ := onePoint_decomp hcl hd hδ hL hc₉ hκ hdiv hRK hℓR hx i
  obtain ⟨Tl', hTl', h2⟩ := onePoint_decomp hcl hd hδ hL hc₉ hκ hdiv' hRK hℓR' hx i
  have hxb : x ∈ boxZ d R := mem_boxZ_of_natAbs_le (by omega) hx
  have hbox : ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ A ∈ (boxZ d R).powerset,
        T ℓ j (embedZ ℓ x) (A.image (embedZ ℓ)) 0 i =
      ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ A ∈ (boxZ d R).powerset,
        T ℓ' j (embedZ ℓ' x) (A.image (embedZ ℓ')) 0 i := by
    refine sum_congr rfl fun j _ => sum_congr rfl fun A hA => ?_
    exact value_agree hcl hdiv hdiv' hℓR hℓR' j hxb (mem_powerset.1 hA) i
  have hdiff : ((onePoint d N ℓ β ν h (embedZ ℓ x) i - onePoint d N ℓ' β ν h (embedZ ℓ' x) i :
      ℝ) : ℂ) = Tl - Tl' := by
    push_cast
    rw [h1, h2, hbox]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff]
  calc ‖Tl - Tl'‖ ≤ ‖Tl‖ + ‖Tl'‖ := norm_sub_le _ _
    _ ≤ 6 * c₉ * (1 / 2) ^ (K + 1) + 6 * c₉ * (1 / 2) ^ (K + 1) := add_le_add hTl hTl'
    _ = _ := by ring

theorem twoPoint_decomp [NeZero N] (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ)
    {ℓ : ℕ} [NeZero ℓ] (hdiv : M * L ^ (kf + 1) ∣ ℓ) {K X0 R : ℕ}
    (hRK : R = M * L ^ (kf + 1) * K + X0 + 1) (hℓR : 4 * R ≤ ℓ) {x y : Fin d → ℤ}
    (hx : ∀ μ, (x μ).natAbs ≤ X0) (i k : Fin N) :
    ∃ Tl : ℂ, ‖Tl‖ ≤ 24 * c₉ * (1 / 2) ^ (K + 1) ∧
      (twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k : ℂ) =
        ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ A ∈ (boxZ d R).powerset,
          dsum T ℓ j (embedZ ℓ x) (embedZ ℓ y) i k (A.image (embedZ ℓ)) + Tl := by
  have hcl' := hcl.1 ℓ hdiv
  have hd1 : 1 ≤ d := by omega
  have hθ : 1 / 2 ≤ ((d : ℝ) - 2) / 2 + δ := by
    have : (3 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  refine ⟨∑ j ∈ Finset.Icc 1 (kf + 1), ∑ X ∈ Finset.univ.filter
    (fun X : Finset (Torus d ℓ) => ¬ X ⊆ boxT d R ℓ),
      dsum T ℓ j (embedZ ℓ x) (embedZ ℓ y) i k X, ?_, ?_⟩
  · refine (norm_sum_le _ _).trans ?_
    calc _ ≤ ∑ j ∈ Finset.Icc 1 (kf + 1),
          8 * (c₉ * (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ)))) * (1 / 2) ^ (K + 1) :=
          sum_le_sum fun j hj => norm_tail_dsum_le hcl' hdiv hd1 hc₉ hκ hj _ _ i k K _
            (fun X hX hp hxX _ => by
              have hnot := (mem_filter.1 hX).2
              exact blockNumber_ge_of_not_subset (by omega) hj hdiv hRK hx hp hxX hnot)
      _ = 8 * c₉ * (1 / 2) ^ (K + 1) * ∑ j ∈ Finset.Icc 1 (kf + 1),
            (L : ℝ) ^ (-((j : ℝ) * (((d : ℝ) - 2) / 2 + δ))) := by
          rw [mul_sum]
          refine sum_congr rfl fun j _ => by ring
      _ ≤ 8 * c₉ * (1 / 2) ^ (K + 1) * 3 :=
          mul_le_mul_of_nonneg_left (sum_rpow_le_three hL hθ _) (by positivity)
      _ = _ := by ring
  · have h4R : 4 * R ≤ ℓ := hℓR
    rw [twoPointTruncated_eq_of_clauses hcl' (embedZ ℓ x) (embedZ ℓ y) i k]
    have : ∀ j, ∑ X : Finset (Torus d ℓ), (fderiv ℂ (termComp T ℓ j (embedZ ℓ x) X i) 0
          (sourceDelta (embedZ ℓ y) k) + fderiv ℂ (termComp T ℓ j (embedZ ℓ y) X k) 0
            (sourceDelta (embedZ ℓ x) i)) =
        ∑ X : Finset (Torus d ℓ), dsum T ℓ j (embedZ ℓ x) (embedZ ℓ y) i k X := fun j => rfl
    simp_rw [this, sum_split h4R (fun X => dsum T ℓ _ (embedZ ℓ x) (embedZ ℓ y) i k X)]
    rw [Finset.sum_add_distrib]

theorem twoPoint_cmp [NeZero N] (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T)
    (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ)
    {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hdiv : M * L ^ (kf + 1) ∣ ℓ)
    (hdiv' : M * L ^ (kf + 1) ∣ ℓ') {K X0 R : ℕ}
    (hRK : R = M * L ^ (kf + 1) * K + X0 + 1) (hℓR : 4 * R ≤ ℓ) (hℓR' : 4 * R ≤ ℓ')
    {x y : Fin d → ℤ} (hx : ∀ μ, (x μ).natAbs ≤ X0) (hy : ∀ μ, (y μ).natAbs ≤ X0)
    (i k : Fin N) :
    |twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k -
        twoPointTruncated d N ℓ' β ν h (embedZ ℓ' x) (embedZ ℓ' y) i k| ≤
      48 * c₉ * (1 / 2) ^ (K + 1) := by
  obtain ⟨Tl, hTl, h1⟩ := twoPoint_decomp hcl hd hδ hL hc₉ hκ hdiv hRK hℓR hx (y := y) i k
  obtain ⟨Tl', hTl', h2⟩ := twoPoint_decomp hcl hd hδ hL hc₉ hκ hdiv' hRK hℓR' hx (y := y) i k
  have hxb : x ∈ boxZ d R := mem_boxZ_of_natAbs_le (by omega) hx
  have hyb : y ∈ boxZ d R := mem_boxZ_of_natAbs_le (by omega) hy
  have hbox : ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ A ∈ (boxZ d R).powerset,
        dsum T ℓ j (embedZ ℓ x) (embedZ ℓ y) i k (A.image (embedZ ℓ)) =
      ∑ j ∈ Finset.Icc 1 (kf + 1), ∑ A ∈ (boxZ d R).powerset,
        dsum T ℓ' j (embedZ ℓ' x) (embedZ ℓ' y) i k (A.image (embedZ ℓ')) := by
    refine sum_congr rfl fun j _ => sum_congr rfl fun A hA => ?_
    unfold dsum
    rw [fderiv_agree hcl hdiv hdiv' hℓR hℓR' j hxb hyb (mem_powerset.1 hA) i k,
      fderiv_agree hcl hdiv hdiv' hℓR hℓR' j hyb hxb (mem_powerset.1 hA) k i]
  have hdiff : ((twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k -
      twoPointTruncated d N ℓ' β ν h (embedZ ℓ' x) (embedZ ℓ' y) i k : ℝ) : ℂ) = Tl - Tl' := by
    push_cast
    rw [h1, h2, hbox]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdiff]
  calc ‖Tl - Tl'‖ ≤ ‖Tl‖ + ‖Tl'‖ := norm_sub_le _ _
    _ ≤ 24 * c₉ * (1 / 2) ^ (K + 1) + 24 * c₉ * (1 / 2) ^ (K + 1) := add_le_add hTl hTl'
    _ = _ := by ring

end Compare

section Limit

variable {d N L M kf : ℕ} {β ν : ℝ} {h : EuclideanSpace ℝ (Fin N)} {κ c₉ δ : ℝ}
  {T : RootFFamily d N}

/-- Admissibility of the tori `ℓ` with `(M L)^n ∣ ℓ`, `n ≥ kf + 1`. -/
theorem admissible_of_dvd_pow {ℓ n : ℕ} (hn : kf + 1 ≤ n) (hℓ : (M * L) ^ n ∣ ℓ) :
    M * L ^ (kf + 1) ∣ ℓ := by
  refine dvd_trans ?_ hℓ
  rw [mul_pow]
  exact mul_dvd_mul (dvd_pow_self M (by omega)) (pow_dvd_pow L hn)

theorem four_mul_le_of_dvd_pow {q ℓ n R : ℕ} (hq : 2 ≤ q) (hℓ : 0 < ℓ) (hn : 4 * R ≤ n)
    (hdvd : q ^ n ∣ ℓ) : 4 * R ≤ ℓ := by
  have h1 : n < q ^ n := Nat.lt_pow_self (by omega)
  have h2 : q ^ n ≤ ℓ := Nat.le_of_dvd hℓ hdvd
  omega

theorem exists_pow_half_lt {c ε : ℝ} (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ K : ℕ, c * (1 / 2) ^ (K + 1) < ε := by
  obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (show 0 < ε / (c + 1) by positivity)
    (show (1 / 2 : ℝ) < 1 by norm_num)
  refine ⟨K, ?_⟩
  have h1 : (1 / 2 : ℝ) ^ (K + 1) ≤ (1 / 2) ^ K := by
    rw [pow_succ]; nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) K]
  calc c * (1 / 2) ^ (K + 1) ≤ (c + 1) * (1 / 2) ^ K := by
        nlinarith [pow_nonneg (show (0 : ℝ) ≤ 1 / 2 by norm_num) (K + 1)]
    _ < (c + 1) * (ε / (c + 1)) := by gcongr
    _ = ε := by field_simp

/-- Theorem 4.1 (one point): the one-point function converges along the tori with side
divisible by `(M L)^n`. -/
theorem onePoint_tendsto_along_multiples [NeZero N]
    (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T) (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L)
    (hM : 1 ≤ M) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ) (x : Fin d → ℤ) (i : Fin N) :
    ∃ m : ℝ, ∀ ε > 0, ∃ n0 : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], (M * L) ^ n0 ∣ ℓ →
      |onePoint d N ℓ β ν h (embedZ ℓ x) i - m| < ε := by
  set X0 : ℕ := Finset.univ.sup fun μ => (x μ).natAbs with hX0
  have hx : ∀ μ, (x μ).natAbs ≤ X0 := fun μ =>
    Finset.le_sup (f := fun μ => (x μ).natAbs) (Finset.mem_univ μ)
  have hq : 2 ≤ M * L := by nlinarith
  set F : ℕ → ℝ := fun ℓ => if hℓ : 0 < ℓ then
    (haveI : NeZero ℓ := NeZero.of_pos hℓ; onePoint d N ℓ β ν h (embedZ ℓ x) i) else 0 with hF
  have hFeq : ∀ (ℓ : ℕ) [NeZero ℓ], F ℓ = onePoint d N ℓ β ν h (embedZ ℓ x) i := by
    intro ℓ _
    have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
    simp [hF, hℓ]
  obtain ⟨m, hm⟩ := exists_tendsto_along_multiples hq F (fun ε hε => by
    obtain ⟨K, hK⟩ := exists_pow_half_lt (show 0 ≤ 12 * c₉ by positivity) hε
    set R := M * L ^ (kf + 1) * K + X0 + 1 with hR
    refine ⟨max (kf + 1) (4 * R), fun ℓ ℓ' hℓ hℓ' hd1 hd2 => ?_⟩
    have : NeZero ℓ := NeZero.of_pos hℓ
    have : NeZero ℓ' := NeZero.of_pos hℓ'
    rw [hFeq ℓ, hFeq ℓ']
    refine lt_of_le_of_lt (onePoint_cmp hcl hd hδ hL hc₉ hκ
      (admissible_of_dvd_pow (le_max_left _ _) hd1) (admissible_of_dvd_pow (le_max_left _ _) hd2)
      hR (four_mul_le_of_dvd_pow hq hℓ (le_max_right _ _) hd1)
      (four_mul_le_of_dvd_pow hq hℓ' (le_max_right _ _) hd2) hx i) ?_
    linarith)
  refine ⟨m, fun ε hε => ?_⟩
  obtain ⟨n0, hn0⟩ := hm ε hε
  exact ⟨n0, fun ℓ _ hdvd => by
    rw [← hFeq ℓ]
    exact hn0 ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ)) hdvd⟩

/-- Theorem 4.1 (two points): the truncated two-point function converges along the tori with side
divisible by `(M L)^n`. -/
theorem twoPoint_tendsto_along_multiples [NeZero N]
    (hcl : RootFClauses d N L M β ν h kf κ c₉ δ T) (hd : 3 ≤ d) (hδ : 0 < δ) (hL : 2 ≤ L)
    (hM : 1 ≤ M) (hc₉ : 0 ≤ c₉) (hκ : kappaStar d ≤ κ) (x y : Fin d → ℤ) (i k : Fin N) :
    ∃ G : ℝ, ∀ ε > 0, ∃ n0 : ℕ, ∀ (ℓ : ℕ) [NeZero ℓ], (M * L) ^ n0 ∣ ℓ →
      |twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k - G| < ε := by
  set X0 : ℕ := Finset.univ.sup fun μ => max (x μ).natAbs (y μ).natAbs with hX0
  have hx : ∀ μ, (x μ).natAbs ≤ X0 := fun μ =>
    (le_max_left _ _).trans (Finset.le_sup (f := fun μ => max (x μ).natAbs (y μ).natAbs)
      (Finset.mem_univ μ))
  have hy : ∀ μ, (y μ).natAbs ≤ X0 := fun μ =>
    (le_max_right _ _).trans (Finset.le_sup (f := fun μ => max (x μ).natAbs (y μ).natAbs)
      (Finset.mem_univ μ))
  have hq : 2 ≤ M * L := by nlinarith
  set F : ℕ → ℝ := fun ℓ => if hℓ : 0 < ℓ then
    (haveI : NeZero ℓ := NeZero.of_pos hℓ;
      twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k) else 0 with hF
  have hFeq : ∀ (ℓ : ℕ) [NeZero ℓ],
      F ℓ = twoPointTruncated d N ℓ β ν h (embedZ ℓ x) (embedZ ℓ y) i k := by
    intro ℓ _
    have hℓ : 0 < ℓ := Nat.pos_of_ne_zero (NeZero.ne ℓ)
    simp [hF, hℓ]
  obtain ⟨G, hG⟩ := exists_tendsto_along_multiples hq F (fun ε hε => by
    obtain ⟨K, hK⟩ := exists_pow_half_lt (show 0 ≤ 48 * c₉ by positivity) hε
    set R := M * L ^ (kf + 1) * K + X0 + 1 with hR
    refine ⟨max (kf + 1) (4 * R), fun ℓ ℓ' hℓ hℓ' hd1 hd2 => ?_⟩
    have : NeZero ℓ := NeZero.of_pos hℓ
    have : NeZero ℓ' := NeZero.of_pos hℓ'
    rw [hFeq ℓ, hFeq ℓ']
    refine lt_of_le_of_lt (twoPoint_cmp hcl hd hδ hL hc₉ hκ
      (admissible_of_dvd_pow (le_max_left _ _) hd1) (admissible_of_dvd_pow (le_max_left _ _) hd2)
      hR (four_mul_le_of_dvd_pow hq hℓ (le_max_right _ _) hd1)
      (four_mul_le_of_dvd_pow hq hℓ' (le_max_right _ _) hd2) hx hy i k) ?_
    linarith)
  refine ⟨G, fun ε hε => ?_⟩
  obtain ⟨n0, hn0⟩ := hG ε hε
  exact ⟨n0, fun ℓ _ hdvd => by
    rw [← hFeq ℓ]
    exact hn0 ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ)) hdvd⟩

end Limit

end Balaban.Correlations
