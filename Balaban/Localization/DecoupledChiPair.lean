/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledGs
public import Balaban.Background.BumpMixed
public import Balaban.Multiscale.PointwiseGeom
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Pair regularity of the cut-off functions `χ_z` at arbitrary displacements (LOCALIZATION.md §3.1)

The Hölder part of (DG2) needs the Hölder seminorm of `∂χ_z` between two sites `x` and
`x' = x + z` with an arbitrary integer displacement `z`.  A lattice path from `x` to `x'` may leave
`Ω₁`, where the denominator of `χ_z = b_z / D` is not bounded below, so (Cov3) cannot be summed
along a path.  Instead the bump `b_z` (a product of B-splines, defined on the whole torus) is
summed along the path, and the quotient is treated by an algebraic identity at the four corners
`x, x + e, x', x' + e`, at which `D ≥ 4⁻ᵈ`:

* `lipschitz_lift`: a function with unit-step increments `≤ c` has increments `≤ c ∑|z_i|` along
  an arbitrary integer displacement `z`;
* `cubeBump_lip`, `cubeBump_mixed_lip`: first and mixed second differences of the bump;
* `chi_pair`: `|χ(x'+e) - χ(x+e)| ≤ c₁ ‖z‖₁ / (M₁ ℓ(x))` and
  `|∂_eχ(x') - ∂_eχ(x)| ≤ c₂ ‖z‖₁ / (M₁ ℓ(x))²`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset

section Lift

variable {d : ℕ}

theorem intTorus_sub_single' {m : ℕ} (w : Fin d → ℤ) (μ : Fin d) :
    (intTorus (w - Pi.single μ 1) : Torus d m) = intTorus w - Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [intTorus_apply]
  · simp [intTorus_apply, h]

theorem intTorus_add_single' {m : ℕ} (w : Fin d → ℤ) (μ : Fin d) :
    (intTorus (w + Pi.single μ 1) : Torus d m) = intTorus w + Pi.single μ 1 := by
  funext i
  by_cases h : i = μ
  · subst h; simp [intTorus_apply]
  · simp [intTorus_apply, h]

/-- **Increments along an integer displacement, from forward unit steps on a ball.**  If the
forward unit-step increments of `F` at the points `y + w'`, `‖w'‖ ≤ R`, are `≤ c`, the increment
along any `w` with `‖w‖ ≤ R` is `≤ c ∑ |w_i|`. -/
theorem lipschitz_ball {m : ℕ} {E : Type*} [SeminormedAddCommGroup E] (F : Torus d m → E)
    (y : Torus d m) {c R : ℝ}
    (hp : ∀ w' : Fin d → ℤ, ‖w'‖ ≤ R → ∀ μ,
      ‖F (y + intTorus w' + Pi.single μ 1) - F (y + intTorus w')‖ ≤ c) :
    ∀ (N : ℕ) (w : Fin d → ℤ), ∑ i, (w i).natAbs = N → ‖w‖ ≤ R →
      ‖F (y + intTorus w) - F y‖ ≤ N * c := by
  intro N
  induction N with
  | zero =>
      intro w hw _
      have h0 : w = 0 := by
        funext i
        have := (Finset.sum_eq_zero_iff.1 hw) i (Finset.mem_univ i)
        simpa using this
      subst h0
      have : (intTorus (0 : Fin d → ℤ) : Torus d m) = 0 := by
        funext μ; simp [intTorus_apply]
      simp [this]
  | succ N ih =>
      intro w hw hwR
      obtain ⟨μ, -, hμ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
        (f := fun i => (w i).natAbs) (by rw [hw]; omega)
      have hwμ : w μ ≠ 0 := by
        intro h; apply hμ; simp [h]
      obtain ⟨w', hsum, hnorm, hw'⟩ := exists_descent w μ hwμ
      have ih' := ih w' (by omega) (hnorm.trans hwR)
      have hc : 0 ≤ c := by
        have := hp 0 (by simpa using ((norm_nonneg w).trans hwR)) μ
        exact (norm_nonneg _).trans this
      rcases hw' with rfl | rfl
      · -- w = w' + e_μ
        have := hp (w - Pi.single μ 1) (hnorm.trans hwR) μ
        have e : y + intTorus (w - Pi.single μ 1) + Pi.single μ 1 = y + intTorus w := by
          rw [intTorus_sub_single']; abel
        rw [e] at this
        calc ‖F (y + intTorus w) - F y‖
            = ‖(F (y + intTorus w) - F (y + intTorus (w - Pi.single μ 1))) +
              (F (y + intTorus (w - Pi.single μ 1)) - F y)‖ := by congr 1; abel
          _ ≤ c + (N * c) := (norm_add_le _ _).trans (add_le_add this ih')
          _ = ((N + 1 : ℕ) : ℝ) * c := by push_cast; ring
      · -- w' = w + e_μ
        have := hp w hwR μ
        have e : y + intTorus w + Pi.single μ 1 = y + intTorus (w + Pi.single μ 1) := by
          rw [intTorus_add_single']; abel
        rw [e] at this
        calc ‖F (y + intTorus w) - F y‖
            = ‖(F (y + intTorus w) - F (y + intTorus (w + Pi.single μ 1))) +
              (F (y + intTorus (w + Pi.single μ 1)) - F y)‖ := by congr 1; abel
          _ ≤ c + (N * c) := by
              refine (norm_add_le _ _).trans (add_le_add ?_ ih')
              rw [norm_sub_rev]; exact this
          _ = ((N + 1 : ℕ) : ℝ) * c := by push_cast; ring

/-- **Increments along an arbitrary integer displacement.**  If all forward unit-step increments
of `F` are `≤ c`, the increment along `w` is `≤ c ∑ |w_i|`. -/
theorem lipschitz_lift {m : ℕ} {E : Type*} [SeminormedAddCommGroup E] (F : Torus d m → E)
    {c : ℝ} (hp : ∀ y μ, ‖F (y + Pi.single μ 1) - F y‖ ≤ c) (N : ℕ) (w : Fin d → ℤ)
    (hw : ∑ i, (w i).natAbs = N) (y : Torus d m) :
    ‖F (y + intTorus w) - F y‖ ≤ N * c :=
  lipschitz_ball F y (R := ‖w‖) (fun w' _ μ => hp (y + intTorus w') μ) N w hw le_rfl

end Lift

section Bump

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L]

/-- Mixed second differences of the cube bump, for all pairs of directions. -/
theorem cubeBump_sq_diff {j : ℕ} (hj : j ≤ K) (hlam : 2 ≤ L ^ (j + m₁))
    (y0 x : Torus d ((N₁ * L ^ m₁) * L ^ K)) (μ ν : Fin d) :
    |cubeBump m₁ j y0 (x + Pi.single μ 1 + Pi.single ν 1) - cubeBump m₁ j y0 (x + Pi.single μ 1) -
        cubeBump m₁ j y0 (x + Pi.single ν 1) + cubeBump m₁ j y0 x| ≤
      22500 * 4 ^ d / ((L : ℝ) ^ (j + m₁)) ^ 2 := by
  have := bump_sq_diff (d := d) (L := L) (N₀ := N₁) (k := K + m₁) (m := j + m₁) (by omega) hlam
    (tor m₁ y0) (tor m₁ x) μ ν
  unfold cubeBump
  rw [tor_add_single, tor_add_single, tor_add_single]
  exact this

/-- **Lipschitz bound of the cube bump along an arbitrary displacement.** -/
theorem cubeBump_lip {j : ℕ} (hj : j ≤ K) (hlam : 2 ≤ L ^ (j + m₁))
    (y0 : Torus d ((N₁ * L ^ m₁) * L ^ K)) (N : ℕ) (w : Fin d → ℤ)
    (hw : ∑ i, (w i).natAbs = N) (y : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    |cubeBump m₁ j y0 (y + intTorus w) - cubeBump m₁ j y0 y| ≤
      N * (150 * 4 ^ d / (L : ℝ) ^ (j + m₁)) := by
  have := lipschitz_lift (fun y => cubeBump m₁ j y0 y) (c := 150 * 4 ^ d / (L : ℝ) ^ (j + m₁))
    (fun y μ => by
      rw [Real.norm_eq_abs]; exact (cubeBump_diff hj hlam y0 y μ).1) N w hw y
  simpa [Real.norm_eq_abs] using this

/-- **Lipschitz bound of the first difference of the cube bump** (mixed second differences along
an arbitrary displacement). -/
theorem cubeBump_mixed_lip {j : ℕ} (hj : j ≤ K) (hlam : 2 ≤ L ^ (j + m₁))
    (y0 : Torus d ((N₁ * L ^ m₁) * L ^ K)) (ν : Fin d) (N : ℕ) (w : Fin d → ℤ)
    (hw : ∑ i, (w i).natAbs = N) (y : Torus d ((N₁ * L ^ m₁) * L ^ K)) :
    |(cubeBump m₁ j y0 (y + intTorus w + Pi.single ν 1) - cubeBump m₁ j y0 (y + intTorus w)) -
        (cubeBump m₁ j y0 (y + Pi.single ν 1) - cubeBump m₁ j y0 y)| ≤
      N * (22500 * 4 ^ d / ((L : ℝ) ^ (j + m₁)) ^ 2) := by
  have := lipschitz_lift (fun y => cubeBump m₁ j y0 (y + Pi.single ν 1) - cubeBump m₁ j y0 y)
    (c := 22500 * 4 ^ d / ((L : ℝ) ^ (j + m₁)) ^ 2)
    (fun y μ => by
      rw [Real.norm_eq_abs]
      have h := cubeBump_sq_diff hj hlam y0 y μ ν
      refine le_trans (le_of_eq ?_) h
      congr 1; ring) N w hw y
  simpa [Real.norm_eq_abs] using this

end Bump


section Algebra

/-- The quotient estimate at two points. -/
theorem quotient_first {b2 b4 D2 D4 δ : ℝ} (hδ : 0 < δ) (h2 : δ ≤ D2) (h4 : δ ≤ D4)
    (hb2 : 0 ≤ b2) (hb2D : b2 ≤ D2) :
    |b4 / D4 - b2 / D2| ≤ (|b4 - b2| + |D4 - D2|) / δ := by
  have hD2 : 0 < D2 := lt_of_lt_of_le hδ h2
  have hD4 : 0 < D4 := lt_of_lt_of_le hδ h4
  have e : b4 / D4 - b2 / D2 = (b4 - b2) / D4 - (b2 / D2) * ((D4 - D2) / D4) := by
    field_simp; ring
  have hq0 : 0 ≤ b2 / D2 := div_nonneg hb2 hD2.le
  have hq1 : b2 / D2 ≤ 1 := (div_le_one hD2).2 hb2D
  rw [e]
  have h1 : |(b4 - b2) / D4| ≤ |b4 - b2| / δ := by
    rw [abs_div, abs_of_pos hD4]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hδ h4
  have h2' : |(b2 / D2) * ((D4 - D2) / D4)| ≤ |D4 - D2| / δ := by
    rw [abs_mul, abs_of_nonneg hq0, abs_div, abs_of_pos hD4]
    calc b2 / D2 * (|D4 - D2| / D4) ≤ 1 * (|D4 - D2| / D4) :=
          mul_le_mul_of_nonneg_right hq1 (by positivity)
      _ = |D4 - D2| / D4 := one_mul _
      _ ≤ |D4 - D2| / δ := div_le_div_of_nonneg_left (abs_nonneg _) hδ h4
  calc _ ≤ |(b4 - b2) / D4| + |(b2 / D2) * ((D4 - D2) / D4)| := abs_sub _ _
    _ ≤ |b4 - b2| / δ + |D4 - D2| / δ := add_le_add h1 h2'
    _ = _ := by ring

/-- Division of a bound by the lower bound of the pivot. -/
theorem abs_le_div_of_mul {D1 δ X E : ℝ} (hδ : 0 < δ) (h1 : δ ≤ D1) (hE : D1 * X = E) :
    |X| ≤ |E| / δ := by
  have hD1 : 0 < D1 := lt_of_lt_of_le hδ h1
  have : |X| = |E| / D1 := by
    rw [← hE, abs_mul, abs_of_pos hD1]; field_simp
  rw [this]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hδ h1

theorem product_second (a1 a2 a3 a4 c1 c2 c3 c4 : ℝ) :
    a4 * c4 - a3 * c3 - a2 * c2 + a1 * c1 =
      a4 * (c4 - c3 - c2 + c1) + c1 * (a4 - a3 - a2 + a1) + (a4 - a3) * (c3 - c1) +
        (a4 - a2) * (c2 - c1) := by ring

end Algebra

section Pair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-- A sum over the centres, supported on a finite set `A` with termwise bound `c`. -/
theorem sum_cubeIdx_le {A : Finset (ℕ × CTorus d L N₁ m₁ K)} (hA : A ⊆ cubeIdx G)
    {f : ℕ × CTorus d L N₁ m₁ K → ℝ} {c : ℝ}
    (h0 : ∀ q ∈ cubeIdx G, q ∉ A → f q = 0) (h1 : ∀ q ∈ A, |f q| ≤ c) :
    |∑ q ∈ cubeIdx G, f q| ≤ A.card * c := by
  rw [← Finset.sum_subset hA h0]
  calc |∑ q ∈ A, f q| ≤ ∑ q ∈ A, |f q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _q ∈ A, c := Finset.sum_le_sum h1
    _ = A.card * c := by simp

theorem pow_scale {L : ℕ} (hL : 1 ≤ L) {n m s m₁ : ℕ} (h : n ≤ m + s) :
    (L : ℝ) ^ (n + m₁) ≤ (L : ℝ) ^ s * (L : ℝ) ^ (m + m₁) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  rw [← pow_add]
  exact pow_le_pow_right₀ hL' (by omega)

/-- `c / L^(m+m₁) ≤ c L^s / L^(n+m₁)` when `n ≤ m + s`. -/
theorem div_pow_scale {L : ℕ} (hL : 1 ≤ L) {n m s m₁ : ℕ} (h : n ≤ m + s) {c : ℝ} (hc : 0 ≤ c) :
    c / (L : ℝ) ^ (m + m₁) ≤ c * (L : ℝ) ^ s / (L : ℝ) ^ (n + m₁) := by
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have h1 : (0 : ℝ) < (L : ℝ) ^ (m + m₁) := by positivity
  have h2 : (0 : ℝ) < (L : ℝ) ^ (n + m₁) := by positivity
  rw [div_le_div_iff₀ h1 h2]
  have := pow_scale (m₁ := m₁) hL h
  nlinarith [mul_le_mul_of_nonneg_left this hc]


/-- The constant of the Lipschitz bound of `χ`. -/
noncomputable def cChi1 (d L : ℕ) : ℝ := 4 ^ d * (150 * 4 ^ d * (L : ℝ) ^ 2 * (1 + 18 * 3 ^ d))

/-- The constant of the mixed second difference of `χ`. -/
noncomputable def cChi2 (d L : ℕ) : ℝ :=
  4 ^ d * (22500 * 4 ^ d * (L : ℝ) ^ 4 * (1 + 18 * 3 ^ d) +
    cH1 d L * L * (18 * 3 ^ d * (150 * 4 ^ d * (L : ℝ) ^ 2)) + cChi1 d L * wU d L)

theorem cChi1_nonneg (d L : ℕ) : 0 ≤ cChi1 d L := by unfold cChi1; positivity

theorem cChi2_nonneg (d L : ℕ) : 0 ≤ cChi2 d L := by
  unfold cChi2
  have := cH1_nonneg d L
  have := cChi1_nonneg d L
  have := wU_nonneg d L
  positivity

/-- **Pair regularity of `χ_z` at an arbitrary displacement.**  For `x` of layer `n`,
`x' = x + z` of layer `n'` with `n ≤ n' + 1`, `N = ∑ |z_i|`, `ℓ(x) M₁ = L^(n+m₁)`:
`|χ(x' + e) - χ(x + e)| ≤ c₁ N / (M₁ ℓ(x))` and
`|(χ(x' + e) - χ(x')) - (χ(x + e) - χ(x))| ≤ c₂ N / (M₁ ℓ(x))²`. -/
theorem chi_pair (hG : CubeAligned G m₁) (hϱ : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ)
    (hd : 1 ≤ d) (hL : 2 ≤ L) {n n' : ℕ} (hn1 : 1 ≤ n) (hnK : n ≤ K) (hn1' : 1 ≤ n')
    (hnK' : n' ≤ K) (hnn : n ≤ n' + 1) {x : CTorus d L N₁ m₁ K} (hx : x ∈ G.layer n)
    (z : Fin d → ℤ) (hx' : x + intTorus z ∈ G.layer n') (ν : Fin d)
    {q : ℕ × CTorus d L N₁ m₁ K} (hq : q ∈ cubeIdx G) :
    |chi G q (x + intTorus z + Pi.single ν 1) - chi G q (x + Pi.single ν 1)| ≤
        cChi1 d L * (∑ i, (z i).natAbs : ℕ) / (L : ℝ) ^ (n + m₁) ∧
    |(chi G q (x + intTorus z + Pi.single ν 1) - chi G q (x + intTorus z)) -
        (chi G q (x + Pi.single ν 1) - chi G q x)| ≤
        cChi2 d L * (∑ i, (z i).natAbs : ℕ) / ((L : ℝ) ^ (n + m₁)) ^ 2 := by
  classical
  set e : CTorus d L N₁ m₁ K := Pi.single ν 1 with he
  set x' : CTorus d L N₁ m₁ K := x + intTorus z with hx'def
  set N : ℝ := ((∑ i, (z i).natAbs : ℕ) : ℝ) with hN
  have hN0 : 0 ≤ N := Nat.cast_nonneg _
  set Bn : ℝ := (L : ℝ) ^ (n + m₁) with hBn
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by omega : 1 ≤ L)
  have hBn0 : 0 < Bn := by positivity
  have hq4 : (0 : ℝ) < (1 / 4 : ℝ) ^ d := by positivity
  -- the denominators at the four corners
  have hD1 := coverDenom_ge hG hL hn1 hnK hx ν (Or.inl rfl)
  have hD2 := coverDenom_ge hG hL hn1 hnK hx ν (Or.inr (Or.inl rfl))
  have hD3 := coverDenom_ge hG hL hn1' hnK' hx' ν (Or.inl rfl)
  have hD4 := coverDenom_ge hG hL hn1' hnK' hx' ν (Or.inr (Or.inl rfl))
  -- the active centres
  set A : Finset (ℕ × CTorus d L N₁ m₁ K) := cubeSupp G x ν ∪ cubeSupp G x' ν with hA
  have hAsub : A ⊆ cubeIdx G := Finset.union_subset (cubeSupp_subset x ν) (cubeSupp_subset x' ν)
  have hAcard : (A.card : ℝ) ≤ 18 * 3 ^ d := by
    have h1 := card_cubeSupp_le hG hϱ hd (by omega) hn1 hnK hx ν
    have h2 := card_cubeSupp_le hG hϱ hd (by omega) hn1' hnK' hx' ν
    have := card_union_le (cubeSupp G x ν) (cubeSupp G x' ν)
    have h3 : A.card ≤ 18 * 3 ^ d := by rw [hA]; omega
    exact_mod_cast h3
  have hAlayer : ∀ q' ∈ A, n ≤ q'.1 + 2 := by
    intro q' hq'
    rcases Finset.mem_union.1 hq' with h | h
    · have := cubeSupp_layer_bounds hG hϱ hd (by omega) hn1 hnK hx ν h; omega
    · have := cubeSupp_layer_bounds hG hϱ hd (by omega) hn1' hnK' hx' ν h; omega
  have hAzero : ∀ q' ∈ cubeIdx G, q' ∉ A →
      cubeBump m₁ q'.1 q'.2 x = 0 ∧ cubeBump m₁ q'.1 q'.2 (x + e) = 0 ∧
      cubeBump m₁ q'.1 q'.2 x' = 0 ∧ cubeBump m₁ q'.1 q'.2 (x' + e) = 0 := by
    intro q' hq' hnA
    have h1 : q' ∉ cubeSupp G x ν := fun h => hnA (Finset.mem_union_left _ h)
    have h2 : q' ∉ cubeSupp G x' ν := fun h => hnA (Finset.mem_union_right _ h)
    obtain ⟨a1, a2, -⟩ := not_mem_cubeSupp hq' h1
    obtain ⟨a3, a4, -⟩ := not_mem_cubeSupp hq' h2
    exact ⟨a1, a2, a3, a4⟩
  -- the bump increments
  have hlam : ∀ q' ∈ cubeIdx G, 2 ≤ L ^ (q'.1 + m₁) := by
    intro q' hq'
    obtain ⟨⟨hm1, hmK⟩, -, -⟩ := (mem_cubeIdx G).1 hq'
    calc 2 ≤ L := hL
      _ = L ^ 1 := (pow_one L).symm
      _ ≤ L ^ (q'.1 + m₁) := Nat.pow_le_pow_right (by omega) (by omega)
  have hbK : ∀ q' ∈ cubeIdx G, q'.1 ≤ K := fun q' hq' => ((mem_cubeIdx G).1 hq').1.2
  set cb1 : ℝ := 150 * 4 ^ d * (L : ℝ) ^ 2 with hcb1
  set cb2 : ℝ := 22500 * 4 ^ d * (L : ℝ) ^ 4 with hcb2
  have hbl : ∀ q' ∈ cubeIdx G, ∀ y : CTorus d L N₁ m₁ K,
      (q' ∈ A → |cubeBump m₁ q'.1 q'.2 (y + intTorus z) - cubeBump m₁ q'.1 q'.2 y| ≤ N * cb1 / Bn) := by
    intro q' hq' y hqA
    have h := cubeBump_lip (hbK q' hq') (hlam q' hq') q'.2 _ z rfl y
    refine h.trans ?_
    have := div_pow_scale (m₁ := m₁) (by omega : 1 ≤ L) (hAlayer q' hqA) (c := 150 * 4 ^ d) (by positivity)
    calc ((∑ i, (z i).natAbs : ℕ) : ℝ) * (150 * 4 ^ d / (L : ℝ) ^ (q'.1 + m₁))
        ≤ N * (150 * 4 ^ d * (L : ℝ) ^ 2 / Bn) := mul_le_mul_of_nonneg_left this hN0
      _ = N * cb1 / Bn := by rw [hcb1]; ring
  have hbm : ∀ q' ∈ cubeIdx G, ∀ y : CTorus d L N₁ m₁ K, q' ∈ A →
      |(cubeBump m₁ q'.1 q'.2 (y + intTorus z + e) - cubeBump m₁ q'.1 q'.2 (y + intTorus z)) -
        (cubeBump m₁ q'.1 q'.2 (y + e) - cubeBump m₁ q'.1 q'.2 y)| ≤ N * cb2 / Bn ^ 2 := by
    intro q' hq' y hqA
    have h := cubeBump_mixed_lip (hbK q' hq') (hlam q' hq') q'.2 ν _ z rfl y
    refine h.trans ?_
    have := div_pow_scale (m₁ := m₁) (by omega : 1 ≤ L) (hAlayer q' hqA) (c := 22500 * 4 ^ d) (by positivity)
    have h2 : 22500 * 4 ^ d / ((L : ℝ) ^ (q'.1 + m₁)) ^ 2 ≤ 22500 * 4 ^ d * (L : ℝ) ^ 4 / Bn ^ 2 := by
      have hq0 : (0 : ℝ) < (L : ℝ) ^ (q'.1 + m₁) := by positivity
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have h3 := pow_scale (m₁ := m₁) (by omega : 1 ≤ L) (hAlayer q' hqA)
      have h4 : Bn ^ 2 ≤ ((L : ℝ) ^ 2 * (L : ℝ) ^ (q'.1 + m₁)) ^ 2 :=
        pow_le_pow_left₀ hBn0.le h3 2
      have : (0 : ℝ) ≤ 22500 * 4 ^ d := by positivity
      nlinarith [mul_le_mul_of_nonneg_left h4 this]
    calc ((∑ i, (z i).natAbs : ℕ) : ℝ) * (22500 * 4 ^ d / ((L : ℝ) ^ (q'.1 + m₁)) ^ 2)
        ≤ N * (22500 * 4 ^ d * (L : ℝ) ^ 4 / Bn ^ 2) := mul_le_mul_of_nonneg_left h2 hN0
      _ = N * cb2 / Bn ^ 2 := by rw [hcb2]; ring
  -- the denominator increments
  have hDsub : ∀ P : CTorus d L N₁ m₁ K, coverDenom G P = ∑ q' ∈ cubeIdx G, cubeBump m₁ q'.1 q'.2 P :=
    fun P => rfl
  have hDlip : ∀ y : CTorus d L N₁ m₁ K,
      (∀ q' ∈ cubeIdx G, q' ∉ A → cubeBump m₁ q'.1 q'.2 y = 0 ∧
        cubeBump m₁ q'.1 q'.2 (y + intTorus z) = 0) →
      |coverDenom G (y + intTorus z) - coverDenom G y| ≤ 18 * 3 ^ d * (N * cb1 / Bn) := by
    intro y hy
    rw [hDsub, hDsub, ← Finset.sum_sub_distrib]
    have := sum_cubeIdx_le (G := G) hAsub
      (f := fun q' => cubeBump m₁ q'.1 q'.2 (y + intTorus z) - cubeBump m₁ q'.1 q'.2 y)
      (c := N * cb1 / Bn) (fun q' hq' hnA => by
        obtain ⟨h1, h2⟩ := hy q' hq' hnA; rw [h1, h2]; ring) (fun q' hq' => hbl q' (hAsub hq') y hq')
    refine this.trans ?_
    have : 0 ≤ N * cb1 / Bn := by positivity
    exact mul_le_mul_of_nonneg_right hAcard this
  have hDpos : ∀ P : CTorus d L N₁ m₁ K, (1 / 4 : ℝ) ^ d ≤ coverDenom G P → 0 < coverDenom G P :=
    fun P h => lt_of_lt_of_le hq4 h
  have hbD : ∀ P : CTorus d L N₁ m₁ K, cubeBump m₁ q.1 q.2 P ≤ coverDenom G P := by
    intro P
    have := Finset.single_le_sum
      (f := fun q : ℕ × CTorus d L N₁ m₁ K => cubeBump m₁ q.1 q.2 P)
      (fun q hq => cubeBump_nonneg_of_mem G hq P) hq
    exact this
  have hb0 : ∀ P : CTorus d L N₁ m₁ K, 0 ≤ cubeBump m₁ q.1 q.2 P :=
    fun P => cubeBump_nonneg_of_mem G hq P
  have hxe : x + intTorus z + e = x' + e := rfl
  have hshift : x + e + intTorus z = x' + e := by rw [hx'def]; abel
  -- bump increments for the given centre
  have hqb1 : |cubeBump m₁ q.1 q.2 (x' + e) - cubeBump m₁ q.1 q.2 (x + e)| ≤ N * cb1 / Bn := by
    by_cases hqA : q ∈ A
    · have := hbl q hq (x + e) hqA
      rwa [hshift] at this
    · obtain ⟨-, a2, -, a4⟩ := hAzero q hq hqA
      rw [a2, a4]; simp; positivity
  have hDe : |coverDenom G (x' + e) - coverDenom G (x + e)| ≤ 18 * 3 ^ d * (N * cb1 / Bn) := by
    have := hDlip (x + e) (fun q' hq' hnA => by
      obtain ⟨-, a2, -, a4⟩ := hAzero q' hq' hnA
      rw [hshift]; exact ⟨a2, a4⟩)
    rwa [hshift] at this
  have hfirst : |chi G q (x' + e) - chi G q (x + e)| ≤ cChi1 d L * N / Bn := by
    have h := quotient_first (b4 := cubeBump m₁ q.1 q.2 (x' + e)) hq4 hD2 hD4 (hb0 (x + e)) (hbD (x + e))
    unfold chi
    refine h.trans ?_
    have hsum : |cubeBump m₁ q.1 q.2 (x' + e) - cubeBump m₁ q.1 q.2 (x + e)| +
        |coverDenom G (x' + e) - coverDenom G (x + e)| ≤
        (1 + 18 * 3 ^ d) * (N * cb1 / Bn) := by nlinarith [hqb1, hDe]
    calc _ ≤ ((1 + 18 * 3 ^ d) * (N * cb1 / Bn)) / (1 / 4 : ℝ) ^ d :=
          div_le_div_of_nonneg_right hsum hq4.le
      _ = cChi1 d L * N / Bn := by
          unfold cChi1; rw [hcb1, one_div, inv_pow]; field_simp
  refine ⟨hfirst, ?_⟩
  -- the mixed second difference
  have hqb2 : |(cubeBump m₁ q.1 q.2 (x' + e) - cubeBump m₁ q.1 q.2 x') -
      (cubeBump m₁ q.1 q.2 (x + e) - cubeBump m₁ q.1 q.2 x)| ≤ N * cb2 / Bn ^ 2 := by
    by_cases hqA : q ∈ A
    · exact hbm q hq x hqA
    · obtain ⟨a1, a2, a3, a4⟩ := hAzero q hq hqA
      rw [a1, a2, a3, a4]; simp; positivity
  have hDmix : |(coverDenom G (x' + e) - coverDenom G x') - (coverDenom G (x + e) - coverDenom G x)| ≤
      18 * 3 ^ d * (N * cb2 / Bn ^ 2) := by
    rw [hDsub, hDsub, hDsub, hDsub]
    have e1 : (∑ q' ∈ cubeIdx G, cubeBump m₁ q'.1 q'.2 (x' + e) -
        ∑ q' ∈ cubeIdx G, cubeBump m₁ q'.1 q'.2 x') -
        (∑ q' ∈ cubeIdx G, cubeBump m₁ q'.1 q'.2 (x + e) -
        ∑ q' ∈ cubeIdx G, cubeBump m₁ q'.1 q'.2 x) =
        ∑ q' ∈ cubeIdx G, ((cubeBump m₁ q'.1 q'.2 (x' + e) - cubeBump m₁ q'.1 q'.2 x') -
          (cubeBump m₁ q'.1 q'.2 (x + e) - cubeBump m₁ q'.1 q'.2 x)) := by
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    rw [e1]
    have := sum_cubeIdx_le (G := G) hAsub
      (f := fun q' => (cubeBump m₁ q'.1 q'.2 (x' + e) - cubeBump m₁ q'.1 q'.2 x') -
          (cubeBump m₁ q'.1 q'.2 (x + e) - cubeBump m₁ q'.1 q'.2 x))
      (c := N * cb2 / Bn ^ 2) (fun q' hq' hnA => by
        obtain ⟨a1, a2, a3, a4⟩ := hAzero q' hq' hnA
        simp only [a1, a2, a3, a4]; ring) (fun q' hq' => hbm q' (hAsub hq') x hq')
    refine this.trans ?_
    have : 0 ≤ N * cb2 / Bn ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hAcard this
  have hD31 : |coverDenom G x' - coverDenom G x| ≤ 18 * 3 ^ d * (N * cb1 / Bn) := by
    have := hDlip x (fun q' hq' hnA => by
      obtain ⟨a1, -, a3, -⟩ := hAzero q' hq' hnA
      exact ⟨a1, a3⟩)
    exact this
  have hx21 : |coverDenom G (x + e) - coverDenom G x| ≤ wU d L / Bn :=
    (coverDenom_diff hG hϱ hd hL hn1 hnK hx ν).1
  have hc43 : |chi G q (x' + e) - chi G q x'| ≤ cH1 d L * L / Bn := by
    have h := (chi_diff hG hϱ hd hL hn1' hnK' hx' ν hq).1
    refine h.trans ?_
    exact div_pow_scale (m₁ := m₁) (by omega : 1 ≤ L) (n := n) (m := n') (s := 1)
      (by omega) (cH1_nonneg d L) |>.trans (by simp [hBn])
  have hc4 : |chi G q (x' + e)| ≤ 1 := by
    have := chi_nbr_mem_unit hG hL hn1' hnK' hx' ν (Or.inr (Or.inl rfl)) hq
    rw [abs_of_nonneg this.1]; exact this.2
  have hid : coverDenom G x * ((chi G q (x' + e) - chi G q x') - (chi G q (x + e) - chi G q x)) =
      ((cubeBump m₁ q.1 q.2 (x' + e) - cubeBump m₁ q.1 q.2 x') -
        (cubeBump m₁ q.1 q.2 (x + e) - cubeBump m₁ q.1 q.2 x)) -
      chi G q (x' + e) * ((coverDenom G (x' + e) - coverDenom G x') -
        (coverDenom G (x + e) - coverDenom G x)) -
      (chi G q (x' + e) - chi G q x') * (coverDenom G x' - coverDenom G x) -
      (chi G q (x' + e) - chi G q (x + e)) * (coverDenom G (x + e) - coverDenom G x) := by
    have hp := product_second (chi G q x) (chi G q (x + e)) (chi G q x') (chi G q (x' + e))
      (coverDenom G x) (coverDenom G (x + e)) (coverDenom G x') (coverDenom G (x' + e))
    have hcb : ∀ P : CTorus d L N₁ m₁ K, 0 < coverDenom G P → chi G q P * coverDenom G P =
        cubeBump m₁ q.1 q.2 P := by
      intro P hP; unfold chi; field_simp
    rw [hcb _ (hDpos _ hD4), hcb _ (hDpos _ hD3), hcb _ (hDpos _ hD2), hcb _ (hDpos _ hD1)] at hp
    linarith
  have hE := abs_le_div_of_mul hq4 hD1 hid
  refine hE.trans ?_
  have hBn2 : 0 < Bn ^ 2 := by positivity
  have t1 := hqb2
  have t2 : |chi G q (x' + e) * ((coverDenom G (x' + e) - coverDenom G x') -
        (coverDenom G (x + e) - coverDenom G x))| ≤ 18 * 3 ^ d * (N * cb2 / Bn ^ 2) := by
    rw [abs_mul]
    calc _ ≤ 1 * (18 * 3 ^ d * (N * cb2 / Bn ^ 2)) :=
          mul_le_mul hc4 hDmix (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have t3 : |(chi G q (x' + e) - chi G q x') * (coverDenom G x' - coverDenom G x)| ≤
      (cH1 d L * L / Bn) * (18 * 3 ^ d * (N * cb1 / Bn)) := by
    rw [abs_mul]
    exact mul_le_mul hc43 hD31 (abs_nonneg _) (by have := cH1_nonneg d L; positivity)
  have t4 : |(chi G q (x' + e) - chi G q (x + e)) * (coverDenom G (x + e) - coverDenom G x)| ≤
      (cChi1 d L * N / Bn) * (wU d L / Bn) := by
    rw [abs_mul]
    exact mul_le_mul hfirst hx21 (abs_nonneg _) (by have := cChi1_nonneg d L; positivity)
  have hsplit : |((cubeBump m₁ q.1 q.2 (x' + e) - cubeBump m₁ q.1 q.2 x') -
        (cubeBump m₁ q.1 q.2 (x + e) - cubeBump m₁ q.1 q.2 x)) -
      chi G q (x' + e) * ((coverDenom G (x' + e) - coverDenom G x') -
        (coverDenom G (x + e) - coverDenom G x)) -
      (chi G q (x' + e) - chi G q x') * (coverDenom G x' - coverDenom G x) -
      (chi G q (x' + e) - chi G q (x + e)) * (coverDenom G (x + e) - coverDenom G x)| ≤
      N * cb2 / Bn ^ 2 + 18 * 3 ^ d * (N * cb2 / Bn ^ 2) +
        (cH1 d L * L / Bn) * (18 * 3 ^ d * (N * cb1 / Bn)) +
        (cChi1 d L * N / Bn) * (wU d L / Bn) := by
    have key : ∀ a b c d' : ℝ, |a - b - c - d'| ≤ |a| + |b| + |c| + |d'| := by
      intro a b c d'
      calc |a - b - c - d'| ≤ |a - b - c| + |d'| := abs_sub _ _
        _ ≤ |a - b| + |c| + |d'| := by gcongr; exact abs_sub _ _
        _ ≤ |a| + |b| + |c| + |d'| := by gcongr; exact abs_sub _ _
    refine (key _ _ _ _).trans ?_
    linarith [t1, t2, t3, t4]
  refine (div_le_div_of_nonneg_right hsplit hq4.le).trans (le_of_eq ?_)
  unfold cChi2
  rw [hcb1, hcb2, one_div, inv_pow]
  field_simp

end Pair

end Balaban.Localization
