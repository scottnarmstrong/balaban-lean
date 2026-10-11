module

public import Balaban.Gaussian.TermDictionary
public import Balaban.Correlations.SumRule
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The kernels `T_j^{ℓ,μ}(x, y)` of the multiscale decomposition on integer points

Integer points `x : Fin d → ℤ` are read modulo `ℓ` (`torusPoint`). `termKernel d L a μ J j m x y`
is the value at `(x mod ℓ, y mod ℓ)`, `ℓ = L ^ J * (m + 1)`, of the `j`-th term `fluctTerm J A₀ a j`
of the `J`-step decomposition of `A₀ = -Δ + μ`.

* `termKernel_nested` : the `j`-th term does not depend on the number `J > j` of steps, only on the
  torus: `T_j^{(n+1+j)}` on the side `L ^ (n+1+j) (m+1)` equals `T_j^{(j+1)}` on the side
  `L ^ (j+1) (m'+1)` whenever `m' + 1 = L ^ n (m + 1)` (nested tori);
* `sum_rule_termKernel` : the sum rule in the form used in CORRELATIONS.md §3.4, for integer
  points: with `S = ∑_{j<J} T_j`,
  `|((-Δ_x + μ) S)(x, y) - δ_{xy mod ℓ}| ≤ C_P L^{-Jd}`.
-/

@[expose] public section

namespace Balaban

open Matrix

/-- The integer point `x`, read modulo `ℓ`. -/
def torusPoint (d ℓ : ℕ) (x : Fin d → ℤ) : Torus d ℓ := fun i => (x i : ZMod ℓ)

theorem torusPoint_add_single (d ℓ : ℕ) (x : Fin d → ℤ) (ν : Fin d) :
    torusPoint d ℓ (x + Pi.single ν 1) = torusPoint d ℓ x + Pi.single ν 1 := by
  funext i
  by_cases h : i = ν
  · subst h; simp [torusPoint]
  · simp [torusPoint, h]

theorem torusPoint_sub_single (d ℓ : ℕ) (x : Fin d → ℤ) (ν : Fin d) :
    torusPoint d ℓ (x - Pi.single ν 1) = torusPoint d ℓ x - Pi.single ν 1 := by
  funext i
  by_cases h : i = ν
  · subst h; simp [torusPoint]
  · simp [torusPoint, h]

/-- The kernel of the `j`-th term of the `J`-step decomposition of `-Δ + μ` on the torus of side
`L ^ J * (m + 1)`, at the integer points `x, y`. -/
noncomputable def termKernel (d L : ℕ) [NeZero L] (a : ℕ → ℝ) (μ : ℝ) (J j m : ℕ)
    (x y : Fin d → ℤ) : ℝ :=
  fluctTerm (L := L) (m := m + 1) J (latticeLaplacian d (L ^ J * (m + 1)) μ) a j
    (torusPoint d _ x) (torusPoint d _ y)

variable {d L : ℕ} [NeZero L]

omit [NeZero L] in
theorem termDirect_congr (j : ℕ) {ℓ ℓ' ℓ₁ ℓ₁' m₂ m₂' : ℕ} [NeZero ℓ] [NeZero ℓ'] [NeZero ℓ₁]
    [NeZero ℓ₁'] [NeZero m₂] [NeZero m₂'] (hℓ : ℓ = ℓ') (h₁ : ℓ₁ = ℓ₁') (h₂ : m₂ = m₂')
    (μ : ℝ) (a : ℕ → ℝ) (x y : Fin d → ℤ) :
    termDirect d L j ℓ ℓ₁ m₂ (latticeLaplacian d ℓ μ) a (torusPoint d ℓ x) (torusPoint d ℓ y) =
      termDirect d L j ℓ' ℓ₁' m₂' (latticeLaplacian d ℓ' μ) a (torusPoint d ℓ' x)
        (torusPoint d ℓ' y) := by
  subst hℓ h₁ h₂
  rfl

/-- Nested tori: the `j`-th term of the decomposition on a given torus does not depend on the
number of steps of the decomposition (as long as it is `> j`). -/
theorem termKernel_nested {μ : ℝ} (hμ : 0 < μ) {a : ℕ → ℝ} (ha : ∀ i, 0 < a i) (n j m m' : ℕ)
    (hm' : m' + 1 = L ^ n * (m + 1)) (x y : Fin d → ℤ) :
    termKernel d L a μ (n + 1 + j) j m x y = termKernel d L a μ (j + 1) j m' x y := by
  unfold termKernel
  rw [fluctTerm_eq_termDirect (L := L) (m := m + 1) j n (n + 1 + j) rfl _ a
      (latticeLaplacian_posDef hμ) ha,
    fluctTerm_eq_termDirect (L := L) (m := m' + 1) j 0 (j + 1) (by omega) _ a
      (latticeLaplacian_posDef hμ) ha]
  refine termDirect_congr j ?_ ?_ ?_ μ a x y
  · rw [show n + 1 + j = j + 1 + n by ring, pow_add, mul_assoc, ← hm']
  · rw [hm']
    ring
  · rw [hm']
    ring

theorem fluct_torusPoint_eq_sum (J m : ℕ) (μ : ℝ) (a : ℕ → ℝ) (x y : Fin d → ℤ) :
    fluct (L := L) (m := m + 1) J (latticeLaplacian d (L ^ J * (m + 1)) μ) a
        (torusPoint d _ x) (torusPoint d _ y) =
      ∑ j ∈ Finset.range J, termKernel d L a μ J j m x y := by
  rw [fluct_eq_sum_fluctTerm, Matrix.sum_apply]
  rfl

/-- Distinct integer points stay distinct modulo `ℓ = L ^ J (m+1)` for `m` large. -/
theorem eventually_torusPoint_eq_iff (J : ℕ) (x y : Fin d → ℤ) :
    ∀ᶠ m in Filter.atTop, (torusPoint d (L ^ J * (m + 1)) x = torusPoint d (L ^ J * (m + 1)) y ↔
      x = y) := by
  refine Filter.eventually_atTop.mpr ⟨∑ i, (x i - y i).natAbs, fun m hm => ⟨fun h => ?_, fun h => by
    rw [h]⟩⟩
  funext i
  by_contra hne
  have hne' : x i - y i ≠ 0 := sub_ne_zero.mpr hne
  have hi := congrFun h i
  have h0 : ((x i - y i : ℤ) : ZMod (L ^ J * (m + 1))) = 0 := by
    push_cast
    rw [sub_eq_zero]
    exact hi
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  have h1 := Int.natAbs_dvd_natAbs.mpr h0
  rw [Int.natAbs_natCast] at h1
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hne') h1
  have hsum : (x i - y i).natAbs ≤ ∑ i, (x i - y i).natAbs :=
    Finset.single_le_sum (f := fun i => (x i - y i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have hpos : 1 ≤ L ^ J := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have : m + 1 ≤ L ^ J * (m + 1) := Nat.le_mul_of_pos_left _ hpos
  omega

/-- The sum rule for the kernels at integer points: with `S(z) = ∑_{j<J} T_j(z, y)`,
`|((-Δ_x + μ) S)(x) - δ_{x ≡ y}| ≤ C_P L^{-Jd}`, where `C_P` bounds the prolongation kernel. -/
theorem sum_rule_termKernel (J m : ℕ) {μ : ℝ} (hμ : 0 < μ) {a : ℕ → ℝ} (ha : ∀ i, 0 < a i)
    {C : ℝ}
    (hC : ∀ y u, |prolong (L := L) (m := m + 1) J (latticeLaplacian d (L ^ J * (m + 1)) μ) a y u| ≤
      C) (x y : Fin d → ℤ) :
    |(∑ ν : Fin d,
        (2 * ∑ j ∈ Finset.range J, termKernel d L a μ J j m x y -
          ∑ j ∈ Finset.range J, termKernel d L a μ J j m (x + Pi.single ν 1) y -
          ∑ j ∈ Finset.range J, termKernel d L a μ J j m (x - Pi.single ν 1) y) +
      μ * ∑ j ∈ Finset.range J, termKernel d L a μ J j m x y) -
      (if torusPoint d (L ^ J * (m + 1)) x = torusPoint d (L ^ J * (m + 1)) y then 1 else 0)| ≤
      C * (((L ^ J : ℕ) : ℝ) ^ d)⁻¹ := by
  have h := sum_rule_apply_abs_le (L := L) (m := m + 1) J hμ ha hC (torusPoint d _ x)
    (torusPoint d _ y)
  simp only [← torusPoint_add_single, ← torusPoint_sub_single, fluct_torusPoint_eq_sum] at h
  exact h

end Balaban
