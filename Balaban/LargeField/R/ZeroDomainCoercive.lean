module

public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.ZMod.Basic
public import Balaban.LargeField.Geometry.Continuous
public import Balaban.Lattice.Laplacian
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Finset Matrix

section OneD

variable {V : Type*} [SeminormedAddCommGroup V]

/-- `∑_{i<N} i (N - i) = (N - 1) N (N + 1) / 6` (real form). -/
theorem sum_mul_sub (N : ℕ) :
    ∑ i ∈ range (N + 1), (i : ℝ) * ((N : ℝ) - i) = ((N : ℝ) - 1) * N * (N + 1) / 6 := by
  have h1 : ∀ M : ℕ, ∑ i ∈ range (M + 1), (i : ℝ) = (M : ℝ) * (M + 1) / 2 := by
    intro M; induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; push_cast; ring
  have h2 : ∀ M : ℕ, ∑ i ∈ range (M + 1), (i : ℝ) ^ 2 = (M : ℝ) * (M + 1) * (2 * M + 1) / 6 := by
    intro M; induction M with
    | zero => simp
    | succ M ih => rw [sum_range_succ, ih]; push_cast; ring
  have : ∑ i ∈ range (N + 1), (i : ℝ) * ((N : ℝ) - i) =
      (N : ℝ) * ∑ i ∈ range (N + 1), (i : ℝ) - ∑ i ∈ range (N + 1), (i : ℝ) ^ 2 := by
    rw [mul_sum, ← sum_sub_distrib]; exact sum_congr rfl fun i _ => by ring
  rw [this, h1, h2]; ring

/-- `min (a X) (b Y) ≤ a b (X + Y) / (a + b)`. -/
theorem min_le_harmonic {a b X Y : ℝ} (ha : 0 < a) (hb : 0 < b) (_hX : 0 ≤ X) (_hY : 0 ≤ Y) {m : ℝ}
    (h1 : m ≤ a * X) (h2 : m ≤ b * Y) : m * (a + b) ≤ a * b * (X + Y) := by
  have e1 : m * b ≤ a * b * X := by nlinarith
  have e2 : m * a ≤ a * b * Y := by nlinarith
  nlinarith

/-- **Discrete Dirichlet–Poincaré inequality** on `N` bonds: a sequence vanishing at `0` and `N` satisfies
`∑_{i<N} ‖w_i‖² ≤ ((N² - 1)/6) ∑_{j<N} ‖w_{j+1} - w_j‖²`. -/
theorem poincare_1d (w : ℕ → V) (N : ℕ) (hN : 1 ≤ N) (h0 : w 0 = 0) (hN0 : w N = 0) :
    ∑ i ∈ range N, ‖w i‖ ^ 2 ≤ (((N : ℝ) ^ 2 - 1) / 6) * ∑ j ∈ range N, ‖w (j + 1) - w j‖ ^ 2 := by
  set E := ∑ j ∈ range N, ‖w (j + 1) - w j‖ ^ 2 with hE
  have hE0 : 0 ≤ E := sum_nonneg fun _ _ => by positivity
  -- pointwise bound
  have key : ∀ i ∈ range N, ‖w i‖ ^ 2 * (N : ℝ) ≤ (i : ℝ) * ((N : ℝ) - i) * E := by
    intro i hi
    have hiN := mem_range.mp hi
    by_cases hi0 : i = 0
    · subst hi0; simp [h0]
    have hipos : 0 < (i : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hi0
    have hNi : 0 < (N : ℝ) - i := by
      have : (i : ℝ) < N := by exact_mod_cast hiN
      linarith
    set X := ∑ j ∈ range i, ‖w (j + 1) - w j‖ ^ 2
    set Y := ∑ j ∈ Ico i N, ‖w (j + 1) - w j‖ ^ 2
    have hXY : X + Y = E := by
      rw [hE, ← sum_range_add_sum_Ico _ hiN.le]
    have hX0 : 0 ≤ X := sum_nonneg fun _ _ => by positivity
    have hY0 : 0 ≤ Y := sum_nonneg fun _ _ => by positivity
    -- left telescoping
    have hL : ‖w i‖ ≤ ∑ j ∈ range i, ‖w (j + 1) - w j‖ := by
      have : w i = ∑ j ∈ range i, (w (j + 1) - w j) := by
        rw [sum_range_sub (fun j => w j), h0, sub_zero]
      rw [this]; exact norm_sum_le _ _
    have hR : ‖w i‖ ≤ ∑ j ∈ Ico i N, ‖w (j + 1) - w j‖ := by
      have : w i = -∑ j ∈ Ico i N, (w (j + 1) - w j) := by
        rw [sum_Ico_eq_sum_range]
        have h := sum_range_sub (fun k => w (i + k)) (N - i)
        rw [show i + (N - i) = N by omega, hN0, add_zero] at h
        have h2 : ∑ k ∈ range (N - i), (w (i + k + 1) - w (i + k)) = - w i := by
          have h' := h; rw [zero_sub] at h'; exact h'
        rw [h2, neg_neg]
      rw [this, norm_neg]; exact norm_sum_le _ _
    have cs : ∀ (m : ℕ) (u : ℕ → ℝ), (∑ j ∈ range m, u j) ^ 2 ≤ m * ∑ j ∈ range m, u j ^ 2 := by
      intro m u
      simpa using _root_.sq_sum_le_card_mul_sum_sq (s := range m) (f := u)
    have hLsq : ‖w i‖ ^ 2 ≤ (i : ℝ) * X := by
      calc ‖w i‖ ^ 2 ≤ (∑ j ∈ range i, ‖w (j + 1) - w j‖) ^ 2 := by gcongr
        _ ≤ i * ∑ j ∈ range i, ‖w (j + 1) - w j‖ ^ 2 := cs i _
    have hRsq : ‖w i‖ ^ 2 ≤ ((N : ℝ) - i) * Y := by
      calc ‖w i‖ ^ 2 ≤ (∑ j ∈ Ico i N, ‖w (j + 1) - w j‖) ^ 2 := by gcongr
        _ ≤ ((Ico i N).card : ℝ) * ∑ j ∈ Ico i N, ‖w (j + 1) - w j‖ ^ 2 := by
          simpa using _root_.sq_sum_le_card_mul_sum_sq (s := Ico i N) (f := fun j => ‖w (j + 1) - w j‖)
        _ = ((N : ℝ) - i) * Y := by
          rw [Nat.card_Ico, Nat.cast_sub hiN.le]
    have h3 := min_le_harmonic hipos hNi hX0 hY0 (le_trans le_rfl hLsq) hRsq
    have h4 : (i : ℝ) + ((N : ℝ) - i) = N := by ring
    rw [h4, hXY] at h3
    exact h3
  have hsum : (∑ i ∈ range N, ‖w i‖ ^ 2) * (N : ℝ) ≤ (((N : ℝ) - 1) * N * (N + 1) / 6) * E := by
    rw [sum_mul]
    calc ∑ i ∈ range N, ‖w i‖ ^ 2 * (N : ℝ) ≤ ∑ i ∈ range N, (i : ℝ) * ((N : ℝ) - i) * E :=
          sum_le_sum key
      _ ≤ ∑ i ∈ range (N + 1), (i : ℝ) * ((N : ℝ) - i) * E := by
          rw [sum_range_succ _ N]; simp [sub_self]
      _ = (((N : ℝ) - 1) * N * (N + 1) / 6) * E := by
          rw [← sum_mul, sum_mul_sub]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have : ((N : ℝ) - 1) * N * (N + 1) / 6 = (((N : ℝ) ^ 2 - 1) / 6) * N := by ring
  rw [this] at hsum
  have := le_of_mul_le_mul_right (by linarith : (∑ i ∈ range N, ‖w i‖ ^ 2) * (N : ℝ) ≤ ((((N : ℝ) ^ 2 - 1) / 6) * E) * N) hNpos
  exact this

/-- On the cycle `ℤ/n`: a function supported on the `s` consecutive points `a, …, a + s - 1`, `s + 1 ≤ n`,
satisfies `∑ ‖g‖² ≤ ((s+1)² - 1)/6 · ∑ ‖g(t+1) - g(t)‖²`. -/
theorem poincare_cycle {n : ℕ} [NeZero n] (g : ZMod n → V) (a : ZMod n) (s : ℕ) (hs : s + 1 ≤ n)
    (hg : ∀ t, (¬ ∃ j < s, t = a + (j : ZMod n)) → g t = 0) :
    ∑ t, ‖g t‖ ^ 2 ≤ ((((s + 1 : ℕ) : ℝ) ^ 2 - 1) / 6) * ∑ t, ‖g (t + 1) - g t‖ ^ 2 := by
  classical
  have hinj : ∀ i j : ℕ, i < n → j < n → (a + (i : ZMod n) = a + (j : ZMod n)) → i = j := by
    intro i j hi hj h
    have := add_left_cancel h
    exact (ZMod.natCast_eq_natCast_iff' i j n).mp this |> fun h' => by
      rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h'
  set w : ℕ → V := fun i => g (a + (i : ZMod n) - 1) with hw
  have hw0 : w 0 = 0 := by
    apply hg
    rintro ⟨j, hj, hjj⟩
    have h1 : a + ((n - 1 : ℕ) : ZMod n) = a + (j : ZMod n) := by
      have hjj' : a - 1 = a + (j : ZMod n) := by simpa using hjj
      rw [← hjj']
      have : ((n - 1 : ℕ) : ZMod n) = -1 := by
        rw [Nat.cast_sub (NeZero.one_le), ZMod.natCast_self]; simp
      rw [this]; ring_nf
    have := hinj (n - 1) j (by have := NeZero.pos n; omega) (by omega) h1
    omega
  have hws : w (s + 1) = 0 := by
    apply hg
    rintro ⟨j, hj, hjj⟩
    have h1 : a + (s : ZMod n) = a + (j : ZMod n) := by
      have hjj' : a + ((s + 1 : ℕ) : ZMod n) - 1 = a + (j : ZMod n) := hjj
      rw [← hjj']; push_cast; ring_nf
    have := hinj s j (by omega) (by omega) h1
    omega
  have key := poincare_1d w (s + 1) (by omega) hw0 hws
  -- left side
  have hL : ∑ t, ‖g t‖ ^ 2 = ∑ i ∈ Finset.range (s + 1), ‖w i‖ ^ 2 := by
    rw [Finset.sum_range_succ', hw0, norm_zero]
    simp only [zero_pow two_ne_zero, add_zero]
    have h1 : ∑ i ∈ Finset.range s, ‖w (i + 1)‖ ^ 2 = ∑ i ∈ Finset.range s, ‖g (a + (i : ZMod n))‖ ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hw]; push_cast; congr 3; ring_nf
    rw [h1]
    rw [← Finset.sum_image (f := fun t => ‖g t‖ ^ 2) (g := fun i : ℕ => a + (i : ZMod n))
      (fun i hi j hj h => hinj i j (by have := Finset.mem_coe.mp hi; simp at this; omega)
        (by have := Finset.mem_coe.mp hj; simp at this; omega) h)]
    symm
    refine Finset.sum_subset (Finset.subset_univ _) fun t _ ht => ?_
    have : g t = 0 := hg t (fun ⟨j, hj, hjt⟩ => ht (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, hjt.symm⟩))
    rw [this, norm_zero]; simp
  -- right side
  have hR : ∑ j ∈ Finset.range (s + 1), ‖w (j + 1) - w j‖ ^ 2 ≤ ∑ t, ‖g (t + 1) - g t‖ ^ 2 := by
    have h1 : ∀ j ∈ Finset.range (s + 1), ‖w (j + 1) - w j‖ ^ 2 =
        ‖g ((a + (j : ZMod n) - 1) + 1) - g (a + (j : ZMod n) - 1)‖ ^ 2 := by
      intro j _
      simp only [hw]; push_cast; congr 3; ring_nf
    rw [Finset.sum_congr rfl h1]
    rw [← Finset.sum_image (f := fun t => ‖g (t + 1) - g t‖ ^ 2)
      (g := fun j : ℕ => a + (j : ZMod n) - 1)
      (fun i hi j hj h => hinj i j (by have := Finset.mem_coe.mp hi; simp at this; omega)
        (by have := Finset.mem_coe.mp hj; simp at this; omega) (sub_left_injective h))]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
  rw [hL]
  refine key.trans ?_
  have hc : 0 ≤ ((((s + 1 : ℕ) : ℝ) ^ 2 - 1) / 6) := by
    have : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos s
    nlinarith
  exact mul_le_mul_of_nonneg_left hR hc

end OneD

/-! ### The Dirichlet form on a box -/

section Box

variable {V : Type*} [SeminormedAddCommGroup V] {d n : ℕ} [NeZero n]

/-- Splitting a site of the torus into its `μ`-coordinate and the rest. -/
theorem split_add_single (μ : Fin d) (t : ZMod n) (r : {j // j ≠ μ} → ZMod n) :
    (Equiv.piSplitAt μ (fun _ => ZMod n)).symm (t, r) + Pi.single μ 1 =
      (Equiv.piSplitAt μ (fun _ => ZMod n)).symm (t + 1, r) := by
  funext i
  by_cases h : i = μ
  · subst h; simp [Equiv.piSplitAt]
  · simp [Equiv.piSplitAt, h]

/-- The constant `c_{D₀} = 4 (D₀ + 1)^{-2}` of Lemma III.3.3. -/
noncomputable def cDirichlet (D : ℕ) : ℝ := 4 / ((D : ℝ) + 1) ^ 2

/-- **Coercivity of the Dirichlet form on a box (`c_{D₀}`, Lemma III.3.3)**: if `f` vanishes outside a
box with all sides `≤ D` (`D + 1 ≤ n`) then
`c_D ∑_x ‖f x‖² ≤ ∑_x ∑_μ ‖f (x + e_μ) - f x‖²` (for `⟨f, -Δ f⟩`, `d ≥ 1`). -/
theorem dirichlet_box_coercive {D : ℕ} (hd : 0 < d) (a : Torus d n) (s : Fin d → ℕ)
    (hs : ∀ i, s i ≤ D) (hn : D + 1 ≤ n) (f : Torus d n → V) (hf : ∀ x, x ∉ box a s → f x = 0) :
    cDirichlet D * ∑ x, ‖f x‖ ^ 2 ≤ ∑ x, ∑ μ : Fin d, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 := by
  classical
  set μ : Fin d := ⟨0, hd⟩
  set e := Equiv.piSplitAt μ (fun _ => ZMod n)
  have hsplit : ∀ F : Torus d n → ℝ, ∑ x, F x = ∑ r, ∑ t : ZMod n, F (e.symm (t, r)) := by
    intro F
    rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type_right]
  have hline : ∀ r : {j // j ≠ μ} → ZMod n,
      ∑ t : ZMod n, ‖f (e.symm (t, r))‖ ^ 2 ≤
        ((((s μ + 1 : ℕ) : ℝ) ^ 2 - 1) / 6) *
          ∑ t : ZMod n, ‖f (e.symm (t + 1, r)) - f (e.symm (t, r))‖ ^ 2 := by
    intro r
    refine poincare_cycle (fun t => f (e.symm (t, r))) (a μ) (s μ) (by have := hs μ; omega) ?_
    intro t ht
    apply hf
    intro hx
    exact ht (by
      obtain ⟨j, hj, hjt⟩ := hx μ
      refine ⟨j, hj, ?_⟩
      simpa [e, Equiv.piSplitAt] using hjt)
  have hc : ((((s μ + 1 : ℕ) : ℝ) ^ 2 - 1) / 6) ≤ 1 / cDirichlet D := by
    unfold cDirichlet
    have h1 : ((s μ + 1 : ℕ) : ℝ) ≤ (D : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ (hs μ)
    have h2 : (1 : ℝ) ≤ ((s μ + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos _
    rw [one_div_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
    nlinarith
  have hbond : ∀ r : {j // j ≠ μ} → ZMod n, ∀ t : ZMod n,
      f (e.symm (t + 1, r)) - f (e.symm (t, r)) = f (e.symm (t, r) + Pi.single μ 1) - f (e.symm (t, r)) := by
    intro r t; rw [split_add_single]
  have hmain : ∑ x, ‖f x‖ ^ 2 ≤ (1 / cDirichlet D) * ∑ x, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 := by
    rw [hsplit (fun x => ‖f x‖ ^ 2),
      show (∑ x, ‖f (x + Pi.single μ 1) - f x‖ ^ 2) = ∑ r, ∑ t : ZMod n,
        ‖f (e.symm (t, r) + Pi.single μ 1) - f (e.symm (t, r))‖ ^ 2 from
        hsplit (fun x => ‖f (x + Pi.single μ 1) - f x‖ ^ 2), Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    refine (hline r).trans ?_
    have hnn : 0 ≤ ∑ t : ZMod n, ‖f (e.symm (t + 1, r)) - f (e.symm (t, r))‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => by positivity
    calc _ ≤ (1 / cDirichlet D) * ∑ t : ZMod n, ‖f (e.symm (t + 1, r)) - f (e.symm (t, r))‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hc hnn
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun t _ => by rw [hbond]
  have hcpos : 0 < cDirichlet D := by unfold cDirichlet; positivity
  have hle : ∑ x, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 ≤
      ∑ x, ∑ ν : Fin d, ‖f (x + Pi.single ν 1) - f x‖ ^ 2 :=
    Finset.sum_le_sum fun x _ =>
      Finset.single_le_sum (f := fun ν : Fin d => ‖f (x + Pi.single ν 1) - f x‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ μ)
  calc cDirichlet D * ∑ x, ‖f x‖ ^ 2 ≤ cDirichlet D * ((1 / cDirichlet D) * ∑ x, ‖f (x + Pi.single μ 1) - f x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmain hcpos.le
    _ = ∑ x, ‖f (x + Pi.single μ 1) - f x‖ ^ 2 := by field_simp
    _ ≤ _ := hle

/-- The same for the lattice Laplacian: `⟨φ, -Δ φ⟩ ≥ c_D ‖φ‖²` for real `φ` supported in a box. -/
theorem dirichlet_box_coercive_laplacian {D : ℕ} (hd : 0 < d) (a : Torus d n) (s : Fin d → ℕ)
    (hs : ∀ i, s i ≤ D) (hn : D + 1 ≤ n) (φ : Torus d n → ℝ) (hφ : ∀ x, x ∉ box a s → φ x = 0) :
    cDirichlet D * ∑ x, φ x ^ 2 ≤ φ ⬝ᵥ Balaban.latticeLaplacian d n 0 *ᵥ φ := by
  have h := dirichlet_box_coercive hd a s hs hn φ hφ
  rw [Balaban.latticeLaplacian_quadratic, zero_mul, add_zero]
  simpa only [Real.norm_eq_abs, sq_abs] using h

end Box

end Balaban.LargeField
