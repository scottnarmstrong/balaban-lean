module

public import Balaban.Correlations.TermKernel
public import Balaban.Correlations.Asymptotics
public import Balaban.Green.Lattice.Main
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# The sum of the infinite-volume kernels is the lattice Green's function (G4)

CORRELATIONS.md §3.4. Hypotheses (named after §2.1; they are supplied by the Green package):
* (G1) `hG1`: for `μ ∈ (0, 2]` the infinite-volume kernels `t_j^μ(x, y)` are the limits of the
  torus kernels `T_j^{ℓ,μ}` as `ℓ = L ^ (j+1) (m+1) → ∞`;
* (G2) `hG2`: decay of `t_j^0` (`KernelDecay`);
* (G3) `hG3`: `t_j^μ → t_j^0` as `μ ↓ 0`;
* (G5) `hG5`: the prolongation kernels are bounded by `C_P`, uniformly in `J, m` and `μ ∈ (0, 2]`.

Conclusion `sum_kernels_eq_latticeGreen` (G4): `∑_j t_j^0(x, y)` converges absolutely and equals
`latticeGreen d (x - y)`. The proof follows §3.4: the torus sum rule (`sum_rule_termKernel`) passes
to the limit `ℓ → ∞` (using `termKernel_nested`, so that the `j`-th kernel is the same for every
number of steps `> j`), then `μ ↓ 0`, then `J → ∞`; the limit solves `-ΔG = δ` and tends to `0`,
so equals `latticeGreen` by `latticeGreen_existsUnique`.
-/

@[expose] public section

open Filter Topology

namespace Balaban

variable {d L : ℕ} [NeZero L]

/-- Balls in `ℤ^d` are finite. -/
theorem finite_norm_le (R : ℝ) : {x : Fin d → ℤ | ‖x‖ ≤ R}.Finite := by
  have : {x : Fin d → ℤ | ‖x‖ ≤ R} ⊆
      Set.pi Set.univ (fun _ => Finset.Icc (-⌈R⌉) ⌈R⌉ : Fin d → Set ℤ) := by
    intro x hx i _
    have h1 : ‖x i‖ ≤ R := (norm_le_pi_norm x i).trans hx
    rw [Int.norm_eq_abs] at h1
    have h2 : |x i| ≤ ⌈R⌉ := by
      have : ((|x i| : ℤ) : ℝ) ≤ R := by simpa using h1
      exact Int.cast_le.mp (this.trans (Int.le_ceil R))
    simp only [Finset.coe_Icc, Set.mem_Icc]
    exact abs_le.mp h2
  exact (Set.Finite.pi (fun _ => (Finset.finite_toSet _))).subset this

theorem tendsto_norm_cofinite : Tendsto (fun x : Fin d → ℤ => ‖x‖) cofinite atTop := by
  rw [Filter.tendsto_atTop]
  intro R
  rw [Filter.eventually_cofinite]
  refine (finite_norm_le R).subset fun x hx => ?_
  exact (not_le.mp hx).le

/-- A function bounded by `B / (1 + ‖z‖)^(d-2)` tends to `0` at infinity. -/
theorem tendsto_cofinite_of_decay (hd : 3 ≤ d) {F : (Fin d → ℤ) → ℝ} {B : ℝ}
    (hF : ∀ z, |F z| ≤ B / (1 + ‖z‖) ^ (d - 2)) : Tendsto F cofinite (𝓝 0) := by
  have h1 : Tendsto (fun z : Fin d → ℤ => 1 + ‖z‖) cofinite atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_norm_cofinite
  have h2 : Tendsto (fun z : Fin d → ℤ => (1 + ‖z‖) ^ (d - 2)) cofinite atTop :=
    (tendsto_pow_atTop (by omega)).comp h1
  have h3 := tendsto_const_nhds (x := B) |>.div_atTop h2
  refine squeeze_zero_norm (fun z => ?_) h3
  rw [Real.norm_eq_abs]
  exact hF z

/-- The hypotheses (G1), (G2), (G3), (G5) of CORRELATIONS.md §2.1 on the Gaussian kernels of the
free flow `α = freeSeq d L a`: `t j μ x y` are the infinite-volume kernels `t_j^μ(x, y)` and
`t0 j x y` the kernels `t_j^0(x, y)` at `μ = 0`. -/
structure KernelHyp (d L : ℕ) [NeZero L] (a : ℝ) (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (C_G δ_G C_P : ℝ) : Prop where
  /-- (G1): `t_j^μ` is the limit of the torus kernels as the torus grows. -/
  g1 : ∀ (j : ℕ) (μ : ℝ), 0 < μ → μ ≤ 2 → ∀ x y,
    Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ (j + 1) j m x y) atTop
      (𝓝 (t j μ x y))
  /-- (G2) at `μ = 0`: exponential decay on the scale `L ^ j`. -/
  g2 : ∀ x y : Fin d → ℤ, KernelDecay d (L : ℝ) C_G δ_G ‖x - y‖ (fun j => t0 j x y)
  /-- (G3): the limit `μ ↓ 0`. -/
  g3 : ∀ (j : ℕ) x y, Tendsto (fun μ => t j μ x y) (𝓝[>] 0) (𝓝 (t0 j x y))
  /-- (G5): the prolongation kernels are bounded. -/
  g5 : ∀ (J m : ℕ) (μ : ℝ), 0 < μ → μ ≤ 2 → ∀ y u,
    |prolong (L := L) (m := m + 1) J (latticeLaplacian d (L ^ J * (m + 1)) μ) (freeSeq d L a) y u|
      ≤ C_P
  nonneg_G : 0 ≤ C_G
  pos_δ : 0 < δ_G

section Limits

variable {a : ℝ} {t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ}
  {t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ} {C_G δ_G C_P : ℝ}

/-- The `j`-th torus kernel on the `J`-step decomposition has the same limit `t_j^μ` for every
`J > j` (nested tori). -/
theorem KernelHyp.tendsto_termKernel (H : KernelHyp d L a t t0 C_G δ_G C_P) (ha : 0 < a)
    {μ : ℝ} (hμ : 0 < μ) (hμ2 : μ ≤ 2) {J j : ℕ} (hj : j < J) (x y : Fin d → ℤ) :
    Tendsto (fun m : ℕ => termKernel d L (freeSeq d L a) μ J j m x y) atTop (𝓝 (t j μ x y)) := by
  obtain ⟨n, rfl⟩ : ∃ n, J = n + 1 + j := ⟨J - j - 1, by omega⟩
  have hpos : 1 ≤ L ^ n := Nat.one_le_pow _ _ (Nat.pos_of_ne_zero (NeZero.ne L))
  have hm' : ∀ m : ℕ, (L ^ n * (m + 1) - 1) + 1 = L ^ n * (m + 1) := fun m => by
    have : 1 ≤ L ^ n * (m + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
    omega
  have hle : ∀ m : ℕ, m ≤ L ^ n * (m + 1) - 1 := fun m => by
    have : m + 1 ≤ L ^ n * (m + 1) := Nat.le_mul_of_pos_left _ hpos
    omega
  have hcomp := (H.g1 j μ hμ hμ2 x y).comp
    (tendsto_atTop_mono hle tendsto_id)
  refine hcomp.congr fun m => ?_
  simp only [Function.comp]
  exact (termKernel_nested hμ (fun i => freeSeq_pos ha i) n j m _ (hm' m) x y).symm

open Finset in
/-- The sum rule in infinite volume, for `∑_{j<J} t_j^μ` (the limit `ℓ → ∞` of
`sum_rule_termKernel`). -/
theorem KernelHyp.sum_rule_limit (H : KernelHyp d L a t t0 C_G δ_G C_P) (ha : 0 < a)
    {μ : ℝ} (hμ : 0 < μ) (hμ2 : μ ≤ 2) (J : ℕ) (x y : Fin d → ℤ) :
    |(∑ ν : Fin d, (2 * ∑ j ∈ range J, t j μ x y - ∑ j ∈ range J, t j μ (x + Pi.single ν 1) y -
          ∑ j ∈ range J, t j μ (x - Pi.single ν 1) y) + μ * ∑ j ∈ range J, t j μ x y) -
        (if x = y then 1 else 0)| ≤ C_P * (((L ^ J : ℕ) : ℝ) ^ d)⁻¹ := by
  have hS : ∀ z, Tendsto (fun m : ℕ => ∑ j ∈ range J, termKernel d L (freeSeq d L a) μ J j m z y)
      atTop (𝓝 (∑ j ∈ range J, t j μ z y)) := fun z =>
    tendsto_finsetSum _ fun j hj => H.tendsto_termKernel ha hμ hμ2 (Finset.mem_range.mp hj) z y
  have hE := (((tendsto_finsetSum (univ : Finset (Fin d)) fun ν _ =>
      (((hS x).const_mul 2).sub (hS (x + Pi.single ν 1))).sub (hS (x - Pi.single ν 1))).add
      ((hS x).const_mul μ)).sub (tendsto_const_nhds (x := (if x = y then (1 : ℝ) else 0))))
  have hev : ∀ᶠ m : ℕ in atTop,
      |(∑ ν : Fin d, (2 * ∑ j ∈ range J, termKernel d L (freeSeq d L a) μ J j m x y -
          ∑ j ∈ range J, termKernel d L (freeSeq d L a) μ J j m (x + Pi.single ν 1) y -
          ∑ j ∈ range J, termKernel d L (freeSeq d L a) μ J j m (x - Pi.single ν 1) y) +
        μ * ∑ j ∈ range J, termKernel d L (freeSeq d L a) μ J j m x y) -
        (if x = y then 1 else 0)| ≤ C_P * (((L ^ J : ℕ) : ℝ) ^ d)⁻¹ := by
    filter_upwards [eventually_torusPoint_eq_iff (L := L) J x y] with m hm
    have := sum_rule_termKernel (L := L) J m hμ (fun i => freeSeq_pos ha i)
      (H.g5 J m μ hμ hμ2) x y
    simpa only [hm] using this
  exact le_of_tendsto hE.abs hev

open Finset in
/-- The sum rule at `μ = 0`: for `s(z) = ∑_{j<J} t_j^0(z, y)`,
`|(-Δ s)(x) - δ_{xy}| ≤ C_P L^{-Jd}`. -/
theorem KernelHyp.sum_rule_zero (H : KernelHyp d L a t t0 C_G δ_G C_P) (ha : 0 < a) (J : ℕ)
    (x y : Fin d → ℤ) :
    |(∑ ν : Fin d, (2 * ∑ j ∈ range J, t0 j x y - ∑ j ∈ range J, t0 j (x + Pi.single ν 1) y -
          ∑ j ∈ range J, t0 j (x - Pi.single ν 1) y)) - (if x = y then 1 else 0)| ≤
      C_P * (((L ^ J : ℕ) : ℝ) ^ d)⁻¹ := by
  have hS : ∀ z, Tendsto (fun μ : ℝ => ∑ j ∈ range J, t j μ z y) (𝓝[>] 0)
      (𝓝 (∑ j ∈ range J, t0 j z y)) := fun z =>
    tendsto_finsetSum _ fun j _ => H.g3 j z y
  have hE := (((tendsto_finsetSum (univ : Finset (Fin d)) fun ν _ =>
      (((hS x).const_mul 2).sub (hS (x + Pi.single ν 1))).sub (hS (x - Pi.single ν 1))).add
      ((tendsto_id (α := ℝ)).mono_left nhdsWithin_le_nhds |>.mul (hS x))).sub
      (tendsto_const_nhds (x := (if x = y then (1 : ℝ) else 0))))
  have hev : ∀ᶠ μ : ℝ in 𝓝[>] 0,
      |(∑ ν : Fin d, (2 * ∑ j ∈ range J, t j μ x y - ∑ j ∈ range J, t j μ (x + Pi.single ν 1) y -
          ∑ j ∈ range J, t j μ (x - Pi.single ν 1) y) + id μ * ∑ j ∈ range J, t j μ x y) -
        (if x = y then 1 else 0)| ≤ C_P * (((L ^ J : ℕ) : ℝ) ^ d)⁻¹ := by
    filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 2 by norm_num)] with μ hμ
    exact H.sum_rule_limit ha hμ.1 hμ.2.le J x y
  have := le_of_tendsto hE.abs hev
  simpa using this

omit [NeZero L] in
theorem tendsto_inv_pow_nat_pow_zero (hL : 1 < L) (hd : d ≠ 0) (C : ℝ) :
    Tendsto (fun J : ℕ => C * (((L ^ J : ℕ) : ℝ) ^ d)⁻¹) atTop (𝓝 0) := by
  have h1 : Tendsto (fun J : ℕ => ((L : ℝ) ^ J)) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast hL)
  have h2 : Tendsto (fun J : ℕ => ((L : ℝ) ^ J) ^ d) atTop atTop :=
    (tendsto_pow_atTop hd).comp h1
  have h3 := (tendsto_inv_atTop_zero.comp h2).const_mul C
  simpa [Nat.cast_pow] using h3

open Finset in
/-- **(G4)**: given (G1), (G2), (G3), (G5), the series `∑_j t_j^0(x, y)` converges absolutely and
its sum is the lattice Green's function `G(x - y)`. -/
theorem KernelHyp.tsum_eq_latticeGreen (H : KernelHyp d L a t t0 C_G δ_G C_P) (ha : 0 < a)
    (hd : 3 ≤ d) (hL : 1 < L) (x y : Fin d → ℤ) :
    Summable (fun j => t0 j x y) ∧
      ∑' j, t0 j x y = LatticeGreen.latticeGreen d (x - y) := by
  obtain ⟨C', -, hC'⟩ := KernelDecay.tsum_abs_le (L := (L : ℝ)) (by exact_mod_cast hL) d hd
    H.pos_δ
  have hsum : ∀ x y, Summable (fun j => t0 j x y) := fun x y =>
    (hC' C_G ‖x - y‖ _ H.nonneg_G (norm_nonneg _) (H.g2 x y)).1
  have hbound : ∀ x y, |∑' j, t0 j x y| ≤ C_G * C' / (1 + ‖x - y‖) ^ (d - 2) := fun x y =>
    (hC' C_G ‖x - y‖ _ H.nonneg_G (norm_nonneg _) (H.g2 x y)).2
  refine ⟨hsum x y, ?_⟩
  -- the equation `-Δ g = δ`
  have heq : ∀ x y : Fin d → ℤ,
      ∑ ν : Fin d, (2 * ∑' j, t0 j x y - ∑' j, t0 j (x + Pi.single ν 1) y -
        ∑' j, t0 j (x - Pi.single ν 1) y) = if x = y then 1 else 0 := by
    intro x y
    have hpart : ∀ z, Tendsto (fun J : ℕ => ∑ j ∈ range J, t0 j z y) atTop
        (𝓝 (∑' j, t0 j z y)) := fun z => (hsum z y).hasSum.tendsto_sum_nat
    have hΦ := ((tendsto_finsetSum (univ : Finset (Fin d)) fun ν _ =>
      (((hpart x).const_mul 2).sub (hpart (x + Pi.single ν 1))).sub
        (hpart (x - Pi.single ν 1)))).sub
      (tendsto_const_nhds (x := (if x = y then (1 : ℝ) else 0)))
    have hzero : Tendsto (fun J : ℕ => (∑ ν : Fin d,
        (2 * ∑ j ∈ range J, t0 j x y - ∑ j ∈ range J, t0 j (x + Pi.single ν 1) y -
          ∑ j ∈ range J, t0 j (x - Pi.single ν 1) y)) - (if x = y then (1 : ℝ) else 0))
        atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun J => ?_) (tendsto_inv_pow_nat_pow_zero hL (by omega : d ≠ 0) C_P)
      rw [Real.norm_eq_abs]
      exact H.sum_rule_zero ha J x y
    have := tendsto_nhds_unique hΦ hzero
    linarith
  -- uniqueness of the lattice Green's function
  have hGy : (fun z : Fin d → ℤ => ∑' j, t0 j (z + y) y) = LatticeGreen.latticeGreen d := by
    refine (LatticeGreen.latticeGreen_existsUnique hd).unique ⟨?_, ?_⟩
      ⟨LatticeGreen.latticeGreen_equation hd, LatticeGreen.latticeGreen_tendsto_zero hd⟩
    · intro z
      have := heq (z + y) y
      have e1 : ∀ ν : Fin d, z + y + Pi.single ν 1 = z + Pi.single ν 1 + y := fun ν =>
        add_right_comm _ _ _
      have e2 : ∀ ν : Fin d, z + y - Pi.single ν 1 = z - Pi.single ν 1 + y := fun ν =>
        (sub_add_eq_add_sub z (Pi.single ν 1) y).symm
      simp only [e1, e2] at this
      simpa using this
    · refine tendsto_cofinite_of_decay hd (B := C_G * C') fun z => ?_
      simpa using hbound (z + y) y
  have := congrFun hGy (x - y)
  simpa using this

end Limits

end Balaban
