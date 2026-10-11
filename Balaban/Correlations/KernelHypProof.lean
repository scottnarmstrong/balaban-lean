module

public import Balaban.Correlations.KernelLimits
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The Gaussian kernel hypotheses hold (interface I-G)

`Balaban.kernelHyp_holds`: for `d ≥ 3`, `L ≥ 3` and `a` in the range of C-1* there are kernels
`t, t0` and constants with `Balaban.KernelHyp d L a t t0 C_G δ_G C_P`; `t_j^μ` is the limit of the
torus kernels (`tLim`) and `t_j^0` the limit `μ ↓ 0` (`t0Lim`), both from
`Balaban.Correlations.KernelLimits`.  This file proves the decay (G2):

* `term_bound_succ`: for `j ≥ 1`, `T_j = L^{-j(d-2)} K C_tr Kᵀ` (dictionary) is bounded on the torus
  by `B L^{-j(d-2)} e^{-(s/4) dist(block x, block y)}`, from the pointwise bound
  `Balaban.Green.oneScale_pointwise` for `K = a_j G Q*`, the Combes--Thomas bound
  `Balaban.Green.coarseGreen_decay` for `C_tr`, and the convolution `triple_sum_bound`;
* `tLim_decay_succ`, `tLim_decay_zero`: the same for the limits `t_j^μ` in terms of `|x - y| / L^j`;
* `kernelHyp_holds`, `kernelHyp_tsum_eq_latticeGreen`: assembly, and the unconditional (G4):
  `∑_j t_j^0(x, y) = latticeGreen d (x - y)`.

Mass range (step 2 of the brief, option (b)): `KernelHyp` was weakened in place
(`GreenIdentification.lean`) to the unit-lattice masses `μ L^{2(j+1)} ≤ 1` that the sum rule uses.
-/

@[expose] public section

namespace Balaban

open Matrix Filter Topology Balaban.Green

section TripleSum

variable {d m : ℕ} [NeZero m]

/-- Convolution of three exponentially decaying kernels on the torus. -/
theorem triple_sum_bound {s : ℝ} (hs : 0 < s) (b b' : Torus d m) :
    ∑ u' : Torus d m, ∑ u : Torus d m, Real.exp (-s * torusDist d m b u) *
        Real.exp (-s * torusDist d m u u') * Real.exp (-s * torusDist d m u' b') ≤
      ballConst d (s / 2) * ballConst d (s / 2 / 2) *
        Real.exp (-(s / 2 / 2) * torusDist d m b b') := by
  have hκ1 : 0 ≤ ballConst d (s / 2) := ballConst_nonneg (by positivity)
  have hκ2 : 0 ≤ ballConst d (s / 2 / 2) := ballConst_nonneg (by positivity)
  have step1 : ∀ u' : Torus d m, ∑ u : Torus d m, Real.exp (-s * torusDist d m b u) *
        Real.exp (-s * torusDist d m u u') * Real.exp (-s * torusDist d m u' b') ≤
      ballConst d (s / 2) * Real.exp (-(s / 2) * torusDist d m b u') *
        Real.exp (-(s / 2) * torusDist d m u' b') := by
    intro u'
    rw [← Finset.sum_mul]
    have h1 := sum_exp_conv_le hs b u'
    have h2 : Real.exp (-s * torusDist d m u' b') ≤ Real.exp (-(s / 2) * torusDist d m u' b') :=
      Real.exp_le_exp.2 (by
        have := torusDist_nonneg_gen (d := d) u' b'
        nlinarith)
    calc _ ≤ (ballConst d (s / 2) * Real.exp (-(s / 2) * torusDist d m b u')) *
          Real.exp (-s * torusDist d m u' b') :=
          mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc _ ≤ ∑ u' : Torus d m, ballConst d (s / 2) * Real.exp (-(s / 2) * torusDist d m b u') *
        Real.exp (-(s / 2) * torusDist d m u' b') := Finset.sum_le_sum fun u' _ => step1 u'
    _ = ballConst d (s / 2) * ∑ u' : Torus d m, Real.exp (-(s / 2) * torusDist d m b u') *
        Real.exp (-(s / 2) * torusDist d m u' b') := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun u' _ => by ring
    _ ≤ ballConst d (s / 2) * (ballConst d (s / 2 / 2) *
        Real.exp (-(s / 2 / 2) * torusDist d m b b')) :=
        mul_le_mul_of_nonneg_left (sum_exp_conv_le (by positivity) b b') hκ1
    _ = _ := by ring

end TripleSum

section TermBound

variable {d L : ℕ} [NeZero L]

/-- **Uniform torus bound for the terms `j ≥ 1`**: `T_j = L^{-j(d-2)} K C_tr Kᵀ` with the pointwise
kernel bound and the Combes--Thomas bound of `C_tr`. -/
theorem term_bound_succ (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ B s : ℝ, 0 ≤ B ∧ 0 < s ∧ ∀ {μ : ℝ}, 0 < μ → ∀ {j : ℕ}, 1 ≤ j →
      μ * ((L : ℝ) ^ j) ^ 2 ≤ 1 → ∀ (m : ℕ) (x y : Fin d → ℤ),
      |termKernel d L (freeSeq d L a) μ (j + 1) j m x y| ≤
        B * ((L : ℝ) ^ (j * (d - 2)))⁻¹ *
          Real.exp (-(s / 2 / 2) * torusDist d (L * (m + 1))
            (blockMap (L ^ j) (L * (m + 1)) (castTorus (L * (m + 1) * L ^ j) x))
            (blockMap (L ^ j) (L * (m + 1)) (castTorus (L * (m + 1) * L ^ j) y))) := by
  have hL1 : 1 < L := by omega
  have hd0 : 0 < d := by omega
  have hhalf := half_le_of_lo hL1 hlo
  have ha0 : 0 < a := by linarith
  obtain ⟨K₀, hK₀, hK⟩ := oneScale_pointwise (d := d) (L := L) hd hL
  set r : ℝ := blockDecayRate d with hr
  set ρ : ℝ := trRate d L with hρ
  set γ : ℝ := trGamma d L with hγ
  have hr0 : 0 < r := blockDecayRate_pos hd0
  have hρ0 : 0 < ρ := trRate_pos (L := L) hd0
  have hγ0 : 0 < γ := trGamma_pos (L := L) hd0
  set s : ℝ := min r ρ with hs
  have hs0 : 0 < s := lt_min hr0 hρ0
  have hsr : s ≤ r := min_le_left _ _
  have hsρ : s ≤ ρ := min_le_right _ _
  have hκ1 : 0 ≤ ballConst d (s / 2) := ballConst_nonneg (by positivity)
  have hκ2 : 0 ≤ ballConst d (s / 2 / 2) := ballConst_nonneg (by positivity)
  refine ⟨K₀ ^ 2 * (2 * γ⁻¹) * ballConst d (s / 2) * ballConst d (s / 2 / 2), s, by positivity,
    hs0, ?_⟩
  intro μ hμ j hj hμ1 m x y
  obtain ⟨haJ1, haJ2⟩ := aScale_mem hL1 hlo hhi (J := j) hj
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  rw [termKernel_eq_termDirect ha0 hμ,
    termDirect_freeSeq_unit (d := d) (L := L) (ℓ := L * (m + 1) * L ^ j) (ℓ₁ := L * (m + 1))
      (m₂ := m + 1) (by omega) hL1 ha0 hμ hj (mul_comm _ _) rfl (by linarith) haJ1 hhalf]
  set ν : ℝ := μ * ((L ^ j : ℕ) : ℝ) ^ 2 with hν
  have hν0 : 0 ≤ ν := by positivity
  have hν1 : ν ≤ 1 := by simpa [hν, Nat.cast_pow] using hμ1
  set Kmat := fineToBlockKernel d (L * (m + 1) * L ^ j) (L ^ j) (L * (m + 1)) ν (aScale L a j)
    with hKmat
  set Cinv := (coarseOperator d (L * (m + 1) * L ^ j) (L ^ j) (L * (m + 1)) L (m + 1) ν
    (aScale L a j) a)⁻¹ with hCinv
  have hKb : ∀ (X : Torus d (L * (m + 1) * L ^ j)) (u : Torus d (L * (m + 1))),
      |Kmat X u| ≤ K₀ * Real.exp (-s * torusDist d (L * (m + 1))
        (blockMap (L ^ j) (L * (m + 1)) X) u) := by
    intro X u
    have h := hK (k := j) (N₀ := L * (m + 1)) (ℓ := L * (m + 1) * L ^ j) hj rfl hν0 hν1 haJ1 haJ2 u X
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hK₀)
    have := torusDist_nonneg_gen (d := d) (blockMap (L ^ j) (L * (m + 1)) X) u
    nlinarith
  have hCb : ∀ u u' : Torus d (L * (m + 1)),
      |Cinv u u'| ≤ 2 * γ⁻¹ * Real.exp (-s * torusDist d (L * (m + 1)) u u') := by
    intro u u'
    have h := coarseGreen_decay (L := L) (N₀ := L * (m + 1)) (M := m + 1) (k := j) hd0 hj rfl
      hν0 (by linarith) haJ1 haJ2 hhalf (by linarith) u u'
    refine h.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) (by positivity))
    have := torusDist_nonneg_gen (d := d) u u'
    nlinarith
  set X := castTorus (L * (m + 1) * L ^ j) x with hX
  set Y := castTorus (L * (m + 1) * L ^ j) y with hY
  set bX := blockMap (L ^ j) (L * (m + 1)) X with hbX
  set bY := blockMap (L ^ j) (L * (m + 1)) Y with hbY
  rw [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ ((L : ℝ) ^ (j * (d - 2)))⁻¹)]
  have hsum : |(Kmat * Cinv * Kmatᵀ) X Y| ≤ K₀ ^ 2 * (2 * γ⁻¹) *
      (ballConst d (s / 2) * ballConst d (s / 2 / 2) *
        Real.exp (-(s / 2 / 2) * torusDist d (L * (m + 1)) bX bY)) := by
    rw [Matrix.mul_apply]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ u', |(Kmat * Cinv) X u' * Kmatᵀ u' Y|
        ≤ ∑ u' : Torus d (L * (m + 1)), ∑ u : Torus d (L * (m + 1)),
            (K₀ ^ 2 * (2 * γ⁻¹)) * (Real.exp (-s * torusDist d (L * (m + 1)) bX u) *
              Real.exp (-s * torusDist d (L * (m + 1)) u u') *
              Real.exp (-s * torusDist d (L * (m + 1)) u' bY)) := by
          refine Finset.sum_le_sum fun u' _ => ?_
          rw [abs_mul, Matrix.mul_apply, Matrix.transpose_apply]
          refine (mul_le_mul_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _)) (abs_nonneg _)).trans ?_
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun u _ => ?_
          rw [abs_mul]
          have h1 := hKb X u
          have h2 := hCb u u'
          have h3 := hKb Y u'
          rw [torusDist_comm_gen (d := d) bY u'] at h3
          calc |Kmat X u| * |Cinv u u'| * |Kmat Y u'|
              ≤ (K₀ * Real.exp (-s * torusDist d (L * (m + 1)) bX u)) *
                (2 * γ⁻¹ * Real.exp (-s * torusDist d (L * (m + 1)) u u')) *
                (K₀ * Real.exp (-s * torusDist d (L * (m + 1)) u' bY)) := by
                gcongr
            _ = _ := by ring
      _ = (K₀ ^ 2 * (2 * γ⁻¹)) * ∑ u' : Torus d (L * (m + 1)), ∑ u : Torus d (L * (m + 1)),
            Real.exp (-s * torusDist d (L * (m + 1)) bX u) *
              Real.exp (-s * torusDist d (L * (m + 1)) u u') *
              Real.exp (-s * torusDist d (L * (m + 1)) u' bY) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun u' _ => ?_
          rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (triple_sum_bound hs0 bX bY) (by positivity)
  calc ((L : ℝ) ^ (j * (d - 2)))⁻¹ * |(Kmat * Cinv * Kmatᵀ) X Y|
      ≤ ((L : ℝ) ^ (j * (d - 2)))⁻¹ * (K₀ ^ 2 * (2 * γ⁻¹) *
      (ballConst d (s / 2) * ballConst d (s / 2 / 2) *
        Real.exp (-(s / 2 / 2) * torusDist d (L * (m + 1)) bX bY))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by ring

end TermBound

section Blocks

variable {d : ℕ}

/-- The block index of the site `x` for blocks of side `N`. -/
def blkInt (N : ℕ) (x : Fin d → ℤ) : Fin d → ℤ := fun i => x i / (N : ℤ)

theorem norm_le_blkInt {N : ℕ} (hN : 0 < N) (x y : Fin d → ℤ) :
    ‖x - y‖ ≤ N * (l1IntDist d (blkInt N x) (blkInt N y) + 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hNi : (0 : ℤ) < N := by exact_mod_cast hN
  have hnn : 0 ≤ (N : ℝ) * (l1IntDist d (blkInt N x) (blkInt N y) + 1) := by
    have : 0 ≤ l1IntDist d (blkInt N x) (blkInt N y) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    positivity
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
  have h1 := Int.mul_ediv_add_emod (x i) N
  have h2 := Int.mul_ediv_add_emod (y i) N
  have e1 := Int.emod_nonneg (x i) hNi.ne'
  have e2 := Int.emod_lt_of_pos (x i) hNi
  have e3 := Int.emod_nonneg (y i) hNi.ne'
  have e4 := Int.emod_lt_of_pos (y i) hNi
  have hterm : ((blkInt N x i - blkInt N y i).natAbs : ℝ) ≤ l1IntDist d (blkInt N x) (blkInt N y) := by
    unfold l1IntDist
    exact Finset.single_le_sum (f := fun j => (((blkInt N x) j - (blkInt N y) j).natAbs : ℝ))
      (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)
  have hz : x i - y i = N * (blkInt N x i - blkInt N y i) + (x i % N - y i % N) := by
    unfold blkInt; linarith
  have hab : ((x i - y i).natAbs : ℤ) ≤ N * ((blkInt N x i - blkInt N y i).natAbs : ℤ) + N := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, hz]
    calc |(N : ℤ) * (blkInt N x i - blkInt N y i) + (x i % N - y i % N)|
        ≤ |(N : ℤ) * (blkInt N x i - blkInt N y i)| + |x i % N - y i % N| := abs_add_le _ _
      _ ≤ N * |blkInt N x i - blkInt N y i| + N := by
          rw [abs_mul, abs_of_pos hNi]
          have : |x i % N - y i % N| ≤ N := by rw [abs_le]; constructor <;> linarith
          linarith
  have hab' : ((x i - y i).natAbs : ℝ) ≤ N * ((blkInt N x i - blkInt N y i).natAbs : ℝ) + N := by
    exact_mod_cast hab
  have hn : ‖x i - y i‖ = ((x i - y i).natAbs : ℝ) := by rw [Int.norm_eq_abs]; simp
  rw [Pi.sub_apply, hn]
  nlinarith [mul_le_mul_of_nonneg_left hterm hNr.le]

theorem eventually_block_dist {L : ℕ} [NeZero L] {j : ℕ} (x y : Fin d → ℤ) :
    ∀ᶠ m : ℕ in atTop,
      torusDist d (L * (m + 1))
        (blockMap (L ^ j) (L * (m + 1)) (castTorus (L * (m + 1) * L ^ j) x))
        (blockMap (L ^ j) (L * (m + 1)) (castTorus (L * (m + 1) * L ^ j) y)) =
      l1IntDist d (blkInt (L ^ j) x) (blkInt (L ^ j) y) := by
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : ∀ᶠ m : ℕ in atTop, ∀ i, 2 * ((blkInt (L ^ j) x - blkInt (L ^ j) y) i).natAbs <
      L * (m + 1) := by
    rw [Filter.eventually_all]
    intro i
    have : Tendsto (fun m : ℕ => L * (m + 1)) atTop atTop :=
      tendsto_atTop_mono (fun m => (Nat.le_succ m).trans (Nat.le_mul_of_pos_left _ hL))
        tendsto_id
    exact this.eventually_gt_atTop _
  filter_upwards [h1] with m hm
  rw [blockMap_castTorus_div (mul_comm _ _) hN x, blockMap_castTorus_div (mul_comm _ _) hN y]
  exact torusDist_castTorus (blkInt (L ^ j) x) (blkInt (L ^ j) y) hm

end Blocks

section DecaySucc

variable {d L : ℕ} [NeZero L]

/-- **Sharp decay of `t_j^μ`, `j ≥ 1`.** -/
theorem tLim_decay_succ (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ {μ : ℝ}, 0 < μ → ∀ {j : ℕ}, 1 ≤ j →
      μ * ((L : ℝ) ^ j) ^ 2 ≤ 1 → ∀ x y : Fin d → ℤ,
      |tLim d L a μ j x y| ≤
        C * ((L : ℝ) ^ (j * (d - 2)))⁻¹ * Real.exp (-(δ * ‖x - y‖ / (L : ℝ) ^ j)) := by
  have hL1 : 1 < L := by omega
  obtain ⟨B, s, hB, hs, h⟩ := term_bound_succ hd hL hlo hhi
  have hδ : 0 < s / 2 / 2 := by positivity
  refine ⟨B * Real.exp (s / 2 / 2), s / 2 / 2, by positivity, hδ, ?_⟩
  intro μ hμ j hj hμ1 x y
  have hN : 0 < L ^ j := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hLp : (0 : ℝ) < (L : ℝ) ^ j := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hT := tendsto_tLim hd hL1 hlo hhi hμ j x y
  refine le_of_tendsto hT.abs ?_
  filter_upwards [eventually_block_dist (L := L) (j := j) x y] with m hm
  refine (h hμ hj hμ1 m x y).trans ?_
  rw [hm]
  have hnorm := norm_le_blkInt hN x y
  push_cast at hnorm
  set l := l1IntDist d (blkInt (L ^ j) x) (blkInt (L ^ j) y) with hl
  have hexp : Real.exp (-(s / 2 / 2) * l) ≤
      Real.exp (s / 2 / 2) * Real.exp (-(s / 2 / 2 * ‖x - y‖ / (L : ℝ) ^ j)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.2
    have h1 : ‖x - y‖ / (L : ℝ) ^ j ≤ l + 1 := by
      rw [div_le_iff₀ hLp]; nlinarith
    have : s / 2 / 2 * (‖x - y‖ / (L : ℝ) ^ j) ≤ s / 2 / 2 * (l + 1) :=
      mul_le_mul_of_nonneg_left h1 hδ.le
    have e : s / 2 / 2 * ‖x - y‖ / (L : ℝ) ^ j = s / 2 / 2 * (‖x - y‖ / (L : ℝ) ^ j) := by ring
    rw [e]; nlinarith
  have hLinv : 0 ≤ ((L : ℝ) ^ (j * (d - 2)))⁻¹ := by positivity
  calc B * ((L : ℝ) ^ (j * (d - 2)))⁻¹ * Real.exp (-(s / 2 / 2) * l)
      ≤ B * ((L : ℝ) ^ (j * (d - 2)))⁻¹ * (Real.exp (s / 2 / 2) *
          Real.exp (-(s / 2 / 2 * ‖x - y‖ / (L : ℝ) ^ j))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = _ := by ring

end DecaySucc

section DecayZero

variable {d L : ℕ} [NeZero L]

theorem gent_decay (hd : 0 < d) (k : ℕ) :
    ∃ c ρ : ℝ, 0 ≤ c ∧ 0 < ρ ∧ ∀ {ℓ N M : ℕ} [NeZero ℓ] [NeZero M], N = L ^ k → ℓ = M * L ^ k →
      ∀ {ν a : ℝ}, 0 ≤ ν → ν ≤ 1 → 1 / 2 ≤ a → a ≤ 2 → ∀ x y : Fin d → ℤ,
      (∀ i, 2 * (x i - y i).natAbs < ℓ) →
      |Gent d ℓ N M ν a x y| ≤ c * Real.exp (-ρ * l1IntDist d x y) := by
  obtain ⟨c, ρ, hc, hρ, h⟩ := fineGreen_decay (L := L) hd k
  refine ⟨c, ρ, hc, hρ, ?_⟩
  intro ℓ N M _ _ hN hℓ ν a h1 h2 h3 h4 x y hxy
  subst hN hℓ
  unfold Gent
  rw [← torusDist_castTorus x y hxy]
  exact h h1 h2 h3 h4 _ _

theorem norm_le_l1IntDist (x y : Fin d → ℤ) : ‖x - y‖ ≤ l1IntDist d x y := by
  have hnn : 0 ≤ l1IntDist d x y := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun i => ?_
  have hn : ‖(x - y) i‖ = (((x i - y i).natAbs : ℕ) : ℝ) := by
    rw [Pi.sub_apply, Int.norm_eq_abs]; simp
  rw [hn]
  unfold l1IntDist
  exact Finset.single_le_sum (f := fun j => (((x j - y j).natAbs : ℕ) : ℝ))
    (fun _ _ => Nat.cast_nonneg _) (Finset.mem_univ i)

/-- Decay of `t_0^μ` (crude constants suffice: `L` is fixed). -/
theorem tLim_decay_zero (hd : 3 ≤ d) (hL : 1 < L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧ ∀ {μ : ℝ}, 0 < μ → μ * (L : ℝ) ^ 2 ≤ 1 → ∀ x y : Fin d → ℤ,
      |tLim d L a μ 0 x y| ≤ C * Real.exp (-(δ * ‖x - y‖)) := by
  have hd0 : 0 < d := by omega
  have hhalf := half_le_of_lo hL hlo
  have ha0 : 0 < a := by linarith
  obtain ⟨c, ρ, hc, hρ, h⟩ := gent_decay (L := L) hd0 1
  refine ⟨(L : ℝ) ^ 2 * c, ρ, by positivity, hρ, ?_⟩
  intro μ hμ hμ1 x y
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hT := tendsto_tLim hd hL hlo hhi hμ 0 x y
  refine le_of_tendsto hT.abs ?_
  have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : ∀ᶠ m : ℕ in atTop, ∀ i, 2 * (x i - y i).natAbs < L * (m + 1) := by
    rw [Filter.eventually_all]
    intro i
    have : Tendsto (fun m : ℕ => L * (m + 1)) atTop atTop :=
      tendsto_atTop_mono (fun m => (Nat.le_succ m).trans (Nat.le_mul_of_pos_left _ hL1))
        tendsto_id
    exact this.eventually_gt_atTop _
  filter_upwards [h1] with m hm
  rw [termKernel_zero (by omega) hL ha0 hμ, abs_mul, abs_of_nonneg (by positivity :
    (0 : ℝ) ≤ (L : ℝ) ^ 2)]
  have hb := h (ℓ := L * (m + 1)) (N := L) (M := m + 1) (by simp) (by ring)
    (ν := μ * (L : ℝ) ^ 2) (a := a) (by positivity) hμ1 hhalf hhi x y hm
  have hn := norm_le_l1IntDist x y
  have he : Real.exp (-ρ * l1IntDist d x y) ≤ Real.exp (-(ρ * ‖x - y‖)) :=
    Real.exp_le_exp.2 (by nlinarith)
  calc (L : ℝ) ^ 2 * |Gent d (L * (m + 1)) L (m + 1) (μ * (L : ℝ) ^ 2) a x y|
      ≤ (L : ℝ) ^ 2 * (c * Real.exp (-ρ * l1IntDist d x y)) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ ≤ (L : ℝ) ^ 2 * (c * Real.exp (-(ρ * ‖x - y‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he hc) (by positivity)
    _ = _ := by ring

end DecayZero

section Main

variable {d L : ℕ} [NeZero L]

/-- **The kernel hypotheses hold** (interface I-G, (G1)--(G3), (G5)).  For `d ≥ 3`, `L ≥ 3` and
`a` with `a (1 - L^{-2}) ≥ 1/2` and `a ≤ 2` (so that `a_j ∈ [1/2, 2]` for all `j ≥ 1`; the range
of C-1* is `a ∈ (1/(2(1 - L^{-2})), 3/2)`) there are kernels `t, t0` and constants such that
`KernelHyp d L a t t0 C_G δ_G C_P` holds. -/
theorem kernelHyp_holds (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
      (C_G δ_G C_P : ℝ), KernelHyp d L a t t0 C_G δ_G C_P := by
  have hL1 : 1 < L := by omega
  have hLp : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hx : (1 : ℝ) < L := by exact_mod_cast hL1
  obtain ⟨C₀, δ₀, hC₀, hδ₀, h₀⟩ := tLim_decay_zero hd hL1 hlo hhi
  obtain ⟨C₁, δ₁, hC₁, hδ₁, h₁⟩ := tLim_decay_succ hd hL hlo hhi
  obtain ⟨C_P, hCP, hP⟩ := prolong_bound hd hL hlo hhi
  refine ⟨fun j μ x y => tLim d L a μ j x y, fun j x y => t0Lim d L a j x y, max C₀ C₁,
    min δ₀ δ₁, C_P, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j μ hμ hμ1 x y
    exact tendsto_tLim hd hL1 hlo hhi hμ j x y
  · intro x y j
    have hLj : (0 : ℝ) < (L : ℝ) ^ (2 * (j + 1)) := by positivity
    have hev : ∀ᶠ μ : ℝ in 𝓝[>] 0, |tLim d L a μ j x y| ≤
        max C₀ C₁ * ((L : ℝ) ^ (j * (d - 2)))⁻¹ *
          Real.exp (-(min δ₀ δ₁ * ‖x - y‖ / (L : ℝ) ^ j)) := by
      filter_upwards [Ioo_mem_nhdsGT (inv_pos.2 hLj)] with μ hμ
      have hμ1 : μ * (L : ℝ) ^ (2 * (j + 1)) ≤ 1 := by
        have := mul_lt_mul_of_pos_right hμ.2 hLj
        rw [inv_mul_cancel₀ hLj.ne'] at this
        exact this.le
      have hLpj : (0 : ℝ) < (L : ℝ) ^ j := by positivity
      have hnorm : 0 ≤ ‖x - y‖ := norm_nonneg _
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · have h2 : μ * (L : ℝ) ^ 2 ≤ 1 := by simpa using hμ1
        refine (h₀ hμ.1 h2 x y).trans ?_
        simp only [zero_mul, pow_zero, inv_one, mul_one, div_one]
        exact mul_le_mul (le_max_left _ _) (Real.exp_le_exp.2 (by nlinarith [min_le_left δ₀ δ₁]))
          (Real.exp_pos _).le (by positivity)
      · have hmj : μ * ((L : ℝ) ^ j) ^ 2 ≤ 1 := by
          refine le_trans (mul_le_mul_of_nonneg_left ?_ hμ.1.le) hμ1
          rw [← pow_mul, mul_comm j 2]
          exact pow_le_pow_right₀ hx.le (by omega)
        refine (h₁ hμ.1 hj hmj x y).trans ?_
        have hinv : 0 ≤ ((L : ℝ) ^ (j * (d - 2)))⁻¹ := by positivity
        have e1 : Real.exp (-(δ₁ * ‖x - y‖ / (L : ℝ) ^ j)) ≤
            Real.exp (-(min δ₀ δ₁ * ‖x - y‖ / (L : ℝ) ^ j)) := by
          apply Real.exp_le_exp.2
          have : min δ₀ δ₁ * ‖x - y‖ / (L : ℝ) ^ j ≤ δ₁ * ‖x - y‖ / (L : ℝ) ^ j := by
            apply div_le_div_of_nonneg_right _ hLpj.le
            exact mul_le_mul_of_nonneg_right (min_le_right _ _) hnorm
          linarith
        exact mul_le_mul (mul_le_mul_of_nonneg_right (le_max_right _ _) hinv) e1
          (Real.exp_pos _).le (by positivity)
    exact le_of_tendsto (tendsto_t0Lim hd hL1 hlo hhi j x y).abs hev
  · intro j x y
    exact tendsto_t0Lim hd hL1 hlo hhi j x y
  · intro J m μ hμ hJ y u
    exact hP J m hμ hJ y u
  · exact (hC₀.trans (le_max_left _ _))
  · exact lt_min hδ₀ hδ₁

/-- **(G4) unconditionally**: with the kernels of `kernelHyp_holds`, `∑_j t_j^0(x, y)` converges
absolutely and equals Root-C's lattice Green's function `G(x - y)`. -/
theorem kernelHyp_tsum_eq_latticeGreen (hd : 3 ≤ d) (hL : 3 ≤ L) {a : ℝ}
    (hlo : 1 ≤ 2 * a * (1 - ((L : ℝ) ^ 2)⁻¹)) (hhi : a ≤ 2) :
    ∃ (t : ℕ → ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (t0 : ℕ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
      (C_G δ_G C_P : ℝ), KernelHyp d L a t t0 C_G δ_G C_P ∧ ∀ x y : Fin d → ℤ,
        Summable (fun j => t0 j x y) ∧
          ∑' j, t0 j x y = LatticeGreen.latticeGreen d (x - y) := by
  obtain ⟨t, t0, C_G, δ_G, C_P, H⟩ := kernelHyp_holds hd hL hlo hhi
  refine ⟨t, t0, C_G, δ_G, C_P, H, fun x y => ?_⟩
  have hx : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have ha : 0 < a := by linarith [half_le_of_lo (by omega : 1 < L) hlo]
  exact H.tsum_eq_latticeGreen ha hd (by omega) x y

end Main

end Balaban
