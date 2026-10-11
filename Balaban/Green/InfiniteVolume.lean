/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.MassLipschitz
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# G-5(c): infinite-volume limits

Tori of growing side have uniformly bounded, uniformly decaying kernels
(`unconstrainedUnitOperator_decay`, `coarseGreen_decay`, and the Lipschitz bounds of
`Balaban.Green.MassLipschitz`).  Compactness of the product of intervals (a countable index set)
gives a subsequence of tori along which the kernels converge entrywise, simultaneously for all
`ν ∈ [0, 2]` (rational `ν` by compactness, the others by the uniform Lipschitz bound), and the
limits satisfy the bounds of (a) and (b) with the `ℓ¹` distance of `ℤ^d`
(`Balaban.Green.infiniteVolume_limits`).  Sites of `ℤ^d` are embedded in the tori by the coordinatewise
cast (`Balaban.Green.castTorus`); the torus distance equals the `ℓ¹` distance once the torus is
large (`Balaban.Green.torusDist_castTorus`).

What is *not* proved: that the limit does not depend on the subsequence (uniqueness of the
infinite-volume Green's function).  By Roland's answer (`review/ROLAND_ANSWERS.md`, batch 2)
limits along tori suffice.
-/

@[expose] public section

namespace Balaban.Green

open Filter Topology

/-! ### A compactness lemma -/

theorem exists_rat_Icc_near {ν δ : ℝ} (hν : ν ∈ Set.Icc (0 : ℝ) 2) (hδ : 0 < δ) :
    ∃ q : ℚ, (q : ℝ) ∈ Set.Icc (0 : ℝ) 2 ∧ |ν - q| < δ := by
  rcases eq_or_lt_of_le hν.1 with h0 | hpos
  · refine ⟨0, by norm_num, ?_⟩
    rw [← h0]; simpa using hδ
  · obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show max 0 (ν - δ) < ν from
      max_lt hpos (by linarith))
    have hq0 : 0 < (q : ℝ) := lt_of_le_of_lt (le_max_left _ _) hq1
    have hq3 : ν - δ < q := lt_of_le_of_lt (le_max_right _ _) hq1
    refine ⟨q, ⟨hq0.le, by linarith [hν.2]⟩, ?_⟩
    rw [abs_lt]; constructor <;> linarith

/-- **Diagonal extraction with a common subsequence for all masses.**  Let `f n i ν` be real
numbers, `i` in a countable set, `ν ∈ [0, 2]`, uniformly bounded and uniformly Lipschitz in `ν`.
Then along a common subsequence `f n i ν` converges for every `i` and every `ν ∈ [0, 2]`. -/
theorem exists_subseq_tendsto {ι : Type*} [Countable ι] (f : ℕ → ι → ℝ → ℝ) (B Λ : ι → ℝ)
    (hB : ∀ n i ν, ν ∈ Set.Icc (0 : ℝ) 2 → |f n i ν| ≤ B i)
    (hΛ : ∀ n i ν ν', ν ∈ Set.Icc (0 : ℝ) 2 → ν' ∈ Set.Icc (0 : ℝ) 2 →
      |f n i ν - f n i ν'| ≤ Λ i * |ν - ν'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ i, ∀ ν ∈ Set.Icc (0 : ℝ) 2,
      ∃ l, Tendsto (fun n => f (φ n) i ν) atTop (𝓝 l) := by
  classical
  let J := ι × {q : ℚ // (q : ℝ) ∈ Set.Icc (0 : ℝ) 2}
  let x : ℕ → (J → ℝ) := fun n j => f n j.1 (j.2.1 : ℝ)
  let s : Set (J → ℝ) := Set.pi Set.univ fun j => Set.Icc (-B j.1) (B j.1)
  have hs : IsCompact s := isCompact_univ_pi fun j => isCompact_Icc
  have hx : ∀ n, x n ∈ s := by
    intro n j _
    exact abs_le.1 (hB n j.1 _ j.2.2)
  obtain ⟨a, -, φ, hφ, hlim⟩ := hs.tendsto_subseq hx
  have hq : ∀ (i : ι) (q : {q : ℚ // (q : ℝ) ∈ Set.Icc (0 : ℝ) 2}),
      Tendsto (fun n => f (φ n) i (q.1 : ℝ)) atTop (𝓝 (a (i, q))) := fun i q =>
    (tendsto_pi_nhds.1 hlim) (i, q)
  refine ⟨φ, hφ, fun i ν hν => ?_⟩
  have hcau : CauchySeq (fun n => f (φ n) i ν) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨q, hq2, hqν⟩ := exists_rat_Icc_near hν (show 0 < ε / (4 * (|Λ i| + 1)) by positivity)
    have hΛ0 : 0 ≤ |Λ i| := abs_nonneg _
    have hclose : ∀ n, |f (φ n) i ν - f (φ n) i q| < ε / 4 := by
      intro n
      calc |f (φ n) i ν - f (φ n) i q| ≤ Λ i * |ν - q| := hΛ _ i ν q hν hq2
        _ ≤ |Λ i| * |ν - q| := mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
        _ ≤ |Λ i| * (ε / (4 * (|Λ i| + 1))) :=
          mul_le_mul_of_nonneg_left hqν.le hΛ0
        _ < ε / 4 := by
          rw [mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
    have hconv := (Metric.tendsto_atTop.1 (hq i ⟨q, hq2⟩)) (ε / 4) (by positivity)
    obtain ⟨N, hN⟩ := hconv
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm
    have h2 := hN n hn
    rw [Real.dist_eq] at h1 h2 ⊢
    have h3 := hclose m
    have h4 := hclose n
    rw [abs_lt] at h1 h2 h3 h4 ⊢
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2]
  exact cauchySeq_tendsto_of_complete hcau

/-! ### Sites of `ℤ^d` in the tori -/

/-- The coordinatewise cast `ℤ^d → (ℤ/mℤ)^d`. -/
def castTorus {d : ℕ} (m : ℕ) (x : Fin d → ℤ) : Torus d m := fun i => ((x i : ℤ) : ZMod m)

theorem cycRep_intCast_of_small {m : ℕ} [NeZero m] (z : ℤ) (hz : 2 * z.natAbs < m) :
    cycRep (z : ZMod m) = z := by
  set c := cycRep (z : ZMod m) with hcdef
  have hc : ((c : ℤ) : ZMod m) = z := cast_cycRep _
  have hbound : 2 * c.natAbs ≤ m := by
    have hv := ZMod.val_lt (z : ZMod m)
    rw [hcdef]
    unfold cycRep
    split_ifs with h
    · rw [Int.natAbs_natCast]; omega
    · have : ((((z : ZMod m).val : ℤ) - m).natAbs) = m - (z : ZMod m).val := by omega
      rw [this]; omega
  have hdvd : (m : ℤ) ∣ c - z := (ZMod.intCast_eq_intCast_iff_dvd_sub z c m).1 hc.symm
  have hlt : |c - z| < m := by
    rw [Int.abs_eq_natAbs]
    have := Int.natAbs_sub_le c z
    exact_mod_cast (by omega : (c - z).natAbs < m)
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  linarith

theorem torusDist_castTorus {d m : ℕ} [NeZero m] (x y : Fin d → ℤ)
    (h : ∀ i, 2 * (x i - y i).natAbs < m) :
    torusDist d m (castTorus m x) (castTorus m y) = l1IntDist d x y := by
  unfold torusDist l1IntDist
  refine Finset.sum_congr rfl fun i _ => ?_
  have : castTorus m x i - castTorus m y i = (((x i - y i : ℤ)) : ZMod m) := by
    simp [castTorus]
  rw [this, cycRep_intCast_of_small _ (h i)]

/-! ### Blocks of `ℤ^d` and their images in the tori -/

/-- The block of `ℤ^d` with index `y`, for blocks of side `N`. -/
def intFibre {d : ℕ} (N : ℕ) (y : Fin d → ℤ) : Finset (Fin d → ℤ) :=
  Fintype.piFinset fun i => Finset.Ico ((N : ℤ) * y i) ((N : ℤ) * y i + N)

theorem mem_intFibre {d N : ℕ} {x y : Fin d → ℤ} :
    x ∈ intFibre N y ↔ ∀ i, (N : ℤ) * y i ≤ x i ∧ x i < (N : ℤ) * y i + N := by
  simp [intFibre, Fintype.mem_piFinset]

/-- The block of `ℤ^d` is mapped by the cast into the corresponding torus block. -/
theorem blockMap_castTorus_of_mem {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m)
    (hN : 0 < N) {x y : Fin d → ℤ} (hx : x ∈ intFibre N y) :
    blockMap N m (castTorus ℓ x) = castTorus m y := by
  funext i
  rw [blockMap_apply]
  obtain ⟨h1, h2⟩ := mem_intFibre.1 hx i
  set v := ((x i : ℤ) : ZMod ℓ).val with hv
  have hvz : (v : ℤ) = x i % ℓ := ZMod.val_intCast (x i)
  have hN0 : (N : ℤ) ≠ 0 := by exact_mod_cast hN.ne'
  have hℓz : (ℓ : ℤ) = N * m := by exact_mod_cast hℓ
  have e1 : (v : ℤ) = (x i - N * y i) + N * (y i - m * (x i / ℓ)) := by
    rw [hvz, Int.emod_def, hℓz]
    rw [hℓz] at *
    ring
  have hr0 : 0 ≤ x i - N * y i := by linarith
  have hr1 : x i - N * y i < N := by linarith
  have hdiv : (v : ℤ) / N = y i - m * (x i / ℓ) := by
    rw [e1, Int.add_mul_ediv_left _ _ hN0, Int.ediv_eq_zero_of_lt hr0 hr1, zero_add]
  show ((((castTorus ℓ x) i).val / N : ℕ) : ZMod m) = ((y i : ℤ) : ZMod m)
  have hnat : (((v / N : ℕ)) : ℤ) = y i - m * (x i / ℓ) := by
    rw [Int.natCast_div]; exact hdiv
  have : ((v / N : ℕ) : ZMod m) = (((v / N : ℕ) : ℤ) : ZMod m) := (Int.cast_natCast _).symm
  show ((v / N : ℕ) : ZMod m) = _
  rw [this, hnat]
  push_cast
  simp

/-- The cast is injective on a block of `ℤ^d`. -/
theorem castTorus_injOn {d ℓ N m : ℕ} [NeZero ℓ] (hℓ : ℓ = N * m) (hm : 0 < m) (y : Fin d → ℤ) :
    Set.InjOn (castTorus (d := d) ℓ) (intFibre N y : Set (Fin d → ℤ)) := by
  intro x hx x' hx' h
  funext i
  have hxi := mem_intFibre.1 (Finset.mem_coe.1 hx) i
  have hxi' := mem_intFibre.1 (Finset.mem_coe.1 hx') i
  have hc : ((x i : ℤ) : ZMod ℓ) = ((x' i : ℤ) : ZMod ℓ) := congrFun h i
  have hdvd := (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (x' i) ℓ).1 hc
  have hNℓ : (N : ℤ) ≤ ℓ := by
    have : (ℓ : ℤ) = N * m := by exact_mod_cast hℓ
    have hm1 : (1 : ℤ) ≤ m := by exact_mod_cast hm
    have hN0 : (0 : ℤ) ≤ N := Nat.cast_nonneg N
    nlinarith
  have hlt : |x' i - x i| < ℓ := by
    rw [abs_lt]; constructor <;> linarith [hxi.1, hxi.2, hxi'.1, hxi'.2]
  have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  linarith

/-- Sums over a block of `ℤ^d` are bounded by sums over the torus block. -/
theorem sum_intFibre_sq_le {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m] (hℓ : ℓ = N * m) (hN : 0 < N)
    (g : Torus d ℓ → ℝ) (y : Fin d → ℤ) :
    ∑ x ∈ intFibre N y, g (castTorus ℓ x) ^ 2 ≤
      ∑ x' ∈ blockFibre N m (castTorus m y), g x' ^ 2 := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [← Finset.sum_image (f := fun x' => g x' ^ 2) (castTorus_injOn hℓ hm y)]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => sq_nonneg _
  intro x' hx'
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hx'
  exact mem_blockFibre.2 (blockMap_castTorus_of_mem hℓ hN hx)

/-- A pointwise value is bounded by the block norm (unit-lattice measure). -/
theorem abs_le_sqrt_mul_blockL2 {d ℓ N m : ℕ} [NeZero ℓ] [NeZero m]
    (hN : 0 < N) (h : Torus d ℓ → ℝ) (z : Torus d ℓ) :
    |h z| ≤ Real.sqrt ((N : ℝ) ^ d) * blockL2 N m (blockMap N m z) h := by
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  have h1 : h z ^ 2 ≤ ∑ x ∈ blockFibre N m (blockMap N m z), h x ^ 2 :=
    Finset.single_le_sum (f := fun x => h x ^ 2) (fun _ _ => sq_nonneg _)
      (mem_blockFibre.2 rfl)
  have h2 : (Real.sqrt ((N : ℝ) ^ d) * blockL2 N m (blockMap N m z) h) ^ 2 =
      ∑ x ∈ blockFibre N m (blockMap N m z), h x ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hNd.le, blockL2, Real.sq_sqrt (by positivity)]
    field_simp
  exact abs_le_of_sq_le_sq (h2 ▸ h1) (mul_nonneg (Real.sqrt_nonneg _) (blockL2_nonneg _ _))

/-! ### The finite-volume kernels, indexed by sites of `ℤ^d` -/

section Limits

variable (d L k : ℕ) [NeZero L]

/-- `Δ_tr` on the coarse torus of side `L M`, evaluated at the sites `y, y' ∈ ℤ^d`. -/
noncomputable def deltaAt (M : ℕ+) (ν a : ℝ) (y y' : Fin d → ℤ) : ℝ :=
  unconstrainedUnitOperator d ((L * (M : ℕ)) * L ^ k) (L ^ k) (L * (M : ℕ)) ν a
    (castTorus (L * (M : ℕ)) y) (castTorus (L * (M : ℕ)) y')

/-- `C_tr` on the coarse torus of side `L M`, evaluated at the sites `y, y' ∈ ℤ^d`. -/
noncomputable def greenAt (M : ℕ+) (ν a a' : ℝ) (y y' : Fin d → ℤ) : ℝ :=
  (coarseOperator d ((L * (M : ℕ)) * L ^ k) (L ^ k) (L * (M : ℕ)) L M ν a a')⁻¹
    (castTorus (L * (M : ℕ)) y) (castTorus (L * (M : ℕ)) y')

variable {d L k}

theorem eventually_torusDist_castTorus (y y' : Fin d → ℤ) (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop) (φ : ℕ → ℕ)
    (hφ : Tendsto φ atTop atTop) :
    ∀ᶠ n in atTop, torusDist d (L * (M (φ n) : ℕ)) (castTorus _ y) (castTorus _ y') =
      l1IntDist d y y' := by
  have hL : 1 ≤ L := Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have h1 : Tendsto (fun n => L * ((M (φ n) : ℕ+) : ℕ)) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left _ hL) (hM.comp hφ)
  have h2 : ∀ᶠ n in atTop, ∀ i, 2 * (y i - y' i).natAbs < L * ((M (φ n) : ℕ+) : ℕ) :=
    Filter.eventually_all.2 fun i => h1.eventually_gt_atTop _
  filter_upwards [h2] with n hn
  exact torusDist_castTorus y y' hn

theorem sum_sq_eq_blockL2 {d ℓ N m : ℕ} [NeZero ℓ] (hN : 0 < N) (y : Torus d m)
    (h : Torus d ℓ → ℝ) :
    ∑ x ∈ blockFibre N m y, h x ^ 2 = (N : ℝ) ^ d * blockL2 N m y h ^ 2 := by
  have hNd : (0 : ℝ) < (N : ℝ) ^ d := by positivity
  rw [blockL2, Real.sq_sqrt (by positivity)]
  field_simp

/-- The fine-to-block kernel `a G Q*` on the torus with `L M` blocks of side `L ^ k` per side,
evaluated at the fine site `x ∈ ℤ^d` and the coarse site `y' ∈ ℤ^d`. -/
noncomputable def fineKernelAt (d L k : ℕ) [NeZero L] (M : ℕ+) (ν a : ℝ) (x y' : Fin d → ℤ) :
    ℝ :=
  fineToBlockKernel d ((L * (M : ℕ)) * L ^ k) (L ^ k) (L * (M : ℕ)) ν a
    (castTorus ((L * (M : ℕ)) * L ^ k) x) (castTorus (L * (M : ℕ)) y')

/-- **G-5(c): infinite-volume limits.**  Along tori of side `L M_n`, `M_n → ∞`, there is a
subsequence along which `a G Q*` (pointwise at fine × coarse sites of `ℤ^d`), `Δ_tr` and `C_tr`
converge entrywise, simultaneously for all `ν ∈ [0, 2]`.  The limits satisfy

* the decay bound of (a), for `a G Q*` in the block `L²` norm (`∑_{x ∈ block y} |K(x, y')|²`,
  i.e. `N^d` times the squared unit-lattice block norm) and for `Δ_tr`, `C_tr` pointwise;
* the Lipschitz bounds of (b);

with the `ℓ¹` distance of `ℤ^d`.  The constants depend on `d, L` only. -/
theorem infiniteVolume_limits (hd : 0 < d) (hk : 1 ≤ k) {a a' : ℝ} (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2) (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Kinf Dinf Cinf : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ,
      (∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        Tendsto (fun n => fineKernelAt d L k (M (φ n)) ν a y y') atTop (𝓝 (Kinf ν y y')) ∧
        Tendsto (fun n => deltaAt d L k (M (φ n)) ν a y y') atTop (𝓝 (Dinf ν y y')) ∧
        Tendsto (fun n => greenAt d L k (M (φ n)) ν a a' y y') atTop (𝓝 (Cinf ν y y'))) ∧
      (∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        ∑ x ∈ intFibre (L ^ k) y, (Kinf ν x y') ^ 2 ≤ (((L ^ k : ℕ) : ℝ) ^ d) *
            (a * blockDecayConst d L * Real.exp (-(blockDecayRate d * l1IntDist d y y'))) ^ 2 ∧
        |Dinf ν y y'| ≤ (2 + 4 * blockDecayConst d L) *
            Real.exp (-(blockDecayRate d * l1IntDist d y y')) ∧
        |Cinf ν y y'| ≤ 2 * (trGamma d L)⁻¹ * Real.exp (-(trRate d L * l1IntDist d y y'))) ∧
      (∀ ν₁ ∈ Set.Icc (0 : ℝ) 2, ∀ ν₂ ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        ∑ x ∈ intFibre (L ^ k) y, (Kinf ν₁ x y' - Kinf ν₂ x y') ^ 2 ≤ (((L ^ k : ℕ) : ℝ) ^ d) *
            (a * (|ν₁ - ν₂| * massLipConst d L *
              Real.exp (-(blockDecayRate d / 2) * l1IntDist d y y'))) ^ 2 ∧
        |Dinf ν₁ y y' - Dinf ν₂ y y'| ≤ 4 * (|ν₁ - ν₂| * massLipConst d L *
            Real.exp (-(blockDecayRate d / 2) * l1IntDist d y y')) ∧
        |Cinf ν₁ y y' - Cinf ν₂ y y'| ≤ |ν₁ - ν₂| * coarseLipConst d L *
            Real.exp (-(lipRate d L / 4) * l1IntDist d y y')) := by
  classical
  have hγ := trGamma_pos (L := L) hd
  have hC0 := blockDecayConst_pos (L := L) hd
  have hr0 := blockDecayRate_pos hd
  have hρ0 := trRate_pos (L := L) hd
  have hlr := lipRate_pos (L := L) hd
  have hml := massLipConst_nonneg (L := L) hd
  have hcl : 0 ≤ coarseLipConst d L := by
    unfold coarseLipConst
    have h1 := ballConst_nonneg (d := d) (by positivity : 0 < lipRate d L / 2)
    have h2 := ballConst_nonneg (d := d) (by positivity : 0 < lipRate d L / 4)
    positivity
  have hNpos : 0 < L ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne L))
  have hexp1 : ∀ r x : ℝ, 0 ≤ r → 0 ≤ x → Real.exp (-r * x) ≤ 1 := fun r x hr hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  set SN : ℝ := Real.sqrt (((L ^ k : ℕ) : ℝ) ^ d) with hSN
  have hSN0 : 0 ≤ SN := Real.sqrt_nonneg _
  -- the finite-volume functions
  let f : ℕ → ((Fin d → ℤ) × (Fin d → ℤ) × Fin 3) → ℝ → ℝ := fun n i ν =>
    if i.2.2 = 2 then fineKernelAt d L k (M n) ν a i.1 i.2.1
    else if i.2.2 = 1 then greenAt d L k (M n) ν a a' i.1 i.2.1
    else deltaAt d L k (M n) ν a i.1 i.2.1
  let B : ((Fin d → ℤ) × (Fin d → ℤ) × Fin 3) → ℝ := fun _ =>
    (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹ + SN * (2 * blockDecayConst d L)
  let Λ : ((Fin d → ℤ) × (Fin d → ℤ) × Fin 3) → ℝ := fun _ =>
    4 * massLipConst d L + coarseLipConst d L + SN * (2 * massLipConst d L)
  have hdelta_dec : ∀ (n : ℕ) (ν : ℝ), ν ∈ Set.Icc (0 : ℝ) 2 → ∀ y y' : Fin d → ℤ,
      |deltaAt d L k (M n) ν a y y'| ≤ (2 + 4 * blockDecayConst d L) *
        Real.exp (-(blockDecayRate d * torusDist d (L * (M n : ℕ)) (castTorus _ y)
          (castTorus _ y'))) := by
    intro n ν hν y y'
    exact unconstrainedUnitOperator_decay (L := L) (N₀ := L * (M n : ℕ)) hd hk hν.1 ha1 ha2 _ _
  have hgreen_dec : ∀ (n : ℕ) (ν : ℝ), ν ∈ Set.Icc (0 : ℝ) 2 → ∀ y y' : Fin d → ℤ,
      |greenAt d L k (M n) ν a a' y y'| ≤ 2 * (trGamma d L)⁻¹ *
        Real.exp (-(trRate d L * torusDist d (L * (M n : ℕ)) (castTorus _ y)
          (castTorus _ y'))) := by
    intro n ν hν y y'
    exact coarseGreen_decay (L := L) (N₀ := L * (M n : ℕ)) (M := (M n : ℕ)) hd hk rfl hν.1 hν.2
      ha1 ha2 ha'1 ha'2 _ _
  have hdelta_lip : ∀ (n : ℕ) (ν₁ ν₂ : ℝ), ν₁ ∈ Set.Icc (0 : ℝ) 2 → ν₂ ∈ Set.Icc (0 : ℝ) 2 →
      ∀ y y' : Fin d → ℤ, |deltaAt d L k (M n) ν₁ a y y' - deltaAt d L k (M n) ν₂ a y y'| ≤
        4 * (|ν₁ - ν₂| * massLipConst d L * Real.exp (-(blockDecayRate d / 2) *
          torusDist d (L * (M n : ℕ)) (castTorus _ y) (castTorus _ y'))) := by
    intro n ν₁ ν₂ h1 h2 y y'
    exact unconstrainedUnitOperator_lipschitz (L := L) (N₀ := L * (M n : ℕ)) hd hk h1.1 h2.1 ha1
      ha2 _ _
  have hgreen_lip : ∀ (n : ℕ) (ν₁ ν₂ : ℝ), ν₁ ∈ Set.Icc (0 : ℝ) 2 → ν₂ ∈ Set.Icc (0 : ℝ) 2 →
      ∀ y y' : Fin d → ℤ, |greenAt d L k (M n) ν₁ a a' y y' - greenAt d L k (M n) ν₂ a a' y y'| ≤
        |ν₁ - ν₂| * coarseLipConst d L * Real.exp (-(lipRate d L / 4) *
          torusDist d (L * (M n : ℕ)) (castTorus _ y) (castTorus _ y')) := by
    intro n ν₁ ν₂ h1 h2 y y'
    exact coarseGreen_lipschitz (L := L) (N₀ := L * (M n : ℕ)) (M := (M n : ℕ)) hd hk rfl h1.1
      h1.2 h2.1 h2.2 ha1 ha2 ha'1 ha'2 _ _
  -- the fine-to-block kernel: block bounds and pointwise bounds
  have hℓ : ∀ n : ℕ, (L * (M n : ℕ)) * L ^ k = L ^ k * (L * (M n : ℕ)) := fun n => mul_comm _ _
  have hfine_blk : ∀ (n : ℕ) (ν : ℝ), ν ∈ Set.Icc (0 : ℝ) 2 → ∀ (y y' : Fin d → ℤ),
      ∑ x ∈ intFibre (L ^ k) y, (fineKernelAt d L k (M n) ν a x y') ^ 2 ≤
        (((L ^ k : ℕ) : ℝ) ^ d) * (a * blockDecayConst d L *
          Real.exp (-(blockDecayRate d * torusDist d (L * (M n : ℕ)) (castTorus _ y)
            (castTorus _ y')))) ^ 2 := by
    intro n ν hν y y'
    have h1 := sum_intFibre_sq_le (hℓ n) hNpos
      (fun x' => fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν a x'
        (castTorus (L * (M n : ℕ)) y')) y
    have h2 := fineToBlockKernel_decay (L := L) (N₀ := L * (M n : ℕ)) hd hk hν.1 ha1 ha2
      (castTorus (L * (M n : ℕ)) y) (castTorus (L * (M n : ℕ)) y')
    rw [sum_sq_eq_blockL2 hNpos] at h1
    refine h1.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (blockL2_nonneg _ _) h2 2
  have hfine_lip_blk : ∀ (n : ℕ) (ν₁ ν₂ : ℝ), ν₁ ∈ Set.Icc (0 : ℝ) 2 → ν₂ ∈ Set.Icc (0 : ℝ) 2 →
      ∀ (y y' : Fin d → ℤ),
      ∑ x ∈ intFibre (L ^ k) y, (fineKernelAt d L k (M n) ν₁ a x y' -
          fineKernelAt d L k (M n) ν₂ a x y') ^ 2 ≤
        (((L ^ k : ℕ) : ℝ) ^ d) * (a * (|ν₁ - ν₂| * massLipConst d L *
          Real.exp (-(blockDecayRate d / 2) * torusDist d (L * (M n : ℕ)) (castTorus _ y)
            (castTorus _ y')))) ^ 2 := by
    intro n ν₁ ν₂ h1 h2 y y'
    have h3 := sum_intFibre_sq_le (hℓ n) hNpos
      (fun x' => fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν₁ a x'
        (castTorus (L * (M n : ℕ)) y') -
        fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν₂ a x'
        (castTorus (L * (M n : ℕ)) y')) y
    have h4 := fineToBlockKernel_lipschitz (L := L) (N₀ := L * (M n : ℕ)) hd hk h1.1 h2.1 ha1 ha2
      (castTorus (L * (M n : ℕ)) y) (castTorus (L * (M n : ℕ)) y')
    rw [sum_sq_eq_blockL2 hNpos] at h3
    refine h3.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact pow_le_pow_left₀ (blockL2_nonneg _ _) h4 2
  have hfine_dec : ∀ (n : ℕ) (ν : ℝ), ν ∈ Set.Icc (0 : ℝ) 2 → ∀ x y' : Fin d → ℤ,
      |fineKernelAt d L k (M n) ν a x y'| ≤ SN * (2 * blockDecayConst d L) := by
    intro n ν hν x y'
    have h1 := abs_le_sqrt_mul_blockL2 (ℓ := (L * (M n : ℕ)) * L ^ k) (N := L ^ k)
      (m := L * (M n : ℕ)) hNpos
      (fun x' => fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν a x'
        (castTorus (L * (M n : ℕ)) y')) (castTorus ((L * (M n : ℕ)) * L ^ k) x)
    have h2 := fineToBlockKernel_decay (L := L) (N₀ := L * (M n : ℕ)) hd hk hν.1 ha1 ha2
      (blockMap (L ^ k) (L * (M n : ℕ)) (castTorus ((L * (M n : ℕ)) * L ^ k) x))
      (castTorus (L * (M n : ℕ)) y')
    have h3 : Real.exp (-(blockDecayRate d * torusDist d (L * (M n : ℕ))
        (blockMap (L ^ k) (L * (M n : ℕ)) (castTorus ((L * (M n : ℕ)) * L ^ k) x))
        (castTorus (L * (M n : ℕ)) y'))) ≤ 1 := by
      rw [← neg_mul]; exact hexp1 _ _ hr0.le (torusDist_nonneg_gen _ _)
    have h4 : a * blockDecayConst d L * Real.exp (-(blockDecayRate d * torusDist d
        (L * (M n : ℕ)) (blockMap (L ^ k) (L * (M n : ℕ))
          (castTorus ((L * (M n : ℕ)) * L ^ k) x)) (castTorus (L * (M n : ℕ)) y'))) ≤
        2 * blockDecayConst d L := by
      calc _ ≤ a * blockDecayConst d L * 1 := mul_le_mul_of_nonneg_left h3 (by positivity)
        _ ≤ 2 * blockDecayConst d L := by nlinarith
    show |fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν a
      (castTorus ((L * (M n : ℕ)) * L ^ k) x) (castTorus (L * (M n : ℕ)) y')| ≤ _
    exact h1.trans (mul_le_mul_of_nonneg_left (h2.trans h4) hSN0)
  have hfine_lip : ∀ (n : ℕ) (ν₁ ν₂ : ℝ), ν₁ ∈ Set.Icc (0 : ℝ) 2 → ν₂ ∈ Set.Icc (0 : ℝ) 2 →
      ∀ x y' : Fin d → ℤ, |fineKernelAt d L k (M n) ν₁ a x y' - fineKernelAt d L k (M n) ν₂ a x y'|
        ≤ SN * (2 * massLipConst d L) * |ν₁ - ν₂| := by
    intro n ν₁ ν₂ h1 h2 x y'
    have h3 := abs_le_sqrt_mul_blockL2 (ℓ := (L * (M n : ℕ)) * L ^ k) (N := L ^ k)
      (m := L * (M n : ℕ)) hNpos
      (fun x' => fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν₁ a x'
        (castTorus (L * (M n : ℕ)) y') -
        fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν₂ a x'
        (castTorus (L * (M n : ℕ)) y')) (castTorus ((L * (M n : ℕ)) * L ^ k) x)
    have h4 := fineToBlockKernel_lipschitz (L := L) (N₀ := L * (M n : ℕ)) hd hk h1.1 h2.1 ha1 ha2
      (blockMap (L ^ k) (L * (M n : ℕ)) (castTorus ((L * (M n : ℕ)) * L ^ k) x))
      (castTorus (L * (M n : ℕ)) y')
    have h5 : Real.exp (-(blockDecayRate d / 2) * torusDist d (L * (M n : ℕ))
        (blockMap (L ^ k) (L * (M n : ℕ)) (castTorus ((L * (M n : ℕ)) * L ^ k) x))
        (castTorus (L * (M n : ℕ)) y')) ≤ 1 :=
      hexp1 _ _ (by positivity) (torusDist_nonneg_gen _ _)
    have h6 : a * (|ν₁ - ν₂| * massLipConst d L * Real.exp (-(blockDecayRate d / 2) *
        torusDist d (L * (M n : ℕ)) (blockMap (L ^ k) (L * (M n : ℕ))
          (castTorus ((L * (M n : ℕ)) * L ^ k) x)) (castTorus (L * (M n : ℕ)) y'))) ≤
        2 * massLipConst d L * |ν₁ - ν₂| := by
      have h7 : |ν₁ - ν₂| * massLipConst d L * Real.exp (-(blockDecayRate d / 2) *
          torusDist d (L * (M n : ℕ)) (blockMap (L ^ k) (L * (M n : ℕ))
            (castTorus ((L * (M n : ℕ)) * L ^ k) x)) (castTorus (L * (M n : ℕ)) y')) ≤
          |ν₁ - ν₂| * massLipConst d L := by
        calc _ ≤ |ν₁ - ν₂| * massLipConst d L * 1 :=
              mul_le_mul_of_nonneg_left h5 (by positivity)
          _ = _ := mul_one _
      have h8 : 0 ≤ |ν₁ - ν₂| * massLipConst d L := by positivity
      nlinarith
    show |fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν₁ a
      (castTorus ((L * (M n : ℕ)) * L ^ k) x) (castTorus (L * (M n : ℕ)) y') -
      fineToBlockKernel d ((L * (M n : ℕ)) * L ^ k) (L ^ k) (L * (M n : ℕ)) ν₂ a
      (castTorus ((L * (M n : ℕ)) * L ^ k) x) (castTorus (L * (M n : ℕ)) y')| ≤ _
    calc _ ≤ SN * blockL2 (L ^ k) (L * (M n : ℕ)) _ _ := h3
      _ ≤ SN * (2 * massLipConst d L * |ν₁ - ν₂|) :=
          mul_le_mul_of_nonneg_left (h4.trans h6) hSN0
      _ = _ := by ring
  have hB : ∀ n i ν, ν ∈ Set.Icc (0 : ℝ) 2 → |f n i ν| ≤ B i := by
    intro n i ν hν
    have hd0 := torusDist_nonneg_gen (m := L * (M n : ℕ)) (castTorus _ i.1) (castTorus _ i.2.1)
    have e1 : Real.exp (-(trRate d L * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
        (castTorus _ i.2.1))) ≤ 1 := by
      rw [← neg_mul]; exact hexp1 _ _ hρ0.le hd0
    have e2 : Real.exp (-(blockDecayRate d * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
        (castTorus _ i.2.1))) ≤ 1 := by
      rw [← neg_mul]; exact hexp1 _ _ hr0.le hd0
    have p1 : 0 ≤ 2 * (trGamma d L)⁻¹ := by positivity
    have p2 : 0 ≤ 2 + 4 * blockDecayConst d L := by positivity
    have p3 : 0 ≤ SN * (2 * blockDecayConst d L) := by positivity
    have h1 := hgreen_dec n ν hν i.1 i.2.1
    have h2 := hdelta_dec n ν hν i.1 i.2.1
    have h3 := hfine_dec n ν hν i.1 i.2.1
    have h1' := mul_le_mul_of_nonneg_left e1 p1
    have h2' := mul_le_mul_of_nonneg_left e2 p2
    show |if i.2.2 = 2 then fineKernelAt d L k (M n) ν a i.1 i.2.1
      else if i.2.2 = 1 then greenAt d L k (M n) ν a a' i.1 i.2.1
      else deltaAt d L k (M n) ν a i.1 i.2.1| ≤ _
    split_ifs
    · show _ ≤ (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹ + SN * (2 * blockDecayConst d L)
      linarith
    · show _ ≤ (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹ + SN * (2 * blockDecayConst d L)
      linarith
    · show _ ≤ (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹ + SN * (2 * blockDecayConst d L)
      linarith
  have hΛ : ∀ n i ν ν', ν ∈ Set.Icc (0 : ℝ) 2 → ν' ∈ Set.Icc (0 : ℝ) 2 →
      |f n i ν - f n i ν'| ≤ Λ i * |ν - ν'| := by
    intro n i ν ν' hν hν'
    have hd0 := torusDist_nonneg_gen (m := L * (M n : ℕ)) (castTorus _ i.1) (castTorus _ i.2.1)
    have e1 : Real.exp (-(lipRate d L / 4) * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
        (castTorus _ i.2.1)) ≤ 1 := hexp1 _ _ (by positivity) hd0
    have e2 : Real.exp (-(blockDecayRate d / 2) * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
        (castTorus _ i.2.1)) ≤ 1 := hexp1 _ _ (by positivity) hd0
    have h1 := hgreen_lip n ν ν' hν hν' i.1 i.2.1
    have h2 := hdelta_lip n ν ν' hν hν' i.1 i.2.1
    have h3 := hfine_lip n ν ν' hν hν' i.1 i.2.1
    have a1 := mul_le_mul_of_nonneg_left e1 (by positivity : 0 ≤ |ν - ν'| * coarseLipConst d L)
    have a2 := mul_le_mul_of_nonneg_left e2 (by positivity : 0 ≤ |ν - ν'| * massLipConst d L)
    have q1 : 0 ≤ coarseLipConst d L * |ν - ν'| := by positivity
    have q2 : 0 ≤ massLipConst d L * |ν - ν'| := by positivity
    have q3 : 0 ≤ SN * (2 * massLipConst d L) * |ν - ν'| := by positivity
    show |(if i.2.2 = 2 then fineKernelAt d L k (M n) ν a i.1 i.2.1
      else if i.2.2 = 1 then greenAt d L k (M n) ν a a' i.1 i.2.1
      else deltaAt d L k (M n) ν a i.1 i.2.1) -
      (if i.2.2 = 2 then fineKernelAt d L k (M n) ν' a i.1 i.2.1
      else if i.2.2 = 1 then greenAt d L k (M n) ν' a a' i.1 i.2.1
      else deltaAt d L k (M n) ν' a i.1 i.2.1)| ≤ _
    split_ifs
    · show _ ≤ (4 * massLipConst d L + coarseLipConst d L + SN * (2 * massLipConst d L)) * |ν - ν'|
      nlinarith
    · show _ ≤ (4 * massLipConst d L + coarseLipConst d L + SN * (2 * massLipConst d L)) * |ν - ν'|
      nlinarith
    · show _ ≤ (4 * massLipConst d L + coarseLipConst d L + SN * (2 * massLipConst d L)) * |ν - ν'|
      nlinarith
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto f B Λ hB hΛ
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hKex : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y', ∃ l,
      Tendsto (fun n => fineKernelAt d L k (M (φ n)) ν a y y') atTop (𝓝 l) := by
    intro ν hν y y'
    obtain ⟨l, hl⟩ := hconv (y, y', 2) ν hν
    exact ⟨l, by simpa [f] using hl⟩
  have hDex : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y', ∃ l,
      Tendsto (fun n => deltaAt d L k (M (φ n)) ν a y y') atTop (𝓝 l) := by
    intro ν hν y y'
    obtain ⟨l, hl⟩ := hconv (y, y', 0) ν hν
    exact ⟨l, by simpa [f] using hl⟩
  have hCex : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y', ∃ l,
      Tendsto (fun n => greenAt d L k (M (φ n)) ν a a' y y') atTop (𝓝 l) := by
    intro ν hν y y'
    obtain ⟨l, hl⟩ := hconv (y, y', 1) ν hν
    exact ⟨l, by simpa [f] using hl⟩
  refine ⟨φ, hφ, fun ν y y' => limUnder atTop (fun n => fineKernelAt d L k (M (φ n)) ν a y y'),
    fun ν y y' => limUnder atTop (fun n => deltaAt d L k (M (φ n)) ν a y y'),
    fun ν y y' => limUnder atTop (fun n => greenAt d L k (M (φ n)) ν a a' y y'), ?_, ?_, ?_⟩
  · intro ν hν y y'
    exact ⟨tendsto_nhds_limUnder (hKex ν hν y y'), tendsto_nhds_limUnder (hDex ν hν y y'),
      tendsto_nhds_limUnder (hCex ν hν y y')⟩
  · intro ν hν y y'
    have hev := eventually_torusDist_castTorus (L := L) y y' M hM φ hφt
    refine ⟨?_, ?_, ?_⟩
    · have hT : Tendsto (fun n => ∑ x ∈ intFibre (L ^ k) y,
          (fineKernelAt d L k (M (φ n)) ν a x y') ^ 2) atTop
          (𝓝 (∑ x ∈ intFibre (L ^ k) y,
            (limUnder atTop (fun n => fineKernelAt d L k (M (φ n)) ν a x y')) ^ 2)) :=
        tendsto_finsetSum _ fun x _ => (tendsto_nhds_limUnder (hKex ν hν x y')).pow 2
      refine le_of_tendsto hT ?_
      filter_upwards [hev] with n hn
      have := hfine_blk (φ n) ν hν y y'
      rwa [hn] at this
    · refine le_of_tendsto (tendsto_nhds_limUnder (hDex ν hν y y')).abs ?_
      filter_upwards [hev] with n hn
      have := hdelta_dec (φ n) ν hν y y'
      rwa [hn] at this
    · refine le_of_tendsto (tendsto_nhds_limUnder (hCex ν hν y y')).abs ?_
      filter_upwards [hev] with n hn
      have := hgreen_dec (φ n) ν hν y y'
      rwa [hn] at this
  · intro ν₁ hν₁ ν₂ hν₂ y y'
    have hev := eventually_torusDist_castTorus (L := L) y y' M hM φ hφt
    refine ⟨?_, ?_, ?_⟩
    · have hT : Tendsto (fun n => ∑ x ∈ intFibre (L ^ k) y,
          (fineKernelAt d L k (M (φ n)) ν₁ a x y' - fineKernelAt d L k (M (φ n)) ν₂ a x y') ^ 2)
          atTop (𝓝 (∑ x ∈ intFibre (L ^ k) y,
            ((limUnder atTop (fun n => fineKernelAt d L k (M (φ n)) ν₁ a x y')) -
              (limUnder atTop (fun n => fineKernelAt d L k (M (φ n)) ν₂ a x y'))) ^ 2)) :=
        tendsto_finsetSum _ fun x _ => ((tendsto_nhds_limUnder (hKex ν₁ hν₁ x y')).sub
          (tendsto_nhds_limUnder (hKex ν₂ hν₂ x y'))).pow 2
      refine le_of_tendsto hT ?_
      filter_upwards [hev] with n hn
      have := hfine_lip_blk (φ n) ν₁ ν₂ hν₁ hν₂ y y'
      rwa [hn] at this
    · refine le_of_tendsto ((tendsto_nhds_limUnder (hDex ν₁ hν₁ y y')).sub
        (tendsto_nhds_limUnder (hDex ν₂ hν₂ y y'))).abs ?_
      filter_upwards [hev] with n hn
      have := hdelta_lip (φ n) ν₁ ν₂ hν₁ hν₂ y y'
      rwa [hn] at this
    · refine le_of_tendsto ((tendsto_nhds_limUnder (hCex ν₁ hν₁ y y')).sub
        (tendsto_nhds_limUnder (hCex ν₂ hν₂ y y'))).abs ?_
      filter_upwards [hev] with n hn
      have := hgreen_lip (φ n) ν₁ ν₂ hν₁ hν₂ y y'
      rwa [hn] at this

end Limits

end Balaban.Green
