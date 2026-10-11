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

/-- **G-5(c): infinite-volume limits.**  Along tori of side `L M_n`, `M_n → ∞`, there is a
subsequence along which `Δ_tr` and `C_tr` converge entrywise on `ℤ^d × ℤ^d`, simultaneously for all
`ν ∈ [0, 2]`; the limits satisfy the decay bound of (a) and the Lipschitz bound of (b) with the
`ℓ¹` distance of `ℤ^d`.  The constants depend on `d, L` only. -/
theorem infiniteVolume_limits (hd : 0 < d) (hk : 1 ≤ k) {a a' : ℝ} (ha1 : 1 / 2 ≤ a)
    (ha2 : a ≤ 2) (ha'1 : 1 / 2 ≤ a') (ha'2 : a' ≤ 2) (M : ℕ → ℕ+)
    (hM : Tendsto (fun n => ((M n : ℕ+) : ℕ)) atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Dinf Cinf : ℝ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ,
      (∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        Tendsto (fun n => deltaAt d L k (M (φ n)) ν a y y') atTop (𝓝 (Dinf ν y y')) ∧
        Tendsto (fun n => greenAt d L k (M (φ n)) ν a a' y y') atTop (𝓝 (Cinf ν y y'))) ∧
      (∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
        |Dinf ν y y'| ≤ (2 + 4 * blockDecayConst d L) *
            Real.exp (-(blockDecayRate d * l1IntDist d y y')) ∧
        |Cinf ν y y'| ≤ 2 * (trGamma d L)⁻¹ * Real.exp (-(trRate d L * l1IntDist d y y'))) ∧
      (∀ ν₁ ∈ Set.Icc (0 : ℝ) 2, ∀ ν₂ ∈ Set.Icc (0 : ℝ) 2, ∀ y y',
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
  have hexp1 : ∀ r x : ℝ, 0 ≤ r → 0 ≤ x → Real.exp (-r * x) ≤ 1 := fun r x hr hx =>
    Real.exp_le_one_iff.2 (by nlinarith)
  -- the finite-volume functions
  let f : ℕ → ((Fin d → ℤ) × (Fin d → ℤ) × Bool) → ℝ → ℝ := fun n i ν =>
    if i.2.2 then greenAt d L k (M n) ν a a' i.1 i.2.1 else deltaAt d L k (M n) ν a i.1 i.2.1
  let B : ((Fin d → ℤ) × (Fin d → ℤ) × Bool) → ℝ := fun _ =>
    (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹
  let Λ : ((Fin d → ℤ) × (Fin d → ℤ) × Bool) → ℝ := fun _ =>
    4 * massLipConst d L + coarseLipConst d L
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
  have hB : ∀ n i ν, ν ∈ Set.Icc (0 : ℝ) 2 → |f n i ν| ≤ B i := by
    intro n i ν hν
    have hd0 := torusDist_nonneg_gen (m := L * (M n : ℕ)) (castTorus _ i.1) (castTorus _ i.2.1)
    by_cases hb : i.2.2
    · simp only [f, hb, ite_true]
      have h := hgreen_dec n ν hν i.1 i.2.1
      have : Real.exp (-(trRate d L * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
          (castTorus _ i.2.1))) ≤ 1 := by
        rw [← neg_mul]; exact hexp1 _ _ hρ0.le hd0
      show _ ≤ (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹
      have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 * (trGamma d L)⁻¹)
      have h3 : 0 ≤ 2 + 4 * blockDecayConst d L := by positivity
      linarith
    · simp only [f, hb, Bool.false_eq_true, ite_false]
      have h := hdelta_dec n ν hν i.1 i.2.1
      have : Real.exp (-(blockDecayRate d * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
          (castTorus _ i.2.1))) ≤ 1 := by
        rw [← neg_mul]; exact hexp1 _ _ hr0.le hd0
      show _ ≤ (2 + 4 * blockDecayConst d L) + 2 * (trGamma d L)⁻¹
      have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ 2 + 4 * blockDecayConst d L)
      have h3 : 0 ≤ 2 * (trGamma d L)⁻¹ := by positivity
      linarith
  have hΛ : ∀ n i ν ν', ν ∈ Set.Icc (0 : ℝ) 2 → ν' ∈ Set.Icc (0 : ℝ) 2 →
      |f n i ν - f n i ν'| ≤ Λ i * |ν - ν'| := by
    intro n i ν ν' hν hν'
    have hd0 := torusDist_nonneg_gen (m := L * (M n : ℕ)) (castTorus _ i.1) (castTorus _ i.2.1)
    by_cases hb : i.2.2
    · simp only [f, hb, ite_true]
      have h := hgreen_lip n ν ν' hν hν' i.1 i.2.1
      have : Real.exp (-(lipRate d L / 4) * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
          (castTorus _ i.2.1)) ≤ 1 := hexp1 _ _ (by positivity) hd0
      show _ ≤ (4 * massLipConst d L + coarseLipConst d L) * |ν - ν'|
      have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ |ν - ν'| * coarseLipConst d L)
      have h3 : 0 ≤ 4 * massLipConst d L * |ν - ν'| := by positivity
      nlinarith
    · simp only [f, hb, Bool.false_eq_true, ite_false]
      have h := hdelta_lip n ν ν' hν hν' i.1 i.2.1
      have : Real.exp (-(blockDecayRate d / 2) * torusDist d (L * (M n : ℕ)) (castTorus _ i.1)
          (castTorus _ i.2.1)) ≤ 1 := hexp1 _ _ (by positivity) hd0
      show _ ≤ (4 * massLipConst d L + coarseLipConst d L) * |ν - ν'|
      have h2 := mul_le_mul_of_nonneg_left this (by positivity : 0 ≤ |ν - ν'| * massLipConst d L)
      have h3 : 0 ≤ coarseLipConst d L * |ν - ν'| := by positivity
      nlinarith
  obtain ⟨φ, hφ, hconv⟩ := exists_subseq_tendsto f B Λ hB hΛ
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hDex : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y', ∃ l,
      Tendsto (fun n => deltaAt d L k (M (φ n)) ν a y y') atTop (𝓝 l) := by
    intro ν hν y y'
    obtain ⟨l, hl⟩ := hconv (y, y', false) ν hν
    exact ⟨l, by simpa [f] using hl⟩
  have hCex : ∀ ν ∈ Set.Icc (0 : ℝ) 2, ∀ y y', ∃ l,
      Tendsto (fun n => greenAt d L k (M (φ n)) ν a a' y y') atTop (𝓝 l) := by
    intro ν hν y y'
    obtain ⟨l, hl⟩ := hconv (y, y', true) ν hν
    exact ⟨l, by simpa [f] using hl⟩
  refine ⟨φ, hφ, fun ν y y' => limUnder atTop (fun n => deltaAt d L k (M (φ n)) ν a y y'),
    fun ν y y' => limUnder atTop (fun n => greenAt d L k (M (φ n)) ν a a' y y'), ?_, ?_, ?_⟩
  · intro ν hν y y'
    exact ⟨tendsto_nhds_limUnder (hDex ν hν y y'), tendsto_nhds_limUnder (hCex ν hν y y')⟩
  · intro ν hν y y'
    have hev := eventually_torusDist_castTorus (L := L) y y' M hM φ hφt
    refine ⟨?_, ?_⟩
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
    refine ⟨?_, ?_⟩
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
