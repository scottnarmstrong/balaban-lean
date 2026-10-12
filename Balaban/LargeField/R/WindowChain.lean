module

public import Balaban.LargeField.R.WindowGaussTree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block tree of a `k`-block and the composed Gaussian (Part III, Lemma III.1.6)

For a `k`-block `z ⊂ Ω^c_k` the Gaussian-only variables form a tree: the non-leaf blocks `y ⊂ z` of
scales `k₁ + 1, …, k`, each with `m = L^d` children that are non-leaf blocks or leaves `x`
(the leaves carry the fixed values `ψ^G(x)`).  `BlockTree m k1 k` is this combinatorial structure.

* `varpi k z n = ∏_{i=n+1}^k z_i⁻¹` (`ϖ_n`), `blockFrac m k s = m^{-(k-s)}` (the volume fraction `w`);
* `composedPrecision` is `β_k a^♮_z`: `(∑_y ϖ_j² w_y² / c_j)⁻¹` (III.1.5);
* `composedMean` is `𝒬^♮_z ψ^G = ∑_x w_x ϖ_{n_x} ψ^G(x)` (III.1.4);
* `windowIntegrand` is the integrand `∏_y z^N t_j(zψ(y), Qψ_j(y))` of (III.1.4), with
  `t_j(a, b) = g_{c_j}(a - b)`;
* `integral_window_comp` is (III.1.4): integrating all non-leaf blocks except the top gives the
  Gaussian density `g_z(ψ_k(z) - 𝒬^♮_z ψ^G)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory

/-- The block tree of a `k`-block: non-leaf blocks `0, …, n` (`0` the top block of scale `k`; block `i > 0` has
parent `par i < i` of scale one higher), leaves `x : Fin nLeaf` attached to non-leaf blocks, every non-leaf
block having `m` children (blocks and leaves); the non-leaf blocks have scales `≥ k₁ + 1`. -/
structure BlockTree (m k1 k : ℕ) where
  /-- the non-leaf blocks are `0, …, n` -/
  n : ℕ
  /-- the scale of a non-leaf block -/
  scale : ℕ → ℕ
  /-- the parent of a non-leaf block (`i ≠ 0`) -/
  par : ℕ → ℕ
  /-- the number of leaves -/
  nLeaf : ℕ
  /-- the non-leaf parent of a leaf -/
  leafPar : Fin nLeaf → ℕ
  /-- the top block has scale `k` -/
  root_scale : scale 0 = k
  /-- parents come first -/
  par_lt : ∀ i, i ≤ n → i ≠ 0 → par i < i
  /-- the parent has scale one higher -/
  scale_par : ∀ i, i ≤ n → i ≠ 0 → scale (par i) = scale i + 1
  /-- non-leaf blocks have scale `≥ k₁ + 1` -/
  scale_ge : ∀ i, i ≤ n → k1 + 1 ≤ scale i
  /-- leaves hang from non-leaf blocks -/
  leafPar_le : ∀ x, leafPar x ≤ n
  /-- every non-leaf block has exactly `m` children -/
  full : ∀ i, i ≤ n →
    ((Finset.range (n + 1)).filter (fun c => c ≠ 0 ∧ par c = i)).card +
      (Finset.univ.filter (fun x : Fin nLeaf => leafPar x = i)).card = m

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- The scale `n_x` of a leaf. -/
def leafScale (x : Fin B.nLeaf) : ℕ := B.scale (B.leafPar x) - 1

theorem scale_le : ∀ i, i ≤ B.n → B.scale i ≤ k := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    by_cases h0 : i = 0
    · subst h0; rw [B.root_scale]
    · have h1 := ih (B.par i) (B.par_lt i hi h0) (by have := B.par_lt i hi h0; omega)
      have h2 := B.scale_par i hi h0
      omega

end BlockTree

/-- The volume fraction `w = m^{-(k-s)}` of a block of scale `s` in a `k`-block. -/
noncomputable def blockFrac (m k s : ℕ) : ℝ := (((m : ℝ)) ^ (k - s))⁻¹

/-- `ϖ_n = ∏_{i=n+1}^k z_i⁻¹` (`ϖ_k = 1`). -/
noncomputable def varpi (k : ℕ) (z : ℕ → ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range (k - n), (z (k - i))⁻¹

theorem varpi_pred {k s : ℕ} (z : ℕ → ℝ) (h1 : 1 ≤ s) (h2 : s ≤ k) :
    varpi k z (s - 1) = (z s)⁻¹ * varpi k z s := by
  unfold varpi
  have : k - (s - 1) = (k - s) + 1 := by omega
  have h3 : k - (k - s) = s := by omega
  rw [this, Finset.prod_range_succ, mul_comm, h3]

theorem blockFrac_succ {m k s : ℕ} (hm : 0 < m) (hs : s < k) :
    (m : ℝ)⁻¹ * blockFrac m k (s + 1) = blockFrac m k s := by
  unfold blockFrac
  have : k - s = (k - (s + 1)) + 1 := by omega
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [this, pow_succ]
  field_simp

namespace BlockTree

variable {m k1 k : ℕ} (B : BlockTree m k1 k)

/-- `β_k a^♮_z = (∑_y ϖ_j² w_y² / c_j)⁻¹` (III.1.5), the sum over the non-leaf blocks `y` of scale
`j + 1`. -/
noncomputable def composedPrecision (c z : ℕ → ℝ) : ℝ :=
  (∑ i ∈ Finset.range (B.n + 1),
    varpi k z (B.scale i - 1) ^ 2 * blockFrac m k (B.scale i) ^ 2 / c (B.scale i - 1))⁻¹

/-- `a^♮_z`, the composed weight: `composedPrecision / β_k`. -/
noncomputable def composedWeight (βk : ℝ) (c z : ℕ → ℝ) : ℝ := B.composedPrecision c z / βk

section Defs

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The block-spin average of the values `ψ` (non-leaf blocks, as a function on `ℕ`) and `ψG` (leaves)
over the children of the non-leaf block `i`: `(Qψ)(y)`. -/
noncomputable def childAvg (ψG : Fin B.nLeaf → V) (ψ : ℕ → V) (i : ℕ) : V :=
  (m : ℝ)⁻¹ • ((∑ c ∈ (Finset.range (B.n + 1)).filter (fun c => c ≠ 0 ∧ B.par c = i), ψ c) +
    ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafPar x = i), ψG x)

/-- The integrand of (III.1.4): `∏_y z_{j+1}^N t_j(z_{j+1} ψ(y), (Qψ_j)(y))`, over the non-leaf blocks
`y` (of scale `j + 1`), `t_j(a, b) = g_{c_j}(a - b)`. -/
noncomputable def windowIntegrand (c z : ℕ → ℝ) (ψG : Fin B.nLeaf → V) (ψ : ℕ → V) : ℝ :=
  ∏ i ∈ Finset.range (B.n + 1), z (B.scale i) ^ Module.finrank ℝ V *
    gaussDens (c (B.scale i - 1)) (z (B.scale i) • ψ i - B.childAvg ψG ψ i)

/-- `𝒬^♮_z ψ^G = ∑_x w_x ϖ_{n_x} ψ^G(x)`. -/
noncomputable def composedMean (z : ℕ → ℝ) (ψG : Fin B.nLeaf → V) : V :=
  ∑ x, (blockFrac m k (B.leafScale x) * varpi k z (B.leafScale x)) • ψG x

/-- The Gaussian tree of the block tree: node `i` (of scale `s_i = j + 1`) has scale `z_{s_i}`, precision `c_j`,
constant `μ_i = m⁻¹ ∑ (its leaf children)` and coefficient `m⁻¹`. -/
noncomputable def toGauss (c z : ℕ → ℝ) (ψG : Fin B.nLeaf → V) : GaussTree V where
  par := B.par
  s := fun i => z (B.scale i)
  p := fun i => c (B.scale i - 1)
  μ := fun i => (m : ℝ)⁻¹ • ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafPar x = i), ψG x
  α := fun _ => (m : ℝ)⁻¹

theorem arg_toGauss (c z : ℕ → ℝ) (ψG : Fin B.nLeaf → V) (ψ : ℕ → V) (i : ℕ) :
    (B.toGauss c z ψG).arg B.n ψ i = z (B.scale i) • ψ i - B.childAvg ψG ψ i := by
  unfold GaussTree.arg childAvg toGauss
  simp only
  rw [← Finset.sum_filter, ← Finset.smul_sum, smul_add]
  abel

theorem windowIntegrand_eq (c z : ℕ → ℝ) (ψG : Fin B.nLeaf → V) (ψ : ℕ → V) :
    B.windowIntegrand c z ψG ψ = (B.toGauss c z ψG).Psi B.n ψ := by
  unfold windowIntegrand GaussTree.Psi GaussTree.factor
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [arg_toGauss]
  rfl

section Main

variable (hm : 0 < m) (c z : ℕ → ℝ) (ψG : Fin B.nLeaf → V)
  (hz : ∀ s, k1 < s → s ≤ k → 0 < z s)

include hm hz

theorem A_toGauss : ∀ i, i ≤ B.n →
    (B.toGauss c z ψG).A i = z k * blockFrac m k (B.scale i) * varpi k z (B.scale i - 1) := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    have hk1 : k1 + 1 ≤ k := by have := B.scale_ge 0 (Nat.zero_le _); rw [B.root_scale] at this; exact this
    by_cases h0 : i = 0
    · subst h0
      have hA : (B.toGauss c z ψG).A 0 = 1 := GaussTree.pathCoef_zero _ _
      rw [hA, B.root_scale]
      have := hz k (by omega) le_rfl
      unfold blockFrac
      have hv : varpi k z (k - 1) = (z k)⁻¹ := by
        unfold varpi
        have : k - (k - 1) = 1 := by omega
        simp [this]
      rw [hv]; field_simp; simp
    · have hpl := B.par_lt i hi h0
      have hsp := B.scale_par i hi h0
      have hsk := B.scale_le (B.par i) (by omega)
      have hge := B.scale_ge i hi
      have hih := ih (B.par i) hpl (by omega)
      have hAi : (B.toGauss c z ψG).A i = (m : ℝ)⁻¹ / z (B.scale i) * (B.toGauss c z ψG).A (B.par i) :=
        GaussTree.pathCoef_pos_index _ _ h0 hpl
      rw [hAi, hih, hsp]
      have hzi := hz (B.scale i) (by omega) (by omega)
      have hfrac := blockFrac_succ hm (show B.scale i < k by omega)
      have hv : varpi k z (B.scale i + 1 - 1) = z (B.scale i) * varpi k z (B.scale i - 1) := by
        rw [show B.scale i + 1 - 1 = B.scale i by omega]
        rw [varpi_pred z (by omega) (by omega)]
        field_simp
      rw [hv, ← hfrac]
      field_simp

theorem var_toGauss :
    (B.toGauss c z ψG).var B.n = z k ^ 2 * (B.composedPrecision c z)⁻¹ := by
  unfold GaussTree.var composedPrecision
  rw [inv_inv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [A_toGauss B hm c z ψG hz i (by have := Finset.mem_range.mp hi; omega)]
  simp only [toGauss]
  ring

theorem mean_toGauss :
    (B.toGauss c z ψG).mean B.n = z k • B.composedMean z ψG := by
  unfold GaussTree.mean composedMean
  have h1 : ∀ i ∈ Finset.range (B.n + 1), (B.toGauss c z ψG).A i • (B.toGauss c z ψG).μ i =
      ∑ x ∈ Finset.univ.filter (fun x : Fin B.nLeaf => B.leafPar x = i),
        (z k * (blockFrac m k (B.scale (B.leafPar x)) * varpi k z (B.scale (B.leafPar x) - 1) *
          (m : ℝ)⁻¹)) • ψG x := by
    intro i hi
    rw [A_toGauss B hm c z ψG hz i (by have := Finset.mem_range.mp hi; omega)]
    simp only [toGauss]
    rw [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hxi : B.leafPar x = i := (Finset.mem_filter.mp hx).2
    rw [hxi]; congr 1; ring
  rw [Finset.sum_congr rfl h1]
  rw [Finset.sum_fiberwise_of_maps_to (g := B.leafPar) (s := Finset.univ)
    (t := Finset.range (B.n + 1))
    (f := fun x : Fin B.nLeaf => (z k * (blockFrac m k (B.scale (B.leafPar x)) *
      varpi k z (B.scale (B.leafPar x) - 1) * (m : ℝ)⁻¹)) • ψG x)
    (fun x _ => Finset.mem_range.mpr (by have := B.leafPar_le x; omega))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [smul_smul]
  congr 1
  have hge := B.scale_ge (B.leafPar x) (B.leafPar_le x)
  have hle := B.scale_le (B.leafPar x) (B.leafPar_le x)
  have hfrac := blockFrac_succ hm (show B.scale (B.leafPar x) - 1 < k by omega)
  rw [show B.scale (B.leafPar x) - 1 + 1 = B.scale (B.leafPar x) by omega] at hfrac
  unfold leafScale
  rw [← hfrac]; ring

theorem composedPrecision_pos (hc : ∀ j, k1 ≤ j → j < k → 0 < c j) :
    0 < B.composedPrecision c z := by
  unfold composedPrecision
  refine inv_pos.mpr (Finset.sum_pos ?_ ⟨0, Finset.mem_range.mpr (Nat.succ_pos _)⟩)
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have hge := B.scale_ge i (by omega)
  have hle := B.scale_le i (by omega)
  have := hc (B.scale i - 1) (by omega) (by omega)
  have hw : 0 < blockFrac m k (B.scale i) := by
    unfold blockFrac
    have : (0 : ℝ) < m := by exact_mod_cast hm
    positivity
  have hv : 0 < varpi k z (B.scale i - 1) := by
    unfold varpi
    refine Finset.prod_pos fun i' hi' => ?_
    have := Finset.mem_range.mp hi'
    exact inv_pos.mpr (hz _ (by omega) (by omega))
  positivity

/-- **(III.1.4), the Gaussian chain on the block tree**, for arbitrary positive coefficients `c_j` and
field renormalizations `z_j`: integrating the non-leaf blocks other than the top one (value `u = ψ_k(z)`)
in the product of the one-step Gaussians gives the Gaussian density of `u - 𝒬^♮_z ψ^G` with precision
`β_k a^♮_z`. -/
theorem integral_window_comp (hc : ∀ j, k1 ≤ j → j < k → 0 < c j) (u : V) :
    ∫ x : Fin B.n → V, B.windowIntegrand c z ψG (extVec u x) =
      gaussDens (B.composedPrecision c z) (u - B.composedMean z ψG) := by
  have hs : ∀ i ≤ B.n, 0 < (B.toGauss c z ψG).s i := fun i hi =>
    hz _ (B.scale_ge i hi) (B.scale_le i hi)
  have hp : ∀ i ≤ B.n, 0 < (B.toGauss c z ψG).p i := fun i hi => by
    have := B.scale_ge i hi; have := B.scale_le i hi
    exact hc _ (by omega) (by omega)
  simp_rw [windowIntegrand_eq]
  rw [GaussTree.integral_Psi _ B.n u hs hp B.par_lt]
  have h0 : (B.toGauss c z ψG).s 0 = z k := by
    simp only [toGauss, B.root_scale]
  rw [h0, mean_toGauss B hm c z ψG hz, var_toGauss B hm c z ψG hz, ← smul_sub]
  have hzk : 0 < z k := hz k (by have := B.scale_ge 0 (Nat.zero_le _); rw [B.root_scale] at this; omega) le_rfl
  have hprec := B.composedPrecision_pos hm c z hz hc
  rw [gaussDens_scale (by positivity) hzk]
  congr 1
  field_simp

end Main

end Defs

end BlockTree

/-- Non-vacuity (rule 10): the block tree with the top block `0` of scale `k` and its `m` leaves. -/
def BlockTree.single (m k1 k : ℕ) (hk : k1 + 1 ≤ k) : BlockTree m k1 k where
  n := 0
  scale := fun _ => k
  par := fun _ => 0
  nLeaf := m
  leafPar := fun _ => 0
  root_scale := rfl
  par_lt := fun i hi h0 => absurd (by omega) h0
  scale_par := fun i hi h0 => absurd (by omega) h0
  scale_ge := fun _ _ => hk
  leafPar_le := fun _ => le_rfl
  full := fun i hi => by
    have : i = 0 := by omega
    subst this
    simp

theorem BlockTree.nonempty (m k1 k : ℕ) (hk : k1 + 1 ≤ k) : Nonempty (BlockTree m k1 k) :=
  ⟨BlockTree.single m k1 k hk⟩

/-- A two-level block tree: the top block (scale `k`) has `m - 1` leaves and one non-leaf child
(scale `k - 1`), which has `m` leaves. -/
def BlockTree.twoLevel (m k1 k : ℕ) (hm : 1 ≤ m) (hk : k1 + 2 ≤ k) : BlockTree m k1 k where
  n := 1
  scale := fun i => if i = 0 then k else k - 1
  par := fun _ => 0
  nLeaf := (m - 1) + m
  leafPar := fun x => if (x : ℕ) < m - 1 then 0 else 1
  root_scale := by simp
  par_lt := fun i hi h0 => by omega
  scale_par := fun i hi h0 => by
    have : i = 1 := by omega
    subst this; simp; omega
  scale_ge := fun i hi => by split_ifs <;> omega
  leafPar_le := fun x => by show (if (x : ℕ) < m - 1 then 0 else 1) ≤ 1; split_ifs <;> omega
  full := fun i hi => by
    have hi' : i = 0 ∨ i = 1 := by omega
    have hc : (Finset.univ.filter (fun x : Fin ((m - 1) + m) => (x : ℕ) < m - 1)).card = m - 1 := by
      rw [Fin.card_filter_val_lt]; omega
    rcases hi' with rfl | rfl
    · have h1 : ((Finset.range (1 + 1)).filter (fun c => c ≠ 0 ∧ (fun _ => 0) c = 0)).card = 1 := by
        decide
      have h2 : (Finset.univ.filter (fun x : Fin ((m - 1) + m) =>
          (if (x : ℕ) < m - 1 then 0 else 1) = 0)).card = m - 1 := by
        have e : (Finset.univ.filter (fun x : Fin ((m - 1) + m) =>
            (if (x : ℕ) < m - 1 then 0 else 1) = 0)) =
            Finset.univ.filter (fun x : Fin ((m - 1) + m) => (x : ℕ) < m - 1) := by
          ext x
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          split_ifs with h <;> simp [h]
        rw [e, hc]
      show ((Finset.range (1 + 1)).filter (fun c => c ≠ 0 ∧ (fun _ => 0) c = 0)).card +
        (Finset.univ.filter (fun x : Fin ((m - 1) + m) => (if (x : ℕ) < m - 1 then 0 else 1) = 0)).card = m
      rw [h1, h2]; omega
    · have h1 : ((Finset.range (1 + 1)).filter (fun c => c ≠ 0 ∧ (fun _ => 0) c = 1)).card = 0 := by
        decide
      have h2 : (Finset.univ.filter (fun x : Fin ((m - 1) + m) =>
          (if (x : ℕ) < m - 1 then 0 else 1) = 1)).card = m := by
        have : (Finset.univ.filter (fun x : Fin ((m - 1) + m) =>
            (if (x : ℕ) < m - 1 then 0 else 1) = 1)) =
            Finset.univ \ (Finset.univ.filter (fun x : Fin ((m - 1) + m) => (x : ℕ) < m - 1)) := by
          ext x; simp
        rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, Fintype.card_fin, hc]
        omega
      show ((Finset.range (1 + 1)).filter (fun c => c ≠ 0 ∧ (fun _ => 0) c = 1)).card +
        (Finset.univ.filter (fun x : Fin ((m - 1) + m) => (if (x : ℕ) < m - 1 then 0 else 1) = 1)).card = m
      rw [h1, h2]; omega

theorem BlockTree.nonempty_twoLevel (m k1 k : ℕ) (hm : 1 ≤ m) (hk : k1 + 2 ≤ k) :
    Nonempty (BlockTree m k1 k) :=
  ⟨BlockTree.twoLevel m k1 k hm hk⟩

end Balaban.LargeField