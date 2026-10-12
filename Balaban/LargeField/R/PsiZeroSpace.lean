/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.PsiZeroSmooth
public import Balaban.LargeField.R.ZeroDomainCoercive

/-!
# Perturbations supported on `Z₀`

The variable of the problem (2.34) is `ψ_k↾Z₀`; `SuppSpace Zf N` is the Euclidean space `ℝ^{Zf × N}`,
`mergeField ψ_k u` is the block field equal to `u` on `Zf` and to `ψ_k` off `Zf`, `extSupp` the zero extension and
`dirichletForm` the form `⟨v, -Δ₁ v⟩` of the zero extension.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

section Space

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L]

/-- The space of perturbations supported in the finite set `Zf` of `k`-blocks. -/
abbrev SuppSpace (Zf : Finset (Torus d (N₀ * L ^ (k - k)))) (N : ℕ) : Type :=
  EuclideanSpace ℝ (↥Zf × Fin N)

variable (Zf : Finset (Torus d (N₀ * L ^ (k - k))))

/-- The block field equal to `u` on `Zf` and to `ψ_k` off `Zf` (the variable of (2.34) is `ψ_k↾Z₀`). -/
def mergeField (ψk : BlockField d L N₀ k N) (u : SuppSpace Zf N) : BlockField d L N₀ k N :=
  fun z i => if h : z ∈ Zf then u (⟨z, h⟩, i) else ψk z i

/-- The restriction of a block field to `Zf`. -/
def restrictSupp (ψ : BlockField d L N₀ k N) : SuppSpace Zf N :=
  WithLp.toLp 2 fun p => ψ p.1 p.2

/-- The constant configuration `ψ₀` on `Zf`. -/
def constSupp (v : EuclideanSpace ℝ (Fin N)) : SuppSpace (L := L) (N₀ := N₀) (k := k) Zf N :=
  WithLp.toLp 2 fun p => v p.2

/-- Zero extension of a perturbation to all `k`-blocks. -/
def extSupp (v : SuppSpace Zf N) (z : Torus d (N₀ * L ^ (k - k))) : EuclideanSpace ℝ (Fin N) :=
  if h : z ∈ Zf then WithLp.toLp 2 fun i => v (⟨z, h⟩, i) else 0

/-- The Dirichlet form `∑_x ∑_μ ‖ṽ(x + e_μ) - ṽ(x)‖²` of the zero extension. -/
noncomputable def dirichletForm (v : SuppSpace Zf N) : ℝ :=
  ∑ x, ∑ μ : Fin d, ‖extSupp Zf v (x + Pi.single μ 1) - extSupp Zf v x‖ ^ 2

variable {Zf}

theorem mergeField_of_not_mem {ψk : BlockField d L N₀ k N} {u : SuppSpace Zf N} {z}
    (hz : z ∉ Zf) : mergeField Zf ψk u z = ψk z := by
  funext i; simp [mergeField, hz]

theorem mergeField_of_mem {ψk : BlockField d L N₀ k N} {u : SuppSpace Zf N} {z} (hz : z ∈ Zf) (i : Fin N) :
    mergeField Zf ψk u z i = u (⟨z, hz⟩, i) := by
  simp [mergeField, hz]

theorem mergeField_restrict {ψk ψ : BlockField d L N₀ k N} (h : ∀ z, z ∉ Zf → ψ z = ψk z) :
    mergeField Zf ψk (restrictSupp Zf ψ) = ψ := by
  funext z i
  by_cases hz : z ∈ Zf
  · simp [mergeField, hz, restrictSupp]
  · simp [mergeField, hz, h z hz]

theorem restrict_mergeField (ψk : BlockField d L N₀ k N) (u : SuppSpace Zf N) :
    restrictSupp Zf (mergeField Zf ψk u) = u := by
  ext ⟨z, i⟩
  simp [restrictSupp, mergeField]

theorem mergeField_mergeField (ψk : BlockField d L N₀ k N) (u w : SuppSpace Zf N) :
    mergeField Zf (mergeField Zf ψk u) w = mergeField Zf ψk w := by
  funext z i
  by_cases hz : z ∈ Zf <;> simp [mergeField, hz]

theorem contDiff_mergeField {n : WithTop ℕ∞} (ψk : BlockField d L N₀ k N) :
    ContDiff ℝ n (mergeField Zf ψk) := by
  refine contDiff_pi.2 fun z => contDiff_pi.2 fun i => ?_
  by_cases hz : z ∈ Zf
  · have : (fun u : SuppSpace Zf N => mergeField Zf ψk u z i) = fun u => u (⟨z, hz⟩, i) :=
      funext fun u => mergeField_of_mem hz i
    rw [this]
    exact (EuclideanSpace.proj (⟨z, hz⟩, i) : SuppSpace Zf N →L[ℝ] ℝ).contDiff
  · have : (fun u : SuppSpace Zf N => mergeField Zf ψk u z i) = fun _ => ψk z i :=
      funext fun u => by simp [mergeField, hz]
    rw [this]
    exact contDiff_const

theorem sq_norm_supp (u : SuppSpace Zf N) : ‖u‖ ^ 2 = ∑ z : ↥Zf, ∑ i : Fin N, u (z, i) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  simp

theorem sq_norm_euc (v : EuclideanSpace ℝ (Fin N)) : ‖v‖ ^ 2 = ∑ i, v i ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp

/-- On a block of `Zf` the merged field is within `‖u - ψ₀‖` of `ψ₀`. -/
theorem norm_merge_sub_le (ψk : BlockField d L N₀ k N) (u : SuppSpace Zf N) (v : EuclideanSpace ℝ (Fin N))
    {z : Torus d (N₀ * L ^ (k - k))} (hz : z ∈ Zf) :
    ‖WithLp.toLp 2 (mergeField Zf ψk u z) - v‖ ≤ ‖u - constSupp Zf v‖ := by
  apply le_of_sq_le_sq _ (norm_nonneg _)
  rw [sq_norm_euc, sq_norm_supp]
  calc ∑ i, (WithLp.toLp 2 (mergeField Zf ψk u z) - v) i ^ 2
      = ∑ i, (u - constSupp Zf v) (⟨z, hz⟩, i) ^ 2 := by
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [mergeField_of_mem hz, constSupp]
    _ ≤ ∑ z' : ↥Zf, ∑ i, (u - constSupp Zf v) (z', i) ^ 2 :=
        Finset.single_le_sum (f := fun z' : ↥Zf => ∑ i, (u - constSupp Zf v) (z', i) ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ (⟨z, hz⟩ : ↥Zf))

/-- Conversely, closeness on every block of `Zf` bounds the norm. -/
theorem norm_restrict_sub_le (ψ : BlockField d L N₀ k N) (v : EuclideanSpace ℝ (Fin N)) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (h : ∀ z ∈ Zf, ‖WithLp.toLp 2 (ψ z) - v‖ ≤ ρ) :
    ‖restrictSupp Zf ψ - constSupp Zf v‖ ≤ Real.sqrt (Zf.card) * ρ := by
  apply le_of_sq_le_sq _ (by positivity)
  rw [sq_norm_supp, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  calc ∑ z : ↥Zf, ∑ i, (restrictSupp Zf ψ - constSupp Zf v) (z, i) ^ 2
      = ∑ z : ↥Zf, ‖WithLp.toLp 2 (ψ z) - v‖ ^ 2 := by
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [sq_norm_euc]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp [restrictSupp, constSupp]
    _ ≤ ∑ z : ↥Zf, ρ ^ 2 :=
        Finset.sum_le_sum fun z _ => pow_le_pow_left₀ (norm_nonneg _) (h z z.2) 2
    _ = (Zf.card : ℝ) * ρ ^ 2 := by simp

theorem sum_sq_extSupp (v : SuppSpace Zf N) : ∑ x, ‖extSupp Zf v x‖ ^ 2 = ‖v‖ ^ 2 := by
  classical
  rw [sq_norm_supp]
  have h1 : ∑ x, ‖extSupp Zf v x‖ ^ 2 = ∑ x ∈ Zf, ‖extSupp Zf v x‖ ^ 2 := by
    refine (Finset.sum_subset (Finset.subset_univ _) fun x _ hx => ?_).symm
    simp [extSupp, hx]
  rw [h1, ← Finset.sum_coe_sort Zf]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [sq_norm_euc]
  simp [extSupp, z.2]

end Space

end Balaban.LargeField
