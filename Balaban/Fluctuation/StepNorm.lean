/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepNormGauss
public import Balaban.Fluctuation.StepIdentityInhabited
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The block kernel `∏ t_k` of one RG step and its normalisation (FLUCTUATION.md Definition 2.1, (2.5))

The kernel `S.tKernel ψ` of `StepObjects` is written on the lifted fields of the fine torus.  Here it
is put in the block-product form `∏_{z ∈ T^{(k+1)}_L} t_k(θ(z), (Qψ)(z))` and normalised:

* `StepSetting.qpsi ψ`: `(Qψ)(z) = L^{-d} ∑_{x ∈ B_{k+1}(z)} ψ(x)` on the block lattice;
* `StepSetting.tKernel_eq_prod`: `tKernel ψ = ∏_z tBlock c (θ z) (Qψ z)` when the datum `θ` of `𝔹'_{k+1}`
  is the lift of a real block field;
* `StepSetting.integral_tKernelAt`: `∫ ∏_z t_k(θ(z), (Qψ)(z)) dθ = 1`, the integral over the block
  fields `θ ∈ (ℝ^N)^{T^{(k+1)}_L}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban.SmallField.Def6 Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField Finset MeasureTheory
open scoped Real

/-- The block lattice `T^{(k+1)}_L`. -/
abbrev BlockLat (d L N₁ m₁ k : ℕ) : Type := Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- The block of the fine site `x` of level `k + 1`. -/
abbrev jb (x : CTorus d L N₁ m₁ (k + 1)) : BlockLat d L N₁ m₁ k :=
  jBlock d L (N₁ * L ^ m₁) (k + 1) (k + 1) x

/-- A block field `θ ∈ (ℝ^N)^{T^{(k+1)}_L}` as a field of the fine torus (constant on blocks). -/
noncomputable def liftθ (θ : BlockLat d L N₁ m₁ k → Rn N) :
    CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ := fun x i => ((θ (jb x) i : ℝ) : ℂ)

/-- **`(Qψ)(z) = L^{-d} ∑_{x ∈ B_{k+1}(z)} ψ(x)`** for the old spin `ψ` on the unit lattice
(`L^{(k+1)d}` fine sites per block). -/
noncomputable def qpsi (ψ : S.E) (z : BlockLat d L N₁ m₁ k) : Rn N :=
  WithLp.toLp 2 fun i => (((L : ℝ) ^ (k + 1)) ^ d)⁻¹ *
    ∑ y ∈ (blockFibre (L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z :
        Finset (CTorus d L N₁ m₁ (k + 1))), liftU S.hG' ψ y i

theorem blockMean_dataU (ψ : S.E) (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    blockMean S.G' (k + 1) (fun y => (S.dataU ψ).Ψ y i) x = ((S.qpsi ψ (jb x) i : ℝ) : ℂ) := by
  unfold blockMean qpsi
  rw [blk_eq_fibre S.G']
  simp only [S.dataU_Ψ]
  push_cast
  rfl

theorem sum_jb {M : Type*} [AddCommMonoid M] [Module ℝ M] (F : BlockLat d L N₁ m₁ k → M) :
    ∑ x : CTorus d L N₁ m₁ (k + 1), F (jb x) =
      (((L : ℝ) ^ (k + 1)) ^ d) • ∑ z, F z := by
  classical
  have h := Finset.sum_fiberwise (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (fun x => jb x) (fun x => F (jb x))
  rw [← h, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  have hz : ∀ x ∈ (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => jb x = z),
      F (jb x) = F z := fun x hx => by rw [(Finset.mem_filter.1 hx).2]
  rw [Finset.sum_congr rfl hz, Finset.sum_const]
  have hc := card_blockFibre (d := d) (N := L ^ (k + 1))
    (ℓ := N₁ * L ^ m₁ * L ^ (k + 1)) (m := N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))
    (side_eq (N₀ := N₁ * L ^ m₁) (L := L) (le_refl (k + 1))) z
  have : (Finset.univ.filter fun x : CTorus d L N₁ m₁ (k + 1) => jb x = z) =
      blockFibre (L ^ (k + 1)) (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) z := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_blockFibre]
    rfl
  rw [this, hc, ← Nat.cast_smul_eq_nsmul ℝ]
  push_cast
  rfl

theorem coupling_eq (θ : BlockLat d L N₁ m₁ k → Rn N) (ψ : S.E) :
    coupling S.G' S.a₁ (k + 1) (liftθ θ) (S.dataU ψ).Ψ =
      (1 / 2) * (S.a₁ / ((L : ℝ) ^ (k + 1)) ^ 2) *
        ((((L : ℝ) ^ (k + 1)) ^ d) * ∑ z, ‖θ z - S.qpsi ψ z‖ ^ 2) := by
  unfold coupling
  congr 1
  have hx : ∀ x : CTorus d L N₁ m₁ (k + 1), ∑ i : Fin N,
      ‖liftθ θ x i - blockMean S.G' (k + 1) (fun y => (S.dataU ψ).Ψ y i) x‖ ^ 2 =
      ‖θ (jb x) - S.qpsi ψ (jb x)‖ ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [S.blockMean_dataU]
    simp only [liftθ, PiLp.sub_apply, Real.norm_eq_abs]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl fun x _ => hx x]
  have := sum_jb (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
    (fun z => ‖θ z - S.qpsi ψ z‖ ^ 2)
  simpa [smul_eq_mul] using this

theorem unitPts_eq_univ : S.U = ↥(unitPts S.G') := rfl

theorem card_U : Fintype.card S.U =
    (N₁ * L ^ m₁ * L ^ (k + 1 - k)) ^ d := by
  have h : (unitPts S.G') = Finset.univ := by
    refine Finset.eq_univ_of_forall fun b => ?_
    obtain ⟨x, rfl⟩ := unitBlock_surj (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) b
    exact (mem_unitPts S.G').2 ⟨x, S.hG'.mem_layer x, rfl⟩
  have h2 : Fintype.card S.U = Fintype.card (UnitTorus d L N₁ m₁ k) := by
    rw [Fintype.card_subtype]
    simp [h]
  rw [h2]
  simp [UnitTorus, Torus]

theorem card_block : Fintype.card (BlockLat d L N₁ m₁ k) = (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) ^ d := by
  simp [BlockLat, Torus]

theorem nBlocks_eq : S.nBlocks = (Fintype.card (BlockLat d L N₁ m₁ k) : ℝ) := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  unfold nBlocks nU
  rw [S.card_U, card_block (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)]
  have h1 : k + 1 - k = 1 := by omega
  have h2 : k + 1 - (k + 1) = 0 := by omega
  rw [h1, h2]
  push_cast
  simp only [pow_zero, mul_one, pow_one]
  rw [mul_pow]
  field_simp

/-- **The kernel `∏_z t_k(θ(z), (Qψ)(z))`** of Definition 2.1 for a real block field `θ`. -/
noncomputable def tKernelAt (θ : BlockLat d L N₁ m₁ k → Rn N) (ψ : S.E) : ℝ :=
  ∏ z, tBlock S.cKernel N (θ z) (S.qpsi ψ z)

/-- **The block-product form of the kernel** (Definition 2.1): if the datum `θ = D'.Ψ` is the lift of
a real block field, `tKernel ψ = ∏_z t_k(θ(z), (Qψ)(z))`. -/
theorem tKernel_eq_prod (ha₁ : 0 < S.a₁) (hβ : 0 < S.β) (θ : BlockLat d L N₁ m₁ k → Rn N)
    (hθ : ∀ x i, S.D'.Ψ x i = ((θ (jb x) i : ℝ) : ℂ)) (ψ : S.E) :
    S.tKernel ψ = S.tKernelAt θ ψ := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hD : S.D'.Ψ = liftθ θ := funext fun x => funext fun i => hθ x i
  have hc : 0 ≤ S.cKernel := by
    unfold cKernel; positivity
  have hpow : ((S.cKernel / (2 * π)) ^ ((N : ℝ) / 2)) ^ Fintype.card (BlockLat d L N₁ m₁ k) =
      (S.cKernel / (2 * π)) ^ ((N : ℝ) * S.nBlocks / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), S.nBlocks_eq]
    congr 1
    ring
  unfold tKernel tKernelAt tBlock
  rw [hD, S.coupling_eq, Finset.prod_mul_distrib, Finset.prod_const, ← Real.exp_sum,
    Finset.card_univ, hpow]
  congr 2
  rw [← Finset.mul_sum]
  unfold cKernel
  field_simp

/-- **Normalisation of the block kernel**: `∫ ∏_z t_k(θ(z), (Qψ)(z)) dθ = 1`. -/
theorem integral_tKernelAt (ha₁ : 0 < S.a₁) (hβ : 0 < S.β) (ψ : S.E) :
    ∫ θ : BlockLat d L N₁ m₁ k → Rn N, S.tKernelAt θ ψ = 1 := by
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc : 0 < S.cKernel := by
    unfold cKernel; positivity
  exact integral_prod_tBlock hc N (S.qpsi ψ)

end StepSetting

end Balaban.Fluctuation
