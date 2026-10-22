/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormMomentAlg
public import Balaban.Flow.MomentLimit

/-!
# The moment sum of the second variation of `C₁`

`QsV Gm f = secondVarScalar w ν ξ₂ ξ₃ ζ (f·f) (f·Gm f) (Gm f·Gm f)` is the second variation of `C₁`
in the direction `f ⊗ e_{i₁}`.  Its polarization is
`BsV Gm f g = secondVarScalar w ν ξ₂ ξ₃ ζ (f·g) (f·Gm g) (Gm f·Gm g)` (`polar_QsV`, `Gm` symmetric).
The moment sum `∑_b |b|² BsV Gm 1_b 1_0` over the blocks `b` is
`-ξ₃ w² (R₁ + ν R₂) + (1+ξ₃) ζ w² (-2 R₁ + w R₂) + ν ξ₂ w² R₂`,
with `R₁ = 1_0 · Gm g`, `R₂ = 1_0 · Gm Gm g` the pairings of `Flow.MomentLimit`
(`momentBs_eq`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Flow Finset Matrix

variable {ι : Type*} [Fintype ι]


theorem dot_mulVec_symm (A : Matrix ι ι ℂ) (hA : Aᵀ = A) (f g : ι → ℂ) :
    f ⬝ᵥ (A *ᵥ g) = (A *ᵥ f) ⬝ᵥ g := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

/-- The second variation of `C₁` in the direction `f ⊗ e_{i₁}`. -/
noncomputable def QsV (w : ℂ) (ν ξ₂ ξ₃ ζ : ℝ) (Gm : Matrix ι ι ℂ) (f : ι → ℂ) : ℂ :=
  secondVarScalar w ν ξ₂ ξ₃ ζ (f ⬝ᵥ f) (f ⬝ᵥ (Gm *ᵥ f)) ((Gm *ᵥ f) ⬝ᵥ (Gm *ᵥ f))

/-- Its polarization. -/
noncomputable def BsV (w : ℂ) (ν ξ₂ ξ₃ ζ : ℝ) (Gm : Matrix ι ι ℂ) (f g : ι → ℂ) : ℂ :=
  secondVarScalar w ν ξ₂ ξ₃ ζ (f ⬝ᵥ g) (f ⬝ᵥ (Gm *ᵥ g)) ((Gm *ᵥ f) ⬝ᵥ (Gm *ᵥ g))

theorem polar_QsV (w : ℂ) (ν ξ₂ ξ₃ ζ : ℝ) (Gm : Matrix ι ι ℂ) (hG : Gmᵀ = Gm) (f g : ι → ℂ) :
    (QsV w ν ξ₂ ξ₃ ζ Gm (f + g) - QsV w ν ξ₂ ξ₃ ζ Gm (f - g)) / 4 =
      BsV w ν ξ₂ ξ₃ ζ Gm f g := by
  unfold QsV BsV secondVarScalar
  have h1 : g ⬝ᵥ f = f ⬝ᵥ g := dotProduct_comm _ _
  have h2 : g ⬝ᵥ (Gm *ᵥ f) = f ⬝ᵥ (Gm *ᵥ g) := by
    rw [dot_mulVec_symm Gm hG g f, dotProduct_comm]
  have h3 : (Gm *ᵥ g) ⬝ᵥ (Gm *ᵥ f) = (Gm *ᵥ f) ⬝ᵥ (Gm *ᵥ g) := dotProduct_comm _ _
  simp only [Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct, dotProduct_sub,
    sub_dotProduct, h1, h2, h3]
  ring

theorem secondVarScalar_linear (w : ℂ) (ν ξ₂ ξ₃ ζ : ℝ) (x y z : ℂ) :
    secondVarScalar w ν ξ₂ ξ₃ ζ x y z =
      ((ξ₃ : ℂ) * w + (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * (2 * w) + (ζ : ℂ) ^ 2 * w)) * x +
      (-(ξ₃ : ℂ) * w ^ 2 - (1 + (ξ₃ : ℂ)) * (ζ : ℂ) * (2 * w ^ 2)) * y +
      (-(ξ₃ : ℂ) * ν * w ^ 2 + (1 + (ξ₃ : ℂ)) * (ζ : ℂ) * w ^ 3 + ((ν * ξ₂ : ℝ) : ℂ) * w ^ 2) * z := by
  unfold secondVarScalar; ring

theorem moment_abstract {κ : Type*} [Fintype κ] (c : κ → ℂ) (e : κ → ι → ℂ) (f0 g : ι → ℂ)
    (w : ℂ) (ν ξ₂ ξ₃ ζ : ℝ) (Gm : Matrix ι ι ℂ) (hG : Gmᵀ = Gm)
    (hg : ∀ y, ∑ b, c b * e b y = g y) (hdiag : ∀ b, c b * (e b ⬝ᵥ f0) = 0) :
    ∑ b, c b * BsV w ν ξ₂ ξ₃ ζ Gm (e b) f0 =
      secondVarScalar w ν ξ₂ ξ₃ ζ 0 (f0 ⬝ᵥ (Gm *ᵥ g)) (f0 ⬝ᵥ (Gm *ᵥ (Gm *ᵥ g))) := by
  have hge : g = ∑ b, c b • e b := by
    funext y; simp [hg y |>.symm, Finset.sum_apply]
  have h1 : ∑ b, c b * (e b ⬝ᵥ (Gm *ᵥ f0)) = f0 ⬝ᵥ (Gm *ᵥ g) := by
    have : ∑ b, c b * (e b ⬝ᵥ (Gm *ᵥ f0)) = g ⬝ᵥ (Gm *ᵥ f0) := by
      rw [hge, sum_dotProduct]
      exact Finset.sum_congr rfl fun b _ => by rw [smul_dotProduct, smul_eq_mul]
    rw [this, dot_mulVec_symm Gm hG g f0, dotProduct_comm]
  have h2 : ∑ b, c b * ((Gm *ᵥ e b) ⬝ᵥ (Gm *ᵥ f0)) = f0 ⬝ᵥ (Gm *ᵥ (Gm *ᵥ g)) := by
    have : ∑ b, c b * ((Gm *ᵥ e b) ⬝ᵥ (Gm *ᵥ f0)) = (Gm *ᵥ g) ⬝ᵥ (Gm *ᵥ f0) := by
      rw [hge, Matrix.mulVec_sum, sum_dotProduct]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Matrix.mulVec_smul, smul_dotProduct, smul_eq_mul]
    rw [this, dot_mulVec_symm Gm hG (Gm *ᵥ g) f0, dotProduct_comm]
  unfold BsV
  have hl : ∀ b, c b * secondVarScalar w ν ξ₂ ξ₃ ζ (e b ⬝ᵥ f0) (e b ⬝ᵥ (Gm *ᵥ f0))
      ((Gm *ᵥ e b) ⬝ᵥ (Gm *ᵥ f0)) =
      ((ξ₃ : ℂ) * w + (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * (2 * w) + (ζ : ℂ) ^ 2 * w)) * (c b * (e b ⬝ᵥ f0)) +
      (-(ξ₃ : ℂ) * w ^ 2 - (1 + (ξ₃ : ℂ)) * (ζ : ℂ) * (2 * w ^ 2)) * (c b * (e b ⬝ᵥ (Gm *ᵥ f0))) +
      (-(ξ₃ : ℂ) * ν * w ^ 2 + (1 + (ξ₃ : ℂ)) * (ζ : ℂ) * w ^ 3 + ((ν * ξ₂ : ℝ) : ℂ) * w ^ 2) *
        (c b * ((Gm *ᵥ e b) ⬝ᵥ (Gm *ᵥ f0))) := fun b => by
    rw [secondVarScalar_linear]; ring
  rw [Finset.sum_congr rfl fun b _ => hl b, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, h1, h2,
    Finset.sum_eq_zero fun b _ => hdiag b, secondVarScalar_linear]

end Balaban.Fluctuation

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Flow Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ} {n : ℕ}

/-- The indicator of the block `b`, as a vector on `Ω₁`. -/
noncomputable def indB (G : GeneratingSet d L N₀ K ϱ) (N' m : ℕ) (b : Torus d m) : G.Ω 1 → ℂ :=
  fun y => if blockMap (d := d) (ℓ := N₀ * L ^ K) N' m (y : Torus d (N₀ * L ^ K)) = b then 1 else 0

/-- `|b|²` of a block coordinate (minimal representatives). -/
noncomputable def liftSqB {m : ℕ} (b : Torus d m) : ℂ :=
  ∑ μ : Fin d, ((ZMod.valMinAbs (b μ) : ℤ) : ℂ) ^ 2

theorem blockInd_eq_indB (G : GeneratingSet d L N₀ K ϱ) (N' m : ℕ) [NeZero (N₀ * L ^ K)] :
    blockInd G N' m = indB G N' m 0 := rfl

theorem liftSqB_zero {m : ℕ} [NeZero m] : liftSqB (0 : Torus d m) = 0 := by
  simp [liftSqB]

theorem indB_dot_of_ne {N' m : ℕ} {b : Torus d m} (hb : b ≠ 0) :
    indB G N' m b ⬝ᵥ indB G N' m 0 = 0 := by
  unfold dotProduct indB
  refine Finset.sum_eq_zero fun y _ => ?_
  by_cases h : blockMap (d := d) (ℓ := N₀ * L ^ K) N' m (y : Torus d (N₀ * L ^ K)) = b
  · have : blockMap (d := d) (ℓ := N₀ * L ^ K) N' m (y : Torus d (N₀ * L ^ K)) ≠ 0 := by
      rw [h]; exact hb
    simp [this]
  · simp [h]

theorem sum_liftSqB_indB {m N' : ℕ} [NeZero m] (y : G.Ω 1) :
    ∑ b : Torus d m, liftSqB b * indB G N' m b y =
      liftSqB (blockMap (d := d) (ℓ := N₀ * L ^ K) N' m (y : Torus d (N₀ * L ^ K))) := by
  classical
  unfold indB
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp

theorem greenD_transpose (a : ℕ → ℝ) (ν : ℝ) : (greenD G a ν 0)ᵀ = greenD G a ν 0 := by
  unfold greenD
  rw [Matrix.transpose_nonsing_inv, dirichletOperator_transpose]

/-- **The moment sum of the second variation in terms of the pairings `R₁`, `R₂`.** -/
theorem momentBs_eq {G : GeneratingSet d L N₀ K ϱ} {n : ℕ} [NeZero (N₀ * L ^ (K - n))]
    (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ) :
    ∑ b : Torus d (N₀ * L ^ (K - n)), liftSqB b *
        BsV (wLevel L a n) ν ξ₂ ξ₃ ζ (greenD G a ν 0) (indB G (L ^ n) (N₀ * L ^ (K - n)) b)
          (indB G (L ^ n) (N₀ * L ^ (K - n)) 0) =
      secondVarScalar (wLevel L a n) ν ξ₂ ξ₃ ζ 0
        (blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ
          (greenD G a ν 0 *ᵥ (fun y : G.Ω 1 => liftSum (d := d)
            (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (N₀ * L ^ K)))))
        (blockInd G (L ^ n) (N₀ * L ^ (K - n)) ⬝ᵥ
          (greenD G a ν 0 *ᵥ (greenD G a ν 0 *ᵥ (fun y : G.Ω 1 => liftSum (d := d)
            (fun s : ZMod (N₀ * L ^ K) => ((sb (L ^ n) (N₀ * L ^ (K - n)) s : ℤ) : ℂ) ^ 2)
            (y : Torus d (N₀ * L ^ K)))))) := by
  classical
  refine moment_abstract (c := fun b : Torus d (N₀ * L ^ (K - n)) => liftSqB b)
    (e := fun b => indB G (L ^ n) (N₀ * L ^ (K - n)) b)
    (f0 := indB G (L ^ n) (N₀ * L ^ (K - n)) 0) _ (wLevel L a n) ν ξ₂ ξ₃ ζ (greenD G a ν 0)
    (greenD_transpose a ν) (fun y => ?_) (fun b => ?_)
  · rw [sum_liftSqB_indB]
    unfold liftSqB liftSum
    rfl
  · by_cases hb : b = 0
    · subst hb; simp [liftSqB_zero]
    · rw [indB_dot_of_ne hb, mul_zero]

end Balaban.Fluctuation
