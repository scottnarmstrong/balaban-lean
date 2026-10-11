module

public import Balaban.Frozen.Model.Torus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

/-!
# The lattice Laplacian on the torus as a matrix

`latticeLaplacian d ℓ ν = -Δ + ν` on `Torus d ℓ` (nearest neighbours, periodic):
`((-Δ + ν) φ)(x) = ∑_μ (2 φ(x) - φ(x + e_μ) - φ(x - e_μ)) + ν φ(x)`.
Its quadratic form is `φᵀ(-Δ+ν)φ = ∑_x ∑_μ (φ(x + e_μ) - φ(x))² + ν ∑_x φ(x)²`, i.e. twice the
quadratic part of the frozen energy `Balaban.energy` (`Balaban/Frozen/Model/Energy.lean`) for a
scalar field. For `ν > 0` the matrix is symmetric positive definite (`latticeLaplacian_posDef`).
-/

@[expose] public section

namespace Balaban

open Matrix

variable {d ℓ : ℕ} [NeZero ℓ]

/-- The shift matrix `(S_μ φ)(x) = φ(x + e_μ)`. -/
def shiftMatrix (μ : Fin d) : Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  fun x y => if y = x + Pi.single μ 1 then 1 else 0

theorem shiftMatrix_mulVec (μ : Fin d) (φ : Torus d ℓ → ℝ) (x : Torus d ℓ) :
    (shiftMatrix μ *ᵥ φ) x = φ (x + Pi.single μ 1) := by
  simp [shiftMatrix, Matrix.mulVec, dotProduct]

/-- The matrix of `-Δ + ν` on the torus. -/
def latticeLaplacian (d ℓ : ℕ) [NeZero ℓ] (ν : ℝ) : Matrix (Torus d ℓ) (Torus d ℓ) ℝ :=
  ((2 * d + ν) • (1 : Matrix (Torus d ℓ) (Torus d ℓ) ℝ)) -
    ∑ μ : Fin d, (shiftMatrix μ + (shiftMatrix μ)ᵀ)

theorem sum_shift (e : Torus d ℓ) (f : Torus d ℓ → ℝ) : ∑ x, f (x + e) = ∑ x, f x :=
  Equiv.sum_comp (Equiv.addRight e) f

theorem latticeLaplacian_mulVec (ν : ℝ) (φ : Torus d ℓ → ℝ) (x : Torus d ℓ) :
    (latticeLaplacian d ℓ ν *ᵥ φ) x =
      ∑ μ : Fin d, (2 * φ x - φ (x + Pi.single μ 1) - φ (x - Pi.single μ 1)) + ν * φ x := by
  have hT : ∀ μ : Fin d, ((shiftMatrix μ)ᵀ *ᵥ φ) x = φ (x - Pi.single μ 1) := by
    intro μ
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, shiftMatrix]
    have : ∀ y : Torus d ℓ, (x = y + Pi.single μ 1) ↔ (y = x - Pi.single μ 1) := fun y => by
      rw [eq_sub_iff_add_eq, eq_comm]
    simp only [this]
    simp
  simp only [latticeLaplacian, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Matrix.sum_mulVec, Finset.sum_apply,
    Matrix.add_mulVec, Pi.add_apply, shiftMatrix_mulVec, hT]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  ring

theorem latticeLaplacian_isHermitian (ν : ℝ) : (latticeLaplacian d ℓ ν).IsHermitian := by
  simp only [Matrix.IsHermitian, latticeLaplacian, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_one, Matrix.transpose_sum,
    Matrix.transpose_add, Matrix.transpose_transpose]
  congr 1
  exact Finset.sum_congr rfl fun μ _ => add_comm _ _

/-- The quadratic form: `φᵀ(-Δ+ν)φ = ∑_x ∑_μ (φ(x+e_μ) - φ(x))² + ν ∑_x φ(x)²`. -/
theorem latticeLaplacian_quadratic (ν : ℝ) (φ : Torus d ℓ → ℝ) :
    φ ⬝ᵥ latticeLaplacian d ℓ ν *ᵥ φ =
      ∑ x, ∑ μ : Fin d, (φ (x + Pi.single μ 1) - φ x) ^ 2 + ν * ∑ x, φ x ^ 2 := by
  have hs : ∀ μ : Fin d, ∑ x, φ (x + Pi.single μ 1) ^ 2 = ∑ x, φ x ^ 2 := fun μ =>
    sum_shift (Pi.single μ 1) (fun x => φ x ^ 2)
  have hm : ∀ μ : Fin d, ∑ x, φ (x - Pi.single μ 1) * φ x = ∑ x, φ x * φ (x + Pi.single μ 1) := by
    intro μ
    refine (sum_shift (Pi.single μ 1) (fun x => φ (x - Pi.single μ 1) * φ x)).symm.trans ?_
    refine Finset.sum_congr rfl fun x _ => ?_
    simp
  simp only [dotProduct, latticeLaplacian_mulVec]
  have hμ : ∀ μ : Fin d, ∑ x, φ x * (2 * φ x - φ (x + Pi.single μ 1) - φ (x - Pi.single μ 1)) =
      ∑ x, (φ (x + Pi.single μ 1) - φ x) ^ 2 := by
    intro μ
    have e1 : ∑ x, φ x * (2 * φ x - φ (x + Pi.single μ 1) - φ (x - Pi.single μ 1)) =
        2 * (∑ x, φ x ^ 2) - (∑ x, φ x * φ (x + Pi.single μ 1)) -
          (∑ x, φ (x - Pi.single μ 1) * φ x) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    have e2 : ∑ x : Torus d ℓ, (φ (x + Pi.single μ 1) - φ x) ^ 2 =
        (∑ x : Torus d ℓ, φ (x + Pi.single μ 1) ^ 2) + (∑ x : Torus d ℓ, φ x ^ 2) - 2 * (∑ x : Torus d ℓ, φ x * φ (x + Pi.single μ 1)) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [e1, e2, hs, hm]
    ring
  simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum]
  rw [Finset.sum_congr rfl fun μ _ => hμ μ, Finset.sum_comm, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun x _ => by ring

theorem latticeLaplacian_posDef {ν : ℝ} (hν : 0 < ν) : (latticeLaplacian d ℓ ν).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨latticeLaplacian_isHermitian ν, ?_⟩
  intro φ hφ
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hφ
  have hx₀' : φ x₀ ≠ 0 := hx₀
  have hpos : 0 < ∑ x, φ x ^ 2 :=
    lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun x => φ x ^ 2)
      (fun x _ => sq_nonneg _) (Finset.mem_univ x₀))
  simp only [star_trivial]
  rw [latticeLaplacian_quadratic]
  have : 0 ≤ ∑ x, ∑ μ : Fin d, (φ (x + Pi.single μ 1) - φ x) ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  nlinarith [mul_pos hν hpos]

end Balaban
