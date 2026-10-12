/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CutCommutator
public import Balaban.Multiscale.CutCube
public import Balaban.Multiscale.CutPointwise
public import Balaban.Multiscale.Analyticity

/-!
# The decoupled Green's operator: definitions and the parametrix identity (LOCALIZATION.md §1.3)

For a centre `z = (j, y₀)` of the cover (`cubeIdx`) let `□_z = box z` be the interaction cube
(`InBox` of half-width `5/2 M₁ ℓ_j`), `c_z = cD z` the multiplication by its indicator,
`H_z(A) = cubeH z` the cut operator of the cube (`cutOperator G a ν (cubeCut G □_z) A`),
`G^{(z)}(A) c_z = cubeG z`, `χ_z = chiD z` and `K_z = χ_z H - H χ_z = Kz z`.  Then
`G*_s(A) = ∑_z s_z χ_z G^{(z)} c_z`, `𝒦_s(A) = ∑_z s_z K_z G^{(z)} c_z` and
`G_s(A) = G*_s (1 - 𝒦_s)⁻¹` (`Gs`).

The algebraic content of the parametrix identity of §1.3 is `parametrix_algebra`:
if `χ_z H G_z = χ_z` for every `z` and `∑ χ_z = 1` then `H G*_1 = 1 - 𝒦_1`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

/-! ### Definitions -/

open Classical in
/-- The interaction cube `□_z` of the centre `z = (j, y₀)`: the periodic box of half-width
`5/2 M₁ ℓ_j` around the centre of the cube (a union of blocks of every layer meeting it). -/
noncomputable def box (q : ℕ × CTorus d L N₁ m₁ K) : Finset (CTorus d L N₁ m₁ K) :=
  Finset.univ.filter fun x => InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) x

theorem mem_box {q : ℕ × CTorus d L N₁ m₁ K} {x : CTorus d L N₁ m₁ K} :
    x ∈ box q ↔ InBox m₁ q.1 q.2 (5 / 2 * (L : ℝ) ^ (q.1 + m₁)) x := by
  classical
  simp [box]

variable (G) in
open Classical in
/-- The multiplication by the indicator `c_z` of the interaction cube. -/
noncomputable def cD (q : ℕ × CTorus d L N₁ m₁ K) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Matrix.diagonal fun x => if (x : CTorus d L N₁ m₁ K) ∈ box q then 1 else 0

variable (G) in
/-- The multiplication by `χ_z`. -/
noncomputable def chiD (q : ℕ × CTorus d L N₁ m₁ K) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Matrix.diagonal fun x => ((chi G q x : ℝ) : ℂ)

variable (G) in
/-- The Neumann cube operator `H_z(A)` of P3 (2.3): the cut operator of the cube cut. -/
noncomputable def cubeH (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  cutOperator G a ν (cubeCut G (box q)) α

variable (G) in
/-- `G^{(z)}(A) c_z`: the inverse of the cube operator after restriction of the source to the
cube. -/
noncomputable def cubeG (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  (cubeH G a ν α q)⁻¹ * cD G q

variable (G) in
/-- The commutator `K_z = χ_z H - H χ_z` (independent of the potential, `Kz_eq`). -/
noncomputable def Kz (a : ℕ → ℝ) (ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  chiD G q * dirichletOperator G a ν 0 - dirichletOperator G a ν 0 * chiD G q

variable (G) in
/-- `G*_s(A) = ∑_z s_z χ_z G^{(z)}(A) c_z`. -/
noncomputable def Gstar (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  ∑ q ∈ cubeIdx G, sProd G s q • (chiD G q * cubeG G a ν α q)

variable (G) in
/-- `𝒦_s(A) = ∑_z s_z K_z G^{(z)}(A) c_z`. -/
noncomputable def Kcal (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  ∑ q ∈ cubeIdx G, sProd G s q • (Kz G a ν q * cubeG G a ν α q)

variable (G) in
/-- **The decoupled Green's operator** `G_s(A) = G*_s(A) (1 - 𝒦_s(A))⁻¹`. -/
noncomputable def Gs (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (s : ℕ × CTorus d L N₁ m₁ K → ℂ) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  Gstar G a ν α s * (1 - Kcal G a ν α s)⁻¹

/-! ### Pure algebra -/

theorem dirichletOperator_eq_add (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) :
    dirichletOperator G a ν α = dirichletOperator G a ν 0 + Matrix.diagonal α := by
  unfold dirichletOperator
  simp

theorem Kz_eq (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    Kz G a ν q = chiD G q * dirichletOperator G a ν α - dirichletOperator G a ν α * chiD G q := by
  have hc : chiD G q * Matrix.diagonal α = Matrix.diagonal α * chiD G q := by
    unfold chiD
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext x; exact mul_comm _ _
  unfold Kz
  rw [dirichletOperator_eq_add a ν α, mul_add, add_mul, hc]
  abel

/-- **The parametrix identity, algebraic form.** If `χ_z H G_z = χ_z` for all centres and the
`χ_z` add up to the identity then `H G*_1 = 1 - 𝒦_1`. -/
theorem parametrix_algebra (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    (hχG : ∀ q ∈ cubeIdx G, chiD G q * dirichletOperator G a ν α * cubeG G a ν α q = chiD G q)
    (hsum : ∑ q ∈ cubeIdx G, chiD G q = 1) :
    dirichletOperator G a ν α * Gstar G a ν α (fun _ => 1) = 1 - Kcal G a ν α (fun _ => 1) := by
  have h1 : ∀ q ∈ cubeIdx G, dirichletOperator G a ν α * (chiD G q * cubeG G a ν α q) =
      chiD G q - Kz G a ν q * cubeG G a ν α q := by
    intro q hq
    have e : Kz G a ν q * cubeG G a ν α q = chiD G q * dirichletOperator G a ν α *
        cubeG G a ν α q - dirichletOperator G a ν α * (chiD G q * cubeG G a ν α q) := by
      rw [Kz_eq a ν α q]; noncomm_ring
    rw [e, hχG q hq]; abel
  unfold Gstar Kcal
  simp only [sProd, Finset.prod_const_one, one_smul]
  rw [Finset.mul_sum, Finset.sum_congr rfl h1, Finset.sum_sub_distrib, hsum]

/-! ### The standing hypotheses -/

/-- The standing hypotheses of the localization setting (LOCALIZATION.md §3.1): `d ≥ 3`, `L ≥ 3`,
cube alignment, `M₁ = L ^ m₁ ≥ 4 L²`, the separation of the cover (`ϱ ≥ 4 d L M₁`) and the
separation `ϱ ≥ R₀` of the Green's function bounds, admissible weights, the mass bound and a torus
with more than five cells of the top cube size. -/
structure DGSetting (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (a : ℕ → ℝ) (ν : ℝ) : Prop where
  hd : 3 ≤ d
  hL : 3 ≤ L
  aligned : CubeAligned G m₁
  hM : 4 * L ^ 2 ≤ L ^ m₁
  cover_sep : (4 * d * L * (L : ℝ) ^ m₁ : ℝ) ≤ ϱ
  sep : 2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ - 1)
  weights : IsAdmissibleWeights K a
  mass : 0 ≤ ν
  massLe : ν * ((L : ℝ) ^ K) ^ 2 ≤ 1
  big : 5 < N₁

/-- The potentials `A` with `|A|₂ ≤ γ₁ = coerciveConst d / 2`, i.e. `ℓ(x)² |A(x)| ≤ γ₁`. -/
def AdmPot (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) (A : G.Ω 1 → ℂ) : Prop :=
  ∀ x, ‖A x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)

/-! ### The cube operators -/

theorem noCutAt_cubeCut (Λ : Finset (CTorus d L N₁ m₁ K)) {p : CTorus d L N₁ m₁ K}
    (h : p ∈ Λ) (h1 : ∀ μ : Fin d, p + Pi.single μ 1 ∈ Λ ∧ p - Pi.single μ 1 ∈ Λ) :
    NoCutAt (cubeCut G Λ) p := by
  intro μ
  constructor
  · intro hc
    rcases (mem_cubeCut G).1 hc with ⟨_, _, h3⟩ | ⟨h1', _, _⟩
    · exact h3 (h1 μ).1
    · exact h1' h
  · intro hc
    rcases (mem_cubeCut G).1 hc with ⟨h2, _, h3⟩ | ⟨h1', _, h3⟩
    · rw [sub_add_cancel] at h3
      exact h3 h
    · exact h1' (by simpa using (h1 μ).2)

theorem dirichlet_row_eq_cut_row (a : ℕ → ℝ) (ν : ℝ) (α : G.Ω 1 → ℂ)
    {cut : Finset (CTorus d L N₁ m₁ K × Fin d)} {x : G.Ω 1}
    (hc : NoCutAt cut (x : CTorus d L N₁ m₁ K)) (u : G.Ω 1 → ℂ) :
    (dirichletOperator G a ν α *ᵥ u) x = (cutOperator G a ν cut α *ᵥ u) x := by
  have h1 := cutOperator_eq G (a := a) (ν := ν) (cut := ∅) (α := α) (u := u)
    (f := dirichletOperator G a ν α *ᵥ u) (by rw [cutOperator_empty]) x
  have h2 := cutOperator_eq G (a := a) (ν := ν) (cut := cut) (α := α) (u := u)
    (f := cutOperator G a ν cut α *ᵥ u) rfl x
  rw [cutFullMatrix_empty] at h1
  rw [cutFullMatrix_mulVec_apply G hc a ν] at h2
  rw [← h1, ← h2]

end Balaban.Localization
