module

public import Balaban.LargeField.Base.BaseFirstCutRecord
public import Balaban.LargeField.Base.BaseComponentDeterminant

/-!
# Local determinant factorization at the first record cut

The crossing-bond cut is made in the local good region. The raw exterior spins remain in
the background datum and in the activity; this result factors only the cut quadratic.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Balaban.Localization Matrix Classical

open Classical in
/-- The local cut operator has a block determinant and split trace logarithm for a selected
base record. Its two coordinate blocks must each contain a site. -/
theorem baseFirstRecord_cut_logDet_factorization_of_goodCubes
    {d N L M : ℕ} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]
    [NeZero N] {ϱ Rk : ℝ} (hnn : ∀ i, i < 1 → nn i = L * nn (i + 1))
    (G : GeneratingSet d L (M * nn 1) 1 ϱ)
    (br : BaseRecord d L (nn 1) Rk)
    (hΩ : ∀ x, x ∈ G.Ω 1 ↔ cubeMap nn L M 1 1 x ∈ br.Omega)
    (regimeB : Prop) (ν δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (φ : Torus d (M * nn 1 * L ^ 1) → Fin N → ℝ)
    (θ : Torus d (M * nn 1 * L ^ (1 - 1)) → Fin N → ℝ)
    (h : Fin N → ℝ)
    (hφ : ∀ x, ∑ i, φ x i ^ 2 = 1) (hh : ∑ i, h i ^ 2 = 1)
    (D : BgData G N)
    (hDΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = (θ (jBlock d L (M * nn 1) 1 1 x) i : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (φ x i : ℂ))
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (h i : ℂ))
    (hsupp : ∀ c : Torus d (nn 1), c ∉ br.P →
      chiPrimeZero nn L M 1 regimeB ν δ₀ h c (φ, θ) = 1)
    (a : ℕ → ℝ) (H : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (U : Set (Torus d (M * nn 1 * L ^ 1))) (hU : IsFirstBlockUnion G U)
    (hU0 : ∃ z : G.Ω 1, (z : Torus d (M * nn 1 * L ^ 1)) ∈ U)
    (hUc : ∃ z : G.Ω 1, (z : Torus d (M * nn 1 * L ^ 1)) ∉ U)
    (s : FineBond d L (M * nn 1) → ℂ) (hs : s ∈ baseParamNbhd G 0)
    (hz : CrossZero G U s) :
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (bgField G a (if regimeB then ν else 0) D (z, i)).re
    let P : G.Ω 1 × Fin N → Prop := fun p =>
      (p.1 : Torus d (M * nn 1 * L ^ 1)) ∈ U
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a (if regimeB then ν else 0)
        (bgMult G a (if regimeB then ν else 0) D) s)
    let AI := A.submatrix (Subtype.val : {p // P p} → _) Subtype.val
    let AJ := A.submatrix (Subtype.val : {p // ¬ P p} → _) Subtype.val
    A.det = Complex.exp (logMat A).trace ∧
      AI.det = Complex.exp (logMat AI).trace ∧
      A.det = AI.det * AJ.det := by
  classical
  dsimp only
  let S := baseSpinSupport_of_baseRecord hnn G br hΩ regimeB ν δ₀ hδ₀
    φ θ h hφ hh D hDΨ hDc hDh hsupp
  let e : G.Ω 1 → Fin N → ℝ := fun z i =>
    (bgField G a (if regimeB then ν else 0) D (z, i)).re
  let α := bgMult G a (if regimeB then ν else 0) D
  let A := baseOp N (fun z i => (e z i : ℂ))
    (baseHamiltonian G a (if regimeB then ν else 0) α s)
  let P : G.Ω 1 × Fin N → Prop := fun p =>
    (p.1 : Torus d (M * nn 1 * L ^ 1)) ∈ U
  have he : ∀ z, ∑ i, e z i ^ 2 = 1 := fun z =>
    (spins_near_background (G := G) H S hΛ1 hΛ2 z).1
  have hα : ∀ z, ‖α z‖ ≤ 1 / (8 * (L : ℝ) ^ 2) :=
    baseFirstCut_multiplier_bound G a φ h D H S hΛ1
  have hd : 0 < d := by have := H.hd; omega
  have hη : (0 : ℝ) ≤ baseCoercivity L / (8 * d) := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    have hcpos := baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L))
    positivity
  have hc : 0 < baseCoercivity L / 2 :=
    half_pos (baseCoercivity_pos (Nat.pos_of_ne_zero (NeZero.ne L)))
  have hA : IsCoercive A (baseCoercivity L / 2) :=
    baseOp_isCoercive_of_close G H.mass H.weights hα le_rfl hη hs e he
  have hR : ResOK A := resOK_baseOp G H.mass H.weights hα le_rfl hη hs e he
  have hRI : ResOK (A.submatrix (Subtype.val : {p // P p} → _) Subtype.val) := by
    have hcomp : IsCoercive (A.submatrix (Subtype.val : {p // P p} → _) Subtype.val)
        (baseCoercivity L / 2) := isCoercive_submatrix hA Subtype.val Subtype.val_injective
    intro x hx
    have hcx : 0 < baseCoercivity L / 2 + x := by linarith
    rw [add_comm]
    exact isUnit_of_isCoercive hcx (hcomp.add_smul_one x)
  have hRJ : ResOK (A.submatrix (Subtype.val : {p // ¬ P p} → _) Subtype.val) := by
    have hcomp : IsCoercive (A.submatrix (Subtype.val : {p // ¬ P p} → _) Subtype.val)
        (baseCoercivity L / 2) := isCoercive_submatrix hA Subtype.val Subtype.val_injective
    intro x hx
    have hcx : 0 < baseCoercivity L / 2 + x := by linarith
    rw [add_comm]
    exact isUnit_of_isCoercive hcx (hcomp.add_smul_one x)
  have : Nonempty (G.Ω 1 × Fin N) := ⟨(hU0.choose, 0)⟩
  have : Nonempty {p : G.Ω 1 × Fin N // P p} :=
    ⟨⟨(hU0.choose, 0), hU0.choose_spec⟩⟩
  have : Nonempty {p : G.Ω 1 × Fin N // ¬ P p} :=
    ⟨⟨(hUc.choose, 0), hUc.choose_spec⟩⟩
  have hblock : BlockDiag P A := baseOp_blockDiag G hU a
    (if regimeB then ν else 0) α hz e
  exact det_eq_exp_trace_logMat_and_mul_blocks P hblock hR hRI hRJ

end Balaban.LargeField
