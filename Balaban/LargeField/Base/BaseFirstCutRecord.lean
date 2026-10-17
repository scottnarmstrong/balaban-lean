module

public import Balaban.LargeField.Base.BaseFirstCutPositive
public import Balaban.LargeField.Base.BaseSupport

/-!
# Positive first cut Hessian on a selected base record

Only good cubes outside the failed set and the fixed raw collar enter the local support
argument. The cut may divide the local coordinates into integrated and retained subsets.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Green
open Balaban.LargeField.Base Matrix

open Classical in
/-- The real first cut Hessian and both principal blocks are positive at the local record
centre. No global all-good test is assumed. -/
theorem baseFirstRecord_cut_posDef_of_goodCubes
    {d N L M : ℕ} {nn : ℕ → ℕ} [∀ k, NeZero (nn k)] [NeZero M] [NeZero L]
    {ϱ Rk : ℝ} (hnn : ∀ i, i < 1 → nn i = L * nn (i + 1))
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
    (s : FineBond d L (M * nn 1) → ℂ) (hs : s ∈ baseParamNbhd G 0)
    (hsr : ∀ b ∈ baseCutBonds G, (s b).im = 0)
    (P : G.Ω 1 × Fin N → Prop) :
    let e : G.Ω 1 → Fin N → ℝ := fun z i =>
      (bgField G a (if regimeB then ν else 0) D (z, i)).re
    let A := baseOp N (fun z i => (e z i : ℂ))
      (baseHamiltonian G a (if regimeB then ν else 0)
        (bgMult G a (if regimeB then ν else 0) D) s)
    let K := A.map Complex.re
    let vI : {p // P p} → G.Ω 1 × Fin N := Subtype.val
    let vJ : {p // ¬ P p} → G.Ω 1 × Fin N := Subtype.val
    K.PosDef ∧ (K.submatrix vI vI).PosDef ∧ (K.submatrix vJ vJ).PosDef := by
  have S := baseSpinSupport_of_baseRecord hnn G br hΩ regimeB ν δ₀ hδ₀
    φ θ h hφ hh D hDΨ hDc hDh hsupp
  exact baseFirstCut_posDef_of_spinSupport G a φ h D H S hΛ1 hΛ2 s hs hsr P

end Balaban.LargeField
