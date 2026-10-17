module

public import Balaban.LargeField.Base.BaseSupport
public import Balaban.LargeField.Base.BaseChartIdentity

/-!
# A first-step chart on the good region of a selected base record

The chart centre uses the block field in the good region and the fixed raw spins on its collar.
The selected record requires good tests only outside its failed set.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale SphereChart MeasureTheory

open Classical in
/-- A spin in the good region of a selected first record lies in the hemisphere of its
local background. This uses only the good tests outside the record's `P` set. -/
theorem baseFirstRecord_inner_pos_of_goodCubes
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
    (x : G.Ω 1) :
    0 < inner ℝ
      (WithLp.toLp 2 (fun i : Fin N =>
        (bgField G a (if regimeB then ν else 0) D (x, i)).re) :
          EuclideanSpace ℝ (Fin N))
      (WithLp.toLp 2 (φ x) : EuclideanSpace ℝ (Fin N)) := by
  have S := baseSpinSupport_of_baseRecord hnn G br hΩ regimeB ν δ₀ hδ₀
    φ θ h hφ hh D hDΨ hDc hDh hsupp
  have hp := (spins_near_background (G := G) H S hΛ1 hΛ2 x).2.2.1
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simpa [dotProduct, mul_comm] using hp

end Balaban.LargeField
