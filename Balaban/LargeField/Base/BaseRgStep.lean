module

public import Balaban.Flow.MatrixInftyAnalytic
public import Balaban.Flow.PhysicalStepThreshold

/-!
# The counterterm system of the first step (`k = 0`)

The flow objects of `Balaban.Flow` are stated for an arbitrary step index `k`; the step `0 → 1` is the
case `k = 0`, with bound `q^{k+1} = q`.  The linear part of the system (P4 (5.21)) at the first step is
the constant matrix `matrixInfty a v τ c₁ c₂ ε` at the unrenormalized values `a = a_{1,u}`,
`v = ν_{1,u} = ν L²`; the dependence on `ξ` of `a_{1}, ν_{1}` is carried by the nonlinear part.

* `baseRgMatrix`: this constant matrix;
* `baseRgMatrix_triangularBounds`: Lemma 3.1 for it, on the real range `InftyRange`;
* `baseRg_step`: `physical_rg_step_of_large_beta` at `k = 0` for this matrix: existence, uniqueness in the
  polydisc, analyticity in the data, reality, and the bound `‖ξ⁰‖ ≤ C_ξ β⁻¹ q`.  The analytic and bounded
  nonlinearities `c, f` (hypothesis (B1), from the localized expansions of the first step) are hypotheses.
-/

@[expose] public section

namespace Balaban.LargeField

open Metric Set Balaban.Flow

/-- The linear part of the counterterm system at the first step, at the unrenormalized values. -/
noncomputable def baseRgMatrix (a v τ c₁ c₂ ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  matrixInfty (a : ℂ) (v : ℂ) (τ : ℂ) (c₁ : ℂ) (c₂ : ℂ) (ε : ℂ)

/-- Lemma 3.1 for the first step's matrix: on the real parameter range the matrix is triangular with the
bounds of `TriangularBounds`. -/
theorem baseRgMatrix_triangularBounds {a v τ c₁ c₂ ε : ℝ} (h : InftyRange a v τ c₁ c₂)
    (hε : 0 < ε) : TriangularBounds (baseRgMatrix a v τ c₁ c₂ ε) ε := by
  obtain ⟨P, -, hp, -, -, hb⟩ := h.exists_complex_chart hε
  exact hb _ hp

/-- The matrix commutes with complex conjugation (real parameters). -/
theorem baseRgMatrix_conj (a v τ c₁ c₂ ε : ℝ) :
    (baseRgMatrix a v τ c₁ c₂ ε).map (starRingEnd ℂ) = baseRgMatrix a v τ c₁ c₂ ε := by
  unfold baseRgMatrix
  rw [matrixInfty_conj]
  simp only [Complex.conj_ofReal]

/-- **The counterterm system of the first step** (`SMALLFIELD.md` §3.4, Theorem 3.2 (a), at `k = 0`).
For real parameters in the range of Lemma 3.1, analytic bounded nonlinearities `c, f` on the polydisc
(hypothesis (B1): `hc, hf, hcb, hfb`), the forcing bound (5.29) at `k = 0`, and the coupling threshold,
the system `A ξ + c(ξ,p) = f(ξ,p)` has a solution `ξ⁰(p)` in the polydisc of radius `rgRadius (42κ) c₁₀`,
unique there, analytic in the data `p`, real at conjugation-fixed data, with
`‖ξ⁰(p)‖ ≤ C_ξ β⁻¹ q`. -/
theorem baseRg_step {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    {a v τ c₁ c₂ ε : ℝ} (hR : InftyRange a v τ c₁ c₂) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    {P : Set G} (hP : IsOpen P)
    {c f : (Fin 3 → ℂ) × G → (Fin 3 → ℂ)} {κ η c₁₀ : ℝ}
    (hκ : 0 < κ) (hη : 0 ≤ η) (hc₁₀ : 0 < c₁₀)
    (hc : AnalyticOnNhd ℂ c (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hf : AnalyticOnNhd ℂ f (closedBall (0 : Fin 3 → ℂ) c₁₀ ×ˢ P))
    (hcb : ∀ p ∈ P, ∀ ε' : ℝ, 0 ≤ ε' → ε' ≤ c₁₀ → ∀ ξ : Fin 3 → ℂ,
      ‖ξ‖ ≤ ε' → ‖c (ξ, p)‖ ≤ κ * ε' ^ 2)
    (hfb : ∀ p ∈ P, ∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ c₁₀ → ‖f (ξ, p)‖ ≤ η)
    {B α₀ β q : ℝ} (hB : 0 ≤ B) (hα : 0 < α₀) (hβ : 0 < β) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hηbd : η ≤ B * (2 / α₀ ^ 2 * (β⁻¹ * q)))
    (hlarge : 1344 * B * max (84 * κ) (1 / c₁₀) / α₀ ^ 2 ≤ β)
    {σ : G → G} (hσP : ∀ p ∈ P, σ p ∈ P)
    (hcσ : ∀ p ∈ P, ∀ ξ, c (conjVec ξ, σ p) = conjVec (c (ξ, p)))
    (hfσ : ∀ p ∈ P, ∀ ξ, f (conjVec ξ, σ p) = conjVec (f (ξ, p))) :
    ∃ ξs : G → (Fin 3 → ℂ),
      (∀ p ∈ P, ‖ξs p‖ ≤ rgRadius (42 * κ) c₁₀ ∧
        (baseRgMatrix a v τ c₁ c₂ ε).mulVec (ξs p) + c (ξs p, p) = f (ξs p, p) ∧
        (∀ ξ : Fin 3 → ℂ, ‖ξ‖ ≤ rgRadius (42 * κ) c₁₀ →
          (baseRgMatrix a v τ c₁ c₂ ε).mulVec ξ + c (ξ, p) = f (ξ, p) → ξ = ξs p) ∧
        ‖ξs p‖ ≤ rgCxi B α₀ * (β⁻¹ * q) ∧
        (σ p = p → ∀ i, (ξs p i).im = 0)) ∧
      AnalyticOnNhd ℂ ξs P := by
  have hηbd' : η ≤ B * (2 / α₀ ^ 2 * (β⁻¹ * q ^ (0 + 1))) := by simpa using hηbd
  have := physical_rg_step_of_large_beta (A := fun _ : G => baseRgMatrix a v τ c₁ c₂ ε) (k := 0)
    hP (fun i j => analyticOnNhd_const) (fun _ _ => baseRgMatrix_triangularBounds hR hε0) hε0.le hε1
    hκ hη hc₁₀ hc hf hcb hfb hB hα hβ hq0 hq1 hηbd' hlarge hσP
    (fun _ _ => (baseRgMatrix_conj a v τ c₁ c₂ ε).symm) hcσ hfσ
  simpa using this

end Balaban.LargeField
