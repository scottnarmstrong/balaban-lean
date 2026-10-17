module

public import Balaban.LargeField.Base.BaseFirstPhysicalP
public import Balaban.LargeField.Base.BaseRetainedDisintegrate
public import Balaban.LargeField.Base.BaseHistory
import Mathlib.Tactic.FunProp

/-!
# Raw conditional first-spin integrals

These identities split the exact physical sphere-spin measure into raw exterior/collar spins
and spins in the record's proposed interior for a chosen first component. They use the
test-free `baseRho1` integrand and the first `P` decomposition. They do not insert the
later `Q,R,S` selectors or identify P5's fluctuation operator.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban MeasureTheory

/-- The physical bare integrand is integrable at every fixed coarse field and complex source. -/
theorem baseRho1_spinIntegrand_integrable
    {d N L n : ℕ} [NeZero L] [NeZero n] [NeZero N]
    (β a z ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (ψ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) :
    Integrable (fun φ : CfgT d N L n =>
      ((baseKernel d N L n β a (z • ψ) φ : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
      (aprioriMeasure d N (L * n)) := by
  have hcont : Continuous (fun φ : CfgT d N L n =>
      ((baseKernel d N L n β a (z • ψ) φ : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) := by
    dsimp [baseKernel, baseQ, gaussT, energy]
    fun_prop
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
  exact Integrable.of_bound hcont.measurable.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun φ => hC φ (Set.mem_univ φ))

open Classical in
/-- The physical density with the spins in the interior chosen by a component and record
integrated conditionally, and every exterior and collar spin retained as a raw sphere variable.
The equality is Fubini's theorem for any such choice of `br`; matching `br` to the history is
a separate requirement for a physical staged record. -/
theorem baseRho1_eq_conditional_recordInterior
    {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {k0 K N : ℕ} [NeZero S.L] [NeZero N]
    (H : RegionHistory S n R k0 K) (Z' : H.Comp 1)
    (br : BaseRecord S.d S.L (n 1) (R 0))
    (β a z ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (ψ : Torus S.d (n 1) → EuclideanSpace ℝ (Fin N))
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ) :
    let ret : Set (Torus S.d (S.L * n 1)) :=
      {x | blockMap S.L (n 1) x ∉ Z'.1 ∨ blockMap S.L (n 1) x ∉ br.Omega}
    let F : CfgT S.d N S.L (n 1) → ℂ := fun φ =>
      ((baseKernel S.d N S.L (n 1) β a (z • ψ) φ : ℝ) : ℂ) *
        Complex.exp (-((β * energy S.d N (S.L * n 1) ν h φ : ℝ) : ℂ) +
          ∑ x : Torus S.d (S.L * n 1), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    baseRho1 S.d N S.L (n 1) β a z ν h ψ g =
      ((z ^ (N * Fintype.card (Torus S.d (n 1))) : ℝ) : ℂ) *
        ∫ σ : (↥ret → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
          ∫ η : (↥retᶜ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
            F (fun x => if hx : x ∈ ret then σ ⟨x, hx⟩ else η ⟨x, hx⟩)
          ∂(Measure.pi fun _ : ↥retᶜ =>
            (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
        ∂(Measure.pi fun _ : ↥ret =>
          (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  classical
  dsimp only
  let ret : Set (Torus S.d (S.L * n 1)) :=
    {x | blockMap S.L (n 1) x ∉ Z'.1 ∨ blockMap S.L (n 1) x ∉ br.Omega}
  let F : CfgT S.d N S.L (n 1) → ℂ := fun φ =>
    ((baseKernel S.d N S.L (n 1) β a (z • ψ) φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy S.d N (S.L * n 1) ν h φ : ℝ) : ℂ) +
        ∑ x : Torus S.d (S.L * n 1), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
  have hInt : Integrable F (aprioriMeasure S.d N (S.L * n 1)) :=
    baseRho1_spinIntegrand_integrable β a z ν h ψ g
  have hdis := baseRetained_disintegrate S.d N S.L (n 1) ret F hInt
  change ((z ^ (N * Fintype.card (Torus S.d (n 1))) : ℝ) : ℂ) *
    (∫ φ, F φ ∂aprioriMeasure S.d N (S.L * n 1)) = _
  rw [hdis]

open Classical in
/-- The first `P` decomposition remains exact after conditioning on the interior spins
chosen by a component and record. The retained variables are still sphere spins. -/
theorem baseRho1_eq_sum_firstP_conditional_recordInterior
    {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)]
    {R : ℕ → ℝ} {k0 K N : ℕ} [NeZero S.L] [NeZero N]
    (H : RegionHistory S n R k0 K) (Z' : H.Comp 1)
    (br : BaseRecord S.d S.L (n 1) (R 0))
    (β a z ν : ℝ) (regimeB : Prop) (δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (ψ : Torus S.d (n 1) → EuclideanSpace ℝ (Fin N))
    (g : Torus S.d (S.L * n 1) → Fin N → ℂ) :
    let ret : Set (Torus S.d (S.L * n 1)) :=
      {x | blockMap S.L (n 1) x ∉ Z'.1 ∨ blockMap S.L (n 1) x ∉ br.Omega}
    let θ := z • ψ
    let W : Finset (Torus S.d (n 1)) → CfgT S.d N S.L (n 1) → ℝ := fun P φ =>
      (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN S.L (n 1)) S.L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
      ∏ c ∈ (Finset.univ : Finset (Torus S.d (n 1))) \ P,
        chiPrimeZero (baseSectorN S.L (n 1)) S.L 1 1 regimeB ν δ₀
          (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)
    let F : CfgT S.d N S.L (n 1) → ℂ := fun φ =>
      ((baseKernel S.d N S.L (n 1) β a θ φ : ℝ) : ℂ) *
        Complex.exp (-((β * energy S.d N (S.L * n 1) ν h φ : ℝ) : ℂ) +
          ∑ x : Torus S.d (S.L * n 1), ∑ i : Fin N,
            g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    baseRho1 S.d N S.L (n 1) β a z ν h ψ g =
      ((z ^ (N * Fintype.card (Torus S.d (n 1))) : ℝ) : ℂ) *
        ∑ P ∈ (Finset.univ : Finset (Torus S.d (n 1))).powerset,
          ∫ σ : (↥ret → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
            ∫ η : (↥retᶜ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
              ((W P (fun x => if hx : x ∈ ret then σ ⟨x, hx⟩ else η ⟨x, hx⟩) : ℝ) : ℂ) *
                F (fun x => if hx : x ∈ ret then σ ⟨x, hx⟩ else η ⟨x, hx⟩)
            ∂(Measure.pi fun _ : ↥retᶜ =>
              (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
          ∂(Measure.pi fun _ : ↥ret =>
            (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  classical
  dsimp only
  let ret : Set (Torus S.d (S.L * n 1)) :=
    {x | blockMap S.L (n 1) x ∉ Z'.1 ∨ blockMap S.L (n 1) x ∉ br.Omega}
  let θ := z • ψ
  let W : Finset (Torus S.d (n 1)) → CfgT S.d N S.L (n 1) → ℝ := fun P φ =>
    (∏ c ∈ P, (1 - chiPrimeZero (baseSectorN S.L (n 1)) S.L 1 1 regimeB ν δ₀
      (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ))) *
    ∏ c ∈ (Finset.univ : Finset (Torus S.d (n 1))) \ P,
      chiPrimeZero (baseSectorN S.L (n 1)) S.L 1 1 regimeB ν δ₀
        (fun i => h i) c (baseSectorSpin φ, baseSectorTheta θ)
  let F : CfgT S.d N S.L (n 1) → ℂ := fun φ =>
    ((baseKernel S.d N S.L (n 1) β a θ φ : ℝ) : ℂ) *
      Complex.exp (-((β * energy S.d N (S.L * n 1) ν h φ : ℝ) : ℂ) +
        ∑ x : Torus S.d (S.L * n 1), ∑ i : Fin N,
          g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
  have hFint : Integrable F (aprioriMeasure S.d N (S.L * n 1)) :=
    baseRho1_spinIntegrand_integrable β a z ν h ψ g
  have hInt (P : Finset (Torus S.d (n 1))) :
      Integrable (fun φ : CfgT S.d N S.L (n 1) => ((W P φ : ℝ) : ℂ) * F φ)
        (aprioriMeasure S.d N (S.L * n 1)) := by
    obtain ⟨hw, hw0, hw1⟩ := baseFirstPhysicalP_weight_measurable_unit
      (d := S.d) (N := N) (L := S.L) (n := n 1) regimeB ν δ₀ h θ P
    refine hFint.norm.mono' ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
      hFint.aestronglyMeasurable) ?_
    exact Filter.Eventually.of_forall fun φ => by
      have hp : |W P φ| ≤ 1 := by
        rw [abs_of_nonneg (hw0 φ)]
        exact hw1 φ
      calc
        ‖((W P φ : ℝ) : ℂ) * F φ‖ = |W P φ| * ‖F φ‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        _ ≤ 1 * ‖F φ‖ := mul_le_mul_of_nonneg_right hp (norm_nonneg _)
        _ = ‖F φ‖ := one_mul _
  have hpart := baseRho1_eq_sum_firstP (d := S.d) (N := N) (L := S.L)
    (n := n 1) β a z ν regimeB δ₀ h g ψ
  change baseRho1 S.d N S.L (n 1) β a z ν h ψ g =
    ((z ^ (N * Fintype.card (Torus S.d (n 1))) : ℝ) : ℂ) *
      ∑ P ∈ (Finset.univ : Finset (Torus S.d (n 1))).powerset,
        ∫ σ : (↥ret → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
          ∫ η : (↥retᶜ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1),
            ((W P (fun x => if hx : x ∈ ret then σ ⟨x, hx⟩ else η ⟨x, hx⟩) : ℝ) : ℂ) *
              F (fun x => if hx : x ∈ ret then σ ⟨x, hx⟩ else η ⟨x, hx⟩)
          ∂(Measure.pi fun _ : ↥retᶜ =>
            (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
        ∂(Measure.pi fun _ : ↥ret =>
          (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
  rw [hpart]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hdis := baseRetained_disintegrate S.d N S.L (n 1) ret
    (fun φ : CfgT S.d N S.L (n 1) => ((W P φ : ℝ) : ℂ) * F φ) (hInt P)
  exact hdis

end Balaban.LargeField
