/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRecordBridge
public import Balaban.LargeField.Base.BaseChartNative

/-!
# The physical first-step integral over the spins of a good region

Fix the spins `φ₀` off the good region `Ω` (those on `Ω` are ignored).  For a configuration `ψ` of
the spins of `Ω` the merged configuration `baseMerge G φ₀ ψ` of the physical torus carries `ψ` on
`Ω` and `φ₀` elsewhere.  The physical first-step density
`baseKernel · exp(-β energy + ⟨g, ·⟩)` at the merged configuration is the constant `K0` times
`exp(-β A_G(ψ) - m ∑ ‖ψ_x - h‖² + ⟨g, ψ⟩)` (`baseKernel_mul_exp_merge`), with `A_G` the action of
the generating set `G` whose `Ω 1` is `Ω`.  The integral over the spins of `Ω` of a cutoff times
this density is then the chart Gaussian integral of `baseNative_chartGaussian`
(`baseGood_physical_chartGaussian`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical MeasureTheory
open Balaban.LargeField.Base

noncomputable section

variable {d N L n : ℕ} [NeZero L] [NeZero n] {ϱ : ℝ} (G : GeneratingSet d L (1 * n) 1 ϱ)

/-- **The merged configuration**: `ψ` on the sites of `Ω` and `φ₀` elsewhere. -/
def baseMerge (φ₀ : CfgT d N L n)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : CfgT d N L n :=
  fun x => if hx : (baseSector_side L n).symm ▸ x ∈ G.Ω 1 then
    ψ ⟨(baseSector_side L n).symm ▸ x, hx⟩ else φ₀ x

/-- On the sites of `Ω` the merged configuration is `ψ`. -/
theorem baseMerge_of_mem (φ₀ : CfgT d N L n)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) (x : G.Ω 1) :
    baseMerge G φ₀ ψ (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) = ψ x := by
  have hr : (baseSector_side L n).symm ▸ (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) =
      (x : Torus d (1 * n * L ^ 1)) :=
    cast_roundtrip_rev (F := fun m : ℕ => Torus d m) (baseSector_side L n) x
  unfold baseMerge
  have hx : (baseSector_side L n).symm ▸ (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) ∈
      G.Ω 1 := by rw [hr]; exact x.2
  simp only [hx, ↓reduceDIte]
  congr 1
  exact Subtype.ext hr

/-- Off the sites of `Ω` the merged configuration is `φ₀`. -/
theorem baseMerge_of_not_mem (φ₀ : CfgT d N L n)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) {x : Torus d (1 * n * L ^ 1)}
    (hx : x ∉ G.Ω 1) : baseMerge G φ₀ ψ (baseSector_side L n ▸ x) = φ₀ (baseSector_side L n ▸ x) := by
  have hr : (baseSector_side L n).symm ▸ (baseSector_side L n ▸ x) = x :=
    cast_roundtrip_rev (F := fun m : ℕ => Torus d m) (baseSector_side L n) x
  unfold baseMerge
  have hx' : ¬ ((baseSector_side L n).symm ▸ (baseSector_side L n ▸ x) ∈ G.Ω 1) := by
    rw [hr]; exact hx
  simp only [hx', ↓reduceDIte]

/-- The spin field of a merged configuration is the spin field of `ψ`. -/
theorem physSpin_baseMerge (φ₀ : CfgT d N L n)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    physSpin G (baseMerge G φ₀ ψ) = sphereSpinField G ψ := by
  funext p
  simp only [physSpin, sphereSpinField]
  rw [baseMerge_of_mem]

/-- The source of `g` on the sites of `Ω`. -/
def sourceΩ (g : Torus d (L * n) → Fin N → ℂ) : G.Ω 1 → Fin N → ℂ := fun x i =>
  g (baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1))) i

/-- **The constant of the physical density off `Ω`**: the block normalization, the part of the
action off `Ω`, the mass and the source off `Ω`. -/
def baseExtConst (β a₀ μ m : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (φ₀ : CfgT d N L n) : ℂ :=
  ((∏ _y : Torus d n, ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^ ((N : ℝ) / 2) : ℝ) :
      ℂ) *
    Complex.exp (-((β * bridgeExt G a₀ μ h θ φ₀ : ℝ) : ℂ) -
      ((m * ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
        ‖(φ₀ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) : ℝ) : ℂ) +
      ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
        ∑ i : Fin N, g (baseSector_side L n ▸ x) i *
          (((φ₀ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))

/-- **The physical density at a merged configuration.**  For the generating set `G` of the good
region, data `D` that are the lifted coarse field on `Ω`, the retained spins on the collar and `h`
on `Ω`, and the merged configuration of `ψ` and the retained spins `φ₀`,
`baseKernel · exp(-β energy ν h + ⟨g, ·⟩) = K0 · exp(-β A_G(ψ) - m ∑_Ω ‖ψ_x - h‖² + ⟨g_Ω, ψ⟩)`
with `m = β (ν - μ) / 2` and `K0 = baseExtConst`. -/
theorem baseDensity_merge {β : ℝ} (a : ℕ → ℝ) (a₀ μ ν : ℝ) (ha : a 1 = a₀)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (φ₀ : CfgT d N L n) (D : BgData G N)
    (hΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = ((θ (blkOf x) i : ℝ) : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (((φ₀ (baseSector_side L n ▸ x) :
      EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    (hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ))
    (hblk : ∀ x y : Torus d (1 * n * L ^ 1), blkOf x = blkOf y → (x ∈ G.Ω 1 ↔ y ∈ G.Ω 1))
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    ((baseKernel d N L n β a₀ θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
      Complex.exp (-((β * energy d N (L * n) ν h (baseMerge G φ₀ ψ) : ℝ) : ℂ) +
        ∑ x : Torus d (L * n), ∑ i : Fin N,
          g x i * (((baseMerge G φ₀ ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) =
    baseExtConst G β a₀ μ (β * (ν - μ) / 2) h θ g φ₀ *
      Complex.exp (-((β * action G a μ D (sphereSpinField G ψ) : ℝ) : ℂ) -
        ((β * (ν - μ) / 2 * ∑ x : G.Ω 1, ‖(ψ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 : ℝ) : ℂ) +
        ∑ x : G.Ω 1, ∑ i : Fin N, sourceΩ G g x i *
          (((ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) := by
  set φ := baseMerge G φ₀ ψ with hφ
  have hagree : ∀ x : Torus d (1 * n * L ^ 1), x ∉ G.Ω 1 →
      φ (baseSector_side L n ▸ x) = φ₀ (baseSector_side L n ▸ x) :=
    fun x hx => baseMerge_of_not_mem G φ₀ ψ hx
  have hDcφ : ∀ x ∈ collar G, ∀ i, D.Ψ x i =
      (((φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) := by
    intro x hx i
    rw [hDc x hx i, hagree x ((mem_collar G).1 hx).1]
  have hAct := baseGood_action_add_ext G a a₀ μ ha h θ φ D hΨ hDcφ hh hblk
  rw [physSpin_baseMerge] at hAct
  have hext := bridgeExt_congr G a₀ μ h θ φ φ₀ hagree
  rw [hext] at hAct
  have hk := baseKernel_mul_exp (d := d) (N := N) (L := L) (n := n) β a₀ θ φ
    (-((β * energy d N (L * n) ν h φ : ℝ) : ℂ) +
      ∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
  rw [hk]
  -- the mass and the source split along `Ω`
  have hmass : ∑ x : Torus d (L * n), ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 =
      ∑ x : G.Ω 1, ‖(ψ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 +
        ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
          ‖(φ₀ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2) := by
    rw [← sum_torus_cast (baseSector_side L n)
      (fun x : Torus d (L * n) => ‖(φ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)]
    rw [sum_split_Ω G (fun x => ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      rw [hφ, baseMerge_of_mem]
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ G.Ω 1
      · simp [hx]
      · simp only [hx, ↓reduceIte]; rw [hagree x hx]
  have hsrc : ∑ x : Torus d (L * n), ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) =
      ∑ x : G.Ω 1, ∑ i : Fin N, sourceΩ G g x i *
          (((ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ) +
        ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
          ∑ i : Fin N, g (baseSector_side L n ▸ x) i *
            (((φ₀ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)) := by
    rw [← sum_torus_cast (baseSector_side L n)
      (fun x : Torus d (L * n) => ∑ i : Fin N,
        g x i * (((φ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))]
    rw [sum_split_Ω G (fun x => ∑ i : Fin N, g (baseSector_side L n ▸ x) i *
      (((φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))]
    congr 1
    · refine Finset.sum_congr rfl fun x _ => ?_
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hφ, baseMerge_of_mem]
      rfl
    · refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x ∈ G.Ω 1
      · simp [hx]
      · simp only [hx, ↓reduceIte]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hagree x hx]
  have hen := energy_mass_split (d := d) (N := N) (L := L) (n := n) ν μ h φ
  unfold baseExtConst
  generalize ((∏ _y : Torus d n, ((β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2) / (2 * Real.pi)) ^
    ((N : ℝ) / 2) : ℝ) : ℂ) = κ
  rw [mul_assoc κ, ← Complex.exp_add]
  congr 2
  have hc : (β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 : ℝ) =
      β * (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) := by ring
  have hR : β * a₀ * (L : ℝ) ^ d / (L : ℝ) ^ 2 / 2 *
        ∑ y : Torus d n, ‖θ y - baseQ d N L n φ y‖ ^ 2 +
      β * energy d N (L * n) ν h φ =
    β * action G a μ D (sphereSpinField G ψ) + β * bridgeExt G a₀ μ h θ φ₀ +
      β * (ν - μ) / 2 * (∑ x : G.Ω 1, ‖(ψ x : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2 +
        ∑ x : Torus d (1 * n * L ^ 1), (if x ∈ G.Ω 1 then 0 else
          ‖(φ₀ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N)) - h‖ ^ 2)) := by
    rw [hen, hmass, hc]
    have := congrArg (fun r : ℝ => β * r) hAct
    nlinarith [this]
  have hRc := congrArg (fun r : ℝ => (r : ℂ)) hR
  rw [hsrc]
  push_cast at hRc ⊢
  linear_combination (-1 : ℂ) * hRc

variable {G} in
/-- **The physical integral over the spins of a good region is a chart Gaussian integral.**
Let `G` be the generating set of the good region, with the data `D` of the retained spins `φ₀` and
the spin support `S`.  If the weight of the integrand at a merged configuration is a constant
`Pfac` (the factors of the failed cubes, which read only retained spins) times a cutoff `w` of the
spins of `Ω` that is supported in the hemispheres around the background centre, then the integral
over the spins of `Ω` of the weight times the physical density is `Pfac` times the Gaussian
prefactor times the standard Gaussian integral of the remainder `chartGaussRem`, with the explicit
constant `baseExtConst`. -/
theorem baseGood_physical_chartGaussian {β : ℝ} (hβ : 0 < β) (a : ℕ → ℝ) (a₀ μ ν δ₀ : ℝ)
    (ha : a 1 = a₀) (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (φ₀ : CfgT d N L n)
    (φs : Torus d (1 * n * L ^ 1) → Fin N → ℝ) (D : BgData G N)
    (S : BaseSpinSupport G μ δ₀ φs (fun i => h i) D) (Hbg : BgHyp d L 1 ϱ a μ)
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4)
    (hΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i = ((θ (blkOf x) i : ℝ) : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = (((φ₀ (baseSector_side L n ▸ x) :
      EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))
    (hblk : ∀ x y : Torus d (1 * n * L ^ 1), blkOf x = blkOf y → (x ∈ G.Ω 1 ↔ y ∈ G.Ω 1))
    (W : CfgT d N L n → ℝ) (Pfac : ℝ)
    (w : (G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℝ) (hw : Measurable w)
    (hw1 : ∀ ψ, |w ψ| ≤ 1)
    (hws : ∀ ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      (∃ x, ¬ 0 < inner ℝ (bgCenter G a μ D x) (ψ x : EuclideanSpace ℝ (Fin N))) → w ψ = 0)
    (hW : ∀ ψ, W (baseMerge G φ₀ ψ) = Pfac * w ψ) :
    ∃ R : Config (G.Ω 1) N ≃ₗ[ℝ] Config (G.Ω 1) N,
      (∀ v, gaussForm (bgCenter G a μ D) (bgHess G a μ D) (R (R v)) = v) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config (G.Ω 1) N →ₗ[ℝ] Config (G.Ω 1) N) =
        Real.sqrt (LinearMap.det (gaussForm (bgCenter G a μ D) (bgHess G a μ D)))⁻¹ ∧
      ∫ ψ, ((W (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
          (((baseKernel d N L n β a₀ θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
            Complex.exp (-((β * energy d N (L * n) ν h (baseMerge G φ₀ ψ) : ℝ) : ℂ) +
              ∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((baseMerge G φ₀ ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
          ∂(Measure.pi fun _ : G.Ω 1 => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
        (Pfac : ℂ) * (((Real.sqrt β)⁻¹ ^ (Fintype.card (G.Ω 1) * (N - 1))) •
          ((((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card (G.Ω 1) / 2) *
            Real.sqrt (LinearMap.det (gaussForm (bgCenter G a μ D) (bgHess G a μ D)))⁻¹ : ℝ) :
              ℂ) *
            ∫ ψ, chartGaussRem β (β * (ν - μ) / 2) (bgCenter G a μ D)
              (bgCenter_unit G φs (fun i => h i) D S Hbg hΛ1 hΛ2)
              (bgHess G a μ D) h (sourceΩ G g)
              (baseExtConst G β a₀ μ (β * (ν - μ) / 2) h θ g φ₀) w
              (action G a μ D (fun p : G.Ω 1 × Fin N => ((bgCenter G a μ D p.1 p.2 : ℝ) : ℂ)))
              (tangentProj (bgCenter G a μ D) (bgCenter_unit G φs (fun i => h i) D S Hbg hΛ1 hΛ2)
                (R ψ)) ∂(stdGaussian (G.Ω 1) N))) := by
  have hh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ) := S.field_eq
  obtain ⟨R, h1, h2, h3, h4⟩ := baseNative_chartGaussian G (a := a) hβ (β * (ν - μ) / 2) φs
    (fun i => h i) D S Hbg hΛ1 hΛ2 (sourceΩ G g)
    (baseExtConst G β a₀ μ (β * (ν - μ) / 2) h θ g φ₀) w hw hw1 hws
  refine ⟨R, h1, h2, h3, ?_⟩
  have hpt : ∀ ψ, ((W (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
      (((baseKernel d N L n β a₀ θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
        Complex.exp (-((β * energy d N (L * n) ν h (baseMerge G φ₀ ψ) : ℝ) : ℂ) +
          ∑ x : Torus d (L * n), ∑ i : Fin N,
            g x i * (((baseMerge G φ₀ ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ))) =
      (Pfac : ℂ) * chartGaussDensity β (β * (ν - μ) / 2) (WithLp.toLp 2 (fun i => h i))
        (sourceΩ G g) (baseExtConst G β a₀ μ (β * (ν - μ) / 2) h θ g φ₀) w
        (fun ψ => action G a μ D (sphereSpinField G ψ)) ψ := by
    intro ψ
    rw [baseDensity_merge G a a₀ μ ν ha h θ g φ₀ D hΨ hDc hh hblk ψ, hW ψ]
    unfold chartGaussDensity
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_const_mul, h4]

end

end Balaban.LargeField
