/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRecordGaussian
public import Balaban.LargeField.Base.BaseFirstChart
public import Balaban.LargeField.Base.BaseRecordGoodRegion

/-!
# The integral over the spins of the good region of a base record

For a base record `br` (with failed cubes `P = br.P` and good region `Ω = br.Omega`), the
generating set `G` with `G.Ω 1` the fine set of `Ω`, and the retained spins `φ₀`, the weight
`∏_{c ∈ P} (1 - χ'_c) ∏_{c ∉ P} χ'_c` of the base decomposition at the merged configuration
`baseMerge G φ₀ ψ` is the constant `∏_{c ∈ P} (1 - χ'_c)(φ₀)` times the cutoff
`w(ψ) = ∏_{c ∉ P} χ'_c` of the spins of `Ω`, supported in the hemispheres around the background
(`baseRecord_physical_chartGaussian`); by `baseGood_physical_chartGaussian` the integral over the
spins of `Ω` of the weighted physical density is a chart Gaussian integral.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix Classical MeasureTheory
open Balaban.LargeField.Base

noncomputable section

variable {d N L n : ℕ} [NeZero L] [NeZero n] {ϱ : ℝ} (G : GeneratingSet d L (1 * n) 1 ϱ)

/-- Transporting the retained spins to the merged configuration is measurable. -/
theorem measurable_baseMerge (φ₀ : CfgT d N L n) : Measurable (baseMerge G φ₀) := by
  refine measurable_pi_iff.mpr fun x => ?_
  by_cases hx : (baseSector_side L n).symm ▸ x ∈ G.Ω 1
  · simp only [baseMerge, hx, ↓reduceDIte]
    exact measurable_pi_apply _
  · simp only [baseMerge, hx, ↓reduceDIte]
    exact measurable_const

/-- The real spin coordinates of a merged configuration. -/
theorem baseSectorSpin_baseMerge (φ₀ : CfgT d N L n)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (x : Torus d (1 * n * L ^ 1)) (i : Fin N) :
    baseSectorSpin (baseMerge G φ₀ ψ) x i =
      if hz : x ∈ G.Ω 1 then (ψ ⟨x, hz⟩ : EuclideanSpace ℝ (Fin N)) i
      else baseSectorSpin φ₀ x i := by
  by_cases hz : x ∈ G.Ω 1
  · simp only [hz, ↓reduceDIte]
    exact congrArg (fun v : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1 =>
      (v : EuclideanSpace ℝ (Fin N)) i) (baseMerge_of_mem G φ₀ ψ ⟨x, hz⟩)
  · simp only [hz, ↓reduceDIte]
    unfold baseSectorSpin
    rw [baseMerge_of_not_mem G φ₀ ψ hz]

/-- **The failed-cube factor of the base decomposition**: `∏_{c ∈ P} (1 - χ'_c)`. -/
def recordWeightIn (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : ℝ :=
  ∏ c ∈ P, (1 - chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
    (baseSectorSpin φ, baseSectorTheta θ))

/-- **The good-cube factor of the base decomposition**: `∏_{c ∉ P} χ'_c`. -/
def recordWeightOut (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : ℝ :=
  ∏ c ∈ (Finset.univ : Finset (Torus d n)) \ P,
    chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ)

theorem chiPrimeZero_mem_unit (regimeB : Prop) (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n) (c : Torus d n) :
    0 ≤ chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ) ∧
      chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
        (baseSectorSpin φ, baseSectorTheta θ) ≤ 1 := by
  rcases chiPrimeZero_eq_zero_or_one (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
    (baseSectorSpin φ, baseSectorTheta θ) with h0 | h0
  · rw [h0]; exact ⟨le_rfl, zero_le_one⟩
  · rw [h0]; exact ⟨zero_le_one, le_rfl⟩

theorem recordWeightOut_nonneg (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : 0 ≤ recordWeightOut P regimeB ν δ₀ h θ φ := by
  exact Finset.prod_nonneg fun c _ => (chiPrimeZero_mem_unit regimeB ν δ₀ h θ φ c).1

theorem recordWeightOut_le_one (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) : recordWeightOut P regimeB ν δ₀ h θ φ ≤ 1 := by
  exact Finset.prod_le_one₀ (fun c _ => (chiPrimeZero_mem_unit regimeB ν δ₀ h θ φ c).1)
    fun c _ => (chiPrimeZero_mem_unit regimeB ν δ₀ h θ φ c).2

theorem measurable_recordWeightOut (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N)) :
    Measurable (recordWeightOut (d := d) (N := N) (L := L) P regimeB ν δ₀ h θ) :=
  Finset.measurable_prod _ fun c _ => measurable_baseSectorCube regimeB ν δ₀ h θ c

theorem chi_eq_one_of_recordWeightOut_ne_zero (P : Finset (Torus d n)) (regimeB : Prop)
    (ν δ₀ : ℝ) (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (φ : CfgT d N L n) (hw : recordWeightOut P regimeB ν δ₀ h θ φ ≠ 0) {c : Torus d n}
    (hc : c ∉ P) : chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ) = 1 := by
  have hne : chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
      (baseSectorSpin φ, baseSectorTheta θ) ≠ 0 := fun h0 =>
    hw (Finset.prod_eq_zero (Finset.mem_sdiff.2 ⟨Finset.mem_univ c, hc⟩) h0)
  rcases chiPrimeZero_eq_zero_or_one (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
    (baseSectorSpin φ, baseSectorTheta θ) with h0 | h1
  · exact absurd h0 hne
  · exact h1

omit [NeZero L] [NeZero n] in
theorem baseSectorSpin_unit (φ : CfgT d N L n) (x : Torus d (1 * n * L ^ 1)) :
    ∑ i, baseSectorSpin φ x i ^ 2 = 1 := by
  have hn : ‖(φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp (φ (baseSector_side L n ▸ x)).property
  have hs := EuclideanSpace.norm_sq_eq (φ (baseSector_side L n ▸ x) : EuclideanSpace ℝ (Fin N))
  simp only [Real.norm_eq_abs, sq_abs] at hs
  simpa [baseSectorSpin] using hs.symm.trans (by rw [hn]; norm_num)

theorem vector_unit (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1) : ∑ i, h i ^ 2 = 1 := by
  have hs := EuclideanSpace.norm_sq_eq h
  simp only [Real.norm_eq_abs, sq_abs] at hs
  calc ∑ i, h i ^ 2 = ‖h‖ ^ 2 := hs.symm
    _ = 1 := by rw [hh]; norm_num

omit [NeZero L] [NeZero n] in
/-- Sites with the same physical block have the same first block. -/
theorem jBlock_eq_of_blkOf_eq {x y : Torus d (1 * n * L ^ 1)} (h : blkOf x = blkOf y) :
    jBlock d L (1 * n) 1 1 x = jBlock d L (1 * n) 1 1 y := by
  have h1 := baseSector_blockMap_transport (d := d) (L := L) (n := n) x
  have h2 := baseSector_blockMap_transport (d := d) (L := L) (n := n) y
  have h3 : baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x =
      baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 y := by
    rw [h1, h2]; exact h
  have := congrArg (fun z : Torus d n => (baseSector_coarse L n).symm ▸ z) h3
  simpa only [cast_roundtrip_rev (F := fun m : ℕ => Torus d m) (baseSector_coarse L n)] using this

/-- **The Gaussian side of the integral over the spins of the good region of a base record**:
the failed-cube factor at the retained spins times the Gaussian prefactor times the standard
Gaussian integral of the remainder, for the transport `R` of the Gaussian form. -/
def recordGaussRHS (P : Finset (Torus d n)) (regimeB : Prop) (β a₀ ν δ₀ : ℝ)
    (a : ℕ → ℝ) (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (φ₀ : CfgT d N L n) (D : BgData G N)
    (he : ∀ x, ‖bgCenter G a (if regimeB then ν else 0) D x‖ = 1)
    (R : Config (G.Ω 1) N ≃ₗ[ℝ] Config (G.Ω 1) N) : ℂ :=
  (recordWeightIn P regimeB ν δ₀ h θ φ₀ : ℂ) *
    (((Real.sqrt β)⁻¹ ^ (Fintype.card (G.Ω 1) * (N - 1))) •
      ((((2 * Real.pi) ^ (((N : ℝ) - 1) * Fintype.card (G.Ω 1) / 2) *
        Real.sqrt (LinearMap.det (gaussForm (bgCenter G a (if regimeB then ν else 0) D)
          (bgHess G a (if regimeB then ν else 0) D)))⁻¹ : ℝ) : ℂ) *
        ∫ ψ, chartGaussRem β (β * (ν - (if regimeB then ν else 0)) / 2)
          (bgCenter G a (if regimeB then ν else 0) D) he
          (bgHess G a (if regimeB then ν else 0) D) h (sourceΩ G g)
          (baseExtConst G β a₀ (if regimeB then ν else 0)
            (β * (ν - (if regimeB then ν else 0)) / 2) h θ g φ₀)
          (fun ψ => recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ))
          (action G a (if regimeB then ν else 0) D
            (fun p : G.Ω 1 × Fin N => ((bgCenter G a (if regimeB then ν else 0) D p.1 p.2 :
              ℝ) : ℂ)))
          (tangentProj (bgCenter G a (if regimeB then ν else 0) D) he (R ψ))
          ∂(stdGaussian (G.Ω 1) N))) 

variable {G} in
/-- **The integral over the spins of the good region of a base record.**  Let `br` be a base
record with failed cubes `P` and good region `Ω`, `G` the generating set with `G.Ω 1` the fine set
of `Ω`, `D` the lifted data (coarse field on `Ω`, retained spins `φ₀` on the collar, `h` on `Ω`),
and suppose the good-cube factor `∏_{c ∉ P} χ'_c` is non-zero at some merged configuration.  Then
the integral over the spins of `Ω` of the weight `∏_{c ∈ P} (1 - χ'_c) ∏_{c ∉ P} χ'_c` times the
physical density is the failed-cube factor at the retained spins times the chart Gaussian integral
of `baseGood_physical_chartGaussian`. -/
theorem baseRecord_physical_chartGaussian {Rk : ℝ}
    (br : BaseRecord d L (baseSectorN L n 1) Rk) (P : Finset (Torus d n))
    (hP : br.P = (↑P : Set (Torus d n)))
    (hΩ : ∀ x, x ∈ G.Ω 1 ↔ cubeMap (baseSectorN L n) L 1 1 1 x ∈ br.Omega)
    {β : ℝ} (hβ : 0 < β) (a : ℕ → ℝ) (a₀ ν δ₀ : ℝ) (regimeB : Prop) (ha : a 1 = a₀)
    (hδ₀ : 0 < δ₀) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (g : Torus d (L * n) → Fin N → ℂ)
    (φ₀ : CfgT d N L n) (Hbg : BgHyp d L 1 ϱ a (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (hΛ2 : (d + 2 + 4 * d * bgK1 d L N) * L * δ₀ ≤ 1 / 4) (D : BgData G N)
    (hDΨ : ∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i =
      ((baseSectorTheta θ (jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ))
    (hDc : ∀ x ∈ collar G, ∀ i, D.Ψ x i = ((baseSectorSpin φ₀ x i : ℝ) : ℂ))
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ))
    (hex : ∃ ψ, recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) ≠ 0) :
    ∀ he : ∀ x, ‖bgCenter G a (if regimeB then ν else 0) D x‖ = 1,
    ∃ R : Config (G.Ω 1) N ≃ₗ[ℝ] Config (G.Ω 1) N,
      (∀ v, gaussForm (bgCenter G a (if regimeB then ν else 0) D)
        (bgHess G a (if regimeB then ν else 0) D) (R (R v)) = v) ∧
      (∀ u v, cinner (R u) v = cinner u (R v)) ∧
      LinearMap.det (R : Config (G.Ω 1) N →ₗ[ℝ] Config (G.Ω 1) N) =
        Real.sqrt (LinearMap.det (gaussForm (bgCenter G a (if regimeB then ν else 0) D)
          (bgHess G a (if regimeB then ν else 0) D)))⁻¹ ∧
      ∫ ψ, ((recordWeightIn P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) *
            recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
          (((baseKernel d N L n β a₀ θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
            Complex.exp (-((β * energy d N (L * n) ν h (baseMerge G φ₀ ψ) : ℝ) : ℂ) +
              ∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((baseMerge G φ₀ ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
          ∂(Measure.pi fun _ : G.Ω 1 => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
        recordGaussRHS (G := G) P regimeB β a₀ ν δ₀ a h θ g φ₀ D he R := by
  intro he
  obtain ⟨ψ₀, hψ₀⟩ := hex
  have hnn : ∀ i, i < 1 → baseSectorN L n i = L * baseSectorN L n (i + 1) :=
    baseSectorN_step L n
  -- the native spin field of a merged configuration
  have hspin : ∀ ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      ∀ x : Torus d (1 * n * L ^ 1), x ∉ G.Ω 1 →
        baseSectorSpin (baseMerge G φ₀ ψ) x = baseSectorSpin φ₀ x := by
    intro ψ x hx
    funext i
    simp only [baseSectorSpin_baseMerge, hx, ↓reduceDIte]
  have hDcψ : ∀ ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      ∀ x ∈ collar G, ∀ i, D.Ψ x i = ((baseSectorSpin (baseMerge G φ₀ ψ) x i : ℝ) : ℂ) := by
    intro ψ x hx i
    rw [hspin ψ x ((mem_collar G).1 hx).1, hDc x hx i]
  have hsupp : ∀ ψ, recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) ≠ 0 →
      ∀ c : Torus d (baseSectorN L n 1), c ∉ br.P →
        chiPrimeZero (baseSectorN L n) L 1 1 regimeB ν δ₀ (fun i => h i) c
          (baseSectorSpin (baseMerge G φ₀ ψ), baseSectorTheta θ) = 1 := by
    intro ψ hψ c hc
    exact chi_eq_one_of_recordWeightOut_ne_zero P regimeB ν δ₀ h θ _ hψ (by rwa [hP] at hc)
  have hS := baseSpinSupport_of_baseRecord (nn := baseSectorN L n) (M := 1) hnn G br hΩ regimeB
    ν δ₀ hδ₀ (baseSectorSpin (baseMerge G φ₀ ψ₀)) (baseSectorTheta θ) (fun i => h i)
    (baseSectorSpin_unit _) (vector_unit h hh) D hDΨ (hDcψ ψ₀) hDh (hsupp ψ₀ hψ₀)
  -- the cutoff
  have hblk : ∀ x y : Torus d (1 * n * L ^ 1), blkOf x = blkOf y → (x ∈ G.Ω 1 ↔ y ∈ G.Ω 1) := by
    intro x y hxy
    have hj : jBlock d L (1 * baseSectorN L n 1) 1 1 x = jBlock d L (1 * baseSectorN L n 1) 1 1 y :=
      jBlock_eq_of_blkOf_eq hxy
    rw [hΩ, hΩ, ← cubeMap_eq_comp hnn le_rfl x, ← cubeMap_eq_comp hnn le_rfl y, hj]
  have hhem : ∀ ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
      recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) ≠ 0 →
      ∀ x : G.Ω 1, 0 < inner ℝ (bgCenter G a (if regimeB then ν else 0) D x)
        (ψ x : EuclideanSpace ℝ (Fin N)) := by
    intro ψ hψ x
    have hp := baseFirstRecord_inner_pos_of_goodCubes (nn := baseSectorN L n) (M := 1) hnn G br
      hΩ regimeB ν δ₀ hδ₀ (baseSectorSpin (baseMerge G φ₀ ψ)) (baseSectorTheta θ) (fun i => h i)
      (baseSectorSpin_unit _) (vector_unit h hh) D hDΨ (hDcψ ψ) hDh (hsupp ψ hψ) a Hbg hΛ1 hΛ2 x
    have hx : (WithLp.toLp 2 (baseSectorSpin (baseMerge G φ₀ ψ) x) :
        EuclideanSpace ℝ (Fin N)) = (ψ x : EuclideanSpace ℝ (Fin N)) := by
      ext i
      change baseSectorSpin (baseMerge G φ₀ ψ) (x : Torus d (1 * n * L ^ 1)) i =
        (ψ x : EuclideanSpace ℝ (Fin N)) i
      rw [baseSectorSpin_baseMerge]; simp only [x.2, ↓reduceDIte]
    have hp' : 0 < inner ℝ (bgCenter G a (if regimeB then ν else 0) D x)
        (WithLp.toLp 2 (baseSectorSpin (baseMerge G φ₀ ψ) (x : Torus d (1 * n * L ^ 1))) :
          EuclideanSpace ℝ (Fin N)) := hp
    rw [hx] at hp'
    exact hp'
  have hWeq : ∀ ψ, recordWeightIn P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) *
      recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) =
      recordWeightIn P regimeB ν δ₀ h θ φ₀ *
        recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) := by
    intro ψ
    congr 1
    unfold recordWeightIn
    refine Finset.prod_congr rfl fun c hc => ?_
    congr 1
    have hcP : c ∈ br.P := by rw [hP]; exact hc
    have := (baseRecord_good_region (nn := baseSectorN L n) (M := 1) (K := 1) hnn le_rfl regimeB ν
      δ₀ (fun i => h i) br).2.2.2 c hcP (baseSectorSpin (baseMerge G φ₀ ψ)) (baseSectorSpin φ₀)
      (baseSectorTheta θ) (fun x hx => by
        have hxΩ : x ∉ G.Ω 1 := fun hmem => hx ((hΩ x).1 hmem)
        exact hspin ψ x hxΩ)
    exact this
  have := baseGood_physical_chartGaussian (G := G) hβ a a₀ (if regimeB then ν else 0) ν δ₀ ha h θ g
    φ₀ (baseSectorSpin (baseMerge G φ₀ ψ₀)) D hS Hbg hΛ1 hΛ2
    (fun x hx i => by
      rw [hDΨ x hx i]
      have := baseSector_blockMap_transport (d := d) (L := L) (n := n) x
      unfold baseSectorTheta
      rw [show baseSector_coarse L n ▸ jBlock d L (1 * n) 1 1 x = blkOf x from this])
    (fun x hx i => by rw [hDc x hx i]; rfl) hblk
    (fun φ => recordWeightIn P regimeB ν δ₀ h θ φ * recordWeightOut P regimeB ν δ₀ h θ φ)
    (recordWeightIn P regimeB ν δ₀ h θ φ₀)
    (fun ψ => recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ))
    ((measurable_recordWeightOut P regimeB ν δ₀ h θ).comp (measurable_baseMerge G φ₀))
    (fun ψ => by
      rw [abs_of_nonneg (recordWeightOut_nonneg P regimeB ν δ₀ h θ _)]
      exact recordWeightOut_le_one P regimeB ν δ₀ h θ _)
    (fun ψ hψ => by
      by_contra hne
      obtain ⟨x, hx⟩ := hψ
      exact hx (hhem ψ hne x))
    hWeq
  obtain ⟨R, h1, h2, h3, h4⟩ := this
  exact ⟨R, h1, h2, h3, h4⟩

variable {G} in
/-- **The integral over the spins of the good region vanishes when the good-cube factor does.**
If the good-cube factor `∏_{c ∉ P} χ'_c` is zero at every merged configuration, the weighted
physical density integrates to zero. -/
theorem baseRecord_integral_eq_zero (P : Finset (Torus d n)) (regimeB : Prop) (ν δ₀ β a₀ : ℝ)
    (h : EuclideanSpace ℝ (Fin N)) (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (g : Torus d (L * n) → Fin N → ℂ) (φ₀ : CfgT d N L n)
    (hz : ∀ ψ, recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) = 0) :
    ∫ ψ, ((recordWeightIn P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) *
            recordWeightOut P regimeB ν δ₀ h θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
          (((baseKernel d N L n β a₀ θ (baseMerge G φ₀ ψ) : ℝ) : ℂ) *
            Complex.exp (-((β * energy d N (L * n) ν h (baseMerge G φ₀ ψ) : ℝ) : ℂ) +
              ∑ x : Torus d (L * n), ∑ i : Fin N,
                g x i * (((baseMerge G φ₀ ψ x : EuclideanSpace ℝ (Fin N)) i : ℝ) : ℂ)))
          ∂(Measure.pi fun _ : G.Ω 1 => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
        = 0 := by
  simp [hz]

end

end Balaban.LargeField
