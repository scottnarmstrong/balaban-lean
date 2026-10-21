/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseRecordInstance
public import Balaban.LargeField.Base.BaseRetainedDisintegrate

/-!
# The interior spins of the retained decomposition are the spins of the good region

For the good region `Ω` given by a generating set `G`, the set of physical sites `retSet G` outside
`Ω` carries the retained spins; the complementary sites are in bijection with `G.Ω 1`
(`siteEquivΩ`).  The integral over the interior spins of the iterated integral of
`baseRetained_disintegrate` is the integral over the spins of `G.Ω 1` of the integrand at the
merged configuration (`integral_interior_eq_merge`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Classical MeasureTheory

noncomputable section

variable {d N L n : ℕ} [NeZero L] [NeZero n] {ϱ : ℝ} (G : GeneratingSet d L (1 * n) 1 ϱ)

/-- **The retained sites**: the physical sites whose native site lies outside `Ω`. -/
def retSet : Set (Torus d (L * n)) := {x | (baseSector_side L n).symm ▸ x ∉ G.Ω 1}

/-- The interior sites are in bijection with the sites of the good region. -/
def siteEquivΩ : G.Ω 1 ≃ ↥(retSet G)ᶜ where
  toFun x := ⟨baseSector_side L n ▸ (x : Torus d (1 * n * L ^ 1)), by
    intro hx
    apply hx
    rw [cast_roundtrip_rev (F := fun m : ℕ => Torus d m) (baseSector_side L n)]
    exact x.2⟩
  invFun y := ⟨(baseSector_side L n).symm ▸ (y : Torus d (L * n)), by
    by_contra hy
    exact y.2 hy⟩
  left_inv x := by
    apply Subtype.ext
    exact cast_roundtrip_rev (F := fun m : ℕ => Torus d m) (baseSector_side L n) x
  right_inv y := by
    apply Subtype.ext
    exact cast_roundtrip_fwd (F := fun m : ℕ => Torus d m) (baseSector_side L n) y

/-- A change of the index set of the spins preserves the product sphere measure. -/
theorem integral_pi_sphere_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι')
    (Φ : (ι' → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) → ℂ) :
    ∫ η, Φ η ∂(Measure.pi fun _ : ι' => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫ ψ, Φ (fun y => ψ (e.symm y))
        ∂(Measure.pi fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  have hmp := measurePreserving_arrowCongr'
    (fun _ : ι => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere)
    (fun _ : ι' => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) e
    (MeasurableEquiv.refl (Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1))
    (fun _ => MeasurePreserving.id _)
  have := hmp.integral_comp' (g := Φ)
  rw [← this]
  rfl

/-- The configuration of the physical torus that is the retained spins `σ` on the retained sites
and the fixed spin `ε₀` elsewhere. -/
def retExtend (σ : ↥(retSet G) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (ε₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) : CfgT d N L n :=
  fun x => if hx : x ∈ retSet G then σ ⟨x, hx⟩ else ε₀

/-- The merge of the retained and the interior spins is the merge of the retained spins with the
spins of the good region. -/
theorem merge_eq_baseMerge (σ : ↥(retSet G) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (ε₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    (fun x : Torus d (L * n) => if hx : x ∈ retSet G then σ ⟨x, hx⟩
        else ((fun y : ↥(retSet G)ᶜ => ψ ((siteEquivΩ G).symm y)) ⟨x, hx⟩)) =
      baseMerge G (retExtend G σ ε₀) ψ := by
  funext x
  by_cases hx : x ∈ retSet G
  · have hx' : ¬ ((baseSector_side L n).symm ▸ x ∈ G.Ω 1) := hx
    simp only [hx, ↓reduceDIte, baseMerge, hx', retExtend]
  · have hx' : (baseSector_side L n).symm ▸ x ∈ G.Ω 1 := by
      by_contra h; exact hx h
    simp only [hx, ↓reduceDIte, baseMerge, hx']
    rfl

/-- **The interior integral of the retained decomposition** is the integral over the spins of the
good region of the integrand at the merged configuration. -/
theorem integral_interior_eq_merge (f : CfgT d N L n → ℂ)
    (σ : ↥(retSet G) → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1)
    (ε₀ : Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1) :
    ∫ η : ↥(retSet G)ᶜ → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
        f (fun x => if hx : x ∈ retSet G then σ ⟨x, hx⟩ else η ⟨x, hx⟩)
        ∂(Measure.pi fun _ : ↥(retSet G)ᶜ =>
          (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) =
      ∫ ψ : G.Ω 1 → Metric.sphere (0 : EuclideanSpace ℝ (Fin N)) 1,
        f (baseMerge G (retExtend G σ ε₀) ψ)
        ∂(Measure.pi fun _ : G.Ω 1 => (volume : Measure (EuclideanSpace ℝ (Fin N))).toSphere) := by
  rw [integral_pi_sphere_equiv (siteEquivΩ G) (fun η => f (fun x =>
    if hx : x ∈ retSet G then σ ⟨x, hx⟩ else η ⟨x, hx⟩))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ψ => ?_)
  exact congrArg f (merge_eq_baseMerge G σ ε₀ ψ)

/-- **The lifted datum of the retained spins and the coarse field.**  For a generating set `G` of
the first step there are data `D` that are the lifted coarse field on `Ω`, the retained spins on
the collar and the constant `h` on `Ω`. -/
theorem exists_recordDatum (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (h : EuclideanSpace ℝ (Fin N)) (φ₀ : CfgT d N L n) :
    ∃ D : BgData G N,
      (∀ x ∈ G.Ω 1, ∀ i, D.Ψ x i =
        ((baseSectorTheta θ (jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ)) ∧
      (∀ x ∈ collar G, ∀ i, D.Ψ x i = ((baseSectorSpin φ₀ x i : ℝ) : ℂ)) ∧
      (∀ x ∈ G.Ω 1, ∀ i, D.h x i = ((h i : ℝ) : ℂ)) := by
  let Ψ : Torus d (1 * n * L ^ 1) → Fin N → ℂ := fun x i =>
    if x ∈ G.Ω 1 then ((baseSectorTheta θ (jBlock d L (1 * n) 1 1 x) i : ℝ) : ℂ)
    else ((baseSectorSpin φ₀ x i : ℝ) : ℂ)
  let hh : Torus d (1 * n * L ^ 1) → Fin N → ℂ := fun _ i => ((h i : ℝ) : ℂ)
  have hΨ : IsLayerConstant G Ψ := by
    intro m hm1 hmk x hx x' hx'
    have hm : m = 1 := by omega
    subst hm
    have hx1 : x ∈ G.Ω 1 := G.layer_subset le_rfl le_rfl hx
    have hx'l : x' ∈ G.layer 1 := (G.mem_layer_iff le_rfl le_rfl (G.mem_blk.1 hx')).2 hx
    have hx'1 : x' ∈ G.Ω 1 := G.layer_subset le_rfl le_rfl hx'l
    funext i
    simp only [Ψ, hx1, hx'1, ↓reduceIte]
    rw [GeneratingSet.mem_blk.1 hx']
  have hhl : IsLayerConstant G hh := fun _ _ _ _ _ _ _ => rfl
  refine ⟨BgData.clip G Ψ hh hΨ hhl, ?_, ?_, ?_⟩
  · intro x hx i
    have hd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
    simp [BgData.clip, hd, Ψ, hx]
  · intro x hx i
    have hd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inr hx)
    have hxn : x ∉ G.Ω 1 := ((mem_collar G).1 hx).1
    simp [BgData.clip, hd, Ψ, hxn]
  · intro x hx i
    simp [BgData.clip, hx, hh]

end

end Balaban.LargeField
