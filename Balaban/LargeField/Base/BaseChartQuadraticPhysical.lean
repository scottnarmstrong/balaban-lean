module

public import Balaban.LargeField.Base.BaseChartActionPhysical
public import Balaban.LargeField.Base.ChordQuadratic

/-!
# The first-step background in the hard-spin chord identity

For the physical first step, the block weight in P4 (2.42)–(2.44) is `a₀ = aw 1`.
The centre `baseSectorCenter` is a background field only on the real data domain;
outside that domain its definition uses the constant fallback `h`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix

variable {d N L n : ℕ} [NeZero L] [NeZero n]

open Classical

private theorem baseSector_cast_roundtrip_back {α : Type*} {F : α → Type*} {a b : α}
    (e : a = b) (x : F a) : e.symm ▸ (e ▸ x) = x := by
  cases e
  rfl

/-- The fine-site block coefficient of the single-scale action is the physical first-step
weight. After summing a block of `L^d` sites this is the coefficient of P4 (2.42). -/
theorem baseSector_weight_match (ϱ : ℝ) (aw : ℕ → ℝ) (a₀ : ℝ)
    (ha : aw 1 = a₀) (x : Torus d (1 * n * L ^ 1)) :
    aw ((GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ).layerIndex x) /
        ((L : ℝ) ^ (GeneratingSet.single (d := d) (L := L)
          (N₀ := 1 * n) (k := 1) ϱ).layerIndex x) ^ 2 =
      a₀ / (L : ℝ) ^ 2 := by
  rw [layerIndex_single (ϱ := ϱ) (d := d) (L := L)
    (N₀ := 1 * n) (k := 1) le_rfl x, ha, pow_one]

/-- On the real data domain, the centre is the real background field in physical coordinates. -/
theorem baseSectorCenter_eq_background (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h))
    (x : Torus d (L * n)) (i : Fin N) :
    (baseSectorCenter ϱ aw regimeB ν h θ x i : ℂ) =
      bgField (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
        aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
        (⟨(baseSector_side L n).symm ▸ x,
          baseSector_mem_single ϱ ((baseSector_side L n).symm ▸ x)⟩, i) := by
  classical
  let y : Torus d (1 * n * L ^ 1) := (baseSector_side L n).symm ▸ x
  have hy : y ∈ (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ).Ω 1 := baseSector_mem_single ϱ y
  have hreal : (bgField (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h) (⟨y, hy⟩, i)).im = 0 := by
    exact ((theorem71 (G := GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) H hU).2.1 ⟨y, hy⟩).1 i
  simp only [baseSectorCenter, hU, reduceIte]
  apply Complex.ext
  · simp
  · change 0 = (bgField (GeneratingSet.single (d := d) (L := L)
        (N₀ := 1 * n) (k := 1) ϱ) aw (if regimeB then ν else 0)
        (baseSectorDatum ϱ θ h) (⟨y, hy⟩, i)).im
    exact hreal.symm

/-- The real physical centre solves the constrained Euler–Lagrange equation of the lifted
first-step datum on the real data domain (P4 (2.43)–(2.44), at hard spin). -/
theorem baseSectorCenter_isEL (ϱ : ℝ) (aw : ℕ → ℝ) (regimeB : Prop) (ν : ℝ)
    (h : EuclideanSpace ℝ (Fin N))
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h)) :
    IsEL (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
      aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)
      (fun p => ((baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ))
      (bgMult (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
        aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h)) := by
  have he : (fun p : (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ).Ω 1 × Fin N => ((baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)) =
      bgField (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ)
        aw (if regimeB then ν else 0) (baseSectorDatum ϱ θ h) := by
    funext p
    have h := baseSectorCenter_eq_background ϱ aw regimeB ν h H θ hU
      (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2
    have hr : (baseSector_side L n).symm ▸
        (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) =
          (p.1 : Torus d (1 * n * L ^ 1)) :=
      baseSector_cast_roundtrip_back (F := fun m : ℕ => Torus d m)
        (baseSector_side L n) (p.1 : Torus d (1 * n * L ^ 1))
    rw [hr] at h
    exact h
  rw [he]
  exact ((theorem71 (G := GeneratingSet.single (d := d) (L := L)
    (N₀ := 1 * n) (k := 1) ϱ) H hU).2.2.1).1

/-- The constrained chord formula at the physical first-step centre, on its real data domain.
The operator is the first-block Hessian with weight `aw 1`, which P4 (2.42)–(2.44)
identifies with the physical weight `a₀`. -/
theorem baseSectorCenter_action_sub_eq_chord (ϱ : ℝ) (aw : ℕ → ℝ)
    (regimeB : Prop) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h))
    (σ : (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ).Ω 1 × Fin N → ℂ)
    (hσ : IsRealUnitField (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) σ) :
    let G := GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ
    let D := baseSectorDatum ϱ θ h
    let e : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)
    let α := bgMult G aw (if regimeB then ν else 0) D
    (((action G aw (if regimeB then ν else 0) D σ -
      action G aw (if regimeB then ν else 0) D e : ℝ)) : ℂ) =
        (1 / 2) * pair G (σ - e)
          (liftOp N (dirichletOperator G aw (if regimeB then ν else 0) α) *ᵥ (σ - e)) := by
  dsimp only
  let G : GeneratingSet d L (1 * n) 1 ϱ := GeneratingSet.single ϱ
  let D : BgData G N := baseSectorDatum ϱ θ h
  let e : G.Ω 1 × Fin N → ℂ := fun p =>
    ((baseSectorCenter ϱ aw regimeB ν h θ
      (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)
  have he : e = bgField G aw (if regimeB then ν else 0) D := by
    funext p
    have hc := baseSectorCenter_eq_background ϱ aw regimeB ν h H θ hU
      (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2
    have hr : (baseSector_side L n).symm ▸
        (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) =
          (p.1 : Torus d (1 * n * L ^ 1)) :=
      baseSector_cast_roundtrip_back (F := fun m : ℕ => Torus d m)
        (baseSector_side L n) (p.1 : Torus d (1 * n * L ^ 1))
    rw [hr] at hc
    exact hc
  have hEL : IsEL G aw (if regimeB then ν else 0) D e
      (bgMult G aw (if regimeB then ν else 0) D) :=
    baseSectorCenter_isEL ϱ aw regimeB ν h H θ hU
  have hreal : D.IsReal := by
    obtain ⟨δ, _, _, hDδ⟩ := hU
    exact isReal_of_inDomainR hDδ
  have hunit : IsRealUnitField G e := by
    rw [he]
    exact (theorem71 (G := G) H hU).2.1
  exact action_sub_eq_chord_quadratic D hreal hEL hunit hσ

/-- On the all-good P5 cube support, the domain premise of the centre chord theorem follows
from the actual physical cutoff. -/
theorem baseSectorCenter_action_sub_eq_chord_of_product_ne_zero
    (ϱ : ℝ) (aw : ℕ → ℝ) (regimeB : Prop) (ν δ₀ : ℝ) (hδ : 0 < δ₀)
    (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (hΛ1 : 4 * d * L * δ₀ ≤ bgC1 d L N)
    (θ : Torus d n → EuclideanSpace ℝ (Fin N)) (φ : CfgT d N L n)
    (hp : baseSectorCubeProduct regimeB ν δ₀ h θ φ ≠ 0)
    (σ : (GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n)
      (k := 1) ϱ).Ω 1 × Fin N → ℂ)
    (hσ : IsRealUnitField (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) σ) :
    let G := GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ
    let D := baseSectorDatum ϱ θ h
    let e : G.Ω 1 × Fin N → ℂ := fun p =>
      ((baseSectorCenter ϱ aw regimeB ν h θ
        (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2 : ℝ) : ℂ)
    let α := bgMult G aw (if regimeB then ν else 0) D
    (((action G aw (if regimeB then ν else 0) D σ -
      action G aw (if regimeB then ν else 0) D e : ℝ)) : ℂ) =
        (1 / 2) * pair G (σ - e)
          (liftOp N (dirichletOperator G aw (if regimeB then ν else 0) α) *ᵥ (σ - e)) := by
  exact baseSectorCenter_action_sub_eq_chord ϱ aw regimeB ν h H θ
    (baseSectorDatum_domain_of_product_ne_zero ϱ aw regimeB ν δ₀ hδ h hh H
      hΛ1 θ φ hp) σ hσ

/-- The hard-spin normal-coordinate exponent after the exact chord identity: the Gaussian
quadratic form plus the mixed/normal term, residual mass, complex source and logarithmic
Jacobian. This is the sphere-chart counterpart of P4 (2.45)–(2.48). -/
theorem baseChart_pointwise_quadratic_remainder {ι : Type*} [Fintype ι]
    {β : ℝ} (hβ : 0 < β) (e : Config ι N)
    (H : Config ι N →ₗ[ℝ] Config ι N)
    (hsymm : ∀ u v, cinner u (H v) = cinner (H u) v)
    (w : Config ι N) (ν μ : ℝ) (h : EuclideanSpace ℝ (Fin N))
    (g : ι → Fin N → ℂ) :
    let z := chartShift β e w
    let Φ := chartPoint β e w
    let M := β * (ν - μ) / 2 * ∑ x, ‖Φ x - h‖ ^ 2
    let S₀ := ∑ x, ∑ i, g x i * (((e x) i : ℝ) : ℂ)
    let S₁ := (((Real.sqrt β)⁻¹ : ℝ) : ℂ) *
      (∑ x, ∑ i, g x i * ((((w x + z x) i : ℝ)) : ℂ))
    ((sphereExponent β e H Φ : ℝ) : ℂ) - (M : ℂ) +
        (∑ x, ∑ i, g x i * (((Φ x) i : ℝ) : ℂ)) +
        ((Real.log (chartJac β w) : ℝ) : ℂ) =
      -(((1 / 2) * cinner w (H w) : ℝ) : ℂ) + S₀ + S₁ -
        ((cinner w (H z) + (1 / 2) * cinner z (H z) + M -
          Real.log (chartJac β w) : ℝ) : ℂ) := by
  dsimp only
  rw [sphereExponent_chartPoint hβ e H hsymm w,
    source_chartPoint_complex (β := β) e w g]
  unfold chartExponent
  push_cast
  ring

end Balaban.LargeField
