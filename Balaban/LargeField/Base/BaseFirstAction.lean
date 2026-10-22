module

public import Balaban.LargeField.Base.BaseChartActionBridge
public import Balaban.LargeField.Base.BaseChartQuadraticPhysical

/-!
# The first-step background action at the single scale

For the first physical step the exponent is `β A₁(φ; θ)` with
`A₁(φ; θ) = H(φ) + (a L^{d-2} / 2) Σ_y |θ_y - (Qφ)_y|²` on the fine lattice of unit spins.
At the background field `e_θ = baseSectorCenter` this is the action of the whole-lattice
generating set at the lifted datum, evaluated at `bgField`.  This file states that identity on the
single-scale generating set; `BaseFirstActionClass` transports it to the class at scale `1`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Background Balaban.Multiscale Matrix

variable {d N L n : ℕ} [NeZero L] [NeZero n]

open Classical

private theorem baseFirst_cast_roundtrip_back {α : Type*} {F : α → Type*} {a b : α}
    (e : a = b) (x : F a) : e.symm ▸ (e ▸ x) = x := by
  cases e
  rfl

/-- **The first-step action at the background field.**  On the real data domain of the lifted
datum, the action of the single-scale generating set at `bgField` is the physical first-step
action `A₁(e_θ; θ) = energy(e_θ) + (a₀ L^d / (2 L²)) Σ_y |θ_y - (Q e_θ)_y|²`, with `a₀ = aw 1`
and `e_θ = baseSectorCenter`. -/
theorem baseFirst_action_bgField (ϱ : ℝ) (aw : ℕ → ℝ) (a₀ : ℝ) (ha : aw 1 = a₀)
    (regimeB : Prop) (ν : ℝ) (h : EuclideanSpace ℝ (Fin N)) (hh : ‖h‖ = 1)
    (H : BgHyp d L 1 ϱ aw (if regimeB then ν else 0))
    (θ : Torus d n → EuclideanSpace ℝ (Fin N))
    (hU : InUnionDomainR (GeneratingSet.single (d := d) (L := L)
      (N₀ := 1 * n) (k := 1) ϱ) (bgC1 d L N) (if regimeB then ν else 0)
      (baseSectorDatum ϱ θ h)) :
    let G := GeneratingSet.single (d := d) (L := L) (N₀ := 1 * n) (k := 1) ϱ
    let D := baseSectorDatum ϱ θ h
    let e : Torus d (L * n) → EuclideanSpace ℝ (Fin N) := baseSectorCenter ϱ aw regimeB ν h θ
    let ec : CfgT d N L n := fun x => ⟨e x,
      mem_sphere_zero_iff_norm.mpr (baseSectorCenter_unit ϱ aw regimeB ν h hh H θ x)⟩
    action G aw (if regimeB then ν else 0) D (bgField G aw (if regimeB then ν else 0) D) =
      energy d N (L * n) (if regimeB then ν else 0) h ec +
        (a₀ * (L : ℝ) ^ d / (2 * (L : ℝ) ^ 2)) *
          ∑ y : Torus d n, ‖θ y - baseQ d N L n ec y‖ ^ 2 := by
  intro G D e ec
  have hφ := baseSector_action_eq_physical ϱ aw a₀ (if regimeB then ν else 0) ha h θ ec
  have he : (fun p : G.Ω 1 × Fin N => (((ec (baseSector_side L n ▸
      (p.1 : Torus d (1 * n * L ^ 1))) : EuclideanSpace ℝ (Fin N)) p.2 : ℝ) : ℂ)) =
      bgField G aw (if regimeB then ν else 0) D := by
    funext p
    have hc := baseSectorCenter_eq_background ϱ aw regimeB ν h H θ hU
      (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) p.2
    have hr : (baseSector_side L n).symm ▸
        (baseSector_side L n ▸ (p.1 : Torus d (1 * n * L ^ 1))) =
          (p.1 : Torus d (1 * n * L ^ 1)) :=
      baseFirst_cast_roundtrip_back (F := fun m : ℕ => Torus d m)
        (baseSector_side L n) (p.1 : Torus d (1 * n * L ^ 1))
    rw [hr] at hc
    exact hc
  rw [← he]
  exact hφ

/-- **The field renormalization at a fixed spin configuration.**  With `θ' = z θ`, the block term
of `A₁` expands exactly in `ζ = z - 1`:
`Σ_y |zθ_y - q_y|² = Σ_y |θ_y - q_y|² + 2ζ Σ_y ⟨θ_y, θ_y - q_y⟩ + ζ² Σ_y |θ_y|²`
(P4 (4.1), `θ = z₁ψ₁`).  This is the part of the difference between the exponent at `z₁ψ₁` and at
`ψ₁` that is explicit; the background field itself also moves with the data. -/
theorem baseFirst_block_scale (z : ℝ) (θ q : Torus d n → EuclideanSpace ℝ (Fin N)) :
    ∑ y, ‖z • θ y - q y‖ ^ 2 =
      ∑ y, ‖θ y - q y‖ ^ 2 + 2 * (z - 1) * ∑ y, inner ℝ (θ y) (θ y - q y) +
        (z - 1) ^ 2 * ∑ y, ‖θ y‖ ^ 2 := by
  have key : ∀ y, ‖z • θ y - q y‖ ^ 2 =
      ‖θ y - q y‖ ^ 2 + 2 * (z - 1) * inner ℝ (θ y) (θ y - q y) +
        (z - 1) ^ 2 * ‖θ y‖ ^ 2 := by
    intro y
    have h1 : z • θ y - q y = (θ y - q y) + (z - 1) • θ y := by
      rw [sub_smul, one_smul]; abel
    rw [h1, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      real_inner_comm]
    ring
  simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum]

end Balaban.LargeField
