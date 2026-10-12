/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.ActionConvDef
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
# Finite algebra of the restricted action (P631 §1, §4 items 1-2)

* `Region.bondPair_green`: the regional Green formula (5),
  `⟨∂w, ∂φ⟩_{D*} = ⟨w, -Δφ⟩_D + S_D(w, φ)`, a finite bond sum on the torus;
* `Region.blockPair_blockAvg`: the block average is self-adjoint on a union of cubes;
* `bulkDiv_of_isEL`: the pointwise form of the Euler-Lagrange equation on `Ω₁`.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

namespace Region

theorem sum_sites_eq (D : Region G) (F : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x ∈ D.sites, F x = ∑ x, if x ∈ D.sites then F x else 0 := by
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-- The scalar Green formula for one direction and one component. -/
theorem green_scalar (D : Region G) (μ : Fin d) (f w : Torus d (N₀ * L ^ K) → ℂ) :
    ∑ x, (D.starWeight x μ : ℂ) * ((f (x + Pi.single μ 1) - f x) * (w (x + Pi.single μ 1) - w x)) =
      ∑ x ∈ D.sites, w x * (2 * f x - f (x + Pi.single μ 1) - f (x - Pi.single μ 1)) +
      ∑ x, ((if x ∈ D.sites then (1 : ℂ) else 0) - (if x + Pi.single μ 1 ∈ D.sites then 1 else 0)) *
        (((w x + w (x + Pi.single μ 1)) / 2) * (f (x + Pi.single μ 1) - f x)) := by
  classical
  have hshift : ∑ x, (if x ∈ D.sites then w x * (f x - f (x - Pi.single μ 1)) else 0) =
      ∑ x, (if x + Pi.single μ 1 ∈ D.sites then
        w (x + Pi.single μ 1) * (f (x + Pi.single μ 1) - f x) else 0) := by
    have := sum_shiftC (Pi.single μ 1 : Torus d (N₀ * L ^ K))
      (fun x => if x ∈ D.sites then w x * (f x - f (x - Pi.single μ 1)) else 0)
    simp only [add_sub_cancel_right] at this
    exact this.symm
  have hD : ∑ x ∈ D.sites, w x * (2 * f x - f (x + Pi.single μ 1) - f (x - Pi.single μ 1)) =
      ∑ x, ((if x ∈ D.sites then w x * (f x - f (x + Pi.single μ 1)) else 0) +
        (if x + Pi.single μ 1 ∈ D.sites then
          w (x + Pi.single μ 1) * (f (x + Pi.single μ 1) - f x) else 0)) := by
    rw [Finset.sum_add_distrib, ← hshift, ← Finset.sum_add_distrib, sum_sites_eq]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [hD, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold starWeight
  split_ifs <;> push_cast <;> ring

theorem sum_xmi_eq_imx {ι : Type*} (s : Finset ι) (T : ι → Fin d → Fin N → ℂ) :
    ∑ x ∈ s, ∑ μ, ∑ i, T x μ i = ∑ i, ∑ μ, ∑ x ∈ s, T x μ i := by
  calc ∑ x ∈ s, ∑ μ, ∑ i, T x μ i = ∑ x ∈ s, ∑ i, ∑ μ, T x μ i :=
        Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ i, ∑ x ∈ s, ∑ μ, T x μ i := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_comm

/-- **The regional Green formula** (P631 (5)): `⟨∂w, ∂f⟩_{D*} = ⟨w, -Δ f⟩_D + S_D(w, f)`. -/
theorem bondPair_green (D : Region G) (w f : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    D.bondPair w f =
      D.massPair w (fun x i => negLap (fun y => f y i) x) + D.starPair w f := by
  classical
  have hstar : D.starPair w f = ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      ((if x ∈ D.sites then (1 : ℂ) else 0) - (if x + Pi.single μ 1 ∈ D.sites then 1 else 0)) *
        ∑ i, ((w x i + w (x + Pi.single μ 1) i) / 2) * (f (x + Pi.single μ 1) i - f x i) := by
    unfold starPair crossing
    rw [Finset.sum_filter, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    unfold outwardDeriv
    by_cases h1 : x ∈ D.sites <;> by_cases h2 : x + Pi.single μ 1 ∈ D.sites <;>
      (simp [h1, h2]; try (rw [← Finset.sum_neg_distrib]; exact Finset.sum_congr rfl fun i _ => by ring))
  rw [hstar]
  unfold bondPair massPair
  have e1 : ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d, (D.starWeight x μ : ℂ) *
      ∑ i, (w (x + Pi.single μ 1) i - w x i) * (f (x + Pi.single μ 1) i - f x i) =
      ∑ i, ∑ μ : Fin d, ∑ x : Torus d (N₀ * L ^ K), (D.starWeight x μ : ℂ) *
        ((f (x + Pi.single μ 1) i - f x i) * (w (x + Pi.single μ 1) i - w x i)) := by
    rw [← sum_xmi_eq_imx (Finset.univ)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e2 : ∑ x ∈ D.sites, ∑ i, w x i * negLap (fun y => f y i) x =
      ∑ i, ∑ μ : Fin d, ∑ x ∈ D.sites, w x i *
        (2 * f x i - f (x + Pi.single μ 1) i - f (x - Pi.single μ 1) i) := by
    refine Eq.trans ?_ (sum_xmi_eq_imx D.sites (fun x μ i => w x i *
      (2 * f x i - f (x + Pi.single μ 1) i - f (x - Pi.single μ 1) i)))
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [negLap, Finset.mul_sum]
    exact Finset.sum_comm
  have e3 : ∑ x : Torus d (N₀ * L ^ K), ∑ μ : Fin d,
      ((if x ∈ D.sites then (1 : ℂ) else 0) - (if x + Pi.single μ 1 ∈ D.sites then 1 else 0)) *
        ∑ i, ((w x i + w (x + Pi.single μ 1) i) / 2) * (f (x + Pi.single μ 1) i - f x i) =
      ∑ i, ∑ μ : Fin d, ∑ x : Torus d (N₀ * L ^ K),
        ((if x ∈ D.sites then (1 : ℂ) else 0) - (if x + Pi.single μ 1 ∈ D.sites then 1 else 0)) *
          (((w x i + w (x + Pi.single μ 1) i) / 2) * (f (x + Pi.single μ 1) i - f x i)) := by
    rw [← sum_xmi_eq_imx (Finset.univ)]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun μ _ => ?_
    rw [Finset.mul_sum]
  rw [e1, e2, e3, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun μ _ => ?_
  exact green_scalar D μ (fun y => f y i) (fun y => w y i)

/-- **The block average is self-adjoint on a union of cubes**: for `g` constant on the blocks,
`⟨Q u, g⟩_{D₁} = ⟨u, g⟩_{D₁}`. -/
theorem blockPair_blockAvg (D : Region G) (a : ℕ → ℝ) (u : G.Ω 1 × Fin N → ℂ)
    (g : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hg : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, g y i = g x i) :
    D.blockPair a (fun x i => blockAvg G u x i) g = D.blockPair a (svec G u) g := by
  classical
  unfold blockPair
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm, Finset.sum_comm (s := D.sites)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have key := blk_sum_comm G a (fun y => g y i)
    (fun y => if y ∈ D.sites then svec G u y i else 0) (hg i)
  rw [Finset.sum_coe_sort (G.Ω 1) (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      g x i * ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) *
        ∑ y ∈ G.blk (G.layerIndex x) x, if y ∈ D.sites then svec G u y i else 0)),
    Finset.sum_coe_sort (G.Ω 1) (fun x => ((a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) *
      g x i * (if x ∈ D.sites then svec G u x i else 0))] at key
  have hout : ∀ x ∈ G.Ω 1, x ∉ D.sites →
      (∑ y ∈ G.blk (G.layerIndex x) x, if y ∈ D.sites then svec G u y i else 0) = 0 := by
    intro x hx hxD
    refine Finset.sum_eq_zero fun y hy => ?_
    have hyD : y ∉ D.sites := fun hyD =>
      hxD (D.blockClosed y hyD x ((mem_blk_iff G hx).1 hy).2.2)
    simp [hyD]
  have hin : ∀ x ∈ D.sites,
      (∑ y ∈ G.blk (G.layerIndex x) x, if y ∈ D.sites then svec G u y i else 0) =
        ∑ y ∈ G.blk (G.layerIndex x) x, svec G u y i := by
    intro x hx
    refine Finset.sum_congr rfl fun y hy => ?_
    simp [D.blockClosed x hx y hy]
  have e1 := Finset.sum_subset D.sub_Ω (f := fun x => ((a (G.layerIndex x) /
      ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) * g x i * ((((((L : ℝ) ^ G.layerIndex x) ^ d)⁻¹ : ℝ) : ℂ) *
        ∑ y ∈ G.blk (G.layerIndex x) x, if y ∈ D.sites then svec G u y i else 0))
    (fun x hx hxD => by simp [hout x hx hxD])
  have e2 := Finset.sum_subset D.sub_Ω (f := fun x => ((a (G.layerIndex x) /
      ((L : ℝ) ^ G.layerIndex x) ^ 2 : ℝ) : ℂ) * g x i *
        (if x ∈ D.sites then svec G u x i else 0)) (fun x hx hxD => by simp [hxD])
  rw [← e1, ← e2] at key
  refine (Finset.sum_congr rfl fun x hx => ?_).trans (key.trans (Finset.sum_congr rfl fun x hx => ?_))
  · rw [hin x hx]
    unfold levelCoeff blockAvg
    ring
  · simp only [hx, ite_true]
    unfold levelCoeff
    ring

end Region

/-- **The Euler-Lagrange equation, pointwise on `Ω₁`**: with the regional bulk divergence,
`-Δφ̄ = a(ψ - Qφ) + ν_el (h - φ) - αφ`. -/
theorem bulkDiv_of_isEL {a : ℕ → ℝ} {ν : ℝ} {Dat : BgData G N} {φ : G.Ω 1 × Fin N → ℂ}
    {α : G.Ω 1 → ℂ} (h : IsEL G a ν Dat φ α) {x : Torus d (N₀ * L ^ K)} (hx : x ∈ G.Ω 1)
    (i : Fin N) :
    bulkDiv Dat φ x i = levelCoeff G a x * (Dat.Ψ x i - blockAvg G φ x i) +
      (ν : ℂ) * (Dat.h x i - svec G φ x i) - zeroExt (G.Ω 1) α x * svec G φ x i := by
  have h1 := congrFun h.1 (⟨x, hx⟩, i)
  rw [H_alpha_apply, H0_apply] at h1
  have h2 := lap_bar Dat φ ⟨x, hx⟩ i
  have h3 : bulkDiv Dat φ x i = lapVec G φ (⟨x, hx⟩, i) - boundaryTerm G Dat.Ψ (⟨x, hx⟩, i) := h2
  rw [h3]
  have h4 : svec G φ x i = φ (⟨x, hx⟩, i) := svec_of_mem G φ ⟨x, hx⟩ i
  have h5 : zeroExt (G.Ω 1) α x = α ⟨x, hx⟩ :=
    zeroExt_mem (G.Ω 1) α ⟨x, hx⟩
  rw [h4, h5]
  have h6 : blockVec G a φ (⟨x, hx⟩, i) = levelCoeff G a x * blockAvg G φ x i := rfl
  have h7 : source G a ν Dat (⟨x, hx⟩, i) = levelCoeff G a x * Dat.Ψ x i +
      (ν : ℂ) * Dat.h x i + boundaryTerm G Dat.Ψ (⟨x, hx⟩, i) := rfl
  rw [h7, h6] at h1
  linear_combination h1

/-- The hard-spin constraints of `φ` and `φ_u` give `w·w = -2 φ·w` on `Ω₁`, `w = φ_u - φ`. -/
theorem hardspin_diff {φ φu : G.Ω 1 × Fin N → ℂ} (hφ : ∀ x : G.Ω 1, ∑ i, φ (x, i) * φ (x, i) = 1)
    (hφu : ∀ x : G.Ω 1, ∑ i, φu (x, i) * φu (x, i) = 1) (x : G.Ω 1) :
    ∑ i, (φu - φ) (x, i) * (φu - φ) (x, i) = -2 * ∑ i, (φu - φ) (x, i) * φ (x, i) := by
  have h1 := hφ x
  have h2 := hφu x
  have e : ∑ i, φu (x, i) * φu (x, i) = ∑ i, φ (x, i) * φ (x, i) +
      2 * ∑ i, (φu - φ) (x, i) * φ (x, i) + ∑ i, (φu - φ) (x, i) * (φu - φ) (x, i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.sub_apply]; ring
  linear_combination h2 - h1 - e


end Balaban.LargeField.ActionConv
