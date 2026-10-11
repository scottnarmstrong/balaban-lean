/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ApproxResidual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Real data (LEMMA53-astra.md, §4 (A6))

For real data `(ψ, h)` the approximate field and the residual are real, and the field is close to
the field of the corresponding complex data; the mass term is controlled by the real local estimate.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- A complex vector with real components. -/
def IsRealVec (v : Fin N → ℂ) : Prop := ∀ i, (v i).im = 0

theorem IsRealVec.eq_cplx {v : Fin N → ℂ} (h : IsRealVec v) : v = cplx (fun i => (v i).re) :=
  funext fun i => Complex.ext (by simp [cplx]) (by simp [cplx, h i])

theorem isRealVec_cplx (x : Fin N → ℝ) : IsRealVec (cplx x) := fun i => by simp [cplx]

theorem IsRealVec.normalize {v : Fin N → ℂ} (h : IsRealVec v) : IsRealVec (normalize v) := by
  rw [h.eq_cplx]
  have : Balaban.Background.normalize (cplx fun i => (v i).re) =
      cplx ((Real.sqrt ((fun i => (v i).re) ⬝ᵥ (fun i => (v i).re)))⁻¹ • fun i => (v i).re) := by
    funext i
    simp [Balaban.Background.normalize, sqrtDot_cplx, cplx]
  rw [this]
  exact isRealVec_cplx _

section Real

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem isRealVec_interp (Φ : Torus d (N₀ * L ^ k) → Fin N → ℂ) (hΦ : ∀ y ∈ G.Ω 1, IsRealVec (Φ y))
    (x : Torus d (N₀ * L ^ k)) : IsRealVec (interp G Φ x) := fun i => by
  simp only [interp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.im_sum,
    Complex.im_ofReal_mul]
  refine Finset.sum_eq_zero fun q hq => ?_
  obtain ⟨⟨hm1, hmk⟩, hql, -⟩ := (mem_blockIdx G).1 hq
  rw [hΦ q.2 (G.layer_subset hm1 hmk hql) i, mul_zero]

theorem isRealVec_locSol {Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hΨ : ∀ y ∈ dataSites G, IsRealVec (Ψ y)) (hh : ∀ y ∈ G.Ω 1, IsRealVec (h y))
    {y : Torus d (N₀ * L ^ k)} (hy : y ∈ dataSites G) : IsRealVec (locSol G a ν Ψ h y) := by
  classical
  by_cases hy1 : y ∈ G.Ω 1
  · simp only [locSol, hy1, ite_true]
    rw [(hΨ y hy).eq_cplx, (hh y hy1).eq_cplx, cMinimizer_cplx]
    exact isRealVec_cplx _
  · simp only [locSol, hy1, ite_false]
    have h0 : (0 : Fin N → ℂ) = cplx 0 := by funext i; simp [cplx]
    rw [(hΨ y hy).eq_cplx, h0, cMinimizer_cplx]
    exact isRealVec_cplx _

theorem isRealVec_approxField {Ψ h : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    (hΨ : ∀ y ∈ dataSites G, IsRealVec (Ψ y)) (hh : ∀ y ∈ G.Ω 1, IsRealVec (h y))
    {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    IsRealVec (approxField G a ν Ψ h x) := by
  classical
  by_cases hx1 : x ∈ G.Ω 1
  · by_cases hl1 : G.layerIndex x ≤ 1
    · simp only [approxField, hx1, ite_true, hl1]
      exact isRealVec_locSol hΨ hh hx
    · simp only [approxField, hx1, ite_true, hl1, ite_false]
      refine IsRealVec.normalize (isRealVec_interp _ (fun y hy => ?_) x)
      exact isRealVec_locSol hΨ hh ((mem_dataSites G).2 (Or.inl hy))
  · have hc : x ∈ collar G := ((mem_dataSites G).1 hx).resolve_left hx1
    simp only [approxField, hx1, ite_false, hc, ite_true]
    exact isRealVec_locSol hΨ hh hx


theorem residual_real (D : BgData G N) (φ : Torus d (N₀ * L ^ k) → Fin N → ℂ)
    (hφ : ∀ y ∈ dataSites G, IsRealVec (φ y)) (hΨ : ∀ y ∈ dataSites G, IsRealVec (D.Ψ y))
    (hh : ∀ y ∈ G.Ω 1, IsRealVec (D.h y)) (x : G.Ω 1) (i : Fin N) :
    (residual G a ν D φ (x, i)).im = 0 := by
  classical
  let R : Subring ℂ := Complex.ofRealHom.range
  have hRe : ∀ z : ℂ, z.im = 0 → z ∈ R := fun z hz => ⟨z.re, Complex.ext (by simp) (by simp [hz])⟩
  have hRe' : ∀ z : ℂ, z ∈ R → z.im = 0 := by rintro z ⟨r, rfl⟩; simp
  have hofReal : ∀ r : ℝ, ((r : ℝ) : ℂ) ∈ R := fun r => ⟨r, rfl⟩
  have h2 : (2 : ℂ) ∈ R := ⟨2, by simp⟩
  have hx := x.2
  obtain ⟨hn1, hnk, hxl⟩ := G.layerIndex_spec hx
  have hxd : x.1 ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
  have hΦR : ∀ y ∈ dataSites G, φ y i ∈ R := fun y hy => hRe _ (hφ y hy i)
  have hΨR : ∀ y ∈ dataSites G, D.Ψ y i ∈ R := fun y hy => hRe _ (hΨ y hy i)
  have hnb : ∀ z, Adj x.1 z → z ∈ dataSites G := fun z hz => by
    by_cases h : z ∈ G.Ω 1
    · exact (mem_dataSites G).2 (Or.inl h)
    · exact (mem_dataSites G).2 (Or.inr (mem_collar_of_adj G hx h hz))
  apply hRe'
  rw [residual_apply]
  refine R.add_mem (R.add_mem (R.add_mem ?_ ?_) ?_) ?_
  · refine R.mul_mem (hofReal _) (R.sub_mem (hΨR _ hxd) (R.mul_mem (hofReal _) (R.sum_mem fun y hy => ?_)))
    exact hΦR y ((mem_dataSites G).2 (Or.inl (G.layer_subset hn1 hnk
      (mem_layer_of_mem_blk G hn1 hnk hxl hy))))
  · exact R.mul_mem (hofReal _) (R.sub_mem (hRe _ (hh x.1 hx i)) (hΦR _ hxd))
  · refine R.sum_mem fun μ _ => ?_
    exact R.sub_mem (R.add_mem (hΦR _ (hnb _ (adj_add x.1 μ))) (hΦR _ (hnb _ (adj_sub x.1 μ))))
      (R.mul_mem h2 (hΦR _ hxd))
  · refine R.sum_mem fun μ _ => R.add_mem ?_ ?_
    · split_ifs
      · exact R.sub_mem (hΨR _ (hnb _ (adj_add x.1 μ))) (hΦR _ (hnb _ (adj_add x.1 μ)))
      · exact R.zero_mem
    · split_ifs
      · exact R.sub_mem (hΨR _ (hnb _ (adj_sub x.1 μ))) (hΦR _ (hnb _ (adj_sub x.1 μ)))
      · exact R.zero_mem

end Real

end Balaban.Background
