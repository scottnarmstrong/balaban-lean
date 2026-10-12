/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Observables.LayerDef

/-!
# The layer at the constant configuration (OBSERVABLES.md §2.2, "Exact form of `G_k(h,h)`")

At the constant unit configuration `ψ ≡ h` (all composed pairs equal `(h, h)` and `φ_k ≡ h`):

* `Mk_const`: `M_k(x; h, h) = m_k(x) h` (P9 (4.10)), from the normalization (2.1) `normM`;
* `Gk_const`: `G_k(x, x'; h, h) = m_k(x) m_k(x') ∑_j β_{j-1}^{-1} G^{(j)}(x, x'; h, h) + R_k(x, x';
  h, h)` (2.6);
* `Gk_longitudinal`: if the Gaussian kernels are transverse at the constant configuration
  (Lemma 2.1, item 3: `hᵀ G^{(j)} = 0`), then `hᵀ G_k h = hᵀ R_k h` (2.7).

The hypotheses on the composed pairs and on `φ_k` are the statements `ψ_k^{(j)}(h, h) = h` and
`φ_k(·; h, h) = h` (zero energy of the constant configuration, BACKGROUND I-1).
-/

@[expose] public section

namespace Balaban.Observables

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
open Balaban.SmallField.Def6 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

section Const

variable {P : Consts} {Q : ObsConsts} {β ν a : ℕ → ℝ} {Tm : Terms d L N₁ m₁ k N ϱ}
  {Ot : ObsTerms d L N₁ m₁ k N}
  {Gker : ℕ → CTorus d L N₁ m₁ k → CTorus d L N₁ m₁ k → Fld d L N₁ m₁ k N →
    Fld d L N₁ m₁ k N → Matrix (Fin N) (Fin N) ℂ}

/-- **`M_k(x; h, h) = m_k(x) h`** at the constant unit configuration (P9 (4.10)). -/
theorem Mk_const (hO : IsObs P Q β ν a Tm Ot Gker) {v : Fin N → ℝ} (hv : v ⬝ᵥ v = 1)
    (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hφ : ∀ (x : CTorus d L N₁ m₁ k) (i : Fin N),
      svec (topGS d L N₁ m₁ k ϱ) (bgField (topGS d L N₁ m₁ k ϱ) (aIdeal L k (a k))
        (bgMass L k (β k) (ν k)) D) x i = (v i : ℂ))
    (hψ : ∀ j, 1 ≤ j → j ≤ k →
      composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D =
        (constFld (fun i => (v i : ℂ)), constFld (fun i => (v i : ℂ))))
    (x : CTorus d L N₁ m₁ k) (i : Fin N) :
    Mk P β ν a Ot D x i = (mFactor β Ot x : ℂ) * (v i : ℂ) := by
  have hsum : ∀ j ∈ Finset.Icc 1 k, ((Real.sqrt (β (j - 1)))⁻¹ : ℂ) *
      Mobs P.m₀ Ot j x (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).1
        (composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D).2 i = 0 := by
    intro j hj
    have hj' := Finset.mem_Icc.1 hj
    rw [hψ j hj'.1 hj'.2]
    have := hO.normM j hj'.1 hj'.2 x v hv
    simp only [this, Pi.zero_apply, mul_zero]
  simp only [Mk]
  rw [Finset.sum_eq_zero hsum, add_zero, hφ]

/-- **(2.6)**: `G_k(x, x'; h, h) = ∑_j β_{j-1}^{-1} m_k(x) m_k(x') G^{(j)}(x, x'; h, h) +
R_k(x, x'; h, h)`, with the composed pairs equal to `(h, h)`. -/
theorem Gk_const {v : Fin N → ℝ} (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hψ : ∀ j, 1 ≤ j → j ≤ k →
      composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D =
        (constFld (fun i => (v i : ℂ)), constFld (fun i => (v i : ℂ))))
    (x x' : CTorus d L N₁ m₁ k) :
    Gk P β ν a Ot Gker D x x' =
      (∑ j ∈ Finset.Icc 1 k, ((β (j - 1))⁻¹ * mFactor β Ot x * mFactor β Ot x' : ℝ) •
        Gker j x x' (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) +
      ∑ i ∈ Finset.Icc 1 k, ∑ j ∈ Finset.Icc i k, ((β (i - 1))⁻¹ : ℝ) •
        Robs P.m₀ Ot i j x x' (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ))) := by
  simp only [Gk, Ck, Rk]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.1 hj
    rw [hψ j hj'.1 hj'.2]
  · refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => ?_
    have hi' := Finset.mem_Icc.1 hi
    have hj' := Finset.mem_Icc.1 hj
    rw [hψ j (hi'.1.trans (Finset.mem_Icc.1 hj).1) hj'.2]

/-- **(2.7)**: if the kernels `G^{(j)}` are transverse at the constant configuration
(`vᵀ G^{(j)} = 0`, Lemma 2.1 item 3), the longitudinal part of `G_k` is that of `R_k`:
`vᵀ G_k(x, x'; h, h) v = vᵀ R_k(x, x'; h, h) v`. -/
theorem Gk_longitudinal {v : Fin N → ℝ} (D : BgData (topGS d L N₁ m₁ k ϱ) N)
    (hψ : ∀ j, 1 ≤ j → j ≤ k →
      composedPair (aIdeal L k (a k)) (bgMass L k (β k) (ν k)) j D =
        (constFld (fun i => (v i : ℂ)), constFld (fun i => (v i : ℂ))))
    (hG : ∀ j x x', Matrix.vecMul (fun i => (v i : ℂ))
      (Gker j x x' (constFld (fun i => (v i : ℂ))) (constFld (fun i => (v i : ℂ)))) = 0)
    (x x' : CTorus d L N₁ m₁ k) :
    (fun i => (v i : ℂ)) ⬝ᵥ (Gk P β ν a Ot Gker D x x').mulVec (fun i => (v i : ℂ)) =
      (fun i => (v i : ℂ)) ⬝ᵥ (Rk P β ν a Ot D x x').mulVec (fun i => (v i : ℂ)) := by
  have h1 : Gk P β ν a Ot Gker D x x' = Ck β ν a Ot Gker D x x' + Rk P β ν a Ot D x x' := rfl
  rw [h1, Matrix.add_mulVec, dotProduct_add]
  have h2 : (fun i => (v i : ℂ)) ⬝ᵥ (Ck β ν a Ot Gker D x x').mulVec (fun i => (v i : ℂ)) = 0 := by
    simp only [Ck]
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_eq_zero fun j hj => ?_
    have hj' := Finset.mem_Icc.1 hj
    rw [hψ j hj'.1 hj'.2, Matrix.smul_mulVec, dotProduct_smul, Matrix.dotProduct_mulVec, hG j x x']
    simp
  rw [h2, zero_add]

end Const

end Balaban.Observables
