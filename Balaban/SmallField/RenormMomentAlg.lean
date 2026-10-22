/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormMomentQuad
public import Balaban.Fluctuation.ExpansionQuad

/-!
# The second variation of `C₁` in terms of three pairings

On a whole-lattice level the second variation `secondVar` of `C₁` along a transverse
layer-constant direction `ψ'` (with first-order response `φ¹`, `H₀ φ¹ = w ψ'`, `w = a_n L^{-2n}`)
depends only on the pairings `vv = ⟨ψ', ψ'⟩`, `a₁ = ⟨ψ', φ¹⟩`, `c₁ = ⟨φ¹, φ¹⟩`:

`ξ₃ (w vv - w a₁ - ν c₁) + (1+ξ₃) ζ w (2 vv - 2 a₁ + c₁) + (1+ξ₃) ζ² w vv + ν ξ₂ c₁`
(`secondVar_inv`).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Flow Finset Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ} {n : ℕ}

/-- The weight `a_n L^{-2n}` of a whole-lattice level, as a complex number. -/
noncomputable def wLevel (L : ℕ) (a : ℕ → ℝ) (n : ℕ) : ℂ := ((a n / ((L : ℝ) ^ n) ^ 2 : ℝ) : ℂ)

/-- A field on the torus as a field on `Ω₁ × Fin N`. -/
def tildeV (G : GeneratingSet d L N₀ K ϱ) (v : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    G.Ω 1 × Fin N → ℂ := fun p => v p.1 p.2

/-- The block average as an operator on fields on `Ω₁ × Fin N`. -/
noncomputable def avgV (G : GeneratingSet d L N₀ K ϱ) (φ : G.Ω 1 × Fin N → ℂ) :
    G.Ω 1 × Fin N → ℂ := fun p => blockAvg G φ p.1 p.2

theorem blockPair_level (hG : IsLevel G n) (a : ℕ → ℝ) (A B : Torus d (N₀ * L ^ K) → Fin N → ℂ) :
    blockPair G a A B = wLevel L a n * pair G (tildeV G A) (tildeV G B) := by
  unfold blockPair pair tildeV wLevel
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [(hG x).2, Finset.mul_sum]

theorem blockVec_level (hG : IsLevel G n) (a : ℕ → ℝ) (φ : G.Ω 1 × Fin N → ℂ) :
    Background.blockVec G a φ = fun p => wLevel L a n * avgV G φ p := by
  funext p
  unfold Background.blockVec blockTerm avgV blockAvg wLevel svec
  rw [(hG p.1).2]

theorem massPair_zero (φ : G.Ω 1 × Fin N → ℂ) :
    massPair G (fun _ _ => 0) φ = pair G φ φ := by
  unfold massPair pair
  rw [Fintype.sum_prod_type]
  simp

theorem bondPair_level (hG : IsLevel G n) (Ψ : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (φ : G.Ω 1 × Fin N → ℂ) : bondPair G Ψ φ = pair G φ (lapVec G φ) := by
  classical
  have hmem : ∀ x : Torus d (N₀ * L ^ K), x ∈ G.Ω 1 := fun x => (hG x).1
  unfold bondPair
  simp only [barField_eq_svec hG, hmem, true_or, ↓reduceIte]
  rw [Finset.sum_comm]
  simp only [Finset.sum_comm (s := (Finset.univ : Finset (Fin d)))]
  unfold pair
  rw [Fintype.sum_prod_type_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := bond_sum_by_parts (fun y => svec G φ y i) (fun y => svec G φ y i)
  rw [h]
  have e1 : ∑ x : Torus d (N₀ * L ^ K), svec G φ x i * ∑ μ : Fin d,
      (2 * svec G φ x i - svec G φ (x + Pi.single μ 1) i - svec G φ (x - Pi.single μ 1) i) =
      ∑ x ∈ G.Ω 1, svec G φ x i * ∑ μ : Fin d,
      (2 * svec G φ x i - svec G φ (x + Pi.single μ 1) i - svec G φ (x - Pi.single μ 1) i) := by
    rw [hG.Ω_one]
  rw [e1, ← Finset.sum_coe_sort (G.Ω 1)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [svec_of_mem G φ x i]
  simp only [Background.lapVec, negLap, svec]
  rw [zeroExt_mem (G.Ω 1) (fun z => φ (z, i)) x]

theorem pair_avgV_eq (hG : IsLevel G n) (a : ℕ → ℝ) (g : Torus d (N₀ * L ^ K) → Fin N → ℂ)
    (hg : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, g y i = g x i)
    (u : G.Ω 1 × Fin N → ℂ) :
    wLevel L a n * pair G (tildeV G g) (avgV G u) = wLevel L a n * pair G (tildeV G g) u := by
  have h := sum_blockAvg (G := G) (a := a) (g := fun i x => g x i) hg u
  have hl : ∀ x : G.Ω 1, G.layerIndex (x : Torus d (N₀ * L ^ K)) = n := fun x => (hG x).2
  simp only [hl] at h
  unfold pair tildeV avgV wLevel
  rw [Fintype.sum_prod_type] at h ⊢
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, mul_assoc] at h ⊢
  exact h

theorem secondVar_inv (hG : IsLevel G n) (a : ℕ → ℝ) (ν ξ₂ ξ₃ ζ : ℝ)
    (ψ' : Torus d (N₀ * L ^ K) → Fin N → ℂ) (hψ' : IsLayerConstant G ψ')
    (φ1 : G.Ω 1 × Fin N → ℂ)
    (hH : ∀ p, lapVec G φ1 p + Background.blockVec G a φ1 p + (ν : ℂ) * φ1 p = qStar G a ψ' p) :
    secondVar G a ν ξ₂ ξ₃ ζ ψ' φ1 =
      (ξ₃ : ℂ) * (wLevel L a n * pair G (tildeV G ψ') (tildeV G ψ') -
          wLevel L a n * pair G (tildeV G ψ') φ1 - ν * pair G φ1 φ1) +
        (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * (wLevel L a n * (2 * pair G (tildeV G ψ') (tildeV G ψ') -
          2 * pair G (tildeV G ψ') φ1 + pair G φ1 φ1)) +
          (ζ : ℂ) ^ 2 * (wLevel L a n * pair G (tildeV G ψ') (tildeV G ψ'))) +
        ((ν * ξ₂ : ℝ) : ℂ) * pair G φ1 φ1 := by
  classical
  set w := wLevel L a n with hw
  set v := tildeV G ψ' with hv
  set P := avgV G φ1 with hP
  have hlc : ∀ i, ∀ x ∈ G.Ω 1, ∀ y ∈ G.blk (G.layerIndex x) x, ψ' y i = ψ' x i := by
    intro i x hx y hy
    obtain ⟨h1, h2, h3⟩ := G.layerIndex_spec hx
    exact congrFun (hψ' _ h1 h2 x h3 y hy) i
  have K1 := pair_avgV_eq hG a ψ' hlc φ1
  have K2 := pair_avgV_eq hG a (fun x i => blockAvg G φ1 x i)
    (fun i x hx y hy => blockAvg_blockConst φ1 i x hx y hy) φ1
  have hE : tildeV G (fun x i => blockAvg G φ1 x i) = P := by funext p; rfl
  rw [hE] at K2
  change w * pair G v P = w * pair G v φ1 at K1
  change w * pair G P P = w * pair G P φ1 at K2
  have hX : tildeV G (fun x i => ψ' x i - blockAvg G φ1 x i) = v - P := by
    funext p; rfl
  have hS : tildeV G (svec G φ1) = φ1 := by
    funext p; simp [tildeV, svec_of_mem]
  have hlap : pair G φ1 (lapVec G φ1) = w * pair G v φ1 - w * pair G P φ1 - ν * pair G φ1 φ1 := by
    have hpt : lapVec G φ1 = fun p => w * v p - w * P p - (ν : ℂ) * φ1 p := by
      funext p
      have h := hH p
      rw [blockVec_level hG] at h
      have hq : qStar G a ψ' p = w * v p := by
        simp only [qStar, hw, wLevel, hv, tildeV, (hG p.1).2]
      rw [hq] at h
      simp only [hP]
      linear_combination h
    rw [hpt]
    unfold pair
    have e1 : ∑ p, φ1 p * (w * v p) = w * ∑ p, v p * φ1 p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    have e2 : ∑ p, φ1 p * (w * P p) = w * ∑ p, P p * φ1 p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    have e3 : ∑ p, φ1 p * ((ν : ℂ) * φ1 p) = (ν : ℂ) * ∑ p, φ1 p * φ1 p := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ => by ring
    simp only [mul_sub, Finset.sum_sub_distrib, e1, e2, e3]
  have hvP : pair G P v = pair G v P := pair_comm _ _
  have hPP : pair G (v - P) (v - P) = pair G v v - 2 * pair G v P + pair G P P := by
    rw [pair_sub_right, pair_sub_left, pair_sub_left, hvP]; ring
  have hvX : pair G v (v - P) = pair G v v - pair G v P := pair_sub_right _ _ _
  unfold secondVar
  simp only [blockPair_level hG, bondPair_level hG, massPair_zero, hX, hE, hS]
  rw [hlap, hPP, hvX]
  linear_combination (-2 * (ξ₃ : ℂ) - 2 * (1 + (ξ₃ : ℂ)) * ζ) * K1 + (ξ₃ : ℂ) * K2

/-- The vector field `u ⊗ e_{i₁}` on the torus. -/
def dirVec (i₁ : Fin N) (u : Torus d (N₀ * L ^ K) → ℂ) : Torus d (N₀ * L ^ K) → Fin N → ℂ :=
  fun z i => if i = i₁ then u z else 0

theorem pair_delta (i₁ : Fin N) (f g : G.Ω 1 → ℂ) :
    pair G (fun p => if p.2 = i₁ then f p.1 else 0) (fun p => if p.2 = i₁ then g p.1 else 0) =
      ∑ x, f x * g x := by
  unfold pair
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single i₁]
  · simp
  · intro i _ hi; simp [hi]
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **The second variation of `C₁` in the direction `u ⊗ e_{i₁}`**, in terms of the Green matrix. -/
noncomputable def secondVarScalar (w : ℂ) (ν ξ₂ ξ₃ ζ : ℝ) (uu uGu GuGu : ℂ) : ℂ :=
  (ξ₃ : ℂ) * (w * uu - w * (w * uGu) - ν * (w ^ 2 * GuGu)) +
    (1 + (ξ₃ : ℂ)) * ((ζ : ℂ) * (w * (2 * uu - 2 * (w * uGu) + w ^ 2 * GuGu)) +
      (ζ : ℂ) ^ 2 * (w * uu)) + ((ν * ξ₂ : ℝ) : ℂ) * (w ^ 2 * GuGu)

theorem secondVar_scalar (hG : IsLevel G n) {a : ℕ → ℝ} {ν : ℝ}
    (hU : IsUnit (dirichletOperator G a ν (0 : G.Ω 1 → ℂ))) (ξ₂ ξ₃ ζ : ℝ) (i₁ : Fin N)
    (u : Torus d (N₀ * L ^ K) → ℂ) (hu : IsLayerConstant G (dirVec i₁ u)) :
    secondVar G a ν ξ₂ ξ₃ ζ (dirVec i₁ u)
        (liftOp N (greenD G a ν 0) *ᵥ qStar G a (dirVec i₁ u)) =
      secondVarScalar (wLevel L a n) ν ξ₂ ξ₃ ζ
        ((fun x : G.Ω 1 => u x) ⬝ᵥ (fun x : G.Ω 1 => u x))
        ((fun x : G.Ω 1 => u x) ⬝ᵥ (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x))
        ((greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) ⬝ᵥ (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x)) := by
  classical
  set φ1 := liftOp N (greenD G a ν 0) *ᵥ qStar G a (dirVec i₁ u) with hφ1
  have hH : ∀ p, lapVec G φ1 p + Background.blockVec G a φ1 p + (ν : ℂ) * φ1 p =
      qStar G a (dirVec i₁ u) p := by
    intro p
    have h1 : liftOp N (dirichletOperator G a ν 0) *ᵥ φ1 = qStar G a (dirVec i₁ u) :=
      liftOp_mulVec_inv hU _
    have := congrFun h1 p
    rw [H0_apply] at this
    exact this
  rw [secondVar_inv hG a ν ξ₂ ξ₃ ζ (dirVec i₁ u) hu φ1 hH]
  have hq : ∀ y : G.Ω 1, ∀ i, qStar G a (dirVec i₁ u) (y, i) =
      wLevel L a n * (if i = i₁ then u y else 0) := by
    intro y i
    simp only [qStar, dirVec, wLevel, (hG y).2]
  have hφ : ∀ x : G.Ω 1, ∀ i, φ1 (x, i) =
      if i = i₁ then wLevel L a n * (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) x else 0 := by
    intro x i
    rw [hφ1, liftOp_mulVec_apply]
    simp only [hq]
    by_cases hi : i = i₁
    · simp only [hi, ↓reduceIte, Matrix.mulVec, dotProduct, Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => by ring
    · simp [hi]
  have e1 : tildeV G (dirVec i₁ u) = fun p => if p.2 = i₁ then u p.1 else 0 := by
    funext p; rfl
  have e2 : φ1 = fun p => if p.2 = i₁ then wLevel L a n * (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) p.1
      else 0 := by
    funext p; exact hφ p.1 p.2
  rw [e1]
  rw [e2]
  have hp1 := pair_delta (G := G) i₁ (fun x => u x) (fun x => u x)
  have hp2 := pair_delta (G := G) i₁ (fun x => u x)
    (fun x => wLevel L a n * (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) x)
  have hp3 := pair_delta (G := G) i₁ (fun x => wLevel L a n * (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) x)
    (fun x => wLevel L a n * (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) x)
  rw [hp1, hp2, hp3]
  unfold secondVarScalar
  have h1 : ∀ (f g : G.Ω 1 → ℂ), ∑ x, f x * (wLevel L a n * g x) = wLevel L a n * ∑ x, f x * g x := by
    intro f g; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  have h2 : ∀ (g : G.Ω 1 → ℂ), ∑ x, wLevel L a n * g x * (wLevel L a n * g x) =
      wLevel L a n ^ 2 * ∑ x, g x * g x := by
    intro g; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x _ => by ring
  beta_reduce
  rw [h1 (fun x => u x) (fun x => (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) x),
    h2 (fun x => (greenD G a ν 0 *ᵥ fun x : G.Ω 1 => u x) x)]
  simp only [dotProduct]

end Balaban.Fluctuation
