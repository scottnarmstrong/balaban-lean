/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.Denominator
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Tactic.Linarith

/-!
# `O(N)`-invariance of the reference density and of `Ẽ₀` (Lemma III.8.2)

The blockwise rotation `rotSupp` of the perturbation space is a linear isometry, so it preserves Lebesgue measure;
`rhoZero_rot` (`ρ_{k,0}(Z)(Qψ_k)(Qu) = ρ_{k,0}(Z)(ψ_k)(u)`, from `effAction_rot`, `psiZero_equivariant` and the
invariance of `rn`) gives `integral_rhoZero_rot` and `tildeE0_rot`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField
open Balaban Balaban.Multiscale Balaban.Background MeasureTheory Matrix

section Rot

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {Zf : Finset (Torus d (N₀ * L ^ (k - k)))}

/-- Blockwise rotation of the perturbation space. -/
noncomputable def rotSuppFun (Q : Matrix (Fin N) (Fin N) ℝ) (u : SuppSpace Zf N) : SuppSpace Zf N :=
  WithLp.toLp 2 fun p => (Q *ᵥ fun j => u (p.1, j)) p.2

theorem rotSuppFun_add (Q : Matrix (Fin N) (Fin N) ℝ) (u v : SuppSpace Zf N) :
    rotSuppFun Q (u + v) = rotSuppFun Q u + rotSuppFun Q v := by
  ext p; simp [rotSuppFun, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]

theorem rotSuppFun_smul (Q : Matrix (Fin N) (Fin N) ℝ) (c : ℝ) (u : SuppSpace Zf N) :
    rotSuppFun Q (c • u) = c • rotSuppFun Q u := by
  ext p; simp [rotSuppFun, Matrix.mulVec, dotProduct, Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => by ring

theorem norm_rotSuppFun {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u : SuppSpace Zf N) :
    ‖rotSuppFun Q u‖ = ‖u‖ := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), sq_norm_supp, sq_norm_supp]
  refine Finset.sum_congr rfl fun z _ => ?_
  have := rn_mulVec hQ (fun j => u (z, j))
  unfold rn at this
  have h0 : 0 ≤ ∑ i, (Q *ᵥ fun j => u (z, j)) i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h1 : 0 ≤ ∑ i, u (z, i) ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h2 := congrArg (· ^ 2) this
  simpa [Real.sq_sqrt h0, Real.sq_sqrt h1, rotSuppFun] using h2


theorem rotSuppFun_rotSuppFun {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u : SuppSpace Zf N) :
    rotSuppFun Qᵀ (rotSuppFun Q u) = u := by
  ext p
  simp only [rotSuppFun]
  simp only [mulVec_mulVec, hQ, one_mulVec]

/-- The blockwise rotation as a linear isometry equivalence. -/
noncomputable def rotSupp {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) : SuppSpace Zf N ≃ₗᵢ[ℝ] SuppSpace Zf N :=
  have hQ' : Q * Qᵀ = 1 := mul_eq_one_comm.1 hQ
  have hQt : (Qᵀ)ᵀ * Qᵀ = 1 := by simpa using hQ'
  { toFun := rotSuppFun Q
    map_add' := rotSuppFun_add Q
    map_smul' := fun c u => by simpa using rotSuppFun_smul Q c u
    invFun := rotSuppFun Qᵀ
    left_inv := rotSuppFun_rotSuppFun hQ
    right_inv := fun u => by simpa using rotSuppFun_rotSuppFun hQt u
    norm_map' := norm_rotSuppFun hQ }

theorem rotSupp_apply {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u : SuppSpace Zf N) :
    rotSupp hQ u = rotSuppFun Q u := rfl

theorem merge_rot (Q : Matrix (Fin N) (Fin N) ℝ) (ψk : BlockField d L N₀ k N) (u : SuppSpace Zf N) :
    mergeField Zf (rotBlock Q ψk) (rotSuppFun Q u) = rotBlock Q (mergeField Zf ψk u) := by
  funext z
  by_cases hz : z ∈ Zf
  · funext i
    rw [mergeField_of_mem hz i]
    simp [rotSuppFun, rotBlock]
    have : (fun j => u.ofLp (⟨z, hz⟩, j)) = mergeField Zf ψk u z :=
      funext fun j => (mergeField_of_mem hz j).symm
    rw [this]
  · rw [mergeField_of_not_mem hz]
    simp [rotBlock, mergeField_of_not_mem hz]

end Rot

section Inv

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ)
  [NeZero N]

variable {D : ℕ} (hd : 2 ≤ d) (hk : 1 ≤ k) (b0 : Torus d (N₀ * L ^ (k - k))) (w : Fin d → ℕ)
  (hw1 : ∀ i, 1 ≤ w i) (hwD : ∀ i, w i ≤ D) (hm : D + 2 ≤ N₀ * L ^ (k - k))
  {X : Set (Torus d (N₀ * L ^ (k - k)))} (hXreg : box b0 w ∪ shellOut (box b0 w) ⊆ X)
  (hΩ : OverTop G (box b0 w ∪ shellOut (box b0 w)))
  (hdata : ∀ x ∈ dataSites G, jBlock d L N₀ k k x ∈ X) (H : BgHyp d L k ϱ a 0)

theorem effActionNorm_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (ψ : BlockField d L N₀ k N) :
    effActionNorm G a (rotBlock Q ψ) = effActionNorm G a ψ := by
  unfold effActionNorm; rw [effAction_rot G hQ]

theorem zeroCutoff_rot {Zf : Finset (Torus d (N₀ * L ^ (k - k)))} {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (ψ0 : BlockField d L N₀ k N) (r : ℝ)
    (u : SuppSpace Zf N) : ZeroCutoff (rotBlock Q ψ0) r (rotSuppFun Q u) ↔ ZeroCutoff ψ0 r u := by
  unfold ZeroCutoff
  refine forall_congr' fun z => ?_
  have : (fun i => rotSuppFun Q u (z, i) - rotBlock Q ψ0 (z : Torus d (N₀ * L ^ (k - k))) i) =
      Q *ᵥ (fun i => u (z, i) - ψ0 z i) := by
    funext i; simp [rotSuppFun, rotBlock]
    rw [← Pi.sub_apply, ← mulVec_sub]; rfl
  rw [this, rn_mulVec hQ]

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **`O(N)`-invariance of the reference density**: `ρ_{k,0}(Z)(Qψ_k)(Q u) = ρ_{k,0}(Z)(ψ_k)(u)`. -/
theorem rhoZero_rot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hψk' : TubeOn G (X \ box b0 w) δ (rotBlock Q ψk)) (β p0 : ℝ)
    (u : SuppSpace (boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) N) :
    rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' β p0 (rotSuppFun Q u) =
      rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u := by
  have hψ0 := psiZero_equivariant N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk'
  unfold rhoZero rhoZeroWith chiZeroCut
  rw [hψ0, merge_rot, effActionNorm_rot G a hQ]
  by_cases h : ZeroCutoff (psiZero N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk)
      (zeroRadius (cSix d D (psiZeroK N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H)) β p0) u
  · simp [(zeroCutoff_rot hQ _ _ u).2 h, h]
  · simp [h, mt (zeroCutoff_rot hQ _ _ u).1 h]

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- The integral of the reference density is `O(N)`-invariant. -/
theorem integral_rhoZero_rot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hψk' : TubeOn G (X \ box b0 w) δ (rotBlock Q ψk)) (β p0 : ℝ) :
    ∫ v, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' β p0 v =
      ∫ u, rhoZero G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 u := by
  have hmp := (rotSupp (Zf := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) hQ).measurePreserving
  rw [← hmp.integral_comp (rotSupp (Zf := boxFinset (L := L) (N₀ := N₀) (k := k) b0 w) hQ).toHomeomorph.measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  exact rhoZero_rot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk' β p0 u

include hd hk hw1 hwD hm hXreg hΩ hdata H in
/-- **`O(N)`-invariance of `Ẽ₀`** (Lemma III.8.2): `Ẽ₀(Qψ_k) = Ẽ₀(ψ_k)`. -/
theorem tildeE0_rot {δ : ℝ} (hδ : 0 < δ)
    (hδc : δ ≤ psiZeroC11 N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H) {ψk : BlockField d L N₀ k N}
    (hψk : TubeOn G (X \ box b0 w) δ ψk) {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1)
    (hψk' : TubeOn G (X \ box b0 w) δ (rotBlock Q ψk)) (β p0 : ℝ) :
    tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk' β p0 =
      tildeE0 G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk β p0 := by
  unfold tildeE0
  rw [integral_rhoZero_rot G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk' β p0,
    psiZero_equivariant N G a hd hk b0 w hw1 hwD hm hXreg hΩ hdata H hδ hδc hψk hQ hψk',
    effActionNorm_rot G a hQ]

end Inv
end Balaban.LargeField
