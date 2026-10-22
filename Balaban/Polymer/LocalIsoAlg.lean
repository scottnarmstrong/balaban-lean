/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.ContractionCore
public import Balaban.Background.Contraction
import Mathlib.Tactic.Linarith

/-!
# The maps of the background contraction under a bijection of the sites

For two generating sets `G`, `H` (of any two tori) and a bijection `e : Ω₁(G) ≃ Ω₁(H)`, the maps
of the contraction of Proposition 5.1 (`Nmap`, `dphi`, the commutator `K`, the remainders `R`, the
defect `g`, the source `F_s - δα φ₀`, the bounds `|·|₂`) are natural: at corresponding matrices
(`M' (e x) (e y) = M x y`), corresponding scalar fields (`u' (e x) = u x`), vector fields
(`v' (e x, i) = v (x, i)`) and fields of the torus (`φ' (e x) = φ x` on `Ω₁`), their values
correspond.  This is the algebraic layer of the exact two-torus transport of local generating sets
(`OmegaIso`): written once, for any bijection.

* `mulVec_corr`, `liftOp_mulVec_corr`, `commK_mulVec_corr`, `Rsc_corr`, `Rvec_corr`;
* `gdef_corr`, `Fsrc_corr`, `dphi_corr`, `Nmap_corr`;
* `small_corr_iff`, `srcBound_corr_iff` (with the correspondence of the spacings).
-/

@[expose] public section

noncomputable section

open scoped Classical

namespace Balaban.Polymer.LocalIso

open Balaban Balaban.Multiscale Balaban.Background Matrix

variable {d L N₀ N₀' k N : ℕ} [NeZero N₀] [NeZero N₀'] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {H : GeneratingSet d L N₀' k ϱ'} (e : G.Ω 1 ≃ H.Ω 1)

/-- The entries of a reindexed matrix. -/
theorem entry_of_submatrix {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (h : M.submatrix e.symm e.symm = M') (x y : G.Ω 1) : M' (e x) (e y) = M x y := by
  rw [← h]; simp

/-- The product of corresponding matrix and vector. -/
theorem mulVec_corr {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (hM : ∀ x y, M' (e x) (e y) = M x y) {u : G.Ω 1 → ℂ} {u' : H.Ω 1 → ℂ}
    (hu : ∀ x, u' (e x) = u x) (x : G.Ω 1) : (M' *ᵥ u') (e x) = (M *ᵥ u) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun y _ => by rw [hM, hu]

/-- The lift to vector fields of corresponding matrices. -/
theorem liftOp_mulVec_corr {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (hM : ∀ x y, M' (e x) (e y) = M x y) {v : G.Ω 1 × Fin N → ℂ} {v' : H.Ω 1 × Fin N → ℂ}
    (hv : ∀ x i, v' (e x, i) = v (x, i)) (x : G.Ω 1) (i : Fin N) :
    (liftOp N M' *ᵥ v') (e x, i) = (liftOp N M *ᵥ v) (x, i) := by
  rw [liftOp_mulVec, liftOp_mulVec]
  exact mulVec_corr e hM (fun y => hv y i) x

/-- The commutator `K(φ₀) s` of corresponding matrices, fields and vector fields. -/
theorem commK_mulVec_corr {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (hM : ∀ x y, M' (e x) (e y) = M x y) {φ : G.Ω 1 → Fin N → ℂ} {φ' : H.Ω 1 → Fin N → ℂ}
    (hφ : ∀ x, φ' (e x) = φ x) {v : G.Ω 1 × Fin N → ℂ} {v' : H.Ω 1 × Fin N → ℂ}
    (hv : ∀ x i, v' (e x, i) = v (x, i)) (x : G.Ω 1) :
    (commK M' φ' *ᵥ v') (e x) = (commK M φ *ᵥ v) x := by
  rw [commK_mulVec, commK_mulVec, ← e.sum_comp]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by rw [hM, hφ, hφ, hv]

/-- The scalar remainder `R(u, w)`. -/
theorem Rsc_corr {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (hM : ∀ x y, M' (e x) (e y) = M x y) {u w : G.Ω 1 → ℂ} {u' w' : H.Ω 1 → ℂ}
    (hu : ∀ x, u' (e x) = u x) (hw : ∀ x, w' (e x) = w x) (x : G.Ω 1) :
    Rsc M' u' w' (e x) = Rsc M u w x := by
  unfold Rsc
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [mulVec_corr e hM (u := u * w) (fun y => by simp [hu, hw]) x, mulVec_corr e hM hw x,
    mulVec_corr e hM hu x, hu, hw]

/-- The vector remainder `R(v, w)`. -/
theorem Rvec_corr {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (hM : ∀ x y, M' (e x) (e y) = M x y) {v w : G.Ω 1 × Fin N → ℂ}
    {v' w' : H.Ω 1 × Fin N → ℂ} (hv : ∀ x i, v' (e x, i) = v (x, i))
    (hw : ∀ x i, w' (e x, i) = w (x, i)) (x : G.Ω 1) :
    Rvec M' v' w' (e x) = Rvec M v w x := by
  unfold Rvec
  exact Finset.sum_congr rfl fun i _ =>
    Rsc_corr e hM (u := comp G v i) (w := comp G w i) (fun y => hv y i) (fun y => hw y i) x

/-- The defect `φ₀ · φ₀ - 1` of corresponding fields. -/
theorem gdef_corr {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ₀' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ₀' (e x) = φ₀ x) (x : G.Ω 1) :
    gdef H φ₀' (e x) = gdef G φ₀ x := by
  unfold gdef; rw [hφ]

/-- The source `F_s - δα φ₀`. -/
theorem Fsrc_corr {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φ₀' : Torus d (N₀' * L ^ k) → Fin N → ℂ} (hφ : ∀ x : G.Ω 1, φ₀' (e x) = φ₀ x)
    {Fs : G.Ω 1 × Fin N → ℂ} {Fs' : H.Ω 1 × Fin N → ℂ} (hF : ∀ x i, Fs' (e x, i) = Fs (x, i))
    {δα : G.Ω 1 → ℂ} {δα' : H.Ω 1 → ℂ} (hδ : ∀ x, δα' (e x) = δα x) (x : G.Ω 1) (i : Fin N) :
    Fsrc φ₀' Fs' δα' (e x, i) = Fsrc φ₀ Fs δα (x, i) := by
  unfold Fsrc; rw [hF, hδ, hφ]

/-- **`δφ(δα) = 𝒢(α₀ + δα)(F_s - δα φ₀)`** at corresponding Green families and data. -/
theorem dphi_corr {𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ}
    {𝒢' : (H.Ω 1 → ℂ) → Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (h𝒢 : ∀ (α : G.Ω 1 → ℂ) (α' : H.Ω 1 → ℂ), (∀ x, α' (e x) = α x) →
      ∀ x y, 𝒢' α' (e x) (e y) = 𝒢 α x y)
    {α₀ : G.Ω 1 → ℂ} {α₀' : H.Ω 1 → ℂ} (hα₀ : ∀ x, α₀' (e x) = α₀ x)
    {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ₀' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ₀' (e x) = φ₀ x)
    {Fs : G.Ω 1 × Fin N → ℂ} {Fs' : H.Ω 1 × Fin N → ℂ} (hF : ∀ x i, Fs' (e x, i) = Fs (x, i))
    {δα : G.Ω 1 → ℂ} {δα' : H.Ω 1 → ℂ} (hδ : ∀ x, δα' (e x) = δα x) (x : G.Ω 1) (i : Fin N) :
    dphi H 𝒢' α₀' φ₀' Fs' δα' (e x, i) = dphi G 𝒢 α₀ φ₀ Fs δα (x, i) := by
  unfold dphi
  exact liftOp_mulVec_corr e (h𝒢 _ _ fun y => by simp [hα₀, hδ])
    (fun y j => Fsrc_corr e hφ hF hδ y j) x i

/-- **The map `𝒩` of (5.2)** at corresponding data. -/
theorem Nmap_corr {M : Matrix (G.Ω 1) (G.Ω 1) ℂ} {M' : Matrix (H.Ω 1) (H.Ω 1) ℂ}
    (hM : ∀ x y, M' (e x) (e y) = M x y) (ιU : Bool)
    {φ₀ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {φ₀' : Torus d (N₀' * L ^ k) → Fin N → ℂ}
    (hφ : ∀ x : G.Ω 1, φ₀' (e x) = φ₀ x)
    {Fs : G.Ω 1 × Fin N → ℂ} {Fs' : H.Ω 1 × Fin N → ℂ} (hF : ∀ x i, Fs' (e x, i) = Fs (x, i))
    {δφ : G.Ω 1 × Fin N → ℂ} {δφ' : H.Ω 1 × Fin N → ℂ} (hδ : ∀ x i, δφ' (e x, i) = δφ (x, i))
    (x : G.Ω 1) :
    Nmap H M' ιU φ₀' Fs' δφ' (e x) = Nmap G M ιU φ₀ Fs δφ x := by
  unfold Nmap
  rw [commK_mulVec_corr e hM (φ := restrictField G φ₀) (φ' := restrictField H φ₀')
    (fun y => hφ y) hδ x, Rvec_corr e hM hδ hδ x,
    mulVec_corr e hM (u := gdef G φ₀) (u' := gdef H φ₀') (gdef_corr e hφ) x]
  simp only [hφ, hδ, hF]

/-- `|δα|₂ ≤ r` at corresponding scalar fields, for corresponding spacings. -/
theorem small_corr_iff (hsp : ∀ x : G.Ω 1,
      H.spacing ((e x : H.Ω 1) : Torus d (N₀' * L ^ k)) = G.spacing (x : Torus d (N₀ * L ^ k)))
    {δα : G.Ω 1 → ℂ} {δα' : H.Ω 1 → ℂ} (hδ : ∀ x, δα' (e x) = δα x) (r : ℝ) :
    Small H δα' r ↔ Small G δα r := by
  constructor
  · intro h x
    have := h (e x)
    rwa [hsp, hδ] at this
  · intro h x'
    obtain ⟨x, rfl⟩ := e.surjective x'
    rw [hsp, hδ]
    exact h x

/-- `|g|₂ ≤ C` at corresponding vector fields, for corresponding spacings. -/
theorem srcBound_corr_iff (hsp : ∀ x : G.Ω 1,
      H.spacing ((e x : H.Ω 1) : Torus d (N₀' * L ^ k)) = G.spacing (x : Torus d (N₀ * L ^ k)))
    {g : G.Ω 1 × Fin N → ℂ} {g' : H.Ω 1 × Fin N → ℂ} (hg : ∀ x i, g' (e x, i) = g (x, i))
    (C : ℝ) : SrcBound H g' C ↔ SrcBound G g C := by
  constructor
  · intro h x i
    have := h (e x) i
    rwa [hsp, hg] at this
  · intro h x' i
    obtain ⟨x, rfl⟩ := e.surjective x'
    rw [hsp, hg]
    exact h x i

end Balaban.Polymer.LocalIso
