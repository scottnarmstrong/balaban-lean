/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Equivariance

/-!
# Invariance of the data domains under real orthogonal rotations (BACKGROUND.md §1.3)

For a real matrix `Q` with `Qᵀ Q = 1` and `cmat Q` its complexification, the rotation
`D ↦ D.rot (cmat Q)` of the data preserves the real and complex data domains
(`inDomainR_rot_iff`, `inDomainC_rot_iff`, `inUnionDomainR_rot_iff`, `inUnionDomainC_rot_iff`):
the conditions (R1)-(R4), (C1)-(C3) involve only Euclidean norms, scalar products and bilinear
forms of the data.  Also the norm identities used by the consumers (`rn_rot`, `vn_rot`,
`vn_sub_rot`, `bilin_vec`, `rot_lap`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

theorem dot_rot_real {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u w : Fin N → ℝ) :
    (Q *ᵥ u) ⬝ᵥ (Q *ᵥ w) = u ⬝ᵥ w := by
  rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose, Matrix.vecMul_vecMul, hQ,
    Matrix.vecMul_one]

theorem rn_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (v : Fin N → ℝ) :
    rn (Q *ᵥ v) = rn v := by
  have := dot_rot_real hQ v v
  simp only [rn]
  congr 1
  simpa [dotProduct, sq] using this

theorem isRealOrth_ofReal {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) :
    IsRealOrth (Q.map (Complex.ofReal : ℝ → ℂ)) := by
  refine ⟨?_, fun i j => by simp⟩
  have e := (Complex.ofRealHom.mapMatrix (m := Fin N)).map_mul Qᵀ Q
  rw [hQ, map_one] at e
  rw [← Matrix.transpose_map]
  exact e.symm

theorem vn_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (v : Fin N → ℂ) :
    vn (R *ᵥ v) = vn v := by
  have := normSq_rot hR v
  simp only [vn, EuclideanSpace.norm_eq]
  congr 1

theorem sum_mul_rot_real {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u w : Fin N → ℝ) :
    ∑ i, (Q *ᵥ u) i * (Q *ᵥ w) i = ∑ i, u i * w i := dot_rot_real hQ u w

theorem sum_sq_rot_real {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u : Fin N → ℝ) :
    ∑ i, (Q *ᵥ u) i ^ 2 = ∑ i, u i ^ 2 := by
  simpa only [dotProduct, sq] using dot_rot_real hQ u u

theorem rn_sub_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (u w : Fin N → ℝ) :
    rn (fun i => (Q *ᵥ u) i - (Q *ᵥ w) i) = rn (fun i => u i - w i) := by
  have : (fun i => (Q *ᵥ u) i - (Q *ᵥ w) i) = Q *ᵥ (fun i => u i - w i) := by
    show _ = Q *ᵥ (u - w)
    rw [Matrix.mulVec_sub]; rfl
  rw [this, rn_rot hQ]

section Domain

variable {G : GeneratingSet d L N₀ k ϱ}

theorem inPsiTilde_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν δ : ℝ}
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ} (H : InPsiTilde G ν δ Ψ h) :
    InPsiTilde G ν δ (fun x => Q *ᵥ Ψ x) (Q *ᵥ h) where
  layerConst := fun n h1 h2 x hx x' hx' => by
    simp only; rw [H.layerConst n h1 h2 x hx x' hx']
  r1 := fun x x' hxx' => by rw [rn_sub_rot hQ]; exact H.r1 x x' hxx'
  r2 := fun x hx => by rw [sum_sq_rot_real hQ]; exact H.r2 x hx
  r3 := fun x hx => by
    rw [sum_mul_rot_real hQ, rn_rot hQ]; exact H.r3 x hx
  r4 := by rw [sum_sq_rot_real hQ]; exact H.r4

/-- The complexification of a real matrix. -/
abbrev cmat (Q : Matrix (Fin N) (Fin N) ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  Q.map (Complex.ofReal : ℝ → ℂ)

theorem cmat_mulVec (Q : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ) (i : Fin N) :
    (((Q *ᵥ v) i : ℝ) : ℂ) = (cmat Q *ᵥ fun j => (v j : ℂ)) i := by
  simp [cmat, Matrix.mulVec, dotProduct]

theorem bilin_vec {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (u w : Fin N → ℂ) :
    ∑ i, (R *ᵥ u) i * (R *ᵥ w) i = ∑ i, u i * w i := by
  simpa [rotFld, Matrix.mulVec, dotProduct] using
    rotFld_bilin (ι := Unit) hR (fun p => u p.2) (fun p => w p.2) ()

theorem inPsiTildeC_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν δ ε : ℝ}
    {Ψ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h : Fin N → ℝ}
    {Ψ' h' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (H : InPsiTildeC G ν δ ε Ψ h Ψ' h') :
    InPsiTildeC G ν δ ε (fun x => Q *ᵥ Ψ x) (Q *ᵥ h) (fun x => cmat Q *ᵥ Ψ' x)
      (fun x => cmat Q *ᵥ h' x) := by
  have hR := isRealOrth_ofReal hQ
  refine
    { inPsiTilde_rot hQ H.toInPsiTilde with
      eps_pos := H.eps_pos
      layerConst' := fun n h1 h2 x hx x' hx' => by
        simp only; rw [H.layerConst' n h1 h2 x hx x' hx']
      hLayerConst' := fun n h1 h2 x hx x' hx' => by
        simp only; rw [H.hLayerConst' n h1 h2 x hx x' hx']
      c1 := fun x x' hxx' => by rw [← Matrix.mulVec_sub, vn_rot hR]; exact H.c1 x x' hxx'
      c2a := fun x hx => by rw [vn_rot hR]; exact H.c2a x hx
      c2b := fun x hx => ?_
      c3a := fun x hx => by rw [vn_rot hR]; exact H.c3a x hx
      c3b := fun x hx => ?_ }
  · have e : ∀ i, ((Q *ᵥ Ψ x) i : ℂ) + (cmat Q *ᵥ Ψ' x) i =
        (cmat Q *ᵥ fun j => (Ψ x j : ℂ) + Ψ' x j) i := fun i => by
      have e3 : (fun j => (Ψ x j : ℂ) + Ψ' x j) = (fun j => (Ψ x j : ℂ)) + Ψ' x := rfl
      rw [cmat_mulVec, e3, Matrix.mulVec_add]; rfl
    have e2 : ∀ i, ((Q *ᵥ Ψ x) i : ℂ) = (cmat Q *ᵥ fun j => (Ψ x j : ℂ)) i := cmat_mulVec Q _
    simp only [e]
    simp only [e2]
    rw [bilin_vec hR.1, bilin_vec hR.1]
    exact H.c2b x hx
  · have e : ∀ i, (((Q *ᵥ Ψ x) i / rn (Q *ᵥ Ψ x) : ℝ) : ℂ) =
        (cmat Q *ᵥ fun j => ((Ψ x j / rn (Ψ x) : ℝ) : ℂ)) i := fun i => by
      rw [rn_rot hQ]
      push_cast
      simp [cmat, Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc]
    simp only [e]
    rw [bilin_vec hR.1]
    exact H.c3b x hx

theorem inDomainR_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν δ : ℝ}
    {D : BgData G N} (H : InDomainR G ν δ D) : InDomainR G ν δ (D.rot (cmat Q)) := by
  obtain ⟨Ψ, h, H, hΨ, hh⟩ := H
  refine ⟨fun x => Q *ᵥ Ψ x, Q *ᵥ h, inPsiTilde_rot hQ H, fun x hx i => ?_, fun x hx i => ?_⟩
  · have : D.Ψ x = fun j => (Ψ x j : ℂ) := funext (hΨ x hx)
    show (cmat Q *ᵥ D.Ψ x) i = _
    rw [this, cmat_mulVec]
  · have : D.h x = fun j => (h j : ℂ) := funext (hh x hx)
    show (cmat Q *ᵥ D.h x) i = _
    rw [this, cmat_mulVec]

theorem inDomainC_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν δ ε : ℝ}
    {D : BgData G N} (H : InDomainC G ν δ ε D) : InDomainC G ν δ ε (D.rot (cmat Q)) := by
  obtain ⟨Ψ, h, Ψ', h', H, hΨ, hh⟩ := H
  refine ⟨fun x => Q *ᵥ Ψ x, Q *ᵥ h, fun x => cmat Q *ᵥ Ψ' x, fun x => cmat Q *ᵥ h' x,
    inPsiTildeC_rot hQ H, fun x hx i => ?_, fun x hx i => ?_⟩
  · have : D.Ψ x = (fun j => (Ψ x j : ℂ)) + Ψ' x := funext fun j => hΨ x hx j
    show (cmat Q *ᵥ D.Ψ x) i = _
    rw [this, Matrix.mulVec_add, cmat_mulVec]; rfl
  · have : D.h x = (fun j => (h j : ℂ)) + h' x := funext fun j => hh x hx j
    show (cmat Q *ᵥ D.h x) i = _
    rw [this, Matrix.mulVec_add, cmat_mulVec]; rfl

theorem inUnionDomainR_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {c₁ ν : ℝ}
    {D : BgData G N} (H : InUnionDomainR G c₁ ν D) : InUnionDomainR G c₁ ν (D.rot (cmat Q)) := by
  obtain ⟨δ, h0, h1, H⟩ := H
  exact ⟨δ, h0, h1, inDomainR_rot hQ H⟩

theorem inUnionDomainC_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {c₀ c₁ ν : ℝ}
    {D : BgData G N} (H : InUnionDomainC G c₀ c₁ ν D) :
    InUnionDomainC G c₀ c₁ ν (D.rot (cmat Q)) := by
  obtain ⟨δ, ε, h0, h1, h2, h3, h4, H⟩ := H
  exact ⟨δ, ε, h0, h1, h2, h3, h4, inDomainC_rot hQ H⟩

theorem vn_sub_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : IsRealOrth R) (u w : Fin N → ℂ) :
    vn (fun i => (R *ᵥ u) i - (R *ᵥ w) i) = vn (fun i => u i - w i) := by
  rw [← vn_rot hR (fun i => u i - w i)]
  congr 1
  funext i
  simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]

theorem rot_lap (R : Matrix (Fin N) (Fin N) ℂ) (m : ℕ) (a b : Fin m → Fin N → ℂ)
    (c : Fin N → ℂ) :
    (fun i => ∑ μ, ((R *ᵥ a μ) i + (R *ᵥ b μ) i - 2 * (R *ᵥ c) i)) =
      R *ᵥ fun i => ∑ μ, (a μ i + b μ i - 2 * c i) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_add, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [Finset.sum_comm (f := fun j μ => R i j * a μ j), Finset.sum_comm (f := fun j μ => R i j * b μ j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring


theorem sub_rot_apply (R : Matrix (Fin N) (Fin N) ℂ) (u w : Fin N → ℂ) (i : Fin N) :
    (R *ᵥ u) i - (R *ᵥ w) i = (R *ᵥ fun j => u j - w j) i := by
  simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]

theorem cmat_transpose (Q : Matrix (Fin N) (Fin N) ℝ) : cmat Qᵀ = (cmat Q)ᵀ :=
  Matrix.transpose_map

theorem orth_transpose_real {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) :
    Qᵀᵀ * Qᵀ = 1 := by
  rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.1 hQ

theorem rot_rot_cmat {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) (D : BgData G N) :
    (D.rot (cmat Q)).rot (cmat Qᵀ) = D := by
  rw [cmat_transpose]
  exact BgData.rot_transpose_rot (isRealOrth_ofReal hQ).1 D

theorem inDomainR_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν δ : ℝ}
    {D : BgData G N} : InDomainR G ν δ (D.rot (cmat Q)) ↔ InDomainR G ν δ D := by
  refine ⟨fun H => ?_, inDomainR_rot hQ⟩
  have := inDomainR_rot (orth_transpose_real hQ) H
  rwa [rot_rot_cmat hQ] at this

theorem inDomainC_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν δ ε : ℝ}
    {D : BgData G N} : InDomainC G ν δ ε (D.rot (cmat Q)) ↔ InDomainC G ν δ ε D := by
  refine ⟨fun H => ?_, inDomainC_rot hQ⟩
  have := inDomainC_rot (orth_transpose_real hQ) H
  rwa [rot_rot_cmat hQ] at this

theorem inUnionDomainR_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {c₁ ν : ℝ}
    {D : BgData G N} : InUnionDomainR G c₁ ν (D.rot (cmat Q)) ↔ InUnionDomainR G c₁ ν D := by
  refine ⟨fun H => ?_, inUnionDomainR_rot hQ⟩
  have := inUnionDomainR_rot (orth_transpose_real hQ) H
  rwa [rot_rot_cmat hQ] at this

theorem inUnionDomainC_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {c₀ c₁ ν : ℝ}
    {D : BgData G N} :
    InUnionDomainC G c₀ c₁ ν (D.rot (cmat Q)) ↔ InUnionDomainC G c₀ c₁ ν D := by
  refine ⟨fun H => ?_, inUnionDomainC_rot hQ⟩
  have := inUnionDomainC_rot (orth_transpose_real hQ) H
  rwa [rot_rot_cmat hQ] at this

end Domain
end Balaban.Background
