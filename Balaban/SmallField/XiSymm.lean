/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.EquivarianceDomain
public import Balaban.SmallField.Xi

/-!
# O(N)-covariance of the analyticity spaces `Ξ`, `Ξ^c` (SMALLFIELD.md §1.7)

For a real orthogonal `Q` (`Qᵀ Q = 1`) acting on the real raw data by `Ψ₀ ↦ Q Ψ₀`, `h₀ ↦ Q h₀` and
on the complex displacements by the complexification `cmat Q`:

* `xi_rot_iff`: `(Q Ψ₀, Q h₀) ∈ Ξ_n(𝔹; σ, ε)` iff `(Ψ₀, h₀) ∈ Ξ_n(𝔹; σ, ε)`;
* `xiC_rot_iff`: the same for `Ξ^c_n`.

The ingredients are the invariance of the data domains (`inUnionDomainR_rot`,
`inUnionDomainC_rot`), of `XiBounds`, `XiCBounds`, and the covariance of the background fields
(`Balaban/Background/Equivariance.lean`).  For a complex orthogonal `R` that is not real, the base
point `(Ψ₀, h₀)` would stop being real, so `Ξ^c` is not defined at the rotated datum; the complex
covariance of `bgFieldC` itself (`bgFieldC_rot`) holds for every complex orthogonal `R`.
-/

@[expose] public section

namespace Balaban.SmallField
open Balaban.Background Balaban.Multiscale Matrix Finset
variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Domain

variable {G : GeneratingSet d L N₀ k ϱ}

theorem realizes_rot {Q : Matrix (Fin N) (Fin N) ℝ} {D : BgData G N}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} (H : Realizes D Ψ₀ h₀) :
    Realizes (D.rot (cmat Q)) (fun x => Q *ᵥ Ψ₀ x) (Q *ᵥ h₀) := by
  refine ⟨fun x hx i => ?_, fun x hx i => ?_⟩
  · have : D.Ψ x = fun j => (Ψ₀ x j : ℂ) := funext (H.1 x hx)
    show (cmat Q *ᵥ D.Ψ x) i = _
    rw [this, cmat_mulVec]
  · have : D.h x = fun j => (h₀ j : ℂ) := funext (H.2 x hx)
    show (cmat Q *ᵥ D.h x) i = _
    rw [this, cmat_mulVec]

theorem realizesC_rot {Q : Matrix (Fin N) (Fin N) ℝ} {D : BgData G N}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (H : RealizesC D Ψ₀ h₀ Ψ'' h'') :
    RealizesC (D.rot (cmat Q)) (fun x => Q *ᵥ Ψ₀ x) (Q *ᵥ h₀) (fun x => cmat Q *ᵥ Ψ'' x)
      (fun x => cmat Q *ᵥ h'' x) := by
  refine ⟨fun x hx i => ?_, fun x hx i => ?_⟩
  · have : D.Ψ x = (fun j => (Ψ₀ x j : ℂ)) + Ψ'' x := funext fun j => H.1 x hx j
    show (cmat Q *ᵥ D.Ψ x) i = _
    rw [this, Matrix.mulVec_add, cmat_mulVec]; rfl
  · have : D.h x = (fun j => (h₀ j : ℂ)) + h'' x := funext fun j => H.2 x hx j
    show (cmat Q *ᵥ D.h x) i = _
    rw [this, Matrix.mulVec_add, cmat_mulVec]; rfl

theorem xiBounds_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν σ ε : ℝ} {n : ℕ}
    {D : BgData G N} {h₀ : Fin N → ℝ} {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (H : XiBounds G ν n σ ε D h₀ φ α) :
    XiBounds G ν n σ ε (D.rot (cmat Q)) (Q *ᵥ h₀) (rotFld (cmat Q) φ) α := by
  have hR := isRealOrth_ofReal hQ
  have hb : ∀ y i, barField G (D.rot (cmat Q)).Ψ (rotFld (cmat Q) φ) y i =
      (cmat Q *ᵥ fun j => barField G D.Ψ φ y j) i := fun y i =>
    congrFun (barField_rot (cmat Q) D.Ψ φ y) i
  refine
    { grad := fun x hx μ => ?_
      lap := fun x hx => ?_
      mult := H.mult
      close := fun x hx => ?_
      collarBond := fun z hz z' hz' hadj => ?_
      mass := fun z => ?_
      hnorm := by rw [sum_sq_rot_real hQ]; exact H.hnorm }
  · simp only [hb]
    rw [vn_sub_rot hR, vn_sub_rot hR]
    exact H.grad x hx μ
  · simp only [hb]
    rw [rot_lap, vn_rot hR]
    exact H.lap x hx
  · have e := congrFun (blockAvg_rot (cmat Q) φ x)
    show vn (fun i => (cmat Q *ᵥ D.Ψ x) i - blockAvg G (rotFld (cmat Q) φ) x i) < _
    simp only [e]
    rw [vn_sub_rot hR]
    exact H.close x hx
  · show vn (fun i => (cmat Q *ᵥ D.Ψ z) i - (cmat Q *ᵥ D.Ψ z') i) < _
    rw [vn_sub_rot hR]
    exact H.collarBond z hz z' hz' hadj
  · have e : ∀ i, ((Q *ᵥ h₀) i : ℂ) = (cmat Q *ᵥ fun j => (h₀ j : ℂ)) i := cmat_mulVec Q h₀
    have e2 : ∀ i, rotFld (cmat Q) φ (z, i) = (cmat Q *ᵥ fun j => φ (z, j)) i := fun i => rfl
    simp only [e, e2]
    rw [vn_sub_rot hR]
    exact H.mass z

theorem xiCBounds_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {ν σ ε : ℝ}
    {Dr Dc : BgData G N} {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ}
    {φr φc : G.Ω 1 × Fin N → ℂ} {αr αc : G.Ω 1 → ℂ}
    (H : XiCBounds G ν σ ε Dr Dc Ψ'' h'' φr φc αr αc) :
    XiCBounds G ν σ ε (Dr.rot (cmat Q)) (Dc.rot (cmat Q)) (fun x => cmat Q *ᵥ Ψ'' x)
      (fun x => cmat Q *ᵥ h'' x) (rotFld (cmat Q) φr) (rotFld (cmat Q) φc) αr αc := by
  have hR := isRealOrth_ofReal hQ
  have hb : ∀ (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) y i,
      barField G (D.rot (cmat Q)).Ψ (rotFld (cmat Q) φ) y i =
      (cmat Q *ᵥ fun j => barField G D.Ψ φ y j) i := fun D φ y i =>
    congrFun (barField_rot (cmat Q) D.Ψ φ y) i
  have key : ∀ f : Fin N → ℂ, vn (fun i => (cmat Q *ᵥ f) i) = vn f := fun f => vn_rot hR f
  refine
    { grad := fun x hx μ => ?_
      lap := fun x hx => ?_
      mult := H.mult
      val := fun x => ?_
      close := fun x hx => ?_
      collarBond := fun z hz z' hz' hadj => ?_
      hAbs := fun x hx => ?_
      hDot := fun x => ?_ }
  · simp only [hb, sub_rot_apply, key]
    exact H.grad x hx μ
  · simp only [hb, sub_rot_apply]
    rw [rot_lap]
    simp only [key]
    exact H.lap x hx
  · have e : ∀ (φ : G.Ω 1 × Fin N → ℂ) i, rotFld (cmat Q) φ (x, i) = (cmat Q *ᵥ fun j => φ (x, j)) i :=
      fun φ i => rfl
    simp only [e]
    rw [vn_sub_rot hR]
    exact H.val x
  · have e := congrFun (blockAvg_rot (cmat Q) (φc - φr) x)
    show vn (fun i => (cmat Q *ᵥ Ψ'' x) i - blockAvg G (rotFld (cmat Q) φc - rotFld (cmat Q) φr) x i) < _
    rw [← rotFld_sub]
    simp only [e]
    rw [vn_sub_rot hR]
    exact H.close x hx
  · show vn (fun i => (cmat Q *ᵥ Ψ'' z) i - (cmat Q *ᵥ Ψ'' z') i) < _
    rw [vn_sub_rot hR]
    exact H.collarBond z hz z' hz' hadj
  · show _ * vn (cmat Q *ᵥ h'' x) < _
    rw [vn_rot hR]
    exact H.hAbs x hx
  · have e : ∀ i, rotFld (cmat Q) φr (x, i) = (cmat Q *ᵥ fun j => φr (x, j)) i := fun i => rfl
    show _ * ‖∑ i, rotFld (cmat Q) φr (x, i) * (cmat Q *ᵥ h'' x) i‖ < _
    simp only [e]
    rw [bilin_vec hR.1]
    exact H.hDot x
end Domain

section Spaces

variable (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)

theorem xi_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    (H : Xi G a ν n σ ε Ψ₀ h₀) : Xi G a ν n σ ε (fun x => Q *ᵥ Ψ₀ x) (Q *ᵥ h₀) := by
  obtain ⟨hσ, hε, D, hre, hdom, hb⟩ := H
  refine ⟨hσ, hε, D.rot (cmat Q), realizes_rot hre, inUnionDomainR_rot hQ hdom, ?_⟩
  rw [bgField_rot a ν (isRealOrth_ofReal hQ), bgMult_rot a ν (isRealOrth_ofReal hQ)]
  exact xiBounds_rot hQ hb

/-- **O(N)-covariance of `Ξ_n(𝔹; σ, ε)`** (real orthogonal `Q`): `(Q Ψ₀, Q h₀) ∈ Ξ` iff
`(Ψ₀, h₀) ∈ Ξ`. -/
theorem xi_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ} :
    Xi G a ν n σ ε (fun x => Q *ᵥ Ψ₀ x) (Q *ᵥ h₀) ↔ Xi G a ν n σ ε Ψ₀ h₀ := by
  refine ⟨fun H => ?_, xi_rot G a ν hQ⟩
  have hQ' : Qᵀᵀ * Qᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.1 hQ
  have := xi_rot G a ν hQ' H
  simpa [Matrix.mulVec_mulVec, hQ] using this

theorem xiC_rot {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} (H : XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'') :
    XiC G a ν n σ ε (fun x => Q *ᵥ Ψ₀ x) (Q *ᵥ h₀) (fun x => cmat Q *ᵥ Ψ'' x)
      (fun x => cmat Q *ᵥ h'' x) := by
  obtain ⟨hσ, hε, Dr, Dc, hr, hrc, hdom, hb⟩ := H
  have hR := isRealOrth_ofReal hQ
  refine ⟨hσ, hε, Dr.rot (cmat Q), Dc.rot (cmat Q), ?_, realizesC_rot hrc,
    inUnionDomainC_rot hQ hdom, ?_⟩
  · obtain ⟨hre, hdomr, hbr⟩ := hr
    refine ⟨realizes_rot hre, inUnionDomainR_rot hQ hdomr, ?_⟩
    rw [bgField_rot a ν hR, bgMult_rot a ν hR]
    exact xiBounds_rot hQ hbr
  · rw [bgField_rot a ν hR, bgMult_rot a ν hR, (bgFieldC_rot a ν hR.1 _ Dc).1,
      (bgFieldC_rot a ν hR.1 _ Dc).2]
    exact xiCBounds_rot hQ hb

/-- **O(N)-covariance of `Ξ^c_n(𝔹; σ, ε)`** (real orthogonal `Q` acting on the real base
point and on the complex displacements). -/
theorem xiC_rot_iff {Q : Matrix (Fin N) (Fin N) ℝ} (hQ : Qᵀ * Q = 1) {n : ℕ} {σ ε : ℝ}
    {Ψ₀ : Torus d (N₀ * L ^ k) → Fin N → ℝ} {h₀ : Fin N → ℝ}
    {Ψ'' h'' : Torus d (N₀ * L ^ k) → Fin N → ℂ} :
    XiC G a ν n σ ε (fun x => Q *ᵥ Ψ₀ x) (Q *ᵥ h₀) (fun x => cmat Q *ᵥ Ψ'' x)
      (fun x => cmat Q *ᵥ h'' x) ↔ XiC G a ν n σ ε Ψ₀ h₀ Ψ'' h'' := by
  refine ⟨fun H => ?_, xiC_rot G a ν hQ⟩
  have hQ' : Qᵀᵀ * Qᵀ = 1 := by
    rw [Matrix.transpose_transpose]; exact mul_eq_one_comm.1 hQ
  have := xiC_rot G a ν hQ' H
  have hc : cmat Qᵀ * cmat Q = 1 := by
    have := (isRealOrth_ofReal hQ).1
    simpa only [cmat, Matrix.transpose_map] using this
  simpa [Matrix.mulVec_mulVec, hQ, hc] using this

end Spaces
end Balaban.SmallField
