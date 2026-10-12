/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Equivariance
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

theorem sub_rot_apply (R : Matrix (Fin N) (Fin N) ℂ) (u w : Fin N → ℂ) (i : Fin N) :
    (R *ᵥ u) i - (R *ᵥ w) i = (R *ᵥ fun j => u j - w j) i := by
  simp [Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]

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
