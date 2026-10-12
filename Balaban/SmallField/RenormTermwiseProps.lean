/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.RenormTermwiseSum

/-!
# Lemma 3.2 (ii): locality, `O(N)`-invariance, analyticity

* `Ttw_congr`, `Ax_congr`, `Phitw_congr`, `Itw_congr`: `T_X` depends on the data only through
  `(ψ(y), b)`, `A_{y,X}` only through `ψ|_X`, `Φ_{y,X}` only through the star
  `{y, y + e_μ}` of `y`, and `I(y,X)` only through `X ∪ star`;
* `Ttw_rot`, `Ax_rot`, `Phitw_rot`, `Itw_rot`: invariance under complex orthogonal `R`;
* `Ttw_analytic`, `Ax_analytic`, `Phitw_analytic`, `Itw_analytic`: analyticity as functions of the
  finitely many coordinates `c : Cfg d N W` of the data on a finite set `W ⊇ X ∪ star`
  (`unpsi`, `unb`).  `I(y,X)` is analytic wherever `𝓔(y,X)` is (the `Tube`) and `ψ(y)·ψ(y)`
  avoids the closed negative axis; the latter is needed by `T_X` (the root `u`) and `Φ_{y,X}`
  (the pole at `ψ(y)·ψ(y) = 0`).
-/

@[expose] public section

open Metric Set Matrix

namespace Balaban.SmallField

variable {d N : ℕ}

/-- The star of the origin: `0` and its forward neighbours `e_μ`. -/
noncomputable def starSet (d : ℕ) : Finset (Site d) := by
  classical exact insert 0 (Finset.univ.image eU)

theorem zero_mem_starSet : (0 : Site d) ∈ starSet d := by
  classical
  unfold starSet
  exact Finset.mem_insert_self _ _

theorem eU_mem_starSet (μ : Fin d) : eU μ ∈ starSet d := by
  classical
  unfold starSet
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ μ))

section Local

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν : ℝ} {X : Finset (Site d)}
  {ψ ψ' : Site d → Spin N} {b : Spin N}

theorem uInv_congr (h : ψ 0 = ψ' 0) : uInv ψ = uInv ψ' := by unfold uInv; rw [h]

theorem vInv_congr (h : ψ 0 = ψ' 0) : vInv ψ b = vInv ψ' b := by
  unfold vInv; rw [h, uInv_congr h]

theorem Ttw_congr (h : ψ 0 = ψ' 0) : Ttw T i₀ ν X ψ b = Ttw T i₀ ν X ψ' b := by
  unfold Ttw; rw [uInv_congr h, vInv_congr h]

theorem pack_congr (h : ∀ x ∈ X, ψ x = ψ' x) (b : Spin N) : pack X ψ b = pack X ψ' b := by
  ext (⟨x, i⟩ | i)
  · simp [pack, h x.1 x.2]
  · simp [pack]

theorem Ax_congr (h : ∀ x ∈ X, ψ x = ψ' x) (h0 : (0 : Site d) ∈ X) :
    Ax T i₀ ν ψ X = Ax T i₀ ν ψ' X := by
  unfold Ax
  rw [h 0 h0]
  congr 1
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [h x.1 x.2]

theorem gradInv_congr (h : ∀ x ∈ starSet d, ψ x = ψ' x) (μ μ' : Fin d) :
    gradInv ψ μ μ' = gradInv ψ' μ μ' := by
  unfold gradInv
  rw [h 0 zero_mem_starSet, h (eU μ) (eU_mem_starSet μ), h (eU μ') (eU_mem_starSet μ')]

theorem Phitw_congr (h : ∀ x ∈ starSet d, ψ x = ψ' x) :
    Phitw T i₀ i₁ ν X ψ = Phitw T i₀ i₁ ν X ψ' := by
  unfold Phitw
  simp only [gradInv_congr h]

/-- **(ii), locality**: `I(y,X)` depends on `ψ` only through `X ∪ star`. -/
theorem Itw_congr (h0 : (0 : Site d) ∈ X) (h : ∀ x ∈ X ∪ starSet d, ψ x = ψ' x) :
    Itw T i₀ i₁ ν X ψ b = Itw T i₀ i₁ ν X ψ' b := by
  have hX : ∀ x ∈ X, ψ x = ψ' x := fun x hx => h x (Finset.mem_union_left _ hx)
  have hs : ∀ x ∈ starSet d, ψ x = ψ' x := fun x hx => h x (Finset.mem_union_right _ hx)
  unfold Itw
  rw [pack_congr hX, Ttw_congr (hs 0 zero_mem_starSet), Ax_congr hX h0, Phitw_congr hs]

end Local

section Rot

variable {T : TermFamily d N} {i₀ i₁ : Fin N} {ν ρ E₀ κ A K₀ : ℝ} {X : Finset (Site d)}
  {Dom : Set ((Site d → Spin N) × Spin N)} {ψ : Site d → Spin N} {b : Spin N}
  {R : Matrix (Fin N) (Fin N) ℂ}

theorem uInv_rot (hR : IsOrth R) : uInv (fun x => R.mulVec (ψ x)) = uInv ψ := by
  unfold uInv; rw [dot_mulVec_rot hR]

theorem vInv_rot (hR : IsOrth R) : vInv (fun x => R.mulVec (ψ x)) (R.mulVec b) = vInv ψ b := by
  unfold vInv; rw [uInv_rot hR, dot_mulVec_rot hR]

theorem Ttw_rot (hR : IsOrth R) :
    Ttw T i₀ ν X (fun x => R.mulVec (ψ x)) (R.mulVec b) = Ttw T i₀ ν X ψ b := by
  unfold Ttw; rw [uInv_rot hR, vInv_rot hR]

theorem Ax_rot (hR : IsOrth R) :
    Ax T i₀ ν (fun x => R.mulVec (ψ x)) X = Ax T i₀ ν ψ X := by
  unfold Ax; simp only [dot_mulVec_rot hR]

theorem gradInv_rot (hR : IsOrth R) (μ μ' : Fin d) :
    gradInv (fun x => R.mulVec (ψ x)) μ μ' = gradInv ψ μ μ' := by
  unfold gradInv
  simp only [← Matrix.mulVec_sub, dot_mulVec_rot hR]

theorem Phitw_rot (hR : IsOrth R) :
    Phitw T i₀ i₁ ν X (fun x => R.mulVec (ψ x)) = Phitw T i₀ i₁ ν X ψ := by
  unfold Phitw; simp only [gradInv_rot hR]

/-- **(ii), `O(N)`-invariance**: `I(y,X)` is invariant under a complex orthogonal `R` with bounded
entries whenever the configuration and its image lie in the analyticity domain of the term. -/
theorem Itw_rot (hP : PremisesTerm T i₀ i₁ ν ρ E₀ κ A K₀ Dom) (hX : X ∈ T.polys)
    (hR : IsOrth R) (hb : EntryBd N R) (hc : pack X ψ b ∈ Tube i₀ ν ρ X)
    (hm : pack X (fun x => R.mulVec (ψ x)) (R.mulVec b) ∈ Tube i₀ ν ρ X) :
    Itw T i₀ i₁ ν X (fun x => R.mulVec (ψ x)) (R.mulVec b) = Itw T i₀ i₁ ν X ψ b := by
  have hm' : rotCfgL R X (pack X ψ b) ∈ Tube i₀ ν ρ X := by rwa [rotCfgL_pack]
  have h := hP.rot_inv X hX _ hc R hR hb hm'
  rw [rotCfgL_pack] at h
  unfold Itw
  rw [h, Ttw_rot hR, Ax_rot hR, Phitw_rot hR]

end Rot

end Balaban.SmallField
