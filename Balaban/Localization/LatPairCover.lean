/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivLat

/-!
# Lattice symmetries between two generating sets: the cut operators and the decoupled Green's
operator

The covariance package of `DecEquivLat.lean` transports the operators of one pair `(C, H)` to
itself (`LatSymm H H σ`, `CoverSymm C σ`).  For the local generating sets `𝔹_{k+1}(Y⁺)` of the
local class a lattice symmetry `σ` maps the generating set of `Y` to that of `σ Y`, a different
generating set with a different cover.  This file proves the transport between two pairs
`(C, H)`, `(C', H')`, for a lattice symmetry `S : LatSymm H H' σ` (`EquivarianceLat.lean`; it maps
`Ω_j(H)` onto `Ω_j(H')`) and a permutation `τ` of the centres which maps the centres of `C` onto
those of `C'` and carries the partition functions, the interaction boxes and the neighbourhoods
`𝒬(z)` (the hypotheses `hidx`, `hchi`, `hbox`, `hqset`, the two-cover form of the fields of
`CoverSymm`):

* `cutOperator_sym_pair`: the cut operator of the image cut;
* `rm_cubeH_pair`, `rm_cubeG_pair`, `rm_Kz_pair`, `rm_Gstar_pair`, `rm_Kcal_pair`;
* `rm_Gs_pair`: `rm σ (G_s(α)) = G'_{s'}(σ α)` for parameters with `s' ∘ τ = s`.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

section CutPair

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G G' : GeneratingSet d L N₀ k ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ k))}
variable (S : LatSymm G G' σ)

theorem mem_cubeCut_bond_pair (Λ : Finset (Torus d (N₀ * L ^ k)))
    (b : Torus d (N₀ * L ^ k) × Fin d) :
    S.bond b ∈ cubeCut G' (siteImage σ Λ) ↔ b ∈ cubeCut G Λ := by
  obtain ⟨x, μ⟩ := b
  have h := S.step x μ
  rw [mem_cubeCut, mem_cubeCut]
  cases hf : S.flip μ
  · rw [hf] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have e : S.bond (x, μ) = (σ x, S.perm μ) := by simp [NbrSymm.bond, hf]
    rw [e]
    simp only [← h, mem_siteImage, S.mem_Ω1]
  · rw [hf] at h
    simp only [↓reduceIte] at h
    have e : S.bond (x, μ) = (σ x - Pi.single (S.perm μ) 1, S.perm μ) := by
      simp [NbrSymm.bond, hf]
    have h2 : σ x - Pi.single (S.perm μ) 1 + Pi.single (S.perm μ) 1 = σ x := by abel
    rw [e, h2, ← h]
    simp only [mem_siteImage, S.mem_Ω1]
    tauto

theorem cubeCut_siteImage_pair (Λ : Finset (Torus d (N₀ * L ^ k))) :
    cubeCut G' (siteImage σ Λ) = (cubeCut G Λ).map (bondEmb S.toNbrSymm) := by
  ext b'
  obtain ⟨b, rfl⟩ := S.bond_surjective b'
  rw [mem_cubeCut_bond_pair S, Finset.mem_map]
  constructor
  · intro h; exact ⟨b, h, rfl⟩
  · rintro ⟨c, hc, hcb⟩
    have : c = b := S.bond_injective hcb
    exact this ▸ hc

theorem cutLaplacian_sym_pair (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (y z : Torus d (N₀ * L ^ k)) :
    cutLaplacian ν (cut.map (bondEmb S.toNbrSymm)) (σ y) (σ z) = cutLaplacian ν cut y z := by
  unfold cutLaplacian
  rw [Matrix.sub_apply, Matrix.sub_apply, S.lap_sym, Matrix.sum_apply, Matrix.sum_apply,
    Finset.sum_map]
  congr 1
  exact Finset.sum_congr rfl fun b _ => S.toNbrSymm.bondMatrix_sym b y z

theorem cutOperator_sym_pair (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    cutOperator G' a ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α) (S.Ω1Equiv x) (S.Ω1Equiv y) =
      cutOperator G a ν cut α x y := by
  simp only [cutOperator, Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.map_apply, LatSymm.coe_Ω1Equiv, cutFullMatrix, Matrix.add_apply,
    cutLaplacian_sym_pair S, S.avg_sym, LatSymm.mul_apply, Equiv.apply_eq_iff_eq]

end CutPair

section TransportPair

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C C' : DecCover d L N₁ m₁ K} {H H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm H H' σ)
  {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

theorem intBox_eq_pair (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (q : ℕ × CTorus d L N₁ m₁ K) : intBox (τ q) = siteImage σ (intBox q) := by
  ext z
  obtain ⟨x, rfl⟩ := σ.surjective z
  rw [mem_siteImage]
  exact hbox q x

/-- The factors `s_z = ∏_{P ∈ 𝒬(z)} s_P` correspond for parameters with `s' ∘ τ = s`. -/
theorem sProd_pair (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ} (hs : ∀ P, s' (τ P) = s P)
    (q : ℕ × CTorus d L N₁ m₁ K) : C'.sProd s' (τ q) = C.sProd s q := by
  unfold DecCover.sProd
  refine (Finset.prod_equiv τ (fun P => (hqset q P).symm) fun P _ => ?_).symm
  rw [hs]

theorem rm_cD_pair (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (q : ℕ × CTorus d L N₁ m₁ K) : rm S.Ω1Equiv (cD H q) = cD H' (τ q) := by
  classical
  unfold cD
  rw [rm_diagonal]
  congr 1
  funext z
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective z
  have h := hbox q x
  simp only [Function.comp, Equiv.symm_apply_apply, LatSymm.coe_Ω1Equiv]
  by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ intBox q
  · simp [hx, h.2 hx]
  · have : σ (x : CTorus d L N₁ m₁ K) ∉ intBox (τ q) := fun hh => hx (h.1 hh)
    simp [hx, this]

theorem rm_chiD_pair (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (Dec2.chiD C H q) = Dec2.chiD C' H' (τ q) := by
  unfold Dec2.chiD
  rw [rm_diagonal]
  congr 1
  funext z
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective z
  simp [hchi]

theorem rm_dirichlet_pair (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) :
    rm S.Ω1Equiv (dirichletOperator H a ν α) = dirichletOperator H' a ν (S.mul α) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply, S.dirichlet_sym]

theorem rm_cubeH_pair (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (cubeH H a ν α q) = cubeH H' a ν (S.mul α) (τ q) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply]
  unfold cubeH
  rw [intBox_eq_pair hbox, cubeCut_siteImage_pair S, cutOperator_sym_pair S]

theorem rm_cubeG_pair (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (cubeG H a ν α q) = cubeG H' a ν (S.mul α) (τ q) := by
  unfold cubeG
  rw [rm_mul, rm_inv, rm_cubeH_pair S hbox, rm_cD_pair S hbox]

theorem rm_Kz_pair (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (a : ℕ → ℝ) (ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (Dec2.Kz C H a ν q) = Dec2.Kz C' H' a ν (τ q) := by
  have h0 : S.mul (0 : H.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  unfold Dec2.Kz
  rw [rm_sub, rm_mul, rm_mul, rm_chiD_pair S hchi, rm_dirichlet_pair S, h0]

theorem rm_Gstar_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hs : ∀ P, s' (τ P) = s P) :
    rm S.Ω1Equiv (Dec2.Gstar C H a ν α s) = Dec2.Gstar C' H' a ν (S.mul α) s' := by
  unfold Dec2.Gstar
  rw [rm_sum]
  refine Finset.sum_equiv τ (fun q => (hidx q).symm) fun q _ => ?_
  rw [rm_smul, rm_mul, rm_chiD_pair S hchi, rm_cubeG_pair S hbox, sProd_pair hqset hs]

theorem rm_Kcal_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hs : ∀ P, s' (τ P) = s P) :
    rm S.Ω1Equiv (Dec2.Kcal C H a ν α s) = Dec2.Kcal C' H' a ν (S.mul α) s' := by
  unfold Dec2.Kcal
  rw [rm_sum]
  refine Finset.sum_equiv τ (fun q => (hidx q).symm) fun q _ => ?_
  rw [rm_smul, rm_mul, rm_Kz_pair S hchi, rm_cubeG_pair S hbox, sProd_pair hqset hs]

/-- **Lattice-symmetry covariance of the decoupled Green's operator between two pairs**:
`G'_{s'}(σ α) = σ G_s(α) σ⁻¹` for `s' ∘ τ = s`. -/
theorem rm_Gs_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) {s s' : ℕ × CTorus d L N₁ m₁ K → ℂ}
    (hs : ∀ P, s' (τ P) = s P) :
    rm S.Ω1Equiv (Dec2.Gs C H a ν α s) = Dec2.Gs C' H' a ν (S.mul α) s' := by
  unfold Dec2.Gs
  rw [rm_mul, rm_Gstar_pair S hidx hchi hbox hqset a ν α hs, rm_inv, rm_sub, rm_one,
    rm_Kcal_pair S hidx hchi hbox hqset a ν α hs]

end TransportPair

end Balaban.Localization.DecEquiv
