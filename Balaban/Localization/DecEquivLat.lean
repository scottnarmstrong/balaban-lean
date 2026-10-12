/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Self
public import Balaban.Background.EquivarianceLat

/-!
# Lattice-symmetry covariance of the cut operators (LOCALIZATION.md, symmetry clause)

For a lattice symmetry `S : LatSymm G G σ` of a generating set (`Balaban/Background/EquivarianceLat.lean`)
the operators of the decoupled Green's function are transported: the bonds of the lattice are
mapped to bonds (`NbrSymm.bond`), the matrices `bondMatrix` are invariant
(`bondMatrix_sym`), the cube cut of the image of a set is the image of the cube cut
(`cubeCut_sym`), and therefore `cutOperator G a ν (cubeCut G (σ Λ)) (S.mul α)` is the transport of
`cutOperator G a ν (cubeCut G Λ) α` (`cutOperator_sym`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {σ : Equiv.Perm (Torus d (N₀ * L ^ k))}

section Bonds

/-- The image of the bond `(x, μ)` under the symmetry: the bond `(σ x, π μ)` or, if the
orientation is reversed, the bond `(σ x - e_{π μ}, π μ)` (it has the endpoints `σ x`, `σ(x + e_μ)`). -/
def NbrSymm.bond (S : NbrSymm σ) (b : Torus d (N₀ * L ^ k) × Fin d) :
    Torus d (N₀ * L ^ k) × Fin d :=
  (if S.flip b.2 then σ b.1 - Pi.single (S.perm b.2) 1 else σ b.1, S.perm b.2)

variable (S : NbrSymm σ)

omit [NeZero N₀] [NeZero L] in
theorem NbrSymm.bondVec_sym (b : Torus d (N₀ * L ^ k) × Fin d) (y : Torus d (N₀ * L ^ k)) :
    bondVec (S.bond b) (σ y) = (if S.flip b.2 then -1 else 1) * bondVec b y := by
  have h := S.step b.1 b.2
  cases hf : S.flip b.2
  · rw [hf] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    have e : S.bond b = (σ b.1, S.perm b.2) := by simp [NbrSymm.bond, hf]
    rw [e]
    simp only [bondVec, Pi.sub_apply, Pi.single_apply, ← h, Equiv.apply_eq_iff_eq]
    simp
  · rw [hf] at h
    simp only [↓reduceIte] at h
    have e : S.bond b = (σ b.1 - Pi.single (S.perm b.2) 1, S.perm b.2) := by simp [NbrSymm.bond, hf]
    rw [e]
    have h2 : σ b.1 - Pi.single (S.perm b.2) 1 + Pi.single (S.perm b.2) 1 = σ b.1 := by abel
    simp only [bondVec, Pi.sub_apply, Pi.single_apply, h2]
    simp only [← h, Equiv.apply_eq_iff_eq]
    simp only [↓reduceIte]
    ring

omit [NeZero N₀] [NeZero L] in
theorem NbrSymm.bondMatrix_sym (b : Torus d (N₀ * L ^ k) × Fin d) (y z : Torus d (N₀ * L ^ k)) :
    bondMatrix (S.bond b) (σ y) (σ z) = bondMatrix b y z := by
  simp only [bondMatrix, Matrix.vecMulVec_apply, S.bondVec_sym]
  cases S.flip b.2 <;> simp

omit [NeZero N₀] [NeZero L] in
theorem NbrSymm.bond_injective : Function.Injective S.bond := by
  rintro ⟨x, μ⟩ ⟨x', μ'⟩ h
  simp only [NbrSymm.bond, Prod.mk.injEq] at h
  obtain ⟨h1, h2⟩ := h
  have hμ : μ = μ' := S.perm.injective h2
  subst hμ
  cases hf : S.flip μ
  · simp only [hf] at h1
    simp [σ.injective h1]
  · simp only [hf] at h1
    have := sub_left_injective h1
    simp [σ.injective this]

omit [NeZero N₀] [NeZero L] in
theorem NbrSymm.bond_surjective : Function.Surjective S.bond := by
  rintro ⟨y, ν⟩
  obtain ⟨μ, rfl⟩ : ∃ μ, S.perm μ = ν := ⟨S.perm.symm ν, by simp⟩
  cases hf : S.flip μ
  · refine ⟨(σ.symm y, μ), ?_⟩
    simp [NbrSymm.bond, hf]
  · refine ⟨(σ.symm (y + Pi.single (S.perm μ) 1), μ), ?_⟩
    simp [NbrSymm.bond, hf]

end Bonds

end Balaban.Background

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L N₀ k ϱ} {σ : Equiv.Perm (Torus d (N₀ * L ^ k))}

/-- The map on bonds of a symmetry, as an embedding. -/
def bondEmb (S : NbrSymm σ) : (Torus d (N₀ * L ^ k) × Fin d) ↪ (Torus d (N₀ * L ^ k) × Fin d) :=
  ⟨S.bond, S.bond_injective⟩

/-- The image of a set of sites under the symmetry. -/
def siteImage (σ : Equiv.Perm (Torus d (N₀ * L ^ k))) (Λ : Finset (Torus d (N₀ * L ^ k))) :
    Finset (Torus d (N₀ * L ^ k)) := Λ.map σ.toEmbedding

omit [NeZero N₀] [NeZero L] in
theorem mem_siteImage {Λ : Finset (Torus d (N₀ * L ^ k))} (x : Torus d (N₀ * L ^ k)) :
    σ x ∈ siteImage σ Λ ↔ x ∈ Λ := by
  simp [siteImage]

section CutSym

variable (S : LatSymm G G σ)

theorem mem_cubeCut_bond (Λ : Finset (Torus d (N₀ * L ^ k))) (b : Torus d (N₀ * L ^ k) × Fin d) :
    S.bond b ∈ cubeCut G (siteImage σ Λ) ↔ b ∈ cubeCut G Λ := by
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

theorem cubeCut_siteImage (Λ : Finset (Torus d (N₀ * L ^ k))) :
    cubeCut G (siteImage σ Λ) = (cubeCut G Λ).map (bondEmb S.toNbrSymm) := by
  ext b'
  obtain ⟨b, rfl⟩ := S.bond_surjective b'
  rw [mem_cubeCut_bond S, Finset.mem_map]
  constructor
  · intro h; exact ⟨b, h, rfl⟩
  · rintro ⟨c, hc, hcb⟩
    have : c = b := S.bond_injective hcb
    exact this ▸ hc

theorem cutLaplacian_sym (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (y z : Torus d (N₀ * L ^ k)) :
    cutLaplacian ν (cut.map (bondEmb S.toNbrSymm)) (σ y) (σ z) = cutLaplacian ν cut y z := by
  unfold cutLaplacian
  rw [Matrix.sub_apply, Matrix.sub_apply, S.lap_sym, Matrix.sum_apply, Matrix.sum_apply,
    Finset.sum_map]
  congr 1
  exact Finset.sum_congr rfl fun b _ => S.toNbrSymm.bondMatrix_sym b y z

theorem cutOperator_sym (a : ℕ → ℝ) (ν : ℝ) (cut : Finset (Torus d (N₀ * L ^ k) × Fin d))
    (α : G.Ω 1 → ℂ) (x y : G.Ω 1) :
    cutOperator G a ν (cut.map (bondEmb S.toNbrSymm)) (S.mul α) (S.Ω1Equiv x) (S.Ω1Equiv y) =
      cutOperator G a ν cut α x y := by
  simp only [cutOperator, Matrix.add_apply, Green.restrictOp, Matrix.submatrix_apply,
    Matrix.diagonal_apply, Matrix.map_apply, LatSymm.coe_Ω1Equiv, cutFullMatrix, Matrix.add_apply,
    cutLaplacian_sym S, S.avg_sym, LatSymm.mul_apply, Equiv.apply_eq_iff_eq]

end CutSym

end Balaban.Localization.DecEquiv

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Compatibility of a lattice symmetry `σ` with a cover.**  The symmetry `σ` of the paved torus
maps the cubes of the cover to cubes of the cover: it induces a permutation `τ` of the centres
`(j, y₀)` (a cube of the layer `j` is sent to a cube of the layer `j`; for a reflection the base
point `y₀` goes to the opposite corner of the image cube), which preserves the index set of the
cover, the partition functions, the interaction boxes and the neighbourhoods `𝒬(z)`. -/
structure CoverSymm (C : DecCover d L N₁ m₁ K) (σ : Equiv.Perm (CTorus d L N₁ m₁ K)) where
  /-- The action on the centres of the cubes. -/
  τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)
  idx : ∀ q, τ q ∈ C.cubeIdx ↔ q ∈ C.cubeIdx
  chi : ∀ q x, C.chi (τ q) (σ x) = C.chi q x
  box : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q
  qset : ∀ q q', τ q' ∈ C.Qset (τ q) ↔ q' ∈ C.Qset q

/-- The identity is compatible with every cover. -/
def CoverSymm.refl (C : DecCover d L N₁ m₁ K) : CoverSymm C (1 : Equiv.Perm (CTorus d L N₁ m₁ K)) where
  τ := 1
  idx := fun _ => Iff.rfl
  chi := fun _ _ => rfl
  box := fun _ _ => Iff.rfl
  qset := fun _ _ => Iff.rfl

theorem coverSymm_nonempty (C : DecCover d L N₁ m₁ K) :
    Nonempty (CoverSymm C (1 : Equiv.Perm (CTorus d L N₁ m₁ K))) := ⟨CoverSymm.refl C⟩

section Reindex

set_option linter.unusedSectionVars false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Transport of a matrix along a bijection of the index set: `(rm e M) (e x) (e y) = M x y`. -/
def rm (e : ι ≃ κ) (M : Matrix ι ι ℂ) : Matrix κ κ ℂ := M.submatrix e.symm e.symm

@[simp] theorem rm_apply (e : ι ≃ κ) (M : Matrix ι ι ℂ) (x y : ι) : rm e M (e x) (e y) = M x y := by
  simp [rm]

theorem rm_mul (e : ι ≃ κ) (A B : Matrix ι ι ℂ) : rm e (A * B) = rm e A * rm e B := by
  simp [rm, Matrix.submatrix_mul_equiv]

theorem rm_add (e : ι ≃ κ) (A B : Matrix ι ι ℂ) : rm e (A + B) = rm e A + rm e B := by
  ext x y; simp [rm]

theorem rm_sub (e : ι ≃ κ) (A B : Matrix ι ι ℂ) : rm e (A - B) = rm e A - rm e B := by
  ext x y; simp [rm]

theorem rm_smul (e : ι ≃ κ) (c : ℂ) (A : Matrix ι ι ℂ) : rm e (c • A) = c • rm e A := by
  ext x y; simp [rm]

theorem rm_one (e : ι ≃ κ) : rm e (1 : Matrix ι ι ℂ) = 1 := by
  simp [rm]

theorem rm_sum (e : ι ≃ κ) {α : Type*} (s : Finset α) (f : α → Matrix ι ι ℂ) :
    rm e (∑ a ∈ s, f a) = ∑ a ∈ s, rm e (f a) := by
  ext x y; simp [rm, Matrix.sum_apply]

theorem rm_diagonal (e : ι ≃ κ) (f : ι → ℂ) : rm e (Matrix.diagonal f) = Matrix.diagonal (f ∘ e.symm) := by
  ext x y
  simp [rm, Matrix.diagonal_apply]

theorem rm_inv (e : ι ≃ κ) (A : Matrix ι ι ℂ) : rm e A⁻¹ = (rm e A)⁻¹ := by
  simp [rm, Matrix.inv_submatrix_equiv]

end Reindex

section Transport

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm H H σ) (CS : CoverSymm C σ)

theorem CoverSymm.intBox_eq (q : ℕ × CTorus d L N₁ m₁ K) :
    intBox (CS.τ q) = siteImage σ (intBox q) := by
  ext z
  obtain ⟨x, rfl⟩ := σ.surjective z
  rw [mem_siteImage]
  exact CS.box q x

/-- The transported decoupling parameters `s ∘ τ⁻¹`. -/
def CoverSymm.par (s : Dec2.DecParams C) : Dec2.DecParams C := fun P =>
  s ⟨CS.τ.symm P.1, (CS.idx _).1 (by simp)⟩

theorem CoverSymm.extS_par (s : Dec2.DecParams C) (P : ℕ × CTorus d L N₁ m₁ K) :
    Dec2.extS C (CS.par s) P = Dec2.extS C s (CS.τ.symm P) := by
  classical
  unfold Dec2.extS CoverSymm.par
  by_cases h : P ∈ C.cubeIdx
  · have h' : CS.τ.symm P ∈ C.cubeIdx := (CS.idx _).1 (by simpa using h)
    simp [h, h']
  · have h' : CS.τ.symm P ∉ C.cubeIdx := fun h' => h (by simpa using (CS.idx _).2 h')
    simp [h, h']

theorem CoverSymm.sProd_par (s : Dec2.DecParams C) (q : ℕ × CTorus d L N₁ m₁ K) :
    C.sProd (Dec2.extS C (CS.par s)) (CS.τ q) = C.sProd (Dec2.extS C s) q := by
  unfold DecCover.sProd
  refine (Finset.prod_equiv CS.τ (fun P => (CS.qset q P).symm) fun P _ => ?_).symm
  rw [CS.extS_par]; simp

theorem rm_cD (q : ℕ × CTorus d L N₁ m₁ K) : rm S.Ω1Equiv (cD H q) = cD H (CS.τ q) := by
  classical
  unfold cD
  rw [rm_diagonal]
  congr 1
  funext z
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective z
  have h := CS.box q x
  simp only [Function.comp, Equiv.symm_apply_apply, LatSymm.coe_Ω1Equiv]
  by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ intBox q
  · simp [hx, h.2 hx]
  · have : σ (x : CTorus d L N₁ m₁ K) ∉ intBox (CS.τ q) := fun hh => hx (h.1 hh)
    simp [hx, this]

theorem rm_chiD (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (Dec2.chiD C H q) = Dec2.chiD C H (CS.τ q) := by
  unfold Dec2.chiD
  rw [rm_diagonal]
  congr 1
  funext z
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective z
  simp [CS.chi]

theorem rm_dirichlet (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) :
    rm S.Ω1Equiv (dirichletOperator H a ν α) = dirichletOperator H a ν (S.mul α) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply, S.dirichlet_sym]

theorem rm_cubeH (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (cubeH H a ν α q) = cubeH H a ν (S.mul α) (CS.τ q) := by
  ext x' y'
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective x'
  obtain ⟨y, rfl⟩ := S.Ω1Equiv.surjective y'
  rw [rm_apply]
  unfold cubeH
  rw [CS.intBox_eq, cubeCut_siteImage S, cutOperator_sym S]

theorem rm_cubeG (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (cubeG H a ν α q) = cubeG H a ν (S.mul α) (CS.τ q) := by
  unfold cubeG
  rw [rm_mul, rm_inv, rm_cubeH S CS, rm_cD S CS]

theorem rm_Kz (a : ℕ → ℝ) (ν : ℝ) (q : ℕ × CTorus d L N₁ m₁ K) :
    rm S.Ω1Equiv (Dec2.Kz C H a ν q) = Dec2.Kz C H a ν (CS.τ q) := by
  have h0 : S.mul (0 : H.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  unfold Dec2.Kz
  rw [rm_sub, rm_mul, rm_mul, rm_chiD S CS, rm_dirichlet S, h0]

theorem rm_Gstar (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (s : Dec2.DecParams C) :
    rm S.Ω1Equiv (Dec2.Gstar C H a ν α (Dec2.extS C s)) =
      Dec2.Gstar C H a ν (S.mul α) (Dec2.extS C (CS.par s)) := by
  unfold Dec2.Gstar
  rw [rm_sum]
  refine Finset.sum_equiv CS.τ (fun q => (CS.idx q).symm) fun q _ => ?_
  rw [rm_smul, rm_mul, rm_chiD S CS, rm_cubeG S CS, CS.sProd_par]

theorem rm_Kcal (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (s : Dec2.DecParams C) :
    rm S.Ω1Equiv (Dec2.Kcal C H a ν α (Dec2.extS C s)) =
      Dec2.Kcal C H a ν (S.mul α) (Dec2.extS C (CS.par s)) := by
  unfold Dec2.Kcal
  rw [rm_sum]
  refine Finset.sum_equiv CS.τ (fun q => (CS.idx q).symm) fun q _ => ?_
  rw [rm_smul, rm_mul, rm_Kz S CS, rm_cubeG S CS, CS.sProd_par]

/-- **Lattice-symmetry covariance of the decoupled Green's operator**:
`G_{s ∘ τ⁻¹}(σ α) = σ G_s(α) σ⁻¹`. -/
theorem rm_Gs (a : ℕ → ℝ) (ν : ℝ) (α : H.Ω 1 → ℂ) (s : Dec2.DecParams C) :
    rm S.Ω1Equiv (Dec2.Gs C H a ν α (Dec2.extS C s)) =
      Dec2.Gs C H a ν (S.mul α) (Dec2.extS C (CS.par s)) := by
  unfold Dec2.Gs
  rw [rm_mul, rm_Gstar S CS, rm_inv, rm_sub, rm_one, rm_Kcal S CS]

end Transport

end Balaban.Localization.DecEquiv
