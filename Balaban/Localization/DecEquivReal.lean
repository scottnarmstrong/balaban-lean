/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.Decoupled2Self
public import Balaban.Localization.DecEquivRot

/-!
# Reality of the decoupled Green's operator (LOCALIZATION.md, symmetry clause)

For real decoupling parameters `s` (`im s_P = 0`) the decoupled Green's operator is conjugated
entrywise by complex conjugation of its argument: `conj (G_s(α)) = G_s(conj α)`
(`Gs_conj`, for a cover `C` and operator generating set `H`, and for the cover `G` by `Gs_self`).
All the ingredients (cut operators, the cube cut, the partition functions, the indicators) are real
matrices plus the diagonal `α`.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

local notation "cj" => starRingEnd ℂ

/-- Entrywise complex conjugate of a complex matrix. -/
def cjm {ι κ : Type*} (M : Matrix ι κ ℂ) : Matrix ι κ ℂ := M.map cj

theorem cjm_mul {ι κ μ : Type*} [Fintype κ] (A : Matrix ι κ ℂ) (B : Matrix κ μ ℂ) :
    cjm (A * B) = cjm A * cjm B := by
  ext i j; simp [cjm, Matrix.mul_apply, map_sum]

theorem cjm_add {ι κ : Type*} (A B : Matrix ι κ ℂ) : cjm (A + B) = cjm A + cjm B := by
  ext i j; simp [cjm]

theorem cjm_sub {ι κ : Type*} (A B : Matrix ι κ ℂ) : cjm (A - B) = cjm A - cjm B := by
  ext i j; simp [cjm]

theorem cjm_smul {ι κ : Type*} (c : ℂ) (A : Matrix ι κ ℂ) : cjm (c • A) = cj c • cjm A := by
  ext i j; simp [cjm]

theorem cjm_one {ι : Type*} [DecidableEq ι] : cjm (1 : Matrix ι ι ℂ) = 1 := by
  ext i j; simp [cjm, Matrix.one_apply]

theorem cjm_sum {ι κ α : Type*} (s : Finset α) (f : α → Matrix ι κ ℂ) :
    cjm (∑ a ∈ s, f a) = ∑ a ∈ s, cjm (f a) := by
  ext i j; simp [cjm, Matrix.sum_apply, map_sum]

theorem cjm_diagonal {ι : Type*} [DecidableEq ι] (f : ι → ℂ) :
    cjm (Matrix.diagonal f) = Matrix.diagonal fun i => cj (f i) := by
  ext i j; simp [cjm, Matrix.diagonal_apply]; split_ifs <;> simp

theorem cjm_inv {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ) :
    cjm A⁻¹ = (cjm A)⁻¹ := by
  rw [Matrix.inv_def, Matrix.inv_def]
  have h1 : ∀ B : Matrix ι ι ℂ, cjm B = (starRingEnd ℂ).mapMatrix B := fun B => rfl
  have h2 : cjm A.adjugate = (cjm A).adjugate := by
    rw [h1, h1, ← RingHom.map_adjugate]
  have h3 : (cjm A).det = cj A.det := by rw [h1, ← RingHom.map_det]
  ext i j
  have := congrFun (congrFun h2 i) j
  simp only [cjm, Matrix.map_apply] at this ⊢
  rw [Matrix.smul_apply, Matrix.smul_apply, ← this]
  simp only [cjm] at h3
  rw [smul_eq_mul, smul_eq_mul, map_mul, h3, Ring.inverse_eq_inv', map_inv₀]

theorem cjm_cjm {ι κ : Type*} (A : Matrix ι κ ℂ) : cjm (cjm A) = A := by
  ext i j; simp [cjm]

theorem cjm_mulVec {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℂ) (v : κ → ℂ) :
    (fun i => cj ((A *ᵥ v) i)) = cjm A *ᵥ fun k => cj (v k) := by
  funext i; simp [cjm, Matrix.mulVec, dotProduct, map_sum]

/-! ### The operators of the decoupled Green's function -/

section Operators

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem cjm_cutOperator (cut : Finset (CTorus d L N₁ m₁ K × Fin d)) (α : H.Ω 1 → ℂ) :
    cjm (cutOperator H a ν cut α) = cutOperator H a ν cut (fun x => cj (α x)) := by
  ext x y
  simp [cjm, cutOperator, Green.restrictOp, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem cjm_dirichlet (α : H.Ω 1 → ℂ) :
    cjm (dirichletOperator H a ν α) = dirichletOperator H a ν (fun x => cj (α x)) := by
  rw [← cutOperator_empty, ← cutOperator_empty, cjm_cutOperator]

theorem cjm_dirichlet_zero :
    cjm (dirichletOperator H a ν (0 : H.Ω 1 → ℂ)) = dirichletOperator H a ν 0 := by
  rw [cjm_dirichlet]; simp; rfl

theorem cjm_cD (q : ℕ × CTorus d L N₁ m₁ K) : cjm (cD H q) = cD H q := by
  unfold cD; rw [cjm_diagonal]; congr 1; funext x; split_ifs <;> simp

theorem cjm_chiD (q : ℕ × CTorus d L N₁ m₁ K) : cjm (Dec2.chiD C H q) = Dec2.chiD C H q := by
  unfold Dec2.chiD; rw [cjm_diagonal]; congr 1; funext x; simp

theorem cjm_cubeG (α : H.Ω 1 → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    cjm (cubeG H a ν α q) = cubeG H a ν (fun x => cj (α x)) q := by
  unfold cubeG cubeH
  rw [cjm_mul, cjm_inv, cjm_cutOperator, cjm_cD]

theorem cjm_Kz (q : ℕ × CTorus d L N₁ m₁ K) : cjm (Dec2.Kz C H a ν q) = Dec2.Kz C H a ν q := by
  unfold Dec2.Kz
  rw [cjm_sub, cjm_mul, cjm_mul, cjm_chiD, cjm_dirichlet_zero]

theorem sProd_conj (s : ℕ × CTorus d L N₁ m₁ K → ℂ) (q : ℕ × CTorus d L N₁ m₁ K) :
    C.sProd (fun P => cj (s P)) q = cj (C.sProd s q) := by
  unfold DecCover.sProd; rw [map_prod]

theorem cjm_Gstar (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    cjm (Dec2.Gstar C H a ν α s) =
      Dec2.Gstar C H a ν (fun x => cj (α x)) (fun P => cj (s P)) := by
  unfold Dec2.Gstar
  rw [cjm_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [cjm_smul, cjm_mul, cjm_chiD, cjm_cubeG, sProd_conj]

theorem cjm_Kcal (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    cjm (Dec2.Kcal C H a ν α s) =
      Dec2.Kcal C H a ν (fun x => cj (α x)) (fun P => cj (s P)) := by
  unfold Dec2.Kcal
  rw [cjm_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [cjm_smul, cjm_mul, cjm_Kz, cjm_cubeG, sProd_conj]

/-- **Conjugation of the decoupled Green's operator**: `conj G_s(α) = G_{conj s}(conj α)`. -/
theorem cjm_Gs (α : H.Ω 1 → ℂ) (s : ℕ × CTorus d L N₁ m₁ K → ℂ) :
    cjm (Dec2.Gs C H a ν α s) =
      Dec2.Gs C H a ν (fun x => cj (α x)) (fun P => cj (s P)) := by
  unfold Dec2.Gs
  rw [cjm_mul, cjm_Gstar, cjm_inv, cjm_sub, cjm_one, cjm_Kcal]

end Operators

/-! ### Real approximate field -/

section ApproxReal

/-- A vector is real. -/
def IsRealVec {ι : Type*} (x : ι → ℂ) : Prop := ∀ i, cj (x i) = x i

theorem sqrtDot_real {ι : Type*} [Fintype ι] {x : ι → ℂ} (hx : IsRealVec x) :
    cj (sqrtDot x) = sqrtDot x := by
  have h : x = cplx (fun i => (x i).re) := by
    funext i
    simp only [cplx]
    exact ((Complex.conj_eq_iff_re).1 (hx i)).symm
  rw [h, sqrtDot_cplx]
  simp

theorem cBlend_real {ι : Type*} [Fintype ι] (a ν : ℝ) {ψ h : ι → ℂ} (hψ : IsRealVec ψ)
    (hh : IsRealVec h) : IsRealVec (cBlend a ν ψ h) := by
  intro i
  simp [cBlend, hψ i, hh i]

theorem cMinimizer_real {ι : Type*} [Fintype ι] (a ν : ℝ) {ψ h : ι → ℂ} (hψ : IsRealVec ψ)
    (hh : IsRealVec h) : IsRealVec (cMinimizer a ν ψ h) := by
  intro i
  have hb := cBlend_real a ν hψ hh
  simp only [cMinimizer, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  rw [sqrtDot_real hb, hb i]

theorem normalize_real {N : ℕ} {v : Fin N → ℂ} (hv : IsRealVec v) :
    IsRealVec (Background.normalize v) := by
  intro i
  simp only [Background.normalize, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
  rw [sqrtDot_real hv, hv i]

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem locSol_real {Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ} (hΨ : ∀ x, IsRealVec (Ψ x))
    (hh : ∀ x, IsRealVec (h x)) (y : CTorus d L N₁ m₁ K) :
    IsRealVec (locSol G a ν Ψ h y) := by
  unfold locSol
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, ite_true]; exact cMinimizer_real _ _ (hΨ y) (hh y)
  · simp only [hy, ite_false]
    exact cMinimizer_real _ _ (hΨ y) (fun _ => by simp)

theorem interp_real {Φ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hΦ : ∀ x, IsRealVec (Φ x))
    (x : CTorus d L N₁ m₁ K) : IsRealVec (interp G Φ x) := by
  intro i
  simp only [interp, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Complex.conj_ofReal, hΦ _ i]

/-- **Reality of the approximate field**: real data give a real `φ₀`. -/
theorem approxField_real {Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ} (hΨ : ∀ x, IsRealVec (Ψ x))
    (hh : ∀ x, IsRealVec (h x)) (x : CTorus d L N₁ m₁ K) :
    IsRealVec (approxField G a ν Ψ h x) := by
  have hl := locSol_real (G := G) (a := a) (ν := ν) hΨ hh
  unfold approxField
  by_cases h1 : x ∈ G.Ω 1
  · by_cases h2 : G.layerIndex x ≤ 1
    · simp only [h1, h2, ite_true]; exact hl x
    · simp only [h1, h2, ite_true, ite_false]
      exact normalize_real (interp_real hl x)
  · by_cases h3 : x ∈ collar G
    · simp only [h1, h3, ite_true, ite_false]; exact hl x
    · simp only [h1, h3, ite_false]; intro i; simp

end ApproxReal

/-! ### Conjugation of `𝒩`, of `δφ(δα)` and of the residual -/

section FixedPoint

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem cj_mulVec_apply {ι κ : Type*} [Fintype κ] (A : Matrix ι κ ℂ) (v : κ → ℂ) (x : ι) :
    cj ((A *ᵥ v) x) = (cjm A *ᵥ fun k => cj (v k)) x := congrFun (cjm_mulVec A v) x

theorem cj_liftOp_mulVec {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℂ)
    (v : ι × Fin N → ℂ) (p : ι × Fin N) :
    cj ((liftOp N A *ᵥ v) p) = (liftOp N (cjm A) *ᵥ fun q => cj (v q)) p := by
  obtain ⟨x, i⟩ := p
  rw [liftOp_mulVec, liftOp_mulVec, cj_mulVec_apply]

theorem residual_real {D : BgData G N} (hD : D.IsReal) {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hφ : ∀ x, IsRealVec (φ₀ x)) (p : G.Ω 1 × Fin N) :
    cj (Background.residual G a ν D φ₀ p) = Background.residual G a ν D φ₀ p := by
  unfold Background.residual
  rw [Pi.sub_apply, map_sub, source_conj D hD, H0_conj]
  have : (fun q : G.Ω 1 × Fin N => cj (φ₀ q.1 q.2)) = fun q => φ₀ q.1 q.2 :=
    funext fun q => hφ q.1 q.2
  rw [this]

theorem gdef_real {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hφ : ∀ x, IsRealVec (φ₀ x))
    (x : G.Ω 1) : cj (gdef G φ₀ x) = gdef G φ₀ x := by
  simp only [gdef, map_sub, map_sum, map_mul, hφ _ _, map_one]

/-- **Conjugation of `𝒩`** for a real operator `H₀`, real `φ₀` and a real source. -/
theorem Nmap_conj {H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ} (hH : cjm H₀ = H₀) (ιU : Bool)
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hφ : ∀ x, IsRealVec (φ₀ x))
    {Fs : G.Ω 1 × Fin N → ℂ} (hF : ∀ p, cj (Fs p) = Fs p) (δφ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) :
    cj (Nmap G H₀ ιU φ₀ Fs δφ x) = Nmap G H₀ ιU φ₀ Fs (fun p => cj (δφ p)) x := by
  unfold Nmap
  have hHe : ∀ y z, cj (H₀ y z) = H₀ y z := fun y z => by
    have := congrFun (congrFun hH y) z; simpa [cjm] using this
  have e1 : ∀ (u : G.Ω 1 × Fin N → ℂ), cj ((commK H₀ (restrictField G φ₀) *ᵥ u) x) =
      (commK H₀ (restrictField G φ₀) *ᵥ fun p => cj (u p)) x := by
    intro u
    rw [commK_mulVec, commK_mulVec, map_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hHe, restrictField, hφ _ _]
  have e2 : cj (Rvec H₀ δφ δφ x) = Rvec H₀ (fun p => cj (δφ p)) (fun p => cj (δφ p)) x := by
    rw [Rvec_eq, Rvec_eq]
    have l1 : ∀ w : G.Ω 1 × Fin N → ℂ, ∀ i,
        cj ((liftOp N H₀ *ᵥ w) (x, i)) = (liftOp N H₀ *ᵥ fun q => cj (w q)) (x, i) := by
      intro w i; rw [cj_liftOp_mulVec, hH]
    simp only [map_sub, map_sum, map_mul, l1]
    congr 2
    rw [cj_mulVec_apply, hH]
    congr 1
    funext y
    simp
  have half : cj (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  have e3 : cj ((H₀ *ᵥ gdef G φ₀) x) = (H₀ *ᵥ gdef G φ₀) x := by
    rw [cj_mulVec_apply, hH]
    congr 1
    funext y
    exact gdef_real hφ y
  have e0 : cj (∑ i, (φ₀ (↑x) i + δφ (x, i)) * Fs (x, i)) =
      ∑ i, (φ₀ (↑x) i + cj (δφ (x, i))) * Fs (x, i) := by
    simp only [map_sum, map_mul, map_add, hφ _ _, hF]
  cases ιU
  · simp only [Bool.false_eq_true, ite_false, map_add, map_sub, map_mul, e0, e1, e2, half,
      map_zero]
  · simp only [ite_true, map_add, map_sub, map_mul, e0, e1, e2, half, e3]

theorem Fsrc_conj {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hφ : ∀ x, IsRealVec (φ₀ x))
    {Fs : G.Ω 1 × Fin N → ℂ} (hF : ∀ p, cj (Fs p) = Fs p) (δα : G.Ω 1 → ℂ) (p : G.Ω 1 × Fin N) :
    cj (Fsrc (G := G) φ₀ Fs δα p) = Fsrc (G := G) φ₀ Fs (fun x => cj (δα x)) p := by
  simp [Fsrc, hF, hφ _ _]

/-- **Conjugation of `δφ(δα)`** at `α₀ = 0`, for a Green family compatible with conjugation. -/
theorem dphi_conj {𝒢 𝒢' : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ}
    (h𝒢 : ∀ α, cjm (𝒢 α) = 𝒢' (fun x => cj (α x))) {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ}
    (hφ : ∀ x, IsRealVec (φ₀ x)) {Fs : G.Ω 1 × Fin N → ℂ} (hF : ∀ p, cj (Fs p) = Fs p)
    (δα : G.Ω 1 → ℂ) (p : G.Ω 1 × Fin N) :
    cj (dphi G 𝒢 (0 : G.Ω 1 → ℂ) φ₀ Fs δα p) =
      dphi G 𝒢' (0 : G.Ω 1 → ℂ) φ₀ Fs (fun x => cj (δα x)) p := by
  unfold dphi
  rw [cj_liftOp_mulVec, h𝒢]
  have e1 : (fun x => cj (((0 : G.Ω 1 → ℂ) + δα) x)) = (0 : G.Ω 1 → ℂ) + fun x => cj (δα x) := by
    funext x; simp
  rw [e1]
  congr 2
  funext q
  exact Fsrc_conj hφ hF δα q

end FixedPoint

/-! ### Reality of the decoupled background field -/

section Bg

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

theorem small_conj {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {α : G.Ω 1 → ℂ} {r : ℝ}
    (h : Small G α r) : Small G (fun x => cj (α x)) r := fun x => by
  rw [RCLike.norm_conj]; exact h x

theorem isRealVec_of_im {x : Fin N → ℂ} (h : ∀ i, (x i).im = 0) : IsRealVec x :=
  fun i => Complex.conj_eq_iff_im.2 (h i)

section Dec2Cover

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem decG2_conj (s : Dec2.DecParams C) (α : H.Ω 1 → ℂ) :
    cjm (Dec2.decG C H a ν s α) =
      Dec2.decG C H a ν (fun P => cj (s P)) (fun x => cj (α x)) := by
  unfold Dec2.decG
  rw [cjm_Gs]
  have : (fun P => cj (Dec2.extS C s P)) = Dec2.extS C (fun P => cj (s P)) := by
    funext P
    unfold Dec2.extS
    split_ifs with h
    · rfl
    · simp
  rw [this]

/-- **Conjugation preserves the system `IsDecBg`** for real data and real parameters. -/
theorem isDecBg2_conj {ρ : ℝ} {s : Dec2.DecParams C}
    {D : BgData H N} (hD : D.IsReal) {φ : H.Ω 1 × Fin N → ℂ} {α : H.Ω 1 → ℂ}
    (h : Dec2.IsDecBg C H a ν ρ s D φ α) :
    Dec2.IsDecBg C H a ν ρ (fun P => cj (s P)) D (fun p => cj (φ p)) (fun x => cj (α x)) := by
  have hΨ : ∀ x, IsRealVec (D.Ψ x) := fun x => isRealVec_of_im fun i => (hD x i).1
  have hh : ∀ x, IsRealVec (D.h x) := fun x => isRealVec_of_im fun i => (hD x i).2
  have hA := approxField_real (G := H) (a := a) (ν := ν) hΨ hh
  have hF := fun p => residual_real (G := H) (a := a) (ν := ν) hD hA p
  have hH0 : cjm (dirichletOperator H a ν (0 : H.Ω 1 → ℂ)) = dirichletOperator H a ν 0 :=
    cjm_dirichlet_zero
  have h𝒢 := fun β => decG2_conj (C := C) (H := H) (a := a) (ν := ν) s β
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨small_conj h1, ?_, ?_⟩
  · unfold Dec2.DecFixed at h2 ⊢
    funext x
    have e := congrFun h2 x
    have := Nmap_conj hH0 true hA hF (dphi H (Dec2.decG C H a ν s) 0 (approxField H a ν D.Ψ D.h)
      (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α) x
    rw [e] at this
    have hd : dphi H (Dec2.decG C H a ν (fun P => cj (s P))) (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
        (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) (fun x => cj (α x)) =
        fun p => cj (dphi H (Dec2.decG C H a ν s) (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
          (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α p) :=
      funext fun p => (dphi_conj h𝒢 hA hF α p).symm
    rw [hd]
    exact this.symm
  · subst h3
    funext p
    simp only [map_add]
    rw [hA p.1 p.2, dphi_conj h𝒢 hA hF α p]

theorem decBg2_real {ρ : ℝ} {s : Dec2.DecParams C} (hs : ∀ P, cj (s P) = s P)
    {D : BgData H N} (hD : D.IsReal) :
    (∀ p, cj (Dec2.decBgField C H a ν ρ s D p) = Dec2.decBgField C H a ν ρ s D p) ∧
      ∀ x, cj (Dec2.decBgMult C H a ν ρ s D x) = Dec2.decBgMult C H a ν ρ s D x := by
  classical
  have hs' : (fun P => cj (s P)) = s := funext hs
  by_cases Hh : ∃! p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ), Dec2.IsDecBg C H a ν ρ s D p.1 p.2
  · have hc := isDecBg2_conj hD Hh.exists.choose_spec
    rw [hs'] at hc
    have e := Hh.unique (y₁ := (fun p => cj (Hh.exists.choose.1 p), fun x => cj (Hh.exists.choose.2 x)))
      hc Hh.exists.choose_spec
    refine ⟨fun p => ?_, fun x => ?_⟩
    · have := congrFun (congrArg Prod.fst e) p
      simpa [Dec2.decBgField, Hh] using this
    · have := congrFun (congrArg Prod.snd e) x
      simpa [Dec2.decBgMult, Hh] using this
  · refine ⟨fun p => ?_, fun x => ?_⟩ <;> simp [Dec2.decBgField, Dec2.decBgMult, Hh]

end Dec2Cover

section OldCover

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Conjugation preserves the system `IsDecBg`** for real data and real parameters. -/
theorem isDecBg_conj {ρ : ℝ} {s : DecParams G}
    {D : BgData G N} (hD : D.IsReal) {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ}
    (h : IsDecBg G a ν ρ s D φ α) :
    IsDecBg G a ν ρ (fun P => cj (s P)) D (fun p => cj (φ p)) (fun x => cj (α x)) := by
  have hΨ : ∀ x, IsRealVec (D.Ψ x) := fun x => isRealVec_of_im fun i => (hD x i).1
  have hh : ∀ x, IsRealVec (D.h x) := fun x => isRealVec_of_im fun i => (hD x i).2
  have hA := approxField_real (G := G) (a := a) (ν := ν) hΨ hh
  have hF := fun p => residual_real (G := G) (a := a) (ν := ν) hD hA p
  have hH0 : cjm (dirichletOperator G a ν (0 : G.Ω 1 → ℂ)) = dirichletOperator G a ν 0 :=
    cjm_dirichlet_zero
  have h𝒢 : ∀ β : G.Ω 1 → ℂ, cjm (decG G a ν s β) = decG G a ν (fun P => cj (s P)) (fun x => cj (β x)) :=
    fun β => decG2_conj (C := coverOf G) (H := G) (a := a) (ν := ν) s β
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨small_conj h1, ?_, ?_⟩
  · unfold DecFixed at h2 ⊢
    funext x
    have e := congrFun h2 x
    have := Nmap_conj hH0 true hA hF (dphi G (decG G a ν s) 0 (approxField G a ν D.Ψ D.h)
      (Background.residual G a ν D (approxField G a ν D.Ψ D.h)) α) x
    rw [e] at this
    have hd : dphi G (decG G a ν (fun P => cj (s P))) (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
        (Background.residual G a ν D (approxField G a ν D.Ψ D.h)) (fun x => cj (α x)) =
        fun p => cj (dphi G (decG G a ν s) (0 : G.Ω 1 → ℂ) (approxField G a ν D.Ψ D.h)
          (Background.residual G a ν D (approxField G a ν D.Ψ D.h)) α p) :=
      funext fun p => (dphi_conj h𝒢 hA hF α p).symm
    rw [hd]
    exact this.symm
  · subst h3
    funext p
    simp only [map_add]
    rw [hA p.1 p.2, dphi_conj h𝒢 hA hF α p]

theorem decBg_real {ρ : ℝ} {s : DecParams G} (hs : ∀ P, cj (s P) = s P)
    {D : BgData G N} (hD : D.IsReal) :
    (∀ p, cj (decBgField G a ν ρ s D p) = decBgField G a ν ρ s D p) ∧
      ∀ x, cj (decBgMult G a ν ρ s D x) = decBgMult G a ν ρ s D x := by
  classical
  have hs' : (fun P => cj (s P)) = s := funext hs
  by_cases Hh : ∃! p : (G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ), IsDecBg G a ν ρ s D p.1 p.2
  · have hc := isDecBg_conj hD Hh.exists.choose_spec
    rw [hs'] at hc
    have e := Hh.unique (y₁ := (fun p => cj (Hh.exists.choose.1 p), fun x => cj (Hh.exists.choose.2 x)))
      hc Hh.exists.choose_spec
    refine ⟨fun p => ?_, fun x => ?_⟩
    · have := congrFun (congrArg Prod.fst e) p
      simpa [decBgField, Hh] using this
    · have := congrFun (congrArg Prod.snd e) x
      simpa [decBgMult, Hh] using this
  · refine ⟨fun p => ?_, fun x => ?_⟩ <;> simp [decBgField, decBgMult, Hh]


end OldCover

end Bg

end Balaban.Localization.DecEquiv
