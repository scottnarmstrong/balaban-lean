/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecoupledBackground
public import Balaban.Localization.Decoupled2Background
public import Balaban.Background.Equivariance
public import Balaban.Background.EquivarianceDomain

/-!
# `O(N)` equivariance of the decoupled background field (LOCALIZATION.md, symmetry clause)

For a complex orthogonal `R` (`Rᵀ R = 1`) acting on the spin index, the approximate field `φ₀`,
the residual `f₀`, the map `𝒩`, the field `δφ(δα)` and the fixed point equation `DecFixed` of
Theorem I-4a all commute with the rotation: the Green family `α ↦ G_s(α)` is a family of scalar
matrices on `Ω₁` and does not see the spin index, so `dphi` is equivariant for every family
(`dphi_rot`).  Consequently the system `IsDecBg` is carried to itself by `(D, φ, α) ↦ (D.rot R,
R φ, α)` (`isDecBg_rot_iff`), and the unique solution is rotated:
`decBgField_rot`, `decBgMult_rot` (for the cover `G` of `Decoupled` and for `Dec2`).
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- The rotation acting on a field `Torus → ℂ^N` pointwise. -/
def rotSite (R : Matrix (Fin N) (Fin N) ℂ) {X : Type*} (φ : X → Fin N → ℂ) : X → Fin N → ℂ :=
  fun x => R *ᵥ φ x

theorem rotSite_apply (R : Matrix (Fin N) (Fin N) ℂ) {X : Type*} (φ : X → Fin N → ℂ) (x : X)
    (i : Fin N) : rotSite R φ x i = ∑ j, R i j * φ x j := rfl

theorem rotFld_site (R : Matrix (Fin N) (Fin N) ℂ) {X : Type*} (φ : X → Fin N → ℂ) :
    (fun p : X × Fin N => rotSite R φ p.1 p.2) =
      rotFld R (fun p : X × Fin N => φ p.1 p.2) := rfl

theorem rotFld_injective {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) :
    Function.Injective (rotFld (ι := ι) R) := fun u w h => by
  rw [← rotFld_rotFld_transpose hR u, h, rotFld_rotFld_transpose hR]

theorem rotFld_add {ι : Type*} (R : Matrix (Fin N) (Fin N) ℂ) (u w : ι × Fin N → ℂ) :
    rotFld R (u + w) = rotFld R u + rotFld R w := by
  funext p; simp [rotFld, mul_add, Finset.sum_add_distrib]

theorem rotFld_smul_fun {ι : Type*} (R : Matrix (Fin N) (Fin N) ℂ) (c : ι → ℂ)
    (φ : ι → Fin N → ℂ) :
    rotFld R (fun p : ι × Fin N => c p.1 * φ p.1 p.2) =
      fun p : ι × Fin N => c p.1 * rotFld R (fun q : ι × Fin N => φ q.1 q.2) p := by
  funext p; simp only [rotFld, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem rotFld_fun_add {ι κ : Type*} (R : Matrix (Fin N) (Fin N) ℂ) (f : ι → κ)
    (φ₀ : κ → Fin N → ℂ) (w : ι × Fin N → ℂ) :
    rotFld R (fun p : ι × Fin N => φ₀ (f p.1) p.2 + w p) =
      fun p => rotSite R φ₀ (f p.1) p.2 + rotFld R w p := by
  funext p
  simp only [rotFld, rotSite, Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]

/-! ### The approximate field and the residual -/

section Approx

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem locSol_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ) (y : CTorus d L N₁ m₁ K) :
    locSol G a ν (rotSite R Ψ) (rotSite R h) y = R *ᵥ locSol G a ν Ψ h y := by
  unfold locSol
  by_cases hy : y ∈ G.Ω 1
  · simp only [hy, ite_true]
    exact cMinimizer_mulVec (a (G.layerIndex y)) (blockMass G ν y) R hR (Ψ y) (h y)
  · simp only [hy, ite_false]
    have := cMinimizer_mulVec (1 : ℝ) 0 R hR (Ψ y) 0
    rwa [Matrix.mulVec_zero] at this

theorem interp_rot (R : Matrix (Fin N) (Fin N) ℂ) (Φ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (x : CTorus d L N₁ m₁ K) : interp G (rotSite R Φ) x = R *ᵥ interp G Φ x := by
  unfold interp rotSite
  rw [Matrix.mulVec_sum]
  exact Finset.sum_congr rfl fun q _ => by rw [Matrix.mulVec_smul]

theorem normalize_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (v : Fin N → ℂ) :
    Background.normalize (R *ᵥ v) = R *ᵥ Background.normalize v := by
  unfold Background.normalize
  rw [sqrtDot_mulVec R hR, Matrix.mulVec_smul]

/-- **Covariance of the approximate field.** -/
theorem approxField_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (Ψ h : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    approxField G a ν (rotSite R Ψ) (rotSite R h) = rotSite R (approxField G a ν Ψ h) := by
  funext x
  have hl : locSol G a ν (rotSite R Ψ) (rotSite R h) = rotSite R (locSol G a ν Ψ h) :=
    funext fun y => locSol_rot hR Ψ h y
  unfold approxField
  simp only [hl]
  show _ = R *ᵥ _
  by_cases h1 : x ∈ G.Ω 1
  · by_cases h2 : G.layerIndex x ≤ 1
    · simp only [h1, h2, ite_true]; exact rfl
    · simp only [h1, h2, ite_true, ite_false]
      show Background.normalize (interp G (rotSite R (locSol G a ν Ψ h)) x) = _
      rw [interp_rot, normalize_rot hR]
  · by_cases h3 : x ∈ collar G
    · simp only [h1, h3, ite_true, ite_false]; exact rfl
    · simp [h1, h3]

/-- **Covariance of the residual.** -/
theorem residual_rot {R : Matrix (Fin N) (Fin N) ℂ} (D : BgData G N)
    (φ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    Background.residual G a ν (D.rot R) (rotSite R φ) = rotFld R (Background.residual G a ν D φ) := by
  unfold Background.residual
  rw [source_rot]
  have e : (fun p : G.Ω 1 × Fin N => rotSite R φ (p.1 : CTorus d L N₁ m₁ K) p.2) =
      rotFld R (fun p : G.Ω 1 × Fin N => φ (p.1 : CTorus d L N₁ m₁ K) p.2) := rfl
  rw [e, rotFld_liftOp]
  funext p; simp [rotFld, Finset.sum_sub_distrib, mul_sub]

end Approx

/-! ### The map `𝒩` and the field `δφ(δα)` -/

section Nmap

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

theorem gdef_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (φ : CTorus d L N₁ m₁ K → Fin N → ℂ) : gdef G (rotSite R φ) = gdef G φ := by
  funext x
  unfold gdef
  show ∑ i, (R *ᵥ φ x) i * (R *ᵥ φ x) i - 1 = _
  rw [bilin_vec hR]

theorem commK_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (φ : CTorus d L N₁ m₁ K → Fin N → ℂ) (s : G.Ω 1 × Fin N → ℂ) :
    commK H₀ (restrictField G (rotSite R φ)) *ᵥ rotFld R s = commK H₀ (restrictField G φ) *ᵥ s := by
  funext x
  rw [commK_mulVec, commK_mulVec]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h := bilin_vec hR (fun i => φ x i - φ y i) (fun i => s (y, i))
  have e1 : ∀ i, restrictField G (rotSite R φ) x i - restrictField G (rotSite R φ) y i =
      (R *ᵥ fun i => φ x i - φ y i) i := by
    intro i; simp only [restrictField, rotSite, Matrix.mulVec, dotProduct, mul_sub,
      Finset.sum_sub_distrib]
  have e2 : ∀ i, rotFld R s (y, i) = (R *ᵥ fun i => s (y, i)) i := fun i => rfl
  simp only [mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [e1, e2, restrictField] at *
  exact h

theorem Rvec_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (v w : G.Ω 1 × Fin N → ℂ) : Rvec H₀ (rotFld R v) (rotFld R w) = Rvec H₀ v w := by
  funext x
  rw [Rvec_eq, Rvec_eq, rotFld_liftOp, rotFld_liftOp]
  have h1 : (fun y : G.Ω 1 => ∑ i, rotFld R v (y, i) * rotFld R w (y, i)) =
      fun y => ∑ i, v (y, i) * w (y, i) := funext fun y => rotFld_bilin hR v w y
  rw [h1, rotFld_bilin hR v _ x, rotFld_bilin hR w _ x]

/-- **Covariance of `𝒩`.** -/
theorem Nmap_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (ιU : Bool) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) :
    Nmap G H₀ ιU (rotSite R φ₀) (rotFld R Fs) (rotFld R δφ) = Nmap G H₀ ιU φ₀ Fs δφ := by
  funext x
  unfold Nmap
  rw [commK_rot hR, Rvec_rot hR, gdef_rot hR]
  congr 3
  have := rotFld_bilin hR (fun p : G.Ω 1 × Fin N => φ₀ p.1 p.2 + δφ p) Fs x
  rw [← this]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  have e : (fun p : G.Ω 1 × Fin N => φ₀ p.1 p.2 + δφ p) =
      (fun p : G.Ω 1 × Fin N => φ₀ p.1 p.2) + δφ := rfl
  rw [e, rotFld_add]
  rfl

theorem Fsrc_rot (R : Matrix (Fin N) (Fin N) ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    Fsrc (G := G) (rotSite R φ₀) (rotFld R Fs) δα = rotFld R (Fsrc (G := G) φ₀ Fs δα) := by
  funext p
  simp only [Fsrc, rotFld, rotSite, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
    Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **Covariance of `δφ(δα)`**, for every family of scalar Green matrices. -/
theorem dphi_rot (R : Matrix (Fin N) (Fin N) ℂ) (𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ)
    (α₀ : G.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ)
    (δα : G.Ω 1 → ℂ) :
    dphi G 𝒢 α₀ (rotSite R φ₀) (rotFld R Fs) δα = rotFld R (dphi G 𝒢 α₀ φ₀ Fs δα) := by
  unfold dphi
  rw [Fsrc_rot, rotFld_liftOp]

end Nmap

/-- **Covariance of the perturbation source** `F_s = Q* a δΨ + 𝔟(δΨ) + f₁`. -/
theorem pertSource_rot {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (R : Matrix (Fin N) (Fin N) ℂ)
    (a : ℕ → ℝ) (δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : H.Ω 1 × Fin N → ℂ) :
    pertSource H a (rotSite R δΨ) (rotFld R f₁) = rotFld R (pertSource H a δΨ f₁) := by
  funext p
  simp only [pertSource, qStar, boundaryTerm, rotFld, rotSite, Matrix.mulVec, dotProduct,
    Finset.mul_sum, mul_add, Finset.sum_add_distrib, Pi.add_apply]
  refine congrArg₂ _ (congrArg₂ _ (Finset.sum_congr rfl fun i _ => by ring) (congrArg₂ _ ?_ ?_))
    rfl <;>
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun μ _ => ?_
    split_ifs <;> simp

/-! ### The fixed point system and the decoupled background field -/

section Bg

/-- Transport of a chosen unique solution along the rotation of fields. -/
theorem choose_rot {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    {P Q : (ι × Fin N → ℂ) × (ι → ℂ) → Prop}
    (hPQ : ∀ s, P s ↔ Q (rotFld R s.1, s.2)) :
    (open Classical in
      if H : ∃! s, Q s then H.exists.choose.1 else 0) =
      rotFld R (open Classical in if H : ∃! s, P s then H.exists.choose.1 else 0) ∧
    (open Classical in
      if H : ∃! s, Q s then H.exists.choose.2 else 0) =
      (open Classical in if H : ∃! s, P s then H.exists.choose.2 else 0) := by
  classical
  let e : ((ι × Fin N → ℂ) × (ι → ℂ)) ≃ ((ι × Fin N → ℂ) × (ι → ℂ)) :=
    (rotEquiv hR).prodCongr (Equiv.refl _)
  have hPQ' : ∀ s, P s ↔ Q (e s) := hPQ
  have h0 : rotFld R (0 : ι × Fin N → ℂ) = 0 := by funext p; simp [rotFld]
  constructor
  · have := dite_existsUnique_equiv e (P := P) (Q := Q) hPQ' (fun s => rotFld R s.1) (fun s => s.1)
      (fun s => rfl) (rotFld R 0)
    rw [h0] at this
    rw [← this]
    split_ifs <;> simp [h0]
  · have := dite_existsUnique_equiv e (P := P) (Q := Q) hPQ' (fun s => s.2) (fun s => s.2)
      (fun s => rfl) 0
    rw [← this]

theorem rotFld_eq_iff {ι : Type*} {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (u w : ι × Fin N → ℂ) : rotFld R u = rotFld R w ↔ u = w :=
  (rotFld_injective hR).eq_iff

section OldCover

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem decFixed_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (s : DecParams G)
    (ιU : Bool) (α₀ : G.Ω 1 → ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ)
    (δα : G.Ω 1 → ℂ) :
    DecFixed G a ν s ιU α₀ (rotSite R φ₀) (rotFld R Fs) δα ↔ DecFixed G a ν s ιU α₀ φ₀ Fs δα := by
  unfold DecFixed
  rw [dphi_rot, Nmap_rot hR]

/-- **`IsDecBg` is carried to itself by the rotation** of the datum and of the field. -/
theorem isDecBg_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (ρ : ℝ)
    (s : DecParams G) (D : BgData G N) (φ : G.Ω 1 × Fin N → ℂ) (α : G.Ω 1 → ℂ) :
    IsDecBg G a ν ρ s (D.rot R) (rotFld R φ) α ↔ IsDecBg G a ν ρ s D φ α := by
  have hA : approxField G a ν (D.rot R).Ψ (D.rot R).h =
      rotSite R (approxField G a ν D.Ψ D.h) := approxField_rot hR D.Ψ D.h
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hA, residual_rot] at h2 h3
    refine ⟨h1, (decFixed_rot_iff hR _ _ _ _ _ _).1 h2, ?_⟩
    apply (rotFld_injective hR)
    rw [h3, rotFld_fun_add, dphi_rot]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [hA, residual_rot]; exact (decFixed_rot_iff hR _ _ _ _ _ _).2 h2
    · rw [hA, residual_rot, dphi_rot, h3, rotFld_fun_add]

theorem decBg_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (ρ : ℝ) (s : DecParams G)
    (D : BgData G N) :
    decBgField G a ν ρ s (D.rot R) = rotFld R (decBgField G a ν ρ s D) ∧
      decBgMult G a ν ρ s (D.rot R) = decBgMult G a ν ρ s D :=
  choose_rot hR (P := fun p => IsDecBg G a ν ρ s D p.1 p.2)
    (Q := fun p => IsDecBg G a ν ρ s (D.rot R) p.1 p.2)
    (fun p => (isDecBg_rot_iff hR ρ s D p.1 p.2).symm)

end OldCover

section Dec2Cover

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}

theorem dec2Fixed_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (s : Dec2.DecParams C) (ιU : Bool) (α₀ : H.Ω 1 → ℂ)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) :
    Dec2.DecFixed C H a ν s ιU α₀ (rotSite R φ₀) (rotFld R Fs) δα ↔
      Dec2.DecFixed C H a ν s ιU α₀ φ₀ Fs δα := by
  unfold Dec2.DecFixed
  rw [dphi_rot, Nmap_rot hR]

/-- **`IsDecBg` of a general cover and operator generating set is carried to itself by the
rotation.** -/
theorem isDecBg2_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (ρ : ℝ)
    (s : Dec2.DecParams C) (D : BgData H N) (φ : H.Ω 1 × Fin N → ℂ) (α : H.Ω 1 → ℂ) :
    Dec2.IsDecBg C H a ν ρ s (D.rot R) (rotFld R φ) α ↔ Dec2.IsDecBg C H a ν ρ s D φ α := by
  have hA : approxField H a ν (D.rot R).Ψ (D.rot R).h =
      rotSite R (approxField H a ν D.Ψ D.h) := approxField_rot hR D.Ψ D.h
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hA, residual_rot] at h2 h3
    refine ⟨h1, (dec2Fixed_rot_iff hR _ _ _ _ _ _).1 h2, ?_⟩
    apply (rotFld_injective hR)
    rw [h3, rotFld_fun_add, dphi_rot]
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [hA, residual_rot]; exact (dec2Fixed_rot_iff hR _ _ _ _ _ _).2 h2
    · rw [hA, residual_rot, dphi_rot, h3, rotFld_fun_add]

theorem decBg2_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (ρ : ℝ)
    (s : Dec2.DecParams C) (D : BgData H N) :
    Dec2.decBgField C H a ν ρ s (D.rot R) = rotFld R (Dec2.decBgField C H a ν ρ s D) ∧
      Dec2.decBgMult C H a ν ρ s (D.rot R) = Dec2.decBgMult C H a ν ρ s D :=
  choose_rot hR (P := fun p => Dec2.IsDecBg C H a ν ρ s D p.1 p.2)
    (Q := fun p => Dec2.IsDecBg C H a ν ρ s (D.rot R) p.1 p.2)
    (fun p => (isDecBg2_rot_iff hR ρ s D p.1 p.2).symm)

/-- **`O(N)` covariance of the fluctuation problem of Theorem I-4a** (cover `C`, operator `H`): the
fixed point equation `δα = 𝒩_s(δα)` with the data `(α₀, φ₀, δΨ, f₁)` is equivalent to the one for the
rotated data `(α₀, R φ₀, R δΨ, R f₁)`; the multiplier `α` is a scalar and does not rotate. -/
theorem fluctFixed_rot_iff {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (s : Dec2.DecParams C) (ιU : Bool) (α₀ : H.Ω 1 → ℂ) (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (f₁ : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) :
    Dec2.DecFixed C H a ν s ιU α₀ (rotSite R φ₀)
        (pertSource H a (rotSite R δΨ) (rotFld R f₁)) δα ↔
      Dec2.DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα := by
  rw [pertSource_rot]; exact dec2Fixed_rot_iff hR s ιU α₀ φ₀ _ δα

/-- The fluctuation field `δφ(δα)` rotates with the data. -/
theorem fluctField_rot (R : Matrix (Fin N) (Fin N) ℂ) (s : Dec2.DecParams C)
    (α₀ : H.Ω 1 → ℂ) (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : H.Ω 1 × Fin N → ℂ)
    (δα : H.Ω 1 → ℂ) :
    dphi H (Dec2.decG C H a ν s) α₀ (rotSite R φ₀) (pertSource H a (rotSite R δΨ) (rotFld R f₁)) δα =
      rotFld R (dphi H (Dec2.decG C H a ν s) α₀ φ₀ (pertSource H a δΨ f₁) δα) := by
  rw [pertSource_rot, dphi_rot]

end Dec2Cover

end Bg

end Balaban.Localization.DecEquiv
