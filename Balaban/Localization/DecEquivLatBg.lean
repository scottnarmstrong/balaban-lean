/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.DecEquivLat
public import Balaban.Localization.DecEquivRot

/-!
# Lattice-symmetry covariance of the decoupled background field (LOCALIZATION.md, symmetry clause)

For a lattice symmetry `S : LatSymm G G σ` compatible with the blocks (`BlockSymm`: `σ` maps the
bumps of the interpolation to bumps) and with the cover (`CoverSymm`), the approximate field, the
residual, the map `𝒩`, the field `δφ(δα)`, the system `IsDecBg` and the decoupled background field
and multiplier are transported: `φ_{k}(σ D, s ∘ τ⁻¹) = φ_k(D, s) ∘ σ⁻¹`.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Compatibility of a lattice symmetry with the blocks of the interpolation.**  The symmetry
maps the bumps `b_B` of the blocks `B` to bumps: it induces a permutation `τ` of the block indices
`(n, y₀)` (the base point of the image of a block is the base point of the block containing the
image of `y₀`; for a reflection it is the opposite corner). -/
structure BlockSymm (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (σ : Equiv.Perm (CTorus d L N₁ m₁ K)) where
  /-- The action on the block indices. -/
  τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)
  idx : ∀ q, τ q ∈ blockIdx G ↔ q ∈ blockIdx G
  layer : ∀ q, (τ q).1 = q.1
  bump : ∀ q x, Background.bump (τ q).1 (τ q).2 (σ x) = Background.bump q.1 q.2 x
  base : ∀ q ∈ blockIdx G,
    jBlock d L (N₁ * L ^ m₁) K q.1 (σ.symm (τ q).2) = jBlock d L (N₁ * L ^ m₁) K q.1 q.2

/-- The identity is compatible with the blocks of every generating set. -/
def BlockSymm.refl (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    BlockSymm G (1 : Equiv.Perm (CTorus d L N₁ m₁ K)) where
  τ := 1
  idx := fun _ => Iff.rfl
  layer := fun _ => rfl
  bump := fun _ _ => rfl
  base := fun _ _ => rfl

theorem blockSymm_nonempty (G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ) :
    Nonempty (BlockSymm G (1 : Equiv.Perm (CTorus d L N₁ m₁ K))) := ⟨BlockSymm.refl G⟩

section Approx

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (B : BlockSymm G σ)

include B

theorem BlockSymm.denom_eq (x : CTorus d L N₁ m₁ K) : denom G (σ x) = denom G x := by
  unfold denom
  refine (Finset.sum_equiv B.τ (fun q => (B.idx q).symm) fun q _ => ?_).symm
  exact (B.bump q x).symm

theorem BlockSymm.weight_eq (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) :
    weight G (B.τ q) (σ x) = weight G q x := by
  unfold weight
  rw [B.bump, B.denom_eq]

variable (S : LatSymm G G σ)

omit B in
theorem locSol_sym (D : BgData G N) (y : CTorus d L N₁ m₁ K) :
    locSol G a ν (S.sym D).Ψ (S.sym D).h (σ y) = locSol G a ν D.Ψ D.h y := by
  unfold locSol
  have hs : (S.sym D).Ψ (σ y) = D.Ψ y := by simp [LatSymm.sym]
  have hh : (S.sym D).h (σ y) = D.h y := by simp [LatSymm.sym]
  by_cases hy : y ∈ G.Ω 1
  · have hy' : σ y ∈ G.Ω 1 := (S.mem_Ω1 y).2 hy
    simp only [hy, hy', ite_true, hs, hh, blockMass, S.layerIndex_eq]
  · have hy' : σ y ∉ G.Ω 1 := fun h => hy ((S.mem_Ω1 y).1 h)
    simp only [hy, hy', ite_false, hs]

omit B in
theorem locSol_block (D : BgData G N) {n : ℕ} (h1 : 1 ≤ n) (hk : n ≤ K) {y y' : CTorus d L N₁ m₁ K}
    (hy : y ∈ G.layer n) (hy' : y' ∈ G.layer n)
    (hb : jBlock d L (N₁ * L ^ m₁) K n y' = jBlock d L (N₁ * L ^ m₁) K n y) :
    locSol G a ν D.Ψ D.h y' = locSol G a ν D.Ψ D.h y := by
  unfold locSol
  have hΩ : ∀ z, z ∈ G.layer n → z ∈ G.Ω 1 := fun z hz =>
    G.Ω_antitone (le_refl 1) h1 (by omega) ((GeneratingSet.mem_layer G).1 hz).1
  have hli : ∀ z, z ∈ G.layer n → G.layerIndex z = n := fun z hz => G.layerIndex_eq h1 hk hz
  have hbl : y' ∈ G.blk n y := GeneratingSet.mem_blk.2 hb
  simp only [hΩ y hy, hΩ y' hy', ite_true, blockMass, hli y hy, hli y' hy',
    D.Ψ_layerConst n h1 hk y hy y' hbl, D.h_layerConst n h1 hk y hy y' hbl]

theorem interp_sym (Φ Φ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hΦ : ∀ q ∈ blockIdx G, Φ' (B.τ q).2 = Φ q.2) (x : CTorus d L N₁ m₁ K) :
    interp G Φ' (σ x) = interp G Φ x := by
  unfold interp
  refine (Finset.sum_equiv B.τ (fun q => (B.idx q).symm) fun q hq => ?_).symm
  rw [B.weight_eq, hΦ q hq]

/-- **Lattice-symmetry covariance of the approximate field** `φ₀`. -/
theorem approxField_sym (D : BgData G N) (x : CTorus d L N₁ m₁ K) :
    approxField G a ν (S.sym D).Ψ (S.sym D).h (σ x) = approxField G a ν D.Ψ D.h x := by
  have hl : ∀ y, locSol G a ν (S.sym D).Ψ (S.sym D).h (σ y) = locSol G a ν D.Ψ D.h y :=
    fun y => locSol_sym S D y
  have hi : interp G (locSol G a ν (S.sym D).Ψ (S.sym D).h) (σ x) =
      interp G (locSol G a ν D.Ψ D.h) x := by
    refine interp_sym B _ _ (fun q hq => ?_) x
    obtain ⟨⟨h1, hk⟩, hqℓ, -⟩ := (mem_blockIdx G).1 hq
    obtain ⟨-, hqℓ', -⟩ := (mem_blockIdx G).1 ((B.idx q).2 hq)
    rw [B.layer] at hqℓ'
    have hy' : σ.symm (B.τ q).2 ∈ G.layer q.1 := by
      rw [← S.mem_layer h1 hk]; simpa using hqℓ'
    have := hl (σ.symm (B.τ q).2)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact locSol_block D h1 hk hqℓ hy' (B.base q hq)
  unfold approxField
  by_cases h1 : x ∈ G.Ω 1
  · have h1' : σ x ∈ G.Ω 1 := (S.mem_Ω1 x).2 h1
    by_cases h2 : G.layerIndex x ≤ 1
    · have h2' : G.layerIndex (σ x) ≤ 1 := by rwa [S.layerIndex_eq]
      simp only [h1, h1', h2, h2', ite_true, hl]
    · have h2' : ¬ G.layerIndex (σ x) ≤ 1 := by rwa [S.layerIndex_eq]
      simp only [h1, h1', h2, h2', ite_true, ite_false, hi]
  · have h1' : σ x ∉ G.Ω 1 := fun h => h1 ((S.mem_Ω1 x).1 h)
    by_cases h3 : x ∈ collar G
    · have h3' : σ x ∈ collar G := (S.mem_collar x).2 h3
      simp only [h1, h1', h3, h3', ite_true, ite_false, hl]
    · have h3' : σ x ∉ collar G := fun h => h3 ((S.mem_collar x).1 h)
      simp [h1, h1', h3, h3']

end Approx

section Fixed

variable {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm G G σ)

theorem coe_Ω1Equiv_symm (y : G.Ω 1) :
    ((S.Ω1Equiv.symm y : G.Ω 1) : CTorus d L N₁ m₁ K) = σ.symm (y : CTorus d L N₁ m₁ K) := by
  have h := S.coe_Ω1Equiv (S.Ω1Equiv.symm y)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

/-- The transported site field `φ₀ ∘ σ⁻¹`. -/
def symSite (σ : Equiv.Perm (CTorus d L N₁ m₁ K)) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    CTorus d L N₁ m₁ K → Fin N → ℂ := fun y => φ₀ (σ.symm y)

theorem mulVec_rm (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v : G.Ω 1 → ℂ) (x : G.Ω 1) :
    (rm S.Ω1Equiv A *ᵥ S.mul v) (S.Ω1Equiv x) = (A *ᵥ v) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp S.Ω1Equiv]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [rm_apply, LatSymm.mul_apply]

theorem liftOp_rm (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) (i : Fin N) :
    (liftOp N (rm S.Ω1Equiv A) *ᵥ S.fld φ) (S.Ω1Equiv x, i) = (liftOp N A *ᵥ φ) (x, i) := by
  rw [liftOp_mulVec, liftOp_mulVec]
  have : (fun b => S.fld φ (b, i)) = S.mul (fun b => φ (b, i)) := by
    funext b; simp [LatSymm.fld, LatSymm.mul]
  rw [this]
  exact mulVec_rm S A _ x

theorem residual_sym (D : BgData G N) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : G.Ω 1)
    (i : Fin N) :
    Background.residual G a ν (S.sym D) (symSite σ φ₀) (S.Ω1Equiv x, i) =
      Background.residual G a ν D φ₀ (x, i) := by
  unfold Background.residual
  have hφ : (fun p : G.Ω 1 × Fin N => symSite σ φ₀ (p.1 : CTorus d L N₁ m₁ K) p.2) =
      S.fld (fun p : G.Ω 1 × Fin N => φ₀ (p.1 : CTorus d L N₁ m₁ K) p.2) := by
    funext p; simp [symSite, LatSymm.fld, coe_Ω1Equiv_symm S]
  rw [Pi.sub_apply, Pi.sub_apply, hφ, S.source_sym]
  have := S.liftOp_sym a ν (0 : G.Ω 1 → ℂ) (fun p : G.Ω 1 × Fin N => φ₀ (p.1 : CTorus d L N₁ m₁ K) p.2) x i
  have h0 : S.mul (0 : G.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  rw [h0] at this
  rw [this]

theorem gdef_sym (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    gdef G (symSite σ φ₀) = S.mul (gdef G φ₀) := by
  funext y
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  simp [gdef, symSite, LatSymm.mul]

theorem commK_sym (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (δφ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    (commK (rm S.Ω1Equiv H₀) (restrictField G (symSite σ φ₀)) *ᵥ S.fld δφ) (S.Ω1Equiv x) =
      (commK H₀ (restrictField G φ₀) *ᵥ δφ) x := by
  rw [commK_mulVec, commK_mulVec, ← Equiv.sum_comp S.Ω1Equiv]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  simp [restrictField, symSite, rm_apply]

theorem Rvec_sym (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v w : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Rvec (rm S.Ω1Equiv H₀) (S.fld v) (S.fld w) (S.Ω1Equiv x) = Rvec H₀ v w x := by
  rw [Rvec_eq, Rvec_eq]
  have e1 : (fun y : G.Ω 1 => ∑ i, S.fld v (y, i) * S.fld w (y, i)) =
      S.mul (fun y => ∑ i, v (y, i) * w (y, i)) := by
    funext y; simp [LatSymm.fld, LatSymm.mul]
  rw [e1, mulVec_rm S]
  simp only [LatSymm.fld_apply, liftOp_rm S]

theorem Nmap_sym (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Nmap G (rm S.Ω1Equiv H₀) ιU (symSite σ φ₀) (S.fld Fs) (S.fld δφ) (S.Ω1Equiv x) =
      Nmap G H₀ ιU φ₀ Fs δφ x := by
  unfold Nmap
  rw [commK_sym S, Rvec_sym S, gdef_sym S, mulVec_rm S]
  simp [symSite, LatSymm.fld]

theorem Fsrc_sym (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ)
    (δα : G.Ω 1 → ℂ) :
    Fsrc (G := G) (symSite σ φ₀) (S.fld Fs) (S.mul δα) = S.fld (Fsrc (G := G) φ₀ Fs δα) := by
  funext p
  simp [Fsrc, symSite, LatSymm.fld, LatSymm.mul, coe_Ω1Equiv_symm S]

/-- **Lattice-symmetry covariance of `δφ(δα)`**, for a family of Green matrices with
`𝒢' (σ α) = σ 𝒢 (α) σ⁻¹`. -/
theorem dphi_sym {𝒢 𝒢' : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ}
    (h𝒢 : ∀ α, 𝒢' (S.mul α) = rm S.Ω1Equiv (𝒢 α)) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    dphi G 𝒢' (0 : G.Ω 1 → ℂ) (symSite σ φ₀) (S.fld Fs) (S.mul δα) =
      S.fld (dphi G 𝒢 (0 : G.Ω 1 → ℂ) φ₀ Fs δα) := by
  funext ⟨y, i⟩
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  unfold dphi
  have h0 : (0 : G.Ω 1 → ℂ) + S.mul δα = S.mul ((0 : G.Ω 1 → ℂ) + δα) := by
    funext z; simp [LatSymm.mul]
  rw [h0, h𝒢, Fsrc_sym S, liftOp_rm S]
  simp [LatSymm.fld]

end Fixed

section Bg

variable {C : DecCover d L N₁ m₁ K} {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm H H σ) (CS : CoverSymm C σ)

theorem decG2_sym (s : Dec2.DecParams C) (β : H.Ω 1 → ℂ) :
    Dec2.decG C H a ν (CS.par s) (S.mul β) = rm S.Ω1Equiv (Dec2.decG C H a ν s β) :=
  (rm_Gs S CS a ν β s).symm

theorem dec2Fixed_sym_iff (s : Dec2.DecParams C) (ιU : Bool)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) :
    Dec2.DecFixed C H a ν (CS.par s) ιU 0 (symSite σ φ₀) (S.fld Fs) (S.mul δα) ↔
      Dec2.DecFixed C H a ν s ιU 0 φ₀ Fs δα := by
  unfold Dec2.DecFixed
  have h0 : S.mul (0 : H.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  have hH : dirichletOperator H a ν (0 : H.Ω 1 → ℂ) =
      rm S.Ω1Equiv (dirichletOperator H a ν (0 : H.Ω 1 → ℂ)) := by
    rw [rm_dirichlet S, h0]
  conv_lhs => rw [hH]
  rw [dphi_sym S (decG2_sym S CS s) φ₀ Fs δα]
  constructor
  · intro h
    funext x
    have := congrFun h (S.Ω1Equiv x)
    rw [Nmap_sym S, LatSymm.mul_apply] at this
    exact this
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    rw [Nmap_sym S, LatSymm.mul_apply]
    exact congrFun h x

variable (B : BlockSymm H σ)

include B in
theorem approxField_symSite (D : BgData H N) :
    approxField H a ν (S.sym D).Ψ (S.sym D).h = symSite σ (approxField H a ν D.Ψ D.h) := by
  funext y
  obtain ⟨x, rfl⟩ := σ.surjective y
  rw [approxField_sym B S D x]
  simp [symSite]

theorem residual_symField (D : BgData H N) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    Background.residual H a ν (S.sym D) (symSite σ φ₀) =
      S.fld (Background.residual H a ν D φ₀) := by
  funext ⟨y, i⟩
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  rw [residual_sym S]
  simp [LatSymm.fld]

include B in
/-- **`IsDecBg` is carried to itself by a lattice symmetry**: the datum, field and multiplier are
transported by `σ`, the decoupling parameters by `τ`. -/
theorem isDecBg2_sym_iff (ρ : ℝ) (s : Dec2.DecParams C) (D : BgData H N) (φ : H.Ω 1 × Fin N → ℂ)
    (α : H.Ω 1 → ℂ) :
    Dec2.IsDecBg C H a ν ρ (CS.par s) (S.sym D) (S.fld φ) (S.mul α) ↔
      Dec2.IsDecBg C H a ν ρ s D φ α := by
  have hA := approxField_symSite S B (a := a) (ν := ν) D
  have hr := residual_symField S (a := a) (ν := ν) D (approxField H a ν D.Ψ D.h)
  have hsm : Small H (S.mul α) ρ ↔ Small H α ρ := by
    refine ⟨fun h x => ?_, fun h y => ?_⟩
    · have := h (S.Ω1Equiv x)
      simpa [S.spacing_eq] using this
    · obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
      simpa [S.spacing_eq] using h x
  have hd := dphi_sym S (decG2_sym S CS s (a := a) (ν := ν)) (approxField H a ν D.Ψ D.h)
    (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hA, hr] at h2 h3
    refine ⟨hsm.1 h1, (dec2Fixed_sym_iff S CS s true _ _ _).1 h2, ?_⟩
    rw [hd] at h3
    funext ⟨y, i⟩
    have := congrFun h3 (S.Ω1Equiv y, i)
    simpa [LatSymm.fld, symSite, coe_Ω1Equiv_symm S] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hsm.2 h1, ?_, ?_⟩
    · rw [hA, hr]; exact (dec2Fixed_sym_iff S CS s true _ _ _).2 h2
    · rw [hA, hr, hd]
      funext ⟨y, i⟩
      obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
      have := congrFun h3 (x, i)
      simpa [LatSymm.fld, symSite, coe_Ω1Equiv_symm S] using this

include B in
/-- **Lattice-symmetry covariance of the decoupled background field and multiplier** (cover `C`,
operator generating set `H`). -/
theorem decBg2_sym (ρ : ℝ) (s : Dec2.DecParams C) (D : BgData H N) :
    Dec2.decBgField C H a ν ρ (CS.par s) (S.sym D) = S.fld (Dec2.decBgField C H a ν ρ s D) ∧
      Dec2.decBgMult C H a ν ρ (CS.par s) (S.sym D) = S.mul (Dec2.decBgMult C H a ν ρ s D) := by
  classical
  have h0 : S.fld (0 : H.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [LatSymm.fld]
  have h0' : S.mul (0 : H.Ω 1 → ℂ) = 0 := rfl
  have hPQ : ∀ p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
      Dec2.IsDecBg C H a ν ρ s D p.1 p.2 ↔
        Dec2.IsDecBg C H a ν ρ (CS.par s) (S.sym D)
          ((S.fldEquiv.prodCongr S.mulEquiv) p).1 ((S.fldEquiv.prodCongr S.mulEquiv) p).2 :=
    fun p => (isDecBg2_sym_iff S CS B ρ s D p.1 p.2).symm
  constructor
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun p => Dec2.IsDecBg C H a ν ρ s D p.1 p.2)
      (Q := fun p => Dec2.IsDecBg C H a ν ρ (CS.par s) (S.sym D) p.1 p.2) hPQ
      (fun p => S.fld p.1) (fun p => p.1) (fun p => rfl) (S.fld 0)
    rw [h0] at this
    unfold Dec2.decBgField
    rw [← this]
    split_ifs <;> simp [h0]
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun p => Dec2.IsDecBg C H a ν ρ s D p.1 p.2)
      (Q := fun p => Dec2.IsDecBg C H a ν ρ (CS.par s) (S.sym D) p.1 p.2) hPQ
      (fun p => S.mul p.2) (fun p => p.2) (fun p => rfl) (S.mul 0)
    rw [h0'] at this
    unfold Dec2.decBgMult
    rw [← this]
    split_ifs <;> simp [h0']

end Bg

section OldCover

variable {H : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm H H σ) (CS : CoverSymm (coverOf H) σ)
  (B : BlockSymm H σ)

theorem decFixed_sym_iff (s : DecParams H) (ιU : Bool)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) :
    DecFixed H a ν (CS.par s) ιU 0 (symSite σ φ₀) (S.fld Fs) (S.mul δα) ↔
      DecFixed H a ν s ιU 0 φ₀ Fs δα := by
  unfold DecFixed
  have h0 : S.mul (0 : H.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  have hH : dirichletOperator H a ν (0 : H.Ω 1 → ℂ) =
      rm S.Ω1Equiv (dirichletOperator H a ν (0 : H.Ω 1 → ℂ)) := by
    rw [rm_dirichlet S, h0]
  have hG : ∀ β : H.Ω 1 → ℂ, decG H a ν (CS.par s) (S.mul β) = rm S.Ω1Equiv (decG H a ν s β) :=
    fun β => decG2_sym S CS s (a := a) (ν := ν) β
  conv_lhs => rw [hH]
  rw [dphi_sym S hG φ₀ Fs δα]
  constructor
  · intro h
    funext x
    have := congrFun h (S.Ω1Equiv x)
    rw [Nmap_sym S, LatSymm.mul_apply] at this
    exact this
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    rw [Nmap_sym S, LatSymm.mul_apply]
    exact congrFun h x


include B in
/-- **`IsDecBg` is carried to itself by a lattice symmetry**: the datum, field and multiplier are
transported by `σ`, the decoupling parameters by `τ`. -/
theorem isDecBg_sym_iff (ρ : ℝ) (s : DecParams H) (D : BgData H N) (φ : H.Ω 1 × Fin N → ℂ)
    (α : H.Ω 1 → ℂ) :
    IsDecBg H a ν ρ (CS.par s) (S.sym D) (S.fld φ) (S.mul α) ↔
      IsDecBg H a ν ρ s D φ α := by
  have hA := approxField_symSite S B (a := a) (ν := ν) D
  have hr := residual_symField S (a := a) (ν := ν) D (approxField H a ν D.Ψ D.h)
  have hsm : Small H (S.mul α) ρ ↔ Small H α ρ := by
    refine ⟨fun h x => ?_, fun h y => ?_⟩
    · have := h (S.Ω1Equiv x)
      simpa [S.spacing_eq] using this
    · obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
      simpa [S.spacing_eq] using h x
  have hG : ∀ β : H.Ω 1 → ℂ, decG H a ν (CS.par s) (S.mul β) = rm S.Ω1Equiv (decG H a ν s β) :=
    fun β => decG2_sym S CS s (a := a) (ν := ν) β
  have hd := dphi_sym S hG (approxField H a ν D.Ψ D.h)
    (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hA, hr] at h2 h3
    refine ⟨hsm.1 h1, (decFixed_sym_iff S CS s true _ _ _).1 h2, ?_⟩
    rw [hd] at h3
    funext ⟨y, i⟩
    have := congrFun h3 (S.Ω1Equiv y, i)
    simpa [LatSymm.fld, symSite, coe_Ω1Equiv_symm S] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hsm.2 h1, ?_, ?_⟩
    · rw [hA, hr]; exact (decFixed_sym_iff S CS s true _ _ _).2 h2
    · rw [hA, hr, hd]
      funext ⟨y, i⟩
      obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
      have := congrFun h3 (x, i)
      simpa [LatSymm.fld, symSite, coe_Ω1Equiv_symm S] using this

include B in
/-- **Lattice-symmetry covariance of the decoupled background field and multiplier** (cover `C`,
operator generating set `H`). -/
theorem decBg_sym (ρ : ℝ) (s : DecParams H) (D : BgData H N) :
    decBgField H a ν ρ (CS.par s) (S.sym D) = S.fld (decBgField H a ν ρ s D) ∧
      decBgMult H a ν ρ (CS.par s) (S.sym D) = S.mul (decBgMult H a ν ρ s D) := by
  classical
  have h0 : S.fld (0 : H.Ω 1 × Fin N → ℂ) = 0 := by funext p; simp [LatSymm.fld]
  have h0' : S.mul (0 : H.Ω 1 → ℂ) = 0 := rfl
  have hPQ : ∀ p : (H.Ω 1 × Fin N → ℂ) × (H.Ω 1 → ℂ),
      IsDecBg H a ν ρ s D p.1 p.2 ↔
        IsDecBg H a ν ρ (CS.par s) (S.sym D)
          ((S.fldEquiv.prodCongr S.mulEquiv) p).1 ((S.fldEquiv.prodCongr S.mulEquiv) p).2 :=
    fun p => (isDecBg_sym_iff S CS B ρ s D p.1 p.2).symm
  constructor
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun p => IsDecBg H a ν ρ s D p.1 p.2)
      (Q := fun p => IsDecBg H a ν ρ (CS.par s) (S.sym D) p.1 p.2) hPQ
      (fun p => S.fld p.1) (fun p => p.1) (fun p => rfl) (S.fld 0)
    rw [h0] at this
    unfold decBgField
    rw [← this]
    split_ifs <;> simp [h0]
  · have := dite_existsUnique_equiv (S.fldEquiv.prodCongr S.mulEquiv)
      (P := fun p => IsDecBg H a ν ρ s D p.1 p.2)
      (Q := fun p => IsDecBg H a ν ρ (CS.par s) (S.sym D) p.1 p.2) hPQ
      (fun p => S.mul p.2) (fun p => p.2) (fun p => rfl) (S.mul 0)
    rw [h0'] at this
    unfold decBgMult
    rw [← this]
    split_ifs <;> simp [h0']


end OldCover


end Balaban.Localization.DecEquiv
