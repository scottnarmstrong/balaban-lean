/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.LatPairCover
public import Balaban.Localization.DecEquivLatBg

/-!
# Lattice symmetries between two generating sets: the decoupled background and the fixed points

The two-pair form of `DecEquivLatBg.lean`: for a lattice symmetry `S : LatSymm H H' σ` between two
generating sets, a permutation `τb` of the block indices carrying the blocks of `H` to those of
`H'` with their bumps (the two-set form of the fields of `BlockSymm`), and a permutation `τ` of the
centres between the covers `C`, `C'` (as in `LatPairCover.lean`):

* `approxField_sym_pair`: the approximate field `φ₀` is transported;
* `dphi_sym_pair`, `pertSource_sym_pair`, `Nmap_sym_pair`;
* `dec2Fixed_sym_iff_pair`, `fluctFixed_sym_iff_pair`: the fixed point equations of I-4a;
* `isDecBg2_sym_iff_pair`, `decBg2_sym_pair`: the decoupled background of I-4b.
The parameters are related by `extS C' s' ∘ τ = extS C s`.
-/

@[expose] public section

namespace Balaban.Localization.DecEquiv

open Balaban Balaban.Multiscale Balaban.Background Finset Matrix

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

section ApproxPair

variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} {τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

theorem denom_eq_pair (hbidx : ∀ q, τb q ∈ blockIdx G' ↔ q ∈ blockIdx G)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (x : CTorus d L N₁ m₁ K) : denom G' (σ x) = denom G x := by
  unfold denom
  refine (Finset.sum_equiv τb (fun q => (hbidx q).symm) fun q _ => ?_).symm
  exact (hbump q x).symm

theorem weight_eq_pair (hbidx : ∀ q, τb q ∈ blockIdx G' ↔ q ∈ blockIdx G)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (q : ℕ × CTorus d L N₁ m₁ K) (x : CTorus d L N₁ m₁ K) :
    weight G' (τb q) (σ x) = weight G q x := by
  unfold weight
  rw [hbump, denom_eq_pair hbidx hbump]

variable (S : LatSymm G G' σ)

theorem locSol_sym_pair (D : BgData G N) (y : CTorus d L N₁ m₁ K) :
    locSol G' a ν (S.sym D).Ψ (S.sym D).h (σ y) = locSol G a ν D.Ψ D.h y := by
  unfold locSol
  have hs : (S.sym D).Ψ (σ y) = D.Ψ y := by simp [LatSymm.sym]
  have hh : (S.sym D).h (σ y) = D.h y := by simp [LatSymm.sym]
  by_cases hy : y ∈ G.Ω 1
  · have hy' : σ y ∈ G'.Ω 1 := (S.mem_Ω1 y).2 hy
    have hm : blockMass G' ν (σ y) = blockMass G ν y := by
      simp only [blockMass, S.layerIndex_eq]
    simp only [hy, hy', ite_true, hs, hh, hm, S.layerIndex_eq]
  · have hy' : σ y ∉ G'.Ω 1 := fun h => hy ((S.mem_Ω1 y).1 h)
    simp only [hy, hy', ite_false, hs]

theorem interp_sym_pair (hbidx : ∀ q, τb q ∈ blockIdx G' ↔ q ∈ blockIdx G)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (Φ Φ' : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (hΦ : ∀ q ∈ blockIdx G, Φ' (τb q).2 = Φ q.2) (x : CTorus d L N₁ m₁ K) :
    interp G' Φ' (σ x) = interp G Φ x := by
  unfold interp
  refine (Finset.sum_equiv τb (fun q => (hbidx q).symm) fun q hq => ?_).symm
  rw [weight_eq_pair hbidx hbump, hΦ q hq]

/-- **Lattice-symmetry covariance of the approximate field `φ₀` between two generating sets.** -/
theorem approxField_sym_pair (hbidx : ∀ q, τb q ∈ blockIdx G' ↔ q ∈ blockIdx G)
    (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx G,
      jBlock d L (N₁ * L ^ m₁) K q.1 (σ.symm (τb q).2) = jBlock d L (N₁ * L ^ m₁) K q.1 q.2)
    (D : BgData G N) (x : CTorus d L N₁ m₁ K) :
    approxField G' a ν (S.sym D).Ψ (S.sym D).h (σ x) = approxField G a ν D.Ψ D.h x := by
  have hl : ∀ y, locSol G' a ν (S.sym D).Ψ (S.sym D).h (σ y) = locSol G a ν D.Ψ D.h y :=
    fun y => locSol_sym_pair S D y
  have hi : interp G' (locSol G' a ν (S.sym D).Ψ (S.sym D).h) (σ x) =
      interp G (locSol G a ν D.Ψ D.h) x := by
    refine interp_sym_pair hbidx hbump _ _ (fun q hq => ?_) x
    obtain ⟨⟨h1, hk⟩, hqℓ, -⟩ := (mem_blockIdx G).1 hq
    obtain ⟨-, hqℓ', -⟩ := (mem_blockIdx G').1 ((hbidx q).2 hq)
    rw [hblayer] at hqℓ'
    have hy' : σ.symm (τb q).2 ∈ G.layer q.1 := by
      rw [← S.mem_layer h1 hk]; simpa using hqℓ'
    have := hl (σ.symm (τb q).2)
    rw [Equiv.apply_symm_apply] at this
    rw [this]
    exact locSol_block D h1 hk hqℓ hy' (hbbase q hq)
  unfold approxField
  by_cases h1 : x ∈ G.Ω 1
  · have h1' : σ x ∈ G'.Ω 1 := (S.mem_Ω1 x).2 h1
    by_cases h2 : G.layerIndex x ≤ 1
    · have h2' : G'.layerIndex (σ x) ≤ 1 := by rwa [S.layerIndex_eq]
      simp only [h1, h1', h2, h2', ite_true, hl]
    · have h2' : ¬ G'.layerIndex (σ x) ≤ 1 := by rwa [S.layerIndex_eq]
      simp only [h1, h1', h2, h2', ite_true, ite_false, hi]
  · have h1' : σ x ∉ G'.Ω 1 := fun h => h1 ((S.mem_Ω1 x).1 h)
    by_cases h3 : x ∈ collar G
    · have h3' : σ x ∈ collar G' := (S.mem_collar x).2 h3
      simp only [h1, h1', h3, h3', ite_true, ite_false, hl]
    · have h3' : σ x ∉ collar G' := fun h => h3 ((S.mem_collar x).1 h)
      simp [h1, h1', h3, h3']

theorem approxField_symSite_pair (hbidx : ∀ q, τb q ∈ blockIdx G' ↔ q ∈ blockIdx G)
    (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx G,
      jBlock d L (N₁ * L ^ m₁) K q.1 (σ.symm (τb q).2) = jBlock d L (N₁ * L ^ m₁) K q.1 q.2)
    (D : BgData G N) :
    approxField G' a ν (S.sym D).Ψ (S.sym D).h = symSite σ (approxField G a ν D.Ψ D.h) := by
  funext y
  obtain ⟨x, rfl⟩ := σ.surjective y
  rw [approxField_sym_pair S hbidx hblayer hbump hbbase D x]
  simp [symSite]

end ApproxPair

section FixedPair

variable {G G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
  {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm G G' σ)

theorem coe_Ω1Equiv_symm_pair (y : G'.Ω 1) :
    ((S.Ω1Equiv.symm y : G.Ω 1) : CTorus d L N₁ m₁ K) = σ.symm (y : CTorus d L N₁ m₁ K) := by
  have h := S.coe_Ω1Equiv (S.Ω1Equiv.symm y)
  rw [Equiv.apply_symm_apply] at h
  rw [h, Equiv.symm_apply_apply]

theorem mulVec_rm_pair (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v : G.Ω 1 → ℂ) (x : G.Ω 1) :
    (rm S.Ω1Equiv A *ᵥ S.mul v) (S.Ω1Equiv x) = (A *ᵥ v) x := by
  simp only [Matrix.mulVec, dotProduct]
  rw [← Equiv.sum_comp S.Ω1Equiv]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [rm_apply, LatSymm.mul_apply]

theorem liftOp_rm_pair (A : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1)
    (i : Fin N) :
    (liftOp N (rm S.Ω1Equiv A) *ᵥ S.fld φ) (S.Ω1Equiv x, i) = (liftOp N A *ᵥ φ) (x, i) := by
  rw [liftOp_mulVec, liftOp_mulVec]
  have : (fun b => S.fld φ (b, i)) = S.mul (fun b => φ (b, i)) := by
    funext b; simp [LatSymm.fld, LatSymm.mul]
  rw [this]
  exact mulVec_rm_pair S A _ x

theorem residual_sym_pair (D : BgData G N) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : G.Ω 1)
    (i : Fin N) :
    Background.residual G' a ν (S.sym D) (symSite σ φ₀) (S.Ω1Equiv x, i) =
      Background.residual G a ν D φ₀ (x, i) := by
  unfold Background.residual
  have hφ : (fun p : G'.Ω 1 × Fin N => symSite σ φ₀ (p.1 : CTorus d L N₁ m₁ K) p.2) =
      S.fld (fun p : G.Ω 1 × Fin N => φ₀ (p.1 : CTorus d L N₁ m₁ K) p.2) := by
    funext p; simp [symSite, LatSymm.fld, coe_Ω1Equiv_symm_pair S]
  rw [Pi.sub_apply, Pi.sub_apply, hφ, S.source_sym]
  have := S.liftOp_sym a ν (0 : G.Ω 1 → ℂ)
    (fun p : G.Ω 1 × Fin N => φ₀ (p.1 : CTorus d L N₁ m₁ K) p.2) x i
  have h0 : S.mul (0 : G.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  rw [h0] at this
  rw [this]

theorem residual_symField_pair (D : BgData G N) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    Background.residual G' a ν (S.sym D) (symSite σ φ₀) =
      S.fld (Background.residual G a ν D φ₀) := by
  funext ⟨y, i⟩
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  rw [residual_sym_pair S]
  simp [LatSymm.fld]

theorem gdef_sym_pair (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) :
    gdef G' (symSite σ φ₀) = S.mul (gdef G φ₀) := by
  funext y
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  simp [gdef, symSite, LatSymm.mul]

theorem commK_sym_pair (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (δφ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    (commK (rm S.Ω1Equiv H₀) (restrictField G' (symSite σ φ₀)) *ᵥ S.fld δφ) (S.Ω1Equiv x) =
      (commK H₀ (restrictField G φ₀) *ᵥ δφ) x := by
  rw [commK_mulVec, commK_mulVec, ← Equiv.sum_comp S.Ω1Equiv]
  refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => ?_
  simp [restrictField, symSite, rm_apply]

theorem Rvec_sym_pair (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (v w : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Rvec (rm S.Ω1Equiv H₀) (S.fld v) (S.fld w) (S.Ω1Equiv x) = Rvec H₀ v w x := by
  rw [Rvec_eq, Rvec_eq]
  have e1 : (fun y : G'.Ω 1 => ∑ i, S.fld v (y, i) * S.fld w (y, i)) =
      S.mul (fun y => ∑ i, v (y, i) * w (y, i)) := by
    funext y; simp [LatSymm.fld, LatSymm.mul]
  rw [e1, mulVec_rm_pair S]
  simp only [LatSymm.fld_apply, liftOp_rm_pair S]

theorem Nmap_sym_pair (H₀ : Matrix (G.Ω 1) (G.Ω 1) ℂ) (ιU : Bool)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs δφ : G.Ω 1 × Fin N → ℂ) (x : G.Ω 1) :
    Nmap G' (rm S.Ω1Equiv H₀) ιU (symSite σ φ₀) (S.fld Fs) (S.fld δφ) (S.Ω1Equiv x) =
      Nmap G H₀ ιU φ₀ Fs δφ x := by
  unfold Nmap
  rw [commK_sym_pair S, Rvec_sym_pair S, gdef_sym_pair S, mulVec_rm_pair S]
  simp [symSite, LatSymm.fld]

theorem Fsrc_sym_pair (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ)
    (δα : G.Ω 1 → ℂ) :
    Fsrc (G := G') (symSite σ φ₀) (S.fld Fs) (S.mul δα) = S.fld (Fsrc (G := G) φ₀ Fs δα) := by
  funext p
  simp [Fsrc, symSite, LatSymm.fld, LatSymm.mul, coe_Ω1Equiv_symm_pair S]

/-- **Lattice-symmetry covariance of `δφ(δα)` between two generating sets**, for Green families
with `𝒢' (σ α) = σ 𝒢 (α) σ⁻¹`. -/
theorem dphi_sym_pair {𝒢 : (G.Ω 1 → ℂ) → Matrix (G.Ω 1) (G.Ω 1) ℂ}
    {𝒢' : (G'.Ω 1 → ℂ) → Matrix (G'.Ω 1) (G'.Ω 1) ℂ}
    (h𝒢 : ∀ α, 𝒢' (S.mul α) = rm S.Ω1Equiv (𝒢 α)) (α₀ : G.Ω 1 → ℂ)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ) :
    dphi G' 𝒢' (S.mul α₀) (symSite σ φ₀) (S.fld Fs) (S.mul δα) =
      S.fld (dphi G 𝒢 α₀ φ₀ Fs δα) := by
  funext ⟨y, i⟩
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  unfold dphi
  have h0 : S.mul α₀ + S.mul δα = S.mul (α₀ + δα) := by
    funext z; simp [LatSymm.mul]
  rw [h0, h𝒢, Fsrc_sym_pair S, liftOp_rm_pair S]
  simp [LatSymm.fld]

/-- **Covariance of the perturbation source between two generating sets.** -/
theorem pertSource_sym_pair (δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : G.Ω 1 × Fin N → ℂ)
    (x : G.Ω 1) (i : Fin N) :
    pertSource G' a (symSite σ δΨ) (S.fld f₁) (S.Ω1Equiv x, i) = pertSource G a δΨ f₁ (x, i) := by
  simp only [pertSource, Pi.add_apply, qStar, boundaryTerm, LatSymm.coe_Ω1Equiv, S.layerIndex_eq,
    symSite, Equiv.symm_apply_apply, LatSymm.fld_apply]
  congr 2
  rw [← Equiv.sum_comp S.perm]
  refine Finset.sum_congr rfl fun μ _ => ?_
  have := S.bdry_swap (fun z => if z ∈ collar G' then δΨ (σ.symm z) i else 0) x μ
  simp only [S.mem_collar, Equiv.symm_apply_apply] at this
  convert this using 2 <;> congr

theorem pertSource_symField_pair (δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ)
    (f₁ : G.Ω 1 × Fin N → ℂ) :
    pertSource G' a (symSite σ δΨ) (S.fld f₁) = S.fld (pertSource G a δΨ f₁) := by
  funext ⟨y, i⟩
  obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
  rw [pertSource_sym_pair S, LatSymm.fld_apply]

end FixedPair

section BgPair

variable {C C' : DecCover d L N₁ m₁ K} {H H' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
  {a : ℕ → ℝ} {ν : ℝ} {σ : Equiv.Perm (CTorus d L N₁ m₁ K)} (S : LatSymm H H' σ)
  {τ : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

/-- The Green family `decG` of `(C, H)` is carried to that of `(C', H')`. -/
theorem decG2_sym_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    {s : Dec2.DecParams C} {s' : Dec2.DecParams C'}
    (hs : ∀ P, Dec2.extS C' s' (τ P) = Dec2.extS C s P) (β : H.Ω 1 → ℂ) :
    Dec2.decG C' H' a ν s' (S.mul β) = rm S.Ω1Equiv (Dec2.decG C H a ν s β) :=
  (rm_Gs_pair S hidx hchi hbox hqset a ν β hs).symm

theorem dec2Fixed_sym_iff_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    {s : Dec2.DecParams C} {s' : Dec2.DecParams C'}
    (hs : ∀ P, Dec2.extS C' s' (τ P) = Dec2.extS C s P) (ιU : Bool) (α₀ : H.Ω 1 → ℂ)
    (φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ) (Fs : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) :
    Dec2.DecFixed C' H' a ν s' ιU (S.mul α₀) (symSite σ φ₀) (S.fld Fs) (S.mul δα) ↔
      Dec2.DecFixed C H a ν s ιU α₀ φ₀ Fs δα := by
  unfold Dec2.DecFixed
  rw [dphi_sym_pair S (decG2_sym_pair S hidx hchi hbox hqset hs) α₀ φ₀ Fs δα,
    ← rm_dirichlet_pair S]
  constructor
  · intro h
    funext x
    have := congrFun h (S.Ω1Equiv x)
    rw [Nmap_sym_pair S, LatSymm.mul_apply] at this
    exact this
  · intro h
    funext y
    obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
    rw [Nmap_sym_pair S, LatSymm.mul_apply]
    exact congrFun h x

/-- **The fixed point equation of the fluctuation field (I-4a, mode P) between two pairs.** -/
theorem fluctFixed_sym_iff_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    {s : Dec2.DecParams C} {s' : Dec2.DecParams C'}
    (hs : ∀ P, Dec2.extS C' s' (τ P) = Dec2.extS C s P) (ιU : Bool) (α₀ : H.Ω 1 → ℂ)
    (φ₀ δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ) (f₁ : H.Ω 1 × Fin N → ℂ) (δα : H.Ω 1 → ℂ) :
    Dec2.DecFixed C' H' a ν s' ιU (S.mul α₀) (symSite σ φ₀)
        (pertSource H' a (symSite σ δΨ) (S.fld f₁)) (S.mul δα) ↔
      Dec2.DecFixed C H a ν s ιU α₀ φ₀ (pertSource H a δΨ f₁) δα := by
  rw [pertSource_symField_pair S]
  exact dec2Fixed_sym_iff_pair S hidx hchi hbox hqset hs ιU α₀ φ₀ _ δα

variable {τb : Equiv.Perm (ℕ × CTorus d L N₁ m₁ K)}

/-- **`IsDecBg` of `(C, H)` is carried to `IsDecBg` of `(C', H')`**: the datum, field and
multiplier are transported by `σ`, the decoupling parameters by `τ`. -/
theorem isDecBg2_sym_iff_pair (hidx : ∀ q, τ q ∈ C'.cubeIdx ↔ q ∈ C.cubeIdx)
    (hchi : ∀ q x, C'.chi (τ q) (σ x) = C.chi q x)
    (hbox : ∀ q x, σ x ∈ intBox (τ q) ↔ x ∈ intBox q)
    (hqset : ∀ q q', τ q' ∈ C'.Qset (τ q) ↔ q' ∈ C.Qset q)
    (hbidx : ∀ q, τb q ∈ blockIdx H' ↔ q ∈ blockIdx H) (hblayer : ∀ q, (τb q).1 = q.1)
    (hbump : ∀ q x, Background.bump (τb q).1 (τb q).2 (σ x) = Background.bump q.1 q.2 x)
    (hbbase : ∀ q ∈ blockIdx H,
      jBlock d L (N₁ * L ^ m₁) K q.1 (σ.symm (τb q).2) = jBlock d L (N₁ * L ^ m₁) K q.1 q.2)
    {s : Dec2.DecParams C} {s' : Dec2.DecParams C'}
    (hs : ∀ P, Dec2.extS C' s' (τ P) = Dec2.extS C s P) (ρ : ℝ) (D : BgData H N)
    (φ : H.Ω 1 × Fin N → ℂ) (α : H.Ω 1 → ℂ) :
    Dec2.IsDecBg C' H' a ν ρ s' (S.sym D) (S.fld φ) (S.mul α) ↔
      Dec2.IsDecBg C H a ν ρ s D φ α := by
  have hA := approxField_symSite_pair (a := a) (ν := ν) S hbidx hblayer hbump hbbase D
  have hr := residual_symField_pair (a := a) (ν := ν) S D (approxField H a ν D.Ψ D.h)
  have hsm : Small H' (S.mul α) ρ ↔ Small H α ρ := by
    refine ⟨fun h x => ?_, fun h y => ?_⟩
    · have := h (S.Ω1Equiv x)
      simpa [S.spacing_eq] using this
    · obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
      simpa [S.spacing_eq] using h x
  have h0 : S.mul (0 : H.Ω 1 → ℂ) = 0 := by funext y; simp [LatSymm.mul]
  have hd := dphi_sym_pair S (decG2_sym_pair (a := a) (ν := ν) S hidx hchi hbox hqset hs)
    (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
    (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α
  rw [h0] at hd
  have hfx := dec2Fixed_sym_iff_pair (a := a) (ν := ν) S hidx hchi hbox hqset hs true
    (0 : H.Ω 1 → ℂ) (approxField H a ν D.Ψ D.h)
    (Background.residual H a ν D (approxField H a ν D.Ψ D.h)) α
  rw [h0] at hfx
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hA, hr] at h2 h3
    refine ⟨hsm.1 h1, hfx.1 h2, ?_⟩
    rw [hd] at h3
    funext ⟨y, i⟩
    have := congrFun h3 (S.Ω1Equiv y, i)
    simpa [LatSymm.fld, symSite, coe_Ω1Equiv_symm_pair S] using this
  · rintro ⟨h1, h2, h3⟩
    refine ⟨hsm.2 h1, ?_, ?_⟩
    · rw [hA, hr]; exact hfx.2 h2
    · rw [hA, hr, hd]
      funext ⟨y, i⟩
      obtain ⟨x, rfl⟩ := S.Ω1Equiv.surjective y
      have := congrFun h3 (x, i)
      simpa [LatSymm.fld, symSite, coe_Ω1Equiv_symm_pair S] using this

end BgPair

end Balaban.Localization.DecEquiv
