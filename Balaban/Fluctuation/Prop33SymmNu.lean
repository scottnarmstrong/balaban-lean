/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33Nu
public import Balaban.Fluctuation.Prop33SymmV
public import Balaban.Fluctuation.Prop33SymmDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `ν`-part of the localized interaction with the symmetry clause

The block functional `nuBlockFun` of the mass variation `V_{ν,1}` is `O(N)`-invariant under
`(φ_{k+1}, δφ, h̃) ↦ (R φ_{k+1}, R δφ, R h̃)` and commutes with complex conjugation.  The terms of
`nupart_locInt` are the first-order ray terms of `evTerm` of `nuBlockFun`; with the engine theorem
`i5_functional_evTerm_sol` they are `O(N)`-covariant and real for real arguments
(`nupart_locInt_symm`, `nupart_locInt_bound_symm`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

local notation "cj" => starRingEnd ℂ

section NuSymm

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ}

theorem dot_rot_sub {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (u v w : Fin N → ℂ) :
    ∑ i, (R *ᵥ u) i * ((R *ᵥ v) i - (R *ᵥ w) i) = ∑ i, u i * (v i - w i) := by
  have := dot_rot hR u (v - w)
  simpa [Matrix.mulVec_sub] using this

/-- **`O(N)` invariance of the density of `V_{ν,1}`.** -/
theorem nuDensity_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1)
    (δφ : Hm.Ω 1 × Fin N → ℂ) (φ₁ : Gp.Ω 1 × Fin N → ℂ)
    (hh : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : CTorus d L N₁ m₁ K) :
    nuDensity Gp Hm (rotFld R δφ) (rotFld R φ₁) (DecEquiv.rotSite R hh) x =
      nuDensity Gp Hm δφ φ₁ hh x := by
  unfold nuDensity
  simp only [svec_rot, Finset.sum_add_distrib]
  have e1 : ∀ i, (DecEquiv.rotSite R hh x) i = (R *ᵥ hh x) i := fun i => rfl
  simp only [e1]
  rw [dot_rot_sub hR, ← Finset.mul_sum, ← Finset.mul_sum, dot_rot hR]

theorem nuBlockFun_rot {R : Matrix (Fin N) (Fin N) ℂ} (hR : Rᵀ * R = 1) (n : ℕ)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) :
    nuBlockFun Gp Hm n z (rotFld R pa.1, pa.2) (rotFld R δφ) (rotU R u) =
      nuBlockFun Gp Hm n z pa δφ u :=
  Finset.sum_congr rfl fun x _ => nuDensity_rot hR δφ pa.1 u.1.2 x

/-- **Conjugation covariance of the density of `V_{ν,1}`.** -/
theorem nuDensity_conj (δφ : Hm.Ω 1 × Fin N → ℂ) (φ₁ : Gp.Ω 1 × Fin N → ℂ)
    (hh : CTorus d L N₁ m₁ K → Fin N → ℂ) (x : CTorus d L N₁ m₁ K) :
    cj (nuDensity Gp Hm δφ φ₁ hh x) =
      nuDensity Gp Hm (fun p => cj (δφ p)) (fun p => cj (φ₁ p)) (DecEquiv.cjSite hh) x := by
  unfold nuDensity
  simp only [svec_conj, map_sum, map_add, map_mul, map_sub, map_div₀, map_one, map_ofNat,
    DecEquiv.cjSite]

theorem nuBlockFun_conj (n : ℕ) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (pa : (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) (δφ : Hm.Ω 1 × Fin N → ℂ)
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))
    (hu : IsRealRaw u.1) :
    cj (nuBlockFun Gp Hm n z pa δφ u) =
      nuBlockFun Gp Hm n z (fun p => cj (pa.1 p), fun x => cj (pa.2 x)) (fun p => cj (δφ p))
        (cjU u) := by
  unfold nuBlockFun
  rw [map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [nuDensity_conj]
  have : DecEquiv.cjSite u.1.2 = u.1.2 := funext fun y => funext fun i =>
    Complex.conj_eq_iff_im.2 (hu y i).2
  simp only [cjU, this]

variable (Gp Hm) in
/-- **The terms of the expansion of a `ν`-block functional.** -/
noncomputable def nuEv (n : ℕ) (m₀ j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ K))
    (X₁f : Finset (CTorus d L N₁ m₁ K))
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1)))) (Y : Set (CTorus d L N₁ m₁ K))
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ :=
  evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
    (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol (nuBlockFun Gp Hm n z)) Y u

variable {j m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

theorem nublock_expansion_sol (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑X₁f) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      F1Spec Gp a₁ ν BG κ F₁ ∧ SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol ∧
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        nuBlockFun Gp Hm n z (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ')
          (rawOf D, ψ') = ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, nuEv Gp Hm n m₀ j 𝒦X X₁f F₁ Sol z Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        nuEv Gp Hm n m₀ j 𝒦X X₁f F₁ Sol z Y u = nuEv Gp Hm n m₀ j 𝒦X X₁f F₁ Sol z Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖nuEv Gp Hm n m₀ j 𝒦X X₁f F₁ Sol z Y u‖ ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (nuEv Gp Hm n m₀ j 𝒦X X₁f F₁ Sol z Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by

  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨F₁, Sol, hF₁, hSol, -, h1', h2', h3', h4'⟩ := i5_functional_evTerm_sol hC hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hEb (Φ := nuBlockFun Gp Hm n z) ((nuBlockFun_analytic (Gp := Gp) (Hm := Hm) n z).mono
      (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using nuBlockFun_bound hC hp hG' hBh0 hBh z ht)
    (Z := ↑(blockSites d L N₁ m₁ K n z)) (Zα := ∅) hZ (fun x hx => absurd hx (Set.notMem_empty x))
    (fun t _ t' _ hφ _ hδ hag _ => nuBlockFun_local n z hφ hδ hag)
  refine ⟨F₁, Sol, hF₁, hSol, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa [nuEv] using this

section NuPartSymm

variable {j : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
variable {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
variable {X₁z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
variable {m₀ : ℕ}

variable (Gp Hm) in
/-- **The terms of the expansion of the mass variation `V_{ν,1}`**, summed over the blocks. -/
noncomputable def nuSum (n : ℕ) (m₀ : ℕ)
    (j : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ)
    (𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K))
    (X₁z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K))
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Dec2.DecParams (coverOf Gp) × Edat Hm N →
      (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Y : Set (CTorus d L N₁ m₁ K))
    (u : RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ)) : ℂ := by
  classical
  exact ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
    nuEv Gp Hm n m₀ (j z) (𝒦X z) (X₁z z) (F₁ z) (Sol z) z Y u else 0

theorem nupart_locInt_symm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) 
    (hωre : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (ω (t : ℂ)).im = 0) :
    ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      (∀ z, F1Spec Gp a₁ ν BG κ (F₁ z)) ∧ (∀ z, SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ (Sol z)) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) (fun Y x₀ w σ Θ => dirTerm (nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) ω x₀ w σ Θ)
        (fun Y => Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) ∧
      TermRot (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ (fun Y x₀ w σ Θ => dirTerm (nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol Y) ω x₀ w σ Θ) ∧
      TermReal (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ (fun Y x₀ w σ Θ => dirTerm (nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol Y) ω x₀ w σ Θ) := by
  classical
  have hex := fun z => nublock_expansion_sol hC hp hG' hBh0 hBh (hcov z) (hX₁ z) hconn hrow (hopt z)
    (hΔ z) hκ₀ hκdec hκ h1 hlog z (hZ z) (δ₁ := δ₁)
  choose F₁ Sol hF hS hsum hloc hbd han using hex
  refine ⟨F₁, Sol, hF, hS, ?_, ?_, ?_⟩
  · refine locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
      (f := onXi Gp a₁ ν eps (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ'))
      (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z))
      (Evs := nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol)
      (b := fun Y => ∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
        nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
          (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0)
      (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
      (AgF := fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
      (isOpen_flBall (N := N) Hm δ₁) ?_ ?_ ?_ ?_ ?_
    · intro Y u hu
      refine Finset.analyticAt_fun_sum _ fun z _ => ?_
      by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
      · simpa only [hY, ite_true] using han z Y u hu
      · simp only [hY, ite_false]; exact analyticAt_const
    · intro Y u hu
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun z _ => ?_)
      by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
      · simpa only [hY, ite_true] using hbd z Y u hu
      · simp [hY]
    · intro Y a a' c' c'' p q ha hb y hy
      simp [ha y hy, hb y hy]
    · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
      refine Finset.sum_congr rfl fun z'' _ => ?_
      by_cases hY : Y ∈ polyDom Gp (X₁z z'') m₀ (j z'') (𝒦X z'')
      · simp only [hY, ite_true]
        exact hloc z'' Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2'
      · simp [hY]
    · rintro Θ ⟨D, hD, rfl⟩ ψ' hψ
      rw [onXi_rawOf hD, ← sum_nuBlockFun (n := n) a₁ ν BG₂ κ D ψ']
      unfold nuSum
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [hsum z D hD ψ' hψ, Finset.sum_ite_mem,
        Finset.inter_eq_right.2 (Finset.subset_biUnion_of_mem
          (fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) (Finset.mem_univ z))]
  · refine termRot_dir (Evs := nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol) ?_ (fun Q hQ Y u hu => ?_) hr hR₁
    · intro Y u hu
      refine Finset.analyticAt_fun_sum _ fun z _ => ?_
      by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
      · simpa only [hY, ite_true] using han z Y u hu
      · simp only [hY, ite_false]; exact analyticAt_const
    · refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
      · simp only [hY, ite_true]
        exact evTermSol_rot hC (hF z) (hS z) hQ (fun bg δφ u => nuBlockFun_rot
          (isRealOrth_ofReal hQ).1 n z bg δφ u) Y hu
      · simp [hY]
  · refine termReal_dir (Evs := nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol) ?_ (fun Y u hu hre => ?_) hωre hr hR₁
    · intro Y u hu
      refine Finset.analyticAt_fun_sum _ fun z _ => ?_
      by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
      · simpa only [hY, ite_true] using han z Y u hu
      · simp only [hY, ite_false]; exact analyticAt_const
    · show cj (∑ z, _) = ∑ z, _
      rw [map_sum]
      refine Finset.sum_congr rfl fun z _ => ?_
      by_cases hY : Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)
      · simp only [hY, ite_true]
        exact evTermSol_conj hC (hF z) (hS z) (fun bg δφ u hu' => nuBlockFun_conj n z bg δφ u hu')
          Y hu hre
      · simp only [hY, ite_false, map_zero]

theorem nupart_locInt_bound_symm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hp : n + 1 ≤ K) (hG' : IsLevel Gp (n + 1)) {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh)
    (hcov : ∀ z, CovSetup Gp m₀ (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁z z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp m₀ (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne m₀ (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (j z)) E₀ = treeLenCovOne m₀ (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne m₀ (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hZ : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁z z))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) 
    (hωre : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (ω (t : ℂ)).im = 0) :
    ∃ (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      (∀ z, F1Spec Gp a₁ ν BG κ (F₁ z)) ∧ (∀ z, SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ (Sol z)) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁z z) m₀ (j z) (𝒦X z)) (fun Y x₀ w σ Θ => dirTerm (nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) ω x₀ w σ Θ)
        (fun Y => Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) *
          Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (n + 1) Y))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) ∧
      TermRot (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ (fun Y x₀ w σ Θ => dirTerm (nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol Y) ω x₀ w σ Θ) ∧
      TermReal (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ (fun Y x₀ w σ Θ => dirTerm (nuSum Gp Hm n m₀ j 𝒦X X₁z F₁ Sol Y) ω x₀ w σ Θ) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hd0 : 0 < d := by omega
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hB1 : 0 ≤ K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh := by
    have hK4 : 0 < K4 d L N BG κ := K4_pos (L := L) (N := N) (κ := κ) hC.hS.fam.2.1 hd0
    have hx1 := one_le_xiC1 d
    have hx2 := hC.eps_pos
    have hx3 : 0 ≤ xiC1 d * eps := by positivity
    have hx4 := mul_nonneg hK4.le hx3
    linarith
  have hEb : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) := by
    unfold nuBd; positivity
  obtain ⟨F₁, Sol, hF, hS, hT, hR, hRe⟩ := nupart_locInt_symm hC hp hG' hBh0 hBh hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1
    hlog hZ hωc hR₁ hω hMω hωb hr hωre (Rσ := Rσ)
  refine ⟨F₁, Sol, hF, hS, hT.mono_on fun Y hY => ?_, hR, hRe⟩
  obtain ⟨z₀, -, hz₀⟩ := Finset.mem_biUnion.1 hY
  have hMD := polyDom_isMultiDom (hcov z₀) hd (hopt z₀) hz₀
  have hcard : ((Finset.univ.filter fun z => Y ∈ polyDom Gp (X₁z z) m₀ (j z)
      (𝒦X z)).card : ℝ) ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) := by
    refine card_blocks_filter_le hG' hp (hcov z₀).hN hMD _ (fun z hz => ?_)
    have h1' := subset_polyDom (Finset.mem_filter.1 hz).2
    rw [← hX₁ z] at h1'
    exact fun x hx => h1' (hZ z hx)
  have ht0 := treeLenCov_nonneg Gp m₀ Y
  have hv : 0 ≤ nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
      (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) := by positivity
  have hs := sum_ite_card_le _ hv hcard
  rw [← treeLenCov_eq_treeLenCovOne hG' m₀ Y]
  have key := one_add_mul_exp_le (treeLenCov Gp m₀ Y) κdec
  have hCn : 0 ≤ Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
      nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
        (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r) := by positivity
  calc Mω * ((∑ z, if Y ∈ polyDom Gp (X₁z z) m₀ (j z) (𝒦X z) then
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) else 0) / r)
      ≤ Mω * ((c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d * (1 + treeLenCov Gp m₀ Y) *
          (nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) *
            Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))) / r) := by
        refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hs hr.le) hMω
    _ = (Mω * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
          nuBd d L N n (cK2' d L N (famConst d L BG₂ κ) * δ₁)
            (K4 d L N BG κ * (xiC1 d * eps) + (1 + 3 * (xiC1 d * eps)) + Bh) / r)) *
          ((1 + treeLenCov Gp m₀ Y) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left key hCn

end NuPartSymm

end NuSymm

end Balaban.Localization
