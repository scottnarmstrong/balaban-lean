/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Prop33CloseNu
public import Balaban.Fluctuation.Prop33CloseReal
public import Balaban.Fluctuation.Prop33SymmV
public import Balaban.Fluctuation.Prop33SymmNu
public import Balaban.Fluctuation.Prop33SymmDef

/-!
# The potential part and the `ν`-part of Proposition 3.3 with the symmetry clause

`prop33_VNu_symm`: the terms of the potential part (`-c_β` times the `V`-terms) and of the
`ν`-part (`c_ν` times the `ν`-terms) of `interaction_expansion_bound_nu_closed` form a localized
expansion (`LocInt`) whose term map is exposed (rays terms of `evTerm` of the concrete functionals
of the decoupled objects `(F₁, Sol)`), which is `O(N)`-covariant (`TermRot`) and, for real `c_β`,
`c_ν`, real for real arguments (`TermReal`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section VNu

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {a₁ ν c BG κ eps : ℝ}

open Classical in
theorem prop33_VNu_symm {Kc Cx c₂ BG₂ δ₁ : ℝ}
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (cβ : ℂ) (hcβ : cβ.im = 0)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    {R₁ : ℝ} (hR₁ : 1 < R₁) {r Rσ : ℝ} (hr : 0 < r)
    -- the potential part
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hsm : 2 * (compC4 d * (bgK1 d L N * (xiC1 d * eps))) + 5 * (R * δ₁) ≤ bgC1 d L N)
    {m₀ : ℕ} {jV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcovV : ∀ z, CovSetup Gp (m₀) (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀) (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne (m₀) (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L (m₀) m₁ (jV z)) E₀ = treeLenCovOne (m₀) (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne (m₀) (jV z) (XV z) = 0)
    (hlogV : ∀ _z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hZV : ∀ z, readSites Hm n z ⊆ ↑(X₁V z))
    (hmarV : ∀ z, BlockMargin Gp (X₁V z)
      (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    -- the `ν`-part: the bound on the external field and the block margin of the blocks
    {Bh : ℝ} (hBh0 : 0 ≤ Bh)
    (hBh : ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
      ∀ x i, ‖D.h x i‖ ≤ Bh) (cν : ℂ) (hcν : cν.im = 0)
    (hZν : ∀ z, (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)) ⊆ ↑(X₁V z)) :
    ∃ (F₁V : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (SolV : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
      (F₁N : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (SolN : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
      (b : Set (CTorus d L N₁ m₁ K) → ℝ),
      (∀ z, F1Spec Gp a₁ ν BG κ (F₁V z)) ∧ (∀ z, SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ (SolV z)) ∧
      (∀ z, F1Spec Gp a₁ ν BG κ (F₁N z)) ∧ (∀ z, SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ (SolN z)) ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (Finset.univ.biUnion (fun z => blockDomains Gp m₀ (jV z) (𝒦XV z) (X₁V z)) ∪
          Finset.univ.biUnion (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)))
        (fun Y x₀ w σ Θ =>
          (if Y ∈ Finset.univ.biUnion (fun z => blockDomains Gp m₀ (jV z) (𝒦XV z) (X₁V z)) then
            (-cβ) * vSum Gp Hm a₁ ν n (fun _ => m₀) jV 𝒦XV X₁V F₁V SolV taylorWeight Y x₀ w σ Θ
            else 0) +
          (if Y ∈ Finset.univ.biUnion (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) then
            cν * dirTerm (nuSum Gp Hm n m₀ jV 𝒦XV X₁V F₁N SolN Y) (fun _ => (1 : ℂ)) x₀ w σ Θ
            else 0))
        (fun x₀ w σ Θ => (-cβ) * raySrc3 (interactionOne hG hG' hp a₁ ν eps) taylorWeight x₀ w σ Θ +
          cν * dirTermSrc (onXi Gp a₁ ν eps
            (fun D ψ' => nuTotal Gp Hm a₁ ν BG₂ κ D ψ')) (fun _ => (1 : ℂ)) x₀ w σ Θ)
        b
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) ∧
      TermRot (XiCRaw Gp (compWeight L a₁) ν K 1 eps) {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ (fun Y x₀ w σ Θ =>
          (if Y ∈ Finset.univ.biUnion (fun z => blockDomains Gp m₀ (jV z) (𝒦XV z) (X₁V z)) then
            (-cβ) * vSum Gp Hm a₁ ν n (fun _ => m₀) jV 𝒦XV X₁V F₁V SolV taylorWeight Y x₀ w σ Θ
            else 0) +
          (if Y ∈ Finset.univ.biUnion (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) then
            cν * dirTerm (nuSum Gp Hm n m₀ jV 𝒦XV X₁V F₁N SolN Y) (fun _ => (1 : ℂ)) x₀ w σ Θ
            else 0)) ∧
      TermReal (XiCRaw Gp (compWeight L a₁) ν K 1 eps) {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ (fun Y x₀ w σ Θ =>
          (if Y ∈ Finset.univ.biUnion (fun z => blockDomains Gp m₀ (jV z) (𝒦XV z) (X₁V z)) then
            (-cβ) * vSum Gp Hm a₁ ν n (fun _ => m₀) jV 𝒦XV X₁V F₁V SolV taylorWeight Y x₀ w σ Θ
            else 0) +
          (if Y ∈ Finset.univ.biUnion (fun z => polyDom Gp (X₁V z) m₀ (jV z) (𝒦XV z)) then
            cν * dirTerm (nuSum Gp Hm n m₀ jV 𝒦XV X₁V F₁N SolN Y) (fun _ => (1 : ℂ)) x₀ w σ Θ
            else 0)) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hωT : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (taylorWeight (t : ℂ)).im = 0 := by
    intro t ht
    simp [taylorWeight, Complex.div_ofNat_im, pow_two, Complex.mul_im]
  obtain ⟨F₁V, SolV, hFV, hSV, hLV, hRV, hReV⟩ := vpart_locInt_symm (m₀ := fun _ => m₀)
    (j := jV) (X := XV) (𝒦X := 𝒦XV) (X₁f := X₁V) hC hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum'
    (hreal_level hC hG hG' hp ha₁ H hc7 (by linarith) hsm) hcovV hX₁V hconn hrow hoptV hΔV hκ₀
    hκdec hκ h1 hlogV hn1 hZV hmarV continuous_taylorWeight hR₁ (analyticOnNhd_taylorWeight _)
    (Mω := 1 / 2) (by norm_num) (fun t ht => norm_taylorWeight_le t ht) hr hωT (Rσ := Rσ)
  obtain ⟨F₁N, SolN, hFN, hSN, hLN, hRN, hReN⟩ := nupart_locInt_bound_symm (m₀ := m₀) (j := jV)
    (X := XV) (𝒦X := 𝒦XV) (X₁z := X₁V) hC hp hG' hBh0 hBh hcovV hX₁V hconn hrow hoptV hΔV hκ₀
    hκdec hκ h1 (hlogV 0) hZν (ω := fun _ => (1 : ℂ)) continuous_const hR₁ analyticOnNhd_const
    (Mω := 1) zero_le_one (fun t ht => by simp) hr (fun t ht => by simp) (Rσ := Rσ)
  have hsub : {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} ⊆
      {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} := fun xw hxw => hxw.1
  have hcβ' : starRingEnd ℂ (-cβ) = -cβ := by
    rw [map_neg, Complex.conj_eq_iff_im.2 hcβ]
  have hcν' : starRingEnd ℂ cν = cν := Complex.conj_eq_iff_im.2 hcν
  have hLoc := (hLV.smul (-cβ)).add₂ ((hLN.mono_XW hsub).smul cν)
  exact ⟨F₁V, SolV, F₁N, SolN, _, hFV, hSV, hFN, hSN, hLoc,
    hRV.add_smul (hRN.mono_XW hsub) _ _ (-cβ) cν,
    hReV.add_smul (hReN.mono_XW hsub) _ _ hcβ' hcν'⟩

end VNu

end Balaban.Localization
