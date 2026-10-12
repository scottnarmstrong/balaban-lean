/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.InteractionSymmSolRot
public import Balaban.Fluctuation.InteractionSymmSolReal
public import Balaban.Fluctuation.Prop33SymmEnergy
public import Balaban.Fluctuation.Prop33SymmDef
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential part of the localized interaction, one block, with the symmetry clause

`vblock_locInt_symm` is `vblock_locInt` with the term map exposed: the terms are the ray terms of
`evTerm` of the concrete functional `blockEnergyFun` of the decoupled objects
`(F₁, Sol)` (whose specifications `F1Spec`, `SolSpec` are part of the conclusion), and they are
`O(N)`-covariant (`TermRot`) and real for real arguments (`TermReal`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

local notation "cj" => starRingEnd ℂ

section VBlockSymm

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ δfl : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

variable (Gp) in
/-- **The specification of the decoupled background map** `F₁` of Theorem I-4b: at parameters of
norm `< e^κ` and data in the union domain it returns the solution `(φ, α)` of the decoupled
system. -/
def F1Spec (a₁ ν BG κ : ℝ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N → (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) :
    Prop :=
  ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
    InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
      (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      F₁ (s, rawOf D) = (φ, α)

/-- `F1Spec` is inhabited: Theorem I-4b provides the background map. -/
theorem f1Spec_exists (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) :
    ∃ F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ), F1Spec Gp a₁ ν BG κ F₁ := by
  obtain ⟨F₁, -, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  exact ⟨F₁, hF₁⟩

theorem vblock_expansion_sol (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : readSites Hm n z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K))) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      F1Spec Gp a₁ ν BG κ F₁ ∧ SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol ∧
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
          (fnOfDec Gp Hm X₁f F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν n z))) Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
          (fnOfDec Gp Hm X₁f F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν n z))) Y u =
          (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
          (fnOfDec Gp Hm X₁f F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν n z))) Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖(evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
          (fnOfDec Gp Hm X₁f F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν n z))) Y u‖ ≤ energyBd d L N (compWeight L a₁) ν n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀ (X1 Gp m₀ j 𝒦X)
          (fnOfDec Gp Hm X₁f F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν n z)) Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ n :=
    (hC.HBp.weights n hn1 (by omega)).1.trans' (by norm_num)
  have hEb := energyBd_nonneg (d := d) (L := L) (N := N) ha hC.HBp.mass hV hC.δ₁_pos.le hρ
  obtain ⟨F₁, Sol, hF₁, hSol, -, h1', h2', h3', h4'⟩ := i5_functional_evTerm_sol hC hcov hX₁
    hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hEb (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν n z)
    ((blockEnergyFun_analytic _ ν n z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using blockEnergyFun_bound hC hn1 hn z ht)
    (Z := readSites Hm n z) (Zα := ↑(blockSites d L N₁ m₁ K n z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local _ ν n z hα hδ hψ)
  refine ⟨F₁, Sol, hF₁, hSol, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

/-- **The potential part of the localized interaction, one block, with the term map exposed and the symmetry clause.** -/
theorem vblock_locInt_symm (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : readSites Hm n z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) 
    (hωre : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → (ω (t : ℂ)).im = 0) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) K N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      F1Spec Gp a₁ ν BG κ F₁ ∧ SolSpec Gp Hm a₁ ν BG BG₂ κ eps δ₁ Sol ∧
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol
            (blockEnergyFun Gp Hm (compWeight L a₁) ν n z)) Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) ∧
      TermRot (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (fun Y x₀ w σ Θ => rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol
            (blockEnergyFun Gp Hm (compWeight L a₁) ν n z)) Y) w) ω x₀ σ Θ) ∧
      TermReal (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (fun Y x₀ w σ Θ => rayTerm (dl3 (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X) (fnOfDec Gp Hm X₁f F₁ Sol
            (blockEnergyFun Gp Hm (compWeight L a₁) ν n z)) Y) w) ω x₀ σ Θ) := by
  classical
  obtain ⟨F₁, Sol, hF₁, hSol, hsum, hloc, hbd, hanY⟩ := vblock_expansion_sol hC hcov hX₁ hconn hrow
    hopt hΔ hκ₀ hκdec hκ h1 hlog hn1 hn z hZ hmar
  refine ⟨F₁, Sol, hF₁, hSol, ?_, ?_, ?_⟩
  · refine locInt_dir3 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
      (f := blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) _ hR₁ hω hωc hMω hωb hr hanY
      (fun Y u hu => hbd Y u hu) ?_ ?_ ?_
    · intro Y a a' b b' p q ha hb y hy
      simp [ha y hy, hb y hy]
    · intro Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2'
      exact hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2'
    · intro Θ hΘ ψ' hψ
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [blockEnergyOne_rawOf hD n z ψ']
      exact hsum D hD ψ' hψ
  · refine termRot_ray hanY (fun Q hQ Y u hu => ?_) hr hR₁
    exact evTermSol_rot hC hF₁ hSol hQ (fun bg δφ u => energyBlock_rot
      (isRealOrth_ofReal hQ).1 _ ν n bg.2 δφ u.2 z) Y hu
  · refine termReal_ray hanY (fun Y u hu hre => ?_) hωre hr hR₁
    exact evTermSol_conj hC hF₁ hSol (fun bg δφ u _ => energyBlock_conj _ ν n bg.2 δφ u.2 z)
      Y hu hre

end VBlockSymm

end Balaban.Localization
