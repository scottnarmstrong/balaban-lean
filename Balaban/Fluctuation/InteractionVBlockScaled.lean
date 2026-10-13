/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.InteractionVBlock
public import Balaban.Fluctuation.InteractionEnergyScaled
public import Balaban.Fluctuation.InteractionLevelPair
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The potential part of the localized interaction with the scale-uniform energy bound

The statements of `vblock_expansion`, `vblock_locInt`, `vblocks_locInt` of `InteractionVBlock.lean`
with the majorant `energyBdScaled` (`InteractionEnergyScaled.lean`) of the block energy in place of
the landed `energyBd`.  The majorant gains a factor of order `L^{2n}` over `energyBd`
(`energyBdScaled_eq`: it equals `L^{n(d-2)}` times a constant, whereas `energyBd` is of order
`L^{nd}`).  The extra hypotheses are the structural ones of a full level: `IsLevel Hm n` and
`IsLevel Gp (n+1)`; the mass and weight bounds come from `FlCore` (`BgHyp.massLe`, `weights`).
The proofs are those of the landed theorems with `blockEnergyFun_bound_scaled` in place of
`blockEnergyFun_bound` (copied, since the bound is used inside the proof); the landed theorems stay
valid as the weaker statements.  Propagation to the hat functions and the activity bound belongs to
later packages.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section VBlockScaled

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **The block energy is bounded in physical units on the realizable triples.**  The hypotheses
are those of `blockEnergyFun_bound` and the structural `IsLevel` of the two generating sets; the
weighted sup bounds hold on the whole of `FlReal` (complex decoupling parameters), by
`flReal_facts`, and the mass bound is `BgHyp.massLe` at the top level `K ≥ n + 1`. -/
theorem blockEnergyFun_bound_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {n : ℕ} (hHm : IsLevel Hm n) (hGp : IsLevel Gp (n + 1)) (hn1 : 1 ≤ n) (hn : n + 1 ≤ K)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    {t : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ))}
    (ht : t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖blockEnergyFun Gp Hm (compWeight L a₁) ν n z t.1 t.2.1 t.2.2‖ ≤
      energyBdScaled d L N (compWeight L a₁) n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
        (rho4 d L N BG κ) := by
  obtain ⟨hα, hsup, hψ⟩ := flReal_facts ht
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
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast (by have := NeZero.ne L; omega : 1 ≤ L)
  have hmass : ν * ((L : ℝ) ^ (n + 1)) ^ 2 ≤ 1 := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ hC.HBp.mass) hC.HBp.massLe
    exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ hL1 hn) 2
  exact energyBlock_bound_scaled hn ha hC.HBp.mass hmass hHm hGp hV hρ hsup hα
    (fun x hx i => by
      have hxd : x ∈ dataSites Hm := (mem_dataSites Hm).2 (Or.inl hx)
      exact (norm_le_vn _ i).trans (hψ x hxd).le) z

/-- **The block energy expands over the domains `Y ⊃ X₁`** with the scale-uniform majorant
(`vblock_expansion` with `energyBdScaled`). -/
theorem vblock_expansion_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (hHm : IsLevel Hm n) (hGp : IsLevel Gp (n + 1)) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : readSites Hm n z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet Gp Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ energyBdScaled d L N (compWeight L a₁) n (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ) * Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
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
  have hEb := energyBdScaled_nonneg (d := d) (L := L) (N := N) ha hV hC.δ₁_pos.le hρ
  obtain ⟨Ev, h1', h2', h3', h4'⟩ := i5_functional hC hcov hX₁ hconn hrow hopt hκ₀ hκdec hκ h1 hlog
    hEb (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν n z)
    ((blockEnergyFun_analytic _ ν n z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ]; simpa using blockEnergyFun_bound_scaled hC hHm hGp hn1 hn z ht)
    (Z := readSites Hm n z) (Zα := ↑(blockSites d L N₁ m₁ K n z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local _ ν n z hα hδ hψ)
  refine ⟨Ev, h1', h2', fun Y u hu => ?_, h4'⟩
  have := h3' Y u hu
  rw [hΔ] at this
  simpa using this

/-- **The potential part of the localized interaction, one block**, with the scale-uniform
majorant (`vblock_locInt` with `energyBdScaled`). -/
theorem vblock_locInt_scaled (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    {n : ℕ} (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (hHm : IsLevel Hm n) (hGp : IsLevel Gp (n + 1)) (z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))))
    (hZ : readSites Hm n z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := vblock_expansion_scaled hC hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ
    h1 hlog hn1 hn hHm hGp z hZ hmar
  refine ⟨Ev, ?_⟩
  refine locInt_dir3 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
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

/-- **The potential part of the localized interaction, all blocks**, with the scale-uniform
majorant (`vblocks_locInt` with `energyBdScaled`). -/
theorem vblocks_locInt_scaled {n : ℕ} (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    {m₀ j : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → ℕ}
    {X 𝒦X : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K)}
    {X₁f : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (CTorus d L N₁ m₁ K)}
    (hcov : ∀ z, CovSetup Gp (m₀ z) (j z) (X z) (𝒦X z))
    (hX₁ : ∀ z, (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) = X1 Gp (m₀ z) (j z) (𝒦X z))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ K))
      (E₀ : Finset (CTorus d L N₁ m₁ K × CTorus d L N₁ m₁ K)),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X z) ∧ MeetsOne (m₀ z) (j z) (𝒦X z) W₀ ∧
        bondCost (scaleW L (m₀ z) m₁ (j z)) E₀ = treeLenCovOne (m₀ z) (j z) (X z))
    (hΔ : ∀ z, treeLenCovOne (m₀ z) (j z) (X z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : ∀ z, Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀ z) ^ d : ℕ) : ℝ)) ≤
      (κ / 2 - 1) / 2)
    (hn1 : 1 ≤ n) (hn : n + 1 ≤ K) (hHm : IsLevel Hm n) (hGp : IsLevel Gp (n + 1))
    (hZ : ∀ z, readSites Hm n z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z) (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ (𝒴 : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Finset (Set (CTorus d L N₁ m₁ K)))
      (T : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (Finset.univ.biUnion 𝒴)
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ 𝒴 z then T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => ∑ z, raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ 𝒴 z then Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hex : ∀ z, ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Ev Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBdScaled d L N (compWeight L a₁) n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := fun z =>
    vblock_locInt_scaled hC (hcov z) (hX₁ z) hconn hrow (hopt z) (hΔ z) hκ₀ hκdec hκ h1 (hlog z) hn1 hn hHm hGp z
      (hZ z) (hmar z) hωc hR₁ hω hMω hωb hr
  choose Ev hEv using hex
  exact ⟨fun z => polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) =>
      i.1.1) Gp (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)),
    fun z Y x₀ w σ Θ => rayTerm (dl3 (Ev z Y) w) ω x₀ σ Θ,
    LocInt.finsum Finset.univ (fun z _ => hEv z)⟩

/-- **The scaled bound at the level pair of the landed step witnesses** (`hatStep`:
`LevelPair.Gp` of level `2` and `LevelPair.Hm` of level `1` on the torus with `K = 2`, `d = L = 3`):
the hypotheses of `blockEnergyFun_bound_scaled` hold (`LevelPair.isLevel_Hm`, `isLevel_Gp`;
`n = 1`, `n + 1 = K`), the scaled bound holds, and it is at most the landed `energyBd`.  The
`FlCore` is the one produced by the witnesses (`hatWitness_core_amp`). -/
theorem blockEnergyFun_bound_scaled_levelPair {m₁ : ℕ} {ϱ : ℝ} {N : ℕ}
    {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus 3 3 9 m₁ 2)}
    (hC : FlCore N (LevelPair.Gp m₁ ϱ) (LevelPair.Hm m₁ ϱ) a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (z : Torus 3 (9 * 3 ^ m₁ * 3 ^ (2 - (1 + 1))))
    {t : (((LevelPair.Gp m₁ ϱ).Ω 1 × Fin N → ℂ) × ((LevelPair.Gp m₁ ϱ).Ω 1 → ℂ)) ×
      ((LevelPair.Hm m₁ ϱ).Ω 1 × Fin N → ℂ) ×
      (RawData 3 3 (9 * 3 ^ m₁) 2 N × (CTorus 3 3 9 m₁ 2 → Fin N → ℂ))}
    (ht : t ∈ FlReal (LevelPair.Gp m₁ ϱ) (LevelPair.Hm m₁ ϱ) a₁ ν BG κ eps X₁f BG₂ δ₁) :
    ‖blockEnergyFun (LevelPair.Gp m₁ ϱ) (LevelPair.Hm m₁ ϱ) (compWeight 3 a₁) ν 1 z t.1 t.2.1
        t.2.2‖ ≤
      energyBdScaled 3 3 N (compWeight 3 a₁) 1 (cK2' 3 3 N (famConst 3 3 BG₂ κ) * δ₁) δ₁
        (rho4 3 3 N BG κ) ∧
    energyBdScaled 3 3 N (compWeight 3 a₁) 1 (cK2' 3 3 N (famConst 3 3 BG₂ κ) * δ₁) δ₁
        (rho4 3 3 N BG κ) ≤
      energyBd 3 3 N (compWeight 3 a₁) ν 1 (cK2' 3 3 N (famConst 3 3 BG₂ κ) * δ₁) δ₁
        (rho4 3 3 N BG κ) := by
  refine ⟨blockEnergyFun_bound_scaled hC LevelPair.isLevel_Hm LevelPair.isLevel_Gp le_rfl
    (by norm_num) z ht, ?_⟩
  have hd0 : 0 < 3 := by norm_num
  have hB0 : 0 ≤ famConst 3 3 BG₂ κ := by
    have := famConst_ge_one (L := 3) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' 3 3 N (famConst 3 3 BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 3 3 N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst 3 3 BG κ := by
      have := famConst_ge_one (L := 3) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  exact energyBdScaled_le_energyBd (by norm_num) (by norm_num) hC.HBp.mass hV hρ

end VBlockScaled

end Balaban.Localization
