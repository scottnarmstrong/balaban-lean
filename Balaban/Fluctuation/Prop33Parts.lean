/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Interaction
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The localized terms with their label sets exposed (Proposition 3.3)

`interaction_expansion` hides the label sets `𝒴` of its expansions behind an existential.  For the
volume-uniform bound of the terms (`Prop33.lean`) the label sets are needed: the terms of the
block `z` are labelled by the polymer domains `Y[𝒞] ⊇ X₁(z)`, so only the blocks in `Y` contribute.

* `polyDom`: the label set `{Y[𝒞]}` of one term (`polymerDomains` of the cover `Pset`);
* `vpart_locInt_dom`: `vpart_locInt` with the label sets `polyDom` of the blocks;
* `fsite_base_locInt`: the amplitude-free expansion of one site of `⟨g, δφ⟩`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation Finset
  Matrix Set Metric

section Parts

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {Hm : GeneratingSet d L (N₁ * L ^ m₁) K ϱm}
variable {n : ℕ} {ν : ℝ}

open Classical in
/-- The label set `{Y[𝒞]}` of the expansion of a term with cover data `(m₀, j, 𝒦X)`:
the polymer domains of the connected families of the cubes disjoint from `X₁`. -/
noncomputable abbrev polyDom (Gp : GeneratingSet d L (N₁ * L ^ m₁) K ϱ)
    (X₁f : Finset (CTorus d L N₁ m₁ K)) (m₀ j : ℕ) (𝒦X : Set (CTorus d L N₁ m₁ K)) :
    Finset (Set (CTorus d L N₁ m₁ K)) :=
  polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
    (X1 Gp m₀ j 𝒦X)

variable {a₁ c BG κ eps Kc' Cx' c₂ BG₂ δ₁ : ℝ}

/-- **The potential part of the localized interaction with its label sets exposed**: as
`vpart_locInt`, with the label set of the block `z` the set `polyDom` of its cover. -/
theorem vpart_locInt_dom (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc' Cx' c₂ BG₂ δ₁)
    (hG : IsLevel Hm n) (hG' : IsLevel Gp (n + 1)) (hp : n + 1 ≤ K) (ha₁ : 0 < a₁)
    (H : BgHyp d L K ϱm (compWeight L a₁) ν) (hc7 : c7 d L N BG κ ≤ thm73C3 d L N)
    {R : ℝ} (hR : 2 ≤ R) (hRs : R * δ₁ ≤ deltaStar d L N)
    (hsmall : cK2 d L N * (R * δ₁) < bgC0 d L N / 2)
    (hnum : cK2 d L N * δ₁ ≤ c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hnum' : cK2' d L N (famConst d L BG₂ κ) * δ₁ ≤
      c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hreal : ∀ D' : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D' →
      ∀ ψ' ∈ FlBall Hm δ₁, IsLayerConstant Hm ψ' → ∃ D : BgData Hm N,
      (∀ x i, D.h x i = D'.h x i) ∧
      compTangent hG hG' hp (compWeight L a₁)
        (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D' D = ψ' ∧
      ∀ t : ℂ, ‖t‖ < R → InUnionDomainC Hm (bgC0 d L N) (bgC1 d L N) ν
        ((composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
          (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
            (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
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
    (hn1 : 1 ≤ n) (hZ : ∀ z, readSites Hm n z ⊆ ↑(X₁f z))
    (hmar : ∀ z, BlockMargin Gp (X₁f z) (↑(blockSites d L N₁ m₁ K n z) : Set (CTorus d L N₁ m₁ K)))
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :    ∃ (T : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))) → Set (CTorus d L N₁ m₁ K) →
        (CTorus d L N₁ m₁ K → Fin N → ℂ) → (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ →
        RawData d L (N₁ * L ^ m₁) K N → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          (∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁) ∧
          IsLayerConstant Hm xw.1 ∧ IsLayerConstant Hm xw.2} Rσ
        (Finset.univ.biUnion fun z => polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z))
        (fun Y x₀ w σ Θ => ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          T z Y x₀ w σ Θ else 0)
        (fun x₀ w σ Θ => raySrc3 (interactionOne hG hG' hp a₁ ν eps) ω x₀ w σ Θ)
        (fun Y => ∑ z, if Y ∈ polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z) then
          Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3) else 0)
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  have hexb : ∀ z, ∃ (Evb : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polyDom Gp (X₁f z) (m₀ z) (j z) (𝒦X z))
        (fun Y x₀ w σ Θ => rayTerm (dl3 (Evb Y) w) ω x₀ σ Θ)
        (fun x₀ w σ Θ => raySrc3 (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) ω x₀ w σ Θ)
        (fun Y => Mω * (6 * ‖energyBd d L N (compWeight L a₁) ν n
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp (m₀ z) Y)‖ / r ^ 3))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := fun z =>
    vblock_locInt hC (hcov z) (hX₁ z) hconn hrow (hopt z) (hΔ z) hκ₀ hκdec hκ h1 (hlog z) hn1 hp z
      (hZ z) (hmar z) hωc hR₁ hω hMω hωb hr
  choose Evb hEvb using hexb
  have hL := LocInt.finsum Finset.univ (fun z _ => hEvb z)
  have hex : ∀ z : Torus d (N₁ * L ^ m₁ * L ^ (K - (n + 1))), ∃ (Ev : Set (CTorus d L N₁ m₁ K) →
      RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ),
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν K 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock Gp Hm (compWeight L a₁) ν n (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') ψ' z =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
          (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z)), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y) (XiCRaw Gp (compWeight L a₁) ν K 1 eps ×ˢ FlBall Hm δ₁)) := by
    intro z
    obtain ⟨Ev, h1', -, -, h4'⟩ := vblock_expansion hC (hcov z) (hX₁ z) hconn hrow (hopt z) (hΔ z)
      hκ₀ hκdec hκ h1 (hlog z) hn1 hp z (hZ z) (hmar z)
    exact ⟨Ev, h1', h4'⟩
  choose Ev hEvsum hEvan using hex
  refine ⟨fun z Y x₀ w σ Θ => rayTerm (dl3 (Evb z Y) w) ω x₀ σ Θ,
    (hL.mono_XW (fun xw hxw => hxw.1)).congr_val ?_⟩
  rintro ⟨x₀, w⟩ ⟨hxw, hx0, hw⟩ σ hσ Θ ⟨D', hD, rfl⟩
  have hreal1 : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖(t : ℂ)‖ < R₁ := fun t ht => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]; linarith [ht.2]
  have hdisc : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * (t : ℂ)) • x₀ + τ • w ∈ FlBall Hm δ₁ := fun t ht τ hτ => hxw σ hσ t (hreal1 t ht) τ hτ
  have hint : ∀ z, IntervalIntegrable (fun t : ℝ => ω (t : ℂ) * dirS3
      (blockEnergyOne Gp Hm a₁ ν BG₂ κ eps n z) w (rawOf D') ((σ * (t : ℂ)) • x₀))
      MeasureTheory.volume 0 1 := by
    intro z
    refine raySrc3_intervalIntegrable (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps)
      (B := FlBall Hm δ₁)
      (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
        (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z))) (Evs := Ev z) (fun Y => hEvan z Y) ?_ hωc
      ⟨D', hD, rfl⟩ hr hdisc
    intro Θ hΘ ψ' hψ
    obtain ⟨D'', hD'', rfl⟩ := hΘ
    rw [blockEnergyOne_rawOf hD'']
    exact hEvsum z D'' hD'' ψ' hψ
  unfold raySrc3
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun z _ => hint z)]
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [Set.uIcc_of_le zero_le_one] at ht
  simp only
  rw [← Finset.mul_sum]
  congr 1
  refine dirS3_interactionOne hC hG hG' hp ha₁ H hc7 hR hRs hsmall hnum hnum' hD
    (hreal D' hD) (isLayerConstant_smul hx0 _) hw hr (fun τ hτ => hdisc t ht τ hτ.le) ?_
  intro z
  refine contDiffAt_line_of_sum (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (polymerDomains (fun i : ParIdx Gp (↑(X₁f z) : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp
      (m₀ z) (X1 Gp (m₀ z) (j z) (𝒦X z))) (Evs := Ev z) (fun Y => hEvan z Y) ?_ ⟨D', hD, rfl⟩ hr (fun τ hτ => hdisc t ht τ hτ)
  intro Θ hΘ ψ' hψ
  obtain ⟨D'', hD'', rfl⟩ := hΘ
  rw [blockEnergyOne_rawOf hD'']
  exact hEvsum z D'' hD'' ψ' hψ

variable {Kc Cx : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ K)} {j m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ K)}

/-- **The amplitude-free expansion of one site of `⟨g, δφ⟩`** (the base of `fsite_locInt`). -/
theorem fsite_base_locInt (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
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
    (y : CTorus d L N₁ m₁ K) (hy : y ∈ X₁f) (i : Fin N)
    {ω : ℂ → ℂ} (hωc : Continuous ω) {R₁ : ℝ} (hR₁ : 1 < R₁)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) {Mω : ℝ} (hMω : 0 ≤ Mω)
    (hωb : ∀ t : ℝ, t ∈ Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω) {r Rσ : ℝ} (hr : 0 < r) :
    ∃ Ev : Set (CTorus d L N₁ m₁ K) →
        RawData d L (N₁ * L ^ m₁) K N × (CTorus d L N₁ m₁ K → Fin N → ℂ) → ℂ,
      LocInt (XiCRaw Gp (compWeight L a₁) ν K 1 eps)
        {xw : (CTorus d L N₁ m₁ K → Fin N → ℂ) × (CTorus d L N₁ m₁ K → Fin N → ℂ) |
          ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
            (σ * t) • xw.1 + τ • xw.2 ∈ FlBall Hm δ₁} Rσ
        (polyDom Gp X₁f m₀ j 𝒦X)
        (fun Y x₀ w σ Θ => dirTerm (Ev Y) ω x₀ w σ Θ)
        (fun x₀ w σ Θ => dirTermSrc (onXi Gp a₁ ν eps
          (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i)) ω x₀ w σ Θ)
        (fun Y => Mω * (((cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) / r))
        (fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
        (fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) := by
  classical
  obtain ⟨Ev, hsum, hloc, hbd, hanY⟩ := fsite_expansion hC hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ
    h1 hlog y hy i
  refine ⟨Ev, ?_⟩
  have hbase := locInt_dir1 (S := XiCRaw Gp (compWeight L a₁) ν K 1 eps) (B := FlBall Hm δ₁)
    (f := onXi Gp a₁ ν eps (fun D ψ' => svec Hm (flFieldOne Gp Hm BG₂ κ a₁ ν D ψ') y i))
    (polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ K)) => i.1.1) Gp m₀
      (X1 Gp m₀ j 𝒦X)) (Evs := Ev)
    (b := fun Y => (cK2' d L N (famConst d L BG₂ κ) * δ₁) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y))
    (AgΘ := fun Y Θ Θ' => agreeOn (thickSet Gp Y) Θ Θ')
    (AgF := fun Y z z' => ∀ y ∈ psiThick Y, z y = z' y) (Rσ := Rσ) hR₁ hω hωc hMω hωb hr
    (isOpen_flBall (N := N) Hm δ₁) hanY (fun Y u hu => hbd Y u hu)
    (fun Y a a' c' c'' p q ha hb y hy => by simp [ha y hy, hb y hy])
    (fun Y Θ hΘ Θ' hΘ' z hz z' hz' h1' h2' => hloc Y (Θ, z) ⟨hΘ, hz⟩ (Θ', z') ⟨hΘ', hz'⟩ h1' h2')
    (fun Θ hΘ ψ' hψ => by
      obtain ⟨D, hD, rfl⟩ := hΘ
      rw [onXi_rawOf hD]
      exact hsum D hD ψ' hψ)
  exact hbase

end Parts

end Balaban.Localization
