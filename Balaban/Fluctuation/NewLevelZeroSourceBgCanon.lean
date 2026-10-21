/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelZeroSourceBgFields
public import Balaban.Fluctuation.NewLevelTermsBgAnalytic
public import Balaban.Fluctuation.NewLevelTermsBgLocal
public import Balaban.Fluctuation.InteractionVBlockScaled
public import Balaban.Fluctuation.LocalSetActDomain

/-!
# The zero-source activities recomputed on a background generating set with the canonical transport

P3 Lemma 4.2 at `Gb`, (AE1), for the zero-source activities (route R-LOC, L4-3): the terms of the
block energies recomputed on `Gb` with the canonical transport are analytic and bounded on the chart
of `Gb` (`evDecBg_canon_bound_analytic` at the marks `(1, 0)` for the block energy of a block in the
top layer of `Gb` and the layer `k` of the fluctuation set `H⁻`), hence the zero-source activity of
a domain inside the top layer of `Gb` has the fields of `zeroActBg_fields` with the bound of the
step's potential terms `8 |β| (6 M_ω c₁ M^d |E_sc| / r³) e^{-(2 κ_dec - 1) d^{cov,1}(Y)}`
(`sum_polyDom_rayBound_le`).

* `energyBdScaled_nonneg_of`: the scale-uniform block-energy majorant is nonnegative;
* `blockLayers_of_top`: a site of the top layer of `Gb` lies in the layer `k` of `H⁻` and the layer
  `k + 1` of `Gb`;
* `zeroEvBg_canon_bound_analytic`: the term of one block, bounded by `E_sc e^{-2 κ_dec d̃(Y)}` and
  analytic on the chart of `Gb` times the box;
* `zeroActBg_canon_fields`: the fields of the zero-source activity of a domain in the top layer.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Finset Metric

/-- **The scale-uniform block-energy majorant is nonnegative.** -/
theorem energyBdScaled_nonneg_of {d L N K k : ℕ} [NeZero L] {ϱb a₁ ν BG BG₂ κ δ₁ : ℝ}
    (HB : BgHyp d L K ϱb (compWeight L a₁) ν) (hk1 : 1 ≤ k) (hkK : k ≤ K) (hBG : 0 ≤ BG)
    (hBG₂ : 0 ≤ BG₂) (hδ₁ : 0 < δ₁) :
    0 ≤ energyBdScaled d L N (compWeight L a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
      (rho4 d L N BG κ) := by
  have hd0 : 0 < d := by have := HB.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hBG₂ κ hd0; linarith
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  exact energyBdScaled_nonneg ((HB.weights k hk1 hkK).1.trans' (by norm_num))
    (mul_nonneg (cK2'_nonneg hB0) hδ₁.le) hδ₁.le hρ

section Canon

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}

/-- **The layers of a site of the top layer of `Gb`**: a site of `Ω_{k+1}(Gb)` lies in the layer
`k` of a fluctuation set `H⁻` with `Ω_k(H⁻) = Ω_k(Gb)` and no layer `k + 1`, and in the layer
`k + 1` of `Gb` (the hypothesis `hblk` of `blockEnergyFun_bound_scaled_of_block`). -/
theorem blockLayers_of_top {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} (hk1 : 1 ≤ k) (hdk : Hm.Ω k = Gb.Ω k)
    (hHm : Hm.Ω (k + 1) = ∅) {x : CTorus d L N₁ m₁ (k + 1)} (hx : x ∈ Gb.Ω (k + 1)) :
    (x ∈ Hm.Ω 1 ∧ Hm.layerIndex x = k) ∧ (x ∈ Gb.Ω 1 ∧ Gb.layerIndex x = k + 1) := by
  have hxk : x ∈ Hm.Ω k := by
    rw [hdk]
    exact Gb.Ω_antitone hk1 (Nat.le_succ k) (by omega) hx
  refine ⟨⟨Hm.Ω_antitone le_rfl hk1 (by omega) hxk, Hm.layerIndex_eq hk1 (Nat.le_succ k)
    (Hm.mem_layer.2 ⟨hxk, by rw [hHm]; exact Finset.notMem_empty _⟩)⟩,
    Gb.Ω_antitone le_rfl (by omega) (by omega) hx, Gb.layerIndex_eq (by omega) le_rfl
      (mem_layer_top hx)⟩

variable (S : StepSetting d L N₁ m₁ k N ϱ) {Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb}
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {m₀ : ℕ} {Kc Cx : ℝ}

/-- **The term of one block recomputed on `Gb` with the canonical transport: bound and
analyticity** (`evDecBg_canon_bound_analytic` at the marks `(1, 0)` and the mask `∅`, for the block
energy of a block `z` in the top layer of `Gb` and the layer `k` of `H⁻`, with the block-energy
bound `blockEnergyFun_bound_scaled_of_block`; the block expansions have `d^{cov,1}_j(X) = 0`). -/
theorem zeroEvBg_canon_bound_analytic (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hBG₂ : 0 ≤ BG₂) (hPmp : Precedes Hm Gb)
    (hHm : Hm.Ω (k + 1) = ∅)
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gb N,
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gb) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hcov : CovSetup S.G' m₀ (jV z) (XV z) (𝒦XV z))
    (hX₁ : (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne m₀ (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV z)) E₀ = treeLenCovOne m₀ (jV z) (XV z))
    (hΔ : treeLenCovOne m₀ (jV z) (XV z) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hX₁top : ∀ x ∈ X₁V z, x ∈ Gb.Ω (k + 1))
    (hblk : ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, (x ∈ Hm.Ω 1 ∧ Hm.layerIndex x = k) ∧
      (x ∈ Gb.Ω 1 ∧ Gb.layerIndex x = k + 1))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    (∀ u ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ},
      ‖zeroEvBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol z Y u‖ ≤
        energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ) * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) ∧
    AnalyticOnNhd ℂ (zeroEvBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol z Y)
      (XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) := by
  have hEb0 := energyBdScaled_nonneg_of (N := N) HBb S.hk1 (Nat.le_succ k) hS.fam.2.1 hBG₂ hδ₁0
    (κ := κ)
  have hW1 : (‖(1 : ℂ)‖ + ‖(0 : ℂ)‖) *
      markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁ := by
    rw [norm_one, norm_zero, add_zero, one_mul]
    exact hδ₁c
  obtain ⟨hB, hA⟩ := evDecBg_canon_bound_analytic S S.hk1 ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps
    hsmall hc7 hphi hmarD hαD hsm ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) hcψ hδ₁0 hPmp hHm hF₁an
    hF₁ hSolan hSol hcov hX₁ hopt hκ₀ hκdec hκκ h1 hlog hEb0 (X₁g := X₁V z) (fun x hx => hx)
    hX₁top (Φ := blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z)
    ((blockEnergyFun_analytic (compWeight L S.a₁) S.ν k z).mono (Set.subset_univ _))
    (fun t ht => by
      rw [hΔ, mul_zero, Real.exp_zero, mul_one]
      exact blockEnergyFun_bound_scaled_of_block HBb hS.fam.2.1 hBG₂ hδ₁0 S.hk1 le_rfl z hblk
        ht.1)
    ∅
  refine ⟨fun u hu => (hB Y (u, ((1 : ℂ), (0 : ℂ))) ⟨hu, hW1⟩).trans_eq ?_, fun u hu => ?_⟩
  · rw [hΔ]
    congr 2
    ring
  · have hm : AnalyticAt ℂ (fun v : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts S.G' × Fin N → ℂ) => (v, ((1 : ℂ), (0 : ℂ)))) u :=
      analyticAt_id.prod analyticAt_const
    have h := (hA Y (u, ((1 : ℂ), (0 : ℂ))) ⟨hu, hW1⟩).comp_of_eq hm rfl
    simp only [Function.comp_def] at h
    exact h

open Classical in
/-- **The fields of the zero-source activity recomputed on `Gb` with the canonical transport**
(P3 pp. 78-79, (4.46) and Lemma 4.2 at `Gb`, (AE1)): for a domain `Y` inside the top layer of `Gb`,
blocks `B_{k+1}(z) ⊆ X₁(z)` and the decoupling pairs `F₁`, `Sol` of `Gb` pinned and analytic, the
zero-source activity `zeroActBg … θ u Y Φ` is bounded by
`8 |β| (6 M_ω c₁ M^d |E_sc| / r³) e^{-(2 κ_dec - 1) d^{cov,1}_{k+1}(Y)}` (`M = L^{m₀ + m₁}`, `E_sc`
the scale-uniform block-energy majorant), analytic in `(θ, u)` on `physVBg Gb × {‖u‖ < 2}`,
continuous in the configuration on the chart and measurable in the configuration. -/
theorem zeroActBg_canon_fields (ha₁ : 1 / 2 ≤ S.a₁) (ha₂ : S.a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (Sb : Dec2.CoverBase (coverOf Gb) Gb (compWeight L S.a₁) S.ν Kc Cx)
    (HBb : BgHyp d L (k + 1) ϱb (compWeight L S.a₁) S.ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁) (hBG₂ : 0 ≤ BG₂) (hPmp : Precedes Hm Gb)
    (hdk : Hm.Ω k = Gb.Ω k) (hHm : Hm.Ω (k + 1) = ∅)
    (hδ₁c : markedRad d L N k S.a₁ κ cψ ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) < δ₁)
    {F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ)}
    (hF₁an : ∀ z, AnalyticOnNhd ℂ (F₁ z) {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧
      ∃ D : BgData Gb N, InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D ∧
        q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ z (s : Dec2.DecParams (coverOf Gb)) (D : BgData Gb N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gb (bgC0 d L N) (c7 d L N BG κ) S.ν D → ∀ (φ : Gb.Ω 1 × Fin N → ℂ)
        (α : Gb.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gb) Gb (compWeight L S.a₁) S.ν (rho4 d L N BG κ) s D φ α →
        F₁ z (s, rawOf D) = (φ, α))
    {Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : ∀ z, AnalyticOnNhd ℂ (Sol z) {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ z (p : Dec2.DecParams (coverOf Gb) × Edat Hm N), (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol z p).1 = dphi Hm (Dec2.decG (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1) p.2.2.1
          p.2.1 (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) (Sol z p).2 ∧
        Small Hm (Sol z p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol z p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol z p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gb) Hm (compWeight L S.a₁) S.ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L S.a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol z p).2))
    (hcovV : ∀ z, CovSetup S.G' m₀ (jV z) (XV z) (𝒦XV z))
    (hX₁V : ∀ z, (↑(X₁V z) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV z) (𝒦XV z))
    (hoptV : ∀ z, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV z) ∧ MeetsOne m₀ (jV z) (𝒦XV z) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV z)) E₀ = treeLenCovOne m₀ (jV z) (XV z))
    (hΔV : ∀ z, treeLenCovOne m₀ (jV z) (XV z) = 0)
    (hzX : ∀ z, ∀ x ∈ blockSites d L N₁ m₁ (k + 1) k z, x ∈ X1 S.G' m₀ (jV z) (𝒦XV z))
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (hYtop : ∀ x ∈ Y, x ∈ Gb.Ω (k + 1))
    (ω : ℂ → ℂ) {ρ : ℝ} (hp : 0 < S.p₁)
    {R₁ : ℝ} (hR₁ : 1 < R₁) (hωc : Continuous ω) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r : ℝ} (hr : 0 < r)
    (hrays : ∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b,
      (S.hatOf m₀ ρ hp Φ, S.hatOf m₀ ρ hp Φ) ∈ HatRays (N := N) S.G' cψ R₁ 2 r) :
    (∀ θ u Φ, ‖zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps
        θ u Y Φ‖ ≤
      8 * (|S.β| * ((6 * Mω * c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d *
        ‖energyBdScaled d L N (compWeight L S.a₁) k (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁
          (rho4 d L N BG κ)‖ / r ^ 3) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y)))) ∧
    (∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b, AnalyticOnNhd ℂ
      (fun p : physParamBg N Gb × ℂ =>
        zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps p.1 p.2
          Y Φ)
      (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) 2)) ∧
    (∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < 2 →
      Continuous (zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps
        θ u Y)) ∧
    (∀ θ u, Measurable (zeroActBg S Gb (BgTransport.canon S.G' Gb N) X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp
      eps θ u Y)) := by
  -- the terms of the blocks whose label set contains `Y`
  have hz := fun z (hY : Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z)) =>
    zeroEvBg_canon_bound_analytic S ha₁ ha₂ hS Sb HBb hκ hM hMX hCx heps hsmall hc7 hphi hmarD
      hαD hsm hcψ hδ₁0 hBG₂ hPmp hHm hδ₁c z (hF₁an z) (hF₁ z) (hSolan z) (hSol z) (hcovV z)
      (hX₁V z) (hoptV z) (hΔV z) hκ₀ hκdec hκκ h1 hlog
      (fun x hx => hYtop x (subset_polyDom hY (by rw [← hX₁V z]; exact hx)))
      (fun x hx => blockLayers_of_top S.hk1 hdk hHm (hYtop x (subset_polyDom hY (hzX z x hx))))
      Y
  obtain ⟨hbd, han, hcont, hmeas⟩ := zeroActBg_fields S Gb (BgTransport.canon S.G' Gb N) X₁V jV
    𝒦XV m₀ F₁ Sol ω hp eps Y
    (b := fun _ => ‖energyBdScaled d L N (compWeight L S.a₁) k
      (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
        Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)‖)
    (fun _ => norm_nonneg _) (fun z hY => (hz z hY).2)
    (fun z hY u hu => ((hz z hY).1 u hu).trans (Real.le_norm_self _)) hR₁ hωc hω hMω hωb hr
    hrays (isOpen_physVBg Gb S.a₁ S.ν eps HBb)
  refine ⟨fun θ u Φ => (hbd θ u Φ).trans ?_, han, hcont, hmeas⟩
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (sum_polyDom_rayBound_le S.hG' hcovV HBb.hd hoptV hzX hMω hr Y) (abs_nonneg _))
    (by norm_num)

end Canon

end Balaban.Fluctuation
