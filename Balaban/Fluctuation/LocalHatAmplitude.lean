/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalHatTerm
public import Balaban.Fluctuation.LocalClassAmplitude
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The local hat term as a function of the amplitude

The per-label objects of the local successor class (W811, `LocalHatTerm.lean`) are stated at a fixed
amplitude `cc` of the fluctuation variable `ψ' = cc C^{1/2}(σ w) ψ̂`.  The new contributions at the
level `k + 1` are differences in the amplitude (P4 (2.35), (2.55); FLUCTUATION (3.3)), and their
bounds carry the factor `|cc| / R` (`LocalClassAmplitude.lean`) as soon as the per-label term is
analytic in `cc` on a disc `|cc| < R`.  Since `ψ'` is linear in `ψ̂`,
`cc • (C^{1/2} *ᵥ ψ̂) = 1 • (C^{1/2} *ᵥ (cc • ψ̂))`, so the integrand at amplitude `cc` and hat
variable `ψ̂` is the integrand at amplitude `1` and the complex hat variable `cc • ψ̂`, which lies
in the box of radius `R c_ψ`: the landed analyticity at amplitude `1`
(`fanLocalHat_analytic_cover`, `fanLocalHat_norm_le_cover`, on the larger box) gives the joint
analyticity in the amplitude.

* `fanLocalHat_integral_cover_amp`: the `ψ̂`-integral of the local term is analytic jointly in
  `((Θ, cc), w)` on the chart times the disc `|cc| < R` times the polydisc, and bounded there by
  `B γ(K)`, under `√N R C_cov c_ψ < δ₁` (the hypothesis `hδ₁` of the fixed-amplitude theorem at
  `‖cc‖ = R`).
* `localB_eTermHat_evTerm_amp`: the per-label term of `localB_eTermHat_evTerm_xiFieldDom` as a
  function of the amplitude, on the class domain: complex differentiable in `cc` on `|cc| < R`,
  bounded there by the per-label bound, and the new contribution `T(cc) - T(0)` (the term at the
  fluctuating field minus the term at the background) bounded by `2 · bound · ‖cc‖ / R`
  (`norm_sub_le_of_ball_bound`).

Not covered: the same for the source terms (`localB_mTermHat_*`, the amplitude together with the
source parameter `g`), and the size of `R` against `β_k^{-1/2} |σ|` (the cut-off `c_ψ = p₁(β_k)` of
the fluctuation integral and `δ₁` of `FlSetting`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory

section HatAmplitude

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*} [Fintype ι]

/-- **The `ψ̂`-integral of the local term, jointly analytic in the amplitude** (the per-label object
of `fanLocalHat_integral_cover` with the amplitude `cc` a variable): for `|cc| < R` with
`√N R C_cov c_ψ < δ₁`, the function `((Θ, cc), w) ↦ ∫_K Φ(…, cc C^{1/2}(σ w) ψ̂) dγ(ψ̂)` is
analytic on `Ξ^c(𝔹; 1, ε') × {|cc| < R} × polydisc` and bounded there by `B γ(K)`. -/
theorem fanLocalHat_integral_cover_amp (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {R : ℝ} (hR : 0 < R) {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (R * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf Gp).cubeIdx),
      P ∉ (coverOf Gp).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦ : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    {B : ℝ} (hΦbd : ∀ t ∈ FlRealLC Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁, ‖Φ t.1 t.2.1 t.2.2‖ ≤ B)
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤) :
    AnalyticOnNhd ℂ (fun q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ) × (ι → ℂ) =>
        ∫ ψ in K,
          Φ (F₁ (σ q.2, q.1.1))
        (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1.1)) q.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (q.1.2 • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1.1 (F₁ (σ q.2, q.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (q.1.2 • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1.1 (F₁ (σ q.2, q.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0) ∂γ)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Metric.ball (0 : ℂ) R) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) ∧
    ∀ q ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Metric.ball (0 : ℂ) R) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ),
      ‖∫ ψ in K,
          Φ (F₁ (σ q.2, q.1.1))
        (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1.1)) q.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (q.1.2 • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1.1 (F₁ (σ q.2, q.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (q.1.2 • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1.1 (F₁ (σ q.2, q.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
            else 0) ∂γ‖ ≤
        B * (γ K).toReal := by
  have hRc : 0 ≤ R * cψ := by positivity
  have hδ₁' : Real.sqrt N * (‖(1 : ℂ)‖ * (covSupConstC d L N (compWeight L a₁ k) κ * (R * cψ))) <
      δ₁ := by
    rw [norm_one, one_mul]
    calc Real.sqrt N * (covSupConstC d L N (compWeight L a₁ k) κ * (R * cψ))
        = Real.sqrt N * (R * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) := by ring
      _ < δ₁ := hδ₁
  have hA := fanLocalHat_analytic_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7
    hphi hmarD hαD hsm 1 hRc hδ₁0 hδ₁' hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hΦ
  have hB := fanLocalHat_norm_le_cover hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7
    hphi hmarD hαD hsm 1 hRc hδ₁0 hδ₁' hPmp hHm hF₁ hSol hσκ hσ1 hΦbd
  have hcv : ∀ (c : ℂ), c ∈ Metric.ball (0 : ℂ) R → ∀ v : unitPts Gp × Fin N → ℂ,
      (∀ r, ‖v r‖ ≤ cψ) → ∀ r, ‖(c • v) r‖ ≤ R * cψ := fun c hc v hv r => by
    rw [Pi.smul_apply, smul_eq_mul, norm_mul]
    exact mul_le_mul (le_of_lt (mem_ball_zero_iff.1 hc)) (hv r) (norm_nonneg _) hR.le
  refine analyticOnNhd_setIntegral_compact
    (P := (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ) × (ι → ℂ))
    (F := fun (q : (RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ) × (ι → ℂ))
      (v : unitPts Gp × Fin N → ℂ) =>
        Φ (F₁ (σ q.2, q.1.1))
        (Sol (σ q.2, flEdat Gp Hm (F₁ (σ q.2, q.1.1)) q.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (q.1.2 • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1.1 (F₁ (σ q.2, q.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ v)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (q.1.2 • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ q.2, q.1.1)).2
                (Dec2.extS (coverOf Gp) (σ q.2)) (barField Gp q.1.1.1 (F₁ (σ q.2, q.1.1)).1)
                (unitQ Gp) (unitP Gp) *ᵥ v)) (⟨unitBlock x, h⟩, i)
            else 0)) hKc hKb hγ ?_ ?_
  · rintro ⟨⟨Θ, c⟩, w⟩ ⟨⟨hΘ, hc⟩, hw⟩ v hv
    have h := hA ((Θ, c • v), w) ⟨⟨hΘ, hcv c hc v hv⟩, hw⟩
    have hφ : AnalyticAt ℂ (fun x : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ) × (ι → ℂ)) ×
        (unitPts Gp × Fin N → ℂ) => ((x.1.1.1, x.1.1.2 • x.2), x.1.2)) (((Θ, c), w), v) :=
      ((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod
        ((analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst)).smul analyticAt_snd)).prod
        (analyticAt_snd.comp analyticAt_fst)
    refine (h.comp_of_eq hφ rfl).congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp, Matrix.mulVec_smul, one_smul]
  · rintro ⟨⟨Θ, c⟩, w⟩ ⟨⟨hΘ, hc⟩, hw⟩ v hv
    have h := hB ((Θ, c • v), w) ⟨⟨hΘ, hcv c hc v hv⟩, hw⟩
    simp only [Matrix.mulVec_smul, one_smul] at h
    exact h

end HatAmplitude

section HatAmplitudeLocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}

/-- **The per-label term of the E-part on `𝔹 = localB t … Y⁺` as a function of the amplitude, and
the amplitude bound of its difference** (decision D3(b); FLUCTUATION (3.3), Proposition 3.3: the
factor `β_k^{-1/2} |σ| r⁻¹`).  `T c p` is the term of the polymer `Y` of
`localB_eTermHat_evTerm_xiFieldDom` at the amplitude `c` of the fluctuation variable
`ψ' = c C^{1/2}(σ w) ψ̂` (for a fixed `c` it is that per-label term), read on the class domain
through the cut-off `clipRaw 𝔹`.  Under `√N R C_cov c_ψ < δ₁` (the hypothesis `hδ₁` of the
fixed-amplitude theorem at `‖c‖ = R`), on the class domain:
* `c ↦ T c p` is complex differentiable on the disc `|c| < R`;
* `‖T c p‖ ≤ Eb γ(K) e^{-κ₀ d^{cov,1}_j(X) - 2 κ_dec d̃^{cov}(Y)}` there (the per-label bound);
* **the new contribution** `T cc p - T 0 p` (the term at the fluctuating field minus the term at
  the background) is bounded by `2 Eb γ(K) e^{…} ‖cc‖ / R`. -/
theorem localB_eTermHat_evTerm_amp {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))} (hcov : CovSetup Ga m₀ j' X 𝒦X)
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga) (hcinj : Function.Injective cI)
    (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec) (hEb0 : 0 ≤ Eb)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ} (ht : t ≤ k + 1)
    (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
    (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)
    (hP : Precedes Gk (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) (hq : Precedes Gj Gk)
    (colk : ∀ z ∈ collar Gk, z ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1)
      (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
    (hN : ∀ x ∈ X₀, x ∈ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 →
      ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
        (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (GsSpec.localB t ht Yp (le_refl (minSep L
          (L ^ m₁)))).spacing x → y ∈ X₁f)
    {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB t ht Yp (le_refl (minSep L
      (L ^ m₁)))) Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
    (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
      InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
    (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
      Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
        bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → ℂ}
    (hE : AnalyticOnNhd ℂ E (XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl)))
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {R : ℝ} (hR : 0 < R) {cψ : ℝ}
    (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (R * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData
      (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N,
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))))
      (D : BgData (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s P‖
        < Real.exp κ) →
      InUnionDomainC (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N)
        (c7 d L N BG κ) ν D → ∀ (φ : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1
          × Fin N → ℂ)
        (α : (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν
            (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
      × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
          (L ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
      (L ^ m₁)))))} (hσan : ∀ w, AnalyticAt ℂ σ w)
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf (GsSpec.localB t ht Yp
      (le_refl (minSep L (L ^ m₁))))).cubeIdx),
      P ∉ (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))).parCubes X₁f
        → σ w ⟨P, hP⟩ = 1)
    {γ : Measure (unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
      {K : Set (unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl),
        ‖E r‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (T : ℂ → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ c p, T c p =
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X)
          (fun (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ) (w : ι → ℂ) =>
          ∫ ψ in K,
            eTermFun (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Gk Gj Hm
              (compWeight L a₁) Fk E (F₁ (σ w, u.1))
        (Sol (σ w, flEdat (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σ w, u.1))
          u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (u.2 • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) u.1.1 (F₁
                  (σ w, u.1)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) then
              (u.2 • (decCovSqrt (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))
                (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf (GsSpec.localB t ht Yp (le_refl (minSep L
                  (L ^ m₁))))) (σ w))
                (barField (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) u.1.1 (F₁
                  (σ w, u.1)).1) (unitQ (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))))
                    (unitP (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r =>
                      (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) Y (clipRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) p, c)) :
    (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      DifferentiableOn ℂ (fun c => T c p) (Metric.ball (0 : ℂ) R)) ∧
    (∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ∀ c ∈ Metric.ball (0 : ℂ) R, ‖T c p‖ ≤ Eb * (γ K).toReal *
          Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y)) ∧
    ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ∀ cc : ℂ, ‖cc‖ < R → ‖T cc p - T 0 p‖ ≤
        2 * (Eb * (γ K).toReal *
          Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y)) * ‖cc‖ / R := by
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  obtain ⟨hA, hB⟩ := fanLocalHat_integral_cover_amp hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX
    (Cchi_nonneg d L) hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm hR hcψ
    hF.num.δ₁_pos hδ₁ hF.hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1
    (localB_eTermFun_analytic hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq colk colj hκ hM
      hnum dsX₀ hN hj hF hFkan hFk hE)
    (fun _ ht' => localB_eTermFun_bound hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq colk
      colj hκ hM hnum dsX₀ hN hj hF hFk hEb ht') hKc hKb hγ
  have hγ0 : 0 ≤ (γ K).toReal := ENNReal.toReal_nonneg
  have hEv := evTerm_bound_analyticOnNhd_of_bd (c := cI)
    (U := RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ)
    hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hκκ h1 hlog (mul_nonneg hEb0 hγ0) hA
    (fun u hu s hs => by
      have := hB (u, s) ⟨hu, hs⟩
      rw [mul_right_comm]
      exact this)
  have hmem : ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ∀ c ∈ Metric.ball (0 : ℂ) R,
        ((clipRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) p, c) :
          RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ) ∈
        XiCRaw (GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (k + 1)
          1 eps ×ˢ Metric.ball (0 : ℂ) R :=
    fun p hp c hc => ⟨clipRaw_mem_xiCRaw_of_xiDom hεseq hp, hc⟩
  have hdiff : ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      DifferentiableOn ℂ (fun c => T c p) (Metric.ball (0 : ℂ) R) := by
    intro p hp
    have han : AnalyticOnNhd ℂ (fun c => T c p) (Metric.ball (0 : ℂ) R) := by
      intro c hc
      simp only [hT]
      exact ((hEv.2 Y) _ (hmem p hp c hc)).comp_of_eq (analyticAt_const.prod analyticAt_id) rfl
    exact han.differentiableOn
  have hbd : ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB t ht Yp
          (le_refl (minSep L (L ^ m₁)))) p.1 p.2 →
      ∀ c ∈ Metric.ball (0 : ℂ) R, ‖T c p‖ ≤ Eb * (γ K).toReal *
          Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y) := by
    intro p hp c hc
    rw [hT]
    exact hEv.1 Y _ (hmem p hp c hc)
  exact ⟨hdiff, hbd, fun p hp cc hcc => norm_sub_le_of_ball_bound hR (hdiff p hp) (hbd p hp) hcc⟩

end HatAmplitudeLocalB

end Balaban.Localization
