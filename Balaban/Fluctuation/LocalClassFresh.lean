/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassMRot
public import Balaban.Fluctuation.LocalClassLocal
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Locality and completion of the fresh source term on the local chart

The fresh source term of P3 (4.46) for a site `y` and a component `i` is the term `E_X(Y)` of the
localization expansion for the `ψ̂`-integral of the site functional `siteFun Gp Hm y i = δφ(y, i)`
(`localB_freshTermHat_evTerm_xiFieldDom`).  The functional reads the fluctuation field `δφ` of the
pair `(coverOf 𝔹, 𝔹⁻)` at the single site `y`, so its locality on the chart is the field part of
the comparison already used for the old terms:

* `localHat_fields_congr` (`LocalClassLocal.lean`): the core shared with `eTermFun_localHat_congr`.
  For two data of the chart agreeing on a set `W` containing the thickened interaction cube of every
  cube with non-vanishing parameter, the decoupled background fields agree on the active interaction
  cubes and the fluctuation fields `δφ` agree at every site;
* `freshSite_localHat_congr`: the integrand at one point;
* `evTerm_freshLocalHat_congr`, `evTerm_freshLocalHat_clipRaw_congr`: the term of `Y` (chart, class
  domain);
* `localB_freshTermHat_evTerm_local`: at `𝔹 = 𝔹_{k+1}(Y⁺)`, with the two properties `hσ0`, `hσY` of
  the parameter map used for the old terms.  No hypothesis on the data sites of `𝔹_k(X)` is needed:
  the fresh term has no composition;
* `localB_freshSource_evTerm_local`: the source term `∑_i g(y, i) T_i` with the source.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory

section Same

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ}

variable (hk1 : 1 ≤ k) (hL2 : 2 ≤ L) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    {c BG : ℝ} (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {F₁ : Dec2.DecParams (coverOf Gp) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf Gp)) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf Gp) Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Kc₂ Cx₂ c₂ BG₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm (compWeight L a₁) ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δ₁ : ℝ} (hδ₁0 : 0 < δ₁)
    (hB : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁ : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
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
    (hPmp : Precedes Hm Gp) (hHm : Hm.Ω (k + 1) = ∅) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁c : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)

include hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁ hSol hPmp hHm hcψ hδ₁c

/-- **Exact locality of the fresh integrand at one point.**  Under the hypotheses of
`localHat_fields_congr`, for two data `D`, `D'` of the chart `Ξ^c(𝔹; 1, ε)` with the same raw values
on `W` and every hat variable `ψ̂` with `|ψ̂| ≤ c_ψ`, the site functional `δφ(y, i)` at the
decoupled background, the fluctuation field and `(Θ, ψ'(Θ))` takes the same value at `Θ = D` and
`Θ = D'`.  The site `y` is arbitrary. -/
theorem freshSite_localHat_congr {s : Dec2.DecParams (coverOf Gp)} (hs : ∀ P, ‖s P‖ < Real.exp κ)
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hact : ∀ q ∈ (coverOf Gp).cubeIdx,
      (coverOf Gp).sProd (Dec2.extS (coverOf Gp) s) q ≠ 0 →
        ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y → y ∈ W ∧ y ∈ Gp.Ω (k + 1))
    {D D' : BgData Gp N} (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D)
    (hD' : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D')
    (hDD : ∀ z ∈ W, D.Ψ z = D'.Ψ z ∧ D.h z = D'.h z)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) :
    siteFun Gp Hm y i (F₁ (s, rawOf D))
        (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D)) (rawOf D).1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D).1 (F₁ (s, rawOf D)).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (rawOf D, (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D)).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D).1 (F₁ (s, rawOf D)).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0)) =
    siteFun Gp Hm y i (F₁ (s, rawOf D'))
        (Sol (s, flEdat Gp Hm (F₁ (s, rawOf D')) (rawOf D').1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D')).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D').1 (F₁ (s, rawOf D')).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0))).1
        (rawOf D', (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts Gp then
              (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (s, rawOf D')).2
                (Dec2.extS (coverOf Gp) s) (barField Gp (rawOf D').1 (F₁ (s, rawOf D')).1)
                (unitQ Gp) (unitP Gp) *ᵥ ψh)) (⟨unitBlock x, h⟩, i)
            else 0)) := by
  have h := (localHat_fields_congr hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁ hSol hPmp hHm cc hcψ hδ₁c hs hact hD hD' hDD hψh).2.1 y
  exact congrFun h i

/-- **Exact locality of the fresh term on the chart.**  The term of `Y` for the site functional
`δφ(y, i)` (the `ψ̂`-integral of `siteFun`) takes the same value at two raw data of the chart
`Ξ^c(𝔹; 1, ε)` agreeing on `W`, provided that for every connected family `𝒞` with `Y[𝒞] = Y` and
every `w` supported on `𝒞` in the polydisc the hypothesis `hact` of `localHat_fields_congr` holds
at `σ w`.  (`evTerm_localHat_congr` for the site functional; no hypothesis `hcomp`.) -/
theorem evTerm_freshLocalHat_congr
    {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hact : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y → y ∈ W ∧ y ∈ Gp.Ω (k + 1))
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Gi : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGi : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gi Θ w =
      ∫ ψ in K, siteFun Gp Hm y i (F₁ (σ w, Θ))
              (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
                (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
              (Θ, (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0)) ∂γ)
    {u u' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hu : u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (hu' : u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)
    (huu : ∀ z ∈ W, u.1 z = u'.1 z ∧ u.2 z = u'.2 z) :
    evTerm cI Ga m₀ X₁ Gi Y u = evTerm cI Ga m₀ X₁ Gi Y u' := by
  classical
  obtain ⟨D, hD, rfl⟩ := hu
  obtain ⟨D', hD', rfl⟩ := hu'
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hκ
  unfold evTerm
  refine Finset.sum_congr rfl fun C hC => coef_congr_near hE1 fun w hw => ?_
  have hwp : w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := fun i => by simpa using hw.2 i
  rw [hGi, hGi]
  refine setIntegral_congr_fun hKc.isClosed.measurableSet fun ψ hψ => ?_
  exact freshSite_localHat_congr hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁ hSol hPmp hHm cc hcψ hδ₁c (hσκ w hwp) (hact C hC w hw) hD hD' huu
    (fun r => by simpa using hKb ψ hψ r) y i

/-- **Exact locality of the fresh term on the class domain.**  `evTerm_freshLocalHat_congr` read
through the cut-off `clipRaw 𝔹` on the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` (`xiFieldDom`,
`ε_{k+1} ≤ ε`): two pairs of fields of the domain with the same values on `W` give equal terms. -/
theorem evTerm_freshLocalHat_clipRaw_congr
    {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf Gp)}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    {W : Set (CTorus d L N₁ m₁ (k + 1))}
    (hact : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        ∀ y, InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y → y ∈ W ∧ y ∈ Gp.Ω (k + 1))
    {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Gi : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGi : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gi Θ w =
      ∫ ψ in K, siteFun Gp Hm y i (F₁ (σ w, Θ))
              (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
                (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
              (Θ, (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0)) ∂γ)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    {p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp
      p.1 p.2)
    (hp' : (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp
      p'.1 p'.2)
    (hpp : ∀ z ∈ W, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) :
    evTerm cI Ga m₀ X₁ Gi Y (clipRaw Gp p) = evTerm cI Ga m₀ X₁ Gi Y (clipRaw Gp p') := by
  classical
  refine evTerm_freshLocalHat_congr hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁ hSol hPmp hHm cc hcψ hδ₁c Y hσκ hact hKc hKb y i Gi hGi
    (clipRaw_mem_xiCRaw_of_xiDom hεseq hp) (clipRaw_mem_xiCRaw_of_xiDom hεseq hp')
    fun z hz => ⟨funext fun i => ?_, funext fun i => ?_⟩
  · show (if z ∈ dataSites Gp then p.1 z i else 0) = (if z ∈ dataSites Gp then p'.1 z i else 0)
    rw [(hpp z hz).1]
  · show (if z ∈ Gp.Ω 1 then p.2 z i else 0) = (if z ∈ Gp.Ω 1 then p'.2 z i else 0)
    rw [(hpp z hz).2]

end Same

section LocalB

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **Exact locality of the fresh term at `𝔹_{k+1}(Y⁺)`** (P3 (4.47) for the source term; the
analogue of `localB_eTermHat_evTerm_local`).  The term of the polymer `Y` for the site functional
`δφ(y, i)` recomputed on `𝔹 = 𝔹_{k+1}(Y⁺) = localB (k + 1) … Y⁺` takes the same value at two pairs of
fields of the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})` that agree on `Y`.  The hypotheses are those
of `localB_freshTermHat_evTerm_xiFieldDom` used by the construction, and the two properties of the
parameter map `σ` used for the old terms: it vanishes at the cubes of the cover of `𝔹` off the top
layer (`hσ0`), and for a connected family `𝒞` with `Y[𝒞] = Y` and `w` supported on `𝒞` the cubes
with `(σ w)_P ≠ 0` lie in `Y` (`hσY`).  The reading of the functional is a single site, so there is
no hypothesis on data sites. -/
theorem localB_freshTermHat_evTerm_local {ι : Type*} [DecidableEq ι] [Fintype ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hk1 : 1 ≤ k) (hk : k + 1 ≤ k + 1) (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁)
    (hMM : 4 * L ^ 2 ≤ L ^ m₁)
    (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG a₁ ν : ℝ}
    (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG)
    (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
    (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
    {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
    {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
    (hF : FlSetting N (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Gk Hm a₁ ν κ BG
      eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
    (hHm : Hm.Ω (k + 1) = ∅)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
    {F₁ : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
      RawData d L (N₁ * L ^ m₁) (k + 1) N →
      ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) ×
        ((GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ)}
    (hF₁ : ∀ (s : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^
      m₁)))))) (D : BgData (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) N), (∀ P, ‖s
        P‖ < Real.exp κ) →
      InUnionDomainC (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (bgC0 d L N) (c7 d
        L N BG κ) ν D →
      ∀ (φ : (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 × Fin N → ℂ) (α :
        (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω 1 → ℂ),
        Dec2.IsDecBg (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))))
          (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) ν (rho4 d L
            N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) ×
      Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSol : ∀ p : Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^
      m₁))))) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L
          ^ m₁))))) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm
          (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) Hm
            (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
    {σ : (ι → ℂ) → Dec2.DecParams (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^
      m₁)))))}
    (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
    (hσ0 : ∀ w, ∀ P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^
      m₁))))).cubeIdx, P.2 ∉ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))).Ω (k + 1) →
      Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ X₁ Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))).cubeIdx,
        Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σ w) P ≠ 0
          →
        ∀ y, SameCell (L ^ (P.1 + m₁)) y P.2 → y ∈ Y)
    {γ : Measure (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
      {K : Set (unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) × Fin N → ℝ)}
    (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    {p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N}
    (hp : (xiFieldDom (compWeight L a₁) ν εseq :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB (k + 1) hk Yp
        (le_refl (minSep L (L ^ m₁)))) p.1 p.2)
    (hp' : (xiFieldDom (compWeight L a₁) ν εseq :
      FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) (GsSpec.localB (k + 1) hk Yp
        (le_refl (minSep L (L ^ m₁)))) p'.1 p'.2)
    (hpp : ∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z)
    (y : CTorus d L N₁ m₁ (k + 1)) (i : Fin N)
    (Gi : RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGi : ∀ (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gi Θ w =
      ∫ ψ in K,
        siteFun (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Hm y i (F₁ (σ w, Θ))
          (Sol (σ w, flEdat (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                    (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σ w))
                      (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0))).1
          (Θ, (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
                  if h : unitBlock x ∈ unitPts (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) then
                    (cc • (decCovSqrt (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                      (Dec2.extS (coverOf (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (σ w))
                      (barField (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) Θ.1 (F₁ (σ w, Θ)).1)
                      (unitQ (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) (unitP (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁))))) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
                  else 0)) ∂γ) :
    evTerm cI Ga m₀ X₁ Gi Y (clipRaw (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p) =
      evTerm cI Ga m₀ X₁ Gi Y (clipRaw (GsSpec.localB (k + 1) hk Yp (le_refl (minSep L (L ^ m₁)))) p') := by
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hcd := localB_coverData hk Yp hN₁ hMM hag HBp
  exact evTerm_freshLocalHat_clipRaw_congr hk1 (by omega) ha₁ ha₂ hS hcd.1 HBp hκ hM hMX
    (Cchi_nonneg d L) hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm hF₁
    hF.hS2.fam hF.SM.toCoverBase hF.hM2 hF.num.δ₁_pos hF.num.B_le hF.num.δ₁_le hSol hF.hPmp hHm
    cc hcψ hδ₁ Y hσκ
    (fun C hC w hw => localB_active_hatBox_subset hk1 hk Yp hm₁ hMM (hσ0 w) (hσY C hC w hw))
    hKc hKb y i Gi hGi hεseq hp hp' hpp

end LocalB

section FreshExt

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset Matrix MeasureTheory

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν Kc Cx : ℝ} {ι : Type*} [Fintype ι]
variable (hk1 : 1 ≤ k) (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2) {c BG : ℝ}
    (hS : Dec2.DecSpecs d L Kc Cx c BG)
    (S : Dec2.CoverBase (coverOf Gp) Gp (compWeight L a₁) ν Kc Cx)
    (HBp : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {κ eps : ℝ} (hκ : 0 < κ)
    (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hMX : Dec2.cstarX d L Cx * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) (hCx : 0 ≤ Cx)
    (heps : 0 < eps) (hsmall : (4 * d + 6) * ((2 * d + 1) * eps) ≤ 1)
    (hc7 : xiC1 d * eps ≤ c7 d L N BG κ) (hphi : (3 + K4 d L N BG κ) * (xiC1 d * eps) < 1 / 2)
    {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {δ₁ BG₂ : ℝ} (hδ₁0 : 0 < δ₁)
    (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
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
  {γ : Measure (unitPts Gp × Fin N → ℝ)} {K : Set (unitPts Gp × Fin N → ℝ)}
  (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)

include hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD hsm hcψ hδ₁0 hδ₁ hPmp
  hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ

theorem freshTermHat_evTerm_ext [DecidableEq ι] {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Ga m₀ j' X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga)
    (hcinj : Function.Injective cI) (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
    (hΔ : treeLenCovOne m₀ j' X = 0) (hBG₂ : 0 ≤ BG₂)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (hL2 : 2 ≤ L) {Kc₂ Cx₂ c₂ : ℝ} (hF₂ : Dec2.FamSpec d L Kc₂ Cx₂ c₂ BG₂)
    (Sf : Dec2.CoverBase (coverOf Gp) Hm (compWeight L a₁) ν Kc₂ Cx₂)
    (hM₂ : c₂ * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hB : 2 * (K4 d L N BG κ * (xiC1 d * eps)) ≤
      deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (hδ₁le : δ₁ ≤ deltaStar' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X1 Ga m₀ j' 𝒦X)
    (Gi : Fin N → RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGi : ∀ (l : Fin N) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gi l Θ w =
      ∫ ψ in K,
        siteFun Gp Hm y l (F₁ (σ w, Θ))
          (Sol (σ w, flEdat Gp Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts Gp then
                (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf Gp) (σ w)) (barField Gp Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ Gp) (unitP Gp) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0)) ∂γ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hact : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ q ∈ (coverOf Gp).cubeIdx, (coverOf Gp).sProd (Dec2.extS (coverOf Gp) (σ w)) q ≠ 0 →
        ∀ y', InBox m₁ q.1 q.2 (hatRad L m₁ q.1) y' → y' ∈ Y ∧ y' ∈ Gp.Ω (k + 1))
    (T : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ p, T p = ∑ l, p.2 y l *
      evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Gi l) Y (clipRaw Gp p.1))
    (cpl : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N →
      Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ p, cpl p = Classical.epsilon (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) Gp Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) Gp Y) p).2 z)) :
    (∀ Ψ Ψ' h h' g g' : Fld d L N₁ m₁ (k + 1) N,
      (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x ∧ g x = g' x) → T (cpl (Ψ, h), g) = T (cpl (Ψ', h'), g')) ∧
    (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p.1 p.2 → T (cpl p, g) = T (p, g)) ∧
    AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) ×
        Fld d L N₁ m₁ (k + 1) N => T (cpl q.1, q.2))
      ({p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N | (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p.1 p.2} ×ˢ Set.univ) := by
  classical
  have hDL : ∀ p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N,
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p.1 p.2 → p ∈ layerSub Gp := fun _ hp => xiDom_mem_layerSub hp
  obtain ⟨c1, c2⟩ := fieldDom_completion_spec (xiFieldDom (compWeight L a₁) ν εseq :
    FieldDom d L N₁ m₁ (k + 1) N ϱ) (k + 1) Gp Y cpl hcpl hDL
  have loc : ∀ (p p' : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g : Fld d L N₁ m₁ (k + 1) N), (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p.1 p.2 → (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p'.1 p'.2 →
      (∀ z ∈ Y, p.1 z = p'.1 z ∧ p.2 z = p'.2 z) → T (p, g) = T (p', g) := by
    intro p p' g hp hp' hpp
    rw [hT, hT]
    exact Finset.sum_congr rfl fun l _ => by
      rw [evTerm_freshLocalHat_clipRaw_congr hk1 hL2 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps hsmall hc7 hphi hmarD hαD
        hsm hF₁ hF₂ Sf hM₂ hδ₁0 hB hδ₁le hSol hPmp hHm cc hcψ hδ₁ Y hσκ hact hKc hKb y l (Gi l) (hGi l)
        hεseq hp hp' hpp]
  have hsrc : ∀ (g g' : Fld d L N₁ m₁ (k + 1) N), (∀ x ∈ Y, g x = g' x) →
      ∀ u : RawData d L (N₁ * L ^ m₁) (k + 1) N,
      ∑ l, g y l * evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Gi l) Y u =
        ∑ l, g' y l * evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Gi l) Y u := fun g g' hg u =>
    fresh_source_local (G := Ga) (m₀ := m₀) cI hy Gi u hg
  have hext2 : ∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
      (g : Fld d L N₁ m₁ (k + 1) N), (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p.1 p.2 → T (cpl p, g) = T (p, g) := fun p g hp =>
    loc _ _ g (c2 p hp).1 hp (fun z hz => (c2 p hp).2 z hz)
  have hAi := fun l => (localB_freshTermHat_evTerm_xiFieldDom hk1 ha₁ ha₂ hS S HBp hκ hM hMX hCx heps
    hsmall hc7 hphi hmarD hαD hsm cc hcψ hδ₁0 hδ₁ hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc
    hKb hγ hcov hd hL hcI hcinj hdisj hopt hΔ hBG₂ hκ₀ hκdec hκκ h1 hlog hεseq y l (Gi l) (hGi l) Y).1
  have hAT : AnalyticOnNhd ℂ T ({p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N | (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N ϱ).dom (k + 1) Gp p.1 p.2} ×ˢ Set.univ) := by
    intro q hq
    have hTf : T = fun p => ∑ l, p.2 y l *
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Gi l) Y (clipRaw Gp p.1) := funext hT
    rw [hTf]
    refine Finset.analyticAt_fun_sum _ fun l _ => AnalyticAt.mul ?_ ?_
    · have hco : AnalyticAt ℂ (fun g : Fld d L N₁ m₁ (k + 1) N => g y l) q.2 :=
        ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) l).comp
          (ContinuousLinearMap.proj (R := ℂ)
            (φ := fun _ : CTorus d L N₁ m₁ (k + 1) => Fin N → ℂ) y)).analyticAt q.2
      exact hco.comp_of_eq analyticAt_snd rfl
    · exact ((hAi l) q.1 hq.1).comp_of_eq analyticAt_fst rfl
  refine ⟨fun Ψ Ψ' h h' g g' hag => ?_, hext2, ?_⟩
  · rw [c1 Ψ Ψ' h h' fun x hx => ⟨(hag x hx).1, (hag x hx).2.1⟩, hT, hT]
    exact hsrc g g' (fun x hx => (hag x hx).2.2) _
  · exact fieldDom_completion_analytic_param _ (k + 1) Gp Y cpl hcpl hDL
      (fun _ hp => xiDom_eventually HBp hp) T hAT
      (fun p p' hp hp' hpp g => loc p p' g hp hp' hpp)

end FreshExt

section FreshExtLocalB

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory


variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ₁ ϱ₂ ϱm : ℝ}
variable {Gk : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₁}
variable {Gj : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ₂}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν : ℝ}
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {b : ℝ} (hb₁ : 1 ≤ b) (hbC : b ≤ scaledC0 d) {t : ℕ} (ht : t ≤ k + 1)
  (Yp : Set (CTorus d L N₁ m₁ (k + 1))) (hN₁ : 5 < N₁) (hMM : 4 * L ^ 2 ≤ L ^ m₁)
  (hag : 2 * d * Real.log L ≤ agmonRate d / 16 * (minSep L (L ^ m₁) - 1)) {c BG : ℝ}
  (hS : Dec2.DecSpecs d L (Dec2.mixedKc d L) (Cchi d L) c BG) (hk1 : 1 ≤ k)
  (ha₁ : 1 / 2 ≤ a₁) (ha₂ : a₁ ≤ 2)
  (HBp : BgHyp d L (k + 1) (minSep L (L ^ m₁)) (compWeight L a₁) ν)
  (HBk : BgHyp d L (k + 1) ϱ₁ (compWeight L a₁) ν)
  (HBj : BgHyp d L (k + 1) ϱ₂ (compWeight L a₁) ν)

set_option hygiene false in
local notation "𝔹ₗ" => GsSpec.localB t ht Yp (le_refl (minSep L (L ^ m₁)))

variable (hP : Precedes Gk 𝔹ₗ) (hq : Precedes Gj Gk)
  (colk : ∀ z ∈ collar Gk, z ∈ (𝔹ₗ).Ω 1) (colj : ∀ z ∈ collar Gj, z ∈ Gk.Ω 1)
  {κ eps δ₃ : ℝ} (hκ : 0 < κ) (hM : c * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hMX : Dec2.cstarX d L (Cchi d L) * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
  (hnum : ChainNum d L N m₁ BG κ (4 * d * (L : ℝ) ^ 3 + L) eps δ₃)
  {X₀ X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} (dsX₀ : ∀ x ∈ dataSites Gk, x ∈ X₀)
  (hN : ∀ x ∈ X₀, x ∈ (𝔹ₗ).Ω 1 →
    ∀ y : CTorus d L N₁ m₁ (k + 1), Green.torusDist d ((N₁ * L ^ m₁) * L ^ (k + 1)) x y <
      (4 * d * (L : ℝ) ^ 3 + L) * (L : ℝ) ^ m₁ * (𝔹ₗ).spacing x → y ∈ X₁f)
  {j : ℕ} (hj : j ≤ k + 1) {Kf Cf c₂ BG₂ δ₁ δfl : ℝ}
  (hF : FlSetting N 𝔹ₗ Gk Hm a₁ ν κ BG eps δ₃ Kf Cf c₂ BG₂ δ₁ δfl X₁f)
  (hHm : Hm.Ω (k + 1) = ∅)
  {Fk : RawData d L (N₁ * L ^ m₁) (k + 1) N → (Gk.Ω 1 × Fin N → ℂ) × (Gk.Ω 1 → ℂ)}
  (hFkan : AnalyticOnNhd ℂ Fk {p | ∃ D : BgData Gk N,
    InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D ∧ p = (D.Ψ, D.h)})
  (hFk : ∀ D : BgData Gk N, InUnionDomainC Gk (bgC0 d L N) (bgC1 d L N) ν D →
    Fk (rawOf D) = (bgFieldC Gk (compWeight L a₁) ν (bgC0 d L N) D,
      bgMultC Gk (compWeight L a₁) ν (bgC0 d L N) D))
  {δc : ℝ} (hmarD : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
  (hαD : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
  (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
  (hδ₁ : Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ)) < δ₁)
  {F₁ : Dec2.DecParams (coverOf 𝔹ₗ) × RawData d L (N₁ * L ^ m₁) (k + 1) N →
    ((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)}
  (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData 𝔹ₗ N,
    InUnionDomainC 𝔹ₗ (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
  (hF₁ : ∀ (s : Dec2.DecParams (coverOf 𝔹ₗ)) (D : BgData 𝔹ₗ N), (∀ P, ‖s P‖ < Real.exp κ) →
    InUnionDomainC 𝔹ₗ (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : (𝔹ₗ).Ω 1 × Fin N → ℂ)
      (α : (𝔹ₗ).Ω 1 → ℂ),
      Dec2.IsDecBg (coverOf 𝔹ₗ) 𝔹ₗ (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
      F₁ (s, rawOf D) = (φ, α))
  {Sol : Dec2.DecParams (coverOf 𝔹ₗ) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
  (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
    StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
  (hSol : ∀ p : Dec2.DecParams (coverOf 𝔹ₗ) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
    StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
      (Sol p).1 = dphi Hm (Dec2.decG (coverOf 𝔹ₗ) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
        (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
      Dec2.DecFixed (coverOf 𝔹ₗ) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
        (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
      Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
      Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
      SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
      (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
        Dec2.DecFixed (coverOf 𝔹ₗ) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2))
  {σ : (ι → ℂ) → Dec2.DecParams (coverOf 𝔹ₗ)} (hσan : ∀ w, AnalyticAt ℂ σ w)
  (hσκ : ∀ w ∈ polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ∀ P, ‖σ w P‖ < Real.exp κ)
  (hσ1 : ∀ w (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ (coverOf 𝔹ₗ).cubeIdx),
    P ∉ (coverOf 𝔹ₗ).parCubes X₁f → σ w ⟨P, hP⟩ = 1)
  {γ : Measure (unitPts 𝔹ₗ × Fin N → ℝ)} {K : Set (unitPts 𝔹ₗ × Fin N → ℝ)}
  (hKc : IsCompact K) (hKb : ∀ ψ ∈ K, ∀ r, |ψ r| ≤ cψ) (hγ : γ K < ⊤)

include hN₁ hMM hag hS hk1 ha₁ ha₂ HBp hκ hM hMX hnum hF hHm hmarD hαD hsm hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan
  hσκ hσ1 hKc hKb hγ


/-- **The fresh source term on all pairs of fields and sources at `𝔹_{k+1}(Y⁺)`** (P3 (4.46)-(4.47);
the clauses `localM`, `analyticM` of the local successor class for the fresh term `∑_i g(y, i) T_i`,
the source `g` carried along).  With `T (p, g) = ∑_i g(y, i) T_i(clipRaw 𝔹 p)` the fresh source term of
`Y` and `cpl` the completion in the class domain at `Y` (`fieldDom_completion_spec`): `T ∘ cpl` takes
the same value at two triples `(Ψ, h, g)`, `(Ψ', h', g')` equal on `Y` (all pairs of fields and all
sources), equals `T` on the class domain, and `(p, g) ↦ T (cpl p, g)` is analytic on the class domain
times all sources.  Instance of `freshTermHat_evTerm_ext` at `𝔹 = 𝔹_{k+1}(Y⁺)`, with `hact` from
`hσ0`, `hσY` (`localB_active_hatBox_subset`). -/
theorem localB_freshTermHat_evTerm_ext (htk : t = k + 1) {ϱa : ℝ}
    {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa} {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)}
    {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Ga m₀ j' X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga)
    (hcinj : Function.Injective cI) (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
    (hΔ : treeLenCovOne m₀ j' X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)
    (y : CTorus d L N₁ m₁ (k + 1)) (hy : y ∈ X1 Ga m₀ j' 𝒦X)
    (Gi : Fin N → RawData d L (N₁ * L ^ m₁) (k + 1) N → (ι → ℂ) → ℂ)
    (hGi : ∀ (l : Fin N) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) (w : ι → ℂ), Gi l Θ w =
      ∫ ψ in K,
        siteFun 𝔹ₗ Hm y l (F₁ (σ w, Θ))
          (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, Θ)) Θ.1
            (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts 𝔹ₗ then
                (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf 𝔹ₗ) (σ w)) (barField 𝔹ₗ Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ 𝔹ₗ) (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0))).1
          (Θ, (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
              if h : unitBlock x ∈ unitPts 𝔹ₗ then
                (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν (F₁ (σ w, Θ)).2
                  (Dec2.extS (coverOf 𝔹ₗ) (σ w)) (barField 𝔹ₗ Θ.1 (F₁ (σ w, Θ)).1)
                  (unitQ 𝔹ₗ) (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ)))) (⟨unitBlock x, h⟩, i)
              else 0)) ∂γ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (hσ0 : ∀ w, ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, P.2 ∉ (𝔹ₗ).Ω (k + 1) →
      Dec2.extS (coverOf 𝔹ₗ) (σ w) P = 0)
    (hσY : ∀ C ∈ connFams cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Y, ∀ w ∈ supN C (Real.exp κ),
      ∀ P ∈ (coverOf 𝔹ₗ).cubeIdx, Dec2.extS (coverOf 𝔹ₗ) (σ w) P ≠ 0 →
        ∀ y', SameCell (L ^ (P.1 + m₁)) y' P.2 → y' ∈ Y)
    (T : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N → ℂ)
    (hT : ∀ p, T p = ∑ l, p.2 y l *
      evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) (Gi l) Y (clipRaw 𝔹ₗ p.1))
    (cpl : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N → Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N)
    (hcpl : ∀ p, cpl p = Classical.epsilon (fun q : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N =>
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ q.1 q.2 ∧ ∀ z ∈ Y,
        q.1 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).1 z ∧
        q.2 z = (Classical.choose (exists_layerProj (N := N) 𝔹ₗ Y) p).2 z)) :
    (∀ Ψ Ψ' h h' g g' : Fld d L N₁ m₁ (k + 1) N,
      (∀ x ∈ Y, Ψ x = Ψ' x ∧ h x = h' x ∧ g x = g' x) → T (cpl (Ψ, h), g) = T (cpl (Ψ', h'), g')) ∧
    (∀ (p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) (g : Fld d L N₁ m₁ (k + 1) N),
      (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2 → T (cpl p, g) = T (p, g)) ∧
    AnalyticOnNhd ℂ (fun q : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × Fld d L N₁ m₁ (k + 1) N => T (cpl q.1, q.2))
      ({p : Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N | (xiFieldDom (compWeight L a₁) ν εseq : FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1 p.2} ×ˢ Set.univ) := by
  subst htk
  have hL : 3 ≤ L := HBp.hL
  have hm₁ : 2 ≤ m₁ := by
    by_contra h
    push Not at h
    have hL2 : L ^ m₁ ≤ L ^ 1 := Nat.pow_le_pow_right (by omega) (by omega)
    nlinarith
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  exact freshTermHat_evTerm_ext hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L)
    hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
    hF.hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hcov hd hL hcI hcinj hdisj hopt hΔ
    hF.hS2.fam.2.1 hκ₀ hκdec hκκ h1 hlog hεseq (by omega) hF.hS2.fam hF.SM.toCoverBase hF.hM2
    hF.num.B_le hF.num.δ₁_le y hy Gi hGi Y
    (fun C hC w hw => localB_active_hatBox_subset hk1 ht Yp hm₁ hMM (hσ0 w) (hσY C hC w hw))
    T hT cpl hcpl

end FreshExtLocalB

end Balaban.Localization
