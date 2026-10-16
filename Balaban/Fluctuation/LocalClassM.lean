/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.LocalClassSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The source terms `ℳ` on the local chart: analyticity in the fields and the source, and the bound

The term of a polymer `Y` of level `k + 1` coming from an inherited source term `ℳ^{(j)}_i(y, X)`
is, for a fixed component `i`, the term of `LocalHatTerm.lean` with the old-term functional
`E_g(r) = ℳ^{(j)}_i(y, X; r.1, r.2, g)`, which depends on the source `g` as a parameter.  The clause
`analyticM` asks analyticity jointly in the fields and in `g`; the clauses already landed for the
energy terms (`localB_eTermHat_evTerm_xiFieldDom`) are analytic in the fields for each fixed
functional.  This file carries a parameter `g` of a finite-dimensional complex space `G`
(analytic on a set `Sg`) through the chain without re-proving it:

* `analyticOnNhd_of_forall_clm`, `analyticOnNhd_mem_of_transfer`: a map into a finite-dimensional
  space is analytic when every continuous linear functional of it is, and if a bound by `0` of
  every function bounded by `0` on a set `Dm` transfers, then its values lie in `Dm`.  Applied to
  the triple map `((Θ, ψ̂), w) ↦ (F₁(σ w, Θ), Sol(σ w, …), (Θ, ψ'))` (from
  `fanLocalHat_analytic_cover`, `fanLocalHat_norm_le_cover`) and to the composition
  `D2raw ∘ d1Triple` (from `localB_eTermFun_analytic`, `localB_eTermFun_bound`), this gives that the
  maps are analytic and take values in the realizable triples, resp. in the chart of the old term;
* `localB_mTermHat_integral_param`: the `ψ̂`-integral of the old-term functional `E (·) g` is
  analytic in `((Θ, g), w)` and bounded by `Bd γ(K)`;
* `localB_mTermHat_evTerm_xiFieldDom`: the clauses `analyticM` (jointly in the pair of fields and
  the source) and the bound of `boundM` for one old label, for the term of `Y` read through the
  cut-off `clipRaw 𝔹` on the class domain `Ξ^c_{k+1}(𝔹; 1, ε_{k+1})`.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.LargeField Balaban.SmallField.Def6 Balaban.SmallField.Def6v2
  Finset Matrix MeasureTheory
section Transfer

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- A map into a finite-dimensional space is analytic on a set when all its continuous linear
functionals are. -/
theorem analyticOnNhd_of_forall_clm {S : Set X} {F : X → V}
    (h : ∀ ℓ : V →L[ℂ] ℂ, AnalyticOnNhd ℂ (fun x => ℓ (F x)) S) : AnalyticOnNhd ℂ F S := by
  classical
  intro x hx
  let b := Module.finBasis ℂ V
  have hF : F = fun y => ∑ i, (LinearMap.toContinuousLinearMap (b.coord i) (F y)) • b i := by
    funext y
    simp [Module.Basis.sum_repr]
  rw [hF]
  exact Finset.analyticAt_fun_sum _ fun i _ => (h _ x hx).smul analyticAt_const

theorem analyticOnNhd_mem_of_transfer {S : Set X} {Dm : Set V} {F : X → V}
    (hA : ∀ Φ : V → ℂ, AnalyticOnNhd ℂ Φ Dm → AnalyticOnNhd ℂ (fun x => Φ (F x)) S)
    (hB : ∀ Φ : V → ℂ, (∀ v ∈ Dm, ‖Φ v‖ ≤ 0) → ∀ x ∈ S, ‖Φ (F x)‖ ≤ 0) :
    AnalyticOnNhd ℂ F S ∧ ∀ x ∈ S, F x ∈ Dm := by
  classical
  refine ⟨analyticOnNhd_of_forall_clm fun ℓ => hA ℓ (ℓ.analyticOnNhd _), fun x hx => ?_⟩
  by_contra hn
  have := hB (fun v => if v ∈ Dm then 0 else 1) (fun v hv => by simp [hv]) x hx
  simp [hn] at this
  norm_num at this

end Transfer

section FinDim

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}

theorem finDim_rawData : FiniteDimensional ℂ (RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
  inferInstance

theorem finDim_fld : FiniteDimensional ℂ (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) :=
  inferInstance

theorem finDim_omega (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    FiniteDimensional ℂ (G.Ω 1 × Fin N → ℂ) := inferInstance

theorem finDim_omega' (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ) :
    FiniteDimensional ℂ (G.Ω 1 → ℂ) := inferInstance

theorem finDim_triple (G : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm) :
    FiniteDimensional ℂ (((G.Ω 1 × Fin N → ℂ) × (G.Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
      (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ))) := by
  have := finDim_rawData (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
  have := finDim_fld (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
  have := finDim_omega (N := N) G
  have := finDim_omega' G
  have := finDim_omega (N := N) Hm
  exact inferInstance

end FinDim

section ParamM

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

include hb₁ hbC hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj
  hF hHm hFkan hFk hmarD hαD hsm hcψ hδ₁ hF₁an hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ

omit [DecidableEq ι] in
theorem localB_mTermHat_integral_param {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {Sg : Set G}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → G → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    {Bd : ℝ} (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg, ‖E r g‖ ≤ Bd)
    (Fi : (RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ) → ℂ)
    (hFi : ∀ q, Fi q =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r q.1.2) (F₁ (σ q.2, q.1.1))
        (Sol (σ q.2, flEdat 𝔹ₗ Hm (F₁ (σ q.2, q.1.1)) q.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ q.2))
                (barField 𝔹ₗ q.1.1.1 (F₁ (σ q.2, q.1.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (q.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ q.2, q.1.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ q.2))
                (barField 𝔹ₗ q.1.1.1 (F₁ (σ q.2, q.1.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) :
    AnalyticOnNhd ℂ Fi ((XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ)) ∧
      ∀ q ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ), ‖Fi q‖ ≤ Bd * (γ K).toReal := by
  classical
  have hcd := localB_coverData ht Yp hN₁ hMM hag HBp
  have ha₁0 : 0 < a₁ := by linarith
  have hfdT := finDim_triple (N := N) 𝔹ₗ Hm
  have hfdR := finDim_rawData (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (N := N)
  -- the triple map of the local hat variable
  obtain ⟨Tmap, hTmap⟩ : ∃ Tmap : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts 𝔹ₗ × Fin N → ℂ)) × (ι → ℂ) →
      (((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)),
      ∀ p, Tmap p = (F₁ (σ p.2, p.1.1),
        (Sol (σ p.2, flEdat 𝔹ₗ Hm (F₁ (σ p.2, p.1.1)) p.1.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf 𝔹ₗ) (σ p.2)) (barField 𝔹ₗ p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ 𝔹ₗ) (unitP 𝔹ₗ) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0))).1,
        (p.1.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν (F₁ (σ p.2, p.1.1)).2
                (Dec2.extS (coverOf 𝔹ₗ) (σ p.2)) (barField 𝔹ₗ p.1.1.1 (F₁ (σ p.2, p.1.1)).1)
                (unitQ 𝔹ₗ) (unitP 𝔹ₗ) *ᵥ p.1.2)) (⟨unitBlock x, h⟩, i)
            else 0)) := ⟨_, fun _ => rfl⟩
  have hT := analyticOnNhd_mem_of_transfer
    (S := (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ))
    (Dm := FlRealLC 𝔹ₗ Hm a₁ ν BG κ eps X₁f BG₂ δ₁) (F := Tmap)
    (fun Φ hΦ => by
      have := fanLocalHat_analytic_cover hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L)
        hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
        hF.hPmp hHm hF₁an hF₁ hSolan hSol hσan hσκ hσ1
        (Φ := fun pa δφ u => Φ (pa, δφ, u)) hΦ
      simpa only [hTmap] using this)
    (fun Φ hΦ p hp => by
      have := fanLocalHat_norm_le_cover hk1 ha₁ ha₂ hS hcd.1 HBp hκ hM hMX (Cchi_nonneg d L)
        hnum.eps_pos hnum.small1 hnum.c7le hF.num.phi_lt hmarD hαD hsm cc hcψ hF.num.δ₁_pos hδ₁
        hF.hPmp hHm hF₁ hSol hσκ hσ1
        (Φ := fun pa δφ u => Φ (pa, δφ, u)) (B := 0) hΦ p hp
      simpa only [hTmap] using this)
  obtain ⟨Cmap, hCmap⟩ : ∃ Cmap : (((𝔹ₗ).Ω 1 × Fin N → ℂ) × ((𝔹ₗ).Ω 1 → ℂ)) × (Hm.Ω 1 × Fin N → ℂ) ×
        (RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N, ∀ τ, Cmap τ = D2raw Gk Gj (compWeight L a₁) Fk
      (d1Triple 𝔹ₗ Gk Hm (compWeight L a₁) τ.1.1 τ.2.1 τ.2.2) := ⟨_, fun _ => rfl⟩
  have hC := analyticOnNhd_mem_of_transfer
    (S := FlRealLC 𝔹ₗ Hm a₁ ν BG κ eps X₁f BG₂ δ₁)
    (Dm := XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl))
    (F := Cmap)
    (fun Φ hΦ => by
      have := localB_eTermFun_analytic hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq
        colk colj hκ hM hnum dsX₀ hN hj hF hFkan hFk (E := Φ) hΦ
      simpa only [hCmap, eTermFun] using this)
    (fun Φ hΦ τ hτ => by
      have := localB_eTermFun_bound hb₁ hbC ht Yp hN₁ hMM hag hS ha₁0 HBp HBk HBj hP hq
        colk colj hκ hM hnum dsX₀ hN hj hF hFk (E := Φ) (Bd := 0) hΦ hτ
      simpa only [hCmap, eTermFun] using this)
  have hPfd : FiniteDimensional ℂ ((RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ)) :=
    inferInstance
  have heq : Fi = fun q => ∫ ψ in K, E (Cmap (Tmap ((q.1.1, fun r => (ψ r : ℂ)), q.2))) q.1.2 ∂γ := by
    funext q
    rw [hFi q]
    simp only [hTmap, hCmap, eTermFun]
  rw [heq]
  refine analyticOnNhd_setIntegral_compact (P := (RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ))
    (I := unitPts 𝔹ₗ × Fin N) (B := Bd) (γ := γ)
    (F := fun q v => E (Cmap (Tmap ((q.1.1, v), q.2))) q.1.2) hKc hKb hγ ?_ ?_
  · intro q hq v hv
    obtain ⟨⟨hΘ, hg⟩, hw⟩ := hq
    have hmemT : ((q.1.1, v), q.2) ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := ⟨⟨hΘ, hv⟩, hw⟩
    have hρ : AnalyticAt ℂ (fun x : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × (ι → ℂ)) ×
        (unitPts 𝔹ₗ × Fin N → ℂ) => ((x.1.1.1, x.2), x.1.2)) (q, v) :=
      ((analyticAt_fst.comp (analyticAt_fst.comp analyticAt_fst)).prod analyticAt_snd).prod
        (analyticAt_snd.comp analyticAt_fst)
    have h1 := hT.1 _ hmemT
    have h2 := hC.1 _ (hT.2 _ hmemT)
    have h3 : AnalyticAt ℂ (fun z : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E z.1 z.2)
        (Cmap (Tmap ((q.1.1, v), q.2)), q.1.2) := hE _ ⟨hC.2 _ (hT.2 _ hmemT), hg⟩
    exact h3.comp_of_eq ((h2.comp_of_eq (h1.comp_of_eq hρ rfl) rfl).prod
      (analyticAt_snd.comp (analyticAt_fst.comp analyticAt_fst))) rfl
  · intro q hq v hv
    obtain ⟨⟨hΘ, hg⟩, hw⟩ := hq
    have hmemT : ((q.1.1, v), q.2) ∈ (XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts 𝔹ₗ × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        polydisc (0 : ι → ℂ) (fun _ => Real.exp κ) := ⟨⟨hΘ, hv⟩, hw⟩
    exact hEb _ (hC.2 _ (hT.2 _ hmemT)) q.1.2 hg

variable {ϱa : ℝ} {Ga : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱa}
  {cI : ι → ℕ × CTorus d L N₁ m₁ (k + 1)} {m₀ j' : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
  (hcov : CovSetup Ga m₀ j' X 𝒦X) (hd : 3 ≤ d) (hL : 3 ≤ L) (hcI : ∀ i, cI i ∈ cubeIdx Ga)
  (hcinj : Function.Injective cI) (hdisj : ∀ i, Disjoint (Pset m₁ (cI i)) (X1 Ga m₀ j' 𝒦X))
  (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
    (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
    ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j' 𝒦X W₀ ∧
      bondCost (scaleW L m₀ m₁ j') E₀ = treeLenCovOne m₀ j' X)
  {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec) (hEb0 : 0 ≤ Eb)
  (hκκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
  (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
  {εseq : ℕ → ℝ} (hεseq : εseq (k + 1) ≤ eps)

include hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hEb0 hκκ h1 hlog hεseq

theorem localB_mTermHat_evTerm_xiFieldDom {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [FiniteDimensional ℂ G] {Sg : Set G}
    {E : RawData d L (N₁ * L ^ m₁) (k + 1) N → G → ℂ}
    (hE : AnalyticOnNhd ℂ (fun q : RawData d L (N₁ * L ^ m₁) (k + 1) N × G => E q.1 q.2)
      (XiCRaw Gj (compWeight L a₁) ν j b
        (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl) ×ˢ Sg))
    (hEb : ∀ r ∈ XiCRaw Gj (compWeight L a₁) ν j b
      (b ^ 2 * eps + xiK2 d L N * δ₃ + xiK2 d L N * δfl), ∀ g ∈ Sg,
        ‖E r g‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (Fi : RawData d L (N₁ * L ^ m₁) (k + 1) N × G → (ι → ℂ) → ℂ)
    (hFi : ∀ u w, Fi u w =
        ∫ ψ in K,
          eTermFun 𝔹ₗ Gk Gj Hm (compWeight L a₁) Fk (fun r => E r u.2) (F₁ (σ w, u.1))
        (Sol (σ w, flEdat 𝔹ₗ Hm (F₁ (σ w, u.1)) u.1.1
          (fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0))).1
        (u.1, fun (x : CTorus d L N₁ m₁ (k + 1)) (i : Fin N) =>
            if h : unitBlock x ∈ unitPts 𝔹ₗ then
              (cc • (decCovSqrt 𝔹ₗ (compWeight L a₁) a₁ ν
                (F₁ (σ w, u.1)).2 (Dec2.extS (coverOf 𝔹ₗ) (σ w))
                (barField 𝔹ₗ u.1.1 (F₁ (σ w, u.1)).1) (unitQ 𝔹ₗ)
                    (unitP 𝔹ₗ) *ᵥ (fun r => (ψ r : ℂ))))
                (⟨unitBlock x, h⟩, i)
            else 0) ∂γ) :
    AnalyticOnNhd ℂ (fun p : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × G =>
        evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2))
      {p | (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1.1 p.1.2 ∧ p.2 ∈ Sg} ∧
    ∀ p : (Fld d L N₁ m₁ (k + 1) N × Fld d L N₁ m₁ (k + 1) N) × G,
      (xiFieldDom (compWeight L a₁) ν εseq :
        FieldDom d L N₁ m₁ (k + 1) N (minSep L (L ^ m₁))).dom (k + 1) 𝔹ₗ p.1.1 p.1.2 →
      p.2 ∈ Sg →
      ‖evTerm cI Ga m₀ (X1 Ga m₀ j' 𝒦X) Fi Y (clipRaw 𝔹ₗ p.1, p.2)‖ ≤
        Eb * (γ K).toReal *
          Real.exp (-κ₀ * treeLenCovOne m₀ j' X - 2 * κdec * treeLenCov Ga m₀ Y) := by
  classical
  have hγ0 : 0 ≤ (γ K).toReal := ENNReal.toReal_nonneg
  obtain ⟨hA, hB⟩ := localB_mTermHat_integral_param hb₁ hbC ht Yp hN₁ hMM hag hS hk1 ha₁ ha₂ HBp HBk
    HBj hP hq colk colj hκ hM hMX hnum dsX₀ hN hj hF hHm hFkan hFk hmarD hαD hsm cc hcψ hδ₁ hF₁an
    hF₁ hSolan hSol hσan hσκ hσ1 hKc hKb hγ hE (Bd := Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j' X))
    hEb (fun q => Fi q.1 q.2) (fun q => hFi q.1 q.2)
  have hEv := evTerm_bound_analyticOnNhd_of_bd (c := cI)
    (U := RawData d L (N₁ * L ^ m₁) (k + 1) N × G) (F := Fi)
    hcov hd hL hcI hcinj hdisj hopt hκ₀ hκdec hκκ h1 hlog (mul_nonneg hEb0 hγ0)
    (S := XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps ×ˢ Sg) hA
    (fun u hu s hs => by
      have := hB (u, s) ⟨hu, hs⟩
      rw [mul_right_comm]
      exact this)
  refine ⟨fun p hp => ?_, fun p hp hg => ?_⟩
  · have hmem : clipRaw 𝔹ₗ p.1 ∈ XiCRaw 𝔹ₗ (compWeight L a₁) ν (k + 1) 1 eps :=
      clipRaw_mem_xiCRaw_of_xiDom hεseq hp.1
    exact (hEv.2 Y (clipRaw 𝔹ₗ p.1, p.2) ⟨hmem, hp.2⟩).comp_of_eq
      (((analyticAt_clipRaw p.1).comp analyticAt_fst).prod analyticAt_snd) rfl
  · exact hEv.1 Y (clipRaw 𝔹ₗ p.1, p.2) ⟨clipRaw_mem_xiCRaw_of_xiDom hεseq hp, hg⟩

end ParamM

end Balaban.Localization
