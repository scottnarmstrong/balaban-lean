/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.NewLevelZeroSourceBg
public import Balaban.Fluctuation.LocalSetActRayBound
public import Balaban.Fluctuation.HatDiagContBase
public import Balaban.Fluctuation.MarkedEvJoint

/-!
# The fields of the zero-source activities recomputed on a background generating set

P3 pp. 78-79, (4.44)-(4.47) and P6 Lemma 4.1 for the zero-source activities `zeroActBg` of the new
level recomputed on a background generating set `Gb` (route R-LOC, L4-3): from the analyticity and
the bound of the terms `Ev_z` of the block energies on the chart of `Gb` times the box of the hat
variable (`zeroEvBg`, the term of the block `z`; supplied by `evDecBg_canon_bound_analytic` at the
marks `(1, 0)`), the zero-source activity of a domain is measurable and continuous in the block
configuration, analytic in the parameter of `Gb` and the coupling `u` on `physVBg Gb × {‖u‖ < 2}`,
and bounded by `8 |β| ∑_z [Y ∈ polyDom_z] M_ω 6 b_z / r³`.  No locality is used.

* `zeroEvBg`, `zeroTermBg_eq_sum`: the term of the block `z` and the zero-source term as the sum of
  its ray integrals;
* `zeroTermBg_analytic_bound`: analyticity in `(Θ, σ)` and the bound on an admissible ray
  (`sum_rayTerm_dl3_analytic_bound`);
* `zeroActBg_of_mem`, `zeroActBg_of_not`: the gate;
* `zeroActBg_fields`: the bound for every parameter, the analyticity on `physVBg Gb × {‖u‖ < 2}`,
  the continuity in the configuration on the chart, and the measurability.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Localization
  Balaban.LargeField Finset Metric

section ZeroFields

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱb ϱm : ℝ}

/-- **The term of the block `z` of the zero-source term on `Gb`**: the term `evDecBg` of the label
`Y` of the expansion of the block energy of `z` recomputed on `Gb` with the transport `Tr`, at the
marks `(1, 0)` and the restriction of the hat variable, as a function of `(Θ, ψ̂)`. -/
noncomputable abbrev zeroEvBg (S : StepSetting d L N₁ m₁ k N ϱ)
    (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb) (Tr : BgTransport S.G' Gb N)
    {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
    (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
    (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
    (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
    (m₀ : ℕ)
    (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
    (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (Y : Set (CTorus d L N₁ m₁ (k + 1))) :
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ) → ℂ :=
  fun u => evDecBg S.G' (X₁V z) m₀ (jV z) (𝒦XV z) Gb S.a₁ S.ν Tr
    ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) (F₁ z) (Sol z)
    (blockEnergyFun Gb Hm (compWeight L S.a₁) S.ν k z) ∅ 1 0 Y (u.1, Tr.res u.2)

variable (S : StepSetting d L N₁ m₁ k N ϱ) (Gb : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱb)
  (Tr : BgTransport S.G' Gb N) {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
  (X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1)))
  (jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ)
  (𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)))
  (m₀ : ℕ)
  (F₁ : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    DecParams Gb × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gb.Ω 1 × Fin N → ℂ) × (Gb.Ω 1 → ℂ))
  (Sol : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
    Dec2.DecParams (coverOf Gb) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
  (ω : ℂ → ℂ)

open Classical in
/-- The zero-source term on `Gb` is `-β` times the sum of the ray integrals of the terms of the
blocks whose label set contains `Y`. -/
theorem zeroTermBg_eq_sum (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (x₀ w : unitPts S.G' × Fin N → ℂ) (σ : ℂ) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N) :
    zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ Θ =
      -(S.β : ℂ) * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then
          rayTerm (dl3 (zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y) w) ω x₀ σ Θ
        else 0 := by
  unfold zeroTermBg
  congr 1

open Classical in
/-- **Analyticity and bound of the zero-source term on `Gb` along an admissible ray**: if the term
of every block `z` whose label set contains `Y` is analytic and bounded by `b z` on `S₀ × B`, then
on an admissible ray `(x₀, w)` the zero-source term of `Y` is analytic in `(Θ, σ)` on
`S₀ × {|σ| < R_σ}` and bounded by `|β| |σ| ∑_z [Y ∈ polyDom_z] M_ω 6 b_z / r³`. -/
theorem zeroTermBg_analytic_bound (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    {S₀ : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {B : Set (unitPts S.G' × Fin N → ℂ)}
    {b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℝ}
    (hEv : ∀ z, Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) →
      AnalyticOnNhd ℂ (zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y) (S₀ ×ˢ B))
    (hb : ∀ z, Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) → ∀ u ∈ S₀ ×ˢ B,
      ‖zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y u‖ ≤ b z)
    {R₁ : ℝ} (hR₁ : 1 < R₁) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r Rσ : ℝ} (hr : 0 < r) {x₀ w : unitPts S.G' × Fin N → ℂ}
    (hxw : ∀ σ : ℂ, ‖σ‖ < Rσ → ∀ t : ℂ, ‖t‖ < R₁ → ∀ τ : ℂ, ‖τ‖ ≤ r →
      (σ * t) • x₀ + τ • w ∈ B) :
    AnalyticOnNhd ℂ (fun p : RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ =>
        zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w p.2 p.1) (S₀ ×ˢ ball (0 : ℂ) Rσ) ∧
    ∀ Θ ∈ S₀, ∀ σ : ℂ, ‖σ‖ < Rσ →
      ‖zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w σ Θ‖ ≤
        |S.β| * (‖σ‖ * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
          if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then Mω * (6 * b z / r ^ 3) else 0) := by
  have hsum := sum_rayTerm_dl3_analytic_bound
    (fun z => Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z))
    (Ev := fun z => zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y) hEv hb hR₁ hω hMω hωb hr hxw
  refine ⟨fun p hp => ?_, fun Θ hΘ σ hσ => ?_⟩
  · have h := (analyticAt_const (v := -(S.β : ℂ))).mul (hsum.1 p hp)
    refine h.congr (Filter.Eventually.of_forall fun q => ?_)
    exact (zeroTermBg_eq_sum S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y x₀ w q.2 q.1).symm
  · rw [zeroTermBg_eq_sum, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hsum.2 Θ hΘ σ hσ) (abs_nonneg _)

variable {ρ : ℝ} (hp : 0 < S.p₁) (eps : ℝ)

/-- The zero-source activity on the chart and the disc. -/
theorem zeroActBg_of_mem {θ : physParamBg N Gb} {u : ℂ}
    (h1 : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps) (h2 : ‖u‖ < 2)
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y Φ =
      u ^ 2 * zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
        (S.hatOf m₀ ρ hp Φ) u (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) := by
  simp only [zeroActBg, h1, h2, and_self, ↓reduceIte]

/-- The zero-source activity vanishes off the chart or off the disc. -/
theorem zeroActBg_of_not {θ : physParamBg N Gb} {u : ℂ}
    (h : ¬ ((θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < 2))
    (Y : Set (CTorus d L N₁ m₁ (k + 1))) (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y Φ = 0 := by
  simp only [zeroActBg, h, ↓reduceIte]

open Classical in
/-- **The fields of the zero-source activity on `Gb`.**  Let the terms of the blocks whose label set
contains `Y` be analytic and bounded by `b z ≥ 0` on the chart `Ξ^c(Gb; 1, ε)` times the box
`|ψ̂| ≤ c_ψ`, let `ω` be continuous, analytic on `|t| < R₁` and bounded by `M_ω` on `[0, 1]`, and let
the hat field of every block configuration be an admissible ray for `|σ| < 2`.  Then the
zero-source activity `zeroActBg … θ u Y Φ`:

1. is bounded by `8 |β| ∑_z [Y ∈ polyDom_z] M_ω 6 b_z / r³` at every parameter and configuration;
2. is analytic in `(θ, u)` on `physVBg Gb × {‖u‖ < 2}` for every configuration;
3. is continuous in the configuration at the parameters of the chart and `‖u‖ < 2`;
4. is measurable in the configuration at every parameter. -/
theorem zeroActBg_fields (Y : Set (CTorus d L N₁ m₁ (k + 1))) {cψ : ℝ}
    {b : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℝ} (hb0 : ∀ z, 0 ≤ b z)
    (hEv : ∀ z, Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) →
      AnalyticOnNhd ℂ (zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y)
        (XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}))
    (hb : ∀ z, Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) →
      ∀ u ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ},
      ‖zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y u‖ ≤ b z)
    {R₁ : ℝ} (hR₁ : 1 < R₁) (hωc : Continuous ω) (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁))
    {Mω : ℝ} (hMω : 0 ≤ Mω) (hωb : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖ω (t : ℂ)‖ ≤ Mω)
    {r : ℝ} (hr : 0 < r)
    (hrays : ∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b,
      (S.hatOf m₀ ρ hp Φ, S.hatOf m₀ ρ hp Φ) ∈ HatRays (N := N) S.G' cψ R₁ 2 r)
    (hV : IsOpen (physVBg N Gb S.a₁ S.ν eps)) :
    (∀ θ u Φ, ‖zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y Φ‖ ≤
      8 * (|S.β| * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
        if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then Mω * (6 * b z / r ^ 3) else 0)) ∧
    (∀ Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b, AnalyticOnNhd ℂ
      (fun p : physParamBg N Gb × ℂ =>
        zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps p.1 p.2 Y Φ)
      (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) 2)) ∧
    (∀ θ : physParamBg N Gb, (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps → ∀ u : ℂ, ‖u‖ < 2 →
      Continuous (zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y)) ∧
    (∀ θ u, Measurable (zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y)) := by
  -- the zero-source term on the chart along the ray of every configuration
  have hT := fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
    zeroTermBg_analytic_bound S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y hEv hb hR₁ hω hMω hωb hr
      (hrays Φ)
  have hsum0 : 0 ≤ ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
      (if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then Mω * (6 * b z / r ^ 3) else 0) :=
    Finset.sum_nonneg fun z _ => by
      split_ifs
      · have := hb0 z; positivity
      · exact le_rfl
  -- continuity of the term in the hat variable along the diagonal
  have hcontT : ∀ Θ ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps, ∀ u : ℂ, ‖u‖ < 2 →
      Continuous (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
          (S.hatOf m₀ ρ hp Φ) u Θ) := by
    intro Θ hΘ u hu
    have hfun : (fun Φ : (∀ b, (S.blockSplit m₀ hp).Ωb b) =>
        zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
          (S.hatOf m₀ ρ hp Φ) u Θ) = fun Φ => -(S.β : ℂ) *
        ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
          if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then
            rayTerm (dl3 (zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y) (S.hatOf m₀ ρ hp Φ)) ω
              (S.hatOf m₀ ρ hp Φ) u Θ
          else 0 :=
      funext fun Φ => zeroTermBg_eq_sum S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y _ _ u Θ
    rw [hfun]
    refine continuous_const.mul (continuous_finsetSum _ fun z _ => ?_)
    by_cases hz : Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z)
    · simp only [hz, ↓reduceIte]
      have hdiag := diagCont_rayTerm (𝒴 := ({()} : Finset Unit))
        (Evs := fun _ : Unit => zeroEvBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol z Y) (Rσ := 2)
        (ω := ω) hR₁ hωc hr (fun _ => hEv z hz) () (Finset.mem_singleton_self _) u hu Θ hΘ
      exact hdiag.comp_continuous (S.continuous_hatOf m₀ ρ hp) fun Φ => hrays Φ
    · simp only [hz, ↓reduceIte]
      exact continuous_const
  refine ⟨fun θ u Φ => ?_, fun Φ => ?_, fun θ hθ u hu => ?_, fun θ u => ?_⟩
  · by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < 2
    · rw [zeroActBg_of_mem S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hc.1 hc.2, norm_mul, norm_pow]
      have hbd := (hT Φ).2 _ hc.1 u hc.2
      have hu2 : ‖u‖ ^ 2 ≤ 4 := by
        have := hc.2
        nlinarith [norm_nonneg u]
      calc ‖u‖ ^ 2 * ‖zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
            (S.hatOf m₀ ρ hp Φ) u (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)‖
          ≤ 4 * (|S.β| * (2 * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
            if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then Mω * (6 * b z / r ^ 3)
              else 0)) := by
            refine mul_le_mul hu2 (hbd.trans ?_) (norm_nonneg _) (by norm_num)
            exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc.2.le hsum0)
              (abs_nonneg _)
        _ = 8 * (|S.β| * ∑ z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))),
            if Y ∈ polyDom S.G' (X₁V z) m₀ (jV z) (𝒦XV z) then Mω * (6 * b z / r ^ 3)
              else 0) := by ring
    · rw [zeroActBg_of_not S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hc, norm_zero]
      have := abs_nonneg S.β
      positivity
  · -- the composite with `(θ, u) ↦ (θ.raw, u)` and `u²`
    let g : physParamBg N Gb × ℂ →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N × ℂ :=
      ((rawSub N Gb).subtypeL.comp (ContinuousLinearMap.fst ℂ _ _)).prodMap
        (ContinuousLinearMap.id ℂ ℂ)
    intro p hp'
    have hmem : g p ∈ XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ×ˢ ball (0 : ℂ) 2 :=
      ⟨hp'.1.1, hp'.2⟩
    have hA := ((hT Φ).1 (g p) hmem).comp_of_eq (g.analyticAt p) rfl
    have hA2 : AnalyticAt ℂ (fun q : physParamBg N Gb × ℂ => q.2 ^ 2 *
        zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ) (S.hatOf m₀ ρ hp Φ)
          (g q).2 (g q).1) p :=
      ((analyticAt_snd (𝕜 := ℂ)).pow 2).mul hA
    have hopen : IsOpen (physVBg N Gb S.a₁ S.ν eps ×ˢ ball (0 : ℂ) 2) := hV.prod isOpen_ball
    refine hA2.congr (Filter.eventually_of_mem (hopen.mem_nhds hp') fun q hq => ?_)
    exact (zeroActBg_of_mem S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω (ρ := ρ) hp eps hq.1.1
      (mem_ball_zero_iff.1 hq.2) Y Φ).symm
  · have e : zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y = fun Φ => u ^ 2 *
        zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
          (S.hatOf m₀ ρ hp Φ) u (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
      funext fun Φ => zeroActBg_of_mem S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hθ hu Y Φ
    rw [e]
    exact continuous_const.mul (hcontT _ hθ u hu)
  · by_cases hc : (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
        XiCRaw Gb (compWeight L S.a₁) S.ν (k + 1) 1 eps ∧ ‖u‖ < 2
    · have e : zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y = fun Φ => u ^ 2 *
          zeroTermBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω Y (S.hatOf m₀ ρ hp Φ)
            (S.hatOf m₀ ρ hp Φ) u (θ.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) :=
        funext fun Φ => zeroActBg_of_mem S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hc.1 hc.2 Y Φ
      rw [e]
      exact (continuous_const.mul (hcontT _ hc.1 u hc.2)).measurable
    · have e : zeroActBg S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω ρ hp eps θ u Y = fun _ => 0 :=
        funext fun Φ => zeroActBg_of_not S Gb Tr X₁V jV 𝒦XV m₀ F₁ Sol ω hp eps hc Y Φ
      rw [e]
      exact measurable_const

end ZeroFields

end Balaban.Fluctuation
