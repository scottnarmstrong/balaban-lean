/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Background.Def5
public import Balaban.Background.LinearResponse
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Def-5: the linear response of the background field and independence of `c₀`
(BACKGROUND.md §5.5, §7)

* `BgData.lineAt D E t`: the line `D + t E` in the (linear) space of data;
* `eventually_inDomainC_lineAt`: the domain `Ψ̃^c(δ, ε)` contains `D + t E` for small `t`;
* `theorem72_linearResponse` (Proposition 5.4 for `bgFieldC`): along every tangent datum `E`
  the pair `(bgFieldC, bgMultC)` is differentiable at `t = 0`, with
  `α̇ = [φ · G φ]⁻¹ φ · G Ṡ`, `φ̇ = (G - Π) Ṡ`, `Ṡ = source E`, `G = H_D(α)⁻¹`, `Π` the
  constrained operator, and the sup bounds of `φ̇` (smallness `δ ≤ bgC2`);
* `bgFieldC_eq_of_le`: `bgFieldC c₀ = bgFieldC (bgC0)` for `bgC0 ≤ c₀ ≤ c₆`.
-/

@[expose] public section

namespace Balaban.Background

open Balaban.Multiscale Matrix Finset Filter Topology

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

section Line

variable {G : GeneratingSet d L N₀ k ϱ}

/-- The line `t ↦ D + t E` in the space of data (`BgData` is a linear space of fields). -/
noncomputable def BgData.lineAt (D E : BgData G N) (t : ℂ) : BgData G N where
  Ψ := D.Ψ + t • E.Ψ
  h := D.h + t • E.h
  Ψ_layerConst := by
    intro n hn1 hnk x hx x' hx'
    simp only [Pi.add_apply, Pi.smul_apply, D.Ψ_layerConst n hn1 hnk x hx x' hx',
      E.Ψ_layerConst n hn1 hnk x hx x' hx']
  h_layerConst := by
    intro n hn1 hnk x hx x' hx'
    simp only [Pi.add_apply, Pi.smul_apply, D.h_layerConst n hn1 hnk x hx x' hx',
      E.h_layerConst n hn1 hnk x hx x' hx']
  Ψ_zero := fun x hx => by simp [D.Ψ_zero x hx, E.Ψ_zero x hx]
  h_zero := fun x hx => by simp [D.h_zero x hx, E.h_zero x hx]

theorem BgData.lineAt_zero (D E : BgData G N) : D.lineAt E 0 = D := by
  cases D; cases E
  simp [BgData.lineAt]

theorem eventually_lt_of_continuous {f : ℂ → ℝ} (hf : Continuous f) {c : ℝ} (h : f 0 < c) :
    ∀ᶠ t in 𝓝 (0 : ℂ), f t < c :=
  hf.continuousAt.eventually (gt_mem_nhds h)

variable {ν : ℝ}

/-- The domain `Ψ̃^c(δ, ε)` is open along every line of data. -/
theorem eventually_inDomainC_lineAt {δ ε : ℝ} {D : BgData G N} (hD : InDomainC G ν δ ε D)
    (E : BgData G N) : ∀ᶠ t in 𝓝 (0 : ℂ), InDomainC G ν δ ε (D.lineAt E t) := by
  classical
  obtain ⟨Ψ, h, Ψ', h', hP, hΨ, hh⟩ := hD
  have e1 : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x x', IsInterfacePair G x x' →
      vn ((Ψ' + t • E.Ψ) x - (Ψ' + t • E.Ψ) x') < δ := by
    refine Filter.eventually_all.2 fun x => Filter.eventually_all.2 fun x' => ?_
    by_cases hx : IsInterfacePair G x x'
    · have := hP.c1 x x' hx
      have h0 : vn ((Ψ' + (0 : ℂ) • E.Ψ) x - (Ψ' + (0 : ℂ) • E.Ψ) x') < δ := by
        simpa using this
      filter_upwards [eventually_lt_of_continuous
        (f := fun t : ℂ => vn ((Ψ' + t • E.Ψ) x - (Ψ' + t • E.Ψ) x'))
        (continuous_vn.comp (by simp only [Pi.add_apply, Pi.smul_apply]; fun_prop)) h0] with t ht
        using fun _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hx
  have e2 : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x ∈ dataSites G, vn ((Ψ' + t • E.Ψ) x) < ε + δ := by
    refine Filter.eventually_all.2 fun x => ?_
    by_cases hx : x ∈ dataSites G
    · have h0 : vn ((Ψ' + (0 : ℂ) • E.Ψ) x) < ε + δ := by simpa using hP.c2a x hx
      filter_upwards [eventually_lt_of_continuous
        (f := fun t : ℂ => vn ((Ψ' + t • E.Ψ) x))
        (continuous_vn.comp (by simp only [Pi.add_apply, Pi.smul_apply]; fun_prop)) h0] with t ht
        using fun _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hx
  have e3 : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x ∈ dataSites G,
      ‖∑ i, ((Ψ x i : ℂ) + (Ψ' + t • E.Ψ) x i) * ((Ψ x i : ℂ) + (Ψ' + t • E.Ψ) x i) -
        ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ < δ := by
    refine Filter.eventually_all.2 fun x => ?_
    by_cases hx : x ∈ dataSites G
    · have h0 : ‖∑ i, ((Ψ x i : ℂ) + (Ψ' + (0 : ℂ) • E.Ψ) x i) *
          ((Ψ x i : ℂ) + (Ψ' + (0 : ℂ) • E.Ψ) x i) - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖ < δ := by
        simpa using hP.c2b x hx
      filter_upwards [eventually_lt_of_continuous
        (f := fun t : ℂ => ‖∑ i, ((Ψ x i : ℂ) + (Ψ' + t • E.Ψ) x i) *
          ((Ψ x i : ℂ) + (Ψ' + t • E.Ψ) x i) - ∑ i, (Ψ x i : ℂ) * (Ψ x i : ℂ)‖)
        (by simp only [Pi.add_apply, Pi.smul_apply]; fun_prop) h0] with t ht using fun _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hx
  have e4 : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      vn ((h' + t • E.h) x) < δ ^ 2 / ε := by
    refine Filter.eventually_all.2 fun x => ?_
    by_cases hx : x ∈ G.Ω 1
    · have hcont : Continuous fun t : ℂ => (h' + t • E.h) x := by
        simp only [Pi.add_apply, Pi.smul_apply]; fun_prop
      have h0 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn ((h' + (0 : ℂ) • E.h) x) < δ ^ 2 / ε := by
        simpa using hP.c3a x hx
      filter_upwards [eventually_lt_of_continuous
        (f := fun t : ℂ => ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 * vn ((h' + t • E.h) x))
        (continuous_const.mul (continuous_vn.comp hcont)) h0] with t ht using fun _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hx
  have e5 : ∀ᶠ t in 𝓝 (0 : ℂ), ∀ x ∈ G.Ω 1, ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
      ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * (h' + t • E.h) x i‖ < δ ^ 2 := by
    refine Filter.eventually_all.2 fun x => ?_
    by_cases hx : x ∈ G.Ω 1
    · have h0 : ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
          ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * (h' + (0 : ℂ) • E.h) x i‖ < δ ^ 2 := by
        simpa using hP.c3b x hx
      filter_upwards [eventually_lt_of_continuous
        (f := fun t : ℂ => ν * ((L : ℝ) ^ G.layerIndex x) ^ 2 *
          ‖∑ i, ((Ψ x i / rn (Ψ x) : ℝ) : ℂ) * (h' + t • E.h) x i‖)
        (by simp only [Pi.add_apply, Pi.smul_apply]; fun_prop) h0] with t ht using fun _ => ht
    · exact Filter.Eventually.of_forall fun t h => absurd h hx
  filter_upwards [e1, e2, e3, e4, e5] with t t1 t2 t3 t4 t5
  refine ⟨Ψ, h, Ψ' + t • E.Ψ, h' + t • E.h, ?_, ?_, ?_⟩
  · exact
      { toInPsiTilde := hP.toInPsiTilde
        eps_pos := hP.eps_pos
        layerConst' := by
          intro n hn1 hnk x hx x' hx'
          simp only [Pi.add_apply, Pi.smul_apply, hP.layerConst' n hn1 hnk x hx x' hx',
            E.Ψ_layerConst n hn1 hnk x hx x' hx']
        hLayerConst' := by
          intro n hn1 hnk x hx x' hx'
          simp only [Pi.add_apply, Pi.smul_apply, hP.hLayerConst' n hn1 hnk x hx x' hx',
            E.h_layerConst n hn1 hnk x hx x' hx']
        c1 := t1
        c2a := t2
        c2b := t3
        c3a := t4
        c3b := t5 }
  · intro x hx i
    simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, hΨ x hx i]
    ring
  · intro x hx i
    simp only [BgData.lineAt, Pi.add_apply, Pi.smul_apply, hh x hx i]
    ring

end Line

section Response

variable (d L N)

/-- The smallness `c₂ ≤ c₁` under which the linear response is available: `K₁ δ` is below the
smallness `δ` of the constraint sandwich and the constrained-operator sup bounds. -/
noncomputable def bgC2 : ℝ :=
  min (bgC1 d L N) (1 / (2 * bgK1 d L N * (1 + smallnessConst d + sandwichConst d L N)))

theorem bgC2_le_bgC1 : bgC2 d L N ≤ bgC1 d L N := min_le_left _ _

variable {d L N}

theorem smallnessConst_nonneg (hd : 0 < d) : 0 ≤ smallnessConst d := by
  unfold smallnessConst
  have := poincareConst_inv_nonneg hd
  positivity

theorem InUnionDomainC.mono {G : GeneratingSet d L N₀ k ϱ} {c₀ c₁ c₁' ν : ℝ} {D : BgData G N}
    (h : c₁ ≤ c₁') (hD : InUnionDomainC G c₀ c₁ ν D) : InUnionDomainC G c₀ c₁' ν D := by
  obtain ⟨δ, ε, h1, h2, h3, h4, h5, h6⟩ := hD
  exact ⟨δ, ε, h1, h2, h3, h4.trans h, h5, h6⟩

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The standing hypotheses of the constrained operator hold for the small solution:
`Φ = φ̄` (extension by `Ψ`), `α = bgMultC`, constant `K₁ δ`, once `δ ≤ c₂`. -/
theorem standing_bgFieldC (H : BgHyp d L k ϱ a ν) {δ ε : ℝ} {D : BgData G N} (hδ0 : 0 < δ)
    (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N) (hδ : δ ≤ bgC2 d L N)
    (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2) (hDC : InDomainC G ν δ ε D) :
    Standing G a ν (bgMultC G a ν (bgC0 d L N) D) (bgK1 d L N * δ)
      (fun y i => barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) y i) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨W⟩ := DataWit.exists hDC
  have hδ1 : δ ≤ bgC1 d L N := hδ.trans (bgC2_le_bgC1 d L N)
  obtain ⟨φ, α, hs, hb, -, hu⟩ := bg_core H hδ0 hδε hε hδ1 hνε W
  obtain ⟨hf, hm⟩ := bgFieldC_eq hs hu
  rw [hf, hm]
  have hK := bgK1_pos d L N
  have hK0 : 0 ≤ bgK1 d L N * δ := by positivity
  have hS0 := smallnessConst_nonneg (d := d) hd0
  have hSw := sandwichConst_nonneg d L N
  have hQ : δ * (2 * bgK1 d L N * (1 + smallnessConst d + sandwichConst d L N)) ≤ 1 := by
    have := hδ.trans (min_le_right _ _)
    rwa [le_div_iff₀ (by positivity)] at this
  obtain ⟨-, -, -, hK32⟩ := bgC1_facts d L N hd0 hδ1
  have hc0 : bgC0 d L N ≤ 1 / 16 := bgC0_le d L N
  refine ⟨hd0, H.mass, H.weights, fun x => ?_, ?_, hK0, ?_⟩
  · have h1 := hs.2 x
    have h2 : bgC0 d L N ≤ coerciveConst d / 8 := by
      have := (bgC0_le_c6 d L N)
      have h3 : c6 d L N ≤ gamma1 d / 4 := min_le_left _ _
      unfold gamma1 at h3
      linarith
    have hp : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by
      have := spacing_pos (G := G) (x := (x : Torus d (N₀ * L ^ k))); positivity
    have hcc := coerciveConst_pos hd0
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  · refine
      { grad := fun x hx μ => hb.grad ⟨x, hx⟩ μ
        lap := fun x hx => hb.lap ⟨x, hx⟩
        bound := fun x hx => ?_
        sq := fun x hx => ?_ }
    · have hxd : x ∈ dataSites G := (mem_dataSites G).2 (Or.inl hx)
      have e : (fun i => barField G D.Ψ φ x i) =
          (fun i => φ (⟨x, hx⟩, i) - D.Ψ x i) + D.Ψ x := by
        funext i; simp [barField, hx]
      show vn (fun i => barField G D.Ψ φ x i) ≤ 3 / 2
      rw [e]
      have h1 := vn_add (fun i => φ (⟨x, hx⟩, i) - D.Ψ x i) (D.Ψ x)
      have h2 := hb.val ⟨x, hx⟩
      have h3 := W.vn_le hδ0 hxd
      have : δ ≤ 1 / 16 := hδε.trans (hε.trans hc0)
      linarith
    · have := hs.1.2 ⟨x, hx⟩
      have e : ∑ i, barField G D.Ψ φ x i * barField G D.Ψ φ x i - 1 = 0 := by
        simp only [barField, hx, dite_true]; rw [this]; ring
      show ‖∑ i, barField G D.Ψ φ x i * barField G D.Ψ φ x i - 1‖ ≤ bgK1 d L N * δ
      rw [e]; simpa using hK0
  · have hδ' : bgK1 d L N * δ ≤ 1 / 2 := by nlinarith
    have : bgK1 d L N * δ * (2 * (1 + smallnessConst d + sandwichConst d L N)) ≤ 1 := by
      nlinarith
    nlinarith

end Response

section Main

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The operator `H_D(α)` of the background field `(bgFieldC, bgMultC)`. -/
noncomputable def bgOp (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) : Matrix (G.Ω 1) (G.Ω 1) ℂ :=
  dirichletOperator G a ν (bgMultC G a ν (bgC0 d L N) D)

/-- The background field `bgFieldC` as a vector field `Ω₁ → ℂ^N`. -/
noncomputable def bgVec (a : ℕ → ℝ) (ν : ℝ) (D : BgData G N) : G.Ω 1 → Fin N → ℂ :=
  fun x i => bgFieldC G a ν (bgC0 d L N) D (x, i)

/-- The data sit in `𝒟`, where `bgFieldC` is analytic, so the pair is differentiable along every
line of data. -/
theorem hasDerivAt_bgFieldC (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) (E : BgData G N) :
    ∃ (φd : G.Ω 1 × Fin N → ℂ) (αd : G.Ω 1 → ℂ),
      HasDerivAt (fun t : ℂ => bgFieldC G a ν (bgC0 d L N) (D.lineAt E t)) φd 0 ∧
      HasDerivAt (fun t : ℂ => bgMultC G a ν (bgC0 d L N) (D.lineAt E t)) αd 0 := by
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  set line : ℂ → RawData d L N₀ k N := fun t => (D.Ψ + t • E.Ψ, D.h + t • E.h) with hline
  have h0 : line 0 = (D.Ψ, D.h) := by simp [hline]
  have hFat : AnalyticAt ℂ F (line 0) := by
    rw [h0]; exact hF _ ⟨D, hD, rfl⟩
  have hl : AnalyticAt ℂ line 0 := by
    refine AnalyticAt.prod ?_ ?_
    · exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
    · exact analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hcomp : AnalyticAt ℂ (F ∘ line) 0 := hFat.comp hl
  have hder := hcomp.differentiableAt.hasDerivAt
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD
  have hev : ∀ᶠ t in 𝓝 (0 : ℂ), (fun t => (bgFieldC G a ν (bgC0 d L N) (D.lineAt E t),
      bgMultC G a ν (bgC0 d L N) (D.lineAt E t))) t = (F ∘ line) t := by
    filter_upwards [eventually_inDomainC_lineAt hDC E] with t ht
    exact (hFe (D.lineAt E t) ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, ht⟩).symm
  have hder' := hder.congr_of_eventuallyEq hev
  have h1 := (hasFDerivAt_fst (𝕜 := ℂ)).comp_hasDerivAt (0 : ℂ) hder'
  have h2 := (hasFDerivAt_snd (𝕜 := ℂ)).comp_hasDerivAt (0 : ℂ) hder'
  exact ⟨(deriv (F ∘ line) 0).1, (deriv (F ∘ line) 0).2, h1, h2⟩

/-- **Proposition 5.4 for `bgFieldC`** (BACKGROUND.md §5.5).  Let `D` be data of the union domain
with parameters `δ ≤ c₂` and `E` a tangent datum.  Then `t ↦ (bgFieldC, bgMultC)(D + t E)` is
differentiable at `t = 0`, with derivative `(φ̇, α̇)` given by
`α̇ = [φ · G φ]⁻¹ φ · G Ṡ`, `φ̇ = (G − Π) Ṡ`, where `Ṡ = source E`, `G = H_D(α)⁻¹`,
`Π = constrainedOp G φ`, `(φ, α) = (bgFieldC, bgMultC) D`.  Moreover, if `ℓ² |Ṡ| ≤ C`, then
`|φ̇|₀, |∂φ̇|₁, |Δ^D φ̇|₂ ≤ (B + B₁') C` (`SupBounds`). -/
theorem theorem72_linearResponse (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC2 d L N) ν D) (E : BgData G N) :
    ∃ (φd : G.Ω 1 × Fin N → ℂ) (αd : G.Ω 1 → ℂ),
      HasDerivAt (fun t : ℂ => bgFieldC G a ν (bgC0 d L N) (D.lineAt E t)) φd 0 ∧
      HasDerivAt (fun t : ℂ => bgMultC G a ν (bgC0 d L N) (D.lineAt E t)) αd 0 ∧
      αd = (constraintForm (bgOp a ν D)⁻¹ (bgVec a ν D))⁻¹ *ᵥ
        ((fieldMul (bgVec a ν D))ᵀ *ᵥ (liftOp N (bgOp a ν D)⁻¹ *ᵥ source G a ν E)) ∧
      φd = (liftOp N (bgOp a ν D)⁻¹ - constrainedOp (bgOp a ν D)⁻¹ (bgVec a ν D)) *ᵥ
        source G a ν E ∧
      ∀ {C : ℝ}, 0 ≤ C → SrcBound G (source G a ν E) C →
        SupBounds G φd ((greenSupConst d L + piSupConst d L N) * C) := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨δ, ε, hδ0, hδε, hε, hδc, hνε, hDC⟩ := hD
  have hD1 : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D :=
    ⟨δ, ε, hδ0, hδε, hε, hδc.trans (bgC2_le_bgC1 d L N), hνε, hDC⟩
  obtain ⟨φd, αd, h1, h2⟩ := hasDerivAt_bgFieldC H hD1 E
  have St := standing_bgFieldC H hδ0 hδε hε hδc hνε hDC
  -- the source is affine in the data
  have hΨ : HasDerivAt (fun t : ℂ => D.Ψ + t • E.Ψ) E.Ψ 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const E.Ψ).const_add D.Ψ
  have hh : HasDerivAt (fun t : ℂ => D.h + t • E.h) E.h 0 := by
    simpa using ((hasDerivAt_id (0 : ℂ)).smul_const E.h).const_add D.h
  have hS : HasDerivAt (fun t : ℂ => source G a ν (D.lineAt E t)) (source G a ν E) 0 :=
    source_hasDerivAt G a ν hΨ hh
  have hEL : ∀ᶠ t in 𝓝 (0 : ℂ),
      liftOp N (dirichletOperator G a ν (bgMultC G a ν (bgC0 d L N) (D.lineAt E t))) *ᵥ
          (fun p => bgFieldC G a ν (bgC0 d L N) (D.lineAt E t) p) = source G a ν (D.lineAt E t) ∧
        ∀ z : G.Ω 1, ∑ i, bgFieldC G a ν (bgC0 d L N) (D.lineAt E t) (z, i) *
          bgFieldC G a ν (bgC0 d L N) (D.lineAt E t) (z, i) = 1 := by
    filter_upwards [eventually_inDomainC_lineAt hDC E] with t ht
    exact (theorem72 H ⟨δ, ε, hδ0, hδε, hε, hδc.trans (bgC2_le_bgC1 d L N), hνε, ht⟩).2.1.1
  have hφ₀ : ∀ (z : G.Ω 1) (i : Fin N),
      bgFieldC G a ν (bgC0 d L N) (D.lineAt E 0) (z, i) =
        restrictField G (fun y i => barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) y i) z i := by
    intro z i
    rw [BgData.lineAt_zero]
    simp [restrictField, barField]
  have hα₀ : bgMultC G a ν (bgC0 d L N) (D.lineAt E 0) = bgMultC G a ν (bgC0 d L N) D := by
    rw [BgData.lineAt_zero]
  have hresp := linearResponse (α₀ := bgMultC G a ν (bgC0 d L N) D) (δ := bgK1 d L N * δ)
    (Φ := fun y i => barField G D.Ψ (bgFieldC G a ν (bgC0 d L N) D) y i)
    (S := fun t => source G a ν (D.lineAt E t))
    (φ := fun t => bgFieldC G a ν (bgC0 d L N) (D.lineAt E t))
    (α := fun t => bgMultC G a ν (bgC0 d L N) (D.lineAt E t)) (t₀ := 0)
    St hS h1 h2 hα₀ hφ₀ hEL
  have hrestrict : restrictField G (fun y i => barField G D.Ψ
      (bgFieldC G a ν (bgC0 d L N) D) y i) = bgVec a ν D := by
    funext z i
    simp [restrictField, barField, bgVec]
  have e1 : αd = (constraintForm (bgOp a ν D)⁻¹ (bgVec a ν D))⁻¹ *ᵥ
        ((fieldMul (bgVec a ν D))ᵀ *ᵥ (liftOp N (bgOp a ν D)⁻¹ *ᵥ source G a ν E)) := by
    rw [← hrestrict]; exact hresp.1
  have e2 : φd = (liftOp N (bgOp a ν D)⁻¹ - constrainedOp (bgOp a ν D)⁻¹ (bgVec a ν D)) *ᵥ
        source G a ν E := by
    rw [← hrestrict]; exact hresp.2
  refine ⟨φd, αd, h1, h2, e1, e2, fun {C} hC hSd => ?_⟩
  have hsep := (H.green (G := G)).sep
  have hδK : (1 + sandwichConst d L N) * (bgK1 d L N * δ) ≤ 1 / 2 := by
    have hK := bgK1_pos d L N
    have hS0 := smallnessConst_nonneg (d := d) hd0
    have hSw := sandwichConst_nonneg d L N
    have hQ : δ * (2 * bgK1 d L N * (1 + smallnessConst d + sandwichConst d L N)) ≤ 1 := by
      have := hδc.trans (min_le_right _ _)
      rwa [le_div_iff₀ (by positivity)] at this
    nlinarith [mul_nonneg hK.le hδ0.le, mul_nonneg (mul_nonneg hK.le hδ0.le) hSw]
  exact linearResponse_sup H.hd H.hL St H.massLe hsep hδK hC hSd hresp.2

end Main

section Tangent

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- The tangent source `Ṡ = source E` of a tangent datum with `|Ψ̇|, |ḣ| ≤ M` obeys
`ℓ² |Ṡ| ≤ (3 + 2 d L²) M` (the first term of `S` costs `2 M`, the mass term `M`, and the collar
sites only occur next to sites of spacing `L`). -/
theorem srcBound_source (H : BgHyp d L k ϱ a ν) (E : BgData G N) {M : ℝ} (hM : 0 ≤ M)
    (hΨ : ∀ y i, ‖E.Ψ y i‖ ≤ M) (hh : ∀ y i, ‖E.h y i‖ ≤ M) :
    SrcBound G (source G a ν E) ((3 + 2 * d * (L : ℝ) ^ 2) * M) := by
  classical
  intro x i
  have hℓ : 0 < G.spacing (x : Torus d (N₀ * L ^ k)) := spacing_pos (G := G)
  have hL0 : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hL2 : 2 ≤ L := by have := H.hL; omega
  obtain ⟨hn1, hnk, -⟩ := G.layerIndex_spec x.2
  set n := G.layerIndex (x : Torus d (N₀ * L ^ k)) with hn
  have hsp : G.spacing (x : Torus d (N₀ * L ^ k)) = (L : ℝ) ^ n := rfl
  have han := H.weights n hn1 hnk
  have hq : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖qStar G a E.Ψ (x, i)‖ ≤ 2 * M := by
    unfold qStar
    rw [← hn]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (div_nonneg (by linarith [han.1]) (sq_nonneg _))]
    have e : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 *
        (a n / ((L : ℝ) ^ n) ^ 2 * ‖E.Ψ x i‖) = a n * ‖E.Ψ x i‖ := by
      rw [hsp]; field_simp
    rw [e]
    nlinarith [hΨ x i, han.2, norm_nonneg (E.Ψ x i)]
  have hm : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖(ν : ℂ) * E.h x i‖ ≤ M := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg H.mass]
    have h1 : G.spacing (x : Torus d (N₀ * L ^ k)) ≤ (L : ℝ) ^ k := spacing_le G x.2
    have h2 : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ ((L : ℝ) ^ k) ^ 2 :=
      pow_le_pow_left₀ hℓ.le h1 2
    have h3 := hh x i
    have h4 := H.massLe
    have h5 := H.mass
    calc G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * (ν * ‖E.h x i‖)
        ≤ ((L : ℝ) ^ k) ^ 2 * (ν * M) := by
          apply mul_le_mul h2 (mul_le_mul_of_nonneg_left h3 h5) (by positivity) (by positivity)
      _ = (ν * ((L : ℝ) ^ k) ^ 2) * M := by ring
      _ ≤ 1 * M := mul_le_mul_of_nonneg_right h4 hM
      _ = M := one_mul M
  have hite : ∀ y : Torus d (N₀ * L ^ k), Adj (x : Torus d (N₀ * L ^ k)) y →
      G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖if y ∈ collar G then E.Ψ y i else 0‖ ≤
        (L : ℝ) ^ 2 * M := by
    intro y hy
    by_cases hc : y ∈ collar G
    · have hs := spacing_eq_L_of_collar (G := G) (H.green (G := G)).sep_gt_one hL2 hc hy
      simp only [hc, ↓reduceIte]
      rw [hs]
      exact mul_le_mul_of_nonneg_left (hΨ y i) (by positivity)
    · simp only [hc, ↓reduceIte, norm_zero, mul_zero]
      positivity
  have hb : G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖boundaryTerm G E.Ψ (x, i)‖ ≤
      (2 * d * (L : ℝ) ^ 2) * M := by
    unfold boundaryTerm
    have hsum := norm_sum_le (Finset.univ : Finset (Fin d)) (fun μ =>
      ((if (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
          E.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i else 0) +
        (if (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
          E.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i else 0)))
    refine (mul_le_mul_of_nonneg_left hsum (by positivity)).trans ?_
    rw [Finset.mul_sum]
    calc ∑ μ : Fin d, G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖_‖
        ≤ ∑ _μ : Fin d, 2 * ((L : ℝ) ^ 2 * M) := by
          refine Finset.sum_le_sum fun μ _ => ?_
          have h1 := hite _ (adj_add (x : Torus d (N₀ * L ^ k)) μ)
          have h2 := hite _ (adj_sub (x : Torus d (N₀ * L ^ k)) μ)
          have h3 := norm_add_le
            (if (x : Torus d (N₀ * L ^ k)) + Pi.single μ 1 ∈ collar G then
              E.Ψ ((x : Torus d (N₀ * L ^ k)) + Pi.single μ 1) i else 0)
            (if (x : Torus d (N₀ * L ^ k)) - Pi.single μ 1 ∈ collar G then
              E.Ψ ((x : Torus d (N₀ * L ^ k)) - Pi.single μ 1) i else 0)
          nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity :
            (0 : ℝ) ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2)]
      _ = (2 * d * (L : ℝ) ^ 2) * M := by simp; ring
  have hS : source G a ν E (x, i) = qStar G a E.Ψ (x, i) + (ν : ℂ) * E.h x i +
      boundaryTerm G E.Ψ (x, i) := rfl
  rw [hS]
  have t1 := norm_add_le (qStar G a E.Ψ (x, i) + (ν : ℂ) * E.h x i) (boundaryTerm G E.Ψ (x, i))
  have t2 := norm_add_le (qStar G a E.Ψ (x, i)) ((ν : ℂ) * E.h x i)
  have hp : 0 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left t1 hp, mul_le_mul_of_nonneg_left t2 hp]

end Tangent

section Independence

variable {G : GeneratingSet d L N₀ k ϱ} {a : ℕ → ℝ} {ν : ℝ}

/-- **Independence of `c₀`** (BACKGROUND.md §7): for data of the union domain `𝒟` and every
`c₀` with `bgC0 ≤ c₀ ≤ c₆`, the small solution in the class `|α|₂ < c₀` is the one in the class
`|α|₂ < bgC0`; so `bgFieldC c₀` and `bgMultC c₀` do not depend on `c₀` in this range. -/
theorem bgFieldC_eq_of_le (H : BgHyp d L k ϱ a ν) {D : BgData G N}
    (hD : InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν D) {c₀ : ℝ} (h1 : bgC0 d L N ≤ c₀)
    (h2 : c₀ ≤ c6 d L N) :
    bgFieldC G a ν c₀ D = bgFieldC G a ν (bgC0 d L N) D ∧
      bgMultC G a ν c₀ D = bgMultC G a ν (bgC0 d L N) D := by
  have hd0 : 0 < d := by have := H.hd; omega
  obtain ⟨δ, ε, hδ0, hδε, hε, hδ, hνε, hDC⟩ := hD
  obtain ⟨W⟩ := DataWit.exists hDC
  obtain ⟨φ, α, hs, -, -, hu0⟩ := bg_core H hδ0 hδε hε hδ hνε W
  obtain ⟨hδa, h2', hC32, hK⟩ := bgC1_facts d L N hd0 hδ
  have hC0 := lemma53Const_pos d L
  have hCδ : 0 ≤ lemma53Const d L * δ := by positivity
  have hdelta := approxDelta_le d L hδa
  have S : ApproxSetting d L k ϱ a ν δ ε :=
    H.approxSetting hδ0 hδε (hε.trans (bgC0_le d L N)) hdelta.1 hνε
  have hyp := prop51Hyp_of_data (N := N) H S hδa W (by linarith) hC32
  obtain ⟨δφ, δα, hP, hSm, hSup, huniq⟩ := prop51_exists_unique hd0 hyp
  rw [pertSource_zeroΨ] at huniq
  have hs' : IsSmallSolution G a ν c₀ D φ α := ⟨hs.1, fun x => (hs.2 x).trans_le h1⟩
  have hu' : ∀ (φ' : G.Ω 1 × Fin N → ℂ) (α' : G.Ω 1 → ℂ),
      IsSmallSolution G a ν c₀ D φ' α' → φ' = φ ∧ α' = α := by
    intro φ' α' hsol
    obtain ⟨hEL, hα'⟩ := hsol
    have hper := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField G a ν D.Ψ D.h)
      (fun p => φ' p - approxField G a ν D.Ψ D.h p.1 p.2) α').2 (by
        convert hEL using 2; ring)
    have hsm : Small G α' (c6 d L N) := fun x => ((hα' x).trans_le h2).le
    obtain ⟨e1, e2⟩ := huniq _ _ hper hsm
    have e3 : (fun p => φ' p - approxField G a ν D.Ψ D.h p.1 p.2) =
        (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) := by
      -- both sides are the increment of the solution of Proposition 5.1
      have hper0 := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField G a ν D.Ψ D.h)
        (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) α).2 (by
          convert hs.1 using 2; ring)
      have hsm0 : Small G α (c6 d L N) := fun x => ((hs.2 x).trans_le (bgC0_le_c6 d L N)).le
      obtain ⟨f1, f2⟩ := huniq _ _ hper0 hsm0
      rw [e1, f1]
    refine ⟨?_, ?_⟩
    · funext p
      have := congrFun e3 p
      linear_combination this
    · have hsm0 : Small G α (c6 d L N) := fun x => ((hs.2 x).trans_le (bgC0_le_c6 d L N)).le
      have hper0 := (isPerturbed_iff_isEL (a := a) (ν := ν) D (approxField G a ν D.Ψ D.h)
        (fun p => φ p - approxField G a ν D.Ψ D.h p.1 p.2) α).2 (by
          convert hs.1 using 2; ring)
      obtain ⟨f1, f2⟩ := huniq _ _ hper0 hsm0
      rw [e2, f2]
  obtain ⟨a1, a2⟩ := bgFieldC_eq hs' hu'
  obtain ⟨b1, b2⟩ := bgFieldC_eq hs hu0
  exact ⟨a1.trans b1.symm, a2.trans b2.symm⟩

end Independence

end Balaban.Background
