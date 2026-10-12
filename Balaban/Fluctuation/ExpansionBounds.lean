module

public import Balaban.Fluctuation.ExpansionQuad
public import Balaban.Fluctuation.ExpansionDomain
public import Balaban.Fluctuation.ExpansionCauchy
public import Balaban.SmallField.TaylorCauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Lemma 2.3 (d): the bounds

* `bounds_abstract`: for a datum `B` in the domain of the linear response, a datum `D` at distance
  `≤ s`, and the disc `{B + t (D - B) : |t| < R}` in the domain `𝒟`: the perturbation
  `φ_D - φ_B` and the linear response `φ¹` of `B` to the tangent `D - B` are bounded by `K₂ s`
  (`K₂ = cK2`), and `φ_D - φ_B - φ¹` by `2 K₂ s / R = 2 K₂ s² / ρ`, `ρ = R s`
  (BG Proposition 5.1 for the first bound, Cauchy estimates for the others, as P6 (4.4));
* `expansion_bounds`: the bounds of Lemma 2.3 (d) for `φ'`, `α'`, `(φ¹, α¹)`, `φ₂`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Metric Set Filter Topology Balaban.SmallField

section Abstract

open Balaban.Multiscale Balaban.Background Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}
  {a : ℕ → ℝ} {ν : ℝ}

/-- The tangent datum `D - B` (with `h̃ = 0`). -/
noncomputable def tangentData (D B : BgData G N) : BgData G N where
  Ψ := fun x i => D.Ψ x i - B.Ψ x i
  h := 0
  Ψ_layerConst := by
    intro n hn1 hnk x hx x' hx'
    funext i
    have h1 := congrFun (D.Ψ_layerConst n hn1 hnk x hx x' hx') i
    have h2 := congrFun (B.Ψ_layerConst n hn1 hnk x hx x' hx') i
    simp only [h1, h2]
  h_layerConst := by
    intro n hn1 hnk x hx x' hx'
    rfl
  Ψ_zero := by
    intro x hx
    funext i
    simp [D.Ψ_zero x hx, B.Ψ_zero x hx]
  h_zero := by
    intro x hx
    rfl

theorem lineAt_tangent (D B : BgData G N) (hh : D.h = B.h) : B.lineAt (tangentData D B) 1 = D := by
  cases D with
  | mk DΨ Dh DL Dhl Dz Dhz =>
    cases B with
    | mk BΨ Bh BL Bhl Bz Bhz =>
      simp only [BgData.lineAt, tangentData, one_smul] at hh ⊢
      congr 1
      · funext x i; simp
      · simp [hh.symm]

theorem vn_smul' (t : ℂ) (v : Fin N → ℂ) : vn (t • v) = ‖t‖ * vn v := by
  unfold vn
  have : (WithLp.toLp 2 (t • v) : EuclideanSpace ℂ (Fin N)) = t • (WithLp.toLp 2 v) := rfl
  rw [this, norm_smul]

/-- **The Cauchy-estimate bounds along a line of data** (the abstract form of Lemma 2.3 (d)).  Let
`B` be a datum in `Ψ̃^c(δ₀, ε₀)` that is also in the domain of the linear response, `D` another datum
with the same `h̃` and `vn (D.Ψ - B.Ψ) ≤ s` pointwise, and suppose the disc
`{B + t (D - B) : |t| < R}` (`R ≥ 2`) lies in the domain `𝒟`, with the smallness of Proposition 5.1
for `R s`.  Then, for `φ' = φ_D - φ_B`, `α' = α_D - α_B` and the linear response `(φ¹, α¹)` of `B` to
the tangent `D - B`, with `K₂ = cK2`: `‖φ'‖_*, |α'|₂ ≤ K₂ s`, `‖φ¹‖_*, |α¹|₂ ≤ K₂ s`, and
`‖φ' - φ¹‖_*, |α' - α¹|₂ ≤ 2 K₂ s / R` (= `2 K₂ s² / ρ` with `ρ = R s`). -/
theorem bounds_abstract (H : BgHyp d L K ϱ a ν) {B D : BgData G N} {δ0 ε0 : ℝ}
    (hδ0 : 0 < δ0) (hδε : δ0 ≤ ε0) (hε : ε0 ≤ bgC0 d L N) (hδ : δ0 ≤ bgC1 d L N)
    (hνε : ν * ((L : ℝ) ^ K) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2) (hB : InDomainC G ν δ0 ε0 B)
    (hK1s : bgK1 d L N * δ0 ≤ deltaStar d L N)
    (hBC2 : InUnionDomainC G (bgC0 d L N) (bgC2 d L N) ν B)
    (hh : D.h = B.h) {s R : ℝ} (hs : 0 ≤ s) (hR : 2 ≤ R)
    (hΨs : ∀ x, vn (D.Ψ x - B.Ψ x) ≤ s)
    (hdisc : ∀ t : ℂ, ‖t‖ < R →
      InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν (B.lineAt (tangentData D B) t))
    (hRs : R * s ≤ deltaStar d L N)
    (hsmall : bgK1 d L N * δ0 + cK2 d L N * (R * s) < bgC0 d L N) :
    (SupBounds G (bgFieldC G a ν (bgC0 d L N) D - bgFieldC G a ν (bgC0 d L N) B)
        (cK2 d L N * s) ∧
      Small G (bgMultC G a ν (bgC0 d L N) D - bgMultC G a ν (bgC0 d L N) B) (cK2 d L N * s)) ∧
    ∃ (φ1 : G.Ω 1 × Fin N → ℂ) (α1 : G.Ω 1 → ℂ),
      φ1 = (liftOp N (bgOp a ν B)⁻¹ - constrainedOp (bgOp a ν B)⁻¹ (bgVec a ν B)) *ᵥ
        source G a ν (tangentData D B) ∧
      α1 = (constraintForm (bgOp a ν B)⁻¹ (bgVec a ν B))⁻¹ *ᵥ
        ((fieldMul (bgVec a ν B))ᵀ *ᵥ (liftOp N (bgOp a ν B)⁻¹ *ᵥ source G a ν (tangentData D B))) ∧
      SupBounds G φ1 (cK2 d L N * s) ∧ Small G α1 (cK2 d L N * s) ∧
      SupBounds G (bgFieldC G a ν (bgC0 d L N) D - bgFieldC G a ν (bgC0 d L N) B - φ1)
        (2 * (cK2 d L N * s) / R) ∧
      Small G (bgMultC G a ν (bgC0 d L N) D - bgMultC G a ν (bgC0 d L N) B - α1)
        (2 * (cK2 d L N * s) / R) := by
  have hd0 : 0 < d := by have := H.hd; omega
  have hR0 : 0 < R := by linarith
  have hK2 : 0 ≤ cK2 d L N := (cK2_pos (d := d) (L := L) (N := N)).le
  set E := tangentData D B with hE
  set c0 := bgC0 d L N with hc0
  have hhE : ∀ t : ℂ, (B.lineAt E t).h = B.h := fun t => by
    simp [BgData.lineAt, hE, tangentData]
  have hpert : ∀ t : ℂ, ‖t‖ < R → ∃ (δφ : G.Ω 1 × Fin N → ℂ) (δα : G.Ω 1 → ℂ),
      SupBounds G δφ (cK2 d L N * (‖t‖ * s)) ∧ Small G δα (cK2 d L N * (‖t‖ * s)) ∧
      bgFieldC G a ν c0 (B.lineAt E t) = bgFieldC G a ν c0 B + δφ ∧
      bgMultC G a ν c0 (B.lineAt E t) = bgMultC G a ν c0 B + δα := by
    intro t ht
    have h1 : 0 ≤ ‖t‖ * s := mul_nonneg (norm_nonneg t) hs
    have hts : ‖t‖ * s ≤ R * s := mul_le_mul_of_nonneg_right ht.le hs
    obtain ⟨δφ, δα, hsup, hsm, hf, hm⟩ := theorem52_perturb_eq H hδ0 hδε hε hδ hνε hB (hdisc t ht)
      (hhE t) h1 (hts.trans hRs) hK1s
      (fun x _ => by
        have e : (B.lineAt E t).Ψ x - B.Ψ x = t • (D.Ψ x - B.Ψ x) := by
          simp [BgData.lineAt, hE, tangentData]
          rfl
        rw [e, vn_smul']
        exact mul_le_mul_of_nonneg_left (hΨs x) (norm_nonneg t))
      (by nlinarith [mul_le_mul_of_nonneg_left hts hK2])
    exact ⟨δφ, δα, hsup, hsm, hf, hm⟩
  obtain ⟨F, hF, hFe⟩ := theorem72_analytic (G := G) (a := a) (ν := ν) H
  let γ : ℂ → RawData d L N₀ K N := fun t => ((B.lineAt E t).Ψ, (B.lineAt E t).h)
  have hγ : ∀ t, AnalyticAt ℂ γ t := fun t => by
    show AnalyticAt ℂ (fun t : ℂ => (B.Ψ + t • E.Ψ, B.h + t • E.h)) t
    exact (analyticAt_const.add (analyticAt_id.smul analyticAt_const)).prod
      (analyticAt_const.add (analyticAt_id.smul analyticAt_const))
  have hFl : ∀ t ∈ ball (0 : ℂ) R, AnalyticAt ℂ (fun t => F (γ t)) t := fun t ht =>
    (hF (γ t) ⟨B.lineAt E t, hdisc t (by simpa using ht), rfl⟩).comp (hγ t)
  have hFeq : ∀ t ∈ ball (0 : ℂ) R, F (γ t) =
      (bgFieldC G a ν c0 (B.lineAt E t), bgMultC G a ν c0 (B.lineAt E t)) := fun t ht =>
    hFe _ (hdisc t (by simpa using ht))
  have h0mem : (0 : ℂ) ∈ ball (0 : ℂ) R := mem_ball_self hR0
  have hF0 : F (γ 0) = (bgFieldC G a ν c0 B, bgMultC G a ν c0 B) := by
    rw [hFeq 0 h0mem, BgData.lineAt_zero]
  -- the linear response
  obtain ⟨φd, αd, hφd, hαd, hαform, hφform, -⟩ := theorem72_linearResponse H hBC2 E
  set Φ : ℂ → G.Ω 1 × Fin N → ℂ := fun t => (F (γ t)).1 - (F (γ 0)).1 with hΦ
  set Λ : ℂ → G.Ω 1 → ℂ := fun t => (F (γ t)).2 - (F (γ 0)).2 with hΛ
  have hΦan : AnalyticOnNhd ℂ Φ (ball 0 R) := fun t ht =>
    (((ContinuousLinearMap.fst ℂ (G.Ω 1 × Fin N → ℂ) (G.Ω 1 → ℂ)).analyticAt _).comp (hFl t ht)).sub
      analyticAt_const
  have hΛan : AnalyticOnNhd ℂ Λ (ball 0 R) := fun t ht =>
    (((ContinuousLinearMap.snd ℂ (G.Ω 1 × Fin N → ℂ) (G.Ω 1 → ℂ)).analyticAt _).comp (hFl t ht)).sub
      analyticAt_const
  have hΦeq : ∀ t ∈ ball (0 : ℂ) R, Φ t =
      bgFieldC G a ν c0 (B.lineAt E t) - bgFieldC G a ν c0 B := fun t ht => by
    simp only [hΦ, hFeq t ht, hF0]
  have hΛeq : ∀ t ∈ ball (0 : ℂ) R, Λ t =
      bgMultC G a ν c0 (B.lineAt E t) - bgMultC G a ν c0 B := fun t ht => by
    simp only [hΛ, hFeq t ht, hF0]
  have hnhd : ball (0 : ℂ) R ∈ 𝓝 (0 : ℂ) := ball_mem_nhds 0 hR0
  have hΦd : HasDerivAt Φ φd 0 := by
    have := hφd.sub_const (bgFieldC G a ν c0 B)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hnhd] with t ht using hΦeq t ht
  have hΛd : HasDerivAt Λ αd 0 := by
    have := hαd.sub_const (bgMultC G a ν c0 B)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hnhd] with t ht using hΛeq t ht
  have hΦ0 : Φ 0 = 0 := by simp [hΦ]
  have hΛ0 : Λ 0 = 0 := by simp [hΛ]
  set M := cK2 d L N * (R * s) with hM
  have hBΦ : ∀ t ∈ ball (0 : ℂ) R, SupBounds G (Φ t) M := fun t ht => by
    obtain ⟨δφ, δα, hsup, -, hf, -⟩ := hpert t (by simpa using ht)
    rw [hΦeq t ht, hf, add_sub_cancel_left]
    refine hsup.mono ?_
    have : ‖t‖ ≤ R := (mem_ball_zero_iff.1 ht).le
    have := mul_le_mul_of_nonneg_right this hs
    nlinarith [mul_le_mul_of_nonneg_left this hK2]
  have hBΛ : ∀ t ∈ ball (0 : ℂ) R, Small G (Λ t) M := fun t ht => by
    obtain ⟨δφ, δα, -, hsm, -, hm⟩ := hpert t (by simpa using ht)
    rw [hΛeq t ht, hm, add_sub_cancel_left]
    intro x
    refine (hsm x).trans ?_
    have : ‖t‖ ≤ R := (mem_ball_zero_iff.1 ht).le
    have := mul_le_mul_of_nonneg_right this hs
    nlinarith [mul_le_mul_of_nonneg_left this hK2]
  obtain ⟨hs1, hs2⟩ := supBounds_cauchy G hR hΦan hΦ0 hΦd hBΦ
  obtain ⟨hl1, hl2⟩ := small_cauchy G hR hΛan hΛ0 hΛd hBΛ
  have h1mem : (1 : ℂ) ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, norm_one]; linarith
  have hD1 : B.lineAt E 1 = D := lineAt_tangent D B hh
  have hMR : M / R = cK2 d L N * s := by rw [hM]; field_simp
  have hMR2 : 2 * M / R ^ 2 = 2 * (cK2 d L N * s) / R := by rw [hM]; field_simp
  obtain ⟨δφ1, δα1, hsup1, hsm1, hf1, hm1⟩ := hpert 1 (by rw [norm_one]; linarith)
  rw [hD1] at hf1 hm1
  rw [norm_one, one_mul] at hsup1 hsm1
  refine ⟨⟨?_, ?_⟩, φd, αd, hφform, hαform, ?_, ?_, ?_, ?_⟩
  · rw [hf1, add_sub_cancel_left]; exact hsup1
  · rw [hm1, add_sub_cancel_left]; exact hsm1
  · rw [← hMR]; exact hs1
  · rw [← hMR]; exact hl1
  · have := hs2
    rw [hΦeq 1 h1mem, hD1, hMR2] at this
    exact this
  · have := hl2
    rw [hΛeq 1 h1mem, hD1, hMR2] at this
    exact this

theorem source_tangent {n : ℕ} (hG : IsLevel G n) (a : ℕ → ℝ) (ν : ℝ) (D B : BgData G N) :
    source G a ν (tangentData D B) = qStar G a (tangentData D B).Ψ := by
  funext p
  have hcol : collar G = ∅ := by
    ext x
    rw [mem_collar]
    simp [(hG x).1]
  simp [source, tangentData, boundaryTerm, hcol]

end Abstract

section Specialized

open Balaban.Multiscale Balaban.Background Matrix

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ} {G : GeneratingSet d L N₀ K ϱ}
  {G' : GeneratingSet d L N₀ K ϱ'} {a₁ ν : ℝ} {n : ℕ}

/-- **Lemma 2.3 (d), bounds.**  Let `D'` be the datum `(θ, h)` of level `n + 1` in `𝒟(𝔹'_k)` with
`δ ≤ thm73C3`, `D` the datum of `ψ = ψ^{(k)} + ψ'` (same `h̃`) with `|ψ'| ≤ s`, and suppose that the
disc `{ψ^{(k)} + t ψ' : |t| < R}`, `R ≥ 2`, of radius `ρ = R s` lies in the domain `𝒟` and that
`ρ ≤ δ_*`, `K₂ ρ < c₀ / 2` (the smallness of Proposition 5.1; `R s = C₃c₇` in the notation of
FLUCTUATION).  With `K₂ = cK2`, `φ' = φ_k(ψ) - φ_{k+1}|`, `α' = α_k(ψ) - α_{k+1}|`:
`‖φ'‖_*, |α'|₂ ≤ K₂ s`, the same for `(φ^{(1)}, α^{(1)})`, and
`‖φ₂‖_*, |α' - α^{(1)}|₂ ≤ 2 K₂ s / R = 2 K₂ s² / ρ`. -/
theorem expansion_bounds (ha₁ : 0 < a₁) (hG : IsLevel G n) (hG' : IsLevel G' (n + 1))
    (hp : n + 1 ≤ K) (H : BgHyp d L K ϱ (compWeight L a₁) ν)
    (H' : BgHyp d L K ϱ' (compWeight L a₁) ν) (D' : BgData G' N)
    (hD' : InUnionDomainC G' (bgC0 d L N) (thm73C3 d L N) ν D') (D : BgData G N)
    (hh : ∀ x i, D.h x i = D'.h x i) {s R : ℝ} (hs : 0 ≤ s) (hR : 2 ≤ R)
    (hψs : ∀ x, vn (compTangent hG hG' hp (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D x) ≤ s)
    (hdisc : ∀ t : ℂ, ‖t‖ < R → InUnionDomainC G (bgC0 d L N) (bgC1 d L N) ν
      ((composeData (hG.precedes hG' hp) (compWeight L a₁)
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D').lineAt
        (tangentData D (composeData (hG.precedes hG' hp) (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D')) t))
    (hRs : R * s ≤ deltaStar d L N) (hsmall : cK2 d L N * (R * s) < bgC0 d L N / 2) :
    SupBounds G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
        (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D'))
      (cK2 d L N * s) ∧
    Small G (bgMultC G (compWeight L a₁) ν (bgC0 d L N) D -
        (hG.precedes hG' hp).restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D'))
      (cK2 d L N * s) ∧
    SupBounds G (phiOne (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (qStar G (compWeight L a₁) (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)))
      (cK2 d L N * s) ∧
    Small G (alphaOne (hG.precedes hG' hp) (compWeight L a₁) ν
        (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
        (qStar G (compWeight L a₁) (compTangent hG hG' hp (compWeight L a₁)
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)))
      (cK2 d L N * s) ∧
    SupBounds G (bgFieldC G (compWeight L a₁) ν (bgC0 d L N) D -
        (hG.precedes hG' hp).restrictφ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') -
        phiOne (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (qStar G (compWeight L a₁) (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)))
      (2 * (cK2 d L N * s) / R) ∧
    Small G (bgMultC G (compWeight L a₁) ν (bgC0 d L N) D -
        (hG.precedes hG' hp).restrictα (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D') -
        alphaOne (hG.precedes hG' hp) (compWeight L a₁) ν
          (bgMultC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
          (qStar G (compWeight L a₁) (compTangent hG hG' hp (compWeight L a₁)
            (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D' D)))
      (2 * (cK2 d L N * s) / R) := by
  have hD'2 : InUnionDomainC G' (bgC0 d L N) (thm73C2 d L N) ν D' :=
    InUnionDomainC.mono (thm73C3_le_thm73C2 d L N) hD'
  have hD'1 : InUnionDomainC G' (bgC0 d L N) (thm73C1 d L N) ν D' :=
    InUnionDomainC.mono (thm73C2_le_thm73C1 d L N) hD'2
  obtain ⟨-, hfield, hmult⟩ := theorem73_complex ha₁ H H' (hG.precedes hG' hp) hD'1
  have hBC2 := theorem73_complex_small ha₁ H H' (hG.precedes hG' hp) hD'2
  obtain ⟨δ0, ε0, hδ0, hδε, hε, hδC2, hνε, hK1, hB⟩ :=
    theorem73_complex_witness ha₁ H H' (hG.precedes hG' hp) hD'
  set h := hG.precedes hG' hp with hh'
  set a := compWeight L a₁ with ha
  set φ₁ := bgFieldC G' a ν (bgC0 d L N) D' with hφ₁
  set α₁ := bgMultC G' a ν (bgC0 d L N) D' with hα₁
  set Bd := composeData h a φ₁ D' with hBd
  have hhB : D.h = Bd.h := funext fun x => funext fun i => by
    rw [hh x i, hBd, composeData_h hG hG' hp]
  have hδ : δ0 ≤ bgC1 d L N := hδC2.trans (bgC2_le_bgC1 d L N)
  have hK1pos := bgK1_pos d L N
  have hc1 : bgK1 d L N * bgC1 d L N ≤ bgC0 d L N / 2 := by
    have : bgC1 d L N ≤ bgC0 d L N / (2 * bgK1 d L N) :=
      (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hsmall' : bgK1 d L N * δ0 + cK2 d L N * (R * s) < bgC0 d L N := by
    have := mul_le_mul_of_nonneg_left hδ hK1pos.le
    linarith
  obtain ⟨⟨h1, h2⟩, φ1, α1, hφ1, hα1, h3, h4, h5, h6⟩ := bounds_abstract (a := a) (ν := ν) H hδ0
    hδε hε hδ hνε hB hK1 hBC2 hhB hs hR (fun x => hψs x) hdisc hRs hsmall'
  have hop : bgOp a ν Bd = opHk h a ν α₁ := by
    unfold bgOp opHk; rw [hmult]
  have hvec : bgVec a ν Bd = fieldBase h φ₁ := by
    funext x i
    unfold bgVec fieldBase
    rw [hfield]
  have hsrc : source G a ν (tangentData D Bd) = qStar G a (compTangent hG hG' hp a φ₁ D' D) := by
    rw [source_tangent hG]; rfl
  have ePhi : phiOne h a ν α₁ φ₁ (qStar G a (compTangent hG hG' hp a φ₁ D' D)) = φ1 := by
    rw [hφ1, hop, hvec, hsrc]; rfl
  have eAlpha : alphaOne h a ν α₁ φ₁ (qStar G a (compTangent hG hG' hp a φ₁ D' D)) = α1 := by
    rw [hα1, hop, hvec, hsrc]; rfl
  rw [hfield] at h1 h5
  rw [hmult] at h2 h6
  rw [ePhi, eAlpha]
  exact ⟨h1, h2, h3, h4, h5, h6⟩

end Specialized

end Balaban.Fluctuation
