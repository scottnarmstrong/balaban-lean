/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireStep
public import Balaban.Fluctuation.FarDecayUncond
public import Balaban.Fluctuation.CubeActionBound

/-!
# Closeness of the global background and the background of a nested generating set

Let `G₀ ≺ G₁` be nested generating sets at level `k + 1` (for the first step `k = 0`; `G₁` the
global set, `G₀ = G_1(□) = genCube □` the cube-local one), `D'` a datum of `G₁` in the complex domain
`𝒟` with parameter `δ'`, and `D` a datum of `G₀` agreeing with `D'` on the data sites of `G₀`
(for the cube, `D` is the lift of the coarse field `ψ₁`). By Theorem 7.3 the background of `G₁`
restricted to `Ω₁(G₀)` is the background of `G₀` for the composed datum `Du`, and `Du - D` is a
change `δΨ` vanishing where the layers of `G₀` and `G₁` agree (LFR Lemma II.2.5 (c)), of size
`≤ (2d + 2) K₁ δ'`. The weighted perturbation theorem (Lemma 4.1) then gives the bounds

`|δφ(x)|, ℓ|∂δφ(x)|, ℓ²|Δδφ(x)|, ℓ²|δα(x)| ≤ K_w c_F (2d + 2) K₁ δ' e^{-γ_w dist(x, shadow W)}`

for the difference `δφ = φ(G₀; Du) - φ(G₀; D)` of the two backgrounds of `G₀`, where `W` is the set
of sites where the layers disagree (`bgField_close_nested`).
-/

@[expose] public section

namespace Balaban.LargeField.Base

variable {d L : ℕ} [NeZero L]

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.Fluctuation
  Balaban.LargeField

open Classical in
/-- **Closeness of the background of a nested generating set to the restriction of the global
background** (Theorem 7.3 and the weighted Lemma 4.1). -/
theorem bgField_close_nested {N : ℕ} (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ k : ℕ} [NeZero N₁] {ϱ0 ϱ1 : ℝ}
        {G0 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ0}
        {G1 : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ1} {a₁ ν δ ε δ' ε' : ℝ},
        0 < a₁ →
        BgHyp d L (k + 1) ϱ0 (compWeight L a₁) ν → BgHyp d L (k + 1) ϱ1 (compWeight L a₁) ν →
        Dec2.OpSetting G0 (compWeight L a₁) ν → ∀ (hprec : Precedes G0 G1) {D' : BgData G1 N},
        0 < δ' → δ' ≤ ε' → ε' ≤ bgC0 d L N → δ' ≤ thm73C1 d L N →
        ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε' ^ 2 ≤ δ' ^ 2 → InDomainC G1 ν δ' ε' D' →
        ∀ {D : BgData G0 N}, (∀ x ∈ dataSites G0, D.Ψ x = D'.Ψ x) →
        (∀ x ∈ G0.Ω 1, D.h x = D'.h x) → 
        0 < δ → δ ≤ ε → ε ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        ν * ((L : ℝ) ^ (k + 1)) ^ 2 * ε ^ 2 ≤ δ ^ 2 → InDomainC G0 ν δ ε D →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        (2 * d + 2) * (bgK1 d L N * δ') ≤ deltaStar d L N →
        (2 * d + 2) * (bgK1 d L N * δ') ≤ δw →
        ∀ {E : Set (Torus d ((N₁ * L ^ m₁) * L ^ (k + 1)))},
        (∀ x ∈ E, ∀ m, 1 ≤ m → m ≤ k + 1 → (x ∈ G0.Ω m ↔ x ∈ G1.Ω m)) →
        bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N)
            (composeData hprec (compWeight L a₁) (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D')
              D') = hprec.restrictφ (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') ∧
          FarBounds G0 (shadow G0 (Finset.univ.filter fun y => y ∉ E)) (gammaW d)
            (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * δ'))))
            (bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N)
                (composeData hprec (compWeight L a₁)
                  (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D') -
              bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D)
            (bgMultC G0 (compWeight L a₁) ν (bgC0 d L N)
                (composeData hprec (compWeight L a₁)
                  (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D') -
              bgMultC G0 (compWeight L a₁) ν (bgC0 d L N) D) := by
  obtain ⟨Kw, δw, hK, hδw, hfar⟩ := lemma41_domain_uncond (d := d) (L := L) (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ k _ ϱ0 ϱ1 G0 G1 a₁ ν δ ε δ' ε' ha₁ H0 H1 hOp hprec D' hδ0' hδε' hε' hδc hνε' hD' D
    hΨ hh hδ0 hδε hε hδ1 hνε hD hK1 hKw hK1' hKw' E hE
  obtain ⟨hDuU, hfield, hΨE, hhE, hbound⟩ := composed_change ha₁ H0 H1 hprec hδ0' hδε' hε' hδc
    hνε' hD' hΨ hh hE
  refine ⟨hfield, ?_⟩
  obtain ⟨δu, εu, hδu0, hδuε, hεu, hδu1, hνεu, hDu⟩ := hDuU
  have hK1pos := bgK1_pos d L N
  have hδ₁0 : 0 ≤ (2 * d + 2) * (bgK1 d L N * δ') := by positivity
  refine hfar H0 hOp hδ0 hδε hε hδ1 hνε hD hδu0 hδuε hεu hδu1 hνεu hDu hK1 hKw
    (δΨ := fun y i => (composeData hprec (compWeight L a₁)
      (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D') D').Ψ y i - D.Ψ y i)
    (Finset.univ.filter fun y => y ∉ E) ?_ (fun x i => by ring) (fun x i => hhE x i) hδ₁0 hK1' hKw'
    (fun x hx => hbound x hx)
  intro y hy
  have hyE : y ∈ E := by simpa using hy
  funext i
  exact hΨE y hyE i

section Transfer

variable {N₁ m₁ K N : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}

theorem vn_le_sqrt_mul (v : Fin N → ℂ) {C : ℝ} (hC : 0 ≤ C) (h : ∀ i, ‖v i‖ ≤ C) :
    vn v ≤ Real.sqrt N * C := by
  have h2 : vn v ^ 2 ≤ (Real.sqrt N * C) ^ 2 := by
    rw [vn_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
    calc ∑ i, ‖v i‖ ^ 2 ≤ ∑ _i : Fin N, C ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (h i) 2
      _ = N * C ^ 2 := by simp
  exact le_of_sq_le_sq h2 (by positivity)

/-- **The bond difference of the background of a nested set transfers to the perturbed one.**
If `g - f` satisfies the far bounds (`FarBounds`) with decay constant `γ` and amplitude `B`,
and `x`, `x + e_μ` lie in `Ω₁`, at path distance at least `Dist` from the set `W`, then
`ℓ |∂_μ g(x)| ≤ ℓ |∂_μ f(x)| + √N B e^{-γ Dist}`. -/
theorem bond_transfer {f g : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ}
    {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)} {γ B Dist : ℝ} (hγ : 0 ≤ γ)
    (hB : 0 ≤ B) (hF : FarBounds G W γ B (g - f) δα) (x y : G.Ω 1) (μ : Fin d)
    (hy : (y : Balaban.Localization.CTorus d L N₁ m₁ K) = (x : Balaban.Localization.CTorus d L N₁ m₁ K) + Pi.single μ 1)
    (hD : ENNReal.ofReal Dist ≤ siteSetDist G W x) :
    G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ K) * vn (fun i => g (y, i) - g (x, i)) ≤
      G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ K) * vn (fun i => f (y, i) - f (x, i)) +
        Real.sqrt N * (B * Real.exp (-(γ * Dist))) := by
  have hL0 : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  have hsp : 0 < G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ K) := by
    unfold GeneratingSet.spacing; positivity
  have hdec := decay_le_exp_dist hγ hD
  set sp := G.spacing (x : Balaban.Localization.CTorus d L N₁ m₁ K) with hsp'
  set δφ := g - f with hδφ
  have hcomp : ∀ i, ‖δφ (y, i) - δφ (x, i)‖ ≤ B * Real.exp (-(γ * Dist)) / sp := by
    intro i
    have h1 := hF.fwd (x : Balaban.Localization.CTorus d L N₁ m₁ K) x.2 μ i
    rw [← hy, svec_of_mem, svec_of_mem] at h1
    rw [le_div_iff₀ hsp, mul_comm]
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_left hdec hB
  have hvn : vn (fun i => δφ (y, i) - δφ (x, i)) ≤ Real.sqrt N * (B * Real.exp (-(γ * Dist)) / sp) :=
    vn_le_sqrt_mul _ (by positivity) hcomp
  have hsplit : (fun i => g (y, i) - g (x, i)) = (fun i => f (y, i) - f (x, i)) +
      (fun i => δφ (y, i) - δφ (x, i)) := by
    funext i; simp [hδφ]; ring
  have h2 := vn_add (fun i => f (y, i) - f (x, i)) (fun i => δφ (y, i) - δφ (x, i))
  rw [← hsplit] at h2
  calc sp * vn (fun i => g (y, i) - g (x, i))
      ≤ sp * (vn (fun i => f (y, i) - f (x, i)) + vn (fun i => δφ (y, i) - δφ (x, i))) :=
        mul_le_mul_of_nonneg_left h2 hsp.le
    _ ≤ sp * (vn (fun i => f (y, i) - f (x, i)) +
          Real.sqrt N * (B * Real.exp (-(γ * Dist)) / sp)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hvn) hsp.le
    _ = sp * vn (fun i => f (y, i) - f (x, i)) + Real.sqrt N * (B * Real.exp (-(γ * Dist))) := by
        field_simp

theorem blockAvg_sub (f g : G.Ω 1 × Fin N → ℂ) (x : Balaban.Localization.CTorus d L N₁ m₁ K)
    (i : Fin N) : blockAvg G g x i - blockAvg G f x i = blockAvg G (g - f) x i := by
  unfold blockAvg
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy : y ∈ G.Ω 1
  · simp [svec_of_mem G _ ⟨y, hy⟩]
  · simp [svec_of_not_mem G _ hy]

/-- **The block deviation transfers to the perturbed background.** If `g - f` satisfies the far
bounds and the sites of the block of `x` in `Ω₁` are at distance at least `Dist` from `W`, then
`|Ψ(x) - (Q g)(x)| ≤ |Ψ(x) - (Q f)(x)| + √N B e^{-γ Dist}`. -/
theorem block_transfer {f g : G.Ω 1 × Fin N → ℂ} {δα : G.Ω 1 → ℂ}
    {W : Finset (Balaban.Localization.CTorus d L N₁ m₁ K)} {γ B Dist : ℝ} (hγ : 0 ≤ γ)
    (hB : 0 ≤ B) (hF : FarBounds G W γ B (g - f) δα)
    (Ψ : Balaban.Localization.CTorus d L N₁ m₁ K → Fin N → ℂ)
    {x : Balaban.Localization.CTorus d L N₁ m₁ K} (hx : x ∈ G.Ω 1)
    (hD : ∀ y ∈ G.blk (G.layerIndex x) x, y ∈ G.Ω 1 → ENNReal.ofReal Dist ≤ siteSetDist G W y) :
    vn (fun i => Ψ x i - blockAvg G g x i) ≤
      vn (fun i => Ψ x i - blockAvg G f x i) + Real.sqrt N * (B * Real.exp (-(γ * Dist))) := by
  have hT : ∀ i, ‖blockAvg G (g - f) x i‖ ≤ B * Real.exp (-(γ * Dist)) := by
    intro i
    refine blockAvg_norm_le (g - f) hx (fun y hy hyΩ j => ?_) i
    refine (hF.val ⟨y, hyΩ⟩ j).trans ?_
    exact mul_le_mul_of_nonneg_left (decay_le_exp_dist hγ (hD y hy hyΩ)) hB
  have hv : vn (fun i => blockAvg G (g - f) x i) ≤ Real.sqrt N * (B * Real.exp (-(γ * Dist))) :=
    vn_le_sqrt_mul _ (by positivity) hT
  have hsplit : (fun i => Ψ x i - blockAvg G g x i) =
      (fun i => Ψ x i - blockAvg G f x i) + (fun i => -(blockAvg G (g - f) x i)) := by
    funext i
    have := blockAvg_sub f g x i
    simp only [Pi.add_apply]
    linear_combination -this
  have h2 := vn_add (fun i => Ψ x i - blockAvg G f x i) (fun i => -(blockAvg G (g - f) x i))
  rw [← hsplit] at h2
  have hneg : vn (fun i => -(blockAvg G (g - f) x i)) = vn (fun i => blockAvg G (g - f) x i) := by
    unfold vn
    have : (WithLp.toLp 2 fun i => -(blockAvg G (g - f) x i) : EuclideanSpace ℂ (Fin N)) =
        -(WithLp.toLp 2 fun i => blockAvg G (g - f) x i) := rfl
    rw [this, norm_neg]
  linarith

end Transfer

end Balaban.LargeField.Base
