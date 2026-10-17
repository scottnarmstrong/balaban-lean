/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.FarDecayUncond
public import Balaban.Localization.DecoupledCompose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Decay of the response of the composed datum to far changes of the data (blocker 5, piece (1))

Let `D`, `D'` be two data of `𝔹'_k` in the data domain, with the same `h`, differing in `Ψ` only on a
finite set `W` of sites, by at most `δ₁`.  The composed fields `ψ(𝔹_j, 𝔹'_k; φ_D, Ψ_D)` of (6.2)
at the complex backgrounds differ at a site `x` where `Ψ_D = Ψ_{D'}` and which is at path distance at
least `n` from the shadow of `W` by at most `5 e^{2dγ_w} K_w C_F δ₁ e^{-γ_w n}`: the far-data
response `lemma41_domain_uncond` (Lemma 4.1) for the background, and `composeField_sub_close` for
the composition.
-/

@[expose] public section

namespace Balaban.Green

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.Fluctuation Finset

/-- A path distance at least `n` from every site of the set gives decay at most `e^{-γ n}`. -/
theorem decay_siteSetDist_le {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {γ n : ℝ} (hγ : 0 ≤ γ)
    {W : Finset (CTorus d L N₁ m₁ K)} {x : CTorus d L N₁ m₁ K}
    (hx : ∀ w ∈ W, ENNReal.ofReal n ≤ G.pathDist x w) :
    decay γ (siteSetDist G W x) ≤ Real.exp (-(γ * n)) := by
  have h : ENNReal.ofReal n ≤ siteSetDist G W x := by
    unfold siteSetDist
    exact le_iInf₂ hx
  unfold decay
  split_ifs with ht
  · exact (Real.exp_pos _).le
  · refine Real.exp_le_exp.2 ?_
    have := (ENNReal.ofReal_le_iff_le_toReal ht).1 h
    nlinarith

/-- **Decay of the response of the composed datum** (see the module docstring). -/
theorem composeField_response_le {d L N : ℕ} [NeZero L] (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ ϱ' : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        {G' : GeneratingSet d L (N₁ * L ^ m₁) K ϱ'} {a : ℕ → ℝ} {ν : ℝ},
        BgHyp d L K ϱ' a ν → Dec2.OpSetting G' a ν → Precedes G G' →
        ∀ {D Du : BgData G' N} {δ : ℝ}, 0 < δ → δ ≤ bgC0 d L N → δ ≤ bgC1 d L N →
        InDomainC G' ν δ δ D → InDomainC G' ν δ δ Du →
        bgK1 d L N * δ ≤ deltaStar d L N → bgK1 d L N * δ ≤ δw →
        ∀ (W : Finset (CTorus d L N₁ m₁ K)), (∀ y ∉ W, Du.Ψ y = D.Ψ y) →
        (∀ x i, Du.h x i = D.h x i) → ∀ {δ₁ : ℝ}, 0 ≤ δ₁ → δ₁ ≤ deltaStar d L N → δ₁ ≤ δw →
        (∀ x ∈ dataSites G', vn (fun i => Du.Ψ x i - D.Ψ x i) ≤ δ₁) →
        ∀ (x : CTorus d L N₁ m₁ K) (n : ℝ),
        (∀ w ∈ shadow G' W, ENNReal.ofReal n ≤ G'.pathDist x w) → Du.Ψ x = D.Ψ x → ∀ i : Fin N,
        ‖composeField G G' a (bgFieldC G' a ν (bgC0 d L N) Du) Du.Ψ x i -
          composeField G G' a (bgFieldC G' a ν (bgC0 d L N) D) D.Ψ x i‖ ≤
        5 * Real.exp (gammaW d * (2 * d)) * (Kw * (cF d L * δ₁)) * Real.exp (-(gammaW d * n)) := by
  obtain ⟨Kw, δw, hK, hδw, hresp⟩ := lemma41_domain_uncond (N := N) hd hL
  refine ⟨Kw, δw, hK, hδw, ?_⟩
  intro N₁ m₁ K _ ϱ ϱ' G G' a ν H hOp hP D Du δ hδ0 hc0 hc1 hD hDu hK1 hKw W hsupp hh δ₁ hδ₁0
    hδ₁s hδ₁w hdΨ x n hxn hxΨ i
  have hd0 : 0 < d := by omega
  have hmass : ν * ((L : ℝ) ^ K) ^ 2 * δ ^ 2 ≤ δ ^ 2 := by
    have := H.massLe
    nlinarith [sq_nonneg δ]
  have hF := hresp H hOp hδ0 le_rfl hc0 hc1 hmass hD hδ0 le_rfl hc0 hc1 hmass hDu hK1 hKw
    (δΨ := fun y i => Du.Ψ y i - D.Ψ y i) W (fun y hy => by
      funext i; simp [hsupp y hy]) (fun x i => by ring) hh hδ₁0 hδ₁s hδ₁w hdΨ
  have hγ : 0 ≤ gammaW d := gammaW_nonneg hd0
  have hC : 0 ≤ Kw * (cF d L * δ₁) := mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hδ₁0)
  set Wh := shadow G' W with hWh
  have hval : ∀ (y : CTorus d L N₁ m₁ K) (j : Fin N),
      ‖svec G' (bgFieldC G' a ν (bgC0 d L N) Du - bgFieldC G' a ν (bgC0 d L N) D) y j‖ ≤
        2 * (Kw * (cF d L * δ₁) / 2) * decay (gammaW d) (siteSetDist G' Wh y) := by
    intro y j
    by_cases hy : y ∈ G'.Ω 1
    · rw [svec_of_mem G' _ ⟨y, hy⟩ j]
      have := hF.val ⟨y, hy⟩ j
      simpa [mul_div_cancel₀] using this
    · unfold svec zeroExt
      simp only [hy, ↓reduceDIte, norm_zero]
      exact mul_nonneg (by linarith [hC]) (decay_nonneg _ _)
  have h2 := composeField_sub_close hP H.weights hγ (by positivity : 0 ≤ Kw * (cF d L * δ₁) / 2)
    hval D.Ψ x i
  have h3 : composeField G G' a (bgFieldC G' a ν (bgC0 d L N) Du) Du.Ψ x i =
      composeField G G' a (bgFieldC G' a ν (bgC0 d L N) Du) D.Ψ x i :=
    composeField_congr a (fun _ _ _ => rfl) (fun j => by rw [hxΨ]) i
  rw [h3]
  refine h2.trans ?_
  have hdec := decay_siteSetDist_le (G := G') (γ := gammaW d) (n := n) hγ (W := Wh) (x := x) hxn
  have hE : 0 ≤ Real.exp (gammaW d * (2 * d)) := (Real.exp_pos _).le
  calc 10 * Real.exp (gammaW d * (2 * d)) * (Kw * (cF d L * δ₁) / 2) *
        decay (gammaW d) (siteSetDist G' Wh x)
      ≤ 10 * Real.exp (gammaW d * (2 * d)) * (Kw * (cF d L * δ₁) / 2) *
        Real.exp (-(gammaW d * n)) :=
        mul_le_mul_of_nonneg_left hdec (by positivity)
    _ = _ := by ring

end Balaban.Green
