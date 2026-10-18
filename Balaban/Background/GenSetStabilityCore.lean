/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.DeltaPhiResp
public import Balaban.Background.GenSetStabilityRestrict
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Two solutions of (EL) on one generating set with a near and a far data change

P3 Proposition 2.1 / Lemma 4.1 of FLUCTUATION.md in the form used for a change of generating set
(P7 (2.14)): two solutions `(φ, α)`, `(φ', α')` of (EL) on the same generating set, for data `D`,
`D'` with the same `h̃`, whose data change `δΨ = D'.Ψ - D.Ψ` is at most `δ₁` everywhere and at most
`δ_d` off a set `Far` (at the site and at its collar neighbours).  Then at a site `y` at path
distance `≥ D₀` from `Far`,
`|φ'(y) - φ(y)| ≤ K_w C_F (δ₁ e^{-γ_w D₀} + δ_d)` (`twoEL_near_far`).

The proof applies the corrected weighted Proposition 5.1 (`WeightedProp51S`) with the weight
`e^{γ_w min(d(x, Far), D₀)}`: it is `1` on `Far` and at most `e^{γ_w D₀}` elsewhere.

`prop51Hyp_of_precedes`: the hypotheses (P1)–(P4) of Proposition 5.1 for a generating set
`𝔹_j ≺ 𝔹'_k` at the base point `φ̄'` of a background of `𝔹'_k` with the bounds of Theorem 5.2
(the spacing of `𝔹_j` is at most that of `𝔹'_k`).
-/

@[expose] public section

namespace Balaban.Background

open Balaban Balaban.Multiscale Balaban.Localization Balaban.Fluctuation Finset

section Core

variable {d L N₁ m₁ K N : ℕ} [NeZero N₁] [NeZero L] {ϱ : ℝ}

/-- **Two solutions of (EL), a near and a far data change.**  `(φ, α)` and `(φ', α')` solve (EL)
on `G` for the data `D`, `D'` (same `h̃`, mass `ν`), `|α' - α|₂ ≤ c₆`, the hypotheses of Proposition
5.1 hold at the base point `φ₀ = φ` with the data change `δΨ = D'.Ψ - D.Ψ` and sizes
`δ₀, δ₁ ≤ δ_w`, and `|δΨ| ≤ δ_d` at the sites of `Ω₁ ∖ Far` and at their collar neighbours.  Then at
a site `y` with `d(y, Far) ≥ D₀`: `|φ'(y) - φ(y)|, ℓ(y) |∂(φ' - φ)(y)| ≤ K_w C_F (δ₁ e^{-γ_w D₀} + δ_d)`
(both difference directions). -/
theorem twoEL_near_far {Kw δw : ℝ} (hW : WeightedProp51S d L N Kw δw)
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} {a : ℕ → ℝ} {ν : ℝ}
    (hS : GreenSetting G a ν) (hOp : Dec2.OpSetting G a ν) {D D' : BgData G N}
    {φ φ' : G.Ω 1 × Fin N → ℂ} {α α' : G.Ω 1 → ℂ}
    (hφ : IsEL G a ν D φ α) (hφ' : IsEL G a ν D' φ' α') (hh : ∀ x i, D'.h x i = D.h x i)
    (hsmall : Small G (α' - α) (c6 d L N))
    {φ₀ : CTorus d L N₁ m₁ K → Fin N → ℂ} (hφ₀ : ∀ (x : G.Ω 1) i, φ₀ x i = φ (x, i))
    {δ₀ δ₁ : ℝ}
    (hP : Prop51Hyp G a ν α φ₀ (fun x i => D'.Ψ x i - D.Ψ x i) (fun _ => 0) δ₀ δ₁)
    (hδ₀ : δ₀ ≤ δw) (hδ₁ : δ₁ ≤ δw)
    (Far : Finset (CTorus d L N₁ m₁ K)) {δd : ℝ} (hδd : 0 ≤ δd)
    (hnear : ∀ x : G.Ω 1, (x : CTorus d L N₁ m₁ K) ∉ Far →
      vn (fun i => D'.Ψ x i - D.Ψ x i) ≤ δd ∧
      ∀ y ∈ collar G, Adj (x : CTorus d L N₁ m₁ K) y → vn (fun i => D'.Ψ y i - D.Ψ y i) ≤ δd)
    {D₀ : ℝ} (hD₀ : 0 ≤ D₀) (y : G.Ω 1)
    (hy : ENNReal.ofReal D₀ ≤ siteSetDist G Far y) :
    (∀ i, ‖(φ' - φ) (y, i)‖ ≤ Kw * (cF d L * (δ₁ * Real.exp (-(gammaW d * D₀)) + δd))) ∧
    (∀ (μ : Fin d) (i : Fin N), G.spacing (y : CTorus d L N₁ m₁ K) *
      ‖svec G (φ' - φ) ((y : CTorus d L N₁ m₁ K) + Pi.single μ 1) i -
        svec G (φ' - φ) (y : CTorus d L N₁ m₁ K) i‖ ≤
      Kw * (cF d L * (δ₁ * Real.exp (-(gammaW d * D₀)) + δd))) ∧
    (∀ (μ : Fin d) (i : Fin N), G.spacing (y : CTorus d L N₁ m₁ K) *
      ‖svec G (φ' - φ) ((y : CTorus d L N₁ m₁ K) - Pi.single μ 1) i -
        svec G (φ' - φ) (y : CTorus d L N₁ m₁ K) i‖ ≤
      Kw * (cF d L * (δ₁ * Real.exp (-(gammaW d * D₀)) + δd))) := by
  classical
  have hd3 : 3 ≤ d := hS.hd
  have hγ : 0 ≤ gammaW d := gammaW_nonneg (by omega)
  set δΨ : CTorus d L N₁ m₁ K → Fin N → ℂ := fun x i => D'.Ψ x i - D.Ψ x i with hδΨ
  have hΨ : ∀ x i, D'.Ψ x i = D.Ψ x i + δΨ x i := fun x i => by simp [hδΨ]
  have hper0 := isPerturbed_of_EL a hΨ hh hφ₀ hφ hφ'
  have hf : (fun p : G.Ω 1 × Fin N => ((ν - ν : ℝ) : ℂ) * (D.h p.1 p.2 - φ p)) =
      fun _ => 0 := by
    funext p; simp
  rw [hf] at hper0
  have hg : ∀ x : G.Ω 1, gdef G φ₀ x = 0 := fun x => by
    show ∑ i, φ₀ x i * φ₀ x i - 1 = 0
    simp only [hφ₀, hφ.2 x, sub_self]
  -- the capped distance and the weight
  set Dc : CTorus d L N₁ m₁ K → ENNReal :=
    fun x => min (siteSetDist G Far x) (ENNReal.ofReal D₀) with hDc
  have htri : ∀ x z, Dc x ≤ G.pathDist x z + Dc z := by
    intro x z
    have h1 := setDist_triangle (G := G) Far x z
    simp only [hDc]
    rcases le_total (siteSetDist G Far z) (ENNReal.ofReal D₀) with hz | hz
    · rw [min_eq_left hz]; exact (min_le_left _ _).trans h1
    · rw [min_eq_right hz]; exact (min_le_right _ _).trans le_add_self
  have hDtop : ∀ x, Dc x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  have hw := isWeight_of_dist G hγ le_rfl Dc htri
  set w : CTorus d L N₁ m₁ K → ℝ :=
    fun x => if Dc x = ⊤ then (1 : ℝ) else Real.exp (gammaW d * (Dc x).toReal) with hwdef
  have hwx : ∀ x, w x = Real.exp (gammaW d * (Dc x).toReal) := fun x => by
    simp only [hwdef, hDtop x, ↓reduceIte]
  have hDle : ∀ x, (Dc x).toReal ≤ D₀ := fun x => by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (min_le_right (siteSetDist G Far x) (ENNReal.ofReal D₀))
    rwa [ENNReal.toReal_ofReal hD₀] at this
  have hcF := cF_pos d L
  have hE := Real.exp_pos (gammaW d * D₀)
  set C : ℝ := cF d L * (δ₁ + Real.exp (gammaW d * D₀) * δd) with hC
  have hC0 : 0 ≤ C := by have := hP.δ₁_nn; positivity
  have hfs : ∀ (x : G.Ω 1) (i : Fin N), w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
      ‖pertSource G a δΨ (fun _ => 0) (x, i)‖) ≤ C := by
    intro x i
    by_cases hx : (x : CTorus d L N₁ m₁ K) ∈ Far
    · have h0 : siteSetDist G Far x = 0 := setDist_of_mem Far hx x.2
      have hw1 : w x = 1 := by
        rw [hwx]
        simp [hDc, h0]
      rw [hw1, one_mul]
      have hb := pertSource_bound (f₁ := fun _ => (0 : ℂ)) hS hP.δ₁_nn hP.dPsi
        (fun x i => by simpa using hP.δ₁_nn) x i
      have : cF d L * δ₁ ≤ C := by
        rw [hC]
        have : 0 ≤ Real.exp (gammaW d * D₀) * δd := by positivity
        nlinarith
      linarith
    · obtain ⟨h1, h2⟩ := hnear x hx
      have hloc := Balaban.LargeField.pertSource_local (δΨ := δΨ) (B := δd) hS hδd x i h1 h2
      have hwle : w x ≤ Real.exp (gammaW d * D₀) := by
        rw [hwx]
        exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hDle x) hγ)
      have hpos : 0 ≤ G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
          ‖pertSource G a δΨ (fun _ => 0) (x, i)‖ := by
        have := spacing_pos G (x := (x : CTorus d L N₁ m₁ K)); positivity
      calc w x * (G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 *
            ‖pertSource G a δΨ (fun _ => 0) (x, i)‖)
          ≤ Real.exp (gammaW d * D₀) * (cF d L * δd) :=
            mul_le_mul hwle hloc hpos hE.le
        _ ≤ C := by
            rw [hC]
            have := hP.δ₁_nn
            nlinarith
  obtain ⟨-, hSup⟩ := hW G a ν α φ₀ δΨ (fun _ => 0) δ₀ δ₁ hP hOp hg hδ₀ hδ₁ w hw C hC0 hfs
    (φ' - φ) (α' - α) hper0 hsmall
  have hDy : Dc y = ENNReal.ofReal D₀ := min_eq_right hy
  have hwy : w y = Real.exp (gammaW d * D₀) := by
    rw [hwx, hDy, ENNReal.toReal_ofReal hD₀]
  have hinv : Real.exp (-(gammaW d * D₀)) * Real.exp (gammaW d * D₀) = 1 := by
    rw [← Real.exp_add]; simp
  have hE' := Real.exp_pos (-(gammaW d * D₀))
  have hconv : ∀ v : ℝ, w y * v ≤ Kw * C →
      v ≤ Kw * (cF d L * (δ₁ * Real.exp (-(gammaW d * D₀)) + δd)) := by
    intro v hv
    rw [hwy] at hv
    calc v = Real.exp (-(gammaW d * D₀)) * (Real.exp (gammaW d * D₀) * v) := by
          rw [← mul_assoc, hinv, one_mul]
      _ ≤ Real.exp (-(gammaW d * D₀)) * (Kw * C) := mul_le_mul_of_nonneg_left hv hE'.le
      _ = Kw * (cF d L * (δ₁ * Real.exp (-(gammaW d * D₀)) + δd)) := by
          rw [hC]
          have : Real.exp (-(gammaW d * D₀)) * (Kw * (cF d L * (δ₁ +
              Real.exp (gammaW d * D₀) * δd))) = Kw * (cF d L * (δ₁ * Real.exp (-(gammaW d * D₀)) +
              (Real.exp (-(gammaW d * D₀)) * Real.exp (gammaW d * D₀)) * δd)) := by ring
          rw [this, hinv, one_mul]
  exact ⟨fun i => hconv _ (hSup.val y i), fun μ i => hconv _ (hSup.fwd y y.2 μ i),
    fun μ i => hconv _ (hSup.bwd y y.2 μ i)⟩

end Core

section Restrict

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱB : ℝ}

/-- **(P1)–(P4) of Proposition 5.1 on `𝔹_j ≺ 𝔹'_k`** at the base point `φ̄'` (the extension of a
real unit field `φ'` of `𝔹'_k` by its data) when `φ'` satisfies the bounds of Theorem 5.2 with size
`c ≤ δ_*` on `𝔹'_k`: the spacing of `𝔹_j` is at most that of `𝔹'_k`, so the smoothness and the
multiplier bounds are inherited; the defect vanishes since `φ' · φ' = 1`. -/
theorem prop51Hyp_of_precedes {G : GeneratingSet d L N₀ k ϱ} {GB : GeneratingSet d L N₀ k ϱB}
    {a : ℕ → ℝ} {ν : ℝ} (hS : GreenSetting GB a ν) (hp : Precedes GB G) {D : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} {c : ℝ} (hb : BgBounds G D φ α c) (hc0 : 0 ≤ c)
    (hc : c ≤ deltaStar d L N) (hunit : IsRealUnitField G φ)
    {δΨ : Torus d (N₀ * L ^ k) → Fin N → ℂ} {δ₁ : ℝ} (hδ₁0 : 0 ≤ δ₁)
    (hδ₁ : δ₁ ≤ deltaStar d L N) (hdΨ : ∀ x ∈ dataSites GB, vn (δΨ x) ≤ δ₁) :
    Prop51Hyp GB a ν (hp.restrictα α) (barField G D.Ψ φ) δΨ (fun _ => 0) c δ₁ := by
  have hbar : ∀ (x : Torus d (N₀ * L ^ k)) (hx : x ∈ G.Ω 1),
      barField G D.Ψ φ x = fun i => φ (⟨x, hx⟩, i) := by
    intro x hx; funext i; simp [barField, hx]
  have hsp : ∀ x ∈ GB.Ω 1, GB.spacing x ≤ G.spacing x := fun x hx => by
    have := scaleGap_one hp x hx
    rwa [one_mul] at this
  have hspB : ∀ x : Torus d (N₀ * L ^ k), 0 < GB.spacing x := fun _ => spacing_pos GB
  have hdot : ∀ y ∈ GB.Ω 1, barField G D.Ψ φ y ⬝ᵥ barField G D.Ψ φ y = 1 := by
    intro y hy
    have hyG := hp.mem_Ω1 hy
    rw [hbar y hyG]
    exact dot_eq_one_of_unit hunit ⟨y, hyG⟩
  refine ⟨hS, hc0, hδ₁0, hc, hδ₁, ⟨fun x hx μ => ?_, fun x hx => ?_⟩, fun x hx => ?_,
    fun x => ?_, fun x i => by simpa using hδ₁0, hdΨ, fun x => ?_, fun x => ?_⟩
  · have hxG := hp.mem_Ω1 hx
    obtain ⟨h1, h2⟩ := hb.grad ⟨x, hxG⟩ μ
    have hle : c / G.spacing x ≤ c / GB.spacing x :=
      div_le_div_of_nonneg_left hc0 (hspB x) (hsp x hx)
    exact ⟨h1.trans hle, h2.trans hle⟩
  · have hxG := hp.mem_Ω1 hx
    have h1 := hb.lap ⟨x, hxG⟩
    have hle : c / G.spacing x ^ 2 ≤ c / GB.spacing x ^ 2 :=
      div_le_div_of_nonneg_left hc0 (by have := hspB x; positivity)
        (pow_le_pow_left₀ (hspB x).le (hsp x hx) 2)
    exact h1.trans hle
  · have hxG := hp.mem_Ω1 hx
    rw [hbar x hxG]
    have hn := (hunit ⟨x, hxG⟩).2
    have hsq : vn (fun i => φ (⟨x, hxG⟩, i)) ^ 2 = 1 := by rw [vn_sq]; exact hn
    have h0 := vn_nonneg (fun i => φ (⟨x, hxG⟩, i))
    nlinarith
  · have h1 := hb.alpha (hp.incl x)
    have h2 : GB.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 :=
      pow_le_pow_left₀ (hspB _).le (hsp x x.2) 2
    calc GB.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖hp.restrictα α x‖
        ≤ G.spacing (x : Torus d (N₀ * L ^ k)) ^ 2 * ‖α (hp.incl x)‖ :=
          mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
      _ ≤ c := h1
  · have e : gdef GB (barField G D.Ψ φ) x = 0 := by
      simp only [gdef]
      rw [sub_eq_zero]
      exact hdot x.1 x.2
    rw [e, norm_zero]; exact hδ₁0
  · rw [negLap_zeroExt_gdef hdot, norm_zero, mul_zero]; exact hδ₁0

end Restrict

end Balaban.Background
