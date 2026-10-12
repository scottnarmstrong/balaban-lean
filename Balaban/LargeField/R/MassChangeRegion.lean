/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.MassChangeHessian
public import Balaban.LargeField.R.MassResponseHyp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The region bound for the mass change from the premises (1.3) (MASS-RESPONSE (2.5))

* `wExt_eq_neg_svec`, `massChange_hbond_of_supBounds`, `massChange_hα_of_small`,
  `massChange_hcoef_of_weights`, `massChange_hgrad_of_bgBounds`: the pointwise premises of
  `massChange_region_bound_of_response` from the response and the region geometry;
* `massChange_region_bound`: the region bound, `Km = √N · Kw`;
* `massChange_region_bound_cube`: the per-cube form at scale `q = k + 1`;
* `massChange_region_hyps_nonempty`: non-vacuity.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization Finset

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

/-- `wExt` of the same datum is minus the zero extension of `φm - φ0`. -/
theorem wExt_eq_neg_svec (Dat : BgData G N) (φ0 φm : G.Ω 1 × Fin N → ℂ)
    (x : Torus d (N₀ * L ^ K)) (i : Fin N) :
    wExt Dat Dat φm φ0 x i = - svec G (φm - φ0) x i := by
  by_cases hx : x ∈ G.Ω 1
  · simp [wExt, barField, svec, zeroExt, hx]
  · simp [wExt, barField, hx, svec_of_not_mem G _ hx]

/-- (a) The bond differences of `w̄` from the forward/backward bounds of the response. -/
theorem massChange_hbond_of_supBounds {m₁ N₁ : ℕ} [NeZero N₁]
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (R : Region G) (Dat : BgData G N)
    {φ0 φm : G.Ω 1 × Fin N → ℂ} {V ℓ₀ : ℝ} (hV : 0 ≤ V) (hℓ : 0 < ℓ₀)
    (hℓR : ∀ x ∈ R.sites, ℓ₀ ≤ G.spacing x)
    (hS : SupBoundsW G (fun _ => 1) (φm - φ0) V)
    (x : Torus d (N₁ * L ^ m₁ * L ^ K)) (μ : Fin d)
    (hx : x ∈ R.sites ∨ x + Pi.single μ 1 ∈ R.sites) :
    vnorm (fun i => wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i)
      ≤ Real.sqrt N * (V / ℓ₀) := by
  have hVl : 0 ≤ V / ℓ₀ := by positivity
  refine vn_le_sqrt_mul hVl fun i => ?_
  have e : wExt Dat Dat φm φ0 (x + Pi.single μ 1) i - wExt Dat Dat φm φ0 x i =
      svec G (φm - φ0) x i - svec G (φm - φ0) (x + Pi.single μ 1) i := by
    rw [wExt_eq_neg_svec, wExt_eq_neg_svec]; ring
  rw [e]
  have key : ∀ y : Torus d (N₁ * L ^ m₁ * L ^ K), y ∈ R.sites →
      ∀ v : ℂ, G.spacing y * ‖v‖ ≤ V → ‖v‖ ≤ V / ℓ₀ := by
    intro y hy v hv
    have hsp := hℓR y hy
    rw [le_div_iff₀ hℓ]
    nlinarith [norm_nonneg v]
  rcases hx with hx | hx
  · have := hS.fwd x (R.sub_Ω hx) μ i
    simp only [one_mul] at this
    rw [norm_sub_rev]
    exact key x hx _ this
  · have := hS.bwd _ (R.sub_Ω hx) μ i
    simp only [one_mul, add_sub_cancel_right] at this
    exact key _ hx _ this

/-- (b) `‖α‖ ≤ δ₀/ℓ₀²` on `D` from `Small G α δ₀`. -/
theorem massChange_hα_of_small {m₁ N₁ : ℕ} [NeZero N₁]
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (R : Region G) {α : G.Ω 1 → ℂ} {δ₀ ℓ₀ : ℝ}
    (hℓ : 0 < ℓ₀) (hℓR : ∀ x ∈ R.sites, ℓ₀ ≤ G.spacing x) (hS : Small G α δ₀) :
    ∀ x : G.Ω 1, (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ∈ R.sites → ‖α x‖ ≤ δ₀ / ℓ₀ ^ 2 := by
  intro x hx
  have h1 := hS x
  have h2 := hℓR _ hx
  rw [le_div_iff₀ (by positivity)]
  have : ℓ₀ ^ 2 ≤ G.spacing (x : Torus d (N₁ * L ^ m₁ * L ^ K)) ^ 2 :=
    pow_le_pow_left₀ hℓ.le h2 2
  nlinarith [norm_nonneg (α x)]

/-- (c) The block coefficient bound from admissible weights (`a_j ∈ [1/2, 2]`, `1 ≤ j ≤ K`);
`G.spacing x = L ^ (layerIndex x)` by definition. -/
theorem massChange_hcoef_of_weights (R : Region G) {a : ℕ → ℝ} {ℓ₀ : ℝ} (hℓ : 0 < ℓ₀)
    (hw : IsAdmissibleWeights K a) (hℓR : ∀ x ∈ R.sites, ℓ₀ ≤ G.spacing x) :
    ∀ x ∈ R.sites, |a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2| ≤ 2 / ℓ₀ ^ 2 := by
  intro x hx
  obtain ⟨h1, h2, -⟩ := G.layerIndex_spec (R.sub_Ω hx)
  obtain ⟨ha1, ha2⟩ := hw _ h1 h2
  have hsp : ℓ₀ ≤ (L : ℝ) ^ G.layerIndex x := hℓR x hx
  have hp : 0 < ((L : ℝ) ^ G.layerIndex x) ^ 2 := by
    have : 0 < (L : ℝ) ^ G.layerIndex x := hℓ.trans_le hsp
    positivity
  rw [abs_div, abs_of_pos hp, abs_of_nonneg (by linarith)]
  calc a (G.layerIndex x) / ((L : ℝ) ^ G.layerIndex x) ^ 2
      ≤ 2 / ((L : ℝ) ^ G.layerIndex x) ^ 2 := div_le_div_of_nonneg_right ha2 hp.le
    _ ≤ 2 / ℓ₀ ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hℓ.le hsp 2)

/-- (d) The wall gradient: `|∂ φ̄ᵐ| ≤ c/ℓ₀` on the crossing bonds, from `BgBounds`. -/
theorem massChange_hgrad_of_bgBounds {m₁ N₁ : ℕ} [NeZero N₁]
    {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ} (R : Region G) {Dat : BgData G N}
    {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} {c ℓ₀ : ℝ} (hc : 0 ≤ c) (hℓ : 0 < ℓ₀)
    (hℓR : ∀ x ∈ R.sites, ℓ₀ ≤ G.spacing x) (hb : BgBounds G Dat φ α c) :
    ∀ b ∈ R.crossing, vnorm (R.outwardDeriv (barField G Dat.Ψ φ) b) ≤ c / ℓ₀ := by
  classical
  intro b hb'
  have hcr : ¬ (b.1 ∈ R.sites ↔ b.1 + Pi.single b.2 1 ∈ R.sites) := by
    simpa [Region.crossing] using hb'
  have key : ∀ y : Torus d (N₁ * L ^ m₁ * L ^ K), y ∈ R.sites → ∀ s : ℝ,
      s ≤ c / G.spacing y → s ≤ c / ℓ₀ := fun y hy s hs =>
    hs.trans (div_le_div_of_nonneg_left hc hℓ (hℓR y hy))
  by_cases h1 : b.1 ∈ R.sites
  · have e : R.outwardDeriv (barField G Dat.Ψ φ) b = fun i =>
        barField G Dat.Ψ φ (b.1 + Pi.single b.2 1) i - barField G Dat.Ψ φ b.1 i := by
      funext i; simp [Region.outwardDeriv, h1]
    rw [e]
    exact key _ h1 _ (hb.grad ⟨b.1, R.sub_Ω h1⟩ b.2).1
  · have h2 : b.1 + Pi.single b.2 1 ∈ R.sites := by
      by_contra h2; exact hcr ⟨fun h => absurd h h1, fun h => absurd h h2⟩
    have e : R.outwardDeriv (barField G Dat.Ψ φ) b = fun i =>
        barField G Dat.Ψ φ b.1 i - barField G Dat.Ψ φ (b.1 + Pi.single b.2 1) i := by
      funext i; simp [Region.outwardDeriv, h1]
    rw [e]
    have := (hb.grad ⟨b.1 + Pi.single b.2 1, R.sub_Ω h2⟩ b.2).2
    simp only [add_sub_cancel_right] at this
    exact key _ h2 _ this

/-- **The region bound for the mass change** (MASS-RESPONSE (2.5)), from the premises (1.3) and
the region geometry.  `Km = √N · Kw`; the wall term is `Ncross · ρ` with `Ncross = 2 d Nsite n`
(crude count `|st(D)| ≤ 2 d |D|`) and `ρ = δ₀ / ℓ₀`. -/
theorem massChange_region_bound (N : ℕ) (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₁ m₁ K : ℕ} [NeZero N₁] {ϱ : ℝ} {G : GeneratingSet d L (N₁ * L ^ m₁) K ϱ}
        (a : ℕ → ℝ) (μ m Bh δ₀ : ℝ) (D : BgData G N)
        {φ0 φm : G.Ω 1 × Fin N → ℂ} {α0 αm : G.Ω 1 → ℂ} (R : Region G) (β ℓ₀ Nsite n : ℝ),
        IsEL G a 0 D φ0 α0 → IsEL G a μ D φm αm →
        BgBounds G D φ0 α0 δ₀ → BgBounds G D φm αm δ₀ →
        GreenSetting G a 0 → Dec2.OpSetting G a 0 →
        0 ≤ δ₀ → δ₀ ≤ min (deltaStar d L N) δw → 2 * δ₀ ≤ c6 d L N →
        0 ≤ m → 0 ≤ Bh → m * Bh ≤ min (deltaStar d L N) δw →
        0 ≤ μ → (∀ x : G.Ω 1, μ * G.spacing (x : CTorus d L N₁ m₁ K) ^ 2 ≤ m) →
        (∀ (x : G.Ω 1) (i : Fin N), ‖φm (x, i) - D.h x i‖ ≤ Bh) →
        (∀ x : G.Ω 1, vn (fun i => φ0 (x, i)) ≤ 3 / 2) →
        0 ≤ β → 0 < ℓ₀ → (∀ x ∈ R.sites, ℓ₀ ≤ G.spacing x) → μ ≤ 1 / ℓ₀ ^ 2 → δ₀ ≤ 1 →
        (R.sites.card : ℝ) ≤ Nsite * n →
        β * ‖actionRegionC R a μ D φ0 - actionRegionC R a μ D φm‖ ≤
          (1 / 2) * ((2 * d + 4) * Nsite / ℓ₀ ^ 2) * ((Real.sqrt N * Kw) * Bh) ^ 2 * β * m ^ 2 * n +
            (Real.sqrt N * Kw) * Bh * β * m * (2 * d * Nsite * n * (δ₀ / ℓ₀)) := by
  obtain ⟨Kw, δw, hK, hδ, H⟩ := massChange_sameData_response N hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₁ m₁ K _ ϱ G a μ m Bh δ₀ D φ0 φm α0 αm R β ℓ₀ Nsite n h0 hm b0 bm hG hO hδ₀ hδs h2 hm0
    hBh0 hmB hμ hμℓ hB hφ hβ hℓ hℓR hμ1 hδ1 hcard
  obtain ⟨⟨hSm, hSup⟩, hresp⟩ := H a μ m Bh δ₀ D h0 hm b0 bm hG hO hδ₀ hδs h2 hm0 hBh0 hmB hμ hμℓ
    hB hφ
  have hV : 0 ≤ Kw * (m * Bh) := by positivity
  have hW0 : 0 ≤ (Real.sqrt N * Kw) * Bh * m := by positivity
  have hbond : ∀ (x : Torus d (N₁ * L ^ m₁ * L ^ K)) (μ' : Fin d),
      (x ∈ R.sites ∨ x + Pi.single μ' 1 ∈ R.sites) →
        vnorm (fun i => wExt D D φm φ0 (x + Pi.single μ' 1) i - wExt D D φm φ0 x i)
          ≤ (Real.sqrt N * Kw) * Bh * m / ℓ₀ := fun x μ' hx =>
    (massChange_hbond_of_supBounds R D hV hℓ hℓR hSup x μ' hx).trans (le_of_eq (by ring))
  have hNc : (R.crossing.card : ℝ) ≤ 2 * d * Nsite * n := by
    have h1 : (R.crossing.card : ℝ) ≤ 2 * d * R.sites.card := by exact_mod_cast R.card_crossing_le
    have h3 : (0 : ℝ) ≤ 2 * d := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hcard h3]
  exact massChange_region_bound_of_response R hm h0.2 (β := β) (m := m) (Km := Real.sqrt N * Kw)
    (Bh := Bh) (ℓ₀ := ℓ₀) (δ₀ := δ₀) (Nsite := Nsite) (n := n) (ρ := δ₀ / ℓ₀)
    (Ncross := 2 * d * Nsite * n) hβ hW0 hℓ (div_nonneg hδ₀ hℓ.le)
    (massChange_hgrad_of_bgBounds R hδ₀ hℓ hℓR bm) hresp hbond
    (massChange_hcoef_of_weights R hℓ hO.weights hℓR)
    (massChange_hα_of_small R hℓ hℓR bm.alpha) hδ₀ hδ1 hμ hμ1 hcard hNc
