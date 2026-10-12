/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.CubeFoldHolderLoc
public import Balaban.Localization.CubeFoldHolderChart
public import Balaban.Localization.CubeFoldHolderScale
public import Balaban.Localization.CutPointwiseWallMax

/-!
# The short regime of the mixed-wall Hölder estimate (VMOD-10 (3.11))

`cubeFold_holder_short_t`: the folded Hölder estimate read at the points `x, x'` through the chart pair,
for a fixed path-distance level `t` and a bound `M` of the retained quantity near `x`.
`cut_cutU_decay`: VMOD-9 (1.4) in decay form. `cubeFold_holder_short`: the estimate with the decay
`decay(γ, d_H(x, y'))` inserted, including infinite path distance (limit `t → ∞`).
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.LatticeGreen Balaban.Reflection Finset Matrix
  Filter Topology

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The short regime at a fixed path-distance level `t`** (VMOD-10 (3.11) before the decay is
inserted): the folded Hölder estimate, read at the points `x, x'` through the chart. -/
theorem cubeFold_holder_short_t (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ}
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c)) {B : ℕ} (hB : 2 ≤ B)
    (hSB : S + B ≤ N₀ * L ^ k)
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'Λ : x' ∈ cubeSet (N₀ * L ^ k) S c) {μ : Fin d}
    (hxe : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'e : x' + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c) {z : Fin d → ℤ}
    (hxz : x' = x + intTorus z) (hz1 : 1 ≤ ‖z‖) (hzB : ‖z‖ < B)
    (hshort : 2 ≤ G.layerIndex x ∧
      8 ≤ cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d ∧
      ‖z‖ ≤ (cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d) / 4)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {t : ℝ} (ht0 : 0 ≤ t)
    (ht : ENNReal.ofReal t ≤ G.pathDist x y') {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ w ∈ G.Ω 1, G.pathDist w x ≤ ENNReal.ofReal (2 * d + 1) →
      cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c))
        (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f))
        w ≤ M) :
    (G.spacing x) ^ 2 *
        ‖(zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x' + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x') -
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x)‖ ≤
      (holderKs d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        (Real.exp (-(agmonRate d / 2 * t)) * ((L : ℝ) ^ (2 * j') * Mf) + M) := by
  classical
  have hd0 : 0 < d := by omega
  set cut := cubeCut G (cubeSet (N₀ * L ^ k) S c) with hcutdef
  have hcut : CutAligned G cut := cubeCut_aligned G hΛ
  set u := (cutOperator G a ν cut α)⁻¹ *ᵥ f with hudef
  have hu : cutOperator G a ν cut α *ᵥ u = f := cutOperator_mulVec_inv G hcut hd0 hν ha α hα f
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hx
  obtain ⟨hj2, hρ8, hzρ⟩ := hshort
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, G.layerIndex x = j₀ + 1 := ⟨G.layerIndex x - 1, by omega⟩
  have hj01 : 1 ≤ j₀ := by omega
  rw [hj₀] at hxl hjk hρ8 hzρ
  simp only [Nat.add_sub_cancel] at hρ8 hzρ
  obtain ⟨p0, hp0, hlow⟩ := exists_lowerHalf (c := c) hxΛ
  obtain ⟨h0, he, hz, hze⟩ := cubeFold_chart_pair S c p0 hB hSB hlow hp0 hxΛ hx'Λ hxe hx'e hxz hzB
  have hfold := cubeFold_holder_fold hd hL hϱ hsep hν hν1 ha α hα S c hSℓ hu hΛ hj01 hjk hj'1 hj'k
    hxl hy' hxΛ hsupp hρ8 hMf0 hMf ht0 ht hM0 hM p0 hp0 hz1 hzρ hθ0 hθ1 μ
  rw [h0, he, hz, hze] at hfold
  rw [G.spacing_eq (by omega : 1 ≤ j₀ + 1) hjk hxl]
  exact hfold

/-- **The pointwise estimate in decay form** (VMOD-9 (1.4), as used by `cubeBlockBounds_mixed`). -/
theorem cut_cutU_decay (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ} (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c))
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (hy'Λ : y' ∈ cubeSet (N₀ * L ^ k) S c) {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf) {w : Torus d (N₀ * L ^ k)}
    (hw : w ∈ G.Ω 1) :
    cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c))
        (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f))
        w ≤
      cutKp d L * decay (agmonRate d / 2) (G.pathDist w y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  have h := cut_prop48_cube hd hL hϱ hsep (G := G) (a := a) (ν := ν) hν hν1 ha hα S c hSℓ hΛ
    hj'1 hj'k hy' hy'Λ hsupp hMf0 hMf hw
  by_cases hinf : G.pathDist w y' = ⊤
  · have := h.2 hinf
    rw [this]; unfold decay; simp [hinf]
  · have := h.1 hinf
    refine this.trans (le_of_eq ?_)
    unfold decay
    simp [hinf]

theorem cutKp_nonneg_of_three_le (hd : 3 ≤ d) : 0 ≤ cutKp d L := by
  have := cutK1_nonneg (L := L) hd
  unfold cutKp
  positivity

/-- The constant of the short regime with the decay inserted: `K_s (1 + K_p e^{γ D₀})`. -/
noncomputable def holderKshort (d L : ℕ) : ℝ :=
  holderKs d L * (1 + cutKp d L * Real.exp (agmonRate d / 2 * (2 * d + 1)))

theorem holderKshort_nonneg (hd : 3 ≤ d) : 0 ≤ holderKshort d L := by
  have := holderKs_nonneg (L := L) hd
  have := cutKp_nonneg_of_three_le (L := L) hd
  unfold holderKshort
  positivity

/-- **VMOD-10 (3.11) (short regime, decay inserted).** -/
theorem cubeFold_holder_short (hd : 3 ≤ d) (hL : 3 ≤ L) {G : GeneratingSet d L N₀ k ϱ}
    (hϱ : 1 ≤ ϱ) (hsep : (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)))
    {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1)
    (ha : IsAdmissibleWeights k a) {α : G.Ω 1 → ℂ}
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2))
    (S : ℕ) [NeZero S] (c : Fin d → ℕ) (hSℓ : S < N₀ * L ^ k)
    (hΛ : BlockAligned G (cubeSet (N₀ * L ^ k) S c)) {B : ℕ} (hB : 2 ≤ B)
    (hSB : S + B ≤ N₀ * L ^ k)
    {j' : ℕ} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (hy'Λ : y' ∈ cubeSet (N₀ * L ^ k) S c) {f : G.Ω 1 → ℂ}
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ i, ‖f i‖ ≤ Mf)
    {x x' : Torus d (N₀ * L ^ k)} (hx : x ∈ G.Ω 1) (hxΛ : x ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'Λ : x' ∈ cubeSet (N₀ * L ^ k) S c) {μ : Fin d}
    (hxe : x + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c)
    (hx'e : x' + Pi.single μ 1 ∈ cubeSet (N₀ * L ^ k) S c) {z : Fin d → ℤ}
    (hxz : x' = x + intTorus z) (hz1 : 1 ≤ ‖z‖) (hzB : ‖z‖ < B)
    (hshort : 2 ≤ G.layerIndex x ∧
      8 ≤ cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d ∧
      ‖z‖ ≤ (cutC0 d L * (L : ℝ) ^ (G.layerIndex x - 1) / d) / 4)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (G.spacing x) ^ 2 *
        ‖(zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x' + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x') -
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x)‖ ≤
      (holderKshort d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        (decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) := by
  classical
  have hd0 : 0 < d := by omega
  have hε0 := agmonRate_pos hd0
  set D0 : ℝ := 2 * d + 1 with hD0
  have hD00 : 0 ≤ D0 := by positivity
  set F : ℝ := (L : ℝ) ^ (2 * j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  set Kp := cutKp d L with hKp
  have hKp0 : 0 ≤ Kp := cutKp_nonneg_of_three_le hd
  have hU := fun {w} (hw : w ∈ G.Ω 1) => cut_cutU_decay hd hL hϱ hsep hν hν1 ha hα S c hSℓ hΛ hj'1
    hj'k hy' hy'Λ hsupp hMf0 hMf hw
  have hnear : ∀ {p q : Torus d (N₀ * L ^ k)}, G.pathDist p y' ≠ ⊤ →
      G.pathDist q p ≤ ENNReal.ofReal D0 → G.pathDist q y' ≠ ⊤ := by
    intro p q hp hqp
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hp⟩)
      ((G.pathDist_triangle q p y').trans (add_le_add hqp le_rfl))
  have hsp0 := spacing_pos G (x := x)
  have hX0 : 0 ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have : (0 : ℝ) < ‖z‖ := by linarith
    positivity
  have hK0 : 0 ≤ holderKshort d L := holderKshort_nonneg hd
  by_cases hinf : G.pathDist x y' = ⊤
  · -- infinite distance: the bound holds for every `t` with `M = 0`
    have hM : ∀ w ∈ G.Ω 1, G.pathDist w x ≤ ENNReal.ofReal D0 →
        cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c))
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f))
          w ≤ 0 := by
      intro w hw hwx
      have hwt : G.pathDist w y' = ⊤ := by
        by_contra hne
        have := hnear (p := w) (q := x) hne (by rw [GeneratingSet.pathDist_comm]; exact hwx)
        exact this hinf
      refine (hU hw).trans (le_of_eq ?_)
      rw [hwt]; unfold decay; simp
    have hbound : ∀ t : ℝ, 0 ≤ t →
        (G.spacing x) ^ 2 *
          ‖(zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x' + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x') -
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f)
              (x + Pi.single μ 1) -
            zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f) x)‖ ≤
          (holderKs d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
            (Real.exp (-(agmonRate d / 2 * t)) * F + 0) := by
      intro t ht0
      exact cubeFold_holder_short_t hd hL hϱ hsep hν hν1 ha α hα S c hSℓ hΛ hB hSB hj'1 hj'k hy'
        hsupp hMf0 hMf hx hxΛ hx'Λ hxe hx'e hxz hz1 hzB hshort hθ0 hθ1 ht0
        (by rw [hinf]; exact le_top) le_rfl hM
    have hlim : Tendsto (fun t : ℝ => (holderKs d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        (Real.exp (-(agmonRate d / 2 * t)) * F + 0)) atTop (nhds 0) := by
      have h1 : Tendsto (fun t : ℝ => agmonRate d / 2 * t) atTop atTop :=
        Filter.tendsto_id.const_mul_atTop (by positivity)
      have h2 := Real.tendsto_exp_neg_atTop_nhds_zero.comp h1
      have h3 := (h2.mul_const F).add_const 0
      have h4 := h3.const_mul ((holderKs d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)))
      simpa using h4
    have hle := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun t ht => hbound t ht⟩)
    have hdec : decay (agmonRate d / 2) (G.pathDist x y') = 0 := by
      rw [hinf]; unfold decay; simp
    rw [hdec]
    simp only [zero_mul, mul_zero]
    exact hle
  · set τ := (G.pathDist x y').toReal with hτ
    have hτ0 : 0 ≤ τ := ENNReal.toReal_nonneg
    have hM : ∀ w ∈ G.Ω 1, G.pathDist w x ≤ ENNReal.ofReal D0 →
        cutU G (cubeCut G (cubeSet (N₀ * L ^ k) S c))
          (zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G (cubeSet (N₀ * L ^ k) S c)) α)⁻¹ *ᵥ f))
          w ≤ Kp * Real.exp (agmonRate d / 2 * D0) * (Real.exp (-(agmonRate d / 2 * τ)) * F) := by
      intro w hw hwx
      have hwt : G.pathDist w y' ≠ ⊤ := hnear hinf hwx
      refine (hU hw).trans ?_
      have hlow : τ - D0 ≤ (G.pathDist w y').toReal := by
        have h1 : G.pathDist x y' ≤ ENNReal.ofReal D0 + G.pathDist w y' := by
          refine (G.pathDist_triangle x w y').trans (add_le_add ?_ le_rfl)
          rw [GeneratingSet.pathDist_comm]; exact hwx
        have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hwt⟩) h1
        rw [ENNReal.toReal_add ENNReal.ofReal_ne_top hwt, ENNReal.toReal_ofReal hD00] at h2
        linarith
      have hdw : decay (agmonRate d / 2) (G.pathDist w y') ≤
          Real.exp (agmonRate d / 2 * D0) * Real.exp (-(agmonRate d / 2 * τ)) := by
        have e : decay (agmonRate d / 2) (G.pathDist w y') =
            Real.exp (-(agmonRate d / 2 * (G.pathDist w y').toReal)) := by
          unfold decay; simp [hwt]
        rw [e, ← Real.exp_add]
        apply Real.exp_le_exp.2
        nlinarith only [hlow, hε0]
      calc Kp * decay (agmonRate d / 2) (G.pathDist w y') * F
          ≤ Kp * (Real.exp (agmonRate d / 2 * D0) * Real.exp (-(agmonRate d / 2 * τ))) * F := by
            gcongr
        _ = _ := by ring
    have hM0 : 0 ≤ Kp * Real.exp (agmonRate d / 2 * D0) * (Real.exp (-(agmonRate d / 2 * τ)) * F) := by
      positivity
    have h := cubeFold_holder_short_t hd hL hϱ hsep hν hν1 ha α hα S c hSℓ hΛ hB hSB hj'1 hj'k hy'
      hsupp hMf0 hMf hx hxΛ hx'Λ hxe hx'e hxz hz1 hzB hshort hθ0 hθ1 hτ0
      (ENNReal.ofReal_toReal hinf).le hM0 hM
    refine h.trans (le_of_eq ?_)
    have hdx : decay (agmonRate d / 2) (G.pathDist x y') = Real.exp (-(agmonRate d / 2 * τ)) := by
      unfold decay; simp [hinf, hτ]
    rw [hdx]
    unfold holderKshort
    ring

end Balaban.Localization
