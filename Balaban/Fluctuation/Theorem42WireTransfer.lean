/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.Theorem42WireDist
public import Balaban.Fluctuation.FarDecayUncond
public import Balaban.Fluctuation.Theorem42RealStep1
public import Balaban.Background.Theorem73

/-!
# Transfer of the regularity inequalities by Lemma 4.1 (FLUCTUATION.md §4.2, Steps 1-2)

For generating sets `𝔹_j ≺ 𝔹'_k` on the same torus whose layers agree on a set `E`, and a datum `D'`
of `𝔹'_k` in the complex domain `𝒟` with weights `compWeight L a₁` (BG (6.1)):

* `composed_sub_le`: the data change of the composition (6.2), `ψ(𝔹_j, 𝔹'_k; ψ̃) - ψ̃`, is bounded on
  the data sites of `𝔹_j` by `(2 d + 2) K₁ δ` (E1 of P2 (4.24) with `θ = 1`, `η = K₁ δ`);
* `composeField_eq_of_layers_agree`: it vanishes on `E` (LFR Lemma II.2.5 (c));
* `blockClose_transfer`, `gradClose_transfer`, `fieldClose_transfer`: if the background of a datum
  `D_0` of `𝔹_j` differs from the restriction of the background of `D'` by a field `δφ` (and a
  multiplier `δα`) that is small on the top layer, the regularity inequalities of `D_0` give those
  of `D'` with the radius increased by the size of `δφ`;
* `regIneq_transfer`: **Lemma 4.1 applied to `𝔹_j ≺ 𝔹'_k`**: the regularity inequalities
  `RegIneq` of the datum `D_0` of `𝔹_j` on a region `R` of the top layer, at distance `Dist` from
  the support of the data change, give those of the datum `D'` of `𝔹'_k` with radius
  `ε + (N+1)(1 + √ν_k) K_w c_F (2 d + 2) K₁ δ' e^{-γ_w Dist}`.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.LargeField

set_option linter.unusedSectionVars false

section Composed

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {G' : GeneratingSet d L N₀ k ϱ'}

/-- **The data change of the composition (6.2) is bounded by the domain parameter** (FLUCTUATION
§4.2 Step 1, "the composition formula (6.2) is affine in these data and has bounded block averaging
coefficients"): for `𝔹_j ≺ 𝔹'_k`, weights `compWeight L a₁` and a datum `D'` of `𝔹'_k` in the complex
domain `Ψ̃^c(𝔹'_k; δ, ε)`, the composed datum differs from `D'` on the data sites of `𝔹_j` by at most
`(2 d + 2) K₁ δ` (E1 of P2 (4.24) with `θ = 1`, `η = K₁ δ`). -/
theorem composed_sub_le {a₁ ν δ ε : ℝ} (ha₁ : 0 < a₁) (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (h : Precedes G G') {D' : BgData G' N} (hδ0 : 0 < δ) (hδε : δ ≤ ε) (hε : ε ≤ bgC0 d L N)
    (hδ1 : δ ≤ bgC1 d L N) (hνε : ν * ((L : ℝ) ^ k) ^ 2 * ε ^ 2 ≤ δ ^ 2)
    (hD : InDomainC G' ν δ ε D') {x : Torus d (N₀ * L ^ k)} (hx : x ∈ dataSites G) :
    vn (fun i => composeField G G' (compWeight L a₁) (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D')
      D'.Ψ x i - D'.Ψ x i) ≤ (2 * d + 2) * (bgK1 d L N * δ) := by
  have hL2 : 2 ≤ L := by have := H'.hL; omega
  have hDU : InUnionDomainC G' (bgC0 d L N) (bgC1 d L N) ν D' :=
    ⟨δ, ε, hδ0, hδε, hε, hδ1, hνε, hD⟩
  obtain ⟨-, hs, hb⟩ := theorem72 H' hDU
  have hb1 := hb δ ε hδ0 hδε hε hδ1 hνε hD
  have hη : 0 ≤ bgK1 d L N * δ := by have := bgK1_ge_one d L N; positivity
  have hC : CompHyp G G' (compWeight L a₁) 1 (bgK1 d L N * δ) D'.Ψ
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') :=
    { prec := h, θ_pos := one_pos, η_nn := hη, gap := scaleGap_one h
      ratio := fun x hx => compWeight_ratio hL2 ha₁ (G.layerIndex_spec hx).1
        (h.layerIndex_le hx)
      layerConst := D'.Ψ_layerConst
      bounds := fieldBounds_of_bgBounds (fun x hx i => rfl) hb1 hs.1.2 }
  have h1 := hC.compVec_sub_bar hx (y := x) (by
    rcases (mem_dataSites G).1 hx with hx | hx
    · rw [blockSet_of_mem G hx]; exact x_mem_blk _ _
    · rw [blockSet_of_not_mem G ((mem_collar G).1 hx).1]; exact Finset.mem_singleton_self _)
  have h2 : vn (Balaban.Background.barVec G' D'.Ψ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') x - D'.Ψ x) ≤
      bgK1 d L N * δ := by
    by_cases hx' : x ∈ G'.Ω 1
    · have := hb1.val ⟨x, hx'⟩
      have e : Balaban.Background.barVec G' D'.Ψ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') x - D'.Ψ x =
          fun i => bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D' (⟨x, hx'⟩, i) - D'.Ψ x i := by
        funext i; simp [Balaban.Background.barVec, barField, hx']
      rw [e]; exact this
    · have e : Balaban.Background.barVec G' D'.Ψ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') x - D'.Ψ x = 0 := by
        funext i; simp [Balaban.Background.barVec, barField, hx']
      rw [e, vn_zero]; exact hη
  have h3 := vn_triangle (compVec G G' (compWeight L a₁)
    (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x)
    (Balaban.Background.barVec G' D'.Ψ (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') x) (D'.Ψ x)
  show vn (compVec G G' (compWeight L a₁)
    (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D') D'.Ψ x - D'.Ψ x) ≤ _
  nlinarith
end Composed

section Agree

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ ϱ' : ℝ}
  {G : GeneratingSet d L N₀ (k + 1) ϱ} {G' : GeneratingSet d L N₀ (k + 1) ϱ'}

/-- **The composed datum equals the datum of `𝔹'` where the layers agree** (the equality `δΨ = 0`
on `E` of Step 1, LFR Lemma II.2.5 (c)), for any datum: the composition (6.2) is the identity at
the sites where the layers of `𝔹_j` and `𝔹'_k` coincide. -/
theorem composeField_eq_of_layers_agree {a : ℕ → ℝ}
    (ha : ∀ j, 1 ≤ j → j ≤ k + 1 → a j ≠ 0) (φ' : G'.Ω 1 × Fin N → ℂ)
    (Ψ' : Torus d (N₀ * L ^ (k + 1)) → Fin N → ℂ) {E : Set (Torus d (N₀ * L ^ (k + 1)))}
    (hE : ∀ x ∈ E, ∀ n, 1 ≤ n → n ≤ k + 1 → (x ∈ G.Ω n ↔ x ∈ G'.Ω n))
    {x : Torus d (N₀ * L ^ (k + 1))} (hx : x ∈ E) (hxd : x ∈ dataSites G) (i : Fin N) :
    composeField G G' a φ' Ψ' x i = Ψ' x i := by
  classical
  rcases (mem_dataSites G).1 hxd with hxΩ | hxc
  · have hli := layerIndex_eq_of_agree hE hx hxΩ
    have hn := G.layerIndex_spec hxΩ
    exact composeField_eq_of_agree a _ _ hxΩ hli (ha _ hn.1 hn.2.1) i
  · rw [composeField_of_collar a φ' Ψ' hxc]
    have hxΩ : x ∉ G.Ω 1 := ((mem_collar G).1 hxc).1
    have hxΩ' : x ∉ G'.Ω 1 := fun hh => hxΩ ((hE x hx 1 le_rfl (by omega)).2 hh)
    simp [barField, hxΩ']

end Agree

section Mono

variable {d L N₀ q N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ q ϱ}
  {D : BgData G N} {T : Finset (Torus d (N₀ * L ^ q))} {δ δ' : ℝ}

theorem blockClose_mono {φ : G.Ω 1 × Fin N → ℂ} (h : BlockClose G D φ T δ) (hle : δ ≤ δ') :
    BlockClose G D φ T δ' := fun x hx => (h x hx).trans_le hle

theorem gradClose_mono {φ : G.Ω 1 × Fin N → ℂ} {α : G.Ω 1 → ℂ} {ℓ : ℝ}
    (h : GradClose G D φ α ℓ T δ) (hle : δ ≤ δ') : GradClose G D φ α ℓ T δ' := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := h x hx
  exact ⟨fun μ => ⟨(h1 μ).1.trans_le hle, (h1 μ).2.trans_le hle⟩, h2.trans_le hle,
    h3.trans_le hle⟩

end Mono

section Shift

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ0 ϱ1 : ℝ}
  {G0 : GeneratingSet d L N₀ (k + 1) ϱ0} {G1 : GeneratingSet d L N₀ (k + 1) ϱ1}
  (hprec : Precedes G0 G1) {D0 : BgData G0 N} {D1 : BgData G1 N}
  {φ0 : G0.Ω 1 × Fin N → ℂ} {φ1 : G1.Ω 1 × Fin N → ℂ} {δφ : G0.Ω 1 × Fin N → ℂ}
  {R R' : Finset (Torus d (N₀ * L ^ (k + 1)))} {Θ ε : ℝ}

section Hyp

variable (hφ : ∀ (z : G0.Ω 1) (i : Fin N), φ1 (hprec.incl z, i) = φ0 (z, i) + δφ (z, i))
  (hRtop : ∀ x ∈ R, x ∈ G0.Ω (k + 1) ∧ x ∈ G1.Ω (k + 1))
  (hRblk : ∀ x ∈ R, ∀ y ∈ G0.blk (k + 1) x, y ∈ R') (hR'Ω : ∀ y ∈ R', y ∈ G0.Ω 1)
  (hsv : ∀ y ∈ R', ∀ (_ : y ∈ G0.Ω 1) (i : Fin N), ‖svec G0 δφ y i‖ ≤ Θ) (hΘ0 : 0 ≤ Θ)

include hφ hRtop hRblk hR'Ω hsv hΘ0

/-- Block closeness transfers from `𝔹_j` to `𝔹'_k` on the top layer. -/
theorem blockClose_transfer (hΨ : ∀ x ∈ dataSites G0, D0.Ψ x = D1.Ψ x)
    (hreg : BlockClose G0 D0 φ0 R ε) :
    BlockClose G1 D1 φ1 R (ε + N * Θ) := by
  intro x hxR
  have hxΩ0 : x ∈ G0.Ω 1 := G0.Ω_antitone le_rfl (by omega) (by omega) (hRtop x hxR).1
  have hxd : x ∈ dataSites G0 := (mem_dataSites G0).2 (Or.inl hxΩ0)
  have hli0 : G0.layerIndex x = k + 1 :=
    G0.layerIndex_eq (by omega) le_rfl ((GeneratingSet.mem_layer G0).2 ⟨(hRtop x hxR).1, by
      rw [G0.top]; exact Finset.notMem_empty _⟩)
  have hli1 : G1.layerIndex x = k + 1 :=
    G1.layerIndex_eq (by omega) le_rfl ((GeneratingSet.mem_layer G1).2 ⟨(hRtop x hxR).2, by
      rw [G1.top]; exact Finset.notMem_empty _⟩)
  have hblk : G1.blk (k + 1) x = G0.blk (k + 1) x := by
    ext y; simp [GeneratingSet.mem_blk]
  have key : ∀ i, blockAvg G1 φ1 x i = blockAvg G0 φ0 x i +
      blockMean G0 (k + 1) (fun y => svec G0 δφ y i) x := by
    intro i
    unfold blockAvg blockMean
    rw [hli0, hli1, hblk, ← mul_add, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy0 := hR'Ω y (hRblk x hxR y hy)
    rw [svec_of_mem G1 _ ⟨y, hprec.mem_Ω1 hy0⟩ i, svec_of_mem G0 _ ⟨y, hy0⟩ i,
      svec_of_mem G0 _ ⟨y, hy0⟩ i]
    exact hφ ⟨y, hy0⟩ i
  have hM : vn (fun i => blockMean G0 (k + 1) (fun y => svec G0 δφ y i) x) ≤ N * Θ :=
    vn_blockMean_le (G := G0) le_rfl (fun y i => svec G0 δφ y i) x (fun y hy =>
      vn_le_card_mul hΘ0 (hsv y (hRblk x hxR y hy) (hR'Ω y (hRblk x hxR y hy))))
  have h1 := hreg x hxR
  unfold blockDev at h1 ⊢
  have e : (fun i => D1.Ψ x i - blockAvg G1 φ1 x i) = fun i =>
      (D0.Ψ x i - blockAvg G0 φ0 x i) - blockMean G0 (k + 1) (fun y => svec G0 δφ y i) x := by
    funext i; rw [key i, ← hΨ x hxd]; ring
  rw [e]
  calc _ ≤ vn (fun i => D0.Ψ x i - blockAvg G0 φ0 x i) +
        vn (fun i => blockMean G0 (k + 1) (fun y => svec G0 δφ y i) x) := vn_sub_le' _ _
    _ < ε + N * Θ := by linarith

variable {α0 : G0.Ω 1 → ℂ} {α1 : G1.Ω 1 → ℂ} {δα : G0.Ω 1 → ℂ}
  (hα : ∀ z : G0.Ω 1, α1 (hprec.incl z) = α0 z + δα z)
  (hRnbr : ∀ x ∈ R, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R' ∧ x - Pi.single μ 1 ∈ R')

omit hRtop hRblk hΘ0 hR'Ω hsv in
theorem barVec_transfer {y : Torus d (N₀ * L ^ (k + 1))} (hy0 : y ∈ G0.Ω 1) :
    LargeField.barVec G1 D1 φ1 y = fun i => LargeField.barVec G0 D0 φ0 y i + svec G0 δφ y i := by
  funext i
  have h1 : y ∈ G1.Ω 1 := hprec.mem_Ω1 hy0
  simp only [LargeField.barVec, barField, h1, hy0, ↓reduceDIte]
  rw [svec_of_mem G0 _ ⟨y, hy0⟩ i]
  exact hφ ⟨y, hy0⟩ i

include hα hRnbr in
/-- Gradient closeness (`ℓ|∂φ̄|, ℓ²|Δφ̄|, ℓ²|α|`) transfers from `𝔹_j` to `𝔹'_k` on the top layer. -/
theorem gradClose_transfer
    (hfwd : ∀ x ∈ R, ∀ (_ : x ∈ G0.Ω 1) (μ : Fin d) (i : Fin N),
      (L : ℝ) ^ (k + 1) * ‖svec G0 δφ (x + Pi.single μ 1) i - svec G0 δφ x i‖ ≤ Θ)
    (hbwd : ∀ x ∈ R, ∀ (_ : x ∈ G0.Ω 1) (μ : Fin d) (i : Fin N),
      (L : ℝ) ^ (k + 1) * ‖svec G0 δφ (x - Pi.single μ 1) i - svec G0 δφ x i‖ ≤ Θ)
    (hlap : ∀ x ∈ R, ∀ (_ : x ∈ G0.Ω 1) (i : Fin N),
      ((L : ℝ) ^ (k + 1)) ^ 2 * ‖∑ μ : Fin d, (2 * svec G0 δφ x i - svec G0 δφ (x + Pi.single μ 1) i -
        svec G0 δφ (x - Pi.single μ 1) i)‖ ≤ Θ)
    (halpha : ∀ x ∈ R, ∀ (hx : x ∈ G0.Ω 1), ((L : ℝ) ^ (k + 1)) ^ 2 * ‖δα ⟨x, hx⟩‖ ≤ Θ)
    (hreg : GradClose G0 D0 φ0 α0 ((L : ℝ) ^ (k + 1)) R ε) :
    GradClose G1 D1 φ1 α1 ((L : ℝ) ^ (k + 1)) R (ε + (N + 1) * Θ) := by
  have hℓ : (0 : ℝ) < (L : ℝ) ^ (k + 1) := by
    have : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
    positivity
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  intro x' hxR
  obtain ⟨x, hx1⟩ := x'
  have hx0 : x ∈ G0.Ω 1 := G0.Ω_antitone le_rfl (by omega) (by omega) (hRtop x hxR).1
  have hxR' : x ∈ R' := hRblk x hxR x (GeneratingSet.mem_blk.2 rfl)
  have hg := hreg ⟨x, hx0⟩ hxR
  refine ⟨fun μ => ?_, ?_, ?_⟩
  · obtain ⟨hp, hm⟩ := hRnbr x hxR μ
    have hp0 := hR'Ω _ hp
    have hm0 := hR'Ω _ hm
    refine ⟨?_, ?_⟩
    · have e : LargeField.barVec G1 D1 φ1 (x + Pi.single μ 1) - LargeField.barVec G1 D1 φ1 x =
          (LargeField.barVec G0 D0 φ0 (x + Pi.single μ 1) - LargeField.barVec G0 D0 φ0 x) +
            fun i => svec G0 δφ (x + Pi.single μ 1) i - svec G0 δφ x i := by
        rw [barVec_transfer hprec hφ hp0, barVec_transfer hprec hφ hx0]
        funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
      have hc : ∀ i, ‖svec G0 δφ (x + Pi.single μ 1) i - svec G0 δφ x i‖ ≤
          Θ / (L : ℝ) ^ (k + 1) := fun i => by
        rw [le_div_iff₀ hℓ, mul_comm]; exact hfwd x hxR hx0 μ i
      have hv := vn_le_card_mul (div_nonneg hΘ0 hℓ.le) hc
      show (L : ℝ) ^ (k + 1) * vn (LargeField.barVec G1 D1 φ1 (x + Pi.single μ 1) -
        LargeField.barVec G1 D1 φ1 x) < _
      rw [e]
      calc (L : ℝ) ^ (k + 1) * vn _ ≤ (L : ℝ) ^ (k + 1) * (vn (LargeField.barVec G0 D0 φ0
            (x + Pi.single μ 1) - LargeField.barVec G0 D0 φ0 x) + N * (Θ / (L : ℝ) ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left ((vn_add' _ _).trans (add_le_add_right hv _)) hℓ.le
        _ < ε + (N + 1) * Θ := by
          have h1 := (hg.1 μ).1
          have : (L : ℝ) ^ (k + 1) * (N * (Θ / (L : ℝ) ^ (k + 1))) = N * Θ := by field_simp
          rw [mul_add, this]; nlinarith
    · have e : LargeField.barVec G1 D1 φ1 (x - Pi.single μ 1) - LargeField.barVec G1 D1 φ1 x =
          (LargeField.barVec G0 D0 φ0 (x - Pi.single μ 1) - LargeField.barVec G0 D0 φ0 x) +
            fun i => svec G0 δφ (x - Pi.single μ 1) i - svec G0 δφ x i := by
        rw [barVec_transfer hprec hφ hm0, barVec_transfer hprec hφ hx0]
        funext i; simp only [Pi.sub_apply, Pi.add_apply]; ring
      have hc : ∀ i, ‖svec G0 δφ (x - Pi.single μ 1) i - svec G0 δφ x i‖ ≤
          Θ / (L : ℝ) ^ (k + 1) := fun i => by
        rw [le_div_iff₀ hℓ, mul_comm]; exact hbwd x hxR hx0 μ i
      have hv := vn_le_card_mul (div_nonneg hΘ0 hℓ.le) hc
      show (L : ℝ) ^ (k + 1) * vn (LargeField.barVec G1 D1 φ1 (x - Pi.single μ 1) -
        LargeField.barVec G1 D1 φ1 x) < _
      rw [e]
      calc (L : ℝ) ^ (k + 1) * vn _ ≤ (L : ℝ) ^ (k + 1) * (vn (LargeField.barVec G0 D0 φ0
            (x - Pi.single μ 1) - LargeField.barVec G0 D0 φ0 x) + N * (Θ / (L : ℝ) ^ (k + 1))) :=
          mul_le_mul_of_nonneg_left ((vn_add' _ _).trans (add_le_add_right hv _)) hℓ.le
        _ < ε + (N + 1) * Θ := by
          have h1 := (hg.1 μ).2
          have : (L : ℝ) ^ (k + 1) * (N * (Θ / (L : ℝ) ^ (k + 1))) = N * Θ := by field_simp
          rw [mul_add, this]; nlinarith
  · have hℓ2 : (0 : ℝ) < ((L : ℝ) ^ (k + 1)) ^ 2 := by positivity
    have e : LargeField.barLap G1 D1 φ1 x = LargeField.barLap G0 D0 φ0 x +
        fun i => -∑ μ : Fin d, (2 * svec G0 δφ x i - svec G0 δφ (x + Pi.single μ 1) i -
          svec G0 δφ (x - Pi.single μ 1) i) := by
      funext i
      unfold LargeField.barLap
      simp only [Finset.sum_apply, Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
      rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun μ _ => ?_
      obtain ⟨hp, hm⟩ := hRnbr x hxR μ
      rw [barVec_transfer hprec hφ (hR'Ω _ hp), barVec_transfer hprec hφ (hR'Ω _ hm),
        barVec_transfer hprec hφ hx0]
      ring
    have hc : ∀ i, ‖-∑ μ : Fin d, (2 * svec G0 δφ x i - svec G0 δφ (x + Pi.single μ 1) i -
          svec G0 δφ (x - Pi.single μ 1) i)‖ ≤ Θ / ((L : ℝ) ^ (k + 1)) ^ 2 := fun i => by
      rw [norm_neg, le_div_iff₀ hℓ2, mul_comm]; exact hlap x hxR hx0 i
    have hv := vn_le_card_mul (div_nonneg hΘ0 hℓ2.le) hc
    show ((L : ℝ) ^ (k + 1)) ^ 2 * vn (LargeField.barLap G1 D1 φ1 x) < _
    rw [e]
    calc ((L : ℝ) ^ (k + 1)) ^ 2 * vn _ ≤ ((L : ℝ) ^ (k + 1)) ^ 2 * (vn (LargeField.barLap G0 D0 φ0 x) +
          N * (Θ / ((L : ℝ) ^ (k + 1)) ^ 2)) :=
        mul_le_mul_of_nonneg_left ((vn_add' _ _).trans (add_le_add_right hv _)) hℓ2.le
      _ < ε + (N + 1) * Θ := by
        have h1 := hg.2.1
        have : ((L : ℝ) ^ (k + 1)) ^ 2 * (N * (Θ / ((L : ℝ) ^ (k + 1)) ^ 2)) = N * Θ := by
          field_simp
        rw [mul_add, this]; nlinarith
  · have h2 := hg.2.2
    have e : α1 ⟨x, hx1⟩ = α0 ⟨x, hx0⟩ + δα ⟨x, hx0⟩ := hα ⟨x, hx0⟩
    show ((L : ℝ) ^ (k + 1)) ^ 2 * ‖α1 ⟨x, hx1⟩‖ < _
    rw [e]
    calc ((L : ℝ) ^ (k + 1)) ^ 2 * ‖α0 ⟨x, hx0⟩ + δα ⟨x, hx0⟩‖ ≤
        ((L : ℝ) ^ (k + 1)) ^ 2 * (‖α0 ⟨x, hx0⟩‖ + ‖δα ⟨x, hx0⟩‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ < ε + (N + 1) * Θ := by
        have := halpha x hxR hx0
        rw [mul_add]; nlinarith

include hφ hRtop hRblk hR'Ω hsv hΘ0 in
omit hα hRnbr in
/-- The mass-term closeness (`|φ - h| < δ/√ν`, `|h·h - 1| < δ²/ν`) transfers from `𝔹_j` to
`𝔹'_k` on the top layer, with the same `h`. -/
theorem fieldClose_transfer {νk : ℝ} (hh : ∀ x ∈ G0.Ω 1, D0.h x = D1.h x)
    (hreg : FieldClose G0 D0 φ0 νk R ε) :
    FieldClose G1 D1 φ1 νk R (ε + ((N : ℝ) + 1) * (1 + Real.sqrt νk) * Θ) := by
  intro hν x' hxR
  obtain ⟨x, hx1⟩ := x'
  have hx0 : x ∈ G0.Ω 1 := G0.Ω_antitone le_rfl (by omega) (by omega) (hRtop x hxR).1
  have hxR' : x ∈ R' := hRblk x hxR x (GeneratingSet.mem_blk.2 rfl)
  obtain ⟨h1, h2⟩ := hreg hν ⟨x, hx0⟩ hxR
  have hs : 0 < Real.sqrt νk := Real.sqrt_pos.2 hν
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hε : 0 ≤ ε := by
    have := lt_of_le_of_lt (vn_nonneg _) h1
    have h3 : 0 < ε / Real.sqrt νk := this
    exact (div_pos_iff_of_pos_right hs).1 h3 |>.le
  have hεΘ : 0 ≤ ((N : ℝ) + 1) * (1 + Real.sqrt νk) * Θ := by positivity
  have hD : D1.h x = D0.h x := (hh x hx0).symm
  refine ⟨?_, ?_⟩
  · have e : (fun i => φ1 (⟨x, hx1⟩, i) - D1.h x i) =
        (fun i => φ0 (⟨x, hx0⟩, i) - D0.h x i) + fun i => δφ (⟨x, hx0⟩, i) := by
      funext i
      have := hφ ⟨x, hx0⟩ i
      simp only [Pi.add_apply, hD]
      rw [show φ1 (⟨x, hx1⟩, i) = φ1 (hprec.incl ⟨x, hx0⟩, i) from rfl, this]; ring
    have hc : ∀ i, ‖δφ (⟨x, hx0⟩, i)‖ ≤ Θ := fun i => by
      have := hsv x hxR' hx0 i
      rwa [svec_of_mem G0 _ ⟨x, hx0⟩ i] at this
    have hv := vn_le_card_mul hΘ0 hc
    rw [e]
    have hpos : N * Θ ≤ ((N : ℝ) + 1) * (1 + Real.sqrt νk) * Θ / Real.sqrt νk := by
      rw [le_div_iff₀ hs]
      nlinarith [mul_nonneg hN0 hΘ0, mul_nonneg (mul_nonneg hN0 hs.le) hΘ0, mul_nonneg hs.le hΘ0,
        mul_nonneg (mul_nonneg hs.le hs.le) hΘ0]
    calc vn _ ≤ vn (fun i => φ0 (⟨x, hx0⟩, i) - D0.h x i) + vn (fun i => δφ (⟨x, hx0⟩, i)) :=
          vn_add' _ _
      _ < ε / Real.sqrt νk + ((N : ℝ) + 1) * (1 + Real.sqrt νk) * Θ / Real.sqrt νk := by linarith
      _ = _ := by field_simp
  · rw [hD]
    refine h2.trans_le ?_
    gcongr
    linarith

end Hyp

end Shift

/-- The increase of the regularity radius in the transfer (`regIneq_transfer`):
`(N+1)(1 + √ν_q) · K_w c_F (2d+2) K₁ δ' · e^{-γ_w Dist}` with `ν_q = ν L^{2q}`. -/
noncomputable def transferShift (d L N q : ℕ) [NeZero L] (ν Kw δ1 Dist : ℝ) : ℝ :=
  ((N : ℝ) + 1) * (1 + Real.sqrt (ν * ((L : ℝ) ^ q) ^ 2)) *
    (Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * δ1))) * Real.exp (-(gammaW d * Dist)))

section Transfer

variable {d L : ℕ} [NeZero L]

/-- **Transfer of the regularity inequalities from a smaller to a larger generating set in the top
layer** (FLUCTUATION §4.2 Step 2: Lemma 4.1 applied to `𝔹_j ≺ 𝔹'_k` agreeing near the cube). -/
theorem regIneq_transfer (hd : 3 ≤ d) (hL : 3 ≤ L) {N : ℕ} :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧
      ∀ {N₀ q N₁ m₁ : ℕ} [NeZero N₀] (_hN : N₀ = N₁ * L ^ m₁) {ϱ0 ϱ1 : ℝ}
        {G0 : GeneratingSet d L N₀ q ϱ0} {G1 : GeneratingSet d L N₀ q ϱ1} {a₁ ν : ℝ},
        0 < a₁ → BgHyp d L q ϱ0 (compWeight L a₁) ν → BgHyp d L q ϱ1 (compWeight L a₁) ν →
        2 * d * Real.log L ≤ agmonRate d / 16 * (ϱ0 - 1) → Precedes G0 G1 →
        ∀ {D1 : BgData G1 N} {δ1 ε1 : ℝ}, 0 < δ1 → δ1 ≤ ε1 → ε1 ≤ bgC0 d L N →
        δ1 ≤ thm73C1 d L N → ν * ((L : ℝ) ^ q) ^ 2 * ε1 ^ 2 ≤ δ1 ^ 2 → InDomainC G1 ν δ1 ε1 D1 →
        ∀ {D0 : BgData G0 N} {δ0 ε0 : ℝ}, 0 < δ0 → δ0 ≤ ε0 → ε0 ≤ bgC0 d L N →
        δ0 ≤ bgC1 d L N → ν * ((L : ℝ) ^ q) ^ 2 * ε0 ^ 2 ≤ δ0 ^ 2 → InDomainC G0 ν δ0 ε0 D0 →
        bgK1 d L N * δ0 ≤ deltaStar d L N → bgK1 d L N * δ0 ≤ δw →
        (2 * d + 2) * (bgK1 d L N * δ1) ≤ deltaStar d L N → (2 * d + 2) * (bgK1 d L N * δ1) ≤ δw →
        (∀ x ∈ dataSites G0, D0.Ψ x = D1.Ψ x) → (∀ x ∈ G0.Ω 1, D0.h x = D1.h x) →
        ∀ (E : Set (Torus d (N₀ * L ^ q))),
        (∀ x ∈ E, ∀ n, 1 ≤ n → n ≤ q → (x ∈ G0.Ω n ↔ x ∈ G1.Ω n)) →
        ∀ (W : Finset (Torus d (N₀ * L ^ q))), (∀ y, y ∉ E → y ∈ W) →
        ∀ (R R' : Finset (Torus d (N₀ * L ^ q))) {ε Dist : ℝ}, 1 ≤ q →
        (∀ x ∈ R, x ∈ G0.Ω q ∧ x ∈ G1.Ω q) →
        (∀ x ∈ R, ∀ μ : Fin d, x + Pi.single μ 1 ∈ R' ∧ x - Pi.single μ 1 ∈ R') →
        (∀ x ∈ R, ∀ y ∈ G0.blk q x, y ∈ R') → (∀ y ∈ R', y ∈ G0.Ω 1) →
        (∀ y ∈ R', ∀ w ∈ shadowN G0 W, ENNReal.ofReal Dist ≤ G0.pathDist y w) →
        RegIneq G0 (compWeight L a₁) ν D0 ε R R →
        RegIneq G1 (compWeight L a₁) ν D1 (ε + transferShift d L N q ν Kw δ1 Dist) R R := by
  obtain ⟨Kw, δw, hK, hδ, hmain⟩ := lemma41_domain_uncond (N := N) hd hL
  refine ⟨Kw, δw, hK, hδ, ?_⟩
  intro N₀ q N₁ m₁ _ hN ϱ0 ϱ1 G0 G1 a₁ ν ha₁ H0 H1 hsep hprec D1 δ1 ε1 hδ10 hδε1 hε1 hδ1c hνε1 hD1
    D0 δ0 ε0 hδ00 hδε0 hε0 hδ0c hνε0 hD0 hK0 hKw0 hK1 hKw1 hΨ hh E hE W hW' R R' ε Dist hq hRtop
    hRnbr hRblk hR'Ω hdist hreg
  subst hN
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  have : NeZero N₁ := ⟨by rintro rfl; exact absurd (by simp) (NeZero.ne (0 * L ^ m₁))⟩
  have hL2 : 2 ≤ L := by omega
  have hOp : Dec2.OpSetting G0 (compWeight L a₁) ν :=
    ⟨⟨H0.hd, H0.hL, H0.mass, H0.weights, hsep⟩, H0.massLe⟩
  have hD1U : InUnionDomainC G1 (bgC0 d L N) (thm73C1 d L N) ν D1 :=
    ⟨δ1, ε1, hδ10, hδε1, hε1, hδ1c, hνε1, hD1⟩
  obtain ⟨hDuU, hfield, hmult⟩ := theorem73_complex ha₁ H0 H1 hprec hD1U
  obtain ⟨δu, εu, hδu0, hδuε, hεu, hδu1, hνεu, hDuD⟩ := hDuU
  have hδ1b : δ1 ≤ bgC1 d L N := by
    have := thm73_small (L := L) (N := N) (by omega) hδ10 hδ1c; exact this.1
  set Du := composeData hprec (compWeight L a₁)
    (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D1) D1 with hDu
  have hsmallΨ : ∀ x ∈ dataSites G0, vn (fun i => Du.Ψ x i - D0.Ψ x i) ≤
      (2 * d + 2) * (bgK1 d L N * δ1) := by
    intro x hx
    have := composed_sub_le ha₁ H1 hprec hδ10 hδε1 hε1 hδ1b hνε1 hD1 hx
    have e : (fun i => Du.Ψ x i - D0.Ψ x i) = fun i => composeField G0 G1 (compWeight L a₁)
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D1) D1.Ψ x i - D1.Ψ x i := by
      funext i; rw [hΨ x hx]; rfl
    rw [e]; exact this
  have hδ₁0 : 0 ≤ (2 * d + 2) * (bgK1 d L N * δ1) := by
    have := bgK1_ge_one d L N
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  have hFar := hmain (δΨ := fun x i => Du.Ψ x i - D0.Ψ x i)
    (δ₁ := (2 * d + 2) * (bgK1 d L N * δ1)) H0 hOp hδ00 hδε0 hε0 hδ0c hνε0 hD0 hδu0 hδuε hεu hδu1
    hνεu hDuD hK0 hKw0 W ?_ (fun x i => by ring) ?_ hδ₁0 hK1 hKw1 hsmallΨ
  rotate_left
  · -- support
    intro y hy
    have hyE : y ∈ E := by by_contra h; exact hy (hW' y h)
    funext i
    show Du.Ψ y i - D0.Ψ y i = 0
    by_cases hyd : y ∈ dataSites G0
    · have := composeField_eq_of_layers_agree (a := compWeight L a₁)
        (fun j hj1 hj2 => (compWeight_pos hL2 ha₁ hj1).ne')
        (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D1) D1.Ψ hE hyE hyd i
      show composeField G0 G1 _ _ D1.Ψ y i - D0.Ψ y i = 0
      rw [this, hΨ y hyd]; ring
    · have h0 : composeField G0 G1 (compWeight L a₁) (bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D1)
          D1.Ψ y i = 0 := composeField_of_not_mem _ _ _ hyd i
      show composeField G0 G1 _ _ D1.Ψ y i - D0.Ψ y i = 0
      rw [h0, D0.Ψ_zero y hyd]; simp
  · -- the same h
    intro x i
    show (if x ∈ G0.Ω 1 then D1.h x i else 0 : ℂ) = D0.h x i
    by_cases hx : x ∈ G0.Ω 1
    · simp only [hx, ↓reduceIte]; rw [hh x hx]
    · simp only [hx, ↓reduceIte]; rw [D0.h_zero x hx]; rfl
  -- the data of the comparison
  set φ0 := bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) D0 with hφ0
  set α0 := bgMultC G0 (compWeight L a₁) ν (bgC0 d L N) D0 with hα0
  set φ1 := bgFieldC G1 (compWeight L a₁) ν (bgC0 d L N) D1 with hφ1
  set α1 := bgMultC G1 (compWeight L a₁) ν (bgC0 d L N) D1 with hα1
  set B : ℝ := Kw * (cF d L * ((2 * d + 2) * (bgK1 d L N * δ1))) with hB
  set Θ : ℝ := B * Real.exp (-(gammaW d * Dist)) with hΘ
  have hB0 : 0 ≤ B := mul_nonneg hK.le (mul_nonneg (cF_pos d L).le hδ₁0)
  have hΘ0 : 0 ≤ Θ := mul_nonneg hB0 (Real.exp_pos _).le
  have hγ : 0 ≤ gammaW d := gammaW_nonneg (by omega)
  set δφ : G0.Ω 1 × Fin N → ℂ := bgFieldC G0 (compWeight L a₁) ν (bgC0 d L N) Du - φ0 with hδφ
  set δα : G0.Ω 1 → ℂ := bgMultC G0 (compWeight L a₁) ν (bgC0 d L N) Du - α0 with hδα
  have hφ : ∀ (z : G0.Ω 1) (i : Fin N), φ1 (hprec.incl z, i) = φ0 (z, i) + δφ (z, i) := by
    intro z i
    have := congrFun hfield (z, i)
    simp only [hδφ, Pi.sub_apply]
    rw [this]; show φ1 (hprec.incl z, i) = φ0 (z, i) + (φ1 (hprec.incl z, i) - φ0 (z, i)); ring
  have hα : ∀ z : G0.Ω 1, α1 (hprec.incl z) = α0 z + δα z := by
    intro z
    have := congrFun hmult z
    simp only [hδα, Pi.sub_apply]
    rw [this]; show α1 (hprec.incl z) = α0 z + (α1 (hprec.incl z) - α0 z); ring
  have hdec : ∀ y ∈ R', y ∈ G0.Ω 1 →
      decay (gammaW d) (siteSetDist G0 (shadow G0 W) y) ≤ Real.exp (-(gammaW d * Dist)) := by
    intro y hy hyΩ
    refine decay_le_exp_dist hγ ?_
    refine le_iInf₂ fun w hw => hdist y hy w ?_
    exact hw
  have hRΩ : ∀ x ∈ R, x ∈ G0.Ω 1 := fun x hx =>
    G0.Ω_antitone le_rfl (by omega) (by omega) (hRtop x hx).1
  have hRR' : ∀ x ∈ R, x ∈ R' := fun x hx => hRblk x hx x (GeneratingSet.mem_blk.2 rfl)
  have hli0 : ∀ x ∈ R, G0.layerIndex x = k + 1 := fun x hx =>
    G0.layerIndex_eq (by omega) le_rfl ((GeneratingSet.mem_layer G0).2 ⟨(hRtop x hx).1, by
      rw [G0.top]; exact Finset.notMem_empty _⟩)
  have hspace : ∀ x ∈ R, G0.spacing x = (L : ℝ) ^ (k + 1) := fun x hx => by
    unfold GeneratingSet.spacing; rw [hli0 x hx]
  have hbd : ∀ x ∈ R, B * decay (gammaW d) (siteSetDist G0 (shadow G0 W) x) ≤ Θ := fun x hx =>
    mul_le_mul_of_nonneg_left (hdec x (hRR' x hx) (hRΩ x hx)) hB0
  have hsv : ∀ y ∈ R', ∀ (_ : y ∈ G0.Ω 1) (i : Fin N), ‖svec G0 δφ y i‖ ≤ Θ := by
    intro y hy hyΩ i
    rw [svec_of_mem G0 _ ⟨y, hyΩ⟩ i]
    exact (hFar.val ⟨y, hyΩ⟩ i).trans (mul_le_mul_of_nonneg_left (hdec y hy hyΩ) hB0)
  have hfwd : ∀ x ∈ R, ∀ (_ : x ∈ G0.Ω 1) (μ : Fin d) (i : Fin N),
      (L : ℝ) ^ (k + 1) * ‖svec G0 δφ (x + Pi.single μ 1) i - svec G0 δφ x i‖ ≤ Θ :=
    fun x hx hx0 μ i => by
      rw [← hspace x hx]; exact (hFar.fwd x hx0 μ i).trans (hbd x hx)
  have hbwd : ∀ x ∈ R, ∀ (_ : x ∈ G0.Ω 1) (μ : Fin d) (i : Fin N),
      (L : ℝ) ^ (k + 1) * ‖svec G0 δφ (x - Pi.single μ 1) i - svec G0 δφ x i‖ ≤ Θ :=
    fun x hx hx0 μ i => by
      rw [← hspace x hx]; exact (hFar.bwd x hx0 μ i).trans (hbd x hx)
  have hlap : ∀ x ∈ R, ∀ (_ : x ∈ G0.Ω 1) (i : Fin N),
      ((L : ℝ) ^ (k + 1)) ^ 2 * ‖∑ μ : Fin d, (2 * svec G0 δφ x i - svec G0 δφ (x + Pi.single μ 1) i -
        svec G0 δφ (x - Pi.single μ 1) i)‖ ≤ Θ :=
    fun x hx hx0 i => by
      rw [← hspace x hx]; exact (hFar.lap x hx0 i).trans (hbd x hx)
  have halpha : ∀ x ∈ R, ∀ (hx : x ∈ G0.Ω 1), ((L : ℝ) ^ (k + 1)) ^ 2 * ‖δα ⟨x, hx⟩‖ ≤ Θ :=
    fun x hx hx0 => by
      rw [← hspace x hx]; exact (hFar.alpha ⟨x, hx0⟩).trans (hbd x hx)
  have hs0 : 0 ≤ Real.sqrt (ν * ((L : ℝ) ^ (k + 1)) ^ 2) := Real.sqrt_nonneg _
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hshift : transferShift d L N (k + 1) ν Kw δ1 Dist =
      ((N : ℝ) + 1) * (1 + Real.sqrt (ν * ((L : ℝ) ^ (k + 1)) ^ 2)) * Θ := rfl
  rw [hshift]
  refine ⟨?_, ?_, ?_⟩
  · refine blockClose_mono (blockClose_transfer hprec hφ hRtop hRblk hR'Ω hsv hΘ0 hΨ hreg.1) ?_
    nlinarith [mul_nonneg hs0 hΘ0, mul_nonneg hN0 hΘ0, mul_nonneg (mul_nonneg hN0 hs0) hΘ0]
  · refine gradClose_mono (gradClose_transfer hprec hφ hRtop hRblk hR'Ω hsv hΘ0 hα hRnbr
      hfwd hbwd hlap halpha hreg.2.1) ?_
    nlinarith [mul_nonneg hs0 hΘ0, mul_nonneg hN0 hΘ0, mul_nonneg (mul_nonneg hN0 hs0) hΘ0]
  · exact fieldClose_transfer hprec hφ hRtop hRblk hR'Ω hsv hΘ0 hh hreg.2.2

end Transfer
end Balaban.Fluctuation
