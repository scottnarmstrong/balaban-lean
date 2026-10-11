/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.NC3

/-!
# NC3 at the smallest cube scale `m = 1` (no reflection)

When the cube has scale `m = 1` every layer index in it is at most `2`, so the factor
`ℓ_{j'}^{d/2}` lost in passing from the `L²` block bound (NC2) to the sup norm is at most `L^d`.
For a cut that is `CutAligned` (for instance `cubeCut G D`, `D = □ ∩ Ω₁`, which is block-aligned)
and a source in one block of layer `j' ≤ 2`:

* `Balaban.Reflection.small_value_cut`: `|ũ(x)| ≤ C₁ e^{-(ε₀/2) d(x, y')} ℓ_{j'}² M_f`;
* `Balaban.Reflection.small_pointwise_cut`: the same for `|ũ(x)| + ℓ(x) |ũ(x + e_μ) - ũ(x)|` on a
  retained bond;
* `Balaban.Reflection.small_laplacian_cut`: `ℓ(x)² |Δ^D u(x)|` at a point without removed bond;
* `Balaban.Reflection.small_holder_pair_cut`: the two-center Hölder bound for layers `≤ 2`.

The constants depend on `d` and `L` only.
-/

@[expose] public section

namespace Balaban.Reflection

open Matrix Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The sup norm bounds the `ℓ²` norm of a source supported in one `j'`-block:
`‖f‖² ≤ (L^{j'})^d M_f²`. -/
theorem sqNorm_le_block (G : GeneratingSet d L N₀ k ϱ) {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}
    (hj'k : j' ≤ k) (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf : ∀ z, ‖f z‖ ≤ Mf) :
    Green.sqNorm f ≤ ((L ^ j' : ℕ) : ℝ) ^ d * Mf ^ 2 := by
  classical
  unfold Green.sqNorm
  have h1 : ∀ i : G.Ω 1, ‖f i‖ ^ 2 ≤
      if jBlock d L N₀ k j' (i : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j' y' then Mf ^ 2 else 0 := by
    intro i
    by_cases hb : jBlock d L N₀ k j' (i : Torus d (N₀ * L ^ k)) = jBlock d L N₀ k j' y'
    · simp only [hb, ↓reduceIte]
      exact pow_le_pow_left₀ (norm_nonneg _) (hMf i) 2
    · simp only [hb, ↓reduceIte]
      have : f i = 0 := by
        by_contra hne
        exact hb (hsupp i hne)
      simp [this]
  calc ∑ i : G.Ω 1, ‖f i‖ ^ 2
      ≤ ∑ i : G.Ω 1, (if jBlock d L N₀ k j' (i : Torus d (N₀ * L ^ k)) =
          jBlock d L N₀ k j' y' then Mf ^ 2 else 0) := Finset.sum_le_sum fun i _ => h1 i
    _ = ∑ x ∈ G.Ω 1, (if jBlock d L N₀ k j' x = jBlock d L N₀ k j' y' then Mf ^ 2 else 0) := by
        rw [← Finset.sum_coe_sort (G.Ω 1)]
    _ ≤ ∑ x : Torus d (N₀ * L ^ k),
          (if jBlock d L N₀ k j' x = jBlock d L N₀ k j' y' then Mf ^ 2 else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun x _ _ => by
          split_ifs <;> positivity
    _ = ((L ^ j' : ℕ) : ℝ) ^ d * Mf ^ 2 := by
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        have e : (Finset.univ.filter (fun x : Torus d (N₀ * L ^ k) =>
            jBlock d L N₀ k j' x = jBlock d L N₀ k j' y')) =
            blockFibre (L ^ j') (N₀ * L ^ (k - j')) (jBlock d L N₀ k j' y') := by
          ext x; rw [Finset.mem_filter, mem_blockFibre]; simp [jBlock]
        rw [e, card_blockFibre (side_eq (N₀ := N₀) (k := k) (j := j') hj'k)]
        push_cast; ring

/-- The solution of the cut problem (the zero extension of `H_cut(α)⁻¹ f`). -/
noncomputable def cutSol (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (cut : Finset (Torus d (N₀ * L ^ k) × Fin d)) (α : G.Ω 1 → ℂ) (f : G.Ω 1 → ℂ) :
    Torus d (N₀ * L ^ k) → ℂ :=
  zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f)

/-- The constant of the bounded-scale estimates. -/
noncomputable def smallConst (d L : ℕ) : ℝ := 13 * L / poincareConst d * (L : ℝ) ^ d

theorem smallConst_nonneg (d L : ℕ) : 0 ≤ smallConst d L := by
  unfold smallConst poincareConst
  positivity

/-- **The block bound at bounded source scale**: the landed `L²` block decay with the sup norm of
the source, `j' ≤ 2`. -/
theorem small_block_bound {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)} (G : GeneratingSet d L N₀ k ϱ)
    (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν0 : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {j j' : ℕ} (hj1 : 1 ≤ j)
    (hjk : j ≤ k) (hj'1 : 1 ≤ j') (hj'2 : j' ≤ 2) (hj'k : j' ≤ k) {x y' : Torus d (N₀ * L ^ k)}
    (hx : x ∈ G.layer j) (hy' : y' ∈ G.layer j') (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ z, ‖f z‖ ≤ Mf) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) :
    (L : ℝ) ^ j * Real.sqrt (cutBlockGrad G cut j x (cutSol G a ν cut α f)) +
        Real.sqrt (∑ z ∈ G.blk j x, ‖cutSol G a ν cut α f z‖ ^ 2) ≤
      smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') *
        ((L : ℝ) ^ (2 * j') * Mf) := by
  have hHu := cutOperator_mulVec_inv G hcut hd hν0 ha α hα f
  obtain ⟨hfin, htop⟩ := green_G2i_cut_of_pathDist G hcut hd hν0 ha α hα hj1 hjk hj'1 hj'k hx hy'
    hHu hsupp hϱ hsep
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hsq : Real.sqrt (Green.sqNorm f) ≤ (L : ℝ) ^ d * Mf := by
    have h1 := sqNorm_le_block G hj'k f hsupp hMf
    have h2 : ((L ^ j' : ℕ) : ℝ) ^ d ≤ ((L : ℝ) ^ d) ^ 2 := by
      push_cast
      rw [← pow_mul, ← pow_mul, mul_comm d 2, mul_comm j' d]
      exact pow_le_pow_right₀ hL1 (by nlinarith)
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    calc Green.sqNorm f ≤ ((L ^ j' : ℕ) : ℝ) ^ d * Mf ^ 2 := h1
      _ ≤ ((L : ℝ) ^ d) ^ 2 * Mf ^ 2 := mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = ((L : ℝ) ^ d * Mf) ^ 2 := by ring
  by_cases ht : G.pathDist x y' = ⊤
  · have := htop ht
    rw [ht, decay_top]
    simp only [mul_zero, zero_mul]
    exact this
  · have h := hfin ht
    rw [decay_of_ne_top ht]
    refine h.trans ?_
    have hc : 0 ≤ 13 * (L : ℝ) / poincareConst d := by
      have := poincareConst_pos hd
      positivity
    have hE := Real.exp_pos (-(agmonRate d / 2 * (G.pathDist x y').toReal))
    calc 13 * L / poincareConst d * Real.exp (-(agmonRate d / 2 * (G.pathDist x y').toReal)) *
          ((L : ℝ) ^ j') ^ 2 * Real.sqrt (Green.sqNorm f)
        ≤ 13 * L / poincareConst d * Real.exp (-(agmonRate d / 2 * (G.pathDist x y').toReal)) *
          ((L : ℝ) ^ j') ^ 2 * ((L : ℝ) ^ d * Mf) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := by
          unfold smallConst
          rw [← pow_mul, mul_comm j' 2]
          ring

/-- **Bounded scale: value bound.** -/
theorem small_value_cut {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν0 : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {j' : ℕ} (hj'1 : 1 ≤ j')
    (hj'2 : j' ≤ 2) (hj'k : j' ≤ k) {x y' : Torus d (N₀ * L ^ k)} (hxΩ : x ∈ G.Ω 1)
    (hy' : y' ∈ G.layer j') (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ z, ‖f z‖ ≤ Mf) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) :
    ‖cutSol G a ν cut α f x‖ ≤
      smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hxΩ
  have h := small_block_bound G hcut hd hν0 ha α hα hj1 hjk hj'1 hj'2 hj'k hxl hy' f hsupp hMf0 hMf
    hϱ hsep
  have hxb : x ∈ G.blk (G.layerIndex x) x := G.mem_blk.2 rfl
  have h1 : ‖cutSol G a ν cut α f x‖ ≤
      Real.sqrt (∑ z ∈ G.blk (G.layerIndex x) x, ‖cutSol G a ν cut α f z‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (cutSol G a ν cut α f x))]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun z => ‖cutSol G a ν cut α f z‖ ^ 2)
      (fun _ _ => sq_nonneg _) hxb)
  have h2 : 0 ≤ (L : ℝ) ^ G.layerIndex x * Real.sqrt (cutBlockGrad G cut (G.layerIndex x) x
      (cutSol G a ν cut α f)) := by positivity
  linarith

/-- **Bounded scale: value and gradient on a retained bond.** -/
theorem small_pointwise_cut {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν0 : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {j' : ℕ} (hj'1 : 1 ≤ j')
    (hj'2 : j' ≤ 2) (hj'k : j' ≤ k) {x y' : Torus d (N₀ * L ^ k)} (hxΩ : x ∈ G.Ω 1)
    (hy' : y' ∈ G.layer j') (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ z, ‖f z‖ ≤ Mf) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) {μ : Fin d} (hμ : (x, μ) ∉ cut) :
    ‖cutSol G a ν cut α f x‖ + G.spacing x *
        ‖cutSol G a ν cut α f (x + Pi.single μ 1) - cutSol G a ν cut α f x‖ ≤
      smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hxΩ
  have h := small_block_bound G hcut hd hν0 ha α hα hj1 hjk hj'1 hj'2 hj'k hxl hy' f hsupp hMf0 hMf
    hϱ hsep
  have hxb : x ∈ G.blk (G.layerIndex x) x := G.mem_blk.2 rfl
  have h1 : ‖cutSol G a ν cut α f x‖ ≤
      Real.sqrt (∑ z ∈ G.blk (G.layerIndex x) x, ‖cutSol G a ν cut α f z‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg (cutSol G a ν cut α f x))]
    exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun z => ‖cutSol G a ν cut α f z‖ ^ 2)
      (fun _ _ => sq_nonneg _) hxb)
  have h2 : ‖cutSol G a ν cut α f (x + Pi.single μ 1) - cutSol G a ν cut α f x‖ ≤
      Real.sqrt (cutBlockGrad G cut (G.layerIndex x) x (cutSol G a ν cut α f)) := by
    rw [← Real.sqrt_sq (norm_nonneg _)]
    exact Real.sqrt_le_sqrt (single_le_cutBlockGrad G _ _ hμ)
  have hL : (0 : ℝ) ≤ (L : ℝ) ^ G.layerIndex x := by positivity
  have hsp : G.spacing x = (L : ℝ) ^ G.layerIndex x := rfl
  rw [hsp]
  nlinarith [mul_le_mul_of_nonneg_left h2 hL]

/-- **Bounded scale: Laplacian bound** at a point without removed bond. -/
theorem small_laplacian_cut {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν0 : 0 ≤ ν) (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (ha : IsAdmissibleWeights k a)
    (α : G.Ω 1 → ℂ) (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {j' : ℕ}
    (hj'1 : 1 ≤ j') (hj'2 : j' ≤ 2) (hj'k : j' ≤ k) {x y' : Torus d (N₀ * L ^ k)}
    (hxΩ : x ∈ G.Ω 1) (hc : NoCutAt cut x) (hy' : y' ∈ G.layer j') (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ z, ‖f z‖ ≤ Mf) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) :
    (G.spacing x) ^ 2 *
        ‖∑ μ : Fin d, (2 * cutSol G a ν cut α f x - cutSol G a ν cut α f (x + Pi.single μ 1) -
          cutSol G a ν cut α f (x - Pi.single μ 1))‖ ≤
      Real.exp (agmonRate d * d) * (1 + 4 * smallConst d L) *
        decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  have hC := smallConst_nonneg d L
  have hlap := laplacian_cut_bound hcut hd hν0 hν1 ha α hα hj'1 hj'k hy' f hsupp hMf0 hMf hxΩ hc
    (V := smallConst d L * ((L : ℝ) ^ (2 * j') * Mf)) (by positivity) (by
      intro q' hq'
      obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hxΩ
      have hq'l : q' ∈ G.layer (G.layerIndex x) := (G.mem_layer_iff hj1 hjk hq').2 hxl
      have hq'Ω : q' ∈ G.Ω 1 := G.layer_subset hj1 hjk hq'l
      have := small_value_cut G hcut hd hν0 ha α hα hj'1 hj'2 hj'k hq'Ω hy' f hsupp hMf0 hMf hϱ hsep
      exact (by simpa [cutSol] using this.trans (le_of_eq (by ring))))
  refine hlap.trans (le_of_eq ?_)
  ring

/-- **Bounded scale: two-center Hölder bound** (layers `≤ 2`). -/
theorem small_holder_pair_cut {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    (G : GeneratingSet d L N₀ k ϱ) (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ}
    (hν0 : 0 ≤ ν) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {j' : ℕ} (hj'1 : 1 ≤ j')
    (hj'2 : j' ≤ 2) (hj'k : j' ≤ k) {y' : Torus d (N₀ * L ^ k)} (hy' : y' ∈ G.layer j')
    (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ z, ‖f z‖ ≤ Mf) (hϱ : 1 ≤ ϱ)
    (hsep : (L : ℝ) ≤ Real.exp (agmonRate d / 2 * (ϱ - 1))) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    {x x' : Torus d (N₀ * L ^ k)} (hxΩ : x ∈ G.Ω 1) (hx'Ω : x' ∈ G.Ω 1)
    (hx2 : G.layerIndex x ≤ 2) (hlay : G.layerIndex x ≤ G.layerIndex x' + 1)
    {z : Fin d → ℤ} (hz : 1 ≤ ‖z‖) {ν' : Fin d} (hν : (x, ν') ∉ cut) (hν' : (x', ν') ∉ cut) :
    (G.spacing x) ^ 2 *
        ‖(cutSol G a ν cut α f (x' + Pi.single ν' 1) - cutSol G a ν cut α f x') -
          (cutSol G a ν cut α f (x + Pi.single ν' 1) - cutSol G a ν cut α f x)‖ ≤
      ((L : ℝ) ^ 3 * smallConst d L / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        ((decay (agmonRate d / 2) (G.pathDist x y') + decay (agmonRate d / 2) (G.pathDist x' y')) *
          ((L : ℝ) ^ (2 * j') * Mf)) := by
  have hC := smallConst_nonneg d L
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have p1 := small_pointwise_cut G hcut hd hν0 ha α hα hj'1 hj'2 hj'k hxΩ hy' f hsupp hMf0 hMf hϱ
    hsep hν
  have p2 := small_pointwise_cut G hcut hd hν0 ha α hα hj'1 hj'2 hj'k hx'Ω hy' f hsupp hMf0 hMf hϱ
    hsep hν'
  set F := (L : ℝ) ^ (2 * j') * Mf with hF
  have hF0 : 0 ≤ F := by positivity
  have d1 := decay_nonneg (agmonRate d / 2) (G.pathDist x y')
  have d2 := decay_nonneg (agmonRate d / 2) (G.pathDist x' y')
  set D1 := cutSol G a ν cut α f (x + Pi.single ν' 1) - cutSol G a ν cut α f x with hD1
  set D2 := cutSol G a ν cut α f (x' + Pi.single ν' 1) - cutSol G a ν cut α f x' with hD2
  have hs1 : 1 ≤ G.spacing x := one_le_pow₀ hL1
  have hs2 : 1 ≤ G.spacing x' := one_le_pow₀ hL1
  have hsx : G.spacing x ≤ (L : ℝ) ^ 2 := by
    unfold GeneratingSet.spacing; exact pow_le_pow_right₀ hL1 hx2
  have hsx' : G.spacing x ≤ L * G.spacing x' := by
    unfold GeneratingSet.spacing
    calc (L : ℝ) ^ G.layerIndex x ≤ (L : ℝ) ^ (G.layerIndex x' + 1) := pow_le_pow_right₀ hL1 hlay
      _ = _ := by ring
  have n1 : G.spacing x * ‖D1‖ ≤ smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') * F := by
    have := norm_nonneg (cutSol G a ν cut α f x)
    linarith
  have n2 : G.spacing x' * ‖D2‖ ≤ smallConst d L * decay (agmonRate d / 2) (G.pathDist x' y') * F := by
    have := norm_nonneg (cutSol G a ν cut α f x')
    linarith
  have hsp0 : 0 < G.spacing x := by linarith
  have hnorm : ‖D2 - D1‖ ≤ ‖D2‖ + ‖D1‖ := norm_sub_le _ _
  -- the bound without the Hölder factor
  have hmain : (G.spacing x) ^ 2 * ‖D2 - D1‖ ≤
      (L : ℝ) ^ 3 * smallConst d L * ((decay (agmonRate d / 2) (G.pathDist x y') +
        decay (agmonRate d / 2) (G.pathDist x' y')) * F) := by
    have e1 : (G.spacing x) ^ 2 * ‖D1‖ ≤ (L : ℝ) ^ 2 * (smallConst d L *
        decay (agmonRate d / 2) (G.pathDist x y') * F) := by
      calc (G.spacing x) ^ 2 * ‖D1‖ = G.spacing x * (G.spacing x * ‖D1‖) := by ring
        _ ≤ (L : ℝ) ^ 2 * (smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') * F) :=
          mul_le_mul hsx n1 (by positivity) (by positivity)
    have e2 : (G.spacing x) ^ 2 * ‖D2‖ ≤ (L : ℝ) ^ 3 * (smallConst d L *
        decay (agmonRate d / 2) (G.pathDist x' y') * F) := by
      calc (G.spacing x) ^ 2 * ‖D2‖ = G.spacing x * (G.spacing x * ‖D2‖) := by ring
        _ ≤ G.spacing x * (L * (G.spacing x' * ‖D2‖)) := by
            refine mul_le_mul_of_nonneg_left ?_ hsp0.le
            nlinarith [norm_nonneg D2]
        _ ≤ (L : ℝ) ^ 2 * (L * (smallConst d L * decay (agmonRate d / 2) (G.pathDist x' y') * F)) :=
            mul_le_mul hsx (mul_le_mul_of_nonneg_left n2 (by positivity)) (by positivity)
              (by positivity)
        _ = _ := by ring
    have hL2 : (L : ℝ) ^ 2 ≤ (L : ℝ) ^ 3 := pow_le_pow_right₀ hL1 (by norm_num)
    calc (G.spacing x) ^ 2 * ‖D2 - D1‖ ≤ (G.spacing x) ^ 2 * (‖D2‖ + ‖D1‖) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (G.spacing x) ^ 2 * ‖D2‖ + (G.spacing x) ^ 2 * ‖D1‖ := by ring
      _ ≤ _ := by
          have h3 : (L : ℝ) ^ 2 * (smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') * F) ≤
              (L : ℝ) ^ 3 * (smallConst d L * decay (agmonRate d / 2) (G.pathDist x y') * F) :=
            mul_le_mul_of_nonneg_right hL2 (by positivity)
          nlinarith
  -- the Hölder factor is at least one
  have hX1 : 1 ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have h1 : 1 ≤ (G.spacing x) ^ θ := Real.one_le_rpow hs1 hθ0.le
    have h2 : 1 ≤ ‖z‖ ^ (1 - θ) := Real.one_le_rpow hz (by linarith)
    nlinarith
  have hθ' : 1 ≤ 1 / θ := by rw [le_div_iff₀ hθ0]; linarith
  have hT : 0 ≤ (decay (agmonRate d / 2) (G.pathDist x y') +
        decay (agmonRate d / 2) (G.pathDist x' y')) * F := by positivity
  have hB : 0 ≤ (L : ℝ) ^ 3 * smallConst d L := by positivity
  refine hmain.trans ?_
  have : (L : ℝ) ^ 3 * smallConst d L / θ = ((L : ℝ) ^ 3 * smallConst d L) * (1 / θ) := by ring
  rw [this]
  have h1θ : (1 : ℝ) ≤ (1 / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) := by nlinarith
  calc _ = ((L : ℝ) ^ 3 * smallConst d L) * 1 * ((decay (agmonRate d / 2) (G.pathDist x y') +
        decay (agmonRate d / 2) (G.pathDist x' y')) * F) := by ring
    _ ≤ ((L : ℝ) ^ 3 * smallConst d L) * ((1 / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ))) *
        ((decay (agmonRate d / 2) (G.pathDist x y') +
        decay (agmonRate d / 2) (G.pathDist x' y')) * F) := by
        refine mul_le_mul_of_nonneg_right ?_ hT
        nlinarith
    _ = _ := by ring

end Balaban.Reflection
