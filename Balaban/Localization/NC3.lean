/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectionSource
public import Balaban.Localization.CubeRegimes
public import Balaban.Multiscale.CutPointwise
import Mathlib.Tactic.Linarith

/-!
# NC3: pointwise and Hölder bounds for the Neumann cube operator (reflection regime)

Let `u = H_cut(α)⁻¹ f`, `H_cut` the cut operator of the cube `□` (the cube cut `cubeCut G □`) and
`f` supported in one complete `j'`-block of `y' ∈ □` with `‖f‖_∞ ≤ M_f`.  Under the folding
hypotheses (`FoldSetting`, which for an aligned cube of scale `m ≥ 2` follow from the localization
separation, `AlignedCube.foldSetting`), the landed bounds for the *uncut* operator on the reflected
generating set give, by the intertwining `R3`/`R4`:

* `Balaban.Reflection.pointwise_cut_cube`: for `x ∈ □` whose forward bonds stay in `□`
  `|ũ(x)| + ℓ(x) ∑_μ |ũ(x + e_μ) - ũ(x)| ≤ K e^{-(ε₀/2) d_G(x, y')} ℓ_{j'}² M_f`
  (the right side is `0` if `d_G(x, y') = ∞`), with `K = K(d, L)` independent of the cube, of
  `k` and of the torus;
* `Balaban.Reflection.holder_pair_cut_cube`: the two-center Hölder bound of `holder_pair_decay`;
* `Balaban.Reflection.holder_connected_cut_cube`: the one-center Hölder bound for pairs at path
  distance `≤ C`.
-/

@[expose] public section

namespace Balaban.Reflection

open Matrix Balaban Balaban.Multiscale Balaban.Localization

variable {d L N₀ k : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}
  {G : GeneratingSet d L N₀ k ϱ} {q s : ℕ} {c : Fin d → ℕ} [NeZero s]

/-- Comparison of two decay factors: if `D₁ ≤ C + D₂` then `e^{-γ D₂} ≤ e^{γ C} e^{-γ D₁}`. -/
theorem decay_le_exp_mul {γ C : ℝ} (hγ : 0 ≤ γ) (hC : 0 ≤ C) {D₁ D₂ : ENNReal}
    (h : D₁ ≤ ENNReal.ofReal C + D₂) : decay γ D₂ ≤ Real.exp (γ * C) * decay γ D₁ := by
  have h1 := decay_anti_dist hγ h
  rw [decay_add_dist, decay_of_ne_top (c := γ) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hC] at h1
  have hee : Real.exp (γ * C) * Real.exp (-(γ * C)) = 1 := by
    rw [← Real.exp_add]; simp
  calc decay γ D₂ = Real.exp (γ * C) * (Real.exp (-(γ * C)) * decay γ D₂) := by
        rw [← mul_assoc, hee, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le

/-- The solution `ũ` of the cube problem: the zero extension to the torus of
`H_cut(α)⁻¹ f` on `Ω₁`, `cut = cubeCut G □`. -/
noncomputable def cubeSol (G : GeneratingSet d L N₀ k ϱ) (a : ℕ → ℝ) (ν : ℝ)
    (Λ : Finset (Torus d (N₀ * L ^ k))) (α : G.Ω 1 → ℂ) (f : G.Ω 1 → ℂ) :
    Torus d (N₀ * L ^ k) → ℂ :=
  zeroExt (G.Ω 1) ((cutOperator G a ν (cubeCut G Λ) α)⁻¹ *ᵥ f)

/-- **Lemma R4 (pointwise form).** The solution of the reflected problem with the even extension of
the source is the even extension of the cube solution. -/
theorem reflSol_reflU (h : FoldSetting G q s c) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν : 0 ≤ ν)
    (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) (f : G.Ω 1 → ℂ)
    (p : Torus d (2 * s * L ^ q)) :
    reflSol h a ν α (reflU h f) p = cubeSol G a ν (cubeOf N₀ L k q s c) α f (foldTo N₀ L k q s c p) := by
  unfold reflSol cubeSol
  rw [← reflU_inv h hd hν ha α hα f]
  exact zeroExt_reflU h _ p

/-- **NC3, pointwise bound for the cube Green's function** (value and forward gradient on retained
bonds).  `ε₀ = agmonRate d`; the constant depends on `d` and `L` only. -/
theorem pointwise_cut_cube (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s], FoldSetting G q s c → ∀ {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ {x : Torus d (N₀ * L ^ k)},
      x ∈ cubeOf N₀ L k q s c → (∀ μ : Fin d, x + Pi.single μ 1 ∈ cubeOf N₀ L k q s c) →
      ‖cubeSol G a ν (cubeOf N₀ L k q s c) α f x‖ + G.spacing x *
          ∑ μ : Fin d, ‖cubeSol G a ν (cubeOf N₀ L k q s c) α f (x + Pi.single μ 1) -
            cubeSol G a ν (cubeOf N₀ L k q s c) α f x‖ ≤
        K * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  obtain ⟨K, hK, hU⟩ := refl_U_le (d := d) (L := L) hd hL
  refine ⟨K, hK, ?_⟩
  intro k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f hsupp Mf hMf0
    hMf x hx hxe
  have hd0 : 0 < d := by omega
  have key := hU G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf
    (unfoldPt N₀ L k q s c x)
  have hF := foldTo_unfoldPt h hx
  simp only [reflSol_reflU h hd0 hν0 ha α hα f, spacing_reflectedGS h, hF,
    foldTo_unfoldPt_add_single h hx _ (hxe _)] at key
  exact key

omit [NeZero N₀] [NeZero L] [NeZero s] in
theorem liftPt_unfoldPt {x x' : Torus d (N₀ * L ^ k)} {z : Fin d → ℤ}
    (hz : ∀ i, z i = ((x' i - (c i : ZMod (N₀ * L ^ k))).val : ℤ) -
      ((x i - (c i : ZMod (N₀ * L ^ k))).val : ℤ)) :
    liftPt (unfoldPt N₀ L k q s c x) z = unfoldPt N₀ L k q s c x' := by
  funext i
  have h1 : (unfoldPt N₀ L k q s c x i) = (((x i - (c i : ZMod (N₀ * L ^ k))).val : ℕ) :
      ZMod (2 * s * L ^ q)) := rfl
  have h2 : (unfoldPt N₀ L k q s c x' i) = (((x' i - (c i : ZMod (N₀ * L ^ k))).val : ℕ) :
      ZMod (2 * s * L ^ q)) := rfl
  simp only [liftPt, Pi.add_apply, h1, h2, hz i]
  push_cast
  ring

/-- **NC3, two-center Hölder bound for the cube Green's function** (`holder_pair_decay` on the
reflected set).  The pair `(x, x')` is given by its chart coordinates, `z = loc x' - loc x`. -/
theorem holder_pair_cut_cube (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s], FoldSetting G q s c → ∀ {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ {x x' : Torus d (N₀ * L ^ k)},
      x ∈ cubeOf N₀ L k q s c → x' ∈ cubeOf N₀ L k q s c →
      G.layerIndex x ≤ G.layerIndex x' + 1 → ∀ {z : Fin d → ℤ},
      (∀ i, z i = ((x' i - (c i : ZMod (N₀ * L ^ k))).val : ℤ) -
        ((x i - (c i : ZMod (N₀ * L ^ k))).val : ℤ)) → 1 ≤ ‖z‖ →
      ∀ (ν' : Fin d), x + Pi.single ν' 1 ∈ cubeOf N₀ L k q s c →
      x' + Pi.single ν' 1 ∈ cubeOf N₀ L k q s c →
      (G.spacing x) ^ 2 *
          ‖(cubeSol G a ν (cubeOf N₀ L k q s c) α f (x' + Pi.single ν' 1) -
              cubeSol G a ν (cubeOf N₀ L k q s c) α f x') -
            (cubeSol G a ν (cubeOf N₀ L k q s c) α f (x + Pi.single ν' 1) -
              cubeSol G a ν (cubeOf N₀ L k q s c) α f x)‖ ≤
        (B / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
          ((decay (agmonRate d / 2) (G.pathDist x y') +
            decay (agmonRate d / 2) (G.pathDist x' y')) * ((L : ℝ) ^ (2 * j') * Mf)) := by
  obtain ⟨B, hB, hH⟩ := refl_holder_le (d := d) (L := L) hd hL
  refine ⟨B, hB, ?_⟩
  intro θ hθ0 hθ1 k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f hsupp Mf
    hMf0 hMf x x' hx hx' hlay z hz hz1 ν' hxe hxe'
  have hd0 : 0 < d := by omega
  have hlay' : (reflectedGS G h).layerIndex (unfoldPt N₀ L k q s c x) ≤
      (reflectedGS G h).layerIndex (unfoldPt N₀ L k q s c x') + 1 := by
    rw [layerIndex_reflectedGS h, layerIndex_reflectedGS h, foldTo_unfoldPt h hx,
      foldTo_unfoldPt h hx']
    exact hlay
  have key := hH hθ0 hθ1 G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf hlay' hz1
    (liftPt_unfoldPt hz) ν'
  simp only [reflSol_reflU h hd0 hν0 ha α hα f, spacing_reflectedGS h, foldTo_unfoldPt h hx,
    foldTo_unfoldPt h hx', foldTo_unfoldPt_add_single h hx ν' hxe,
    foldTo_unfoldPt_add_single h hx' ν' hxe'] at key
  exact key

/-- **NC3, one-center Hölder bound for locally connected pairs.** If `d_G(x, x') ≤ C` the two
decay factors are comparable: the bound is `(B (1 + e^{(ε₀/2) C}) / θ) ... e^{-(ε₀/2) d_G(x, y')}`. -/
theorem holder_connected_cut_cube (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {C θ : ℝ}, 0 ≤ C → 0 < θ → θ < 1 → ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ}
      (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s], FoldSetting G q s c → ∀ {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ {x x' : Torus d (N₀ * L ^ k)},
      x ∈ cubeOf N₀ L k q s c → x' ∈ cubeOf N₀ L k q s c →
      G.layerIndex x ≤ G.layerIndex x' + 1 → G.pathDist x x' ≤ ENNReal.ofReal C →
      ∀ {z : Fin d → ℤ},
      (∀ i, z i = ((x' i - (c i : ZMod (N₀ * L ^ k))).val : ℤ) -
        ((x i - (c i : ZMod (N₀ * L ^ k))).val : ℤ)) → 1 ≤ ‖z‖ →
      ∀ (ν' : Fin d), x + Pi.single ν' 1 ∈ cubeOf N₀ L k q s c →
      x' + Pi.single ν' 1 ∈ cubeOf N₀ L k q s c →
      (G.spacing x) ^ 2 *
          ‖(cubeSol G a ν (cubeOf N₀ L k q s c) α f (x' + Pi.single ν' 1) -
              cubeSol G a ν (cubeOf N₀ L k q s c) α f x') -
            (cubeSol G a ν (cubeOf N₀ L k q s c) α f (x + Pi.single ν' 1) -
              cubeSol G a ν (cubeOf N₀ L k q s c) α f x)‖ ≤
        (B * (1 + Real.exp (agmonRate d / 2 * C)) / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
          (decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf)) := by
  obtain ⟨B, hB, hH⟩ := holder_pair_cut_cube (d := d) (L := L) hd hL
  refine ⟨B, hB, ?_⟩
  intro C θ hC hθ0 hθ1 k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f
    hsupp Mf hMf0 hMf x x' hx hx' hlay hconn z hz hz1 ν' hxe hxe'
  have key := hH hθ0 hθ1 G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf hx hx' hlay
    hz hz1 ν' hxe hxe'
  set γ := agmonRate d / 2 with hγ
  have hγ0 : 0 ≤ γ := by
    have := agmonRate_pos (show 0 < d by omega)
    positivity
  -- comparison of the two decay factors
  have htri : G.pathDist x y' ≤ ENNReal.ofReal C + G.pathDist x' y' :=
    (G.pathDist_triangle x x' y').trans (add_le_add hconn le_rfl)
  have hdec : decay γ (G.pathDist x' y') ≤ Real.exp (γ * C) * decay γ (G.pathDist x y') :=
    decay_le_exp_mul hγ0 hC htri
  have hF : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have hBθ : 0 ≤ B / θ := by positivity
  have hX : 0 ≤ (G.spacing x) ^ θ * ‖z‖ ^ (1 - θ) := by
    have := spacing_pos G (x := x)
    positivity
  have hsum : decay γ (G.pathDist x y') + decay γ (G.pathDist x' y') ≤
      (1 + Real.exp (γ * C)) * decay γ (G.pathDist x y') := by nlinarith
  refine key.trans ?_
  have e : B * (1 + Real.exp (γ * C)) / θ = B / θ * (1 + Real.exp (γ * C)) := by ring
  rw [e]
  calc _ ≤ (B / θ) * ((G.spacing x) ^ θ * ‖z‖ ^ (1 - θ)) *
        (((1 + Real.exp (γ * C)) * decay γ (G.pathDist x y')) * ((L : ℝ) ^ (2 * j') * Mf)) := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hBθ hX)
        exact mul_le_mul_of_nonneg_right hsum hF
    _ = _ := by ring

/-- **The Laplacian bound at an interior point** (any cut, any regime): if no removed bond ends at
`x` and the solution obeys the value bound `V e^{-(ε₀/2) d(·, y')}` on the block of `x`, then
`ℓ(x)² |Δ^D u(x)| ≤ e^{ε₀ d} (ℓ_{j'}² M_f + 4 V) e^{-(ε₀/2) d(x, y')}`.  (Poisson equation
`laplacian_eq_of_cut` and the row bound (4.4) `laplacian_bound_cut`.) -/
theorem laplacian_cut_bound {cut : Finset (Torus d (N₀ * L ^ k) × Fin d)}
    (hcut : CutAligned G cut) (hd : 0 < d) {a : ℕ → ℝ} {ν : ℝ} (hν0 : 0 ≤ ν)
    (hν1 : ν * ((L : ℝ) ^ k) ^ 2 ≤ 1) (ha : IsAdmissibleWeights k a) (α : G.Ω 1 → ℂ)
    (hα : ∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) {j' : ℕ}
    {y' : Torus d (N₀ * L ^ k)} (hj'1 : 1 ≤ j') (hj'k : j' ≤ k) (hy' : y' ∈ G.layer j')
    (f : G.Ω 1 → ℂ)
    (hsupp : ∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y')
    {Mf : ℝ} (hMf0 : 0 ≤ Mf) (hMf : ∀ z, ‖f z‖ ≤ Mf) {x : Torus d (N₀ * L ^ k)}
    (hxΩ : x ∈ G.Ω 1) (hc : NoCutAt cut x) {V : ℝ} (hV0 : 0 ≤ V)
    (hV : ∀ q', jBlock d L N₀ k (G.layerIndex x) q' = jBlock d L N₀ k (G.layerIndex x) x →
      ‖zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) q'‖ ≤
        V * decay (agmonRate d / 2) (G.pathDist q' y')) :
    (G.spacing x) ^ 2 *
        ‖∑ μ : Fin d, (2 * zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) x -
          zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) (x + Pi.single μ 1) -
          zeroExt (G.Ω 1) ((cutOperator G a ν cut α)⁻¹ *ᵥ f) (x - Pi.single μ 1))‖ ≤
      Real.exp (agmonRate d * d) * ((L : ℝ) ^ (2 * j') * Mf + 4 * V) *
        decay (agmonRate d / 2) (G.pathDist x y') := by
  obtain ⟨hj1, hjk, hxl⟩ := G.layerIndex_spec hxΩ
  set j := G.layerIndex x with hj
  set u := (cutOperator G a ν cut α)⁻¹ *ᵥ f with hu
  have hHu : cutOperator G a ν cut α *ᵥ u = f := cutOperator_mulVec_inv G hcut hd hν0 ha α hα f
  have hγ0 : 0 ≤ agmonRate d / 2 := by
    have := agmonRate_pos hd
    positivity
  have hsp : 0 < G.spacing x := spacing_pos G
  -- decay comparison on the block of x
  have hblock : ∀ q', jBlock d L N₀ k j q' = jBlock d L N₀ k j x →
      decay (agmonRate d / 2) (G.pathDist q' y') ≤
        Real.exp (agmonRate d * d) * decay (agmonRate d / 2) (G.pathDist x y') := by
    intro q' hq'
    have h2 := G.pathDist_block_le hj1 hjk hxl hq'
    have htri : G.pathDist x y' ≤ ENNReal.ofReal (2 * d) + G.pathDist q' y' :=
      (G.pathDist_triangle x q' y').trans (add_le_add h2 le_rfl)
    have := decay_le_exp_mul hγ0 (by positivity) htri
    have e : agmonRate d / 2 * (2 * (d : ℝ)) = agmonRate d * d := by ring
    rwa [e] at this
  set M := V * (Real.exp (agmonRate d * d) * decay (agmonRate d / 2) (G.pathDist x y')) with hM
  have hdx := decay_nonneg (agmonRate d / 2) (G.pathDist x y')
  have hM0 : 0 ≤ M := by positivity
  have hMq : ∀ q', jBlock d L N₀ k j q' = jBlock d L N₀ k j x → ‖zeroExt (G.Ω 1) u q'‖ ≤ M :=
    fun q' hq' => (hV q' hq').trans (by
      rw [hM]
      exact mul_le_mul_of_nonneg_left (hblock q' hq') hV0)
  have hlap := laplacian_bound_cut G hν0 hν1 ha hα hHu hxΩ hc hM0 hMq
  -- the source term
  have hfx : (G.spacing x) ^ 2 * ‖zeroExt (G.Ω 1) f x‖ ≤
      Real.exp (agmonRate d * d) * ((L : ℝ) ^ (2 * j') * Mf) *
        decay (agmonRate d / 2) (G.pathDist x y') := by
    by_cases hf0 : zeroExt (G.Ω 1) f x = 0
    · rw [hf0]; simp only [norm_zero, mul_zero]
      positivity
    · have hzf : zeroExt (G.Ω 1) f x = f ⟨x, hxΩ⟩ := zeroExt_mem (G.Ω 1) f ⟨x, hxΩ⟩
      have hfx' : f ⟨x, hxΩ⟩ ≠ 0 := by rwa [hzf] at hf0
      have hb := hsupp ⟨x, hxΩ⟩ hfx'
      have hxl' : x ∈ G.layer j' := (G.mem_layer_iff hj'1 hj'k hb).2 hy'
      have hjj : j = j' := by
        rw [hj]; exact G.layerIndex_eq hj'1 hj'k hxl'
      have h2 := G.pathDist_block_le hj'1 hj'k hy' hb
      have hdist : decay (agmonRate d / 2) (G.pathDist y' x) ≥
          Real.exp (-(agmonRate d / 2 * (2 * d))) := decay_ofReal_ge hγ0 (by positivity) h2
      rw [G.pathDist_comm] at hdist
      have hspx : G.spacing x = (L : ℝ) ^ j' := G.spacing_eq hj'1 hj'k hxl'
      have hfn : ‖zeroExt (G.Ω 1) f x‖ ≤ Mf := by
        have : zeroExt (G.Ω 1) f x = f ⟨x, hxΩ⟩ := by simp [zeroExt, hxΩ]
        rw [this]; exact hMf _
      have hee : Real.exp (agmonRate d * d) * Real.exp (-(agmonRate d / 2 * (2 * d))) = 1 := by
        rw [← Real.exp_add]; ring_nf; simp
      have hLp : 0 ≤ (L : ℝ) ^ (2 * j') := by positivity
      calc (G.spacing x) ^ 2 * ‖zeroExt (G.Ω 1) f x‖ ≤ (L : ℝ) ^ (2 * j') * Mf := by
            rw [hspx, ← pow_mul, mul_comm j' 2]
            exact mul_le_mul_of_nonneg_left hfn hLp
        _ = Real.exp (agmonRate d * d) * Real.exp (-(agmonRate d / 2 * (2 * d))) *
              ((L : ℝ) ^ (2 * j') * Mf) := by rw [hee, one_mul]
        _ ≤ _ := by
            have := mul_le_mul_of_nonneg_left hdist (Real.exp_pos (agmonRate d * d)).le
            have hF : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
            nlinarith
  have hinv : (G.spacing x) ^ 2 * (3 + 1) * ((G.spacing x ^ 2)⁻¹ * M) = 4 * M := by
    field_simp; ring
  calc (G.spacing x) ^ 2 * ‖_‖ ≤ (G.spacing x) ^ 2 *
        (‖zeroExt (G.Ω 1) f x‖ + (3 + 1) * ((G.spacing x ^ 2)⁻¹) * M) :=
        mul_le_mul_of_nonneg_left hlap (by positivity)
    _ = (G.spacing x) ^ 2 * ‖zeroExt (G.Ω 1) f x‖ + 4 * M := by
        rw [mul_add, ← hinv]; ring
    _ ≤ _ := by
        rw [hM]
        nlinarith [hfx, hdx, Real.exp_pos (agmonRate d * d)]

theorem layerIndex_le_of_mem_cubeOf (h : FoldSetting G q s c) {x : Torus d (N₀ * L ^ k)}
    (hx : x ∈ cubeOf N₀ L k q s c) : G.layerIndex x ≤ q := by
  have := layerIndex_le h (unfoldPt N₀ L k q s c x)
  rwa [foldTo_unfoldPt h hx] at this

/-- **NC3, value bound** at every point of the cube. -/
theorem value_cut_cube (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s], FoldSetting G q s c → ∀ {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ {x : Torus d (N₀ * L ^ k)},
      x ∈ cubeOf N₀ L k q s c →
      ‖cubeSol G a ν (cubeOf N₀ L k q s c) α f x‖ ≤
        K * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  obtain ⟨K, hK, hU⟩ := refl_U_le (d := d) (L := L) hd hL
  refine ⟨K, hK, ?_⟩
  intro k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f hsupp Mf hMf0
    hMf x hx
  have hd0 : 0 < d := by omega
  have key := hU G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf
    (unfoldPt N₀ L k q s c x)
  have hF := foldTo_unfoldPt h hx
  have hsp := (spacing_pos (reflectedGS G h) (x := unfoldPt N₀ L k q s c x)).le
  have hnn : 0 ≤ (reflectedGS G h).spacing (unfoldPt N₀ L k q s c x) *
      ∑ μ : Fin d, ‖reflSol h a ν α (reflU h f) (unfoldPt N₀ L k q s c x + Pi.single μ 1) -
        reflSol h a ν α (reflU h f) (unfoldPt N₀ L k q s c x)‖ :=
    mul_nonneg hsp (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have key2 := (le_add_of_nonneg_right hnn).trans key
  simp only [reflSol_reflU h hd0 hν0 ha α hα f, hF] at key2
  exact key2

/-- **NC3, Laplacian bound** at a point whose neighbours lie in the cube:
`ℓ(x)² |Δ^D u(x)| ≤ K e^{-(ε₀/2) d_G(x, y')} ℓ_{j'}² M_f`. -/
theorem laplacian_cut_cube (hd : 3 ≤ d) (hL : 3 ≤ L) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {k N₀ : ℕ} [NeZero N₀] {ϱ : ℝ} (G : GeneratingSet d L N₀ k ϱ)
      {q s : ℕ} {c : Fin d → ℕ} [NeZero s], FoldSetting G q s c → ∀ {a : ℕ → ℝ} {ν : ℝ},
      0 ≤ ν → ν * ((L : ℝ) ^ k) ^ 2 ≤ 1 → IsAdmissibleWeights k a →
      ∀ (α : G.Ω 1 → ℂ), (∀ x, ‖α x‖ ≤ coerciveConst d / (2 * (G.spacing x) ^ 2)) →
      1 ≤ ϱ → (L : ℝ) ^ d ≤ Real.exp (agmonRate d / 2 * (ϱ - 1)) →
      ∀ {j' : ℕ} {y' : Torus d (N₀ * L ^ k)}, 1 ≤ j' → j' ≤ k → y' ∈ G.layer j' →
      y' ∈ cubeOf N₀ L k q s c → ∀ (f : G.Ω 1 → ℂ),
      (∀ z : G.Ω 1, f z ≠ 0 → jBlock d L N₀ k j' z = jBlock d L N₀ k j' y') →
      ∀ {Mf : ℝ}, 0 ≤ Mf → (∀ z, ‖f z‖ ≤ Mf) → ∀ {x : Torus d (N₀ * L ^ k)},
      x ∈ cubeOf N₀ L k q s c →
      (∀ μ : Fin d, x + Pi.single μ 1 ∈ cubeOf N₀ L k q s c ∧
        x - Pi.single μ 1 ∈ cubeOf N₀ L k q s c) →
      (G.spacing x) ^ 2 *
          ‖∑ μ : Fin d, (2 * cubeSol G a ν (cubeOf N₀ L k q s c) α f x -
            cubeSol G a ν (cubeOf N₀ L k q s c) α f (x + Pi.single μ 1) -
            cubeSol G a ν (cubeOf N₀ L k q s c) α f (x - Pi.single μ 1))‖ ≤
        K * decay (agmonRate d / 2) (G.pathDist x y') * ((L : ℝ) ^ (2 * j') * Mf) := by
  obtain ⟨K, hK, hV⟩ := value_cut_cube (d := d) (L := L) hd hL
  refine ⟨Real.exp (agmonRate d * d) * (1 + 4 * K), by positivity, ?_⟩
  intro k N₀ _ ϱ G q s c _ h a ν hν0 hν1 ha α hα hϱ hsep j' y' hj'1 hj'k hy' hyc f hsupp Mf hMf0
    hMf x hx hxe
  have hd0 : 0 < d := by omega
  have hxΩ : x ∈ G.Ω 1 := h.mem_Ω x hx
  have hnc : NoCutAt (cubeCut G (cubeOf N₀ L k q s c)) x := fun μ =>
    ⟨fun hc => (cut_up_iff h hx μ).1 hc (hxe μ).1,
     fun hc => (cut_dn_iff h hx μ).1 hc (hxe μ).2⟩
  have hjq := layerIndex_le_of_mem_cubeOf h hx
  have hF0 : 0 ≤ (L : ℝ) ^ (2 * j') * Mf := by positivity
  have hlap := laplacian_cut_bound (cubeCut_aligned' h) hd0 hν0 hν1 ha α hα hj'1 hj'k hy' f hsupp
    hMf0 hMf hxΩ hnc (V := K * ((L : ℝ) ^ (2 * j') * Mf)) (by positivity) (by
      intro q' hq'
      have hq'c : q' ∈ cubeOf N₀ L k q s c := mem_cubeOf_of_jBlock_eq h hjq hx hq'
      have := hV G h hν0 hν1 ha α hα hϱ hsep hj'1 hj'k hy' hyc f hsupp hMf0 hMf hq'c
      exact (by simpa [cubeSol] using this.trans (le_of_eq (by ring))))
  refine hlap.trans (le_of_eq ?_)
  ring

end Balaban.Reflection
