/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Localization.ReflectionSource
public import Balaban.Localization.CubeRegimes
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

end Balaban.Reflection
