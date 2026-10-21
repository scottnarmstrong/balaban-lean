/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfFluct
public import Balaban.Polymer.BlockTorus

/-!
# The local form of the fluctuation integrand on the box

A6-3, the interface between the localization of the last integral and its gas layer (reading B-1 of
`notes/phase1/PLAN-B.md`; P4 (6.6), P7 (4.9)). On one torus of the family, with the context `C` of a
member of the class at the stopping scale, the Gaussian variable `w` of the box integral
(`ctxBoxIntegral`) is a real field on the `k`-blocks `Λ` and the spin components, `w : Λ × Fin N → ℝ`,
and the box is `|w_p| ≤ p₁` (`gaussBox`). `BoxLocalForm C vc hv p₁ G₀ a ε W` says that on the box the
fluctuation integrand, i.e. the Gaussian integrand `sfGaussIntegrand` (form `K = β_k D`, centre `h`)
divided by `exp X₀`, `X₀ = (𝒜_k + ℱ_k)(T; h, h, g)` (`constExponent`), is `exp(E₀ + Σ_Y W_Y(w, g))`
for a family `W` of local terms indexed by the sets `Y` of `k`-blocks:

* (W1) `W_Y(w, g)` depends on `w` only through `w|_{Y × Fin N}`;
* (W2) it depends on the source `g` only through its values at the fine sites of the blocks of `Y`;
* (W3) `W_Y = 0` unless `Y` is nonempty and connected in the nearest-neighbour graph of the blocks;
* (W4) for `w` in the box, `g ↦ W_Y(w, g)` is analytic on the `ℓ¹` ball `‖g‖₁ < G₀`, `G₀ > 1` (room for
  the increment bound on the unit ball, `Analysis.norm_sub_le_of_l1Ball`), and `(g, w) ↦ W_Y(w, g)` is
  continuous on (ball) × (box) (for the analyticity in `g` of the integrals over the box,
  `Analysis.analyticAt_integral_of_continuousOn`);
* (W5) on the box and the ball, `Σ_{Y ∋ x} ‖W_Y(w, g)‖ e^{a|Y|} ≤ ε` for every block `x`;
* (W6) on the box and the unit ball, `sfGaussIntegrand(w) · exp(-X₀(g)) = exp(E₀ + Σ_Y W_Y(w, g))`
  for a constant `E₀` of the torus, independent of `w` and `g`.

In the source this is the result of the localization expansions of the fluctuation integral
(P4 (6.6); P5 §3, P6 §2 at the last step): the cubic remainder of the main action, the change of the
inherited terms and of the source term against their values at the constant configuration, all
localized in polymers of blocks with exponential decay; on the box `χ_k = 1`.

`ctxFluctBoxIntegral_eq_of_boxLocalForm` is the first consequence: the box average of the fluctuation
integrand is `Z_K e^{E₀} ∫_{box} exp(Σ_Y W_Y) dγ`. Rule 10: `boxLocalForm_zero` (the zero family, for a
negative cutoff).
-/

@[expose] public section

open MeasureTheory Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7
  Balaban.LargeField.Def7v2 Balaban.Green

namespace Balaban.RootFSpine

/-- The open `ℓ¹` ball `‖g‖₁ < G` of sources. -/
def l1BallR (ι : Type*) [Fintype ι] (G : ℝ) : Set (ι → ℂ) := {g | ∑ i, ‖g i‖ < G}

theorem l1BallR_one (ι : Type*) [Fintype ι] : l1BallR ι 1 = l1Ball ι := rfl

theorem isOpen_l1BallR (ι : Type*) [Fintype ι] (G : ℝ) : IsOpen (l1BallR ι G) :=
  isOpen_lt (continuous_finsetSum _ fun i _ => (continuous_apply i).norm) continuous_const

theorem l1Ball_subset_l1BallR (ι : Type*) [Fintype ι] {G : ℝ} (hG : 1 ≤ G) :
    l1Ball ι ⊆ l1BallR ι G := fun _ hg => lt_of_lt_of_le hg hG

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ}

/-- The `k`-block of a fine site of the torus (`jBlock`). -/
def fineBlock (k : ℕ) (x : Torus S.d (M * n K * S.L ^ K)) : BlockAt S n M K k :=
  jBlock S.d S.L (M * n K) K k x

/-- **The local form of the fluctuation integrand on the box** (A6-3; P4 (6.6), P7 (4.9)): the
clauses (W1)–(W6) of the module docstring for the family `W` of local terms on the sets `Y` of
`k`-blocks, the cutoff `p₁`, the radius `G₀` of the source ball, the decay rate `a` and the
smallness `ε`. -/
structure BoxLocalForm (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (p1 G₀ a ε : ℝ)
    (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) →
      (GIdx S n M K N → ℂ) → ℂ) : Prop where
  /-- the source ball is larger than the unit ball -/
  one_lt_G₀ : 1 < G₀
  /-- (W1) `W_Y` reads the Gaussian variable on `Y × Fin N` only -/
  local_w : ∀ Y w w' g, (∀ x ∈ Y, ∀ i, w (x, i) = w' (x, i)) → W Y w g = W Y w' g
  /-- (W2) `W_Y` reads the source at the fine sites of the blocks of `Y` only -/
  local_g : ∀ Y w g g', (∀ x, fineBlock k x ∈ Y → ∀ i, g (x, i) = g' (x, i)) → W Y w g = W Y w g'
  /-- (W3) `W_Y = 0` unless `Y` is a nonempty connected set of blocks -/
  support : ∀ Y, ¬ Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) Y →
    ∀ w g, W Y w g = 0
  /-- (W4) analyticity in the source on the ball of radius `G₀`, on the box -/
  analytic : ∀ Y, ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1,
    AnalyticOnNhd ℂ (W Y w) (l1BallR (GIdx S n M K N) G₀)
  /-- (W4) joint continuity on (ball) × (box) -/
  cont : ∀ Y, ContinuousOn (fun q : (GIdx S n M K N → ℂ) × (BlockAt S n M K k × Fin N → ℝ) =>
    W Y q.2 q.1) (l1BallR (GIdx S n M K N) G₀ ×ˢ gaussBox (BlockAt S n M K k × Fin N) p1)
  /-- (W5) the summed bound with exponential decay in the number of blocks -/
  bound : ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1, ∀ g ∈ l1BallR (GIdx S n M K N) G₀,
    ∀ x : BlockAt S n M K k,
      ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
        ‖W Y w g‖ * Real.exp (a * (Y.card : ℝ)) ≤ ε
  /-- (W6) the fluctuation integrand on the box is `exp(E₀ + Σ_Y W_Y)` -/
  identity : ∃ E₀ : ℂ, ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1,
    ∀ g ∈ l1Ball (GIdx S n M K N),
      sfGaussIntegrand C vc Set.univ hv g (sfFinalK C hv) (fun _ => hv) w *
          Complex.exp (-constExponent C vc hv g) =
        Complex.exp (E₀ + ∑ Y, W Y w g)

/-- **The box average of the fluctuation integrand in the local form**: under `BoxLocalForm`, for
every source of the unit ball, `ctxFluctBoxIntegral = Z_K e^{E₀} ∫_{box} exp(Σ_Y W_Y(w, g)) dγ(w)`. -/
theorem ctxFluctBoxIntegral_eq_of_boxLocalForm {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d}
    {hv : EuclideanSpace ℝ (Fin N)} {p1 G₀ a ε : ℝ}
    {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → (GIdx S n M K N → ℂ) → ℂ}
    (hW : BoxLocalForm C vc hv p1 G₀ a ε W) :
    ∃ E₀ : ℂ, ∀ g ∈ l1Ball (GIdx S n M K N),
      ctxFluctBoxIntegral C vc hv p1 g =
        (pdGaussNorm (BlockAt S n M K k × Fin N) ℝ (sfFinalK C hv) : ℂ) * Complex.exp E₀ *
          ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1, Complex.exp (∑ Y, W Y w g)
            ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
  obtain ⟨E₀, hE⟩ := hW.identity
  refine ⟨E₀, fun g hg => ?_⟩
  have hbox : MeasurableSet (gaussBox (BlockAt S n M K k × Fin N) p1) := by
    have : gaussBox (BlockAt S n M K k × Fin N) p1 =
        ⋂ p, {w : BlockAt S n M K k × Fin N → ℝ | |w p| ≤ p1} := by
      ext w; simp [gaussBox]
    rw [this]
    exact MeasurableSet.iInter fun p =>
      measurableSet_le ((measurable_pi_apply p).abs) measurable_const
  have e : ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
        sfGaussIntegrand C vc Set.univ hv g (sfFinalK C hv) (fun _ => hv) w *
          Complex.exp (-constExponent C vc hv g) ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) =
      Complex.exp E₀ * ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
        Complex.exp (∑ Y, W Y w g) ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
    rw [← integral_const_mul]
    exact setIntegral_congr_fun hbox fun w hw => by rw [hE w hw g hg, Complex.exp_add]
  unfold ctxFluctBoxIntegral
  rw [e]
  ring

/-- **Rule 10: `BoxLocalForm` is inhabited** — the zero family, for a negative cutoff (the box is
empty, `N ≥ 1`), every radius `G₀ > 1` and every rate `a` and bound `ε`. -/
theorem boxLocalForm_zero (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) [NeZero N] {p1 : ℝ} (hp1 : p1 < 0) {G₀ : ℝ} (hG₀ : 1 < G₀)
    (a ε : ℝ) : BoxLocalForm C vc hv p1 G₀ a ε (fun _ _ _ => 0) := by
  have hempty : ∀ w, w ∉ gaussBox (BlockAt S n M K k × Fin N) p1 := fun w hw => by
    have := hw (0, 0)
    linarith [abs_nonneg (w (0, 0))]
  refine ⟨hG₀, fun _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl,
    fun _ _ _ => analyticOnNhd_const, fun _ => continuousOn_const, fun w hw => absurd hw (hempty w),
    ⟨0, fun w hw => absurd hw (hempty w)⟩⟩

end Balaban.RootFSpine
