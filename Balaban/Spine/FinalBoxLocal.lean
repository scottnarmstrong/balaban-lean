/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalSfFluct
public import Balaban.Polymer.BlockTorus
public import Balaban.Green.FinalMacroCover

/-!
# The local form of the fluctuation integrand on the box

A6-3, the interface between the localization of the last integral and its gas layer (readings B-1
and B-1′ of `notes/phase1/PLAN-B.md`; P4 (6.6), P7 (4.9), P5 (2.39)). On one torus of the family,
with the context `C` of a member of the class at the stopping scale, the field of the box integral
is `ψ_k = h + A w` for a whitening `A` (an invertible real linear map of the `k`-blocks `Λ` and the
spin components; in the source `A = β_k^{-1/2} L` with `L` the localized square root of the
covariance, P5 (2.39), P7 §4), the Gaussian variable `w : Λ × Fin N → ℝ` is standard, and the box is
`|w_p| ≤ p₁` (`gaussBox`). `BoxLocalForm C vc hv A p₁ G₀ R_t M_c a ε ε_U W U` says that on the box
the fluctuation integrand at the whitening, i.e. `sfGaussIntegrandL` (the small-field factor at
`h + A w` with the Gaussian part of `K = β_k D` divided out) times the mismatch factor
`exp(-½⟨w, (Aᵀ K A - 1) w⟩)` (`mismatchFactor`) divided by `exp X₀`, `X₀ = (𝒜_k + ℱ_k + ℛ^{(k)})(T; h, h, g)`
the whole exponent of the small-field factor at the constant configuration (`constExponentR`), is
`exp(E₀ + Σ_Y W_Y(w, g) + Σ_Y U_Y(w))` for a family `W` of dilated local terms on complex fields
`ζ : Λ × Fin N → ℂ` (the real field `w` enters as `ζ = w`) and a family `U` of undilated local terms
on real fields, indexed by the sets `Y` of `k`-blocks:

* (W1) `W_Y(ζ, g)` depends on `ζ` only through `ζ|_{Y × Fin N}`;
* (W2) it depends on the source `g` only through its values at the fine sites of the blocks of `Y`;
* (W3) `W_Y = 0` unless `Y` is nonempty and connected in the nearest-neighbour graph of the blocks;
* (W0) the terms are normalized at the constant configuration: `W_Y(0, g) = 0`;
* (W4) for `w` in the box, the dilated terms `(t, g) ↦ W_Y(t w, g)` are analytic on the polydisc
  `|t| < R_t`, `‖g‖₁ < G₀` (`R_t ≥ 2`, `G₀ ≥ 1`: room for the Cauchy estimate in `t`), and jointly
  continuous with `w` on (polydisc) × (box);
* (W5) for `w` in the box, `|t| < R_t` and `‖g‖₁ < G₀`,
  `Σ_{Y ∋ x} ‖W_Y(t w, g)‖ e^{a·#_c(Y)} ≤ ε` for every block `x`, where `#_c(Y)` (`cellCount`) is the
  number of macro cells of side `M_c` (`Green.macZ`, the cells of the cut family of the
  localization) meeting `Y`;
* (U) the undilated part: `U_Y(w)` depends on `w|_{Y × Fin N}` only, vanishes unless `Y` is
  connected, is even (`U_Y(-w) = U_Y(w)`), continuous on the box, independent of the source, and
  `Σ_{Y ∋ x} ‖U_Y(w)‖ e^{a·#_c(Y)} ≤ ε_U` on the box (in the source: the pair terms
  `-½ Q_{xy} w_x w_y` of the mismatch `Q = Aᵀ K A - 1`, small by the row bounds of the cut family);
* (A) the whitening `A` is invertible;
* (W6) on the box and the unit ball,
  `sfGaussIntegrandL(w) · mismatch(w) · exp(-X₀(g)) = exp(E₀ + Σ_Y W_Y(w, g) + Σ_Y U_Y(w))` for a
  constant `E₀` of the torus, independent of `w` and `g`.

The dilation `t` is the device that makes the scale-`(k+1)` increments second order: the box measure
is symmetric under `w ↦ -w`, so the gas of the terms `W_Y(t w) + U_Y(w)` is even in `t` (the part
`U` is even and is not dilated) and, by (W0), at `t = 0` it is the gas of `U` only, independent of
the source; the Cauchy estimate in `t` of the increments in `g` gains `R_t^{-2}`. The remainder
`ℛ^{(k)}(T; h, h, g)` at the constant configuration is in `X₀`; it is regrouped into scale-`(k+1)`
activities with the bounds of the class (`RTermsH4`).

In the source this is the result of the localization expansions of the fluctuation integral
(P4 (6.6); P5 §3, P6 §2 at the last step): the cubic remainder of the main action, the change of the
inherited terms and of the source term against their values at the constant configuration, all
localized in polymers of blocks with exponential decay; on the box `χ_k = 1`.

`ctxFluctBoxIntegralL_eq_of_boxLocalForm` is the first consequence: the box average of the
fluctuation integrand is `|det A| (2π)^{n/2} e^{E₀ + ℛ^{(k)}(T; h, h, g)} ∫_{box} exp(Σ_Y W_Y + Σ_Y U_Y)
dγ`. Rule 10: `boxLocalForm_zero` (the zero families, for a negative cutoff).
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

/-- **The whole exponent of the small-field factor at the constant configuration**:
`X₀(g) = (𝒜_k + ℱ_k + ℛ^{(k)})(T; ψ_k ≡ h, h, g)`. -/
noncomputable def constExponentR (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (g : GIdx S n M K N → ℂ) : ℂ :=
  constExponent C vc hv g + C.Rres Set.univ (fun _ => hv) hv g

/-- **The number of macro cells meeting a set of `k`-blocks**: the cells of side `M_c` of the
`k`-block torus (`Green.macZ`; intervals of `M_c` to `2M_c - 1` blocks in each coordinate, the cells
of the cut family `boxCut` of the localization). -/
def cellCount (k Mc : ℕ) (Y : Finset (BlockAt S n M K k)) : ℕ :=
  (Y.image (Green.macZ (d := S.d) (m := M * n K * S.L ^ (K - k)) Mc)).card

/-- **The local form of the fluctuation integrand on the box at a whitening** (A6-3; P4 (6.6),
P7 (4.9), P5 (2.39)): the clauses (W0)–(W6) and (U) of the module docstring for the family `W` of
dilated local terms on complex fields and the family `U` of undilated even local terms on real
fields, on the sets `Y` of `k`-blocks, at the whitening `A`, with the cutoff `p₁`, the radius `G₀`
of the source ball, the radius `R_t` of the dilations, the side `M_c` of the macro cells, the decay
rate `a` per cell and the smallness `ε` of `W` and `ε_U` of `U`. -/
structure BoxLocalForm (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N))
    (A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ)
    (p1 G₀ Rt : ℝ) (Mc : ℕ) (a ε εU : ℝ)
    (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ)
    (U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ) : Prop where
  /-- the whitening is invertible -/
  det_ne_zero : A.det ≠ 0
  /-- the source ball contains the unit ball -/
  one_le_G₀ : 1 ≤ G₀
  /-- the dilations reach `|t| = 2` -/
  two_le_Rt : 2 ≤ Rt
  /-- (W1) `W_Y` reads the field on `Y × Fin N` only -/
  local_w : ∀ Y ζ ζ' g, (∀ x ∈ Y, ∀ i, ζ (x, i) = ζ' (x, i)) → W Y ζ g = W Y ζ' g
  /-- (W2) `W_Y` reads the source at the fine sites of the blocks of `Y` only -/
  local_g : ∀ Y ζ g g', (∀ x, fineBlock k x ∈ Y → ∀ i, g (x, i) = g' (x, i)) → W Y ζ g = W Y ζ g'
  /-- (W0) the terms vanish at the constant configuration -/
  normalized : ∀ Y g, W Y 0 g = 0
  /-- (W3) `W_Y = 0` unless `Y` is a nonempty connected set of blocks -/
  support : ∀ Y, ¬ Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) Y →
    ∀ ζ g, W Y ζ g = 0
  /-- (W4) joint analyticity of the dilated terms in the dilation and the source, on the box -/
  analytic : ∀ Y, ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1,
    AnalyticOnNhd ℂ (fun q : ℂ × (GIdx S n M K N → ℂ) => W Y (fun p => q.1 * (w p : ℂ)) q.2)
      (Metric.ball (0 : ℂ) Rt ×ˢ l1BallR (GIdx S n M K N) G₀)
  /-- (W4) joint continuity of the dilated terms -/
  cont : ∀ Y, ContinuousOn
    (fun q : (ℂ × (GIdx S n M K N → ℂ)) × (BlockAt S n M K k × Fin N → ℝ) =>
      W Y (fun p => q.1.1 * (q.2 p : ℂ)) q.1.2)
    ((Metric.ball (0 : ℂ) Rt ×ˢ l1BallR (GIdx S n M K N) G₀) ×ˢ
      gaussBox (BlockAt S n M K k × Fin N) p1)
  /-- (W5) the summed bound of the dilated terms, with decay in the number of macro cells -/
  bound : ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1, ∀ t : ℂ, ‖t‖ < Rt →
    ∀ g ∈ l1BallR (GIdx S n M K N) G₀, ∀ x : BlockAt S n M K k,
      ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
        ‖W Y (fun p => t * (w p : ℂ)) g‖ * Real.exp (a * (cellCount k Mc Y : ℝ)) ≤ ε
  /-- (U) the undilated part reads the field on `Y × Fin N` only -/
  local_u : ∀ Y w w', (∀ x ∈ Y, ∀ i, w (x, i) = w' (x, i)) → U Y w = U Y w'
  /-- (U) the undilated part vanishes off the nonempty connected sets of blocks -/
  support_u : ∀ Y, ¬ Polymer.IsAnimal (Polymer.blockGraph S.d (M * n K * S.L ^ (K - k))) Y →
    ∀ w, U Y w = 0
  /-- (U) the undilated part is even -/
  even_u : ∀ Y w, U Y (-w) = U Y w
  /-- (U) the undilated part is continuous on the box -/
  cont_u : ∀ Y, ContinuousOn (U Y) (gaussBox (BlockAt S n M K k × Fin N) p1)
  /-- (U) the summed bound of the undilated part, with decay in the number of macro cells -/
  bound_u : ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1, ∀ x : BlockAt S n M K k,
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
      ‖U Y w‖ * Real.exp (a * (cellCount k Mc Y : ℝ)) ≤ εU
  /-- (W6) the fluctuation integrand at the whitening on the box is
  `exp(E₀ + Σ_Y W_Y + Σ_Y U_Y)` -/
  identity : ∃ E₀ : ℂ, ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1,
    ∀ g ∈ l1Ball (GIdx S n M K N),
      sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
          (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-constExponentR C vc hv g) =
        Complex.exp (E₀ + ∑ Y, W Y (fun p => (w p : ℂ)) g + ∑ Y, U Y w)

/-- **The box average of the fluctuation integrand in the local form**: under `BoxLocalForm`, for
every source of the unit ball, `ctxFluctBoxIntegralL = |det A| (2π)^{n/2} e^{E₀ + ℛ^{(k)}(T; h, h, g)}
∫_{box} exp(Σ_Y W_Y(w, g) + Σ_Y U_Y(w)) dγ(w)`. -/
theorem ctxFluctBoxIntegralL_eq_of_boxLocalForm {C : SFCtx S n R M K N k m₁ ϱ}
    {vc : CorrCoef S.d} {hv : EuclideanSpace ℝ (Fin N)}
    {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} {p1 G₀ Rt : ℝ}
    {Mc : ℕ} {a ε εU : ℝ}
    {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
    {U : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℝ) → ℂ}
    (hW : BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU W U) :
    ∃ E₀ : ℂ, ∀ g ∈ l1Ball (GIdx S n M K N),
      ctxFluctBoxIntegralL C vc hv A p1 g =
        (whitenNorm A : ℂ) * Complex.exp (E₀ + C.Rres Set.univ (fun _ => hv) hv g) *
          ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
            Complex.exp (∑ Y, W Y (fun p => (w p : ℂ)) g + ∑ Y, U Y w)
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
        sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
          (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-constExponent C vc hv g)
          ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) =
      Complex.exp (E₀ + C.Rres Set.univ (fun _ => hv) hv g) *
        ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
          Complex.exp (∑ Y, W Y (fun p => (w p : ℂ)) g + ∑ Y, U Y w)
          ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hbox fun w hw => ?_
    have h1 := hE w hw g hg
    have h2 : sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
          (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-constExponent C vc hv g) =
        sfGaussIntegrandL C vc Set.univ hv g (sfFinalK C hv) A (fun _ => hv) w *
          (mismatchFactor (sfFinalK C hv) A w : ℂ) * Complex.exp (-constExponentR C vc hv g) *
          Complex.exp (C.Rres Set.univ (fun _ => hv) hv g) := by
      rw [mul_assoc _ (Complex.exp _), ← Complex.exp_add]
      congr 2
      unfold constExponentR
      ring
    rw [h2, h1, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  unfold ctxFluctBoxIntegralL
  rw [e]
  ring

/-- **Rule 10: `BoxLocalForm` is inhabited** — the zero families, for a negative cutoff (the box is
empty, `N ≥ 1`), every invertible whitening `A`, radius `G₀ ≥ 1`, `R_t ≥ 2`, cell side `M_c`, rate
`a` and bounds `ε`, `ε_U`. -/
theorem boxLocalForm_zero (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) [NeZero N]
    {A : Matrix (BlockAt S n M K k × Fin N) (BlockAt S n M K k × Fin N) ℝ} (hA : A.det ≠ 0)
    {p1 : ℝ} (hp1 : p1 < 0) {G₀ Rt : ℝ} (hG₀ : 1 ≤ G₀) (hRt : 2 ≤ Rt) (Mc : ℕ) (a ε εU : ℝ) :
    BoxLocalForm C vc hv A p1 G₀ Rt Mc a ε εU (fun _ _ _ => 0) (fun _ _ => 0) := by
  have hempty : ∀ w, w ∉ gaussBox (BlockAt S n M K k × Fin N) p1 := fun w hw => by
    have := hw (0, 0)
    linarith [abs_nonneg (w (0, 0))]
  exact
    { det_ne_zero := hA
      one_le_G₀ := hG₀
      two_le_Rt := hRt
      normalized := fun _ _ => rfl
      local_w := fun _ _ _ _ _ => rfl
      local_g := fun _ _ _ _ _ => rfl
      support := fun _ _ _ _ => rfl
      analytic := fun _ _ _ => analyticOnNhd_const
      cont := fun _ => continuousOn_const
      bound := fun w hw => absurd hw (hempty w)
      local_u := fun _ _ _ _ => rfl
      support_u := fun _ _ _ => rfl
      even_u := fun _ _ => rfl
      cont_u := fun _ => continuousOn_const
      bound_u := fun w hw => absurd hw (hempty w)
      identity := ⟨0, fun w hw => absurd hw (hempty w)⟩ }

end Balaban.RootFSpine
