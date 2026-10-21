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

A6-3, the interface between the localization of the last integral and its gas layer (reading B-1 of
`notes/phase1/PLAN-B.md`; P4 (6.6), P7 (4.9)). On one torus of the family, with the context `C` of a
member of the class at the stopping scale, the Gaussian variable `w` of the box integral
(`ctxBoxIntegral`) is a real field on the `k`-blocks `Λ` and the spin components, `w : Λ × Fin N → ℝ`,
and the box is `|w_p| ≤ p₁` (`gaussBox`). `BoxLocalForm C vc hv p₁ G₀ R_t M_c a ε W` says that on the
box the fluctuation integrand, i.e. the Gaussian integrand `sfGaussIntegrand` (form `K = β_k D`,
centre `h`) divided by `exp X₀`, `X₀ = (𝒜_k + ℱ_k + ℛ^{(k)})(T; h, h, g)` the whole exponent of the
small-field factor at the constant configuration (`constExponentR`), is
`exp(E₀ + Σ_Y W_Y(w, g))` for a family `W` of local terms indexed by the sets `Y` of `k`-blocks and
defined on complex fields `ζ : Λ × Fin N → ℂ` (the real field `w` enters as `ζ = w`):

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
* (W6) on the box and the unit ball, `sfGaussIntegrand(w) · exp(-X₀(g)) = exp(E₀ + Σ_Y W_Y(w, g))`
  for a constant `E₀` of the torus, independent of `w` and `g`.

The dilation `t` is the device that makes the scale-`(k+1)` increments second order: the box measure
is symmetric under `w ↦ -w`, so the gas of the terms at the dilation `t` is even in `t` and, by (W0),
vanishes at `t = 0`, and the Cauchy estimate in `t` gains `R_t^{-2}`. The remainder
`ℛ^{(k)}(T; h, h, g)` at the constant configuration is in `X₀`; it is regrouped into scale-`(k+1)`
activities with the bounds of the class (`RTermsH4`).

In the source this is the result of the localization expansions of the fluctuation integral
(P4 (6.6); P5 §3, P6 §2 at the last step): the cubic remainder of the main action, the change of the
inherited terms and of the source term against their values at the constant configuration, all
localized in polymers of blocks with exponential decay; on the box `χ_k = 1`.

`ctxFluctBoxIntegral_eq_of_boxLocalForm` is the first consequence: the box average of the fluctuation
integrand is `Z_K e^{E₀ + ℛ^{(k)}(T; h, h, g)} ∫_{box} exp(Σ_Y W_Y) dγ`. Rule 10: `boxLocalForm_zero` (the zero family, for a
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

/-- **The local form of the fluctuation integrand on the box** (A6-3; P4 (6.6), P7 (4.9)): the
clauses (W1)–(W6) of the module docstring for the family `W` of local terms on the sets `Y` of
`k`-blocks, defined on complex fields, with the cutoff `p₁`, the radius `G₀` of the source ball, the
radius `R_t` of the dilations, the side `M_c` of the macro cells, the decay rate `a` per cell and the
smallness `ε`. -/
structure BoxLocalForm (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) (p1 G₀ Rt : ℝ) (Mc : ℕ) (a ε : ℝ)
    (W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) →
      (GIdx S n M K N → ℂ) → ℂ) : Prop where
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
  /-- (W6) the fluctuation integrand on the box is `exp(E₀ + Σ_Y W_Y)` -/
  identity : ∃ E₀ : ℂ, ∀ w ∈ gaussBox (BlockAt S n M K k × Fin N) p1,
    ∀ g ∈ l1Ball (GIdx S n M K N),
      sfGaussIntegrand C vc Set.univ hv g (sfFinalK C hv) (fun _ => hv) w *
          Complex.exp (-constExponentR C vc hv g) =
        Complex.exp (E₀ + ∑ Y, W Y (fun p => (w p : ℂ)) g)

/-- **The box average of the fluctuation integrand in the local form**: under `BoxLocalForm`, for
every source of the unit ball, `ctxFluctBoxIntegral = Z_K e^{E₀} ∫_{box} exp(Σ_Y W_Y(w, g)) dγ(w)`. -/
theorem ctxFluctBoxIntegral_eq_of_boxLocalForm {C : SFCtx S n R M K N k m₁ ϱ} {vc : CorrCoef S.d}
    {hv : EuclideanSpace ℝ (Fin N)} {p1 G₀ Rt : ℝ} {Mc : ℕ} {a ε : ℝ}
    {W : Finset (BlockAt S n M K k) → (BlockAt S n M K k × Fin N → ℂ) → (GIdx S n M K N → ℂ) → ℂ}
    (hW : BoxLocalForm C vc hv p1 G₀ Rt Mc a ε W) :
    ∃ E₀ : ℂ, ∀ g ∈ l1Ball (GIdx S n M K N),
      ctxFluctBoxIntegral C vc hv p1 g =
        (pdGaussNorm (BlockAt S n M K k × Fin N) ℝ (sfFinalK C hv) : ℂ) *
          Complex.exp (E₀ + C.Rres Set.univ (fun _ => hv) hv g) *
          ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
            Complex.exp (∑ Y, W Y (fun p => (w p : ℂ)) g)
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
      Complex.exp (E₀ + C.Rres Set.univ (fun _ => hv) hv g) *
        ∫ w in gaussBox (BlockAt S n M K k × Fin N) p1,
          Complex.exp (∑ Y, W Y (fun p => (w p : ℂ)) g)
          ∂(pdGaussian (BlockAt S n M K k × Fin N) ℝ) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun hbox fun w hw => ?_
    have h1 := hE w hw g hg
    have h2 : sfGaussIntegrand C vc Set.univ hv g (sfFinalK C hv) (fun _ => hv) w *
          Complex.exp (-constExponent C vc hv g) =
        sfGaussIntegrand C vc Set.univ hv g (sfFinalK C hv) (fun _ => hv) w *
          Complex.exp (-constExponentR C vc hv g) *
          Complex.exp (C.Rres Set.univ (fun _ => hv) hv g) := by
      rw [mul_assoc, ← Complex.exp_add]
      congr 2
      unfold constExponentR
      ring
    rw [h2, h1, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  unfold ctxFluctBoxIntegral
  rw [e]
  ring

/-- **Rule 10: `BoxLocalForm` is inhabited** — the zero family, for a negative cutoff (the box is
empty, `N ≥ 1`), every radius `G₀ ≥ 1`, `R_t ≥ 2`, cell side `M_c`, rate `a` and bound `ε`. -/
theorem boxLocalForm_zero (C : SFCtx S n R M K N k m₁ ϱ) (vc : CorrCoef S.d)
    (hv : EuclideanSpace ℝ (Fin N)) [NeZero N] {p1 : ℝ} (hp1 : p1 < 0) {G₀ Rt : ℝ} (hG₀ : 1 ≤ G₀)
    (hRt : 2 ≤ Rt) (Mc : ℕ) (a ε : ℝ) :
    BoxLocalForm C vc hv p1 G₀ Rt Mc a ε (fun _ _ _ => 0) := by
  have hempty : ∀ w, w ∉ gaussBox (BlockAt S n M K k × Fin N) p1 := fun w hw => by
    have := hw (0, 0)
    linarith [abs_nonneg (w (0, 0))]
  exact
    { one_le_G₀ := hG₀
      two_le_Rt := hRt
      normalized := fun _ _ => rfl
      local_w := fun _ _ _ _ _ => rfl
      local_g := fun _ _ _ _ _ => rfl
      support := fun _ _ _ _ => rfl
      analytic := fun _ _ _ => analyticOnNhd_const
      cont := fun _ => continuousOn_const
      bound := fun w hw => absurd hw (hempty w)
      identity := ⟨0, fun w hw => absurd hw (hempty w)⟩ }

end Balaban.RootFSpine
