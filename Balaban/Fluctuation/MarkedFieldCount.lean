/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedSharpCount
public import Balaban.Fluctuation.MarkedCubicJoint
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The count of the marked terms for an arbitrary unit field (`MarkedFieldCount`)

`MarkedSharpCount.marked_count_scaled` counts the marked terms of the zero class along the marked
tangent `v_t = u ψ' + t M_z ψ'` of the step, `ψ' = shiftUC ψ̂`, while the datum `Θ` ranges over the
chart.  For a family of data the tangent off the fibre `h = h₀` is not the shift of the fixed step,
so the count is re-proved here for an **arbitrary** complex field `y` of the unit lattice in place
of `shiftUC ψ̂`, with the coordinate bound `|y(b)| ≤ Y₀` at every unit point and the radius
condition `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, uniform for the radial marks `|u| < R_σ`.

* `markedBlockTerm_congr_of_local`: two marked terms `P(Θ, a + t c)`, `P(Θ', a' + t' c')` are equal
  when the functional takes the same values along the two discs of directions.  The landed
  `deriv_markedBlockTerm_eq_zero_of_local` is the case `a' = a`, `c' = c`, `t' = 0`, `Θ' = Θ`.
* `liftC_maskUC_congr`, `markedBlockTerm_field_congr`,
  `deriv_markedBlockTerm_eq_zero_of_psiThick_disjoint_field`: the mask-locality lemmas for an
  arbitrary unit field: the marked term of a label `Y` reads the field only through its lift on
  `psiThick Y` and the datum only on `thickSet Y`; if `psiThick Y` misses the block `B(z)`, the
  `t`-derivative at `0` vanishes.
* `norm_deriv_markedBlockTerm_field_le_of_vblock`: the Cauchy bound
  `3 ‖E‖ e^{-2 κ_dec d(Y)} / (r³ t₀)` of one term.
* `MarkedCountClauses`: the four clauses of the conclusion of `marked_count_scaled` for a family
  `a + t c`, a datum `Θ`, a prefactor `F₀` and a rate `a₀` (finite-sum identity; bound
  `F₀ e^{-a₀ d(Y')}`; a non-zero rooted sum has `Y' ∈ 𝒟_K` with the root cube among its cubes; the
  anchored sum).  `markedCountClauses_of_terms`: the clauses from term bounds, the number of blocks
  through a domain and the vanishing of the terms left out.
* `marked_count_field_of_vblock`, `marked_count_field`: **the field-generic count**.
  `marked_count_field` returns one family `Ev` of block terms (the one of
  `vblock_expansion_scaled`, with its four clauses) serving every marked block `z`, every unit
  field and every datum of the chart.
* `exists_radial_margin`, `marked_count_scaled_of_vblock_via_field`,
  `marked_count_scaled_via_field`: the statements of the landed `marked_count_scaled_of_vblock`
  and `marked_count_scaled`, word for word, deduced from the field-generic count at
  `y = shiftUC ψ̂` (a radius `R_σ > |u|` with the uniform margin exists because the landed radius
  condition is strict).
* `markedOut_field_congr`: a rooted sum `markedOut z Y'` reads the unit field only through its
  lift on `psiThick Y'` and the datum only on `thickSet Y'`.

## Scope

Zero class, undecoupled level, generator-neutral (nothing depends on a choice of generating sets
for the class terms).  The locality proved here is locality in the **unit field** `y`.  For
`y = β_k^{-1/2} C^{1/2}(Θ) ψ̂` this is NOT locality in the configuration `ψ̂` (the field `y` at one
unit point reads `ψ̂` at all unit points through the matrix `C^{1/2}`); no `DepOn` statement for
configurations is proved.  The clamped global marks, the common label system and the `E1MarksC`
inhabitant are NOT constructed here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Polymer Balaban.Multiscale MeasureTheory Filter
  Balaban.SmallField.Def6 Balaban.Background Balaban.SmallField Set

/-! ### Locality of the marked term, abstract form -/

section Local

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {a c a' c' : F} {Θ Θ' : Λ} {R₁ r : ℝ}

/-- **Two marked terms that the functional cannot distinguish are equal.**  If the discs
`σ (a + t c)` and `σ (a' + t' c')`, `|σ| < R₁ + r`, lie in the analytic region of `Ev` at the data
`Θ`, `Θ'`, and `Ev(Θ, σ (a + t c)) = Ev(Θ', σ (a' + t' c'))` on them, then the cubic Taylor terms
`P(Θ, a + t c)` and `P(Θ', a' + t' c')` are equal. -/
theorem markedBlockTerm_congr_of_local (hR₁ : 1 < R₁) (hr : 0 < r)
    (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : Θ ∈ S) (hΘ' : Θ' ∈ S) {t t' : ℂ}
    (hdom : ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a + t • c) ∈ B)
    (hdom' : ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (a' + t' • c') ∈ B)
    (hloc : ∀ σ : ℂ, ‖σ‖ < R₁ + r → Ev (Θ, σ • (a + t • c)) = Ev (Θ', σ • (a' + t' • c'))) :
    markedBlockTerm Ev ω a c Θ t = markedBlockTerm Ev ω a' c' Θ' t' := by
  unfold markedBlockTerm rayTerm
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hs' : ‖(1 : ℂ) * (s : ℂ)‖ ≤ 1 := by
    rw [one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; exact hs.2
  have hn : ∀ τ : ℂ, ‖τ‖ < r → ‖(1 : ℂ) * (s : ℂ) + τ‖ < R₁ + r := fun τ hτ =>
    calc ‖(1 : ℂ) * (s : ℂ) + τ‖ ≤ ‖(1 : ℂ) * (s : ℂ)‖ + ‖τ‖ := norm_add_le _ _
      _ < R₁ + r := by linarith
  have hf : ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (Θ, ((1 : ℂ) * (s : ℂ)) • (a + t • c) + τ • (a + t • c)) := by
    intro τ hτ
    rw [← add_smul]
    exact hEv _ ⟨hΘ, hdom _ (hn τ hτ)⟩
  have hf' : ∀ τ : ℂ, ‖τ‖ < r →
      AnalyticAt ℂ Ev (Θ', ((1 : ℂ) * (s : ℂ)) • (a' + t' • c') + τ • (a' + t' • c')) := by
    intro τ hτ
    rw [← add_smul]
    exact hEv _ ⟨hΘ', hdom' _ (hn τ hτ)⟩
  show ω (s : ℂ) * dl3 Ev (a + t • c) (Θ, ((1 : ℂ) * (s : ℂ)) • (a + t • c)) =
    ω (s : ℂ) * dl3 Ev (a' + t' • c') (Θ', ((1 : ℂ) * (s : ℂ)) • (a' + t' • c'))
  rw [dl3_apply, dl3_apply, dirL3_eq hr hf, dirL3_eq hr hf']
  unfold dirS3
  congr 1
  refine Filter.EventuallyEq.iteratedDeriv_eq 3 ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hr] with τ hτ
  have hτ' : ‖τ‖ < r := by simpa using hτ
  rw [← add_smul, ← add_smul, hloc _ (hn τ hτ')]

end Local

/-! ### The clauses of the rooted count -/

section Clauses

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {β : Type*} [Fintype β]
  {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- **The clauses of the rooted count** (the conclusion of `marked_count_scaled`), for block terms
`Ev b Y`, `Y ∈ dom b`, the family `a + t c` of tangents, a datum `Θ`, a prefactor `F₀` and a rate
`a₀`.  With `markedOut z Y'` the sum of the `t`-derivatives at `0` of the marked terms whose bridge
to the root `z` is `Y'`, and `𝒴_z = bridgeFamily`:

1. `∑_{Y' ∈ 𝒴_z} markedOut z Y' = ∑_b ∑_{Y ∈ dom b} ∂_t P_{b,Y}(Θ, a + t c)|_{t=0}`, and this is the
   `t`-derivative at `0` of the sum of all the marked terms;
2. `|markedOut z Y'| ≤ F₀ e^{-a₀ d(Y')}` for every `Y'`;
3. `markedOut z Y' ≠ 0` implies `Y' ∈ 𝒟_K` and the root cube of `z` is a cube of `Y'`;
4. for `aEnt + 1 ≤ a₀ - a''`, `∑_{Y' ∈ 𝒴_z} |markedOut z Y'| e^{a'' d(Y')} ≤ F₀ K₀(d, L, a₀ - a'')`.

`d(Y) = treeLenCovOne m₀ K Y`; the index is `markedIdx` with the trivial read set. -/
def MarkedCountClauses (m₀ : ℕ) (dom : β → Finset (Set (CTorus d L N₁ m₁ K)))
    (z : RootIdx d L N₁ m₁ K) (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (a c : F) (Θ : Λ)
    (F₀ a₀ : ℝ) : Prop :=
  (∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ) dom z,
        markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight a c Θ Y' =
      ∑ b, ∑ Y ∈ dom b, deriv (markedBlockTerm (Ev b Y) taylorWeight a c Θ) 0 ∧
    deriv (fun t : ℂ => ∑ b, ∑ Y ∈ dom b, markedBlockTerm (Ev b Y) taylorWeight a c Θ t) 0 =
      ∑ b, ∑ Y ∈ dom b, deriv (markedBlockTerm (Ev b Y) taylorWeight a c Θ) 0) ∧
  (∀ Y', ‖markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight a c Θ Y'‖ ≤
      F₀ * Real.exp (-a₀ * treeLenCovOne m₀ K Y')) ∧
  (∀ Y', markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight a c Θ Y' ≠ 0 →
      IsDj m₀ K Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ K Set.univ Y') ∧
  (∀ {a'' : ℝ}, aEnt d L + 1 ≤ a₀ - a'' →
    ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ) dom z},
        ‖markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight a c Θ Y'.1‖ *
          Real.exp (a'' * treeLenCovOne m₀ K Y'.1) ≤
      F₀ * K0 d L (a₀ - a''))

variable {m₀ : ℕ}

open Classical in
/-- **The clauses of the rooted count from term bounds.**  Let the `t`-derivatives at `0` of the
marked terms be bounded by `C₀ e^{-2κ d(Y)}`, let at most `M (1 + d(Y))` pairs of `markedIdx` share
a domain `Y`, let the terms left out of `markedIdx` have zero derivative, and let every term be
differentiable at `t = 0`.  Then the clauses hold with `F₀ = C₀ M nFibre e^{(2κ-1) cBr}` and the
rate `2κ - 1`. -/
theorem markedCountClauses_of_terms (hN : L ^ m₀ ∣ N₁) (hL : 2 ≤ L)
    (dom : β → Finset (Set (CTorus d L N₁ m₁ K))) (hdom : ∀ b, ∀ Y ∈ dom b, IsDj m₀ K Y)
    (z : RootIdx d L N₁ m₁ K) (Ev : β → Set (CTorus d L N₁ m₁ K) → Λ × F → ℂ) (a c : F) (Θ : Λ)
    {C₀ M κdec : ℝ} (hC₀ : 0 ≤ C₀) (hM : 0 ≤ M) (hκ : 1 ≤ 2 * κdec)
    (hbd : ∀ b Y, ‖deriv (markedBlockTerm (Ev b Y) taylorWeight a c Θ) 0‖ ≤
      C₀ * Real.exp (-(2 * κdec) * treeLenCovOne m₀ K Y))
    (hcount : ∀ Y, (((markedIdx (fun _ : β => (Set.univ : Set (CTorus d L N₁ m₁ K))) dom z).filter
      (fun q => q.2 = Y)).card : ℝ) ≤ M * (1 + treeLenCovOne m₀ K Y))
    (hzero : ∀ b, ∀ Y ∈ dom b,
      (b, Y) ∉ markedIdx (fun _ : β => (Set.univ : Set (CTorus d L N₁ m₁ K))) dom z →
      deriv (markedBlockTerm (Ev b Y) taylorWeight a c Θ) 0 = 0)
    (hdiff : ∀ b, ∀ Y ∈ dom b,
      DifferentiableAt ℂ (markedBlockTerm (Ev b Y) taylorWeight a c Θ) 0) :
    MarkedCountClauses m₀ dom z Ev a c Θ
      (C₀ * M * ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L))) (2 * κdec - 1) := by
  have hbound := fun Y' => norm_markedOut_le_of_term_bounds hN (fun _ => Set.univ) dom hdom z Ev
    taylorWeight a c Θ hC₀ hM hκ (fun q _ => hbd q.1 q.2) hcount Y'
  have hF₀ : 0 ≤ C₀ * M * ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) :=
    mul_nonneg (mul_nonneg hC₀ hM) (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  have hB : ∀ Y', ‖markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight a c Θ Y'‖ ≤
      C₀ * M * ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
        Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ K Y') := by
    intro Y'
    refine (hbound Y').trans (le_of_eq ?_)
    ring
  refine ⟨⟨?_, ?_⟩, hB,
    fun Y' h => rootCube_mem_of_markedOut_ne_zero hN hL hdom z Ev taylorWeight a c Θ h,
    fun {a''} ha => sum_norm_markedOut_le_of_bound hN hL (fun _ => Set.univ) dom hdom z Ev
      taylorWeight a c Θ hF₀ hB ha⟩
  · rw [sum_markedOut_eq]
    exact sum_markedIdx_eq _ _ z _ hzero
  · exact deriv_sum_sum_of_differentiableAt _ _ _ fun b _ Y hY => hdiff b Y hY

end Clauses

/-- **A radius with the uniform margin.**  If `(R₁ + r)(|u| + t₁) Y₀ < δ₁` with `Y₀ ≥ 0` and
`R₁ + r ≥ 0`, there is `R_σ > |u|` with `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`. -/
theorem exists_radial_margin {R₁ r t₁ Y₀ δ₁ : ℝ} {u : ℂ} (hY0 : 0 ≤ Y₀) (hRr : 0 ≤ R₁ + r)
    (h : (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁) :
    ∃ Rσ : ℝ, ‖u‖ < Rσ ∧ (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁ := by
  have hA0 : 0 ≤ (R₁ + r) * Y₀ := mul_nonneg hRr hY0
  have hg0 : 0 < δ₁ - (R₁ + r) * (‖u‖ + t₁) * Y₀ := by linarith
  set A := (R₁ + r) * Y₀ with hA
  set g := δ₁ - (R₁ + r) * (‖u‖ + t₁) * Y₀ with hg
  have hε : 0 < g / (2 * (A + 1)) := by positivity
  refine ⟨‖u‖ + g / (2 * (A + 1)), by linarith, ?_⟩
  have h1 : A * (g / (2 * (A + 1))) ≤ g / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have e : (R₁ + r) * (‖u‖ + g / (2 * (A + 1)) + t₁) * Y₀ =
      (R₁ + r) * (‖u‖ + t₁) * Y₀ + A * (g / (2 * (A + 1))) := by rw [hA]; ring
  rw [e]
  linarith

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-! ### Mask locality for an arbitrary unit field -/

section FieldLocal

variable (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm} {a₁ ν eps δ₁ Y₀ R₁ r Rσ t₁ : ℝ}
  {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}

/-- The lift of the masked field at a fine site is determined by the lift of the field at that
site. -/
theorem liftC_maskUC_congr {y y' : S.EC} {x : CTorus d L N₁ m₁ (k + 1)}
    (h : liftC S.hG' y x = liftC S.hG' y' x) :
    liftC S.hG' (S.maskUC z y) x = liftC S.hG' (S.maskUC z y') x := by
  classical
  funext i
  have hi : y (unitPt S.hG' x, i) = y' (unitPt S.hG' x, i) := congrFun h i
  rw [liftC_apply, liftC_apply]
  by_cases hb : unitPt S.hG' x ∈ S.blockU z <;> simp [maskUC, hb, hi]

/-- **Locality of the marked term in the unit field and the datum.**  Let `Ev` be analytic on
`Ξ^c × FlBall Hm δ₁` and local in the sense of `vblock_expansion_scaled` for the label `Y`.  Let
`y`, `y'` be unit fields of Euclidean norm at most `Y₀` at the unit points whose lifts agree on
`psiThick Y`, and `Θ`, `Θ'` data of the chart that agree on `thickSet Y`.  Under the radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, for `|u| < R_σ` and `|t| < t₁` the marked terms along
`u y + t M_z y` at `Θ` and along `u y' + t M_z y'` at `Θ'` are equal. -/
theorem markedBlockTerm_field_congr {y y' : S.EC} {u t : ℂ}
    {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hR₁ : 1 < R₁) (hr : 0 < r) (hY : ∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀)
    (hY' : ∀ b : S.U, vn (fun i => y' (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hu : ‖u‖ < Rσ) (ht : ‖t‖ < t₁) (hHm : IsLevel Hm k)
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (han : AnalyticOnNhd ℂ Ev (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    (hloc : ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ w' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) w.1 w'.1 → (∀ x ∈ psiThick Y, w.2 x = w'.2 x) → Ev w = Ev w')
    (hag : agreeOn (thickSet S.G' Y) Θ Θ')
    (hyy : ∀ x ∈ psiThick Y, liftC S.hG' y x = liftC S.hG' y' x) :
    markedBlockTerm Ev taylorWeight (liftC S.hG' (u • y)) (liftC S.hG' (S.maskUC z y)) Θ t =
      markedBlockTerm Ev taylorWeight (liftC S.hG' (u • y')) (liftC S.hG' (S.maskUC z y'))
        Θ' t := by
  have hd : ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y)) ∈ FlBall Hm δ₁ :=
    fun σ hσ => S.markedDisc_field_mem_flBall z hHm hY hrad hu ht hσ
  have hd' : ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • y') + t • liftC S.hG' (S.maskUC z y')) ∈ FlBall Hm δ₁ :=
    fun σ hσ => S.markedDisc_field_mem_flBall z hHm hY' hrad hu ht hσ
  refine markedBlockTerm_congr_of_local hR₁ hr han hΘ hΘ' hd hd' fun σ hσ => ?_
  have hw : (Θ, σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y))) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁ := ⟨hΘ, hd σ hσ⟩
  have hw' : (Θ', σ • (liftC S.hG' (u • y') + t • liftC S.hG' (S.maskUC z y'))) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁ := ⟨hΘ', hd' σ hσ⟩
  refine hloc _ hw _ hw' hag fun x hx => ?_
  show (σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y))) x =
    (σ • (liftC S.hG' (u • y') + t • liftC S.hG' (S.maskUC z y'))) x
  rw [Pi.smul_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.add_apply, Pi.smul_apply,
    map_smul, map_smul, Pi.smul_apply, Pi.smul_apply, hyy x hx, S.liftC_maskUC_congr z (hyy x hx)]

/-- **Locality of the marked term for an arbitrary unit field.**  If the block term `Ev` is analytic
on `Ξ^c × FlBall Hm δ₁`, local in the sense of `vblock_expansion_scaled` (it reads the tangent only
on `psiThick Y`), and `psiThick Y` misses the fine block `B(z)`, then for every unit field `y` of
Euclidean norm at most `Y₀` at the unit points, under the radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁` and `|u| < R_σ`, the `t`-derivative at `0` of the marked term along
`u y + t M_z y` vanishes (`deriv_markedBlockTerm_eq_zero_of_psiThick_disjoint_of_local` with `y`
in place of `shiftUC ψ̂`). -/
theorem deriv_markedBlockTerm_eq_zero_of_psiThick_disjoint_field {y : S.EC} {u : ℂ}
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} {Y : Set (CTorus d L N₁ m₁ (k + 1))}
    (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁) (hY : ∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hu : ‖u‖ < Rσ) (hHm : IsLevel Hm k)
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (han : AnalyticOnNhd ℂ Ev (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    (hloc : ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ w' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) w.1 w'.1 → (∀ x ∈ psiThick Y, w.2 x = w'.2 x) → Ev w = Ev w')
    (hmiss : ∀ x ∈ psiThick Y, x ∉ fineBlock z) :
    deriv (markedBlockTerm Ev taylorWeight (liftC S.hG' (u • y))
      (liftC S.hG' (S.maskUC z y)) Θ) 0 = 0 := by
  have hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y)) ∈ FlBall Hm δ₁ :=
    fun t ht σ hσ => S.markedDisc_field_mem_flBall z hHm hY hrad hu ht hσ
  refine deriv_markedBlockTerm_eq_zero_of_local hR₁ hr ht₁ han hΘ hdisc ?_
  intro t ht σ hσ
  have h0 : ‖(0 : ℂ)‖ < t₁ := by simpa using ht₁
  have hw : (Θ, σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y))) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁ :=
    ⟨hΘ, hdisc t ht σ hσ⟩
  have hw' : (Θ, σ • liftC S.hG' (u • y)) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁ := by
    have := hdisc 0 h0 σ hσ
    rw [zero_smul, add_zero] at this
    exact ⟨hΘ, this⟩
  refine hloc _ hw _ hw' (agreeOn_refl _ Θ) fun x hx => ?_
  have hc := S.liftC_maskUC_apply_of_notMem z y (hmiss x hx)
  show (σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y))) x =
    (σ • liftC S.hG' (u • y)) x
  rw [Pi.smul_apply, Pi.add_apply, Pi.smul_apply, hc, smul_zero, add_zero, Pi.smul_apply]

/-- **The Cauchy bound for the marked terms of the block expansion along an arbitrary unit field**
(`norm_deriv_markedBlockTerm_field_le` with the bound `E e^{-2κ_dec d(Y)}` of the block term, in the
size `treeLenCovOne` of the bridge). -/
theorem norm_deriv_markedBlockTerm_field_le_of_vblock (hHm : IsLevel Hm k) {t₀ E κdec : ℝ}
    {m₀ : ℕ} {y : S.EC} {u : ℂ} {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    {Y : Set (CTorus d L N₁ m₁ (k + 1))} (hY : ∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hu : ‖u‖ < Rσ) (hR₁ : 1 < R₁) (hr : 0 < r)
    (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁)
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (han : AnalyticOnNhd ℂ Ev (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    (hbd : ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
      ‖Ev w‖ ≤ E * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) :
    ‖deriv (markedBlockTerm Ev taylorWeight (liftC S.hG' (u • y))
      (liftC S.hG' (S.maskUC z y)) Θ) 0‖ ≤
      (3 * ‖E‖ / (r ^ 3 * t₀)) * Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by
  have h := S.norm_deriv_markedBlockTerm_field_le z hHm hrad hR₁ hr han hΘ hY hbd ht₀ ht₀₁ hu
  refine h.trans ?_
  rw [treeLenCov_eq_treeLenCovOne S.hG' m₀ Y]
  have hex : Real.exp (-2 * κdec * treeLenCovOne m₀ (k + 1) Y) =
      Real.exp (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y) := by congr 1; ring
  rw [hex]
  have hr3 : 0 < r ^ 3 * t₀ := by positivity
  rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hr3]
  nlinarith [Real.exp_pos (-(2 * κdec) * treeLenCovOne m₀ (k + 1) Y), le_abs_self E,
    Real.norm_eq_abs E]

end FieldLocal

/-! ### The field-generic count -/

section Count

open Balaban.Multiscale

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The field-generic count for given block terms.**  The hypotheses `han`, `hbd`, `hloc` are the
analyticity, bound (with a constant `E` in place of `energyBdScaled`) and locality clauses of
`vblock_expansion_scaled` for the terms `Ev`.  For every marked block `z`, every complex field `y`
of the unit lattice with `|y(b)| ≤ Y₀` at the unit points, every radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `0 < t₀ < t₁`, every `|u| < R_σ` and every datum
`Θ` of the chart, the clauses of the rooted count (`MarkedCountClauses`) hold for the family
`lift (u y) + t · lift (M_z y)`, with
`F₀ = 3 ‖E‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}`, `M = L^{m₀+m₁}`, and the rate
`2κ_dec - 1`.  The step enters only through its generating set and the mask. -/
theorem marked_count_field_of_vblock (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hd : 3 ≤ d) (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    {κdec : ℝ} (hκ1 : 1 ≤ 2 * κdec) (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b)) (hL : 2 ≤ L)
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    {E : ℝ}
    (hloc : ∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ w' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) w.1 w'.1 → (∀ x ∈ psiThick Y, w.2 x = w'.2 x) →
        Ev b Y w = Ev b Y w')
    (hbd : ∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev b Y w‖ ≤ E * Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y))
    (han : ∀ b, ∀ Y, AnalyticOnNhd ℂ (Ev b Y)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁)) :
    ∀ {Y₀ R₁ r Rσ t₁ t₀ : ℝ} {y : S.EC}, (∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀) →
      (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
      ∀ {u : ℂ}, ‖u‖ < Rσ → ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
        Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
      MarkedCountClauses m₀ (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z Ev
        (liftC S.hG' (u • y)) (liftC S.hG' (S.maskUC z y)) Θ
        (3 * ‖E‖ / (r ^ 3 * t₀) * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
          ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L))) (2 * κdec - 1) := by
  classical
  intro Y₀ R₁ r Rσ t₁ t₀ y hY hrad hR₁ hr ht₀ ht₀₁ u hu Θ hΘ
  have ht₁ : 0 < t₁ := ht₀.trans ht₀₁
  have hN : L ^ m₀ ∣ N₁ := (hcovV z).hN
  have hdom : ∀ b, ∀ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), IsDj m₀ (k + 1) Y :=
    fun b Y hY => isDj_of_polymerDomains
      (fun i : ParIdx S.G' (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
      S.hG' (hcovV b) hd (fun i => i.1.2) (hoptV b) hY
  have hdisc : ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r →
      σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y)) ∈ FlBall Hm δ₁ :=
    fun t ht σ hσ => S.markedDisc_field_mem_flBall z hHm hY hrad hu ht hσ
  have hc1 : 0 ≤ c1 d L := by unfold c1; positivity
  have hM : 0 ≤ c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d := by positivity
  have hC₀ : 0 ≤ 3 * ‖E‖ / (r ^ 3 * t₀) := by positivity
  exact markedCountClauses_of_terms hN hL _ hdom z Ev _ _ Θ hC₀ hM hκ1
    (fun b Y => S.norm_deriv_markedBlockTerm_field_le_of_vblock z hHm hY hrad hu hR₁ hr ht₀ ht₀₁
      hΘ (han b Y) (hbd b Y))
    (S.card_markedIdx_fibre_le z hd hcovV hX₁V hoptV hZV)
    (fun b Y hY' hnot => S.deriv_markedBlockTerm_eq_zero_of_psiThick_disjoint_field z hR₁ hr ht₁
      hY hrad hu hHm hΘ (han b Y) (hloc b Y) fun x hx hxz =>
        hnot (mem_markedIdx.2 ⟨hY', ⟨rootSite z, trivial, rootSite_mem_fineBlock z⟩,
          ⟨x, hx, hxz⟩⟩))
    (fun b Y _ => ((analyticOnNhd_markedBlockTerm hR₁ hr (analyticOnNhd_taylorWeight _) (han b Y)
      hΘ hdisc) 0 (Metric.mem_ball_self ht₁)).differentiableAt)

/-- **The field-generic count** (`MARK-SCALED-COUNT` for an arbitrary unit field).  The hypotheses
are those of `marked_count_scaled`.  There is one family of block terms `E_{b,Y}` (`Ev b Y`, the
terms of `vblock_expansion_scaled`, with its four clauses: sum identity, locality, the bound
`E* e^{-2κ_dec d(Y)}`, analyticity on `Ξ^c × FlBall Hm δ₁`) such that for **every** marked block
`z`, every complex field `y` of the unit lattice with `|y(b)| ≤ Y₀` at the unit points, every
radial margin `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `0 < t₀ < t₁`, every `|u| < R_σ` and
every datum `Θ` of the chart, the clauses of the rooted count hold for the family
`lift (u y) + t · lift (M_z y)`, with `F₀ = 3‖E*‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}`
and the rate `2κ_dec - 1`.  The terms do not depend on `z`, `y`, `u`, `Θ` or the radii. -/
theorem marked_count_field
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hΔV : ∀ b, treeLenCovOne m₀ (jV b) (XV b) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hmarV : ∀ b, BlockMargin S.G' (X₁V b)
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hL : 2 ≤ L) :
    ∃ Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      (∀ b, ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock S.G' Hm (compWeight L a₁) ν k (bgMultC S.G' (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') ψ' b =
        ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), Ev b Y (rawOf D, ψ')) ∧
      (∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ w' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) w.1 w'.1 → (∀ x ∈ psiThick Y, w.2 x = w'.2 x) →
        Ev b Y w = Ev b Y w') ∧
      (∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev b Y w‖ ≤ energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) ∧
      (∀ b, ∀ Y, AnalyticOnNhd ℂ (Ev b Y)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁)) ∧
      ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) {Y₀ R₁ r Rσ t₁ t₀ : ℝ} {y : S.EC},
        (∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀) →
        (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        ∀ {u : ℂ}, ‖u‖ < Rσ → ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
          Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        MarkedCountClauses m₀ (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z Ev
          (liftC S.hG' (u • y)) (liftC S.hG' (S.maskUC z y)) Θ
          (3 * ‖energyBdScaled d L N (compWeight L a₁) k
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀) *
            (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
            ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L))) (2 * κdec - 1) := by
  classical
  have hd : 3 ≤ d := hC.HBp.hd
  have hex := fun b => vblock_expansion_scaled hC (hcovV b) (hX₁V b) hconn hrow (hoptV b) (hΔV b)
    hκ₀ hκdec hκ h1 hlog S.hk1 le_rfl hHm S.hG' b (hZV b) (hmarV b)
  choose Ev hsum hloc hbd han using hex
  exact ⟨Ev, fun b => hsum b, hloc, hbd, han, fun z => S.marked_count_field_of_vblock z hd hcovV
    hX₁V hoptV (by linarith) hHm hZV hL Ev hloc hbd han⟩

/-! ### The landed count is the field-generic count at `y = shiftUC ψ̂` -/

/-- **The landed `marked_count_scaled_of_vblock` from the field-generic count.**  The statement is
that of `marked_count_scaled_of_vblock`, word for word; the proof is
`marked_count_field_of_vblock` at the unit field `y = shiftUC ψ̂`, with a radius `R_σ > |u|` chosen
by `exists_radial_margin` (the landed radius condition `(R₁ + r)(|u| + t₁) Y₀ < δ₁` is strict). -/
theorem marked_count_scaled_of_vblock_via_field
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) (hd : 3 ≤ d)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    {κdec : ℝ} (hκ1 : 1 ≤ 2 * κdec) (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b)) (hL : 2 ≤ L)
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hloc : ∀ b, ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev b Y u = Ev b Y u')
    (hbd : ∀ b, ∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev b Y u‖ ≤ energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y))
    (han : ∀ b, ∀ Y, AnalyticOnNhd ℂ (Ev b Y)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁)) :
      ∀ {Y₀ R₁ r t₁ t₀ : ℝ}, 0 ≤ Y₀ → ∀ {x : S.E} {u : ℂ},
        (∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀) →
        (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
          Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        (∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
            markedOut m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0 ∧
          deriv (fun t : ℂ => ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ t) 0 =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0) ∧
        (∀ Y', ‖markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'‖ ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
        (∀ Y', markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' ≠ 0 →
            IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
        (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
          ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z},
            ‖markedOut m₀ (fun _ => Set.univ)
                (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
                Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'.1‖ *
              Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              K0 d L (2 * κdec - 1 - a'')) := by
  intro Y₀ R₁ r t₁ t₀ hY0 x u hY hrad hR₁ hr ht₀ ht₀₁ Θ hΘ
  obtain ⟨Rσ, hu, hrad'⟩ := exists_radial_margin hY0 (by linarith) hrad
  exact S.marked_count_field_of_vblock z hd hcovV hX₁V hoptV hκ1 hHm hZV hL Ev hloc hbd han
    hY hrad' hR₁ hr ht₀ ht₀₁ hu hΘ

/-- **The landed `marked_count_scaled` from the field-generic count.**  The statement is that of
`marked_count_scaled`, word for word; the proof is `marked_count_field` at the unit field
`y = shiftUC ψ̂`.  So the landed count is the special case of the field-generic count in which the
unit field is the shift of the fixed step. -/
theorem marked_count_scaled_via_field (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    (hΔV : ∀ b, treeLenCovOne m₀ (jV b) (XV b) = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b))
    (hmarV : ∀ b, BlockMargin S.G' (X₁V b)
      (↑(blockSites d L N₁ m₁ (k + 1) k b) : Set (CTorus d L N₁ m₁ (k + 1))))
    (hL : 2 ≤ L) :
    ∃ Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      (∀ b, ∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock S.G' Hm (compWeight L a₁) ν k (bgMultC S.G' (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') ψ' b =
        ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b), Ev b Y (rawOf D, ψ')) ∧
      ∀ {Y₀ R₁ r t₁ t₀ : ℝ}, 0 ≤ Y₀ → ∀ {x : S.E} {u : ℂ},
        (∀ q : S.U, vn (fun i => S.shiftUC x (q, i)) ≤ Y₀) →
        (R₁ + r) * (‖u‖ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        ∀ {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N},
          Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps →
        (∑ Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z,
            markedOut m₀ (fun _ => Set.univ) (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0 ∧
          deriv (fun t : ℂ => ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ t) 0 =
            ∑ b, ∑ Y ∈ polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b),
              deriv (markedBlockTerm (Ev b Y) taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ) 0) ∧
        (∀ Y', ‖markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'‖ ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              Real.exp (-(2 * κdec - 1) * treeLenCovOne m₀ (k + 1) Y')) ∧
        (∀ Y', markedOut m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
              Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
              (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y' ≠ 0 →
            IsDj m₀ (k + 1) Y' ∧ rootCube (m₀ := m₀) z ∈ blocksOf m₀ (k + 1) Set.univ Y') ∧
        (∀ {a'' : ℝ}, aEnt d L + 1 ≤ 2 * κdec - 1 - a'' →
          ∑ Y' : {Y' // Y' ∈ bridgeFamily m₀ (fun _ => Set.univ)
              (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z},
            ‖markedOut m₀ (fun _ => Set.univ)
                (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) z
                Ev taylorWeight (liftC S.hG' (u • S.shiftUC x))
                (liftC S.hG' (S.maskUC z (S.shiftUC x))) Θ Y'.1‖ *
              Real.exp (a'' * treeLenCovOne m₀ (k + 1) Y'.1) ≤
            (3 * ‖energyBdScaled d L N (compWeight L a₁) k
                (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀)) *
              (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
              ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L)) *
              K0 d L (2 * κdec - 1 - a'')) := by
  obtain ⟨Ev, hsum, -, -, -, hfield⟩ := S.marked_count_field hC hcovV hX₁V hconn hrow hoptV hΔV
    hκ₀ hκdec hκ h1 hlog hHm hZV hmarV hL
  refine ⟨Ev, hsum, ?_⟩
  intro Y₀ R₁ r t₁ t₀ hY0 x u hY hrad hR₁ hr ht₀ ht₀₁ Θ hΘ
  obtain ⟨Rσ, hu, hrad'⟩ := exists_radial_margin hY0 (by linarith) hrad
  exact hfield z hY hrad' hR₁ hr ht₀ ht₀₁ hu hΘ

/-! ### Locality of the rooted sums in the unit field -/

/-- **A rooted sum reads the unit field only near its label.**  Let the block terms `Ev b Y` be
analytic on `Ξ^c × FlBall Hm δ₁` and local in the sense of `vblock_expansion_scaled`.  Let `y`,
`y'` be unit fields of Euclidean norm at most `Y₀` at the unit points whose lifts agree on
`psiThick Y'`, and `Θ`, `Θ'` data of the chart that agree on `thickSet Y'`.  Under the radial
margin and `|u| < R_σ`, the rooted sums `markedOut z Y'` built with `(y, Θ)` and with `(y', Θ')`
are equal: every term of the fibre of `Y'` has its label inside `Y'`.

This is locality in the unit field.  For `y = β_k^{-1/2} C^{1/2}(Θ) ψ̂` it does not give locality in
the configuration `ψ̂`. -/
theorem markedOut_field_congr (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1)))) (hHm : IsLevel Hm k)
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (hloc : ∀ b, ∀ Y, ∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ w' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) w.1 w'.1 → (∀ x ∈ psiThick Y, w.2 x = w'.2 x) →
        Ev b Y w = Ev b Y w')
    (han : ∀ b, ∀ Y, AnalyticOnNhd ℂ (Ev b Y)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    {Y₀ R₁ r Rσ t₁ : ℝ} {y y' : S.EC} (hY : ∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀)
    (hY' : ∀ b : S.U, vn (fun i => y' (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁) {u : ℂ}
    (hu : ‖u‖ < Rσ) {Θ Θ' : RawData d L (N₁ * L ^ m₁) (k + 1) N}
    (hΘ : Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    (hΘ' : Θ' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps)
    {Y' : Set (CTorus d L N₁ m₁ (k + 1))} (hag : agreeOn (thickSet S.G' Y') Θ Θ')
    (hyy : ∀ x ∈ psiThick Y', liftC S.hG' y x = liftC S.hG' y' x) :
    markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight (liftC S.hG' (u • y))
        (liftC S.hG' (S.maskUC z y)) Θ Y' =
      markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight (liftC S.hG' (u • y'))
        (liftC S.hG' (S.maskUC z y')) Θ' Y' := by
  classical
  unfold markedOut
  refine Finset.sum_congr rfl fun q hq => ?_
  have hsub : q.2 ⊆ Y' := (Finset.mem_filter.1 hq).2 ▸ subset_bridge z q.2
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) ht₁] with t ht
  exact S.markedBlockTerm_field_congr z hR₁ hr hY hY' hrad hu (by simpa using ht) hHm hΘ hΘ'
    (han q.1 q.2) (hloc q.1 q.2) (agreeOn_mono (thickSet_mono hsub) hag)
    (fun x hx => hyy x (psiThick_mono hsub hx))

end Count

end StepSetting

end Balaban.Fluctuation
