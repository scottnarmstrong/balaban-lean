/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.SourceExponentFamily
public import Balaban.Inhabited.SourceFamilyRelativeFromTower
public import Balaban.Fluctuation.ObsScalarTilt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The analytic activity family of the source exponent, with its value and its `W` identities

The exponent of the step of the zero class is `W₁ + W₂` of a joint representation `Jr`.
`SourceExponentFamily.lean` writes it as a label-activity sum on the constant-`h₀` fibre of the
chart, with activities chosen separately at each chart point.  Here the same identities are proved
for the **one** family `A(e, u) = labelActFamilyOn … e u` of the direct terms, which is jointly
analytic in the chart point `e` and the complex parameter `u`.

* `labelActFamilyOn_sum`, `ae_labelActFamilyOn_sum`: the label sum of the family at `e ∈ V`,
  `‖u‖ < R_σ` is the expanded function `val` at the hat variable and the datum `J e`; almost
  everywhere it is `val` at the hat field `ψ̂` (one null set for all `e` and `u`).
* `sqFactor`, `zeroSourceAct`: the zero-source family `A⁰(e, u) = u² · A((e.1, 0), u)` for
  `‖u‖ < R_u` (and `0` otherwise), a scalar multiple of the family at the zero-source point; its
  sum, analyticity in `(e, u)`, differentiability in `u`, continuity, and the transfer of the
  identity `W(s) = s² ∑ A((q,0), s)` to `W(s) = ∑ A⁰(s)`.
* `segAct_hW_of_parts`: the two-segment identity for `segAct` of two families from the identities
  of `W₁` and `W₂`.
* `activityFamilyAnalytic_fromTower`: at the shared tower, **one** choice of `Jr`, `val`, `𝒴`,
  `Tt`, `I`, `hF` carries the clauses of `sourceDirectTerms_scale_fromTower` (formula of `val`,
  sharp locality, diagonal continuity, an instance at every point of the slice), and for
  `A = labelActFamilyOn … I hF`:
  analyticity on `physVq × ball 0 2`, continuity in the configuration, the value of the label sum,
  and, on the fibre `h ≡ h₀`,
  `Jr.W1 (e.1, s ψ̂) = s² ∑_y A((e.1, 0), s)_y` and
  `Jr.W2 e.2 (e.1, t ψ̂) = ∑_y A(e, t)_y − ∑_y A((e.1, 0), t)_y`
  for almost every `ψ̂` (one null set for all `e`, `s`, `t`), the same with `W₁`, `W₂` of the
  step `S.withDatum D` at every datum `D` of the chart with `D.h ≡ h₀`, the two-segment identity
  for `segAct (A (e.1, 0)) (A e)`, and for the zero-source family `A⁰ = zeroSourceAct A 2`:
  analyticity on `physV × ball 0 2`, continuity, and `(S.withDatum D).WoneC s = ∑_y A⁰(·, s)_y`.

**Normalization.**  The parameter `u` of `labelActFamilyOn` is the parameter `σ` of the direct terms
at the unscaled hat pair `(ψ̂, ψ̂)`.  Hence `W₁(s) = s² · (value at σ = s)`, while the source part
`W₂(t)` is a difference of values at `σ = t` with no power of `t`.

**Where the identities hold.**  Analyticity of `A` is on all of `physVq … q` and that of `A⁰` on
all of `physV` (complex `h` allowed).  The `W` identities are on the fibre `h ≡ h₀` only: the step
`S.withDatum D` exists only there, and `Jr.W1` is identified with the hat expansion only there
(`wone_chartIdentity_fromTower`).

**One witness.**  The landed `sourceDirectTerms_scale_fromTower` and
`sourceFamilyRelative_scale_fromTower` return separate existentials.  Here `val`, `𝒴`, `Tt` are
taken from the first, the record `I` from its instance clause at `(rawOf S.D', 0)`, and the family
`hF` is rebuilt from its continuity clause by `directTermsFamilyOn_scaled`; the second theorem is
used only for the bound on the amplitude, an inequality between real numbers.

The marks, the common label system of the roots and `E1MarksC` are NOT in this file.  Zero class;
independent of the choice of generators.
-/

@[expose] public section

namespace Balaban.Fluctuation

open MeasureTheory Balaban Balaban.Localization Balaban.Multiscale Balaban.Polymer
  Balaban.Background Metric

section FamilySum

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (m₀ : ℕ) {Λ F' E : Type}
  [NormedAddCommGroup Λ] [NormedSpace ℂ Λ] [NormedAddCommGroup E] [NormedSpace ℂ E]
  {hp : 0 < S.p₁} {emb : (S.U × Fin N → ℂ) → F'} {ρ Rσ εU a : ℝ} {Θ₀ : Λ}
  {SΛ : Set Λ} {XW : Set (F' × F')} {val : F' → F' → ℂ → Λ → ℂ}
  {AgΘ : Set (CTorus d L N₁ m₁ (k + 1)) → Λ → Λ → Prop}
  {AgF : Set (CTorus d L N₁ m₁ (k + 1)) → F' → F' → Prop}
  (J : E →L[ℂ] Λ)
  {I : DirectTerms S m₀ hp emb ρ Rσ εU a Θ₀ SΛ XW val AgΘ AgF} {V : Set E}
  (hF : DirectTermsFamilyOn S m₀ J I V)
  (hN : L ^ m₀ ∣ N₁) (hρ : 0 < ρ) (hRσ : 0 ≤ Rσ) (hεU : 0 ≤ εU)
  {κ0 Kc : ℝ} (hκ0 : aEnt d L + 1 ≤ κ0) (hKc : K0 d L κ0 ≤ Kc)

/-- **The label sum of the family.**  At `e ∈ V` and `‖u‖ < R_σ` the sum over the labels of the
activities of `labelActFamilyOn` is the expanded function `val` at the hat variable of the
configuration, the parameter `u` and the datum `J e`. -/
theorem labelActFamilyOn_sum {e : E} (he : e ∈ V) {u : ℂ} (hu : ‖u‖ < Rσ)
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    ∑ y, (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H y Φ =
      val (emb (S.hatOf m₀ ρ hp Φ)) (emb (S.hatOf m₀ ρ hp Φ)) u (J e) := by
  simp only [labelActFamilyOn_H S m₀ J hF hN hρ hRσ hεU hκ0 hKc he hu]
  rw [Finset.sum_coe_sort I.𝒴 (fun Y => I.T Y (emb (S.hatOf m₀ ρ hp Φ))
    (emb (S.hatOf m₀ ρ hp Φ)) u (J e))]
  exact (I.loc.sum (emb (S.hatOf m₀ ρ hp Φ), emb (S.hatOf m₀ ρ hp Φ))
    (I.xw _ (S.hatOf_mem m₀ hρ hp Φ)) u hu (J e) (hF.sub ⟨e, he, rfl⟩)).symm

/-- **The label sum at the hat field, almost everywhere.**  For `p₁ ≤ ρ` there is one
`ν_{p₁}`-null set outside of which, for every `e ∈ V` and every `‖u‖ < R_σ`, the label sum of the
family at the block variables of `ψ̂` is `val` at the hat field `ψ̂` itself. -/
theorem ae_labelActFamilyOn_sum (hpρ : S.p₁ ≤ ρ) :
    ∀ᵐ x ∂S.nuFl, ∀ e ∈ V, ∀ u : ℂ, ‖u‖ < Rσ →
      ∑ y, (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H y
          ((S.blockSplit m₀ hp).restr x) =
        val (emb (S.hatC x)) (emb (S.hatC x)) u (J e) := by
  filter_upwards [S.ae_hatOf_restr m₀ hρ hp hpρ] with x hx
  intro e he u hu
  rw [labelActFamilyOn_sum S m₀ J hF hN hρ hRσ hεU hκ0 hKc he hu, hx]

/-- **Holomorphy in `u` at a fixed parameter.**  For `e ∈ V`, every label and every
configuration, `u ↦ A(e, u)_y(Φ)` is differentiable on the disc `‖u‖ < R_σ`. -/
theorem labelActFamilyOn_differentiableOn {e : E} (he : e ∈ V) (y : {Y // Y ∈ I.𝒴})
    (Φ : ∀ b, (S.blockSplit m₀ hp).Ωb b) :
    DifferentiableOn ℂ
      (fun u => (labelActFamilyOn S m₀ J I hF hN hρ hRσ hεU hκ0 hKc e u).H y Φ)
      (ball (0 : ℂ) Rσ) := by
  have h := (dtAct_spec S m₀ (I.atThetaOn S m₀ J hF he) hN hρ hRσ hεU hκ0 hKc).1 y Φ
  refine h.congr fun u _ => ?_
  rw [labelActFamilyOn_eq_dtAct S m₀ J hF hN hρ hRσ hεU hκ0 hKc he u]

end FamilySum

section ZeroSource

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
variable {Lb : Type*} [Fintype Lb] {Lab : CubeLabels m₀ j Ω Lb} {εH κH κ0 Kc : ℝ}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {E₁ E₂ : Type*}

/-- **The factor of the interaction exponent**: `u²` on the open disc `‖u‖ < R_u`, and `0`
outside (so that it is bounded on all of `ℂ`). -/
noncomputable def sqFactor (Ru : ℝ) (u : ℂ) : ℂ := if ‖u‖ < Ru then u ^ 2 else 0

theorem norm_sqFactor_le {Ru : ℝ} (hRu : 0 ≤ Ru) (u : ℂ) : ‖sqFactor Ru u‖ ≤ Ru ^ 2 := by
  unfold sqFactor
  split_ifs with h
  · rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg u) h.le 2
  · simpa using pow_nonneg hRu 2

theorem sqFactor_of_lt {Ru : ℝ} {u : ℂ} (h : ‖u‖ < Ru) : sqFactor Ru u = u ^ 2 := by
  simp [sqFactor, h]

/-- On the real segment `[0,1]` the factor is `s²` (for `1 < R_u`). -/
theorem sqFactor_ofReal {Ru : ℝ} (hRu : 1 < Ru) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    sqFactor Ru (s : ℂ) = (s : ℂ) ^ 2 :=
  sqFactor_of_lt (norm_ofReal_lt_of_mem hs hRu)

/-- **The zero-source family.**  For a family `A` over a parameter space `E₁ × E₂` (datum and
source), `A⁰(e, u) = u² · A((e.1, 0), u)` for `‖u‖ < R_u` and `0` otherwise: a scalar multiple
(`LabelAct.rscale`) of the family at the zero-source point, with the same labels, rate and entropy
constant and the amplitude `R_u² ε_H`.  It does not depend on the source coordinate `e.2`. -/
noncomputable def zeroSourceAct [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Ru : ℝ) (hRu : 0 ≤ Ru) (e : E₁ × E₂) (u : ℂ) : LabelAct Lab Ωb (Ru ^ 2 * εH) κH κ0 Kc :=
  (A (e.1, 0) u).rscale (Ru ^ 2) (sqFactor Ru u) (norm_sqFactor_le hRu u)

theorem zeroSourceAct_H [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Ru : ℝ) (hRu : 0 ≤ Ru) (e : E₁ × E₂) (u : ℂ) (y : Lb) (Φ : ∀ b, Ωb b) :
    (zeroSourceAct A Ru hRu e u).H y Φ = sqFactor Ru u * (A (e.1, 0) u).H y Φ := rfl

/-- The label sum of the zero-source family. -/
theorem zeroSourceAct_total [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Ru : ℝ) (hRu : 0 ≤ Ru) (e : E₁ × E₂) (u : ℂ) (Φ : ∀ b, Ωb b) :
    ∑ y, (zeroSourceAct A Ru hRu e u).H y Φ = sqFactor Ru u * ∑ y, (A (e.1, 0) u).H y Φ := by
  simp only [zeroSourceAct_H, Finset.mul_sum]

/-- The zero-source family depends on the parameter only through the datum coordinate. -/
theorem zeroSourceAct_congr_fst [Zero E₂] (A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc)
    (Ru : ℝ) (hRu : 0 ≤ Ru) {e e' : E₁ × E₂} (h : e.1 = e'.1) (u : ℂ) :
    zeroSourceAct A Ru hRu e u = zeroSourceAct A Ru hRu e' u := by
  unfold zeroSourceAct
  rw [h]

/-- **Joint analyticity of the zero-source family.**  If `(e, u) ↦ A(e, u)_y(Φ)` is analytic on
`V × ball 0 R`, `R_u ≤ R`, and `V₀` is an open set of parameters whose zero-source points lie in
`V`, then `(e, u) ↦ A⁰(e, u)_y(Φ)` is analytic on `V₀ × ball 0 R_u`. -/
theorem zeroSourceAct_analyticOnNhd [NormedAddCommGroup E₁] [NormedSpace ℂ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℂ E₂]
    {A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {V V₀ : Set (E₁ × E₂)} {R Ru : ℝ}
    (hRu : 0 ≤ Ru) (hR : Ru ≤ R) (hV₀ : IsOpen V₀) (hsub : ∀ e ∈ V₀, (e.1, (0 : E₂)) ∈ V)
    {y : Lb} {Φ : ∀ b, Ωb b}
    (h : AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => (A p.1 p.2).H y Φ) (V ×ˢ ball (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => (zeroSourceAct A Ru hRu p.1 p.2).H y Φ)
      (V₀ ×ˢ ball (0 : ℂ) Ru) := by
  have hL : AnalyticOnNhd ℂ
      (fun p : (E₁ × E₂) × ℂ => (((p.1.1, (0 : E₂)), p.2) : (E₁ × E₂) × ℂ)) Set.univ :=
    (((ContinuousLinearMap.fst ℂ E₁ E₂).prod (0 : E₁ × E₂ →L[ℂ] E₂)).prodMap
      (ContinuousLinearMap.id ℂ ℂ)).analyticOnNhd _
  have h1 := h.comp (hL.mono (Set.subset_univ (V₀ ×ˢ ball (0 : ℂ) Ru)))
    (fun p hp' => ⟨hsub p.1 hp'.1, ball_subset_ball hR hp'.2⟩)
  have h2 : AnalyticOnNhd ℂ (fun p : (E₁ × E₂) × ℂ => p.2 ^ 2) (V₀ ×ˢ ball (0 : ℂ) Ru) :=
    analyticOnNhd_snd.pow 2
  refine (h2.mul h1).congr (hV₀.prod isOpen_ball) fun p hp' => ?_
  have hu : ‖p.2‖ < Ru := by simpa using hp'.2
  show p.2 ^ 2 * (A (p.1.1, 0) p.2).H y Φ = sqFactor Ru p.2 * (A (p.1.1, 0) p.2).H y Φ
  rw [sqFactor_of_lt hu]

/-- **Holomorphy in `u` of the zero-source family at a fixed parameter.** -/
theorem zeroSourceAct_differentiableOn [Zero E₂]
    {A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {R Ru : ℝ} (hRu : 0 ≤ Ru) (hR : Ru ≤ R)
    (e : E₁ × E₂) {y : Lb} {Φ : ∀ b, Ωb b}
    (h : DifferentiableOn ℂ (fun u => (A (e.1, 0) u).H y Φ) (ball (0 : ℂ) R)) :
    DifferentiableOn ℂ (fun u => (zeroSourceAct A Ru hRu e u).H y Φ) (ball (0 : ℂ) Ru) := by
  have h1 : DifferentiableOn ℂ (fun u : ℂ => u ^ 2 * (A (e.1, 0) u).H y Φ) (ball (0 : ℂ) Ru) :=
    (differentiableOn_id.pow 2).mul (h.mono (ball_subset_ball hR))
  refine h1.congr fun u hu => ?_
  have hu' : ‖u‖ < Ru := by simpa using hu
  rw [zeroSourceAct_H, sqFactor_of_lt hu']

/-- **Continuity in the configuration of the zero-source family.** -/
theorem zeroSourceAct_continuous [Zero E₂] [TopologicalSpace (∀ b, Ωb b)]
    {A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {Ru : ℝ} (hRu : 0 ≤ Ru) (e : E₁ × E₂)
    (u : ℂ) {y : Lb} (h : Continuous ((A (e.1, 0) u).H y)) :
    Continuous ((zeroSourceAct A Ru hRu e u).H y) :=
  continuous_const.mul h

/-- **The exponent identity of the zero-source family.**  If, for real `s ∈ [0,1]`,
`W(s) = s² ∑_y A((e.1, 0), s)_y` almost everywhere, then `W(s) = ∑_y A⁰(e, s)_y` almost
everywhere (`1 < R_u`): the shape of `InterpMarks.hW`. -/
theorem zeroSourceAct_hW [Zero E₂] {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {A : E₁ × E₂ → ℂ → LabelAct Lab Ωb εH κH κ0 Kc} {Ru : ℝ} (hRu0 : 0 ≤ Ru) (hRu : 1 < Ru)
    (e : E₁ × E₂) {W : ℝ → X → ℂ} {restr : X → ∀ b, Ωb b}
    (hW : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = (s : ℂ) ^ 2 * ∑ y, (A (e.1, 0) (s : ℂ)).H y (restr x)) :
    ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ᵐ x ∂ν,
      W s x = ∑ y, (zeroSourceAct A Ru hRu0 e (s : ℂ)).H y (restr x) := by
  intro s hs
  filter_upwards [hW s hs] with x hx
  rw [hx, zeroSourceAct_total, sqFactor_ofReal hRu hs]

end ZeroSource

section Segments

variable {d L N₁ m₁ K : ℕ} [NeZero N₁] [NeZero L] {m₀ j : ℕ} {Ω : Set (CTorus d L N₁ m₁ K)}
variable {Lb₀ Lb₁ : Type*} [Fintype Lb₀] [Fintype Lb₁]
  {Lab₀ : CubeLabels m₀ j Ω Lb₀} {Lab₁ : CubeLabels m₀ j Ω Lb₁}
  {Ωb : CubeB (L := L) (N₁ := N₁) (m₁ := m₁) (K := K) m₀ j Ω → Type*}
  [∀ b, MeasurableSpace (Ωb b)] {ε κH κ0 Kc E2 : ℝ}

/-- **The two-segment identity from the identities of `W₁` and `W₂`.**  Let `A0`, `Ag` be two
families with, at a point `x`, `W₁(s) = s² ∑ A0(s)` and `W₂(t) = ∑ Ag(t) − ∑ A0(t)` for
`s, t ∈ [0,1]`, and `W₂(0) = 0`.  Then for every point `(s, t)` of the two segments
`W₁(s) + W₂(t)` is the label sum of `segAct A0 Ag` (with the factor `s²` on the first segment). -/
theorem segAct_hW_of_parts (A0 : ℂ → LabelAct Lab₀ Ωb ε κH κ0 Kc)
    (Ag : ℂ → LabelAct Lab₁ Ωb ε κH κ0 Kc) (h0 : 0 ≤ ε) (hE : ε + ε ≤ E2)
    {W1 W2 : ℝ → ℂ} {Φ : ∀ b, Ωb b}
    (h1 : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → W1 s = (s : ℂ) ^ 2 * ∑ y, (A0 (s : ℂ)).H y Φ)
    (h2 : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      W2 t = ∑ y, (Ag (t : ℂ)).H y Φ - ∑ y, (A0 (t : ℂ)).H y Φ)
    (h20 : W2 0 = 0) {p : ℝ × ℝ} (hp : p ∈ stepSegments) :
    W1 p.1 + W2 p.2 = ∑ y, (segAct A0 Ag h0 hE
      (fun s => ((if s ∈ Set.Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ)) norm_ite_sq_le p).H y Φ := by
  obtain ⟨hs1, ht1⟩ := mem_Icc_of_mem_stepSegments hp
  obtain ⟨s, t⟩ := p
  by_cases ht : t = 0
  · subst ht
    rw [segAct_total_zero _ _ _ _ _ _ (p := (s, 0)) rfl, h1 s hs1, h20, add_zero]
    simp only [hs1, ite_true]
    push_cast
    rfl
  · have hs : s = 1 := by
      rcases hp with ⟨-, h⟩ | ⟨h, -⟩
      · exact absurd h ht
      · exact h
    subst hs
    rw [segAct_total_ne _ _ _ _ _ _ (p := (1, t)) ht, h1 1 hs1, h2 t ht1]
    simp only [Complex.ofReal_one, one_pow, one_mul]
    ring

end Segments

section PhysPoints

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) {a₁ ν eps q : ℝ}

/-- The zero-source point `(e.1, 0)` of a chart point `e ∈ physV` lies in `physVq … q` for every
`q > 0`. -/
theorem fst_zero_mem_physVq {e : physParam N S} (he : e ∈ physV S a₁ ν eps) (hq : 0 < q) :
    ((e.1, 0) : physParam N S) ∈ physVq S a₁ ν eps q := by
  refine ⟨⟨he.1, ?_⟩, ?_⟩
  · show (0 : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) ∈ l1Ball d L N₁ m₁ (k + 1) N
    simp [l1Ball]
  · simpa using hq

/-- The constant-`h₀` fibre lies in `physVq … 1` (which is `physV`, `physVq_one`); a point `e` of
the fibre lies in `physVq … q` exactly when `∑ |e.2| < q`. -/
theorem physFibre_subset_physVq_one :
    physFibre S a₁ ν eps ⊆ physVq (N := N) S a₁ ν eps 1 := fun _ he => ⟨he.1, he.1.2⟩

/-- A datum `D` of the chart with `D.h ≡ h₀`, together with a source of the open `ℓ¹` ball, is a
point of the constant-`h₀` fibre. -/
theorem mk_mem_physFibre {D : BgData S.G' N} (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < 1) :
    ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈ physFibre S a₁ ν eps :=
  ⟨⟨⟨D, hX, rfl⟩, hg⟩, fun y i => hDh y i⟩

/-- The zero-source point `(e.1, 0)` of a chart point `e ∈ physVRho … ρ` lies in
`physVqRho … ρ q` for `ρ > 0` and `q > 0`. -/
theorem fst_zero_mem_physVqRho {ρ : ℝ} (hρ : 0 < ρ) {e : physParam N S}
    (he : e ∈ physVRho S a₁ ν eps ρ) (hq : 0 < q) :
    ((e.1, 0) : physParam N S) ∈ physVqRho S a₁ ν eps ρ q := by
  refine ⟨⟨he.1, ?_⟩, ?_⟩
  · exact zero_mem_l1BallRho hρ
  · simpa using hq

/-- A datum `D` of the chart with `D.h ≡ h₀`, together with a source of the open `ℓ¹` ball of
radius `ρ`, is a point of the constant-`h₀` fibre at radius `ρ`. -/
theorem mk_mem_physFibreRho {ρ : ℝ} {D : BgData S.G' N} (hDh : ∀ y i, D.h y i = (S.h₀ i : ℂ))
    (hX : XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D)
    {g : CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ} (hg : ∑ x, ∑ i, ‖g x i‖ < ρ) :
    ((⟨rawOf D, rawOf_mem_rawSub _⟩ : rawSub N S.G'), g) ∈ physFibreRho S a₁ ν eps ρ :=
  ⟨⟨⟨D, hX, rfl⟩, hg⟩, fun y i => hDh y i⟩

end PhysPoints

end Balaban.Fluctuation

namespace Balaban.Inhabited

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.Localization Balaban.Localization.LevelPair Balaban.Localization.I5Inhabited
  Balaban.Polymer Balaban.SmallField.Def6 Balaban.Inhabited.LevelStep Filter Topology
  MeasureTheory Set Metric

open Classical in
/-- **The analytic activity family of the source exponent for a given source witness, at source
radius `ρ`.**  The statement of `activityFamilyAnalytic_of_witness` with the carriers `physVqRho`,
`physFibreRho`, `physVRho` of radius `ρ` in place of `physVq`, `physFibre`, `physV`, for
`0 < q ≤ ρ` and `max 1 ρ ≤ β`.  The witness `val, 𝒴, Tt` is the one of
`sourceDirectTerms_scale_fromTower_rho` at the slice `η = q/β`; the amplitude is the same
expression of `q/β` as for `ρ = 1`.  The zero-source part uses `0 ∈ B_ρ` only. -/
theorem activityFamilyAnalytic_of_witness_rho {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β ρ : ℝ) (hβρ : max 1 ρ ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ ρ)
    (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt)
    (hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (q / S.β)) :
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S S.a₁ S.ν T.t ρ q))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β) ∧
            ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
            ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
                  (physVqRho S S.a₁ S.ν T.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam 2 S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit 1 hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physVRho S S.a₁ S.ν T.t ρ ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ u ∈ ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) := by
  classical
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβρ
  have hρ : 0 < ρ := lt_of_lt_of_le hq0 hq
  have hβ0 : 0 < β := by linarith
  have ht0 := T.t_pos
  have hr0 := D.r_pos
  have hQ := cK2'_pos' (B := famConst 3 3 T.BG₂ T.κ) T.fam_nonneg
  have hc1 := one_le_c1 3 3
  have hN3 : 3 ^ 1 ∣ N₁ := by simpa using h3N
  have hR2 : (0 : ℝ) ≤ 2 := by norm_num
  have hSβ : S.β = β := by subst hS; rfl
  have hSa : S.a₁ = 1 := by subst hS; rfl
  have hSp : S.p₁ = p₁ := by subst hS; rfl
  have hβρS : max 1 ρ ≤ S.β := by rw [hSβ]; exact hβρ
  have hH : BgHyp 3 3 (k + 1) (rhoSep T.m₁) (compWeight 3 S.a₁) S.ν := by
    subst hS
    exact bgHyp_lv (k := k) T.m₁ hνpos.le hν
  have hle : S.p₁ ≤ 2 * p₁ := by rw [hSp]; linarith
  -- the sign of the amplitude
  have hεpos : 0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β) := by
    rw [hSβ, hSa, sourceEta_scaled_identity 3 3 2 T.m₁ k 1 1 T.BG T.BG₂ T.κ T.t
      (lvR T.κ T.t (β * 3 ^ k) p₁) q β hβ0.ne']
    refine add_pos_of_nonneg_of_pos (mul_nonneg hβ0.le (div_nonneg ?_ (by positivity))) ?_
    · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
        (pow_nonneg (by positivity) _)) (norm_nonneg _)
    · exact div_pos (mul_pos hq0 (mul_pos hQ ht0)) hr0
  -- the joint representation and the direct terms, chosen once
  obtain ⟨Jr, hJ1, hJ2⟩ := wone_chartIdentity_fromTower_rho T k hk N₁ ν hνpos hν β p₁ hp0 D S hS
  obtain ⟨I, h𝒴, hT⟩ := hI _ hmem0
  have hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
      (physVqRho S S.a₁ S.ν T.t ρ q) :=
    directTermsFamilyOn_scaled_rho S 1 (ρ := ρ) (by rw [h𝒴, hT]; exact hcont) hH hβρS hq
  refine ⟨Jr, I, h𝒴, hT, hF, hεpos.le, hεpos, ?_⟩
  intro Kc hKc
  -- the values of `W₁` and `W₂` on the fibre in terms of `val`
  have hW1val : ∀ e : physParam 2 S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ →
      ∀ x : S.E, ‖x‖ < 2 * p₁ → ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
          ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
        (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
    intro e he x hxn s hs
    obtain ⟨D', hX, hq'⟩ := he.1.1
    have hq'' : (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) = rawOf D' := hq'
    have hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ) := fun y i => by
      have := he.2 y i
      rw [hq''] at this
      exact this
    rw [hq'', hJ1 D' hDh hX x hxn s hs, hval, physInclScaled_zeroClass_eq]
    simp only [hq'', Pi.zero_apply, zero_div, zero_mul, Finset.sum_const_zero, mul_zero, add_zero]
  have hsumval : ∀ e : physParam 2 S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ →
      ∀ x : S.E, ‖x‖ < 2 * p₁ → ∀ s τ : ℝ, s ∈ Icc (0 : ℝ) 1 → τ ∈ Icc (0 : ℝ) 1 →
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
          ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) +
        Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
          ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (τ : ℂ) • S.hatC x) =
        (s : ℂ) ^ 2 * val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (s : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) +
          (val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) -
            val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
              (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0))) := by
    intro e he x hxn s τ hs hτ
    have := @hJ2 0 0 0 Empty Empty _ _ (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun e => e.elim) (fun e => e.elim) (fun _ => ∅) (fun _ => ∅) (fun _ => 0)
      (fun e => e.elim) (fun e => e.elim) (fun _ => ∅) (fun _ => ∅) (fun _ => 0)
      (fun _ => 0) (fun _ => 0) ∅ ∅ (fun τ h => absurd h (by simp))
      (fun τ h => absurd h (by simp)) (fun e => e.elim) (fun e => e.elim)
      (fun τ h => absurd h (by simp)) (fun τ h => absurd h (by simp)) 0 rfl rfl rfl ρ
      e he.1 he.2 x hxn s τ hs hτ
    simp only [physVal_zeroClass_eq] at this
    simp only [hval]
    exact this
  have hW2val : ∀ e : physParam 2 S, e ∈ physFibreRho S S.a₁ S.ν T.t ρ →
      ∀ x : S.E, ‖x‖ < 2 * p₁ → ∀ τ : ℝ, τ ∈ Icc (0 : ℝ) 1 →
      Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
          ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (τ : ℂ) • S.hatC x) =
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) -
          val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) (τ : ℂ)
            (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) (e.1, 0)) := by
    intro e he x hxn τ hτ
    have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
    have h := hsumval e he x hxn 1 τ h1 hτ
    rw [hW1val e he x hxn 1 h1] at h
    exact add_left_cancel h
  -- the label sums at the hat field, at a point `x` where the hat variable is recovered
  have hsum : ∀ x : S.E, S.hatOf 1 p₁ hp ((S.blockSplit 1 hp).restr x) = S.hatC x →
      ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
      ∑ y, (labelActFamilyOn S 1 (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ)) I hF hN3 hp0 hR2
          hεpos.le T.κ0_ent hKc e u).H y ((S.blockSplit 1 hp).restr x) =
        val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
          (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ) e) := by
    intro x hx e he u hu
    rw [labelActFamilyOn_sum S 1 _ hF hN3 hp0 hR2 hεpos.le T.κ0_ent hKc he hu, hx]
  have hW1pt : ∀ x : S.E, S.hatOf 1 p₁ hp ((S.blockSplit 1 hp).restr x) = S.hatC x →
      ‖x‖ < 2 * p₁ → ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
      Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
          ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
        (s : ℂ) ^ 2 * ∑ y, (labelActFamilyOn S 1 (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ)) I hF
          hN3 hp0 hR2 hεpos.le T.κ0_ent hKc ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
          ((S.blockSplit 1 hp).restr x) := by
    intro x hx hxn e he s hs
    rw [hW1val e he x hxn s hs, hsum x hx _ (fst_zero_mem_physVqRho S hρ he.1 hq0) _
      (norm_ofReal_lt_of_mem hs one_lt_two)]
  have hW2pt : ∀ x : S.E, S.hatOf 1 p₁ hp ((S.blockSplit 1 hp).restr x) = S.hatC x →
      ‖x‖ < 2 * p₁ → ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
      ∀ t ∈ Icc (0 : ℝ) 1,
      Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
          ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
        ∑ y, (labelActFamilyOn S 1 (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ)) I hF hN3 hp0 hR2
            hεpos.le T.κ0_ent hKc e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
          ∑ y, (labelActFamilyOn S 1 (physInclScaled 2 S ((1 / S.β : ℝ) : ℂ)) I hF hN3 hp0 hR2
            hεpos.le T.κ0_ent hKc ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
            ((S.blockSplit 1 hp).restr x) := by
    intro x hx hxn e he heq t ht
    rw [hW2val e he x hxn t ht, hsum x hx e ⟨he.1, heq⟩ _ (norm_ofReal_lt_of_mem ht one_lt_two),
      hsum x hx _ (fst_zero_mem_physVqRho S hρ he.1 hq0) _ (norm_ofReal_lt_of_mem ht one_lt_two)]
  have hball : ∀ x : S.E, chiFl S.U 2 S.p₁ x = 1 → ‖x‖ < S.p₁ ∧ ‖x‖ < 2 * p₁ := fun x hχ => by
    have h1 : ‖x‖ < S.p₁ := (chiFl_eq_one_iff hp x).1 hχ
    exact ⟨h1, lt_of_lt_of_le h1 hle⟩
  refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun y Φ => labelActFamilyOn_analytic S 1 _ hF hN3 hp0 hR2 hεpos.le T.κ0_ent hKc y Φ
  · exact fun e he u hu y =>
      labelActFamilyOn_continuous S 1 _ hF hN3 hp0 hR2 hεpos.le T.κ0_ent hKc he hu y
  · exact fun e he u hu Φ =>
      labelActFamilyOn_sum S 1 _ hF hN3 hp0 hR2 hεpos.le T.κ0_ent hKc he hu Φ
  · filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le] with x hx
    exact fun e he u hu => hsum x hx e he u hu
  · filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le, S.ae_ball hp] with x hx hχ
    exact fun e he s hs => hW1pt x hx (hball x hχ).2 e he s hs
  · filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le, S.ae_ball hp] with x hx hχ
    exact fun e he heq t ht => hW2pt x hx (hball x hχ).2 e he heq t ht
  · filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le, S.ae_ball hp] with x hx hχ
    intro D' hDh hX s hs
    rw [← Jr.W1_withDatum (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) D' hDh hX
      (S.abs_mul_le_of_mem hle hs (hball x hχ).1.le)]
    exact hW1pt x hx (hball x hχ).2 _ (mk_mem_physFibreRho S hDh hX (g := 0) (by simpa using hρ)) s hs
  · filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le, S.ae_ball hp] with x hx hχ
    intro D' hDh hX g hg t ht
    rw [← Jr.W2_withDatum (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) D' hDh hX g
      (S.abs_mul_le_of_mem hle ht (hball x hχ).1.le)]
    exact hW2pt x hx (hball x hχ).2 _
      (mk_mem_physFibreRho S hDh hX (lt_of_lt_of_le hg hq)) hg t ht
  · filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le, S.ae_ball hp] with x hx hχ
    intro e he heq p hp'
    have hW20 : Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
        ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), ((0 : ℝ) : ℂ) • S.hatC x) = 0 := by
      obtain ⟨D', hX, hq'⟩ := he.1.1
      have hq'' : (e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2) = rawOf D' := hq'
      have hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ) := fun y i => by
        have := he.2 y i
        rw [hq''] at this
        exact this
      have h := Jr.W2_withDatum (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) D' hDh hX e.2
        (t := 0) (x := x) (by rw [abs_zero, zero_mul]; linarith)
      rw [hq'']
      exact h.trans ((S.withDatum D' hDh).WtwoC_zero _ e.2 x)
    exact segAct_hW_of_parts _ _ _ _
      (W1 := fun s : ℝ => Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
        ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x))
      (W2 := fun t : ℝ => Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
        ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x))
      (fun s hs => hW1pt x hx (hball x hχ).2 e he s hs)
      (fun t ht => hW2pt x hx (hball x hχ).2 e he heq t ht) hW20 hp'
  · exact fun y Φ => zeroSourceAct_analyticOnNhd zero_le_two le_rfl
      (isOpen_physVRho S S.a₁ S.ν T.t ρ hH) (fun e he => fst_zero_mem_physVqRho S hρ he hq0)
      (labelActFamilyOn_analytic S 1 _ hF hN3 hp0 hR2 hεpos.le T.κ0_ent hKc y Φ)
  · exact fun e he u hu y => zeroSourceAct_continuous zero_le_two e u
      (labelActFamilyOn_continuous S 1 _ hF hN3 hp0 hR2 hεpos.le T.κ0_ent hKc
        (fst_zero_mem_physVqRho S hρ he hq0) (by simpa using hu) y)
  · intro D' hDh hX g
    refine zeroSourceAct_hW zero_le_two one_lt_two _ ?_
    intro s hs
    filter_upwards [S.ae_hatOf_restr 1 hp0 hp hSp.le, S.ae_ball hp] with x hx hχ
    rw [← Jr.W1_withDatum (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) D' hDh hX
      (S.abs_mul_le_of_mem hle hs (hball x hχ).1.le)]
    exact hW1pt x hx (hball x hχ).2 _ (mk_mem_physFibreRho S hDh hX (g := 0) (by simpa using hρ)) s hs

open Classical in
/-- **The analytic activity family of the source exponent for a given source witness.**  Let
`val, 𝒴, Tt` be the witness of `sourceDirectTerms_scale_fromTower` at the slice `η = q/β` (the
formula for `val`, diagonal continuity of `𝒴, Tt`, an instance with domains `𝒴` and terms `Tt` at
every point of the slice, and the central point `(rawOf S.D', 0)` in the slice).  Then there are a
joint representation `Jr`, a `DirectTerms` record `I` at the central point with `I.𝒴 = 𝒴`,
`I.T = Tt`, and a relative family `hF` over `physVq … q`, such that the amplitude is positive and,
for every `K_c ≥ K₀(T.κ0)`, the family `A = labelActFamilyOn … I hF` has the properties 1–12 listed
for `activityFamilyAnalytic_fromTower`.  `activityFamilyAnalytic_fromTower` is this theorem applied
to one call of the producer, together with the amplitude bound. -/
theorem activityFamilyAnalytic_of_witness {κmin : ℝ} (T : StepTower κmin)
    (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁)
    (ν : ℝ) (hνpos : 0 < ν) (hν : ν * 3 ^ (2 * (k + 1)) ≤ 1) (β : ℝ) (hβ1 : 1 ≤ β)
    (p₁ : ℝ) (hp0 : 0 < p₁) (q : ℝ) (hq0 : 0 < q) (hq : q ≤ 1)
    (D : StepScaleData T k hk N₁ ν β p₁)
    (S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) (hS : S = T.step k hk N₁ ν β p₁)
    (hp : 0 < S.p₁)
    (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
    (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
    (hval : ∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1))
    (hcont : DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt)
    (hI : ∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt)
    (hmem0 : (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) ∈
      physSΛEta S S.a₁ S.ν T.t (q / S.β)) :
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t q))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β) ∧
            ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
            ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
                  (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam 2 S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit 1 hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) := by
  classical
  exact activityFamilyAnalytic_of_witness_rho T k hk N₁ h3N ν hνpos hν β 1
    (by rw [max_self]; exact hβ1) p₁ hp0 q hq0 hq D S hS hp val 𝒴 Tt hval hcont hI hmem0

open Classical in
/-- **The analytic activity family of the source exponent at the shared tower, at source radius
`ρ`.**  The statement of `activityFamilyAnalytic_fromTower` with the carriers `physVqRho`,
`physFibreRho`, `physVRho` of radius `ρ`, for `0 < q ≤ ρ` and `max 1 ρ ≤ β`.  The threshold `β₀`
and the amplitude constants `C_E`, `C_F` are chosen after `T` and do not depend on `ρ`; the
amplitude bound is `4 ε_U ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k`, linear in the
source size `q ≤ ρ`.  Clauses 1–12 are those of `activityFamilyAnalytic_fromTower` on the
carriers of radius `ρ`. -/
theorem activityFamilyAnalytic_fromTower_rho {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β → ∀ ρ : ℝ, max 1 ρ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ ρ →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          PhysicalSharpLocEta S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁) S.a₁
            S.ν T.t (q / S.β) 𝒴 Tt ∧
          DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
          (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt) ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVqRho S S.a₁ S.ν T.t ρ q))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β) ∧
            4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                  q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
            ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
            ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
                  (physVqRho S S.a₁ S.ν T.t ρ q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVqRho S S.a₁ S.ν T.t ρ q, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibreRho S S.a₁ S.ν T.t ρ, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam 2 S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit 1 hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physVRho S S.a₁ S.ν T.t ρ ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVRho S S.a₁ S.ν T.t ρ, ∀ u ∈ ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) := by
  classical
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, hfam⟩ := sourceFamilyRelative_scale_fromTower_rho T hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ ρ hβρ p₁ hp0 hp₁ q hq0 hq D S hS hp
  have hβ1 : 1 ≤ β := (le_max_left _ _).trans hβρ
  have hρ : 0 < ρ := lt_of_lt_of_le hq0 hq
  obtain ⟨_, _, _, _, _, _, _, _, _, hε4, _⟩ := hfam k hk N₁ h3N hN ν hνpos hν β hβ ρ hβρ p₁ hp0
    hp₁ q hq0 hq D S hS hp
  obtain ⟨val, 𝒴, Tt, hval, hloc, hcont, hI, hmem0, -⟩ := sourceDirectTerms_scale_fromTower_rho T k
    hk N₁ h3N hN ν hνpos hν β ρ hρ hβρ p₁ q hq0 hq D S hS hp
  obtain ⟨Jr, I, h𝒴, hT, hF, hεU, hεpos, H⟩ := activityFamilyAnalytic_of_witness_rho T k hk N₁ h3N
    ν hνpos hν β ρ hβρ p₁ hp0 q hq0 hq D S hS hp val 𝒴 Tt hval hcont hI hmem0
  exact ⟨Jr, val, 𝒴, Tt, I, h𝒴, hT, hval, hloc, hcont, hI, hF, hεU, hεpos, hε4, H⟩

open Classical in
/-- **The analytic activity family of the source exponent at the shared tower, with its value and
its `W` identities.**  After the tower `T` choose `β₀, C_E, C_F`.  For every scale, torus, mass,
`β ≥ β₀`, cutoff `0 < p₁ ≤ A₁ (log β_k)^p`, source radius `0 < q ≤ 1` and per-scale package, at the
step `S = T.step k hk N₁ ν β p₁` there is **one** choice of a joint representation `Jr`, the
expanded function `val`, the domains `𝒴`, the terms `Tt`, a `DirectTerms` record `I` at the central
point `(rawOf S.D', 0)` and the relative family `hF` over `physVq … q` such that:

* (same witness as `sourceDirectTerms_scale_fromTower`) `I.𝒴 = 𝒴`, `I.T = Tt`, the formula for
  `val`, sharp locality and diagonal continuity of `𝒴, Tt` on the slice `q/β`, and an instance with
  domains `𝒴` and terms `Tt` at every point of the slice;
* the amplitude `ε_U = β · prop33EpsEtaScaled … (q/β)` is positive and
  `4 ε_U ≤ C_E (log β_k)^{3p}/√β_k + q C_F (log β_k)^p/√β_k`;
* for every `K_c ≥ K₀(T.κ0)`, the family `A = labelActFamilyOn … I hF` (labels
  `thickLabels I.𝒴 I.dom`, amplitude `2 ε_U`, rate `2 κ_dec - 1`, `κ₀ = T.κ0`) satisfies
  1. `(e, u) ↦ A(e, u)_y(Φ)` is analytic on `physVq … q × ball 0 2`, for every label and
     configuration;
  2. `Φ ↦ A(e, u)_y(Φ)` is continuous for `e ∈ physVq … q`, `‖u‖ < 2`;
  3. (value) `∑_y A(e, u)_y(Φ) = val (ψ̂_Φ, ψ̂_Φ) (ψ̂_Φ, ψ̂_Φ) u (e.1, e.2/β)` for `e ∈ physVq … q`,
     `‖u‖ < 2`, `ψ̂_Φ` the clamped hat field of `Φ`;
  4. almost everywhere, for all such `e, u`, the same at the block variables of `ψ̂` with `ψ̂_Φ = ψ̂`;
  5. (`W₁` on the fibre) almost everywhere, for every `e` of the fibre `h ≡ h₀` and `s ∈ [0,1]`,
     `Jr.W1 (e.1, s ψ̂) = s² ∑_y A((e.1, 0), s)_y`;
  6. (`W₂` on the fibre) almost everywhere, for every `e` of the fibre with `∑ |e.2| < q` and
     `t ∈ [0,1]`, `Jr.W2 e.2 (e.1, t ψ̂) = ∑_y A(e, t)_y − ∑_y A((e.1, 0), t)_y`;
  7. (slice, `W₁`) almost everywhere, for every datum `D` of the chart with `D.h ≡ h₀` and
     `s ∈ [0,1]`, `(S.withDatum D).WoneC s ψ̂ = s² ∑_y A((rawOf D, 0), s)_y`;
  8. (slice, `W₂`) almost everywhere, for every such `D`, every source `∑ |g| < q` and `t ∈ [0,1]`,
     `(S.withDatum D).WtwoC g t ψ̂ = ∑_y A((rawOf D, g), t)_y − ∑_y A((rawOf D, 0), t)_y`.

  9. (both segments) almost everywhere, for every `e` of the fibre with `∑ |e.2| < q` and every
     point `(s, t)` of `stepSegments`, `Jr.W1 (e.1, s ψ̂) + Jr.W2 e.2 (e.1, t ψ̂)` is the label sum
     of `segAct (A (e.1, 0)) (A e)` at `(s, t)` (labels `thickLabels.sum thickLabels`): the
     activity of `sourceExponentFamily_fromTower` as `segAct` of the one analytic family.

  10. (zero-source family, `holA`) for `A⁰ = zeroSourceAct A 2`, that is
     `A⁰(e, u) = u² A((e.1, 0), u)` for `‖u‖ < 2`: `(e, u) ↦ A⁰(e, u)_y(Φ)` is analytic on
     `physV × ball 0 2` (all of `physV`), for every label and configuration;
  11. (zero-source family, `contA`) `Φ ↦ A⁰(e, u)_y(Φ)` is continuous for `e ∈ physV`, `‖u‖ < 2`;
  12. (zero-source family, `hW`) for every datum `D` of the chart with `D.h ≡ h₀`, every source
     coordinate `g` and `s ∈ [0,1]`: `(S.withDatum D).WoneC s ψ̂ = ∑_y A⁰((rawOf D, g), s)_y` almost
     everywhere (the shape of `InterpMarks.hW`).

In 4–9 "almost everywhere" is `ν_{p₁}`-almost every `ψ̂`, with one null set for all the other
variables.  At `D = S.D'` the step `S.withDatum D` is `S` (`withDatum_self`). -/
theorem activityFamilyAnalytic_fromTower {κmin : ℝ} (T : StepTower κmin) {A₁ : ℝ}
    (hA : 0 < A₁) (p : ℕ) :
    ∃ (β₀ CE CF : ℝ), 2 ≤ β₀ ∧ 0 < CE ∧ 0 < CF ∧
      ∀ (k : ℕ) (hk : 1 ≤ k) (N₁ : ℕ) [NeZero N₁] (h3N : 3 ∣ N₁), 5 < N₁ →
      ∀ ν : ℝ, 0 < ν → ν * 3 ^ (2 * (k + 1)) ≤ 1 → ∀ β : ℝ, β₀ ≤ β →
      ∀ p₁ : ℝ, ∀ hp0 : 0 < p₁, p₁ ≤ pLog A₁ p (β * 3 ^ k) → ∀ q : ℝ, 0 < q → q ≤ 1 →
      StepScaleData T k hk N₁ ν β p₁ →
      ∀ S : StepSetting 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁),
        S = T.step k hk N₁ ν β p₁ → ∀ hp : 0 < S.p₁,
      ∃ (Jr : S.JointRep T.t (2 * p₁))
          (val : ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ℂ → (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (𝒴 : Finset (Set (CTorus 3 3 N₁ T.m₁ (k + 1))))
          (Tt : Set (CTorus 3 3 N₁ T.m₁ (k + 1)) → ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) →
            ((S.U × Fin 2 → ℂ) × (S.U × Fin 2 → ℂ)) → ℂ →
            (RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2 × (CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) → ℂ)
          (I : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1)
                (rawOf S.D', (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ))
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S)),
          I.𝒴 = 𝒴 ∧ I.T = Tt ∧
          (∀ x w σ Θ, val x w σ Θ =
            (-(S.β : ℂ)) * raySrc3 (hatFun S.G' S.a₁ S.ν T.t S.hG'
              ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
              (interactionOne S.hG S.hG' (le_refl (k + 1)) S.a₁ S.ν T.t)) taylorWeight x.1 w.1 σ
                Θ.1 +
            (S.β : ℂ) * (∑ s : CTorus 3 3 N₁ T.m₁ (k + 1) × Fin 2, Θ.2 s.1 s.2 *
              dirTermSrc (hatFun S.G' S.a₁ S.ν T.t S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
                (onXi S.G' S.a₁ S.ν T.t
                  (fun D ψ' => svec (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁))
                    (flFieldOne S.G' (stepG 3 3 N₁ T.m₁ k (rhoSep T.m₁)) T.BG₂ T.κ S.a₁ S.ν D ψ')
                      s.1 s.2)))
                (fun _ => (1 : ℂ)) x.2 w.2 σ Θ.1)) ∧
          PhysicalSharpLocEta S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁) S.a₁
            S.ν T.t (q / S.β) 𝒴 Tt ∧
          DiagCont (fun ψ : S.U × Fin 2 → ℂ => (ψ, ψ))
            (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁))
            (physSΛEta S S.a₁ S.ν T.t (q / S.β)) 2 𝒴 Tt ∧
          (∀ Θ ∈ physSΛEta S S.a₁ S.ν T.t (q / S.β),
            ∃ I' : DirectTerms S 1 hp (fun ψ => (ψ, ψ)) p₁ 2
                (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) (2 * T.κdec - 1) Θ
                (physSΛEta S S.a₁ S.ν T.t (q / S.β))
                (physXW S (lvCpsi T.κ T.t (β * 3 ^ k)) 2 2 (lvR T.κ T.t (β * 3 ^ k) p₁)) val
                (physAgΘ S) (AgFDirPair S),
              I'.𝒴 = 𝒴 ∧ I'.T = Tt) ∧
          ∃ (hF : DirectTermsFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I
              (physVq S S.a₁ S.ν T.t q))
            (hεU : 0 ≤ S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)),
            0 < S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β) ∧
            4 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β)) ≤
                CE * (Real.log (β * 3 ^ k)) ^ (3 * p) / Real.sqrt (β * 3 ^ k) +
                  q * CF * (Real.log (β * 3 ^ k)) ^ p / Real.sqrt (β * 3 ^ k) ∧
            ∀ {Kc : ℝ} (hKc : K0 3 3 T.κ0 ≤ Kc),
            ∃ A : physParam 2 S → ℂ → LabelAct (thickLabels I.𝒴 I.dom) (S.blockSplit 1 hp).Ωb
                (2 * (S.β * prop33EpsEtaScaled 3 3 2 T.m₁ k 1 S.a₁ T.BG T.BG₂ T.κ T.t
                  (lvR T.κ T.t (β * 3 ^ k) p₁) 0 0 (q / S.β))) (2 * T.κdec - 1) T.κ0 Kc,
              A = labelActFamilyOn S 1 (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ)) I hF
                    (show 3 ^ 1 ∣ N₁ by simpa using h3N) hp0 (by norm_num) hεU T.κ0_ent hKc ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ => (A r.1 r.2).H y Φ)
                  (physVq S S.a₁ S.ν T.t q ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 → ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((A e u).H y)) ∧
              (∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∀ Φ : ∀ b, (S.blockSplit 1 hp).Ωb b,
                ∑ y, (A e u).H y Φ =
                  val (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ)
                    (S.hatOf 1 p₁ hp Φ, S.hatOf 1 p₁ hp Φ) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physVq S S.a₁ S.ν T.t q, ∀ u : ℂ, ‖u‖ < 2 →
                ∑ y, (A e u).H y ((S.blockSplit 1 hp).restr x) =
                  val (S.hatC x, S.hatC x) (S.hatC x, S.hatC x) u
                    (physInclScaled 2 S (((1 / S.β : ℝ)) : ℂ) e)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∀ s ∈ Icc (0 : ℝ) 1,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (s : ℂ) • S.hatC x) =
                  (s : ℂ) ^ 2 * ∑ y, (A ((e.1, 0) : physParam 2 S) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ t ∈ Icc (0 : ℝ) 1,
                Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (t : ℂ) • S.hatC x) =
                  ∑ y, (A e (t : ℂ)).H y ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((e.1, 0) : physParam 2 S) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ s ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                  (s : ℂ) ^ 2 * ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                    (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (s : ℂ)).H y
                    ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' →
                ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2, ∑ x', ∑ i, ‖g x' i‖ < q → ∀ t ∈ Icc (0 : ℝ) 1,
                (S.withDatum D' hDh).WtwoC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) g t x =
                  ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x) -
                    ∑ y, (A ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'),
                      (0 : CTorus 3 3 N₁ T.m₁ (k + 1) → Fin 2 → ℂ)) (t : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) ∧
              (∀ᵐ x ∂S.nuFl, ∀ e ∈ physFibre S S.a₁ S.ν T.t, ∑ x', ∑ i, ‖e.2 x' i‖ < q →
                ∀ p ∈ stepSegments,
                Jr.W1 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁))
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.1 : ℂ) • S.hatC x) +
                  Jr.W2 (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) e.2
                    ((e.1 : RawData 3 3 (N₁ * 3 ^ T.m₁) (k + 1) 2), (p.2 : ℂ) • S.hatC x) =
                  ∑ y, (segAct (A ((e.1, 0) : physParam 2 S)) (A e)
                    (mul_nonneg zero_le_two hεU) (two_mul _).ge
                    (fun s => ((if s ∈ Icc (0 : ℝ) 1 then s ^ 2 else 0 : ℝ) : ℂ))
                    norm_ite_sq_le p).H y ((S.blockSplit 1 hp).restr x)) ∧
              (∀ (y : {Y // Y ∈ I.𝒴}) (Φ : ∀ b, (S.blockSplit 1 hp).Ωb b),
                AnalyticOnNhd ℂ (fun r : physParam 2 S × ℂ =>
                  (zeroSourceAct A 2 zero_le_two r.1 r.2).H y Φ)
                  (physV S S.a₁ S.ν T.t ×ˢ ball (0 : ℂ) 2)) ∧
              (∀ e ∈ physV S S.a₁ S.ν T.t, ∀ u ∈ ball (0 : ℂ) 2, ∀ y : {Y // Y ∈ I.𝒴},
                Continuous ((zeroSourceAct A 2 zero_le_two e u).H y)) ∧
              (∀ (D' : BgData S.G' 2) (hDh : ∀ y i, D'.h y i = (S.h₀ i : ℂ)),
                XiCData S.G' S.a S.ν (k + 1) 1 T.t D' → ∀ g : Fld 3 3 N₁ T.m₁ (k + 1) 2,
                ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 → ∀ᵐ x ∂S.nuFl,
                  (S.withDatum D' hDh).WoneC (zeroClass 3 3 N₁ T.m₁ k 2 (rhoSep T.m₁)) s x =
                    ∑ y, (zeroSourceAct A 2 zero_le_two
                      ((⟨rawOf D', rawOf_mem_rawSub _⟩ : rawSub 2 S.G'), g) (s : ℂ)).H y
                      ((S.blockSplit 1 hp).restr x)) := by
  classical
  obtain ⟨β₀, CE, CF, hβ₀, hCE, hCF, h⟩ := activityFamilyAnalytic_fromTower_rho T hA p
  refine ⟨β₀, CE, CF, hβ₀, hCE, hCF, ?_⟩
  intro k hk N₁ _ h3N hN ν hνpos hν β hβ p₁ hp0 hp₁ q hq0 hq D S hS hp
  exact h k hk N₁ h3N hN ν hνpos hν β hβ 1 (by rw [max_self]; linarith) p₁ hp0 hp₁ q hq0 hq D S
    hS hp

end Balaban.Inhabited
