/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedCubicTaylor
public import Balaban.Fluctuation.MarkedEvJoint

/-!
# Joint analyticity of the marked cubic block terms in (datum, marks) (`MarkedCubicJoint`)

`MarkedCubicTaylor` proves, at a fixed datum `Θ` and a fixed radial mark `u`, that the marked block
term `t ↦ P(Θ, v_t) = ∫₀¹ ω(s) D³Ev(Θ, s v_t)[v_t]³ ds` (`markedBlockTerm`) is analytic on `|t| < t₁`
and that its `t`-derivative at `0` is at most `3 b / (r³ t₀)`.  This file proves the family
statement of the note `MARKPARAM` (leaf `markedCubic_joint_param`): the term is analytic jointly in
the datum and both marks.

* `analyticOnNhd_deriv_last`: the derivative in the last complex variable at `0` of a jointly
  analytic function is analytic in the remaining variables.
* `analyticOnNhd_rayTerm_dl3_param`, `analyticOnNhd_markedBlockTerm_param`: for a functional `Ev`
  analytic on `S × B` and analytic families `q ↦ Θ(q) ∈ S`, `q ↦ w(q)` on an open set `V` with
  `σ w(q) ∈ B` for `|σ| < R₁ + r`, the cubic Taylor term `q ↦ ∫₀¹ ω(s) D³Ev(Θ(q), s w(q))[w(q)]³ ds`
  is analytic on `V` (the third directional derivative is the third `σ`-derivative of the jointly
  analytic `(σ, q) ↦ Ev(Θ(q), σ w(q))`; then differentiation under the compact `s`-integral,
  `analyticOnNhd_unitIntegral`).
* `hatCovSqrt_coord_le`, `exists_analytic_hatCovSqrt_bdd`, `analyticOnNhd_smul_mulVec`,
  `exists_analytic_hatField_chart`, `exists_analytic_shiftUC_chart`: the unit field
  `cc • C^{1/2}(Θ) ψ̂` as a function of the raw data (one matrix function `M` for all hat fields),
  analytic on the chart (jointly with the hat field), equal to `hatCovSqrt` (to `shiftUC` of the
  step with the datum, on the fibre `h = h₀`) at every datum of the chart, and bounded there:
  Euclidean norm at most `markedRad = √N · |cc| · C_sup · c_ψ` at every unit point (the coordinate
  bound of the landed `hatSqrtF_coord_le` at the cut point `s ≡ 1`).
* `markedDisc_field_mem_flBall`, `norm_deriv_markedBlockTerm_field_le`,
  `markedBlockTerm_family_withDatum`: the discs of formula (2) of `MARKCUBIC` and the Cauchy
  estimate for an arbitrary unit field `y` in place of `shiftUC ψ̂`; on the fibre `h = h₀` the term
  of the family is the landed marked term of the step with the datum.
* `markedBlockTerm_joint_family`, `deriv_markedBlockTerm_analytic_family`: for an open set `V₀` of
  a parameter space, analytic families `p ↦ Θ(p)` (in the analytic region of `Ev`) and `p ↦ y(p)`
  (unit fields of Euclidean norm at most `Y₀`) and the radial margin `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`:
  the marked term along `v_t(p, u) = u · y(p) + t · M_z y(p)` is analytic in `((p, u), t)` on
  `(V₀ × {|u| < R_σ}) × {|t| < t₁}`, and its `t`-derivative at `0` is analytic in `(p, u)`.
* `markedCubic_joint_physV`: the case `V₀ = physV`, `Θ(e) = e.1`, `y(e) = Q(e.1)`.
* `markedCubic_joint_param`: for the terms `E_{b,Y}` of `vblock_expansion_scaled` (one family `Ev`,
  with its four landed clauses): joint analyticity on `(physV × {|u| < R_σ}) × {|t| < t₁}`,
  analyticity of the derivative marks, and the bound
  `3 E* e^{-2 κ_dec d(Y)} / (r³ t₀)` for each old block.

Zero class only.  The root assembly (the sum over old blocks and labels, the factor `-β`, the
anchoring at the root), the clamped global marks, the common label system and the `E1MarksC`
inhabitant are NOT constructed here; no mark family is constructed.  Nothing depends on a choice of
generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Finset Set Matrix Metric

section Abstract

variable {Λ : Type*} [NormedAddCommGroup Λ] [NormedSpace ℂ Λ]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
variable {Q : Type*} [NormedAddCommGroup Q] [NormedSpace ℂ Q]

/-- **The derivative in the last variable of a jointly analytic function.**  If `f (x, t)` is
analytic at every point of `A × T` and `0 ∈ T`, then `x ↦ ∂_t f (x, t)|_{t=0}` is analytic at every
point of `A` (it is a directional derivative of `f`). -/
theorem analyticOnNhd_deriv_last {A : Set Q} {T : Set ℂ} {f : Q × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (A ×ˢ T)) (h0 : (0 : ℂ) ∈ T) :
    AnalyticOnNhd ℂ (fun x : Q => deriv (fun t : ℂ => f (x, t)) 0) A := by
  intro a ha
  have h0' : AnalyticAt ℂ (lineD ((0 : Q), (1 : ℂ)) f) (a, 0) :=
    analyticAt_lineD _ (hf _ ⟨ha, h0⟩)
  have hm : AnalyticAt ℂ (fun x : Q => ((x, (0 : ℂ)) : Q × ℂ)) a :=
    analyticAt_id.prod analyticAt_const
  have e : (fun x : Q => deriv (fun t : ℂ => f (x, t)) 0) =
      fun x : Q => lineD ((0 : Q), (1 : ℂ)) f (x, 0) := by
    funext x
    unfold lineD
    congr 1
    funext t
    congr 1
    ext <;> simp
  rw [e]
  exact h0'.comp_of_eq hm rfl

variable {S : Set Λ} {B : Set F} {Ev : Λ × F → ℂ} {ω : ℂ → ℂ} {R₁ r : ℝ}
  {V : Set Q} {Θf : Q → Λ} {wf : Q → F}

/-- The function `(σ, q) ↦ Ev(Θ(q), σ w(q))` is analytic at `(σ, q)` for `q ∈ V`, `‖σ‖ < R₁ + r`,
when `Θ`, `w` are analytic on `V`, `Θ(q) ∈ S` and the disc `σ w(q)` stays in `B`. -/
theorem analyticAt_param_H (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B)) (hΘ : AnalyticOnNhd ℂ Θf V)
    (hw : AnalyticOnNhd ℂ wf V) (hmem : ∀ q ∈ V, Θf q ∈ S)
    (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • wf q ∈ B) {x : ℂ × Q}
    (hx1 : ‖x.1‖ < R₁ + r) (hx2 : x.2 ∈ V) :
    AnalyticAt ℂ (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2)) x := by
  have hm : AnalyticAt ℂ (fun x : ℂ × Q => ((Θf x.2, x.1 • wf x.2) : Λ × F)) x :=
    AnalyticAt.prod ((hΘ x.2 hx2).comp analyticAt_snd)
      (analyticAt_fst.smul ((hw x.2 hx2).comp analyticAt_snd))
  exact (hEv _ ⟨hmem x.2 hx2, hdom x.2 hx2 x.1 hx1⟩).comp_of_eq hm rfl

/-- The third directional derivative of `Ev` at `s w(q)` in the direction `w(q)` is the third
`σ`-derivative of `(σ, q) ↦ Ev(Θ(q), σ w(q))` at `σ = s`. -/
theorem dirL3_param_eq (hr : 0 < r) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : AnalyticOnNhd ℂ Θf V) (hw : AnalyticOnNhd ℂ wf V) (hmem : ∀ q ∈ V, Θf q ∈ S)
    (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • wf q ∈ B) {q : Q} (hq : q ∈ V) {s : ℂ}
    (hs : ‖s‖ < R₁) :
    dirL3 Ev (wf q) (Θf q) (s • wf q) =
      (lineD ((1 : ℂ), (0 : Q)))^[3] (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2)) (s, q) := by
  have hr' : ∀ τ : ℂ, ‖τ‖ < r → ‖s + τ‖ < R₁ + r := fun τ hτ =>
    (norm_add_le _ _).trans_lt (add_lt_add hs hτ)
  have hf : ∀ τ : ℂ, ‖τ‖ < r → AnalyticAt ℂ Ev (Θf q, s • wf q + τ • wf q) := fun τ hτ => by
    rw [← add_smul]
    exact hEv _ ⟨hmem q hq, hdom q hq _ (hr' τ hτ)⟩
  rw [dirL3_eq hr hf]
  unfold dirS3
  have e : (fun τ : ℂ => Ev (Θf q, s • wf q + τ • wf q)) =
      fun τ : ℂ => (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2))
        ((s, q) + τ • ((1 : ℂ), (0 : Q))) := by
    funext τ
    have h2 : ((s, q) + τ • ((1 : ℂ), (0 : Q)) : ℂ × Q) = (s + τ, q) := by ext <;> simp
    rw [h2]
    show Ev (Θf q, s • wf q + τ • wf q) = Ev (Θf q, (s + τ) • wf q)
    rw [add_smul]
  rw [e]
  have := iteratedDeriv_line (E := ℂ × Q) (s, q) ((1 : ℂ), (0 : Q)) (r := r) 3
    (fun x : ℂ × Q => Ev (Θf x.2, x.1 • wf x.2))
    (fun τ hτ => analyticAt_param_H hEv hΘ hw hmem hdom (by simpa using hr' τ hτ)
      (by simpa using hq)) 0 (by simpa using hr)
  simpa using this

/-- **The cubic Taylor term is analytic in a parameter.**  Let `Ev` be analytic on `S × B`, `V` an
open set of a parameter space, `q ↦ Θ(q)` and `q ↦ w(q)` analytic on `V` with `Θ(q) ∈ S` and
`σ w(q) ∈ B` for `‖σ‖ < R₁ + r` (`R₁ > 1`, `r > 0`), and `ω` analytic on `‖σ‖ < R₁`.  Then
`q ↦ ∫₀¹ ω(s) D³Ev(Θ(q), s w(q))[w(q), w(q), w(q)] ds` is analytic on `V`. -/
theorem analyticOnNhd_rayTerm_dl3_param (hV : IsOpen V) (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    (hΘ : AnalyticOnNhd ℂ Θf V) (hw : AnalyticOnNhd ℂ wf V) (hmem : ∀ q ∈ V, Θf q ∈ S)
    (hdom : ∀ q ∈ V, ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • wf q ∈ B) :
    AnalyticOnNhd ℂ (fun q => rayTerm (dl3 Ev (wf q)) ω (wf q) 1 (Θf q)) V := by
  set H : ℂ × Q → ℂ := fun x => Ev (Θf x.2, x.1 • wf x.2) with hHdef
  have hK : ∀ x : ℂ × Q, ‖x.1‖ < R₁ + r → x.2 ∈ V →
      AnalyticAt ℂ ((lineD ((1 : ℂ), (0 : Q)))^[3] H) x := by
    intro x h1 h2
    exact analyticAt_lineD _ (analyticAt_lineD _ (analyticAt_lineD _
      (analyticAt_param_H hEv hΘ hw hmem hdom h1 h2)))
  have hint : AnalyticOnNhd ℂ (fun q : Q => ∫ s in (0 : ℝ)..1,
      ω (s : ℂ) * ((lineD ((1 : ℂ), (0 : Q)))^[3] H) ((s : ℂ), q)) V := by
    refine analyticOnNhd_unitIntegral (f := fun (q : Q) (s : ℂ) =>
      ω s * ((lineD ((1 : ℂ), (0 : Q)))^[3] H) (s, q)) hR₁ ?_
    rintro ⟨q, s⟩ ⟨hq, hs⟩
    have hs' : ‖s‖ < R₁ := mem_ball_zero_iff.1 hs
    have hm : AnalyticAt ℂ (fun p : Q × ℂ => (p.2, p.1)) (q, s) :=
      analyticAt_snd.prod analyticAt_fst
    exact ((hω s hs).comp (analyticAt_snd (𝕜 := ℂ))).mul
      ((hK (s, q) (by simp only; linarith) hq).comp_of_eq hm rfl)
  refine hint.congr hV fun q hq => ?_
  unfold rayTerm
  rw [one_mul]
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le zero_le_one] at hs
  have hs' : ‖(s : ℂ)‖ < R₁ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]; linarith [hs.2]
  rw [dl3_apply, one_mul, dirL3_param_eq hr hEv hΘ hw hmem hdom hq hs']

/-- **The marked term is analytic jointly in a parameter and the mark.**  Let `Ev` be analytic on
`S × B`, `V₀` an open set of a parameter space, and `p ↦ Θ(p) ∈ S`, `p ↦ a(p)`, `p ↦ c(p)` analytic
on `V₀`, with the discs `σ (a(p) + t c(p))`, `‖σ‖ < R₁ + r`, `‖t‖ < t₁`, in `B`.  Then
`(p, t) ↦ P(Θ(p), a(p) + t c(p))` (`markedBlockTerm`) is analytic on `V₀ × {‖t‖ < t₁}`. -/
theorem analyticOnNhd_markedBlockTerm_param {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    {V₀ : Set P} (hV₀ : IsOpen V₀) {t₁ : ℝ} (hR₁ : 1 < R₁) (hr : 0 < r)
    (hω : AnalyticOnNhd ℂ ω (ball (0 : ℂ) R₁)) (hEv : AnalyticOnNhd ℂ Ev (S ×ˢ B))
    {Θp : P → Λ} {af cf : P → F} (hΘ : AnalyticOnNhd ℂ Θp V₀) (ha : AnalyticOnNhd ℂ af V₀)
    (hc : AnalyticOnNhd ℂ cf V₀) (hmem : ∀ p ∈ V₀, Θp p ∈ S)
    (hdom : ∀ p ∈ V₀, ∀ t : ℂ, ‖t‖ < t₁ → ∀ σ : ℂ, ‖σ‖ < R₁ + r → σ • (af p + t • cf p) ∈ B) :
    AnalyticOnNhd ℂ (fun x : P × ℂ => markedBlockTerm Ev ω (af x.1) (cf x.1) (Θp x.1) x.2)
      (V₀ ×ˢ ball (0 : ℂ) t₁) := by
  have hΘ' : AnalyticOnNhd ℂ (fun x : P × ℂ => Θp x.1) (V₀ ×ˢ ball (0 : ℂ) t₁) :=
    fun x hx => (hΘ x.1 hx.1).comp analyticAt_fst
  have hw' : AnalyticOnNhd ℂ (fun x : P × ℂ => af x.1 + x.2 • cf x.1) (V₀ ×ˢ ball (0 : ℂ) t₁) :=
    fun x hx => ((ha x.1 hx.1).comp analyticAt_fst).add
      (analyticAt_snd.smul ((hc x.1 hx.1).comp analyticAt_fst))
  have key := analyticOnNhd_rayTerm_dl3_param (hV₀.prod isOpen_ball) hR₁ hr hω hEv hΘ' hw'
    (fun x hx => hmem x.1 hx.1)
    (fun x hx σ hσ => hdom x.1 hx.1 x.2 (mem_ball_zero_iff.1 hx.2) σ hσ)
  exact key

end Abstract

end Balaban.Fluctuation

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section HatField

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ}

/-- **Coordinate bound of the unit field at the cut point `s ≡ 1`**: for a datum `D` of the chart and
`|ψ̂| ≤ c_ψ`, every coordinate of `cc • C^{1/2}(1) ψ̂` (`hatCovSqrt`) is at most
`|cc| · C_sup · c_ψ` (`hatSqrtF_coord_le` at `s ≡ 1`). -/
theorem hatCovSqrt_coord_le (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁) (hk : 1 ≤ k)
    (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) {D : BgData Gp N}
    (hD : XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D) {ψh : unitPts Gp × Fin N → ℂ}
    (hψh : ∀ p, ‖ψh p‖ ≤ cψ) (q : unitPts Gp × Fin N) :
    ‖(cc • (hatCovSqrt Gp a₁ ν D *ᵥ ψh)) q‖ ≤
      ‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ) := by
  obtain ⟨F₁, -, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  have hs : ∀ P, ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ := fun P => by
    simpa using hE1
  have h := hatSqrtF_coord_le hC hk cc hcψ hMX hdm hα hsm hF₁ hs hD hψh q
  rwa [hatSqrtF_one_apply hC hF₁ hD] at h

/-- **The square root `C^{1/2}` as an analytic function of the raw data, with the bound of the unit
fields on the whole chart.**  There is one matrix-valued function `M` of the raw data, with entries
analytic at every point of `Ξ^c(𝔹_{k+1}; 1, ε)`, equal to `hatCovSqrt D` at every datum `D` of the
chart (complex `h` included; the function of `exists_analytic_hatCovSqrt`), such that for every
factor `cc`, every hat field `|ψ̂| ≤ c_ψ` and every point `Θ` of the chart the unit field
`cc • M(Θ) ψ̂` has Euclidean norm at most `markedRad = √N · |cc| · C_sup · c_ψ` at every unit
point.  One `M` serves all hat fields. -/
theorem exists_analytic_hatCovSqrt_bdd (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) :
    ∃ M : RawData d L (N₁ * L ^ m₁) (k + 1) N →
        Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ,
      (∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps)) ∧
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        M (rawOf D) = hatCovSqrt Gp a₁ ν D) ∧
      ∀ (cc : ℂ) {cψ : ℝ}, 0 ≤ cψ → ∀ {ψh : unitPts Gp × Fin N → ℂ}, (∀ p, ‖ψh p‖ ≤ cψ) →
        ∀ Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : unitPts Gp,
          vn (fun i => (cc • (M Θ *ᵥ ψh)) (b, i)) ≤ markedRad d L N k a₁ κ cψ cc := by
  obtain ⟨M, hMan, hM⟩ := exists_analytic_hatCovSqrt hC hk hMX hdm hα hsm
  refine ⟨M, hMan, hM, ?_⟩
  rintro cc cψ hcψ ψh hψh Θ ⟨D, hD, rfl⟩ b
  rw [hM D hD]
  have hcoord := hatCovSqrt_coord_le hC hk cc hcψ hMX hdm hα hsm hD hψh
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have h0 : vn (fun i : Fin 0 => (cc • (hatCovSqrt Gp a₁ ν D *ᵥ ψh)) (b, i)) = 0 := by
      rw [vn_eq_sqrt]; simp
    rw [h0]
    simp [markedRad]
  · have hV : 0 ≤ ‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ) :=
      (norm_nonneg _).trans (hcoord ⟨b, ⟨0, hN⟩⟩)
    exact vn_le_sqrt_mul hV (fun i => hcoord (b, i))

/-- **The unit field `cc • M(Θ) ψ̂` is analytic jointly in the raw data and the hat field**: if the
entries of the matrix function `M` are analytic at the points of a set `A` of raw data, then
`(Θ, ψ̂) ↦ cc • M(Θ) ψ̂` is analytic at every point of `A × univ`. -/
theorem analyticOnNhd_smul_mulVec {A : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)}
    {M : RawData d L (N₁ * L ^ m₁) (k + 1) N →
      Matrix (unitPts Gp × Fin N) (unitPts Gp × Fin N) ℂ}
    (hM : ∀ p q, AnalyticOnNhd ℂ (fun Θ => M Θ p q) A) (cc : ℂ) :
    AnalyticOnNhd ℂ (fun x : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ) => cc • (M x.1 *ᵥ x.2)) (A ×ˢ (Set.univ)) := by
  rintro ⟨Θ, ψh⟩ ⟨hΘ, -⟩
  refine analyticAt_pi_iff.2 fun q => ?_
  simp only [Pi.smul_apply, Matrix.mulVec, dotProduct, smul_eq_mul]
  refine analyticAt_const.mul (Finset.analyticAt_fun_sum _ fun r _ => ?_)
  have h1 : AnalyticAt ℂ (fun x : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ) => M x.1 q r) (Θ, ψh) :=
    (hM q r Θ hΘ).comp_of_eq analyticAt_fst rfl
  have h2 : AnalyticAt ℂ (fun x : RawData d L (N₁ * L ^ m₁) (k + 1) N ×
      (unitPts Gp × Fin N → ℂ) => x.2 r) (Θ, ψh) :=
    analyticAt_pi_iff.1 analyticAt_snd r
  exact h1.mul h2

/-- **The unit field `cc • C^{1/2}(Θ) ψ̂` as an analytic function of the raw data, with its bound on
the whole chart.**  For a hat field `|ψ̂| ≤ c_ψ` there is one function `Q` of the raw data, analytic
at every point of `Ξ^c(𝔹_{k+1}; 1, ε)`, equal to `cc • hatCovSqrt D ψ̂` at every datum `D` of the
chart (complex `h` included), whose Euclidean norm at every unit point is at most
`markedRad = √N · |cc| · C_sup · c_ψ` on the chart. -/
theorem exists_analytic_hatField_chart (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (cc : ℂ) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    {ψh : unitPts Gp × Fin N → ℂ} (hψh : ∀ p, ‖ψh p‖ ≤ cψ) :
    ∃ Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → unitPts Gp × Fin N → ℂ,
      AnalyticOnNhd ℂ Q (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps) ∧
      (∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        Q (rawOf D) = cc • (hatCovSqrt Gp a₁ ν D *ᵥ ψh)) ∧
      ∀ Θ ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : unitPts Gp,
        vn (fun i => Q Θ (b, i)) ≤ markedRad d L N k a₁ κ cψ cc := by
  obtain ⟨M, hMan, hM, hMb⟩ := exists_analytic_hatCovSqrt_bdd hC hk hMX hdm hα hsm
  refine ⟨fun Θ => cc • (M Θ *ᵥ ψh), fun Θ hΘ => ?_, fun D hD => ?_,
    fun Θ hΘ b => hMb cc hcψ hψh Θ hΘ b⟩
  · exact (analyticOnNhd_smul_mulVec hMan cc (Θ, ψh) ⟨hΘ, Set.mem_univ _⟩).comp_of_eq
      (analyticAt_id.prod analyticAt_const) rfl
  · show cc • (M (rawOf D) *ᵥ ψh) = _
    rw [hM D hD]

end HatField

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Finset Set Matrix Metric

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

/-- **The shift `shiftUC ψ̂` as an analytic function of the raw data, with its bound on the whole
chart.**  The function of `exists_analytic_shiftUC` (it returns `shiftUC ψ̂` of the step with the datum
`D` on the fibre `h = h₀`), with the additional information that at every point of the chart
(complex `h` included) its Euclidean norm at every unit point is at most
`markedRad = √N · β_k^{-1/2} · C_sup · c_ψ`, for `|ψ̂| ≤ c_ψ`. -/
theorem exists_analytic_shiftUC_chart {c BG κ eps Kc Cx c₂ BG₂ δ₁ δc : ℝ}
    (hC : FlCore N S.G' Hm S.a₁ S.ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁)
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4) (x : S.E) {cψ : ℝ} (hcψ : 0 ≤ cψ)
    (hx : ∀ p, ‖yhat x p‖ ≤ cψ) :
    ∃ Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC,
      AnalyticOnNhd ℂ Q (XiCRaw S.G' S.a S.ν (k + 1) 1 eps) ∧
      (∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)),
        XiCData S.G' S.a S.ν (k + 1) 1 eps D → Q (rawOf D) = (S.withDatum D hD).shiftUC x) ∧
      ∀ Θ ∈ XiCRaw S.G' S.a S.ν (k + 1) 1 eps, ∀ b : S.U,
        vn (fun i => Q Θ (b, i)) ≤
          markedRad d L N k S.a₁ κ cψ (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) := by
  obtain ⟨Q, hQan, hQ, hQb⟩ := exists_analytic_hatField_chart hC S.hk1 hMX hdm hα hsm
    (((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)) hcψ hx
  refine ⟨Q, hQan, fun D hD hX => ?_, hQb⟩
  have e : (S.withDatum D hD).covSqrtC = hatCovSqrt S.G' S.a₁ S.ν D :=
    (S.withDatum D hD).covSqrtC_eq_hatCovSqrt
  rw [hQ D hX, ← e]
  rfl

/-- **The discs of the third-derivative Cauchy estimate for an arbitrary unit field.**  Let `y` be a
complex field of the unit lattice of Euclidean norm at most `Y₀` at every unit point, and
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁`.  Then for `|u| < R_σ`, `|t| < t₁`, `|σ| < R₁ + r` the field
`σ · lift(u y + t M_z y)` lies in `FlBall Hm δ₁` (`markedDisc_hdom` with `y` in place of
`shiftUC ψ̂` and the bound `R_σ` on `|u|`). -/
theorem markedDisc_field_mem_flBall (hG : IsLevel Hm k) {δ₁ Y₀ R₁ r Rσ t₁ : ℝ} {y : S.EC}
    (hY : ∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀) (h : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁)
    {u t σ : ℂ} (hu : ‖u‖ < Rσ) (ht : ‖t‖ < t₁) (hσ : ‖σ‖ < R₁ + r) :
    σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y)) ∈ FlBall Hm δ₁ := by
  have hm : σ • (liftC S.hG' (u • y) + t • liftC S.hG' (S.maskUC z y)) =
      liftC S.hG' ((σ * u) • y + (σ * t) • maskBlock (S.blockU z) y) := by
    rw [S.maskBlock_blockU z]
    simp only [map_add, map_smul, smul_add, smul_smul]
  rw [hm]
  refine (liftC_mem_flBallLC hG S.hG' fun b => ?_).1
  refine lt_of_le_of_lt ((vn_marked_le (S.blockU z) (σ * u) (σ * t) y b).trans ?_) h
  have hsum : ‖σ * u‖ + ‖σ * t‖ ≤ (R₁ + r) * (Rσ + t₁) := by
    rw [norm_mul, norm_mul, ← mul_add]
    exact mul_le_mul hσ.le (add_le_add hu.le ht.le) (add_nonneg (norm_nonneg _) (norm_nonneg _))
      ((norm_nonneg σ).trans hσ.le)
  exact mul_le_mul hsum (hY b) (vn_nonneg _)
    ((add_nonneg (norm_nonneg _) (norm_nonneg _)).trans hsum)

/-- **The Cauchy estimate for the derivative mark along an arbitrary unit field.**  Let `Ev` be
analytic on `S' × FlBall Hm δ₁` with `|Ev| ≤ b` there, `Θ ∈ S'`, `y` a unit field of Euclidean norm
at most `Y₀` at the unit points, `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `|u| < R_σ` and
`0 < t₀ < t₁`.  Then `|∂_t P(Θ, u y + t M_z y)|_{t=0}| ≤ 3 b / (r³ t₀)`
(`norm_deriv_markedBlockTerm_taylorWeight_le`; the bound does not depend on `Θ`, `y`, `u`). -/
theorem norm_deriv_markedBlockTerm_field_le (hG : IsLevel Hm k)
    {S' : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {δ₁ Y₀ R₁ r Rσ t₁ : ℝ}
    {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r)
    (hEv : AnalyticOnNhd ℂ Ev (S' ×ˢ FlBall Hm δ₁))
    {Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N} (hΘ : Θ ∈ S') {y : S.EC}
    (hY : ∀ b : S.U, vn (fun i => y (b, i)) ≤ Y₀) {b t₀ : ℝ}
    (hb : ∀ w ∈ S' ×ˢ FlBall Hm δ₁, ‖Ev w‖ ≤ b) (ht₀ : 0 < t₀) (ht₀₁ : t₀ < t₁) {u : ℂ}
    (hu : ‖u‖ < Rσ) :
    ‖deriv (markedBlockTerm Ev taylorWeight (liftC S.hG' (u • y))
      (liftC S.hG' (S.maskUC z y)) Θ) 0‖ ≤ 3 * b / (r ^ 3 * t₀) :=
  norm_deriv_markedBlockTerm_taylorWeight_le hR₁ hr hEv hΘ
    (fun _ ht _ hσ => S.markedDisc_field_mem_flBall z hG hY hrad hu ht hσ) hb ht₀ ht₀₁

/-- **On the fibre `h = h₀` the family is the marked term of the step with the datum.**  If `Q` returns
`shiftUC ψ̂` of the step with the datum `D` (`D.h = h₀`) at `rawOf D` (as the function of
`exists_analytic_shiftUC_chart` does on the chart), the marked term of the family at `Θ = rawOf D`
is the landed marked term along the lifted marked tangent `markedTangentC` of that step
(`markedBlockTerm_marked_eq`). -/
theorem markedBlockTerm_family_withDatum
    {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC} {x : S.E} (D : BgData S.G' N)
    (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (hQ : Q (rawOf D) = (S.withDatum D hD).shiftUC x)
    (Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (ω : ℂ → ℂ) (u t : ℂ) :
    markedBlockTerm Ev ω (liftC S.hG' (u • Q (rawOf D)))
        (liftC S.hG' (S.maskUC z (Q (rawOf D)))) (rawOf D) t =
      rayTerm (dl3 Ev (liftC S.hG' ((S.withDatum D hD).markedTangentC z u t x))) ω
        (liftC S.hG' ((S.withDatum D hD).markedTangentC z u t x)) 1 (rawOf D) := by
  rw [hQ]
  exact (S.withDatum D hD).markedBlockTerm_marked_eq z Ev ω (rawOf D) u t x

section Family

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {V₀ : Set P}
  {S' : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {δ₁ Y₀ R₁ r Rσ t₁ : ℝ}
  {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
  {Θf : P → RawData d L (N₁ * L ^ m₁) (k + 1) N} {y : P → S.EC}

/-- **The marked block term is analytic jointly in a parameter and both marks.**  Let `V₀` be an
open set of a parameter space, `p ↦ Θ(p)` analytic on `V₀` with values in a set `S'` such that `Ev`
is analytic on `S' × FlBall Hm δ₁`, `p ↦ y(p)` an analytic family of unit fields of Euclidean norm
at most `Y₀` at the unit points, and `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`.  Then the marked
term along `v_t(p, u) = u · y(p) + t · M_z y(p)`,
`((p, u), t) ↦ ∫₀¹ ω(s) D³Ev(Θ(p), s v_t)[v_t]³ ds`, is analytic on
`(V₀ × {|u| < R_σ}) × {|t| < t₁}`. -/
theorem markedBlockTerm_joint_family (hV₀ : IsOpen V₀) (hG : IsLevel Hm k)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r)
    (hEv : AnalyticOnNhd ℂ Ev (S' ×ˢ FlBall Hm δ₁))
    (hΘ : AnalyticOnNhd ℂ Θf V₀) (hy : AnalyticOnNhd ℂ y V₀) (hmem : ∀ p ∈ V₀, Θf p ∈ S')
    (hY : ∀ p ∈ V₀, ∀ b : S.U, vn (fun i => y p (b, i)) ≤ Y₀) :
    AnalyticOnNhd ℂ (fun x : (P × ℂ) × ℂ => markedBlockTerm Ev taylorWeight
        (liftC S.hG' (x.1.2 • y x.1.1)) (liftC S.hG' (S.maskUC z (y x.1.1))) (Θf x.1.1) x.2)
      ((V₀ ×ˢ ball (0 : ℂ) Rσ) ×ˢ ball (0 : ℂ) t₁) := by
  have hΘ' : AnalyticOnNhd ℂ (fun p : P × ℂ => Θf p.1) (V₀ ×ˢ ball (0 : ℂ) Rσ) :=
    fun p hp => (hΘ p.1 hp.1).comp analyticAt_fst
  have hy' : AnalyticOnNhd ℂ (fun p : P × ℂ => y p.1) (V₀ ×ˢ ball (0 : ℂ) Rσ) :=
    fun p hp => (hy p.1 hp.1).comp analyticAt_fst
  have ha' : AnalyticOnNhd ℂ (fun p : P × ℂ => liftC S.hG' (p.2 • y p.1))
      (V₀ ×ˢ ball (0 : ℂ) Rσ) :=
    analyticOnNhd_liftC S.hG' (v := fun p : P × ℂ => p.2 • y p.1)
      (fun p hp => analyticAt_snd.smul (hy' p hp))
  have hc' : AnalyticOnNhd ℂ (fun p : P × ℂ => liftC S.hG' (S.maskUC z (y p.1)))
      (V₀ ×ˢ ball (0 : ℂ) Rσ) := by
    refine analyticOnNhd_liftC S.hG' (v := fun p : P × ℂ => S.maskUC z (y p.1)) fun p hp => ?_
    exact AnalyticAt.comp (g := S.maskUCL z) (f := fun p : P × ℂ => y p.1)
      ((S.maskUCL z).analyticAt (y p.1)) (hy' p hp)
  have key := analyticOnNhd_markedBlockTerm_param (hV₀.prod isOpen_ball) (t₁ := t₁) hR₁ hr
    (analyticOnNhd_taylorWeight _) hEv hΘ' ha' hc' (fun p hp => hmem p.1 hp.1)
    (fun p hp t ht σ hσ => S.markedDisc_field_mem_flBall z hG (hY p.1 hp.1) hrad
      (mem_ball_zero_iff.1 hp.2) ht hσ)
  exact key

/-- **The derivative marks of the marked block term are analytic in the parameter and the radial
mark**: under the hypotheses of `markedBlockTerm_joint_family` and `t₁ > 0`,
`(p, u) ↦ ∂_t P(Θ(p), v_t(p, u))|_{t=0}` is analytic on `V₀ × {|u| < R_σ}`. -/
theorem deriv_markedBlockTerm_analytic_family (hV₀ : IsOpen V₀) (hG : IsLevel Hm k)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁)
    (hEv : AnalyticOnNhd ℂ Ev (S' ×ˢ FlBall Hm δ₁))
    (hΘ : AnalyticOnNhd ℂ Θf V₀) (hy : AnalyticOnNhd ℂ y V₀) (hmem : ∀ p ∈ V₀, Θf p ∈ S')
    (hY : ∀ p ∈ V₀, ∀ b : S.U, vn (fun i => y p (b, i)) ≤ Y₀) :
    AnalyticOnNhd ℂ (fun x : P × ℂ => deriv (markedBlockTerm Ev taylorWeight
        (liftC S.hG' (x.2 • y x.1)) (liftC S.hG' (S.maskUC z (y x.1))) (Θf x.1)) 0)
      (V₀ ×ˢ ball (0 : ℂ) Rσ) := by
  have key := analyticOnNhd_deriv_last
    (S.markedBlockTerm_joint_family z hV₀ hG hrad hR₁ hr hEv hΘ hy hmem hY)
    (mem_ball_self ht₁)
  exact key

end Family

section PhysV

variable {a₁ ν eps : ℝ}

/-- **Joint analyticity of the marked cubic block term on the parameter set `physV`.**  Let `Ev` be
analytic on `Ξ^c × FlBall Hm δ₁`, and `Q` a function of the raw data, analytic on the chart `Ξ^c`,
with values unit fields of Euclidean norm at most `Y₀` at the unit points on the chart (for the
physical step: the shift `shiftUC ψ̂` as a function of the datum, `exists_analytic_shiftUC_chart`).
Under the radial margin `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `t₁ > 0`, on the parameter
space `physParam = rawSub × sources` (the source coordinate does not enter), with the marked
tangent `v_t(e, u) = u · Q(e.1) + t · M_z Q(e.1)`:

1. `((e, u), t) ↦ P(e.1, v_t(e, u))` (`markedBlockTerm`) is analytic on
   `(physV × {|u| < R_σ}) × {|t| < t₁}`;
2. the derivative mark `(e, u) ↦ ∂_t P(e.1, v_t(e, u))|_{t=0}` is analytic on `physV × {|u| < R_σ}`
   (the shape of the field `holG` of `ParamMarkFamily`);
3. if `|Ev| ≤ b` on `Ξ^c × FlBall Hm δ₁` and `0 < t₀ < t₁`, then
   `|∂_t P(e.1, v_t(e, u))|_{t=0}| ≤ 3 b / (r³ t₀)` for every `e ∈ physV`, `|u| < R_σ`. -/
theorem markedCubic_joint_physV (hG : IsLevel Hm k)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν) {δ₁ Y₀ R₁ r Rσ t₁ : ℝ}
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁)
    {Ev : RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hEv : AnalyticOnNhd ℂ Ev
      (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC}
    (hQ : AnalyticOnNhd ℂ Q (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps))
    (hQb : ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : S.U,
      vn (fun i => Q Θ (b, i)) ≤ Y₀) :
    AnalyticOnNhd ℂ (fun x : (physParam N S × ℂ) × ℂ => markedBlockTerm Ev taylorWeight
        (liftC S.hG' (x.1.2 • Q (x.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
        (liftC S.hG' (S.maskUC z (Q (x.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
        (x.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) x.2)
      ((physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ) ×ˢ ball (0 : ℂ) t₁) ∧
    AnalyticOnNhd ℂ (fun x : physParam N S × ℂ => deriv (markedBlockTerm Ev taylorWeight
        (liftC S.hG' (x.2 • Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
        (liftC S.hG' (S.maskUC z (Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
        (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) 0)
      (physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ) ∧
    ∀ {b t₀ : ℝ}, (∀ w ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev w‖ ≤ b) → 0 < t₀ → t₀ < t₁ → ∀ e ∈ physV S a₁ ν eps, ∀ u : ℂ, ‖u‖ < Rσ →
      ‖deriv (markedBlockTerm Ev taylorWeight
        (liftC S.hG' (u • Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
        (liftC S.hG' (S.maskUC z (Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
        (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) 0‖ ≤ 3 * b / (r ^ 3 * t₀) := by
  have hV : IsOpen (physV S a₁ ν eps) := isOpen_physV S a₁ ν eps H
  have hmem : ∀ e ∈ physV S a₁ ν eps, (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
      XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps := fun e he => he.1
  have hΘ : AnalyticOnNhd ℂ (fun e : physParam N S =>
      (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) (physV S a₁ ν eps) := by
    let g : physParam N S →L[ℂ] RawData d L (N₁ * L ^ m₁) (k + 1) N :=
      (rawSub N S.G').subtypeL.comp (ContinuousLinearMap.fst ℂ _ _)
    exact g.analyticOnNhd _
  have hy : AnalyticOnNhd ℂ (fun e : physParam N S =>
      Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) (physV S a₁ ν eps) :=
    fun e he => AnalyticAt.comp (g := Q)
      (f := fun e : physParam N S => (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))
      (hQ _ (hmem e he)) (hΘ e he)
  have hY : ∀ e ∈ physV S a₁ ν eps, ∀ b : S.U,
      vn (fun i => Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) (b, i)) ≤ Y₀ :=
    fun e he b => hQb _ (hmem e he) b
  have j1 := S.markedBlockTerm_joint_family z hV hG hrad hR₁ hr hEv hΘ hy hmem hY
  have j2 := S.deriv_markedBlockTerm_analytic_family z hV hG hrad hR₁ hr ht₁ hEv hΘ hy hmem hY
  refine ⟨j1, j2, ?_⟩
  intro b t₀ hb ht₀ ht₀₁ e he u hu
  have j3 := S.norm_deriv_markedBlockTerm_field_le z hG hrad hR₁ hr hEv (hmem e he)
    (hY e he) hb ht₀ ht₀₁ hu
  exact j3

end PhysV

section VBlock

variable {a₁ ν c BG κ eps : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **`markedCubic_joint_param`: the terms of the landed block expansion along the marked tangent,
jointly in the datum and the marks.**  The hypotheses are those of `vblock_expansion_scaled` for the
old block `zb` of the step (`Gp = S.G'` of level `k + 1`, `K = k + 1`, `n = k`); `z` is the marked
block.  There is one family `Ev` of terms `E_{zb,Y}` with the four clauses of the landed theorem
(sum identity, locality, the bound `E* e^{-2 κ_dec d(Y)}` with `E* = energyBdScaled`, analyticity on
`Ξ^c × FlBall Hm δ₁`) such that, for every label `Y`, every function `Q` of the raw data analytic on
the chart with values unit fields of Euclidean norm at most `Y₀` there, and every radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `t₁ > 0`, with
`v_t(e, u) = u · Q(e.1) + t · M_z Q(e.1)` and `P_{zb,Y}(Θ, v) = ∫₀¹ ω(s) D³E_{zb,Y}(Θ, s v)[v]³ ds`:

* `((e, u), t) ↦ P_{zb,Y}(e.1, v_t(e, u))` is analytic on `(physV × {|u| < R_σ}) × {|t| < t₁}`;
* the derivative mark `(e, u) ↦ ∂_t P_{zb,Y}(e.1, v_t(e, u))|_{t=0}` is analytic on
  `physV × {|u| < R_σ}`;
* for `0 < t₀ < t₁`, every `e ∈ physV` and `|u| < R_σ`,
  `|∂_t P_{zb,Y}(e.1, v_t(e, u))|_{t=0}| ≤ 3 E* e^{-2 κ_dec d(Y)} / (r³ t₀)`. -/
theorem markedCubic_joint_param
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hcov : CovSetup S.G' m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ j 𝒦X)
    (hconn : HatConn S.G') (hrow : RowInHat (coverOf S.G') Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hHm : IsLevel Hm k) (zb : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k zb ⊆ ↑X₁f)
    (hmar : BlockMargin S.G' X₁f (↑(blockSites d L N₁ m₁ (k + 1) k zb) :
      Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ Ev : Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ,
      -- the four clauses of `vblock_expansion_scaled`
      (∀ D : BgData S.G' N, XiCData S.G' (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψ' ∈ FlBall Hm δ₁,
        energyBlock S.G' Hm (compWeight L a₁) ν k (bgMultC S.G' (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne S.G' Hm BG₂ κ a₁ ν D ψ') ψ' zb =
        ∑ Y ∈ polymerDomains (fun i : ParIdx S.G' (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) =>
          i.1.1) S.G' m₀ (X1 S.G' m₀ j 𝒦X), Ev Y (rawOf D, ψ')) ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ∀ u' ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        agreeOn (thickSet S.G' Y) u.1 u'.1 → (∀ y ∈ psiThick Y, u.2 y = u'.2 y) →
        Ev Y u = Ev Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁,
        ‖Ev Y u‖ ≤ energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (Ev Y)
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁)) ∧
      -- the family of marked terms on `physV`
      ∀ Y, ∀ {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC},
        AnalyticOnNhd ℂ Q (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps) →
        ∀ {Y₀ R₁ r Rσ t₁ : ℝ},
        (∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : S.U,
          vn (fun i => Q Θ (b, i)) ≤ Y₀) →
        (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₁ →
        AnalyticOnNhd ℂ (fun x : (physParam N S × ℂ) × ℂ =>
            markedBlockTerm (Ev Y) taylorWeight
              (liftC S.hG' (x.1.2 • Q (x.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
              (liftC S.hG' (S.maskUC z (Q (x.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
              (x.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) x.2)
          ((physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ) ×ˢ ball (0 : ℂ) t₁) ∧
        AnalyticOnNhd ℂ (fun x : physParam N S × ℂ => deriv (markedBlockTerm (Ev Y) taylorWeight
            (liftC S.hG' (x.2 • Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
            (liftC S.hG' (S.maskUC z (Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
            (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) 0)
          (physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ) ∧
        ∀ {t₀ : ℝ}, 0 < t₀ → t₀ < t₁ → ∀ e ∈ physV S a₁ ν eps, ∀ u : ℂ, ‖u‖ < Rσ →
          ‖deriv (markedBlockTerm (Ev Y) taylorWeight
            (liftC S.hG' (u • Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
            (liftC S.hG' (S.maskUC z (Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
            (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)) 0‖ ≤
            3 * (energyBdScaled d L N (compWeight L a₁) k
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
              Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y)) / (r ^ 3 * t₀) := by
  obtain ⟨Ev, hsum, hloc, hbd, han⟩ := vblock_expansion_scaled hC hcov hX₁ hconn hrow hopt hΔ hκ₀
    hκdec hκ h1 hlog S.hk1 le_rfl hHm S.hG' zb hZ hmar
  refine ⟨Ev, hsum, hloc, hbd, han, fun Y Q hQ Y₀ R₁ r Rσ t₁ hQb hrad hR₁ hr ht₁ => ?_⟩
  obtain ⟨j1, j2, j3⟩ := S.markedCubic_joint_physV z hHm hC.HBp hrad hR₁ hr ht₁ (han Y) hQ hQb
  exact ⟨j1, j2, fun ht₀ ht₀₁ e he u hu => j3 (fun w hw => hbd Y w hw) ht₀ ht₀₁ e he u hu⟩

end VBlock

end StepSetting

end Balaban.Fluctuation
