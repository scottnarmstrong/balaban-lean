/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedFieldCount

/-!
# The rooted sums of the marked terms as an analytic family on the chart (`MarkedRootFamily`)

For a family of data the tangent of the marked terms is a function `Q` of the raw data, analytic on
the chart `Ξ^c(𝔹_{k+1}; 1, ε)`, with values unit fields of Euclidean norm at most `Y₀` there (for
the physical step: `Q(Θ) = β_k^{-1/2} C^{1/2}(Θ) ψ̂`, `exists_analytic_shiftUC_chart`; on the fibre
`h = h₀` it is the shift of the step with the datum).  The rooted sums `markedOut z Y'` built with
the tangent `Q(e.1)` are functions of the parameter `e ∈ physV` and of the radial mark `u`.  The
index sets `markedIdx`, `bridgeFamily`, `polyDom` do not depend on the datum, so:

* `markedOut_analytic_family`, `markedOut_analytic_physV`: each rooted sum is a finite sum of the
  analytic derivative marks of `deriv_markedBlockTerm_analytic_family`, hence analytic in `(e, u)`
  on `physV × {|u| < R_σ}`;
* `markedOut_family_withDatum`: on the fibre `h = h₀`, where `Q (rawOf D)` is the shift of the step
  with the datum `D`, the rooted sum of the family is the rooted sum of that step (the object of
  the landed `marked_count_scaled` applied to `S.withDatum D hD`);
* `MarkedRootFamily`: the three clauses (analyticity; the clauses of the rooted count
  `MarkedCountClauses` at **every** point of `physV × {|u| < R_σ}`, complex `h` included; the fibre
  identity);
* `markedRoot_family_of_vblock`, `markedRoot_family`: the clauses hold, for given block terms and
  for the terms of `vblock_expansion_scaled`.  The bound off the fibre needs no ingredient beyond
  the landed clauses: the bound `E* e^{-2κ_dec d(Y)}` of the block terms holds on the whole chart,
  and the count is the field-generic one of `MarkedFieldCount`.

## Scope

Zero class, undecoupled level, generator-neutral.  One hat field at a time (the tangent `Q` is a
hypothesis); the factor `-β`, the identification with the integrand of `E1MarksC` and `MARK-REAL`
are in `MarkedRootAssembly`.  The clamped global marks, the common label system and the `E1MarksC`
inhabitant are NOT constructed here.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization Balaban.SmallField
  Balaban.Polymer Set Metric

namespace StepSetting

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
  {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}

section Family

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P] {V₀ : Set P}
  {S' : Set (RawData d L (N₁ * L ^ m₁) (k + 1) N)} {δ₁ Y₀ R₁ r Rσ t₁ : ℝ} {m₀ : ℕ}
  {Θf : P → RawData d L (N₁ * L ^ m₁) (k + 1) N} {y : P → S.EC}

/-- **The rooted sums are analytic in a parameter and the radial mark.**  Under the hypotheses of
`deriv_markedBlockTerm_analytic_family` for every block term (`Ev b Y` analytic on
`S' × FlBall Hm δ₁`; `p ↦ Θ(p) ∈ S'` and `p ↦ y(p)` analytic on the open set `V₀`, `|y(p)(b)| ≤ Y₀`;
the radial margin), the rooted sum
`(p, u) ↦ markedOut z Y'` built with the tangent `u y(p) + t M_z y(p)` at the datum `Θ(p)` is
analytic on `V₀ × {|u| < R_σ}`: its index set does not depend on `(p, u)`. -/
theorem markedOut_analytic_family (hV₀ : IsOpen V₀) (hG : IsLevel Hm k)
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (han : ∀ b Y, AnalyticOnNhd ℂ (Ev b Y) (S' ×ˢ FlBall Hm δ₁))
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁)
    (hΘ : AnalyticOnNhd ℂ Θf V₀) (hy : AnalyticOnNhd ℂ y V₀) (hmem : ∀ p ∈ V₀, Θf p ∈ S')
    (hY : ∀ p ∈ V₀, ∀ b : S.U, vn (fun i => y p (b, i)) ≤ Y₀)
    (Y' : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun x : P × ℂ => markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
        (liftC S.hG' (x.2 • y x.1)) (liftC S.hG' (S.maskUC z (y x.1))) (Θf x.1) Y')
      (V₀ ×ˢ ball (0 : ℂ) Rσ) := by
  classical
  unfold markedOut
  exact Finset.analyticOnNhd_fun_sum _ fun q _ =>
    S.deriv_markedBlockTerm_analytic_family z hV₀ hG hrad hR₁ hr ht₁ (han q.1 q.2) hΘ hy hmem hY

end Family

section PhysV

variable {a₁ ν eps δ₁ Y₀ R₁ r Rσ t₁ : ℝ} {m₀ : ℕ}

/-- **The rooted sums are analytic on the parameter set `physV`.**  Let the block terms be analytic
on `Ξ^c × FlBall Hm δ₁`, and `Q` a function of the raw data, analytic on the chart, with values
unit fields of Euclidean norm at most `Y₀` there.  Under the radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `t₁ > 0`, the rooted sum
`(e, u) ↦ markedOut z Y'` built with the tangent `u Q(e.1) + t M_z Q(e.1)` at the datum `e.1` is
analytic on `physV × {|u| < R_σ}` (the source coordinate of `physParam` does not enter). -/
theorem markedOut_analytic_physV (hG : IsLevel Hm k)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (han : ∀ b Y, AnalyticOnNhd ℂ (Ev b Y)
      (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₁ : 0 < t₁)
    {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC}
    (hQ : AnalyticOnNhd ℂ Q (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps))
    (hQb : ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : S.U,
      vn (fun i => Q Θ (b, i)) ≤ Y₀) (Y' : Set (CTorus d L N₁ m₁ (k + 1))) :
    AnalyticOnNhd ℂ (fun x : physParam N S × ℂ => markedOut m₀ (fun _ => Set.univ) dom z Ev
        taylorWeight (liftC S.hG' (x.2 • Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
        (liftC S.hG' (S.maskUC z (Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
        (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) Y')
      (physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ) := by
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
  exact S.markedOut_analytic_family z hV hG dom Ev han hrad hR₁ hr ht₁ hΘ hy hmem hY Y'

/-- **On the fibre `h = h₀` the rooted sum of the family is the rooted sum of the step with the
datum.**  If `Q` returns `shiftUC ψ̂` of the step with the datum `D` (`D.h = h₀`) at `rawOf D`, the
rooted sum built with the tangent `Q (rawOf D)` at the datum `rawOf D` is the rooted sum of the
landed count for the step `S.withDatum D hD`, at its own datum. -/
theorem markedOut_family_withDatum {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC}
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) {x : S.E}
    (hQ : Q (rawOf D) = (S.withDatum D hD).shiftUC x) (u : ℂ)
    (Y' : Set (CTorus d L N₁ m₁ (k + 1))) :
    markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight (liftC S.hG' (u • Q (rawOf D)))
        (liftC S.hG' (S.maskUC z (Q (rawOf D)))) (rawOf D) Y' =
      markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
        (liftC (S.withDatum D hD).hG' (u • (S.withDatum D hD).shiftUC x))
        (liftC (S.withDatum D hD).hG' ((S.withDatum D hD).maskUC z ((S.withDatum D hD).shiftUC x)))
        (rawOf D) Y' := by
  rw [hQ]
  rfl

/-- **The rooted sums of the family on the chart.**  For block terms `Ev b Y`, `Y ∈ dom b`, a
function `Q` of the raw data (the tangent of the family), the chart `Ξ^c(𝔹_{k+1}; 1, ε)` with
weights `compWeight L a₁` and mass `ν`, a radius `R_σ`, a prefactor `F₀` and a rate `a₀`:

1. for every `Y'`, the rooted sum `(e, u) ↦ markedOut z Y'` built with the tangent
   `u Q(e.1) + t M_z Q(e.1)` at the datum `e.1` is analytic on `physV × {|u| < R_σ}`;
2. at every point of `physV × {|u| < R_σ}` (complex `h` included) the clauses of the rooted count
   hold: the finite-sum identity, `|markedOut z Y'| ≤ F₀ e^{-a₀ d(Y')}`, the root clause, and the
   anchored sum;
3. on the fibre `h = h₀`: if `Q (rawOf D)` is the shift `shiftUC ψ̂` of the step with the datum `D`,
   the rooted sum at `rawOf D` is the rooted sum of that step. -/
def MarkedRootFamily (m₀ : ℕ)
    (dom : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) →
      Finset (Set (CTorus d L N₁ m₁ (k + 1))))
    (Ev : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1)) →
        RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (a₁ ν eps Rσ : ℝ) (Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC) (F₀ a₀ : ℝ) : Prop :=
  (∀ Y', AnalyticOnNhd ℂ (fun x : physParam N S × ℂ => markedOut m₀ (fun _ => Set.univ) dom z Ev
        taylorWeight (liftC S.hG' (x.2 • Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
        (liftC S.hG' (S.maskUC z (Q (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
        (x.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) Y')
      (physV S a₁ ν eps ×ˢ ball (0 : ℂ) Rσ)) ∧
  (∀ e ∈ physV S a₁ ν eps, ∀ u : ℂ, ‖u‖ < Rσ →
    MarkedCountClauses m₀ dom z Ev
      (liftC S.hG' (u • Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N)))
      (liftC S.hG' (S.maskUC z (Q (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N))))
      (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) F₀ a₀) ∧
  ∀ (D : BgData S.G' N) (hD : ∀ y i, D.h y i = (S.h₀ i : ℂ)) (x : S.E),
    Q (rawOf D) = (S.withDatum D hD).shiftUC x → ∀ (u : ℂ) (Y' : Set (CTorus d L N₁ m₁ (k + 1))),
    markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight (liftC S.hG' (u • Q (rawOf D)))
        (liftC S.hG' (S.maskUC z (Q (rawOf D)))) (rawOf D) Y' =
      markedOut m₀ (fun _ => Set.univ) dom z Ev taylorWeight
        (liftC (S.withDatum D hD).hG' (u • (S.withDatum D hD).shiftUC x))
        (liftC (S.withDatum D hD).hG' ((S.withDatum D hD).maskUC z ((S.withDatum D hD).shiftUC x)))
        (rawOf D) Y'

end PhysV

section Count

variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The rooted sums of the family, for given block terms.**  The hypotheses on the cover and on
the terms `Ev` are those of `marked_count_field_of_vblock`; `H` makes the chart open in the
parameter space.  For every function `Q` of the raw data, analytic on the chart, with values unit
fields of Euclidean norm at most `Y₀` there, and every radial margin
`(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`, `0 < t₀ < t₁`, the clauses of `MarkedRootFamily`
hold with `F₀ = 3 ‖E‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}` and the rate `2κ_dec - 1`. -/
theorem markedRoot_family_of_vblock (hd : 3 ≤ d)
    (hcovV : ∀ b, CovSetup S.G' m₀ (jV b) (XV b) (𝒦XV b))
    (hX₁V : ∀ b, (↑(X₁V b) : Set (CTorus d L N₁ m₁ (k + 1))) = X1 S.G' m₀ (jV b) (𝒦XV b))
    (hoptV : ∀ b, ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ XV b) ∧ MeetsOne m₀ (jV b) (𝒦XV b) W₀ ∧
        bondCost (scaleW L m₀ m₁ (jV b)) E₀ = treeLenCovOne m₀ (jV b) (XV b))
    {κdec : ℝ} (hκ1 : 1 ≤ 2 * κdec) (hHm : IsLevel Hm k)
    (hZV : ∀ b, readSites Hm k b ⊆ ↑(X₁V b)) (hL : 2 ≤ L)
    (H : BgHyp d L (k + 1) ϱ (compWeight L a₁) ν)
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
        (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ FlBall Hm δ₁))
    {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC}
    (hQ : AnalyticOnNhd ℂ Q (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps))
    {Y₀ R₁ r Rσ t₁ t₀ : ℝ}
    (hQb : ∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : S.U,
      vn (fun i => Q Θ (b, i)) ≤ Y₀)
    (hrad : (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁) (hR₁ : 1 < R₁) (hr : 0 < r) (ht₀ : 0 < t₀)
    (ht₀₁ : t₀ < t₁) :
    S.MarkedRootFamily z m₀ (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) Ev a₁ ν eps Rσ Q
      (3 * ‖E‖ / (r ^ 3 * t₀) * (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
        ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L))) (2 * κdec - 1) :=
  ⟨fun Y' => S.markedOut_analytic_physV z hHm H _ Ev han hrad hR₁ hr (ht₀.trans ht₀₁) hQ hQb Y',
    fun _ he _ hu => S.marked_count_field_of_vblock z hd hcovV hX₁V hoptV hκ1 hHm hZV hL Ev hloc
      hbd han (hQb _ he.1) hrad hR₁ hr ht₀ ht₀₁ hu he.1,
    fun D hD _ hQx u Y' => S.markedOut_family_withDatum z _ Ev D hD hQx u Y'⟩

end Count

section Main

variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {m₀ : ℕ}
  {jV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → ℕ}
  {XV 𝒦XV : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Set (CTorus d L N₁ m₁ (k + 1))}
  {X₁V : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))) → Finset (CTorus d L N₁ m₁ (k + 1))}

/-- **The rooted sums of the marked terms as an analytic family on the chart.**  The hypotheses
are those of `marked_count_scaled`.  There is one family of block terms `E_{b,Y}` (the terms of
`vblock_expansion_scaled`, with its four clauses) such that for every marked block `z`, every
function `Q` of the raw data, analytic on the chart, with values unit fields of Euclidean norm at
most `Y₀` there, and every radial margin `(R₁ + r)(R_σ + t₁) Y₀ < δ₁`, `R₁ > 1`, `r > 0`,
`0 < t₀ < t₁`:

1. each rooted sum `(e, u) ↦ markedOut z Y'`, built with the tangent `u Q(e.1) + t M_z Q(e.1)` at
   the datum `e.1`, is analytic on `physV × {|u| < R_σ}`;
2. at every point of `physV × {|u| < R_σ}` the clauses of the rooted count hold with
   `F₀ = 3‖E*‖/(r³ t₀) · c₁ M^d · nFibre · e^{(2κ_dec-1) cBr}` and the rate `2κ_dec - 1`
   (the bound is uniform on the chart, not only on the fibre `h = h₀`);
3. on the fibre `h = h₀`, where `Q (rawOf D)` is the shift of the step with the datum `D`, the
   rooted sum is the rooted sum of the landed count for `S.withDatum D hD`. -/
theorem markedRoot_family
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
      ∀ (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
        {Q : RawData d L (N₁ * L ^ m₁) (k + 1) N → S.EC},
        AnalyticOnNhd ℂ Q (XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps) →
        ∀ {Y₀ R₁ r Rσ t₁ t₀ : ℝ},
        (∀ Θ ∈ XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps, ∀ b : S.U,
          vn (fun i => Q Θ (b, i)) ≤ Y₀) →
        (R₁ + r) * (Rσ + t₁) * Y₀ < δ₁ → 1 < R₁ → 0 < r → 0 < t₀ → t₀ < t₁ →
        S.MarkedRootFamily z m₀ (fun b => polyDom S.G' (X₁V b) m₀ (jV b) (𝒦XV b)) Ev a₁ ν eps Rσ
          Q (3 * ‖energyBdScaled d L N (compWeight L a₁) k
              (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ)‖ / (r ^ 3 * t₀) *
            (c1 d L * ((L : ℝ) ^ (m₀ + m₁)) ^ d) *
            ((nFibre d L : ℝ) * Real.exp ((2 * κdec - 1) * cBr d L))) (2 * κdec - 1) := by
  obtain ⟨Ev, hsum, hloc, hbd, han, -⟩ := S.marked_count_field hC hcovV hX₁V hconn hrow hoptV hΔV
    hκ₀ hκdec hκ h1 hlog hHm hZV hmarV hL
  exact ⟨Ev, hsum, hloc, hbd, han, fun z _ hQ _ _ _ _ _ _ hQb hrad hR₁ hr ht₀ ht₀₁ =>
    S.markedRoot_family_of_vblock z hC.HBp.hd hcovV hX₁V hoptV (by linarith) hHm hZV hL hC.HBp Ev
      hloc hbd han hQ hQb hrad hR₁ hr ht₀ ht₀₁⟩

end Main

end StepSetting

end Balaban.Fluctuation
