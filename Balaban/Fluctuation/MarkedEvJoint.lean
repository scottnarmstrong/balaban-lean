/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedTwoMarkLocal
public import Balaban.Fluctuation.ParamActivitySubspace
public import Balaban.Polymer.MarkedHoloParam

/-!
# Joint analyticity of the localized terms of the decoupled marked expansion (`MarkedEvJoint`)

The landed decoupled marked expansion (`MarkedVBlockDec`, `MarkedTwoMarkLocal`) gives terms
`evDec … um tm Y (Θ, ψ̂)` that are analytic in the marks `(um, tm)` at fixed data and analytic in the
data at fixed marks.  This file proves the joint statement (J) of the note `MARKPARAM`: for one pair
`(F₁, Sol)` of the decoupled background and fluctuation maps (the pair of the landed theorems) and
every label `Y`, the term is analytic in `(Θ, ψ̂, um, tm)` as one parameter, at every point of
`(Ξ^c × B̂) × W`, `W = {(u, t) | (‖u‖ + ‖t‖) · markedRad < δ₁}`.

* `analyticOnNhd_prod_right_comm`, `analyticOnNhd_deriv_mark`, `analyticOnNhd_deriv_mark_cauchy`:
  exchange of two factors of a product parameter; the derivative in the second mark at `0` of a
  jointly analytic function is analytic in the remaining variables, from the directional derivative
  (any set of parameters) and from the landed Cauchy-integral lemma `analyticOnNhd_deriv_zero`
  (open set of a finite-dimensional space, uniform bound).
* `marked_expansion_product_pair`: the landed `localization_expansion` applied to the product
  parameter `p = ((Θ, ψ̂), (um, tm))` with the functional `F p s = FFmarked … um tm (Θ, ψ̂) s` and the
  agreement law "`AgHatDir` on the component and equal marks".  Its hypotheses are supplied by
  `fanH_analytic_marked` (joint analyticity), the bound of the block functional on `FlReal`
  (uniform bound) and `fanHL_local_marked` (locality at equal marks).  The coefficient is the landed
  `evTerm`: `evTerm c … F Y p` and `evTerm c … (FFmarked … um tm) Y (Θ, ψ̂)` are the same expression,
  so no new family is chosen.
* `MarkedBlockExpansionDecPair`: the eight clauses of the landed `MarkedBlockExpansionDecTwo` as a
  predicate of the pair (`markedBlockExpansionDecTwo_iff_exists_pair`: the landed proposition is
  the existence of a pair with these clauses; no new object is defined).
* `vblock_expansion_hat_marked_joint_pair`, `markedEv_joint_param`: for the block functional, the
  eight landed clauses and (J) for the same pair, under the hypotheses of
  `vblock_expansion_hat_marked_scaled`.
* `analyticOnNhd_physV_of_chart`, `markedEv_joint_physV`: composition with the inclusion `physIncl`
  of the parameter space `physParam = rawSub × sources`: for a step `S` (`Gp = S.G'`) the terms are
  analytic on `(physV × B̂) × W` (the source coordinate does not enter), and the derivative marks
  `∂_t evDec|_{t=0}` are analytic on `physV × {‖u‖ < a}` for every `a`, `b > 0` with
  `(a + b) · markedRad < δ₁` (the shape of the field `holG` of `ParamMarkFamily`, per label), and
  jointly with the hat variable.

Zero class only.  The root assembly, the clamped global marks, the common label system and the
`E1MarksC` inhabitant are NOT constructed here; no mark family is constructed.  Nothing depends on a
choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Generic

variable {E G H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup G]
  [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- **Exchange of the last two factors of a product parameter.**  If `f` is analytic at every point
of `(A × P) × W`, then `((x, w), s) ↦ f ((x, s), w)` is analytic at every point of `(A × W) × P`. -/
theorem analyticOnNhd_prod_right_comm {A : Set E} {P : Set G} {W : Set H} {f : (E × G) × H → ℂ}
    (hf : AnalyticOnNhd ℂ f ((A ×ˢ P) ×ˢ W)) :
    AnalyticOnNhd ℂ (fun x : (E × H) × G => f ((x.1.1, x.2), x.1.2)) ((A ×ˢ W) ×ˢ P) :=
  hf.comp (f := fun x : (E × H) × G => ((x.1.1, x.2), x.1.2))
    (fun _ _ => ((analyticAt_fst.comp analyticAt_fst).prod analyticAt_snd).prod
      (analyticAt_snd.comp analyticAt_fst))
    (fun _ hx => ⟨⟨hx.1.1, hx.2⟩, hx.1.2⟩)

/-- **A slice at a fixed middle variable.**  If `f ((x, y), w)` is analytic at every point of
`(A × B) × W` and `y₀ ∈ B`, then `(x, w) ↦ f ((x, y₀), w)` is analytic at every point of `A × W`. -/
theorem analyticOnNhd_slice_mid {A : Set E} {B : Set G} {W : Set H} {f : (E × G) × H → ℂ}
    (hf : AnalyticOnNhd ℂ f ((A ×ˢ B) ×ˢ W)) {y₀ : G} (hy : y₀ ∈ B) :
    AnalyticOnNhd ℂ (fun x : E × H => f ((x.1, y₀), x.2)) (A ×ˢ W) :=
  hf.comp (f := fun x : E × H => ((x.1, y₀), x.2))
    (fun _ _ => (analyticAt_fst.prod analyticAt_const).prod analyticAt_snd)
    (fun _ hx => ⟨⟨hx.1, hy⟩, hx.2⟩)

/-- **The derivative in the second mark of a jointly analytic function.**  If `f (x, (u, t))` is
analytic at every point of `A × W`, then `(x, u) ↦ ∂_t f (x, (u, t))|_{t=0}` is analytic at every
point `(x, u)` with `x ∈ A`, `(u, 0) ∈ W` (it is a directional derivative of `f`). -/
theorem analyticOnNhd_deriv_mark {A : Set E} {W : Set (ℂ × ℂ)} {f : E × (ℂ × ℂ) → ℂ}
    (hf : AnalyticOnNhd ℂ f (A ×ˢ W)) :
    AnalyticOnNhd ℂ (fun x : E × ℂ => deriv (fun t : ℂ => f (x.1, (x.2, t))) 0)
      (A ×ˢ {u : ℂ | (u, (0 : ℂ)) ∈ W}) := by
  rintro ⟨a, u⟩ ⟨ha, hu⟩
  have h0 : AnalyticAt ℂ (lineD ((0 : E), ((0 : ℂ), (1 : ℂ))) f) (a, (u, 0)) :=
    analyticAt_lineD _ (hf _ ⟨ha, hu⟩)
  have hm : AnalyticAt ℂ (fun x : E × ℂ => ((x.1, (x.2, (0 : ℂ))) : E × (ℂ × ℂ))) (a, u) :=
    analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)
  have e : (fun x : E × ℂ => deriv (fun t : ℂ => f (x.1, (x.2, t))) 0) =
      fun x : E × ℂ => lineD ((0 : E), ((0 : ℂ), (1 : ℂ))) f (x.1, (x.2, 0)) := by
    funext x
    unfold lineD
    congr 1
    funext t
    congr 1
    ext <;> simp
  rw [e]
  exact h0.comp_of_eq hm rfl

/-- **The derivative in the second mark, by the Cauchy integral** (the landed
`analyticOnNhd_deriv_zero`).  Let `V` be open in a finite-dimensional space, `f (e, (u, t))` analytic
at every point of `V × W`, with `W` containing the bidisc `‖u‖ < a`, `‖t‖ < b`, `b > 0`, and
`‖f‖ ≤ M` on `V` times that bidisc.  Then `(e, u) ↦ ∂_t f (e, (u, t))|_{t=0}` is analytic on
`V × {‖u‖ < a}`. -/
theorem analyticOnNhd_deriv_mark_cauchy [FiniteDimensional ℂ E] {V : Set E} (hV : IsOpen V)
    {W : Set (ℂ × ℂ)} {f : E × (ℂ × ℂ) → ℂ} (hf : AnalyticOnNhd ℂ f (V ×ˢ W)) {a b M : ℝ}
    (hb : 0 < b) (hW : ∀ u t : ℂ, ‖u‖ < a → ‖t‖ < b → (u, t) ∈ W)
    (hM : ∀ e ∈ V, ∀ u t : ℂ, ‖u‖ < a → ‖t‖ < b → ‖f (e, (u, t))‖ ≤ M) :
    AnalyticOnNhd ℂ (fun x : E × ℂ => deriv (fun t : ℂ => f (x.1, (x.2, t))) 0)
      (V ×ˢ Metric.ball (0 : ℂ) a) := by
  refine analyticOnNhd_deriv_zero (E := E × ℂ) (V := V ×ˢ Metric.ball (0 : ℂ) a)
    (hV.prod Metric.isOpen_ball) (f := fun (x : E × ℂ) (t : ℂ) => f (x.1, (x.2, t)))
    (r := b) (M := M) hb ?_ ?_ ?_
  · intro l hl
    refine hf.comp (f := fun x : E × ℂ => (x.1, (x.2, l)))
      (fun _ _ => analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)) ?_
    rintro ⟨e, u⟩ ⟨he, hu⟩
    exact ⟨he, hW u l (mem_ball_zero_iff.1 hu) hl⟩
  · rintro ⟨e, u⟩ ⟨he, hu⟩ t ht
    have hpt : AnalyticAt ℂ (fun t : ℂ => f (e, (u, t))) t :=
      (hf _ ⟨he, hW u t (mem_ball_zero_iff.1 hu) (mem_ball_zero_iff.1 ht)⟩).comp_of_eq
        (analyticAt_const.prod (analyticAt_const.prod analyticAt_id)) rfl
    exact hpt.differentiableAt.differentiableWithinAt
  · rintro ⟨e, u⟩ ⟨he, hu⟩ l hl
    exact hM e he u l (mem_ball_zero_iff.1 hu) hl

end Generic

section Product

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **The resummation with the marks in the parameter, for a given pair `(F₁, Sol)`.**  The landed
`localization_expansion` applied to the product parameter `p = ((Θ, ψ̂), (um, tm))`, on the set
`(Ξ^c × B̂) × W`, `W = {(u, t) | (‖u‖ + ‖t‖) · markedRad < δ₁}`, with the functional
`F p s = FFmarked … um tm (Θ, ψ̂) s` and the agreement law "`AgHatDir` on the component and equal
marks".  The hypotheses are those of `i5_functional_hat_marked_exposed_pair`.  The four clauses are
those of `localization_expansion`; the coefficient `evTerm c … F Y p` is the landed term
`evTerm c … (FFmarked … um tm) Y (Θ, ψ̂)`:

1. sum identity at the cut point `s ≡ 1`;
2. locality: `AgHatDir Y` on the data and equal marks;
3. the bound `Eb · exp (-κ₀ · treeLenCovOne - 2 κdec · treeLenCov Y)`;
4. **joint analyticity in `(Θ, ψ̂, um, tm)`** at every point of `(Ξ^c × B̂) × W`. -/
theorem marked_expansion_product_pair (hk : 1 ≤ k) (hG : IsLevel Hm k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ : ℕ} {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb)
    {Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ}
    (hΦan : AnalyticOnNhd ℂ (fun t => Φ t.1 t.2.1 t.2.2)
      (FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁))
    (hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖Φ t.1 t.2.1 t.2.2‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2)
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) :
    -- 1. sum identity at the cut point, product parameter
    (∀ p ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁},
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2 p.1 1 =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2) Y p.1) ∧
      -- 2. locality: `AgHatDir` on the data, equal marks
      (∀ Y, ∀ p ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁},
        ∀ p' ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁},
        AgHatDir hG' Y p.1 p'.1 → p.2 = p'.2 →
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2) Y p.1 =
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p'.2.1 p'.2.2) Y p'.1) ∧
      -- 3. the bound, product parameter
      (∀ Y, ∀ p ∈ (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2) Y p.1‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- 4. joint analyticity in the data and the marks
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ℂ × ℂ) =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2) Y p.1)
        ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  classical
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  set W : Set (ℂ × ℂ) :=
    {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} with hWdef
  have hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}, ∀ w ∈ W,
      markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    intro σ hσ D hD ψh hψh w hw
    have hs' : ∀ i, ‖σ i‖ < Real.exp κ := fun i => by simpa using hσ i
    exact (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁
      (norm_extParams_lt hE1 hs') hD hψh Zm hw).1
  have hanaW := fanH_analytic_marked hC hk hG' cc
    {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ} Zm W
    hMX hdm hα hsm hF₁an hF₁ hSolan hSolprop hΦan hSup
  have hbdW : ∀ w ∈ W, ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ},
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2 u s‖ ≤
        Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := by
    intro w hw
    rintro ⟨u1, ψh⟩ ⟨⟨D, hD, rfl⟩, hψh⟩ s hs
    have hs' : ∀ i, ‖s i‖ < Real.exp κ := fun i => by simpa using hs i
    have hsx : ∀ P, ‖extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s P‖ < Real.exp κ :=
      norm_extParams_lt hE1 hs'
    have hψ := hSup s hs D hD ψh hψh w hw
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ := point_facts_core hC hF₁ hSolprop hsx
      (extParams_hs1 (X₁f := X₁f) (Gp := Gp) s) hD hψ
    show ‖Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
      (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
        flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, rawOf D))
          D.Ψ (markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
            (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh))).1
      (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) (rawOf D) ψh)‖ ≤ _
    rw [hFeq, hSeq]
    exact hΦbd _ hmem
  set cm : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcdef
  have hc : ∀ i, cm i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective cm := fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ (cm i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  have hsub : ∀ C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))),
      compY cm (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C ⊆
        Ysites Gp m₀ cm (X1 Gp m₀ j 𝒦X) C := by
    intro C
    have e1 : compY cm (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C =
        compY cm (X1 Gp m₀ j 𝒦X) C := congrArg (fun S => compY cm S C) hX₁
    rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
  have hana : AnalyticOnNhd ℂ
      (fun x : ((RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ℂ × ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm x.1.2.1 x.1.2.2 x.1.1 x.2)
      (((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ W) ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) :=
    analyticOnNhd_prod_right_comm hanaW
  have hloc : LocalityAEOn (Real.exp κ)
      ((XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ W)
      (fun i => Pset m₁ (cm i)) (compY cm (X1 Gp m₀ j 𝒦X))
      (fun C p p' => AgHatDir hG' (compY cm (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) p.1 p'.1 ∧
        p.2 = p'.2)
      (fun p s => FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2 p.1 s) := by
    have e2 : compY cm (X1 Gp m₀ j 𝒦X) = compY cm (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) :=
      congrArg (fun S => compY cm S) hX₁.symm
    rw [e2]
    rintro C ⟨u, w⟩ ⟨u', w'⟩ ⟨hu, hw⟩ ⟨hu', -⟩ s s' hs hs' hag ⟨hAg, hww⟩
    obtain rfl : w = w' := hww
    exact fanHL_local_marked hC hk hG hG' cc hcψ hMX hdm hα hsm Zm w.1 w.2 hw hcov hX₁ hconn hrow
      hF₁ hSolprop hZ hBM (fun t ht t' ht' => hΦlocDir t ht.1 t' ht'.1) C u u' hu hu' s s' hs hs'
      hag hAg
  obtain ⟨r1, r2, r3, r4⟩ := localization_expansion (c := cm) hcov hC.HBp.hd hC.HBp.hL hc hcinj
    hdisj hopt hκ₀ hκdec hκ h1 hlog hEb
    (S := (XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ W)
    (F := fun p s => FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm p.2.1 p.2.2 p.1 s)
    (Ag := fun C p p' =>
      AgHatDir hG' (compY cm (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) p.1 p'.1 ∧ p.2 = p'.2)
    (AgY := fun Y p p' => AgHatDir hG' Y p.1 p'.1 ∧ p.2 = p'.2)
    (fun C p _ => ⟨agHatDir_refl hG' _ p.1, rfl⟩)
    (fun C p p' h => ⟨agHatDir_mono hG' (hsub C) h.1, h.2⟩) hana
    (fun p hp s hs => hbdW p.2 hp.2 p.1 hp.1 s hs) hloc
  exact ⟨r1, fun Y p hp p' hp' hA hw => r2 Y p hp p' hp' ⟨hA, hw⟩, r3, r4⟩

end Product

section Block

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The clauses of `MarkedBlockExpansionDecTwo` for a given pair `(F₁, Sol)`**: the eight clauses of
the landed proposition (sum identity, locality, bound on closed bidiscs, analyticity in the marks,
Cauchy estimate, sum identity for the derivatives, mark-locality, vanishing of the `t`-derivative),
copied, as a predicate of the pair.  The landed proposition is the existence of a pair with these
clauses (`markedBlockExpansionDecTwo_iff_exists_pair`). -/
def MarkedBlockExpansionDecPair (N : ℕ) (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ)
    (Zm : Finset (unitPts Gp)) (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)) :
    Prop :=
    -- 1. sum identity
    (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
      markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) D ψh =
      ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X,
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um tm Y (rawOf D, ψh)) ∧
    -- 2. locality
    (∀ um tm : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AgHatDir hG' Y u u' →
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um tm Y u') ∧
    -- 3. bound on closed bidiscs
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um tm Y u‖ ≤
        energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y)) ∧
    -- 4. analyticity in the marks
    (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          w.1 w.2 Y u)
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) ∧
    -- 5. Cauchy estimate
    (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b →
      (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ um : ℂ, ‖um‖ ≤ a →
      ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      ‖deriv (fun t : ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um t Y u) 0‖ ≤
        energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) / t₀) ∧
    -- 6. sum identity for the derivatives
    (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
      deriv (fun tm : ℂ =>
        markedFunDec hG' cc a₁ ν BG₂ κ Zm um tm (blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
          D ψh) 0 =
      ∑ Y ∈ polyDom Gp X₁f m₀ j 𝒦X, deriv (fun t : ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um t Y (rawOf D, ψh)) 0) ∧
    -- 7. mark-locality: marks differing only on the mask, mask missing `Y`
    (∀ um tm tm' : ℂ, (‖um‖ + ‖tm‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      (‖um‖ + ‖tm'‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ y ∈ Y, unitPt hG' y ∉ Zm) →
      ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um tm Y u =
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um tm' Y u) ∧
    -- 8. the `t`-derivative at `0` vanishes when the mask misses `Y`
    (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁ →
      ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)), (∀ y ∈ Y, unitPt hG' y ∉ Zm) →
      ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
      deriv (fun t : ℂ =>
        evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
          um t Y u) 0 = 0)

/-- The landed proposition `MarkedBlockExpansionDecTwo` is the existence of a pair `(F₁, Sol)` with
the clauses `MarkedBlockExpansionDecPair` (by definition). -/
theorem markedBlockExpansionDecTwo_iff_exists_pair (N : ℕ)
    (Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ) (a₁ ν BG BG₂ κ eps δ₁ κdec cψ : ℝ)
    (Zm : Finset (unitPts Gp)) (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (m₀ j : ℕ)
    (𝒦X : Set (CTorus d L N₁ m₁ (k + 1))) (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1)))) :
    MarkedBlockExpansionDecTwo N Hm hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z ↔
      ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
          (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
        (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
        MarkedBlockExpansionDecPair N Hm hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
          F₁ Sol :=
  Iff.rfl

/-- **The block expansion along the masked tangent for a given pair, with joint analyticity.**
Under the hypotheses of `vblock_expansion_hat_marked_scaled`, for a pair `(F₁, Sol)` with the
defining properties and the analyticity of the landed pair (`i4b_analytic`, `Dec2.i4a_analytic`):
the eight clauses of `MarkedBlockExpansionDecTwo` (`MarkedBlockExpansionDecPair`), and the statement
(J): for every `Y` the term `evDec … um tm Y (Θ, ψ̂)` is analytic in `((Θ, ψ̂), (um, tm))` at every
point of `(Ξ^c × B̂) × W`, `W = {(u, t) | (‖u‖ + ‖t‖) · markedRad < δ₁}`. -/
theorem vblock_expansion_hat_marked_joint_pair
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1))))
    {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
    (hF₁an : AnalyticOnNhd ℂ F₁ {q | (∀ P, ‖q.1 P‖ < Real.exp κ) ∧ ∃ D : BgData Gp N,
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D ∧ q.2 = (D.Ψ, D.h)})
    (hF₁ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
      InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
        (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
        F₁ (s, rawOf D) = (φ, α))
    {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
    (hSolan : AnalyticOnNhd ℂ Sol {p | (∀ P, ‖p.1 P‖ < Real.exp κ) ∧
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2})
    (hSolprop : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
      StrictDataM Hm N false (2 * (K4 d L N BG κ * (xiC1 d * eps))) δ₁ p.2 →
        (Sol p).1 = dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν p.1) p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
          (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) (Sol p).2 ∧
        Small Hm (Sol p).2 (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) ∧
        Small Hm (Sol p).2 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        SupBounds Hm (Sol p).1 (cK2' d L N (famConst d L BG₂ κ) * δ₁) ∧
        (∀ δα' : Hm.Ω 1 → ℂ, Small Hm δα' (c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8)) →
          Dec2.DecFixed (coverOf Gp) Hm (compWeight L a₁) ν p.1 false p.2.2.1 p.2.1
            (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)) :
    MarkedBlockExpansionDecPair N Hm hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z F₁ Sol ∧
      ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            p.2.1 p.2.2 Y p.1)
        ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) := by
  unfold MarkedBlockExpansionDecPair
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB0 : 0 ≤ famConst d L BG₂ κ := by
    have := famConst_ge_one (L := L) hC.hS2.fam.2.1 κ hd0; linarith
  have hV : 0 ≤ cK2' d L N (famConst d L BG₂ κ) * δ₁ :=
    mul_nonneg (cK2'_nonneg hB0) hC.δ₁_pos.le
  have hρ : 0 ≤ rho4 d L N BG κ := by
    have hBG := hC.hS.fam.2.1
    have hB1 : 0 ≤ famConst d L BG κ := by
      have := famConst_ge_one (L := L) hBG κ hd0; linarith
    unfold rho4
    exact (c6'_pos hB1 (by have := gamma1_pos hd0; positivity)).le
  have ha : 0 ≤ compWeight L a₁ k :=
    (hC.HBp.weights k hk (by omega)).1.trans' (by norm_num)
  have hEb := energyBdScaled_nonneg (d := d) (L := L) (N := N) ha hV hC.δ₁_pos.le hρ
  have hΦbd : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ‖blockEnergyFun Gp Hm (compWeight L a₁) ν k z t.1 t.2.1 t.2.2‖ ≤
        energyBdScaled d L N (compWeight L a₁) k
          (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
          Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X) := fun t ht => by
    rw [hΔ]; simpa using blockEnergyFun_bound_scaled hC hG hG' hk le_rfl z ht
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, eM⟩ := i5_functional_hat_marked_exposed_pair hC hk hG hG'
    cc hcψ Zm hMX hdm hα hsm hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
    ((blockEnergyFun_analytic _ ν k z).mono (Set.subset_univ _)) hΦbd
    hconn hrow (Z := readSites Hm k z) (Zα := ↑(blockSites d L N₁ m₁ (k + 1) k z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local_dir _ ν k z hα hδ hψ)
    hF₁an hF₁ hSolan hSolprop
  obtain ⟨-, -, -, hJ⟩ := marked_expansion_product_pair hC hk hG hG'
    cc hcψ Zm hMX hdm hα hsm hcov hX₁ hopt hκ₀ hκdec hκ h1 hlog hEb
    (Φ := blockEnergyFun Gp Hm (compWeight L a₁) ν k z)
    ((blockEnergyFun_analytic _ ν k z).mono (Set.subset_univ _)) hΦbd
    hconn hrow (Z := readSites Hm k z) (Zα := ↑(blockSites d L N₁ m₁ (k + 1) k z)) hZ hmar
    (fun t _ t' _ _ hα hδ _ hψ => blockEnergyFun_local_dir _ ν k z hα hδ hψ)
    hF₁an hF₁ hSolan hSolprop
  have hexp : ∀ Y : Set (CTorus d L N₁ m₁ (k + 1)),
      Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y) =
        Real.exp (-2 * κdec * treeLenCov Gp m₀ Y) := by
    intro Y; rw [hΔ]; congr 1; ring
  refine ⟨⟨e1, e2, ?_, e6, ?_, e8, eM, ?_⟩, hJ⟩
  · intro a b ha hb hab um tm hu ht Y u hu'
    have := e4 a b ha hb hab um tm hu ht Y u hu'
    rwa [hexp] at this
  · intro a b t₀ ha hb ht₀ htb hab um hu Y u hu'
    have := e7 a b t₀ ha hb ht₀ htb hab um hu Y u hu'
    rwa [hexp] at this
  · intro um h0 Y hY u hu
    have hnhds : {t : ℂ | (um, t) ∈ {w : ℂ × ℂ |
        (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}} ∈ nhds (0 : ℂ) :=
      ((isOpen_markedRadiusSet (markedRad d L N k a₁ κ cψ cc) δ₁).preimage
        (continuous_const.prodMk continuous_id)).mem_nhds h0
    have hev : (fun t : ℂ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
        (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm um t Y u) =ᶠ[nhds (0 : ℂ)]
        fun _ => evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol
          (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm um 0 Y u := by
      filter_upwards [hnhds] with t ht
      exact eM um t 0 ht h0 Y hY u hu
    rw [hev.deriv_eq]
    simp

/-- **`markedEv_joint_param`: joint analyticity of the localized marked terms, statement (J).**
Under the hypotheses of `vblock_expansion_hat_marked_scaled` there is one pair `(F₁, Sol)` (not
depending on the marks) for which the eight clauses of the landed `MarkedBlockExpansionDecTwo` hold
and, for every `Y`, the term `evDec … um tm Y (Θ, ψ̂)` is analytic in `((Θ, ψ̂), (um, tm))` at every
point of `(Ξ^c × B̂) × W`, `B̂ = {‖ψ̂‖ ≤ c_ψ}`, `W = {(u, t) | (‖u‖ + ‖t‖) · markedRad < δ₁}` (as a
function on all of `(RawData × hat fields) × ℂ²`, like the landed analyticity statements). -/
theorem markedEv_joint_param
    (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hk : 1 ≤ k) (hG : IsLevel Hm k) (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    (hΔ : treeLenCovOne m₀ j X = 0)
    {κdec κ₀ : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin Gp X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      MarkedBlockExpansionDecPair N Hm hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
        F₁ Sol ∧
      ∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν hG' cc F₁ Sol (blockEnergyFun Gp Hm (compWeight L a₁) ν k z) Zm
            p.2.1 p.2.2 Y p.1)
        ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) := by
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hB2 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le
      (by have := one_le_xiC1 d; have := hC.eps_pos; positivity))
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB2 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  exact ⟨F₁, Sol, vblock_expansion_hat_marked_joint_pair hC hk hG hG' cc hcψ Zm hMX hdm hα hsm
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ hmar hF₁an hF₁ hSolan hSolprop⟩

end Block

end Balaban.Localization

namespace Balaban.Fluctuation

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Localization Balaban.Polymer Finset Matrix

section Chart

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ ϱm : ℝ}
  (S : StepSetting d L N₁ m₁ k N ϱ)

/-- **From the chart to the parameter set `physV`.**  If `f ((Θ, x), w)` is analytic at every point
of `(Ξ^c × B) × W` (as a function on all of `(RawData × G) × H`), then on the parameter space
`physParam = rawSub × sources` the function `((e, x), w) ↦ f ((e.1, x), w)` is analytic at every
point of `(physV × B) × W`; the source coordinate of `e` does not enter.  (Composition with the
continuous linear inclusion `physIncl`.) -/
theorem analyticOnNhd_physV_of_chart {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    [NormedAddCommGroup H] [NormedSpace ℂ H] (a₁ ν eps : ℝ) {B : Set G} {W : Set H}
    {f : (RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × H → ℂ}
    (hf : AnalyticOnNhd ℂ f ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B) ×ˢ W)) :
    AnalyticOnNhd ℂ (fun p : (physParam N S × G) × H =>
      f (((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2), p.2))
      ((physV S a₁ ν eps ×ˢ B) ×ˢ W) := by
  let g : (physParam N S × G) × H →L[ℂ] (RawData d L (N₁ * L ^ m₁) (k + 1) N × G) × H :=
    (((rawSub N S.G').subtypeL.comp (ContinuousLinearMap.fst ℂ _ _)).prodMap
      (ContinuousLinearMap.id ℂ G)).prodMap (ContinuousLinearMap.id ℂ H)
  refine hf.comp (g.analyticOnNhd _) fun p hp => ?_
  exact ⟨⟨hp.1.1.1, hp.1.2⟩, hp.2⟩

variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))} {j : ℕ}
variable {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **Joint analyticity of the localized marked terms on the parameter set `physV`, and of the
derivative marks.**  For a step `S` (`Gp = S.G'`), under the hypotheses of
`vblock_expansion_hat_marked_scaled` there is one pair `(F₁, Sol)` such that:

1. the eight clauses of the landed `MarkedBlockExpansionDecTwo` hold (`MarkedBlockExpansionDecPair`);
2. (J): `evDec … um tm Y (Θ, ψ̂)` is analytic in `((Θ, ψ̂), (um, tm))` at every point of
   `(Ξ^c × B̂) × W`;
3. on the parameter space `physParam = rawSub × sources`: `((e, ψ̂), (um, tm)) ↦ evDec … Y (e.1, ψ̂)`
   is analytic at every point of `(physV × B̂) × W`;
4. the derivative marks: for every hat field `‖ψ̂‖ ≤ c_ψ` and radii `a ≥ 0`, `b > 0` with
   `(a + b) · markedRad < δ₁`, `(e, u) ↦ ∂_t evDec … u t Y (e.1, ψ̂)|_{t=0}` is analytic on
   `physV × {‖u‖ < a}` (by the Cauchy integral over the `t`-disc of radius `b`,
   `analyticOnNhd_deriv_zero`): the shape of the field `holG` of `ParamMarkFamily`, per label;
5. the derivative marks jointly with the hat field: `((e, ψ̂), u) ↦ ∂_t evDec … u t Y (e.1, ψ̂)|_{t=0}`
   is analytic at every point of `(physV × B̂) × {u | (u, 0) ∈ W}`. -/
theorem markedEv_joint_physV
    (hC : FlCore N S.G' Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
    (hG : IsLevel Hm k) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts S.G'))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
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
    (z : Torus d (N₁ * L ^ m₁ * L ^ (k + 1 - (k + 1))))
    (hZ : readSites Hm k z ⊆ ↑X₁f)
    (hmar : BlockMargin S.G' X₁f
      (↑(blockSites d L N₁ m₁ (k + 1) k z) : Set (CTorus d L N₁ m₁ (k + 1)))) :
    ∃ (F₁ : DecParams S.G' × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (S.G'.Ω 1 × Fin N → ℂ) × (S.G'.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf S.G') × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      -- 1. the landed clauses
      MarkedBlockExpansionDecPair N Hm S.hG' cc a₁ ν BG BG₂ κ eps δ₁ κdec cψ Zm X₁f m₀ j 𝒦X z
        F₁ Sol ∧
      -- 2. (J) on the chart
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y p.1)
        ((XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
      -- 3. (J) on the parameter set `physV`
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y
            ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2))
        ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) ∧
      -- 4. the derivative marks on `physV × {‖u‖ < a}`, fixed hat field
      (∀ Y, ∀ ψh : unitPts S.G' × Fin N → ℂ, (∀ q, ‖ψh q‖ ≤ cψ) →
        ∀ a b : ℝ, 0 ≤ a → 0 < b → (a + b) * markedRad d L N k a₁ κ cψ cc < δ₁ →
        AnalyticOnNhd ℂ (fun p : physParam N S × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2 t Y
            ((p.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)) 0)
          (physV S a₁ ν eps ×ˢ Metric.ball (0 : ℂ) a)) ∧
      -- 5. the derivative marks jointly with the hat field
      (∀ Y, AnalyticOnNhd ℂ
        (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × ℂ => deriv (fun t : ℂ =>
          evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
            (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2 t Y
            ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2)) 0)
        ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
          {u : ℂ | (‖u‖ + ‖(0 : ℂ)‖) * markedRad d L N k a₁ κ cψ cc < δ₁})) := by
  obtain ⟨F₁, Sol, hP, hJ⟩ := markedEv_joint_param hC S.hk1 hG S.hG' cc hcψ Zm hMX hdm hα hsm
    hcov hX₁ hconn hrow hopt hΔ hκ₀ hκdec hκ h1 hlog z hZ hmar
  have hT2 : ∀ Y, AnalyticOnNhd ℂ
      (fun p : (physParam N S × (unitPts S.G' × Fin N → ℂ)) × (ℂ × ℂ) =>
        evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm p.2.1 p.2.2 Y
          ((p.1.1.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), p.1.2))
      ((physV S a₁ ν eps ×ˢ {ψh : unitPts S.G' × Fin N → ℂ | ∀ q, ‖ψh q‖ ≤ cψ}) ×ˢ
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁}) := fun Y => by
    have key := analyticOnNhd_physV_of_chart S a₁ ν eps (hJ Y)
    exact key
  have hbd := hP.2.2.1
  refine ⟨F₁, Sol, hP, hJ, hT2, ?_, fun Y => ?_⟩
  · intro Y ψh hψh a b ha hb hab
    have hf := analyticOnNhd_slice_mid (hT2 Y) (y₀ := ψh) hψh
    have hW : ∀ u t : ℂ, ‖u‖ < a → ‖t‖ < b → (u, t) ∈
        {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) * markedRad d L N k a₁ κ cψ cc < δ₁} :=
      fun u t hu ht => mem_markedRadiusSet_of_pos hC.δ₁_pos hab hu.le ht.le
    have hM : ∀ e ∈ physV S a₁ ν eps, ∀ u t : ℂ, ‖u‖ < a → ‖t‖ < b →
        ‖evDec X₁f m₀ j 𝒦X a₁ ν S.hG' cc F₁ Sol
          (blockEnergyFun S.G' Hm (compWeight L a₁) ν k z) Zm u t Y
          ((e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N), ψh)‖ ≤
          energyBdScaled d L N (compWeight L a₁) k
            (cK2' d L N (famConst d L BG₂ κ) * δ₁) δ₁ (rho4 d L N BG κ) *
            Real.exp (-2 * κdec * treeLenCov S.G' m₀ Y) := by
      intro e he u t hu ht
      have hΘ : (e.1 : RawData d L (N₁ * L ^ m₁) (k + 1) N) ∈
          XiCRaw S.G' (compWeight L a₁) ν (k + 1) 1 eps := he.1
      exact hbd a b ha hb.le hab u t hu.le ht.le Y _ ⟨hΘ, hψh⟩
    have key := analyticOnNhd_deriv_mark_cauchy (isOpen_physV S a₁ ν eps hC.HBp) hf hb hW hM
    exact key
  · have key := analyticOnNhd_deriv_mark (hT2 Y)
    exact key

end Chart

end Balaban.Fluctuation
