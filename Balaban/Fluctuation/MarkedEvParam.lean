/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.MarkedI5Functional

/-!
# Dependence of the localized marked block terms on the marks (`MarkedEvParam`)

`i5_functional_hat_marked` produces, for fixed marks `(um, tm)`, an existentially quantified family
`Ev`.  Here the family is exposed: `Ev Y = evTerm c Gp m₀ X₁ (FFmarked … um tm) Y`, where
`FFmarked` is the inline cut-parameter functional of the fan hypothesis (a literal copy), built from
the two auxiliary maps `F₁` (background) and `Sol` (fluctuation solution) of the landed proof.
Because `F₁`, `Sol` do not depend on the marks, one pair serves for all marks of the open radius set
`W = {(u, t) | (‖u‖ + ‖t‖) · B < δ₁}`.

* `expansion_of_AE_hat_dir_exposed`: `expansion_of_AE_hat_dir` with `Ev = evTerm`.
* `FFmarked`, `FFmarked_one_zero`, `FFmarked_empty` (value at `(1, 0)`; empty block).
* `norm_deriv_mark_le` (Cauchy estimate), `deriv_mark_eq_of_eq_near` (locality of the mark
  derivative), `deriv_sum_marks` (sum identity for derivatives), `deriv_evTerm_marked_empty`
  (empty block).
* `i5_functional_hat_marked_exposed_of_fan`, `i5_functional_hat_marked_exposed`: the clauses of
  `i5_functional_hat_marked` (sum identity, locality, bound, analyticity in the data) for the
  explicit family and every mark of `W`, together with analyticity in the marks at fixed data, the
  bound on every closed bidisc inside `W`, the Cauchy estimate for the `t`-derivative at `0`,
  locality of that derivative and the sum identity for derivatives.

`MARK-COUNT` (decoupled resummation), `MARK-PARAM` and the marked family are NOT proved here;
nothing depends on a choice of generating sets for the class terms.
-/

@[expose] public section

namespace Balaban.Localization

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Analysis
  Balaban.Fluctuation Balaban.Polymer Finset Matrix

section Exposed

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν κ eps δ₁ : ℝ} {j : ℕ} {m₀ : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}

/-- **The marked cut-parameter functional.**  For a fixed pair of marks `(um, tm)`, the functional
`(Θ, ψ̂) ↦ (s ↦ Φ (F₁ (s, Θ)) (Sol (s, …)).1 (Θ, markedHatPsiF … s Θ ψ̂))` of the fan hypothesis of
`i5_functional_hat_marked_of_fan`, with the cut parameters `s` on the blocks of `X₁f`
extended by `1` outside. -/
noncomputable def FFmarked (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (a₁ ν : ℝ)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gp)) (um tm : ℂ) :
    RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ :=
  fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
    (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
      flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        u.1.1 (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
    (u.1, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
      (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2)

/-- At the marks `(1, 0)` the marked functional is the unmarked one (`hatPsiF` in place of the
masked tangent). -/
theorem FFmarked_one_zero (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (Zm : Finset (unitPts Gp)) :
    FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm 1 0 =
      fun u s => Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s, u.1))
            u.1.1 (hatPsiF Gp a₁ ν hG' cc F₁
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2))).1
        (u.1, hatPsiF Gp a₁ ν hG' cc F₁
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) s) u.1 u.2) := by
  funext u s
  simp only [FFmarked, markedHatPsiF_one_zero]

/-- For the empty block the mask vanishes: the marked functional does not depend on `tm`. -/
theorem FFmarked_empty (X₁f : Finset (CTorus d L N₁ m₁ (k + 1))) (hG' : IsLevel Gp (k + 1))
    (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    (um tm : ℂ) :
    FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ (∅ : Finset (unitPts Gp)) um tm =
      FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ (∅ : Finset (unitPts Gp)) um 0 := by
  have h : ∀ (s : DecParams Gp) (Θ : RawData d L (N₁ * L ^ m₁) (k + 1) N)
      (ψh : unitPts Gp × Fin N → ℂ), markedHatPsiF a₁ ν hG' cc F₁ (∅ : Finset (unitPts Gp)) um tm
        s Θ ψh = markedHatPsiF a₁ ν hG' cc F₁ (∅ : Finset (unitPts Gp)) um 0 s Θ ψh := by
    intro s Θ ψh
    funext y i
    rw [markedHatPsiF_apply, markedHatPsiF_apply]
    simp
  funext u s
  simp only [FFmarked, h]


/-- **`expansion_of_AE_hat_dir` with the family exposed.**  The same hypotheses and the same four
clauses, with `Ev` equal to `evTerm`. -/
theorem expansion_of_AE_hat_dir_exposed (hd : 3 ≤ d) (hL : 3 ≤ L) (hG' : IsLevel Gp (k + 1))
    (hcov : CovSetup Gp m₀ j X 𝒦X) {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hopt : ∃ (W₀ : Finset (CTorus d L N₁ m₁ (k + 1)))
      (E₀ : Finset (CTorus d L N₁ m₁ (k + 1) × CTorus d L N₁ m₁ (k + 1))),
      ConnStruct W₀ E₀ ∧ (↑W₀ ⊆ X) ∧ MeetsOne m₀ j 𝒦X W₀ ∧
        bondCost (scaleW L m₀ m₁ j) E₀ = treeLenCovOne m₀ j X)
    {κdec κ₀ Eb : ℝ} (hκ₀ : 0 ≤ κ₀) (hκdec : 3 * κ₀ + 3 ≤ κdec)
    (hκ : 4 * d * (((2 * L + 1) ^ d : ℕ) : ℝ) * κdec ≤ κ) (h1 : 1 ≤ (κ / 2 - 1) / 2)
    (hlog : Real.log ((((2 * L + 1) ^ d : ℕ) : ℝ) * (((L ^ m₀) ^ d : ℕ) : ℝ)) ≤ (κ / 2 - 1) / 2)
    (hEb : 0 ≤ Eb) {B' : Set (unitPts Gp × Fin N → ℂ)}
    {FF : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ) →
      (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) → ℂ}
    (hana : AnalyticOnNhd ℂ (fun p : (RawData d L (N₁ * L ^ m₁) (k + 1) N ×
        (unitPts Gp × Fin N → ℂ)) ×
        (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => FF p.1 p.2)
      ((XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B') ×ˢ
        polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)))
    (hbd : ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
      ∀ s ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ),
      ‖FF u s‖ ≤ Eb * Real.exp (-(κdec - 1) * treeLenCovOne m₀ j X))
    (hloc : LocalityAEOn (Real.exp κ) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')
      (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
      (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
      (fun C u u' => AgHatDir hG' (compY
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u') FF) :
    (∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        FF u 1 = ∑ Y ∈ polymerDomains
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X), evTerm
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u) ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        AgHatDir hG' Y u u' → evTerm
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u = evTerm
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u') ∧
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B',
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      (∀ Y, AnalyticOnNhd ℂ (evTerm
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) FF Y) (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')) := by
  classical
  set c : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℕ × CTorus d L N₁ m₁ (k + 1) :=
    fun i => i.1.1 with hcdef
  have hc : ∀ i, c i ∈ cubeIdx Gp := fun i => i.1.2
  have hcinj : Function.Injective c := fun i i' h => Subtype.ext (Subtype.ext h)
  have hdisj : ∀ i, Disjoint (Pset m₁ (c i)) (X1 Gp m₀ j 𝒦X) := fun i => hX₁ ▸ i.2
  have hsub : ∀ C : Finset (ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1)))),
      compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C ⊆
        Ysites Gp m₀ c (X1 Gp m₀ j 𝒦X) C := by
    intro C
    have e1 : compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C =
        compY c (X1 Gp m₀ j 𝒦X) C := congrArg (fun S => compY c S C) hX₁
    rw [e1]; exact compY_subset_Ysites hcov.hU hcov.hN hc _ C
  have hloc' : LocalityAEOn (Real.exp κ)
      (XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ B')
      (fun i => Pset m₁ (c i)) (compY c (X1 Gp m₀ j 𝒦X))
      (fun C u u' => AgHatDir hG' (compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u') FF := by
    have e2 : compY c (X1 Gp m₀ j 𝒦X) = compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) :=
      congrArg (fun S => compY c S) hX₁.symm
    rw [e2]; exact hloc
  exact localization_expansion (c := c) hcov hd hL hc hcinj hdisj
    hopt hκ₀ hκdec hκ h1 hlog hEb
    (Ag := fun C u u' => AgHatDir hG' (compY c (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u')
    (AgY := fun Y u u' => AgHatDir hG' Y u u')
    (fun C u _ => agHatDir_refl hG' _ u)
    (fun C u u' h => agHatDir_mono hG' (hsub C) h) hana hbd hloc'


end Exposed

section Generic

/-- A closed bidisc `‖u‖ ≤ a`, `‖t‖ ≤ b` with `(a + b) · B < δ₁` lies in the radius set
(no sign condition on `B`, but `0 < δ₁`). -/
theorem mem_markedRadiusSet_of_pos {B δ₁ a b : ℝ} (hδ : 0 < δ₁)
    (h : (a + b) * B < δ₁) {u t : ℂ} (hu : ‖u‖ ≤ a) (ht : ‖t‖ ≤ b) :
    (u, t) ∈ {p : ℂ × ℂ | (‖p.1‖ + ‖p.2‖) * B < δ₁} := by
  rcases le_or_gt 0 B with hB | hB
  · exact mem_markedRadiusSet hB h hu ht
  · show (‖u‖ + ‖t‖) * B < δ₁
    nlinarith [norm_nonneg u, norm_nonneg t]

/-- **Cauchy estimate for the mark derivative.**  If `g` is analytic on a set `W` of marks that
contains the closed disc `{(um, t) | ‖t‖ ≤ b}` and `‖g‖ ≤ C` on `W`, then for `0 < t₀ ≤ b`
`‖∂_t g(um, t)|_{t=0}‖ ≤ C / t₀`. -/
theorem norm_deriv_mark_le {W : Set (ℂ × ℂ)} {g : ℂ × ℂ → ℂ} {C : ℝ} {um : ℂ} {b t₀ : ℝ}
    (hg : AnalyticOnNhd ℂ g W) (hbd : ∀ w ∈ W, ‖g w‖ ≤ C) (ht₀ : 0 < t₀) (htb : t₀ ≤ b)
    (hW : ∀ t : ℂ, ‖t‖ ≤ b → (um, t) ∈ W) :
    ‖deriv (fun t : ℂ => g (um, t)) 0‖ ≤ C / t₀ := by
  have hd : DifferentiableOn ℂ (fun t : ℂ => g (um, t)) (Metric.closedBall (0 : ℂ) t₀) := by
    intro t ht
    have ht' : ‖t‖ ≤ b := by
      have := mem_closedBall_zero_iff.1 ht
      linarith
    exact ((hg _ (hW t ht')).comp (g := g) (f := fun t : ℂ => (um, t))
      (analyticAt_const.prod analyticAt_id)).differentiableAt.differentiableWithinAt
  have hcl : DiffContOnCl ℂ (fun t : ℂ => g (um, t)) (Metric.ball (0 : ℂ) t₀) :=
    hd.diffContOnCl_ball Set.Subset.rfl
  refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le ht₀ hcl (fun z hz => ?_)
  have hz' : ‖z‖ ≤ b := by
    have := mem_sphere_zero_iff_norm.1 hz
    linarith
  exact hbd _ (hW z hz')

/-- The slice `t ↦ g (um, t)` of a function analytic at `(um, 0)` is differentiable at `0`. -/
theorem differentiableAt_mark_slice {g : ℂ × ℂ → ℂ} {um : ℂ} (h : AnalyticAt ℂ g (um, 0)) :
    DifferentiableAt ℂ (fun t : ℂ => g (um, t)) 0 :=
  (h.comp_of_eq (f := fun t : ℂ => (um, t)) (analyticAt_const.prod analyticAt_id)
    rfl).differentiableAt

/-- **Locality of the mark derivative.**  If two functions of `t` agree on a neighbourhood of `0`,
their derivatives at `0` agree. -/
theorem deriv_mark_eq_of_eq_near {f g : ℂ → ℂ} {ε : ℝ} (hε : 0 < ε)
    (h : ∀ t : ℂ, ‖t‖ < ε → f t = g t) : deriv f 0 = deriv g 0 := by
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hε] with t ht
  exact h t (by simpa using ht)

/-- **Sum identity for mark derivatives.**  If `f t = ∑ i ∈ s, g i t` for all `t` with
`(um, t)` in an open set `W` of marks, `(um, 0) ∈ W`, and each `g i` is differentiable at `0`, then
`f' (0) = ∑ i ∈ s, (g i)' (0)`. -/
theorem deriv_sum_marks {ι : Type*} (s : Finset ι) {W : Set (ℂ × ℂ)} (hW : IsOpen W) {um : ℂ}
    (h0 : (um, (0 : ℂ)) ∈ W) {f : ℂ → ℂ} {g : ι → ℂ → ℂ}
    (hsum : ∀ t : ℂ, (um, t) ∈ W → f t = ∑ i ∈ s, g i t)
    (hd : ∀ i, DifferentiableAt ℂ (g i) 0) :
    deriv f 0 = ∑ i ∈ s, deriv (g i) 0 := by
  have hnhds : {t : ℂ | (um, t) ∈ W} ∈ nhds (0 : ℂ) :=
    (hW.preimage (continuous_const.prodMk continuous_id)).mem_nhds h0
  have hev : f =ᶠ[nhds (0 : ℂ)] fun t => ∑ i ∈ s, g i t := by
    filter_upwards [hnhds] with t ht using hsum t ht
  rw [hev.deriv_eq, deriv_fun_sum (fun i _ => hd i)]

end Generic

section Core

variable {d L N₁ m₁ k N : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱm : ℝ}
variable {Gp : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱ}
variable {Hm : GeneratingSet d L (N₁ * L ^ m₁) (k + 1) ϱm}
variable {a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁ : ℝ} {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
variable (hC : FlCore N Gp Hm a₁ ν c BG κ eps Kc Cx c₂ BG₂ δ₁)
include hC

/-- **`i5_functional_hat_marked_of_fan` with the family exposed, uniformly in the marks.**
The pair `(F₁, Sol)` of the landed proof does not depend on the marks; for it and every mark
`(um, tm)` of the open radius set `W = {(u, t) | (‖u‖ + ‖t‖) · B < δ₁}`
(`B = √N · (‖cc‖ · (C_sup · cψ))`) one has, with
`Ev Y = evTerm c Gp m₀ X₁ (FFmarked … um tm) Y`:

* the sum identity of `i5_functional_hat_marked` (clause 1), the locality `AgHatDir`, the bound
  `Eb · exp (-κ₀ · treeLenCovOne - 2 κdec · treeLenCov Y)` and analyticity in the data;
* the same bound on every closed bidisc `‖u‖ ≤ a`, `‖t‖ ≤ b`, `(a + b) · B < δ₁`;
* for fixed data, analyticity of `(u, t) ↦ Ev Y` on `W` (separately in the marks; the data domain
  `XiCRaw` is not open, so no joint statement is made);
* the Cauchy estimate `‖∂_t Ev Y (um, t)|_{t=0}‖ ≤ bound / t₀` for `0 < t₀ ≤ b`, `‖um‖ ≤ a`;
* the sum identity for the `t`-derivatives of the block functional at `0`. -/
theorem i5_functional_hat_marked_exposed_of_fan (hk : 1 ≤ k) (hG : IsLevel Hm k)
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
    (hfan : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
      ∀ {F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)}
      (_ : ∀ (s : DecParams Gp) (D : BgData Gp N), (∀ P, ‖s P‖ < Real.exp κ) →
        InUnionDomainC Gp (bgC0 d L N) (c7 d L N BG κ) ν D → ∀ (φ : Gp.Ω 1 × Fin N → ℂ)
          (α : Gp.Ω 1 → ℂ), IsDecBg Gp (compWeight L a₁) ν (rho4 d L N BG κ) s D φ α →
          F₁ (s, rawOf D) = (φ, α))
      {Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)}
      (_ : ∀ p : Dec2.DecParams (coverOf Gp) × Edat Hm N, (∀ P, ‖p.1 P‖ < Real.exp κ) →
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
              (pertSource Hm (compWeight L a₁) p.2.2.2.1 p.2.2.2.2) δα' → δα' = (Sol p).2)),
      LocalityAEOn (Real.exp κ)
        (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})
        (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => Pset m₁ i.1.1)
        (compY (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))))
        (fun C u u' => AgHatDir hG' (compY
          (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) C) u u')
        (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm)) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      -- sum identity, every mark of the radius set
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y (rawOf D, ψh)) ∧
      -- locality
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' →
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u =
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u') ∧
      -- the bound, every mark of the radius set
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- the bound, uniform on every closed bidisc
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- analyticity in the data
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, AnalyticOnNhd ℂ
          (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y)
          (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      -- analyticity in the marks, at fixed data
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) ∧
      -- Cauchy estimate for the mark derivative at `t = 0`
      (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖deriv (fun t : ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um t) Y u) 0‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y) / t₀) ∧
      -- sum identity for the derivatives at `t = 0`
      (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        deriv (fun tm : ℂ =>
          Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))) 0 =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), deriv (fun t : ℂ =>
            evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
              (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um t) Y (rawOf D, ψh)) 0) := by
  classical
  have hd0 : 0 < d := by have := hC.HBp.hd; omega
  have hc1 := one_le_xiC1 d
  have hε := hC.eps_pos
  have hδ0 : 0 < xiC1 d * eps := by positivity
  have hB0 : 0 ≤ 2 * (K4 d L N BG κ * (xiC1 d * eps)) :=
    mul_nonneg (by norm_num) (mul_nonneg (K4_pos hC.hS.fam.2.1 hd0).le hδ0.le)
  obtain ⟨F₁, hF₁an, hF₁⟩ := i4b_analytic hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM
  obtain ⟨Sol, hSolan, hSolprop⟩ := Dec2.i4a_analytic (N := N) hC.hS2.fam hC.hS2.an
    hC.SM.toCoverBase hC.hκ.le hC.hM2 false hB0 hC.δ₁_pos.le hC.B_le hC.δ₁_le
  have hE1 : 1 < Real.exp κ := Real.one_lt_exp_iff.2 hC.hκ
  set W : Set (ℂ × ℂ) := {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
    (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁} with hWdef
  have hWopen : IsOpen W := isOpen_markedRadiusSet _ _
  have hSup : ∀ σ ∈ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
        (fun _ => Real.exp κ), ∀ D : BgData Gp N,
      XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
      ∀ ψh ∈ {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ}, ∀ w ∈ W,
      markedHatPsiF a₁ ν hG' cc F₁ Zm w.1 w.2
        (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) σ)
        (rawOf D) ψh ∈ FlBall Hm δ₁ := by
    intro σ hσ D hD ψh hψh w hw
    have hs' : ∀ i, ‖σ i‖ < Real.exp κ := fun i => by simpa using hσ i
    exact (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁
      (norm_extParams_lt hE1 hs') hD hψh Zm hw).1
  have hanaW := fanH_analytic_marked hC hk hG' cc
    {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} Zm W
    hMX hdm hα hsm hF₁an hF₁ hSolan hSolprop hΦan hSup
  have hbdW : ∀ w ∈ W, ∀ u ∈ XiCRaw (N := N) Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
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
  have hexp := fun (um tm : ℂ) (hw : (‖um‖ + ‖tm‖) *
      (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁) =>
    expansion_of_AE_hat_dir_exposed (a₁ := a₁) hC.HBp.hd hC.HBp.hL hG' hcov hX₁ hopt hκ₀ hκdec
      hκ h1 hlog hEb
      (FF := FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm)
      (analyticOnNhd_slice_marks hanaW (show (um, tm) ∈ W from hw))
      (fun u hu s hs => hbdW (um, tm) hw u hu s hs)
      (hfan um tm hw hF₁ hSolprop)
  have hanaM : ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u) W := by
    intro Y u hu
    have hslice : AnalyticOnNhd ℂ (fun x : (ℂ × ℂ) × (ParIdx Gp
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm x.1.1 x.1.2 u x.2)
        (W ×ˢ polydisc (0 : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ)
          (fun _ => Real.exp κ)) := by
      refine hanaW.comp (f := fun x : (ℂ × ℂ) × (ParIdx Gp
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) => (((u, x.2), x.1)))
        (fun x _ => (analyticAt_const.prod analyticAt_snd).prod analyticAt_fst)
        (fun x hx => ⟨⟨hu, hx.2⟩, hx.1⟩)
    intro w hw
    unfold evTerm
    refine Finset.analyticAt_fun_sum _ fun C _ => ?_
    exact analyticOnNhd_coef (Φ := fun x : (ℂ × ℂ) × (ParIdx Gp
        (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) → ℂ) =>
        FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm x.1.1 x.1.2 u x.2) hE1 hWopen hslice
      (fun x hx => hbdW x.1 hx.1 u hu x.2 hx.2) C w hw
  have hsumall : ∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y (rawOf D, ψh) := by
    intro um tm hw D hD ψh hψh
    have hsum' := (hexp um tm hw).1 (rawOf D, ψh) ⟨⟨D, hD, rfl⟩, hψh⟩
    rw [← hsum']
    have hsx : ∀ P : ↥(cubeIdx Gp), ‖(fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) P‖ < Real.exp κ :=
      fun P => by simpa using hE1
    have hs1 : ∀ (P : ℕ × CTorus d L N₁ m₁ (k + 1)) (hP : P ∈ cubeIdx Gp), P ∉ parCubes Gp X₁f →
        (fun _ : ↥(cubeIdx Gp) => (1 : ℂ)) ⟨P, hP⟩ = 1 := fun P hP hPn => rfl
    have hψ1 := (markedHatPsiF_mem_flBallLC hC hk hG hG' cc hcψ hMX hdm hα hsm hF₁ hsx hD hψh
      Zm hw).1
    symm
    show Φ (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
        (Sol (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1,
          flEdat Gp Hm (F₁ (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1, rawOf D))
            D.Ψ (markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
              (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh))).1
        (rawOf D, markedHatPsiF a₁ ν hG' cc F₁ Zm um tm
          (extParams Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) 1) (rawOf D) ψh) = _
    rw [extParams_one]
    set ψ' := markedHatPsiF a₁ ν hG' cc F₁ Zm um tm (fun _ => 1) (rawOf D) ψh with hψ'def
    obtain ⟨φ, α, δφ, δα, hI, hFeq, hstrict, hSeq, hmem⟩ :=
      point_facts_core hC hF₁ hSolprop hsx hs1 hD hψ1
    have hδ1 : xiC1 d * eps ≤ c7 d L N BG κ := hC.c7le
    have hδ0' : xiC1 d * eps ≤ bgC0 d L N := hδ1.trans ((c7_le_bgC1 d L N BG κ).trans
      (bgC1_le_bgC0 d L N hd0))
    have hνε : ν * ((L : ℝ) ^ (k + 1)) ^ 2 * (xiC1 d * eps) ^ 2 ≤ (xiC1 d * eps) ^ 2 := by
      have := hC.HBp.massLe; nlinarith [sq_nonneg (xiC1 d * eps)]
    have hDom := xiCData_inDomainC hC.HBp hC.small1 hD
    obtain ⟨-, hφ1, hα1⟩ := i4b_one hC.hS hC.Sp hC.HBp hC.hκ.le hC.hM hδ0 le_rfl hδ0' hδ1
      hνε hDom hI
    have hψeq : ψ' = liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
        (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
        (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
        tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
        (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
        (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
        (unitQ Gp) (unitP Gp) *ᵥ ψh))) := by
      rw [hψ'def, markedHatPsiF_eq_liftC]
      unfold hatSqrtF
      rw [hFeq, extS_one, hφ1, hα1]
      rfl
    rw [← hψeq]
    rw [hFeq, hSeq]
    obtain ⟨hfld, hfix, hs6, -, -, huniq⟩ := hSolprop ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
      flEdat Gp Hm (φ, α) D.Ψ ψ') hsx hstrict
    have hmult := flMult_spec (C := coverOf Gp) (Hm := Hm) (a := compWeight L a₁) (ν := ν)
      (ρ := c6' d L N (famConst d L BG₂ κ) (gamma1 d / 8))
      (s := fun _ : ↥(cubeIdx Gp) => (1 : ℂ))
      (e := flEdat Gp Hm (φ, α) D.Ψ ψ') ⟨hs6, hfix⟩ (fun δα' h => huniq δα' h.1 h.2)
    have hfl : flFieldOne Gp Hm BG₂ κ a₁ ν D ψ' = δφ := by
      have hSol1 : (Sol ((fun _ : ↥(cubeIdx Gp) => (1 : ℂ)),
          flEdat Gp Hm (φ, α) D.Ψ ψ')).1 = δφ := congrArg Prod.fst hSeq
      unfold flFieldOne flField
      rw [hφ1, hα1]
      exact (congrArg (dphi Hm (Dec2.decG (coverOf Gp) Hm (compWeight L a₁) ν
        (fun _ : ↥(cubeIdx Gp) => (1 : ℂ))) (flEdat Gp Hm (φ, α) D.Ψ ψ').2.1
        (flEdat Gp Hm (φ, α) D.Ψ ψ').1 (pertSource Hm (compWeight L a₁)
        (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.1 (flEdat Gp Hm (φ, α) D.Ψ ψ').2.2.2)) hmult).trans
        (hfld.symm.trans hSol1)
    rw [hφ1, hα1, hfl]
  refine ⟨F₁, Sol, hsumall, fun um tm hw => (hexp um tm hw).2.1,
    fun um tm hw => (hexp um tm hw).2.2.1, ?_, fun um tm hw => (hexp um tm hw).2.2.2, hanaM,
    ?_, ?_⟩
  · intro a b ha hb hab um tm hum htm Y u hu
    exact (hexp um tm (mem_markedRadiusSet_of_pos hC.δ₁_pos hab hum htm)).2.2.1 Y u hu
  · intro a b t₀ ha hb ht₀ htb hab um hum Y u hu
    exact norm_deriv_mark_le (W := W) (g := fun w : ℂ × ℂ =>
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
        (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u)
      (hanaM Y u hu) (fun w hw => (hexp w.1 w.2 hw).2.2.1 Y u hu) ht₀ htb
      (fun t ht => mem_markedRadiusSet_of_pos hC.δ₁_pos hab hum ht)
  · intro um h0 D hD ψh hψh
    have hu : (rawOf D, ψh) ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
        {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ} := ⟨⟨D, hD, rfl⟩, hψh⟩
    refine deriv_sum_marks _ hWopen (um := um) (show (um, (0 : ℂ)) ∈ W from h0) ?_ ?_
    · intro t ht
      exact hsumall um t ht D hD ψh hψh
    · intro Y
      exact differentiableAt_mark_slice (g := fun w : ℂ × ℂ =>
        evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
          (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y (rawOf D, ψh))
        ((hanaM Y (rawOf D, ψh) hu) (um, 0) h0)

omit hC in
/-- **T6.**  For the empty block the mark derivative at `0` of every localized term vanishes. -/
theorem deriv_evTerm_marked_empty {X₁f : Finset (CTorus d L N₁ m₁ (k + 1))}
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
      (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
    (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ))
    (Φ : ((Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ)) → (Hm.Ω 1 × Fin N → ℂ) →
      RawData d L (N₁ * L ^ m₁) (k + 1) N × (CTorus d L N₁ m₁ (k + 1) → Fin N → ℂ) → ℂ)
    {m₀ : ℕ} {X₁ : Set (CTorus d L N₁ m₁ (k + 1))} (um : ℂ)
    (Y : Set (CTorus d L N₁ m₁ (k + 1)))
    (u : RawData d L (N₁ * L ^ m₁) (k + 1) N × (unitPts Gp × Fin N → ℂ)) :
    deriv (fun t : ℂ =>
      evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀ X₁
        (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ (∅ : Finset (unitPts Gp)) um t) Y u) 0 = 0 := by
  simp only [FFmarked_empty]
  exact deriv_const _ _

/-- **`i5_functional_hat_marked` with the family exposed, uniformly in the marks** (T1--T5).
The hypotheses are those of `i5_functional_hat_marked` with the marks `(um, tm)` removed (they
range over the open radius set `W` in the conclusion). -/
theorem i5_functional_hat_marked_exposed (hk : 1 ≤ k) (hG : IsLevel Hm k)
    (hG' : IsLevel Gp (k + 1)) (cc : ℂ)
    {cψ : ℝ} (hcψ : 0 ≤ cψ) (Zm : Finset (unitPts Gp))
    (hMX : cstarX d L * Real.exp (N0 d L * κ) ≤ (L : ℝ) ^ m₁) {δc : ℝ}
    (hdm : decDomMargin d L N BG κ (xiC1 d * eps) < δc)
    (hα : K4 d L N BG κ * (xiC1 d * eps) < coerciveConst d / 2)
    (hsm : δc ^ 2 * smallConstX d L κ ≤ 1 / 4)
    {m₀ : ℕ} {j : ℕ} {X 𝒦X : Set (CTorus d L N₁ m₁ (k + 1))}
    (hcov : CovSetup Gp m₀ j X 𝒦X)
    (hX₁ : (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) = X1 Gp m₀ j 𝒦X)
    (hconn : HatConn Gp) (hrow : RowInHat (coverOf Gp) Hm (compWeight L a₁) ν)
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
    {Z Zα : Set (CTorus d L N₁ m₁ (k + 1))} (hZ : Z ⊆ ↑X₁f) (hBM : BlockMargin Gp X₁f Zα)
    (hΦlocDir : ∀ t ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      ∀ t' ∈ FlReal Gp Hm a₁ ν BG κ eps X₁f BG₂ δ₁,
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.1.1 (y, i) = t'.1.1 (y, i)) →
      (∀ y : Gp.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Zα → t.1.2 y = t'.1.2 y) →
      (∀ y : Hm.Ω 1, (y : CTorus d L N₁ m₁ (k + 1)) ∈ Z → ∀ i, t.2.1 (y, i) = t'.2.1 (y, i)) →
      agreeOn (thickSet Gp Z) t.2.2.1 t'.2.2.1 → (∀ y ∈ Z, t.2.2.2 y = t'.2.2.2 y) →
      Φ t.1 t.2.1 t.2.2 = Φ t'.1 t'.2.1 t'.2.2) :
    ∃ (F₁ : DecParams Gp × RawData d L (N₁ * L ^ m₁) (k + 1) N →
        (Gp.Ω 1 × Fin N → ℂ) × (Gp.Ω 1 → ℂ))
      (Sol : Dec2.DecParams (coverOf Gp) × Edat Hm N → (Hm.Ω 1 × Fin N → ℂ) × (Hm.Ω 1 → ℂ)),
      -- sum identity, every mark of the radius set
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))) =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), evTerm
            (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y (rawOf D, ψh)) ∧
      -- locality
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ∀ u' ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AgHatDir hG' Y u u' →
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u =
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u') ∧
      -- the bound, every mark of the radius set
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- the bound, uniform on every closed bidisc
      (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um tm : ℂ, ‖um‖ ≤ a → ‖tm‖ ≤ b →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y u‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y)) ∧
      -- analyticity in the data
      (∀ um tm : ℂ, (‖um‖ + ‖tm‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ Y, AnalyticOnNhd ℂ
          (evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um tm) Y)
          (XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
            {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ})) ∧
      -- analyticity in the marks, at fixed data
      (∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        AnalyticOnNhd ℂ (fun w : ℂ × ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm w.1 w.2) Y u)
          {w : ℂ × ℂ | (‖w.1‖ + ‖w.2‖) *
            (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁}) ∧
      -- Cauchy estimate for the mark derivative at `t = 0`
      (∀ a b t₀ : ℝ, 0 ≤ a → 0 ≤ b → 0 < t₀ → t₀ ≤ b → (a + b) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ um : ℂ, ‖um‖ ≤ a →
        ∀ Y, ∀ u ∈ XiCRaw Gp (compWeight L a₁) ν (k + 1) 1 eps ×ˢ
          {ψh : unitPts Gp × Fin N → ℂ | ∀ p, ‖ψh p‖ ≤ cψ},
        ‖deriv (fun t : ℂ =>
          evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
            (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um t) Y u) 0‖ ≤
          Eb * Real.exp (-κ₀ * treeLenCovOne m₀ j X - 2 * κdec * treeLenCov Gp m₀ Y) / t₀) ∧
      -- sum identity for the derivatives at `t = 0`
      (∀ um : ℂ, (‖um‖ + ‖(0 : ℂ)‖) *
        (Real.sqrt N * (‖cc‖ * (covSupConstC d L N (compWeight L a₁ k) κ * cψ))) < δ₁ →
        ∀ D : BgData Gp N, XiCData Gp (compWeight L a₁) ν (k + 1) 1 eps D →
        ∀ ψh : unitPts Gp × Fin N → ℂ, (∀ p, ‖ψh p‖ ≤ cψ) →
        deriv (fun tm : ℂ =>
          Φ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D,
            bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D)
          (flFieldOne Gp Hm BG₂ κ a₁ ν D
            (liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)))))
          (rawOf D, liftC hG' (um • (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh)) +
              tm • maskBlock Zm (cc • (decCovSqrt Gp (compWeight L a₁) a₁ ν
              (bgMultC Gp (compWeight L a₁) ν (bgC0 d L N) D) (fun _ => 1)
              (barField Gp D.Ψ (bgFieldC Gp (compWeight L a₁) ν (bgC0 d L N) D))
              (unitQ Gp) (unitP Gp) *ᵥ ψh))))) 0 =
        ∑ Y ∈ polymerDomains (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1)
          Gp m₀ (X1 Gp m₀ j 𝒦X), deriv (fun t : ℂ =>
            evTerm (fun i : ParIdx Gp (↑X₁f : Set (CTorus d L N₁ m₁ (k + 1))) => i.1.1) Gp m₀
              (X1 Gp m₀ j 𝒦X) (FFmarked X₁f a₁ ν hG' cc F₁ Sol Φ Zm um t) Y (rawOf D, ψh)) 0) := by
  classical
  exact i5_functional_hat_marked_exposed_of_fan hC hk hG hG' cc hcψ Zm hMX hdm hα hsm hcov hX₁
    hopt hκ₀ hκdec hκ h1 hlog hEb hΦan hΦbd
    (fun um tm hδ F₁ hF₁ Sol hSol => fanHL_local_marked hC hk hG hG' cc hcψ hMX hdm hα hsm Zm um tm
      hδ hcov hX₁ hconn hrow hF₁ hSol hZ hBM (fun t ht t' ht' => hΦlocDir t ht.1 t' ht'.1))

end Core

end Balaban.Localization
