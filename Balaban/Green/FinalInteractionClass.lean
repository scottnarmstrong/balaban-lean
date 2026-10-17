/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Green.FinalConstants
public import Balaban.SmallField.Def6v2
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The last-scale interaction of the class, as the interaction of the last integral (blocker 5)

The interaction part of the density of the small-field class is the sum of the localized energy
terms, `F_K(Ψ, h) = ∑_{j=1}^{K} ℰ^{(j)}(Ψ, h)` (`Def6.Edens`, (H.2), (H.4)).  The clauses
`analyticE` and `boundE` of the class (`SFTermClauses`) give, on every set of data lying in the
domain of each term `ℰ^{(j)}(y, X)`:

* `edensSum_analyticOnNhd_of_dom`: `F_K` is analytic there;
* `norm_edensSum_le_of_dom`: `‖F_K‖ ≤ ∑_j ∑_y ∑_{X ∋ y} E₀ e^{-κ d_j(X)}`, the sum of the
  bounds `boundE` over the polymers of each site (a finite number, one per torus);
* `cutoffInteraction_final_class_of_polydisc_subset`: if `Λ` is an analytic map from the polydisc
  of radius `fluctRadius` around `φ₀` into the data of the class, mapping into the domains of all
  terms, then the cutoff integral of `F_K ∘ Λ` is analytic on the polydisc of radius `e^κ`
  (`cutoffInteraction_final_phys` with `Rphys = R`, `F = F_K ∘ Λ`, `B'` the sum above).

The radius is a parameter: the term `ℰ^{(j)}` lives on a chart of radius `ε_j`, which decreases
with `j`, so `R` is a multiple of `ε_{K}`, not the constant `fluctRadius`.  The inclusion of the polydisc into the domains of the terms is the hypothesis `hsub`; it is not
derived here.
-/

@[expose] public section

open Finset Set MeasureTheory Metric Balaban.Localization Balaban.Analysis Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Balaban.Fluctuation

namespace Balaban.Green

section Sum

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

/-- A finite sum over the polymers through a site of functions analytic at a point is analytic. -/
theorem analyticAt_finsum_polysAt_general {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (m₀ j : ℕ) (y : CTorus d L N₁ m₁ k) (f : Set (CTorus d L N₁ m₁ k) → E → F)
    {p₀ : E} (hf : ∀ X, IsPolyDom m₀ j X → y ∈ X → AnalyticAt ℂ (f X) p₀) :
    AnalyticAt ℂ (fun p => ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      m₀ j y, f X p) p₀ := by
  have hfin : (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) m₀ j y).Finite :=
    Set.toFinite _
  have : (fun p => ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
      m₀ j y, f X p) = fun p => ∑ X ∈ hfin.toFinset, f X p :=
    funext fun p => finsum_mem_eq_finite_toFinset_sum _ hfin
  rw [this]
  exact Finset.analyticAt_fun_sum _ fun X hX =>
    hf X (hfin.mem_toFinset.1 hX).1 (hfin.mem_toFinset.1 hX).2

variable {P : Consts} {Dom : FieldDom d L N₁ m₁ k N ϱ} {Tm : Terms d L N₁ m₁ k N ϱ}

/-- **The interaction `F_K = ∑_{j ≤ K} ℰ^{(j)}` of the class is analytic on every set of data lying
in the domain of each term** (clause `analyticE`). -/
theorem edensSum_analyticOnNhd_of_dom (hT : SFTermClauses P Dom Tm) {K : ℕ} (hK : K ≤ k)
    {U : Set (Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N)}
    (hU : ∀ r ∈ U, ∀ j, 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X →
      Dom.dom j (Tm.gs j X) r.1 r.2) :
    AnalyticOnNhd ℂ (fun r : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N =>
      ∑ j ∈ Finset.Icc 1 K, Edens P.m₀ Tm j r.1 r.2) U := by
  intro r hr
  refine Finset.analyticAt_fun_sum _ fun j hj => ?_
  have hj' := Finset.mem_Icc.1 hj
  unfold Edens
  refine Finset.analyticAt_fun_sum _ fun y _ => ?_
  unfold Eloc
  refine analyticAt_finsum_polysAt_general (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
    P.m₀ j y
    (fun X (p : Fld d L N₁ m₁ k N × Fld d L N₁ m₁ k N) => Tm.E j y X p.1 p.2) fun X hX hy => ?_
  exact hT.analyticE j hj'.1 (hj'.2.trans hK) y X hX hy r (hU r hr j hj'.1 hj'.2 X hX)

/-- The sum of the bounds `boundE` over the polymers through a site, a finite sum. -/
theorem norm_Eloc_le_of_dom (hT : SFTermClauses P Dom Tm) {j : ℕ} (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (y : CTorus d L N₁ m₁ k) (Ψ h : Fld d L N₁ m₁ k N)
    (hd : ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) Ψ h) :
    ‖Eloc P.m₀ Tm j y Ψ h‖ ≤
      ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y,
        P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  have hfin : (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y).Finite :=
    Set.toFinite _
  unfold Eloc
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun X hX => ?_)
  have hX' := hfin.mem_toFinset.1 hX
  exact hT.boundE j hj1 hjk y X hX'.1 hX'.2 Ψ h (hd X hX'.1)

/-- **The bound of the interaction of the class**: on data lying in the domain of each term,
`‖F_K‖ ≤ ∑_{j ≤ K} ∑_y ∑_{X ∋ y} E₀ e^{-κ d_j(X)}` (the clause `boundE`; `E₀ ≥ 0`). -/
theorem norm_edensSum_le_of_dom (hT : SFTermClauses P Dom Tm) {K : ℕ} (hK : K ≤ k)
    (hE₀ : 0 ≤ P.E₀) (Ψ h : Fld d L N₁ m₁ k N)
    (hd : ∀ j, 1 ≤ j → j ≤ K → ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) Ψ h) :
    ‖∑ j ∈ Finset.Icc 1 K, Edens P.m₀ Tm j Ψ h‖ ≤
      ∑ j ∈ Finset.Icc 1 K, ∑ y : CTorus d L N₁ m₁ k,
        ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y,
          P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := by
  classical
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj' := Finset.mem_Icc.1 hj
  unfold Edens
  refine (norm_sum_le _ _).trans ?_
  have hnn : ∀ y : CTorus d L N₁ m₁ k, 0 ≤
      ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y,
        P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) := fun y => by
    have hfin : (polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y).Finite :=
      Set.toFinite _
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    exact Finset.sum_nonneg fun X _ => mul_nonneg hE₀ (Real.exp_pos _).le
  calc _ ≤ ∑ y ∈ (Finset.univ : Finset (CTorus d L N₁ m₁ k)).filter (Aligned (L ^ j)),
        ∑ᶠ X ∈ polysAt (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) P.m₀ j y,
          P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X) :=
        Finset.sum_le_sum fun y _ =>
          norm_Eloc_le_of_dom hT hj'.1 (hj'.2.trans hK) y Ψ h (hd j hj'.1 hj'.2)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun y _ _ => hnn y

end Sum

section Final

variable {d N₀ M : ℕ} [NeZero N₀] {L k : ℕ} [NeZero L] {v a : ℝ}

/-- **The last integral for the interaction of the class** (conditional on the inclusion `hsub`).
Let `F_K = ∑_{j ≤ K} ℰ^{(j)}` be the interaction of a class on the torus of level `k_c`, and `Λ` an
analytic map from the polydisc of radius `R` around `φ₀` into the data of the class that
lands in the domain of every term (`hsub`).  Then `F = F_K ∘ Λ` is analytic on that polydisc and
bounded by the sum `B'` of the bounds `boundE` over the polymers, and the cutoff integral of `F` is
analytic on the polydisc of radius `e^κ` (`cutoffInteraction_final_phys`; the radius `R` is arbitrary, the comparison `B β^{-1/2} ρ < R` is `hBR`). -/
theorem cutoffInteraction_final_class_of_polydisc_subset
    {d' : ℕ} {R : ℝ} {N₁ m₁ kc N : ℕ} [NeZero N₁] {ϱ : ℝ}
    {P : Consts} {Dom : FieldDom d' L N₁ m₁ kc N ϱ} {Tm : Terms d' L N₁ m₁ kc N ϱ}
    (hT : SFTermClauses P Dom Tm) {K : ℕ} (hK : K ≤ kc) (hE₀ : 0 ≤ P.E₀)
    {φ₀ : L1Torus d N₀ → ℂ}
    {Λ : (L1Torus d N₀ → ℂ) → Fld d' L N₁ m₁ kc N × Fld d' L N₁ m₁ kc N}
    (hΛ : AnalyticOnNhd ℂ Λ (polydisc φ₀ (fun _ => R)))
    (hsub : ∀ w ∈ polydisc φ₀ (fun _ => R), ∀ j, 1 ≤ j → j ≤ K →
      ∀ X, IsPolyDom P.m₀ j X → Dom.dom j (Tm.gs j X) (Λ w).1 (Λ w).2)
    (hd : 0 < d) (hk : 1 ≤ k) (hv0 : 0 ≤ v)
    (hv1 : v ≤ 1) (ha1 : 1 / 2 ≤ a) (ha2 : a ≤ 2) (hmass : 7 / 8 * ((L : ℝ) ^ 2)⁻¹ < v)
    (hM : 0 < M) {κ : ℝ} (hκ : 1 ≤ κ)
    (hMB : 4 * (pdB d L * Real.exp (pdH d * κ)) ≤ M) (hMκ : 8 * κ * 7 ^ d ≤ pdEps d L * M)
    {γ : Measure (L1Torus d N₀ → ℝ)} {ρ β : ℝ} (hρ : 0 ≤ ρ) (hβ : 0 < β)
    (hγ : γ {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ} < ⊤)
    (hBR : (4 / 3 * (2 * Real.exp (pdH d * κ) * ballConst d (pdEps d L / 2)) /
      Real.sqrt (finalGap d L)) * (β ^ (-(1 / 2 : ℝ)) * ρ) < R) :
    AnalyticOnNhd ℂ (fun s : MacIdx d N₀ M → ℂ =>
      ∫ ψ in {ψ : L1Torus d N₀ → ℝ | ∀ y, |ψ y| ≤ ρ},
        (fun w : L1Torus d N₀ → ℂ => ∑ j ∈ Finset.Icc 1 K,
            Edens P.m₀ Tm j (Λ w).1 (Λ w).2)
          (fun x => φ₀ x + ((β ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
            ∑ y, taggedCfin d L N₀ k M v a s x y * ((ψ y : ℝ) : ℂ)) ∂γ)
      (polydisc (0 : MacIdx d N₀ M → ℂ) (fun _ => Real.exp κ)) := by
  have hFa : AnalyticOnNhd ℂ (fun w : L1Torus d N₀ → ℂ =>
      ∑ j ∈ Finset.Icc 1 K, Edens P.m₀ Tm j (Λ w).1 (Λ w).2)
      (polydisc φ₀ (fun _ => R)) := by
    intro w hw
    have h1 := edensSum_analyticOnNhd_of_dom hT hK
      (U := Λ '' polydisc φ₀ (fun _ => R))
      (by rintro _ ⟨w', hw', rfl⟩ j hj1 hjK X hX; exact hsub w' hw' j hj1 hjK X hX)
      (Λ w) ⟨w, hw, rfl⟩
    exact h1.comp (hΛ w hw)
  refine (cutoffInteraction_final_phys (Rphys := R) hd hk hv0 hv1 ha1 ha2
    hmass hM hκ hMB hMκ hρ hβ hγ hBR hFa (B' := ∑ j ∈ Finset.Icc 1 K, ∑ y : CTorus d' L N₁ m₁ kc,
        ∑ᶠ X ∈ polysAt (d := d') (L := L) (N₁ := N₁) (m₁ := m₁) (k := kc) P.m₀ j y,
          P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ j X))
    (fun w hw => norm_edensSum_le_of_dom hT hK hE₀ _ _ (fun j hj1 hjK X hX =>
      hsub w hw j hj1 hjK X hX))).1

end Final

end Balaban.Green
