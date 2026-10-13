/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Fluctuation.StepActivityHatGeneral
public import Balaban.SmallField.Def6v2
public import Balaban.Fluctuation.StepActivityHatLevel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The old energy terms of a class member as inputs of the step's activity constructor

The general activity constructor `stepActivityBound_direct_source_of_oldHatMatch` takes the old
energy terms of the class as functionals `EE τ` of one raw datum, indexed by a finite set of labels
`τ`.  Here the labels of a class member `C` are the triples `(j, y, X)` with `1 ≤ j ≤ k`, `y` an
`L^j`-aligned site and `X` a polymer of `𝒟_j` containing `y`; the functional is
`EE (j, y, X) (Ψ, h) = β⁻¹ ℰ^{(j)}(y, X; Ψ, h)` (the factor `β⁻¹` is cancelled by the outer factor
`β` of the expansion), with generating set `𝔹_j(X)` of the class, `j_τ = j`, `X_τ = X`.

* `sum_classLabels_E_eq_Edens`, `sum_classLabels_E_eq_Edens_level`: the sum of the label terms over
  the labels is `ℰ_k` (resp. the density `ℰ^{(j)}`), the sums used by `EcompAtC`.
* `classOldEnergy_analytic_bound`: the two chart hypotheses of the constructor (`hEanE`, `hEbdE`)
  for these functionals, from the term clauses `analyticE`, `boundE` of the class, under an explicit
  hypothesis that the chart `Ξ^c(𝔹_j(X); …)` lies in the field domain of the class.
* `oldEnergyHatMatch_of_label_identity`: the matching predicate `OldEnergyHatMatch` for the label
  functionals, from the identity of each label functional with the label term at the composed pair
  of the step (the composition identity on localized generating sets).
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The sum of the label terms is the density.**  For `m₀` and a family of terms, the sum over the
labels `(j, y, X)`, `1 ≤ j ≤ k`, `y` an `L^j`-aligned site, `X ∈ 𝒟_j` with `y ∈ X`, of
`ℰ^{(j)}(y, X; ψ, h)` is `∑_{j=1}^k ℰ^{(j)}(ψ, h)`. -/
theorem sum_classLabels_E_eq_Edens (m₀ : ℕ) (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (ψ : ℕ → Fld d L N₁ m₁ (k + 1) N) (h : ℕ → Fld d L N₁ m₁ (k + 1) N) :
    ∑ τ ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2),
      Tm.E τ.1 τ.2.1 τ.2.2 (ψ τ.1) (h τ.1) =
    ∑ j ∈ Finset.Icc 1 k, Edens m₀ Tm j (ψ j) (h j) := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Edens Eloc
  rw [Fintype.sum_prod_type, Finset.sum_filter]
  refine Finset.sum_congr rfl fun y _ => ?_
  by_cases hy' : Aligned (L ^ j) y
  · simp only [hy', true_and]
    rw [ite_true, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), ← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext X
    simp [polysAt]
  · simp [hy']


open Classical in
/-- **Membership in the label set.**  The labels of the old energy terms of `C`: `(j, y, X)` with
`1 ≤ j ≤ k`, `y` an `L^j`-aligned site, `X ∈ 𝒟_j` and `y ∈ X`. -/
theorem mem_classLabels_E_iff (m₀ : ℕ) (τ : ℕ × CTorus d L N₁ m₁ (k + 1) ×
    Set (CTorus d L N₁ m₁ (k + 1))) :
    τ ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2) ↔
    (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2 := by
  simp [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]

open Classical in
/-- **The chart hypotheses of the constructor for the old energy terms of a class.**  Let `𝒯E` be a
finite set of labels `τ = (j, y, X)` (for instance the label set of `mem_classLabels_E_iff`), the
generating set of `τ` be `𝔹_j(X) = C.Tm.gs j X`, `j_τ = j`, `X_τ = X` and
`EE τ (Ψ, h) = β⁻¹ ℰ^{(j)}(y, X; Ψ, h)`.  If the term clauses `analyticE`, `boundE` hold on a field
domain `Dom` that contains the chart `Ξ^c(𝔹_j(X); …)` (the hypothesis `hchart`), and
`κ_dec - 1 ≤ κ_P`, then `EE` is analytic on the chart and bounded there by
`β⁻¹ E₀ exp(-(κ_dec - 1) d_j(X))`. -/
theorem classOldEnergy_analytic_bound {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {β : ℝ} (hβ : 0 < β) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hE₀ : 0 ≤ P.E₀) (a : ℕ → ℝ) (ν : ℝ) (σ ε : ℝ)
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯E, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2)
    (hchart : ∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2) r.1 r.2) :
    (∀ τ ∈ 𝒯E, AnalyticOnNhd ℂ
      (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => (β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 r.1 r.2)
      (XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε)) ∧
    (∀ τ ∈ 𝒯E, ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε,
      ‖(β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 r.1 r.2‖ ≤ β⁻¹ * P.E₀ *
        Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2)) := by
  refine ⟨fun τ hτ => ?_, fun τ hτ r hr => ?_⟩
  · obtain ⟨⟨h1, h2⟩, hX, hy⟩ := h𝒯 τ hτ
    have han := hcl.analyticE τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2 (hm ▸ hX) hy
    have hf : AnalyticOnNhd ℂ (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        C.Tm.E τ.1 τ.2.1 τ.2.2 r.1 r.2) (XiCRaw (C.Tm.gs τ.1 τ.2.2) a ν τ.1 σ ε) :=
      han.mono fun r hr => hchart τ hτ r hr
    exact analyticOnNhd_const.mul hf
  · obtain ⟨⟨h1, h2⟩, hX, hy⟩ := h𝒯 τ hτ
    have hb := hcl.boundE τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2 (hm ▸ hX) hy r.1 r.2
      (hchart τ hτ r hr)
    have key : P.E₀ * Real.exp (-P.κ * sizeJ P.m₀ τ.1 τ.2.2) ≤
        P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2) := by
      unfold sizeJ
      rw [hm]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hE₀
      have := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        C.m₀ τ.1 τ.2.2
      nlinarith
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hβ.le]
    calc β⁻¹ * ‖C.Tm.E τ.1 τ.2.1 τ.2.2 r.1 r.2‖
        ≤ β⁻¹ * (P.E₀ * Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2)) :=
          mul_le_mul_of_nonneg_left (hb.trans key) (inv_nonneg.2 hβ.le)
      _ = _ := by ring


open Classical in
/-- **`OldEnergyHatMatch` for the label functionals, from the label composition identity** (named
conditional result).  Let `𝒯E` be the label set of `mem_classLabels_E_iff`, `EE τ = β⁻¹ ℰ^{(j)}(y, X; ·)`.
If each label functional at the physical hat variable `ψ̂` (`‖ψ̂‖ < p⁺`) is the label term at the
composed pair of the step (`hid`: the composition identity on the localized generating sets
`𝔹_k(X)`, `𝔹_j(X)`, which is proved in `hatFun_flComp_level_real` only for the whole-lattice sets),
then `β ∑_τ (F_τ(ψ̂) - F_τ(0)) = δℰ_k(ψ')`. -/
theorem oldEnergyHatMatch_of_label_identity (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) {pp : ℝ} (R0 : S.RayData pp) (hlt : S.p₁ < pp)
    (hp₁ : 0 < S.p₁) {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {ϱ₁ ϱ₂ : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) → ℝ}
    {GkE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjE : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {X₀E X₁E : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) →
      Finset (CTorus d L N₁ m₁ (k + 1))}
    {jE : (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))) → ℕ}
    (𝒯E : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯E = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => Aligned (L ^ τ.1) τ.2.1 ∧ IsPolyDom C.m₀ τ.1 τ.2.2 ∧ τ.2.1 ∈ τ.2.2))
    (hBE : ∀ τ ∈ 𝒯E,
      BgSetting N S.G' (GkE τ) (GjE τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀E τ) (X₁E τ) (jE τ))
    (hFE : ∀ τ ∈ 𝒯E,
      FlSetting N S.G' (GkE τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
        (X₁E τ))
    (hid : ∀ τ (hτ : τ ∈ 𝒯E),
      ∀ y : S.E, ‖y‖ < pp →
        hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBE τ hτ) (hFE τ hτ)
            (fun raw => (S.β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 raw.1 raw.2))
          (rawOf S.D', S.hatC y) =
        (S.β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 y))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 y))).2) :
    OldEnergyHatMatch S C 𝒯E
      hBE hFE (fun τ raw => (S.β : ℂ)⁻¹ * C.Tm.E τ.1 τ.2.1 τ.2.2 raw.1 raw.2) := by
  subst h𝒯
  intro x hx
  have hβ : (S.β : ℂ) ≠ 0 := by exact_mod_cast R0.hβ.ne'
  have hxn : ‖x‖ < pp := ((chiFl_eq_one_iff hp₁ x).1 hx).trans hlt
  have h0n : ‖(0 : S.E)‖ < pp := by simpa using R0.hpp
  rw [Finset.sum_congr rfl (g := fun τ => (S.β : ℂ)⁻¹ *
      (C.Tm.E τ.1 τ.2.1 τ.2.2
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 x))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 x))).2 -
        C.Tm.E τ.1 τ.2.1 τ.2.2
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU S.psi0)).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU S.psi0)).2))
    (fun τ hτ => by
      rw [dite_eq_left hτ, ← S.hatC_zero, hid τ hτ x hxn, hid τ hτ 0 h0n, S.psiAt_zero_right]
      ring)]
  rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul, Finset.sum_sub_distrib,
    sum_classLabels_E_eq_Edens C.m₀ C.Tm
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).1)
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).2),
    sum_classLabels_E_eq_Edens C.m₀ C.Tm
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).1)
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).2)]
  rfl

end Balaban.Fluctuation
