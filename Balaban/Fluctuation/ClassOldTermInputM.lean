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
# The old observable terms of a class member as inputs of the step's activity constructor

The observable half of `ClassOldTermInputE`.  The labels of the old observable terms of a class
member `C` are the quadruples `(j, y, i, X)` with `1 ≤ j ≤ k`, `y` a site, `i` a component and `X` a
polymer of `𝒟_j` containing `y`; the functional is the `i`-th component of
`ℳ^{(j)}(y, X; Ψ, h, g)` for the fixed source `g`, with generating set `𝔹_j(X)`, `j_τ = j`,
`X_τ = X`, `y_τ = y`, `i_τ = i`.  The source factor `g_{y,i}/β` of the expansion is not part of the
functional (it is the factor of `OldObsHatMatch`).

* `sum_classLabels_M_eq_Floc`: the label sum `∑ g_{y,i} ℳ^{(j)}_i(y, X; ψ_j, h_j, g)` is
  `∑_{j=1}^k ℱ^{(j)}(ψ_j, h_j, g)`, the sum used by `FcompAt`.
* `mem_classLabels_M_iff`: membership in the label set.
* `classOldObs_analytic_bound`: the chart hypotheses of the constructor (`hEanM`, `hEbdM`).
* `oldObsHatMatch_of_label_identity`: `OldObsHatMatch` for the label functionals from the
  composition identity on the label terms.
-/

@[expose] public section

namespace Balaban.Fluctuation

open Balaban Balaban.Localization Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.SmallField.Def6v2 Finset

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}

open Classical in
/-- **The sum of the label terms is the density.**  The sum over the labels `(j, y, i, X)`,
`1 ≤ j ≤ k`, `X ∈ 𝒟_j` with `y ∈ X`, of `g_{y,i} ℳ^{(j)}_i(y, X; ψ_j, h_j, g)` is
`∑_{j=1}^k ℱ^{(j)}(ψ_j, h_j, g)`. -/
theorem sum_classLabels_M_eq_Floc (m₀ : ℕ) (Tm : Terms d L N₁ m₁ (k + 1) N ϱ)
    (ψ : ℕ → Fld d L N₁ m₁ (k + 1) N) (h : ℕ → Fld d L N₁ m₁ (k + 1) N)
    (g : Fld d L N₁ m₁ (k + 1) N) :
    ∑ τ ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2),
      g τ.2.1 τ.2.2.1 * Tm.M τ.1 τ.2.1 τ.2.2.2 (ψ τ.1) (h τ.1) g τ.2.2.1 =
    ∑ j ∈ Finset.Icc 1 k, Floc m₀ Tm j (ψ j) (h j) g := by
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => ?_
  unfold Floc Mloc
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.sum_apply, Finset.mul_sum,
    ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext X
  simp [polysAt]

open Classical in
/-- **Membership in the label set.**  The labels of the old observable terms of `C`:
`(j, y, i, X)` with `1 ≤ j ≤ k`, `X ∈ 𝒟_j` and `y ∈ X`. -/
theorem mem_classLabels_M_iff (m₀ : ℕ) (τ : ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N ×
    Set (CTorus d L N₁ m₁ (k + 1))) :
    τ ∈ ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2) ↔
    (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2 := by
  simp [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]

/-- A component of a vector is bounded by its Euclidean norm `vn`. -/
theorem norm_apply_le_vn (v : Fin N → ℂ) (i : Fin N) : ‖v i‖ ≤ vn v := by
  unfold vn
  exact PiLp.norm_apply_le (WithLp.toLp 2 v) i

open Classical in
/-- **The chart hypotheses of the constructor for the old observable terms of a class.**  Let `𝒯M`
be a finite set of labels `τ = (j, y, i, X)` (for instance the label set of `mem_classLabels_M_iff`),
the generating set of `τ` be `𝔹_j(X) = C.Tm.gs j X`, `j_τ = j`, `X_τ = X` and
`EM τ (Ψ, h) = ℳ^{(j)}_i(y, X; Ψ, h, g)` for a fixed source `g` with `‖g‖ < 1` in the class
(`Def6.l1 g < 1`).  If the term clauses `analyticM`, `boundM` hold on a field domain `Dom` that
contains the chart `Ξ^c(𝔹_j(X); …)` (the hypothesis `hchart`), and `κ_dec - 1 ≤ κ_P`, then `EM` is
analytic on the chart and bounded there by
`c₉ (L^j)^{-((d-2)/2 + γ - α₁)} exp(-(κ_dec - 1) d_j(X))`. -/
theorem classOldObs_analytic_bound {P : Consts} {Dom : FieldDom d L N₁ m₁ (k + 1) N ϱ}
    (C : StepClass d L N₁ m₁ k N ϱ) (hm : P.m₀ = C.m₀)
    (hcl : SFTermClauses P Dom C.Tm) {κdec : ℝ} (hκ : κdec - 1 ≤ P.κ)
    (hc₉ : 0 ≤ P.c₉) (g : Fld d L N₁ m₁ (k + 1) N) (hg : Def6.l1 g < 1)
    (a : ℕ → ℝ) (ν : ℝ) (σ ε : ℝ)
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : ∀ τ ∈ 𝒯M, (1 ≤ τ.1 ∧ τ.1 ≤ k) ∧ IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2)
    (hchart : ∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2.2) a ν τ.1 σ ε,
      Dom.dom τ.1 (C.Tm.gs τ.1 τ.2.2.2) r.1 r.2) :
    (∀ τ ∈ 𝒯M, AnalyticOnNhd ℂ
      (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N =>
        C.Tm.M τ.1 τ.2.1 τ.2.2.2 r.1 r.2 g τ.2.2.1)
      (XiCRaw (C.Tm.gs τ.1 τ.2.2.2) a ν τ.1 σ ε)) ∧
    (∀ τ ∈ 𝒯M, ∀ r ∈ XiCRaw (C.Tm.gs τ.1 τ.2.2.2) a ν τ.1 σ ε,
      ‖C.Tm.M τ.1 τ.2.1 τ.2.2.2 r.1 r.2 g τ.2.2.1‖ ≤
        P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
          Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2.2)) := by
  refine ⟨fun τ hτ => ?_, fun τ hτ r hr => ?_⟩
  · obtain ⟨⟨h1, h2⟩, hX, hy⟩ := h𝒯 τ hτ
    have han := hcl.analyticM τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2.2 (hm ▸ hX) hy
    intro r hr
    have hpt : AnalyticAt ℂ (fun r : RawData d L (N₁ * L ^ m₁) (k + 1) N => (r.1, r.2, g)) r :=
      analyticAt_fst.prod (analyticAt_snd.prod analyticAt_const)
    have hF := han (r.1, r.2, g) ⟨hchart τ hτ r hr, hg⟩
    have hpr : AnalyticAt ℂ (fun v : Fin N → ℂ => v τ.2.2.1)
        (C.Tm.M τ.1 τ.2.1 τ.2.2.2 r.1 r.2 g) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) τ.2.2.1).analyticAt _
    exact hpr.comp_of_eq (hF.comp_of_eq hpt rfl) rfl
  · obtain ⟨⟨h1, h2⟩, hX, hy⟩ := h𝒯 τ hτ
    have hb := hcl.boundM τ.1 h1 (h2.trans (Nat.le_succ k)) τ.2.1 τ.2.2.2 (hm ▸ hX) hy r.1 r.2 g
      (hchart τ hτ r hr) hg
    have key : Real.exp (-P.κ * sizeJ P.m₀ τ.1 τ.2.2.2) ≤
        Real.exp (-(κdec - 1) * treeLenCovOne C.m₀ τ.1 τ.2.2.2) := by
      unfold sizeJ
      rw [hm]
      refine Real.exp_le_exp.2 ?_
      have := treeLenCovOne_nonneg (d := d) (L := L) (N₁ := N₁) (m₁ := m₁) (K := k + 1)
        C.m₀ τ.1 τ.2.2.2
      nlinarith
    have hpos : 0 ≤ P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) := by
      have : (0 : ℝ) ≤ ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) :=
        Real.rpow_nonneg (by positivity) _
      positivity
    calc ‖C.Tm.M τ.1 τ.2.1 τ.2.2.2 r.1 r.2 g τ.2.2.1‖
        ≤ vn (C.Tm.M τ.1 τ.2.1 τ.2.2.2 r.1 r.2 g) := norm_apply_le_vn _ _
      _ ≤ P.c₉ * ((L : ℝ) ^ τ.1)⁻¹ ^ (((d : ℝ) - 2) / 2 + P.γ - P.α₁) *
            Real.exp (-P.κ * sizeJ P.m₀ τ.1 τ.2.2.2) := hb.le
      _ ≤ _ := mul_le_mul_of_nonneg_left key hpos

open Classical in
/-- **`OldObsHatMatch` for the label functionals, from the label composition identity** (named
conditional result).  Let `𝒯M` be the label set of `mem_classLabels_M_iff`, `ys τ = y`, `is τ = i`,
`EM τ = ℳ^{(j)}_i(y, X; ·, g)`.  If each label functional at the physical hat variable `ψ̂`
(`‖ψ̂‖ < p⁺`) is the label term at the composed pair of the step (`hid`: the composition identity on
the localized generating sets, which is proved in `hatFun_flComp_level_real` only for the
whole-lattice sets), then `β ∑_τ (g_{y,i}/β)(F_τ(ψ̂) - F_τ(0)) = δℱ_k(ψ', g)` minus the same for
the zero class. -/
theorem oldObsHatMatch_of_label_identity (S : StepSetting d L N₁ m₁ k N ϱ)
    (C : StepClass d L N₁ m₁ k N ϱ) (g : Fld d L N₁ m₁ (k + 1) N) {pp : ℝ} (R0 : S.RayData pp)
    (hlt : S.p₁ < pp) (hp₁ : 0 < S.p₁) {c BG κ eps Kc Cx c₂ BG₂ δ₁ r₀ δ₃ δfl : ℝ}
    {ϱ₁ ϱ₂ : (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))) → ℝ}
    {GkM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₁ τ)}
    {GjM : ∀ τ, GeneratingSet d L (N₁ * L ^ m₁) (k + 1) (ϱ₂ τ)}
    {X₀M X₁M : (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))) →
      Finset (CTorus d L N₁ m₁ (k + 1))}
    {jM : (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))) → ℕ}
    (𝒯M : Finset (ℕ × CTorus d L N₁ m₁ (k + 1) × Fin N × Set (CTorus d L N₁ m₁ (k + 1))))
    (h𝒯 : 𝒯M = ((Finset.Icc 1 k) ×ˢ (Finset.univ : Finset (CTorus d L N₁ m₁ (k + 1) × Fin N ×
        Set (CTorus d L N₁ m₁ (k + 1))))).filter
      (fun τ => IsPolyDom C.m₀ τ.1 τ.2.2.2 ∧ τ.2.1 ∈ τ.2.2.2))
    (hBM : ∀ τ ∈ 𝒯M,
      BgSetting N S.G' (GkM τ) (GjM τ) S.a₁ S.ν c BG κ r₀ eps δ₃ (X₀M τ) (X₁M τ) (jM τ))
    (hFM : ∀ τ ∈ 𝒯M,
      FlSetting N S.G' (GkM τ) (stepG d L N₁ m₁ k ϱ) S.a₁ S.ν κ BG eps δ₃ Kc Cx c₂ BG₂ δ₁ δfl
        (X₁M τ))
    (hid : ∀ τ (hτ : τ ∈ 𝒯M),
      ∀ y : S.E, ‖y‖ < pp →
        hatFun S.G' S.a₁ S.ν eps S.hG' ((S.betaU ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
          (flComp (hBM τ hτ) (hFM τ hτ)
            (fun raw => C.Tm.M τ.1 τ.2.1 τ.2.2.2 raw.1 raw.2 g τ.2.2.1))
          (rawOf S.D', S.hatC y) =
        C.Tm.M τ.1 τ.2.1 τ.2.2.2
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 y))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 y))).2 g τ.2.2.1) :
    OldObsHatMatch S C g 𝒯M (fun τ => τ.2.1) (fun τ => τ.2.2.1)
      hBM hFM (fun τ raw => C.Tm.M τ.1 τ.2.1 τ.2.2.2 raw.1 raw.2 g τ.2.2.1) := by
  subst h𝒯
  intro x hx
  have hβ : (S.β : ℂ) ≠ 0 := by exact_mod_cast R0.hβ.ne'
  have hxn : ‖x‖ < pp := ((chiFl_eq_one_iff hp₁ x).1 hx).trans hlt
  have h0n : ‖(0 : S.E)‖ < pp := by simpa using R0.hpp
  rw [Finset.sum_congr rfl (g := fun τ => (S.β : ℂ)⁻¹ * (g τ.2.1 τ.2.2.1 *
      (C.Tm.M τ.1 τ.2.1 τ.2.2.2
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 x))).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU (S.psiAt 1 x))).2 g τ.2.2.1 -
        C.Tm.M τ.1 τ.2.1 τ.2.2.2
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU S.psi0)).1
          (composedPairAt S.a S.ν (Nat.le_succ k) τ.1 (S.dataU S.psi0)).2 g τ.2.2.1)))
    (fun τ hτ => by
      rw [dite_eq_left hτ, ← S.hatC_zero, hid τ hτ x hxn, hid τ hτ 0 h0n, S.psiAt_zero_right]
      ring)]
  rw [← Finset.mul_sum, ← mul_assoc, mul_inv_cancel₀ hβ, one_mul]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib,
    sum_classLabels_M_eq_Floc C.m₀ C.Tm
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).1)
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU (S.psiAt 1 x))).2) g,
    sum_classLabels_M_eq_Floc C.m₀ C.Tm
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).1)
      (fun j => (composedPairAt S.a S.ν (Nat.le_succ k) j (S.dataU S.psi0)).2) g]
  unfold StepSetting.dF
  have hz : ∀ D, FcompAt C.m₀ C.Tm S.a S.ν (Nat.le_succ k) D g =
      FcompAt (zeroClass d L N₁ m₁ k N ϱ).m₀ (zeroClass d L N₁ m₁ k N ϱ).Tm S.a S.ν
        (Nat.le_succ k) D g + ∑ j ∈ Finset.Icc 1 k, Floc C.m₀ C.Tm j (composedPairAt S.a S.ν
          (Nat.le_succ k) j D).1 (composedPairAt S.a S.ν (Nat.le_succ k) j D).2 g := by
    intro D
    show _ = FcompAt 0 (zeroTerms d L N₁ m₁ (k + 1) N ϱ) S.a S.ν (Nat.le_succ k) D g + _
    rw [FcompAt_zero_eq]
    rfl
  rw [hz (S.dataU (S.psiAt 1 x)), hz (S.dataU S.psi0)]
  ring

end Balaban.Fluctuation
