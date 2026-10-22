/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalBoxLocR

/-!
# The local form of the terms `ℛ^{(k)}` on the box (A6-3, (L3)-(L4), level-`k` instance)

The terms `ℛ^{(k)}_n(X)` of the class form a family of polymer terms of the block field
(`rPolyTerms`: labels `(n, X)`, amplitudes `max 0 (fac_n β_k^{-n-1})`, decay `κ_R = κ` of the
class), under the class clause `RTermsH4`, the standing hypotheses `BgHyp` and the radius `r` of
`RDomConsts`.  The local form `rLocal = polyLocal rPolyTerms` has (FinalBoxLocPoly) the locality
in `w` and `g`, the support on connected sets, the joint analyticity in `(g, w)` and `W_Y(0, g) = 0`,
and:

* `sum_rLocal`: `∑_Y W_Y(w, g) = ℛ^{(k)}(T; h + c L w, h, g) - ℛ^{(k)}(T; h, h, g)`;
* `rLocal_bound` (W5, cell units): `∑_{Y ∋ x} ‖W_Y‖ e^{α #cells(Y)} ≤
  polyBoundConst (∑_n max 0 (fac_n β_k^{-n-1})) m r κ 0 κ_c α`, `m = |c| B_box ρ`, under
  `BoxCutConsts` (cut radius `κ_c`, macro side `L^{m₀+m₁}`) and `PolyTies` at `λ = 0`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.Multiscale Balaban.LargeField Balaban.LargeField.Def7 Balaban.Localization
  Balaban.Green Balaban.SmallField Balaban.Background Finset

section RForm

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N k m₁ : ℕ} {ϱ : ℝ} {C : SFCtx S n R M K N k m₁ ϱ}
  {hv : EuclideanSpace ℝ (Fin N)} {fac : ℕ → ℝ} {P6 : Def6.Consts} {δ r : ℝ} {D mp : ℕ}

/-- **The terms `ℛ^{(k)}_n(X)` as a family of polymer terms of the block field.** -/
noncomputable def rPolyTerms
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r) :
    PolyTerms C hv r P6.κ (RIdx C) where
  X := fun t => t.2.1
  isPoly := fun t => t.2.2
  τ := boxLocRTerm C hv
  amp := fun _ t => max 0 (fac t.1.1 * (C.sf.β k)⁻¹ ^ (t.1.1 + 1))
  amp_nonneg := fun _ _ => le_max_left _ _
  reads := fun g t => readsOn_boxLocRTerm hv hR g t
  congr_g := fun t _ _ h ψ => boxLocRTerm_congr_g hv hR t h ψ
  analytic := fun t => analyticOnNhd_boxLocRTerm C hv hR hm₀ H hunit hD.hδ0 hD.hδc0 hD.hδc1 hD.hr0
    hD.hr hD.hε t
  bound := fun t _ hp =>
    (norm_boxLocRTerm_le C hv hR hm₀ H hunit hD.hδ0 hD.hδc0 hD.hδc1 hD.hr0 hD.hr hD.hε t hp).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)

/-- **The local form of the terms `ℛ^{(k)}`.** -/
noncomputable def rLocal
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r)
    (c : ℂ) (Mc : ℕ) (v a : ℝ) (D mp : ℕ) (g : GIdx S n M K N → ℂ) (Y : Finset (BlockAt S n M K k))
    (w : BlockAt S n M K k × Fin N → ℂ) : ℂ :=
  polyLocal (rPolyTerms hR hm₀ H hunit hD) c Mc v a D mp g Y w

/-- **The sum of the local form is the change of `ℛ^{(k)}`**:
`∑_Y W_Y(w, g) = ℛ^{(k)}(T; h + T(1) w, h, g) - ℛ^{(k)}(T; h, h, g)`. -/
theorem sum_rLocal
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r) {Mc : ℕ}
    {v a κ α : ℝ} (hBC : BoxCutConsts S.d S.L k Mc v a κ α) {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ < r) {g : GIdx S n M K N → ℂ}
    (hg : ∑ q, ‖g q‖ < 1) {w : BlockAt S n M K k × Fin N → ℂ} (hw : ∀ q, ‖w q‖ ≤ ρ) :
    ∑ Y, rLocal hR hm₀ H hunit hD c Mc v a D mp g Y w =
      C.RresC Set.univ (fun b i => linField (hvField hv) (blockCut hv c Mc v a D mp) (fun _ => 1) w
        (b, i)) hv g - C.RresC Set.univ (fun _ i => ((hv i : ℝ) : ℂ)) hv g := by
  unfold rLocal
  rw [sum_polyLocal _ hunit hBC hρ hm hg hw, Finset.sum_sub_distrib]
  exact congrArg₂ (· - ·) (sum_boxLocRTerm C hv g _) (sum_boxLocRTerm C hv g _)

/-- The label count of the terms `ℛ^{(k)}`: the labels of a polymer carry the amplitude
`∑_n max 0 (fac_n β_k^{-n-1})`. -/
theorem rPolyTerms_count
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r)
    (g : GIdx S n M K N → ℂ) (X : Set (Localization.CTorus S.d S.L C.N₁ m₁ k)) :
    ∑ t ∈ Finset.univ.filter (fun t => (rPolyTerms hR hm₀ H hunit hD).X t = X),
        (rPolyTerms hR hm₀ H hunit hD).amp g t ≤
      (∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁), max 0 (fac nn * (C.sf.β k)⁻¹ ^ (nn + 1))) *
        Real.exp (0 * Def6.sizeJ C.m₀ k X) := by
  classical
  rw [zero_mul, Real.exp_zero, mul_one, Finset.sum_filter, Fintype.sum_prod_type,
    ← Finset.sum_coe_sort (Finset.Icc 1 (C.m₀ + m₁))]
  refine Finset.sum_le_sum fun nn _ => ?_
  by_cases hX : Def6.IsPolyDom C.m₀ k X
  · refine le_of_eq ?_
    rw [Finset.sum_eq_single ⟨X, hX⟩]
    · simp [rPolyTerms]
    · intro X' _ hne
      have : X'.1 ≠ X := fun h => hne (Subtype.ext h)
      simp [rPolyTerms, this]
    · simp
  · refine le_trans (le_of_eq (Finset.sum_eq_zero fun X' _ => ?_)) (le_max_left _ _)
    have : X'.1 ≠ X := fun h => hX (h ▸ X'.2)
    simp [rPolyTerms, this]

/-- **(W5) The summed bound of the local form of `ℛ^{(k)}`, in cell units**: with macro cells of
side `M = L^{m₀+m₁}`, for sources of the unit ball and complex variables with `‖w‖_∞ ≤ ρ`,
`∑_{Y ∋ x} ‖W_Y‖ e^{α #cells(Y)} ≤ polyBoundConst (∑_n max 0 (fac_n β_k^{-n-1})) m r κ 0 κ_c α`,
`m = |c| B_box ρ`. -/
theorem rLocal_bound
    (hR : Def7.RTermsH4 (ϱ := ϱ) P6 C.sf.β C.sf.ν C.sf.a C.N₁ (C.sf.Rt C.N₁) fac)
    (hm₀ : P6.m₀ = C.m₀)
    (H : BgHyp S.d S.L k ϱ (Def6.aIdeal S.L k (C.sf.a k))
      (Def6.bgMass S.L k (C.sf.β k) (C.sf.ν k)))
    (hunit : ‖hv‖ = 1) (hD : RDomConsts S.d S.L N (P6.eps S.d S.L k) δ r)
    (hN : S.L ^ C.m₀ ∣ C.N₁) {v a κ α : ℝ}
    (hBC : BoxCutConsts S.d S.L k (S.L ^ (C.m₀ + m₁)) v a κ α)
    (hTies : PolyTies S.d S.L P6.κ 0 κ α)
    {c : ℂ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hm : ‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ < r)
    {g : GIdx S n M K N → ℂ} (hg : ∑ q, ‖g q‖ < 1) {w : BlockAt S n M K k × Fin N → ℂ}
    (hw : ∀ q, ‖w q‖ ≤ ρ) (x : BlockAt S n M K k) :
    ∑ Y ∈ Finset.univ.filter (fun Y : Finset (BlockAt S n M K k) => x ∈ Y),
        ‖rLocal hR hm₀ H hunit hD c (S.L ^ (C.m₀ + m₁)) v a D mp g Y w‖ *
          Real.exp (α * (macCellCount S.d (M * n K * S.L ^ (K - k)) (S.L ^ (C.m₀ + m₁)) Y : ℝ)) ≤
      polyBoundConst S.d S.L
        (∑ nn ∈ Finset.Icc 1 (C.m₀ + m₁), max 0 (fac nn * (C.sf.β k)⁻¹ ^ (nn + 1)))
        (‖c‖ * boxCutConst S.d S.L N a κ 1 * ρ) r P6.κ 0 κ α :=
  polyLocal_bound _ hunit hN hBC (Finset.sum_nonneg fun _ _ => le_max_left _ _) hTies hρ hm hg
    (rPolyTerms_count hR hm₀ H hunit hD g) hw x

end RForm

end Balaban.RootFSpine
