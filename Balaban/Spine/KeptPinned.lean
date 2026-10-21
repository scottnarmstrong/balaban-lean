/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KappaLocal
public import Balaban.Spine.CorrHist
public import Balaban.Spine.CorrLoc
public import Balaban.Spine.CorrKappa

/-!
# The pinned exponent of the kept half of `R` is torus coherent

The exponent `κ_k` of the output of `R` at a kept component is the pinned exponent
`κ^pre_k(Z, 𝔸 ∩ Z)` of the canonical histories (`pinnedExp`).  For corresponding localized
histories of two tori it is the same number:

* every kept component of an admissible region history is the localized history of a kept
  non-removed component of a history of a complete set (`exists_canon_of_kept`: the lineage
  localization is an admissible history without removals, and the localized history of the
  localization is the localized history);
* the exponents of the canonical histories of a pinned representation with label-independent kept
  costs are the model exponents (`kappaH_eq_kapM`), and these agree for corresponding components
  (`kapPreM_corr`).
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

section Realize

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L]

/-- **Every kept component of an admissible region history is the localized history of a kept
non-removed component of a history of a complete set.** -/
theorem exists_canon_of_kept {k : ℕ} (hkK : k ≤ K) {𝔄 : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) 𝔄) {H : RegionHistory S n R k0 K} (Z : H.Comp k)
    (hk : IsKept H k Z) :
    ∃ B ∈ 𝔄, ∃ Z' : B.H.Comp k, IsKept B.H k Z' ∧ Z'.1 ∉ B.H.rem k ∧
      B.H.localHistory M K k Z' = H.localHistory M K k Z := by
  classical
  set loc := H.locRH k Z with hloc
  have hadm : loc.Admissible := fun j c hc => by
    exact absurd hc (by simp [hloc, locRH_rem])
  let L : LabHist S n R k0 K := ⟨loc, hadm, fun _ _ => 0⟩
  obtain ⟨B, ⟨hB, hLB⟩, -⟩ := hc L
  have hag : HAgr k L.H B.H := HAgr.of_agree hLB
  let Zloc : loc.Comp k := ⟨Z.1, locComp_mem H hkK Z⟩
  have hlh : loc.localHistory M K k Zloc = H.localHistory M K k Z := localHistory_locRH hkK Z
  obtain ⟨-, -, hbk⟩ := spine_bk_eq_of_localHistory_eq (M := M) k hkK loc H Zloc Z hlh
  refine ⟨B, hB, hag.cmap le_rfl Zloc, ?_, ?_, ?_⟩
  · have : IsKept loc k Zloc := by
      unfold IsKept at hk ⊢
      rw [hbk]; exact hk
    exact (hag.isKept_iff le_rfl Zloc).2 this
  · rw [hag.rem_iff le_rfl Zloc]
    show Zloc.1 ∉ (H.locRH k Z).rem k
    rw [locRH_rem]
    exact Finset.notMem_empty _
  · rw [hag.localHistory_eq le_rfl M K Zloc]
    exact hlh



end Realize

section Pinned

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ} {geo₁ : Geo S n₁ R M} {geo₂ : Geo S n₂ R M}
  {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

theorem HistCorr.symm' {cc : Fin S.d → ℤ} {M K : ℕ} {a₁ : LocalHistory S n₁ M K}
    {a₂ : LocalHistory S n₂ M K} (h : HistCorr cc a₁ a₂) : HistCorr cc a₂ a₁ := fun j =>
  ⟨(h j).1.symm, (h j).2.1.symm, (h j).2.2.1.symm, (h j).2.2.2.1.symm, (h j).2.2.2.2.1.symm,
    (h j).2.2.2.2.2.1.symm, (h j).2.2.2.2.2.2.1.symm, (h j).2.2.2.2.2.2.2.symm⟩

/-- **Transfer of a pinned witness between two tori**: a kept non-removed component of a history
of the canonical set of the first torus, with the localized history of `Z₁`, gives one on the second
torus with the localized history of `Z₂`, and the exponents `κ^pre_k` of the two components agree. -/
theorem pinned_transfer (r₁ : Rep S n₁ R k0 K M N geo₁ cs P k) (r₂ : Rep S n₂ R k0 K M N geo₂ cs P k)
    (D₁ : KeptScaleData r₁) (D₂ : KeptScaleData r₂) {j : ℕ} (hk : k = j + 1) (hkK : k ≤ K)
    (hpin₁ : D4Pin k (keptRep r₁ D₁)) (hpin₂ : D4Pin k (keptRep r₂ D₂)) (γ : ℕ → ℝ)
    (hγ₁ : ∀ i, i < k → ∀ l, D₁.KD.gam i l = γ i) (hγ₂ : ∀ i, i < k → ∀ l, D₂.KD.gam i l = γ i)
    {cc : Fin S.d → ℤ} {H₁ : RegionHistory S n₁ R k0 K} {H₂ : RegionHistory S n₂ R k0 K}
    (Z₁ : H₁.Comp k) (Z₂ : H₂.Comp k)
    (hH : HistCorr cc (H₁.localHistory M K k Z₁) (H₂.localHistory M K k Z₂))
    (hV : SetCorr cc (Vsites R (H₁.localHistory M K k Z₁) k) (Vsites R (H₂.localHistory M K k Z₂) k))
    {A : LabHist S n₁ R k0 K} (hA : A ∈ canonHist S n₁ R k0 K k (k + 1)) (Z : A.H.Comp k)
    (hkept : IsKept A.H k Z) (hrem : Z.1 ∉ A.H.rem k)
    (hlh : A.H.localHistory M K k Z = H₁.localHistory M K k Z₁) :
    ∃ B ∈ canonHist S n₂ R k0 K k (k + 1), ∃ Z' : B.H.Comp k, IsKept B.H k Z' ∧
      Z'.1 ∉ B.H.rem k ∧ B.H.localHistory M K k Z' = H₂.localHistory M K k Z₂ ∧
      r₁.kappaPreH A k Z = r₂.kappaPreH B k Z' := by
  subst hk
  have hjK : j + 1 ≤ K := hkK
  have hH' : HistCorr cc (A.H.localHistory M K (j + 1) Z) (H₂.localHistory M K (j + 1) Z₂) := by
    rw [hlh]; exact hH
  have hV' : SetCorr cc (Vsites R (A.H.localHistory M K (j + 1) Z) (j + 1))
      (Vsites R (H₂.localHistory M K (j + 1) Z₂) (j + 1)) := by
    rw [hlh]; exact hV
  obtain ⟨E, hLin, hm₁, hm₂⟩ := corr_of_V hjK geo₁ geo₂ Z Z₂ hH' hV'
  have hbk := bk_corr E (j + 1) le_rfl Z Z₂ hLin hm₁ hm₂
  have hkept₂ : IsKept H₂ (j + 1) Z₂ := by
    unfold IsKept at hkept ⊢
    rw [← hbk]; exact hkept
  obtain ⟨B, hB, Z', hkB, hrB, hlhB⟩ := exists_canon_of_kept (M := M) hkK
    (canonHist_complete (S := S) (n := n₂) (R := R) (k0 := k0) (K := K) (j + 1) (j + 1 + 1)) Z₂ hkept₂
  refine ⟨B, hB, Z', hkB, hrB, hlhB, ?_⟩
  have hH'' : HistCorr cc (A.H.localHistory M K (j + 1) Z) (B.H.localHistory M K (j + 1) Z') := by
    rw [hlhB]; exact hH'
  have hV'' : SetCorr cc (Vsites R (A.H.localHistory M K (j + 1) Z) (j + 1))
      (Vsites R (B.H.localHistory M K (j + 1) Z') (j + 1)) := by
    rw [hlhB]; exact hV'
  obtain ⟨E', hLin', hm₁', hm₂'⟩ := corr_of_V hjK geo₁ geo₂ Z Z' hH'' hV''
  have e₁ := kappaPreH_eq_kapPreM (keptRep r₁ D₁) hpin₁ γ hγ₁ (A := A) hA le_rfl Z
  have e₂ := kappaPreH_eq_kapPreM (keptRep r₂ D₂) hpin₂ γ hγ₂ (A := B) hB le_rfl Z'
  rw [kappaPreH_keptRep r₁ D₁ A Z, kappaPreH_keptRep r₂ D₂ B Z', e₁, e₂]
  exact kapPreM_corr E' P _ le_rfl hLin' hm₁' hm₂'



/-- **The pinned exponents of the two tori agree** at corresponding localized histories: the
exponent `κ_k = κ^pre_k` of the kept components of the canonical histories is a function of the
localized history that is the same on the two tori (LFR Definition II.6.2 (D8), the pinned
exponent). -/
theorem pinnedExp_corr (r₁ : Rep S n₁ R k0 K M N geo₁ cs P k) (r₂ : Rep S n₂ R k0 K M N geo₂ cs P k)
    (D₁ : KeptScaleData r₁) (D₂ : KeptScaleData r₂) {j : ℕ} (hk : k = j + 1) (hkK : k ≤ K)
    (hpin₁ : D4Pin k (keptRep r₁ D₁)) (hpin₂ : D4Pin k (keptRep r₂ D₂))
    (hloc₁ : KappaPreLocal r₁ (canonHist S n₁ R k0 K k (k + 1)) k)
    (hloc₂ : KappaPreLocal r₂ (canonHist S n₂ R k0 K k (k + 1)) k) (γ : ℕ → ℝ)
    (hγ₁ : ∀ i, i < k → ∀ l, D₁.KD.gam i l = γ i) (hγ₂ : ∀ i, i < k → ∀ l, D₂.KD.gam i l = γ i)
    {cc : Fin S.d → ℤ} {H₁ : RegionHistory S n₁ R k0 K} {H₂ : RegionHistory S n₂ R k0 K}
    (Z₁ : H₁.Comp k) (Z₂ : H₂.Comp k)
    (hH : HistCorr cc (H₁.localHistory M K k Z₁) (H₂.localHistory M K k Z₂))
    (hV : SetCorr cc (Vsites R (H₁.localHistory M K k Z₁) k) (Vsites R (H₂.localHistory M K k Z₂) k)) :
    pinnedExp r₂ (canonHist S n₂ R k0 K k (k + 1)) k (H₂.localHistory M K k Z₂) =
      pinnedExp r₁ (canonHist S n₁ R k0 K k (k + 1)) k (H₁.localHistory M K k Z₁) := by
  classical
  by_cases h₁ : ∃ A ∈ canonHist S n₁ R k0 K k (k + 1), ∃ Z : A.H.Comp k, IsKept A.H k Z ∧
      Z.1 ∉ A.H.rem k ∧ A.H.localHistory M K k Z = H₁.localHistory M K k Z₁
  · obtain ⟨A, hA, Z, hkp, hrm, hlh⟩ := h₁
    obtain ⟨B, hB, Z', hkB, hrB, hlhB, hval⟩ := pinned_transfer r₁ r₂ D₁ D₂ hk hkK hpin₁ hpin₂ γ hγ₁ hγ₂
      Z₁ Z₂ hH hV hA Z hkp hrm hlh
    have p₁ := pinnedExp_spec hloc₁ hA Z hkp hrm
    have p₂ := pinnedExp_spec hloc₂ hB Z' hkB hrB
    rw [hlh] at p₁
    rw [hlhB] at p₂
    rw [p₁, p₂, hval]
  · by_cases h₂ : ∃ B ∈ canonHist S n₂ R k0 K k (k + 1), ∃ Z : B.H.Comp k, IsKept B.H k Z ∧
        Z.1 ∉ B.H.rem k ∧ B.H.localHistory M K k Z = H₂.localHistory M K k Z₂
    · exfalso
      obtain ⟨B, hB, Z, hkp, hrm, hlh⟩ := h₂
      obtain ⟨A, hA, Z', hkA, hrA, hlhA, -⟩ := pinned_transfer r₂ r₁ D₂ D₁ hk hkK hpin₂ hpin₁ γ hγ₂ hγ₁
        Z₂ Z₁ hH.symm' (by simpa using hV.symm) hB Z hkp hrm hlh
      exact h₁ ⟨A, hA, Z', hkA, hrA, hlhA⟩
    · unfold pinnedExp
      simp only [h₁, h₂, dite_false]

end Pinned

end Balaban.RootFSpine
