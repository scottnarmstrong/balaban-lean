/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.KeptHalf
public import Balaban.LargeField.Budget.KeptPositions

/-!
# The exponent `κ^pre_k` is a function of the localized history (OPEN-R-TOP-PIN)

LFR Definition I.4.1, Lemma I.4.3, Lemma I.4.13; P7 (1.3)--(1.6).  For two histories `𝔸, 𝔸'` and
components `Z, Z'` of `Z^pre_k` with the same localized history `𝔥_k(Z) = 𝔥_k(Z')`:

* the spine and the book of `Z` and `Z'` agree (`spine_bk_eq_of_localHistory_eq`: the choice of the
  spine by `Classical.choose` is a choice among the spines allowed by `SpineOK`, a property of the
  cubes of `Z`, of the old parts as a set of cubes with their spines, and of the number of new
  cubes, all functions of the localized history), so the kept events of `Z` and `Z'` agree;
* the old parts of `Z` and `Z'` are the components of the same set of cubes and have the same
  localized histories (`record_forward`), the same new cubes, and the same number of cubes of
  `Z_{k-1}^c` over them (`card_oldCubes_add_outCubes`);
* the kept costs `γ_j(ϰ)` do not depend on the label `ϰ`.

Hence `κ_j` and `κ^pre_k` are functions of the localized history (`kappaH_eq_of_localHistory_eq`,
`kappaPreH_eq_of_localHistory_eq`), which is `KappaPreLocal` (`kappaPreLocal_of_gam_indep`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

section Generic

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]

/-- **`κ^pre` is a function of the localized history, given the exponents of the old parts.**
For components `Z₁, Z₂` of `Z^pre_{k+1}` of two region histories with the same localized history,
`∑_Y κ_k(Y) + κ^{(k)}(Z)` agrees as soon as the exponents `κ_k` agree at old parts with the same
cubes and the same localized history. -/
theorem kappaPre_eq_of_localHistory_eq (P : BudgetConsts) {H₁ H₂ : RegionHistory S n R k0 K}
    {k : ℕ} (hkK : k + 1 ≤ K) (κ₁ : H₁.Comp k → ℝ) (κ₂ : H₂.Comp k → ℝ)
    (Z₁ : H₁.Comp (k + 1)) (Z₂ : H₂.Comp (k + 1))
    (h : localHistory H₁ M K (k + 1) Z₁ = localHistory H₂ M K (k + 1) Z₂)
    (hκ : ∀ (c₁ : H₁.Comp k) (c₂ : H₂.Comp k), c₁ ∈ H₁.parts k Z₁ → c₂ ∈ H₂.parts k Z₂ →
      c₁.1 = c₂.1 → localHistory H₁ M K k c₁ = localHistory H₂ M K k c₂ → κ₁ c₁ = κ₂ c₂) :
    H₁.kappaPre P k κ₁ Z₁ = H₂.kappaPre P k κ₂ Z₂ := by
  classical
  obtain ⟨hZ, hold, hnew, hfam⟩ := record_forward hkK Z₁ Z₂ h
  have hk : k < K := by omega
  have e1 := H₁.parts_image_eq_comps hk Z₁
  have e2 := H₂.parts_image_eq_comps hk Z₂
  have hex : ∀ c₁ ∈ H₁.parts k Z₁, ∃ c₂ ∈ H₂.parts k Z₂, c₂.1 = c₁.1 := by
    intro c₁ hc₁
    have : c₁.1 ∈ (H₂.parts k Z₂).image Subtype.val := by
      rw [e2, ← hold, ← e1]; exact Finset.mem_image_of_mem _ hc₁
    obtain ⟨c₂, hc₂, hv⟩ := Finset.mem_image.mp this
    exact ⟨c₂, hc₂, hv⟩
  have hex' : ∀ c₂ ∈ H₂.parts k Z₂, ∃ c₁ ∈ H₁.parts k Z₁, c₁.1 = c₂.1 := by
    intro c₂ hc₂
    have : c₂.1 ∈ (H₁.parts k Z₁).image Subtype.val := by
      rw [e1, hold, ← e2]; exact Finset.mem_image_of_mem _ hc₂
    obtain ⟨c₁, hc₁, hv⟩ := Finset.mem_image.mp this
    exact ⟨c₁, hc₁, hv⟩
  have hsum : ∑ c ∈ H₁.parts k Z₁, κ₁ c = ∑ c ∈ H₂.parts k Z₂, κ₂ c := by
    refine Finset.sum_bij (fun c hc => (hex c hc).choose) (fun c hc => (hex c hc).choose_spec.1)
      (fun c hc c' hc' hcc => ?_) (fun c₂ hc₂ => ?_) (fun c hc => ?_)
    · have h1 := (hex c hc).choose_spec.2
      have h2 := (hex c' hc').choose_spec.2
      exact Subtype.ext (by rw [← h1, ← h2, hcc])
    · obtain ⟨c₁, hc₁, hv⟩ := hex' c₂ hc₂
      refine ⟨c₁, hc₁, Subtype.ext ?_⟩
      rw [(hex c₁ hc₁).choose_spec.2, hv]
    · have hv := (hex c hc).choose_spec.2
      have hY : c.1 ∈ comps (S.omega k) (H₁.oldCubes k Z₁) := by
        rw [← e1]; exact Finset.mem_image_of_mem _ hc
      have hmem := (hex c hc).choose_spec.1
      have hc2 : (hex c hc).choose = ⟨c.1, (hv ▸ (hex c hc).choose.2)⟩ := Subtype.ext hv
      exact hκ c _ hc hmem hv.symm (by
        rw [hc2]; exact hfam c.1 c.2 (hv ▸ (hex c hc).choose.2) hY)
  unfold RegionHistory.kappaPre
  rw [hsum, ← hnew]
  congr 2
  have c1 := H₁.card_oldCubes_add_outCubes hk Z₁
  have c2 := H₂.card_oldCubes_add_outCubes hk Z₂
  rw [hold, hZ] at c1
  omega

end Generic

section RepLocal

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **`κ_j(Z, 𝔸 ∩ Z)` is a function of the localized history** (below the scale `j` the costs
`γ_i(ϰ)` of the kept labels do not depend on the label). -/
theorem kappaH_eq_of_localHistory_eq (r : Rep S n R k0 K M N geo cs P k)
    (A B : LabHist S n R k0 K) :
    ∀ j, j ≤ K → (∀ i, i ≤ j → ∀ l l', r.KD.gam i l = r.KD.gam i l') →
      ∀ (Z : A.H.Comp j) (Z' : B.H.Comp j),
        localHistory A.H M K j Z = localHistory B.H M K j Z' → r.kappaH A j Z = r.kappaH B j Z'
  | 0, _, _, Z, _, _ => (A.H.F.isEmpty_comp_zero.false Z).elim
  | j + 1, hjK, hgam, Z, Z', h => by
    classical
    unfold Rep.kappaH
    simp only [RegionHistory.kappa]
    by_cases hk : A.H.IsKeptEvent (j + 1) Z
    · have hk2 : B.H.IsKeptEvent (j + 1) Z' := (isKeptEvent_iff_of_localHistory_eq hjK Z Z' h).1 hk
      simp only [hk, hk2, ite_true]
      unfold Rep.keptExp
      rw [h, hgam (j + 1) le_rfl _ (B.lab (j + 1) Z'.1)]
    · have hk2 : ¬ B.H.IsKeptEvent (j + 1) Z' :=
        fun h' => hk ((isKeptEvent_iff_of_localHistory_eq hjK Z Z' h).2 h')
      simp only [hk, hk2, ite_false]
      refine kappaPre_eq_of_localHistory_eq P hjK _ _ Z Z' h fun c₁ c₂ _ _ _ hh => ?_
      exact kappaH_eq_of_localHistory_eq r A B j (by omega) (fun i hi => hgam i (by omega)) c₁ c₂ hh

/-- **`κ^pre_j(Z, 𝔸 ∩ Z)` is a function of the localized history** (below the scale `j` the costs
`γ_i(ϰ)` of the kept labels do not depend on the label). -/
theorem kappaPreH_eq_of_localHistory_eq (r : Rep S n R k0 K M N geo cs P k)
    (A B : LabHist S n R k0 K) {j : ℕ} (hjK : j ≤ K)
    (hgam : ∀ i, i < j → ∀ l l', r.KD.gam i l = r.KD.gam i l')
    (Z : A.H.Comp j) (Z' : B.H.Comp j)
    (h : localHistory A.H M K j Z = localHistory B.H M K j Z') :
    r.kappaPreH A j Z = r.kappaPreH B j Z' := by
  cases j with
  | zero => rfl
  | succ j =>
    refine kappaPre_eq_of_localHistory_eq P hjK _ _ Z Z' h fun c₁ c₂ _ _ _ hh => ?_
    exact kappaH_eq_of_localHistory_eq r A B j (by omega) (fun i hi => hgam i (by omega)) c₁ c₂ hh

/-- **OPEN-R-TOP-PIN: the locality of `κ^pre_k`.**  The exponent `κ^pre_k(Z, 𝔸 ∩ Z)` of a
component is a function of its localized history, for any set of histories, as soon as the kept costs
`γ_i(ϰ)`, `i < k`, do not depend on the label. -/
theorem kappaPreLocal_of_gam_indep (r₀ : Rep S n R k0 K M N geo cs P k)
    (hist : Finset (LabHist S n R k0 K)) (hkK : k ≤ K)
    (hgam : ∀ i, i < k → ∀ l l', r₀.KD.gam i l = r₀.KD.gam i l') : KappaPreLocal r₀ hist k :=
  fun A _ Z _ _ B _ Z' _ _ h =>
    kappaPreH_eq_of_localHistory_eq r₀ A B hkK hgam Z Z' h

end RepLocal

end Balaban.RootFSpine
