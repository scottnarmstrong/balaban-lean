/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.AgreeTransportLocal
public import Balaban.LargeField.Def7

/-!
# The pin `D4Pin` along `Agree`

`d4Pin_of_agree`: if `rep₁`, `rep₂` have the same kept exponents `κK` and kept costs `γ`, the same
budget constants `c₁, c₂, β_j` for `j < m`, `rep₁` satisfies `D4Pin (m + 1)` and every history of
`rep₂` agrees up to `m` (with the `R`-records up to `m`) with a history of `rep₁`, then `rep₂`
satisfies `D4Pin (m + 1)`. The ingredients are the transports of `HAgr` (components, spines and
books, lineages and localized histories, the exponents `κ_j`) and the equality of the kept labels
of non-removed kept components under `Agree`.
-/

@[expose] public section

namespace Balaban.RootFSpine

open Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- The kept labels of a non-removed kept component are the same along `Agree`. -/
theorem lab_eq_of_agree {m : ℕ} {A B : LabHist S n R k0 K} (hAB : A.Agree m (m + 1) B) {i : ℕ}
    (hi : i ≤ m) (c : A.H.Comp i) (hk : IsKept A.H i c) (hr : c.1 ∉ A.H.rem i) :
    A.lab i c.1 = B.lab i c.1 := by
  classical
  have h := HAgr.of_agree hAB
  have e := congrFun (hAB.2 i (by omega)).2 c.1
  have hB : c.1 ∈ comps (S.omega i) (B.H.Zp i) := by
    have := (h.cmap hi c).2
    rwa [h.cmap_val] at this
  have hc : (⟨c.1, hB⟩ : B.H.Comp i) = h.cmap hi c := Subtype.ext (h.cmap_val hi c).symm
  have hkB : IsKept B.H i ⟨c.1, hB⟩ := by rw [hc]; exact (h.isKept_iff hi c).2 hk
  have hrB : c.1 ∉ B.H.rem i := by rw [← h.rem i hi]; exact hr
  have e1 : A.keptLab i c.1 = some (A.lab i c.1) := by
    unfold LabHist.keptLab; simp [c.2, hk, hr]
  have e2 : B.keptLab i c.1 = some (B.lab i c.1) := by
    unfold LabHist.keptLab; simp [hB, hkB, hrB]
  exact Option.some.inj ((e1.symm.trans e).trans e2)

variable {M N : ℕ} [NeZero M] [NeZero S.L] {geo : Geo S n R M}

/-- **Transport of the pin along `Agree`.** -/
theorem d4Pin_of_agree {cs₁ cs₂ : OpConsts} {P₁ P₂ : BudgetConsts} {k₁ k₂ : ℕ}
    (rep₁ : Rep S n R k0 K M N geo cs₁ P₁ k₁) (rep₂ : Rep S n R k0 K M N geo cs₂ P₂ k₂) (m : ℕ)
    (hκ : rep₂.κK = rep₁.κK) (hgam : ∀ j l, rep₂.KD.gam j l = rep₁.KD.gam j l)
    (hc1 : P₂.c1 = P₁.c1) (hc2 : P₂.c2 = P₁.c2) (hβ : ∀ i, i < m → P₂.beta i = P₁.beta i)
    (hpin : D4Pin (m + 1) rep₁)
    (hcomp : ∀ A ∈ rep₂.hist, ∃ B ∈ rep₁.hist, A.Agree m (m + 1) B) : D4Pin (m + 1) rep₂ := by
  intro A hA j hj1 hjt Z hK hr
  obtain ⟨B, hB, hAB⟩ := hcomp A hA
  have h := HAgr.of_agree hAB
  have hjm : j ≤ m := by omega
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hK' : IsKept B.H (j' + 1) (h.cmap hjm Z) := (h.isKept_iff hjm Z).2 hK
  have hr' : (h.cmap hjm Z).1 ∉ B.H.rem (j' + 1) := (h.rem_iff hjm Z).2 hr
  have hp := hpin B hB (j' + 1) hj1 (by omega) _ hK' hr'
  have hP : ∀ i, i < m → ∀ a b, P₁.kappaStep S i a b = P₂.kappaStep S i a b := by
    intro i hi a b
    unfold BudgetConsts.kappaStep
    rw [hc1, hc2, hβ i hi]
  have hke : ∀ i (hi : i ≤ m) (c : A.H.Comp i), c.1 ∉ A.H.rem i → A.H.IsKeptEvent i c →
      rep₁.keptExp B i (h.cmap hi c) = rep₂.keptExp A i c := by
    intro i hi c hrc hkc
    unfold Rep.keptExp
    rw [h.localHistory_eq hi M K c, ← congrFun (congrFun hκ i) _, hgam,
      lab_eq_of_agree hAB hi c hkc hrc, h.cmap_val]
  have hkp : rep₁.kappaPreH B (j' + 1) (h.cmap hjm Z) = rep₂.kappaPreH A (j' + 1) Z := by
    show B.H.kappaPre P₁ j' (rep₁.kappaH B j') _ = A.H.kappaPre P₂ j' (rep₂.kappaH A j') Z
    refine h.kappaPre_eq P₂ P₁ hP (rep₂.kappaH A j') (rep₁.kappaH B j') hjm Z ?_
    intro c hc
    have hrc := ((A.H.mem_parts j' c Z).1 hc).1
    exact h.kappa_eq P₂ P₁ hP (rep₂.keptExp A) (rep₁.keptExp B) hke j' (by omega) c hrc
  rw [← hkp, ← hp, ← congrFun (congrFun hκ (j' + 1)) _, h.localHistory_eq hjm M K Z]

end Balaban.RootFSpine
