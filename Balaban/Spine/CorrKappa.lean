/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.CorrBook
public import Balaban.LargeField.Budget.Exponents
public import Balaban.LargeField.Def7

/-!
# The exponents `κ^pre` of corresponding components of two tori

`kapM` is the model of the exponents `κ_k(Z, 𝔸 ∩ Z)` of Definition II.5.11 for a representation
whose kept exponents are pinned to `κ^pre` and whose kept costs `γ_j(ϰ)` do not depend on the
label: `κ_{j+1} = ∑ κ_j + κ^{(j)} + c_{j+1}` at the kept events and `∑ κ_j + κ^{(j)}` elsewhere,
with a constant `c_j`.  It depends on the history only through its bookkeeping, so it agrees for
components of two tori with corresponding lineages (`kapM_corr`, `kapPreM_corr`, from `bk_corr`).
`kappaH_eq_kapM` shows that the exponents of a pinned representation are the model exponents.
-/

@[expose] public section

open Balaban Balaban.LargeField

set_option linter.unusedSectionVars false

namespace Balaban.RootFSpine

section Kappa

variable {S : Setting} {n₁ n₂ : ℕ → ℕ} [∀ k, NeZero (n₁ k)] [∀ k, NeZero (n₂ k)] {R : ℕ → ℝ}
  {k0 K : ℕ} {M : ℕ} [NeZero M] [NeZero S.L] {H₁ : RegionHistory S n₁ R k0 K}
  {H₂ : RegionHistory S n₂ R k0 K}

open RegionHistory

/-- The number of cubes of a corresponding pair of sets is the same. -/
theorem card_eq_of_fcorr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} {j : ℕ}
    (hj : j ≤ kmax) {A₁ : Finset (Torus S.d (n₁ j))} {A₂ : Finset (Torus S.d (n₂ j))}
    (h : FCorr M cc j A₁ A₂ (K := K)) : A₁.card = A₂.card := by
  obtain ⟨-, -, hl⟩ := fcorr_lifts E hj h
  rw [← card_cliftSet (P := S.L ^ j * M) (cc := cc) A₁,
    ← card_cliftSet (P := S.L ^ j * M) (cc := cc) A₂]
  exact congrArg Finset.card hl

/-- **`κ^pre` of corresponding components**, given the exponents of corresponding old parts. -/
theorem kappaPre_corr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} {j : ℕ}
    (hj : j + 1 ≤ kmax) {Z₁ : H₁.Comp (j + 1)} {Z₂ : H₂.Comp (j + 1)}
    (h : LinCorr M H₁ H₂ cc (j + 1) Z₁ Z₂) (P : BudgetConsts)
    (κ₁ : H₁.Comp j → ℝ) (κ₂ : H₂.Comp j → ℝ)
    (hκ : ∀ c₁ ∈ H₁.parts j Z₁, ∀ c₂ ∈ H₂.parts j Z₂,
      partLift M cc j c₁.1 = partLift M cc j c₂.1 → κ₁ c₁ = κ₂ c₂) :
    H₁.kappaPre P j κ₁ Z₁ = H₂.kappaPre P j κ₂ Z₂ := by
  classical
  have hjK : j < K := by have := E.hkK; omega
  have hP := parts_corr E hj h
  have he₁ : Function.Injective (fun c : H₁.Comp j => partLift M cc j c.1) :=
    (partLift_injective M cc j).comp Subtype.val_injective
  have he₂ : Function.Injective (fun c : H₂.Comp j => partLift M cc j c.1) :=
    (partLift_injective M cc j).comp Subtype.val_injective
  have hnew : (Z₁.1 ∩ H₁.newCubes (j + 1)).card = (Z₂.1 ∩ H₂.newCubes (j + 1)).card :=
    card_eq_of_fcorr E hj h.new
  have hold : (H₁.oldCubes j Z₁).card = (H₂.oldCubes j Z₂).card :=
    card_eq_of_fcorr E (by omega) (h.old (M := M) hjK)
  have htop : Z₁.1.card = Z₂.1.card := card_eq_of_fcorr E hj h.top
  have hout : (H₁.outCubes j Z₁).card = (H₂.outCubes j Z₂).card := by
    have c1 := H₁.card_oldCubes_add_outCubes hjK Z₁
    have c2 := H₂.card_oldCubes_add_outCubes hjK Z₂
    rw [hold, htop] at c1
    omega
  unfold RegionHistory.kappaPre
  rw [sum_eq_of_image he₁ he₂ hP κ₁ κ₂ hκ, hnew, hout]

/-- The model of the exponents `κ_k` of the components of `Z^pre_k`: `κ^pre_k` plus a constant
`cst k` at the kept events. -/
noncomputable def kapM {n : ℕ → ℕ} [∀ k, NeZero (n k)] (H : RegionHistory S n R k0 K)
    (P : BudgetConsts) (cst : ℕ → ℝ) : ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | k + 1, Z' =>
    H.kappaPre P k (kapM H P cst k) Z' + (open Classical in
      if H.IsKeptEvent (k + 1) Z' then cst (k + 1) else 0)

/-- **The model exponents of corresponding components agree.** -/
theorem kapM_corr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} (P : BudgetConsts)
    (cst : ℕ → ℝ) :
    ∀ (k : ℕ), k ≤ kmax → ∀ (Z₁ : H₁.Comp k) (Z₂ : H₂.Comp k),
      LinCorr M H₁ H₂ cc k Z₁ Z₂ →
      Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) k Z₁.1 →
      Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) k Z₂.1 →
      kapM H₁ P cst k Z₁ = kapM H₂ P cst k Z₂
  | 0, _, Z₁, _, _, _, _ => (H₁.F.isEmpty_comp_zero.false Z₁).elim
  | j + 1, hj, Z₁, Z₂, h, m₁, m₂ => by
    classical
    have hIH := parts_ih E hj h m₁ m₂ (fun c₁ c₂ => kapM H₁ P cst j c₁ = kapM H₂ P cst j c₂)
      (fun c₁ c₂ hl m1 m2 => kapM_corr E P cst j (by omega) c₁ c₂ hl m1 m2)
    have hbk := bk_corr E (j + 1) hj Z₁ Z₂ h m₁ m₂
    have hkept : H₁.IsKeptEvent (j + 1) Z₁ ↔ H₂.IsKeptEvent (j + 1) Z₂ := by
      unfold RegionHistory.IsKeptEvent
      rw [hbk]
    simp only [kapM]
    rw [kappaPre_corr E hj h P _ _ hIH]
    by_cases hk : H₁.IsKeptEvent (j + 1) Z₁
    · simp [hk, hkept.1 hk]
    · have hk2 : ¬ H₂.IsKeptEvent (j + 1) Z₂ := fun h' => hk (hkept.2 h')
      simp [hk, hk2]


/-- `κ^pre_k` in the model: `0` at `k = 0`, and `κ^pre_{j+1} = ∑ κ_j + κ^{(j)}` with the model
exponents `κ_j`. -/
noncomputable def kapPreM {n : ℕ → ℕ} [∀ k, NeZero (n k)] (H : RegionHistory S n R k0 K)
    (P : BudgetConsts) (cst : ℕ → ℝ) : ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | k + 1, Z' => H.kappaPre P k (kapM H P cst k) Z'

/-- **The model `κ^pre` of corresponding components agree.** -/
theorem kapPreM_corr {kmax : ℕ} (E : CorrEnv S n₁ n₂ M K kmax) {cc : Fin S.d → ℤ} (P : BudgetConsts)
    (cst : ℕ → ℝ) {k : ℕ} (hk : k ≤ kmax) {Z₁ : H₁.Comp k} {Z₂ : H₂.Comp k}
    (h : LinCorr M H₁ H₂ cc k Z₁ Z₂)
    (m₁ : Marg (S := S) (n := n₁) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) k Z₁.1)
    (m₂ : Marg (S := S) (n := n₂) M K cc (M * n₁ K * S.L ^ K) (M * n₂ K * S.L ^ K) k Z₂.1) :
    kapPreM H₁ P cst k Z₁ = kapPreM H₂ P cst k Z₂ := by
  cases k with
  | zero => rfl
  | succ j =>
    refine kappaPre_corr E hk h P _ _ ?_
    exact parts_ih E hk h m₁ m₂ (fun c₁ c₂ => kapM H₁ P cst j c₁ = kapM H₂ P cst j c₂)
      (fun c₁ c₂ hl m1 m2 => kapM_corr E P cst j (by omega) c₁ c₂ hl m1 m2)

end Kappa

section Model

open Balaban.LargeField.Def7

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}

/-- **Along a history of a representation whose kept exponents are pinned and whose kept costs are
`γ_i`, the exponents `κ_j` of the non-removed components are the model exponents.** -/
theorem kappaH_eq_kapM (rep : Rep S n R k0 K M N geo cs P k) {top : ℕ} (hpin : D4Pin top rep)
    (γ : ℕ → ℝ) (hgam : ∀ i, i < top → ∀ l, rep.KD.gam i l = γ i) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) :
    ∀ j, j < top → ∀ Z : A.H.Comp j, Z.1 ∉ A.H.rem j →
      rep.kappaH A j Z =
        kapM A.H P (fun i => -(S.CR * S.lam i ^ (2 * S.d + 1)) + γ i) j Z
  | 0, _, Z, _ => (A.H.F.isEmpty_comp_zero.false Z).elim
  | j + 1, hj, Z, hZ => by
    classical
    have key : rep.kappaH A (j + 1) Z =
        if A.H.IsKeptEvent (j + 1) Z then rep.keptExp A (j + 1) Z
        else A.H.kappaPre P j (rep.kappaH A j) Z := by
      show A.H.kappa P (rep.keptExp A) (j + 1) Z = _
      simp only [RegionHistory.kappa]
      rfl
    have hparts : A.H.kappaPre P j (rep.kappaH A j) Z =
        A.H.kappaPre P j (kapM A.H P (fun i => -(S.CR * S.lam i ^ (2 * S.d + 1)) + γ i) j) Z := by
      unfold RegionHistory.kappaPre
      congr 1
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' := (A.H.mem_parts j c Z).1 hc
      exact kappaH_eq_kapM rep hpin γ hgam hA j (by omega) c hc'.1
    rw [key]
    simp only [kapM]
    by_cases hk : A.H.IsKeptEvent (j + 1) Z
    · simp only [hk, ite_true]
      have hkept : IsKept A.H (j + 1) Z := hk
      have hp := hpin A hA (j + 1) (by omega) hj Z hkept hZ
      unfold Rep.keptExp
      rw [hp, hgam (j + 1) hj]
      show A.H.kappaPre P j (rep.kappaH A j) Z - _ + _ = _
      rw [hparts]
      ring
    · simp only [hk, ite_false, add_zero]
      exact hparts

theorem kappaPreH_eq_kapPreM (rep : Rep S n R k0 K M N geo cs P k) {top : ℕ} (hpin : D4Pin top rep)
    (γ : ℕ → ℝ) (hgam : ∀ i, i < top → ∀ l, rep.KD.gam i l = γ i) {A : LabHist S n R k0 K}
    (hA : A ∈ rep.hist) {j : ℕ} (hj : j ≤ top) (Z : A.H.Comp j) :
    rep.kappaPreH A j Z =
      kapPreM A.H P (fun i => -(S.CR * S.lam i ^ (2 * S.d + 1)) + γ i) j Z := by
  cases j with
  | zero => rfl
  | succ j =>
    show A.H.kappaPre P j (rep.kappaH A j) Z = A.H.kappaPre P j (kapM A.H P _ j) Z
    unfold RegionHistory.kappaPre
    congr 1
    refine Finset.sum_congr rfl fun c hc => ?_
    have hc' := (A.H.mem_parts j c Z).1 hc
    exact kappaH_eq_kapM rep hpin γ hgam hA j (by omega) c hc'.1

end Model

end Balaban.RootFSpine

