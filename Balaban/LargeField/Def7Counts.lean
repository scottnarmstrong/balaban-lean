module

public import Balaban.LargeField.Def7Basic
public import Balaban.LargeField.Budget.Fine
public import Balaban.LargeField.Budget.Injective
import Mathlib.Tactic.Linarith

/-!
# Def-7: Lemma II.6.3 (a), "(D4) implies (D5)" — DRAFT

* `newCnt_localHistory`, `outCnt_localHistory`, `kappaStepLoc_localHistory`: the step exponent
  `κ^{(k)}(Z', 𝔞)` read off the localized history `𝔞 = 𝔥_{k+1}(Z')` (`kappaStepLoc`, the
  exponent of the step data of a representation) is the step exponent of the budget computed on
  the region history (`BudgetConsts.kappaStep` with `|𝒩_{k+1} ∩ Z'|_#`, `|Z^c_k ∩ Z'|_{#k}`),
  below the horizon.
* `Rep.locOp_bound`, `Rep.preOpTop_bound`, `Rep.opBound_of_data`: **Lemma II.6.3 (a)**: the data
  (D4) of a representation (the step data (S1)-(S2) with the exponents `κ^{(k)}`, the kept data
  (S3)) give the operator bound (D5) at every scale, for the post- and the pre-`R` operators
  (induction on the scale with Lemma II.5.13, `preOp_pkgBound`), given the signs `z_{j+1} > 0`,
  `β_j a L^{d-2} ≥ 0` of the running constants.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField.Def7

open MeasureTheory Balaban RegionHistory

section Counts

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L]

theorem fineSet_union {j : ℕ} (A B : Set (Torus S.d (n j))) :
    RegionHistory.fineSet (S := S) (n := n) M K j A ∪ RegionHistory.fineSet M K j B =
      RegionHistory.fineSet M K j (A ∪ B) := rfl

theorem fineSet_diff {j : ℕ} (A B : Set (Torus S.d (n j))) :
    RegionHistory.fineSet (S := S) (n := n) M K j A \ RegionHistory.fineSet M K j B =
      RegionHistory.fineSet M K j (A \ B) := rfl

theorem newCnt_localHistory (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (Z' : H.Comp (k + 1)) :
    newCnt M (H.localHistory M K (k + 1) Z') k = (Z'.1 ∩ H.newCubes (k + 1)).card := by
  have := H.neZero_L
  obtain ⟨hP, hQ, hR, hS⟩ := H.localHistory_new (M := M) Z' hk (j := k) (Nat.lt_succ_self k)
  have hU : (H.localHistory M K (k + 1) Z').P k ∪ (H.localHistory M K (k + 1) Z').Q k ∪
      (H.localHistory M K (k + 1) Z').R k ∪ (H.localHistory M K (k + 1) Z').Sset k =
      RegionHistory.fineSet (S := S) (n := n) M K (k + 1)
        ((Z'.1 ∩ H.newCubes (k + 1) : Finset (Torus S.d (n (k + 1)))) : Set _) := by
    rw [hP, hQ, hR, hS, fineSet_union, fineSet_union, fineSet_union, H.lin_self]
    congr 1
    ext x
    simp only [RegionHistory.newCubes, Finset.coe_inter, coe_finOf, Set.mem_union,
      Set.mem_inter_iff, RegionStep.newCubes, Region.newCubes, Finset.mem_coe]
    tauto
  unfold newCnt
  rw [hU, card_fineSet H.F.hnn hk]
  have hpos : 0 < (M * S.L ^ (k + 1)) ^ S.d := by
    have := NeZero.pos M; have := NeZero.pos S.L; positivity
  rw [show S.L ^ (k + 1) * M = M * S.L ^ (k + 1) by ring]
  exact Nat.mul_div_cancel_left _ hpos

theorem outCnt_localHistory (H : RegionHistory S n R k0 K) {k : ℕ} (hk : k + 1 ≤ K)
    (Z' : H.Comp (k + 1)) :
    outCnt M (H.localHistory M K (k + 1) Z') k = (H.outCubes k Z').card := by
  classical
  have := H.neZero_L
  have h1 := H.localHistory_Z (M := M) Z' hk (j := k + 1) le_rfl
  have h0 := H.localHistory_Z (M := M) Z' hk (j := k) (Nat.le_succ k)
  rw [H.lin_self] at h1
  rw [H.lin_succ_self (by omega)] at h0
  have hD : (H.localHistory M K (k + 1) Z').Z (k + 1) \ (H.localHistory M K (k + 1) Z').Z k =
      RegionHistory.fineSet (S := S) (n := n) M K k
        ((H.outCubes k Z' : Finset (Torus S.d (n k))) : Set _) := by
    rw [h1, h0]
    ext x
    simp only [RegionHistory.fineSet, Set.mem_sdiff, Set.mem_ofPred_eq, Finset.mem_coe,
      RegionHistory.oldCubes, RegionHistory.outCubes, Finset.mem_filter, Finset.mem_univ,
      true_and]
    rw [← cubeMap_succ H.F.hnn hk x]
    tauto
  unfold outCnt
  rw [hD, card_fineSet H.F.hnn (by omega)]
  have hpos : 0 < (M * S.L ^ k) ^ S.d := by
    have := NeZero.pos M; have := NeZero.pos S.L; positivity
  rw [show S.L ^ k * M = M * S.L ^ k by ring]
  exact Nat.mul_div_cancel_left _ hpos

/-- **The step exponent read off the localized history is the step exponent of the budget**
(below the horizon). -/
theorem kappaStepLoc_localHistory (P : BudgetConsts) (H : RegionHistory S n R k0 K) {k : ℕ}
    (hk : k + 1 ≤ K) (Z' : H.Comp (k + 1)) :
    kappaStepLoc S P M k (H.localHistory M K (k + 1) Z') =
      P.kappaStep S k (Z'.1 ∩ H.newCubes (k + 1)).card (H.outCubes k Z').card := by
  unfold kappaStepLoc
  rw [newCnt_localHistory H hk Z', outCnt_localHistory H hk Z']

end Counts

section Bound

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {geo : Geo S n R M} {cs : OpConsts} {P : BudgetConsts} {k : ℕ}
  (rep : Rep S n R k0 K M N geo cs P k)

/-- **Lemma II.6.3 (a), post-`R` operators**: every localized operator `𝕋_j(Z, 𝔸 ∩ Z)`, `j ≤ K`,
satisfies (1.26) with the exponent `κ_j(Z, 𝔸 ∩ Z)` (Definition II.5.11). -/
theorem Rep.locOp_bound (hz : ∀ j, 0 < cs.z (j + 1))
    (hc : ∀ j, 0 ≤ cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (A : LabHist S n R k0 K) :
    ∀ (j : ℕ) (hj : j ≤ K) (c : A.H.Comp j),
      PkgBound (A.H.localHistory M K j c) j
        (locOp geo cs rep.SD rep.KD A.adm (fun i c => A.lab i c.1) j hj c) (rep.kappaH A j c) := by
  intro j
  induction j with
  | zero => intro _ c; exact (A.H.F.isEmpty_comp_zero.false c).elim
  | succ j ih =>
    intro hj c
    by_cases hkept : IsKept A.H (j + 1) c
    · have e := locOp_kept geo cs rep.SD rep.KD (lab := fun i c => A.lab i c.1) (hH := A.adm) hj
        hkept
      have hb := (rep.KD.bound A.H A.adm (j + 1) c hkept.1 hkept.2.1 hkept.2.2
        (A.lab (j + 1) c.1)).2
      have hκ : rep.kappaH A (j + 1) c = rep.keptExp A (j + 1) c := by
        have hev : A.H.IsKeptEvent (j + 1) c := hkept
        simp only [Rep.kappaH, RegionHistory.kappa, hev, ite_true]
      rw [e, hκ]
      exact hb
    · have e := locOp_level geo cs rep.SD rep.KD (lab := fun i c => A.lab i c.1) (hH := A.adm) hj
        hkept
      have hb := preOp_pkgBound geo cs rep.SD A.adm hj c
        (fun Y _ => locOp geo cs rep.SD rep.KD A.adm (fun i c => A.lab i c.1) j (by omega) Y)
        (hz j) (hc j) (fun Y => rep.kappaH A j Y.1) (fun Y => ih (by omega) Y.1)
      have hκ : rep.kappaH A (j + 1) c = kappaStepLoc S P M j (A.H.localHistory M K (j + 1) c) +
          ∑ Y : ↥(A.H.parts j c), rep.kappaH A j Y.1 := by
        have hev : ¬ A.H.IsKeptEvent (j + 1) c := hkept
        rw [kappaStepLoc_localHistory P A.H hj c, Finset.sum_coe_sort]
        simp only [Rep.kappaH, RegionHistory.kappa, hev, ite_false, RegionHistory.kappaPre]
        ring
      rw [e, hκ]
      exact hb

/-- **Lemma II.6.3 (a), pre-`R` operators**: every pre-`R` operator `𝕋^pre_j(Z, 𝔸 ∩ Z)` satisfies
(1.26) with the exponent `κ^pre_j(Z, 𝔸 ∩ Z)`. -/
theorem Rep.preOpTop_bound (hz : ∀ j, 0 < cs.z (j + 1))
    (hc : ∀ j, 0 ≤ cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (A : LabHist S n R k0 K) :
    ∀ (j : ℕ) (hj : j ≤ K) (c : A.H.Comp j),
      PkgBound (A.H.localHistory M K j c) j (preOpTop geo cs rep.SD rep.KD A j hj c)
        (rep.kappaPreH A j c)
  | 0, _, c => (A.H.F.isEmpty_comp_zero.false c).elim
  | j + 1, hj, c => by
    have hb := preOp_pkgBound geo cs rep.SD A.adm hj c
      (fun Y _ => locOp geo cs rep.SD rep.KD A.adm (fun i c => A.lab i c.1) j (by omega) Y)
      (hz j) (hc j) (fun Y => rep.kappaH A j Y.1)
      (fun Y => rep.locOp_bound hz hc A j (by omega) Y.1)
    have hκ : rep.kappaPreH A (j + 1) c = kappaStepLoc S P M j (A.H.localHistory M K (j + 1) c) +
        ∑ Y : ↥(A.H.parts j c), rep.kappaH A j Y.1 := by
      rw [kappaStepLoc_localHistory P A.H hj c, Finset.sum_coe_sort]
      simp only [Rep.kappaPreH, RegionHistory.kappaPre]
      ring
    rw [hκ]
    exact hb

/-- **Lemma II.6.3 (a): (D4) implies (D5).**  The step and kept data of a representation (which
satisfy (S0)-(S3) by their types) give the operator bound (D5), at every top scale. -/
theorem Rep.opBound_of_data (hz : ∀ j, 0 < cs.z (j + 1))
    (hc : ∀ j, 0 ≤ cs.beta j * cs.aKer * (S.L : ℝ) ^ (S.d - 2)) (top : ℕ) (hkK : k ≤ K) :
    D5Bound top hkK rep :=
  fun A _ j hj => ⟨fun _ c _ => rep.locOp_bound hz hc A j (hj.trans hkK) c,
    fun c => rep.preOpTop_bound hz hc A j (hj.trans hkK) c⟩

end Bound

end Balaban.LargeField.Def7
