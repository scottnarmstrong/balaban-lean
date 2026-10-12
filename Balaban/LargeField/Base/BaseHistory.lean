module

public import Balaban.LargeField.Base.BaseRecord
public import Balaban.LargeField.Budget.LemmaB
public import Balaban.LargeField.History.StepKinds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The base record inside a region history (LF-RECONSTRUCTION Lemma II.7.2)

For a region history `H` the step `0 → 1` is a base record (`RegionHistory.baseRecord`,
`Z_0 = ∅`).  Lemma II.7.2 (RH holds for every `FlowSteps`):

* (a) `Ω'_1 = 𝕋_1`, no component of `Z^pre_0`, `rem_0 = ∅`, and (with (c)) `rem_1 = ∅` for an
  admissible history, so `Z_1 = Z^pre_1`;
* (b) `baseRecord_seeds_new` (G1 with new seeds only);
* (c) `base_noRipe`: every component of `Z^pre_1` contains a new cube, the step `0 → 1` is a (T2)
  output with no old part, and no component is ripe;
* (d) `base_P_nbhd_compl`, `base_bond_comp`, `base_not_mem_P_of_near_Omega`;
* (e) `base_budget`: the budget recursion (B) of LF-2 at `k = 0` with the exponents
  `κ^{(0)}(Z') = A₃ (log β)^{2 p₀} |𝒩_1 ∩ Z'|_# - (c₁ log β + c₂) |Z'|_1` and
  `log C_1(Z') = (5/4) |Z'|_{#0}`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

theorem step_zero_Z : (H.step 0).Z = ∅ := by
  have h := H.Z_eq 0
  rw [H.rem_empty 0 (Or.inl rfl)] at h
  simpa [FlowSteps.Zpre] using h

theorem step_zero_OmegaPrime [NeZero S.L] : (H.step 0).OmegaPrime = Set.univ := by
  show Region.OmegaPrime S.L _ (Region.Uprime S.L (n 1) _ (H.step 0).Z) = _
  rw [H.step_zero_Z]
  exact omegaPrime_of_empty _ _

/-- The step `0 → 1` of a region history as a base record. -/
noncomputable def baseRecord [NeZero S.L] : BaseRecord S.d S.L (n 1) (R 0) :=
  BaseRecord.ofStep (H.step 0) H.step_zero_Z

theorem baseRecord_toStep [NeZero S.L] :
    H.baseRecord.toStep (n 0) (R (0 - 1)) = H.step 0 :=
  baseRecord_ofStep_toStep _ _

/-! ### (a) -/

/-- **Lemma II.7.2 (a)**: `Z_0 = ∅`, `U_0 = U'_0 = ∅`, `Ω'_1 = 𝕋_1`, there are no components at
scale `0`, and the removed set at scale `0` is empty. -/
theorem base_geometry [NeZero S.L] :
    (H.step 0).Z = ∅ ∧ (H.step 0).U = ∅ ∧ (H.step 0).Uprime = ∅ ∧
      (H.step 0).OmegaPrime = Set.univ ∧ H.Zp 0 = ∅ ∧ IsEmpty (H.Comp 0) ∧ H.rem 0 = ∅ := by
  have h := baseRecord_isStep H.baseRecord (n 0) (R (0 - 1))
  rw [H.baseRecord_toStep] at h
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, H.F.Zp_zero, H.F.isEmpty_comp_zero,
    H.rem_empty 0 (Or.inl rfl)⟩

/-! ### (b) -/

/-- **Lemma II.7.2 (b)** ((G1) at `k = 0` with new seeds only): every `x ∈ Z^{(0)}_1` is linked in
`Z^{(0)}_1` (width `ω_1`) to a new cube `q ∈ 𝒩_1` with `d(x, q) ≤ 5 r_0` (`5 = s'`, the weight of
a new seed); in particular `x` lies in the component of `q`. -/
theorem baseRecord_seeds_new {x : Torus S.d (n 1)} (hx : x ∈ (H.step 0).Z0) :
    ∃ q ∈ (H.step 0).newCubes, supDist x q ≤ 5 * S.r 0 ∧
      Linked (S.omega 1) (H.step 0).Z0 x q ∧
      ∃ C ∈ comps (S.omega 1) (finOf (H.step 0).Z0), x ∈ C ∧ q ∈ C := by
  have hg := H.stepGeom 0
  obtain ⟨σ, hσ, y, hy, hd, hl⟩ := (H.step 0).attribution_seeds (ωk := S.omega 0) hg.rad hg.hn hx
  have hold : (H.step 0).oldSeeds (S.omega 0) = ∅ := by
    ext σ'
    simp only [RegionStep.oldSeeds, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨Y, hY, -⟩
    rw [H.step_zero_Z] at hY
    simp [finOf, comps] at hY
  rcases hσ with hσ | ⟨q, hq, rfl⟩
  · rw [hold] at hσ; exact absurd hσ (Set.notMem_empty _)
  · rw [Set.mem_singleton_iff] at hy
    subst hy
    have hw : (H.step 0).seedWeight (S.omega 0) {y} = 5 := by
      unfold RegionStep.seedWeight
      rw [hold]; simp
    rw [hw] at hd
    refine ⟨y, hq, hd, hl, ?_⟩
    obtain ⟨C, hC, hxC⟩ := mem_comp_self (ω := S.omega 1) (mem_finOf.mpr hx)
    refine ⟨C, hC, hxC, ?_⟩
    rw [mem_comp_iff hC hxC]
    refine ⟨mem_finOf.mpr ((H.step 0).newCubes_subset_Z0 hq), ?_⟩
    rwa [coe_finOf]

/-! ### (c) -/

theorem base_parts_empty (Z' : H.Comp 1) : H.parts 0 Z' = ∅ :=
  Finset.eq_empty_of_forall_notMem fun c _ => (H.F.isEmpty_comp_zero.false c).elim

/-- **Lemma II.7.2 (c)**, first part: every component of `Z^pre_1` contains a new cube (all seeds
are new), so the step `0 → 1` is quiet in no component. -/
theorem base_newCube (Z' : H.Comp 1) : 1 ≤ (Z'.1 ∩ H.newCubes 1).card := by
  have h := H.seed_pos 0 Z'
  rwa [H.base_parts_empty Z', Finset.card_empty, zero_add] at h

/-- **Lemma II.7.2 (c)**: in regime (A) (`1 ≤ k₀`) the book of a component `Z'` of `Z^pre_1` is a
(T2) output (`m = 0` old parts, `r ≥ 1` new cubes), its window state is `Pre` or
`Active(1, 1, ∅)` (`WState.restart`), and it is not ripe (`t^* ≥ 2`). -/
theorem base_noRipe (G : S.Good) (hk0 : 1 ≤ k0) (Z' : H.Comp 1) :
    H.parts 0 Z' = ∅ ∧ 1 ≤ H.nr 0 Z' ∧
      (H.bk 1 Z').st = WState.restart 1 (H.bk 1 Z').pt ∧ ¬ S.Ripe 1 (H.bk 1 Z') := by
  obtain ⟨-, hcase, hs1, -⟩ := H.step_facts G (k := 0) hk0 Z'
  have hr : 1 ≤ H.nr 0 Z' := H.base_newCube Z'
  refine ⟨H.base_parts_empty Z', hr, hs1 hr, ?_⟩
  cases hcase with
  | shadow i hparts hr0 => omega
  | new hr' hf =>
    obtain ⟨h1, h2, -⟩ := hf
    have h1 : S.tStar (H.bk 1 Z') = (H.bk 1 Z').s + S.nq (H.bk 1 Z').s := h1
    have h2 : 1 ≤ (H.bk 1 Z').s := h2
    rintro ⟨-, h3⟩
    have : 1 ≤ S.nq (H.bk 1 Z').s := by unfold Setting.nq; omega
    omega
  | mergePre hr0 => omega
  | mergeCap hr0 => omega
  | overflow hr0 => omega

/-- **Lemma II.7.2 (a)/(c)**: for an admissible history no component of `Z^pre_1` is removed, so
`Z_1 = Z^pre_1`. -/
theorem base_rem_one (G : S.Good) (hadm : H.Admissible) : H.rem 1 = ∅ := by
  classical
  by_cases hk : 1 ≤ k0
  · refine Finset.eq_empty_of_forall_notMem fun Y hY => ?_
    have hr := hadm 1 ⟨Y, H.rem_sub 1 hY⟩ hY
    exact (H.base_noRipe G hk ⟨Y, H.rem_sub 1 hY⟩).2.2.2 hr
  · exact H.rem_empty 1 (Or.inr (by omega))

theorem base_Z_one (G : S.Good) (hadm : H.Admissible) : (H.step 1).Z = H.F.Zpre 1 := by
  have h := H.Z_eq 1
  rw [H.base_rem_one G hadm] at h
  simpa using h

/-! ### (d) -/

/-- **Lemma II.7.2 (d)**: `P_1^{∼3} ⊆ Ω_1^c ⊆ Z^pre_1`. -/
theorem base_P_nbhd_compl [NeZero S.L] :
    nbhd 3 (H.step 0).P ⊆ (H.step 0).Omegaᶜ ∧ (H.step 0).Omegaᶜ ⊆ H.F.Zpre 1 := by
  refine ⟨?_, ?_⟩
  · have := H.baseRecord.nbhd_P_subset_compl_Omega
    have h := baseRecord_isStep H.baseRecord (n 0) (R (0 - 1))
    rw [H.baseRecord_toStep] at h
    rw [h.2.2.2.2.2.2.2.2.1]
    exact this
  · exact fun x hx => (H.step 0).Z0_subset_Zpre _ _ ((H.step 0).Omega_compl_subset_Z0 hx)

/-- **Lemma II.7.2 (d)**: no cube of `𝕋_1` at index distance `≤ 3` from `Ω_1` lies in `P_1`. -/
theorem base_not_mem_P_of_near_Omega [NeZero S.L] [NeZero (n 1)] {c : Torus S.d (n 1)}
    (h : ∃ o ∈ (H.step 0).Omega, supDist c o ≤ 3) : c ∉ (H.step 0).P := by
  have hb := baseRecord_isStep H.baseRecord (n 0) (R (0 - 1))
  rw [H.baseRecord_toStep] at hb
  have := H.baseRecord.not_mem_P_of_near_Omega (c := c) (by rwa [← hb.2.2.2.2.2.2.2.2.1])
  rwa [← hb.2.2.2.2.1] at this

/-- **Lemma II.7.2 (d)**: two cubes of `𝕋_1` within distance `1` of each other, one in `P_1`, lie
in `Ω_1^c` and in one component of `Z^pre_1`. -/
theorem base_nbhd_comp [NeZero S.L] [NeZero (n 1)] {p p' : Torus S.d (n 1)}
    (hp : p ∈ (H.step 0).P) (hd : supDist p p' ≤ 1) :
    p ∈ (H.step 0).Omegaᶜ ∧ p' ∈ (H.step 0).Omegaᶜ ∧
      ∃ Z' : H.Comp 1, p ∈ Z'.1 ∧ p' ∈ Z'.1 := by
  obtain ⟨h1, h2⟩ := H.base_P_nbhd_compl
  have hpc : p ∈ (H.step 0).Omegaᶜ := h1 (subset_nbhd 3 _ hp)
  have hp'c : p' ∈ (H.step 0).Omegaᶜ :=
    h1 (mem_nbhd.mpr ⟨p, hp, by rw [supDist_comm]; omega⟩)
  have hω : 1 < S.omega 1 := by
    have := le_omegaW S.L S.Rb S.lam 1
    rw [S.omega_eq_omegaW]; omega
  obtain ⟨Y, hY, hpY, hp'Y⟩ := exists_comp_of_close (ω := S.omega 1)
    (X := H.Zp 1) (x := p) (y := p') (mem_finOf.mpr (h2 hpc)) (mem_finOf.mpr (h2 hp'c))
    (by omega)
  exact ⟨hpc, hp'c, ⟨Y, hY⟩, hpY, hp'Y⟩

/-- **Lemma II.7.2 (d)** for fine sites (`K ≥ 1`): a nearest-neighbour bond `(x, x + e_μ)` with an
end point in a cube of `P_1` has both end points in cubes of `Ω_1^c`, inside one component of
`Z^pre_1`. -/
theorem base_bond_comp [NeZero S.L] [NeZero (n 1)] {M K : ℕ} [NeZero M] (hK : 1 ≤ K)
    (x : Torus S.d (M * n K * S.L ^ K)) (μ : Fin S.d)
    (h : cubeMap n S.L M K 1 x ∈ (H.step 0).P ∨
      cubeMap n S.L M K 1 (x + Pi.single μ 1) ∈ (H.step 0).P) :
    cubeMap n S.L M K 1 x ∈ (H.step 0).Omegaᶜ ∧
      cubeMap n S.L M K 1 (x + Pi.single μ 1) ∈ (H.step 0).Omegaᶜ ∧
      ∃ Z' : H.Comp 1, cubeMap n S.L M K 1 x ∈ Z'.1 ∧
        cubeMap n S.L M K 1 (x + Pi.single μ 1) ∈ Z'.1 := by
  have hd := supDist_cubeMap_add_single_le (M := M) (K := K) H.F.hnn hK x μ
  rcases h with h | h
  · exact H.base_nbhd_comp h hd
  · obtain ⟨h1, h2, Z', h3, h4⟩ := H.base_nbhd_comp h (by rwa [supDist_comm])
    exact ⟨h2, h1, Z', h4, h3⟩

/-! ### (e) -/

variable (P : BudgetConsts)

/-- **Lemma II.7.2 (e)**, the exponents at `k = 0` (Definition II.5.11): for a component `Z'` of
`Z^pre_1`, `κ^{(0)}(Z') = A₃ (log β)^{2 p₀} |𝒩_1 ∩ Z'|_# - (c₁ log β + c₂) |Z'|_1` with
`|Z'|_1 = M^d · #Z'`, and `log C_1(Z') = (5/4) |Z'|_{#0}` with `|Z'|_{#0} = L^d · #Z'`. -/
theorem base_exponents (κ0 logC0 : H.Comp 0 → ℝ) (Z' : H.Comp 1) :
    H.kappaPre P 0 κ0 Z' =
      S.A3 * Real.log (P.beta 0) ^ (2 * S.p0) * ((Z'.1 ∩ H.newCubes 1).card : ℝ) -
        (P.c1 * Real.log (P.beta 0) + P.c2) * ((S.M : ℝ) ^ S.d * (Z'.1.card : ℝ)) ∧
    H.logCPre 0 logC0 Z' = 5 / 4 * ((S.L : ℝ) ^ S.d * (Z'.1.card : ℝ)) := by
  have hold : H.oldCubes 0 Z' = ∅ := by
    classical
    refine Finset.eq_empty_of_forall_notMem fun x hx => ?_
    simp only [oldCubes, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [H.step_zero_Z] at hx
    exact hx.1
  have hcnt := H.card_oldCubes_add_outCubes 0 Z'
  rw [hold, Finset.card_empty, zero_add] at hcnt
  have hcntR : ((H.outCubes 0 Z').card : ℝ) = (S.L : ℝ) ^ S.d * (Z'.1.card : ℝ) := by
    exact_mod_cast hcnt
  have hL : (0 : ℝ) < (S.L : ℝ) ^ S.d := H.F.ok.L_pow_pos
  have hpar := H.base_parts_empty Z'
  constructor
  · unfold kappaPre BudgetConsts.kappaStep
    rw [hpar, Finset.sum_empty, zero_add, hcntR]
    field_simp
  · unfold logCPre
    rw [hpar, Finset.sum_empty, zero_add, hold, Finset.card_empty, hcntR]
    simp

/-- **Lemma II.7.2 (e)** (the budget recursion (B) of LF-2 at `k = 0`; Lemma II.5.12 with no old
part): for every component `Z'` of `Z^pre_1`,
`G^pre_1(Z') = κ^{(0)}(Z') - log C_1(Z') - H_1 M^d #Z'` with `κ^{(0)}`, `log C_1` as in
`base_exponents`, and
`g_0 |𝒩_1 ∩ Z'|_# - c_v λ_1 |Z'|_# ≤ G^pre_1(Z')`. -/
theorem base_budget {P : BudgetConsts} (B : BudgetSetup S P) (ok : S.Ok)
    (κ logC : ∀ k, H.Comp k → ℝ) (Z' : H.Comp 1) :
    H.Gpre P κ logC 1 Z' =
      (S.A3 * Real.log (P.beta 0) ^ (2 * S.p0) * ((Z'.1 ∩ H.newCubes 1).card : ℝ) -
        (P.c1 * Real.log (P.beta 0) + P.c2) * ((S.M : ℝ) ^ S.d * (Z'.1.card : ℝ))) -
      5 / 4 * ((S.L : ℝ) ^ S.d * (Z'.1.card : ℝ)) -
      HRun P.H0 P.beta 1 * ((S.M : ℝ) ^ S.d * (Z'.1.card : ℝ)) ∧
    S.g 0 * ((Z'.1 ∩ H.newCubes 1).card : ℝ) - S.cv * S.lam 1 * (Z'.1.card : ℝ) ≤
      H.Gpre P κ logC 1 Z' := by
  obtain ⟨he1, he2⟩ := H.base_exponents (P := P) (κ 0) (logC 0) Z'
  refine ⟨?_, ?_⟩
  · show P.budgetG S 1 (H.kappaPre P 0 (κ 0) Z') (H.logCPre 0 (logC 0) Z') Z'.1.card = _
    unfold BudgetConsts.budgetG BudgetConsts.cubeVol
    rw [he1, he2]
  · have h := H.lemmaB B ok κ logC 1 0 (by omega) Z'
    rw [H.base_parts_empty Z', Finset.sum_empty, zero_add] at h
    exact h

end RegionHistory


end Balaban.LargeField
