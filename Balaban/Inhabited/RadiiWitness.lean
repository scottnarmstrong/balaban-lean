/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RadiiRipe
public import Balaban.Inhabited.RadiiSetting

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The ripe-regime witness with genuine radii

One parameter choice: `d = L = 3`, `M = 14 M₁`, `R_base = 32`, `β = RadiiSet.wβ`, `ν = 1/(β 27^T)`
(`T = RadiiHist.Tstar`), radii `R_j = R_base λ_j²` (`RadiiSet.wR`), so `Geo` (`RadiiSet.wGeo`) holds.
The region history is `RadiiHist.hist` (one created cube, one component with a ripe book at scale
`T`; side factor `bigN`), kept data `RadiiRipe.keptK`.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace RadiiWit

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness RadiiHist

instance : NeZero (14 * RadiiSet.M1) := ⟨by have := RadiiSet.M1_pos; omega⟩

theorem twelve_le_log : 12 ≤ Real.log (RadiiSet.wβ * (5 / 4)) + 1 :=
  RadiiRipe.twelve_le_anaThreshold.trans RadiiSet.wβ_spec.2.2

theorem setting_Cν_gt (β : ℝ) : 1 < (RadiiSet.setting β).Cν := by
  have hl : 0 < Real.log 3 := RadiiSet.log_three_pos
  have hcp : 0 < RadiiSet.typing0.cPrime := by
    show 0 < (1 + Real.log 3 / (1 * Real.log ((3 : ℕ) : ℝ))) * (1 + 3 * Real.log 3)
    have : ((3 : ℕ) : ℝ) = 3 := by norm_num
    rw [this]
    positivity
  show 1 < RadiiSet.typing0.Cr
  have h9 := pow_pos hcp 9
  show 1 < 2 * (1 : ℝ) * RadiiSet.typing0.cPrime ^ (9 : ℕ) + 1
  linarith

theorem setting_numax_two (β : ℝ) (hβ : 10 < β) (j : ℕ) : 2 ≤ (RadiiSet.setting β).numax j := by
  have hC := setting_Cν_gt β
  have hlam : 1 ≤ (RadiiSet.setting β).lam j := (RadiiSet.setting_ok β hβ).one_le_lam j
  have hp : (1 : ℝ) ≤ (RadiiSet.setting β).lam j ^ (RadiiSet.setting β).p2 := one_le_pow₀ hlam
  have : (1 : ℝ) < (RadiiSet.setting β).Cν * (RadiiSet.setting β).lam j ^ (RadiiSet.setting β).p2 := by
    nlinarith
  unfold Setting.numax
  have := Nat.lt_ceil.mpr (by exact_mod_cast this : ((1 : ℕ) : ℝ) <
    (RadiiSet.setting β).Cν * (RadiiSet.setting β).lam j ^ (RadiiSet.setting β).p2)
  omega

section Witness

/-- The common `β`. -/
noncomputable abbrev β0 : ℝ := RadiiSet.wβ

theorem hβ0 : 10 < β0 := RadiiSet.wβ_gt

/-- The setting. -/
noncomputable abbrev S0 : Setting := RadiiSet.wS

/-- The flow. -/
noncomputable abbrev F0 : FlowSeq := RadiiRipe.flow β0 hβ0

theorem F0_k0 : F0.k0 = RadiiHist.Tstar S0 := RadiiRipe.flow_k0 β0 hβ0

theorem T_le_kf : RadiiHist.Tstar S0 ≤ F0.kf := (RadiiRipe.flow_k0_lt_kf β0 hβ0).le

/-- The history of the ripe witness. -/
noncomputable abbrev H0 : RegionHistory S0 (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf)
    RadiiSet.wR F0.k0 F0.kf :=
  RadiiHist.hist (N := RadiiHist.bigN S0) (K := F0.kf) (k0 := F0.k0)
    (RadiiSet.wS_ok) le_rfl le_rfl
    RadiiSet.wRH

theorem H0_ripe_iff (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ F0.k0) (c : H0.Comp k) :
    S0.Ripe k (H0.bk k c) ↔ k = RadiiHist.Tstar S0 :=
  RadiiRipe.ripe_iff (RadiiSet.wS_ok) le_rfl le_rfl
    RadiiSet.wRH T_le_kf F0_k0 k h1 h2 c

/-- **The ripe-regime witness at `L = 3`**: all hypotheses of `flow_counter`, with `k₀ = T`
and a ripe component at scale `T` whose (Rg) inequality is solved by the kept data `RadiiRipe.keptK`. -/
noncomputable def radiiWitness : FlowCounterWitness :=
  let ok := RadiiSet.wS_ok
  let h4 : 4 ≤ S0.sS := le_rfl
  let h5 : 5 ≤ S0.sP := le_rfl
  let hRb := RadiiSet.wRH
  let P := RadiiSet.budgetConsts β0
  let B := RadiiSet.budgetSetup β0 (RadiiRipe.nuT β0) hβ0 (RadiiRipe.nuT_pos β0 hβ0) RadiiSet.wβ_spec.2.2
  { S := S0
    G := RadiiSet.wS_good
    F := F0
    hS := RadiiRipe.flow_matches β0 hβ0
    n := RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf
    R := RadiiSet.wR
    H := H0
    hadm := fun k c hc => absurd hc (by simp [H0, RadiiHist.hist])
    hkf := RadiiRipe.flow_one_le_kf β0 hβ0
    hΛ12 := RadiiRipe.flow_hΛ12 β0 hβ0 twelve_le_log
    hgen := RadiiRipe.flow_hgen β0 hβ0
    P := P
    B := B
    Gp := H0.budgetPre P (RadiiRipe.keptK H0 P) (fun _ _ => 0)
    G' := H0.budgetPost P (RadiiRipe.keptK H0 P) (fun _ _ => 0)
    budget := H0.lemmaB_recursive B ok (RadiiRipe.keptK H0 P) (fun _ _ => 0)
    rg_ripe := fun k h1 h2 c _ hr => by
      have hk : k = RadiiHist.Tstar S0 := (H0_ripe_iff k h1 h2 c).mp hr
      subst hk
      exact RadiiRipe.rg_kept H0 P c (RadiiRipe.kept_T ok h4 h5 hRb T_le_kf F0_k0 c)
        (fun m hm c' => RadiiRipe.not_kept_of_ne ok h4 h5 hRb T_le_kf F0_k0 (Nat.ne_of_lt hm) c')
        ok.CR_nonneg (le_trans zero_le_one (ok.one_le_lam _))
    rg_nonripe := fun k h1 h2 c _ hn =>
      RadiiRipe.budgetPost_eq_pre_of_not_kept H0 P _ _ c (fun h => hn h.2.2)
    rg_frozen := fun k hk c =>
      RadiiRipe.budgetPost_eq_pre_of_not_kept H0 P _ _ c (fun h => by have := h.2.1; omega) }

theorem radiiWitness_k0 : radiiWitness.F.k0 = RadiiHist.Tstar S0 := F0_k0

theorem radiiWitness_L : radiiWitness.S.L = 3 := rfl
theorem radiiWitness_M : radiiWitness.S.M = 14 * RadiiSet.M1 := rfl
theorem radiiWitness_d : radiiWitness.S.d = 3 := rfl

/-- `k₀ ≥ 1`, and `k₀ < k_f`. -/
theorem radiiWitness_k0_pos : 1 ≤ radiiWitness.F.k0 ∧ radiiWitness.F.k0 < radiiWitness.F.kf := by
  refine ⟨?_, ?_⟩
  · show 1 ≤ F0.k0
    rw [F0_k0]; exact RadiiHist.one_le_Tstar _
  · show F0.k0 < F0.kf
    rw [F0_k0]; exact RadiiRipe.flow_k0_lt_kf β0 hβ0

/-- **The ripe branch of (Rg) is non-vacuous**: the witness has a ripe component at a scale
`1 ≤ k ≤ k₀`, and exactly one scale (`k = T`) with ripe components. -/
theorem radiiWitness_ripe :
    ∃ (k : ℕ) (c : radiiWitness.H.Comp k), 1 ≤ k ∧ k ≤ radiiWitness.F.k0 ∧
      c.1 ∉ radiiWitness.H.rem k ∧ radiiWitness.S.Ripe k (radiiWitness.H.bk k c) := by
  obtain ⟨c, -, hrip⟩ := RadiiRipe.exists_ripe (RadiiSet.wS_ok) le_rfl
    le_rfl RadiiSet.wRH T_le_kf F0_k0 (N := RadiiHist.bigN S0)
  exact ⟨RadiiHist.Tstar S0, c, RadiiHist.one_le_Tstar _, F0_k0.symm.le,
    Finset.notMem_empty _, hrip⟩

/-- The kept event occurs: the kept data `RadiiRipe.keptK` enters at the ripe component, and the (Rg)
inequality is the budget gain `G_T = G^pre_T + A₃' λ_T^{p_R}`. -/
theorem radiiWitness_kept (c : radiiWitness.H.Comp (RadiiHist.Tstar S0)) :
    radiiWitness.H.IsKeptEvent (RadiiHist.Tstar S0) c :=
  RadiiRipe.kept_T (RadiiSet.wS_ok) le_rfl le_rfl
    RadiiSet.wRH T_le_kf F0_k0 c

theorem radiiWitness_counter :
    CounterConclusion
      ((radiiWitness.H.toLF2Hyp radiiWitness.hadm radiiWitness.Gp radiiWitness.G'
        radiiWitness.budget radiiWitness.rg_ripe radiiWitness.rg_nonripe
        radiiWitness.rg_frozen).toCounterHist radiiWitness.G.ok) radiiWitness.F.kfhat :=
  radiiWitness.counter

/-- **`RipeWindow`** for the ripe component of the history of `radiiWitness`. -/
theorem ripeWindow_rad :
    ∃ c : H0.Comp (RadiiHist.Tstar S0), H0.RipeWindow (RadiiHist.Tstar S0) c :=
  RadiiRipe.ripeWindow_exists' (RadiiSet.wS_ok) le_rfl
    le_rfl RadiiSet.wRH
    (RadiiSet.wS_good) T_le_kf F0_k0

/-- **`T4Facts`** for the merge at scale `T` of two parts with the ripe book of the witness
(`ν_max(T+1) ≥ 2` at `L = 3`). -/
theorem t4Facts_rad :
    ∃ (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts S0 (RadiiHist.Tstar S0) parts f b' :=
  RadiiRipe.t4Facts_exists' (RadiiSet.wS_ok) le_rfl
    le_rfl RadiiSet.wRH
    (RadiiSet.wS_good) T_le_kf F0_k0
    (setting_numax_two β0 hβ0 _)

/-- **`RemCluster`** for the ripe component of the history of the witness (`M = 14 M₁`, final scale
`T`); the kept configuration is empty. -/
theorem remCluster_rad :
    ∃ (Kc : HistConfig S0 (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) RadiiSet.wR F0.k0
        F0.kf (14 * RadiiSet.M1) (RadiiHist.Tstar S0))
      (C : Finset (ConfigPair S0 (RadiiHist.side S0 (RadiiHist.bigN S0) F0.kf) (14 * RadiiSet.M1) F0.kf
        (RadiiHist.Tstar S0))), RemCluster Kc C :=
  RadiiRipe.remCluster_exists (RadiiSet.wS_ok) le_rfl
    le_rfl RadiiSet.wRH T_le_kf F0_k0 (14 * RadiiSet.M1)


end Witness

end RadiiWit
end Balaban.Inhabited
