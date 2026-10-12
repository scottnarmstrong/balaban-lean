/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RipeL4

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The ripe-regime witness at `L = 4`

One parameter choice: `d = 3`, `L = M = 4`, `β = JointL4.jointBeta`, `ν = 1/(β 64^T)`
(`T = RipeHist.Tstar`), so `k₀ = T ≥ 1` and `T < k_f`; the history `RipeHist.hist` with side factor
`bigN` (one created cube, a single component with a ripe book at scale `T`); kept data
`RipeL4.keptK`.

* `ripeWitnessL4 : FlowCounterWitness` — all hypotheses of `flow_counter`, the ripe branch of (Rg)
  being non-vacuous (`ripeWitnessL4_ripe`: the component at `T` is ripe with `1 ≤ T ≤ k₀`);
* `ripeWindow_L4`, `t4Facts_L4`, `remCluster_L4` for the same history.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace RipeL4

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness

theorem setting_Cν_gt (β : ℝ) : 1 < (JointL4.setting β).Cν := by
  have hl : 0 < Real.log 4 := JointL4.log_four_pos
  have hcp : 0 < JointL4.typing0.cPrime := by
    show 0 < (1 + Real.log 4 / (1 * Real.log ((4 : ℕ) : ℝ))) * (1 + 3 * Real.log 4)
    have : ((4 : ℕ) : ℝ) = 4 := by norm_num
    rw [this]
    positivity
  show 1 < JointL4.typing0.Cr
  have h9 := pow_pos hcp 9
  show 1 < 2 * (1 : ℝ) * JointL4.typing0.cPrime ^ (9 : ℕ) + 1
  linarith

theorem setting_numax_two (β : ℝ) (hβ : 20 < β) (j : ℕ) : 2 ≤ (JointL4.setting β).numax j := by
  have hC := setting_Cν_gt β
  have hlam : 1 ≤ (JointL4.setting β).lam j := (JointL4.setting_ok β hβ).one_le_lam j
  have hp : (1 : ℝ) ≤ (JointL4.setting β).lam j ^ (JointL4.setting β).p2 := one_le_pow₀ hlam
  have : (1 : ℝ) < (JointL4.setting β).Cν * (JointL4.setting β).lam j ^ (JointL4.setting β).p2 := by
    nlinarith
  unfold Setting.numax
  have := Nat.lt_ceil.mpr (by exact_mod_cast this : ((1 : ℕ) : ℝ) <
    (JointL4.setting β).Cν * (JointL4.setting β).lam j ^ (JointL4.setting β).p2)
  omega

section Witness

/-- The common `β`. -/
noncomputable abbrev β0 : ℝ := JointL4.jointBeta

theorem hβ0 : 20 < β0 := JointL4.jointBeta_gt

/-- The setting. -/
noncomputable abbrev S0 : Setting := JointL4.setting β0

/-- The flow. -/
noncomputable abbrev F0 : FlowSeq := flow β0 hβ0

theorem F0_k0 : F0.k0 = RipeHist.Tstar S0 := flow_k0 β0 hβ0

theorem T_le_kf : RipeHist.Tstar S0 ≤ F0.kf := (flow_k0_lt_kf β0 hβ0).le

/-- The history of the ripe witness. -/
noncomputable abbrev H0 : RegionHistory S0 (RipeHist.side S0 (RipeHist.bigN S0) F0.kf)
    JointWitness.radii F0.k0 F0.kf :=
  RipeHist.hist (N := RipeHist.bigN S0) (K := F0.kf) (k0 := F0.k0)
    (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0) (JointL4.setting_s5 β0)
    (JointL4.setting_Rb β0)

theorem H0_ripe_iff (k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ F0.k0) (c : H0.Comp k) :
    S0.Ripe k (H0.bk k c) ↔ k = RipeHist.Tstar S0 :=
  ripe_iff (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0) (JointL4.setting_s5 β0)
    (JointL4.setting_Rb β0) T_le_kf F0_k0 k h1 h2 c

/-- **The ripe-regime witness at `L = 4`**: all hypotheses of `flow_counter`, with `k₀ = T`
and a ripe component at scale `T` whose (Rg) inequality is solved by the kept data `keptK`. -/
noncomputable def ripeWitnessL4 : FlowCounterWitness :=
  let ok := JointL4.setting_ok β0 hβ0
  let h4 := JointL4.setting_s4 β0
  let h5 := JointL4.setting_s5 β0
  let hRb := JointL4.setting_Rb β0
  let P := JointL4.budgetConsts β0
  let B := budgetSetup β0 hβ0 JointL4.jointBeta_spec.2.2.1
  { S := S0
    G := JointL4.setting_good β0 hβ0 JointL4.jointBeta_spec.2.1
    F := F0
    hS := flow_matches β0 hβ0
    n := RipeHist.side S0 (RipeHist.bigN S0) F0.kf
    R := JointWitness.radii
    H := H0
    hadm := fun k c hc => absurd hc (by simp [H0, RipeHist.hist])
    hkf := flow_one_le_kf β0 hβ0
    hΛ12 := flow_hΛ12 β0 hβ0 JointL4.jointBeta_spec.2.2.2
    hgen := flow_hgen β0 hβ0
    P := P
    B := B
    Gp := H0.budgetPre P (keptK H0 P) (fun _ _ => 0)
    G' := H0.budgetPost P (keptK H0 P) (fun _ _ => 0)
    budget := H0.lemmaB_recursive B ok (keptK H0 P) (fun _ _ => 0)
    rg_ripe := fun k h1 h2 c _ hr => by
      have hk : k = RipeHist.Tstar S0 := (H0_ripe_iff k h1 h2 c).mp hr
      subst hk
      exact rg_kept H0 P c (kept_T ok h4 h5 hRb T_le_kf F0_k0 c)
        (fun m hm c' => not_kept_of_ne ok h4 h5 hRb T_le_kf F0_k0 (Nat.ne_of_lt hm) c')
        ok.CR_nonneg (le_trans zero_le_one (ok.one_le_lam _))
    rg_nonripe := fun k h1 h2 c _ hn =>
      budgetPost_eq_pre_of_not_kept H0 P _ _ c (fun h => hn h.2.2)
    rg_frozen := fun k hk c =>
      budgetPost_eq_pre_of_not_kept H0 P _ _ c (fun h => by have := h.2.1; omega) }

theorem ripeWitnessL4_k0 : ripeWitnessL4.F.k0 = RipeHist.Tstar S0 := F0_k0

theorem ripeWitnessL4_L : ripeWitnessL4.S.L = 4 := rfl
theorem ripeWitnessL4_M : ripeWitnessL4.S.M = 4 := rfl
theorem ripeWitnessL4_d : ripeWitnessL4.S.d = 3 := rfl

/-- `k₀ ≥ 1`, and `k₀ < k_f`. -/
theorem ripeWitnessL4_k0_pos : 1 ≤ ripeWitnessL4.F.k0 ∧ ripeWitnessL4.F.k0 < ripeWitnessL4.F.kf := by
  refine ⟨?_, ?_⟩
  · show 1 ≤ F0.k0
    rw [F0_k0]; exact RipeHist.one_le_Tstar _
  · show F0.k0 < F0.kf
    rw [F0_k0]; exact flow_k0_lt_kf β0 hβ0

/-- **The ripe branch of (Rg) is non-vacuous**: the witness has a ripe component at a scale
`1 ≤ k ≤ k₀`, and exactly one scale (`k = T`) with ripe components. -/
theorem ripeWitnessL4_ripe :
    ∃ (k : ℕ) (c : ripeWitnessL4.H.Comp k), 1 ≤ k ∧ k ≤ ripeWitnessL4.F.k0 ∧
      c.1 ∉ ripeWitnessL4.H.rem k ∧ ripeWitnessL4.S.Ripe k (ripeWitnessL4.H.bk k c) := by
  obtain ⟨c, -, hrip⟩ := exists_ripe (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0)
    (JointL4.setting_s5 β0) (JointL4.setting_Rb β0) T_le_kf F0_k0 (N := RipeHist.bigN S0)
  exact ⟨RipeHist.Tstar S0, c, RipeHist.one_le_Tstar _, F0_k0.symm.le,
    Finset.notMem_empty _, hrip⟩

/-- The kept event occurs: the kept data `keptK` enters at the ripe component, and the (Rg)
inequality is the budget gain `G_T = G^pre_T + A₃' λ_T^{p_R}`. -/
theorem ripeWitnessL4_kept (c : ripeWitnessL4.H.Comp (RipeHist.Tstar S0)) :
    ripeWitnessL4.H.IsKeptEvent (RipeHist.Tstar S0) c :=
  kept_T (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0) (JointL4.setting_s5 β0)
    (JointL4.setting_Rb β0) T_le_kf F0_k0 c

theorem ripeWitnessL4_counter :
    CounterConclusion
      ((ripeWitnessL4.H.toLF2Hyp ripeWitnessL4.hadm ripeWitnessL4.Gp ripeWitnessL4.G'
        ripeWitnessL4.budget ripeWitnessL4.rg_ripe ripeWitnessL4.rg_nonripe
        ripeWitnessL4.rg_frozen).toCounterHist ripeWitnessL4.G.ok) ripeWitnessL4.F.kfhat :=
  ripeWitnessL4.counter

/-- **`RipeWindow`** for the ripe component of the history of `ripeWitnessL4`. -/
theorem ripeWindow_L4 :
    ∃ c : H0.Comp (RipeHist.Tstar S0), H0.RipeWindow (RipeHist.Tstar S0) c :=
  ripeWindow_exists' (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0)
    (JointL4.setting_s5 β0) (JointL4.setting_Rb β0)
    (JointL4.setting_good β0 hβ0 JointL4.jointBeta_spec.2.1) T_le_kf F0_k0

/-- **`T4Facts`** for the merge at scale `T` of two parts with the ripe book of the witness
(`ν_max(T+1) ≥ 2` at `L = 4`). -/
theorem t4Facts_L4 :
    ∃ (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts S0 (RipeHist.Tstar S0) parts f b' :=
  t4Facts_exists' (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0)
    (JointL4.setting_s5 β0) (JointL4.setting_Rb β0)
    (JointL4.setting_good β0 hβ0 JointL4.jointBeta_spec.2.1) T_le_kf F0_k0
    (setting_numax_two β0 hβ0 _)

/-- **`RemCluster`** for the ripe component of the history of the witness (`M = 4`, final scale
`T`); the kept configuration is empty. -/
theorem remCluster_L4 :
    ∃ (Kc : HistConfig S0 (RipeHist.side S0 (RipeHist.bigN S0) F0.kf) JointWitness.radii F0.k0
        F0.kf 4 (RipeHist.Tstar S0))
      (C : Finset (ConfigPair S0 (RipeHist.side S0 (RipeHist.bigN S0) F0.kf) 4 F0.kf
        (RipeHist.Tstar S0))), RemCluster Kc C :=
  remCluster_exists (JointL4.setting_ok β0 hβ0) (JointL4.setting_s4 β0)
    (JointL4.setting_s5 β0) (JointL4.setting_Rb β0) T_le_kf F0_k0 4

/-- `BgHyp` at the flow's mass `ν = 1/(β 64^T)` for every scale `k ≤ k₀`. -/
theorem bgHyp_ripeL4 (k : ℕ) (hk : k ≤ RipeHist.Tstar S0) :
    Balaban.Background.BgHyp 3 4 k (Balaban.Background.bgR0 3 4) (fun _ => 1) (nuT β0) where
  hd := le_rfl
  hL := by norm_num
  hϱ := le_rfl
  weights := fun j _ _ => ⟨by norm_num, by norm_num⟩
  mass := (nuT_pos β0 hβ0).le
  massLe := by
    have hβ := hβ0
    have h1 : ((4 : ℝ) ^ k) ^ 2 ≤ 64 ^ RipeHist.Tstar S0 := by
      rw [show ((4 : ℝ) ^ k) ^ 2 = 16 ^ k by rw [← pow_mul, mul_comm, pow_mul]; norm_num]
      calc (16 : ℝ) ^ k ≤ 64 ^ k := pow_le_pow_left₀ (by norm_num) (by norm_num) k
        _ ≤ 64 ^ RipeHist.Tstar S0 := pow_le_pow_right₀ (by norm_num) hk
    have h2 : (0 : ℝ) < 64 ^ RipeHist.Tstar S0 := by positivity
    show nuT β0 * (((4 : ℕ) : ℝ) ^ k) ^ 2 ≤ 1
    have h3 : nuT β0 = 1 / (β0 * 64 ^ RipeHist.Tstar S0) := rfl
    rw [h3, Nat.cast_ofNat, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith

/-- **All constraints at the one parameter choice** `d = 3`, `L = M = 4`, `ν = 1/(β 64^T)`:
`Setting.Good`, the budget setup with its `RunningHyp`, `BgHyp` at the flow's mass for all scales
`k ≤ k₀`, `IsAdmDelta`, `RadiusHyp`, `StepRadii`, `k₀ ≥ 1` and a ripe component at `k₀`. -/
theorem ripeL4_constraints :
    ripeWitnessL4.S.L = 4 ∧ ripeWitnessL4.S.M = 4 ∧ ripeWitnessL4.S.d = 3 ∧
    Nonempty ripeWitnessL4.S.Good ∧
    (∀ k, k ≤ ripeWitnessL4.F.k0 →
      Balaban.Background.BgHyp 3 4 k (Balaban.Background.bgR0 3 4) (fun _ => 1) ripeWitnessL4.F.ν) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ k1 k : ℕ, IsAdmDelta 3 4 ε k1 k (fun i => (1 / 2 : ℝ) ^ i)) ∧
    RadiusHyp 4 ripeWitnessL4.S.Rb ripeWitnessL4.S.lam JointWitness.radii ∧
    (∃ ω r : ℕ, StepRadii 4 ω r (4 * 4 + 20 : ℝ) (4 * 4 + 20 : ℝ)) ∧
    Nonempty (RunningHyp 3 4 ripeWitnessL4.B.β ripeWitnessL4.B.ν ripeWitnessL4.B.a
      ripeWitnessL4.B.ε ripeWitnessL4.P.beta ripeWitnessL4.B.nuRun) ∧
    1 ≤ ripeWitnessL4.F.k0 ∧
    (∃ (k : ℕ) (c : ripeWitnessL4.H.Comp k), 1 ≤ k ∧ k ≤ ripeWitnessL4.F.k0 ∧
      ripeWitnessL4.S.Ripe k (ripeWitnessL4.H.bk k c)) := by
  refine ⟨rfl, rfl, rfl, ⟨ripeWitnessL4.G⟩, ?_, ?_, ?_, ?_, ⟨ripeWitnessL4.B.run⟩,
    ripeWitnessL4_k0_pos.1, ?_⟩
  · intro k hk
    exact bgHyp_ripeL4 k (by rw [← F0_k0]; exact hk)
  · intro ε hε k1 k
    exact isAdmDelta_nonempty (by norm_num) (by norm_num) hε k1 k
  · exact JointWitness.radiusHyp _ ripeWitnessL4.G.ok (JointL4.setting_Rb _)
  · have := stepRadii_nonempty (L := 4) (by norm_num)
    simpa using this
  · obtain ⟨k, c, h1, h2, -, h3⟩ := ripeWitnessL4_ripe
    exact ⟨k, c, h1, h2, h3⟩

end Witness

end RipeL4
end Balaban.Inhabited
