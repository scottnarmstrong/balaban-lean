/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.JointL4Setting
public import Balaban.Inhabited.RipeHistory
public import Balaban.Inhabited.Numerics
public import Balaban.Background.ExistenceSetup

/-!
# A joint witness with `L = 4` and a non-empty region history

The parameters of `JointL4Setting` (`d = 3`, `L = M = 4`) together with the region history of
`RipeHistory` (one large-field cube created at `0 → 1`, one component `Z_k` at every
`1 ≤ k ≤ k_f`), `k_f = F.kf`, `k_0 = F.k0 = 0` (as `β ν > 1`).  The budget data are
`G^pre = budgetPre`, `G = budgetPost` of Definition II.5.11 with vanishing kept data, for which
`lemmaB_recursive` gives the budget inequality; (Rg) is vacuous for `k_0 = 0` and `G = G^pre` for
`k > k_0`.  `jointWitnessL4 : FlowCounterWitness` packages all hypotheses of
`RegionHistory.flow_counter`; the history has a component at every scale `1 ≤ k ≤ k_f`.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace JointL4

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness

/-- For `k > k₀` the kept event does not occur, so `G_k = G^pre_k`. -/
theorem budgetPost_eq_pre {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) (κK δ : ∀ k, H.Comp k → ℝ) {k : ℕ}
    (hk : k0 < k) (c : H.Comp k) : H.budgetPost P κK δ k c = H.budgetPre P κK δ k c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hn : ¬ H.IsKeptEvent (j + 1) c := fun h => by
    have := h.2.1; omega
  simp [RegionHistory.budgetPost, RegionHistory.budgetPre, RegionHistory.Gpost,
    RegionHistory.Gpre, RegionHistory.kappa, RegionHistory.logC, hn, RegionHistory.kappaPre,
    RegionHistory.logCPre]

section Witness

variable (β : ℝ) (hβ : 20 < β)

/-- The history: `RipeHist.hist` at `N = 1`, `K = k_f`, `k₀ = F.k0`. -/
noncomputable def hist :
    RegionHistory (setting β) (RipeHist.side (setting β) 1 (flow β hβ).kf)
      JointWitness.radii (flow β hβ).k0 (flow β hβ).kf :=
  RipeHist.hist (N := 1) (K := (flow β hβ).kf) (k0 := (flow β hβ).k0)
    (setting_ok β hβ) (setting_s4 β) (setting_s5 β) (setting_Rb β)

theorem hist_nonempty_comp (k : ℕ) (hk : 1 ≤ k) (hkf : k ≤ (flow β hβ).kf) :
    Nonempty ((hist β hβ).Comp k) := by
  obtain ⟨c, -⟩ := RipeHist.comp_unique (N := 1) (K := (flow β hβ).kf) (k0 := (flow β hβ).k0)
    (setting_ok β hβ) (setting_s4 β) (setting_s5 β) (setting_Rb β) k hk hkf
  exact ⟨c⟩

/-- The component at a scale `k ≥ 1` contains the created cube. -/
theorem hist_comp_one_card_pos (c : (hist β hβ).Comp 1) :
    0 < c.1.card :=
  Finset.card_pos.mpr ⟨0, RipeHist.zero_mem_comp_one (N := 1) (K := (flow β hβ).kf)
    (k0 := (flow β hβ).k0) (setting_ok β hβ) (setting_s4 β) (setting_s5 β) (setting_Rb β) c
    (flow_one_le_kf β hβ)⟩

end Witness

/-- **The joint witness with `L = 4`**: all hypotheses of `flow_counter` (and of `lemmaB`)
for a non-empty region history. -/
noncomputable def jointWitnessL4 : FlowCounterWitness :=
  let β := jointBeta
  let hβ : 20 < β := jointBeta_gt
  let ok := setting_ok β hβ
  let F := flow β hβ
  let H := hist β hβ
  let B := budgetSetup β hβ jointBeta_spec.2.2.1
  have hk0 : F.k0 = 0 := flow_k0 β hβ
  { S := setting β
    G := setting_good β hβ jointBeta_spec.2.1
    F := F
    hS := flow_matches β hβ
    n := RipeHist.side (setting β) 1 F.kf
    R := JointWitness.radii
    H := H
    hadm := fun k c hc => absurd hc (by simp [H, hist, RipeHist.hist])
    hkf := flow_one_le_kf β hβ
    hΛ12 := flow_hΛ12 β hβ jointBeta_spec.2.2.2
    hgen := flow_hgen β hβ
    P := budgetConsts β
    B := B
    Gp := H.budgetPre (budgetConsts β) (fun _ _ => 0) (fun _ _ => 0)
    G' := H.budgetPost (budgetConsts β) (fun _ _ => 0) (fun _ _ => 0)
    budget := H.lemmaB_recursive B ok (fun _ _ => 0) (fun _ _ => 0)
    rg_ripe := fun k h1 h2 _ => by omega
    rg_nonripe := fun k h1 h2 _ => by omega
    rg_frozen := fun k hk c => (budgetPost_eq_pre H _ _ _ hk c) }

theorem nonempty_jointWitnessL4 : Nonempty FlowCounterWitness := ⟨jointWitnessL4⟩

theorem jointWitnessL4_L : jointWitnessL4.S.L = 4 := rfl
theorem jointWitnessL4_d : jointWitnessL4.S.d = 3 := rfl

/-- The history of the witness has a component at every scale `1 ≤ k ≤ k_f` (so the conclusion of
`flow_counter` is not about an empty history). -/
theorem jointWitnessL4_comp (k : ℕ) (hk : 1 ≤ k) (hkf : k ≤ jointWitnessL4.F.kf) :
    Nonempty (jointWitnessL4.H.Comp k) :=
  hist_nonempty_comp jointBeta jointBeta_gt k hk hkf

theorem jointWitnessL4_comp_one : Nonempty (jointWitnessL4.H.Comp 1) :=
  jointWitnessL4_comp 1 le_rfl (flow_one_le_kf jointBeta jointBeta_gt)

/-- The component at scale `1` is non-empty as a set of cubes. -/
theorem jointWitnessL4_comp_card_pos (c : jointWitnessL4.H.Comp 1) : 0 < c.1.card :=
  hist_comp_one_card_pos jointBeta jointBeta_gt c

/-- Hypotheses of `flow_counter` are jointly satisfiable with a non-empty history, hence its
conclusion applies. -/
theorem jointWitnessL4_counter :
    CounterConclusion
      ((jointWitnessL4.H.toLF2Hyp jointWitnessL4.hadm jointWitnessL4.Gp jointWitnessL4.G'
        jointWitnessL4.budget jointWitnessL4.rg_ripe jointWitnessL4.rg_nonripe
        jointWitnessL4.rg_frozen).toCounterHist jointWitnessL4.G.ok) jointWitnessL4.F.kfhat :=
  jointWitnessL4.counter

theorem jointWitnessL4_lemmaB (κ logC : ∀ k, jointWitnessL4.H.Comp k → ℝ) :
    ∀ k, k < jointWitnessL4.F.kf → ∀ Z' : jointWitnessL4.H.Comp (k + 1),
      ∑ c ∈ jointWitnessL4.H.parts k Z', jointWitnessL4.H.Gpost jointWitnessL4.P κ logC k c +
          jointWitnessL4.S.g k * (Z'.1 ∩ jointWitnessL4.H.newCubes (k + 1)).card -
        jointWitnessL4.S.cv * jointWitnessL4.S.lam (k + 1) * Z'.1.card ≤
          jointWitnessL4.H.Gpre jointWitnessL4.P κ logC (k + 1) Z' :=
  jointWitnessL4.lemmaB κ logC

/-! ### The remaining constraints at the same parameters -/

theorem bgHyp_jointL4 (k : ℕ) :
    Balaban.Background.BgHyp 3 4 k (Balaban.Background.bgR0 3 4) (fun _ => 1) 0 where
  hd := le_rfl
  hL := by norm_num
  hϱ := le_rfl
  weights := fun j _ _ => ⟨by norm_num, by norm_num⟩
  mass := le_rfl
  massLe := by simp

/-- `BgHyp` at the flow's mass `ν = 1/20` at scale `k = 0`. -/
theorem bgHyp_jointL4_flow :
    Balaban.Background.BgHyp 3 4 0 (Balaban.Background.bgR0 3 4) (fun _ => 1) (1 / 20) where
  hd := le_rfl
  hL := by norm_num
  hϱ := le_rfl
  weights := fun j h1 h2 => by omega
  mass := by norm_num
  massLe := by norm_num

/-- **All constraints at the one parameter choice** `d = 3`, `L = M = 4`: `Setting.Good`,
`BudgetSetup` (with its `RunningHyp`), `BgHyp`, `IsAdmDelta`, `RadiusHyp`, `StepRadii`, and the
non-empty history of `jointWitnessL4`. -/
theorem jointL4_constraints :
    jointWitnessL4.S.L = 4 ∧ jointWitnessL4.S.M = 4 ∧ jointWitnessL4.S.d = 3 ∧
    Nonempty jointWitnessL4.S.Good ∧
    (∀ k, Balaban.Background.BgHyp 3 4 k (Balaban.Background.bgR0 3 4) (fun _ => 1) 0) ∧
    (∀ ε : ℝ, 0 ≤ ε → ∀ k1 k : ℕ, IsAdmDelta 3 4 ε k1 k (fun i => (1 / 2 : ℝ) ^ i)) ∧
    RadiusHyp 4 jointWitnessL4.S.Rb jointWitnessL4.S.lam JointWitness.radii ∧
    (∃ ω r : ℕ, StepRadii 4 ω r (4 * 4 + 20 : ℝ) (4 * 4 + 20 : ℝ)) ∧
    Nonempty (RunningHyp 3 4 jointWitnessL4.B.β jointWitnessL4.B.ν jointWitnessL4.B.a
      jointWitnessL4.B.ε jointWitnessL4.P.beta jointWitnessL4.B.nuRun) ∧
    (∀ k, 1 ≤ k → k ≤ jointWitnessL4.F.kf → Nonempty (jointWitnessL4.H.Comp k)) := by
  refine ⟨rfl, rfl, rfl, ⟨jointWitnessL4.G⟩, bgHyp_jointL4, ?_, ?_, ?_, ⟨jointWitnessL4.B.run⟩,
    fun k h1 h2 => jointWitnessL4_comp k h1 h2⟩
  · intro ε hε k1 k
    exact isAdmDelta_nonempty (by norm_num) (by norm_num) hε k1 k
  · exact JointWitness.radiusHyp _ jointWitnessL4.G.ok (setting_Rb _)
  · have := stepRadii_nonempty (L := 4) (by norm_num)
    simpa using this

end JointL4
end Balaban.Inhabited
