/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RadiiHist
public import Balaban.Inhabited.RadiiSetting
public import Balaban.LargeField.Counter.FlowHorizon
public import Balaban.Inhabited.JointL4Setting

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The `L = 3` flow with `k₀ = T` (ripe regime) and the ripe history with arbitrary radii

On the Def-7 witness setting (`d = L = 3`, `M = 27`, `R_base = 32`; `RadiiSet.setting β`) let
`T = t^*(Active(1,1,∅), s = 1)`.  The flow has `β_k = β 3^k`, `ν_k = ν 9^k` with the mass
`ν = 1 / (β 27^T)`, so that `β_k ν_k = 27^(k-T)`: the regime index is `k₀ = T ≥ 1`, and
`k₀ < k_f`.  The second half transports the ripeness facts of `RadiiHist` (the history of
arbitrary radii satisfying (RH)) to this regime: kept data, (Rg) at the ripe component,
`RemCluster`, `RipeWindow`, `T4Facts`.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace RadiiRipe

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness RadiiHist

theorem log_three_gt : 1 < Real.log 3 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- The analytic threshold is at least `12`. -/
theorem twelve_le_anaThreshold : 12 ≤ JointWitness.anaThreshold := by
  refine le_trans ?_ (le_max_left _ _)
  have hx : (3 / 4 : ℝ) ≤ (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) := by
    have h1 : ((3 / 4 : ℝ) ^ (10 : ℕ)) ≤ (1 / 2 : ℝ) := by norm_num
    have h2 : ((3 / 4 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 / 10 : ℝ) :=
      Real.rpow_le_rpow (by positivity) h1 (by norm_num)
    have h3 : ((3 / 4 : ℝ) ^ (10 : ℕ)) ^ (1 / 10 : ℝ) = 3 / 4 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
    have h4 : (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) = (1 / 2 : ℝ) ^ (1 / 10 : ℝ) := by
      rw [Real.rpow_neg (by norm_num), one_div (2 : ℝ), Real.inv_rpow (by norm_num)]
      norm_num
    rw [h4]; linarith
  have hpos : 0 < 1 - (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) := by
    have : (2 : ℝ) ^ (-(1 / (2 * (5 : ℝ)))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    linarith
  rw [le_div_iff₀ hpos]
  linarith

/-- The ripeness time of the book `Active(1,1,∅)`, clock `1`, for `RadiiSet.setting β`. -/
noncomputable def T (β : ℝ) : ℕ := RadiiHist.Tstar (RadiiSet.setting β)

theorem one_le_T (β : ℝ) : 1 ≤ T β := RadiiHist.one_le_Tstar _

/-- The mass `ν = 1 / (β 27^T)`. -/
noncomputable def nuT (β : ℝ) : ℝ := 1 / (β * 27 ^ T β)

theorem nuT_pos (β : ℝ) (hβ : 10 < β) : 0 < nuT β := by
  unfold nuT; have : 0 < β := by linarith
  positivity

theorem beta_mul_nuT (β : ℝ) (hβ : 10 < β) : β * nuT β = 1 / 27 ^ T β := by
  unfold nuT
  have : β ≠ 0 := by linarith
  field_simp

theorem nuT_le (β : ℝ) (hβ : 10 < β) : nuT β ≤ 1 / 270 := by
  unfold nuT
  have h1 : (27 : ℝ) ≤ 27 ^ T β := by
    calc (27 : ℝ) = 27 ^ 1 := by norm_num
      _ ≤ 27 ^ T β := pow_le_pow_right₀ (by norm_num) (one_le_T β)
  rw [div_le_div_iff₀ (by have : 0 < β := by linarith
                          positivity) (by norm_num)]
  nlinarith

/-- The flow data: `ν = 1/(β 27^T)`. -/
noncomputable def flow (β : ℝ) (hβ : 10 < β) : FlowSeq where
  d := 3
  L := 3
  β := β
  ν := nuT β
  a := 5 / 4
  γ := fun _ => 1
  δ := fun _ => 1
  hd := le_rfl
  hL := by norm_num
  hβ := by linarith
  hν0 := nuT_pos β hβ
  hν1 := (nuT_le β hβ).trans (by norm_num)
  ha1 := by norm_num
  ha2 := by norm_num
  hγ := fun _ => by norm_num
  hδ := fun _ => by norm_num
  hγ0 := rfl
  hδ0 := rfl

theorem flow_matches (β : ℝ) (hβ : 10 < β) : (flow β hβ).Matches (RadiiSet.setting β) where
  d_eq := rfl
  L_eq := rfl
  lam_eq := fun j => by
    rw [RadiiSet.setting_lam]
    simp [FlowSeq.lamHat, flow, FlowSeq.e]
  cH_eq := by
    show 3 * Real.log 3 = ((3 : ℕ) + 3 : ℝ) * (((3 : ℕ) - 2 : ℕ) : ℝ) / 2 * Real.log ((3 : ℕ) : ℝ)
    norm_num

theorem flow_e (β : ℝ) (hβ : 10 < β) : (flow β hβ).e = 1 := rfl

theorem flow_beta (β : ℝ) (hβ : 10 < β) (k : ℕ) : (flow β hβ).beta k = β * 3 ^ k := by
  unfold FlowSeq.beta; rw [flow_e]; simp [flow]

theorem flow_nu (β : ℝ) (hβ : 10 < β) (k : ℕ) : (flow β hβ).nu k = nuT β * 9 ^ k := by
  unfold FlowSeq.nu
  simp only [flow, pow_mul, mul_one]
  norm_num

theorem flow_betanu (β : ℝ) (hβ : 10 < β) (k : ℕ) :
    (flow β hβ).beta k * (flow β hβ).nu k = 27 ^ k / 27 ^ T β := by
  rw [flow_beta, flow_nu]
  have h : β * 3 ^ k * (nuT β * 9 ^ k) = (β * nuT β) * (3 ^ k * 9 ^ k) := by ring
  rw [h, beta_mul_nuT β hβ, ← mul_pow]
  norm_num
  ring

/-- The regime index is exactly `T`. -/
theorem flow_k0 (β : ℝ) (hβ : 10 < β) : (flow β hβ).k0 = T β := by
  have hpos : (0 : ℝ) < 27 ^ T β := by positivity
  rcases (flow β hβ).k0_cases with ⟨h1, h2⟩ | ⟨h1, -⟩
  · rw [flow_betanu, div_le_one hpos] at h1
    rw [flow_betanu, one_lt_div hpos] at h2
    have a1 := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 27)).mp h1
    have a2 := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℝ) < 27)).mp h2
    omega
  · exfalso
    have h1' : 1 < β * nuT β := h1
    rw [beta_mul_nuT β hβ] at h1'
    have h3 : 1 / (27 : ℝ) ^ T β ≤ 1 := by
      rw [div_le_one hpos]; exact one_le_pow₀ (by norm_num)
    linarith

theorem flow_one_le_kf (β : ℝ) (hβ : 10 < β) : 1 ≤ (flow β hβ).kf := by
  by_contra h
  have h0 : (flow β hβ).kf = 0 := by omega
  have hk := (flow β hβ).kf_spec
  rw [h0] at hk
  have : (flow β hβ).nu 0 = nuT β := by rw [flow_nu]; simp
  rw [this] at hk
  have h2 : ((flow β hβ).L : ℝ) = 3 := by simp [flow]
  rw [h2] at hk
  have := nuT_le β hβ
  norm_num at hk
  linarith

theorem flow_hgen (β : ℝ) (hβ : 10 < β) :
    (flow β hβ).beta (flow β hβ).k0 * (flow β hβ).nu (flow β hβ).k0 ≤ 1 →
      2 * ((flow β hβ).L : ℝ) ^ 2 ≤ (flow β hβ).beta (flow β hβ).k0 := by
  intro _
  rw [flow_k0]
  have h1 : (3 : ℝ) ≤ 3 ^ T β := by
    calc (3 : ℝ) = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ T β := pow_le_pow_right₀ (by norm_num) (one_le_T β)
  have h2 : (flow β hβ).beta (T β) = β * 3 ^ T β := flow_beta β hβ _
  have h3 : ((flow β hβ).L : ℝ) = 3 := by simp [flow]
  rw [h2, h3]
  nlinarith

theorem flow_k0_lt_kf (β : ℝ) (hβ : 10 < β) : T β < (flow β hβ).kf := by
  have := (flow β hβ).k0_lt_kf (flow_one_le_kf β hβ) (flow_hgen β hβ)
  rwa [flow_k0] at this

theorem flow_hΛ12 (β : ℝ) (hβ : 10 < β) (h12 : 12 ≤ Real.log (β * (5 / 4)) + 1) :
    (((flow β hβ).d : ℝ) + 3) / 2 ≤
      (RadiiSet.setting β).lam (flow β hβ).k0 * (1 - 1 / (2 * Real.log (flow β hβ).L)) := by
  have hlam : 12 ≤ (RadiiSet.setting β).lam (flow β hβ).k0 := by
    rw [RadiiSet.setting_lam]
    have := RadiiSet.log_three_pos
    have : (0 : ℝ) ≤ ((flow β hβ).k0 : ℝ) * Real.log 3 := by positivity
    linarith
  have hd : (((flow β hβ).d : ℝ) + 3) / 2 = 3 := by simp [flow]
  have hL : Real.log ((flow β hβ).L : ℝ) = Real.log 3 := by simp [flow]
  rw [hd, hL]
  have h6 := log_three_gt
  have hc : 1 / 4 ≤ 1 - 1 / (2 * Real.log 3) := by
    have : 1 / (2 * Real.log 3) ≤ 3 / 4 := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    linarith
  nlinarith


section Generic

variable {S : Setting} [NeZero S.L] (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
  {R : ℕ → ℝ} (RH : RadiusHyp S.L S.Rb S.lam R) {N K k0 : ℕ} [NeZero N]

local notation "Hs" => (RadiiHist.hist (N := N) (K := K) (k0 := k0) ok h4 h5 RH)

include ok h4 h5 RH

/-- With `k₀ = T ≤ K`: a component at a scale `1 ≤ k ≤ k₀` is ripe iff `k = T`. -/
theorem ripe_iff (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ k0)
    (c : (Hs).Comp k) : S.Ripe k ((Hs).bk k c) ↔ k = Tstar S := by
  obtain ⟨hst, hs, -⟩ := RadiiHist.book_facts (N := N) (K := K) (k0 := k0) ok h4 h5 RH k hk1
    (by omega) hk (by omega) c
  constructor
  · rintro ⟨-, h⟩
    rw [tStar_of hst hs] at h
    exact h.symm
  · rintro rfl
    exact ⟨⟨1, 1, ∅, hst⟩, tStar_of hst hs⟩

theorem not_kept_of_ne (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) {k : ℕ} (hk : k ≠ Tstar S)
    (c : (Hs).Comp k) : ¬ (Hs).IsKeptEvent k c := fun h =>
  hk ((ripe_iff ok h4 h5 RH hK hk0 k h.1 h.2.1 c).mp h.2.2)

theorem kept_T (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) (c : (Hs).Comp (Tstar S)) :
    (Hs).IsKeptEvent (Tstar S) c :=
  ⟨one_le_Tstar S, hk0.symm.le, (ripe_iff ok h4 h5 RH hK hk0 _ (one_le_Tstar S) hk0.symm.le c).mpr rfl⟩

omit [NeZero S.L] ok h4 h5 RH in
/-- `G = G^pre` whenever the kept event does not occur. -/
theorem budgetPost_eq_pre_of_not_kept {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) (κK δ : ∀ k, H.Comp k → ℝ) {k : ℕ}
    (c : H.Comp k) (hn : ¬ H.IsKeptEvent k c) :
    H.budgetPost P κK δ k c = H.budgetPre P κK δ k c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases k with _ | j
    · exact (H.F.isEmpty_comp_zero.false c).elim
    · exact ⟨j, rfl⟩
  simp [RegionHistory.budgetPost, RegionHistory.budgetPre, RegionHistory.Gpost,
    RegionHistory.Gpre, RegionHistory.kappa, RegionHistory.logC, hn, RegionHistory.kappaPre,
    RegionHistory.logCPre]

omit [NeZero S.L] ok h4 h5 RH in
/-- `κ` depends on the kept data only through the kept events. -/
theorem kappa_congr {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) (κ κ' : ∀ k, H.Comp k → ℝ) (m : ℕ)
    (h : ∀ k ≤ m, ∀ c : H.Comp k, H.IsKeptEvent k c → κ k c = κ' k c) :
    ∀ k ≤ m, ∀ c : H.Comp k, H.kappa P κ k c = H.kappa P κ' k c := by
  intro k
  induction k with
  | zero => intro _ c; exact (H.F.isEmpty_comp_zero.false c).elim
  | succ k ih =>
    intro hk c
    by_cases hc : H.IsKeptEvent (k + 1) c
    · simp only [RegionHistory.kappa, hc, ite_true]
      exact h _ hk c hc
    · simp only [RegionHistory.kappa, hc, ite_false, RegionHistory.kappaPre]
      congr 1
      refine Finset.sum_congr rfl fun y _ => ?_
      exact ih (by omega) y

omit [NeZero S.L] ok h4 h5 RH in
/-- The kept data `κK_{j+1}(Z') = κ^pre_{j+1}(Z') + A₃' λ_{j+1}^{p_R}`, with `κ^pre` computed
from the recursion with vanishing kept data. -/
noncomputable def keptK {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) :
    ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | j + 1, Z' => H.kappaPre P j (H.kappa P (fun _ _ => 0) j) Z' + S.A3' * S.lam (j + 1) ^ S.pR

omit [NeZero S.L] ok h4 h5 RH in
theorem keptK_succ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) (j : ℕ) (Z' : H.Comp (j + 1)) :
    keptK H P (j + 1) Z' =
      H.kappaPre P j (H.kappa P (fun _ _ => 0) j) Z' + S.A3' * S.lam (j + 1) ^ S.pR := rfl

omit [NeZero S.L] ok h4 h5 RH in
/-- **(Rg) at a kept ripe component, first kept event**: with the kept data `keptK`,
`G^pre_k(Z) - C_R λ_k^{2d+1} + A₃' λ_k^{p_R} ≤ G_k(Z)`. -/
theorem rg_kept {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) {k : ℕ} (c : H.Comp k)
    (hkept : H.IsKeptEvent k c) (hnk : ∀ m < k, ∀ c' : H.Comp m, ¬ H.IsKeptEvent m c')
    (hCR : 0 ≤ S.CR) (hlam : 0 ≤ S.lam k) :
    H.budgetPre P (keptK H P) (fun _ _ => 0) k c - S.CR * S.lam k ^ (2 * S.d + 1)
        + S.A3' * S.lam k ^ S.pR ≤ H.budgetPost P (keptK H P) (fun _ _ => 0) k c := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := by
    rcases k with _ | j
    · exact (H.F.isEmpty_comp_zero.false c).elim
    · exact ⟨j, rfl⟩
  have hk : H.kappa P (keptK H P) j = H.kappa P (fun _ _ => 0) j := by
    funext c'
    exact kappa_congr H P _ _ j (fun m hm c'' hc'' => absurd hc'' (hnk m (by omega) c'')) j
      le_rfl c'
  have e1 : H.kappa P (keptK H P) (j + 1) c =
      H.kappaPre P j (H.kappa P (fun _ _ => 0) j) c + S.A3' * S.lam (j + 1) ^ S.pR := by
    simp only [RegionHistory.kappa, hkept, ite_true]
    rfl
  have e2 : H.logC (fun _ _ => (0 : ℝ)) (j + 1) c = H.logCPre j (H.logC (fun _ _ => 0) j) c := by
    simp [RegionHistory.logC]
  have hpow : 0 ≤ S.CR * S.lam (j + 1) ^ (2 * S.d + 1) := mul_nonneg hCR (pow_nonneg hlam _)
  have h1 : H.budgetPre P (keptK H P) (fun _ _ => 0) (j + 1) c =
      P.budgetG S (j + 1) (H.kappaPre P j (H.kappa P (fun _ _ => 0) j) c)
        (H.logCPre j (H.logC (fun _ _ => 0) j) c) c.1.card := by
    simp only [RegionHistory.budgetPre, RegionHistory.Gpre, hk]
  have h2 : H.budgetPost P (keptK H P) (fun _ _ => 0) (j + 1) c =
      P.budgetG S (j + 1) (H.kappaPre P j (H.kappa P (fun _ _ => 0) j) c +
        S.A3' * S.lam (j + 1) ^ S.pR) (H.logCPre j (H.logC (fun _ _ => 0) j) c) c.1.card := by
    simp only [RegionHistory.budgetPost, RegionHistory.Gpost, e1, e2]
  rw [h1, h2]
  unfold BudgetConsts.budgetG
  linarith

/-- The unique component at scale `T` is ripe. -/
theorem exists_ripe (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) :
    ∃ c : (Hs).Comp (Tstar S), (∀ c' : (Hs).Comp (Tstar S), c' = c) ∧
      S.Ripe (Tstar S) ((Hs).bk (Tstar S) c) := by
  obtain ⟨c, hc⟩ := RadiiHist.comp_unique (N := N) (K := K) (k0 := k0) ok h4 h5 RH
    (Tstar S) (one_le_Tstar S) hK
  exact ⟨c, hc, (ripe_iff ok h4 h5 RH hK hk0 _ (one_le_Tstar S) hk0.symm.le c).mpr rfl⟩

/-- **`RemCluster` has a member for the ripe history**: a removed cluster consisting of the ripe
component of `Z^pre_T` (with `K = k_f > k₀`), with the empty kept configuration. -/
theorem remCluster_exists (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) (M : ℕ) [NeZero M] :
    ∃ (Kc : HistConfig S (RadiiHist.side S N K) R k0 K M (Tstar S))
      (C : Finset (ConfigPair S (RadiiHist.side S N K) M K (Tstar S))), RemCluster Kc C := by
  classical
  obtain ⟨c, hc, hrip⟩ := exists_ripe ok h4 h5 RH hK hk0 (N := N)
  have hH : Hs ∈ (RegionHistory.historiesWithFinal (R := R)
      (k0 := k0) (K := K) (Tstar S) c.1 :
      Set (RegionHistory S (RadiiHist.side S N K) R k0 K)) := by
    have hZp : (Hs).F.Zp (Tstar S) = c.1 := by
      ext x
      constructor
      · intro hx
        obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega (Tstar S)) hx
        have := hc ⟨Y, hY⟩
        have h2 : Y = c.1 := congrArg Subtype.val this
        rwa [h2] at hxY
      · intro hx; exact comp_subset c.2 hx
    refine ⟨fun k c0 h => absurd h (by simp [RadiiHist.rem_eq]), hZp, ?_⟩
    rw [← hZp]
    ext Y
    rw [Finset.mem_singleton]
    constructor
    · intro hY; exact (congrArg Subtype.val (hc ⟨Y, hY⟩)).trans hZp.symm
    · intro h
      have : Y = c.1 := h.trans hZp
      rw [this]; exact c.2
  refine ⟨HistConfig.empty, {(c.1, (Hs).localHistory M K (Tstar S) c)},
    ⟨⟨_, Finset.mem_singleton_self _⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro m hm
    rw [Finset.mem_singleton] at hm
    subst hm
    exact ⟨_, hH, c, rfl, rfl, hrip⟩
  · intro m hm
    rw [Finset.mem_singleton] at hm
    subst hm
    exact ⟨_, hH, c, rfl, rfl⟩
  · intro m hm m' hm' hne
    rw [Finset.mem_singleton] at hm hm'
    exact absurd (hm.trans hm'.symm) hne
  · intro m _ m' hm'
    simp [HistConfig.empty] at hm'
  · intro m hm m' hm'
    rw [Finset.mem_singleton] at hm hm'
    rw [hm, hm']

/-- **`RipeWindow`** for the ripe component of the history with `K = k_f > k₀`, side factor
`bigN S`. -/
theorem ripeWindow_exists' (G : S.Good) (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) :
    ∃ c : (RadiiHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 RH).Comp (Tstar S),
      (RadiiHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 RH).RipeWindow (Tstar S) c := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 RH hK hk0 (N := bigN S)
  refine ⟨c, RegionHistory.ripe_window G ?_ hk0.symm.le hK hrip⟩
  intro k _ hk
  have hk' : k ∈ Finset.range (Tstar S + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 4 * S.rho k + 21 ≤ ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21) :=
    Finset.single_le_sum (f := fun j => 4 * S.rho j + 21) (fun _ _ => Nat.zero_le _) hk'
  have h2 : bigN S ≤ RadiiHist.side S (bigN S) K k := by
    unfold RadiiHist.side
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
  have h3 : bigN S = 1 + ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21) := rfl
  omega

/-- **`T4Facts`** for the merge, at scale `T`, of two parts carrying the ripe book (cap
`ν_max(T+1) ≥ 2`). -/
theorem t4Facts_exists' (G : S.Good) (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S)
    (hcap : 2 ≤ S.numax (Tstar S + 1)) :
    ∃ (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts S (Tstar S) parts f b' := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 RH hK hk0 (N := bigN S)
  obtain ⟨hst, -, -⟩ := RadiiHist.book_facts (N := bigN S) (K := K) (k0 := k0) ok h4 h5 RH
    (Tstar S) (one_le_Tstar S) hK hk0.symm.le le_rfl c
  set b := (RadiiHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 RH).bk (Tstar S) c with hb
  have hinv : BookInv S (Tstar S) b :=
    ((RadiiHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 RH).window_inv' G (Tstar S)
      (one_le_Tstar S) hk0.symm.le hK c).1
  have hlen : b.len = 0 := RegionHistory.len_zero_of_ripe hinv hrip
  have hnu : b.nu = 1 := Book.nu_active hst
  refine ⟨(Finset.univ : Finset (Fin 2)), fun _ => b,
    ⟨S.t4State (Tstar S + 1) (Finset.univ : Finset (Fin 2)) (fun _ => b) (Tstar S + 1), Tstar S + 1, 0, True⟩,
    by simp, ?_⟩
  refine Setting.Good.t4_inv G (b' := ⟨S.t4State (Tstar S + 1) (Finset.univ : Finset (Fin 2)) (fun _ => b)
    (Tstar S + 1), Tstar S + 1, 0, True⟩) (by simp) (fun _ _ => hinv)
    (fun _ _ => Or.inl hrip.1) ?_ rfl le_rfl (fun _ => rfl) ?_ (fun h => absurd trivial h)
    (fun _ => rfl)
  · simpa [hnu] using hcap
  · simp only [hlen, zero_div, Finset.sum_const_zero, zero_add]
    exact mul_nonneg (by simp) (S.D_nonneg _)


end Generic

end RadiiRipe
end Balaban.Inhabited
