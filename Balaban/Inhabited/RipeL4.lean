/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RipeL4Flow

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# A ripe component in the large-field flow at `L = 4`

The history `RipeHist.hist` of `RipeHistory.lean` (one cube created at `0 → 1`, a single component
`Z_k` with book `Active(1,1,∅)` and clock `s = 1` at every `1 ≤ k ≤ K`) on the flow of
`RipeL4Flow` (`k₀ = T = t^*(Active(1,1,∅), 1)`, `K = k_f > k₀`).  The component at scale `T` is
ripe, at a scale `1 ≤ T ≤ k₀`, and no component is ripe at another scale `≤ k₀`.  The kept data
`κK` solve the recursion of Definition II.5.11 at the (only) kept event, so that (Rg) for ripe
components holds with equality at `A₃' λ_T^{p_R}` (`C_R = 0`), and `ripeWitnessL4 :
FlowCounterWitness` witnesses `rg_ripe` non-vacuously.
-/

@[expose] public section

namespace Balaban.Inhabited
namespace RipeL4

open Balaban Balaban.LargeField Balaban.LargeField.JointWitness RipeHist

section Generic

variable {S : Setting} [NeZero S.L] (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
  (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) {N K k0 : ℕ} [NeZero N]

local notation "Hs" => (RipeHist.hist (N := N) (K := K) (k0 := k0) ok h4 h5 hRb)

include ok h4 h5 hRb

/-- With `k₀ = T ≤ K`: a component at a scale `1 ≤ k ≤ k₀` is ripe iff `k = T`. -/
theorem ripe_iff (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) (k : ℕ) (hk1 : 1 ≤ k) (hk : k ≤ k0)
    (c : (Hs).Comp k) : S.Ripe k ((Hs).bk k c) ↔ k = Tstar S := by
  obtain ⟨hst, hs, -⟩ := RipeHist.book_facts (N := N) (K := K) (k0 := k0) ok h4 h5 hRb k hk1
    (by omega) hk (by omega) c
  constructor
  · rintro ⟨-, h⟩
    rw [tStar_of hst hs] at h
    exact h.symm
  · rintro rfl
    exact ⟨⟨1, 1, ∅, hst⟩, tStar_of hst hs⟩

theorem not_kept_of_ne (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) {k : ℕ} (hk : k ≠ Tstar S)
    (c : (Hs).Comp k) : ¬ (Hs).IsKeptEvent k c := fun h =>
  hk ((ripe_iff ok h4 h5 hRb hK hk0 k h.1 h.2.1 c).mp h.2.2)

theorem kept_T (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) (c : (Hs).Comp (Tstar S)) :
    (Hs).IsKeptEvent (Tstar S) c :=
  ⟨one_le_Tstar S, hk0.symm.le, (ripe_iff ok h4 h5 hRb hK hk0 _ (one_le_Tstar S) hk0.symm.le c).mpr rfl⟩

omit [NeZero S.L] ok h4 h5 hRb in
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

omit [NeZero S.L] ok h4 h5 hRb in
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

omit [NeZero S.L] ok h4 h5 hRb in
/-- The kept data `κK_{j+1}(Z') = κ^pre_{j+1}(Z') + A₃' λ_{j+1}^{p_R}`, with `κ^pre` computed
from the recursion with vanishing kept data. -/
noncomputable def keptK {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) :
    ∀ k, H.Comp k → ℝ
  | 0, _ => 0
  | j + 1, Z' => H.kappaPre P j (H.kappa P (fun _ _ => 0) j) Z' + S.A3' * S.lam (j + 1) ^ S.pR

omit [NeZero S.L] ok h4 h5 hRb in
theorem keptK_succ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
    (H : RegionHistory S n R k0 K) (P : BudgetConsts) (j : ℕ) (Z' : H.Comp (j + 1)) :
    keptK H P (j + 1) Z' =
      H.kappaPre P j (H.kappa P (fun _ _ => 0) j) Z' + S.A3' * S.lam (j + 1) ^ S.pR := rfl

omit [NeZero S.L] ok h4 h5 hRb in
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
  obtain ⟨c, hc⟩ := RipeHist.comp_unique (N := N) (K := K) (k0 := k0) ok h4 h5 hRb
    (Tstar S) (one_le_Tstar S) hK
  exact ⟨c, hc, (ripe_iff ok h4 h5 hRb hK hk0 _ (one_le_Tstar S) hk0.symm.le c).mpr rfl⟩

/-- **`RemCluster` has a member for the ripe history**: a removed cluster consisting of the ripe
component of `Z^pre_T` (with `K = k_f > k₀`), with the empty kept configuration. -/
theorem remCluster_exists (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S) (M : ℕ) [NeZero M] :
    ∃ (Kc : HistConfig S (RipeHist.side S N K) JointWitness.radii k0 K M (Tstar S))
      (C : Finset (ConfigPair S (RipeHist.side S N K) M K (Tstar S))), RemCluster Kc C := by
  classical
  obtain ⟨c, hc, hrip⟩ := exists_ripe ok h4 h5 hRb hK hk0 (N := N)
  have hH : Hs ∈ (RegionHistory.historiesWithFinal (R := JointWitness.radii)
      (k0 := k0) (K := K) (Tstar S) c.1 :
      Set (RegionHistory S (RipeHist.side S N K) JointWitness.radii k0 K)) := by
    have hZp : (Hs).F.Zp (Tstar S) = c.1 := by
      ext x
      constructor
      · intro hx
        obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega (Tstar S)) hx
        have := hc ⟨Y, hY⟩
        have h2 : Y = c.1 := congrArg Subtype.val this
        rwa [h2] at hxY
      · intro hx; exact comp_subset c.2 hx
    refine ⟨fun k c0 h => absurd h (by simp [RipeHist.rem_eq]), hZp, ?_⟩
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
    ∃ c : (RipeHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 hRb).Comp (Tstar S),
      (RipeHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 hRb).RipeWindow (Tstar S) c := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 hRb hK hk0 (N := bigN S)
  refine ⟨c, RegionHistory.ripe_window G ?_ hk0.symm.le hK hrip⟩
  intro k _ hk
  have hk' : k ∈ Finset.range (Tstar S + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 4 * S.rho k + 21 ≤ ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21) :=
    Finset.single_le_sum (f := fun j => 4 * S.rho j + 21) (fun _ _ => Nat.zero_le _) hk'
  have h2 : bigN S ≤ RipeHist.side S (bigN S) K k := by
    unfold RipeHist.side
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
  have h3 : bigN S = 1 + ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21) := rfl
  omega

/-- **`T4Facts`** for the merge, at scale `T`, of two parts carrying the ripe book (cap
`ν_max(T+1) ≥ 2`). -/
theorem t4Facts_exists' (G : S.Good) (hK : Tstar S ≤ K) (hk0 : k0 = Tstar S)
    (hcap : 2 ≤ S.numax (Tstar S + 1)) :
    ∃ (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts S (Tstar S) parts f b' := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 hRb hK hk0 (N := bigN S)
  obtain ⟨hst, -, -⟩ := RipeHist.book_facts (N := bigN S) (K := K) (k0 := k0) ok h4 h5 hRb
    (Tstar S) (one_le_Tstar S) hK hk0.symm.le le_rfl c
  set b := (RipeHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 hRb).bk (Tstar S) c with hb
  have hinv : BookInv S (Tstar S) b :=
    ((RipeHist.hist (N := bigN S) (K := K) (k0 := k0) ok h4 h5 hRb).window_inv' G (Tstar S)
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

end RipeL4
end Balaban.Inhabited
