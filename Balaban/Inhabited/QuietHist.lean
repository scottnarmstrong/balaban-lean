/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.InhabitedJoint
public import Balaban.LargeField.History.RipeWindow
public import Balaban.LargeField.Base.BaseRecord


/-!
# A region history with a quiet step, on arbitrary tori and radii

The history of `RipeHistory.lean` (one large-field cube created at `0 → 1`, nothing afterwards, no
removed components), generalized to arbitrary tori `n` with `n_k = L n_{k+1}` below the horizon
and arbitrary radii `R` with `RadiusHyp`.  For every `1 ≤ k ≤ K` there is exactly one component of
`Z^pre_k` (`comp_unique`), and no cube is new at a scale `≥ 2` (`mem_newCubes_succ`), so every step
`k → k + 1`, `1 ≤ k`, is quiet in it.
-/

@[expose] public section

namespace Balaban.Inhabited.QuietHist

open Balaban Balaban.LargeField

variable {S : Setting} [NeZero S.L] {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ}

/-- The step from the region `Z`: a single new cube `{0}` in `P` at `k = 0` (`Z = ∅`), otherwise
no new cubes. -/
noncomputable def mkStep (k : ℕ) (Z : Set (Torus S.d (n k))) :
    RegionStep S.d S.L (n k) (n (k + 1)) (R (k - 1)) (R k) where
  Z := Z
  P := {x | k = 0 ∧ Z = ∅ ∧ x = 0}
  Q := ∅
  R := ∅
  S := ∅
  P_sub := by
    rintro x ⟨-, rfl, -⟩
    rw [omegaPrime_of_empty]
    exact Set.mem_univ _
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := Set.empty_subset _

variable (S n R) (k0 : ℕ)

/-- The regions `Z^pre_k`. -/
noncomputable def regions : ∀ k, Set (Torus S.d (n k))
  | 0 => ∅
  | k + 1 => (mkStep (S := S) (n := n) (R := R) k (regions k)).Zpre (S.omega (k + 1))
      (critOpt S k0 (k + 1))

variable {S n R k0}

/-- The flow steps. -/
noncomputable def flowSteps {K : ℕ} (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) (hnn : ∀ k, k < K → n k = S.L * n (k + 1)) :
    FlowSteps S n R k0 K where
  ok := ok
  s4 := h4
  s5 := h5
  RH := RH
  hnn := hnn
  step := fun k => mkStep k (regions S n R k0 k)

theorem flowSteps_Zpre {K : ℕ} (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) (hnn : ∀ k, k < K → n k = S.L * n (k + 1)) :
    ∀ k, (flowSteps (k0 := k0) ok h4 h5 RH hnn).Zpre k = regions S n R k0 k
  | 0 => rfl
  | _ + 1 => rfl

/-- The history: one large-field cube at `0 → 1`, then no new cubes. -/
noncomputable def hist {K : ℕ} (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) (hnn : ∀ k, k < K → n k = S.L * n (k + 1)) :
    RegionHistory S n R k0 K where
  F := flowSteps ok h4 h5 RH hnn
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [flowSteps_Zpre]
    simp [flowSteps, mkStep]

section Comps

variable {K : ℕ} (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
  (RH : RadiusHyp S.L S.Rb S.lam R) (hnn : ∀ k, k < K → n k = S.L * n (k + 1))

local notation "Hs" => (hist (k0 := k0) ok h4 h5 RH hnn)

theorem rem_eq (k : ℕ) : (Hs).rem k = ∅ := rfl

theorem mem_newCubes_succ (k : ℕ) (x : Torus S.d (n (k + 1))) :
    x ∈ (Hs).newCubes (k + 1) ↔ k = 0 ∧ x = 0 := by
  have : (Hs).newCubes (k + 1) = finOf ((Hs).step k).newCubes := rfl
  rw [this, mem_finOf]
  show x ∈ ((mkStep k (regions S n R k0 k)).P ∪ ∅ ∪ ∅ ∪ ∅) ↔ _
  simp only [Set.union_empty, mkStep, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨rfl, h3⟩; exact ⟨rfl, rfl, h3⟩

theorem comp_unique : ∀ k, 1 ≤ k → k ≤ K → ∃ c : (Hs).Comp k, ∀ c' : (Hs).Comp k, c' = c := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hK
    have hg := (Hs).stepGeom (k := 0) (by omega)
    have h0 : (0 : Torus S.d (n 1)) ∈ ((Hs).step 0).newCubes :=
      Or.inl (Or.inl (Or.inl ⟨rfl, rfl, rfl⟩))
    have hσ : ({0} : Set (Torus S.d (n 1))) ∈ ((Hs).step 0).seeds (S.omega 0) :=
      Or.inr ⟨0, h0, rfl⟩
    obtain ⟨C, hC, hsub⟩ := ((Hs).step 0).seed_in_comp_Zpre hg.hn hg.hlt (critOpt S k0 1) hσ
    have hmem : ∀ c' : (Hs).Comp 1, (0 : Torus S.d (n 1)) ∈ c'.1 := by
      intro c'
      have h := (Hs).seed_pos (k := 0) (by omega) c'
      have hp : ((Hs).parts 0 c').card = 0 := by
        have : IsEmpty ((Hs).Comp 0) := (Hs).F.isEmpty_comp_zero
        rw [Finset.card_eq_zero]
        exact Finset.eq_empty_of_isEmpty _
      rw [hp, zero_add, Nat.one_le_iff_ne_zero] at h
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have := (mem_newCubes_succ (k0 := k0) ok h4 h5 RH hnn 0 x).mp hx2
      rw [this.2] at hx1
      exact hx1
    refine ⟨⟨C, hC⟩, fun c' => Subtype.ext ?_⟩
    exact comp_eq_of_mem c'.2 hC (hmem c') (hsub rfl)
  | succ k hk ih =>
    intro hK
    obtain ⟨c, hc⟩ := ih (by omega)
    obtain ⟨Z', hZ'⟩ := (Hs).exists_succ (k := k) (by omega) (c := c) (by simp [rem_eq])
    refine ⟨Z', fun c' => ?_⟩
    have h := (Hs).seed_pos (k := k) (by omega) c'
    have hn : (c'.1 ∩ (Hs).newCubes (k + 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := (mem_newCubes_succ (k0 := k0) ok h4 h5 RH hnn k x).mp (Finset.mem_inter.mp hx).2
      omega
    rw [hn, add_zero] at h
    obtain ⟨y, hy⟩ := Finset.card_pos.mp h
    have hy' := ((Hs).mem_parts k y c').mp hy
    rw [hc y] at hy'
    exact RegionHistory.IsSucc.unique (H := Hs) hy'.2 hZ'

end Comps

end Balaban.Inhabited.QuietHist
