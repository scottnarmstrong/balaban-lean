/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.RemovalHist
public import Balaban.Spine.LastIntegral
public import Balaban.Spine.FinalRepGroup
public import Balaban.LargeField.History.InhabitedJoint

/-!
# `n₀ = 1`: one history with empty region and no removal record (ruling R12)

In a complete set of histories there is exactly one history with empty region at the scale `k` and
no removal record `Rem_j`, `j ≤ k` (`card_remFree_empty_eq_one`). Without removal a nonempty region
of the scale `j` has a nonempty successor region at the scale `j + 1` (`RegionHistory.exists_succ`),
and the new cubes `P, Q, R, S` lie in the region `Z^{(0)} ⊆ Z^pre`; so a removal-free history with
`Z_k = ∅` has empty regions and empty step records at all scales below `k`, and two such histories
agree. The trivial history (all steps empty) shows that one exists.
-/

@[expose] public section

open Balaban Balaban.LargeField Balaban.LargeField.Def7 Balaban.LargeField.Def7v2 RegionHistory

namespace Balaban.RootFSpine

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

section Chain

variable (H : RegionHistory S n R k0 K)

theorem Zp_succ_nonempty {j : ℕ} (hj : j < K) (hrem : H.rem j = ∅) (hne : (H.Zp j).Nonempty) :
    (H.Zp (j + 1)).Nonempty := by
  obtain ⟨x, hx⟩ := hne
  have hc : linkClass (S.omega j) (H.Zp j) x ∈ comps (S.omega j) (H.Zp j) :=
    mem_comps_iff.2 ⟨x, hx, rfl⟩
  obtain ⟨Z', hZ'⟩ := H.exists_succ hj (c := ⟨_, hc⟩) (by rw [hrem]; simp)
  obtain ⟨y, hy⟩ := comp_nonempty Z'.2
  exact ⟨y, comp_subset Z'.2 hy⟩

/-- Without removal records, an empty region at the scale `k` forces empty regions at all scales
`j ≤ k`. -/
theorem Zp_empty_of_top {k : ℕ} (hkK : k ≤ K) (hrem : ∀ j, j ≤ k → H.rem j = ∅)
    (hk : H.Zp k = ∅) : ∀ j, j ≤ k → H.Zp j = ∅ := by
  have key : ∀ m j, j + m = k → H.Zp j = ∅ := by
    intro m
    induction m with
    | zero => intro j hj; simpa using (show j = k by omega) ▸ hk
    | succ m ih =>
      intro j hj
      by_contra hne
      have h1 := ih (j + 1) (by omega)
      have := Zp_succ_nonempty H (by omega) (hrem j (by omega)) (Finset.nonempty_iff_ne_empty.2 hne)
      rw [h1] at this
      exact Finset.not_nonempty_empty this
  exact fun j hj => key (k - j) j (by omega)

/-- The new cubes of a step lie in the next region. -/
theorem newCubes_empty_of_Zp_empty {j : ℕ} (h : H.Zp (j + 1) = ∅) :
    (H.step j).P = ∅ ∧ (H.step j).Q = ∅ ∧ (H.step j).R = ∅ ∧ (H.step j).S = ∅ := by
  have hsub : (H.step j).newCubes ⊆ H.F.Zpre (j + 1) := fun x hx =>
    (H.step j).Z0_subset_Zpre _ _ ((H.step j).newCubes_subset_Z0 hx)
  have hZ : H.F.Zpre (j + 1) = ∅ := by
    have := coe_finOf (H.F.Zpre (j + 1))
    have h' : H.Zp (j + 1) = finOf (H.F.Zpre (j + 1)) := rfl
    rw [← h', h] at this
    simpa using this.symm
  rw [hZ] at hsub
  have e : ∀ {T : Set (Torus S.d (n (j + 1)))}, T ⊆ (H.step j).newCubes → T = ∅ := fun hT =>
    Set.subset_empty_iff.1 (hT.trans hsub)
  refine ⟨e fun x hx => Or.inl (Or.inl (Or.inl hx)), e fun x hx => Or.inl (Or.inl (Or.inr hx)),
    e fun x hx => Or.inl (Or.inr hx), e fun x hx => Or.inr hx⟩

end Chain

section Agree

/-- Two removal-free histories with empty region at the scale `k` agree (records of the steps and
of the removals). -/
theorem agree_of_remFree_empty {k : ℕ} (hkK : k ≤ K) (A B : LabHist S n R k0 K)
    (hA : (A.H.step k).Z = ∅) (hB : (B.H.step k).Z = ∅)
    (hrA : ∀ j, j ≤ k → A.H.rem j = ∅) (hrB : ∀ j, j ≤ k → B.H.rem j = ∅) :
    A.Agree k (k + 1) B := by
  classical
  have key : ∀ H : RegionHistory S n R k0 K, (H.step k).Z = ∅ → (∀ j, j ≤ k → H.rem j = ∅) →
      ∀ j, j ≤ k → H.Zp j = ∅ := by
    intro H hZ hrem
    refine Zp_empty_of_top H hkK hrem ?_
    have h := H.Z_eq k
    rw [hrem k le_rfl] at h
    simp at h
    rw [hZ] at h
    have : ((H.Zp k : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) = ∅ := by
      show ((finOf (H.F.Zpre k) : Finset (Torus S.d (n k))) : Set (Torus S.d (n k))) = ∅
      rw [coe_finOf]; exact h.symm
    exact_mod_cast this
  have kA := key A.H hA hrA
  have kB := key B.H hB hrB
  refine ⟨fun j hj => ?_, fun j hj => ?_⟩
  · have e := fun (H : RegionHistory S n R k0 K) (hZ : H.Zp (j + 1) = ∅) =>
      newCubes_empty_of_Zp_empty H hZ
    obtain ⟨a1, a2, a3, a4⟩ := e A.H (kA (j + 1) (by omega))
    obtain ⟨b1, b2, b3, b4⟩ := e B.H (kB (j + 1) (by omega))
    exact ⟨a1.trans b1.symm, a2.trans b2.symm, a3.trans b3.symm, a4.trans b4.symm⟩
  · refine ⟨(hrA j (by omega)).trans (hrB j (by omega)).symm, ?_⟩
    funext c
    have eA := kA j (by omega)
    have eB := kB j (by omega)
    unfold LabHist.keptLab
    have hc : ∀ H : RegionHistory S n R k0 K, H.Zp j = ∅ →
        ¬ c ∈ comps (S.omega j) (H.Zp j) := by
      intro H h hcm
      obtain ⟨x, hx⟩ := comp_nonempty hcm
      have := comp_subset hcm hx
      rw [h] at this
      simp at this
    simp [hc A.H eA, hc B.H eB]

end Agree

section Trivial

variable [NeZero S.L]

/-- The labelled history without large-field cubes and without removal, built on the flow data of
any labelled history. -/
noncomputable def trivialOf (A0 : LabHist S n R k0 K) : LabHist S n R k0 K where
  H :=
    { F := { A0.H.F with step := fun k => RegionHistory.emptyStep S n R k ∅ }
      rem := fun _ => ∅
      rem_sub := fun _ => Finset.empty_subset _
      rem_empty := fun _ _ => rfl
      Z_eq := fun k => by
        have : ({ A0.H.F with step := fun k => RegionHistory.emptyStep S n R k ∅ } :
            FlowSteps S n R k0 K).Zpre k = ∅ := by
          cases k with
          | zero => rfl
          | succ k => exact JointWitness.emptyStep_Zpre_empty S n R k _ _
        rw [this]
        simp [RegionHistory.emptyStep] }
  adm := fun k c hc => absurd hc (by simp)
  lab := fun _ _ => 0

theorem trivialOf_region (A0 : LabHist S n R k0 K) (k : ℕ) : ((trivialOf A0).H.step k).Z = ∅ := rfl

theorem trivialOf_rem (A0 : LabHist S n R k0 K) (k : ℕ) : (trivialOf A0).H.rem k = ∅ := rfl

/-- **`n₀ = 1`** (ruling R12): a complete set of histories contains exactly one history with empty
region at the scale `k` and no removal record. -/
theorem card_remFree_empty_eq_one {k : ℕ} (hkK : k ≤ K) {hist : Finset (LabHist S n R k0 K)}
    (hc : IsComplete k (k + 1) hist) (A0 : LabHist S n R k0 K) :
    (hist.filter (fun A => lastRegion A k = ∅ ∧ ∀ j, j ≤ k → A.H.rem j = ∅)).card = 1 := by
  classical
  refine le_antisymm (Finset.card_le_one.2 fun a ha b hb => ?_) (Finset.card_pos.2 ?_)
  · obtain ⟨ha1, ha2, ha3⟩ := Finset.mem_filter.1 ha
    obtain ⟨hb1, hb2, hb3⟩ := Finset.mem_filter.1 hb
    have hab := agree_of_remFree_empty hkK a b ((lastRegion_eq_empty_iff a k).1 ha2)
      ((lastRegion_eq_empty_iff b k).1 hb2) ha3 hb3
    exact ((hc a).unique ⟨ha1, LabHist.agree_refl _ _ a⟩ ⟨hb1, hab⟩)
  · obtain ⟨B, ⟨hB, hAB⟩, -⟩ := hc (trivialOf A0)
    refine ⟨B, Finset.mem_filter.2 ⟨hB, ?_, fun j hj => ?_⟩⟩
    · rw [lastRegion_eq_empty_iff, ← LabHist.Agree.region_eq (Nat.lt_succ_self k) hAB k le_rfl]
      rfl
    · have := (hAB.2 j (by omega)).1
      rw [← this]; rfl

end Trivial

section Weight

open Classical

variable {S : Setting} {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M] [NeZero S.L] {N : ℕ}
  {geo : ∀ (nK : ℕ) [NeZero nK], Geo S (sides S.L K nK) R M} {cs : OpConsts} {P : BudgetConsts}
  {P6 : Balaban.SmallField.Def6.Consts} {C7 : Consts7} {k : ℕ} {ϱ : ℝ}

/-- **The weight of the empty region is `Ξ^sf`** (P7 (4.11); ruling R12, `n₀ = 1`): for a
representation whose set of histories is complete, the weight of the empty region of the last
integral is exactly `sfIntegral`. -/
theorem lastRegionWeight_empty_eq_sfIntegral_of_complete
    (F : RepFam S R k0 K M N geo cs P k C7.m₁ ϱ) (hM6 : M = S.L ^ (P6.m₀ + C7.m₁))
    (hkK : k ≤ K) (vc : CorrCoef S.d) (hv : EuclideanSpace ℝ (Fin N)) (nK : ℕ) [NeZero nK]
    (g : GIdx S (sides S.L K nK) M K N → ℂ)
    (hc : IsComplete k (k + 1) (F.lf nK).hist) (A0 : LabHist S (sides S.L K nK) R k0 K) :
    lastRegionWeight (F.ctx hM6 hkK nK) vc (F.lf nK) hv g ∅ = sfIntegral F hM6 hkK vc hv nK g :=
  lastRegionWeight_empty_eq_sfIntegral F hM6 hkK vc hv nK g (card_remFree_empty_eq_one hkK hc A0)

end Weight

end Balaban.RootFSpine
