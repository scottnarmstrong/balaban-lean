/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseHistRecords

/-!
# Every base record is the base record of an admissible history

Given a base record `br = (P₁, Q₁, R₁, S₁)` there is an admissible region history whose step
`0 → 1` is the step of `br` (`exists_labHist_of_baseRecord`): the steps `k ≥ 1` have empty records
`P = Q = R = S = ∅` and the region `Z_k = Z^pre_k` of the previous steps (`baseZ`), there are no
removals (so the admissibility condition on the removed components is vacuous), and the labels
are arbitrary.  The typing hypotheses are the conditions of `FlowSteps`: `S.Ok`, `s_* ≥ 4`,
`s' ≥ 5`, the radius hypotheses and `n_k = L n_{k+1}` below the horizon.

Hence, with the completeness of a set of histories at scale `1`, every base record is the base
record of exactly one of its histories (`canonHist_baseRecord_bijOn`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.LargeField.Def7 RegionHistory Balaban.RootFSpine

section Exists

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L]
  (k0 : ℕ) (br : BaseRecord S.d S.L (n 1) (R 0))

/-- **The step `k → k+1` of the constructed history** with the region `Z_k = Z`: the step of the
base record for `k = 0`, and the step with empty records for `k ≥ 1`. -/
noncomputable def baseStepAt : (k : ℕ) → Set (Torus S.d (n k)) →
    RegionStep S.d S.L (n k) (n (k + 1)) (R (k - 1)) (R k)
  | 0, _ => br.toStep (n 0) (R (0 - 1))
  | _ + 1, Z =>
    { Z := Z
      P := ∅
      Q := ∅
      R := ∅
      S := ∅
      P_sub := Set.empty_subset _
      Q_sub := Set.empty_subset _
      R_sub := Set.empty_subset _
      S_sub := Set.empty_subset _ }

/-- **The regions `Z_k = Z^pre_k`** of the constructed history. -/
noncomputable def baseZ : (k : ℕ) → Set (Torus S.d (n k))
  | 0 => ∅
  | k + 1 => (baseStepAt (R := R) br k (baseZ k)).Zpre (S.omega (k + 1)) (critOpt S k0 (k + 1))

variable {k0}

/-- **The constructed history**: the steps `baseStepAt k (baseZ k)`, no removals. -/
noncomputable def baseHistory {K : ℕ} (ok : S.Ok) (s4 : 4 ≤ S.sS) (s5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) (hnn : ∀ k, k < K → n k = S.L * n (k + 1)) :
    RegionHistory S n R k0 K where
  F := { ok := ok, s4 := s4, s5 := s5, RH := RH, hnn := hnn
         step := fun k => baseStepAt (R := R) br k (baseZ k0 br k) }
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := by
    intro k
    cases k with
    | zero => simp [baseStepAt, BaseRecord.toStep, FlowSteps.Zpre]
    | succ k => simp [baseStepAt, FlowSteps.Zpre, baseZ]

/-- **Every base record is the base record of an admissible history.**  The labels are arbitrary
(here constant), and the history has no removals, so the ripeness of the removed components is
vacuous. -/
theorem exists_labHist_of_baseRecord {K : ℕ} (ok : S.Ok) (s4 : 4 ≤ S.sS) (s5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) (hnn : ∀ k, k < K → n k = S.L * n (k + 1)) :
    ∃ A : LabHist S n R k0 K, A.H.baseRecord = br := by
  let H : RegionHistory S n R k0 K := baseHistory br ok s4 s5 RH hnn
  refine ⟨⟨H, fun k c hc => absurd hc (by simp [H, baseHistory]), fun _ _ => 0⟩, ?_⟩
  show BaseRecord.ofStep (H.step 0) H.step_zero_Z = br
  have h0 : H.step 0 = br.toStep (n 0) (R (0 - 1)) := rfl
  obtain ⟨P, Q, R', S', hQ, hR, hS⟩ := br
  rfl

end Exists

section Bijection

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} [NeZero S.L] {k0 K : ℕ}

omit [NeZero S.L] in
/-- A base record of a history is determined by the records of its step `0 → 1`. -/
theorem baseRecord_ext {A B : LabHist S n R k0 K} [NeZero S.L]
    (hP : (A.H.step 0).P = (B.H.step 0).P) (hQ : (A.H.step 0).Q = (B.H.step 0).Q)
    (hR : (A.H.step 0).R = (B.H.step 0).R) (hS : (A.H.step 0).S = (B.H.step 0).S) :
    A.H.baseRecord = B.H.baseRecord := by
  show BaseRecord.ofStep (A.H.step 0) A.H.step_zero_Z = BaseRecord.ofStep (B.H.step 0) B.H.step_zero_Z
  unfold BaseRecord.ofStep
  congr 1

/-- **The histories of a complete set at scale `1` are in bijection with the base records**
(with the typing hypotheses of `FlowSteps`). -/
theorem canonHist_baseRecord_bijOn {𝔄 : Finset (LabHist S n R k0 K)} (h : IsComplete 1 1 𝔄)
    (ok : S.Ok) (s4 : 4 ≤ S.sS) (s5 : 5 ≤ S.sP) (RH : RadiusHyp S.L S.Rb S.lam R)
    (hnn : ∀ k, k < K → n k = S.L * n (k + 1)) :
    Set.BijOn (fun A : LabHist S n R k0 K => A.H.baseRecord) (↑𝔄)
      (Set.univ : Set (BaseRecord S.d S.L (n 1) (R 0))) := by
  refine ⟨fun _ _ => Set.mem_univ _, ?_, ?_⟩
  · intro A hA B hB hAB
    have := congrArg BaseRecord.P hAB
    have h2 := congrArg BaseRecord.Q hAB
    have h3 := congrArg BaseRecord.R hAB
    have h4 := congrArg BaseRecord.S hAB
    exact canonHist_baseRecord_injOn 𝔄 h hA hB this h2 h3 h4
  · intro br _
    obtain ⟨A, hA⟩ := exists_labHist_of_baseRecord (k0 := k0) br ok s4 s5 RH hnn
    obtain ⟨B, ⟨hB, hAB⟩, -⟩ := h A
    refine ⟨B, hB, ?_⟩
    rw [← hA]
    obtain ⟨hP, hQ, hR, hS⟩ := (agree_one_iff A B).1 hAB
    exact (baseRecord_ext hP hQ hR hS).symm

end Bijection

end Balaban.LargeField
