/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.Base.BaseGenCanon
public import Balaban.Spine.HistCanon

/-!
# The histories at scale `1` and the sets of failed cubes

A history up to scale `1` is determined by its base record `(P₁, Q₁, R₁, S₁)`: the records of the
steps `j < 1` and the `R`-records at the scales `j < 1` (which are trivial, `Z₀ = ∅`).  So a
complete set of histories up to scale `1` has exactly one history for each admissible base record
(`canonHist_baseRecord_injOn`), and the term of the decomposition of the first density for the set
`P₁` of a history is determined by the failed set only: the generating set of the history is
`baseGen` of its good region, the record may be replaced by `BaseRecord.trivial`
(`baseRecord_Omega_eq`).  Distinct histories with the same failed set `P₁` differ in `(Q₁, R₁, S₁)`
and share the term of `baseRho1_eq_sum_retained_canon`; the sum over the complete set of histories
is therefore the sum over the failed sets only once the terms are split by `(Q₁, R₁, S₁)`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.LargeField.Def7 RegionHistory Balaban.RootFSpine

section Hist

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} [NeZero S.L]

/-- The good region of the base record of a history is `Ω(P₁)`. -/
theorem baseRecord_Omega_eq (H : RegionHistory S n R k0 K) :
    H.baseRecord.Omega = Region.Omega S.L (H.step 0).P Set.univ := rfl

/-- The failed set of the base record of a history is `P₁`. -/
theorem baseRecord_P_eq (H : RegionHistory S n R k0 K) : H.baseRecord.P = (H.step 0).P := rfl

omit [NeZero S.L] in
/-- **The records of a history at scale `1` are the base record.** Two histories agree up to
scale `1` (with `R`-records below `1`) iff their steps `0 → 1` have the same `(P, Q, R, S)`. -/
theorem agree_one_iff (A B : LabHist S n R k0 K) :
    A.Agree 1 1 B ↔ (A.H.step 0).P = (B.H.step 0).P ∧ (A.H.step 0).Q = (B.H.step 0).Q ∧
      (A.H.step 0).R = (B.H.step 0).R ∧ (A.H.step 0).S = (B.H.step 0).S := by
  constructor
  · intro h
    exact h.1 0 (by omega)
  · intro h
    refine ⟨fun j hj => ?_, fun j hj => ?_⟩
    · have : j = 0 := by omega
      subst this
      exact h
    · have : j = 0 := by omega
      subst this
      refine ⟨?_, ?_⟩
      · rw [A.H.rem_empty 0 (Or.inl rfl), B.H.rem_empty 0 (Or.inl rfl)]
      · funext c
        unfold LabHist.keptLab
        have hA : ¬ c ∈ comps (S.omega 0) (A.H.Zp 0) := by
          intro hc
          have := A.H.F.isEmpty_comp_zero
          exact this.false ⟨c, hc⟩
        have hB : ¬ c ∈ comps (S.omega 0) (B.H.Zp 0) := by
          intro hc
          have := B.H.F.isEmpty_comp_zero
          exact this.false ⟨c, hc⟩
        simp [hA, hB]

/-- **The histories of a complete set at scale `1` are determined by their base record**: each
base record occurs at most once. -/
theorem canonHist_baseRecord_injOn (𝔄 : Finset (LabHist S n R k0 K)) (h : IsComplete 1 1 𝔄)
    {A B : LabHist S n R k0 K} (hA : A ∈ 𝔄) (hB : B ∈ 𝔄)
    (hP : (A.H.step 0).P = (B.H.step 0).P) (hQ : (A.H.step 0).Q = (B.H.step 0).Q)
    (hR : (A.H.step 0).R = (B.H.step 0).R) (hS : (A.H.step 0).S = (B.H.step 0).S) : A = B := by
  obtain ⟨C, hC, huniq⟩ := h A
  have h1 := huniq A ⟨hA, LabHist.agree_refl 1 1 A⟩
  have h2 := huniq B ⟨hB, (agree_one_iff A B).2 ⟨hP, hQ, hR, hS⟩⟩
  exact h1.trans h2.symm

/-- **Histories with the same failed set have the same good region**, hence the same generating
set `baseGen` and the same retained set. -/
theorem baseRecord_Omega_eq_of_P_eq {A B : RegionHistory S n R k0 K}
    (h : (A.step 0).P = (B.step 0).P) : A.baseRecord.Omega = B.baseRecord.Omega := by
  rw [baseRecord_Omega_eq, baseRecord_Omega_eq, h]

end Hist

end Balaban.LargeField
