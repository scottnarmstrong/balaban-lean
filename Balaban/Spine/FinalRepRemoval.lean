/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Spine.FinalRepGroup
public import Balaban.LargeField.History.InhabitedRipeRemoval

/-!
# Histories with an empty region and different removal records

`n₀`, the number of histories of a representation with empty region `Z_k(𝔸) = ∅`
(`Spine/FinalRepGroup.lean`), is at least two as soon as there is an admissible global history
with a removal that ends with `Z_k = ∅`, because `IsComplete k (k+1)` keeps one history of every
class of `Agree k (k+1)`, which compares the removal records `Rem_j`, `j ≤ k`.

* `LabHist.Agree.region_eq`: histories that agree up to `k` have the same regions `Z_j`, `j ≤ k`
  (the regions are functions of the records, Definition I.4.1).
* `two_le_card_empty_region`: if two histories have empty region at the scale `k` and do not
  agree, every complete set contains two histories with empty region.
* `two_le_card_empty_region_ripeRem`: the concrete case of the genuine-radii setting `wS`,
  `k₀ = k_f = T`, horizon `K = T + 1`, where the trivial history and `ripeRemHistory` (the ripe
  component of `Z^pre_T` removed at the scale `T`) both have `Z_T = ∅`.
-/

@[expose] public section

open MeasureTheory Balaban Balaban.LargeField Balaban.LargeField.Def7 RegionHistory

namespace Balaban.RootFSpine

theorem regionStep_ext {d L n0 n1 : ℕ} {Rp Rk : ℝ} {st st' : RegionStep d L n0 n1 Rp Rk}
    (hZ : st.Z = st'.Z) (hP : st.P = st'.P) (hQ : st.Q = st'.Q) (hR : st.R = st'.R)
    (hS : st.S = st'.S) : st = st' := by
  cases st; cases st'
  simp only at hZ hP hQ hR hS
  subst hZ hP hQ hR hS
  rfl

section
variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- Histories that agree up to scale `k` (with removal records up to `k`) have the same
regions `Z_j`, `j ≤ k`. -/
theorem LabHist.Agree.region_eq {k r : ℕ} (hr : k < r) {A B : LabHist S n R k0 K}
    (h : A.Agree k r B) : ∀ j, j ≤ k → (A.H.step j).Z = (B.H.step j).Z := by
  intro j
  induction j with
  | zero =>
    intro _
    have hA := A.H.Z_eq 0
    have hB := B.H.Z_eq 0
    rw [hA, hB]
    have := A.H.rem_empty 0 (Or.inl rfl)
    have := B.H.rem_empty 0 (Or.inl rfl)
    simp [FlowSteps.Zpre, *]
  | succ j ih =>
    intro hj
    have hjk : j < k := by omega
    have hstep : A.H.step j = B.H.step j := by
      obtain ⟨h1, -⟩ := h
      obtain ⟨hP, hQ, hR, hS⟩ := h1 j hjk
      exact regionStep_ext (ih (by omega)) hP hQ hR hS
    have hrem : A.H.rem (j + 1) = B.H.rem (j + 1) := (h.2 (j + 1) (by omega)).1
    rw [A.H.Z_eq (j + 1), B.H.Z_eq (j + 1), hrem]
    have : A.H.F.Zpre (j + 1) = B.H.F.Zpre (j + 1) := by
      show (A.H.F.step j).Zpre _ _ = (B.H.F.step j).Zpre _ _
      exact congrArg (fun st => RegionStep.Zpre st _ _) hstep
    rw [this]

end

section Two

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}

/-- **Two non-agreeing histories with empty region give two elements of a complete set with
empty region.** -/
theorem two_le_card_empty_region {k : ℕ} (hist : Finset (LabHist S n R k0 K))
    (hc : IsComplete k (k + 1) hist) (A₁ A₂ : LabHist S n R k0 K)
    (h₁ : (A₁.H.step k).Z = ∅) (h₂ : (A₂.H.step k).Z = ∅) (hne : ¬ A₁.Agree k (k + 1) A₂) :
    2 ≤ (hist.filter (fun A => lastRegion A k = ∅)).card := by
  classical
  obtain ⟨B₁, ⟨hB₁, ha₁⟩, -⟩ := hc A₁
  obtain ⟨B₂, ⟨hB₂, ha₂⟩, -⟩ := hc A₂
  have hB : B₁ ≠ B₂ := by
    rintro rfl
    exact hne (LabHist.agree_trans ha₁ (LabHist.agree_symm ha₂))
  have e₁ : lastRegion B₁ k = ∅ := by
    rw [lastRegion_eq_empty_iff, ← LabHist.Agree.region_eq (Nat.lt_succ_self k) ha₁ k le_rfl, h₁]
  have e₂ : lastRegion B₂ k = ∅ := by
    rw [lastRegion_eq_empty_iff, ← LabHist.Agree.region_eq (Nat.lt_succ_self k) ha₂ k le_rfl, h₂]
  exact Finset.one_lt_card.2 ⟨B₁, Finset.mem_filter.2 ⟨hB₁, e₁⟩, B₂,
    Finset.mem_filter.2 ⟨hB₂, e₂⟩, hB⟩

end Two

section Witness

open Balaban.Inhabited Balaban.Inhabited.RadiiHist Balaban.Inhabited.RipeRemoval
  Balaban.Inhabited.RadiiSet

/-- The flow steps of the genuine-radii setting without new cubes. -/
noncomputable def trivFlow : FlowSteps wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS)
    (Tstar wS + 1) :=
  { flowSteps2 wS wR (bigN wS) (Tstar wS + 1) wS_ok le_rfl le_rfl wRH with
    step := fun k => RegionHistory.emptyStep wS (side wS (bigN wS) (Tstar wS + 1)) wR k ∅ }

theorem trivFlow_Zpre : ∀ k, trivFlow.Zpre k = ∅
  | 0 => rfl
  | k + 1 => JointWitness.emptyStep_Zpre_empty wS (side wS (bigN wS) (Tstar wS + 1)) wR k _ _

/-- The region history without large-field cubes and without removal. -/
noncomputable def trivHist : RegionHistory wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS)
    (Tstar wS + 1) where
  F := trivFlow
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [trivFlow_Zpre]
    simp [trivFlow, RegionHistory.emptyStep]

/-- The labelled trivial history. -/
noncomputable def trivLab : LabHist wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS)
    (Tstar wS + 1) where
  H := trivHist
  adm := fun k c hc => absurd hc (by simp [trivHist])
  lab := fun _ _ => 0

/-- The labelled history of the ripe removal at the scale `T`. -/
noncomputable def remLab : LabHist wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS)
    (Tstar wS + 1) where
  H := ripeRemHistory
  adm := ripeRemHistory_admissible
  lab := fun _ _ => 0

theorem trivLab_region : (trivLab.H.step (Tstar wS)).Z = ∅ := rfl

theorem remLab_region : (remLab.H.step (Tstar wS)).Z = ∅ := by
  classical
  show (ripeRemHistory.step (Tstar wS)).Z = ∅
  rw [ripeRemHistory.Z_eq (Tstar wS)]
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_coe, exists_prop, Set.mem_empty_iff_false,
    iff_false, not_and, not_exists, not_forall]
  intro hx
  have hxF : x ∈ ripeRemHistory.F.Zp (Tstar wS) := by simpa [FlowSteps.Zp] using hx
  have hY : linkClass (wS.omega (Tstar wS)) (ripeRemHistory.F.Zp (Tstar wS)) x ∈
      comps (wS.omega (Tstar wS)) (ripeRemHistory.F.Zp (Tstar wS)) :=
    mem_comps_iff.2 ⟨x, hxF, rfl⟩
  refine ⟨linkClass (wS.omega (Tstar wS)) (ripeRemHistory.F.Zp (Tstar wS)) x, ?_,
    not_not.2 (mem_linkClass.2 ⟨hxF, Linked.refl _⟩)⟩
  exact mem_rem_T (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH (one_le_Tstar _)
    ⟨_, hY⟩

theorem trivLab_not_agree_remLab : ¬ trivLab.Agree (Tstar wS) (Tstar wS + 1) remLab := by
  intro h
  have := (h.2 (Tstar wS) (Nat.lt_succ_self _)).1
  obtain ⟨Y, hY⟩ := ripeRemHistory_rem_nonempty
  have h' : (∅ : Finset (Finset _)) = ripeRemHistory.rem (Tstar wS) := this
  rw [← h'] at hY
  simp at hY

/-- **Every complete set of histories at the genuine-radii witness (`k₀ = k_f = T`, horizon
`K = T + 1`) has at least two histories with empty region at the scale `k_f = T`**: the trivial
history and the history in which the ripe component is removed. -/
theorem two_le_card_empty_region_ripeRem
    (hist : Finset (LabHist wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS) (Tstar wS + 1)))
    (hc : IsComplete (Tstar wS) (Tstar wS + 1) hist) :
    2 ≤ (hist.filter (fun A => lastRegion A (Tstar wS) = ∅)).card :=
  two_le_card_empty_region hist hc trivLab remLab trivLab_region remLab_region
    trivLab_not_agree_remLab

end Witness

end Balaban.RootFSpine
