module

public import Balaban.LargeField.History.FlowSteps
public import Balaban.LargeField.History.CompsRemove
public import Balaban.LargeField.History.NextBook
import Mathlib.Tactic.Linarith

/-!
# Region histories (Part I, Definitions I.4.1-I.4.2)

A `RegionHistory` consists of the steps of the region calculus (`FlowSteps`) and, for each scale
`k`, the set `Rem_k` of removed components of `Z^pre_k` (empty unless `1 ≤ k ≤ k₀`), with
`Z_k = Z^pre_k ∖ ⋃ Rem_k`.  The successor of a component of `Z^pre_k` is the component of
`Z^pre_{k+1}` containing its coarsening (Lemma I.3.7 (a)), the parts of a component `Z'` of
`Z^pre_{k+1}` are the non-removed components with successor `Z'`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban

/-- A region history up to all scales (Definition I.4.1), without the ripeness condition on the
removed components (which refers to the bookkeeping derived from the history,
`RegionHistory.Admissible`). -/
structure RegionHistory (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 K : ℕ) where
  /-- the steps of the region calculus (with the horizon `K`) -/
  F : FlowSteps S n R k0 K
  /-- the components of `Z^pre_k` removed by `R^{(k)}` -/
  rem : ∀ k, Finset (Finset (Torus S.d (n k)))
  rem_sub : ∀ k, rem k ⊆ comps (S.omega k) (finOf (F.Zpre k))
  rem_empty : ∀ k, (k = 0 ∨ k0 < k) → rem k = ∅
  /-- `Z_k = Z^pre_k ∖ ⋃ Rem_k` -/
  Z_eq : ∀ k, (F.step k).Z = F.Zpre k \ ⋃ c ∈ rem k, (c : Set (Torus S.d (n k)))

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ}
  (H : RegionHistory S n R k0 K)

/-- The steps. -/
abbrev step (k : ℕ) := H.F.step k

/-- `Z^pre_k` as a finite set. -/
noncomputable abbrev Zp (k : ℕ) : Finset (Torus S.d (n k)) := H.F.Zp k

/-- The components of `Z^pre_k`. -/
abbrev Comp (k : ℕ) : Type := H.F.Comp k

include H in
theorem stepGeom {k : ℕ} (hk : k < K) :
    StepGeom S.L (n k) (n (k + 1)) (S.omega k) (S.omega (k + 1)) (S.r k) (R (k - 1)) (R k) :=
  H.F.stepGeom hk

theorem finOf_Z (k : ℕ) : finOf (H.step k).Z = H.Zp k \ (H.rem k).biUnion id := by
  ext x
  simp only [H.Z_eq, mem_finOf, Set.mem_sdiff, Set.mem_iUnion, Finset.mem_sdiff,
    Finset.mem_biUnion, id, exists_prop, Finset.mem_coe]

theorem mem_comps_Z (k : ℕ) {Y : Finset (Torus S.d (n k))} :
    Y ∈ comps (S.omega k) (finOf (H.step k).Z) ↔ Y ∈ comps (S.omega k) (H.Zp k) ∧ Y ∉ H.rem k := by
  rw [H.finOf_Z, mem_comps_sdiff (H.rem_sub k)]

theorem comp_mem_Z {k : ℕ} {c : H.Comp k} (hc : c.1 ∉ H.rem k) :
    c.1 ∈ comps (S.omega k) (finOf (H.step k).Z) :=
  (H.mem_comps_Z k).mpr ⟨c.2, hc⟩

/-- A non-removed component has a successor: its coarsening lies in a component of `Z^pre_{k+1}`
(Lemma I.3.7 (a)). -/
theorem exists_succ {k : ℕ} (hk : k < K) {c : H.Comp k} (hc : c.1 ∉ H.rem k) :
    ∃ Z' : H.Comp (k + 1), blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ⊆
      (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
  have hg := H.stepGeom hk
  have hσ : blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ∈
      (H.step k).seeds (S.omega k) := Or.inl ⟨c.1, H.comp_mem_Z hc, rfl⟩
  obtain ⟨C, hC, hsub⟩ := (H.step k).seed_in_comp_Zpre hg.hn hg.hlt (critOpt S k0 (k + 1)) hσ
  exact ⟨⟨C, hC⟩, hsub⟩

/-- `Z'` is the successor of `c` (a component of `Z^pre_k`): the coarsening of `c` lies in `Z'`. -/
abbrev IsSucc (k : ℕ) (c : H.Comp k) (Z' : H.Comp (k + 1)) : Prop :=
  blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ⊆
    (Z'.1 : Set (Torus S.d (n (k + 1))))

theorem IsSucc.unique {k : ℕ} {c : H.Comp k} {Z Z' : H.Comp (k + 1)} (h : H.IsSucc k c Z)
    (h' : H.IsSucc k c Z') : Z = Z' := by
  obtain ⟨x, hx⟩ := comp_nonempty c.2
  exact Subtype.ext (comp_eq_of_mem Z.2 Z'.2 (h ⟨x, hx, rfl⟩) (h' ⟨x, hx, rfl⟩))

/-- The successor of a non-removed component of `Z^pre_k` (below the horizon `k < K`): the
component of `Z^pre_{k+1}` containing its coarsening. -/
noncomputable def succ {k : ℕ} (hk : k < K) (c : H.Comp k) (hc : c.1 ∉ H.rem k) : H.Comp (k + 1) :=
  (H.exists_succ hk hc).choose

theorem succ_spec {k : ℕ} (hk : k < K) {c : H.Comp k} (hc : c.1 ∉ H.rem k) :
    H.IsSucc k c (H.succ hk c hc) :=
  (H.exists_succ hk hc).choose_spec

theorem succ_eq_iff {k : ℕ} (hk : k < K) {c : H.Comp k} (hc : c.1 ∉ H.rem k)
    {Z' : H.Comp (k + 1)} : H.succ hk c hc = Z' ↔ H.IsSucc k c Z' := by
  constructor
  · rintro rfl; exact H.succ_spec hk hc
  · intro h
    obtain ⟨x, hx⟩ := comp_nonempty c.2
    have hx' : blockMap S.L (n (k + 1)) x ∈ (H.succ hk c hc).1 := H.succ_spec hk hc ⟨x, hx, rfl⟩
    have hx'' : blockMap S.L (n (k + 1)) x ∈ Z'.1 := h ⟨x, hx, rfl⟩
    exact Subtype.ext (comp_eq_of_mem (H.succ hk c hc).2 Z'.2 hx' hx'')

open Classical in
/-- The old parts of a component of `Z^pre_{k+1}`: the non-removed components of `Z^pre_k` whose
coarsening lies in it (below the horizon these are the non-removed components with this
successor, `mem_parts_iff_succ`). -/
noncomputable def parts (k : ℕ) (Z' : H.Comp (k + 1)) : Finset (H.Comp k) :=
  Finset.univ.filter fun c => c.1 ∉ H.rem k ∧ H.IsSucc k c Z'

theorem mem_parts (k : ℕ) (c : H.Comp k) (Z' : H.Comp (k + 1)) :
    c ∈ H.parts k Z' ↔ c.1 ∉ H.rem k ∧ H.IsSucc k c Z' := by
  classical
  simp [parts]

theorem mem_parts_iff_succ {k : ℕ} (hk : k < K) (c : H.Comp k) (Z' : H.Comp (k + 1)) :
    c ∈ H.parts k Z' ↔ ∃ hc : c.1 ∉ H.rem k, H.succ hk c hc = Z' := by
  rw [H.mem_parts]
  constructor
  · rintro ⟨hc, h⟩
    exact ⟨hc, (H.succ_eq_iff hk hc).mpr h⟩
  · rintro ⟨hc, h⟩
    exact ⟨hc, (H.succ_eq_iff hk hc).mp h⟩

/-- The new cubes `𝒩_k ⊆ 𝕋_k` (empty for `k = 0`). -/
noncomputable def newCubes : ∀ k, Finset (Torus S.d (n k))
  | 0 => ∅
  | k + 1 => finOf (H.step k).newCubes

end RegionHistory

end Balaban.LargeField
