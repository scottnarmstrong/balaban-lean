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
structure RegionHistory (S : Setting) (n : ℕ → ℕ) [∀ k, NeZero (n k)] (R : ℕ → ℝ) (k0 : ℕ) where
  /-- the steps of the region calculus -/
  F : FlowSteps S n R k0
  /-- the components of `Z^pre_k` removed by `R^{(k)}` -/
  rem : ∀ k, Finset (Finset (Torus S.d (n k)))
  rem_sub : ∀ k, rem k ⊆ comps (S.omega k) (finOf (F.Zpre k))
  rem_empty : ∀ k, (k = 0 ∨ k0 < k) → rem k = ∅
  /-- `Z_k = Z^pre_k ∖ ⋃ Rem_k` -/
  Z_eq : ∀ k, (F.step k).Z = F.Zpre k \ ⋃ c ∈ rem k, (c : Set (Torus S.d (n k)))
  /-- if `Z^pre_k` has a removed component, then `Z^pre_{k+1}` has a component (the abstract
  history `LF2Hyp` has a total successor map) -/
  removed_succ : ∀ k, (rem k).Nonempty → Nonempty (F.Comp (k + 1))

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ}
  (H : RegionHistory S n R k0)

/-- The steps. -/
abbrev step (k : ℕ) := H.F.step k

/-- `Z^pre_k` as a finite set. -/
noncomputable abbrev Zp (k : ℕ) : Finset (Torus S.d (n k)) := H.F.Zp k

/-- The components of `Z^pre_k`. -/
abbrev Comp (k : ℕ) : Type := H.F.Comp k

include H in
theorem stepGeom (k : ℕ) :
    StepGeom S.L (n k) (n (k + 1)) (S.omega k) (S.omega (k + 1)) (S.r k) (R (k - 1)) (R k) :=
  H.F.stepGeom k

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
theorem exists_succ (k : ℕ) {c : H.Comp k} (hc : c.1 ∉ H.rem k) :
    ∃ Z' : H.Comp (k + 1), blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ⊆
      (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
  have hg := H.stepGeom k
  have hσ : blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ∈
      (H.step k).seeds (S.omega k) := Or.inl ⟨c.1, H.comp_mem_Z hc, rfl⟩
  obtain ⟨C, hC, hsub⟩ := (H.step k).seed_in_comp_Zpre hg.hn hg.hlt (critOpt S k0 (k + 1)) hσ
  exact ⟨⟨C, hC⟩, hsub⟩

theorem nonempty_succ (k : ℕ) (c : H.Comp k) : Nonempty (H.Comp (k + 1)) := by
  by_cases hc : c.1 ∈ H.rem k
  · exact H.removed_succ k ⟨c.1, hc⟩
  · obtain ⟨Z', -⟩ := H.exists_succ k hc
    exact ⟨Z'⟩

open Classical in
/-- The successor of a component of `Z^pre_k`: the component of `Z^pre_{k+1}` containing its
coarsening (for removed components, an arbitrary component). -/
noncomputable def succ (k : ℕ) (c : H.Comp k) : H.Comp (k + 1) :=
  if h : ∃ Z' : H.Comp (k + 1), blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ⊆
      (Z'.1 : Set (Torus S.d (n (k + 1)))) then h.choose
  else Classical.choice (H.nonempty_succ k c)

theorem succ_spec (k : ℕ) {c : H.Comp k} (hc : c.1 ∉ H.rem k) :
    blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ⊆
      ((H.succ k c).1 : Set (Torus S.d (n (k + 1)))) := by
  classical
  have h := H.exists_succ k hc
  unfold succ
  split_ifs
  exact h.choose_spec

theorem succ_eq_iff (k : ℕ) {c : H.Comp k} (hc : c.1 ∉ H.rem k) {Z' : H.Comp (k + 1)} :
    H.succ k c = Z' ↔ blockMap S.L (n (k + 1)) '' (c.1 : Set (Torus S.d (n k))) ⊆
      (Z'.1 : Set (Torus S.d (n (k + 1)))) := by
  constructor
  · rintro rfl; exact H.succ_spec k hc
  · intro h
    obtain ⟨x, hx⟩ := comp_nonempty c.2
    have hx' : blockMap S.L (n (k + 1)) x ∈ (H.succ k c).1 := H.succ_spec k hc ⟨x, hx, rfl⟩
    have hx'' : blockMap S.L (n (k + 1)) x ∈ Z'.1 := h ⟨x, hx, rfl⟩
    exact Subtype.ext (comp_eq_of_mem (H.succ k c).2 Z'.2 hx' hx'')

open Classical in
/-- The old parts of a component of `Z^pre_{k+1}`: the non-removed components with this
successor. -/
noncomputable def parts (k : ℕ) (Z' : H.Comp (k + 1)) : Finset (H.Comp k) :=
  Finset.univ.filter fun c => c.1 ∉ H.rem k ∧ H.succ k c = Z'

theorem mem_parts (k : ℕ) (c : H.Comp k) (Z' : H.Comp (k + 1)) :
    c ∈ H.parts k Z' ↔ c.1 ∉ H.rem k ∧ H.succ k c = Z' := by
  classical
  simp [parts]

/-- The new cubes `𝒩_k ⊆ 𝕋_k` (empty for `k = 0`). -/
noncomputable def newCubes : ∀ k, Finset (Torus S.d (n k))
  | 0 => ∅
  | k + 1 => finOf (H.step k).newCubes

end RegionHistory

end Balaban.LargeField
