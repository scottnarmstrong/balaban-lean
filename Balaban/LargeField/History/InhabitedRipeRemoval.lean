module

public import Balaban.Inhabited.RadiiRipe


/-!
# An admissible region history with a ripe removal (Definition I.4.1)

The ripe-component history of `RadiiHist` (one large-field cube created at the step `0 → 1`,
nothing afterwards) has a single component `Z_k` of `Z^pre_k` at every scale `1 ≤ k ≤ T`, with
book `Active(1, 1, ∅)` and clock `s = 1`.  (T1 lifetime: the cube is created at scale `1` (a
restart, `Active(1,1,∅)` as the spine is a point), stays quiet - no new cube, one part, the
(T1)-shadow of an active point-spine book keeps `Active(1,1,∅)` and `s = 1` - and the book is
ripe at the first scale `k` with `t^*(b) = k`, namely `k = T := max (1 + nq 1) (1 + n2 1)`; before
that `t^* = T > k` so it is not ripe.)  Here the history is modified at scale `T` only: the
component is removed, `Rem_T = comps Z^pre_T`, `Z_T = Z^pre_T ∖ ⋃ Rem_T = ∅`, and the steps from
scale `T` on have no new cubes.  The books of scales `≤ T` only depend on the data below `T`, so
the component is still ripe: the removal is admissible (LF-RECONSTRUCTION §I.4, Definition I.4.1).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField RadiiHist

namespace RipeRemoval

variable {S : Setting} [NeZero S.L] {R : ℕ → ℝ} {N K : ℕ} [NeZero N]

variable (S R N K) in
/-- The step at scale `k` from the region `Z`: the ripe-history step below `T`, and no new cubes
from `T` on. -/
noncomputable def stepAt (k : ℕ) (Z : Set (Torus S.d (side S N K k))) :
    RegionStep S.d S.L (side S N K k) (side S N K (k + 1)) (R (k - 1)) (R k) :=
  if k < Tstar S then mkStep S R N K k Z else RegionHistory.emptyStep S (side S N K) R k Z

omit [NeZero N] in
theorem stepAt_Z (k : ℕ) (Z : Set (Torus S.d (side S N K k))) :
    (stepAt S R N K k Z).Z = Z := by
  unfold stepAt; split_ifs <;> rfl

omit [NeZero N] in
theorem stepAt_lt {k : ℕ} (hk : k < Tstar S) (Z : Set (Torus S.d (side S N K k))) :
    stepAt S R N K k Z = mkStep S R N K k Z := by
  simp only [stepAt, hk, ↓reduceIte]

variable (S R N K) in
open Classical in
/-- The removed components: all components of `Z^pre_T` (there is one), at scale `T` only. -/
noncomputable def remAt (k : ℕ) : Finset (Finset (Torus S.d (side S N K k))) :=
  if k = Tstar S then comps (S.omega k) (finOf (regions S R N K (Tstar S) k)) else ∅

theorem remAt_ne {k : ℕ} (hk : k ≠ Tstar S) : remAt S R N K k = ∅ := by
  simp only [remAt, hk, ↓reduceIte]

variable (S R N K) in
/-- The regions `Z_k = Z^pre_k ∖ ⋃ Rem_k`. -/
noncomputable def regs : ∀ k, Set (Torus S.d (side S N K k))
  | 0 => ∅
  | k + 1 => (stepAt S R N K k (regs k)).Zpre (S.omega (k + 1)) (critOpt S (Tstar S) (k + 1))
      \ ⋃ Y ∈ remAt S R N K (k + 1), (Y : Set (Torus S.d (side S N K (k + 1))))

theorem regs_eq : ∀ k, k < Tstar S → regs S R N K k = regions S R N K (Tstar S) k
  | 0, _ => rfl
  | k + 1, hk => by
    have ih := regs_eq k (by omega)
    show (stepAt S R N K k (regs S R N K k)).Zpre _ _ \ _ = (mkStep S R N K k (regions S R N K (Tstar S) k)).Zpre _ _
    rw [stepAt_lt (by omega), ih, remAt_ne (by omega)]
    simp

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (RH : RadiusHyp S.L S.Rb S.lam R)

variable (S R N K) in
/-- The flow steps. -/
noncomputable def flowSteps2 (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) : FlowSteps S (side S N K) R (Tstar S) K where
  ok := ok
  s4 := h4
  s5 := h5
  RH := RH
  hnn := fun k hk => by
    unfold RadiiHist.side
    rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]
    ring
  step := fun k => stepAt S R N K k (regs S R N K k)

theorem flowSteps2_Zpre : ∀ k, k ≤ Tstar S →
    (flowSteps2 S R N K ok h4 h5 RH).Zpre k = regions S R N K (Tstar S) k
  | 0, _ => rfl
  | k + 1, hk => by
    show (stepAt S R N K k (regs S R N K k)).Zpre _ _ = (mkStep S R N K k (regions S R N K (Tstar S) k)).Zpre _ _
    rw [stepAt_lt (by omega), regs_eq k (by omega)]

variable (S R N K) in
/-- **The history with a ripe removal**: `RadiiHist.hist` (with `k₀ = T`) up to scale `T`, then
`Rem_T = comps Z^pre_T` and no new cubes. -/
noncomputable def hist2 (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) (hT : 1 ≤ Tstar S) :
    RegionHistory S (side S N K) R (Tstar S) K where
  F := flowSteps2 S R N K ok h4 h5 RH
  rem := remAt S R N K
  rem_sub := fun k => by
    by_cases hk : k = Tstar S
    · subst hk
      rw [flowSteps2_Zpre ok h4 h5 RH _ le_rfl]
      simp only [remAt, ↓reduceIte]; exact Finset.Subset.refl _
    · rw [remAt_ne hk]; exact Finset.empty_subset _
  rem_empty := fun k hk => by
    apply remAt_ne; omega
  Z_eq := fun k => by
    cases k with
    | zero =>
      show (stepAt S R N K 0 (regs S R N K 0)).Z = (∅ : Set _) \ _
      rw [stepAt_Z]; simp [regs]
    | succ j =>
      show (stepAt S R N K (j + 1) (regs S R N K (j + 1))).Z = _
      rw [stepAt_Z]; rfl


section Comps

variable (hT : 1 ≤ Tstar S) (hK : Tstar S ≤ K)

local notation "H2" => (hist2 S R N K ok h4 h5 RH hT)

include hT in
theorem rem_lt {k : ℕ} (hk : k < Tstar S) : (H2).rem k = ∅ := remAt_ne (by omega)

include hT in
theorem step_lt {k : ℕ} (hk : k < Tstar S) :
    (H2).step k = mkStep S R N K k (regions S R N K (Tstar S) k) := by
  show stepAt S R N K k (regs S R N K k) = _
  rw [stepAt_lt hk, regs_eq k hk]

include hT in
theorem mem_newCubes_succ {k : ℕ} (hk : k < Tstar S) (x : Torus S.d (side S N K (k + 1))) :
    x ∈ (H2).newCubes (k + 1) ↔ k = 0 ∧ x = 0 := by
  have : (H2).newCubes (k + 1) = finOf ((H2).step k).newCubes := rfl
  rw [this, mem_finOf, step_lt ok h4 h5 RH hT hk]
  show x ∈ ((mkStep S R N K k (regions S R N K (Tstar S) k)).P ∪ ∅ ∪ ∅ ∪ ∅) ↔ _
  simp only [Set.union_empty, mkStep, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨rfl, h3⟩; exact ⟨rfl, rfl, h3⟩

include hT hK in
theorem comp_unique : ∀ k, 1 ≤ k → k ≤ Tstar S → ∃ c : (H2).Comp k, ∀ c' : (H2).Comp k, c' = c := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hKk
    have hg := (H2).stepGeom (k := 0) (by omega)
    have h0 : (0 : Torus S.d (side S N K 1)) ∈ ((H2).step 0).newCubes := by
      rw [step_lt ok h4 h5 RH hT (by omega)]
      exact Or.inl (Or.inl (Or.inl ⟨rfl, rfl, rfl⟩))
    have hσ : ({0} : Set (Torus S.d (side S N K 1))) ∈ ((H2).step 0).seeds (S.omega 0) :=
      Or.inr ⟨0, h0, rfl⟩
    obtain ⟨C, hC, hsub⟩ := ((H2).step 0).seed_in_comp_Zpre hg.hn hg.hlt (critOpt S (Tstar S) 1) hσ
    have hmem : ∀ c' : (H2).Comp 1, (0 : Torus S.d (side S N K 1)) ∈ c'.1 := by
      intro c'
      have h := (H2).seed_pos (k := 0) (by omega) c'
      have hp : ((H2).parts 0 c').card = 0 := by
        have : IsEmpty ((H2).Comp 0) := (H2).F.isEmpty_comp_zero
        rw [Finset.card_eq_zero]
        exact Finset.eq_empty_of_isEmpty _
      rw [hp, zero_add, Nat.one_le_iff_ne_zero] at h
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have := (mem_newCubes_succ ok h4 h5 RH hT (k := 0) (by omega) x).mp hx2
      rw [this.2] at hx1
      exact hx1
    refine ⟨⟨C, hC⟩, fun c' => Subtype.ext ?_⟩
    exact comp_eq_of_mem c'.2 hC (hmem c') (hsub rfl)
  | succ k hk ih =>
    intro hKk
    obtain ⟨c, hc⟩ := ih (by omega)
    obtain ⟨Z', hZ'⟩ := (H2).exists_succ (k := k) (by omega) (c := c)
      (by rw [rem_lt ok h4 h5 RH hT (by omega)]; simp)
    refine ⟨Z', fun c' => ?_⟩
    have h := (H2).seed_pos (k := k) (by omega) c'
    have hn : (c'.1 ∩ (H2).newCubes (k + 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := (mem_newCubes_succ ok h4 h5 RH hT (k := k) (by omega) x).mp (Finset.mem_inter.mp hx).2
      omega
    rw [hn, add_zero] at h
    obtain ⟨y, hy⟩ := Finset.card_pos.mp h
    have hy' := ((H2).mem_parts k y c').mp hy
    rw [hc y] at hy'
    exact RegionHistory.IsSucc.unique (H := H2) hy'.2 hZ'

include hT in
theorem zero_mem_comp_one (c : (H2).Comp 1) (hK : 1 ≤ K) :
    (0 : Torus S.d (side S N K 1)) ∈ c.1 := by
  have h := (H2).seed_pos (k := 0) (by omega) c
  have hp : ((H2).parts 0 c).card = 0 := by
    have : IsEmpty ((H2).Comp 0) := (H2).F.isEmpty_comp_zero
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_isEmpty _
  rw [hp, zero_add, Nat.one_le_iff_ne_zero] at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  have := (mem_newCubes_succ ok h4 h5 RH hT (k := 0) (by omega) x).mp hx2
  rw [this.2] at hx1
  exact hx1

include hT hK in
theorem book_facts : ∀ k, 1 ≤ k → k ≤ Tstar S → ∀ c : (H2).Comp k,
    ((H2).bk k c).st = .active 1 1 ∅ ∧ ((H2).bk k c).s = 1 ∧ ((H2).bk k c).len = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hk0 c
    have hr := (H2).book_rule (k := 0) (by omega) c
    have hr1 : (c.1 ∩ (H2).newCubes (0 + 1)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton]
      rw [mem_newCubes_succ ok h4 h5 RH hT (k := 0) (by omega) x]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · rintro rfl
        exact ⟨zero_mem_comp_one ok h4 h5 RH hT c (by omega), rfl, rfl⟩
    have hlen : ((H2).bk 1 c).len = 0 := by
      have h1 := hr.len_gen
      have h2 := hr.len_nonneg
      have hp : (H2).parts 0 c = ∅ := by
        have : IsEmpty ((H2).Comp 0) := (H2).F.isEmpty_comp_zero
        exact Finset.eq_empty_of_isEmpty _
      rw [hp, hr1] at h1
      simp at h1
      linarith
    have hpt : ((H2).bk 1 c).pt := by
      rw [RegionHistory.bk_pt, ← RegionHistory.bk_len]; exact hlen
    have hst := (hr.state (by omega)).1 (by rw [hr1])
    refine ⟨?_, ?_, hlen⟩
    · rw [hst]; simp [WState.restart, hpt]
    · refine hr.clock_pt_other hpt ?_
      rw [hr1]; simp
  | succ k hk ih =>
    intro hk0 c'
    obtain ⟨c, hc⟩ := comp_unique (N := N) (K := K) ok h4 h5 RH hT hK k hk (by omega)
    obtain ⟨hst, hs, hlen⟩ := ih (by omega) c
    have hr := (H2).book_rule (k := k) (by omega) c'
    have hparts : (H2).parts k c' = {c} := by
      ext y
      rw [(H2).mem_parts, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -⟩; exact hc y
      · rintro rfl
        obtain ⟨Z', hZ'⟩ := (H2).exists_succ (k := k) (by omega) (c := y)
          (by rw [rem_lt ok h4 h5 RH hT (by omega)]; simp)
        obtain ⟨c0, hc0⟩ := comp_unique (N := N) (K := K) ok h4 h5 RH hT hK (k + 1) (by omega) hk0
        refine ⟨by rw [rem_lt ok h4 h5 RH hT (by omega)]; simp, ?_⟩
        rw [hc0 c']
        have := hc0 Z'
        rw [this] at hZ'
        exact hZ'
    have hnew : (c'.1 ∩ (H2).newCubes (k + 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := (mem_newCubes_succ ok h4 h5 RH hT (k := k) (by omega) x).mp (Finset.mem_inter.mp hx).2
      omega
    have hf : S.postBook (Tstar S) k ((H2).bk k c) = (H2).bk k c := by
      unfold Setting.postBook
      have hn : ¬ (1 ≤ k ∧ k ≤ Tstar S ∧ S.Ripe k ((H2).bk k c)) :=
        fun h => not_ripe_of hst hs (by omega) h.2.2
      simp [hn]
    rw [hparts, hnew] at hr
    have hlen' : ((H2).bk (k + 1) c').len = 0 := by
      have h1 := hr.len_gen
      have h2 := hr.len_nonneg
      simp [hf, hlen] at h1
      linarith
    have hpt : ((H2).bk (k + 1) c').pt := by
      rw [RegionHistory.bk_pt, ← RegionHistory.bk_len]; exact hlen'
    have hptk : ((H2).bk k c).pt := by
      rw [RegionHistory.bk_pt, ← RegionHistory.bk_len]; exact hlen
    refine ⟨?_, ?_, hlen'⟩
    · have := ((hr.state (by omega)).2.1 rfl c rfl)
      simp only [hf] at this
      rw [this]; simp [WState.shadow, hst]
    · have hptk' : (S.postBook (Tstar S) k ((H2).bk k c)).pt := by rw [hf]; exact hptk
      have := hr.clock_pt_shadow hpt rfl c rfl hptk'
      simp only [hf] at this
      rw [this, hs]

end Comps

end RipeRemoval

end Balaban.Inhabited
