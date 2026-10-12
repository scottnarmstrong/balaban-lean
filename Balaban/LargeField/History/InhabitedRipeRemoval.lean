module

public import Balaban.Inhabited.RadiiRipe
public import Balaban.Inhabited.RadiiWitnessOps
public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.History.OmegaPost


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


section Final

variable (hT : 1 ≤ Tstar S) (hK : Tstar S ≤ K)

local notation "H2" => (hist2 S R N K ok h4 h5 RH hT)

include hT hK in
/-- The unique component at scale `T` is ripe (LF-RECONSTRUCTION §I.4: `t^* = T`). -/
theorem exists_ripe : ∃ c : (H2).Comp (Tstar S), (∀ c' : (H2).Comp (Tstar S), c' = c) ∧
    S.Ripe (Tstar S) ((H2).bk (Tstar S) c) := by
  obtain ⟨c, hc⟩ := comp_unique (N := N) (K := K) ok h4 h5 RH hT hK (Tstar S) hT le_rfl
  obtain ⟨hst, hs, -⟩ := book_facts (N := N) (K := K) ok h4 h5 RH hT hK (Tstar S) hT le_rfl c
  exact ⟨c, hc, ⟨1, 1, ∅, hst⟩, tStar_of hst hs⟩

include hT hK in
/-- **The removal is admissible**: every removed component is ripe (Definition I.4.1). -/
theorem admissible : (H2).Admissible := by
  intro k c hc
  by_cases hk : k = Tstar S
  · subst hk
    obtain ⟨c0, hc0, hrip⟩ := exists_ripe (N := N) (K := K) ok h4 h5 RH hT hK
    rw [hc0 c]; exact hrip
  · exfalso
    have : (H2).rem k = ∅ := remAt_ne hk
    rw [this] at hc
    exact Finset.notMem_empty _ hc

include hT in
/-- Every component of `Z^pre_T` is removed at scale `T`. -/
theorem mem_rem_T (c : (H2).Comp (Tstar S)) : c.1 ∈ (H2).rem (Tstar S) := by
  have hZ : (H2).F.Zp (Tstar S) = finOf (regions S R N K (Tstar S) (Tstar S)) := by
    show finOf ((flowSteps2 S R N K ok h4 h5 RH).Zpre (Tstar S)) = _
    rw [flowSteps2_Zpre ok h4 h5 RH _ le_rfl]
  have h := c.2
  show c.1 ∈ remAt S R N K (Tstar S)
  generalize c.1 = Y at h ⊢
  rw [hZ] at h
  simp only [remAt, ↓reduceIte]
  exact h

include hT hK in
/-- The removed set at scale `T` is nonempty. -/
theorem rem_nonempty : ((H2).rem (Tstar S)).Nonempty := by
  obtain ⟨c, -, -⟩ := exists_ripe (N := N) (K := K) ok h4 h5 RH hT hK
  exact ⟨c.1, mem_rem_T ok h4 h5 RH hT c⟩


include ok h4 h5 RH hT hK in
/-- **`RemCluster` has a nonempty member whose history is the one with the removal**: the cluster
consisting of the removed ripe component of `Z^pre_T`, with its localized history taken from
the admissible history `hist2` (which itself removes that component), and the empty kept
configuration (Definition III.10.3). -/
theorem remCluster_exists (M : ℕ) [NeZero M] :
    ∃ (Kc : HistConfig S (side S N K) R (Tstar S) K M (Tstar S))
      (C : Finset (ConfigPair S (side S N K) M K (Tstar S))), RemCluster Kc C := by
  classical
  obtain ⟨c, hc, hrip⟩ := exists_ripe (N := N) (K := K) ok h4 h5 RH hT hK
  have hH : H2 ∈ (RegionHistory.historiesWithFinal (R := R) (k0 := Tstar S) (K := K) (Tstar S)
      c.1 : Set (RegionHistory S (side S N K) R (Tstar S) K)) := by
    have hZp : (H2).F.Zp (Tstar S) = c.1 := by
      ext x
      constructor
      · intro hx
        obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega (Tstar S)) hx
        have := hc ⟨Y, hY⟩
        have h2 : Y = c.1 := congrArg Subtype.val this
        rwa [h2] at hxY
      · intro hx; exact comp_subset c.2 hx
    refine ⟨admissible ok h4 h5 RH hT hK, hZp, ?_⟩
    rw [← hZp]
    ext Y
    rw [Finset.mem_singleton]
    constructor
    · intro hY; exact (congrArg Subtype.val (hc ⟨Y, hY⟩)).trans hZp.symm
    · intro h
      have : Y = c.1 := h.trans hZp
      rw [this]; exact c.2
  refine ⟨HistConfig.empty, {(c.1, (H2).localHistory M K (Tstar S) c)},
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

end Final

omit [NeZero S.L] in
/-- Every removed component is nonempty, lies in `Z^pre_k` and is disjoint from `Z_k`
(Definition I.3.11). -/
theorem rem_visible {n : ℕ → ℕ} [∀ k, NeZero (n k)] {k0 K : ℕ} (H : RegionHistory S n R k0 K)
    {k : ℕ} {Y : Finset (Torus S.d (n k))} (hY : Y ∈ H.rem k) :
    Y.Nonempty ∧ (∀ x ∈ Y, x ∈ H.F.Zpre k) ∧ (∀ x ∈ Y, x ∉ (H.step k).Z) := by
  have hc := H.rem_sub k hY
  refine ⟨comp_nonempty hc, fun x hx => mem_finOf.mp (comp_subset hc hx), fun x hx hxZ => ?_⟩
  have h := (H.Z_eq k) ▸ hxZ
  simp only [Set.mem_sdiff, Set.mem_iUnion, Finset.mem_coe, exists_prop] at h
  exact h.2 ⟨Y, hY, hx⟩

section Omega

variable {d L n0 n1 : ℕ} [NeZero L] [NeZero n0] [NeZero n1] {Rp Rk : ℝ}

omit [NeZero L] in
/-- A step whose `Z` is nonempty has `Ω ≠ 𝕋` (the cube over a point of `Z` is not in `Ω'`). -/
theorem step_omega_ne_univ (st : RegionStep d L n0 n1 Rp Rk) (hZ : st.Z.Nonempty) :
    st.Omega ≠ Set.univ := by
  obtain ⟨x, hx⟩ := hZ
  intro h
  have hy : blockMap L n1 x ∈ (Set.univ : Set (Torus d n1)) := Set.mem_univ _
  rw [← h] at hy
  obtain ⟨c, hyc, hsub, -⟩ := hy
  obtain ⟨c', hyc', hle⟩ := hsub hyc
  have hxU : x ∈ Region.U ⌊Rp⌋₊ st.Z := subset_nbhd _ _ hx
  have hyU : blockMap L n1 x ∈ Region.Uprime L n1 ⌊Rp⌋₊ st.Z := ⟨x, hxU, rfl⟩
  have hyF : blockMap L n1 x ∈ nbhd 3 (Region.Uprime L n1 ⌊Rp⌋₊ st.Z) := subset_nbhd _ _ hyU
  have := (le_setDist_iff).mp hle _ hyc' _ hyF
  rw [supDist_self] at this
  omega

end Omega


section Post

variable (hT : 1 ≤ Tstar S) (hK : Tstar S ≤ K)

local notation "H2" => (hist2 S R N K ok h4 h5 RH hT)

omit [NeZero S.L] in
theorem two_le_Tstar : 2 ≤ Tstar S := by
  have := S.one_le_nq 1
  unfold Tstar
  exact le_trans (by omega) (le_max_left _ _)

include hT hK in
/-- **The post-removal domain differs from the raw one** (T3): at the removal scale `T`,
`Ω_T^post ≠ Ω_T^pre`.  Indeed `(Ω_T^pre)ᶜ ⊆ Z^(0)_T ⊆ Z^pre_T = ⋃ Rem_T`, and `Ω_T^pre ≠ 𝕋_T`
because the previous region `Z_{T-1}` is nonempty. -/
theorem omegaPost_ne_OmegaCube :
    (H2).omegaPost (Tstar S) ≠ Def7.OmegaCube (H2) (Tstar S) := by
  have key : ∀ k, k = Tstar S → 2 ≤ k → (H2).omegaPost k ≠ Def7.OmegaCube (H2) k := by
    intro k hk hk2
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨c, -⟩ := comp_unique (N := N) (K := K) ok h4 h5 RH hT hK j (by omega) (by omega)
    obtain ⟨x, hx⟩ := comp_nonempty c.2
    have hxZ : x ∈ ((H2).step j).Z := by
      have h1 : x ∈ (H2).F.Zpre j := mem_finOf.mp (comp_subset c.2 hx)
      have h2 : (H2).F.Zpre j = regions S R N K (Tstar S) j :=
        flowSteps2_Zpre ok h4 h5 RH j (by omega)
      show x ∈ (stepAt S R N K j (regs S R N K j)).Z
      rw [stepAt_Z, regs_eq j (by omega)]
      rwa [h2] at h1
    obtain ⟨y, hy⟩ := (Set.ne_univ_iff_exists_notMem _).1
      (step_omega_ne_univ ((H2).step j) ⟨x, hxZ⟩)
    have hyZpre : y ∈ (H2).F.Zp (j + 1) :=
      mem_finOf.mpr (((H2).step j).Z0_subset_Zpre _ _ (((H2).step j).Omega_compl_subset_Z0 hy))
    obtain ⟨Y, hY, hyY⟩ := mem_comp_self (ω := S.omega (j + 1)) hyZpre
    have hYrem : Y ∈ (H2).rem (j + 1) := by
      show Y ∈ remAt S R N K (j + 1)
      have h2 : (H2).F.Zp (j + 1) = finOf (regions S R N K (Tstar S) (j + 1)) := by
        show finOf ((flowSteps2 S R N K ok h4 h5 RH).Zpre (j + 1)) = _
        rw [flowSteps2_Zpre ok h4 h5 RH _ (by omega)]
      rw [h2] at hY
      unfold remAt
      split_ifs
      exact hY
    intro heq
    have : y ∈ (H2).omegaPost (j + 1) :=
      Or.inr (RegionHistory.mem_removedSet_iff (H2) |>.mpr ⟨Y, hYrem, hyY⟩)
    rw [heq] at this
    exact hy this
  exact key _ rfl (two_le_Tstar)

end Post


/-! ### The concrete history -/

section Concrete

open RadiiSet

/-- **The admissible history with a ripe removal**: the genuine-radii setting `wS` (`d = L = 3`,
`R_j = R_base λ_j²`, `M = 14 M₁`), side factor `bigN wS`, `k₀ = T`, horizon `K = T + 1`;
the single component of `Z^pre_T` is removed at scale `T`. -/
noncomputable def ripeRemHistory :
    RegionHistory wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS) (Tstar wS + 1) :=
  hist2 wS wR (bigN wS) (Tstar wS + 1) wS_ok le_rfl le_rfl wRH (one_le_Tstar _)

theorem ripeRemHistory_admissible : ripeRemHistory.Admissible :=
  admissible (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH (one_le_Tstar _)
    (Nat.le_succ _)

theorem ripeRemHistory_rem_nonempty : (ripeRemHistory.rem (Tstar wS)).Nonempty :=
  rem_nonempty (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH (one_le_Tstar _)
    (Nat.le_succ _)

/-- **An admissible region history with a nonempty removed set** (Definition I.4.1): some
`1 ≤ k ≤ k₀` has `Rem_k ≠ ∅`, and every removed component is ripe. -/
theorem exists_admissible_regionHistory_rem :
    ∃ (S : Setting) (n : ℕ → ℕ) (_ : ∀ k, NeZero (n k)) (R : ℕ → ℝ) (k0 K : ℕ)
      (H : RegionHistory S n R k0 K),
      (∃ k, 1 ≤ k ∧ k ≤ k0 ∧ (H.rem k).Nonempty) ∧ H.Admissible :=
  ⟨wS, _, inferInstance, wR, Tstar wS, Tstar wS + 1, ripeRemHistory,
    ⟨Tstar wS, one_le_Tstar _, le_rfl, ripeRemHistory_rem_nonempty⟩, ripeRemHistory_admissible⟩

/-- **The removal is visible** (T3): a removed component is nonempty, lies in `Z^pre_T`, and is
disjoint from `Z_T`. -/
theorem ripeRemHistory_visible : ∃ Y ∈ ripeRemHistory.rem (Tstar wS),
    Y.Nonempty ∧ (∀ x ∈ Y, x ∈ ripeRemHistory.F.Zpre (Tstar wS)) ∧
      (∀ x ∈ Y, x ∉ (ripeRemHistory.step (Tstar wS)).Z) :=
  let ⟨Y, hY⟩ := ripeRemHistory_rem_nonempty
  ⟨Y, hY, rem_visible ripeRemHistory hY⟩

/-- **`Ω_T^post ≠ Ω_T^pre`** for the history with the removal (T3). -/
theorem ripeRemHistory_omegaPost_ne :
    ripeRemHistory.omegaPost (Tstar wS) ≠ Def7.OmegaCube ripeRemHistory (Tstar wS) :=
  omegaPost_ne_OmegaCube (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH
    (one_le_Tstar _) (Nat.le_succ _)

/-- **The window of the removed ripe component** (T4): the unique component `Z` of `Z^pre_T` is
removed and ripe, it has the geometric window of Lemma III.1.2 (`RipeWindow`), and the window pieces
`windowOfHistory` built from the geometry datum `RadiiSet.wGeo` (`M = 14 M₁`, `R_j ≥ R_base`) satisfy
`WindowPieces.Hyp`. -/
theorem ripeRemHistory_windowOfHistory_hyp :
    ∃ Z : ripeRemHistory.Comp (Tstar wS), Z.1 ∈ ripeRemHistory.rem (Tstar wS) ∧
      wS.Ripe (Tstar wS) (ripeRemHistory.bk (Tstar wS) Z) ∧
      ∃ hW : ripeRemHistory.RipeWindow (Tstar wS) Z,
        (RegionHistory.windowOfHistory ripeRemHistory Z (wGeo _) (Nat.le_succ _) hW).Hyp := by
  obtain ⟨c, -, hrip⟩ := exists_ripe (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH
    (one_le_Tstar _) (Nat.le_succ _)
  have hW : ripeRemHistory.RipeWindow (Tstar wS) c := by
    refine RegionHistory.ripe_window wS_good ?_ le_rfl (Nat.le_succ _) hrip
    intro k _ hk
    have hk' : k ∈ Finset.range (Tstar wS + 1) := Finset.mem_range.mpr (by omega)
    have h1 : 4 * wS.rho k + 21 ≤ ∑ j ∈ Finset.range (Tstar wS + 1), (4 * wS.rho j + 21) :=
      Finset.single_le_sum (f := fun j => 4 * wS.rho j + 21) (fun _ _ => Nat.zero_le _) hk'
    have h2 : bigN wS ≤ side wS (bigN wS) (Tstar wS + 1) k := by
      unfold RadiiHist.side
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
    have h3 : bigN wS = 1 + ∑ j ∈ Finset.range (Tstar wS + 1), (4 * wS.rho j + 21) := rfl
    omega
  exact ⟨c, mem_rem_T (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH
    (one_le_Tstar _) c, hrip, hW, RegionHistory.windowOfHistory_hyp _ hW⟩

/-- **`RemCluster` for the history with the removal** (genuine radii, `M = 14 M₁`). -/
theorem ripeRem_remCluster :
    ∃ (Kc : HistConfig wS (side wS (bigN wS) (Tstar wS + 1)) wR (Tstar wS) (Tstar wS + 1)
        wS.M (Tstar wS))
      (C : Finset (ConfigPair wS (side wS (bigN wS) (Tstar wS + 1)) wS.M (Tstar wS + 1)
        (Tstar wS))), RemCluster Kc C :=
  remCluster_exists (N := bigN wS) (K := Tstar wS + 1) wS_ok le_rfl le_rfl wRH
    (one_le_Tstar _) (Nat.le_succ _) wS.M

end Concrete

end RipeRemoval

end Balaban.Inhabited
