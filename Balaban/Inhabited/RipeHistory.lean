/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.History.InhabitedJoint
public import Balaban.LargeField.History.RipeWindow
public import Balaban.LargeField.R.RemCluster

/-!
# A region history with a ripe component

One large-field cube is created at the step `0 → 1` (a base record with `P = {0}`), and nothing
afterwards: no new cubes, no removed components, radii `R_j = 0`.  At every scale `1 ≤ k ≤ K` the
region `Z^pre_k` has a single component `Z_k`, whose bookkeeping is `Active(1, 1, ∅)` with clock
`s = 1` and a point spine (the single-seed bound of `BookRule.len_gen`); it is therefore ripe at
`k = T := t^*(Active(1,1,∅), s = 1)`, and we take `K = k₀ = T`.  The side lengths are
`n_k = N L^{K-k}` with `N` large enough for `4 ρ_j + 21 ≤ n_j` (hypothesis of `ripe_window`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField

namespace RipeHist

variable (S : Setting) [NeZero S.L] (N K : ℕ) [NeZero N]

/-- The torus sides `n_k = N L^{K-k}`. -/
noncomputable def side (k : ℕ) : ℕ := N * S.L ^ (K - k)

instance side_neZero (k : ℕ) : NeZero (side S N K k) :=
  ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ (NeZero.ne _))⟩

/-- The step from the region `Z`: a single new cube `{0}` in `P` at `k = 0` (`Z = ∅`), otherwise
no new cubes. -/
noncomputable def mkStep (k : ℕ) (Z : Set (Torus S.d (side S N K k))) :
    RegionStep S.d S.L (side S N K k) (side S N K (k + 1))
      (JointWitness.radii (k - 1)) (JointWitness.radii k) where
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

variable (k0 : ℕ)

/-- The regions `Z^pre_k`. -/
noncomputable def regions : ∀ k, Set (Torus S.d (side S N K k))
  | 0 => ∅
  | k + 1 => (mkStep S N K k (regions k)).Zpre (S.omega (k + 1)) (critOpt S k0 (k + 1))

variable {S N K k0}

/-- The flow steps. -/
noncomputable def flowSteps (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) :
    FlowSteps S (side S N K) JointWitness.radii k0 K where
  ok := ok
  s4 := h4
  s5 := h5
  RH := JointWitness.radiusHyp S ok hRb
  hnn := fun k hk => by
    unfold side
    rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]
    ring
  step := fun k => mkStep S N K k (regions S N K k0 k)

theorem flowSteps_Zpre (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) :
    ∀ k, (flowSteps (N := N) (K := K) (k0 := k0) ok h4 h5 hRb).Zpre k = regions S N K k0 k
  | 0 => rfl
  | _ + 1 => rfl

/-- The history. -/
noncomputable def hist (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb) : RegionHistory S (side S N K) JointWitness.radii k0 K where
  F := flowSteps ok h4 h5 hRb
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [flowSteps_Zpre]
    simp [flowSteps, mkStep]

section Comps

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb)

local notation "Hs" => (hist (N := N) (K := K) (k0 := k0) ok h4 h5 hRb)

theorem rem_eq (k : ℕ) : (Hs).rem k = ∅ := rfl

theorem step_zero_Z : ((Hs).step 0).Z = ∅ := rfl

theorem mem_newCubes_succ (k : ℕ) (x : Torus S.d (side S N K (k + 1))) :
    x ∈ (Hs).newCubes (k + 1) ↔ k = 0 ∧ x = 0 := by
  have : (Hs).newCubes (k + 1) = finOf ((Hs).step k).newCubes := rfl
  rw [this, mem_finOf]
  show x ∈ ((mkStep S N K k (regions S N K k0 k)).P ∪ ∅ ∪ ∅ ∪ ∅) ↔ _
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
    have h0 : (0 : Torus S.d (side S N K 1)) ∈ ((Hs).step 0).newCubes :=
      Or.inl (Or.inl (Or.inl ⟨rfl, rfl, rfl⟩))
    have hσ : ({0} : Set (Torus S.d (side S N K 1))) ∈ ((Hs).step 0).seeds (S.omega 0) :=
      Or.inr ⟨0, h0, rfl⟩
    obtain ⟨C, hC, hsub⟩ := ((Hs).step 0).seed_in_comp_Zpre hg.hn hg.hlt (critOpt S k0 1) hσ
    have hmem : ∀ c' : (Hs).Comp 1, (0 : Torus S.d (side S N K 1)) ∈ c'.1 := by
      intro c'
      have h := (Hs).seed_pos (k := 0) (by omega) c'
      have hp : ((Hs).parts 0 c').card = 0 := by
        have : IsEmpty ((Hs).Comp 0) := (Hs).F.isEmpty_comp_zero
        rw [Finset.card_eq_zero]
        exact Finset.eq_empty_of_isEmpty _
      rw [hp, zero_add, Nat.one_le_iff_ne_zero] at h
      obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
      obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
      have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 hRb 0 x).mp hx2
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
      have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 hRb k x).mp (Finset.mem_inter.mp hx).2
      omega
    rw [hn, add_zero] at h
    obtain ⟨y, hy⟩ := Finset.card_pos.mp h
    have hy' := ((Hs).mem_parts k y c').mp hy
    rw [hc y] at hy'
    exact RegionHistory.IsSucc.unique (H := Hs) hy'.2 hZ'

theorem zero_mem_comp_one (c : (Hs).Comp 1) (hK : 1 ≤ K) :
    (0 : Torus S.d (side S N K 1)) ∈ c.1 := by
  have h := (Hs).seed_pos (k := 0) (by omega) c
  have hp : ((Hs).parts 0 c).card = 0 := by
    have : IsEmpty ((Hs).Comp 0) := (Hs).F.isEmpty_comp_zero
    rw [Finset.card_eq_zero]
    exact Finset.eq_empty_of_isEmpty _
  rw [hp, zero_add, Nat.one_le_iff_ne_zero] at h
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  obtain ⟨hx1, hx2⟩ := Finset.mem_inter.mp hx
  have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 hRb 0 x).mp hx2
  rw [this.2] at hx1
  exact hx1

/-- The ripeness time of the book `Active(1, 1, ∅)` with clock `s = 1`. -/
noncomputable def Tstar (S : Setting) : ℕ := max (1 + S.nq 1) (1 + S.n2 1)

omit [NeZero S.L] in
theorem tStar_of {b : Book} (hst : b.st = .active 1 1 ∅) (hs : b.s = 1) :
    S.tStar b = Tstar S := by
  have hq : b.q = 1 := by simp [Book.q, hst]
  simp [Setting.tStar, hq, hs, Tstar]

omit [NeZero S.L] in
theorem not_ripe_of {b : Book} (hst : b.st = .active 1 1 ∅) (hs : b.s = 1) {k : ℕ}
    (hk : k < Tstar S) : ¬ S.Ripe k b := by
  rintro ⟨-, h⟩
  rw [tStar_of hst hs] at h
  omega

theorem book_facts : ∀ k, 1 ≤ k → k ≤ K → k ≤ k0 → k ≤ Tstar S → ∀ c : (Hs).Comp k,
    ((Hs).bk k c).st = .active 1 1 ∅ ∧ ((Hs).bk k c).s = 1 ∧ ((Hs).bk k c).len = 0 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base =>
    intro hK hk0 _ c
    have hr := (Hs).book_rule (k := 0) (by omega) c
    have hr1 : (c.1 ∩ (Hs).newCubes (0 + 1)).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨0, ?_⟩
      ext x
      simp only [Finset.mem_inter, Finset.mem_singleton]
      rw [mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 hRb 0 x]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · rintro rfl; exact ⟨zero_mem_comp_one (N := N) (K := K) (k0 := k0) ok h4 h5 hRb c hK, rfl, rfl⟩
    have hlen : ((Hs).bk 1 c).len = 0 := by
      have h1 := hr.len_gen
      have h2 := hr.len_nonneg
      have hp : (Hs).parts 0 c = ∅ := by
        have : IsEmpty ((Hs).Comp 0) := (Hs).F.isEmpty_comp_zero
        exact Finset.eq_empty_of_isEmpty _
      rw [hp, hr1] at h1
      simp at h1
      linarith
    have hpt : ((Hs).bk 1 c).pt := by
      rw [RegionHistory.bk_pt, ← RegionHistory.bk_len]; exact hlen
    have hst := (hr.state (by omega)).1 (by rw [hr1])
    refine ⟨?_, ?_, hlen⟩
    · rw [hst]; simp [WState.restart, hpt]
    · refine hr.clock_pt_other hpt ?_
      rw [hr1]; simp
  | succ k hk ih =>
    intro hK hk0 hT c'
    obtain ⟨c, hc⟩ := comp_unique (N := N) (K := K) (k0 := k0) ok h4 h5 hRb k hk (by omega)
    obtain ⟨hst, hs, hlen⟩ := ih (by omega) (by omega) (by omega) c
    have hr := (Hs).book_rule (k := k) (by omega) c'
    have hparts : (Hs).parts k c' = {c} := by
      ext y
      rw [(Hs).mem_parts, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -⟩; exact hc y
      · rintro rfl
        obtain ⟨Z', hZ'⟩ := (Hs).exists_succ (k := k) (by omega) (c := y) (by simp [rem_eq])
        obtain ⟨c0, hc0⟩ := comp_unique (N := N) (K := K) (k0 := k0) ok h4 h5 hRb (k + 1) (by omega) (by omega)
        refine ⟨by simp [rem_eq], ?_⟩
        rw [hc0 c']
        have := hc0 Z'
        rw [this] at hZ'
        exact hZ'
    have hnew : (c'.1 ∩ (Hs).newCubes (k + 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 hRb k x).mp (Finset.mem_inter.mp hx).2
      omega
    have hf : S.postBook k0 k ((Hs).bk k c) = (Hs).bk k c := by
      unfold Setting.postBook
      have hn : ¬ (1 ≤ k ∧ k ≤ k0 ∧ S.Ripe k ((Hs).bk k c)) :=
        fun h => not_ripe_of hst hs (by omega) h.2.2
      simp [hn]
    rw [hparts, hnew] at hr
    have hlen' : ((Hs).bk (k + 1) c').len = 0 := by
      have h1 := hr.len_gen
      have h2 := hr.len_nonneg
      simp [hf, hlen] at h1
      linarith
    have hpt : ((Hs).bk (k + 1) c').pt := by
      rw [RegionHistory.bk_pt, ← RegionHistory.bk_len]; exact hlen'
    have hptk : ((Hs).bk k c).pt := by
      rw [RegionHistory.bk_pt, ← RegionHistory.bk_len]; exact hlen
    refine ⟨?_, ?_, hlen'⟩
    · have := ((hr.state (by omega)).2.1 rfl c rfl)
      simp only [hf] at this
      rw [this]; simp [WState.shadow, hst]
    · have hptk' : (S.postBook k0 k ((Hs).bk k c)).pt := by rw [hf]; exact hptk
      have := hr.clock_pt_shadow hpt rfl c rfl hptk'
      simp only [hf] at this
      rw [this, hs]

theorem one_le_Tstar (S : Setting) : 1 ≤ Tstar S := by
  unfold Tstar; exact le_trans (by omega) (le_max_left _ _)

end Comps

section Final

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb)
  (N : ℕ) [NeZero N]

include ok h4 h5 hRb

/-- The history with `K = k₀ = T`. -/
noncomputable abbrev histT : RegionHistory S (side S N (Tstar S)) JointWitness.radii (Tstar S)
    (Tstar S) :=
  hist (N := N) (K := Tstar S) (k0 := Tstar S) ok h4 h5 hRb

/-- The unique component at scale `T` is ripe. -/
theorem exists_ripe : ∃ c : (histT ok h4 h5 hRb N).Comp (Tstar S),
    (∀ c' : (histT ok h4 h5 hRb N).Comp (Tstar S), c' = c) ∧
      S.Ripe (Tstar S) ((histT ok h4 h5 hRb N).bk (Tstar S) c) := by
  obtain ⟨c, hc⟩ := comp_unique (N := N) (K := Tstar S) (k0 := Tstar S) ok h4 h5 hRb
    (Tstar S) (one_le_Tstar S) le_rfl
  obtain ⟨hst, hs, -⟩ := book_facts (N := N) (K := Tstar S) (k0 := Tstar S) ok h4 h5 hRb
    (Tstar S) (one_le_Tstar S) le_rfl le_rfl le_rfl c
  exact ⟨c, hc, ⟨1, 1, ∅, hst⟩, (tStar_of hst hs)⟩

/-- **`RemCluster` has a non-empty member**: a removed cluster consisting of one ripe component of
`Z^pre_T`, with the empty kept configuration. -/
theorem remCluster_exists (M : ℕ) [NeZero M] :
    ∃ (Kc : HistConfig S (side S N (Tstar S)) JointWitness.radii (Tstar S) (Tstar S) M (Tstar S))
      (C : Finset (ConfigPair S (side S N (Tstar S)) M (Tstar S) (Tstar S))),
      RemCluster Kc C := by
  classical
  obtain ⟨c, hc, hrip⟩ := exists_ripe ok h4 h5 hRb N
  have hH : histT ok h4 h5 hRb N ∈ (RegionHistory.historiesWithFinal (R := JointWitness.radii)
      (k0 := Tstar S) (K := Tstar S) (Tstar S) c.1 :
      Set (RegionHistory S (side S N (Tstar S)) JointWitness.radii (Tstar S) (Tstar S))) := by
    have hZp : (histT ok h4 h5 hRb N).F.Zp (Tstar S) = c.1 := by
      ext x
      constructor
      · intro hx
        obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S.omega (Tstar S)) hx
        have := hc ⟨Y, hY⟩
        have h2 : Y = c.1 := congrArg Subtype.val this
        rwa [h2] at hxY
      · intro hx; exact comp_subset c.2 hx
    refine ⟨fun k c0 h => absurd h (by simp [rem_eq]), hZp, ?_⟩
    rw [← hZp]
    ext Y
    rw [Finset.mem_singleton]
    constructor
    · intro hY; exact (congrArg Subtype.val (hc ⟨Y, hY⟩)).trans hZp.symm
    · intro h
      have : Y = c.1 := h.trans hZp
      rw [this]; exact c.2
  refine ⟨HistConfig.empty, {(c.1, (histT ok h4 h5 hRb N).localHistory M (Tstar S) (Tstar S) c)},
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

section Window

variable (S) in
/-- A side factor large enough for `4 ρ_j + 21 ≤ n_j`, `1 ≤ j ≤ T`. -/
noncomputable def bigN : ℕ := 1 + ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21)

variable (S) in
instance bigN_neZero : NeZero (bigN S) := ⟨by unfold bigN; omega⟩

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb)

/-- **`RipeWindow` is inhabited**: the ripe component of the history `histT` (side factor
`bigN S`), for any setting with `S.Good`. -/
theorem ripeWindow_exists (G : S.Good) :
    ∃ c : (histT ok h4 h5 hRb (bigN S)).Comp (Tstar S),
      (histT ok h4 h5 hRb (bigN S)).RipeWindow (Tstar S) c := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 hRb (bigN S)
  refine ⟨c, RegionHistory.ripe_window G ?_ le_rfl le_rfl hrip⟩
  intro k _ hk
  have hk' : k ∈ Finset.range (Tstar S + 1) := Finset.mem_range.mpr (by omega)
  have h1 : 4 * S.rho k + 21 ≤ ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21) :=
    Finset.single_le_sum (f := fun j => 4 * S.rho j + 21) (fun _ _ => Nat.zero_le _) hk'
  have h2 : bigN S ≤ side S (bigN S) (Tstar S) k := by
    unfold side
    exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero (pow_ne_zero _ (NeZero.ne _)))
  have h3 : bigN S = 1 + ∑ j ∈ Finset.range (Tstar S + 1), (4 * S.rho j + 21) := rfl
  omega

end Window

section T4

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (hRb : (4 * S.L + 20 : ℝ) ≤ S.Rb)

include ok h4 h5 hRb

/-- **`T4Facts` is inhabited**: the merge, at scale `T`, of two parts carrying the book of the ripe
component of `histT` (both `Active(1, 1, ∅)` with point spines), provided the cap
`ν_max(T+1) ≥ 2`. -/
theorem t4Facts_exists (G : S.Good) (hcap : 2 ≤ S.numax (Tstar S + 1)) :
    ∃ (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts S (Tstar S) parts f b' := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 hRb (bigN S)
  obtain ⟨hst, -, -⟩ := book_facts (N := bigN S) (K := Tstar S) (k0 := Tstar S) ok h4 h5 hRb
    (Tstar S) (one_le_Tstar S) le_rfl le_rfl le_rfl c
  set b := (histT ok h4 h5 hRb (bigN S)).bk (Tstar S) c with hb
  have hinv : BookInv S (Tstar S) b :=
    ((histT ok h4 h5 hRb (bigN S)).window_inv' G (Tstar S) (one_le_Tstar S) le_rfl le_rfl c).1
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

end T4

end RipeHist

section Concrete

open JointWitness RipeHist

theorem setting_Cν_gt (β : ℝ) : 1 < (setting β).Cν := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcp : 0 < typing0.cPrime := by
    show 0 < (1 + Real.log 2 / (1 * Real.log ((2 : ℕ) : ℝ))) * (1 + 3 * Real.log 2)
    have : ((2 : ℕ) : ℝ) = 2 := by norm_num
    rw [this]
    positivity
  show 1 < typing0.Cr
  have h9 := pow_pos hcp 9
  show 1 < 2 * (1 : ℝ) * typing0.cPrime ^ (9 : ℕ) + 1
  linarith

theorem setting_numax_two (β : ℝ) (hβ : 10 < β) (j : ℕ) : 2 ≤ (setting β).numax j := by
  have hC := setting_Cν_gt β
  have hlam : 1 ≤ (setting β).lam j := (setting_ok β hβ).one_le_lam j
  have hp : (1 : ℝ) ≤ (setting β).lam j ^ (setting β).p2 := one_le_pow₀ hlam
  have : (1 : ℝ) < (setting β).Cν * (setting β).lam j ^ (setting β).p2 := by nlinarith
  unfold Setting.numax
  have := Nat.lt_ceil.mpr (by exact_mod_cast this : ((1 : ℕ) : ℝ) <
    (setting β).Cν * (setting β).lam j ^ (setting β).p2)
  omega

/-- **`RemCluster` is inhabited by a non-empty cluster with a ripe member**, for the setting of
the joint witness (`d = 3`, `L = 2`, `λ_j = log (5β/4) + 1 + j log 2`, `β = jointBeta`). -/
theorem remCluster_nonempty :
    ∃ (n : ℕ → ℕ) (_ : ∀ k, NeZero (n k)) (R : ℕ → ℝ) (k0 K M k : ℕ) (_ : NeZero M)
      (Kc : HistConfig (setting jointBeta) n R k0 K M k)
      (C : Finset (ConfigPair (setting jointBeta) n M K k)), RemCluster Kc C :=
  ⟨side (setting jointBeta) 1 (Tstar (setting jointBeta)), inferInstance, JointWitness.radii,
    Tstar (setting jointBeta), Tstar (setting jointBeta), 1, Tstar (setting jointBeta),
    ⟨one_ne_zero⟩,
    remCluster_exists (setting_ok jointBeta jointBeta_gt) (setting_s4 _) (setting_s5 _)
      (setting_Rb _) 1 1⟩

/-- **`RipeWindow` is inhabited** (a ripe component of a non-empty region history). -/
theorem ripeWindow_nonempty :
    ∃ (n : ℕ → ℕ) (_ : ∀ k, NeZero (n k)) (R : ℕ → ℝ) (k0 K : ℕ)
      (H : RegionHistory (setting jointBeta) n R k0 K) (k : ℕ) (Z : H.Comp k),
      H.RipeWindow k Z := by
  obtain ⟨c, hc⟩ := ripeWindow_exists (setting_ok jointBeta jointBeta_gt) (setting_s4 _)
    (setting_s5 _) (setting_Rb _)
    (setting_good jointBeta jointBeta_gt jointBeta_spec.2.1)
  exact ⟨_, inferInstance, _, _, _, histT (setting_ok jointBeta jointBeta_gt) (setting_s4 _)
    (setting_s5 _) (setting_Rb _) (bigN (setting jointBeta)), _, c, hc⟩

/-- **`T4Facts` is inhabited** (a merge of two ripe-book parts at scale `T`). -/
theorem t4Facts_nonempty :
    ∃ (k : ℕ) (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts (setting jointBeta) k parts f b' := by
  obtain ⟨parts, f, b', h1, h2⟩ := t4Facts_exists (setting_ok jointBeta jointBeta_gt)
    (setting_s4 _) (setting_s5 _) (setting_Rb _)
    (setting_good jointBeta jointBeta_gt jointBeta_spec.2.1)
    (setting_numax_two jointBeta jointBeta_gt _)
  exact ⟨_, parts, f, b', h1, h2⟩

end Concrete

end Balaban.Inhabited
