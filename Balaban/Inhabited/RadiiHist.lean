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

This is `RipeHistory.lean` with the radii left arbitrary subject to the radius hypotheses (RH):
the proofs never use the size of `R`.  One large-field cube is created at the step `0 → 1` (a
base record with `P = {0}`), and nothing afterwards: no new cubes, no removed components.  At every scale `1 ≤ k ≤ K` the
region `Z^pre_k` has a single component `Z_k`, whose bookkeeping is `Active(1, 1, ∅)` with clock
`s = 1` and a point spine (the single-seed bound of `BookRule.len_gen`); it is therefore ripe at
`k = T := t^*(Active(1,1,∅), s = 1)`, and we take `K = k₀ = T`.  The side lengths are
`n_k = N L^{K-k}` with `N` large enough for `4 ρ_j + 21 ≤ n_j` (hypothesis of `ripe_window`).
-/

@[expose] public section

namespace Balaban.Inhabited

open Balaban Balaban.LargeField

namespace RadiiHist

variable (S : Setting) [NeZero S.L] (R : ℕ → ℝ) (N K : ℕ) [NeZero N]

/-- The torus sides `n_k = N L^{K-k}`. -/
noncomputable def side (k : ℕ) : ℕ := N * S.L ^ (K - k)

instance side_neZero (k : ℕ) : NeZero (side S N K k) :=
  ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ (NeZero.ne _))⟩

/-- The step from the region `Z`: a single new cube `{0}` in `P` at `k = 0` (`Z = ∅`), otherwise
no new cubes. -/
noncomputable def mkStep (k : ℕ) (Z : Set (Torus S.d (side S N K k))) :
    RegionStep S.d S.L (side S N K k) (side S N K (k + 1))
      (R (k - 1)) (R k) where
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
  | k + 1 => (mkStep S R N K k (regions k)).Zpre (S.omega (k + 1)) (critOpt S k0 (k + 1))

variable {S R N K k0}

/-- The flow steps. -/
noncomputable def flowSteps (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) :
    FlowSteps S (side S N K) R k0 K where
  ok := ok
  s4 := h4
  s5 := h5
  RH := RH
  hnn := fun k hk => by
    unfold side
    rw [show K - k = (K - (k + 1)) + 1 by omega, pow_succ]
    ring
  step := fun k => mkStep S R N K k (regions S R N K k0 k)

theorem flowSteps_Zpre (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) :
    ∀ k, (flowSteps (N := N) (K := K) (k0 := k0) ok h4 h5 RH).Zpre k = regions S R N K k0 k
  | 0 => rfl
  | _ + 1 => rfl

/-- The history. -/
noncomputable def hist (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP)
    (RH : RadiusHyp S.L S.Rb S.lam R) : RegionHistory S (side S N K) R k0 K where
  F := flowSteps ok h4 h5 RH
  rem := fun _ => ∅
  rem_sub := fun _ => Finset.empty_subset _
  rem_empty := fun _ _ => rfl
  Z_eq := fun k => by
    rw [flowSteps_Zpre]
    simp [flowSteps, mkStep]

section Comps

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (RH : RadiusHyp S.L S.Rb S.lam R)

local notation "Hs" => (hist (N := N) (K := K) (k0 := k0) ok h4 h5 RH)

theorem rem_eq (k : ℕ) : (Hs).rem k = ∅ := rfl

theorem step_zero_Z : ((Hs).step 0).Z = ∅ := rfl

theorem mem_newCubes_succ (k : ℕ) (x : Torus S.d (side S N K (k + 1))) :
    x ∈ (Hs).newCubes (k + 1) ↔ k = 0 ∧ x = 0 := by
  have : (Hs).newCubes (k + 1) = finOf ((Hs).step k).newCubes := rfl
  rw [this, mem_finOf]
  show x ∈ ((mkStep S R N K k (regions S R N K k0 k)).P ∪ ∅ ∪ ∅ ∪ ∅) ↔ _
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
      have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 RH 0 x).mp hx2
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
      have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 RH k x).mp (Finset.mem_inter.mp hx).2
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
  have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 RH 0 x).mp hx2
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
      rw [mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 RH 0 x]
      constructor
      · rintro ⟨-, -, h⟩; exact h
      · rintro rfl; exact ⟨zero_mem_comp_one (N := N) (K := K) (k0 := k0) ok h4 h5 RH c hK, rfl, rfl⟩
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
    obtain ⟨c, hc⟩ := comp_unique (N := N) (K := K) (k0 := k0) ok h4 h5 RH k hk (by omega)
    obtain ⟨hst, hs, hlen⟩ := ih (by omega) (by omega) (by omega) c
    have hr := (Hs).book_rule (k := k) (by omega) c'
    have hparts : (Hs).parts k c' = {c} := by
      ext y
      rw [(Hs).mem_parts, Finset.mem_singleton]
      constructor
      · rintro ⟨-, -⟩; exact hc y
      · rintro rfl
        obtain ⟨Z', hZ'⟩ := (Hs).exists_succ (k := k) (by omega) (c := y) (by simp [rem_eq])
        obtain ⟨c0, hc0⟩ := comp_unique (N := N) (K := K) (k0 := k0) ok h4 h5 RH (k + 1) (by omega) (by omega)
        refine ⟨by simp [rem_eq], ?_⟩
        rw [hc0 c']
        have := hc0 Z'
        rw [this] at hZ'
        exact hZ'
    have hnew : (c'.1 ∩ (Hs).newCubes (k + 1)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x hx
      have := (mem_newCubes_succ (N := N) (K := K) (k0 := k0) ok h4 h5 RH k x).mp (Finset.mem_inter.mp hx).2
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

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (RH : RadiusHyp S.L S.Rb S.lam R)
  (N : ℕ) [NeZero N]

include ok h4 h5 RH

/-- The history with `K = k₀ = T`. -/
noncomputable abbrev histT : RegionHistory S (side S N (Tstar S)) R (Tstar S)
    (Tstar S) :=
  hist (N := N) (K := Tstar S) (k0 := Tstar S) ok h4 h5 RH

/-- The unique component at scale `T` is ripe. -/
theorem exists_ripe : ∃ c : (histT ok h4 h5 RH N).Comp (Tstar S),
    (∀ c' : (histT ok h4 h5 RH N).Comp (Tstar S), c' = c) ∧
      S.Ripe (Tstar S) ((histT ok h4 h5 RH N).bk (Tstar S) c) := by
  obtain ⟨c, hc⟩ := comp_unique (N := N) (K := Tstar S) (k0 := Tstar S) ok h4 h5 RH
    (Tstar S) (one_le_Tstar S) le_rfl
  obtain ⟨hst, hs, -⟩ := book_facts (N := N) (K := Tstar S) (k0 := Tstar S) ok h4 h5 RH
    (Tstar S) (one_le_Tstar S) le_rfl le_rfl le_rfl c
  exact ⟨c, hc, ⟨1, 1, ∅, hst⟩, (tStar_of hst hs)⟩

/-- **`RemCluster` has a non-empty member**: a removed cluster consisting of one ripe component of
`Z^pre_T`, with the empty kept configuration. -/
theorem remCluster_exists (M : ℕ) [NeZero M] :
    ∃ (Kc : HistConfig S (side S N (Tstar S)) R (Tstar S) (Tstar S) M (Tstar S))
      (C : Finset (ConfigPair S (side S N (Tstar S)) M (Tstar S) (Tstar S))),
      RemCluster Kc C := by
  classical
  obtain ⟨c, hc, hrip⟩ := exists_ripe ok h4 h5 RH N
  have hH : histT ok h4 h5 RH N ∈ (RegionHistory.historiesWithFinal (R := R)
      (k0 := Tstar S) (K := Tstar S) (Tstar S) c.1 :
      Set (RegionHistory S (side S N (Tstar S)) R (Tstar S) (Tstar S))) := by
    have hZp : (histT ok h4 h5 RH N).F.Zp (Tstar S) = c.1 := by
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
  refine ⟨HistConfig.empty, {(c.1, (histT ok h4 h5 RH N).localHistory M (Tstar S) (Tstar S) c)},
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

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (RH : RadiusHyp S.L S.Rb S.lam R)

/-- **`RipeWindow` is inhabited**: the ripe component of the history `histT` (side factor
`bigN S`), for any setting with `S.Good`. -/
theorem ripeWindow_exists (G : S.Good) :
    ∃ c : (histT ok h4 h5 RH (bigN S)).Comp (Tstar S),
      (histT ok h4 h5 RH (bigN S)).RipeWindow (Tstar S) c := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 RH (bigN S)
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

variable (ok : S.Ok) (h4 : 4 ≤ S.sS) (h5 : 5 ≤ S.sP) (RH : RadiusHyp S.L S.Rb S.lam R)

include ok h4 h5 RH

/-- **`T4Facts` is inhabited**: the merge, at scale `T`, of two parts carrying the book of the ripe
component of `histT` (both `Active(1, 1, ∅)` with point spines), provided the cap
`ν_max(T+1) ≥ 2`. -/
theorem t4Facts_exists (G : S.Good) (hcap : 2 ≤ S.numax (Tstar S + 1)) :
    ∃ (parts : Finset (Fin 2)) (f : Fin 2 → Book) (b' : Book),
      parts.card = 2 ∧ T4Facts S (Tstar S) parts f b' := by
  obtain ⟨c, -, hrip⟩ := exists_ripe ok h4 h5 RH (bigN S)
  obtain ⟨hst, -, -⟩ := book_facts (N := bigN S) (K := Tstar S) (k0 := Tstar S) ok h4 h5 RH
    (Tstar S) (one_le_Tstar S) le_rfl le_rfl le_rfl c
  set b := (histT ok h4 h5 RH (bigN S)).bk (Tstar S) c with hb
  have hinv : BookInv S (Tstar S) b :=
    ((histT ok h4 h5 RH (bigN S)).window_inv' G (Tstar S) (one_le_Tstar S) le_rfl le_rfl c).1
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

end RadiiHist

end Balaban.Inhabited
