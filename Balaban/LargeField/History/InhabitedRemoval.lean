module

public import Balaban.LargeField.History.Inhabited
import Mathlib.Tactic.Linarith

/-!
# A region history in which a component is removed (Definition I.4.1)

All earlier witnesses of `RegionHistory` have `Rem_k = ∅`.  Here the scales are `n_k = 2^(2-k)`
(horizon `K = 2`, `k₀ = 1`).  The step `0 → 1` starts from `Z_0 = ∅` and has one new cube
`S = {0}`; then `Z^pre_1` contains `0`, the component `C` of `Z^pre_1` through `0` is removed
by `R^{(1)}` (so `Z_1 = Z^pre_1 ∖ C`), and the later steps have no new cubes.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Witness

namespace Witness

variable {d n : ℕ} [NeZero n]

omit [NeZero n] in
theorem opening_empty_eq_univ {L : ℕ} (hL : 0 < L) (m : ℕ) :
    opening L m (∅ : Set (Torus d n)) = Set.univ := by
  ext y
  refine ⟨fun _ => trivial, fun _ => ⟨y, ⟨fun _ => 0, fun _ => hL, by ext i; simp⟩, ?_⟩⟩
  rw [setDist_eq_top_iff.mpr (Or.inr rfl)]; exact le_top

theorem openingIn_empty_univ {L : ℕ} (hL : 0 < L) (m : ℕ) :
    openingIn L m (∅ : Set (Torus d n)) Set.univ = Set.univ :=
  openingIn_empty m (Ω := Set.univ) fun x _ => ⟨x, ⟨fun _ => 0, fun _ => hL, by ext i; simp⟩,
    fun _ _ => trivial⟩

/-- With `Z = ∅`, `Ω''` is everything. -/
theorem omegaDD_empty {L : ℕ} (hL : 0 < L) {n0 : ℕ} (ρ r : ℕ) :
    Region.OmegaDD L (Region.FDD ρ (∅ : Set (Torus d n)) ∅)
      (Region.Omega L ∅ (Region.OmegaPrime L ρ (Region.Uprime L n (n0 := n0) r ∅))) =
      Set.univ := by
  have hU : Region.Uprime L n (n0 := n0) r (∅ : Set (Torus d n0)) = ∅ := by
    simp [Region.Uprime, Region.U, thick, nbhd_empty]
  simp only [Region.OmegaDD, Region.FDD, Region.Omega, Region.OmegaPrime, hU, nbhd_empty,
    Set.union_empty, opening_empty_eq_univ hL, openingIn_empty_univ hL]

end Witness

/-- The step `0 → 1`: `Z_0 = ∅` and the single new cube `S = {0}`. -/
noncomputable def remStep0 (K : ℕ) :
    RegionStep setting.d setting.L (sideLen K 0) (sideLen K 1) (radii (0 - 1)) (radii 0) where
  Z := ∅
  P := ∅
  Q := ∅
  R := ∅
  S := {0}
  P_sub := Set.empty_subset _
  Q_sub := Set.empty_subset _
  R_sub := Set.empty_subset _
  S_sub := by
    rw [omegaDD_empty (by show 0 < 2; norm_num)]
    intro x _ hx
    obtain ⟨y, hy, _⟩ := (mem_nbhd).mp hx
    exact hy trivial

theorem zero_mem_Z0 (K : ℕ) : (0 : Torus setting.d (sideLen K 1)) ∈ (remStep0 K).Z0 := by
  have hD : (remStep0 K).OmegaDD = Set.univ := omegaDD_empty (by show 0 < 2; norm_num) _ _
  intro ⟨c, hc, hm⟩
  have hF : (0 : Torus setting.d (sideLen K 1)) ∈ (remStep0 K).FZ :=
    Or.inr (subset_nbhd 1 _ rfl)
  have := (le_setDist_iff).mp hm 0 hc 0 hF
  rw [supDist_self] at this
  omega

/-- `Z^pre_1`. -/
noncomputable def remZp1 (k0 K : ℕ) : Set (Torus setting.d (sideLen K 1)) :=
  (remStep0 K).Zpre (setting.omega 1) (critOpt setting k0 1)

theorem zero_mem_remZp1 (k0 K : ℕ) : (0 : Torus setting.d (sideLen K 1)) ∈ remZp1 k0 K :=
  Region.subset_Zpre _ _ _ (zero_mem_Z0 K)

/-- The removed component of `Z^pre_1`: the component through `0`. -/
noncomputable def remComp (k0 K : ℕ) : Finset (Torus setting.d (sideLen K 1)) :=
  linkClass (setting.omega 1) (finOf (remZp1 k0 K)) 0

theorem remComp_mem (k0 K : ℕ) :
    remComp k0 K ∈ comps (setting.omega 1) (finOf (remZp1 k0 K)) :=
  mem_comps_iff.mpr ⟨0, mem_finOf.mpr (zero_mem_remZp1 k0 K), rfl⟩

theorem zero_mem_remComp (k0 K : ℕ) : (0 : Torus setting.d (sideLen K 1)) ∈ remComp k0 K :=
  mem_linkClass.mpr ⟨mem_finOf.mpr (zero_mem_remZp1 k0 K), Linked.refl _⟩

/-- The removed components: `{C}` at scale `1`. -/
noncomputable def remAt (k0 K : ℕ) : ∀ k, Finset (Finset (Torus setting.d (sideLen K k)))
  | 1 => {remComp k0 K}
  | _ => ∅

/-- The steps, given the region `Z_k` (the step `0` ignores it: `Z_0 = ∅`). -/
noncomputable def remStepAt (K : ℕ) : ∀ k, Set (Torus setting.d (sideLen K k)) →
    RegionStep setting.d setting.L (sideLen K k) (sideLen K (k + 1)) (radii (k - 1)) (radii k)
  | 0, _ => remStep0 K
  | k + 1, Z => RegionHistory.emptyStep setting (sideLen K) radii (k + 1) Z

/-- The regions `Z_k = Z^pre_k ∖ ⋃ Rem_k`. -/
noncomputable def remZ (k0 K : ℕ) : ∀ k, Set (Torus setting.d (sideLen K k))
  | 0 => ∅
  | k + 1 => (remStepAt K k (remZ k0 K k)).Zpre (setting.omega (k + 1)) (critOpt setting k0 (k + 1))
      \ ⋃ c ∈ remAt k0 K (k + 1), (c : Set (Torus setting.d (sideLen K (k + 1))))

/-- The steps with the removal. -/
noncomputable def remFlowSteps (k0 K : ℕ) : FlowSteps setting (sideLen K) radii k0 K where
  ok := setting_ok
  s4 := le_refl _
  s5 := le_refl _
  RH := radiusHyp
  hnn := fun _ hk => sideLen_succ K hk
  step := fun k => remStepAt K k (remZ k0 K k)

theorem remFlowSteps_Zpre (k0 K : ℕ) : ∀ k, (remFlowSteps k0 K).Zpre (k + 1) =
    (remStepAt K k (remZ k0 K k)).Zpre (setting.omega (k + 1)) (critOpt setting k0 (k + 1)) :=
  fun _ => rfl

/-- **A region history with a removed component** (Definition I.4.1; the overwrite `Z_k =
Z^pre_k ∖ ⋃ Rem_k` of Definition I.3.11): `n_k = 2^(2-k)`, `K = 2`, `k₀ = 1`, `Rem_1 = {C}`. -/
noncomputable def remRegionHistory : RegionHistory setting (sideLen 2) radii 1 2 where
  F := remFlowSteps 1 2
  rem := remAt 1 2
  rem_sub := fun k => by
    cases k with
    | zero => exact Finset.empty_subset _
    | succ j =>
      cases j with
      | zero =>
        intro c hc
        have : c = remComp 1 2 := Finset.mem_singleton.mp hc
        subst this
        exact remComp_mem 1 2
      | succ j => exact Finset.empty_subset _
  rem_empty := fun k hk => by
    rcases hk with rfl | hk
    · rfl
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 2 := ⟨k - 2, by omega⟩
      rfl
  Z_eq := fun k => by
    cases k with
    | zero => simp [remFlowSteps, remStepAt, remStep0, FlowSteps.Zpre, remAt]
    | succ j => rfl

theorem exists_regionHistory_rem :
    ∃ (H : RegionHistory setting (sideLen 2) radii 1 2), ∃ k, 1 ≤ k ∧ k ≤ 1 ∧ (H.rem k).Nonempty :=
  ⟨remRegionHistory, 1, le_rfl, le_rfl, ⟨remComp 1 2, Finset.mem_singleton_self _⟩⟩

/-! ### The removal is visible -/

theorem remRegionHistory_rem_one :
    remRegionHistory.rem 1 = {remComp 1 2} := rfl

/-- The removed component is nonempty, lies in `Z^pre_1`, and is disjoint from `Z_1`. -/
theorem remRegionHistory_visible :
    (remComp 1 2).Nonempty ∧ (∀ x ∈ remComp 1 2, x ∈ remRegionHistory.F.Zpre 1) ∧
      (∀ x ∈ remComp 1 2, x ∉ (remRegionHistory.step 1).Z) := by
  refine ⟨⟨0, zero_mem_remComp 1 2⟩, fun x hx => ?_, fun x hx hxZ => ?_⟩
  · exact mem_finOf.mp (comp_subset (remComp_mem 1 2) hx)
  · have h := (remRegionHistory.Z_eq 1) ▸ hxZ
    simp only [remRegionHistory_rem_one, Finset.mem_singleton, Set.mem_sdiff, Set.mem_iUnion,
      Finset.mem_coe, exists_prop, exists_eq_left] at h
    exact h.2 hx

/-- The removed component is a component of `Z^pre_1` and not a component of `Z_1`. -/
theorem remRegionHistory_comp :
    remComp 1 2 ∈ comps (setting.omega 1) (remRegionHistory.Zp 1) ∧
      remComp 1 2 ∉ comps (setting.omega 1) (finOf (remRegionHistory.step 1).Z) := by
  refine ⟨remComp_mem 1 2, fun h => ?_⟩
  have := ((remRegionHistory.mem_comps_Z 1).mp h).2
  exact this (Finset.mem_singleton_self _)

/-! ### Admissibility fails for this witness -/

/-- A component whose book was produced with a new cube (`r ≥ 1`, a restart) is never ripe. -/
theorem nextBook_not_ripe {S : Setting} {ι : Type*} (μ : ℕ) (parts : Finset ι) (f : ι → Book)
    (r : ℕ) (hr : 1 ≤ r) (Γ' : Spine S.d) : ¬ S.Ripe μ (S.nextBook μ parts f r Γ') := by
  rintro ⟨⟨q, ν, M, hst⟩, ht⟩
  have hst' : (S.nextBook μ parts f r Γ').st = WState.restart μ (Γ'.length = 0) := by
    simp [Setting.nextBook, Setting.nextState, hr]
  have hq := Book.q_active hst
  have h2 : WState.restart μ (Γ'.length = 0) = .active q ν M := hst' ▸ hst
  unfold WState.restart at h2
  split_ifs at h2 with hp
  · injection h2 with h3
    have h4 : S.nq (S.nextBook μ parts f r Γ').q + (S.nextBook μ parts f r Γ').q ≤
        S.tStar (S.nextBook μ parts f r Γ') := by
      unfold Setting.tStar; rw [add_comm]; exact le_max_left _ _
    have := S.one_le_nq (S.nextBook μ parts f r Γ').q
    omega

/-- The witness is not admissible: `C` is a component of `Z^pre_1` containing the new cube `0`,
so its book at scale `1` is a restart and `C` is not ripe (Definition I.4.1, ripeness). -/
theorem remRegionHistory_not_admissible : ¬ remRegionHistory.Admissible := by
  intro h
  have hC : remComp 1 2 ∈ remRegionHistory.rem 1 := Finset.mem_singleton_self _
  have hr := h 1 ⟨remComp 1 2, remComp_mem 1 2⟩ hC
  refine nextBook_not_ripe (S := setting) 1 _ _ _ ?_ _ hr
  refine Finset.card_pos.mpr ⟨0, Finset.mem_inter.mpr ⟨zero_mem_remComp 1 2, ?_⟩⟩
  exact mem_finOf.mpr (Or.inr rfl)

end Balaban.LargeField
