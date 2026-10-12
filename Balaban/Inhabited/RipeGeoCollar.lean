/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.Inhabited.RipeGeoWitness
public import Balaban.LargeField.Budget.Fine

/-!
# The inner collar of the actual window

Geometry of the genuine-radii witness (`RipeGeoWitness`): the region `Z_q = Z^pre_q` (a single
component) contains the sup-ball of radius `⌊2 R_{q-1}⌋ + 6` around a point of `Ω''ᶜ`
(Lemma I.3.5 (d), (e)), so a cube at depth `> 2⌊R_{q-1}⌋ + 3` from `Z_qᶜ` exists, which is not in
the one-neighbourhood of the core set `W = (Z_qᶜ)^{≈2}` (Definition III.2.1).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.Inhabited.RipeGeo

open Balaban Balaban.LargeField Balaban.Inhabited Balaban.Multiscale Balaban.Background

theorem comp_unique0 (j : ℕ) (hj : 1 ≤ j) (hjT : j ≤ T) (c c' : H0.Comp j) : c = c' := by
  obtain ⟨c0, h⟩ := RadiiHist.comp_unique (N := N1) (K := T) (k0 := T) RadiiSet.wS_ok le_rfl le_rfl
    RadiiSet.wRH j hj hjT
  rw [h c, h c']

theorem desc_exists0 (q : ℕ) (hq : 1 ≤ q) (Y : H0.Comp q) :
    ∀ j, q ≤ j → j ≤ T → ∀ Y' : H0.Comp j, H0.Desc q j Y Y' := by
  intro j hqj
  induction j, hqj using Nat.le_induction with
  | base =>
    intro hT Y'
    rw [comp_unique0 q hq hT Y' Y]; exact RegionHistory.Desc.refl _
  | succ j hqj ih =>
    intro hT Y'
    obtain ⟨cj, -⟩ := RadiiHist.comp_unique (N := N1) (K := T) (k0 := T) RadiiSet.wS_ok le_rfl le_rfl
      RadiiSet.wRH j (by omega) (by omega)
    have hrem : cj.1 ∉ H0.rem j := Finset.notMem_empty _
    obtain ⟨Z', hZ'⟩ := H0.exists_succ (k := j) (by omega) (c := cj) hrem
    rw [comp_unique0 (j+1) (by omega) hT Y' Z']
    exact RegionHistory.Desc.step j Y cj Z' (ih (by omega) cj) hrem hZ'

/-- the lineage at scale `q` is the whole `Z^pre_q`. -/
theorem lin_eq_Zpre0 (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T) :
    ((H0.lin q T Z0 : Finset (Torus S0.d (n0 q))) : Set _) = H0.F.Zpre q := by
  ext x
  constructor
  · intro hx
    obtain ⟨Y, -, hxY⟩ := RegionHistory.mem_lin.mp (Finset.mem_coe.mp hx)
    exact mem_finOf.mp (comp_subset Y.2 hxY)
  · intro hx
    obtain ⟨Y, hY, hxY⟩ := mem_comp_self (ω := S0.omega q) (mem_finOf.mpr hx)
    exact Finset.mem_coe.mpr (RegionHistory.mem_lin.mpr
      ⟨⟨Y, hY⟩, desc_exists0 q hq ⟨Y, hY⟩ T hqT le_rfl Z0, hxY⟩)


theorem Z_nonempty0 (k : ℕ) (hk : 1 ≤ k) (hkT : k ≤ T) : ∃ z, z ∈ (H0.step k).Z := by
  obtain ⟨c, -⟩ := RadiiHist.comp_unique (N := N1) (K := T) (k0 := T) RadiiSet.wS_ok le_rfl le_rfl
    RadiiSet.wRH k hk hkT
  obtain ⟨z, hz', hc⟩ := mem_comps_iff.mp c.2
  have hz : z ∈ c.1 := by
    rw [hc]; exact mem_linkClass.mpr ⟨hz', Linked.refl _⟩
  exact ⟨z, (H0.mem_Z_iff hz).2 (Finset.notMem_empty _)⟩

theorem ball_Z0 {d L a n1 : ℕ} [NeZero a] [NeZero n1] {Rp Rk : ℝ} (st : RegionStep d L a n1 Rp Rk) {v : Torus d n1}
    (hv : v ∈ st.OmegaDDᶜ) : nbhd (⌊2 * Rk⌋₊ + 6) {v} ⊆ st.Z0 := by
  have h1 : nbhd 4 {v} ⊆ st.FZ :=
    (nbhd_mono le_rfl (Set.singleton_subset_iff.2 hv)).trans Set.subset_union_left
  refine Set.Subset.trans ?_ st.nbhd_FZ_subset_Z0
  have := nbhd_mono (m := ⌊2 * Rk⌋₊ + 2) le_rfl h1
  rw [nbhd_nbhd] at this
  intro y hy
  exact this (nbhd_mono (by omega) subset_rfl hy)


theorem deep0 (k : ℕ) (hk : k + 1 ≤ T) :
    ∃ v : Torus S0.d (n0 (k + 1)), nbhd (⌊2 * RadiiSet.wR k⌋₊ + 6) {v} ⊆ H0.F.Zpre (k + 1) := by
  have hsub : (H0.step k).Z0 ⊆ H0.F.Zpre (k + 1) :=
    (H0.step k).Z0_subset_Zpre (S0.omega (k + 1)) (critOpt S0 T (k + 1))
  rcases Nat.eq_zero_or_pos k with rfl | hk1
  · have h0 : (0 : Torus S0.d (n0 1)) ∈ (H0.step 0).P := ⟨rfl, rfl, rfl⟩
    refine ⟨0, (ball_Z0 (H0.step 0)
      ((H0.step 0).Omega_compl_subset_OmegaDD_compl ((H0.step 0).P_subset_compl_Omega h0))).trans hsub⟩
  · obtain ⟨z, hz⟩ := Z_nonempty0 k hk1 (by omega)
    have hv := (H0.step k).Omega_compl_subset_OmegaDD_compl
      ((H0.step k).OmegaPrime_compl_subset_Omega_compl
        ((H0.step k).Uprime_subset_compl ((H0.step k).blockMap_Z_subset_Uprime hz)))
    exact ⟨_, (ball_Z0 (H0.step k) hv).trans hsub⟩


theorem deepA (q : ℕ) (hq : 1 ≤ q) (hqT : q ≤ T) :
    ∃ u : Torus S0.d (n0 q), u ∈ ((H0.locRH T Z0).step q).Z ∧
      u ∉ nbhd 1 (RegionHistory.coreW H0 Z0 q) := by
  obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, hv⟩ := deep0 k hqT
  rw [← lin_eq_Zpre0 (k + 1) hq hqT] at hv
  have hZ := RegionHistory.locRH_Z (H := H0) Z0 hqT hqT
  refine ⟨v, ?_, ?_⟩
  · rw [hZ]; exact hv (subset_nbhd _ _ rfl)
  · intro hmem
    unfold RegionHistory.coreW at hmem
    rw [hZ, thick2_eq, nbhd_nbhd] at hmem
    obtain ⟨w, hw, hd⟩ := mem_nbhd.mp hmem
    have hR : 0 ≤ RadiiSet.wR k := RadiiSet.wRH.nonneg k
    have h2 : 2 * ⌊RadiiSet.wR k⌋₊ ≤ ⌊2 * RadiiSet.wR k⌋₊ := by
      apply Nat.le_floor
      push_cast
      have := Nat.floor_le hR
      linarith
    have : w ∈ nbhd (⌊2 * RadiiSet.wR k⌋₊ + 6) {v} := by
      rw [mem_nbhd]; exact ⟨v, rfl, by rw [supDist_comm]; show _ ≤ _; simp at hd ⊢; omega⟩
    exact hw (hv this)


theorem exists_out0 (q : ℕ) (hqq : q = (H0.bk T Z0).q) : ∃ w : Torus S0.d (n0 q),
    w ∉ ((H0.locRH T Z0).step q).Z := by
  classical
  subst hqq
  have hW := hW0
  have hq1 : 1 ≤ (H0.bk T Z0).q := by rw [← hW.core_k1]; exact hW.k1_pos hkK0
  have hqT : (H0.bk T Z0).q ≤ T := by rw [← hW.core_k1]; exact RegionHistory.k1_le hW
  set q := (H0.bk T Z0).q with hqdef
  obtain ⟨Y, -⟩ := RadiiHist.comp_unique (N := N1) (K := T) (k0 := T) RadiiSet.wS_ok le_rfl le_rfl
    RadiiSet.wRH q hq1 hqT
  obtain ⟨B, hcard, hb, hsub⟩ := hW.core_box Y (desc_exists0 q hq1 Y T hqT le_rfl Z0)
  have hZsub : ((H0.locRH T Z0).step q).Z ⊆ (Y.1 : Set (Torus S0.d (n0 q))) := by
    rw [RegionHistory.locRH_Z (H := H0) Z0 hqT hqT]
    intro x hx
    obtain ⟨Y', -, hxY'⟩ := RegionHistory.mem_lin.mp (Finset.mem_coe.mp hx)
    rw [comp_unique0 q hq1 hqT Y Y']; exact hxY'
  by_cases hB : B = ∅
  · subst hB
    refine ⟨0, fun h0 => ?_⟩
    have := hsub (hZsub h0)
    simp at this
  · obtain ⟨b, hbB⟩ := Finset.nonempty_iff_ne_empty.2 hB
    have hn := crit_le0 q hq1 hqT
    refine ⟨fun i => b.1 i + ((S0.crit q + 1 : ℕ) : ZMod (n0 q)), fun h0 => ?_⟩
    have h1 := hsub (hZsub h0)
    simp only [Set.mem_iUnion] at h1
    obtain ⟨b', hb', hmem⟩ := h1
    have hbb : b' = b := Finset.card_le_one.1 hcard b' hb' b hbB
    subst hbb
    obtain ⟨j, hj, hjeq⟩ := hmem ⟨0, by decide⟩
    have hjc : j ≤ S0.crit q := (hj.trans_le (hb b' hb' _)).le
    have h2 : ((S0.crit q + 1 : ℕ) : ZMod (n0 q)) = ((j : ℕ) : ZMod (n0 q)) := add_left_cancel hjeq
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
    omega

section Conn
variable {d N₀ L k : ℕ} [NeZero N₀] [NeZero L]

theorem adj_single_steps (μ : Fin d) (t : ℕ) (x : Torus d (N₀ * L ^ k)) :
    Relation.ReflTransGen Adj x (x + t • Pi.single μ (1 : ZMod (N₀ * L ^ k))) := by
  induction t with
  | zero => simpa using Relation.ReflTransGen.refl
  | succ t ih =>
    refine ih.tail ⟨μ, Or.inl ?_⟩
    rw [succ_nsmul, add_assoc]

theorem adj_sum_steps (c : Fin d → ℕ) (s : Finset (Fin d)) (x : Torus d (N₀ * L ^ k)) :
    Relation.ReflTransGen Adj x (x + ∑ μ ∈ s, c μ • Pi.single μ (1 : ZMod (N₀ * L ^ k))) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Relation.ReflTransGen.refl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine ih.trans ?_
    have := adj_single_steps (N₀ := N₀) (L := L) (k := k) a (c a) (x + ∑ μ ∈ s, c μ • Pi.single μ 1)
    have e : x + (c a • Pi.single a (1 : ZMod (N₀ * L ^ k)) + ∑ μ ∈ s, c μ • Pi.single μ 1) =
        x + ∑ μ ∈ s, c μ • Pi.single μ 1 + c a • Pi.single a 1 := by abel
    rw [e]; exact this

theorem adj_connected (x y : Torus d (N₀ * L ^ k)) : Relation.ReflTransGen Adj x y := by
  classical
  have : NeZero (N₀ * L ^ k) := ⟨mul_ne_zero (NeZero.ne _) (pow_ne_zero _ (NeZero.ne _))⟩
  have := adj_sum_steps (N₀ := N₀) (L := L) (k := k) (fun μ => (y μ - x μ).val) Finset.univ x
  convert this using 1
  funext ν
  have key : (∑ μ : Fin d, (y μ - x μ).val • Pi.single μ (1 : ZMod (N₀ * L ^ k))) ν =
      (((y ν - x ν).val : ℕ) : ZMod (N₀ * L ^ k)) := by
    rw [Finset.sum_apply, Finset.sum_eq_single ν]
    · simp
    · intro b _ hb; simp [hb.symm]
    · simp
  rw [Pi.add_apply, key, ZMod.natCast_zmod_val]
  ring

end Conn

section Fine

theorem hnn0 : ∀ i, i < T → n0 i = S0.L * n0 (i + 1) := fun i hi => H0.F.hnn i hi

theorem exit0 : ∀ y ∈ W0.Zk1, ∀ x, Adj y x → x ∉ W0.Zk1 → y ∈ G0.Ω 1 := by
  intro y hy x hadj hx
  have hqk := RegionHistory.k1_le hW0
  have hk1 := hW0.k1_pos hkK0
  have hxZ : cubeMap n0 S0.L S0.M T (S0.k1 T) x ∈ (((H0.locRH T Z0).step (S0.k1 T)).Z)ᶜ := by
    have := hx
    rw [RegionHistory.windowOfHistory_Zk1 (g := g0) hkK0 hW0, RegionHistory.mem_locFineFin,
      RegionHistory.mem_locFine] at this
    exact this
  have hnb : supDist (cubeMap n0 S0.L S0.M T (S0.k1 T) y) (cubeMap n0 S0.L S0.M T (S0.k1 T) x) ≤ 1 := by
    rw [supDist_comm]; exact RegionHistory.cubeMap_adj hnn0 hqk hadj.symm
  have hW' : cubeMap n0 S0.L S0.M T (S0.k1 T) y ∈ RegionHistory.coreW H0 Z0 (S0.k1 T) := by
    unfold RegionHistory.coreW thick2 thick
    exact subset_nbhd _ _ (nbhd_mono (by omega) subset_rfl (mem_nbhd.2 ⟨_, hxZ, hnb⟩))
  have hc := RegionHistory.windowCore_top_mem (g := g0) hnn0 (S0.k1 T) hqk hW'
  have hc1 : y ∈ (RegionHistory.windowCore H0 Z0 g0 (S0.k1 T) hqk).Ω 1 :=
    (RegionHistory.windowCore H0 Z0 g0 (S0.k1 T) hqk).Ω_antitone le_rfl hk1 (by omega) hc
  rw [WindowPieces.windowGenSet_Ω]
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_inter.2 ⟨hc1, hy⟩))

theorem not_mem0 (y : Torus S0.d (S0.M * n0 T * S0.L ^ T)) (hy : y ∈ W0.Zk1)
    (hdeep : cubeMap n0 S0.L S0.M T (S0.k1 T) y ∉ nbhd 1 (RegionHistory.coreW H0 Z0 (S0.k1 T))) :
    y ∉ G0.Ω 1 := by
  intro h
  have hqk := RegionHistory.k1_le hW0
  rw [WindowPieces.windowGenSet_Ω] at h
  rcases Finset.mem_union.1 h with h | h
  · rcases Finset.mem_union.1 h with h | h
    · exact hdeep (RegionHistory.cubeMap_nbhd_of_mem_cast (g := g0) H0.F.ok.two_le_L hnn0 hqk
        (min_le_right _ _) (Finset.mem_inter.1 h).1)
    · exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).2).2 hy
  · exact (Finset.mem_sdiff.1 (Finset.mem_inter.1 h).2).2 (W0_hZ hy)

/-- **The inner collar of the actual window is nonempty.** -/
theorem collarIn_nonempty0 : (collarIn W0 W0_hyp).Nonempty := by
  have hqk := RegionHistory.k1_le hW0
  have hk1 := hW0.k1_pos hkK0
  obtain ⟨u, huZ, hudeep⟩ := deepA (S0.k1 T) hk1 hqk
  obtain ⟨w, hw⟩ := exists_out0 (S0.k1 T) hW0.core_k1
  obtain ⟨y0, hy0⟩ := cubeMap_surjective (S := S0) (n := n0) (M := S0.M) (K := T)
    hnn0 hqk u
  obtain ⟨z, hz⟩ := cubeMap_surjective (S := S0) (n := n0) (M := S0.M) (K := T)
    hnn0 hqk w
  have hy0Z : y0 ∈ W0.Zk1 := by
    rw [RegionHistory.windowOfHistory_Zk1 (g := g0) hkK0 hW0, RegionHistory.mem_locFineFin,
      RegionHistory.mem_locFine, hy0]; exact huZ
  have hzZ : z ∉ W0.Zk1 := by
    rw [RegionHistory.windowOfHistory_Zk1 (g := g0) hkK0 hW0, RegionHistory.mem_locFineFin,
      RegionHistory.mem_locFine, hz]; exact hw
  have hy0G : y0 ∉ G0.Ω 1 := not_mem0 y0 hy0Z (by rw [hy0]; exact hudeep)
  have key : ∀ y, Relation.ReflTransGen Adj y z → y ∈ W0.Zk1 → y ∉ G0.Ω 1 →
      (collarIn W0 W0_hyp).Nonempty := by
    intro y hr
    induction hr using Relation.ReflTransGen.head_induction_on with
    | refl => intro h; exact absurd h hzZ
    | @head a b hadj _ ih =>
      intro hya hyG
      by_cases hb : b ∈ W0.Zk1
      · by_cases hbG : b ∈ G0.Ω 1
        · exact ⟨a, (mem_collarIn W0 W0_hyp).2 ⟨(mem_collar _).2 ⟨hyG, b, hbG, hadj.symm⟩, hya⟩⟩
        · exact ih hb hbG
      · exact absurd (exit0 a hya b hadj hb) hyG
  exact key y0 (adj_connected y0 z) hy0Z hy0G

end Fine

/-- **Non-vacuous collar bound at the actual window.**  The inner collar is nonempty and the bound
(2.3) holds at every one of its sites. -/
theorem collar_bound_W0_nonvacuous {ε : ℝ} {δ : ℕ → ℝ} (hδ : IsAdmDelta S0.d S0.L ε (S0.k1 T) T δ)
    (hδ' : IsAdmDelta S0.d S0.L ε (S0.k1 T - 1) (S0.k1 T) δ) (hδpos : ∀ j, 0 < δ j)
    {N : ℕ} (hN : 0 < N) (h : Fin N → ℝ) :
    (collarIn W0 W0_hyp).Nonempty ∧ ∃ K6 : ℝ, 0 < K6 ∧ ∀ c ∈ collarIn W0 W0_hyp,
      vn (deltaPsiColl W0 W0_hyp (H0.windowOfHistory_parentRefines Z0 g0 hkK0 hW0) W0_precedes
          (compWeight S0.L 1) (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ))
          (fun _ => EuclideanSpace.single (⟨0, hN⟩ : Fin N) (1 : ℝ)) h c) <
        (3 * S0.d * S0.L + 2) * S0.hatW ε T * δ (S0.k1 T) :=
  ⟨collarIn_nonempty0, collar_bound_W0 hδ hδ' hδpos hN h⟩

/-- The bound with the admissible tolerances `δ_i = (3/4)^i`, `ε = 0`, one field component. -/
theorem collar_bound_W0_geom :
    (collarIn W0 W0_hyp).Nonempty ∧ ∃ K6 : ℝ, 0 < K6 ∧ ∀ c ∈ collarIn W0 W0_hyp,
      vn (deltaPsiColl W0 W0_hyp (H0.windowOfHistory_parentRefines Z0 g0 hkK0 hW0) W0_precedes
          (compWeight S0.L 1) (fun _ => EuclideanSpace.single (⟨0, Nat.one_pos⟩ : Fin 1) (1 : ℝ))
          (fun _ => EuclideanSpace.single (⟨0, Nat.one_pos⟩ : Fin 1) (1 : ℝ)) (fun _ => 0) c) <
        (3 * S0.d * S0.L + 2) * S0.hatW 0 T * (3 / 4 : ℝ) ^ (S0.k1 T) :=
  collar_bound_W0_nonvacuous
    (isAdmDelta_geom S0.d S0.L (by show 3 ≤ 3; norm_num) (by show 2 ≤ 3; norm_num) le_rfl _ _)
    (isAdmDelta_geom S0.d S0.L (by show 3 ≤ 3; norm_num) (by show 2 ≤ 3; norm_num) le_rfl _ _)
    (fun i => by positivity) Nat.one_pos _

end Balaban.Inhabited.RipeGeo
