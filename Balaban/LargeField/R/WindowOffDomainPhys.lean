/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffZoneExt
public import Balaban.LargeField.R.WindowOffDomain
public import Balaban.LargeField.R.WindowConvPhysSwitchLoc

/-!
# The domain of the window datum from the domains of the pieces

P7 p. 500 after (2.11): the configuration is in the space (1.32) [5] localized to `W_j ∩ U_{j+1}` for
every piece `j`; after (2.14): the window background is then defined on the space localized to
`W_{k₁} ∩ U_k`.  `inDomainR_window_of_pieces`: for the window of a ripe component and a block field
`ψ` whose two-scale lifts are the data of the pieces (on their data sites), if every piece datum is
in `Ψ̃(G_i; δ)` and the external direction is a unit vector, then the physical window datum of `ψ`
is in `Ψ̃(𝔹_{k₁,k}; δ)`.  The zones (`inDomainR_of_zones`): the ball `L^j M` around the region of each
piece, the sites of `Z_{k₁}` over a component `c` of scale `k₁ + 1` for the piece `(k₁, c)`
(`WindowOffZoneCore`), the sites outside `Z` for the top piece (`WindowOffZoneExt`).  Constant
condition: `2 L + 1 ≤ M`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv

section Inst

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

/-- The facts on the top piece `(m', Z)`, for a piece equal to it as an element of the sigma type. -/
theorem top_piece_facts (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hM : 2 * S.L + 1 ≤ M)
    {j : ℕ} {c : H.Comp (j + 1)} (hs : (⟨j, c⟩ : Σ j, H.Comp (j + 1)) = ⟨m', Z⟩) (hj : j ≤ m')
    (hK : j + 1 ≤ K) :
    j = m' ∧
    (∀ y, y ∉ (windowOfHistory H Z g hmK hW).Z →
      (∀ q, 1 ≤ q → (y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet
          (windowOfHistory_hyp hmK hW)).Ω q ↔
        torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
          (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK).Ω q)) ∧
      torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
        fineK1 g.M1 g.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega) ∧
    (∀ y y', y ∉ (windowOfHistory H Z g hmK hW).Z → supDist y y' ≤ 2 * S.L ^ (m' + 1) + 1 →
      y' ∉ (windowOfHistory H Z g hmK hW).Z ∨
        torusCast (piece_torus_eq g H.F.hnn hmK hj) y' ∈ Xfine g (H.locRH (j + 1) c) j c.1) := by
  obtain ⟨rfl, h2⟩ := Sigma.mk.inj_iff.1 hs
  obtain rfl := eq_of_heq h2
  exact ⟨rfl, fun y hy => ⟨ext_window_layers_iff hmK hW hy, ext_cast_mem_Omega hmK hW hy⟩,
    fun y y' hy hd => near_ext hmK hW hM hy hd⟩

/-- **Every site of `Z ∖ Z_{k₁}` lies in the region of a piece** (the pieces partition the window
region): for the least `j' > k₁` with the site in `Z_{j'}`, the piece `(j' - 1, c)` with `c` the
component of `Lin_{j'}(Z)` of its cube. -/
theorem exists_piece_of_mem (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))} (hyZ : y ∈ (windowOfHistory H Z g hmK hW).Z)
    (hyK : y ∉ (windowOfHistory H Z g hmK hW).Zk1) :
    ∃ j, ∃ _ : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧ cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1 ∧
        cubeMap n S.L M (m' + 1) j y ∉ H.lin j (j + 1) c := by
  classical
  have hk1m := k1_le hW
  have hP : ∃ j', j' ≤ m' + 1 ∧ y ∈ H.locFine Z M j' := ⟨m' + 1, le_rfl, by
    rw [windowOfHistory_Z, mem_locFineFin] at hyZ; exact hyZ⟩
  obtain ⟨hj'm, hyj'⟩ := Nat.find_spec hP
  have hk1j : S.k1 (m' + 1) < Nat.find hP := by
    by_contra hle
    push Not at hle
    apply hyK
    rw [windowOfHistory_Zk1, mem_locFineFin]
    exact locFine_mono hmK hle hk1m hyj'
  obtain ⟨j, hjj⟩ : ∃ j, Nat.find hP = j + 1 := ⟨Nat.find hP - 1, by omega⟩
  have hnj : y ∉ H.locFine Z M j := fun h =>
    Nat.find_min hP (show j < Nat.find hP by omega) ⟨by omega, h⟩
  rw [hjj] at hyj' hj'm
  rw [mem_locFine_iff_lin hmK (by omega)] at hyj' hnj
  obtain ⟨c, hc, hyc⟩ := mem_lin.mp (Finset.mem_coe.1 hyj')
  refine ⟨j, ⟨by omega, by omega⟩, c, mem_ancFin.mpr hc, hyc, fun h => hnj ?_⟩
  exact Finset.mem_coe.2 (lin_anc_subset (mem_ancFin.mpr hc) h)

open Classical in
/-- **The domain of the window datum from the domains of the pieces** (P7 pp. 500-501: the space
(1.32) [5] on `W_{k₁} ∩ U_k` from the spaces on `W_j ∩ U_{j+1}`). -/
theorem inDomainR_window_of_pieces {N : ℕ} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hM : 2 * S.L + 1 ≤ M) {ι : Type*} (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hcov : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' →
      c ∈ H.ancFin (j + 1) (m' + 1) Z → ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
    (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (hjK : ∀ i, jf i + 1 ≤ K)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hlift : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
        dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i)
                ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ))
    {ν δ : ℝ} (hδ : 0 < δ)
    (hdom : ∀ i, InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)) ν δ
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv)) :
    InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ν δ
      (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
        (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)) := by
  have hk1m : S.k1 (m' + 1) ≤ m' := by
    have h1 := hW.core_window.1
    have h2 := S.one_le_nq (H.bk (m' + 1) Z).q
    rw [hW.core_k1]; omega
  have hL := H.F.ok.two_le_L
  set W := windowOfHistory H Z g hmK hW with hWdef
  set G := W.windowGenSet (windowOfHistory_hyp hmK hW) with hGdef
  set Dw := physicalWindowData W (windowOfHistory_hyp hmK hW)
    (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q) with hDw
  set e : ∀ i, Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)) ≃
      Torus S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) :=
    fun i => Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)) with he_def
  have hea : ∀ i y, e i y = torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y :=
    fun i y => torusCast_equivCast_apply _ y
  have he : ∀ i x (μ : Fin S.d), e i (x + Pi.single μ 1) = e i x + Pi.single μ 1 :=
    fun i x μ => equivCast_add_single (piece_torus_eq g H.F.hnn hmK (hjf i).2) x μ
  -- the zones
  let A : ι → Set (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) := fun i =>
    {y | (∃ x, torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
          Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 ∧ supDist y x ≤ S.L ^ jf i * M) ∨
      (jf i = S.k1 (m' + 1) ∧ y ∈ W.Zk1 ∧ cubeMap n S.L M (m' + 1) (jf i + 1) y ∈ (cf i).1) ∨
      ((⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨m', Z⟩ ∧ y ∉ W.Z)}
  have hpos : ∀ j, 1 ≤ S.L ^ j * M := fun j => Nat.one_le_iff_ne_zero.2 (by
    have := NeZero.ne S.L; have := NeZero.ne M; positivity)
  -- `Ω₁` on the balls
  have hballΩ : ∀ i x y, torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 → supDist y x ≤ 2 * (S.L ^ jf i * M) →
      (y ∈ G.Ω 1 ↔ e i y ∈ (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)).Ω 1) := fun i x y hx hxy => by
    rw [hea]
    exact (piece_window_layers_iff_ball_two hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hx hxy
      le_rfl (by omega)).symm
  have hΩ : ∀ i y, y ∈ A i → ∀ y', (y' = y ∨ Adj y y') →
      (y' ∈ G.Ω 1 ↔ e i y' ∈ (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)).Ω 1) := by
    intro i y hy y' hy'
    have hd1 : supDist y y' ≤ 1 := by
      rcases hy' with rfl | h
      · rw [supDist_self]; exact Nat.zero_le _
      · exact Adj.supDist_le_one h
    rcases hy with ⟨x, hx, hxy⟩ | ⟨hjk, hyK, hyc⟩ | ⟨hs, hyZ⟩
    · refine hballΩ i x y' hx ?_
      have t := supDist_triangle y' y x
      have := supDist_comm y y'
      have := hpos (jf i)
      omega
    · have hd2 : supDist y y' ≤ 2 * S.L ^ jf i + 1 := by
        have : 1 ≤ S.L ^ jf i := Nat.one_le_iff_ne_zero.2 (by have := NeZero.ne S.L; positivity)
        omega
      rcases near_core hmK hW (hjf i).2 hjk (hjK i) (hcf i) hyK hyc hd2 with ⟨hy'K, hy'c⟩ | hX
      · rw [hea]; exact core_window_layers_iff hmK hW (hjf i).2 hjk (hjK i) (hcf i) hy'K hy'c 1
      · exact hballΩ i y' y' hX (by rw [supDist_self]; exact Nat.zero_le _)
    · obtain ⟨-, htop, hnear⟩ := top_piece_facts (g := g) hmK hW hM hs (hjf i).2 (hjK i)
      have hd2 : supDist y y' ≤ 2 * S.L ^ (m' + 1) + 1 := by
        have : 1 ≤ S.L ^ (m' + 1) := Nat.one_le_iff_ne_zero.2 (by
          have := NeZero.ne S.L; positivity)
        omega
      rcases hnear y y' hyZ hd2 with hy'Z | hX
      · rw [hea]; exact (htop y' hy'Z).1 1 le_rfl
      · exact hballΩ i y' y' hX (by rw [supDist_self]; exact Nat.zero_le _)
  -- layer indices on the zones
  have hlay : ∀ i y, y ∈ A i → G.layerIndex y =
      (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex (e i y) := by
    intro i y hy
    rw [hea]
    rcases hy with ⟨x, hx, hxy⟩ | ⟨hjk, hyK, hyc⟩ | ⟨hs, hyZ⟩
    · exact ball_layerIndex_eq hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hx (by omega)
    · exact layerIndex_eq_of_Ω_iff G _ (by have := (hjf i).2; omega)
        (fun q _ => core_window_layers_iff hmK hW (hjf i).2 hjk (hjK i) (hcf i) hyK hyc q)
    · obtain ⟨-, htop, -⟩ := top_piece_facts (g := g) hmK hW hM hs (hjf i).2 (hjK i)
      exact layerIndex_eq_of_Ω_iff G _ (by have := (hjf i).2; omega) (htop y hyZ).1
  -- the data on the zones
  have hΨ : ∀ i y, y ∈ A i → y ∈ dataSites G → Dw.Ψ y =
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (e i y) := by
    intro i y hy hyd
    have hdl : e i y ∈ dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i)) :=
      (dataSites_iff_of_Ω_one G _ (e i) (he i) (hΩ i y hy)).1 hyd
    rw [hea] at hdl ⊢
    rw [hlift i y hdl]
    -- the parent layer of `y` in `𝔹_k` is the branch of the lift
    have hpar : y ∈ W.full.Ω 1 ∧ W.full.layerIndex y =
        if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
            fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i)
              ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
          then jf i + 1 else jf i := by
      rcases hy with ⟨x, hx, hxy⟩ | ⟨hjk, hyK, hyc⟩ | ⟨hs, hyZ⟩
      · obtain ⟨h1, h2⟩ := full_layerIndex_ball hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hx
          (y := y) (by omega)
        exact ⟨W.full.Ω_antitone le_rfl (by have := (hjf i).1; have := hW.k1_pos hmK; omega)
          (by have := (hjf i).2; omega) h1, h2⟩
      · obtain ⟨h1, h2⟩ := core_full_layer (g := g) hmK hW hjk hyK hyd
        have hn := core_cast_not_mem_Omega (g := g) hmK hW (hjf i).2 hjk (hcf i) hyK hyc
        simp only [hn, ↓reduceIte]
        exact ⟨W.full.Ω_antitone le_rfl (by have := hW.k1_pos hmK; omega)
          (by have := (hjf i).2; omega) h1, h2⟩
      · obtain ⟨hjm, htop, -⟩ := top_piece_facts (g := g) hmK hW hM hs (hjf i).2 (hjK i)
        obtain ⟨h1, h2⟩ := ext_full_layer (g := g) hmK hW hyZ
        simp only [(htop y hyZ).2, ↓reduceIte]
        rw [h2, hjm]
        exact ⟨W.full.Ω_antitone le_rfl (by omega) (by omega) h1, rfl⟩
    funext q
    rw [hDw, physicalWindowData_Ψ W (windowOfHistory_hyp hmK hW)
        (windowOfHistory_parentRefines H Z g hmK hW) ψ _ hyd q, inheritedField_eq_parentBlock,
      parentBlock_of_mem _ hpar.1, hpar.2]
  -- every data site is in a zone
  have hbase : ∀ y, y ∈ dataSites G → ∃ i,
      (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
          Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) ∨
        (jf i = S.k1 (m' + 1) ∧ y ∈ W.Zk1 ∧ cubeMap n S.L M (m' + 1) (jf i + 1) y ∈ (cf i).1) ∨
        ((⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨m', Z⟩ ∧ y ∉ W.Z) := by
    intro y _
    by_cases hyK : y ∈ W.Zk1
    · have hy1 : y ∈ H.locFine Z M (S.k1 (m' + 1) + 1) := by
        rw [windowOfHistory_Zk1, mem_locFineFin] at hyK
        exact locFine_mono hmK (Nat.le_succ _) (by omega) hyK
      rw [mem_locFine_iff_lin hmK (by omega)] at hy1
      obtain ⟨c, hc, hyc⟩ := mem_lin.mp (Finset.mem_coe.1 hy1)
      obtain ⟨i, hi⟩ := hcov _ c le_rfl hk1m (mem_ancFin.mpr hc)
      have key : ∀ s : Σ j, H.Comp (j + 1), s = ⟨S.k1 (m' + 1), c⟩ →
          s.1 = S.k1 (m' + 1) ∧ cubeMap n S.L M (m' + 1) (s.1 + 1) y ∈ s.2.1 := by
        rintro s rfl; exact ⟨rfl, hyc⟩
      obtain ⟨h1, h2⟩ := key _ hi
      exact ⟨i, Or.inr (Or.inl ⟨h1, hyK, h2⟩)⟩
    by_cases hyZ : y ∈ W.Z
    · obtain ⟨j, hj, c, hc, h1, h2⟩ := exists_piece_of_mem (g := g) hmK hW hyZ hyK
      obtain ⟨i, hi⟩ := hcov j c hj.1 hj.2 hc
      have key : ∀ s : Σ j, H.Comp (j + 1), s = ⟨j, c⟩ →
          cubeMap n S.L M (m' + 1) (s.1 + 1) y ∈ s.2.1 ∧
            cubeMap n S.L M (m' + 1) s.1 y ∉ H.lin s.1 (s.1 + 1) s.2 := by
        rintro s rfl; exact ⟨h1, h2⟩
      exact ⟨i, Or.inl ((mem_Xfine_cast_iff g hmK (hjf i).2 (cf i) (hjK i) y).2 (key _ hi))⟩
    · obtain ⟨i, hi⟩ := hcov m' Z hk1m le_rfl (mem_ancFin.mpr (Desc.refl Z))
      exact ⟨i, Or.inr (Or.inr ⟨hi, hyZ⟩)⟩
  have hbaseA : ∀ i y, (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
        Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) → y ∈ A i := fun i y h =>
    Or.inl ⟨y, h, by rw [supDist_self]; exact Nat.zero_le _⟩
  have hcovA : ∀ y ∈ dataSites G, ∃ i, y ∈ A i := by
    intro y hy
    obtain ⟨i, h | h | h⟩ := hbase y hy
    · exact ⟨i, hbaseA i y h⟩
    · exact ⟨i, Or.inr (Or.inl h)⟩
    · exact ⟨i, Or.inr (Or.inr h)⟩
  -- every interface pair is in a zone
  have hpair : ∀ y y', IsInterfacePair G y y' → ∃ i, y ∈ A i ∧ y' ∈ A i := by
    intro y y' hp
    have hd := interfacePair_supDist_le G hp
    obtain ⟨i, h | ⟨hjk, hyK, hyc⟩ | ⟨hs, hyZ⟩⟩ := hbase y hp.1
    · refine ⟨i, hbaseA i y h, Or.inl ⟨y, h, ?_⟩⟩
      have hl : G.layerIndex y ≤ jf i + 1 := by
        rw [hlay i y (hbaseA i y h)]; exact layerIndex_le_top _ _
      have h1 : S.L ^ G.layerIndex y ≤ S.L ^ (jf i + 1) :=
        Nat.pow_le_pow_right (by omega) hl
      have h2 : 2 * S.L ^ (jf i + 1) + 1 ≤ S.L ^ jf i * M := by
        have e1 : S.L ^ (jf i + 1) = S.L ^ jf i * S.L := pow_succ _ _
        have hp : 1 ≤ S.L ^ jf i := Nat.one_le_iff_ne_zero.2 (by
          have := NeZero.ne S.L; positivity)
        nlinarith
      rw [supDist_comm]; omega
    · have hl : G.layerIndex y ≤ jf i := by
        by_contra hgt
        push Not at hgt
        have hy1 : y ∈ G.Ω 1 := by
          by_contra hn; rw [layerIndex_of_not_mem G hn] at hgt; omega
        obtain ⟨-, hk, hly⟩ := G.layerIndex_spec hy1
        have hyΩ : y ∈ G.Ω (S.k1 (m' + 1) + 1) :=
          G.Ω_antitone (by omega) (by omega) (by omega) (G.mem_layer.1 hly).1
        rw [hGdef, WindowPieces.windowGenSet_Ω] at hyΩ
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at hyΩ
        rcases hyΩ with (⟨h1, -⟩ | ⟨-, -, h3⟩) | ⟨-, -, h3⟩
        · exact windowCore_not_mem_of_gt (H := H) (Z := Z) (g := g) (S.k1 (m' + 1)) (k1_le hW)
            (m := S.k1 (m' + 1) + 1) (by omega) y h1
        · exact h3 hyK
        · exact h3 (windowOfHistory_hZ (g := g) hmK hW hyK)
      have h1 : S.L ^ G.layerIndex y ≤ S.L ^ jf i := Nat.pow_le_pow_right (by omega) hl
      rcases near_core hmK hW (hjf i).2 hjk (hjK i) (hcf i) hyK hyc (y' := y') (by omega) with
        h' | h'
      · exact ⟨i, Or.inr (Or.inl ⟨hjk, hyK, hyc⟩), Or.inr (Or.inl ⟨hjk, h'⟩)⟩
      · exact ⟨i, Or.inr (Or.inl ⟨hjk, hyK, hyc⟩), hbaseA i y' h'⟩
    · obtain ⟨-, -, hnear⟩ := top_piece_facts (g := g) hmK hW hM hs (hjf i).2 (hjK i)
      have h1 : S.L ^ G.layerIndex y ≤ S.L ^ (m' + 1) :=
        Nat.pow_le_pow_right (by omega) (layerIndex_le_top G y)
      rcases hnear y y' hyZ (by omega) with h' | h'
      · exact ⟨i, Or.inr (Or.inr ⟨hs, hyZ⟩), Or.inr (Or.inr ⟨hs, h'⟩)⟩
      · exact ⟨i, Or.inr (Or.inr ⟨hs, hyZ⟩), hbaseA i y' h'⟩
  -- the external fields
  have hh : ∀ y ∈ G.Ω 1, ∀ q, Dw.h y q = ((hv q : ℝ) : ℂ) := fun y hy q => by
    rw [hDw, physicalWindowData_h _ _ _ _ _ hy q]
  have hhl : ∀ i, ∀ x ∈ (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i)).Ω 1, ∀ q,
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).h x q = ((hv q : ℝ) : ℂ) := fun i x hx q => by
    unfold locData
    rw [liftMixed_h _ _ _ _ _ _ hx]
  have hr4 : ν * ((S.L : ℝ) ^ (m' + 1)) ^ 2 * |∑ q, (hv q) ^ 2 - 1| < δ ^ 2 := by
    have hs : ∑ q, (hv q) ^ 2 = 1 := by
      rw [← EuclideanSpace.real_norm_sq_eq, hunit, one_pow]
    rw [hs, sub_self, abs_zero, mul_zero]
    positivity
  exact inDomainR_of_zones G Dw (N₀ := fun i => g.M1 * (g.c * n (jf i + 1)))
    (kl := fun i => jf i + 1)
    (fun i => locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i))
    (fun i => locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
      (hjK i) (ou i) (xu i) hv) e he
    (fun i k hk1 hk2 x y hxy => by
      have := (jBlock_equivCast_iff (piece_torus_eq g H.F.hnn hmK (hjf i).2) hk2 hk1 (e i x)
        (e i y)).2
      simp only [he_def, Equiv.symm_apply_apply] at this
      exact this hxy)
    A hΩ hlay hΨ hcovA hpair hdom (fun q => hv q) hh hhl hr4

end Inst

end Balaban.LargeField
