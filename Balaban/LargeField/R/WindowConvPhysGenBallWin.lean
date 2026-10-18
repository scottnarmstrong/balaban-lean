/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysGenBallHist
public import Balaban.LargeField.R.WindowOfHistory
public import Balaban.LargeField.R.WindowRegionGeom
public import Balaban.LargeField.R.RRipeCard
public import Balaban.LargeField.R.ZeroDomainSep

/-!
# The window generating set agrees with `𝔹_k` on a ball around a piece

P7 (2.14), geometric half.  Let `x` be a site of the piece `(j, c)` of the window of a ripe
component `Z` (`k₁ ≤ j ≤ m'`, `k = m' + 1`), i.e. the `π_{j+1}`-cube of `x` is in `c` and its
`π_j`-cube is outside `Lin_j(c)`.  For `y` within `t · L^j M` of `x`, `1 ≤ m ≤ j + 1`:
`y ∈ Ω_m(window) ↔ y ∈ Ω_m(𝔹_k)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale RegionHistory

namespace RegionHistory

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

theorem supDist_ball_mono {q q' t : ℕ} (hqq : q ≤ q') {k : ℕ} {x y : Torus S.d (M * n k * S.L ^ k)}
    (h : supDist y x ≤ t * (S.L ^ q * M)) : supDist y x ≤ t * (S.L ^ q' * M) :=
  h.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right
    (Nat.pos_of_ne_zero (NeZero.ne S.L)) hqq)))

/-- A site of the piece has its `π_j`-cube outside `Lin_j(Z)`. -/
theorem piece_not_mem_lin (hkK : m' + 1 ≤ K) (hj : j ≤ m') {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) :
    cubeMap n S.L M (m' + 1) j x ∉ ((H.lin j (m' + 1) Z : Finset (Torus S.d (n j))) : Set _) :=
  fun h => hx2 (cube_mem_lin_of_anc hkK hj hc hx1 (Finset.mem_coe.mp h))

/-- Near a site of the piece the `π_{j+1}`-cube lies in `Lin_{j+1}(Z)` only if it lies in `c`. -/
theorem cube_mem_of_ball (hkK : m' + 1 ≤ K) (hj : j ≤ m') {c : H.Comp (j + 1)}
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) {t : ℕ} (htj : t ≤ ⌊R j⌋₊)
    (hxy : supDist y x ≤ t * (S.L ^ j * M))
    (hy : cubeMap n S.L M (m' + 1) (j + 1) y ∈ ((H.lin (j + 1) (m' + 1) Z : Finset (Torus S.d (n (j + 1)))) : Set _)) :
    cubeMap n S.L M (m' + 1) (j + 1) y ∈ c.1 := by
  obtain ⟨Y, hd, hyY⟩ := mem_lin.mp (Finset.mem_coe.mp hy)
  by_cases hYc : Y = c
  · subst hYc; exact hyY
  · exfalso
    have h1 := cubeMap_supDist_le_of_ball H hkK (show j + 1 ≤ m' + 1 by omega)
      (supDist_ball_mono (show j ≤ j + 1 by omega) hxy)
    have h2 := comp_sep hYc hyY hx1
    have : NeZero S.M := ⟨by have := H.F.ok.one_le_M; omega⟩
    have h3 := H.radius_lt_omega (k := j + 1) (by omega)
    simp only [Nat.add_sub_cancel] at h3
    omega

/-- A site of `Z_q`'s complement coarse neighbourhood lies in the top layer of the core piece. -/
theorem core_top_mem_of_ball (hkK : m' + 1 ≤ K) {q : ℕ} (hq : q ≤ m' + 1)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : cubeMap n S.L M (m' + 1) q x ∉ ((H.lin q (m' + 1) Z : Finset (Torus S.d (n q))) : Set _))
    (hxy : supDist (cubeMap n S.L M (m' + 1) q y) (cubeMap n S.L M (m' + 1) q x) ≤
      2 * (⌊R (q - 1)⌋₊ + 1)) :
    y ∈ (windowCore H Z g q hq).Ω q := by
  refine windowCore_top_mem (g := g) (fun i hi => H.F.hnn i (by omega)) q hq ?_
  unfold coreW
  rw [thick2_eq]
  refine mem_nbhd.2 ⟨cubeMap n S.L M (m' + 1) q x, ?_, hxy⟩
  rw [locRH_Z Z hq (hq.trans hkK)]
  exact hx

theorem windowGenSet_Ω_ball (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hk1j : S.k1 (m' + 1) ≤ j) {c : H.Comp (j + 1)} (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1)
    (hx2 : cubeMap n S.L M (m' + 1) j x ∉ H.lin j (j + 1) c) {t : ℕ}
    (ht1 : t ≤ ⌊R (j - 1)⌋₊ + 2) (ht2 : t ≤ ⌊R m'⌋₊ + 1)
    (hxy : supDist y x ≤ t * (S.L ^ j * M)) {m : ℕ} (hm1 : 1 ≤ m) (hmj : m ≤ j + 1) :
    y ∈ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω m ↔
      y ∈ (windowOfHistory H Z g hkK hW).full.Ω m := by
  classical
  have hk1pos := hW.k1_pos hkK
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  have hL := H.F.ok.two_le_L
  have hRnn := H.F.RH.nonneg
  have hnx : cubeMap n S.L M (m' + 1) (i + 1) x ∉
      ((H.lin (i + 1) (m' + 1) Z : Finset (Torus S.d (n (i + 1)))) : Set _) :=
    piece_not_mem_lin hkK hj hc hx1 hx2
  have hfull : ∀ q, (windowOfHistory H Z g hkK hW).full.Ω q =
      (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω q :=
    fun q => windowOfHistory_full_Ω hkK hW q
  have hxΩ : x ∈ (windowOfHistory H Z g hkK hW).full.Ω (i + 1) := by
    rw [hfull]; exact mem_locGen_j hkK hL (fun j _ _ => g.hRlow j) hc (by omega) hj hx1 hx2
  have hyΩ : y ∈ (windowOfHistory H Z g hkK hW).full.Ω (i + 1) := by
    rw [hfull]
    refine mem_locGen_of_ball H hkK (Z := Z) (i := i) (by omega) (t := t) ?_ hnx hxy hL
      (fun j _ _ => g.hRlow j)
    have : ⌊R i⌋₊ ≤ ⌊2 * R i⌋₊ := Nat.floor_le_floor (by linarith [hRnn i])
    simp only [Nat.add_sub_cancel] at ht1
    omega
  have hmΩ : m ≤ i + 1 → y ∈ (windowOfHistory H Z g hkK hW).full.Ω m := fun hm =>
    (windowOfHistory H Z g hkK hW).full.Ω_antitone hm1 hm (by omega) hyΩ
  have hnn : ∀ q, q < m' + 1 → n q = S.L * n (q + 1) := fun q hq => H.F.hnn q (by omega)
  have hxk : cubeMap n S.L M (m' + 1) (m' + 1) x ∈ Z.1 :=
    (mem_locFine_k hkK).1 (cube_mem_locFine_top hkK hc hx1)
  by_cases hyZ : y ∈ (windowOfHistory H Z g hkK hW).Z
  · by_cases hyK : y ∈ (windowOfHistory H Z g hkK hW).Zk1
    · have hkj : S.k1 (m' + 1) = i + 1 := by
        by_contra hne
        have hki : S.k1 (m' + 1) ≤ i := by omega
        have hyi : y ∈ H.locFine Z M i := by
          rw [windowOfHistory_Zk1, mem_locFineFin] at hyK
          exact locFine_mono hkK hki (by omega) hyK
        rw [mem_locFine] at hyi
        have hOm : blockMap S.L (n (i + 1)) (cubeMap n S.L M (m' + 1) i x) ∈
            ((H.locRH (m' + 1) Z).step i).Omega := by
          rw [cubeMap_succ hnn (by omega) x]
          have := hxΩ
          rw [hfull, mem_locGen_succ (by omega)] at this
          exact this
        have hfar := ((H.locRH (m' + 1) Z).step i).fine_far
          (Nat.pos_of_ne_zero (NeZero.ne S.L)) (hnn i (by omega)) hOm hyi
        have hd := cubeMap_supDist_le_of_ball H hkK (show i ≤ m' + 1 by omega) (t := t * S.L)
          (x := x) (y := y) (by
            have : t * (S.L ^ (i + 1) * M) = t * S.L * (S.L ^ i * M) := by ring
            rw [← this]; exact hxy)
        rw [supDist_comm] at hd
        simp only [Nat.add_sub_cancel] at ht1
        have h4 : t * S.L ≤ (⌊R i⌋₊ + 2) * S.L := Nat.mul_le_mul_right _ ht1
        have : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
        nlinarith
      have hcore : y ∈ (windowOfHistory H Z g hkK hW).core.Ω (S.k1 (m' + 1)) := by
        refine core_top_mem_of_ball hkK (k1_le hW) (x := x) ?_ ?_
        · rw [hkj]; exact hnx
        · have := cubeMap_supDist_le_of_ball H hkK (show i + 1 ≤ m' + 1 by omega) hxy
          rw [hkj]
          simp only [Nat.add_sub_cancel] at ht1 ⊢
          omega
      rw [hkj] at hcore
      by_cases hmle : m ≤ i + 1
      · have h1 : y ∈ (windowOfHistory H Z g hkK hW).core.Ω m :=
          (windowOfHistory H Z g hkK hW).core.Ω_antitone hm1 hmle (by omega) hcore
        rw [WindowPieces.windowGenSet_Ω]
        exact ⟨fun _ => hmΩ hmle, fun _ => Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_inter.2 ⟨h1, hyK⟩))⟩
      · have hm2 : m = i + 2 := by omega
        have hno : y ∉ (windowOfHistory H Z g hkK hW).full.Ω m := by
          have := windowOfHistory_hZk1top (g := g) hkK hW y hyK
          rw [hkj] at this
          rw [hm2]; exact this
        refine iff_of_false ?_ hno
        rw [WindowPieces.windowGenSet_Ω]
        intro h
        simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h
        rcases h with (⟨h1, -⟩ | ⟨-, -, h3⟩) | ⟨-, -, h3⟩
        · exact windowCore_not_mem_of_gt (H := H) (Z := Z) (g := g) (S.k1 (m' + 1)) (k1_le hW)
            (m := m) (by omega) y h1
        · exact h3 hyK
        · exact h3 hyZ
    · exact windowGenSet_mem_iff_full _ _ (Finset.mem_sdiff.2 ⟨hyZ, hyK⟩) hyZ m
  · have hyZ' : cubeMap n S.L M (m' + 1) (m' + 1) y ∉ Z.1 := by
      rw [windowOfHistory_Z, mem_locFineFin, mem_locFine_k hkK] at hyZ; exact hyZ
    have hyU : cubeMap n S.L M (m' + 1) (m' + 1) y ∈ bdryU H Z := by
      unfold bdryU thick
      refine mem_nbhd.2 ⟨_, hxk, ?_⟩
      have := cubeMap_supDist_le_of_ball H hkK le_rfl
        (supDist_ball_mono (show i + 1 ≤ m' + 1 by omega) hxy)
      simp only [Nat.add_sub_cancel]
      omega
    have hbd : y ∈ (windowOfHistory H Z g hkK hW).bdry.Ω m :=
      (windowOfHistory H Z g hkK hW).bdry.Ω_antitone hm1 (show m ≤ m' + 1 by omega) (Nat.le_succ _)
        (windowBdry_top_mem (g := g) hyU)
    have hUnb : y ∈ (windowOfHistory H Z g hkK hW).Unb := by
      rw [windowOfHistory_Unb, mem_fineFin]
      unfold bdryUnb
      exact subset_nbhd _ _ hyU
    have hfm : y ∈ (windowOfHistory H Z g hkK hW).full.Ω m :=
      (windowOfHistory H Z g hkK hW).full.Ω_antitone hm1 (show m ≤ m' + 1 by omega) (Nat.le_succ _)
        (windowOfHistory_hOmK hkK hW (by omega) y hyZ)
    rw [WindowPieces.windowGenSet_Ω]
    exact ⟨fun _ => hfm, fun _ => Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hbd,
      Finset.mem_sdiff.2 ⟨hUnb, hyZ⟩⟩)⟩

/-- Above the layer `j + 1` the window has no site on the ball around a piece `(j, c)` with
`j < m'`. -/
theorem windowGenSet_Ω_not_mem_ball (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j < m') (hk1j : S.k1 (m' + 1) ≤ j) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) {t : ℕ} (ht : t ≤ ⌊R (j + 1)⌋₊)
    (hxy : supDist y x ≤ t * (S.L ^ j * M)) {m : ℕ} (hm : j + 2 ≤ m) (hmk : m ≤ m' + 1) :
    y ∉ ((windowOfHistory H Z g hkK hW).windowGenSet (windowOfHistory_hyp hkK hW)).Ω m := by
  classical
  have hL := H.F.ok.two_le_L
  have hk1pos := hW.k1_pos hkK
  have hnn : ∀ q, q < m' + 1 → n q = S.L * n (q + 1) := fun q hq => H.F.hnn q (by omega)
  have hfull : ∀ q, (windowOfHistory H Z g hkK hW).full.Ω q =
      (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω q :=
    fun q => RegionHistory.windowOfHistory_full_Ω hkK hW q
  have hyn : y ∉ (windowOfHistory H Z g hkK hW).full.Ω (j + 2) := by
    rw [hfull, mem_locGen_succ (by omega)]
    intro hy
    have hxz : cubeMap n S.L M (m' + 1) (j + 1) x ∈ ((H.locRH (m' + 1) Z).step (j + 1)).Z := by
      rw [locRH_Z Z (show j + 1 ≤ m' + 1 by omega) (by omega)]
      exact Finset.mem_coe.2 (mem_lin.2 ⟨c, mem_ancFin.1 hc, hx1⟩)
    have hOm : blockMap S.L (n (j + 1 + 1)) (cubeMap n S.L M (m' + 1) (j + 1) y) ∈
        ((H.locRH (m' + 1) Z).step (j + 1)).Omega := by
      rw [cubeMap_succ hnn (by omega) y]; exact hy
    have hfar := ((H.locRH (m' + 1) Z).step (j + 1)).fine_far
      (Nat.pos_of_ne_zero (NeZero.ne S.L)) (hnn (j + 1) (by omega)) hOm hxz
    have hd := cubeMap_supDist_le_of_ball H hkK (show j + 1 ≤ m' + 1 by omega)
      (supDist_ball_mono (show j ≤ j + 1 by omega) hxy)
    have : 0 < S.L := Nat.pos_of_ne_zero (NeZero.ne S.L)
    have h5 := Nat.le_mul_of_pos_left (⌊R (j + 1)⌋₊ + 4) this
    omega
  have hyZ : y ∈ (windowOfHistory H Z g hkK hW).Z := by
    by_contra hyZ
    exact hyn ((windowOfHistory H Z g hkK hW).full.Ω_antitone (by omega) (show j + 2 ≤ m' + 1 by omega)
      (Nat.le_succ _) (windowOfHistory_hOmK hkK hW (by omega) y hyZ))
  intro h
  rw [WindowPieces.windowGenSet_Ω] at h
  simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff] at h
  rcases h with (⟨h1, -⟩ | ⟨h1, -⟩) | ⟨-, -, h3⟩
  · exact windowCore_not_mem_of_gt (H := H) (Z := Z) (g := g) (S.k1 (m' + 1)) (k1_le hW)
      (m := m) (by omega) y h1
  · exact hyn ((windowOfHistory H Z g hkK hW).full.Ω_antitone (by omega) (show j + 2 ≤ m by omega)
      (by omega) h1)
  · exact h3 hyZ

end RegionHistory

end Balaban.LargeField
