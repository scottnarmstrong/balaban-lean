/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowConvPhysGenBall
public import Balaban.LargeField.R.WindowOfHistoryCollar
public import Balaban.LargeField.R.DeltaPsiCollar

/-!
# The window datum on the ball around a piece

P7 p. 501 (2.14) with P6 p. 7 (2.16): the background of the piece `(j, c)` and the window
background are both functions of the configuration `ψ̃`, and the configuration entering the
difference `δφ` "is equal to 0 on the domain where the generating sets coincide".  For the window of
a ripe component (`windowOfHistory`) and a site `y` within `2 L^j M` (sup distance) of the region
`X_{Z'}` of the piece:

* `full_layerIndex_ball`: the layer index of `y` in `𝔹_k` (the parent of the physical window datum)
  is `j + 1` if the cast of `y` lies in `Ω_{j+1}` of the step `j` (the set of the two-scale lift
  `lift_{j,j+1}` of `locData`, Definition II.2.1 (b)) and `j` otherwise;
* `piece_window_Ψ_eq_of_lift`: hence if the local datum of the piece is the two-scale lift of the
  block field `ψ` at `y` (its scale-`j` field is `ψ_j` and its scale-`(j+1)` field is `ψ_{j+1}`),
  then it equals the physical window datum of `ψ` at `y`: `δψ = 0` on the ball;
* `bgData_h_eq_of_Ω_one`: the external fields `h̃` of two data that are the same constant on `Ω₁`
  agree wherever the `Ω₁` agree.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory

section Generic

variable {d L N₀l kl N₀w kw N : ℕ} [NeZero N₀l] [NeZero N₀w] [NeZero L] {ϱl ϱw : ℝ}

/-- **Equal external fields where the `Ω₁` agree**: two data whose field `h̃` is the same constant
`h` on `Ω₁` (and zero off `Ω₁`, as for every `BgData`) agree at `x`, `y` as soon as `x ∈ Ω₁` and
`y ∈ Ω₁` are equivalent. -/
theorem bgData_h_eq_of_Ω_one {Gl : GeneratingSet d L N₀l kl ϱl} {Gw : GeneratingSet d L N₀w kw ϱw}
    (Dl : BgData Gl N) (Dw : BgData Gw N) (h : Fin N → ℂ) (hl : ∀ x ∈ Gl.Ω 1, Dl.h x = h)
    (hw : ∀ y ∈ Gw.Ω 1, Dw.h y = h) {x : Torus d (N₀l * L ^ kl)} {y : Torus d (N₀w * L ^ kw)}
    (hxy : x ∈ Gl.Ω 1 ↔ y ∈ Gw.Ω 1) : Dl.h x = Dw.h y := by
  by_cases hx : x ∈ Gl.Ω 1
  · rw [hl x hx, hw y (hxy.1 hx)]
  · rw [Dl.h_zero x hx, Dw.h_zero y (fun hy => hx (hxy.2 hy))]

end Generic

section Ball

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}
  {N : ℕ}

/-- On the ball around a site of the piece `(j, c)`, the cast of `y` lies in the `(j+1)`-cube
union `U_{Z'}` of the local family (`stepU`). -/
theorem cast_mem_stepU_of_ball (hkK : m' + 1 ≤ K) (hj : j ≤ m') {c : H.Comp (j + 1)}
    {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx1 : cubeMap n S.L M (m' + 1) (j + 1) x ∈ c.1) (htj : 2 ≤ ⌊R j⌋₊)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M)) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
      stepU g.M1 g.c (n (j + 1)) S.L j ⌊R j⌋₊ (c.1 : Set (Torus S.d (n (j + 1)))) := by
  have hd1 := cubeMap_supDist_le_of_ball H hkK (show j + 1 ≤ m' + 1 by omega)
    (supDist_ball_mono (show j ≤ j + 1 by omega) hxy)
  unfold stepU
  rw [mem_fineK1, blockMap_castSite_cube]
  unfold thick
  exact mem_nbhd.2 ⟨_, Finset.mem_coe.2 hx1, by omega⟩

/-- **The layer of `𝔹_k` on the ball around a piece** (P7 (2.14), geometric half): `y ∈ Ω_j(𝔹_k)`,
`y ∉ Ω_{j+2}(𝔹_k)`, and `y ∈ Ω_{j+1}(𝔹_k)` exactly when the cast of `y` lies in `Ω_{j+1}` of the
step `j` of the piece; so the layer index of `y` in `𝔹_k` is `j + 1` or `j` accordingly. -/
theorem full_layerIndex_ball (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M)) :
    y ∈ (windowOfHistory H Z g hkK hW).full.Ω j ∧
      (windowOfHistory H Z g hkK hW).full.layerIndex y =
        if torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
            fineK1 g.M1 g.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega
        then j + 1 else j := by
  classical
  have hk1pos := hW.k1_pos hkK
  have hL := H.F.ok.two_le_L
  have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
  have hLr : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
  have hfl : ∀ q, 2 ≤ ⌊R q⌋₊ := fun q => by
    refine Nat.le_floor ?_
    have := g.hRlow q
    push_cast; linarith
  obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hkK hj c hK x).1 hx
  set W := windowOfHistory H Z g hkK hW with hWdef
  have hfull : ∀ q, W.full.Ω q =
      (H.locGen Z M hkK H.F.ok.two_le_L (fun j _ _ => g.hRlow j)).Ω q := fun _ => rfl
  -- (a) `y ∈ Ω_j(𝔹_k)`
  have hyj : y ∈ W.full.Ω j := by
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [hfull]
    refine mem_locGen_of_ball H hkK (Z := Z) (i := i) (by omega) (t := 2) (by omega)
      (piece_not_mem_lin hkK hj hc hx1 hx2) hxy hL (fun j _ _ => g.hRlow j)
  -- (b) `y ∉ Ω_{j+2}(𝔹_k)`
  have hyn : y ∉ W.full.Ω (j + 2) := by
    rcases lt_or_eq_of_le hj with hjm | hjm
    · have hnw := windowGenSet_Ω_not_mem_ball (g := g) hkK hW hjm hk1j hc hx1 (t := 2) (hfl (j + 1)) hxy
        (m := j + 2) le_rfl (by omega)
      intro hy
      by_cases hyZ : y ∈ W.Z
      · by_cases hyK : y ∈ W.Zk1
        · exact windowOfHistory_hZk1top (g := g) hkK hW y hyK
            (W.full.Ω_antitone (by omega) (by omega) (by omega) hy)
        · exact hnw ((windowGenSet_mem_iff_full W (windowOfHistory_hyp hkK hW)
            (Finset.mem_sdiff.2 ⟨hyZ, hyK⟩) hyZ (j + 2)).2 hy)
      · have hxk : cubeMap n S.L M (m' + 1) (m' + 1) x ∈ Z.1 :=
          (mem_locFine_k hkK).1 (cube_mem_locFine_top hkK hc hx1)
        have hyU : cubeMap n S.L M (m' + 1) (m' + 1) y ∈ bdryU H Z := by
          unfold bdryU thick
          refine mem_nbhd.2 ⟨_, hxk, ?_⟩
          have := cubeMap_supDist_le_of_ball H hkK le_rfl
            (supDist_ball_mono (show j ≤ m' + 1 by omega) hxy)
          have := hfl m'
          simp only [Nat.add_sub_cancel]
          omega
        have hbd : y ∈ W.bdry.Ω (j + 2) :=
          W.bdry.Ω_antitone (by omega) (show j + 2 ≤ m' + 1 by omega) (Nat.le_succ _)
            (windowBdry_top_mem (g := g) hyU)
        have hUnb : y ∈ W.Unb := by
          rw [windowOfHistory_Unb, mem_fineFin]
          unfold bdryUnb
          exact subset_nbhd _ _ hyU
        apply hnw
        rw [WindowPieces.windowGenSet_Ω]
        exact Finset.mem_union_right _ (Finset.mem_inter.2 ⟨hbd, Finset.mem_sdiff.2 ⟨hUnb, hyZ⟩⟩)
    · subst hjm
      rw [W.full.top]
      exact Finset.notMem_empty _
  -- (c) `y ∈ Ω_{j+1}(𝔹_k)` iff the cast of `y` lies in `Ω_{j+1}` of the step
  have hyU := cast_mem_stepU_of_ball (g := g) hkK hj hx1 (hfl j) hxy
  have hiff : y ∈ W.full.Ω (j + 1) ↔ torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
      fineK1 g.M1 g.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega := by
    rw [← windowGenSet_Ω_ball hkK hW hj hk1j hc hx1 hx2 (t := 2) (by omega)
      (by have := hfl m'; omega) hxy (by omega) le_rfl,
      ← piece_window_layers_iff_ball_two hkK hW hj hk1j hK hc hx hxy (by omega) le_rfl,
      locGen_Ω_top_iff' g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK, mem_fineK1]
    exact ⟨fun h => h.2, fun h => ⟨hyU, h⟩⟩
  refine ⟨hyj, ?_⟩
  split_ifs with hΩ
  · exact W.full.layerIndex_eq (by omega) (by omega)
      (W.full.mem_layer.2 ⟨hiff.2 hΩ, hyn⟩)
  · exact W.full.layerIndex_eq (by omega) (by omega)
      (W.full.mem_layer.2 ⟨hyj, fun h => hΩ (hiff.1 h)⟩)

/-- **`δψ = 0` on the ball** (P6 (2.16), P7 (2.14)): if the local datum of the piece `(j, c)` at
the cast of `y` is the two-scale lift of the block field `ψ` (the value of `ψ_{j+1}` on the
`(j+1)`-block of `y` if the cast lies in `Ω_{j+1}` of the step `j`, the value of `ψ_j` on the
`j`-block of `y` otherwise), then it equals the physical window datum of `ψ` at `y`, for every
site `y` within `2 L^j M` of the piece region. -/
theorem piece_window_Ψ_eq_of_lift (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (h : Fin N → ℝ)
    (D : BgData (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK) N)
    (hlift : D.Ψ (torusCast (piece_torus_eq g H.F.hnn hkK hj) y) =
      fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
        (if torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
            fineK1 g.M1 g.c (n (j + 1)) S.L j ((H.locRH (j + 1) c).step j).Omega
          then j + 1 else j) y) q : ℝ) : ℂ)) :
    D.Ψ (torusCast (piece_torus_eq g H.F.hnn hkK hj) y) =
      (physicalWindowData (windowOfHistory H Z g hkK hW) (windowOfHistory_hyp hkK hW)
        (windowOfHistory_parentRefines H Z g hkK hW) ψ h).Ψ y := by
  classical
  have hk1pos := hW.k1_pos hkK
  obtain ⟨hyj, hlay⟩ := full_layerIndex_ball hkK hW hj hk1j hK hc hx hxy
  set W := windowOfHistory H Z g hkK hW with hWdef
  have hy1 : y ∈ W.full.Ω 1 := W.full.Ω_antitone le_rfl (by omega) (by omega) hyj
  obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hkK hj c hK x).1 hx
  have hRm : 1 ≤ ⌊R m'⌋₊ := by
    refine Nat.le_floor ?_
    have := g.hRlow m'
    have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
    push_cast; linarith
  have hyw : y ∈ (W.windowGenSet (windowOfHistory_hyp hkK hW)).Ω 1 :=
    (windowGenSet_Ω_ball hkK hW hj hk1j hc hx1 hx2 (t := 2) (by omega) (by omega) hxy le_rfl
      (by omega)).2 hy1
  rw [hlift]
  funext q
  rw [physicalWindowData_Ψ W (windowOfHistory_hyp hkK hW)
      (windowOfHistory_parentRefines H Z g hkK hW) ψ h ((mem_dataSites _).2 (Or.inl hyw)) q,
    inheritedField_eq_parentBlock, parentBlock_of_mem _ hy1, hlay]

end Ball

end Balaban.LargeField
