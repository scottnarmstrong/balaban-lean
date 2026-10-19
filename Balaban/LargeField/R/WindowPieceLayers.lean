/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowPieceTheta
public import Balaban.LargeField.R.WindowNodeCongr

/-!
# The `ψ_k` side of the piece datum and the mixed pairs from `ChiDomProp` (blocker 4)

Piece `C` of scale `k + 1 = i + 2`, localized history, `B = chiDomGen`.  A data site off
`Ω_{k+1}` carries the datum `ψ_k` at its `k`-block; its `π_k`-cube lies in `Ω_k` of the localization
(`locGen_dataSite_cube_mem_Omega`), so the `k`-block is in the layer `k` of `B`, and the multiscale
field of `ChiDomAt` takes the value of the datum there (`piece_psi_value`).

* near `Ω_{k+1}` (the cube of the site in `Ω^∼_{k+1}`): the first family of `ChiDomProp` at the cube
  (`PieceFirstFamily`, radius `3 d L δ_k`) gives the sphere bound `piece_psi_sphere`, the pair bound
  for two `ψ_k`-sites `piece_psi_pair` and the mixed pair bound `piece_mixed_pair` between a
  `ψ_{k+1}`-site and a `ψ_k`-site (layers `k + 1`, `k` of `B`);
* far from `Ω_{k+1}` and not meeting `Z_k`: the second family at scale `k`
  (`PieceSecondFamily`, radius `3 δ_k`) gives `piece_psi_sphere_far`, `piece_psi_pair_far`.

The sites over `Z_k` far from `Ω_{k+1}` are not covered here (they are the outputs of the
ancestors, tested by the first family of `ChiDomProp` at scale `k`).
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

section PieceLayers

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N i : ℕ}
  (H : RegionHistory S n R k0 K) (g : Geo S n R M) (C : H.Comp (i + 1 + 1))
  (hjK : i + 1 + 1 ≤ K)

/-- The datum at a data site off `Ω_{k+1}` is the field `ψ_k` at the `k`-block of the site. -/
theorem locData_Ψ_of_not_omega (o : OutT N R (locHist (H.locRH (i + 1 + 1) C) M K (i + 1 + 1) C.1) (i + 1 + 1))
    (x : NewCfg N (locHist (H.locRH (i + 1 + 1) C) M K (i + 1 + 1) C.1) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega) :
    (locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s =
      fun l => ((subVarField N x (i + 1) (torusCast (histScale_eq g.hM H.F.hnn (Nat.le_succ (i + 1)) hjK)
        (jBlock S.d S.L (g.M1 * (g.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1) s)) l : ℝ) : ℂ) := by
  unfold locData
  rw [liftMixed_Ψ _ _ _ _ _ _ hs]
  unfold mixedLift
  have hm : s ∉ fineK1 g.M1 g.c (n (i + 1 + 1)) S.L (i + 1) ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega := by
    rw [mem_fineK1]; exact hO
  simp only [hm, ↓reduceIte]
  rfl

omit [NeZero M] [NeZero S.L] in
/-- A cube of `Ω_k` of the localized history (`k = i + 1`) is a cube of `lhOmega` at scale `k`. -/
theorem cubeSub_lhOmega_of_omega_k {q : Torus S.d (n (i + 1))}
    (hq : q ∈ ((H.locRH (i + 1 + 1) C).step i).Omega) :
    CubeSub (S := S) (n := n) M K (i + 1)  q
      (lhOmega (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1)) := by
  intro x' hx'
  by_cases hqC : cubeMap n S.L M K (i + 1 + 1) x' ∈ C.1
  · left
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (i + 1) x' ∈ ((H.locRH (i + 1 + 1) C).step i).Omega
      rw [hx']; exact hq
    · exact hqC
  · right
    intro hz
    exact hqC hz.2

include hjK in
/-- The block of scale `k = i + 1` of a site whose `π_k`-cube lies in `Ω_k` of the localized history
lies in `lhOmega`, so that the gate of `subMultiscaleField` is open. -/
theorem blockSub_lhOmega_of_cube {y : BlockAt S n M K (i + 1)}
    (hy : blockCube S n M K (i + 1) y ∈ ((H.locRH (i + 1 + 1) C).step i).Omega) :
    BlockSub (S := S) (n := n) (M := M) (K := K) (i + 1) y
      (lhOmega (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1)) := by
  intro x' hx'
  have hc : cubeMap n S.L M K (i + 1) x' = blockCube S n M K (i + 1) y :=
    (blockCube_eq_cubeMap H.F.hnn (by omega) hx').symm
  exact cubeSub_lhOmega_of_omega_k (M := M) H C (q := blockCube S n M K (i + 1) y) hy x' hc

include hjK in
/-- The value of the datum at a site off `Ω_{k+1}` whose `π_k`-cube lies in `Ω_k` is the multiscale
field of `ChiDomAt` at the `k`-block of the site. -/
theorem piece_psi_value (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega) :
    ∀ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re =
      (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s))) l := by
  intro l
  rw [locData_Ψ_of_not_omega H g C hjK o x hv hs hO]
  simp only [Complex.ofReal_re]
  have hb1 := jBlock_bgToFine_gen g H.F.hnn hjK (Nat.le_succ (i + 1)) s
  have hmask := blockSub_lhOmega_of_cube H C hjK (y := jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s))
    (by
      rw [blockCube, cubeMap_eq_comp H.F.hnn (by omega), cubeMap_bgToFine_gen]
      exact hy)
  show _ = (subMultiscaleField N (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
    (Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)) x o (i + 1) _) l
  unfold subMultiscaleField
  simp only [Nat.lt_succ_self, ↓reduceIte, hmask, or_true]
  rw [hb1]
  rfl

omit [NeZero M] [NeZero S.L] in
include hjK in
/-- A fine site over a cube of `C` is a site of `Z_{k+1}` of the localized history, so the cube
satisfies `CubeSub` for it. -/
theorem cubeSub_Z_of_mem_comp {q : Torus S.d (n (i + 1 + 1))} (hq : q ∈ C.1) :
    CubeSub (S := S) (n := n) M K (i + 1 + 1) q ((H.localHistory M K (i + 1 + 1) C).Z (i + 1 + 1)) := by
  intro x hx
  refine ⟨?_, ?_⟩
  · show cubeMap n S.L M K (i + 1 + 1) x ∈ ((H.locRH (i + 1 + 1) C).step (i + 1 + 1)).Z
    rw [locRH_Z C le_rfl hjK, hx]
    simp [lin_self, hq]
  · show cubeMap n S.L M K (i + 1 + 1) x ∈ C.1
    rw [hx]; exact hq

omit [NeZero M] [NeZero S.L] in
/-- A cube of `Ω_{k+1}` of the localized history is a cube of `lhOmega`. -/
theorem cubeSub_lhOmega_of_omega {z : Torus S.d (n (i + 1 + 1))}
    (hz : z ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega) :
    CubeSub (S := S) (n := n) M K (i + 1 + 1) z
      (lhOmega (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)) := by
  intro x hx
  by_cases hzC : z ∈ C.1
  · left
    refine ⟨?_, ?_⟩
    · show cubeMap n S.L M K (i + 1 + 1) x ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega
      rw [hx]; exact hz
    · show cubeMap n S.L M K (i + 1 + 1) x ∈ C.1
      rw [hx]; exact hzC
  · right
    intro h
    apply hzC
    have := h.2
    simpa [fineSet, hx] using this

include hjK in
/-- A site off `Ω_{k+1}` lies over a cube of `C` (the complement of `Ω_{k+1}` is in `Z^pre_{k+1}`,
which for the localization is `C`). -/
theorem mem_comp_of_not_omega {q : Torus S.d (n (i + 1 + 1))}
    (hq : q ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega) : q ∈ C.1 := by
  have h1 := Omega_compl_subset_Zpre' (i + 1) ((H.locRH (i + 1 + 1) C).step (i + 1)) (S.omega (i + 1 + 1))
    (critOpt S k0 (i + 1 + 1)) hq
  have h2 : q ∈ (H.locRH (i + 1 + 1) C).F.Zp (i + 1 + 1) := mem_finOf.2 h1
  rwa [locRH_Zp hjK C] at h2

include hjK in
/-- A site off `Ω_{k+1}` whose `π_k`-cube lies in `Ω_k` is in the layer `k` of `B`. -/
theorem mem_layer_psi {x : Torus S.d (M * n K * S.L ^ K)}
    (hy : cubeMap n S.L M K (i + 1) x ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hO : cubeMap n S.L M K (i + 1 + 1) x ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega) :
    x ∈ (chiDomGen H g (i + 1 + 1) C).layer (i + 1) := by
  rw [GeneratingSet.mem_layer]
  unfold chiDomGen
  rw [mem_histGen, mem_histGen]
  refine ⟨⟨by omega, ?_⟩, ?_⟩
  · exact hy
  · rintro ⟨-, h⟩
    exact hO h

/-- The first family of `ChiDomProp` at the top scale (the hypothesis of the lemmas below). -/
def PieceFirstFamily (ψ' : MultiField S n M K N) (η : ℝ) : Prop :=
  ∀ q : Torus S.d (n (i + 1 + 1)),
    CubeSub (S := S) (n := n) M K (i + 1 + 1) q ((H.localHistory M K (i + 1 + 1) C).Z (i + 1 + 1)) →
    q ∈ lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1) →
    PsiTildeMulti ψ'
      (genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1 + 1) (nbhd 1 {q})) η

include hjK in
/-- **The sphere bound at a site off `Ω_{k+1}` near `Ω_{k+1}`** (R2 for the `ψ_k` datum). -/
theorem piece_psi_sphere {η : ℝ}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (ψ' : MultiField S n M K N)
    (hagK : ∀ b, ψ' (i + 1) b = pieceField H C o x (i + 1) b)
    (hψ : PieceFirstFamily H g C ψ' η)
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hsim : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈
      lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)) :
    |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re ^ 2 - 1| < η := by
  have hq : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1 :=
    mem_comp_of_not_omega H C hjK (by rw [cubeMap_bgToFine_gen]; exact hO)
  have hZ := cubeSub_Z_of_mem_comp (M := M) H C hjK hq
  have hlay := mem_layer_psi H g C hjK (x := bgToFine g H.F.hnn hjK s)
    (by rw [cubeMap_bgToFine_gen]; exact hy) (by rw [cubeMap_bgToFine_gen]; exact hO)
  have hb : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1 + 1)
        (nbhd 1 {cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨Nat.succ_pos i, (by show i + 1 ≤ K; omega), _, hlay, rfl, mem_nbhd.2 ⟨_, rfl, by simp [supDist_self]⟩⟩
  have key := (hψ _ hZ hsim).2 _ hb
  simp only [hagK] at key
  have e := piece_psi_value H g C hjK o x hv hs hO hy
  simp_rw [e]
  rw [parent_sum_sq_eq_norm_sq]
  exact key

include hjK in
/-- A data site off `Ω_{k+1}` has layer index at most `k`. -/
theorem layerIndex_le_of_not_omega
    {s : BgT g (i + 1 + 1)}
    (hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega) :
    (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK).layerIndex s ≤ i + 1 := by
  set G := locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK with hG
  by_cases hs : s ∈ G.Ω 1
  · obtain ⟨-, hle, hl⟩ := G.layerIndex_spec hs
    by_contra hgt
    have h1 : G.layerIndex s = i + 1 + 1 := by omega
    rw [h1] at hl
    have h2 : s ∈ G.Ω (i + 1 + 1) := ((GeneratingSet.mem_layer G).1 hl).1
    have h3 := locGen_top_subset g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK h2
    rw [mem_fineK1] at h3
    exact hO h3
  · rw [layerIndex_of_not_mem G hs]; exact Nat.zero_le _

omit [∀ k, NeZero (n k)] [NeZero S.L] [NeZero M] in
/-- Symmetry of `BlockAdj`. -/
theorem blockAdj_symm' {b b' : BlockPt S n M K} (h : BlockAdj b b') : BlockAdj b' b := by
  obtain ⟨x, x', hx, hx', hadj⟩ := h
  exact ⟨x', x, hx', hx, hadj.symm⟩

include hjK in
/-- Adjacent `k`-blocks for an interface pair (in either order) of two sites off `Ω_{k+1}`. -/
theorem blockAdj_psi_of_pair {s s' : BgT g (i + 1 + 1)}
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s s' ∨
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s' s)
    (hOs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hOs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega) :
    BlockAdj (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K)
      (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s')⟩ : BlockPt S n M K) := by
  have hls := layerIndex_le_of_not_omega H g C hjK hOs
  have hls' := layerIndex_le_of_not_omega H g C hjK hOs'
  rcases hp with hp | hp
  · exact blockAdj_of_interfacePair_le H g hjK hp hls hls' (by omega) (by omega)
  · exact blockAdj_symm' (blockAdj_of_interfacePair_le H g hjK hp hls' hls (by omega) (by omega))

include hjK in
/-- **The mixed pair bound** (R1 between a `ψ_{k+1}`-site and a `ψ_k`-site): for `s` over `Ω_{k+1}`
and `s'` off it with an interface pair, the multiscale field at their blocks (layers `k + 1`, `k`)
is within `η`, from the first family of `ChiDomProp` at the cube of `s'`. -/
theorem piece_mixed_pair {η : ℝ}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (ψ' : MultiField S n M K N)
    (hagK : ∀ b, ψ' (i + 1) b = pieceField H C o x (i + 1) b)
    (hagT : ∀ b, ψ' (i + 1 + 1) b = pieceField H C o x (i + 1 + 1) b)
    (hψ : PieceFirstFamily H g C ψ' η)
    {s s' : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hs' : s' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s s' ∨
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s' s)
    (hOs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hOs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy' : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s' ∈ ((H.locRH (i + 1 + 1) C).step i).Omega) :
    rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re -
      ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s' l).re) < η := by
  have hq : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s') ∈ C.1 :=
    mem_comp_of_not_omega H C hjK (by rw [cubeMap_bgToFine_gen]; exact hOs')
  have hnear : supDist (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s))
      (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s')) ≤ 1 := by
    rcases hp with hp | hp
    · rw [supDist_comm]; exact (blockAdj_of_interfacePair H g hjK hp).1
    · exact (blockAdj_of_interfacePair H g hjK hp).1
  have hZ := cubeSub_Z_of_mem_comp (M := M) H C hjK hq
  have hsim : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s') ∈
      lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1) := by
    unfold lhOmegaSim lhOmegaNb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    refine mem_nbhd.2 ⟨cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s), ?_, ?_⟩
    · exact cubeSub_lhOmega_of_omega (M := M) H C (by rw [cubeMap_bgToFine_gen]; exact hOs)
    · rw [supDist_comm]; exact hnear
  have hn : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ nbhd 1 C.1 :=
    mem_nbhd.2 ⟨_, hq, hnear⟩
  have hΩ : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1 →
      cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ (H.step (i + 1)).Omega := fun hc =>
    (omega_loc_iff H C hjK hc).1 (by rw [cubeMap_bgToFine_gen]; exact hOs)
  have hb := topBlock_mem_genBlocksIn H g hjK C hn hΩ
    (q := cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s')) hnear
  have hlay := mem_layer_psi H g C hjK (x := bgToFine g H.F.hnn hjK s')
    (by rw [cubeMap_bgToFine_gen]; exact hy') (by rw [cubeMap_bgToFine_gen]; exact hOs')
  have hb' : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s')⟩ : BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1 + 1)
        (nbhd 1 {cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s')}) :=
    ⟨Nat.succ_pos i, (by show i + 1 ≤ K; omega), _, hlay, rfl, mem_nbhd.2 ⟨_, rfl, by simp [supDist_self]⟩⟩
  have hls' := layerIndex_le_of_not_omega H g C hjK hOs'
  have hadj : BlockAdj (⟨i + 1 + 1, jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K)
      (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s')⟩ : BlockPt S n M K) := by
    rcases hp with hp | hp
    · exact blockAdj_of_interfacePair_le H g hjK hp (layerIndex_le_k _ _) hls' le_rfl (by omega)
    · exact blockAdj_symm' (blockAdj_of_interfacePair_le H g hjK hp hls' (layerIndex_le_k _ _) (by omega) le_rfl)
  have key := (hψ _ hZ hsim).1 _ hb _ hb' (Or.inr rfl) hadj
  simp only [hagK, hagT] at key
  have e := piece_theta_value H g C hjK o x hv hs hn (by rw [cubeMap_bgToFine_gen] at *; exact hOs)
  have e' := piece_psi_value H g C hjK o x hv hs' hOs' hy'
  simp_rw [e, e']
  rw [show (fun l => (pieceField H C o x (i + 1 + 1) (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjK s))) l -
      (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l) =
    fun l => (pieceField H C o x (i + 1 + 1) (jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjK s)) -
      pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l from rfl,
    rn_fun_eq_norm]
  exact key

include hjK in
/-- **The pair bound for two `ψ_k`-sites near `Ω_{k+1}`** (R1), from the first family of `ChiDomProp`
at the cube of `s`. -/
theorem piece_psi_pair {η : ℝ}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (ψ' : MultiField S n M K N)
    (hagK : ∀ b, ψ' (i + 1) b = pieceField H C o x (i + 1) b)
    (hψ : PieceFirstFamily H g C ψ' η)
    {s s' : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hs' : s' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s s' ∨
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s' s)
    (hOs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hOs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hy' : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s' ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hsim : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈
      lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)) :
    rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re -
      ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s' l).re) < η := by
  have hq : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1 :=
    mem_comp_of_not_omega H C hjK (by rw [cubeMap_bgToFine_gen]; exact hOs)
  have hadj := blockAdj_psi_of_pair H g C hjK hp hOs hOs'
  have hnear : supDist (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s'))
      (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s)) ≤ 1 := by
    rw [supDist_comm]
    exact supDist_cubeMap_le_one (show i + 1 ≤ i + 1 + 1 by omega) hjK H.F.hnn
      (cube_near_of_blockAdj H.F.hnn (show i + 1 ≤ K by omega) hadj)
  have hZ := cubeSub_Z_of_mem_comp (M := M) H C hjK hq
  have hmem : ∀ (t : BgT g (i + 1 + 1)),
      blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) t ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) t ∈ ((H.locRH (i + 1 + 1) C).step i).Omega →
      supDist (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK t))
        (cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s)) ≤ 1 →
      (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK t)⟩ : BlockPt S n M K) ∈
        genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1 + 1)
          (nbhd 1 {cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s)}) := by
    intro t ht1 ht2 ht3
    have hlay := mem_layer_psi H g C hjK (x := bgToFine g H.F.hnn hjK t)
      (by rw [cubeMap_bgToFine_gen]; exact ht2) (by rw [cubeMap_bgToFine_gen]; exact ht1)
    exact ⟨Nat.succ_pos i, (by show i + 1 ≤ K; omega), _, hlay, rfl, mem_nbhd.2 ⟨_, rfl, ht3⟩⟩
  have hb := hmem s hOs hy (by simp [supDist_self])
  have hb' := hmem s' hOs' hy' hnear
  have hadj := blockAdj_psi_of_pair H g C hjK hp hOs hOs'
  have key := (hψ _ hZ hsim).1 _ hb _ hb' (Or.inl rfl) hadj
  simp only [hagK] at key
  have e := piece_psi_value H g C hjK o x hv hs hOs hy
  have e' := piece_psi_value H g C hjK o x hv hs' hOs' hy'
  simp_rw [e, e']
  rw [show (fun l => (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s))) l -
      (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l) =
    fun l => (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)) -
      pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l from rfl,
    rn_fun_eq_norm]
  exact key

/-- The second family of `ChiDomProp` at the scale `k = i + 1` (the cubes far from `Ω_{k+1}`
and not meeting `Z_k`): the hypothesis of the lemmas below. -/
def PieceSecondFamily (ψ' : MultiField S n M K N) (η : ℝ) : Prop :=
  ∀ y : Torus S.d (n (i + 1)),
    CubeSub (S := S) (n := n) M K (i + 1) y (fineSet (S := S) (n := n) M K (i + 1 + 1) (C.1 : Set (Torus S.d (n (i + 1 + 1))))) →
    (∀ z, cubeMap n S.L M K (i + 1) z = y → z ∉ (H.localHistory M K (i + 1 + 1) C).Z (i + 1)) →
    (∀ z, cubeMap n S.L M K (i + 1) z = y →
      cubeMap n S.L M K (i + 1 + 1) z ∉ lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)) →
    PsiTildeMulti ψ' (scaleBlocksIn (i + 1) (nbhd 1 {y})) η

include hjK in
/-- The cube of a site over `C` at scale `k` is a subset of `C`. -/
theorem cubeSub_fineSet_of_cube {t : Torus S.d (M * n K * S.L ^ K)}
    (hq : cubeMap n S.L M K (i + 1 + 1) t ∈ C.1) :
    CubeSub (S := S) (n := n) M K (i + 1) (cubeMap n S.L M K (i + 1) t)
      (fineSet (S := S) (n := n) M K (i + 1 + 1) (C.1 : Set (Torus S.d (n (i + 1 + 1))))) := by
  intro z hz
  show cubeMap n S.L M K (i + 1 + 1) z ∈ C.1
  rw [← cubeMap_succ H.F.hnn (by omega) z, hz, cubeMap_succ H.F.hnn (by omega) t]
  exact hq

include hjK in
/-- **The sphere bound at a site off `Ω_{k+1}` far from `Ω_{k+1}`** (R2 for the `ψ_k` datum), from
the second family of `ChiDomProp`. -/
theorem piece_psi_sphere_far {η : ℝ}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (ψ' : MultiField S n M K N)
    (hagK : ∀ b, ψ' (i + 1) b = pieceField H C o x (i + 1) b)
    (hψ : PieceSecondFamily H C ψ' η)
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hZk : ∀ z, cubeMap n S.L M K (i + 1) z = cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) →
      z ∉ (H.localHistory M K (i + 1 + 1) C).Z (i + 1))
    (hfar : ∀ z, cubeMap n S.L M K (i + 1) z = cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) →
      cubeMap n S.L M K (i + 1 + 1) z ∉ lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)) :
    |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re ^ 2 - 1| < η := by
  have hq : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1 :=
    mem_comp_of_not_omega H C hjK (by rw [cubeMap_bgToFine_gen]; exact hO)
  have hb : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K) ∈
      scaleBlocksIn (i + 1) (nbhd 1 {cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨_, rfl, bgToFine g H.F.hnn hjK s, rfl, mem_nbhd.2 ⟨_, rfl, by simp [supDist_self]⟩⟩
  have key := (hψ _ (cubeSub_fineSet_of_cube H C hjK hq) hZk hfar).2 _ hb
  simp only [hagK] at key
  have e := piece_psi_value H g C hjK o x hv hs hO hy
  simp_rw [e]
  rw [parent_sum_sq_eq_norm_sq]
  exact key

include hjK in
/-- **The pair bound for two `ψ_k`-sites far from `Ω_{k+1}`** (R1), from the second family of
`ChiDomProp` at the `π_k`-cube of `s`. -/
theorem piece_psi_pair_far {η : ℝ}
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (ψ' : MultiField S n M K N)
    (hagK : ∀ b, ψ' (i + 1) b = pieceField H C o x (i + 1) b)
    (hψ : PieceSecondFamily H C ψ' η)
    {s s' : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hs' : s' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s s' ∨
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s' s)
    (hOs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hOs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hy' : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s' ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hZk : ∀ z, cubeMap n S.L M K (i + 1) z = cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) →
      z ∉ (H.localHistory M K (i + 1 + 1) C).Z (i + 1))
    (hfar : ∀ z, cubeMap n S.L M K (i + 1) z = cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) →
      cubeMap n S.L M K (i + 1 + 1) z ∉ lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1 + 1)) :
    rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re -
      ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s' l).re) < η := by
  have hq : cubeMap n S.L M K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈ C.1 :=
    mem_comp_of_not_omega H C hjK (by rw [cubeMap_bgToFine_gen]; exact hOs)
  have hadj := blockAdj_psi_of_pair H g C hjK hp hOs hOs'
  have hnear := cube_near_of_blockAdj H.F.hnn (show i + 1 ≤ K by omega) hadj
  have hb : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K) ∈
      scaleBlocksIn (i + 1) (nbhd 1 {cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨_, rfl, bgToFine g H.F.hnn hjK s, rfl, mem_nbhd.2 ⟨_, rfl, by simp [supDist_self]⟩⟩
  have hb' : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s')⟩ : BlockPt S n M K) ∈
      scaleBlocksIn (i + 1) (nbhd 1 {cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨_, rfl, bgToFine g H.F.hnn hjK s', rfl, mem_nbhd.2 ⟨_, rfl, by rw [supDist_comm]; exact hnear⟩⟩
  have key := (hψ _ (cubeSub_fineSet_of_cube H C hjK hq) hZk hfar).1 _ hb _ hb' (Or.inl rfl) hadj
  simp only [hagK] at key
  have e := piece_psi_value H g C hjK o x hv hs hOs hy
  have e' := piece_psi_value H g C hjK o x hv hs' hOs' hy'
  simp_rw [e, e']
  rw [show (fun l => (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s))) l -
      (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l) =
    fun l => (pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)) -
      pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l from rfl,
    rn_fun_eq_norm]
  exact key

/-- The first family of `ChiDomProp` at the scale `k = i + 1` (the cubes of `Z_k`): the hypothesis
of the lemmas for the sites over `Z_k`.  `ψw` is the multiscale field of the operator whose domain
is tested. -/
def PieceZkFamily (ψw : MultiField S n M K N) (η : ℝ) : Prop :=
  ∀ q : Torus S.d (n (i + 1)),
    CubeSub (S := S) (n := n) M K (i + 1) q ((H.localHistory M K (i + 1 + 1) C).Z (i + 1)) →
    q ∈ lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1) →
    PsiTildeMulti ψw (genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1) (nbhd 1 {q})) η

include hjK in
/-- **The sphere bound at a site off `Ω_{k+1}` over `Z_k`** (R2 for the `ψ_k` datum): the cube
`□ ⊂ Z_k ∩ Ω_k` is tested by the first family of `ChiDomProp` at the scale `k`. -/
theorem piece_psi_sphere_Zk {η : ℝ} (ψw : MultiField S n M K N)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hψ : PieceZkFamily H g C ψw η)
    {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hO : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hZk : CubeSub (S := S) (n := n) M K (i + 1) (cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s))
      ((H.localHistory M K (i + 1 + 1) C).Z (i + 1)))
    (hag : ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)) =
      pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s))) :
    |∑ l, ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re ^ 2 - 1| < η := by
  have hyk : cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) ∈ ((H.locRH (i + 1 + 1) C).step i).Omega := by
    rw [cubeMap_bgToFine_gen]; exact hy
  have hsim : cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) ∈
      lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1) := by
    unfold lhOmegaSim lhOmegaNb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact mem_nbhd.2 ⟨_, cubeSub_lhOmega_of_omega_k (M := M) H C hyk, by simp [supDist_self]⟩
  have hlay := mem_layer_psi H g C hjK (x := bgToFine g H.F.hnn hjK s)
    hyk (by rw [cubeMap_bgToFine_gen]; exact hO)
  have hb : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1)
        (nbhd 1 {cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨Nat.succ_pos i, (by show i + 1 ≤ K; omega), _, hlay, rfl, mem_nbhd.2 ⟨_, rfl, by simp [supDist_self]⟩⟩
  have key := (hψ _ hZk hsim).2 _ hb
  have e := piece_psi_value H g C hjK o x hv hs hO hy
  simp_rw [e, ← hag]
  rw [parent_sum_sq_eq_norm_sq]
  exact key

include hjK in
/-- **The pair bound for two `ψ_k`-sites, the cube of the first over `Z_k`** (R1). -/
theorem piece_psi_pair_Zk {η : ℝ} (ψw : MultiField S n M K N)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hψ : PieceZkFamily H g C ψw η)
    {s s' : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hs' : s' ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hp : IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s s' ∨
      IsInterfacePair (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) s' s)
    (hOs : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hOs' : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s' ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega)
    (hy : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hy' : blockMap (S.L ^ (i + 1) * (g.c * g.M1)) (n (i + 1)) s' ∈ ((H.locRH (i + 1 + 1) C).step i).Omega)
    (hZk : CubeSub (S := S) (n := n) M K (i + 1) (cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s))
      ((H.localHistory M K (i + 1 + 1) C).Z (i + 1)))
    (hag : ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)) =
      pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)))
    (hag' : ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s')) =
      pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) :
    rn (fun l => ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s l).re -
      ((locData g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv).Ψ s' l).re) < η := by
  have hyk : cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) ∈ ((H.locRH (i + 1 + 1) C).step i).Omega := by
    rw [cubeMap_bgToFine_gen]; exact hy
  have hsim : cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s) ∈
      lhOmegaSim (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) (i + 1) := by
    unfold lhOmegaSim lhOmegaNb
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by omega))]
    exact mem_nbhd.2 ⟨_, cubeSub_lhOmega_of_omega_k (M := M) H C hyk, by simp [supDist_self]⟩
  have hadj := blockAdj_psi_of_pair H g C hjK hp hOs hOs'
  have hnear := cube_near_of_blockAdj H.F.hnn (show i + 1 ≤ K by omega) hadj
  have hlay := mem_layer_psi H g C hjK (x := bgToFine g H.F.hnn hjK s)
    hyk (by rw [cubeMap_bgToFine_gen]; exact hOs)
  have hlay' := mem_layer_psi H g C hjK (x := bgToFine g H.F.hnn hjK s')
    (by rw [cubeMap_bgToFine_gen]; exact hy') (by rw [cubeMap_bgToFine_gen]; exact hOs')
  have hb : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)⟩ : BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1)
        (nbhd 1 {cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨Nat.succ_pos i, (by show i + 1 ≤ K; omega), _, hlay, rfl, mem_nbhd.2 ⟨_, rfl, by simp [supDist_self]⟩⟩
  have hb' : (⟨i + 1, jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s')⟩ : BlockPt S n M K) ∈
      genBlocksIn (chiDomGen H g (i + 1 + 1) C) (i + 1)
        (nbhd 1 {cubeMap n S.L M K (i + 1) (bgToFine g H.F.hnn hjK s)}) :=
    ⟨Nat.succ_pos i, (by show i + 1 ≤ K; omega), _, hlay', rfl,
      mem_nbhd.2 ⟨_, rfl, by rw [supDist_comm]; exact hnear⟩⟩
  have key := (hψ _ hZk hsim).1 _ hb _ hb' (Or.inl rfl) hadj
  have e := piece_psi_value H g C hjK o x hv hs hOs hy
  have e' := piece_psi_value H g C hjK o x hv hs' hOs' hy'
  simp_rw [e, e', ← hag, ← hag']
  rw [show (fun l => (ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s))) l -
      (ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l) =
    fun l => (ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s)) -
      ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine g H.F.hnn hjK s'))) l from rfl,
    rn_fun_eq_norm]
  exact key

end PieceLayers

end Balaban.LargeField
