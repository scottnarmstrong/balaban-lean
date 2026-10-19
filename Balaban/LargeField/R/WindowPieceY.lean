/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowPieceAssemble
public import Balaban.LargeField.R.WindowThetaY

/-!
# The real domain of a piece datum with the outside tested by `χ_{k+1}(Y)` (blocker 4)

`piece_inDomainR_of_chiY`: the datum of a piece `C` (scale `k + 1`) lies in the real domain
`Ψ̃(G; ν, η)` when the domain conditions of the piece hold (the first and second families of
`ChiDomProp`, the first family at scale `k` for the multiscale field of the operator) and the data
sites outside `C` are tested by `χ_{k+1}(Y)` of the post-weight field `ψk` of the window point
(`WindowPostSupport`), `Y = Z_{k+1}ᶜ`.  The data sites outside `C` lie over `Y`
(`dataSite_cube_mem_Y`: the components of `Z^pre_{k+1}` are separated) and their top blocks lie in
`V` (`dataSite_block_mem_Vblk`), where `ψk` agrees with the output off the zero set.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

section PieceY

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K : ℕ} {M : ℕ} [NeZero M]
  [NeZero S.L] {N i : ℕ} (H : RegionHistory S n R k0 K) (g : Geo S n R M) (C : H.Comp (i + 1 + 1))
  (hjK : i + 1 + 1 ≤ K)

include hjK in
/-- The top block of a data site of the local family of `C` lies in `V`. -/
theorem dataSite_block_mem_Vblk {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK)) :
    jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine g H.F.hnn hjK s) ∈
      Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) := by
  have h := dataSite_cube_mem_nbhd_comp H g C hjK hs
  show blockCube S n M K (i + 1 + 1) _ ∈ Vcubes R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1)
  unfold blockCube Vcubes
  rw [cubeMap_eq_comp H.F.hnn hjK, cubeMap_bgToFine_gen]
  unfold thick
  rw [Nat.add_sub_cancel]
  rw [nbhd_nbhd]
  refine nbhd_mono (le_of_eq (by omega)) ?_ h
  intro q hq
  exact cubeSub_Z_of_mem_comp (M := M) H C hjK hq



/-- `χ_k(Y) ≠ 0` implies `χ_k(Y') ≠ 0` for `Y' ⊆ Y` (a product of factors, each nonzero). -/
theorem chiY_ne_zero_of_subset {m₁ : ℕ} {ϱ : ℝ} {j : ℕ} (Cx : Def7.SFCtx S n R M K N (j + 1) m₁ ϱ)
    {Y Y' : Set (Torus S.d (n (j + 1)))} (hYY : Y' ⊆ Y)
    {ψk : BlockAt S n M K (j + 1) → EuclideanSpace ℝ (Fin N)} {hv : EuclideanSpace ℝ (Fin N)}
    (h : Cx.chiY Y ψk hv ≠ 0) : Cx.chiY Y' ψk hv ≠ 0 := by
  unfold Def7.SFCtx.chiY cubeProd at h ⊢
  rw [Finset.prod_ne_zero_iff] at h ⊢
  intro y hy
  exact h y (by simp only [cubeFin, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢; exact hYY hy)

variable {m₁ : ℕ} {ϱ : ℝ}

include hjK in
/-- The small-field region `Y = Z_{k+1}ᶜ` contains the cubes of the data sites that are not over
`C`, and `C` is disjoint from `Y` when `C` is retained. -/
theorem dataSite_cube_mem_Y {s : BgT g (i + 1 + 1)}
    (hs : s ∈ dataSites (locGen g (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK))
    (hq : blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∉ C.1) :
    blockMap (S.L ^ (i + 1 + 1) * (g.c * g.M1)) (n (i + 1 + 1)) s ∈ ((H.step (i + 1 + 1)).Z)ᶜ := by
  intro hZ
  exact dataSite_cube_not_mem_Zp H g C hjK hs hq (mem_finOf.2 (H.Z_subset_Zpre _ hZ))

omit [NeZero M] [NeZero S.L] in
/-- A retained component is disjoint from `Y = Z_{k+1}ᶜ`. -/
theorem comp_notMem_Y {q : Torus S.d (n (i + 1 + 1))} (hret : C.1 ∉ H.rem (i + 1 + 1))
    (hq : q ∈ ((H.step (i + 1 + 1)).Z)ᶜ) : q ∉ C.1 := fun hC => hq ((H.mem_Z_iff hC).2 hret)

include hjK in
/-- **The datum of a piece lies in the real domain, the outside being tested by `χ_{k+1}(Y)`.**
`Cx` is the small-field context of scale `k + 1`, `Y = Z_{k+1}ᶜ`, `ψk` the post-weight field of the
window point (it agrees with the output `o` on the blocks of `V` off the zero set `Z0`, which lies over
`C`), and `χ_{k+1}(Y)(ψk) ≠ 0`.  The remaining hypotheses are the domain conditions of the piece
(first and second family of `ChiDomProp` at the scales `k + 1`, `k`; the first family at scale `k`
for the multiscale field `ψw` of the operator) and the typing data (`ν ≥ 0`, `|h| = 1`,
`2 ν L^{2(k+1)} < η²`). -/
theorem piece_inDomainR_of_chiY {η1 η2 η3 ν : ℝ} (Cx : Def7.SFCtx S n R M K N (i + 1 + 1) m₁ ϱ)
    (ψw : MultiField S n M K N)
    (o : OutT N R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1))
    (x : NewCfg N (H.localHistory M K (i + 1 + 1) C) (i + 1)) (hv : EuclideanSpace ℝ (Fin N))
    (hν : 0 ≤ ν) (hunit : ‖hv‖ = 1)
    (hη : 0 < max (max η1 η2) (max η3 (max (3 * Cx.cs.delta (i + 1 + 1))
      ((S.d + 1) * Cx.cs.delta (i + 1 + 1) * (2 + (S.d + 1) * Cx.cs.delta (i + 1 + 1))))))
    (hmass : 2 * ν * ((S.L : ℝ) ^ (i + 1 + 1)) ^ 2 < (max (max η1 η2) (max η3 (max (3 * Cx.cs.delta (i + 1 + 1))
      ((S.d + 1) * Cx.cs.delta (i + 1 + 1) * (2 + (S.d + 1) * Cx.cs.delta (i + 1 + 1)))))) ^ 2)
    (ψ' : MultiField S n M K N)
    (hagT : ∀ b, ψ' (i + 1 + 1) b = pieceField H C o x (i + 1 + 1) b)
    (hagK : ∀ b, ψ' (i + 1) b = pieceField H C o x (i + 1) b)
    (hF1 : PieceFirstFamily H Cx.geo C ψ' η1) (hF2 : PieceSecondFamily H C ψ' η2)
    (hFZ : PieceZkFamily H Cx.geo C ψw η3)
    (hag : ∀ t : BgT Cx.geo (i + 1 + 1),
      t ∈ dataSites (locGen Cx.geo (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (Cx.geo.c * Cx.geo.M1)) (n (i + 1 + 1)) t ∉ ((H.locRH (i + 1 + 1) C).step (i + 1)).Omega →
      ψw (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine Cx.geo H.F.hnn hjK t)) =
        pieceField H C o x (i + 1) (jBlock S.d S.L (M * n K) K (i + 1) (bgToFine Cx.geo H.F.hnn hjK t)))
    (ψk : BlockAt S n M K (i + 1 + 1) → EuclideanSpace ℝ (Fin N))
    (hχ : Cx.chiY ((H.step (i + 1 + 1)).Z)ᶜ ψk hv ≠ 0)
    (HB : BgHyp S.d S.L (i + 1 + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (i + 1 + 1)))
    (Z0 : Set (BlockAt S n M K (i + 1 + 1)))
    (hZ0C : ∀ b ∈ Z0, blockCube S n M K (i + 1 + 1) b ∈ C.1)
    (hψk : ∀ b ∈ Vblk R (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1), b ∉ Z0 → ψk b = outField N o b) :
    InDomainR (locGen Cx.geo (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) ν
      (max (max η1 η2) (max η3 (max (3 * Cx.cs.delta (i + 1 + 1))
        ((S.d + 1) * Cx.cs.delta (i + 1 + 1) * (2 + (S.d + 1) * Cx.cs.delta (i + 1 + 1))))))
      (locData Cx.geo (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK o x hv) := by
  have hYZ : ∀ y ∈ ((H.step (i + 1 + 1)).Z)ᶜ \ C.1, y ∉ (H.locRH (i + 1 + 1) C).F.Zp (i + 1 + 1) := by
    intro y hy hy'
    rw [locRH_Zp hjK C] at hy'
    exact hy.2 hy'
  have hχ' : Cx.chiY (((H.step (i + 1 + 1)).Z)ᶜ \ C.1) ψk hv ≠ 0 := chiY_ne_zero_of_subset Cx Set.sdiff_subset hχ
  have hψ : ∀ t : BgT Cx.geo (i + 1 + 1),
      t ∈ dataSites (locGen Cx.geo (H.locRH (i + 1 + 1) C) (i + 1) C.1 (locComp_mem H hjK C) hjK) →
      blockMap (S.L ^ (i + 1 + 1) * (Cx.geo.c * Cx.geo.M1)) (n (i + 1 + 1)) t ∉ C.1 →
      ψk (blkToBlock Cx.geo (H.locRH (i + 1 + 1) C).F.hnn hjK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1 + 1) t)) =
        outField N o (blkToBlock Cx.geo (H.locRH (i + 1 + 1) C).F.hnn hjK
          (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1 + 1) t)) := by
    intro t ht hq
    have hb1 : blkToBlock Cx.geo H.F.hnn hjK
        (jBlock S.d S.L (Cx.geo.M1 * (Cx.geo.c * n (i + 1 + 1))) (i + 1 + 1) (i + 1 + 1) t) =
        jBlock S.d S.L (M * n K) K (i + 1 + 1) (bgToFine Cx.geo H.F.hnn hjK t) :=
      (jBlock_bgToFine_gen Cx.geo H.F.hnn hjK le_rfl t).symm
    show ψk (blkToBlock Cx.geo H.F.hnn hjK _) = outField N o (blkToBlock Cx.geo H.F.hnn hjK _)
    rw [hb1]
    refine hψk _ (dataSite_block_mem_Vblk H Cx.geo C hjK ht) fun hb0 => ?_
    have := hZ0C _ hb0
    rw [blockCube, cubeMap_eq_comp H.F.hnn hjK, cubeMap_bgToFine_gen] at this
    exact hq this
  refine piece_inDomainR H Cx.geo C hjK ψw o x hv hν hunit hη hmass ψ' hagT hagK hF1 hF2 hFZ hag ?_ ?_
  · intro t ht hq
    refine lt_of_lt_of_le (locData_sphere_over_Y Cx (H.locRH (i + 1 + 1) C) C.1 (locComp_mem H hjK C) hjK
      _ ψk hv hχ' HB hYZ o x ht ⟨dataSite_cube_mem_Y H Cx.geo C hjK ht hq, hq⟩ (hψ t ht hq)) ?_
    · exact le_max_right _ _
  · intro t t' ht ht' hp hq hq' hO hO'
    refine lt_of_lt_of_le (locData_pair_over_Y Cx (H.locRH (i + 1 + 1) C) C.1 (locComp_mem H hjK C) hjK
      _ ψk hv hχ' hYZ o x ht ht' hp ⟨dataSite_cube_mem_Y H Cx.geo C hjK ht hq, hq⟩ hO' (hψ t ht hq) (hψ t' ht' hq')) ?_
    · exact le_max_left _ _

end PieceY

end Balaban.LargeField
