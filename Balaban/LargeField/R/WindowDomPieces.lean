/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowPieceParent
public import Balaban.LargeField.R.WindowDomAnc
public import Balaban.LargeField.R.WindowDomMass
public import Balaban.LargeField.R.WindowDomXi
public import Balaban.LargeField.R.WindowPostSupport

/-!
# The small-radius real domain of the piece data at the window point (blocker 4)

At a window point `(o, x)` where the kernel of the operator of `Z` is nonzero and the output is in the
support of the post weight (`WindowPostSupport`), every piece datum `locData … (ou i) (xu i) hv` lies in
the real domain `Ψ̃(G_i; ν, δ)` of every radius `δ ≥ r_{j_i}` and every mass `ν ≥ 0` with
`2 ν L^{2(j_i+1)} < δ²` (`PieceDomain`), where `r_j` is the largest radius of the families used:

* the window piece (`j = m'`): the first and second families of `ChiDomAt` of `Z` and the test by
  `χ_{k+1}(Y)` of the post-weight field outside the component (`piece_inDomainR_of_chiDomAt`);
* an ancestor piece `c` of scale `j + 1`, `k₁ ≤ j < m'`: the families of `ChiDomAt` of `c` at the point
  read from its successor `P`, and the second family of `ChiDomAt` of `P` at scale `j + 1` outside `c`
  (`piece_inDomainR_of_parent`, `chiDomAt_anc_of_locOp_kernel_ne_zero`).

`window_piece_none_domain` and `window_piece_some_domain` identify the index casts `jf`/`cf` of the
window family with these data.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.LargeField.Def7 RegionHistory

/-- The radius of the datum of an ancestor piece of scale `j + 1`
(`max (3dLδ_j, 3δ_j, 3dLδ_{j-1}, 3δ_{j+1})`). -/
noncomputable def pieceRadiusAnc (S : Setting) (cs : OpConsts) (j : ℕ) : ℝ :=
  max (max (3 * S.d * S.L * cs.delta j) (3 * cs.delta j))
    (max (3 * S.d * S.L * cs.delta (j - 1)) (3 * cs.delta (j + 1)))

/-- The radius of the datum of the window piece of scale `j + 1`: the radius of an ancestor piece and
the radius `(d+1)δ_{j+1}(2 + (d+1)δ_{j+1})` of the test by `χ_{j+1}(Y)`. -/
noncomputable def pieceRadiusWin (S : Setting) (cs : OpConsts) (j : ℕ) : ℝ :=
  max (max (3 * S.d * S.L * cs.delta j) (3 * cs.delta j))
    (max (3 * S.d * S.L * cs.delta (j - 1)) (max (3 * cs.delta (j + 1))
      ((S.d + 1) * cs.delta (j + 1) * (2 + (S.d + 1) * cs.delta (j + 1)))))

theorem pieceRadiusAnc_le_win (S : Setting) (cs : OpConsts) (j : ℕ) :
    pieceRadiusAnc S cs j ≤ pieceRadiusWin S cs j := by
  unfold pieceRadiusAnc pieceRadiusWin
  refine max_le_max le_rfl (max_le_max le_rfl ?_)
  exact le_max_left _ _

section Domain

variable {d L N₀ k N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- **The datum is in the real domain of every larger radius and every mass small against it.** -/
def PieceDomain {G : GeneratingSet d L N₀ k ϱ} (D : BgData G N) (rad : ℝ) : Prop :=
  ∀ μ δ' : ℝ, rad ≤ δ' → 0 ≤ μ → 2 * μ * ((L : ℝ) ^ k) ^ 2 < δ' ^ 2 → InDomainR G μ δ' D

theorem pieceDomain_of_inDomainR {G : GeneratingSet d L N₀ k ϱ} {D : BgData G N} {η rad : ℝ}
    {hv : Fin N → ℝ} (hD : InDomainR G 0 η D) (hη : η ≤ rad) (hhv : ∑ i, hv i ^ 2 = 1)
    (hDh : ∀ x ∈ G.Ω 1, ∀ i, D.h x i = (hv i : ℂ)) : PieceDomain D rad :=
  fun _ _ hδ hμ hmass => inDomainR_mass_change hD (hη.trans hδ) hhv hDh hμ hmass

end Domain

section Piece

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- A block of `Z_k` of the localized history of `C` lies over a cube of `C`. -/
theorem blockCube_mem_of_zblk {i : ℕ} (C : H.Comp (i + 1 + 1)) (hjK : i + 1 + 1 ≤ K)
    {b : BlockAt S n M K (i + 1 + 1)} (hb : ZBlk (H.localHistory M K (i + 1 + 1) C) (i + 1 + 1) b) :
    blockCube S n M K (i + 1 + 1) b ∈ C.1 := by
  obtain ⟨x, hx⟩ := exists_site_in_block hjK b
  have h := (hb x hx).2
  rw [blockCube_eq_cubeMap H.F.hnn hjK hx]
  exact h


section Window

variable (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The window piece**: the datum of the piece whose component is the window component `Z` is in the
real domain, for the index data `(j₁, c₁)` of the window family identified with `(m', Z)`. -/
theorem window_piece_none_domain {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hmk : S.k1 (m' + 1) < m' + 1) (hk1p : 1 ≤ S.k1 (m' + 1)) (hk1 : S.k1 (m' + 1) ≤ m')
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
    {m₁ : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (m' + 1) m₁ ϱ) (hgeo : Cx.geo = geo)
    (hcs : Cx.cs = cs)
    (Z0 : Set (BlockAt S n M K (m' + 1))) (hvp : EuclideanSpace ℝ (Fin N)) (hpost : WindowPostSupport H Cx hvp Z0 o)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (HB : BgHyp S.d S.L (m' + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (m' + 1)))
    (hδpos : ∀ j, 0 < cs.delta j)
    (j1 : ℕ) (c1 : H.Comp (j1 + 1)) (hf : (⟨j1, c1⟩ : Σ j, H.Comp (j + 1)) = ⟨m', Z⟩)
    (hjK1 : j1 + 1 ≤ K)
    (ou1 : OutT N R (locHist (H.locRH (j1 + 1) c1) M K (j1 + 1) c1.1) (j1 + 1))
    (xu1 : NewCfg N (locHist (H.locRH (j1 + 1) c1) M K (j1 + 1) c1.1) j1)
    (hou : HEq ou1 o)
    (hxu : HEq xu1 (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) x)) :
    PieceDomain (locData geo (H.locRH (j1 + 1) c1) j1 c1.1 (locComp_mem H hjK1 c1) hjK1 ou1 xu1 hv)
      (pieceRadiusWin S cs j1) := by
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.1 hf
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hou
  obtain rfl := eq_of_heq hxu
  obtain ⟨i0, rfl⟩ : ∃ i0, j1 = i0 + 1 := ⟨j1 - 1, by omega⟩
  subst hgeo hcs
  have hχd := chiDomAt_of_locOp_kernel_ne_zero Cx.geo Cx.cs SD KD hm _ _ x hv hK
  obtain ⟨ψk, hψ, hχ, -⟩ := hpost
  have hd1 := hδpos (i0 + 1 + 1)
  have hη : 0 < pieceRadiusWin S Cx.cs (i0 + 1) :=
    lt_of_lt_of_le (show 0 < 3 * Cx.cs.delta (i0 + 1 + 1) by linarith)
      (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
  have hD := piece_inDomainR_of_chiDomAt H _ hjK1 (ν := 0) Cx Cx.cs (newVars_sub_locOp_A Cx.geo Cx.cs SD KD hm (hq _ hmk _ (Desc.refl _))) _ _ hχd hv (le_refl 0)
    hunit hη (by simp only [mul_zero, zero_mul]; exact pow_pos hη 2) ψk hvp hχ HB
    {b | b ∈ Z0 ∧ b ∈ Vblk R (H.localHistory M K (i0 + 1 + 1) _) (i0 + 1 + 1)}
    (fun b hb => blockCube_mem_of_zblk _ hjK1 (hZ0 b hb.2 hb.1))
    (fun b hb hb0 => hψ b hb fun h0 => hb0 ⟨h0, hb⟩)
  refine pieceDomain_of_inDomainR (hv := fun l => hv l) hD le_rfl ?_ ?_
  · rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  · intro y hy l
    exact locData_h_eq H Cx.geo _ hjK1 _ _ hv hy l

open Classical in
/-- **An ancestor piece**: the datum of the piece of the ancestor `c ∈ parts_{j+1}(P)`, `P` a successor
in the lineage of the window component `Z`, is in the real domain, for the index data `(j₁, c₁)` of the
window family identified with `(j, c)`. -/
theorem window_piece_some_domain {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hk1p : 1 ≤ S.k1 (m' + 1)) (hk1 : S.k1 (m' + 1) ≤ m')
    (ρ : ∀ (s : ℕ), S.k1 (m' + 1) ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : S.k1 (m' + 1) ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
    (hδpos : ∀ j, 0 < cs.delta j)
    (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
    (c : ↥(H.parts (j.1 + 1) P.1))
    (j1 : ℕ) (c1 : H.Comp (j1 + 1)) (hf : (⟨j1, c1⟩ : Σ j, H.Comp (j + 1)) = ⟨j.1, c.1⟩)
    (hjK1 : j1 + 1 ≤ K)
    (ou1 : OutT N R (locHist (H.locRH (j1 + 1) c1) M K (j1 + 1) c1.1) (j1 + 1))
    (xu1 : NewCfg N (locHist (H.locRH (j1 + 1) c1) M K (j1 + 1) c1.1) j1)
    (hou : HEq ou1 (ancOut (N := N) (R := R) c.1 P.1
      (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x)))
    (hxu : HEq xu1 (newRestrict (H.localHistory M K (j.1 + 1) c.1)
      (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
        (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
          (desc_of_parts c.2 (mem_ancFin.mp P.2))))
      (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
        (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) :
    PieceDomain (locData geo (H.locRH (j1 + 1) c1) j1 c1.1 (locComp_mem H hjK1 c1) hjK1 ou1 xu1 hv)
      (pieceRadiusWin S cs j1) := by
  have hχd := chiDomAt_anc_of_locOp_kernel_ne_zero geo cs SD KD _ m' hk1 hm Z hq ρ hρ o x hv hK j P c
  obtain ⟨oP, hχP⟩ := chiDomAt_exists_of_ancFin geo cs SD KD _ m' hk1 hm Z hq ρ hρ o x hv hK j P
  have hjP : j.1 + 1 + 1 ≤ K := (mem_ancFin.mp P.2).le.trans hm
  have hnewc := newVars_sub_locOp_A geo cs SD KD (lab := lab) (hH := hH)
    ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
    (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
      (desc_of_parts c.2 (mem_ancFin.mp P.2)))
  obtain ⟨j0, hj0⟩ := j
  obtain ⟨i0, rfl⟩ : ∃ i0, j0 = i0 + 1 := ⟨j0 - 1, by have := (Finset.mem_Ico.mp hj0).1; omega⟩
  obtain ⟨rfl, hc⟩ := Sigma.mk.inj_iff.1 hf
  obtain rfl := eq_of_heq hc
  obtain rfl := eq_of_heq hou
  obtain rfl := eq_of_heq hxu
  have hd1 := hδpos (i0 + 1 + 1)
  have hη : 0 < pieceRadiusAnc S cs (i0 + 1) :=
    lt_of_lt_of_le (show 0 < 3 * cs.delta (i0 + 1 + 1) by linarith)
      (le_max_of_le_right (le_max_right _ _))
  have hD := piece_inDomainR_of_parent H geo c.1 P.1 c.2 hjP hjK1 cs (ν := 0) hnewc _ _ hχd hv oP _ hχP
    (fun b hb => by unfold outField ancOut; simp [hb]) (le_refl 0) hunit hη
    (by simp only [mul_zero, zero_mul]; exact pow_pos hη 2)
  refine pieceDomain_of_inDomainR (hv := fun l => hv l) hD (pieceRadiusAnc_le_win S cs _) ?_ ?_
  · rw [parent_sum_sq_eq_norm_sq, hunit]; norm_num
  · intro y hy l
    exact locData_h_eq H geo _ hjK1 _ _ hv hy l

end Window

end Piece

end Balaban.LargeField
