/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomPieces
public import Balaban.LargeField.R.WindowDuPt

/-!
# The domain premises of the window conversion at a window point (blocker 4)

`window_pieces_domain`: at a window point where the kernel of the operator of `Z` is nonzero and the
output is in the support of the post weight (`WindowPostSupport`), every piece datum of the window family
is in `PieceDomain` with the radius `pieceRadiusWin S cs (j_i)` (the cases of the window piece and of
the ancestor pieces, with the index casts `jf`/`cf`/`ou`/`xu` of the window family).

`window_domain_facts`: the premises of `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` on the domain of
the piece data (the three families of `XiCOneReal` and `InDomainR … δ_l`, in the explicit form of
`pieceChain`) from `PieceDomain` and the size conditions on the radii and masses.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.LargeField.Def7 RegionHistory

theorem pieceRadiusWin_pos (S : Setting) (cs : OpConsts) (hδpos : ∀ j, 0 < cs.delta j) (j : ℕ) :
    0 < pieceRadiusWin S cs j :=
  lt_of_lt_of_le (show 0 < 3 * cs.delta (j + 1) by linarith [hδpos (j + 1)])
    (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))

section Facts

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ}
  {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **Every piece datum of the window family is in `PieceDomain`** at a window point of nonzero
kernel in the support of the post weight. -/
theorem window_pieces_domain {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hW : H.RipeWindow (m' + 1) Z)
    (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hk1p : 1 ≤ S.k1 (m' + 1))
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
    {m₁ : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (m' + 1) m₁ ϱ) (hgeo : Cx.geo = geo)
    (hcs : Cx.cs = cs)
    (Z0 : Set (BlockAt S n M K (m' + 1))) (hpost : WindowPostSupport H Cx hv Z0 o)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (HB : BgHyp S.d S.L (m' + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (m' + 1)))
    (hδpos : ∀ j, 0 < cs.delta j)
    (jf : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'),
      Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → ℕ)
    (cf : ∀ i, H.Comp (jf i + 1))
    (hfam : ∀ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) =
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩))
    (hjK : ∀ i, jf i + 1 ≤ K)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hou0 : HEq (ou none) o)
    (hxu0 : HEq (xu none) (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm
        (hq (m' + 1) (Nat.lt_succ_of_le hW.k1_le_sub_one) Z (Desc.refl Z))) x))
    (hou1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (ou (some ⟨j, P, c⟩)) (ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
          (mem_ancFin.mp P.2) x)))
    (hxu1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) :
    ∀ i, PieceDomain (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv) (pieceRadiusWin S cs (jf i)) := by
  intro i
  have hk1 := hW.k1_le_sub_one
  cases i with
  | none =>
    exact window_piece_none_domain geo cs SD KD hm hq (Nat.lt_succ_of_le hk1) hk1p hk1 o x hv hunit
      hK Cx hgeo hcs Z0 hpost hZ0 HB hδpos (jf none) (cf none) (hfam none) (hjK none)
      (ou none) (xu none) hou0 hxu0
  | some s =>
    obtain ⟨j, P, c⟩ := s
    exact window_piece_some_domain geo cs SD KD hm hq hk1p hk1 ρ hρ o x hv hunit hK hδpos j P c
      (jf _) (cf _) (hfam _) (hjK _) (ou _) (xu _) (hou1 j P c) (hxu1 j P c)

/-- With `β ≠ 0` the layer coefficients of the chain at the scale `j + 1` are the weights `a_n`. -/
theorem chain_a_base (S : Setting) [NeZero S.L] (cs : OpConsts) {j : ℕ} (hβ : cs.beta (j + 1) ≠ 0) :
    (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 /
      betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0)) = cs.aw := by
  have hb : betaCanon S.d S.L (cs.beta (j + 1)) (j + 1) 0 ≠ 0 := by
    unfold betaCanon
    exact div_ne_zero hβ (pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne S.L)))
  funext l
  rw [div_self hb, mul_one]

open Classical in
/-- **The domain premises of `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` on the piece data**: the
three families of `XiCOneReal` (in the explicit form of `pieceChain`: the coefficients
`a_m = a · β^{(j+1)}_{j+1} / β^{(m)}_m`, the masses `μ_act(m)`, the radius `ε_{j_i+1}`) and
`InDomainR … δ_l`, from `PieceDomain` of the piece data and the size conditions on the radii
(`pieceRadiusWin ≤ δ_x(j_i) ≤ c₁`, `(2K₁+2) δ_x ≤ ε`, `pieceRadiusWin ≤ δ_l`) and on the masses
(`2 μ_act(m) L^{2(j_i+1)} < δ_x(j_i)²`, `< δ_l²`). -/
theorem window_domain_facts {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hW : H.RipeWindow (m' + 1) Z)
    (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (hk1p : 1 ≤ S.k1 (m' + 1))
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
    {m₁ : ℕ} {ϱ : ℝ} (Cx : SFCtx S n R M K N (m' + 1) m₁ ϱ) (hgeo : Cx.geo = geo)
    (hcs : Cx.cs = cs)
    (Z0 : Set (BlockAt S n M K (m' + 1))) (hpost : WindowPostSupport H Cx hv Z0 o)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (HB : BgHyp S.d S.L (m' + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (m' + 1)))
    (hδpos : ∀ j, 0 < cs.delta j)
    (jf : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'),
      Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → ℕ)
    (cf : ∀ i, H.Comp (jf i + 1))
    (hfam : ∀ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) =
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hjK : ∀ i, jf i + 1 ≤ K)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hou0 : HEq (ou none) o)
    (hxu0 : HEq (xu none) (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A geo cs SD KD hm
        (hq (m' + 1) (Nat.lt_succ_of_le hW.k1_le_sub_one) Z (Desc.refl Z))) x))
    (hou1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (ou (some ⟨j, P, c⟩)) (ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1
          (mem_ancFin.mp P.2) x)))
    (hxu1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)))
    (α α₀ δl : ℝ) (δx : ℕ → ℝ) (ak : ℕ → ℝ)
    (hμ0 : ∀ m, 0 ≤ cs.muAct m)
    (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0)
    (hBj : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1) cs.aw (cs.muAct (jf i + 1)))
    (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (cs.muAct m))
    (hBaw : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1) cs.aw (cs.muAct (m' + 1)))
    (hBak : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1) ak (cs.muAct (m' + 1)))
    (hδx_rad : ∀ i, pieceRadiusWin S cs (jf i) ≤ δx (jf i))
    (hδx_c1 : ∀ i, δx (jf i) ≤ bgC1 S.d S.L N)
    (hδx_eps : ∀ i, (2 * bgK1 S.d S.L N + 2) * δx (jf i) ≤ epsSeq S.L α α₀ (jf i + 1))
    (hδx_mass : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 →
      2 * cs.muAct m * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 < δx (jf i) ^ 2)
    (hδl_rad : ∀ i, pieceRadiusWin S cs (jf i) ≤ δl)
    (hδl_mass : ∀ i, 2 * cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 < δl ^ 2) :
    (∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 →
      XiCOneReal (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i))
        (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
          betaCanon S.d S.L (cs.beta m) m 0)) (cs.muAct m) (epsSeq S.L α α₀ (jf i + 1))
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)) ∧
    (∀ i, XiCOneReal (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) cs.aw (cs.muAct (m' + 1))
        (epsSeq S.L α α₀ (jf i + 1))
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)) ∧
    (∀ i, XiCOneReal (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1))
        (epsSeq S.L α α₀ (jf i + 1))
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)) ∧
    (∀ i, InDomainR (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)) := by
  have hpd := window_pieces_domain geo cs SD KD hm hW hq hk1p ρ hρ o x hv hunit hK Cx hgeo hcs
    Z0 hpost hZ0 HB hδpos jf cf hfam hjK ou xu hou0 hxu0 hou1 hxu1
  have hδ0 : ∀ i, 0 < δx (jf i) := fun i =>
    lt_of_lt_of_le (pieceRadiusWin_pos S cs hδpos _) (hδx_rad i)
  refine ⟨fun i m h1 h2 => ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
  · have hD := hpd i (cs.muAct m) (δx (jf i)) (hδx_rad i) (hμ0 m) (hδx_mass i m h1 h2)
    by_cases hm1 : m = jf i + 1
    · subst hm1
      rw [chain_a_base S cs (hβ i _ le_rfl h2)]
      exact xiCOneReal_of_inDomainR (hBj i) (hδ0 i) (hδx_c1 i) (hδx_eps i) hD
    · exact xiCOneReal_of_inDomainR (hBn i m (by omega) h2) (hδ0 i) (hδx_c1 i) (hδx_eps i) hD
  · have h1 : jf i + 1 ≤ m' + 1 := by have := (hjf i).2; omega
    exact xiCOneReal_of_inDomainR (hBaw i) (hδ0 i) (hδx_c1 i) (hδx_eps i)
      (hpd i (cs.muAct (m' + 1)) (δx (jf i)) (hδx_rad i) (hμ0 _) (hδx_mass i (m' + 1) h1 le_rfl))
  · have h1 : jf i + 1 ≤ m' + 1 := by have := (hjf i).2; omega
    exact xiCOneReal_of_inDomainR (hBak i) (hδ0 i) (hδx_c1 i) (hδx_eps i)
      (hpd i (cs.muAct (m' + 1)) (δx (jf i)) (hδx_rad i) (hμ0 _) (hδx_mass i (m' + 1) h1 le_rfl))
  · exact hpd i (cs.muAct (m' + 1)) δl (hδl_rad i) (hμ0 _) (hδl_mass i)

/-- Above the scale `k₀` no component is removed, so the window component is retained. -/
theorem window_retained_of_gt {m' : ℕ} {Z : H.Comp (m' + 1)} (h : k0 < m' + 1) :
    Z.1 ∉ H.rem (m' + 1) := by
  rw [H.rem_empty (m' + 1) (Or.inr h)]
  exact Finset.notMem_empty _

end Facts

end Balaban.LargeField
