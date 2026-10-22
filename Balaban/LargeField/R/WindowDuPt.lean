/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowLiftConv
public import Balaban.LargeField.R.WindowDuConv
public import Balaban.LargeField.R.WindowDuAgree

/-!
# The window conversion at the window point and the reference datum `Du` (blocker 4)

`sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` is `sum_mainActionLoc_eq_gen_of_flow_window_pt` with the
window action `A_{X_win}(a_k, 0, Du, φ_Du)` of the hid datum `Du` (external field `0`, values on `Ω₁` the
variables of the window point read at the layer index of the window generating set, any values on the
collar) in place of the physical datum: `Du` agrees with the physical datum on the balls around the
pieces (`du_ball_eq`; the layer indices of the window and of the parent generating sets agree there,
`window_layer_eq_full_ball`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

universe u

section Pt

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- **sum_mainActionLoc_eq_gen_of_flow_window_pt_Du with the constants first**: the constants `K_w, δ_w, K_s, δ_s, K_w', δ_m` are produced before the window point and all the data, and depend only on `(d, L, N)`.  The landed `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` is this theorem at the data. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_pt_Du_constsP (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Kw δw Ks δs Kw' δm : ℝ, 0 < Kw ∧ 0 < δw ∧ 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 g cs N κs) (KD : KeptData k0 g cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5} (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y) (ρ : ∀ (s : ℕ), S.k1 (m' + 1) ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp g cs SD KD hH lab (m' + 1) hmK Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp g cs SD KD hH lab s (hd.le.trans hmK) P).A) (_ : ∀ s (hs : S.k1 (m' + 1) ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl g cs SD KD hmK hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩) (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1)) (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp g cs SD KD hH lab (m' + 1) hmK Z).A) (jf : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (_ : ∀ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩)) (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hjK : ∀ i, jf i + 1 ≤ K) (Xw : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (_ : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (decomp : ∀ i, StepDecomp (Xc i)) (_ : ∀ i c, (decomp i).wt c = 1) (_ : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).blk (((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x) x ∧
        ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x ≤ jf i + 1) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (_ : HEq (ou none) o) (_ : HEq (xu none) (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A g cs SD KD hmK (hq (m' + 1) (Nat.lt_succ_of_le hW.k1_le_sub_one) Z (Desc.refl Z))) x)) (_ : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (ou (some ⟨j, P, c⟩)) (ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))) (_ : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A g cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hmK)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) (hv : EuclideanSpace ℝ (Fin N)) (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0) (hμ : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0) (hB0 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muBg (jf i + 1))) (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (cs.muAct m)) (hS : ∀ i, InUnionDomainR ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (bgC1 S.d S.L N) (cs.muBg (jf i + 1))
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv) ∧
      ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 →
        InUnionDomainR ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (bgC1 S.d S.L N) (cs.muAct m)
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)) (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1) ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N) (_ : ∀ i, chain i = pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) MassBranch.complete (Xc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)) {k0' k' m₁ N' : ℕ} {ϱ' : ℝ} {sf : Def7.SFData S.d S.L m₁ k' N' ϱ'} {hv' : EuclideanSpace ℝ (Fin N')} (_ : Def7.FieldClauses S k0' k' cs sf hv') (_ : m' + 1 ≤ k') (_ : ‖hv‖ = 1) (t : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → ℕ) (_ : ∀ i, BallRadiusOK R m' (jf i) (t i)) (_ : ∀ i, 2 ≤ t i) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N) (_ : ∀ x i, Du.h x i = 0) (Fs : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N)) (Ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ∀ s y, Fs s y = subVarField N x s y) (_ : ∀ y, Ft y = outField N o y) (_ : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y ≠ m' + 1 →
        ∀ i, Du.Ψ y i = ((Fs (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
          (jBlock S.d S.L (M * n K) K (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
            (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ)) (_ : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y = m' + 1 →
        ∀ i, Du.Ψ y i = ((Ft (jBlock S.d S.L (M * n K) K (m' + 1)
          (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ)),
    WindowDuClaimP g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du t Kw δw Ks δs Kw' δm := by
  classical
  obtain ⟨Kw, δw, Ks, δs, Kw', δm, h0, h1, h2, h3, h4, h5, Hc⟩ := sum_mainActionLoc_eq_gen_of_flow_window_Du_constsP S N hd3 hL3
  refine ⟨Kw, δw, Ks, δs, Kw', δm, h0, h1, h2, h3, h4, h5, ?_⟩
  intro n _ R k0 K M _ H g cs m' Z hmK hW κs κ' lamHat SD KD hH lab hq ρ hρ o x jf cf hfam hjf hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hou0 hxu0 hou1 hxu1 hv hβ hμ hB0 hBn hS chain hchain k0' k' m₁ N' ϱ' sf hv' hF hk' hunit t hR ht2 Du hDuh Fs Ft hFs hFt hDu1 hDu2
  have hk1 := hW.k1_le_sub_one
  have hspec := windowField_pt_spec hmK o x
  obtain ⟨hcf, hinj, hcov⟩ := window_family_facts hk1 jf cf hfam
  have hdb := du_ball_eqT (hR := hR) hmK hW jf cf hjf hcf hjK Xc hXc o x hv (fun b : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) => if h : b.1 ≤ m' + 1 then (if hb : b.1 = m' + 1 then outField N o (torusCast (by rw [hb]; exact blk_eq_top H.F.hnn hmK le_rfl) b.2) else subVarField N x b.1 (torusCast (blk_eq_top H.F.hnn hmK h) b.2)) else 0) hspec.1 hspec.2 Du Fs Ft hFs hFt hDu1 hDu2
  exact Hc g cs hmK hW jf cf hjf hcf hinj hcov hjK
    Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hF hk'
    (fun b : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) => if h : b.1 ≤ m' + 1 then (if hb : b.1 = m' + 1 then outField N o (torusCast (by rw [hb]; exact blk_eq_top H.F.hnn hmK le_rfl) b.2) else subVarField N x b.1 (torusCast (blk_eq_top H.F.hnn hmK h) b.2)) else 0)
    hunit (window_hlift_pt_fam g cs SD KD hk1 hmK hq ρ hρ o x hv jf cf hfam hjf hjK ou xu hou0 hxu0
      hou1 hxu1 (fun b : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) => if h : b.1 ≤ m' + 1 then (if hb : b.1 = m' + 1 then outField N o (torusCast (by rw [hb]; exact blk_eq_top H.F.hnn hmK le_rfl) b.2) else subVarField N x b.1 (torusCast (blk_eq_top H.F.hnn hmK h) b.2)) else 0) hspec.1 hspec.2) t hR ht2 Du hDuh hdb

open Classical in
/-- **sum_mainActionLoc_eq_gen_of_flow_window_pt_Du with the constants first**: the constants `K_w, δ_w, K_s, δ_s, K_w', δ_m` are produced before the window point and all the data, and depend only on `(d, L, N)`.  The landed `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` is this theorem at the data. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_pt_Du_consts (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Kw δw Ks δs Kw' δm : ℝ, 0 < Kw ∧ 0 < δw ∧ 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 g cs N κs) (KD : KeptData k0 g cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5} (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y) (ρ : ∀ (s : ℕ), S.k1 (m' + 1) ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp g cs SD KD hH lab (m' + 1) hmK Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp g cs SD KD hH lab s (hd.le.trans hmK) P).A) (_ : ∀ s (hs : S.k1 (m' + 1) ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl g cs SD KD hmK hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩) (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1)) (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp g cs SD KD hH lab (m' + 1) hmK Z).A) (jf : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (_ : ∀ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩)) (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hjK : ∀ i, jf i + 1 ≤ K) (Xw : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (_ : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (decomp : ∀ i, StepDecomp (Xc i)) (_ : ∀ i c, (decomp i).wt c = 1) (_ : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).blk (((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x) x ∧
        ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x ≤ jf i + 1) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (_ : HEq (ou none) o) (_ : HEq (xu none) (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A g cs SD KD hmK (hq (m' + 1) (Nat.lt_succ_of_le hW.k1_le_sub_one) Z (Desc.refl Z))) x)) (_ : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (ou (some ⟨j, P, c⟩)) (ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))) (_ : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A g cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hmK)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))) (hv : EuclideanSpace ℝ (Fin N)) (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0) (hμ : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0) (hB0 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muBg (jf i + 1))) (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (cs.muAct m)) (hS : ∀ i, InUnionDomainR ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (bgC1 S.d S.L N) (cs.muBg (jf i + 1))
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv) ∧
      ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 →
        InUnionDomainR ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (bgC1 S.d S.L N) (cs.muAct m)
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)) (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1) ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N) (_ : ∀ i, chain i = pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) MassBranch.complete (Xc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)) {k0' k' m₁ N' : ℕ} {ϱ' : ℝ} {sf : Def7.SFData S.d S.L m₁ k' N' ϱ'} {hv' : EuclideanSpace ℝ (Fin N')} (_ : Def7.FieldClauses S k0' k' cs sf hv') (_ : m' + 1 ≤ k') (_ : ‖hv‖ = 1) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N) (_ : ∀ x i, Du.h x i = 0) (Fs : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N)) (Ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ∀ s y, Fs s y = subVarField N x s y) (_ : ∀ y, Ft y = outField N o y) (_ : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y ≠ m' + 1 →
        ∀ i, Du.Ψ y i = ((Fs (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
          (jBlock S.d S.L (M * n K) K (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
            (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ)) (_ : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y = m' + 1 →
        ∀ i, Du.Ψ y i = ((Ft (jBlock S.d S.L (M * n K) K (m' + 1)
          (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ)),
    WindowDuClaim g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du Kw δw Ks δs Kw' δm := by
  classical
  obtain ⟨Kw, δw, Ks, δs, Kw', δm, hKw, hδw, hKs, hδs, hKw', hδm, Hc⟩ :=
    sum_mainActionLoc_eq_gen_of_flow_window_pt_Du_constsP S N hd3 hL3
  refine ⟨Kw, δw, Ks, δs, Kw', δm, hKw, hδw, hKs, hδs, hKw', hδm, ?_⟩
  intro n _ R k0 K M _ H g cs m' Z hmK hW κs κ' lamHat SD KD hH lab hq ρ hρ o x jf cf hfam hjf hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hou0 hxu0 hou1 hxu1 hv hβ hμ hB0 hBn hS chain hchain k0' k' m₁ N' ϱ' sf hv' hF hk' hunit Du hDuh Fs Ft hFs hFt hDu1 hDu2
  exact WindowDuClaim.of_P g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du Kw δw Ks δs Kw' δm
    (fun i => (hjf i).2)
    (Hc g cs hmK hW SD KD hq ρ hρ o x jf cf hfam hjf hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hou0 hxu0 hou1 hxu1 hv hβ hμ hB0 hBn hS chain hchain hF hk' hunit
      (fun _ => 2) (fun i => ballRadiusOK_two H g m' (jf i)) (fun _ => le_rfl) Du hDuh Fs Ft hFs hFt hDu1 hDu2)

open Classical in
/-- **The window conversion at the window point and the reference datum `Du`**. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_pt_Du (g : Geo S n R M) (cs : OpConsts) {m' : ℕ}
    {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L)
    (hW : H.RipeWindow (m' + 1) Z)
    {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 g cs N κs)
    (KD : KeptData k0 g cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
    (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), S.k1 (m' + 1) ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp g cs SD KD hH lab (m' + 1) hmK Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp g cs SD KD hH lab s (hd.le.trans hmK) P).A)
    (hρ : ∀ s (hs : S.k1 (m' + 1) ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl g cs SD KD hmK hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp g cs SD KD hH lab (m' + 1) hmK Z).A)
    (jf : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hfam : ∀ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xw : (Option (Σ j : ↥(Finset.Ico (S.k1 (m' + 1)) m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXwin : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (decomp : ∀ i, StepDecomp (Xc i))
    (hwt1 : ∀ i c, (decomp i).wt c = 1)
    (hcells : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).blk (((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x) x ∧
        ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x ≤ jf i + 1)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hou0 : HEq (ou none) o)
    (hxu0 : HEq (xu none) (newRestrict (H.localHistory M K (m' + 1) Z)
      (newVars_sub_locOp_A g cs SD KD hmK (hq (m' + 1) (Nat.lt_succ_of_le hW.k1_le_sub_one) Z (Desc.refl Z))) x))
    (hou1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (ou (some ⟨j, P, c⟩)) (ancOut (N := N) (R := R) c.1 P.1
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x)))
    (hxu1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A g cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hmK)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)))
    (hv : EuclideanSpace ℝ (Fin N))
    (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0)
    (hμ : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0)
    (hB0 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muBg (jf i + 1)))
    (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (cs.muAct m))
    (hS : ∀ i, InUnionDomainR ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (bgC1 S.d S.L N) (cs.muBg (jf i + 1))
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv) ∧
      ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 →
        InUnionDomainR ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (bgC1 S.d S.L N) (cs.muAct m)
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv))
    (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1) ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N)
    (hchain : ∀ i, chain i = pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) MassBranch.complete (Xc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i))
    {k0' k' m₁ N' : ℕ} {ϱ' : ℝ} {sf : Def7.SFData S.d S.L m₁ k' N' ϱ'}
    {hv' : EuclideanSpace ℝ (Fin N')} (hF : Def7.FieldClauses S k0' k' cs sf hv')
    (hk' : m' + 1 ≤ k')
    (hunit : ‖hv‖ = 1)
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (hDuh : ∀ x i, Du.h x i = 0)
    (Fs : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (Ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hFs : ∀ s y, Fs s y = subVarField N x s y) (hFt : ∀ y, Ft y = outField N o y)
    (hDu1 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y ≠ m' + 1 →
        ∀ i, Du.Ψ y i = ((Fs (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
          (jBlock S.d S.L (M * n K) K (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
            (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    (hDu2 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y = m' + 1 →
        ∀ i, Du.Ψ y i = ((Ft (jBlock S.d S.L (M * n K) K (m' + 1)
          (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    :
      ∃ Kw δw Ks δs Kw' δm : ℝ, 0 < Kw ∧ 0 < δw ∧ 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀
      (ak : ℕ → ℝ)
      (β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch : ℝ)
      (gf δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
      (_ : 0 < β) (_ : 0 < ν) (_ : 0 < α₀) (_ : 0 ≤ Cξ) (_ : 0 ≤ α) (_ : 0 < γ)
      (_ : (S.d : ℝ) - 2 - 2 * α = 2 * γ)
      (_ : ∀ m, cs.beta m = β * (S.L : ℝ) ^ ((S.d - 2) * m) * gf m)
      (_ : ∀ m, cs.muAct m = ν * δ m)
      (_ : ∀ m, gf m = gf (m + 1) * (1 + ξ m 2))
      (_ : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
      (_ : ∀ m, Real.exp (-η) ≤ gf m ∧ gf m ≤ Real.exp η)
      (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ)
      (_ : ∀ m c, |ξ m c| ≤ Cξ * β⁻¹ * ((S.L : ℝ) ^ (-(2 * γ))) ^ (m + 1))
      (_ : Cξ * Real.exp (2 * η) * (S.L : ℝ) ^ (-(2 * γ)) /
        (β * (1 - (S.L : ℝ) ^ (-(2 * γ)))) ≤ 1 / 2)
      (_ : ∀ i, cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 *
        ((S.L : ℝ) ^ (-(2 * γ))) ^ (jf i + 1) ≤ A₀)
      (_ : ∀ i, cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax)
      (_ : ∀ ℓ, |ak ℓ| ≤ Ka) (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : ∀ ℓ, |cs.aw ℓ - ak ℓ| ≤ Δ)
      (_ : 0 ≤ cν) (_ : ν * (S.L : ℝ) ^ (2 * (m' + 1)) * Dδ ≤ cν ^ 2)
      (_ : β * |ν| * (S.L : ℝ) ^ ((m' + 1) * S.d) ≤ 1)
      (_ : 0 < ε₀) (_ : ε₀ ≤ α₀ * ((S.L : ℝ) ^ (-α)) ^ (m' + 1))
      (_ : ∀ i, ∃ N₁ m₁ : ℕ, g.M1 * (g.c * n (jf i + 1)) = N₁ * S.L ^ m₁)
      (_ : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muAct (m' + 1)))
      (_ : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) ak (cs.muAct (m' + 1)))
      (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
      (_ : ∀ i, (4 * S.d + 6) * ((2 * S.d + 1) * epsSeq S.L α α₀ (jf i + 1)) ≤ 1)
      (_ : ∀ i, xiC1 S.d * epsSeq S.L α α₀ (jf i + 1) ≤ bgC1 S.d S.L N)
      (_ : ∀ i, ∀ m, jf i + 1 ≤ m → m ≤ m' + 1 →
        XiCOneReal ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ((chain i).a m) ((chain i).ν m) (epsSeq S.L α α₀ (jf i + 1))
          ((chain i).Dat () m))
      (_ : ∀ i, XiCOneReal ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) cs.aw (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1))
        ((chain i).Dat () (m' + 1)))
      (_ : ∀ i, XiCOneReal ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ak (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1))
        ((chain i).Dat () (m' + 1)))
      (_ : ∀ i, bgK1 S.d S.L N * (xiC1 S.d * epsSeq S.L α α₀ (jf i + 1)) ≤
        min (deltaStar S.d S.L N) δw)
      (_ : ∀ i, epsSeq S.L α α₀ (jf i + 1) * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤
        min (deltaStar S.d S.L N) δw)
      (_ : ∀ i, Δ * (2 * epsSeq S.L α α₀ (jf i + 1)) ≤ min (deltaStar S.d S.L N) δw)
      (_ : ∀ i, epsSeq S.L α α₀ (jf i + 1) ≤ Emax)
      (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
      (_ : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
      (_ : (4 * Emax ^ 2) * (β * Real.exp η * (S.L : ℝ) ^ ((S.d - 2) * (m' + 1)) * Δ) / 2 ≤ Kwt)
      (_ : Kw * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ V1)
      (_ : Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
        Real.sqrt ((4 * S.d * Real.exp (2 * η)) * (S.d * (N * Real.exp (2 * η)) * V1 ^ 2)) +
        Real.sqrt ((12 * Real.exp (2 * η)) * (N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2)) +
        (N * Ka * V1 ^ 2 + S.d * (N * Real.exp (2 * η)) * V1 ^ 2 +
          N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2) / 2 +
        4 * S.d * Real.exp (2 * η) + 12 * Real.exp (2 * η) ≤ Ksrc)
      (_ : Ksrc * (Cξ * Real.exp (2 * η) * (S.L : ℝ) ^ (-(2 * γ)) * A₀ /
        (2 * β * (1 - (S.L : ℝ) ^ (-(2 * γ))))) ≤ Kpair)
      (_ : 2 * (Ka + Δ) * A₀ * Cξ * Real.exp (2 * η) * (S.L : ℝ) ^ (-(2 * γ)) /
            (β * (1 - (S.L : ℝ) ^ (-(2 * γ)))) + Kwt +
          Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
            Real.sqrt ((S.d * ((4 * Emax ^ 2) * Cg)) * (S.d * (N * Cg))) +
            Real.sqrt (((4 * Emax ^ 2 / |cs.muAct (m' + 1)|) * Cm) * (N * Cm))) +
            (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + S.d * (N * Cg) + N * Cm)) ≤ Kcoef)
      (_ : 0 ≤ Kpair) (_ : 0 ≤ Kcoef) (_ : 0 ≤ Kswitch)
      -- the switch (P7 (2.14)) to the window background at mass `0` of the datum `Du`
      (ϱB δl δu V Kmass m : ℝ)
      (_ : IsAdmissibleWeights (m' + 1) ak) (_ : cν ≤ 1)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : 0 < δl) (_ : δl ≤ bgC1 S.d S.L N)
      (_ : ∀ i, InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv))
      (_ : 0 < δu) (_ : δu ≤ bgC1 S.d S.L N) (_ : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
      (_ : bgK1 S.d S.L N * (δl + δu) ≤ δs)
      (_ : bgK1 S.d S.L N * δl ≤ min (deltaStar S.d S.L N) δm) (_ : 0 ≤ m)
      (_ : m * 2 ≤ min (deltaStar S.d S.L N) δm)
      (_ : ∀ i, cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 ≤ m)
      (_ : ∀ i, Ks * ((δl + δu) * Real.exp (-(gammaW S.d *
        ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
          (S.L : ℝ) ^ (jf i + 1))))) + Kw' * (m * 2) ≤ V)
      (_ : Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((S.d * ((4 * Emax ^ 2) * Cg)) * (S.d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |cs.muAct (m' + 1)|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + S.d * (N * Cg) + N * Cm)) ≤ Kswitch)
      (_ : 2 * (Cm * Amax) ≤ Kmass),
      ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak 0 Du
            (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du)).re - C.re ∧
      ‖C‖ ≤ (9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (S.L : ℝ) ^ (-(2 * γ))) + (Kpair + Kcoef + Kswitch + Kmass)) *
          ∑ i, (decomp i).total := by
  obtain ⟨Kw, δw, Ks, δs, Kw', δm, h0, h1, h2, h3, h4, h5, Hc⟩ := sum_mainActionLoc_eq_gen_of_flow_window_pt_Du_consts S N hd3 hL3
  exact ⟨Kw, δw, Ks, δs, Kw', δm, h0, h1, h2, h3, h4, h5, Hc g cs hmK hW SD KD hq ρ hρ o x jf cf hfam hjf hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hou0 hxu0 hou1 hxu1 hv hβ hμ hB0 hBn hS chain hchain hF hk' hunit Du hDuh Fs Ft hFs hFt hDu1 hDu2⟩

end Pt

end Balaban.LargeField
