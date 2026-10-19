/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomFacts
public import Balaban.LargeField.R.WindowDomHS
public import Balaban.LargeField.R.WindowRadiusRegime
public import Balaban.LargeField.R.ChainSeq

/-!
# The domain clauses of the window conversion in the `δ`-regime (blocker 4)

`window_domain_clauses_of_regime`: at a window point where the kernel of the operator of `Z` is nonzero
and the output is in the support of the post weight (`WindowPostSupport` at some direction), with the
running constants in the regime `λ̂_0` large (`pieceRadiusWin_regime`, `cs.delta = deltaRun …`,
positivity by `deltaRun_pos`), the radii `δ_x(j_i) = pieceRadiusWin S cs j_i` and `δ_l = c₁`:

* both clauses of `hS` of `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` (`window_pieces_hS`);
* the three families of `XiCOneReal` and `InDomainR … c₁` of `window_domain_facts`.

The conditions on the masses, `2 μ_act(m) L^{2(j_i+1)} < pieceRadiusWin(j_i)²`, are the choice of `ν`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.SmallField Balaban.Fluctuation
  Balaban.LargeField.Def7 RegionHistory

section Regime

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ}
  {lamK : ℕ → ℝ} (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamK)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The domain clauses of the window conversion in the `δ`-regime** (see the module docstring). -/
theorem window_domain_clauses_of_regime {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
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
    (Z0 : Set (BlockAt S n M K (m' + 1))) (hvp : EuclideanSpace ℝ (Fin N)) (hpost : WindowPostSupport H Cx hvp Z0 o)
    (hZ0 : ∀ y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1), y ∈ Z0 →
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y)
    (HB : BgHyp S.d S.L (m' + 1) (minSep S.L Cx.geo.M1) Cx.weights (Cx.cs.mu (m' + 1)))
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
    (α α₀ : ℝ) (ak : ℕ → ℝ) {β ν a ε : ℝ} {b nu : ℕ → ℝ} (hrun : RunningHyp S.d S.L β ν a ε b nu)
    (hd3 : 3 ≤ S.d) (hα : 0 ≤ α) (hα₀ : 0 < α₀) (hα₀2 : α₀ ≤ 2) {γ : ℝ} (hγ : 0 < γ)
    (hrel : (S.d : ℝ) - 2 - 2 * α = 2 * γ) {A0 : ℝ} (hA0 : 0 < A0) (p0 : ℕ) (hp0 : 1 ≤ p0)
    (hlam : ∀ i, 12 * (p0 : ℝ) ≤ runLam a b i) (h3 : 3 ≤ lamHat S.d S.L β a 0)
    (hcond : ((2 * bgK1 S.d S.L N + 2) * (3 * (S.d : ℝ) * S.L) * (2 * (S.L : ℝ) ^ α)) *
        (Real.exp 1 * A0 * (p0.factorial : ℝ) / (γ / (2 * ((S.d : ℝ) - 2))) ^ p0) *
        (S.L : ℝ) ^ α ≤ α₀ * Real.exp (lamHat S.d S.L β a 0 / 4))
    (hcsd : ∀ j, cs.delta j = deltaRun A0 p0 a b j)
    (hε1 : ∀ j, epsSeq S.L α α₀ (j + 1) ≤ bgC1 S.d S.L N)
    (hμ0 : ∀ m, 0 ≤ cs.muAct m)
    (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0)
    (hBj : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1) cs.aw (cs.muAct (jf i + 1)))
    (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta (jf i + 1)) (jf i + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (cs.muAct m))
    (hBaw : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1) cs.aw (cs.muAct (m' + 1)))
    (hBak : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L geo.M1) ak (cs.muAct (m' + 1)))
    (hmassRad : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 →
      2 * cs.muAct m * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 < pieceRadiusWin S cs (jf i) ^ 2) :
    (∀ i, InUnionDomainR
      (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))
      (bgC1 S.d S.L N) (cs.muBg (jf i + 1))
      (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv) ∧
    ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 →
      InUnionDomainR
        (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i)) (bgC1 S.d S.L N) (cs.muAct m)
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)) ∧
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
          (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) (bgC1 S.d S.L N)
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv)) := by
  have hδpos : ∀ j, 0 < cs.delta j := fun j => by
    rw [hcsd j]; exact deltaRun_pos hrun hA0 hp0 hlam j
  have hK1 := bgK1_pos S.d S.L N
  have hreg := fun j => pieceRadiusWin_regime S cs hrun hd3 hα hα₀ hα₀2 hγ hrel hA0.le
    hK1.le p0 h3 hcond hcsd (fun j => (hδpos j).le) j
  have hc1 : ∀ j, pieceRadiusWin S cs j ≤ bgC1 S.d S.L N := fun j => by
    have h1 := hreg j
    have h2 := hε1 j
    nlinarith [pieceRadiusWin_pos S cs hδpos j]
  have hmassC : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 →
      2 * cs.muAct m * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 < (bgC1 S.d S.L N) ^ 2 := fun i m h1 h2 =>
    (hmassRad i m h1 h2).trans_le (pow_le_pow_left₀ (pieceRadiusWin_pos S cs hδpos _).le (hc1 _) 2)
  refine ⟨window_pieces_hS geo cs SD KD hm hW hq ρ hρ o x hv hK jf cf hfam hjf hjK ou xu hou0 hxu0
    hou1 hxu1 (by omega) hunit hμ0 (fun i m h1 h2 => hmassC i m (by omega) h2), ?_⟩
  exact window_domain_facts geo cs SD KD hm hW hq hk1p ρ hρ o x hv hunit hK Cx hgeo hcs Z0 hvp hpost
    hZ0 HB hδpos jf cf hfam hjf hjK ou xu hou0 hxu0 hou1 hxu1 α α₀ (bgC1 S.d S.L N)
    (fun j => pieceRadiusWin S cs j) ak hμ0 hβ hBj hBn hBaw hBak (fun i => le_rfl)
    (fun i => hc1 _)
    (fun i => by have := hreg (jf i); nlinarith [pieceRadiusWin_pos S cs hδpos (jf i)])
    hmassRad (fun i => hc1 _) (fun i => hmassC i (m' + 1) (by have := (hjf i).2; omega) le_rfl)

end Regime

end Balaban.LargeField
