/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomKernel
public import Balaban.LargeField.R.WindowDomMass

/-!
# The first clause of `hS` at the masses `μ_act(m)` (blocker 4)

On the support of the window integrand every piece datum lies in the real domain of the background
mass (`window_pieces_inUnionDomainR`).  The second clause of `hS` of
`sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` asks the same at the masses `μ_act(m)`,
`j_i + 2 ≤ m ≤ m' + 1`.  The radius `c₁` is attained (`inDomainR_mass_change`), so the passage to
another mass is the single condition `2 μ_act(m) L^{2(j_i+1)} < c₁²` on the masses (clause R3 of the
real domain; P5 (1.4): the fine-unit mass `ν_m L^{-2m}` is small against `c₁²`); R4 holds at every
mass for the unit direction `h = hv`.
-/

@[expose] public section

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background RegionHistory

section Window

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **The two clauses of `hS` on the support of the window integrand**: if the kernel of the operator
of `Z` is nonzero at the window point `(o, x)`, every piece datum is in `𝒟_ℝ(G_i; c₁, μ_Bg(j_i+1))`
and, for `j_i + 2 ≤ m ≤ m' + 1`, in `𝒟_ℝ(G_i; c₁, μ_act(m))`, provided the masses satisfy
`2 μ_act(m) L^{2(j_i+1)} < c₁²`. -/
theorem window_pieces_hS (geo : Geo S n R M) (cs : OpConsts)
    {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ} (SD : StepData k0 geo cs N κs)
    (KD : KeptData k0 geo cs N κ' lamHat) {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
    {m' : ℕ} (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)} (hW : H.RipeWindow (m' + 1) Z)
    (hq : ∀ s, S.k1 (m' + 1) < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    (ρ : ∀ (s : ℕ), S.k1 (m' + 1) ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (hρ : ∀ s (hs : S.k1 (m' + 1) ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h')
        p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
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
        (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x)))
    (hxu1 : ∀ (j : ↥(Finset.Ico (S.k1 (m' + 1)) m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), HEq (xu (some ⟨j, P, c⟩))
        (newRestrict (H.localHistory M K (j.1 + 1) c.1)
          (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm)
            (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
              (desc_of_parts c.2 (mem_ancFin.mp P.2))))
          (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1
            (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)))
    (hd : 0 < S.d) (hunit : ‖hv‖ = 1) (hμ0 : ∀ m, 0 ≤ cs.muAct m)
    (hmass : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 →
      2 * cs.muAct m * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 < (bgC1 S.d S.L N) ^ 2) :
    ∀ i, InUnionDomainR
      (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))
      (bgC1 S.d S.L N) (cs.muBg (jf i + 1))
      (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv) ∧
    ∀ m, jf i + 2 ≤ m → m ≤ m' + 1 →
      InUnionDomainR
        (locGen geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i)) (bgC1 S.d S.L N) (cs.muAct m)
        (locData geo (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv) := by
  intro i
  have h1 := window_pieces_inUnionDomainR geo cs SD KD hm hW hq ρ hρ o x hv hK jf cf hfam hjf hjK
    ou xu hou0 hxu0 hou1 hxu1 i
  have hsum : ∑ q, hv q ^ 2 = 1 := by
    have h := EuclideanSpace.norm_sq_eq hv
    rw [hunit] at h
    simpa [sq_abs] using h.symm
  refine ⟨h1, fun m hm1 hm2 => ?_⟩
  exact inUnionDomainR_mass_change (hv := fun q => hv q) (bgC1_pos_of hd) h1 hsum
    (fun z hz q => congrFun (liftMixed_h _ _ _ _ _ _ hz) q) (hμ0 m) (hmass i m hm1 hm2)

end Window

end Balaban.LargeField
