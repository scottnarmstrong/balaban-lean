/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowCompose
public import Balaban.LargeField.R.WindowComposeCongr

/-!
# The sum identity of the main actions of the pieces at a configuration of the window (blocker 4, W964)

`notes/phase1/LF4R-PLAN.md` §9.  `window_sum_pt`: `sum_mainActionLoc_eq_gen` for the family `(j, P, c)` of the pieces of
`locOp_absW_le_chain` plus the top piece (`chain_piece_*`), at the configuration `(o, x, hv)` of the window: the sum
`𝒜_(m'+1)(Z) + ∑_(j,P,c) 𝒜_(j+1)(c)` of the exponent of `window_chain_le_action` is `Re(β_k A_(X_win)) - Re C`,
`‖C‖ ≤ C₁₅ ∑ mcount`.  The restrictions `ρ` and the data of the pieces `(ou, xu)` are tied by their defining equations
(`hou0`, `hxu0`, `hou1`, `hxu1`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField

section Sum

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}

open Classical in
/-- **The sum of the main actions of the pieces at a configuration of the window** (LFR (2.15′), P7 (2.12)-(2.16)). -/
theorem window_sum_pt {k1 m' : ℕ} (hk1p : 1 ≤ k1) (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) {Z : H.Comp (m' + 1)}
    (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
    {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : Wp.Hyp)
    (Xw : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))) → Region (Wp.windowGenSet hWh))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔
      torusCast (piece_torus_eq geo H.F.hnn hm (chain_piece_spec (Z := Z) hk1 i).2.1) x ∈
        Xfine geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1)
    (Xwin : Region (Wp.windowGenSet hWh))
    (hXwin : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq geo H.F.hnn hm hj.2) x ∈ Xfine geo (H.locRH (j + 1) c) j c.1)
    (Xc : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), Region (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
      (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)))
    (hXc : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (Xc i).sites = Xfine geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1)
    (decomp : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), StepDecomp (Xc i))
    (ak : ℕ → ℝ) (νk βk : ℝ) (Datw : BgData (Wp.windowGenSet hWh) N)
    (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (br : MassBranch)
    (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ou : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), OutT N R (H.localHistory M K ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1))
    (xu : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), NewCfg N (H.localHistory M K ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1))
    (hou0 : ou none = o) (hxu0 : xu none = newRestrict (H.localHistory M K (m' + 1) Z) (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x)
    (hou1 : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), ou (some ⟨j, P, c⟩) = ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x))
    (hxu1 : ∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
      (c : ↥(H.parts (j.1 + 1) P.1)), xu (some ⟨j, P, c⟩) = newRestrict (H.localHistory M K (j.1 + 1) c.1) (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm) (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)))) (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) x))
    (hβ : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0)
    (hμ : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0)
    (hB0 : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), BgHyp S.d S.L ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (minSep S.L geo.M1) cs.aw (cs.muBg ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)))
    (hBn : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) (minSep S.L geo.M1)
      (fun l => cs.aw l * (betaCanon S.d S.L (cs.beta ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) 0 /
        betaCanon S.d S.L (cs.beta m) m 0)) (br.elMass (cs.muAct m)))
    (hS : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), InUnionDomainR (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
        (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)) (bgC1 S.d S.L N) (cs.muBg ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1))
        (locData geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1 (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2))
          (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) (ou i) (xu i) hv) ∧
      ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 →
        InUnionDomainR (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
          (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)) (bgC1 S.d S.L N) (br.elMass (cs.muAct m))
          (locData geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1 (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2))
            (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) (ou i) (xu i) hv))
    {Kconv Kbg γw M₀ M₁ : ℝ} {ε Rhat : ℕ → ℝ}
    (p7_first : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 →
      ‖(pieceChain geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
        (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) cs Set.univ (m' + 1) br (Xc i) (fun _ => ou i)
        (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)).cost () m‖ ≤ Kconv *
      ((cs.beta ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) * ε ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ^ 2) / (cs.beta m * ε m ^ 2)) * (decomp i).total)
    (window_decay : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))),
      ‖(pieceChain geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
        (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) cs Set.univ (m' + 1) br (Xc i) (fun _ => ou i)
        (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)).T () (m' + 1) -
        (βk : ℂ) * actionRegionC (Xw i) ak νk Datw φw‖ ≤
      Kbg * Real.exp (-γw * (M₀ * (Rhat ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 - 1) - 1) - 2 * M₁)) * (decomp i).total)
    {γ η α α₀ : ℝ} (hd : 2 ≤ S.d) (hL : 1 < S.L) (hγ : 0 < γ) (hα₀ : 0 < α₀)
    (hε : ε = epsSeq S.L α α₀) (hγα : (S.d : ℝ) - 2 - 2 * α = 2 * γ)
    (hflow : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), ∃ B : ℝ, 0 < B ∧ ∃ gg : ℕ → ℝ,
      (∀ m, Real.exp (-η) ≤ gg m ∧ gg m ≤ Real.exp η) ∧
      ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1 ≤ m → m ≤ m' + 1 →
        cs.beta m = B * (S.L : ℝ) ^ ((S.d - 2) * m) * gg m)
    (hKc : 0 ≤ Kconv) (hKb : 0 ≤ Kbg) (hγw : 0 ≤ γw)
    (hsep : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), 0 ≤ M₀ * (Rhat ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 - 1) - 1) - 2 * M₁) :
    ∃ C : ℂ, (mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs
        (locRH_rem (m' + 1) Z) o (newRestrict (H.localHistory M K (m' + 1) Z) (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) (by omega) Z (Desc.refl Z))) x) hv +
      ∑ j : ↥(Finset.Ico k1 m'), ∑ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ∑ c : ↥(H.parts (j.1 + 1) P.1),
          mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
            (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
            (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
            (ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) P.1 (mem_ancFin.mp P.2) x)) (newRestrict (H.localHistory M K (j.1 + 1) c.1) (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm) (hq (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)))) (ρ (j.1 + 1) (by have := (Finset.mem_Ico.mp j.2).1; omega) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) hv) =
      ((βk : ℂ) * actionRegionC Xwin ak νk Datw φw).re - C.re ∧
    ‖C‖ ≤ (9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) *
      ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (decomp i).total := by
  classical
  obtain ⟨C, hC, hCb⟩ := sum_mainActionLoc_eq_gen geo cs (Z := Z) (k1 := k1) hm Wp hWh (ι := (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))))
    (fun i => (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) (fun i => (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)
    (fun i => ⟨(chain_piece_spec (Z := Z) hk1 i).1, (chain_piece_spec (Z := Z) hk1 i).2.1⟩)
    (fun i => (chain_piece_spec (Z := Z) hk1 i).2.2) chain_piece_inj
    (fun j c h1 h2 hc => chain_piece_cover j c h1 h2 hc) (fun i => (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)) hk1p Xw hXw Xwin hXwin Xc hXc
    decomp ak νk βk Datw φw br ou xu hv hβ hμ hB0 hBn hS
    (fun i => pieceChain geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
      (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) cs Set.univ (m' + 1) br (Xc i) (fun _ => ou i)
      (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i))
    (fun i => rfl) p7_first window_decay hd hL hγ hα₀ hε hγα hflow hKc hKb hγw hsep
  refine ⟨C, ?_, hCb⟩
  rw [← hC]
  rw [Fintype.sum_option]
  rw [Fintype.sum_sigma]
  refine congrArg₂ (· + ·) ?_ ?_
  · show _ = mainActionLoc geo (H.locRH (m' + 1) Z) m' Z.1 (locComp_mem H hm Z) hm cs (locRH_rem (m' + 1) Z)
      (ou none) (xu none) hv
    rw [hou0, hxu0]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun P _ => Finset.sum_congr rfl fun c _ => ?_
    show _ = mainActionLoc geo (H.locRH (j.1 + 1) c.1) j.1 c.1.1
      (locComp_mem H (by have := (Finset.mem_Ico.mp j.2).2; omega) c.1)
      (by have := (Finset.mem_Ico.mp j.2).2; omega) cs (locRH_rem (j.1 + 1) c.1)
      (ou (some ⟨j, P, c⟩)) (xu (some ⟨j, P, c⟩)) hv
    rw [hou1 j P c, hxu1 j P c]

end Sum

end Balaban.LargeField
