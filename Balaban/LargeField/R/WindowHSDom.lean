/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDomHS
public import Balaban.LargeField.R.WindowCompose

/-!
# The domain clauses `hS` at a window point as a proposition (blocker 4)

`WindowHS`: both clauses of `hS` of `sum_mainActionLoc_eq_gen_of_flow_window_pt_Du` for the pieces of the
window family, for every choice of the piece outputs and new variables read from the window point
`(o, x)` (the form in which the named inputs of the Close chain state them).

`windowHS_of_kernel`: `WindowHS` holds at every window point with `K ≠ 0`, once the masses
`br.elMass (μ_act(m))` do not exceed `μ_Bg(j_i + 1)` (`window_pieces_inUnionDomainR`, monotonicity of
the real domain in the mass); no unit direction is needed.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  ActionConv RegionHistory Balaban.SmallField

section HS

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}
  (geo : Geo S n R M) (cs : OpConsts) {κs κ' : ℕ → LocalHistory S n M K → ℝ} {lamHat : ℕ → ℝ}
  (SD : StepData k0 geo cs N κs) (KD : KeptData k0 geo cs N κ' lamHat)
  {hH : H.Admissible} {lab : ∀ k, H.Comp k → Fin 5}
  {k1 m' : ℕ} (hk1 : k1 ≤ m') (hm : m' + 1 ≤ K) (hmk : k1 < m' + 1) {Z : H.Comp (m' + 1)}
  (hq : ∀ s, k1 < s → ∀ Y : H.Comp s, H.Desc s (m' + 1) Y Z → ¬ IsKept H s Y)
  (ρ : ∀ (s : ℕ), k1 ≤ s → ∀ (P : H.Comp s) (hd : H.Desc s (m' + 1) P Z),
      SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
        (locOp geo cs SD KD hH lab (m' + 1) hm Z).A →
      SubCfg N (H.localHistory M K s P) s (locOp geo cs SD KD hH lab s (hd.le.trans hm) P).A)
  (br : MassBranch)

open Classical in
/-- **Both clauses of `hS` at the window point `(o, x)`, direction `hv`.** -/
def WindowHS (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A) (hv : EuclideanSpace ℝ (Fin N)) : Prop :=
  ∀ (ou : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), OutT N R (H.localHistory M K ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1))
            (xu : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), NewCfg N (H.localHistory M K ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1)),
          ou none = o → xu none = newRestrict (H.localHistory M K (m' + 1) Z) (newVars_sub_locOp_A geo cs SD KD hm (hq (m' + 1) hmk Z (Desc.refl Z))) x →
          (∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)), ou (some ⟨j, P, c⟩) = ancOut (N := N) (R := R) c.1 P.1 (ρ (j.1 + 1 + 1) (Nat.le_succ_of_le (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1)) P.1 (mem_ancFin.mp P.2) x)) →
          (∀ (j : ↥(Finset.Ico k1 m')) (P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z))
            (c : ↥(H.parts (j.1 + 1) P.1)), xu (some ⟨j, P, c⟩) = newRestrict (H.localHistory M K (j.1 + 1) c.1) (newVars_sub_locOp_A geo cs SD KD ((desc_of_parts c.2 (mem_ancFin.mp P.2)).le.trans hm) (hq (j.1 + 1) (Nat.lt_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)))) (ρ (j.1 + 1) (Nat.le_succ_of_le (Finset.mem_Ico.mp j.2).1) c.1 (desc_of_parts c.2 (mem_ancFin.mp P.2)) x)) →
          (∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), InUnionDomainR (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
              (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)) (bgC1 S.d S.L N) (cs.muBg ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1))
              (locData geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1 (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2))
                (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) (ou i) (xu i) hv) ∧
            ∀ m, (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m → m ≤ m' + 1 →
              InUnionDomainR (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
                (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)) (bgC1 S.d S.L N) (br.elMass (cs.muAct m))
                (locData geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1 (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2))
                  (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) (ou i) (xu i) hv))

open Classical in
/-- **`WindowHS` on the support of the kernel**, under `μ^{br}_act(m) ≤ μ_Bg(j_i + 1)`. -/
theorem windowHS_of_kernel (hW : H.RipeWindow (m' + 1) Z) (hk1def : S.k1 (m' + 1) = k1)
    (hρ : ∀ s (hs : k1 ≤ s) P (hd : H.Desc s (m' + 1) P Z) x p, ρ s hs P hd x p =
      x ⟨_, locOp_A_incl geo cs SD KD hm hd
        (fun t ht Y' h' => hq t (lt_of_le_of_lt hs ht) Y' h') p.1 p.2⟩)
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1)
      (locOp geo cs SD KD hH lab (m' + 1) hm Z).A) (hv : EuclideanSpace ℝ (Fin N))
    (hK : (locOp geo cs SD KD hH lab (m' + 1) hm Z).T.K o x hv ≠ 0)
    (hle : ∀ (i : Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z),
        ↥(H.parts (j.1 + 1) P.1))) m,
      (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 2 ≤ m →
      m ≤ m' + 1 → br.elMass (cs.muAct m) ≤
        cs.muBg ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1)) :
    WindowHS geo cs SD KD hk1 hm hmk hq ρ br o x hv := by
  subst hk1def
  unfold WindowHS
  intro ou xu hou0 hxu0 hou1 hxu1 i
  have h1 := window_pieces_inUnionDomainR geo cs SD KD hm hW hq ρ hρ o x hv hK
    (fun i => (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1)
    (fun i => (Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)
    (fun _ => rfl) (fun i => ⟨(chain_piece_spec hk1 i).1, (chain_piece_spec hk1 i).2.1⟩)
    (fun i => le_trans (Nat.succ_le_succ (chain_piece_spec hk1 i).2.1) hm) ou xu
    (heq_of_eq hou0) (heq_of_eq hxu0) (fun j P c => heq_of_eq (hou1 j P c))
    (fun j P c => heq_of_eq (hxu1 j P c)) i
  exact ⟨h1, fun m hm1 hm2 => inUnionDomainR_mass_le h1 (hle i m hm1 hm2)⟩

end HS

end Balaban.LargeField
