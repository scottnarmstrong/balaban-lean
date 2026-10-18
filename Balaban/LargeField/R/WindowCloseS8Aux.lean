/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowCloseAZ
public import Balaban.LargeField.R.WindowCloseBridge
public import Balaban.LargeField.R.WindowCloseHbGMain

/-!
# The bridge to the consumer's `e^{L_c}` (blocker 4, W1004)

`window_constNat_le_exp`: `const^♮ ≤ e^{L_c}` from `a_z ≤ a₁` (`window_hbG_aZ_le`), the relation `hβa` and `hwz2`.
`window_Qtot_le_exp`: `e^{B_w} Q_tot ≤ e^{B_w} e^{L_c} Q_b` for `Q_b = exp(F_z + C_Ẽ D^d + C_nat λ^{2d+1} + 4 + C_k)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open MeasureTheory Balaban Balaban.Multiscale Balaban.Background Balaban.Fluctuation Balaban.Localization
  ActionConv RegionHistory ENNReal Balaban.SmallField

section Core

open Classical

variable {S : Setting}
variable {n : ℕ → ℕ}
variable [∀ k, NeZero (n k)]
variable {R : ℕ → ℝ}
variable {k0 : ℕ}
variable {M K : ℕ}
variable [NeZero M]
variable [NeZero S.L]
variable {N : ℕ}
variable {H : RegionHistory S n R k0 K}
variable (geo : Geo S n R M)
variable (cs : OpConsts)
variable {κs κ' : ℕ → LocalHistory S n M K → ℝ}
variable {lamHat : ℕ → ℝ}
variable (SD : StepData k0 geo cs N κs)
variable (KD : KeptData k0 geo cs N κ' lamHat)
variable {hH : H.Admissible}
variable {lab : ∀ k, H.Comp k → Fin 5}
variable {k1 m' : ℕ}
variable (hk1 : k1 ≤ m')
variable (hm : m' + 1 ≤ K)
variable {Z : H.Comp (m' + 1)}
variable (Z0 V2 G3 : Set (BlockAt S n M K (m' + 1)))
variable (P2 : BlockAt S n M K (m' + 1) → Prop)
variable (hV2 : ∀ y, y ∈ V2 → P2 y → y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧
      ZBlk (H.localHistory M K (m' + 1) Z) (m' + 1) y ∧ y ∉ Z0)
variable (T : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
variable [Fintype ↑T]
variable (Nd : Set ↥(locOp geo cs SD KD hH lab (m' + 1) hm Z).A)
variable [Fintype ↑Nd]
variable (nd : (Σ s, BlockAt S n M K s) → Prop)
variable (hN2 : 2 ≤ N)
variable (Qtot : ℝ≥0∞)
variable [NeZero S.M]
variable [NeZero N]
variable (hZ0g : Z0 ⊆ gaussBlocks (H.localHistory M K (m' + 1) Z) m')
variable (hV2full : ∀ y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m', y ∉ Z0 → y ∈ V2 ∧ P2 y)
variable (hMS : M = S.M)
variable (G : S.Good)
variable (h18 : ∀ j, S.Rb * (S.lam j + S.θp + 1) ^ 2 + 1 ≤ 9 / 8 * (S.Rb * S.lam j ^ 2 - 1))
variable (h3 : 8 ≤ S.L * S.lateR (m' + 1))
variable (hW : H.RipeWindow (m' + 1) Z)
variable (hk1def : S.k1 (m' + 1) = k1)
variable [hfin : Fintype {b : Σ s, BlockAt S n M K s // nd b}]
variable [hfinl : Fintype {q : (Σ s, BlockAt S n M K s) × {b : Σ s, BlockAt S n M K s // nd b} //
      (⟨q.1.1 + 1, blockMap S.L (M * n K * S.L ^ (K - (q.1.1 + 1))) q.1.2⟩ :
        Σ s, BlockAt S n M K s) = q.2.1 ∧ ¬ nd q.1}]
variable (Fx : {b : Σ s, BlockAt S n M K s // nd b} → Prop)
variable [DecidablePred Fx]
variable {a₁ β0 : ℝ}
variable (hβ0 : 0 < β0)
variable (ha₁ : 0 < a₁)
variable {D0 : ℕ}
variable (b0 : Torus S.d ((M * n (m' + 1)) * S.L ^ ((m' + 1) - (m' + 1))))
variable (wb : Fin S.d → ℕ)
variable {CEt Cnat : ℝ}
variable (hbx : ∀ x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)),
      jBlock S.d S.L (M * n (m' + 1)) (m' + 1) (m' + 1) x ∈ box b0 wb ↔
        torusCast (congrArg (· * n (m' + 1)) hMS) (blockMap (S.L ^ (m' + 1)) (M * n (m' + 1)) x) ∈
          H.Zzero (m' + 1) Z)
variable (hZ0b : ∀ y : BlockAt S n M K (m' + 1), (y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0) ↔
      torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y ∈ boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb)
variable (Zb : Finset (Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1 - (m' + 1)))))
variable (hZb : ∀ zb, zb ∈ Zb ↔ ∃ y : BlockAt S n M K (m' + 1), y ∈ V2 ∧ P2 y ∧
      y ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' ∧ zb = torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm y)
variable (Xc : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), Region (locGen geo (H.locRH ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1 + 1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).1) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2).1
      (locComp_mem H (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm) ((Option.elim i (⟨m', Z⟩ : Σ j, H.Comp (j + 1)) fun s => ⟨s.1.1, s.2.2.1⟩).2)) (le_trans (Nat.succ_le_succ (chain_piece_spec (Z := Z) hk1 i).2.1) hm)))
variable (decomp : ∀ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), StepDecomp (Xc i))
variable {Kconv Kbg γw M₀ M₁ : ℝ}
variable {γ η α α₀ : ℝ}
variable (hQtotv : Qtot = ENNReal.ofReal (ActionConv.constNat N (betaK S.d S.L (m' + 1) β0)
      (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb * Real.exp ((N : ℝ) / 2 * Real.log (betaK S.d S.L (m' + 1) β0) * ((boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb).card : ℝ) + CEt * (D0 : ℝ) ^ S.d + Cnat * S.lam (m' + 1) ^ (2 * S.d + 1) + 4 + ((9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) * ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (decomp i).total))))
variable (wz : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} → ℝ)
variable {Lc : ℝ}
variable (hLc : Real.exp Lc = ∏ i, (wz i / Real.pi) ^ ((N : ℝ) / 2))
variable (hwz1 : ∀ i, Real.pi ≤ wz i)
variable (hwz2 : ∀ i, cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2) * cs.z (m' + 1) ^ 2 ≤ 2 * wz i)
variable {Fz Ck Qb : ℝ}
variable (hFz : Fz = (N : ℝ) / 2 * Real.log (betaK S.d S.L (m' + 1) β0) *
      Nat.card {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0})
variable (bw0 : ℝ)
variable (hCk : Ck = (9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) * ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))), (decomp i).total)
variable (hβa : betaK S.d S.L (m' + 1) β0 * a₁ ≤ cs.beta m' * cs.aKer * (S.L : ℝ) ^ (S.d - 2) * cs.z (m' + 1) ^ 2)
variable (hQbdef : Qb = Real.exp (Fz + CEt * (D0 : ℝ) ^ S.d + Cnat * S.lam (m' + 1) ^ (2 * S.d + 1) + 4 + Ck))

include S n R k0 M K N H geo cs κs κ' lamHat SD KD hH lab k1 m' hk1 hm Z Z0 V2 G3 P2 hV2 T Nd nd hN2 Qtot hZ0g hV2full hMS G h18 h3 hW hk1def Fx a₁ β0 hβ0 ha₁ D0 b0 wb CEt Cnat hbx hZ0b Zb hZb Xc decomp Kconv Kbg γw M₀ M₁ γ η α α₀ hQtotv wz Lc hLc hwz1 hwz2 Fz Ck Qb hFz bw0 hCk hβa hQbdef

open Classical in
/-- **`const^♮ ≤ e^{L_c}`.** -/
theorem window_constNat_le_exp :
    ActionConv.constNat N (betaK S.d S.L (m' + 1) β0)
      (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb ≤
        Real.exp Lc := by
  classical
  have hβk : 0 < betaK S.d S.L (m' + 1) β0 := by
    unfold betaK
    have : (0 : ℝ) < S.L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne S.L)
    positivity
  have haZ := window_hbG_aZ_le geo hm Z0 V2 P2 hV2 hZ0g hV2full hMS G h18 h3 hW hk1def ha₁ b0 wb hbx hZ0b Zb hZb
  have hmem : ∀ i : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y}, i.1 ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m' →
      torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm i.1 ∈ Zb := fun i hi => by
    rw [hZb]; exact ⟨i.1, i.2.1, i.2.2, hi, rfl⟩
  have hY : Zb = (Finset.univ.filter (fun i : {y : BlockAt S n M K (m' + 1) // y ∈ V2 ∧ P2 y} =>
      i.1 ∈ gaussBlocks (H.localHistory M K (m' + 1) Z) m')).image
      (fun i => torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm i.1) := by
    ext zb
    rw [hZb, Finset.mem_image]
    constructor
    · rintro ⟨y, hy1, hy2, hy3, rfl⟩
      exact ⟨⟨y, hy1, hy2⟩, by simpa using hy3, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i.1, i.2.1, i.2.2, by simpa using hi, rfl⟩
  rw [hLc]
  unfold ActionConv.constNat
  rw [hY]
  refine prod_rpow_image_le N _ _ ?_ (fun z => betaK S.d S.L (m' + 1) β0 * compWeightZ
    (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁ z) wz hwz1 ?_ ?_
  · intro i j h
    exact Subtype.ext (torusCast_injective _ h)
  · intro i hi
    exact mul_nonneg hβk.le (haZ _ (hmem i (by simpa using hi))).1.le
  · intro i hi
    have hi' := hmem i (by simpa using hi)
    have h1 : betaK S.d S.L (m' + 1) β0 * compWeightZ
        (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁
        (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm i.1) ≤
        betaK S.d S.L (m' + 1) β0 * a₁ := mul_le_mul_of_nonneg_left (haZ _ hi').2 hβk.le
    have h4 : betaK S.d S.L (m' + 1) β0 * compWeightZ
        (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁
        (torusCast (blk_eq_top H.F.hnn hm (le_refl (m' + 1))).symm i.1) ≤ 2 * wz i := by
      linarith [hwz2 i]
    rw [div_le_div_iff₀ (by positivity) Real.pi_pos]
    nlinarith [Real.pi_pos]

open Classical in
/-- **`e^{B_w} Q_tot ≤ e^{B_w} e^{L_c} Q_b`.** -/
theorem window_Qtot_le_exp (hCN : ActionConv.constNat N (betaK S.d S.L (m' + 1) β0)
      (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb ≤
        Real.exp Lc)
    (hbox : Nat.card {y : BlockAt S n M K (m' + 1) // y ∈ Vblk R (H.localHistory M K (m' + 1) Z) (m' + 1) ∧ y ∈ Z0} =
      (boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb).card) (hQb : 0 < Qb) :
    ENNReal.ofReal (Real.exp bw0) * Qtot ≤ ENNReal.ofReal (Real.exp bw0 * Real.exp Lc * Qb) := by
  rw [hQtotv, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  refine ENNReal.ofReal_le_ofReal ?_
  have hexp : Real.exp ((N : ℝ) / 2 * Real.log (betaK S.d S.L (m' + 1) β0) *
      ((boxFinset (L := S.L) (N₀ := M * n (m' + 1)) (k := m' + 1) b0 wb).card : ℝ) + CEt * (D0 : ℝ) ^ S.d +
      Cnat * S.lam (m' + 1) ^ (2 * S.d + 1) + 4 + ((9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) *
      ∑ i : (Option (Σ j : ↥(Finset.Ico k1 m'), Σ P : ↥(H.ancFin (j.1 + 1 + 1) (m' + 1) Z), ↥(H.parts (j.1 + 1) P.1))),
        (decomp i).total)) = Qb := by
    rw [hQbdef, ← hCk, hFz, hbox]
  rw [hexp]
  calc Real.exp bw0 * (ActionConv.constNat N (betaK S.d S.L (m' + 1) β0)
        (compWeightZ (windowOfHistory H Z geo hm hW |>.windowGenSet (windowOfHistory_hyp (g := geo) hm hW)) a₁) Zb * Qb)
      ≤ Real.exp bw0 * (Real.exp Lc * Qb) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCN hQb.le) (Real.exp_pos _).le
    _ = Real.exp bw0 * Real.exp Lc * Qb := by ring

end Core

end Balaban.LargeField
