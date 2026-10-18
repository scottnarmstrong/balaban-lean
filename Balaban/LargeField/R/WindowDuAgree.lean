/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuBall
public import Balaban.LargeField.R.WindowLiftConv

/-!
# The reference datum agrees with the physical datum on the balls (blocker 4)

`du_eq_physical_of_fields`: a datum `Du` of the window generating set whose values on `Ω₁` are the
variables of the window point (`ψ_s` on the layer `s ≠ m'+1`, the output `o` on the layer `m'+1`),
read at the layer index of the window generating set, is the physical datum of the variable field
`ψ` (read at the layer index of the parent generating set) at every site where the two layer indices
agree.  `window_layer_eq_full_ball`: they agree on the ball `B(X_i, 2 L^{j_i} M)` around the region of
every piece.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

section Agree

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K} {m' : ℕ} {Z : H.Comp (m' + 1)}
  {g : Geo S n R M}

/-- **The datum `Du` is the physical datum where the layer indices agree.** -/
theorem du_eq_physical_of_fields (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {A : Set (InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1))}
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ1 : ∀ b, ψ ⟨m' + 1, b⟩ = outField N o (torusCast (blk_eq_top H.F.hnn hmK le_rfl) b))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hmK (hi.trans (Nat.le_succ _))) b))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (Fs : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (Ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hFs : ∀ s y, Fs s y = subVarField N x s y) (hFt : ∀ y, Ft y = outField N o y)
    (hDu1 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1,
      ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y ≠ m' + 1 →
        ∀ i, Du.Ψ y i = ((Fs (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
          (jBlock S.d S.L (M * n K) K
            (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
            (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    (hDu2 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1,
      ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y = m' + 1 →
        ∀ i, Du.Ψ y i = ((Ft (jBlock S.d S.L (M * n K) K (m' + 1)
          (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hy : y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1)
    (hyf : y ∈ (windowOfHistory H Z g hmK hW).full.Ω 1)
    (hlay : ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y =
      (windowOfHistory H Z g hmK hW).full.layerIndex y) :
    Du.Ψ y = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
      (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ y := by
  classical
  have hyd : y ∈ dataSites ((windowOfHistory H Z g hmK hW).windowGenSet
      (windowOfHistory_hyp hmK hW)) := (mem_dataSites _).2 (Or.inl hy)
  funext i
  rw [physicalWindowData_Ψ _ _ _ ψ _ hyd i, inheritedField_eq_parentBlock,
    parentBlock_of_mem _ hyf, ← hlay]
  obtain ⟨hl1, hl2, -⟩ := ((windowOfHistory H Z g hmK hW).windowGenSet
    (windowOfHistory_hyp hmK hW)).layerIndex_spec hy
  have h1 := hDu1 y hy
  have h2 := hDu2 y hy
  generalize ((windowOfHistory H Z g hmK hW).windowGenSet
    (windowOfHistory_hyp hmK hW)).layerIndex y = ℓ at hl1 hl2 h1 h2 ⊢
  have hx0 : jBlock S.d S.L (M * n K) K ℓ (torusCast (fine_eq_top H.F.hnn hmK).symm y) =
      torusCast (blk_eq_top H.F.hnn hmK hl2)
        (jBlock S.d S.L (M * n (m' + 1)) (m' + 1) ℓ y) :=
    jBlock_torusCast hl2 (hl2.trans hmK) (fine_eq_top H.F.hnn hmK).symm _ y
  by_cases hℓ : ℓ = m' + 1
  · subst hℓ
    rw [h2 rfl i, hx0, hFt]
    unfold blockOf
    rw [hψ1]
  · have hℓ' : ℓ ≤ m' := by omega
    rw [h1 hℓ i, hx0, hFs]
    unfold blockOf
    rw [hψ0 ℓ hℓ']

/-- **The layer index of the window generating set is that of the parent on the ball** around the
region of a piece (P7 (2.14)). -/
theorem window_layer_eq_full_ball {j : ℕ} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j ≤ m') (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M)) :
    y ∈ (windowOfHistory H Z g hmK hW).full.Ω 1 ∧
      y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1 ∧
      ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y =
        (windowOfHistory H Z g hmK hW).full.layerIndex y := by
  classical
  have hk1pos := hW.k1_pos hmK
  have hL := H.F.ok.two_le_L
  have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
  have hLr : (2 : ℝ) ≤ S.L := by exact_mod_cast hL
  have hfl : ∀ q, 2 ≤ ⌊R q⌋₊ := fun q => by
    refine Nat.le_floor ?_
    have := g.hRlow q
    push_cast; linarith
  obtain ⟨hyj, hlay⟩ := full_layerIndex_ball hmK hW hj hk1j hK hc hx hxy
  obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hmK hj c hK x).1 hx
  set W := windowOfHistory H Z g hmK hW with hWdef
  have hy1 : y ∈ W.full.Ω 1 := W.full.Ω_antitone le_rfl (by omega) (by omega) hyj
  have hiff : ∀ q, 1 ≤ q → q ≤ j + 1 →
      (y ∈ (W.windowGenSet (windowOfHistory_hyp hmK hW)).Ω q ↔ y ∈ W.full.Ω q) :=
    fun q hq1 hq2 => windowGenSet_Ω_ball hmK hW hj hk1j hc hx1 hx2 (t := 2) (by omega)
      (by have := hfl m'; omega) hxy hq1 hq2
  have hyw1 : y ∈ (W.windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1 :=
    (hiff 1 le_rfl (by omega)).2 hy1
  refine ⟨hy1, hyw1, ?_⟩
  obtain ⟨hf1, hf2, hf3⟩ := W.full.layerIndex_spec hy1
  rw [W.full.mem_layer] at hf3
  have hnw : y ∉ (W.windowGenSet (windowOfHistory_hyp hmK hW)).Ω (j + 2) := by
    rcases lt_or_eq_of_le hj with hjm | hjm
    · exact windowGenSet_Ω_not_mem_ball hmK hW hjm hk1j hc hx1 (t := 2) (hfl (j + 1)) hxy
        (m := j + 2) le_rfl (by omega)
    · subst hjm
      rw [(W.windowGenSet (windowOfHistory_hyp hmK hW)).top]
      exact Finset.notMem_empty _
  have hlj : W.full.layerIndex y ≤ j + 1 := by rw [hlay]; split_ifs <;> omega
  refine (W.windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex_eq hf1 hf2 ?_
  rw [(W.windowGenSet (windowOfHistory_hyp hmK hW)).mem_layer]
  refine ⟨(hiff _ hf1 hlj).2 hf3.1, fun h => ?_⟩
  by_cases hq : W.full.layerIndex y + 1 ≤ j + 1
  · exact hf3.2 ((hiff _ (by omega) hq).1 h)
  · have h2 : W.full.layerIndex y = j + 1 := by omega
    rw [h2] at h
    exact hnw h

universe u

/-- **`Du` is the physical datum on the balls around the regions of the pieces.** -/
theorem du_ball_eq (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    {ι : Type u} (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    {A : Set (InternalVars (H.localHistory M K (m' + 1) Z) (m' + 1))}
    (o : OutT N R (H.localHistory M K (m' + 1) Z) (m' + 1))
    (x : SubCfg N (H.localHistory M K (m' + 1) Z) (m' + 1) A)
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hψ1 : ∀ b, ψ ⟨m' + 1, b⟩ = outField N o (torusCast (blk_eq_top H.F.hnn hmK le_rfl) b))
    (hψ0 : ∀ i (hi : i ≤ m') b, ψ ⟨i, b⟩ =
      subVarField N x i (torusCast (blk_eq_top H.F.hnn hmK (hi.trans (Nat.le_succ _))) b))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (Fs : ∀ s, BlockAt S n M K s → EuclideanSpace ℝ (Fin N))
    (Ft : BlockAt S n M K (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hFs : ∀ s y, Fs s y = subVarField N x s y) (hFt : ∀ y, Ft y = outField N o y)
    (hDu1 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y ≠ m' + 1 →
        ∀ i, Du.Ψ y i = ((Fs (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
          (jBlock S.d S.L (M * n K) K (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y)
            (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ))
    (hDu2 : ∀ y ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1, ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).layerIndex y = m' + 1 →
        ∀ i, Du.Ψ y i = ((Ft (jBlock S.d S.L (M * n K) K (m' + 1)
          (torusCast (fine_eq_top H.F.hnn hmK).symm y)) i : ℝ) : ℂ)) :
    ∀ (i : ι) (x' : Torus S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1))),
      (∃ z ∈ (Xc i).sites, Green.torusDist S.d
        (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x' ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x') = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x') := by
  intro i x' ⟨z, hz, hzx⟩
  rw [hXc i] at hz
  obtain ⟨z', hz'X, hsup⟩ := ball_witness hmK (hjf i).2 hz hzx
  obtain ⟨hyf, hyw, hl⟩ := window_layer_eq_full_ball hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i)
    hz'X hsup
  exact du_eq_physical_of_fields hmK hW o x hv ψ hψ1 hψ0 Du Fs Ft hFs hFt hDu1 hDu2 hyw hyf hl

end Agree

end Balaban.LargeField
