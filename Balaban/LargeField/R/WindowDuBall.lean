/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffPhysDom
public import Balaban.LargeField.R.WindowDuRead

/-!
# The data of the pieces on the balls around their regions (blocker 4)

For a block field `ψ` whose two-scale lift is the datum of every piece on its data sites
(`hlift`, the hypothesis of `sum_mainActionLoc_eq_gen_of_flow_window_dom`):
* `window_hread_of_lift`: the read identity of the physical datum of `ψ` on the regions of the
  pieces (`window_field_read_eq_of_agree`);
* `window_ball_data_eq`: on the ball `B(X_i, 2 L^{j_i} M)` the datum of the piece `i` is the physical
  datum of `ψ` read at the identification (`piece_window_Ψ_eq_of_lift`), the equality of the data used
  in the stability estimate.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

universe u

section Ball

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K} {m' : ℕ} {Z : H.Comp (m' + 1)}
  {g : Geo S n R M}

/-- A site within `2 L^j M` (in the local torus) of the region of the piece `(j, c)` is, in the local
torus, a data site of the local generating set. -/
theorem ball_dist_mem_dataSites {j : ℕ} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (hj : j ≤ m') (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z)
    {y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    {z : Torus S.d (g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1))}
    (hz : z ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hzy : Green.torusDist S.d (g.M1 * (g.c * n (j + 1)) * S.L ^ (j + 1)) z
      (torusCast (piece_torus_eq g H.F.hnn hmK hj) y) ≤ 2 * ((S.L : ℝ) ^ j * M)) :
    torusCast (piece_torus_eq g H.F.hnn hmK hj) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK) := by
  set hT := piece_torus_eq g H.F.hnn hmK hj with hhT
  set e := Equiv.cast (congrArg (Torus S.d) hT) with he
  have hez : torusCast hT (e.symm z) = z := by
    rw [← torusCast_equivCast_apply]; exact e.apply_symm_apply z
  have hey : e.symm (torusCast hT y) = y := by
    rw [← torusCast_equivCast_apply]; exact e.symm_apply_apply y
  have hzX : torusCast hT (e.symm z) ∈ Xfine g (H.locRH (j + 1) c) j c.1 := by
    rw [hez]; exact hz
  have hd : Green.torusDist S.d (M * n (m' + 1) * S.L ^ (m' + 1)) y (e.symm z) ≤
      2 * ((S.L : ℝ) ^ j * M) := by
    have h1 := torusDist_equivCast_symm hT (torusCast hT y) z
    rw [hey] at h1
    rw [h1, Green.torusDist_comm_gen]; exact hzy
  have hsup : supDist y (e.symm z) ≤ 2 * (S.L ^ j * M) := by
    have := supDist_le_torusDist y (e.symm z)
    have h2 : (supDist y (e.symm z) : ℝ) ≤ ((2 * (S.L ^ j * M) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  exact ball_cast_mem_dataSites hmK hW hj hk1j hK hc hzX hsup

variable {ι : Type u} [Fintype ι]

/-- The hypotheses `hlift` of `sum_mainActionLoc_eq_gen_of_flow_window_dom`: the datum of each piece
is the two-scale lift of `ψ` on its data sites. -/
theorem window_hread_of_lift (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hlift : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈ dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) :
    ∀ (φw : ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω 1 × Fin N → ℂ)
      (a : ℕ → ℝ) (ν : ℝ) (i : ι),
      actionRegionC (Xc i) a ν (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ φw) =
        actionRegionC (Xw i) a ν (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)) φw := by
  classical
  have hk1p : 1 ≤ S.k1 (m' + 1) := hW.k1_pos hmK
  have hψ : ∀ i x, x ∈ (Xw i).sites →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          ((windowOfHistory H Z g hmK hW).full.layerIndex x) x) q : ℝ) : ℂ) := by
    intro i x hx
    have hxX := (hXw i x).1 hx
    obtain ⟨-, hlay⟩ := full_layerIndex_ball hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hxX
      (y := x) (by rw [supDist_self]; exact Nat.zero_le _)
    rw [hlay]
    refine hlift i x (ball_dist_mem_dataSites hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i)
      (z := torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) hxX ?_)
    rw [Green.torusDist_self_eq_zero]
    positivity
  intro φw a ν i
  exact window_field_read_eq_of_agree g hmK H.F.ok.two_le_L (fun j _ _ => g.hRlow j) hk1p
    (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
    (windowOfHistory_parentRefines H Z g hmK hW) (fun _ => rfl) rfl rfl jf cf hjf hcf hjK Xw hXw Xc
    hXc ou xu hv ψ hψ φw a ν i

/-- **The datum of a piece is the physical datum on the ball around its region** (`δψ = 0`, P7 (2.14)). -/
theorem window_ball_data_eq (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hlift : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈ dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) :
    ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
        (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ x = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) := by
  classical
  intro i x hx
  obtain ⟨z, hz, hzx⟩ := hx
  set hT := piece_torus_eq g H.F.hnn hmK (hjf i).2 with hhT
  set e := Equiv.cast (congrArg (Torus S.d) hT) with he
  have hex : torusCast hT (e.symm x) = x := by
    rw [← torusCast_equivCast_apply]; exact e.apply_symm_apply x
  have hez : torusCast hT (e.symm z) = z := by
    rw [← torusCast_equivCast_apply]; exact e.apply_symm_apply z
  have hzX : torusCast hT (e.symm z) ∈ Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 := by
    rw [hez, ← hXc i]; exact hz
  have hd : Green.torusDist S.d (M * n (m' + 1) * S.L ^ (m' + 1)) (e.symm x) (e.symm z) ≤
      2 * ((S.L : ℝ) ^ jf i * M) := by
    rw [torusDist_equivCast_symm hT x z, Green.torusDist_comm_gen]; exact hzx
  have hsup : supDist (e.symm x) (e.symm z) ≤ 2 * (S.L ^ jf i * M) := by
    have := supDist_le_torusDist (e.symm x) (e.symm z)
    have h2 : (supDist (e.symm x) (e.symm z) : ℝ) ≤ ((2 * (S.L ^ jf i * M) : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h2
  have hl := hlift i (e.symm x)
    (ball_dist_mem_dataSites hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) (z := z) (by
      rw [hXc i] at hz; exact hz) (by rw [hex]; exact hzx))
  have key := piece_window_Ψ_eq_of_lift hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hzX hsup ψ
    (fun q => hv q) _ hl
  rw [hex] at key
  exact key

/-- **Equal layers on the ball** (wrapper of `piece_window_layers_switch`). -/
theorem window_ball_layers (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) :
    ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      ∀ q, 1 ≤ q → q ≤ jf i + 1 + 1 →
        (x ∈ (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).Ω q ↔ (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x ∈ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)).Ω q) :=
  fun i x hx q hq1 hq2 => piece_window_layers_switch hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i)
    (Xc i).sites (fun z hz => by rw [hXc i] at hz; exact hz) x hx q hq1 hq2

section Piece

variable {Hl : RegionHistory S n R k0 K} {j : ℕ} {Zc : Finset (Torus S.d (n (j + 1)))}
  {hZc : Zc ∈ comps (S.omega (j + 1)) (Hl.F.Zp (j + 1))} {hk : j + 1 ≤ K}

/-- The external field of the local datum is the unit vector `hv` on `Ω₁`. -/
theorem locData_h_unit (o : OutT N R (locHist Hl M K (j + 1) Zc) (j + 1))
    (x : NewCfg N (locHist Hl M K (j + 1) Zc) j) (hv : EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1) (y : (locGen g Hl j Zc hZc hk).Ω 1) :
    ∑ q, ‖(locData g Hl j Zc hZc hk o x hv).h y q‖ ^ 2 = 1 := by
  have hh : (locData g Hl j Zc hZc hk o x hv).h y = fun q => ((hv q : ℝ) : ℂ) := by
    unfold locData
    rw [liftMixed_h _ _ _ _ _ _ y.2]
  have h1 := EuclideanSpace.norm_sq_eq hv
  rw [hunit] at h1
  rw [hh]
  simpa [Complex.norm_real] using h1.symm

end Piece

/-- **The region of the window is the union of the regions of the pieces.** -/
theorem window_sites_subset (hmK : m' + 1 ≤ K)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hcov : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
    (hW : H.RipeWindow (m' + 1) Z)
    (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXwin : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1) :
    Xwin.sites ⊆ Finset.univ.biUnion fun i => (Xw i).sites := by
  classical
  have hQ : ∀ (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) (s s' : Σ j, H.Comp (j + 1)),
      s = s' → ((∃ hj : s.1 ≤ m', torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        Xfine g (H.locRH (s.1 + 1) s.2) s.1 s.2.1) ↔
      ∃ hj : s'.1 ≤ m', torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        Xfine g (H.locRH (s'.1 + 1) s'.2) s'.1 s'.2.1) := by
    intro x s s' h
    subst h
    exact Iff.rfl
  intro x hx
  obtain ⟨j, hj, c, hc, hx'⟩ := (hXwin x).1 hx
  obtain ⟨i, hi⟩ := hcov j c hj.1 hj.2 hc
  refine Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, (hXw i x).2 ?_⟩
  exact ((hQ x _ _ hi.symm).1 ⟨hj.2, hx'⟩).2

/-- The regions of a piece in the window and in the local generating set have the same number of sites. -/
theorem window_card_sites_eq (hmK : m' + 1 ≤ K)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hjK : ∀ i, jf i + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (i : ι) :
    (Xw i).sites.card = (Xc i).sites.card :=
  Finset.card_equiv (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) fun x => by
    rw [hXw i x, hXc i, torusCast_equivCast_apply]

end Ball

section Generic

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ}

/-- The mass term `ν ℓ(x)²` is at most `m` as soon as `ν L^{2k} ≤ m`. -/
theorem mass_spacing_le {G : GeneratingSet d L N₀ K ϱ} {ν m : ℝ} (hν : 0 ≤ ν)
    (hm : ν * ((L : ℝ) ^ K) ^ 2 ≤ m) (x : G.Ω 1) :
    ν * G.spacing (x : Torus d (N₀ * L ^ K)) ^ 2 ≤ m := by
  have h1 := spacing_le G x.2
  have h0 := (spacing_pos G (x := (x : Torus d (N₀ * L ^ K)))).le
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 2) hν).trans hm

/-- The radius `2 L^j M` of the ball around a piece is at least `1`. -/
theorem one_le_ball_radius {M : ℕ} [NeZero M] (j : ℕ) : (1 : ℝ) ≤ 2 * ((L : ℝ) ^ j * M) := by
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne L)
  have hM : (1 : ℝ) ≤ M := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne M)
  have hp : (1 : ℝ) ≤ (L : ℝ) ^ j := one_le_pow₀ hL
  nlinarith only [hp, hM]

end Generic

section Near

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' : ℕ} {Z : H.Comp (m' + 1)}
  {g : Geo S n R M} {ι : Type u} [Fintype ι]

/-- A site in or next to the region of the window lies in the ball around the region of some piece. -/
theorem window_near_ball (hmK : m' + 1 ≤ K)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hjK : ∀ i, jf i + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (hsub : Xwin.sites ⊆ Finset.univ.biUnion fun i => (Xw i).sites)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1)))
    (hy : y ∈ Xwin.sites ∨ ∃ μ : Fin S.d, y + Pi.single μ 1 ∈ Xwin.sites ∨
      y - Pi.single μ 1 ∈ Xwin.sites) :
    ∃ i, ∃ z ∈ (Xc i).sites, Green.torusDist S.d
      (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z
      ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) y) ≤ 2 * ((S.L : ℝ) ^ jf i * M) := by
  classical
  obtain ⟨x, hx, hrel⟩ : ∃ x ∈ Xwin.sites,
      (y = x ∨ ∃ μ : Fin S.d, y = x + Pi.single μ 1 ∨ y = x - Pi.single μ 1) := by
    rcases hy with hy | ⟨μ, hy | hy⟩
    · exact ⟨y, hy, Or.inl rfl⟩
    · exact ⟨_, hy, Or.inr ⟨μ, Or.inr (by simp)⟩⟩
    · exact ⟨_, hy, Or.inr ⟨μ, Or.inl (by simp)⟩⟩
  obtain ⟨i, -, hxi⟩ := Finset.mem_biUnion.1 (hsub hx)
  refine ⟨i, (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) x, ?_, ?_⟩
  · rw [hXc i, torusCast_equivCast_apply]
    exact (hXw i x).1 hxi
  · refine (torusDist_le_one_of_near _ _ ?_).trans (one_le_ball_radius (L := S.L) (M := M) (jf i))
    rcases hrel with rfl | ⟨μ, rfl | rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨μ, Or.inl (equivCast_add_single (piece_torus_eq g H.F.hnn hmK (hjf i).2) x μ)⟩
    · refine Or.inr ⟨μ, Or.inr ?_⟩
      have h1 := equivCast_add_single (piece_torus_eq g H.F.hnn hmK (hjf i).2) (x - Pi.single μ 1) μ
      rw [sub_add_cancel] at h1
      rw [eq_sub_iff_add_eq, ← h1]

end Near

end Balaban.LargeField
