/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffPhysDom
public import Balaban.LargeField.R.WindowDuPiece
public import Balaban.LargeField.R.WindowDuBall
public import Balaban.LargeField.R.WindowDuAssemble

/-!
# The window conversion at the reference datum of the hid chain (blocker 4)

P7 (2.11)-(2.16), (2.58').  `sum_mainActionLoc_eq_gen_of_flow_window_Du` is
`sum_mainActionLoc_eq_gen_of_flow_window_dom` with the window background `bgFieldC` at the mass `ν_{m'+1}`
of the physical datum replaced by the window background at mass `0` of a datum `Du` with external field
`0` and the same `Ψ` as the physical datum on the balls around the pieces (the hid datum, with the
inherited collar).  The window action is `A_{X_win}(a_k, 0, Du, φ_Du)`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

universe u

section Du

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

/-- **window_Du_hswitch with the constants first**: the constants are produced before the window point and all the data and depend only on `(d, L, N)`.  The landed `window_Du_hswitch` is this theorem at the data. -/
theorem window_Du_hswitch_constsP (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Ks δs Kw' δm : ℝ, 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (_ : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (hjK : ∀ i, jf i + 1 ≤ K) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (_ : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (decomp : ∀ i, StepDecomp (Xc i)) (_ : ∀ i c, (decomp i).wt c = 1) (_ : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).blk ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x) x ∧
        (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x ≤ jf i + 1) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ‖hv‖ = 1) (_ : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈ dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) (t : ι → ℕ) (_ : ∀ i, BallRadiusOK R m' (jf i) (t i)) (_ : ∀ i, 2 ≤ t i) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N) (_ : ∀ x i, Du.h x i = 0) (_ : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ (t i : ℝ) * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x))
    (i : ι)
      (ak : ℕ → ℝ) (β ν η Ka ε₀ α α₀ Emax Amax Cb Cg Cm V Kswitch ϱB δl δu m : ℝ)
      (gf δ : ℕ → ℝ) (_ : 0 < β) (_ : 0 < α₀) (_ : 0 ≤ α)
      (_ : ∀ m, cs.beta m = β * (S.L : ℝ) ^ ((S.d - 2) * m) * gf m)
      (_ : ∀ m, cs.muAct m = ν * δ m)
      (_ : ∀ m, Real.exp (-η) ≤ gf m ∧ gf m ≤ Real.exp η)
      (_ : β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) *
        epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax)
      (_ : ∀ ℓ, |ak ℓ| ≤ Ka)
      (_ : 0 < ε₀) (_ : ε₀ ^ 2 ≤ epsSeq S.L α α₀ (jf i + 1) ^ 2)
      (_ : ∃ N₁ m₁ : ℕ, g.M1 * (g.c * n (jf i + 1)) = N₁ * S.L ^ m₁)
      (_ : BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) ak (cs.muAct (m' + 1)))
      (_ : (4 * S.d + 6) * ((2 * S.d + 1) * epsSeq S.L α α₀ (jf i + 1)) ≤ 1)
      (_ : xiC1 S.d * epsSeq S.L α α₀ (jf i + 1) ≤ bgC1 S.d S.L N)
      (_ : XiCOneReal (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
      (_ : epsSeq S.L α α₀ (jf i + 1) ≤ Emax)
      (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
      (_ : 0 ≤ Cm)
      (_ : β * Real.exp η * (((S.L : ℝ) ^ (jf i + 1)) ^ S.d * (|ν| * |δ (m' + 1)|)) ≤
        Cm * (β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2))
      (_ : 0 < cs.muAct (m' + 1))
      (_ : BgHyp S.d S.L (m' + 1) (winSep g) ak 0)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : 0 < δl) (_ : δl ≤ bgC1 S.d S.L N)
      (_ : InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
      (_ : 0 < δu) (_ : δu ≤ bgC1 S.d S.L N) (_ : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
      (_ : bgK1 S.d S.L N * (δl + δu) ≤ δs)
      (_ : bgK1 S.d S.L N * δl ≤ min (deltaStar S.d S.L N) δm) (_ : 0 ≤ m)
      (_ : m * 2 ≤ min (deltaStar S.d S.L N) δm)
      (_ : cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 ≤ m)
      (_ : Ks * ((δl + δu) * Real.exp (-(gammaW S.d *
        (((t i : ℝ) * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
          (S.L : ℝ) ^ (jf i + 1))))) + Kw' * (m * 2) ≤ V)
      (_ : Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((S.d * ((4 * Emax ^ 2) * Cg)) * (S.d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |cs.muAct (m' + 1)|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + S.d * (N * Cg) + N * Cm)) ≤ Kswitch),
      ‖(betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (bgFieldC (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)) -
        (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ
              (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du))‖ ≤ Kswitch * (decomp i).total := by
  obtain ⟨Ks, δs, Kw', δm, hKs, hδs, hKw', hδm, hpiece⟩ :=
    switch_piece_massZeroP (L := S.L) N hd3 hL3
  refine ⟨Ks, δs, Kw', δm, hKs, hδs, hKw', hδm, ?_⟩
  intro n _ R k0 K M _ H g cs m' Z hmK hW ι _ jf cf hjf hcf hjK Xc hXc decomp hwt1 hcells ou xu hv ψ hunit hlift t hR ht2 Du hDuh hDuball i ak β ν η Ka ε₀ α α₀ Emax Amax Cb Cg Cm V Kswitch ϱB δl δu m gf δ q1 q3 q5 q8 q9 q12
    qA q19 q25 q26 q27 q29 q31 q32 q35 q39 q40 q41 qC0 q42 hνk hHw0 s2 s3 s4 hconst s7 s8 s9 u1
    u2 u3 t16 mA mB mC mD tV tK
  have hdat := window_ball_data_eqT (hR := hR) hmK hW jf cf hjf hcf hjK Xc hXc ou xu hv ψ hlift
  have hlay := window_ball_layersT (hR := hR) hmK hW jf cf hjf hcf hjK Xc hXc
  have hj1 : jf i + 1 ≤ m' + 1 := Nat.succ_le_succ (hjf i).2
  have hβ' : betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 = β * gf (m' + 1) :=
    betaCanon_eq_of_flow cs S.d S.L β gf q8 (m' + 1)
  have hεpos : 0 < epsSeq S.L α α₀ (jf i + 1) := epsSeq_pos_aux S.L α α₀ q3 (jf i + 1)
  have hΨi : ∀ x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ (t i : ℝ) * ((S.L : ℝ) ^ jf i * M)) →
      vn (fun j => (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ x j - Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) j) ≤ 0 := by
    intro x hx
    rw [hdat i x hx, hDuball i x hx]
    have h0 : (fun j => (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) j - (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) j) = (0 : Fin N → ℂ) :=
      funext fun _ => sub_self _
    rw [h0, vn_zero]
  have key := hpiece _ ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) (piece_torus_eq g H.F.hnn hmK (hjf i).2) q27 q29 hHw0 s2 s3 s4
    hj1 (Xc i) (decomp i) (hwt1 i) (hcells i) ((t i : ℝ) * ((S.L : ℝ) ^ jf i * M))
    (ball_radius_of_const_t g ϱB hconst (jf i) (ht2 i)) (hlay i) s7 s8 s9 u1 u2 u3 le_rfl hΨi
    (fun x _ j => hDuh _ j) (fun y => locData_h_unit (ou i) (xu i) hv hunit y)
    (by rw [add_zero]; exact t16) mA mB mC
    (fun x => mass_spacing_le hνk.le mD x) hβ' q1 (q12 _).2 (q12 _).1 (q12 _).1 (q9 _) hνk
    q25 q26 q19 q40 q41 qC0 q42 hεpos q31 q32 q35 q39 qA (by rw [zero_add]; exact tV) tK
  have hnear : ∀ y : ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).Ω 1,
      (((y : Torus S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1))) ∈ (Xc i).sites ∨ ∃ μ : Fin S.d,
        (y : Torus S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1))) + Pi.single μ 1 ∈ (Xc i).sites ∨
        (y : Torus S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1))) - Pi.single μ 1 ∈ (Xc i).sites)) →
      ∀ j, transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ
          (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du) (y, j) =
        transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) Du.Ψ
          (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du) (y, j) := by
    intro y hy j
    have hb := Region.exists_dist_le_of_near (Xc i) hy (one_le_ball_radius_t (L := S.L) (M := M) (jf i) (ht2 i))
    have hy1 := (hlay i _ hb 1 le_rfl (by omega)).1 y.2
    exact transportField_congr_of_mem _ _ _ _ y hy1 j
  rw [actionRegionC_congr_field (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv) hnear]
  exact key

/-- **window_Du_hswitch with the constants first**: the constants are produced before the window point and all the data and depend only on `(d, L, N)`.  The landed `window_Du_hswitch` is this theorem at the data. -/
theorem window_Du_hswitch_consts (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Ks δs Kw' δm : ℝ, 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (_ : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (hjK : ∀ i, jf i + 1 ≤ K) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (_ : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (decomp : ∀ i, StepDecomp (Xc i)) (_ : ∀ i c, (decomp i).wt c = 1) (_ : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).blk ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x) x ∧
        (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x ≤ jf i + 1) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ‖hv‖ = 1) (_ : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈ dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N) (_ : ∀ x i, Du.h x i = 0) (_ : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x))
    (i : ι)
      (ak : ℕ → ℝ) (β ν η Ka Dδ ε₀ α α₀ Emax Amax Cb Cg Cm V Kswitch ϱB δl δu m : ℝ)
      (gf δ : ℕ → ℝ) (_ : 0 < β) (_ : 0 < α₀) (_ : 0 ≤ α)
      (_ : ∀ m, cs.beta m = β * (S.L : ℝ) ^ ((S.d - 2) * m) * gf m)
      (_ : ∀ m, cs.muAct m = ν * δ m)
      (_ : ∀ m, Real.exp (-η) ≤ gf m ∧ gf m ≤ Real.exp η)
      (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ)
      (_ : β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) *
        epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax)
      (_ : ∀ ℓ, |ak ℓ| ≤ Ka)
      (_ : β * |ν| * (S.L : ℝ) ^ ((m' + 1) * S.d) ≤ 1)
      (_ : 0 < ε₀) (_ : ε₀ ≤ α₀ * ((S.L : ℝ) ^ (-α)) ^ (m' + 1))
      (_ : ∃ N₁ m₁ : ℕ, g.M1 * (g.c * n (jf i + 1)) = N₁ * S.L ^ m₁)
      (_ : BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) ak (cs.muAct (m' + 1)))
      (_ : (4 * S.d + 6) * ((2 * S.d + 1) * epsSeq S.L α α₀ (jf i + 1)) ≤ 1)
      (_ : xiC1 S.d * epsSeq S.L α α₀ (jf i + 1) ≤ bgC1 S.d S.L N)
      (_ : XiCOneReal (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
      (_ : epsSeq S.L α α₀ (jf i + 1) ≤ Emax)
      (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
      (_ : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
      (_ : 0 < cs.muAct (m' + 1))
      (_ : BgHyp S.d S.L (m' + 1) (winSep g) ak 0)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : 0 < δl) (_ : δl ≤ bgC1 S.d S.L N)
      (_ : InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
      (_ : 0 < δu) (_ : δu ≤ bgC1 S.d S.L N) (_ : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
      (_ : bgK1 S.d S.L N * (δl + δu) ≤ δs)
      (_ : bgK1 S.d S.L N * δl ≤ min (deltaStar S.d S.L N) δm) (_ : 0 ≤ m)
      (_ : m * 2 ≤ min (deltaStar S.d S.L N) δm)
      (_ : cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 ≤ m)
      (_ : Ks * ((δl + δu) * Real.exp (-(gammaW S.d *
        ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
          (S.L : ℝ) ^ (jf i + 1))))) + Kw' * (m * 2) ≤ V)
      (_ : Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((S.d * ((4 * Emax ^ 2) * Cg)) * (S.d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |cs.muAct (m' + 1)|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + S.d * (N * Cg) + N * Cm)) ≤ Kswitch),
      ‖(betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (bgFieldC (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)) -
        (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ
              (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du))‖ ≤ Kswitch * (decomp i).total := by
  obtain ⟨Ks, δs, Kw', δm, hKs, hδs, hKw', hδm, HP⟩ := window_Du_hswitch_constsP S N hd3 hL3
  refine ⟨Ks, δs, Kw', δm, hKs, hδs, hKw', hδm, ?_⟩
  intro n _ R k0 K M _ H g cs m' Z hmK hW ι _ jf cf hjf hcf hjK Xc hXc decomp hwt1 hcells ou xu hv ψ hunit hlift Du hDuh hDuball i ak β ν η Ka Dδ ε₀ α α₀ Emax Amax Cb Cg Cm V Kswitch ϱB δl δu m gf δ q1 q3 q5 q8 q9 q12 q13
    q14 qA q19 q24 q25 q26 q27 q29 q31 q32 q35 q39 q40 q41 q42 hνk hHw0 s2 s3 s4 hconst s7 s8 s9 u1
    u2 u3 t16 mA mB mC mD tV tK
  have hj1 : jf i + 1 ≤ m' + 1 := Nat.succ_le_succ (hjf i).2
  have hδk : |δ (m' + 1)| ≤ Dδ := by rw [abs_of_pos (q13 _)]; exact q14 _
  have hE2 : ε₀ ^ 2 ≤ epsSeq S.L α α₀ (jf i + 1) ^ 2 :=
    (pow_le_pow_left₀ q25.le q26 2).trans (ActionConv.epsSeq_sq_ge S.L q5 q3 hj1)
  have hCm0' : 0 ≤ Cm := le_trans (by
    have : 0 ≤ Dδ := (abs_nonneg _).trans hδk
    positivity) q42
  have hCm' : β * Real.exp η * (((S.L : ℝ) ^ (jf i + 1)) ^ S.d * (|ν| * |δ (m' + 1)|)) ≤
      Cm * (β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) *
        epsSeq S.L α α₀ (jf i + 1) ^ 2) :=
    mass_budget_of_regime q1 hj1 q25 hE2 (q12 _).1 q24 hδk q42
  exact @HP n _ R k0 K M _ H g cs m' Z hmK hW ι _ jf cf hjf hcf hjK Xc hXc decomp hwt1 hcells ou xu hv
    ψ hunit hlift (fun _ => 2) (fun i => ballRadiusOK_two H g m' (jf i)) (fun _ => le_rfl) Du hDuh
    (by simpa using hDuball) i ak β ν η Ka ε₀ α α₀ Emax Amax Cb Cg Cm V Kswitch ϱB δl δu m gf δ q1 q3
    q5 q8 q9 q12 qA q19 q25 hE2 q27 q29 q31 q32 q35 q39 q40 q41 hCm0' hCm' hνk hHw0 s2 s3 s4 hconst s7
    s8 s9 u1 u2 u3 t16 mA mB mC mD (by simpa using tV) tK

/-- **The switch of the piece `i`** to the window background at mass `0` of `Du`, on the real flow,
read through the physical datum of `ψ`. -/
theorem window_Du_hswitch (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)}
    (hmK : m' + 1 ≤ K) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) (hW : H.RipeWindow (m' + 1) Z)
    {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (hXc : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (decomp : ∀ i, StepDecomp (Xc i))
    (hwt1 : ∀ i c, (decomp i).wt c = 1)
    (hcells : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).blk ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x) x ∧
        (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x ≤ jf i + 1)
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hv : EuclideanSpace ℝ (Fin N))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1)
    (hlift : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈ dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (hDuh : ∀ x i, Du.h x i = 0)
    (hDuball : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x)) :
    ∃ Ks δs Kw' δm : ℝ, 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ (i : ι)
      (ak : ℕ → ℝ) (β ν η Ka Dδ ε₀ α α₀ Emax Amax Cb Cg Cm V Kswitch ϱB δl δu m : ℝ)
      (gf δ : ℕ → ℝ) (_ : 0 < β) (_ : 0 < α₀) (_ : 0 ≤ α)
      (_ : ∀ m, cs.beta m = β * (S.L : ℝ) ^ ((S.d - 2) * m) * gf m)
      (_ : ∀ m, cs.muAct m = ν * δ m)
      (_ : ∀ m, Real.exp (-η) ≤ gf m ∧ gf m ≤ Real.exp η)
      (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ)
      (_ : β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) *
        epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax)
      (_ : ∀ ℓ, |ak ℓ| ≤ Ka)
      (_ : β * |ν| * (S.L : ℝ) ^ ((m' + 1) * S.d) ≤ 1)
      (_ : 0 < ε₀) (_ : ε₀ ≤ α₀ * ((S.L : ℝ) ^ (-α)) ^ (m' + 1))
      (_ : ∃ N₁ m₁ : ℕ, g.M1 * (g.c * n (jf i + 1)) = N₁ * S.L ^ m₁)
      (_ : BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) ak (cs.muAct (m' + 1)))
      (_ : (4 * S.d + 6) * ((2 * S.d + 1) * epsSeq S.L α α₀ (jf i + 1)) ≤ 1)
      (_ : xiC1 S.d * epsSeq S.L α α₀ (jf i + 1) ≤ bgC1 S.d S.L N)
      (_ : XiCOneReal (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
      (_ : epsSeq S.L α α₀ (jf i + 1) ≤ Emax)
      (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
      (_ : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
      (_ : 0 < cs.muAct (m' + 1))
      (_ : BgHyp S.d S.L (m' + 1) (winSep g) ak 0)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : 0 < δl) (_ : δl ≤ bgC1 S.d S.L N)
      (_ : InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
      (_ : 0 < δu) (_ : δu ≤ bgC1 S.d S.L N) (_ : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
      (_ : bgK1 S.d S.L N * (δl + δu) ≤ δs)
      (_ : bgK1 S.d S.L N * δl ≤ min (deltaStar S.d S.L N) δm) (_ : 0 ≤ m)
      (_ : m * 2 ≤ min (deltaStar S.d S.L N) δm)
      (_ : cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 ≤ m)
      (_ : Ks * ((δl + δu) * Real.exp (-(gammaW S.d *
        ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
          (S.L : ℝ) ^ (jf i + 1))))) + Kw' * (m * 2) ≤ V)
      (_ : Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((S.d * ((4 * Emax ^ 2) * Cg)) * (S.d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |cs.muAct (m' + 1)|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + S.d * (N * Cg) + N * Cm)) ≤ Kswitch),
      ‖(betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (bgFieldC (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)) -
        (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC (Xc i) ak (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))) (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ
              (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du))‖ ≤ Kswitch * (decomp i).total := by
  obtain ⟨Ks, δs, Kw', δm, h0, h1, h2, h3, Hc⟩ := window_Du_hswitch_consts S N hd3 hL3
  exact ⟨Ks, δs, Kw', δm, h0, h1, h2, h3, Hc g cs hmK hW jf cf hjf hcf hjK Xc hXc decomp hwt1 hcells ou xu hv ψ hunit hlift Du hDuh hDuball⟩

open Classical in
open Classical in
/-- The conclusion of `sum_mainActionLoc_eq_gen_of_flow_window_Du` with per-piece constants, for given constants `Kw δw Ks δs Kw' δm`: for every admissible choice of the caller's constants, the sum of the piece actions equals the real part of the window action at the datum `Du` up to a remainder bounded by the weights. -/
def WindowDuClaimP (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjK : ∀ i, jf i + 1 ≤ K) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (decomp : ∀ i, StepDecomp (Xc i)) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1) ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (t : ι → ℕ) (Kw δw Ks δs Kw' δm : ℝ) : Prop :=
  ∀
      (ak : ℕ → ℝ)
      (β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair : ℝ)
      (Δ Kwt Cb Cg Cm Amax Emax ε₀ Kcoef Kswitch : ι → ℝ)
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
      (_ : ∀ i, cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax i)
      (_ : ∀ ℓ, |ak ℓ| ≤ Ka) (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : ∀ i, ∀ ℓ, |cs.aw ℓ - ak ℓ| ≤ Δ i)
      (_ : 0 ≤ cν) (_ : ν * (S.L : ℝ) ^ (2 * (m' + 1)) * Dδ ≤ cν ^ 2)
      (_ : ∀ i, 0 < ε₀ i) (_ : ∀ i, ε₀ i ^ 2 ≤ epsSeq S.L α α₀ (jf i + 1) ^ 2)
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
      (_ : ∀ i, Δ i * (2 * epsSeq S.L α α₀ (jf i + 1)) ≤ min (deltaStar S.d S.L N) δw)
      (_ : ∀ i, epsSeq S.L α α₀ (jf i + 1) ≤ Emax i)
      (_ : ∀ i, Real.exp (2 * η) * Ka / ε₀ i ^ 2 ≤ Cb i) (_ : ∀ i, Real.exp (2 * η) / ε₀ i ^ 2 ≤ Cg i)
      (_ : ∀ i, 0 ≤ Cm i)
      (_ : ∀ i, β * Real.exp η * (((S.L : ℝ) ^ (jf i + 1)) ^ S.d * (|ν| * |δ (m' + 1)|)) ≤
        Cm i * (cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2))
      (_ : ∀ i, (4 * Emax i ^ 2) * (β * Real.exp η * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * Δ i) / 2 ≤ Kwt i)
      (_ : Kw * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ V1)
      (_ : Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
        Real.sqrt ((4 * S.d * Real.exp (2 * η)) * (S.d * (N * Real.exp (2 * η)) * V1 ^ 2)) +
        Real.sqrt ((12 * Real.exp (2 * η)) * (N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2)) +
        (N * Ka * V1 ^ 2 + S.d * (N * Real.exp (2 * η)) * V1 ^ 2 +
          N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2) / 2 +
        4 * S.d * Real.exp (2 * η) + 12 * Real.exp (2 * η) ≤ Ksrc)
      (_ : Ksrc * (Cξ * Real.exp (2 * η) * (S.L : ℝ) ^ (-(2 * γ)) * A₀ /
        (2 * β * (1 - (S.L : ℝ) ^ (-(2 * γ))))) ≤ Kpair)
      (_ : ∀ i, 2 * (Ka + Δ i) * A₀ * Cξ * Real.exp (2 * η) * (S.L : ℝ) ^ (-(2 * γ)) /
            (β * (1 - (S.L : ℝ) ^ (-(2 * γ)))) + Kwt i +
          Amax i * (Kw * (Δ i * (2 * Emax i)) * (Real.sqrt (((4 * Emax i ^ 2) * Cb i) * (N * Cb i)) +
            Real.sqrt ((S.d * ((4 * Emax i ^ 2) * Cg i)) * (S.d * (N * Cg i))) +
            Real.sqrt (((4 * Emax i ^ 2 / |cs.muAct (m' + 1)|) * Cm i) * (N * Cm i))) +
            (Kw * (Δ i * (2 * Emax i))) ^ 2 / 2 * (N * Cb i + S.d * (N * Cg i) + N * Cm i)) ≤ Kcoef i)
      (_ : 0 ≤ Kpair) (_ : ∀ i, 0 ≤ Kcoef i) (_ : ∀ i, 0 ≤ Kswitch i)
      -- the switch (P7 (2.14)) to the window background at mass `0` of the datum `Du`
      (ϱB δu : ℝ) (δl V Kmass m : ι → ℝ)
      (_ : IsAdmissibleWeights (m' + 1) ak) (_ : cν ≤ 1)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : ∀ i, 0 < δl i) (_ : ∀ i, δl i ≤ bgC1 S.d S.L N)
      (_ : ∀ i, InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) (δl i)
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv))
      (_ : 0 < δu) (_ : δu ≤ bgC1 S.d S.L N) (_ : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
      (_ : ∀ i, bgK1 S.d S.L N * (δl i + δu) ≤ δs)
      (_ : ∀ i, bgK1 S.d S.L N * δl i ≤ min (deltaStar S.d S.L N) δm) (_ : ∀ i, 0 ≤ m i)
      (_ : ∀ i, m i * 2 ≤ min (deltaStar S.d S.L N) δm)
      (_ : ∀ i, cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 ≤ m i)
      (_ : ∀ i, Ks * ((δl i + δu) * Real.exp (-(gammaW S.d *
        (((t i : ℝ) * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
          (S.L : ℝ) ^ (jf i + 1))))) + Kw' * (m i * 2) ≤ V i)
      (_ : ∀ i, Amax i * (V i * (Real.sqrt (((4 * Emax i ^ 2) * Cb i) * (N * Cb i)) +
          Real.sqrt ((S.d * ((4 * Emax i ^ 2) * Cg i)) * (S.d * (N * Cg i))) +
          Real.sqrt (((4 * Emax i ^ 2 / |cs.muAct (m' + 1)|) * Cm i) * (N * Cm i))) +
          V i ^ 2 / 2 * (N * Cb i + S.d * (N * Cg i) + N * Cm i)) ≤ Kswitch i)
      (_ : ∀ i, 2 * (Cm i * Amax i) ≤ Kmass i),
      ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak 0 Du
            (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du)).re - C.re ∧
      ‖C‖ ≤ 9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (S.L : ℝ) ^ (-(2 * γ))) * ∑ i, (decomp i).total +
          ∑ i, (Kpair + Kcoef i + Kswitch i + Kmass i) * (decomp i).total


open Classical in
/-- The conclusion of `sum_mainActionLoc_eq_gen_of_flow_window_Du` for given constants `Kw δw Ks δs Kw' δm`: for every admissible choice of the caller's constants, the sum of the piece actions equals the real part of the window action at the datum `Du` up to a remainder bounded by the weights. -/
def WindowDuClaim (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjK : ∀ i, jf i + 1 ≤ K) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (decomp : ∀ i, StepDecomp (Xc i)) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1) ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (Kw δw Ks δs Kw' δm : ℝ) : Prop :=
  ∀
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
          ∑ i, (decomp i).total

/-- The landed claim is the per-piece claim at constant constants and radius `2`. -/
theorem WindowDuClaim.of_P (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjK : ∀ i, jf i + 1 ≤ K) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (decomp : ∀ i, StepDecomp (Xc i)) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1) ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (Kw δw Ks δs Kw' δm : ℝ) (hjf : ∀ i, jf i ≤ m')
    (hP : WindowDuClaimP g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du (fun _ => 2) Kw δw Ks δs Kw' δm) :
    WindowDuClaim g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du Kw δw Ks δs Kw' δm := by
  classical
  unfold WindowDuClaim
  intro ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch gf δ ξ
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50
    ϱB δl δu V Kmass m hak hcν1 s2 s3 s4 hconst s7 s8 s9 u1 u2 u3 t16 mA mB mC mD tV tK tKm
  have hL1 : (1 : ℝ) ≤ S.L := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne S.L)
  have hj1 : ∀ i, jf i + 1 ≤ m' + 1 := fun i => Nat.succ_le_succ (hjf i)
  have hE2 : ∀ i, ε₀ ^ 2 ≤ epsSeq S.L α α₀ (jf i + 1) ^ 2 := fun i =>
    (pow_le_pow_left₀ p25.le p26 2).trans (ActionConv.epsSeq_sq_ge S.L p5 p3 (hj1 i))
  have hδk : |δ (m' + 1)| ≤ Dδ := by rw [abs_of_pos (p13 _)]; exact p14 _
  have hCmB : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm := by assumption
  have hCm0 : 0 ≤ Cm := le_trans (by
    have : 0 ≤ Dδ := (abs_nonneg _).trans hδk
    have := p1
    positivity) hCmB
  have hCmb : ∀ i, β * Real.exp η * (((S.L : ℝ) ^ (jf i + 1)) ^ S.d * (|ν| * |δ (m' + 1)|)) ≤
      Cm * (cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2) := fun i => by
    rw [p8 (jf i + 1)]
    exact mass_budget_of_regime p1 (hj1 i) p25 (hE2 i) (p12 _).1 p24 hδk hCmB
  have hKwt : ∀ i, (4 * Emax ^ 2) * (β * Real.exp η * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * Δ) / 2 ≤ Kwt := fun i => by
    refine le_trans ?_ (by assumption : (4 * Emax ^ 2) * (β * Real.exp η * (S.L : ℝ) ^ ((S.d - 2) * (m' + 1)) * Δ) / 2 ≤ Kwt)
    have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (p21 0)
    have hpow : (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) ≤ (S.L : ℝ) ^ ((S.d - 2) * (m' + 1)) :=
      pow_le_pow_right₀ hL1 (Nat.mul_le_mul_left _ (hj1 i))
    have := p1
    gcongr
  obtain ⟨C, hC, hCb⟩ := hP ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair (fun _ => Δ) (fun _ => Kwt)
    (fun _ => Cb) (fun _ => Cg) (fun _ => Cm) (fun _ => Amax) (fun _ => Emax) (fun _ => ε₀)
    (fun _ => Kcoef) (fun _ => Kswitch) gf δ ξ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    (fun _ _ => p21 _) p22 p23 (fun _ => p25) hE2 (by assumption) (by assumption) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    (by assumption) (by assumption) (by assumption) (by assumption) (by assumption)
    (fun _ => by assumption) (fun _ => by assumption) (fun _ => hCm0) hCmb hKwt
    (by assumption) (by assumption) (by assumption) (fun _ => by assumption) (by assumption)
    (fun _ => by assumption) (fun _ => by assumption) ϱB δu (fun _ => δl) (fun _ => V)
    (fun _ => Kmass) (fun _ => m) hak hcν1 s2 s3 s4 hconst (fun _ => s7) (fun _ => s8) s9 u1 u2 u3
    (fun _ => t16) (fun _ => mA) (fun _ => mB) (fun _ => mC) mD (fun i => by simpa using tV i)
    (fun _ => tK) (fun _ => tKm)
  refine ⟨C, hC, hCb.trans (le_of_eq ?_)⟩
  rw [← Finset.mul_sum]
  ring

/-- **sum_mainActionLoc_eq_gen_of_flow_window_Du with the constants first**: the constants are produced before the window point and all the data and depend only on `(d, L, N)`.  The landed `sum_mainActionLoc_eq_gen_of_flow_window_Du` is this theorem at the data. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_Du_constsP (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Kw δw Ks δs Kw' δm : ℝ, 0 < Kw ∧ 0 < δw ∧ 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (_ : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (_ : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1))) (_ : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩) (hjK : ∀ i, jf i + 1 ≤ K) (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (_ : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (decomp : ∀ i, StepDecomp (Xc i)) (_ : ∀ i c, (decomp i).wt c = 1) (_ : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).blk (((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x) x ∧
        ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x ≤ jf i + 1) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0) (hμ : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0) (hB0 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muBg (jf i + 1))) (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1)
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
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)) {k0' k' m₁ N' : ℕ} {ϱ' : ℝ} {sf : Def7.SFData S.d S.L m₁ k' N' ϱ'} {hv' : EuclideanSpace ℝ (Fin N')} (_ : Def7.FieldClauses S k0' k' cs sf hv') (_ : m' + 1 ≤ k') (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ‖hv‖ = 1) (_ : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
        dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) (t : ι → ℕ) (_ : ∀ i, BallRadiusOK R m' (jf i) (t i)) (_ : ∀ i, 2 ≤ t i) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N) (_ : ∀ x i, Du.h x i = 0) (_ : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
        (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ (t i : ℝ) * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x)),
    WindowDuClaimP g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du t Kw δw Ks δs Kw' δm := by
  classical
  obtain ⟨Ks, δs, Kw', δm, hKs, hδs, hKw', hδm, hsw0⟩ := window_Du_hswitch_constsP S N hd3 hL3
  obtain ⟨Kw, δw, hKw, hδw, hmain0⟩ := sum_mainActionLoc_eq_gen_of_flow_of_read_constsP S N hd3 hL3
  refine ⟨Kw, δw, Ks, δs, Kw', δm, hKw, hδw, hKs, hδs, hKw', hδm, ?_⟩
  intro n _ R k0 K M _ H g cs m' Z hmK hW ι _ jf cf hjf hcf hinj hcov hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain k0' k' m₁ N' ϱ' sf hv' hF hk' ψ hunit hlift t hR ht2 Du hDuh hDuball
  have hsw := hsw0 g cs hmK hW jf cf hjf hcf hjK Xc hXc decomp hwt1 hcells ou xu hv ψ hunit hlift t hR ht2 Du hDuh hDuball
  have hread := window_hread_of_lift hmK hW jf cf hjf hcf hjK Xw hXw Xc hXc ou xu hv ψ hlift
  have hmain := hmain0 g cs hmK
    (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
    (windowOfHistory_parentRefines H Z g hmK hW) jf cf hjf hcf hinj hcov hjK (hW.k1_pos hmK) Xw hXw
    Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain
    (fun i => by have := (hjf i).2; rw [hF.muBg_eq _ (by omega), hF.muAct_eq _ (by omega)]) ψ hread
  unfold WindowDuClaimP
  intro ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair Δ Kwt Cb Cg Cm Amax Emax ε₀ Kcoef Kswitch gf δ ξ
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 pC0 p42 p43 p44 p45 p46 p47 p48 p49 p50
    ϱB δu δl V Kmass m hak hcν1 s2 s3 s4 hconst s7 s8 s9 u1 u2 u3 t16 mA mB mC mD tV tK tKm
  have hRb : (2 : ℝ) ≤ S.Rb := by
    have hb := H.F.RH.base
    have h0 : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
    linarith only [hb, h0]
  have hνk : 0 < cs.muAct (m' + 1) := by rw [p9]; exact mul_pos p2 (p13 _)
  have hνL : cs.muAct (m' + 1) * ((S.L : ℝ) ^ (m' + 1)) ^ 2 ≤ 1 := by
    rw [p9]; exact mass_le_one_of_flow p2 (p14 _) (Nat.cast_nonneg _) p22 hcν1 p23
  have s1 : BgHyp S.d S.L (m' + 1) (winSep g) ak (cs.muAct (m' + 1)) :=
    bgHyp_winSep_of_const g hd3 hL3 hRb (s2.trans s4) hak hνk.le hνL
  have hHw0 : BgHyp S.d S.L (m' + 1) (winSep g) ak 0 := BgHyp.of_mass_zero s1
  have hm2 := hmain ak (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du) β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair Δ Kwt Cb Cg Cm Amax Emax ε₀
    Kcoef Kswitch gf δ ξ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20
    p21 p22 p23 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 pC0 p42 p43
    p44 p45 p46 p47 p48 p49 p50
  obtain ⟨C, hC, hCb⟩ := hm2 (fun i => by
    have hdat' : (chain i).Dat () (m' + 1) = (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv) := by
      rw [hchain i]; rfl
    have hXi := p35 i
    rw [hdat'] at hXi
    have hAmax : β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) *
        epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax i := by
      rw [← p8 (jf i + 1)]; exact p18 i
    have hCmi := p42 i
    rw [p8 (jf i + 1)] at hCmi
    exact hsw i ak β ν η Ka (ε₀ i) α α₀ (Emax i) (Amax i) (Cb i) (Cg i) (Cm i) (V i) (Kswitch i) ϱB (δl i) δu (m i) gf δ p1 p3 p5 p8 p9
      p12 hAmax p19 (p25 i) (p26 i) (p27 i) (p29 i) (p31 i) (p32 i) hXi (p39 i) (p40 i) (p41 i) (pC0 i) hCmi hνk
      hHw0 s2 s3 s4 hconst (s7 i) (s8 i) (s9 i) u1 u2 u3 (t16 i) (mA i) (mB i) (mC i) (mD i) (tV i) (tK i))
  have hcm : ∀ i, ∀ c, β * gf (m' + 1) * ∑ _x ∈ ((decomp i).cube c).sites, |ν * δ (m' + 1)| ≤
      Cm i * (cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 * (decomp i).wt c) := fun i c => by
    have hCmi := p42 i
    rw [p8 (jf i + 1)] at hCmi
    have h := switch_mass_cube_budget (Xc i) (decomp i) (hwt1 i) (hcells i) p1 (p12 (m' + 1)).2 hCmi c
    rw [p8 (jf i + 1)]
    exact h
  obtain ⟨C', hC'1, hC'2⟩ := window_Du_finishP cs hmK hW jf cf hjf hjK hcov Xw hXw Xwin hXwin Xc hXc
    decomp hwt1 t ht2 hv hunit ψ Du hDuball ak β η α α₀ ν
    (9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
      (1 - (S.L : ℝ) ^ (-(2 * γ))) * ∑ i, (decomp i).total +
      ∑ i, (Kpair + Kcoef i + Kswitch i + 0) * (decomp i).total) Amax Cm Kmass gf δ p1 p8 p9 p12
    p18 pC0 hcm hHw0 u1 u2 u3 tKm hC hCb
  refine ⟨C', hC'1, hC'2.trans (le_of_eq ?_)⟩
  rw [add_assoc, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **sum_mainActionLoc_eq_gen_of_flow_window_Du with the constants first**: the constants are produced before the window point and all the data and depend only on `(d, L, N)`.  The landed `sum_mainActionLoc_eq_gen_of_flow_window_Du` is this theorem at the data. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_Du_consts (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Kw δw Ks δs Kw' δm : ℝ, 0 < Kw ∧ 0 < δw ∧ 0 < Ks ∧ 0 < δs ∧ 0 < Kw' ∧ 0 < δm ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (_ : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (_ : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1))) (_ : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩) (hjK : ∀ i, jf i + 1 ≤ K) (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))) (_ : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : S.k1 (m' + 1) ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
      c ∈ H.ancFin (j + 1) (m' + 1) Z ∧
        torusCast (piece_torus_eq g H.F.hnn hmK hj.2) x ∈ Xfine g (H.locRH (j + 1) c) j c.1) (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) (_ : ∀ i, (Xc i).sites = Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (decomp : ∀ i, StepDecomp (Xc i)) (_ : ∀ i c, (decomp i).wt c = 1) (_ : ∀ i c, ∃ x ∈ (Xc i).sites,
      ((decomp i).cube c).sites = ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).blk (((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x) x ∧
        ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))).layerIndex x ≤ jf i + 1) (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1)) (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i)) (hv : EuclideanSpace ℝ (Fin N)) (hβ : ∀ i m, jf i + 1 ≤ m → m ≤ m' + 1 → cs.beta m ≠ 0) (hμ : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → cs.muAct m ≠ 0) (hB0 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muBg (jf i + 1))) (hBn : ∀ i m, jf i + 2 ≤ m → m ≤ m' + 1 → BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1)
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
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)) {k0' k' m₁ N' : ℕ} {ϱ' : ℝ} {sf : Def7.SFData S.d S.L m₁ k' N' ϱ'} {hv' : EuclideanSpace ℝ (Fin N')} (_ : Def7.FieldClauses S k0' k' cs sf hv') (_ : m' + 1 ≤ k') (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ‖hv‖ = 1) (_ : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
        dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N) (_ : ∀ x i, Du.h x i = 0) (_ : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
        (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x)),
    WindowDuClaim g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du Kw δw Ks δs Kw' δm := by
  classical
  obtain ⟨Kw, δw, Ks, δs, Kw', δm, hKw, hδw, hKs, hδs, hKw', hδm, Hc⟩ :=
    sum_mainActionLoc_eq_gen_of_flow_window_Du_constsP S N hd3 hL3
  refine ⟨Kw, δw, Ks, δs, Kw', δm, hKw, hδw, hKs, hδs, hKw', hδm, ?_⟩
  intro n _ R k0 K M _ H g cs m' Z hmK hW ι _ jf cf hjf hcf hinj hcov hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain k0' k' m₁ N' ϱ' sf hv' hF hk' ψ hunit hlift Du hDuh hDuball
  exact WindowDuClaim.of_P g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du Kw δw Ks δs Kw' δm
    (fun i => (hjf i).2)
    (Hc g cs hmK hW jf cf hjf hcf hinj hcov hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv
      hβ hμ hB0 hBn hS chain hchain hF hk' ψ hunit hlift (fun _ => 2)
      (fun i => ballRadiusOK_two H g m' (jf i)) (fun _ => le_rfl) Du hDuh (by simpa using hDuball))

/-- **The window conversion at the reference datum `Du` of mass `0`**. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_Du (g : Geo S n R M) (cs : OpConsts) {m' : ℕ}
    {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L)
    (hW : H.RipeWindow (m' + 1) Z)
    {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
    (hcov : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
    (hjK : ∀ i, jf i + 1 ≤ K)
    (Xw : ι → Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
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
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hunit : ‖hv‖ = 1)
    (hlift : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
        dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          (if torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
              fineK1 g.M1 g.c (n (jf i + 1)) S.L (jf i) ((H.locRH (jf i + 1) (cf i)).step (jf i)).Omega
            then jf i + 1 else jf i) y) q : ℝ) : ℂ))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (hDuh : ∀ x i, Du.h x i = 0)
    (hDuball : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
        (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x)) :
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
  obtain ⟨Kw, δw, Ks, δs, Kw', δm, h0, h1, h2, h3, h4, h5, Hc⟩ := sum_mainActionLoc_eq_gen_of_flow_window_Du_consts S N hd3 hL3
  exact ⟨Kw, δw, Ks, δs, Kw', δm, h0, h1, h2, h3, h4, h5, Hc g cs hmK hW jf cf hjf hcf hinj hcov hjK Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hF hk' ψ hunit hlift Du hDuh hDuball⟩

end Du

end Balaban.LargeField
