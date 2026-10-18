/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffPhys
public import Balaban.LargeField.R.WindowOffDomainPhys

/-!
# The window conversion at the configuration, with the domain of the window datum

P7 pp. 500-501 ((2.11)-(2.16)): every background is evaluated at the same configuration `ψ̃`, which
lies in the space (1.32) [5] localized to `W_j ∩ U_{j+1}` for every piece `j`; the window background
is then defined (the space localized to `W_{k₁} ∩ U_k`) and the window conversion (2.16) holds.
`sum_mainActionLoc_eq_gen_of_flow_window_dom` is `sum_mainActionLoc_eq_gen_of_flow_window` with the
domain of the window datum proved from the domains of the pieces (`inDomainR_window_of_pieces`,
`δ_win = δ_l`): its only hypothesis on the window field `ψ` is `hlift`, that the datum of each piece
is the two-scale lift of `ψ` on the data sites of the piece (the restriction of the configuration
to the piece), and the external direction is a unit vector (`Def7.FieldClauses.h_unit`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

universe u

section Ball

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {H : RegionHistory S n R k0 K} {m' j : ℕ} {Z : H.Comp (m' + 1)} {g : Geo S n R M}

/-- The sites of the ball `2 L^j M` around the region of a piece are data sites of its local
generating set. -/
theorem ball_cast_mem_dataSites (hkK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z) (hj : j ≤ m')
    (hk1j : S.k1 (m' + 1) ≤ j) (hK : j + 1 ≤ K) {c : H.Comp (j + 1)}
    (hc : c ∈ H.ancFin (j + 1) (m' + 1) Z) {x y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))}
    (hx : torusCast (piece_torus_eq g H.F.hnn hkK hj) x ∈ Xfine g (H.locRH (j + 1) c) j c.1)
    (hxy : supDist y x ≤ 2 * (S.L ^ j * M)) :
    torusCast (piece_torus_eq g H.F.hnn hkK hj) y ∈
      dataSites (locGen g (H.locRH (j + 1) c) j c.1 (locComp_mem H hK c) hK) := by
  have hk1 := hW.k1_pos hkK
  obtain ⟨hyj, -⟩ := full_layerIndex_ball hkK hW hj hk1j hK hc hx hxy
  obtain ⟨hx1, hx2⟩ := (mem_Xfine_cast_iff g hkK hj c hK x).1 hx
  have hRm : 1 ≤ ⌊R m'⌋₊ := by
    refine Nat.le_floor ?_
    have := g.hRlow m'
    have hb : (4 * S.L + 20 : ℝ) ≤ S.Rb := H.F.RH.base
    push_cast; linarith
  have hy1 : y ∈ (windowOfHistory H Z g hkK hW).full.Ω 1 :=
    (windowOfHistory H Z g hkK hW).full.Ω_antitone le_rfl (by omega) (by omega) hyj
  have hyw := (windowGenSet_Ω_ball hkK hW hj hk1j hc hx1 hx2 (t := 2) (by omega) (by omega) hxy
    le_rfl (by omega)).2 hy1
  exact (mem_dataSites _).2 (Or.inl ((piece_window_layers_iff_ball_two hkK hW hj hk1j hK hc hx hxy
    le_rfl (by omega)).2 hyw))

/-- **The constant condition `2 L + 1 ≤ M`** follows from the radius condition
`(ϱ_B + 3d) L + 2 ≤ 2 c M₁` with `ϱ_B ≥ R₀(d, L) ≥ 0` and `d ≥ 3`. -/
theorem two_L_add_one_le_of_radius (g : Geo S n R M) (hd3 : 3 ≤ S.d) {ϱB : ℝ}
    (s2 : bgR0 S.d S.L ≤ ϱB) (hconst : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1)) :
    2 * S.L + 1 ≤ M := by
  have h0 : (0 : ℝ) ≤ ϱB := by
    refine le_trans ?_ s2
    unfold bgR0
    exact le_trans (by positivity) (le_max_left _ _)
  have hMr : (M : ℝ) = (g.c : ℝ) * g.M1 := by exact_mod_cast g.hM
  have hd : (3 : ℝ) ≤ S.d := by exact_mod_cast hd3
  have hL0 : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
  have h1 := mul_nonneg h0 hL0
  have h3 : (9 : ℝ) * S.L ≤ 3 * S.d * S.L := by nlinarith
  have h2 : (2 * S.L + 1 : ℝ) ≤ M := by nlinarith
  exact_mod_cast h2

end Ball

section Phys

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **The window conversion at the configuration** (P7 (2.11)-(2.16)): for the window of a ripe
component and a block field `ψ` of the window whose two-scale lifts are the data of the pieces
(`hlift`, on the data sites of each piece), with a unit external direction, the sum of the main
actions of the pieces is `Re(β_k A_{X_win}(ψ, φ_{k₁,k}))` up to `C`,
`‖C‖ ≤ (… + K_switch) Σ_i total_i`, the window background `φ_{k₁,k}` being `bgFieldC` of the window
generating set at the physical datum of `ψ`.  No ball premise and no domain premise of the window
datum remain (`δ_win = δ_l`). -/
theorem sum_mainActionLoc_eq_gen_of_flow_window_dom (g : Geo S n R M) (cs : OpConsts) {m' : ℕ}
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
            then jf i + 1 else jf i) y) q : ℝ) : ℂ)) :
      ∃ Kw δw Ks δs : ℝ, 0 < Kw ∧ 0 < δw ∧ 0 < Ks ∧ 0 < δs ∧ ∀
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
      -- the switch (P7 (2.14)): the window background against the local backgrounds
      (ϱB δl V : ℝ)
      (_ : IsAdmissibleWeights (m' + 1) ak) (_ : cν ≤ 1)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : 0 < δl) (_ : δl ≤ bgC1 S.d S.L N)
      (_ : ∀ i, InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv))
      (_ : bgK1 S.d S.L N * (δl + δl) ≤ δs)
      (_ : ∀ i, Ks * ((δl + δl) * Real.exp (-(gammaW S.d *
        ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
          (S.L : ℝ) ^ (jf i + 1))))) ≤ V)
      (_ : Amax * (V * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((S.d * ((4 * Emax ^ 2) * Cg)) * (S.d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |cs.muAct (m' + 1)|) * Cm) * (N * Cm))) +
          V ^ 2 / 2 * (N * Cb + S.d * (N * Cg) + N * Cm)) ≤ Kswitch),
      ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak (cs.muAct (m' + 1))
            (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q))
            (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N)
              (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)))).re - C.re ∧
      ‖C‖ ≤ (9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (S.L : ℝ) ^ (-(2 * γ))) + (Kpair + Kcoef + Kswitch + 0)) *
          ∑ i, (decomp i).total := by
  classical
  have hball : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z
        (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y ∈
        dataSites (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i)) := by
    rintro i y ⟨z, hz, hzy⟩
    set hT := piece_torus_eq g H.F.hnn hmK (hjf i).2 with hhT
    set e := Equiv.cast (congrArg (Torus S.d) hT) with he
    have hez : torusCast hT (e.symm z) = z := by
      rw [← torusCast_equivCast_apply]; exact e.apply_symm_apply z
    have hey : e.symm (torusCast hT y) = y := by
      rw [← torusCast_equivCast_apply]; exact e.symm_apply_apply y
    have hzX : torusCast hT (e.symm z) ∈ Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 := by
      rw [hez, ← hXc i]; exact hz
    have hd : Green.torusDist S.d (M * n (m' + 1) * S.L ^ (m' + 1)) y (e.symm z) ≤
        2 * ((S.L : ℝ) ^ jf i * M) := by
      have h1 := torusDist_equivCast_symm hT (torusCast hT y) z
      rw [hey] at h1
      rw [h1, Green.torusDist_comm_gen]; exact hzy
    have hsup : supDist y (e.symm z) ≤ 2 * (S.L ^ jf i * M) := by
      have := supDist_le_torusDist y (e.symm z)
      have h2 : (supDist y (e.symm z) : ℝ) ≤ ((2 * (S.L ^ jf i * M) : ℕ) : ℝ) := by
        push_cast; linarith
      exact_mod_cast h2
    exact ball_cast_mem_dataSites hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hzX hsup
  obtain ⟨Kw, δw, Ks, δs, hKw, hδw, hKs, hδs, hmain⟩ :=
    sum_mainActionLoc_eq_gen_of_flow_window g cs hmK hd3 hL3 hW jf cf hjf hcf hinj hcov hjK Xw hXw
      Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hF hk' ψ
      (fun i y hy => hlift i y (hball i y hy))
  refine ⟨Kw, δw, Ks, δs, hKw, hδw, hKs, hδs, ?_⟩
  intro ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch gf δ ξ
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50
    ϱB δl V hak hcν1 s2 s3 s4 hconst s7 s8 s9 t16 t17 t18
  -- the constant condition `2 L + 1 ≤ M` from the radius condition
  have hM : 2 * S.L + 1 ≤ M := two_L_add_one_le_of_radius g hd3 s2 hconst
  have s12 := inDomainR_window_of_pieces hmK hW hM jf cf hjf hcov hcf hjK ou xu hv hunit ψ hlift s7
    s9
  exact hmain ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch
    gf δ ξ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48
    p49 p50 ϱB δl δl V hak hcν1 s2 s3 s4 hconst s7 s8 s9 s7 s8 s12 t16 t17 t18

end Phys

end Balaban.LargeField
