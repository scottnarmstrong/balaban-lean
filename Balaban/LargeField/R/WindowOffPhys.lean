/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowOffSwitch
public import Balaban.LargeField.R.WindowOffBall
public import Balaban.LargeField.R.WindowConvPhysSwitchLocBall
public import Balaban.LargeField.R.WindowConvPhysBallRadius
public import Balaban.LargeField.R.WindowConvPhysBallBg
import Mathlib.Tactic.Linarith

/-!
# The window conversion at the configuration (P7 (2.14): one `ψ̃` for all backgrounds)

P7 p. 501 (2.14) (with P6 p. 7 (2.16)): the background `φ_k(B_{j+1}(∂_{j+1}); ψ̃)` of every piece and
the window background `φ_{k₁,k} = φ_k(B_{k₁,k}; ψ̃)` are evaluated at the *same* configuration `ψ̃`,
so the configuration in the difference `δφ_k(∂_{j+1})` vanishes where the generating sets agree.
`sum_mainActionLoc_eq_gen_of_flow_window` is the physical window conversion for the window of a
ripe component (`windowOfHistory`), at a given block field `ψ` of the window, under the hypothesis
`hlift` that the datum of each piece is, on the ball of radius `2 L^j M` around its region, the
two-scale lift `lift_{j,j+1}(ψ_j, ψ_{j+1})` of `ψ` (Definition II.2.1 (b); P5 (2.11)-(2.12)).
Compared with `sum_mainActionLoc_eq_gen_of_flow_ballAgree`:

* the window field is not the glue of the piece data (default `0` off the piece regions) but `ψ`;
* the read identity follows from `hlift` on the piece regions (`window_field_read_eq_of_agree`
  with `full_layerIndex_ball`);
* the ball premises are proved with `rad_i = 2 L^{j_i} M`: equal layers
  (`piece_window_layers_switch`), equal data (`δ_d = 0`, `piece_window_Ψ_eq_of_lift`), equal `h̃`
  (`bgData_h_eq_of_Ω_one`);
* `BgHyp` of the window generating set comes from `bgHyp_winSep_of_const` (admissible `ak`,
  `c_ν ≤ 1`), the radius from the constant condition `(ϱ_B + 3d) L + 2 ≤ 2 c M₁`
  (`ball_radius_of_const`).

The domain `InDomainR` of the window datum (the source's "ψ in the space (1.32) [5] with
`X = W_{k₁} ∩ U_k`", P7 p. 501 after (2.14)) stays a premise.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

universe u

section Phys

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **The window conversion at the configuration** (P7 (2.14)-(2.16)): for the window of a ripe
component and a block field `ψ` of the window whose two-scale lifts are the data of the pieces on
the balls `B(X_i, 2 L^{j_i} M)` (`hlift`), the sum of the main actions of the pieces is
`Re(β_k A_{X_win}(ψ, φ_{k₁,k}))` up to `C` with `‖C‖ ≤ (… + K_switch) Σ_i total_i`, the window
background `φ_{k₁,k}` being `bgFieldC` of the window generating set at the physical datum of `ψ`.
No ball premise remains; the domain of the window datum is a premise. -/
theorem sum_mainActionLoc_eq_gen_of_flow_window (g : Geo S n R M) (cs : OpConsts) {m' : ℕ}
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
    (hlift : ∀ i (y : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))),
      (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z
        (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) y) ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
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
      (ϱB δl δwin V : ℝ)
      (_ : IsAdmissibleWeights (m' + 1) ak) (_ : cν ≤ 1)
      (_ : bgR0 S.d S.L ≤ ϱB) (_ : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
      (_ : ϱB ≤ minSep S.L g.M1)
      (_ : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
      (_ : 0 < δl) (_ : δl ≤ bgC1 S.d S.L N)
      (_ : ∀ i, InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i) (ou i) (xu i) hv))
      (_ : 0 < δwin) (_ : δwin ≤ bgC1 S.d S.L N)
      (_ : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) (cs.muAct (m' + 1)) δwin (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)))
      (_ : bgK1 S.d S.L N * (δl + δwin) ≤ δs)
      (_ : ∀ i, Ks * ((δl + δwin) * Real.exp (-(gammaW S.d *
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
  have hk1p : 1 ≤ S.k1 (m' + 1) := hW.k1_pos hmK
  have hRb : (2 : ℝ) ≤ S.Rb := by
    have := H.F.RH.base
    have : (0 : ℝ) ≤ S.L := Nat.cast_nonneg _
    linarith
  -- the read identity from the lift on the piece regions
  have hψ : ∀ i x, x ∈ (Xw i).sites →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ (torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x) =
        fun q => ((ψ (blockOf S.d S.L (M * n (m' + 1)) (m' + 1)
          ((windowOfHistory H Z g hmK hW).full.layerIndex x) x) q : ℝ) : ℂ) := by
    intro i x hx
    have hxX := (hXw i x).1 hx
    obtain ⟨-, hlay⟩ := full_layerIndex_ball hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hxX
      (y := x) (by rw [supDist_self]; exact Nat.zero_le _)
    rw [hlay]
    refine hlift i x ⟨_, by rw [hXc i]; exact hxX, ?_⟩
    rw [Green.torusDist_self_eq_zero]
    positivity
  have hread := window_field_read_eq_of_agree g hmK H.F.ok.two_le_L (fun j _ _ => g.hRlow j) hk1p
    (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
    (windowOfHistory_parentRefines H Z g hmK hW) (fun _ => rfl) rfl rfl jf cf hjf hcf hjK Xw hXw Xc
    hXc ou xu hv ψ hψ
  obtain ⟨Kw, δw, Ks, δs, hKw, hδw, hKs, hδs, hmain⟩ :=
    sum_mainActionLoc_eq_gen_of_flow_ballAgree_of_read g cs hmK hd3 hL3
      (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
      (windowOfHistory_parentRefines H Z g hmK hW) jf cf hjf hcf hinj hcov hjK hk1p Xw hXw Xwin
      hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hF hk' ψ hread
  refine ⟨Kw, δw, Ks, δs, hKw, hδw, hKs, hδs, ?_⟩
  intro ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch gf δ ξ
    p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24 p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48 p49 p50
    ϱB δl δwin V hak hcν1 s2 s3 s4 hconst s7 s8 s9 s10 s11 s12 t16 t17 t18
  -- `BgHyp` of the window generating set
  have hνk : 0 < cs.muAct (m' + 1) := by rw [p9]; exact mul_pos p2 (p13 _)
  have hνL : cs.muAct (m' + 1) * ((S.L : ℝ) ^ (m' + 1)) ^ 2 ≤ 1 := by
    rw [p9]; exact mass_le_one_of_flow p2 (p14 _) (Nat.cast_nonneg _) p22 hcν1 p23
  have s1 : BgHyp S.d S.L (m' + 1) (winSep g) ak (cs.muAct (m' + 1)) :=
    bgHyp_winSep_of_const g hd3 hL3 hRb (s2.trans s4) hak hνk.le hνL
  -- equal layers on the balls
  have s6 : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
      (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      ∀ q, 1 ≤ q → q ≤ jf i + 1 + 1 →
        (x ∈ (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
          (hjK i)).Ω q ↔ (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK
            (hjf i).2))).symm x ∈ ((windowOfHistory H Z g hmK hW).windowGenSet
              (windowOfHistory_hyp hmK hW)).Ω q) :=
    fun i x hx q hq1 hq2 => piece_window_layers_switch hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i)
      (Xc i).sites (fun z hz => by rw [hXc i] at hz; exact hz) x hx q hq1 hq2
  -- equal data on the balls (`δ_d = 0`)
  have hdat : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
      (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).Ψ x =
      (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
        (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ
        ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) := by
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
    have hl := hlift i (e.symm x) ⟨z, hz, by rw [hex]; exact hzx⟩
    have key := piece_window_Ψ_eq_of_lift hmK hW (hjf i).2 (hjf i).1 (hjK i) (hcf i) hzX hsup ψ
      (fun q => hv q) _ hl
    rw [hex] at key
    exact key
  have s14 : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
      (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      vn (fun j => (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv).Ψ x j -
        (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
          (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ
          ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) j)
        ≤ 0 := by
    intro i x hx
    rw [hdat i x hx]
    have h0 : (fun j => (physicalWindowData (windowOfHistory H Z g hmK hW)
        (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ
        (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK
          (hjf i).2))).symm x) j - (physicalWindowData (windowOfHistory H Z g hmK hW)
        (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ
        (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK
          (hjf i).2))).symm x) j) = (0 : Fin N → ℂ) := funext fun _ => sub_self _
    rw [h0, vn_zero]
  -- equal external fields on the balls
  have s15 : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d
      (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
        (hjK i) (ou i) (xu i) hv).h x =
      (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW)
        (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h
        ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) := by
    intro i x hx
    refine bgData_h_eq_of_Ω_one _ _ (fun q => (hv q : ℂ)) (fun y hy => ?_) (fun y hy => ?_)
      (s6 i x hx 1 le_rfl (by omega))
    · unfold locData
      rw [liftMixed_h _ _ _ _ _ _ hy]
    · funext q
      rw [physicalWindowData_h _ _ _ _ _ hy q]
  exact hmain ak β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch
    gf δ ξ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 p16 p17 p18 p19 p20 p21 p22 p23 p24
    p25 p26 p27 p28 p29 p30 p31 p32 p33 p34 p35 p36 p37 p38 p39 p40 p41 p42 p43 p44 p45 p46 p47 p48
    p49 p50 ϱB δl δwin 0 V (fun i => 2 * ((S.L : ℝ) ^ jf i * M)) s1 s2 s3 s4
    (fun i => ball_radius_of_const g ϱB hconst (jf i)) s6 s7 s8 s9 s10 s11 s12 le_rfl s14 s15
    (by rw [add_zero]; exact t16) (fun i => by rw [zero_add]; exact t17 i) t18

end Phys

end Balaban.LargeField
