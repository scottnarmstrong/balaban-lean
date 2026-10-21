/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowCompose
public import Balaban.LargeField.R.WindowConvR2
public import Balaban.LargeField.R.WindowConvPhysAssemblyParts
public import Balaban.LargeField.R.WindowConvPhysReadMain
public import Balaban.LargeField.R.CoeffResponseCubeDecomp
import Mathlib.Tactic.Linarith

/-!
# The physical window conversion at a given window field

P7 p. 501 (2.14)-(2.16): the background of every piece and the window background are functions of
the same configuration `ψ̃`.  `sum_mainActionLoc_eq_gen_of_flow_of_read` is the physical window
conversion of `sum_mainActionLoc_eq_gen_of_flow` with the window field `ψ` given (not chosen inside
the proof): its only property used is the read identity `hread` (the physical datum of `ψ` reads
the local datum of each piece on its region).  The landed `sum_mainActionLoc_eq_gen_of_flow` is
this theorem at the glued field of `exists_window_field_read_eq`.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow

universe u

section Phys

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **sum_mainActionLoc_eq_gen_of_flow_of_read with the constants first**: the constants are produced before the window point and all the data and depend only on `(d, L, N)`.  The landed `sum_mainActionLoc_eq_gen_of_flow_of_read` is this theorem at the data. -/
theorem sum_mainActionLoc_eq_gen_of_flow_of_read_constsP (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : Wp.Hyp) (href : ParentRefines (Wp.windowGenSet hWh) Wp.full) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (_ : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (_ : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1))) (_ : ∀ j (c : H.Comp (j + 1)), k1 ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩) (hjK : ∀ i, jf i + 1 ≤ K) (_ : 1 ≤ k1) (Xw : ι → Region (Wp.windowGenSet hWh)) (_ : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (Xwin : Region (Wp.windowGenSet hWh)) (_ : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
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
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)) (_ : ∀ i, cs.muBg (jf i + 1) = cs.muAct (jf i + 1)) (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ∀ (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν : ℝ) (i : ι),
      actionRegionC (Xc i) a ν
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw) =
        actionRegionC (Xw i) a ν (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw)
   
      (ak : ℕ → ℝ) (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ)
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
      (_ : ∀ i,
        ‖(betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
            actionRegionC (Xc i) ak (cs.muAct (m' + 1))
              (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
              (bgFieldC ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N)
                (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                  (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)) -
          (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
            actionRegionC (Xc i) ak (cs.muAct (m' + 1))
              (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
              (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
                (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
                (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw)‖ ≤
          Kswitch i * (decomp i).total),
      ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak (cs.muAct (m' + 1))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw).re - C.re ∧
      ‖C‖ ≤ 9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (S.L : ℝ) ^ (-(2 * γ))) * ∑ i, (decomp i).total +
          ∑ i, (Kpair + Kcoef i + Kswitch i + 0) * (decomp i).total := by
  classical
  obtain ⟨Kw, δw, hKw, hδw, H1⟩ := PieceWindowSetup.exists_window_conversion_of_flow_constsP.{0, u}
    (d := S.d) (L := S.L) (N := N) hd3 hL3
  refine ⟨Kw, δw, hKw, hδw, ?_⟩
  intro n _ R k0 K M _ H g cs k1 m' Z hmK ϱ Wp hWh href ι _ jf cf hjf hcf hinj hcov hjK hk1p Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hcoh ψ hread
  obtain rfl : chain = fun i => pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) MassBranch.complete (Xc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i)
      (fun _ _ => hS i) := funext hchain
  intro ak φw β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair Δ Kwt Cb Cg Cm Amax Emax ε₀ Kcoef Kswitch
    gf δ ξ hβp hνp hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq hAmax hKa hKaw hΔ
    hcν0 hcν hε₀ hE2 hN H0 H1' hsepO hsm hc1 hXi D0 D1 hsmall hSB hmB hEmax hCb hCg hCm0 hCm
    hKwt hV1 hK hKpair hKcoef hKp0 hKc0 hKs0 hsw
  have hQ : ∀ (x : Torus S.d (M * n (m' + 1) * S.L ^ (m' + 1))) (s s' : Σ j, H.Comp (j + 1)),
      s = s' → ((∃ hj : s.1 ≤ m', torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        Xfine g (H.locRH (s.1 + 1) s.2) s.1 s.2.1) ↔
      ∃ hj : s'.1 ≤ m', torusCast (piece_torus_eq g H.F.hnn hmK hj) x ∈
        Xfine g (H.locRH (s'.1 + 1) s'.2) s'.1 s'.2.1) := by
    intro x s s' h
    subst h
    exact Iff.rfl
  have hsites : Xwin.sites = Finset.univ.biUnion fun i => (Xw i).sites := by
    ext x
    rw [hXwin, Finset.mem_biUnion]
    constructor
    · rintro ⟨j, hj, c, hc, hx⟩
      obtain ⟨i, hi⟩ := hcov j c hj.1 hj.2 hc
      refine ⟨i, Finset.mem_univ _, (hXw i x).mpr ?_⟩
      have := (hQ x _ _ hi.symm).mp ⟨hj.2, hx⟩
      exact this.2
    · rintro ⟨i, -, hx⟩
      exact ⟨jf i, hjf i, cf i, hcf i, (hXw i x).mp hx⟩
  let W := pieceWindowSetupOfFamily g hmK Wp hWh jf cf hjf hcf hinj hjK Xw hXw
    Xwin hsites Xc decomp ak (cs.muAct (m' + 1))
    (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0)
    (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw MassBranch.complete
    (fun i => pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) MassBranch.complete (Xc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i)
      (fun _ _ => hS i))
  have hanT : ∀ (i : ι) (m : ℕ), jf i + 1 ≤ m → m ≤ m' + 1 →
      AnalyticOnNhd ℂ (fun u => (W.chain i).T u m) Set.univ := by
    intro i m _ _
    have : (fun u => (W.chain i).T u m) = fun _ => (W.chain i).T () m :=
      funext fun u => by rw [Subsingleton.elim u ()]
    rw [this]; exact analyticOnNhd_const
  have hanW : ∀ i, AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) *
      actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) Set.univ := by
    intro i
    have : (fun u => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) =
        fun _ => (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw ()) (W.φw ()) :=
      funext fun u => by rw [Subsingleton.elim u ()]
    rw [this]; exact analyticOnNhd_const
  have hA1 : ∀ i, (W.chain i).a (jf i + 1) = cs.aw := fun i => pieceChain_a_first (hβ := hβ i) (hμ := hμ i) (hB0 := hB0 i) (hBn := hBn i)
    (hS := fun _ _ => hS i) (br := MassBranch.complete) (by have := (hjf i).2; omega)
  have hjk : ∀ i, jf i + 1 ≤ m' + 1 := fun i => by have := (hjf i).2; omega
  obtain ⟨C, hC, -, hCb⟩ := H1 W cs
    (fun i _ => (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
      actionRegionC (Xc i) ak (cs.muAct (m' + 1))
        (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
          (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
        (transportField
          (Gl := locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
            (locComp_mem H (hjK i) (cf i)) (hjK i))
          (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
          (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw))
    β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair Δ Kwt Cb Cg Cm Amax Emax ε₀ Kcoef Kswitch (fun _ => 0) gf δ ξ
    hβp hνp hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq hAmax
    (fun i m _ _ => rfl) (fun i m _ _ => rfl) hA1
    (fun i u _ m _ _ => rfl)
    (fun i u _ m h1 h2 => pieceChain_φ (hβ := hβ i) (hμ := hμ i) (hB0 := hB0 i) (hBn := hBn i)
      (hS := fun _ _ => hS i) (br := MassBranch.complete) (hcoh i) h1 h2 u)
    hwt1 hcells hjk hKa hKaw hΔ hcν0 hcν hε₀ hE2 hN
    (fun i m h1 h2 => by
      rcases Nat.eq_or_lt_of_le h1 with e | hlt
      · subst e
        have h := hB0 i
        rw [hcoh i] at h
        show BgHyp S.d S.L (W.Kc i) (W.ϱc i) ((W.chain i).a (jf i + 1))
          ((W.chain i).ν (jf i + 1))
        rw [hA1 i]
        exact h
      · exact hBn i m (by omega) h2)
    H0 H1' (fun _ => hsepO) hsm hc1
    (fun i u _ m h1 h2 => hXi i m h1 h2) (fun i u _ => D0 i) (fun i u _ => D1 i)
    hsmall hSB hmB hEmax hCb hCg hCm0 hCm hKwt hV1 hK hKpair hKcoef hKp0 hKc0 hKs0 (fun _ => le_rfl)
    (fun i u _ => hsw i)
    (fun i u _ => by
      have h0 : (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) * actionRegionC (Xc i) ak
            (cs.muAct (m' + 1)) (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
              (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
            (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i)))
              (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
              (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw) -
          (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) * actionRegionC (Xw i) ak
            (cs.muAct (m' + 1)) (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw = 0 := by
        rw [hread φw ak (cs.muAct (m' + 1)) i, sub_self]
      exact (norm_eq_zero.2 h0).le.trans (by simp))
    (fun i m _ _ => hanT i m (by omega) (by omega)) hanW
  refine ⟨C (), ?_, ?_⟩
  · have h1 := hC () (Set.mem_univ _)
    have h2 := congrArg Complex.re h1
    rw [Complex.add_re, Complex.re_sum] at h2
    have h3 : ∀ i, ((W.chain i).T () (jf i + 1)).re = mainActionLoc g (H.locRH (jf i + 1) (cf i))
        (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
        (ou i) (xu i) hv := by
      intro i
      have hj1 : 1 ≤ jf i := le_trans hk1p (hjf i).1
      exact pieceChain_T g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
        (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i)) hj1 Set.univ
        (m' + 1) MassBranch.complete (Xc i) (hXc i) (fun _ => ou i) (fun _ => xu i)
        (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i) (hjk i) (Set.mem_univ ())
    simp only [h3] at h2
    exact (by simpa only [W, pieceWindowSetupOfFamily] using h2.symm.trans rfl : _) |> fun h => by linarith
  · simpa only [W, pieceWindowSetupOfFamily] using hCb () (Set.mem_univ _)

open Classical in
/-- **sum_mainActionLoc_eq_gen_of_flow_of_read with the constants first**: the constants are produced before the window point and all the data and depend only on `(d, L, N)`.  The landed `sum_mainActionLoc_eq_gen_of_flow_of_read` is this theorem at the data. -/
theorem sum_mainActionLoc_eq_gen_of_flow_of_read_consts (S : Setting) [NeZero S.L] (N : ℕ) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀ {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
    {H : RegionHistory S n R k0 K}
    (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ) (hWh : Wp.Hyp) (href : ParentRefines (Wp.windowGenSet hWh) Wp.full) {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1)) (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (_ : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z) (_ : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1))) (_ : ∀ j (c : H.Comp (j + 1)), k1 ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩) (hjK : ∀ i, jf i + 1 ≤ K) (_ : 1 ≤ k1) (Xw : ι → Region (Wp.windowGenSet hWh)) (_ : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1) (Xwin : Region (Wp.windowGenSet hWh)) (_ : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
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
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i) (fun _ _ => hS i)) (_ : ∀ i, cs.muBg (jf i + 1) = cs.muAct (jf i + 1)) (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N)) (_ : ∀ (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν : ℝ) (i : ι),
      actionRegionC (Xc i) a ν
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw) =
        actionRegionC (Xw i) a ν (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw)
   
      (ak : ℕ → ℝ) (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ)
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
      (_ : ∀ i,
        ‖(betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
            actionRegionC (Xc i) ak (cs.muAct (m' + 1))
              (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
              (bgFieldC ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N)
                (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                  (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)) -
          (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
            actionRegionC (Xc i) ak (cs.muAct (m' + 1))
              (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
              (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
                (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
                (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw)‖ ≤
          Kswitch * (decomp i).total),
      ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak (cs.muAct (m' + 1))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw).re - C.re ∧
      ‖C‖ ≤ (9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (S.L : ℝ) ^ (-(2 * γ))) + (Kpair + Kcoef + Kswitch + 0)) *
          ∑ i, (decomp i).total := by
  classical
  obtain ⟨Kw, δw, hKw, hδw, H1⟩ := sum_mainActionLoc_eq_gen_of_flow_of_read_constsP S N hd3 hL3
  refine ⟨Kw, δw, hKw, hδw, ?_⟩
  intro n _ R k0 K M _ H g cs k1 m' Z hmK ϱ Wp hWh href ι _ jf cf hjf hcf hinj hcov hjK hk1p Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hcoh ψ hread
  intro ak φw β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch
    gf δ ξ hβp hνp hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq hAmax hKa hKaw hΔ
    hcν0 hcν hreg hε₀ hε₀le hN H0 H1' hsepO hsm hc1 hXi D0 D1 hsmall hSB hmB hEmax hCb hCg hCm
    hKwt hV1 hK hKpair hKcoef hKp0 hKc0 hKs0 hsw
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
  have hE2' : ∀ i, ε₀ ^ 2 ≤ epsSeq S.L α α₀ (jf i + 1) ^ 2 := fun i =>
    (pow_le_pow_left₀ hε₀.le hε₀le 2).trans
      (epsSeq_sq_ge S.L hα hα₀ (by have := (hjf i).2; omega))
  have hCm0' : ∀ _ : ι, 0 ≤ Cm := fun _ => le_trans (by
    have : 0 ≤ Dδ := (hδp 0).le.trans (hδb 0)
    positivity) hCm
  have hCm' : ∀ i, β * Real.exp η * (((S.L : ℝ) ^ (jf i + 1)) ^ S.d * (|ν| * |δ (m' + 1)|)) ≤
      Cm * (cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2) := fun i => by
    rw [hβcs (jf i + 1)]
    exact mass_budget_of_regime hβp (by have := (hjf i).2; omega) hε₀ (hE2' i)
      (hgenv _).1 hreg (by rw [abs_of_pos (hδp _)]; exact hδb _) hCm
  have hKwt' : ∀ i, (4 * Emax ^ 2) * (β * Real.exp η * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * Δ) / 2 ≤
      Kwt := fun i =>
    kwt_of_top hβp hΔ0 (by positivity) (by have := (hjf i).2; omega) hKwt
  obtain ⟨C, hC, hCb'⟩ := @H1 n _ R k0 K M _ H g cs k1 m' Z hmK ϱ Wp hWh href ι _ jf cf hjf hcf hinj hcov
    hjK hk1p Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hcoh ψ hread
    ak φw β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Kpair (fun _ => Δ) (fun _ => Kwt) (fun _ => Cb)
    (fun _ => Cg) (fun _ => Cm) (fun _ => Amax) (fun _ => Emax) (fun _ => ε₀) (fun _ => Kcoef)
    (fun _ => Kswitch) gf δ ξ hβp hνp hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq
    hAmax hKa hKaw (fun _ => hΔ) hcν0 hcν (fun _ => hε₀) hE2' hN H0 H1' hsepO hsm hc1 hXi D0 D1
    hsmall hSB hmB hEmax (fun _ => hCb) (fun _ => hCg) hCm0' hCm' hKwt' hV1 hK hKpair
    (fun _ => hKcoef) hKp0 (fun _ => hKc0) (fun _ => hKs0) (fun i => hsw i)
  refine ⟨C, hC, hCb'.trans (le_of_eq ?_)⟩
  rw [← Finset.mul_sum]
  ring

/-- **The physical window conversion at a given window field** (P7 (2.10)-(2.16)): the conclusion
of `sum_mainActionLoc_eq_gen_of_flow` for any block field `ψ` of the window whose physical datum
reads the local data of the pieces on their regions (`hread`, the read identity of
`window_field_read_eq_of_agree`). -/
theorem sum_mainActionLoc_eq_gen_of_flow_of_read (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ}
    {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L)
    {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : Wp.Hyp) (href : ParentRefines (Wp.windowGenSet hWh) Wp.full)
    {ι : Type u} [Fintype ι] (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, k1 ≤ jf i ∧ jf i ≤ m') (hcf : ∀ i, cf i ∈ H.ancFin (jf i + 1) (m' + 1) Z)
    (hinj : Function.Injective fun i => (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)))
    (hcov : ∀ j (c : H.Comp (j + 1)), k1 ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
    (hjK : ∀ i, jf i + 1 ≤ K) (hk1p : 1 ≤ k1)
    (Xw : ι → Region (Wp.windowGenSet hWh))
    (hXw : ∀ i x, x ∈ (Xw i).sites ↔ torusCast (piece_torus_eq g H.F.hnn hmK (hjf i).2) x ∈
      Xfine g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1)
    (Xwin : Region (Wp.windowGenSet hWh))
    (hXwin : ∀ x, x ∈ Xwin.sites ↔ ∃ j, ∃ hj : k1 ≤ j ∧ j ≤ m', ∃ c : H.Comp (j + 1),
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
    (hcoh : ∀ i, cs.muBg (jf i + 1) = cs.muAct (jf i + 1))
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (hread : ∀ (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν : ℝ) (i : ι),
      actionRegionC (Xc i) a ν
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw) =
        actionRegionC (Xw i) a ν (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw) :
      ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀
      (ak : ℕ → ℝ) (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ)
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
      (_ : ∀ i,
        ‖(betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
            actionRegionC (Xc i) ak (cs.muAct (m' + 1))
              (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
              (bgFieldC ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ak (cs.muAct (m' + 1)) (bgC0 S.d S.L N)
                (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                  (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)) -
          (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
            actionRegionC (Xc i) ak (cs.muAct (m' + 1))
              (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
                (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv)
              (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
                (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
                (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw)‖ ≤
          Kswitch * (decomp i).total),
      ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak (cs.muAct (m' + 1))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)) φw).re - C.re ∧
      ‖C‖ ≤ (9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (S.L : ℝ) ^ (-(2 * γ))) + (Kpair + Kcoef + Kswitch + 0)) *
          ∑ i, (decomp i).total := by
  obtain ⟨Kw, δw, h0, h1, Hc⟩ := sum_mainActionLoc_eq_gen_of_flow_of_read_consts S N hd3 hL3
  exact ⟨Kw, δw, h0, h1, Hc g cs hmK Wp hWh href jf cf hjf hcf hinj hcov hjK hk1p Xw hXw Xwin hXwin Xc hXc decomp hwt1 hcells ou xu hv hβ hμ hB0 hBn hS chain hchain hcoh ψ hread⟩

end Phys

end Balaban.LargeField
