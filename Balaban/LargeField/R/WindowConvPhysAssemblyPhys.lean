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
# The physical window conversion (P7 (2.10)-(2.16); P6 (2.31))

`sum_mainActionLoc_eq_gen_of_flow`: the sum of the main actions of the pieces of the window is
`Re (β_k A*_k(X_win)) - Re C` with `|C|` bounded by the constant of
`window_conversion_pieces_of_rg_source`, for the pieces `pieceChain` (complete mass branch) at the
physical target `β_k = betaCanon (cs.beta (m'+1)) (m'+1) 0`, `ν_k = cs.muAct (m'+1)`, and the
common window field `ψ` of `exists_window_field_hread_zero`.  The source estimate, the pair
estimate, the coefficient comparison and the read comparison are proved; the first-scale
background is `bgFieldC` by `pieceChain_φ` under the coherence `cs.muBg (j+1) = cs.muAct (j+1)`.
The comparison `hswitch` of the local reference background with the field transported from the
window background remains a premise.
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
theorem sum_mainActionLoc_eq_gen_of_flow (g : Geo S n R M) (cs : OpConsts) {k1 m' : ℕ}
    {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K) (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L)
    (hL : 2 ≤ S.L) (hR : ∀ i, 1 ≤ i → i < m' + 1 → S.Rb ≤ R i)
    {ϱ : ℝ} (Wp : WindowPieces S.d S.L (M * n (m' + 1)) (m' + 1) ϱ)
    (hWh : Wp.Hyp) (href : ParentRefines (Wp.windowGenSet hWh) Wp.full)
    (hWfull : ∀ q, Wp.full.Ω q = (H.locGen Z M hmK hL hR).Ω q)
    (hWZ : Wp.Z = H.locFineFin Z (m' + 1)) (hWZk1 : Wp.Zk1 = H.locFineFin Z k1)
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
    (hcoh : ∀ i, cs.muBg (jf i + 1) = cs.muAct (jf i + 1)) :
    ∃ ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N),
      (∀ (φw : (Wp.windowGenSet hWh).Ω 1 × Fin N → ℂ) (a : ℕ → ℝ) (ν β' : ℝ) (i : ι),
        (β' : ℂ) * actionRegionC (Xc i) a ν
          (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i))
            (hjK i) (ou i) (xu i) hv)
          (transportField (Gl := (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
            (Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2)))
            (physicalWindowData Wp hWh href ψ (fun q => hv q)).Ψ φw) -
        (β' : ℂ) * actionRegionC (Xw i) a ν (physicalWindowData Wp hWh href ψ (fun q => hv q))
          φw = 0) ∧
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
  classical
  obtain rfl : chain = fun i => pieceChain g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1
      (locComp_mem H (hjK i) (cf i)) (hjK i) cs Set.univ (m' + 1) MassBranch.complete (Xc i)
      (fun _ => ou i) (fun _ => xu i) (fun _ => hv) (hβ i) (hμ i) (hB0 i) (hBn i)
      (fun _ _ => hS i) := funext hchain
  obtain ⟨Kw, δw, hKw, hδw, H1⟩ := PieceWindowSetup.exists_window_conversion_of_flow.{0, u}
    (d := S.d) (L := S.L) (N₀ := M * n (m' + 1)) (K := m' + 1) (N := N) (U := Unit)
    (S := Set.univ) (ι := ι) (sc := jf) (k1 := k1) (k := m' + 1) hd3 hL3
  obtain ⟨ψ, hψ⟩ := exists_window_field_hread_zero g hmK hL hR hk1p Wp hWh href hWfull hWZ hWZk1
    jf cf hjf hcf hinj hjK Xw hXw Xc hXc ou xu hv
  refine ⟨ψ, hψ, Kw, δw, hKw, hδw, ?_⟩
  intro ak φw β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch
    gf δ ξ hβp hνp hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq hAmax hKa hKaw hΔ
    hcν0 hcν hreg hε₀ hε₀le hN H0 H1' hsepO hsm hc1 hXi D0 D1 hsmall hSB hmB hEmax hCb hCg hCm
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
    β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch 0 gf δ ξ
    hβp hνp hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq hAmax
    (fun i m _ _ => rfl) (fun i m _ _ => rfl) hA1
    (fun i u _ m _ _ => rfl)
    (fun i u _ m h1 h2 => pieceChain_φ (hβ := hβ i) (hμ := hμ i) (hB0 := hB0 i) (hBn := hBn i)
      (hS := fun _ _ => hS i) (br := MassBranch.complete) (hcoh i) h1 h2 u)
    hwt1 hcells hjk hKa hKaw hΔ hcν0 hcν hreg hε₀ hε₀le hN
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
    hsmall hSB hmB hEmax hCb hCg hCm hKwt hV1 hK hKpair hKcoef hKp0 hKc0 hKs0 le_rfl
    (fun i u _ => hsw i)
    (fun i u _ => by
      have h0 := hψ φw ak (cs.muAct (m' + 1)) (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0) i
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

end Phys

end Balaban.LargeField
