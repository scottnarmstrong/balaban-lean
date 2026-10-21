/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuPt
public import Balaban.LargeField.R.WindowDuFlowEst
public import Balaban.LargeField.R.WindowDuBranch
public import Balaban.Green.FinalConstsClose

/-!
# The constants of the window conversion at the datum `Du` (blocker 4)

`WindowDuClaim` (`WindowDuConv`) holds the conclusion of the window conversion for caller constants
`V1, Ksrc, Kwt, Cb, Cg, Cm, Kpair, Kcoef, V, Kswitch, Kmass, A₀, Amax, Emax, ε₀` satisfying closure inequalities.
Here these constants are chosen: `winKsrc`, `winKb` are explicit functions of the flow data (`WinConsts`
below), and `WindowDuClaim.exists_bound` gives, for every `Kconv ≥ 9 K_src C_ξ α₀² e^η` and
`Kbg ≥ K_b`, the sum identity with the remainder bound
`‖C‖ ≤ (9 e^{2η} K_conv / (1 - L^{-2γ}) + K_bg) · ∑ total`.

The remaining premises are the flow relations (P4), the bounds of the weights, the size of the mass
(`ν L^{2(m'+1)} D_δ ≤ c_ν² ≤ 1`), the geometry of the separations, the domain facts of the piece data
(three `XiCOneReal` families, `InDomainR … δ_l`, the datum `Du` in `InDomainR … 0 δ_u`) and the
smallness conditions (`WindowSideConds`).  The constants `A₀`, `Amax`, `Emax = 3 α₀`, `ε₀` are derived
from the flow (`beta_epsSq_decay_le`).
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace Balaban.LargeField

open Balaban Balaban.Multiscale Balaban.Fluctuation Balaban.Background RegionHistory
  Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow Balaban.Localization

universe u

section Consts

/-- `ε₀ = α₀ (L^{-α})^{m'+1}`. -/
noncomputable def winEps0 (L m' : ℕ) (α α₀ : ℝ) : ℝ := α₀ * ((L : ℝ) ^ (-α)) ^ (m' + 1)

/-- `A₀ = 9 β e^η α₀²`: `β_j ε_j² (L^{-2γ})^j ≤ A₀`. -/
noncomputable def winA0 (β η α₀ : ℝ) : ℝ := 9 * β * Real.exp η * α₀ ^ 2

/-- `A_max = A₀ (L^{2γ})^{m'+1}`: `β_j ε_j² ≤ A_max` for `j ≤ m' + 1`. -/
noncomputable def winAmax (L m' : ℕ) (β η α₀ γ : ℝ) : ℝ := winA0 β η α₀ * ((L : ℝ) ^ (2 * γ)) ^ (m' + 1)

/-- `C_b`. -/
noncomputable def winCb (η Ka ε₀ : ℝ) : ℝ := Real.exp (2 * η) * Ka / ε₀ ^ 2

/-- `C_g`. -/
noncomputable def winCg (η ε₀ : ℝ) : ℝ := Real.exp (2 * η) / ε₀ ^ 2

/-- `C_m`. -/
noncomputable def winCm (η Dδ β ε₀ : ℝ) : ℝ := Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2)

/-- `K_wt`. -/
noncomputable def winKwt (d L m' : ℕ) (η β Δ Emax : ℝ) : ℝ :=
  (4 * Emax ^ 2) * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * (m' + 1)) * Δ) / 2

/-- `V₁`. -/
noncomputable def winV1 (Kw η Ka cν : ℝ) : ℝ := Kw * (4 * Real.exp (2 * η) * Ka + 24 * cν)

/-- `K_src`. -/
noncomputable def winKsrc (d N : ℕ) (η Ka cν V1 : ℝ) : ℝ :=
  Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
    Real.sqrt ((4 * d * Real.exp (2 * η)) * (d * (N * Real.exp (2 * η)) * V1 ^ 2)) +
    Real.sqrt ((12 * Real.exp (2 * η)) * (N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2)) +
    (N * Ka * V1 ^ 2 + d * (N * Real.exp (2 * η)) * V1 ^ 2 +
      N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2) / 2 +
    4 * d * Real.exp (2 * η) + 12 * Real.exp (2 * η)

/-- `K_pair`. -/
noncomputable def winKpair (L : ℕ) (Ksrc Cξ η γ A₀ β : ℝ) : ℝ :=
  Ksrc * (Cξ * Real.exp (2 * η) * (L : ℝ) ^ (-(2 * γ)) * A₀ / (2 * β * (1 - (L : ℝ) ^ (-(2 * γ)))))

/-- The three square roots of the switch and coefficient comparisons. -/
noncomputable def winSqS (d N : ℕ) (E μ Cb Cg Cm : ℝ) : ℝ :=
  Real.sqrt (((4 * E ^ 2) * Cb) * (N * Cb)) + Real.sqrt ((d * ((4 * E ^ 2) * Cg)) * (d * (N * Cg))) +
    Real.sqrt (((4 * E ^ 2 / |μ|) * Cm) * (N * Cm))

/-- The quadratic budget of the switch and coefficient comparisons. -/
noncomputable def winSqQ (d N : ℕ) (Cb Cg Cm : ℝ) : ℝ := N * Cb + d * (N * Cg) + N * Cm

/-- `K_coef`. -/
noncomputable def winKcoef (d L N m' : ℕ) (Kw η Ka Δ E β Cξ γ A₀ Amax Cb Cg Cm μ : ℝ) : ℝ :=
  2 * (Ka + Δ) * A₀ * Cξ * Real.exp (2 * η) * (L : ℝ) ^ (-(2 * γ)) /
      (β * (1 - (L : ℝ) ^ (-(2 * γ)))) + winKwt d L m' η β Δ E +
    Amax * (Kw * (Δ * (2 * E)) * winSqS d N E μ Cb Cg Cm +
      (Kw * (Δ * (2 * E))) ^ 2 / 2 * winSqQ d N Cb Cg Cm)

/-- `V`: the bound of the switch radius. -/
noncomputable def winV (Ks Kw' δl δu m : ℝ) : ℝ := Ks * (δl + δu) + Kw' * (m * 2)

/-- `K_switch`. -/
noncomputable def winKswitch (d N : ℕ) (Amax V E μ Cb Cg Cm : ℝ) : ℝ :=
  Amax * (V * winSqS d N E μ Cb Cg Cm + V ^ 2 / 2 * winSqQ d N Cb Cg Cm)

/-- `K_mass`. -/
noncomputable def winKmass (Cm Amax : ℝ) : ℝ := 2 * (Cm * Amax)

/-- **The constant `K_b = K_pair + K_coef + K_switch + K_mass` of the window conversion.** -/
noncomputable def winKb (d L N m' : ℕ) (Kw Ks Kw' η Ka cν Dδ β α α₀ γ Cξ Δ δl δu m μ : ℝ) : ℝ :=
  winKpair L (winKsrc d N η Ka cν (winV1 Kw η Ka cν)) Cξ η γ (winA0 β η α₀) β +
    winKcoef d L N m' Kw η Ka Δ (3 * α₀) β Cξ γ (winA0 β η α₀) (winAmax L m' β η α₀ γ)
      (winCb η Ka (winEps0 L m' α α₀)) (winCg η (winEps0 L m' α α₀))
      (winCm η Dδ β (winEps0 L m' α α₀)) μ +
    winKswitch d N (winAmax L m' β η α₀ γ) (winV Ks Kw' δl δu m) (3 * α₀) μ
      (winCb η Ka (winEps0 L m' α α₀)) (winCg η (winEps0 L m' α α₀))
      (winCm η Dδ β (winEps0 L m' α α₀)) +
    winKmass (winCm η Dδ β (winEps0 L m' α α₀)) (winAmax L m' β η α₀ γ)

end Consts

section Du

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 : ℕ} {M K : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K}

open Classical in
/-- **The window conversion at `Du` with explicit constants.** For `K_conv ≥ 9 K_src C_ξ α₀² e^η` and `K_bg ≥ K_b` the
sum of the piece actions is the real part of the window action at `Du` up to a remainder of norm at most
`(9 e^{2η} K_conv / (1 - L^{-2γ}) + K_bg) ∑ total`. -/
theorem WindowDuClaim.exists_bound (hd3 : 3 ≤ S.d) (hL3 : 3 ≤ S.L)
    (g : Geo S n R M) (cs : OpConsts) {m' : ℕ} {Z : H.Comp (m' + 1)} (hmK : m' + 1 ≤ K)
    (hW : H.RipeWindow (m' + 1) Z) {ι : Type u} [Fintype ι] (jf : ι → ℕ)
    (cf : ∀ i, H.Comp (jf i + 1)) (hjK : ∀ i, jf i + 1 ≤ K)
    (Xwin : Region ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)))
    (Xc : ∀ i, Region (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
    (decomp : ∀ i, StepDecomp (Xc i))
    (ou : ∀ i, OutT N R (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i + 1))
    (xu : ∀ i, NewCfg N (locHist (H.locRH (jf i + 1) (cf i)) M K (jf i + 1) (cf i).1) (jf i))
    (hv : EuclideanSpace ℝ (Fin N))
    (chain : ∀ i, ConvChain (Set.univ : Set Unit) (jf i) (m' + 1)
      ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)))
      (Xc i) MassBranch.complete N)
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    {Kw δw Ks δs Kw' δm : ℝ} (hKw : 0 ≤ Kw) (hKs : 0 ≤ Ks) (hKw' : 0 ≤ Kw')
    (hcl : WindowDuClaim g cs hmK hW jf cf hjK Xwin Xc decomp ou xu hv chain Du Kw δw Ks δs Kw' δm)
    (hjf : ∀ i, jf i ≤ m')
    (ak : ℕ → ℝ) (β ν η Ka cν Dδ Cξ α α₀ γ Δ : ℝ) (gf δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    (ϱB δl δu m : ℝ)
    (h4 : 0 < β)
    (h5 : 0 < ν)
    (h6 : 0 < α₀)
    (h7 : 0 ≤ Cξ)
    (h8 : 0 ≤ α)
    (h9 : 0 < γ)
    (h10 : (S.d : ℝ) - 2 - 2 * α = 2 * γ)
    (h11 : ∀ m, cs.beta m = β * (S.L : ℝ) ^ ((S.d - 2) * m) * gf m)
    (h12 : ∀ m, cs.muAct m = ν * δ m)
    (h13 : ∀ m, gf m = gf (m + 1) * (1 + ξ m 2))
    (h14 : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
    (h15 : ∀ m, Real.exp (-η) ≤ gf m ∧ gf m ≤ Real.exp η)
    (h16 : ∀ m, 0 < δ m)
    (h17 : ∀ m, δ m ≤ Dδ)
    (h18 : ∀ m c, |ξ m c| ≤ Cξ * β⁻¹ * ((S.L : ℝ) ^ (-(2 * γ))) ^ (m + 1))
    (h19 : Cξ * Real.exp (2 * η) * (S.L : ℝ) ^ (-(2 * γ)) / (β * (1 - (S.L : ℝ) ^ (-(2 * γ)))) ≤ 1 / 2)
    (h22 : ∀ ℓ, |ak ℓ| ≤ Ka)
    (h23 : ∀ ℓ, |cs.aw ℓ| ≤ Ka)
    (h24 : ∀ ℓ, |cs.aw ℓ - ak ℓ| ≤ Δ)
    (h25 : 0 ≤ cν)
    (h26 : ν * (S.L : ℝ) ^ (2 * (m' + 1)) * Dδ ≤ cν ^ 2)
    (h27 : β * |ν| * (S.L : ℝ) ^ ((m' + 1) * S.d) ≤ 1)
    (h30 : ∀ i, ∃ N₁ m₁ : ℕ, g.M1 * (g.c * n (jf i + 1)) = N₁ * S.L ^ m₁)
    (h31 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) cs.aw (cs.muAct (m' + 1)))
    (h32 : ∀ i, BgHyp S.d S.L (jf i + 1) (minSep S.L g.M1) ak (cs.muAct (m' + 1)))
    (h33 : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (minSep S.L g.M1 - 1))
    (h34 : ∀ i, (4 * S.d + 6) * ((2 * S.d + 1) * epsSeq S.L α α₀ (jf i + 1)) ≤ 1)
    (h35 : ∀ i, xiC1 S.d * epsSeq S.L α α₀ (jf i + 1) ≤ bgC1 S.d S.L N)
    (h36 : ∀ i, ∀ m, jf i + 1 ≤ m → m ≤ m' + 1 → XiCOneReal ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ((chain i).a m) ((chain i).ν m) (epsSeq S.L α α₀ (jf i + 1)) ((chain i).Dat () m))
    (h37 : ∀ i, XiCOneReal ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) cs.aw (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1)) ((chain i).Dat () (m' + 1)))
    (h38 : ∀ i, XiCOneReal ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i))) ak (cs.muAct (m' + 1)) (epsSeq S.L α α₀ (jf i + 1)) ((chain i).Dat () (m' + 1)))
    (h39 : ∀ i, bgK1 S.d S.L N * (xiC1 S.d * epsSeq S.L α α₀ (jf i + 1)) ≤ min (deltaStar S.d S.L N) δw)
    (h40 : ∀ i, epsSeq S.L α α₀ (jf i + 1) * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ min (deltaStar S.d S.L N) δw)
    (h41 : ∀ i, Δ * (2 * epsSeq S.L α α₀ (jf i + 1)) ≤ min (deltaStar S.d S.L N) δw)
    (h56 : IsAdmissibleWeights (m' + 1) ak)
    (h57 : cν ≤ 1)
    (h58 : bgR0 S.d S.L ≤ ϱB)
    (h59 : 2 * S.d * Real.log S.L ≤ agmonRate S.d / 16 * (ϱB - 1))
    (h60 : ϱB ≤ minSep S.L g.M1)
    (h61 : (ϱB + 3 * S.d) * (S.L : ℝ) + 2 ≤ 2 * ((g.c : ℝ) * g.M1))
    (h62 : 0 < δl)
    (h63 : δl ≤ bgC1 S.d S.L N)
    (h64 : ∀ i, InDomainR (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)) (cs.muAct (m' + 1)) δl (locData g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) (ou i) (xu i) hv))
    (h65 : 0 < δu)
    (h66 : δu ≤ bgC1 S.d S.L N)
    (h67 : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
    (h68 : bgK1 S.d S.L N * (δl + δu) ≤ δs)
    (h69 : bgK1 S.d S.L N * δl ≤ min (deltaStar S.d S.L N) δm)
    (h70 : 0 ≤ m)
    (h71 : m * 2 ≤ min (deltaStar S.d S.L N) δm)
    (h72 : ∀ i, cs.muAct (m' + 1) * ((S.L : ℝ) ^ (jf i + 1)) ^ 2 ≤ m)
    (hxsep : ∀ i, 0 ≤ 2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2)
    (Kconv Kbg : ℝ)
    (hKc : 9 * winKsrc S.d N η Ka cν (winV1 Kw η Ka cν) * Cξ * α₀ ^ 2 * Real.exp η ≤ Kconv)
    (hKb : winKb S.d S.L N m' Kw Ks Kw' η Ka cν Dδ β α α₀ γ Cξ Δ δl δu m (cs.muAct (m' + 1)) ≤ Kbg) :
    ∃ C : ℂ, ∑ i, mainActionLoc g (H.locRH (jf i + 1) (cf i)) (jf i)
          (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i) cs (locRH_rem (jf i + 1) (cf i))
          (ou i) (xu i) hv =
        ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
          actionRegionC Xwin ak 0 Du
            (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du)).re - C.re ∧
      ‖C‖ ≤ (9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) + Kbg) *
          ∑ i, (decomp i).total := by
  classical
  have hd2 : 2 ≤ S.d := by omega
  have hL1 : (1 : ℝ) < S.L := by exact_mod_cast (by omega : 1 < S.L)
  have hLpos : (0 : ℝ) < S.L := by linarith
  have hKa : 0 ≤ Ka := (abs_nonneg _).trans (h22 0)
  have hΔ : 0 ≤ Δ := (abs_nonneg _).trans (h24 0)
  have hqq : 0 < 1 - (S.L : ℝ) ^ (-(2 * γ)) := by
    have : (S.L : ℝ) ^ (-(2 * γ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
    linarith
  have hA0 : 0 ≤ winA0 β η α₀ := by unfold winA0; have := h4; have := h6; positivity
  have hAmax0 : 0 ≤ winAmax S.L m' β η α₀ γ := by
    unfold winAmax; exact mul_nonneg hA0 (by positivity)
  set ε₀ := winEps0 S.L m' α α₀ with hε₀def
  have hε0 : 0 < ε₀ := by
    rw [hε₀def]; unfold winEps0
    exact mul_pos h6 (pow_pos (Real.rpow_pos_of_pos hLpos _) _)
  have hg0 : ∀ m, 0 ≤ gf m := fun m => (Real.exp_pos _).le.trans (h15 m).1
  have h20 : ∀ i, cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 *
      ((S.L : ℝ) ^ (-(2 * γ))) ^ (jf i + 1) ≤ winA0 β η α₀ := fun i =>
    beta_epsSq_decay_le S.L S.d hd2 h4.le h6.le h10 (h11 _) (hg0 _) (h15 _).2
  have h21 : ∀ i, cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤
      winAmax S.L m' β η α₀ γ := fun i => by
    unfold winAmax winA0
    exact beta_epsSq_le_pow S.L S.d hd2 h4.le h6.le h9.le h10 (h11 _) (hg0 _) (h15 _).2
      (by have := hjf i; omega)
  have h42 : ∀ i, epsSeq S.L α α₀ (jf i + 1) ≤ 3 * α₀ := fun i =>
    Balaban.Green.epsSeq_le_three_alpha S.L h6 h8 _
  have hKsrc0 : 0 ≤ winKsrc S.d N η Ka cν (winV1 Kw η Ka cν) := by
    unfold winKsrc; positivity
  have h51 : 0 ≤ winKpair S.L (winKsrc S.d N η Ka cν (winV1 Kw η Ka cν)) Cξ η γ
      (winA0 β η α₀) β := by
    unfold winKpair
    refine mul_nonneg hKsrc0 (div_nonneg ?_ (mul_pos (mul_pos two_pos h4) hqq).le)
    have := h7; positivity
  have hS0 : ∀ (E μ Cb Cg Cm : ℝ), 0 ≤ winSqS S.d N E μ Cb Cg Cm := fun _ _ _ _ _ => by
    unfold winSqS; positivity
  have hQ0 : ∀ (Cb Cg Cm : ℝ), 0 ≤ Cb → 0 ≤ Cg → 0 ≤ Cm → 0 ≤ winSqQ S.d N Cb Cg Cm :=
    fun _ _ _ a b c => by unfold winSqQ; positivity
  have hCb0 : 0 ≤ winCb η Ka ε₀ := by unfold winCb; positivity
  have hCg0 : 0 ≤ winCg η ε₀ := by unfold winCg; positivity
  have hCm0 : 0 ≤ winCm η Dδ β ε₀ := by
    unfold winCm
    have hD : 0 ≤ Dδ := ((h16 0).trans_le (h17 0)).le
    have := h4; positivity
  have h52 : 0 ≤ winKcoef S.d S.L N m' Kw η Ka Δ (3 * α₀) β Cξ γ (winA0 β η α₀)
      (winAmax S.L m' β η α₀ γ) (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀)
      (cs.muAct (m' + 1)) := by
    unfold winKcoef
    refine add_nonneg (add_nonneg (div_nonneg ?_ (mul_nonneg h4.le hqq.le)) ?_) ?_
    · have := h7; have := h4; positivity
    · unfold winKwt; have := h4; positivity
    · exact mul_nonneg hAmax0 (add_nonneg (mul_nonneg (by positivity) (hS0 _ _ _ _ _))
        (mul_nonneg (by positivity) (hQ0 _ _ _ hCb0 hCg0 hCm0)))
  have hV0 : 0 ≤ winV Ks Kw' δl δu m := by
    unfold winV; have := h62; have := h65; have := h70; positivity
  have h53 : 0 ≤ winKswitch S.d N (winAmax S.L m' β η α₀ γ) (winV Ks Kw' δl δu m) (3 * α₀)
      (cs.muAct (m' + 1)) (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀) := by
    unfold winKswitch
    exact mul_nonneg hAmax0 (add_nonneg (mul_nonneg hV0 (hS0 _ _ _ _ _))
      (mul_nonneg (by positivity) (hQ0 _ _ _ hCb0 hCg0 hCm0)))
  have h73 : ∀ i, Ks * ((δl + δu) * Real.exp (-(gammaW S.d *
      ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) /
        (S.L : ℝ) ^ (jf i + 1))))) + Kw' * (m * 2) ≤ winV Ks Kw' δl δu m := fun i => by
    unfold winV
    have hy : 0 ≤ gammaW S.d * ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) *
        (S.L : ℝ) ^ (jf i + 1) - 2) / (S.L : ℝ) ^ (jf i + 1)) :=
      mul_nonneg (Balaban.Localization.gammaW_nonneg (by omega))
        (div_nonneg (hxsep i) (by positivity))
    have he : Real.exp (-(gammaW S.d * ((2 * ((S.L : ℝ) ^ jf i * M) - (ϱB + 3 * S.d) *
        (S.L : ℝ) ^ (jf i + 1) - 2) / (S.L : ℝ) ^ (jf i + 1)))) ≤ 1 :=
      Real.exp_le_one_iff.2 (by linarith)
    have h1 : (δl + δu) * Real.exp (-(gammaW S.d * ((2 * ((S.L : ℝ) ^ jf i * M) -
        (ϱB + 3 * S.d) * (S.L : ℝ) ^ (jf i + 1) - 2) / (S.L : ℝ) ^ (jf i + 1)))) ≤ δl + δu :=
      mul_le_of_le_one_right (by linarith) he
    have := mul_le_mul_of_nonneg_left h1 hKs
    linarith
  obtain ⟨C, hC, hCb⟩ := hcl ak β ν η Ka cν Dδ (winV1 Kw η Ka cν)
    (winKsrc S.d N η Ka cν (winV1 Kw η Ka cν)) Cξ α α₀ γ (winA0 β η α₀) Δ
    (winKwt S.d S.L m' η β Δ (3 * α₀)) (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀)
    (winAmax S.L m' β η α₀ γ) (3 * α₀) ε₀
    (winKpair S.L (winKsrc S.d N η Ka cν (winV1 Kw η Ka cν)) Cξ η γ (winA0 β η α₀) β)
    (winKcoef S.d S.L N m' Kw η Ka Δ (3 * α₀) β Cξ γ (winA0 β η α₀) (winAmax S.L m' β η α₀ γ)
      (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀) (cs.muAct (m' + 1)))
    (winKswitch S.d N (winAmax S.L m' β η α₀ γ) (winV Ks Kw' δl δu m) (3 * α₀)
      (cs.muAct (m' + 1)) (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀))
    gf δ ξ h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21 h22 h23 h24 h25 h26 h27
    hε0 le_rfl h30 h31 h32 h33 h34 h35 h36 h37 h38 h39 h40 h41 h42
    (by unfold winCb; exact le_rfl) (by unfold winCg; exact le_rfl)
    (by unfold winCm; exact le_rfl) (by unfold winKwt; exact le_rfl)
    (by unfold winV1; exact le_rfl) (by unfold winKsrc; exact le_rfl)
    (by unfold winKpair; exact le_rfl) (by unfold winKcoef; exact le_rfl) h51 h52 h53
    ϱB δl δu (winV Ks Kw' δl δu m) (winKmass (winCm η Dδ β ε₀) (winAmax S.L m' β η α₀ γ)) m
    h56 h57 h58 h59 h60 h61 h62 h63 h64 h65 h66 h67 h68 h69 h70 h71 h72 h73
    (by unfold winKswitch winSqS winSqQ; exact le_rfl) (by unfold winKmass; exact le_rfl)
  refine ⟨C, hC, hCb.trans ?_⟩
  have hT : 0 ≤ ∑ i, (decomp i).total := Finset.sum_nonneg fun i _ => (decomp i).total_nonneg
  refine mul_le_mul_of_nonneg_right ?_ hT
  have h1 : 9 * Real.exp (2 * η) * (9 * winKsrc S.d N η Ka cν (winV1 Kw η Ka cν) * Cξ * α₀ ^ 2 *
      Real.exp η) / (1 - (S.L : ℝ) ^ (-(2 * γ))) ≤
      9 * Real.exp (2 * η) * Kconv / (1 - (S.L : ℝ) ^ (-(2 * γ))) :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hKc (by positivity)) hqq.le
  have h2 : winKpair S.L (winKsrc S.d N η Ka cν (winV1 Kw η Ka cν)) Cξ η γ (winA0 β η α₀) β +
      winKcoef S.d S.L N m' Kw η Ka Δ (3 * α₀) β Cξ γ (winA0 β η α₀) (winAmax S.L m' β η α₀ γ)
        (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀) (cs.muAct (m' + 1)) +
      winKswitch S.d N (winAmax S.L m' β η α₀ γ) (winV Ks Kw' δl δu m) (3 * α₀)
        (cs.muAct (m' + 1)) (winCb η Ka ε₀) (winCg η ε₀) (winCm η Dδ β ε₀) +
      winKmass (winCm η Dδ β ε₀) (winAmax S.L m' β η α₀ γ) ≤ Kbg := hKb
  linarith
