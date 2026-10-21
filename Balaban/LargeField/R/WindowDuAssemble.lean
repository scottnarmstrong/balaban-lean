/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.WindowDuMassTerm
public import Balaban.LargeField.R.WindowConvPhysSwitchLocBudget
public import Balaban.LargeField.R.WindowDuBall

/-!
# The mass budget of a piece on the real flow (blocker 4)

`piece_mass_card_le`: `β g_k |ν_k| |X| ≤ C_m A_max |X|_{mix}` for the region `X` of a piece, from the per-cube
budget of the mass term (`switch_cube_budgets`).
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.Multiscale Balaban.Background Finset

variable {d L N₀ K : ℕ} [NeZero N₀] [NeZero L] {ϱ : ℝ} {G : GeneratingSet d L N₀ K ϱ}

theorem piece_mass_card_leP (X : Region G) (Dc : StepDecomp X) (hwt1 : ∀ c, Dc.wt c = 1)
    {β gk ν δk Cm Amax A : ℝ} (hCm0 : 0 ≤ Cm) (hAmax : A ≤ Amax)
    (hcm : ∀ c, β * gk * ∑ _x ∈ (Dc.cube c).sites, |ν * δk| ≤ Cm * (A * Dc.wt c)) :
    β * gk * |ν * δk| * (X.sites.card : ℝ) ≤ Cm * Amax * Dc.total := by
  refine (Dc.card_budget (β := β * gk) (κ := Cm * Amax) (ν * δk) (fun c => ?_))
  refine (hcm c).trans ?_
  rw [hwt1 c, mul_one, mul_one]
  exact mul_le_mul_of_nonneg_left hAmax hCm0

theorem piece_mass_card_le (X : Region G) (Dc : StepDecomp X) (hd : 2 ≤ d) {j k : ℕ}
    (hjk : j + 1 ≤ k) (hwt1 : ∀ c, Dc.wt c = 1)
    (hcells : ∀ c, ∃ x ∈ X.sites, (Dc.cube c).sites = G.blk (G.layerIndex x) x ∧
      G.layerIndex x ≤ j + 1)
    (a : ℕ → ℝ) {β η gk gj Ka Dδ ε₀ E ν δk Cb Cg Cm Amax : ℝ} (hβ : 0 < β)
    (hgk : gk ≤ Real.exp η) (hgk' : Real.exp (-η) ≤ gk) (hgj : Real.exp (-η) ≤ gj)
    (hε₀ : 0 < ε₀) (hE : ε₀ ^ 2 ≤ E ^ 2)
    (hKa : ∀ ℓ, |a ℓ| ≤ Ka) (hreg : β * |ν| * (L : ℝ) ^ (k * d) ≤ 1) (hδk : |δk| ≤ Dδ)
    (hCb : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (hCg : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (hCm : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
    (hAmax : β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 ≤ Amax) :
    β * gk * |ν * δk| * (X.sites.card : ℝ) ≤ Cm * Amax * Dc.total := by
  have hgk0 : 0 < gk := lt_of_lt_of_le (Real.exp_pos _) hgk'
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hDδ0 : 0 ≤ Dδ := (abs_nonneg _).trans hδk
  have hε2 : 0 < ε₀ ^ 2 := by positivity
  have hCm0 : 0 ≤ Cm := le_trans (by positivity) hCm
  obtain ⟨-, -, hcm⟩ := switch_cube_budgets X Dc hd hjk hwt1 hcells a hβ hgk hgj hε₀ hE hKa hreg
    hδk hCb hCg hCm
  have hA0 : 0 ≤ β * (L : ℝ) ^ ((d - 2) * (j + 1)) * gj * E ^ 2 := by
    have := lt_of_lt_of_le (Real.exp_pos _) hgj
    positivity
  exact piece_mass_card_leP X Dc hwt1 hCm0 hAmax hcm

section Split

open Balaban Balaban.Multiscale Balaban.Fluctuation RegionHistory Balaban.LargeField.ActionConv Balaban.SmallField Balaban.Flow

universe u

variable {S : Setting} {n : ℕ → ℕ} [∀ k, NeZero (n k)] {R : ℕ → ℝ} {k0 K M : ℕ} [NeZero M]
  [NeZero S.L] {N : ℕ} {H : RegionHistory S n R k0 K} {m' : ℕ} {Z : H.Comp (m' + 1)}
  {g : Geo S n R M} {ι : Type u} [Fintype ι]

/-- **The window action at mass `ν` and the physical datum is the window action at mass `0` and the datum
`Du` up to the mass term** (P7 (2.16)): `β A_X(a, ν, D^{ph}, φ) = β A_X(a, 0, Du, φ) + M`,
`‖M‖ ≤ 2 C_m A_max ∑_i |X_i|_{mix}`, for a unit field `φ` and a datum `Du` with the same `Ψ` as
`D^{ph}` on the balls around the pieces. -/
theorem window_Du_mass_split (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hjK : ∀ i, jf i + 1 ≤ K)
    (hcov : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
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
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (hDuball : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x))
    (ak : ℕ → ℝ) (φ : (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))).Ω 1 × Fin N → ℂ)
    (hφ : ∀ x : (((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW))).Ω 1, ∑ j, ‖φ (x, j)‖ ^ 2 = 1)
    (βc ν Cm Amax : ℝ) (hβc : 0 ≤ βc)
    (hbud : ∀ i, βc * |ν| * ((Xc i).sites.card : ℝ) ≤ Cm * Amax * (decomp i).total) :
    ∃ M : ℂ, (βc : ℂ) * actionRegionC Xwin ak ν (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)) φ =
        (βc : ℂ) * actionRegionC Xwin ak 0 Du φ + M ∧
      ‖M‖ ≤ 2 * (Cm * Amax) * ∑ i, (decomp i).total := by
  classical
  have hsub := window_sites_subset hmK jf cf hjf hcov hW Xw hXw Xwin hXwin
  have hΨ : ∀ y, (y ∈ Xwin.sites ∨ ∃ μ : Fin S.d, y + Pi.single μ 1 ∈ Xwin.sites ∨
      y - Pi.single μ 1 ∈ Xwin.sites) → (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ y = Du.Ψ y := by
    intro y hy
    obtain ⟨i, z, hz, hzd⟩ := window_near_ball hmK jf cf hjf hjK hW Xw hXw Xwin hsub Xc hXc y hy
    have := hDuball i _ ⟨z, hz, hzd⟩
    rw [Equiv.symm_apply_apply] at this
    exact this.symm
  have e1 := actionRegionC_mass_sub Xwin ak ν (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)) φ
  have e2 := actionRegionC_congr_Ψ_zero Xwin ak hΨ φ
  refine ⟨(βc : ℂ) * ((ν : ℂ) / 2 * Xwin.massPair (fun x j => svec ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) φ x j - (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h x j)
      (fun x j => svec ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) φ x j - (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h x j)), ?_, ?_⟩
  · have h3 : actionRegionC Xwin ak ν (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)) φ = actionRegionC Xwin ak 0 Du φ +
        (ν : ℂ) / 2 * Xwin.massPair (fun x j => svec ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) φ x j - (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h x j)
          (fun x j => svec ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) φ x j - (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h x j) := by
      rw [← e2]; linear_combination e1
    rw [h3]; ring
  · have hh1 : ∑ j, ‖((hv j : ℝ) : ℂ)‖ ^ 2 = 1 := by
      have h1 := EuclideanSpace.norm_sq_eq hv
      rw [hunit] at h1
      simpa [Complex.norm_real] using h1.symm
    have hu : ∀ x ∈ Xwin.sites, ∑ j, ‖svec ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) φ x j - (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h x j‖ ^ 2 ≤ 4 := by
      intro x hx
      have hx1 := Xwin.sub_Ω hx
      have e3 : ∀ j, svec ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) φ x j = φ (⟨x, hx1⟩, j) := fun j => svec_of_mem _ φ ⟨x, hx1⟩ j
      have e4 : ∀ j, (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).h x j = ((hv j : ℝ) : ℂ) := fun j =>
        physicalWindowData_h _ _ _ ψ (fun q => hv q) hx1 j
      simp only [e3, e4]
      exact sum_norm_sub_sq_le_four _ _ (hφ ⟨x, hx1⟩) hh1
    have h5 := massTerm_norm_le Xwin Xw hsub _ (B := 4) (by norm_num) hu βc ν
    refine h5.trans ?_
    have hcard : ∑ i, ((Xw i).sites.card : ℝ) = ∑ i, ((Xc i).sites.card : ℝ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact_mod_cast window_card_sites_eq hmK jf cf hjf hjK hW Xw hXw Xc hXc i
    rw [hcard, abs_of_nonneg hβc]
    have h6 : βc * |ν| * ∑ i, ((Xc i).sites.card : ℝ) ≤ Cm * Amax * ∑ i, (decomp i).total := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_le_sum fun i _ => hbud i
    calc βc * |ν| / 2 * (4 * ∑ i, ((Xc i).sites.card : ℝ))
        = 2 * (βc * |ν| * ∑ i, ((Xc i).sites.card : ℝ)) := by ring
      _ ≤ 2 * (Cm * Amax * ∑ i, (decomp i).total) := by linarith only [h6]
      _ = 2 * (Cm * Amax) * ∑ i, (decomp i).total := by ring

open Balaban.Flow in
/-- **The sum of the main actions at the reference datum `Du`**: from the conversion at the physical datum
(`T = Re(β_k A_X(a, ν, D^{ph}, φ)) - Re C`) to `T = Re(β_k A_X(a, 0, Du, φ)) - Re C'`. -/
theorem window_Du_finish (cs : OpConsts) (hmK : m' + 1 ≤ K) (hW : H.RipeWindow (m' + 1) Z)
    (jf : ι → ℕ) (cf : ∀ i, H.Comp (jf i + 1))
    (hjf : ∀ i, S.k1 (m' + 1) ≤ jf i ∧ jf i ≤ m')
    (hjK : ∀ i, jf i + 1 ≤ K)
    (hcov : ∀ j (c : H.Comp (j + 1)), S.k1 (m' + 1) ≤ j → j ≤ m' → c ∈ H.ancFin (j + 1) (m' + 1) Z →
      ∃ i, (⟨jf i, cf i⟩ : Σ j, H.Comp (j + 1)) = ⟨j, c⟩)
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
      ((decomp i).cube c).sites = (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).blk ((locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x) x ∧
        (locGen g (H.locRH (jf i + 1) (cf i)) (jf i) (cf i).1 (locComp_mem H (hjK i) (cf i)) (hjK i)).layerIndex x ≤ jf i + 1)
    (hv : EuclideanSpace ℝ (Fin N)) (hunit : ‖hv‖ = 1)
    (ψ : BlockV S.d S.L (M * n (m' + 1)) (m' + 1) → EuclideanSpace ℝ (Fin N))
    (Du : BgData ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) N)
    (hDuball : ∀ i x, (∃ z ∈ (Xc i).sites, Green.torusDist S.d (g.M1 * (g.c * n (jf i + 1)) * S.L ^ (jf i + 1)) z x ≤ 2 * ((S.L : ℝ) ^ jf i * M)) →
      Du.Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x) = (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)).Ψ ((Equiv.cast (congrArg (Torus S.d) (piece_torus_eq g H.F.hnn hmK (hjf i).2))).symm x))
    (ak : ℕ → ℝ) (β η Ka Dδ ε₀ α α₀ Amax Cb Cg Cm Kmass ν Bc : ℝ) (gf δ : ℕ → ℝ)
    (p1 : 0 < β) (p3 : 0 < α₀) (p5 : 0 ≤ α)
    (p8 : ∀ m, cs.beta m = β * (S.L : ℝ) ^ ((S.d - 2) * m) * gf m)
    (p9 : ∀ m, cs.muAct m = ν * δ m)
    (p12 : ∀ m, Real.exp (-η) ≤ gf m ∧ gf m ≤ Real.exp η)
    (p13 : ∀ m, 0 < δ m) (p14 : ∀ m, δ m ≤ Dδ)
    (p18 : ∀ i, cs.beta (jf i + 1) * epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax)
    (p19 : ∀ ℓ, |ak ℓ| ≤ Ka) (p24 : β * |ν| * (S.L : ℝ) ^ ((m' + 1) * S.d) ≤ 1)
    (p25 : 0 < ε₀) (p26 : ε₀ ≤ α₀ * ((S.L : ℝ) ^ (-α)) ^ (m' + 1))
    (p40 : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (p41 : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (p42 : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
    {δu : ℝ} (hHw0 : BgHyp S.d S.L (m' + 1) (winSep g) ak 0) (u1 : 0 < δu) (u2 : δu ≤ bgC1 S.d S.L N)
    (u3 : InDomainR ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) 0 δu Du)
    (tKm : 2 * (Cm * Amax) ≤ Kmass)
    {T : ℝ} {C : ℂ}
    (hT : T = ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
      actionRegionC Xwin ak (cs.muAct (m' + 1)) (physicalWindowData (windowOfHistory H Z g hmK hW) (windowOfHistory_hyp hmK hW) (windowOfHistory_parentRefines H Z g hmK hW) ψ (fun q => hv q)) (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du)).re - C.re)
    (hCb : ‖C‖ ≤ Bc * ∑ i, (decomp i).total) :
    ∃ C' : ℂ, T = ((betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 : ℂ) *
        actionRegionC Xwin ak 0 Du (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du)).re - C'.re ∧
      ‖C'‖ ≤ (Bc + Kmass) * ∑ i, (decomp i).total := by
  classical
  have hj1 : ∀ i, jf i + 1 ≤ m' + 1 := fun i => Nat.succ_le_succ (hjf i).2
  have hβ' : betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 = β * gf (m' + 1) :=
    betaCanon_eq_of_flow cs S.d S.L β gf p8 (m' + 1)
  have hδk : |δ (m' + 1)| ≤ Dδ := by rw [abs_of_pos (p13 _)]; exact p14 _
  have hgf0 : 0 < gf (m' + 1) := lt_of_lt_of_le (Real.exp_pos _) (p12 _).1
  obtain ⟨φ₀, α₀', hs0, -, hu0, hunit0, -, -⟩ := bg_real hHw0 u1 u2 u3
  have hφw : (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du) = φ₀ := (bgFieldC_eq hs0 hu0).1
  have hbud : ∀ i, betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 * |cs.muAct (m' + 1)| *
      ((Xc i).sites.card : ℝ) ≤ Cm * Amax * (decomp i).total := by
    intro i
    have hE2 : ε₀ ^ 2 ≤ epsSeq S.L α α₀ (jf i + 1) ^ 2 :=
      (pow_le_pow_left₀ p25.le p26 2).trans (ActionConv.epsSeq_sq_ge S.L p5 p3 (hj1 i))
    have hAmax : β * (S.L : ℝ) ^ ((S.d - 2) * (jf i + 1)) * gf (jf i + 1) *
        epsSeq S.L α α₀ (jf i + 1) ^ 2 ≤ Amax := by
      rw [← p8 (jf i + 1)]; exact p18 i
    have h1 := piece_mass_card_le (Xc i) (decomp i) (by have := hHw0.hd; omega) (hj1 i) (hwt1 i)
      (hcells i) ak (gk := gf (m' + 1)) (gj := gf (jf i + 1)) (δk := δ (m' + 1)) (ν := ν)
      (E := epsSeq S.L α α₀ (jf i + 1)) p1 (p12 _).2 (p12 _).1 (p12 _).1 p25 hE2 p19 p24 hδk p40 p41
      p42 hAmax
    rw [← p9 (m' + 1), ← hβ'] at h1
    exact h1
  have hβc0 : 0 ≤ betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0 := by
    rw [hβ']; exact (mul_pos p1 hgf0).le
  obtain ⟨M', hM1, hM2⟩ := window_Du_mass_split hmK hW jf cf hjf hjK hcov Xw hXw Xwin hXwin Xc hXc
    decomp hv hunit ψ Du hDuball ak (bgFieldC ((windowOfHistory H Z g hmK hW).windowGenSet (windowOfHistory_hyp hmK hW)) ak 0 (bgC0 S.d S.L N) Du)
    (by rw [hφw]; intro x; exact (hunit0 x).2)
    (betaCanon S.d S.L (cs.beta (m' + 1)) (m' + 1) 0) (cs.muAct (m' + 1)) Cm Amax hβc0 hbud
  have hT0 : 0 ≤ ∑ i, (decomp i).total := Finset.sum_nonneg fun i _ => (decomp i).total_nonneg
  refine ⟨C - M', ?_, ?_⟩
  · rw [hT, hM1]
    simp only [Complex.add_re, Complex.sub_re]
    ring
  · refine (norm_sub_le _ _).trans ?_
    have h7 : 2 * (Cm * Amax) * ∑ i, (decomp i).total ≤ Kmass * ∑ i, (decomp i).total :=
      mul_le_mul_of_nonneg_right tKm hT0
    linarith only [hCb, hM2, h7]

end Split

end Balaban.LargeField.ActionConv
