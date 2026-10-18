/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.LargeField.R.CoeffResponseBlock
public import Balaban.LargeField.R.WindowConvPhysSourceFinal
public import Balaban.LargeField.R.WindowConvPhysPairFinal
public import Balaban.LargeField.R.WindowConvUniform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Assembly of the window conversion from its parts (P7 (2.11), (2.14)-(2.16))

`PieceWindowSetup.exists_window_conversion_of_flow` composes `exists_hsource_of_flow` (the source
estimate `p7_first`), `exists_hpair_of_flow`, `exists_hcoef_of_flow_cubes_block` and the read
comparison through `window_uniform_of_parts` and `window_conversion_pieces_of_rg_source`.  The
constants `(K_w, δ_w)` of the three parts are unified (maximum, minimum).  The mass switch
`hswitch` and the read comparison `hread` stay as premises (with an arbitrary intermediate action
`R`); all other premises are source regime data, the typing of the chains, and class domains.
-/

@[expose] public section

namespace Balaban.LargeField.ActionConv

open Balaban.LargeField Balaban.Flow Balaban.Multiscale Balaban.Background Balaban.SmallField
  Balaban.Fluctuation Finset

universe u₁ u₂

section Aux

variable {d L : ℕ} [NeZero L]

/-- The increments of the flow are at most `1/2` when `C_ξ e^{2η} q / (β (1 - q)) ≤ 1/2`. -/
theorem norm_xi_le_half_of_decay {β Cξ η q : ℝ} {v : Fin 3 → ℝ} {t : ℕ} (hβ : 0 < β)
    (hCξ : 0 ≤ Cξ) (hq0 : 0 ≤ q) (hq1 : q < 1) (hη : 0 ≤ η)
    (hρ : Cξ * Real.exp (2 * η) * q / (β * (1 - q)) ≤ 1 / 2)
    (hv : ∀ c, |v c| ≤ Cξ * β⁻¹ * q ^ (t + 1)) : ‖v‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 hv |>.trans ?_
  have h1 : q ^ (t + 1) ≤ q := by
    calc q ^ (t + 1) ≤ q ^ 1 := pow_le_pow_of_le_one hq0 hq1.le (by omega)
      _ = q := pow_one q
  have hq' : 0 < 1 - q := by linarith
  have he : 1 ≤ Real.exp (2 * η) := Real.one_le_exp (by linarith)
  have h2 : Cξ * Real.exp (2 * η) * q ≤ 1 / 2 * (β * (1 - q)) := by
    have := (div_le_iff₀ (by positivity)).1 hρ
    linarith
  have h3 : Cξ * β⁻¹ * q ≤ 1 / 2 := by
    have hCq : Cξ * q ≤ Cξ * Real.exp (2 * η) * q := by
      have : 0 ≤ Cξ * q := by positivity
      nlinarith
    have h4 : Cξ * q ≤ 1 / 2 * (β * (1 - q)) := hCq.trans h2
    calc Cξ * β⁻¹ * q = (Cξ * q) / β := by field_simp
      _ ≤ (1 / 2 * (β * (1 - q))) / β := by gcongr
      _ = 1 / 2 * (1 - q) := by field_simp
      _ ≤ 1 / 2 := by nlinarith
  calc Cξ * β⁻¹ * q ^ (t + 1) ≤ Cξ * β⁻¹ * q := by gcongr
    _ ≤ 1 / 2 := h3

/-- The mass regime on the sites of a generating set of depth at most `k`. -/
theorem window_mass_spacing_le {N₀' K' : ℕ} [NeZero N₀'] {ϱ' : ℝ} (G : GeneratingSet d L N₀' K' ϱ')
    (x : G.Ω 1) {k : ℕ} (hK : K' ≤ k) {ν Dδ cν : ℝ} (hDδ : 0 ≤ Dδ) (hν : 0 ≤ ν)
    (h : ν * (L : ℝ) ^ (2 * k) * Dδ ≤ cν ^ 2) (hL : 1 ≤ L) :
    ν * G.spacing x.1 ^ 2 * Dδ ≤ cν ^ 2 := by
  refine le_trans ?_ h
  have hx := G.layerIndex_spec x.2
  have hL1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hle : (L : ℝ) ^ G.layerIndex x.1 ≤ (L : ℝ) ^ k :=
    pow_le_pow_right₀ hL1 (hx.2.1.trans hK)
  have h2 : ((L : ℝ) ^ G.layerIndex x.1) ^ 2 ≤ (L : ℝ) ^ (2 * k) := by
    rw [pow_mul']
    exact pow_le_pow_left₀ (by positivity) hle 2
  unfold GeneratingSet.spacing
  gcongr

theorem coef_const_mono {a Kwt Amax X Ssum T Kc Kw : ℝ} (hA : 0 ≤ Amax) (hX : 0 ≤ X)
    (hS : 0 ≤ Ssum) (hT : 0 ≤ T) (hKc : 0 ≤ Kc) (h : Kc ≤ Kw) :
    a + Kwt + Amax * (Kc * X * Ssum + (Kc * X) ^ 2 / 2 * T) ≤
      a + Kwt + Amax * (Kw * X * Ssum + (Kw * X) ^ 2 / 2 * T) := by
  have h1 : Kc * X ≤ Kw * X := mul_le_mul_of_nonneg_right h hX
  have h0 : 0 ≤ Kc * X := mul_nonneg hKc hX
  gcongr

theorem epsSeq_pos_aux (L : ℕ) [NeZero L] (α α₀ : ℝ) (hα₀ : 0 < α₀) (j : ℕ) :
    0 < epsSeq L α α₀ j := by
  unfold epsSeq
  have := epsTail_pos j
  have hL : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  positivity

end Aux

section Assembly

variable {d L N₀ K N : ℕ} [NeZero N₀] [NeZero L]
  {U : Type u₁} [NormedAddCommGroup U] [NormedSpace ℂ U] {S : Set U} {ι : Type u₂} [Fintype ι]
  {sc : ι → ℕ} {k1 k : ℕ}

/-- **The window conversion from the flow.**  The parts `hsource`, `hpair`, `hcoef` are proved;
`hswitch` and `hread` (for an intermediate action `R`) are premises. -/
theorem PieceWindowSetup.exists_window_conversion_of_flow (hd3 : 3 ≤ d) (hL3 : 3 ≤ L) :
    ∃ Kw δw : ℝ, 0 < Kw ∧ 0 < δw ∧ ∀
    (W : PieceWindowSetup d L N₀ K N S ι sc k1 k) (cs : OpConsts) (R : ι → U → ℂ)
    (β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀
      Kpair Kcoef Kswitch Kread : ℝ) (g δ : ℕ → ℝ) (ξ : ℕ → Fin 3 → ℝ)
    -- the real flow and its decay
    (_ : 0 < β) (_ : 0 < ν) (_ : 0 < α₀) (_ : 0 ≤ Cξ) (_ : 0 ≤ α) (_ : 0 < γ)
    (_ : (d : ℝ) - 2 - 2 * α = 2 * γ)
    (_ : ∀ m, cs.beta m = β * (L : ℝ) ^ ((d - 2) * m) * g m)
    (_ : ∀ m, cs.muAct m = ν * δ m)
    (_ : ∀ m, g m = g (m + 1) * (1 + ξ m 2))
    (_ : ∀ m, δ m * (1 + ξ m 2) = δ (m + 1) * (1 + ξ m 1))
    (_ : ∀ m, Real.exp (-η) ≤ g m ∧ g m ≤ Real.exp η)
    (_ : ∀ m, 0 < δ m) (_ : ∀ m, δ m ≤ Dδ)
    (_ : ∀ m c, |ξ m c| ≤ Cξ * β⁻¹ * ((L : ℝ) ^ (-(2 * γ))) ^ (m + 1))
    (_ : Cξ * Real.exp (2 * η) * (L : ℝ) ^ (-(2 * γ)) / (β * (1 - (L : ℝ) ^ (-(2 * γ)))) ≤ 1 / 2)
    -- the size of the sources `A_i = cs.beta (sc i + 1) ε²`
    (_ : ∀ i, cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 *
      ((L : ℝ) ^ (-(2 * γ))) ^ (sc i + 1) ≤ A₀)
    (_ : ∀ i, cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2 ≤ Amax)
    -- the typing of the chains
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k → (W.chain i).β m = betaCanon d L (cs.beta m) m 0)
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k → (W.chain i).ν m = cs.muAct m)
    (_ : ∀ i, (W.chain i).a (sc i + 1) = cs.aw)
    (_ : ∀ i, ∀ u ∈ S, ∀ m, sc i + 1 ≤ m → m ≤ k → (W.chain i).Dat u m = (W.chain i).Dat u k)
    (_ : ∀ i, ∀ u ∈ S, ∀ m, sc i + 1 ≤ m → m ≤ k → (W.chain i).φ u m =
      bgFieldC (W.Gc i) ((W.chain i).a m) ((W.chain i).ν m) (bgC0 d L N) ((W.chain i).Dat u m))
    -- the cells of the decompositions: layer blocks of weight one
    (_ : ∀ i c, (W.decomp i).wt c = 1)
    (_ : ∀ i c, ∃ x ∈ (W.Xc i).sites,
      ((W.decomp i).cube c).sites = (W.Gc i).blk ((W.Gc i).layerIndex x) x ∧
        (W.Gc i).layerIndex x ≤ sc i + 1)
    (_ : ∀ i, W.Kc i ≤ k)
    -- the sizes of the coefficients and of the mass, and the regime
    (_ : ∀ ℓ, |W.ak ℓ| ≤ Ka) (_ : ∀ ℓ, |cs.aw ℓ| ≤ Ka) (_ : ∀ ℓ, |cs.aw ℓ - W.ak ℓ| ≤ Δ)
    (_ : 0 ≤ cν) (_ : ν * (L : ℝ) ^ (2 * k) * Dδ ≤ cν ^ 2)
    (_ : β * |ν| * (L : ℝ) ^ (k * d) ≤ 1)
    (_ : 0 < ε₀) (_ : ε₀ ≤ α₀ * ((L : ℝ) ^ (-α)) ^ k)
    -- the standing hypotheses and the class domains
    (_ : ∀ i, ∃ N₁ m₁ : ℕ, W.N₀c i = N₁ * L ^ m₁)
    (_ : ∀ i m, sc i + 1 ≤ m → m ≤ k →
      BgHyp d L (W.Kc i) (W.ϱc i) ((W.chain i).a m) ((W.chain i).ν m))
    (_ : ∀ i, BgHyp d L (W.Kc i) (W.ϱc i) cs.aw ((W.chain i).ν k))
    (_ : ∀ i, BgHyp d L (W.Kc i) (W.ϱc i) W.ak ((W.chain i).ν k))
    (_ : ∀ i, 2 * d * Real.log L ≤ agmonRate d / 16 * (W.ϱc i - 1))
    (_ : ∀ i, (4 * d + 6) * ((2 * d + 1) * epsSeq L α α₀ (sc i + 1)) ≤ 1)
    (_ : ∀ i, xiC1 d * epsSeq L α α₀ (sc i + 1) ≤ bgC1 d L N)
    (_ : ∀ i, ∀ u ∈ S, ∀ m, sc i + 1 ≤ m → m ≤ k →
      XiCOneReal (W.Gc i) ((W.chain i).a m) ((W.chain i).ν m) (epsSeq L α α₀ (sc i + 1))
        ((W.chain i).Dat u m))
    (_ : ∀ i, ∀ u ∈ S, XiCOneReal (W.Gc i) cs.aw ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    (_ : ∀ i, ∀ u ∈ S, XiCOneReal (W.Gc i) W.ak ((W.chain i).ν k) (epsSeq L α α₀ (sc i + 1))
      ((W.chain i).Dat u k))
    -- smallness of the data
    (_ : ∀ i, bgK1 d L N * (xiC1 d * epsSeq L α α₀ (sc i + 1)) ≤ min (deltaStar d L N) δw)
    (_ : ∀ i, epsSeq L α α₀ (sc i + 1) * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤
      min (deltaStar d L N) δw)
    (_ : ∀ i, Δ * (2 * epsSeq L α α₀ (sc i + 1)) ≤ min (deltaStar d L N) δw)
    -- the constants
    (_ : ∀ i, epsSeq L α α₀ (sc i + 1) ≤ Emax)
    (_ : Real.exp (2 * η) * Ka / ε₀ ^ 2 ≤ Cb) (_ : Real.exp (2 * η) / ε₀ ^ 2 ≤ Cg)
    (_ : Real.exp (2 * η) * Dδ / (β * ε₀ ^ 2) ≤ Cm)
    (_ : (4 * Emax ^ 2) * (β * Real.exp η * (L : ℝ) ^ ((d - 2) * k) * Δ) / 2 ≤ Kwt)
    (_ : Kw * (4 * Real.exp (2 * η) * Ka + 24 * cν) ≤ V1)
    (_ : Real.sqrt ((4 * Ka) * (N * Ka * V1 ^ 2)) +
      Real.sqrt ((4 * d * Real.exp (2 * η)) * (d * (N * Real.exp (2 * η)) * V1 ^ 2)) +
      Real.sqrt ((12 * Real.exp (2 * η)) * (N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2)) +
      (N * Ka * V1 ^ 2 + d * (N * Real.exp (2 * η)) * V1 ^ 2 +
        N * (Real.exp (2 * η) * cν ^ 2) * V1 ^ 2) / 2 +
      4 * d * Real.exp (2 * η) + 12 * Real.exp (2 * η) ≤ Ksrc)
    (_ : Ksrc * (Cξ * Real.exp (2 * η) * (L : ℝ) ^ (-(2 * γ)) * A₀ /
      (2 * β * (1 - (L : ℝ) ^ (-(2 * γ))))) ≤ Kpair)
    (_ : 2 * (Ka + Δ) * A₀ * Cξ * Real.exp (2 * η) * (L : ℝ) ^ (-(2 * γ)) /
          (β * (1 - (L : ℝ) ^ (-(2 * γ)))) + Kwt +
        Amax * (Kw * (Δ * (2 * Emax)) * (Real.sqrt (((4 * Emax ^ 2) * Cb) * (N * Cb)) +
          Real.sqrt ((d * ((4 * Emax ^ 2) * Cg)) * (d * (N * Cg))) +
          Real.sqrt (((4 * Emax ^ 2 / |cs.muAct k|) * Cm) * (N * Cm))) +
          (Kw * (Δ * (2 * Emax))) ^ 2 / 2 * (N * Cb + d * (N * Cg) + N * Cm)) ≤ Kcoef)
    (_ : 0 ≤ Kpair) (_ : 0 ≤ Kcoef) (_ : 0 ≤ Kswitch) (_ : 0 ≤ Kread)
    -- the mass switch and the read comparison, through the intermediate action `R`
    (_ : ∀ i, ∀ u ∈ S,
      ‖((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) W.ak ((W.chain i).ν k)
          ((W.chain i).Dat u k) (bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N)
            ((W.chain i).Dat u k)) - R i u‖ ≤ Kswitch * W.mcount i)
    (_ : ∀ i, ∀ u ∈ S,
      ‖R i u - (W.βk : ℂ) * actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)‖ ≤
        Kread * W.mcount i)
    -- analyticity
    (_ : ∀ i, ∀ n, sc i + 1 ≤ n → n ≤ k → AnalyticOnNhd ℂ (fun u => (W.chain i).T u n) S)
    (_ : ∀ i, AnalyticOnNhd ℂ (fun u => (W.βk : ℂ) *
      actionRegionC (W.Xw i) W.ak W.νk (W.Datw u) (W.φw u)) S),
    ∃ C : U → ℂ,
      (∀ u ∈ S, (W.βk : ℂ) * actionRegionC W.Xwin W.ak W.νk (W.Datw u) (W.φw u) =
        ∑ i, (W.chain i).T u (sc i + 1) + C u) ∧
      AnalyticOnNhd ℂ C S ∧
      ∀ u ∈ S, ‖C u‖ ≤
        (9 * Real.exp (2 * η) * (9 * Ksrc * Cξ * α₀ ^ 2 * Real.exp η) /
            (1 - (L : ℝ) ^ (-(2 * γ))) + (Kpair + Kcoef + Kswitch + Kread)) *
          ∑ i, W.mcount i := by
  obtain ⟨Kc, δc, hKc, hδc, Hc⟩ := PieceWindowSetup.exists_hcoef_of_flow_cubes_block
    (d := d) (L := L) (N₀ := N₀) (K := K) (N := N) (S := S) (ι := ι) (sc := sc) (k1 := k1)
    (k := k) hd3 hL3
  obtain ⟨Ks, δs, hKs, hδs, Hs⟩ := PieceWindowSetup.exists_hsource_of_flow.{u₁, u₂}
    (d := d) (L := L) (N := N) hd3 hL3
  obtain ⟨Kp, δp, hKp, hδp, Hp⟩ := PieceWindowSetup.exists_hpair_of_flow.{u₁, u₂}
    (d := d) (L := L) (N := N) hd3 hL3
  refine ⟨max Kc (max Ks Kp), min δc (min δs δp), lt_max_of_lt_left hKc,
    lt_min hδc (lt_min hδs hδp), ?_⟩
  intro W cs R β ν η Ka cν Dδ V1 Ksrc Cξ α α₀ γ A₀ Δ Kwt Cb Cg Cm Amax Emax ε₀ Kpair Kcoef Kswitch
    Kread g δ ξ hβ hν hα₀ hCξ hα hγ hγα hβcs hμcs hg hδ hgenv hδp hδb hξ hρ hAq hAmax hchβ hchν
    hchA hchD hchφ hwt1 hcells hKcK hKa hKaw hΔ hcν0 hcν hreg hε₀ hε₀le hN hBg H0 H1 hsepO hsm hc1
    hXi D0 D1 hsmall hSB hmB hEmax hCb hCg hCm hKwt hV1 hK hKpair hKcoef hKp0 hKc0 hKs0 hKr0 hsw hrd
    hanT hanW
  have hL1 : (1 : ℝ) < L := by exact_mod_cast (by omega : 1 < L)
  have hq0 : 0 ≤ (L : ℝ) ^ (-(2 * γ)) := by positivity
  have hq1 : (L : ℝ) ^ (-(2 * γ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hL1 (by linarith)
  set q : ℝ := (L : ℝ) ^ (-(2 * γ)) with hqdef
  have hη : 0 ≤ η := by
    have := Real.exp_le_exp.1 ((hgenv 0).1.trans (hgenv 0).2)
    linarith
  have hKa0 : 0 ≤ Ka := (abs_nonneg _).trans (hKa 0)
  have hΔ0 : 0 ≤ Δ := (abs_nonneg _).trans (hΔ 0)
  have hεpos : ∀ i, 0 < epsSeq L α α₀ (sc i + 1) := fun i => epsSeq_pos_aux L α α₀ hα₀ _
  have hgp : ∀ n, 0 < g n := fun n => lt_of_lt_of_le (Real.exp_pos _) (hgenv n).1
  have hbp : ∀ n, 0 < cs.beta n := fun n => by rw [hβcs n]; have := hgp n; positivity
  have hmin : ∀ {x a : ℝ}, x ≤ min a (min δc (min δs δp)) →
      x ≤ min a δc ∧ x ≤ min a δs ∧ x ≤ min a δp := by
    intro x a h
    simp only [le_min_iff] at h ⊢
    tauto
  have hKwc : Kc ≤ max Kc (max Ks Kp) := le_max_left _ _
  have hKws : Ks ≤ max Kc (max Ks Kp) := (le_max_left _ _).trans (le_max_right _ _)
  have hKwp : Kp ≤ max Kc (max Ks Kp) := (le_max_right _ _).trans (le_max_right _ _)
  have hcν' : ∀ i, ∀ x : (W.Gc i).Ω 1, ν * (W.Gc i).spacing x ^ 2 * Dδ ≤ cν ^ 2 := fun i x =>
    window_mass_spacing_le (W.Gc i) x (hKcK i) ((hδp 0).le.trans (hδb 0)) hν.le hcν (by omega)
  have hξn : ∀ t, ‖ξ t‖ ≤ Cξ * β⁻¹ * q ^ (t + 1) := fun t =>
    (pi_norm_le_iff_of_nonneg (by positivity)).2 (hξ t)
  have hρ1 : Cξ * Real.exp (2 * η) * q / (β * (1 - q)) ≤ 1 := hρ.trans (by norm_num)
  have hξhalf : ∀ t, ‖ξ t‖ ≤ 1 / 2 := fun t =>
    norm_xi_le_half_of_decay hβ hCξ hq0 hq1 hη hρ (hξ t)
  have hsc : ∀ i, sc i + 1 ≤ k := fun i => by have := W.sc_lt i; omega
  -- the source estimate
  have hsrc := Hs W cs β ν η Ka cν Dδ V1 Ksrc α α₀ g δ ξ hβ hν hα₀ hβcs hμcs hg hδ hgenv hδp hδb
    hξhalf hchβ hchν hchA hchD hchφ hwt1 hcells hKaw hcν0 hcν' hN hBg hsepO hsm hc1 hXi
    (fun i => (hmin (hsmall i)).2.1) (fun i => (hmin (hSB i)).2.1)
    (le_trans (mul_le_mul_of_nonneg_right hKws (by positivity)) hV1) hK
  -- the pair estimate
  have hpair := Hp W cs β ν η Ka cν Dδ V1 Ksrc Cξ q α α₀ A₀ Kpair g δ ξ hβ hν hα₀ hCξ hq0 hq1
    hβcs hμcs hg hδ hgenv hδp hδb hξ hρ1 hAq hchβ (fun i => hchν i k (hsc i) le_rfl) hchA
    (fun i u hu => hchφ i u hu k (hsc i) le_rfl) hwt1 hcells hKaw hcν0 hcν' hN H0
    (fun i => hBg i k (hsc i) le_rfl) hsepO hsm hc1 D0
    (fun i u hu => hXi i u hu k (hsc i) le_rfl) (fun i => (hmin (hsmall i)).2.2)
    (fun i => (hmin (hSB i)).2.2)
    (le_trans (mul_le_mul_of_nonneg_right hKwp (by positivity)) hV1) hK hKpair
  -- the coefficient comparison
  have hcoef := Hc W (fun i => cs.beta (sc i + 1) * epsSeq L α α₀ (sc i + 1) ^ 2)
    (fun i => by have := hbp (sc i + 1); have := hεpos i; positivity) (by omega) hwt1 hcells cs
    β ν η Cξ q g δ ξ hβ hCξ hq0 hq1 hβcs hμcs hg hδ
    (fun n => by rw [hμcs n]; have := hδp n; positivity) hgenv hξ
    (fun i => by simpa using hchβ i (sc i + 1) le_rfl (hsc i))
    (fun i => hchβ i k (hsc i) le_rfl) hAq α α₀ ε₀ hα hα₀ hε₀ hε₀le (fun _ => rfl)
    Ka Δ Dδ hKa hchA hΔ (fun i => hchν i k (hsc i) le_rfl) hreg (by rw [abs_of_pos (hδp k)]; exact hδb k) hCb hCg hCm hKwt hN H0 H1
    hsepO hsm hc1 D0 D1 (fun i => (hmin (hsmall i)).1) (fun i => (hmin (hmB i)).1) hEmax hAmax
  have hAm : ∀ i, 0 ≤ Amax := fun i => le_trans
    (by have := hbp (sc i + 1); have := hεpos i; positivity) (hAmax i)
  have hX : ∀ i, 0 ≤ Δ * (2 * Emax) := fun i =>
    mul_nonneg hΔ0 (by have := hεpos i; have := hEmax i; linarith)
  have hCb0 : 0 ≤ Cb := le_trans (by positivity) hCb
  have hCg0 : 0 ≤ Cg := le_trans (by positivity) hCg
  have hCm0 : 0 ≤ Cm := le_trans (by have : 0 ≤ Dδ := (hδp 0).le.trans (hδb 0); positivity) hCm
  have hT : 0 ≤ (N : ℝ) * Cb + d * (N * Cg) + N * Cm := by positivity
  have hKsrc0 : 0 ≤ Ksrc := by
    refine le_trans ?_ hK
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    positivity
  have hwin := PieceWindowSetup.window_uniform_of_parts W
    (fun i u => ((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) ((W.chain i).a k)
      ((W.chain i).ν k) ((W.chain i).Dat u k)
      (bgFieldC (W.Gc i) cs.aw ((W.chain i).ν k) (bgC0 d L N) ((W.chain i).Dat u k)))
    (fun i u => ((W.chain i).β k : ℂ) * actionRegionC (W.Xc i) W.ak ((W.chain i).ν k)
      ((W.chain i).Dat u k) (bgFieldC (W.Gc i) W.ak ((W.chain i).ν k) (bgC0 d L N)
        ((W.chain i).Dat u k)))
    R Kpair Kcoef Kswitch Kread hpair
    (fun i u hu => (hcoef i u hu).trans
      (mul_le_mul_of_nonneg_right (le_trans (coef_const_mono (hAm i) (hX i) (by positivity) hT hKc.le hKwc) hKcoef) (W.mcount_nonneg i))) hsw hrd
  exact window_conversion_pieces_of_rg_source W (fun _ m => cs.beta m) (fun _ t => ξ t) β Cξ Ksrc
    (Kpair + Kcoef + Kswitch + Kread) α α₀ γ η hβ hCξ hKsrc0
    (by linarith) (by omega) (by omega) hγ hα₀ hγα
    (fun _ => ⟨g, hgenv, hβcs⟩) (fun _ t => hξn t) hsrc hanT hwin hanW

end Assembly

end Balaban.LargeField.ActionConv
