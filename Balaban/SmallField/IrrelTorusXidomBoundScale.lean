/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomBound
public import Balaban.SmallField.IrrelTorusXidomThresholdScale
import Mathlib.Tactic.Linarith

/-!
# The non-special label bound from the scale ratio
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {a : ℕ → ℝ} {μ ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- For a centre within half the chart radius, the standard scale ratio fixes the
small-versus-large threshold and gives the per-label anisotropic estimate. -/
theorem irrelTorus_bound_of_dataHyp_of_scale_ratio
    (hP : P.Admissible d L)
    (hcl : SFTermClauses P (xiFieldDom a μ (P.eps d L)) Tm)
    (hBg : BgHyp d L k ϱ a μ) (hN : L ^ P.m₀ ∣ N₁)
    (hν : 0 < ν) (hμν : μ * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X) (hsm : relBox P.m₀ y X)
    (hXne : X ≠ box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j))
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {Λ Ksig γ C₀ KR s σ ε K₂ q : ℝ}
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S
            (pack S p.1 p.2) z) ∧
        XiDom (Tm.gs j X) a μ j (P.eps d L j) Ψ' h'} ν σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      ((ν : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεr : ε ≤ r) (hεΛ : ε ≤ Λ * r) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : ν ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hq : q ≤ r / 2)
    (hb : ∀ i, ‖((ν : ℂ) • hv) i -
      (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖((ν : ℂ) • hv) i₀ - (ν : ℂ)‖ < r ^ 2) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  have hα1 : P.α₁ < 1 := by
    have := hP.α₁_lt
    have := hP.γ_pos
    linarith
  obtain ⟨ρ, Cρ, hρ, hCρ, hbase, hρpow⟩ :=
    threshold_of_scale_ratio (A := diamA d L P.m₀ m₁)
      (α := P.α₁) (diamA_nonneg d L P.m₀ m₁) hC₀ hs hσs hσ1
      hε hrad.1 hεr hR hq hP.α₁_pos.le hα1
  exact irrelTorus_bound_of_dataHyp_of_threshold hP hcl hBg hN hν hμν hνb
    hj1 hjk hy hX hyX hsm hXne hSdef hne hrad hΨb hΛ hKsig hC₀ dat
    hs hσs hR hε hεΛ hσ1 hτ hνσ hK hcentre hb hbl hρ hbase hCρ hρpow

end Balaban.SmallField.Def6v2
