/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomBound
public import Balaban.SmallField.IrrelTorusDefectBirthSurrogate

/-!
# The non-special label estimate on the birth-mass domains

The class of ruling R6 is on the birth-mass domains `birthXiDom` (mass `μ_j` at the level `j`), while
the non-special label estimate `irrelTorus_bound_of_dataOn_of_threshold` takes the class clauses on
the one-mass domain `xiFieldDom a μ ε`.  A label of the level `j` reads the terms of that level
only, so the estimate holds for the birth-mass class at the birth mass of the level
(`irrelTorus_bound_of_dataOn_of_threshold_birth`), through the level-only family of the terms.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L N₁ m₁ k N : ℕ} [NeZero L] [NeZero N₁] {ϱ : ℝ}
  {P : Consts} {ν : ℝ} {Tm : Terms d L N₁ m₁ k N ϱ} {j : ℕ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}

open Classical in
/-- **The non-special label estimate for a class on the birth-mass domains** (ruling R6; (M5)): the
class clauses on `birthXiDom` (mass `μ_j = ν_j L^{-2j}` at the level `j`) and the standing
hypotheses at the birth mass of the level of the label.  The label reads the terms of its level
only: the level-only family `Tm'` (`exists_levelOnly_terms`) satisfies the clauses on the one-mass
domain `xiFieldDom` at `μ_j` (`SFTermClauses.levelOnly`), to which
`irrelTorus_bound_of_dataOn_of_threshold` applies, and its irrelevant part is that of `Tm`. -/
theorem irrelTorus_bound_of_dataOn_of_threshold_birth
    (hP : P.Admissible d L)
    {Rg : Regime L} {a : ℕ → ℝ}
    (hcl : SFTermClauses P (birthXiDom P Rg a N₁) Tm)
    (hBg : BgHyp d L k ϱ (aIdeal L k (a k)) (physMass L j (Rg.ν j))) (hN : L ^ P.m₀ ∣ N₁)
    (hν : 0 < ν) (hμν : physMass L j (Rg.ν j) * ((L : ℝ) ^ j) ^ 2 ≤ ν) (hνb : ν ≤ 1)
    (hj1 : 1 ≤ j) (hjk : j ≤ k)
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hXne : X ≠ box (cbase (cellSide L P.m₀ m₁ j) y -
      natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j))
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀) {r : ℝ} (hrad : AnisoRadiusOK d L N P j r)
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ z ∈ X, ∀ x, jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j z → Ψ x = Ψ z)
    {Λ Ksig γ C₀ KR s σ ε K₂ q ρ Cρ A : ℝ} (hAd : diamA d L P.m₀ m₁ ≤ A)
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAnisoOn {S} (fun _ => A * (1 + sizeJ P.m₀ j X))
      {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) ν S
            (pack S p.1 p.2) z) ∧
        XiDom (Tm.gs j X) (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ' h'}
      ν σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      ((ν : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / r ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * r) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : ν ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖((ν : ℂ) • hv) i -
      (ν : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ r)
    (hbl : ‖((ν : ℂ) • hv) i₀ - (ν : ℂ)‖ < r ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + A * (σ * ε) / ρ ≤ r)
    (hCρ : 0 ≤ Cρ)
    (hρpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁))) :
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) := by
  obtain ⟨Tm', hE, hM, hgs, hE0, hM0⟩ := exists_levelOnly_terms Tm j
  set P' : Consts := { P with c₉ := |P.c₉| + 1 } with hP'def
  have hP' : P'.Admissible d L := ⟨hP.γ_pos, hP.γ_lt, hP.α₁_pos, hP.α₁_lt, hP.α₀_pos, hP.κ_pos,
    hP.νbar_pos, hP.νbar_le, hP.c₈_pos, hP.E₀_nonneg⟩
  have hcl' : SFTermClauses P'
      (xiFieldDom (aIdeal L k (a k)) (physMass L j (Rg.ν j)) (P.eps d L)) Tm' :=
    (hcl.of_c9_le (c := |P.c₉| + 1) (by linarith [le_abs_self P.c₉])).levelOnly
      (fun _ _ _ => Iff.rfl) hE hM hgs hE0 hM0 hP.E₀_nonneg (by positivity)
  have hirr : irrelTorus P.m₀ Tm' i₀ i₁ j y X Ψ (constFld hv) =
      irrelTorus P.m₀ Tm i₀ i₁ j y X Ψ (constFld hv) := by
    simp only [irrelTorus, hE]
  rw [← hirr]
  exact irrelTorus_bound_of_dataOn_of_threshold (P := P') (Tm := Tm') hP' hcl' hBg hN hν hμν hνb
    hj1 hjk hy hX hyX hXne hSdef hne hrad hΨb hAd hΛ hKsig hC₀ (by rw [hgs]; exact dat) hs hσs
    hR hε hεΛ hσ1 hτ hνσ hK hcentre hb hbl hρ hbase hCρ hρpow

end Balaban.SmallField.Def6v2
