/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBoxBoundClass
public import Balaban.SmallField.IrrelTorusDefectBirthCapMain

/-!
# The filed sum of the box selection on the birth-mass domains

`norm_filed_relBox_le_power_birth_cap`: the bound `norm_filed_relBox_le_power` of the filed sum
`Σ_{Z ∋ y, relBox y Z} (T_Z + Φ_{y,Z})` for a member of the class on the birth-mass domains
`birthXiDom` (ruling R6), with the condition `e² ν̄ ≤ 7/8 L⁻²` on the constants, through the
level-only family of `IsSFFamily2.exists_levelOnly_cap` (as `norm_filed_le_power_birth_cap`): the
relevant parts read the level-`j` terms only, which the two families share.
-/

@[expose] public section

namespace Balaban.SmallField.Def6v2

open Balaban Balaban.Multiscale Balaban.Background Balaban.Localization Balaban.SmallField
  Balaban.SmallField.Def6 Balaban.Fluctuation Metric Set Filter

variable {d L m₁ k N : ℕ} [NeZero L] {ϱ : ℝ} {P : Consts} {Rg : Regime L} {β a : ℕ → ℝ}
  {Ek : ℕ → ℝ}
  {Tm : ∀ (N₁ : ℕ) [NeZero N₁], Terms d L N₁ m₁ k N ϱ}
  {ρd : ∀ (N₁ : ℕ) [NeZero N₁], (CTorus d L N₁ m₁ k → Fin N → ℝ) → (Fin N → ℝ) →
    (CTorus d L N₁ m₁ k → Fin N → ℝ) → ℝ}
  {j : ℕ}

open Classical in
/-- **The filed sum of the selection `relBox` on the birth-mass domains** (as
`norm_filed_relBox_le_power`, through `IsSFFamily2.exists_levelOnly_cap`, the condition
`e² ν̄ ≤ 7/8 L⁻²` on the constants, ruling R6; the relevant parts read the level-`j` terms only). -/
theorem norm_filed_relBox_le_power_birth_cap
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hνbar : Real.exp 2 * P.νbar ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} (hy : Aligned (L ^ j) y)
    (Ψ : Fld d L N₁ m₁ k N) (hv : Fin N → ℂ)
    {σ ε K₂ Λ : ℝ} (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hε : 0 < ε)
    (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hτ : σ ^ 2 * ε ≤ 1 / 4)
    (hdat : ∀ {Dom : Set ((Site d → Spin N) × Spin N)},
      ((fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom ∧
        ((fun _ => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j 0)),
          ((Rg.ν j : ℝ) : ℂ) • hv) ∈ Dom →
      (∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) →
      DataHypAniso Dom (Rg.ν j) σ ε K₂
        (fun s => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j s))
        (((Rg.ν j : ℝ) : ℂ) • hv))
    (hsec : ∀ (x : Site d) (μ μ' : Fin d),
        ‖Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j
            (x + Pi.single μ 1 + Pi.single μ' 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ 1)) -
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x + Pi.single μ' 1)) +
          Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j x)‖ ≤ K₂) :
    ‖∑ᶠ Z ∈ polysAt P.m₀ j y,
        (if relBox P.m₀ y Z then relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z else 0)‖ ≤
      (filedPowerConst d L N P m₁ Λ + relBoxTailConst d L N P m₁ Λ) * P.E₀ *
        (((L : ℝ) ^ (k - j)) ^ (-(((d : ℝ) + (1 - 2 * P.γ - P.α₁))))) := by
  obtain ⟨Rg', β', Tm', hν, hT, hF'⟩ :=
    hF.exists_levelOnly_cap (by have := hn.hL; omega) hn.hj1 hn.hjk hνbar
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hdat' := @hdat
  rw [← hnu] at hdat'
  have hn' : MomNum d L N k j ϱ
      { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  have h := norm_filed_relBox_le_power hF' hn' hne hN hy Ψ hv hσ hσ1 hε hεΛ hτ hdat' hsec
  have hR : ∀ Z, relPartTorus (Tm' N₁) i₀ i₁ j y Ψ (constFld hv) Z =
      relPartTorus (Tm N₁) i₀ i₁ j y Ψ (constFld hv) Z := fun Z => by
    simp only [relPartTorus, hE N₁]
  simp only [hR] at h
  exact h

end Balaban.SmallField.Def6v2
