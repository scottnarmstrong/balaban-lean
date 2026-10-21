/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusBoxBoundClass
public import Balaban.SmallField.IrrelTorusDefectBirthCapMain

/-!
# The box selection on the birth-mass domains

`norm_filed_relBox_le_power_birth_cap`: the bound `norm_filed_relBox_le_power` of the filed sum
`Σ_{Z ∋ y, relBox y Z} (T_Z + Φ_{y,Z})` for a member of the class on the birth-mass domains
`birthXiDom` (ruling R6), with the condition `e² ν̄ ≤ 7/8 L⁻²` on the constants, through the
level-only family of `IsSFFamily2.exists_levelOnly_cap` (as `norm_filed_le_power_birth_cap`): the
relevant parts read the level-`j` terms only, which the two families share;
`irrelTorus_label_bound_of_class_birth_cap`: the label bound of `irrelTorus` (ruling R15) at every
label, `irrelTorus_label_bound_of_class` on the birth-mass domains (`irrelTorus_congr_E`: the label
functional reads the terms of its level only).
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


/-- **The label functional reads the terms of its level only.** -/
theorem irrelTorus_congr_E {N₁ : ℕ} [NeZero N₁] {Tm Tm' : Terms d L N₁ m₁ k N ϱ}
    (hE : Tm'.E j = Tm.E j) (m₀ : ℕ) (i₀ i₁ : Fin N) (y : CTorus d L N₁ m₁ k)
    (X : Set (CTorus d L N₁ m₁ k)) (Ψ h : Fld d L N₁ m₁ k N) :
    irrelTorus m₀ Tm' i₀ i₁ j y X Ψ h = irrelTorus m₀ Tm i₀ i₁ j y X Ψ h := by
  simp only [irrelTorus_eq_irrelTorusOn, irrelTorusOn, relPartTorus, aTermTorus, hE]

open Classical in
/-- **The label bound of `irrelTorus` (ruling R15) for the members of the class on the birth-mass
domains** (blocker 6; `irrelTorus_label_bound_of_class` through the level-only family of
`IsSFFamily2.exists_levelOnly_cap`, with the condition `e² ν̄ ≤ 7/8 L⁻²` on the constants, ruling
R6): at every label `(j, y, X)`,
`|ℰ_{irrel}(y, X)| ≤ C_I E₀ s^{d+α₃} e^{-(κ-1) d_j(X)} + C E₀ L^{-(k-j)(d+α₃)} e^{-(κ-1) d_j(X)}
+ 1_{X = □(y)} C' E₀ L^{-(k-j)(d+α₃)}`; the data hypotheses are stated at the birth mass
`ν_j L^{-2j}` and the level coupling `ν_j` of level `j`. -/
theorem irrelTorus_label_bound_of_class_birth_cap
    (hF : IsSFFamily2 P Rg β a (birthXiDom P Rg a) Tm ρd Ek)
    (hνbar : Real.exp 2 * P.νbar ≤ 7 / 8 * ((L : ℝ) ^ 2)⁻¹)
    (hn : MomNum d L N k j ϱ P) {i₀ i₁ : Fin N} (hne : i₁ ≠ i₀)
    {N₁ : ℕ} [NeZero N₁] (hN : L ^ P.m₀ ∣ N₁)
    {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)} {S : Finset (Site d)}
    (hy : Aligned (L ^ j) y) (hX : IsPolyDom P.m₀ j X) (hyX : y ∈ X)
    (hSdef : S = (Finset.univ.filter (fun x => Aligned (L ^ j) x ∧ x ∈ X)).image
      (fun x => unlift (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j (x - y)))
    {Ψ : Fld d L N₁ m₁ k N} {hv : Fin N → ℂ}
    (hΨb : ∀ x x', jBlock d L (N₁ * L ^ m₁) k j x =
      jBlock d L (N₁ * L ^ m₁) k j x' → Ψ x = Ψ x')
    {Λ Ksig γ C₀ KR s σ ε K₂ q ρ Cρ : ℝ}
    (hΛ : 1 ≤ Λ) (hKsig : 0 ≤ Ksig) (hC₀ : 0 < C₀)
    (dat : DataHypAniso {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) (Rg.ν j) S
            (pack S p.1 p.2) z) ∧
        XiDom ((Tm N₁).gs j X) (aIdeal L k (a k)) (physMass L j (Rg.ν j)) j (P.eps d L j) Ψ' h'}
      (Rg.ν j) σ ε K₂
      (fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v))
      (((Rg.ν j : ℝ) : ℂ) • hv))
    (hs : 0 < s) (hσs : σ = C₀ * s)
    (hR : ε / anisoRadius d L N P j ≤ KR * s ^ (((d : ℝ) - 2) / 2 - γ))
    (hε : 0 < ε) (hεΛ : ε ≤ Λ * anisoRadius d L N P j) (hσ1 : σ ≤ 1)
    (hτ : σ ^ 2 * ε ≤ 1 / 4) (hνσ : Rg.ν j ≤ σ ^ 2)
    (hK : K₂ ≤ Ksig * σ ^ (2 - P.α₁) * ε)
    (hcentre : ∀ i, ‖Ψ y i - (Pi.single i₀ 1 : Spin N) i‖ ≤ q)
    (hb : ∀ i, ‖(((Rg.ν j : ℝ) : ℂ) • hv) i -
      ((Rg.ν j : ℝ) : ℂ) * (Pi.single i₀ 1 : Spin N) i‖ ≤ anisoRadius d L N P j)
    (hbl : ‖(((Rg.ν j : ℝ) : ℂ) • hv) i₀ - ((Rg.ν j : ℝ) : ℂ)‖ <
      anisoRadius d L N P j ^ 2)
    (hρ : 0 < ρ)
    (hbase : q + diamA d L P.m₀ m₁ * (σ * ε) / ρ ≤ anisoRadius d L N P j)
    (hCρ : 0 ≤ Cρ)
    (hρpow : ρ ^ 3 ≤ Cρ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)))
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
    ∃ CI : ℝ, 0 ≤ CI ∧
      ‖irrelTorus P.m₀ (Tm N₁) i₀ i₁ j y X Ψ (constFld hv)‖ ≤
        CI * P.E₀ * s ^ ((d : ℝ) + (1 - 2 * γ - P.α₁)) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        relBoxLargeConst d L N P m₁ Λ * P.E₀ *
          ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁))) *
          Real.exp (-(P.κ - 1) * sizeJ P.m₀ j X) +
        (if X = box (cbase (cellSide L P.m₀ m₁ j) y -
            natT fun _ => L / 2 * cellSide L P.m₀ m₁ j) (L * cellSide L P.m₀ m₁ j) then
          (filedPowerConst d L N P m₁ Λ + relBoxTailConst d L N P m₁ Λ) * P.E₀ *
            ((L : ℝ) ^ (k - j)) ^ (-((d : ℝ) + (1 - 2 * P.γ - P.α₁)))
          else 0) := by
  obtain ⟨Rg', β', Tm', hν, hT, hF'⟩ :=
    hF.exists_levelOnly_cap (by have := hn.hL; omega) hn.hj1 hn.hjk hνbar
  have hE : ∀ (N₁ : ℕ) [NeZero N₁], (Tm' N₁).E j = (Tm N₁).E j := fun N₁ _ => (hT N₁).1
  have hgs : (Tm' N₁).gs = (Tm N₁).gs := (hT N₁).2.2
  have hnu : nuIdeal L k (Rg'.ν k) j = Rg.ν j := by rw [hν]; exact nuIdeal_levelOnly j k _
  have hmass : Rg'.sfBgMass k = physMass L j (Rg.ν j) := by
    show physMass L k (Rg'.ν k) = _
    rw [hν]
    exact physMass_levelOnly j k hn.hjk _
  have hn' : MomNum d L N k j ϱ
      { P with p := fun _ => 0, c₉ := |P.c₉| + 1, νbar := Real.exp 2 * P.νbar } :=
    ⟨hn.hd, hn.hL, hn.hϱ, hn.hκ, hn.hj1, hn.hjk, hn.hsmall⟩
  have dat' := dat
  rw [← hmass, ← hnu, ← hgs] at dat'
  have hνσ' := hνσ
  rw [← hnu] at hνσ'
  have hb' := hb
  have hbl' := hbl
  rw [← hnu] at hb' hbl'
  have hdat' := @hdat
  rw [← hnu] at hdat'
  obtain ⟨CI, hCI0, hCI⟩ := irrelTorus_label_bound_of_class hF' hn' hne hN hy hX hyX hSdef hΨb hΛ
    hKsig hC₀ dat' hs hσs hR hε hεΛ hσ1 hτ hνσ' hK hcentre hb' hbl' hρ hbase hCρ hρpow hdat' hsec
  refine ⟨CI, hCI0, ?_⟩
  rw [← irrelTorus_congr_E (hE N₁)]
  exact hCI

end Balaban.SmallField.Def6v2
