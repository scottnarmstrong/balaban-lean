/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Balaban.SmallField.IrrelTorusXidomCanonicalData
public import Balaban.SmallField.IrrelTorusBoundId

/-!
# The chosen composition in the torus label's exact pullback domain

The domain below is the existential `Dom` consumed by the landed torus irrelevant bound.
Its `XiDom` mass is a parameter, so an inherited label may use its birth mass.
-/

@[expose] public section

namespace Balaban.SmallField

open Balaban Balaban.Background Balaban.Multiscale Balaban.Localization
  Balaban.SmallField.GsSpec Balaban.SmallField.Def6 Balaban.SmallField.Def6v2

variable {d L N₁ m₁ k N j : ℕ} [NeZero N₁] [NeZero L] {ϱ ϱ' : ℝ}
  {G' : GeneratingSet d L (N₁ * L ^ m₁) k ϱ'}
  {a₁ ν s e ε θh μ : ℝ} {D : BgData G' N}
  {P : Consts} {Tm : Terms d L N₁ m₁ k N ϱ}
  {y : CTorus d L N₁ m₁ k} {X : Set (CTorus d L N₁ m₁ k)}
  {S : Finset (Site d)} {i₀ : Fin N}

/-- `DataHypAniso` on the exact existential pullback carrier of the torus label. The two
membership hypotheses are the same-mass chart obligation for the full field and its centre. -/
theorem xiCData_dataHypAniso_exact_pullback
    (hd : 3 ≤ d) (hL : 3 ≤ L) (hj1 : 1 ≤ j) (hjk : j < k)
    (H' : BgHyp d L k ϱ' (compWeight L a₁) ν)
    (hprec : Precedes (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le) G')
    (ha₁ : 0 < a₁) (hs : 0 < s) (hs1 : s ≤ 1)
    (hjs : (L : ℝ) ^ j = s * (L : ℝ) ^ k)
    (hgap : ScaleGap (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le) G' s)
    (hcol : ∀ z ∈ collar (levelGS (d := d) (L := L) (N₁ := N₁)
      (m₁ := m₁) (k := k) (ϱ := ϱ) j hjk.le), z ∈ G'.Ω 1 ∧ 1 ≤ s * G'.spacing z)
    (hsmall : (4 * d + 6) * (xiC1 d * e) ≤ 1)
    (hc1 : xiC1 d * e ≤ bgC1 d L N)
    (hD : XiCData G' (compWeight L a₁) ν k 1 e D)
    (hθh0 : 0 < θh) (hθh1 : θh < 1)
    (hν : 0 < ν * ((L : ℝ) ^ j) ^ 2)
    (hτ1 : scaledC0 d * s ≤ 1)
    (hντ : ν * ((L : ℝ) ^ j) ^ 2 ≤ (scaledC0 d * s) ^ 2)
    (hζ1 : xiC1 d * e ≤ 1 / 200) (hee : e ≤ ε) :
    let Ψ : Fld d L N₁ m₁ k N := composeField
      (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
        (k := k) (ϱ := ϱ) j hjk.le)
      G' (compWeight L a₁)
      (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ
    let ψ : Site d → Spin N :=
      fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v)
    let b : Spin N := (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • D.h y)
    let Dom : Set ((Site d → Spin N) × Spin N) :=
      {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
        (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
            (pack S p.1 p.2) (z - y) ∧
          h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
            (ν * ((L : ℝ) ^ j) ^ 2) S (pack S p.1 p.2) z) ∧
        XiDom (Tm.gs j X) (compWeight L a₁) μ j (P.eps d L j) Ψ' h'}
    ∃ B : ℝ, 0 ≤ B ∧
      ((ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom →
        DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2)
          (16 * scaledC0 d * xiC1 d * s) ε
          (xiSigma d L N B θh * s ^ (2 - θh) * e) ψ b) := by
  let Ψ : Fld d L N₁ m₁ k N := composeField
    (levelGS (d := d) (L := L) (N₁ := N₁) (m₁ := m₁)
      (k := k) (ϱ := ϱ) j hjk.le)
    G' (compWeight L a₁)
    (bgFieldC G' (compWeight L a₁) ν (bgC0 d L N) D) D.Ψ
  let ψ : Site d → Spin N :=
    fun v => Ψ (y + ibase (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j v)
  let b : Spin N := (((ν * ((L : ℝ) ^ j) ^ 2 : ℝ) : ℂ) • D.h y)
  let Dom : Set ((Site d → Spin N) × Spin N) :=
    {p | ∃ Ψ' h' : Fld d L N₁ m₁ k N,
      (∀ z ∈ X, Ψ' z = fieldOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k) j i₀ S
          (pack S p.1 p.2) (z - y) ∧
        h' z = hOf (L := L) (N₁ := N₁) (m₁ := m₁) (k := k)
          (ν * ((L : ℝ) ^ j) ^ 2) S (pack S p.1 p.2) z) ∧
      XiDom (Tm.gs j X) (compWeight L a₁) μ j (P.eps d L j) Ψ' h'}
  change ∃ B : ℝ, 0 ≤ B ∧
    ((ψ, b) ∈ Dom ∧ ((fun _ => ψ 0), b) ∈ Dom →
      DataHypAniso Dom (ν * ((L : ℝ) ^ j) ^ 2)
        (16 * scaledC0 d * xiC1 d * s) ε
        (xiSigma d L N B θh * s ^ (2 - θh) * e) ψ b)
  obtain ⟨B, hB0, hB⟩ := xiCData_dataHypAniso_of_levelGS_canonical
    hd hL hj1 hjk H' hprec ha₁ hs hs1 hjs hgap hcol hsmall hc1 hD
    hθh0 hθh1 hν hτ1 hντ hζ1 hee
  refine ⟨B, hB0, ?_⟩
  intro hchart
  exact hB y ψ b (fun _ => rfl) rfl hchart

end Balaban.SmallField
